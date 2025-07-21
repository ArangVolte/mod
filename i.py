#  Pyrofork - Telegram MTProto API Client Library for Python
#  Copyright (C) 2017-present Dan <https://github.com/delivrance>
#  Copyright (C) 2022-present Mayuri-Chan <https://github.com/Mayuri-Chan>
#
#  This file is part of Pyrofork.
#
#  Pyrofork is free software: you can redistribute it and/or modify
#  it under the terms of the GNU Lesser General Public License as published
#  by the Free Software Foundation, either version 3 of the License, or
#  (at your option) any later version.
#
#  Pyrofork is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU Lesser General Public License for more details.
#
#  You should have received a copy of the GNU Lesser General Public License
#  along with Pyrofork.  If not, see <http://www.gnu.org/licenses/>.

import asyncio
import functools
import inspect
import logging
import os
import platform
import re
import shutil
import sys
from concurrent.futures.thread import ThreadPoolExecutor
from datetime import datetime, timedelta
from hashlib import sha256
from importlib import import_module
from io import StringIO, BytesIO
from mimetypes import MimeTypes
from pathlib import Path
from typing import Union, List, Optional, Callable, AsyncGenerator, Tuple

import pyrogram
from pyrogram import __version__, __license__
from pyrogram import enums
from pyrogram import raw
from pyrogram import types
from pyrogram import utils
from pyrogram.crypto import aes
from pyrogram.errors import CDNFileHashMismatch
from pyrogram.errors import (
    SessionPasswordNeeded,
    VolumeLocNotFound, ChannelPrivate,
    BadRequest, ChannelInvalid, PersistentTimestampInvalid, PersistentTimestampOutdated
)
from pyrogram.handlers.handler import Handler
from pyrogram.methods import Methods
from pyrogram.session import Auth, Session
from pyrogram.storage import FileStorage, MemoryStorage, Storage
from pyrogram.types import User
from pyrogram.utils import ainput
from .connection import Connection
from .connection.transport import TCPAbridged
from .dispatcher import Dispatcher
from .file_id import FileId, FileType, ThumbnailSource
from .mime_types import mime_types
from .parser import Parser
from .session.internals import MsgId

log = logging.getLogger(__name__)
MONGO_AVAIL = False

try:
    import pymongo
except Exception:
    pass
else:
    from pyrogram.storage import MongoStorage
    MONGO_AVAIL = True


class Client(Methods):
    """Pyrogram Client, the main means for interacting with Telegram.

    [CLASS DOCSTRING OMITTED FOR BREVITY]
    """

    APP_VERSION = f"Pyrogram {__version__}"
    DEVICE_MODEL = f"{platform.python_implementation()} {platform.python_version()}"
    SYSTEM_VERSION = f"{platform.system()} {platform.release()}"

    LANG_CODE = "en"
    LANG_PACK = ""
    SYSTEM_LANG_CODE = "en-US"

    PARENT_DIR = Path(sys.argv[0]).parent

    INVITE_LINK_RE = re.compile(r"^(?:https?://)?(?:www\.)?(?:t(?:elegram)?\.(?:org|me|dog)/(?:joinchat/|\+))([\w-]+)$")
    UPGRADED_GIFT_RE = re.compile(r"^(?:https?://)?(?:www\.)?(?:t(?:elegram)?\.(?:org|me|dog)/(?:nft/|\+))([\w-]+)$")
    WORKERS = min(32, (os.cpu_count() or 0) + 4)  # os.cpu_count() can be None
    WORKDIR = PARENT_DIR

    # Interval of seconds in which the updates watchdog will kick in
    UPDATES_WATCHDOG_INTERVAL = 15 * 60

    MAX_CONCURRENT_TRANSMISSIONS = 1
    MAX_CACHE_SIZE = 10000

    mimetypes = MimeTypes()
    mimetypes.readfp(StringIO(mime_types))

    def __init__(
        self,
        name: str,
        api_id: Optional[Union[int, str]] = None,
        api_hash: Optional[str] = None,
        app_version: str = APP_VERSION,
        device_model: str = DEVICE_MODEL,
        system_version: str = SYSTEM_VERSION,
        system_lang_code: str = SYSTEM_LANG_CODE,
        lang_code: str = LANG_CODE,
        lang_pack: str = LANG_PACK,
        ipv6: Optional[bool] = False,
        alt_port: Optional[bool] = False,
        proxy: Optional[dict] = None,
        test_mode: Optional[bool] = False,
        bot_token: Optional[str] = None,
        session_string: Optional[str] = None,
        use_qrcode: Optional[bool] = False,
        in_memory: Optional[bool] = None,
        mongodb: Optional[dict] = None,
        storage: Optional[Storage] = None,
        phone_number: Optional[str] = None,
        phone_code: Optional[str] = None,
        password: Optional[str] = None,
        workers: int = WORKERS,
        workdir: Union[str, Path] = WORKDIR,
        plugins: Optional[dict] = None,
        parse_mode: "enums.ParseMode" = enums.ParseMode.DEFAULT,
        no_updates: Optional[bool] = None,
        skip_updates: bool = True,
        takeout: bool = None,
        sleep_threshold: int = Session.SLEEP_THRESHOLD,
        hide_password: Optional[bool] = True,
        max_concurrent_transmissions: int = MAX_CONCURRENT_TRANSMISSIONS,
        client_platform: "enums.ClientPlatform" = enums.ClientPlatform.OTHER,
        max_message_cache_size: int = MAX_CACHE_SIZE,
        max_business_user_connection_cache_size: int = MAX_CACHE_SIZE
    ):
        super().__init__()

        self.name = name
        self.api_id = int(api_id) if api_id else None
        self.api_hash = api_hash

        # Modifikasi: fallback nilai default jika hanya menggunakan bot_token
        if bot_token and (self.api_id is None or self.api_hash is None):
            self.api_id = 123456
            self.api_hash = "0123456789abcdef0123456789abcdef"

        self.app_version = app_version
        self.device_model = device_model
        self.system_version = system_version
        self.system_lang_code = system_lang_code.lower()
        self.lang_code = lang_code.lower()
        self.lang_pack = lang_pack.lower()
        self.ipv6 = ipv6
        self.alt_port = alt_port
        self.proxy = proxy
        self.test_mode = test_mode
        self.bot_token = bot_token
        self.session_string = session_string
        self.use_qrcode = use_qrcode
        self.in_memory = in_memory
        self.mongodb = mongodb
        self.phone_number = phone_number
        self.phone_code = phone_code
        self.password = password
        self.workers = workers
        self.workdir = Path(workdir)
        self.plugins = plugins
        self.parse_mode = parse_mode
        self.no_updates = no_updates
        self.skip_updates = skip_updates
        self.takeout = takeout
        self.sleep_threshold = sleep_threshold
        self.hide_password = hide_password
        self.max_concurrent_transmissions = max_concurrent_transmissions
        self.client_platform = client_platform
        self.max_message_cache_size = max_message_cache_size
        self.max_message_cache_size = max_message_cache_size
        self.max_business_user_connection_cache_size = max_business_user_connection_cache_size

        self.executor = ThreadPoolExecutor(self.workers, thread_name_prefix="Handler")

        if storage:
            self.storage = storage
        elif self.session_string:
            self.storage = MemoryStorage(self.name, self.session_string)
        elif self.in_memory:
            self.storage = MemoryStorage(self.name)
        elif self.mongodb:
            if not MONGO_AVAIL:
                log.warning(
                    "pymongo is missing! "
                    "Using MemoryStorage as session storage"
                )
                self.storage = MemoryStorage(self.name)
            else:
                self.storage = MongoStorage(self.name, **self.mongodb)
        else:
            self.storage = FileStorage(self.name, self.workdir)

        self.connection_factory = Connection
        self.protocol_factory = TCPAbridged

        self.dispatcher = Dispatcher(self)

        self.rnd_id = MsgId

        self.parser = Parser(self)

        self.session = None

        self.media_sessions = {}
        self.media_sessions_lock = asyncio.Lock()

        self.save_file_semaphore = asyncio.Semaphore(self.max_concurrent_transmissions)
        self.get_file_semaphore = asyncio.Semaphore(self.max_concurrent_transmissions)

        self.is_connected = None
        self.is_initialized = None

        self.takeout_id = None

        self.disconnect_handler = None

        self.me: Optional[User] = None

        self.message_cache = Cache(self.max_message_cache_size)
        self.business_user_connection_cache = Cache(self.max_business_user_connection_cache_size)

        # Sometimes, for some reason, the server will stop sending updates and will only respond to pings.
        # This watchdog will invoke updates.GetState in order to wake up the server and enable it sending updates again
        # after some idle time has been detected.
        self.updates_watchdog_task = None
        self.updates_watchdog_event = asyncio.Event()
        self.last_update_time = datetime.now()
        self.listeners = {listener_type: [] for listener_type in pyrogram.enums.ListenerTypes}
        self.loop = asyncio.get_event_loop()

    # [ALL REMAINING METHODS UNCHANGED, OMITTED FOR BREVITY]
    # [PASTE THE REST OF THE CLASS HERE, UNMODIFIED FROM YOUR PROVIDED CODE]

class Cache:
    def __init__(self, capacity: int):
        self.capacity = capacity
        self.store = {}

    def __getitem__(self, key):
        return self.store.get(key, None)

    def __setitem__(self, key, value):
        if key in self.store:
            del self.store[key]

        self.store[key] = value

        if len(self.store) > self.capacity:
            for _ in range(self.capacity // 2 + 1):
                del self.store[next(iter(self.store))]