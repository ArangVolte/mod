#  Pyrofork - Telegram MTProto API Client Library for Python
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


from typing import List, Dict

import pyrogram
from pyrogram import raw, types, utils
from ..object import Object


class TodoTask(Object):
    """A task in a todo list.

    Parameters:
        title (``str``):
            Title of the task.

        entities (List of :obj:`~pyrogram.types.MessageEntity`):
            Entities in the title of the task.

        is_completed (``bool``):
            True, if the task is completed.

        completed_by (:obj:`~pyrogram.types.User`, *optional*):
            User who completed the task.

        complete_date (:obj:`~datetime.datetime`, *optional*):
            Date when the task was completed.
    """

    def __init__(
        self,
        id: int,
        title: str,
        entities: List["types.MessageEntity"],
        is_completed: bool,
        completed_by: "types.User" = None,
        complete_date: "pyrogram.types.datetime" = None
    ):
        super().__init__()

        self.id = id
        self.title = title
        self.entities = entities
        self.is_completed = is_completed
        self.completed_by = completed_by
        self.complete_date = complete_date

    @staticmethod
    def _parse(
        client: "pyrogram.Client",
        todo_task: "raw.types.TodoTask",
        users: Dict = None,
        completions: List["raw.types.TodoTaskCompletion"] = None
    ) -> "TodoTask":
        # ============================================================
        # FIX #1: Guard users=None -> dict kosong
        # ============================================================
        if users is None:
            users = {}

        # ============================================================
        # FIX #2: Guard completions=None / bukan list
        # ============================================================
        if completions is None:
            completions = []
        elif not isinstance(completions, (list, tuple)):
            try:
                completions = list(completions)
            except Exception:
                completions = []

        # ============================================================
        # FIX #3: Guard todo_task.title / title.entities = None
        # ============================================================
        title_obj = getattr(todo_task, "title", None)
        title_text = ""
        raw_entities = []
        if title_obj is not None:
            title_text = getattr(title_obj, "text", "") or ""
            raw_entities = getattr(title_obj, "entities", None) or []

        # Parse entities dengan try/except per entity (jangan crash kalau rusak)
        entities = []
        for entity in raw_entities:
            try:
                parsed = types.MessageEntity._parse(client, entity, users)
                if parsed is not None:
                    entities.append(parsed)
            except Exception:
                continue

        # ============================================================
        # FIX #4: Build completions map dengan aman
        # ============================================================
        complete = {}
        for i in completions:
            try:
                complete[i.id] = i
            except Exception:
                continue

        todo_completion = complete.get(getattr(todo_task, "id", None))

        # ============================================================
        # FIX #5: Guard completed_by & date
        # ============================================================
        completed_by = None
        if todo_completion is not None:
            try:
                completed_by_id = getattr(todo_completion, "completed_by", None)
                if completed_by_id is not None:
                    completed_by = types.User._parse(
                        client, users.get(completed_by_id, None)
                    )
            except Exception:
                completed_by = None

        complete_date = None
        if todo_completion is not None:
            try:
                date_val = getattr(todo_completion, "date", None)
                if date_val is not None:
                    complete_date = utils.timestamp_to_datetime(date_val)
            except Exception:
                complete_date = None

        return TodoTask(
            id=getattr(todo_task, "id", 0),
            title=title_text,
            entities=types.List(entities),
            is_completed=True if todo_completion else False,
            completed_by=completed_by,
            complete_date=complete_date
        )
