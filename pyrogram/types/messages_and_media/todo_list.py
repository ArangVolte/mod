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
from pyrogram import raw, types
from ..object import Object


class TodoList(Object):
    """A list of tasks.

    Parameters:
        title (``str``):
            Title of the todo list.

        entities (List of :obj:`~pyrogram.types.MessageEntity`):
            Entities in the title of the todo list.

        tasks (List of :obj:`~pyrogram.types.TodoTask`):
            List of tasks in the todo list.

        can_append (``bool``, optional):
            True, if other users can append tasks to this todo list.

        can_complete (``bool``, optional):
            True, if other users can complete tasks in this todo list.
    """

    def __init__(
        self,
        title: str,
        entities: List["types.MessageEntity"],
        tasks: List["types.TodoTask"] = None,
        can_append: bool = False,
        can_complete: bool = False
    ):
        super().__init__()

        self.title = title
        self.entities = entities
        self.tasks = tasks
        self.can_append = can_append
        self.can_complete = can_complete

    @staticmethod
    def _parse(
        client: "pyrogram.Client",
        todo: "raw.types.TodoList",
        users: Dict = None
    ) -> "TodoList":
        # ============================================================
        # FIX #1: Guard users=None
        # ============================================================
        if users is None:
            users = {}

        # ============================================================
        # FIX #2: Guard todo.todo=None
        # ============================================================
        todo_list = getattr(todo, "todo", None)
        if todo_list is None:
            return TodoList(
                title="",
                entities=types.List([]),
                tasks=[],
                can_append=False,
                can_complete=False
            )

        completions = getattr(todo, "completions", None) or []

        # ============================================================
        # FIX #3: Guard title & entities=None
        # ============================================================
        title_obj = getattr(todo_list, "title", None)
        title_text = ""
        raw_entities = []
        if title_obj is not None:
            title_text = getattr(title_obj, "text", "") or ""
            raw_entities = getattr(title_obj, "entities", None) or []

        title_entities = []
        for entity in raw_entities:
            try:
                parsed = types.MessageEntity._parse(client, entity, users)
                if parsed is not None:
                    title_entities.append(parsed)
            except Exception:
                continue

        # ============================================================
        # FIX #4: Guard list tasks=None
        # ============================================================
        raw_tasks = getattr(todo_list, "list", None) or []
        tasks = []
        for task in raw_tasks:
            try:
                parsed_task = types.TodoTask._parse(
                    client, task, users, completions
                )
                if parsed_task is not None:
                    tasks.append(parsed_task)
            except Exception:
                continue

        return TodoList(
            title=title_text,
            entities=types.List(title_entities),
            tasks=tasks,
            can_append=getattr(todo_list, "others_can_append", False) or False,
            can_complete=getattr(todo_list, "others_can_complete", False) or False
        )
