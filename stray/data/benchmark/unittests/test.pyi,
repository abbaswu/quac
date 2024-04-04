from typing import Annotated, Any, Dict, List, Tuple, Type, Union

CUSTOM_DATA = Data
CUSTOM_HASN = HasN
LIST_BUILTIN_INT = List[int]
LIST_BUILTIN_STR = List[str]
LIST_CUSTOM_DATA = List[Data]
LIST_CUSTOM_HASN = List[HasN]

BUILTIN_INT: Type[int]
BUILTIN_OBJECT: type
BUILTIN_STR: Type[str]
long_words: Dict[str, str]

class Data:
    _last_travel_first: int
    _last_travel_second: List[int]
    _object: Object
    class_messages: List[Tuple[int, str]]
    hints: Dict[int, Hint]
    magic_messages: Dict[int, str]
    messages: Dict[int, Message]
    objects: Dict[int, Object]
    rooms: Dict[int, Room]
    vocabulary: Dict[int, Word]
    def __init__(self) -> None: ...
    def referent(self, word) -> None: ...

class HasN:
    n: int
    def __init__(self) -> None: ...

class Hint(HasN):
    __doc__: str
    message: Message
    n: int
    penalty: int
    question: Message
    rooms: List[Room]
    turn_counter: int
    turns_needed: int
    used: bool
    def __init__(self) -> None: ...

class Message(HasN):
    __doc__: str
    n: int
    text: str
    def __init__(self) -> None: ...
    def __str__(self) -> str: ...

class Move(HasN):
    __doc__: str
    action: Union[Message, Room, int]
    condition: str
    is_forced: bool
    n: int
    synonyms: List[Word]
    text: str
    verbs: List[Word]
    def __eq__(self, text) -> bool: ...
    def __init__(self) -> None: ...
    def __repr__(self) -> str: ...

class Object(HasN):
    __doc__: str
    contents: Any
    inventory_message: str
    is_fixed: bool
    is_toting: bool
    is_treasure: bool
    messages: Dict[int, str]
    n: int
    names: List[str]
    prop: int
    rooms: List[Room]
    starting_rooms: List[Room]
    def __eq__(self, other) -> bool: ...
    def __hash__(self) -> int: ...
    def __init__(self) -> None: ...
    def __repr__(self) -> str: ...
    def carry(self) -> None: ...
    def destroy(self) -> None: ...
    def drop(self, room) -> None: ...
    def hide(self) -> None: ...
    def is_at(self, room) -> bool: ...

class Room(HasN):
    __doc__: str
    at_witts_end: bool
    is_aboveground: Annotated[Any, 'property']
    is_after_hall_of_mists: Annotated[Any, 'property']
    is_before_hall_of_mists: Annotated[Any, 'property']
    is_dark: Annotated[bool, 'property']
    is_forbidden_to_pirate: bool
    is_forced: Annotated[Any, 'property']
    is_light: bool
    liquid: Any
    long_description: str
    lost_in_maze: bool
    n: int
    pondering_dark_room: bool
    short_description: str
    times_described: int
    travel_table: List[Move]
    trying_to_catch_bird: bool
    trying_to_deal_with_snake: bool
    trying_to_get_into_cave: bool
    visited: bool
    def __init__(self) -> None: ...
    def __repr__(self) -> str: ...

class Word(HasN):
    __doc__: str
    default_message: Message
    kind: str
    n: int
    synonyms: List[Word]
    text: str
    def __eq__(self, text) -> bool: ...
    def __init__(self) -> None: ...
    def __repr__(self) -> str: ...
    def add_synonym(self, other) -> None: ...

def accumulate_message(dictionary, n, line) -> None: ...
def expand_tabs(segments) -> Any: ...
def make_object(dictionary, klass, n) -> Any: ...
def section1(data, n, etc) -> None: ...
def section10(data, score, line) -> None: ...
def section11(data, n, turns_needed, penalty, question_n, message_n) -> None: ...
def section12(data, n, line) -> None: ...
def section2(data, n, line) -> None: ...
def section3(data, x, y, verbs) -> None: ...
def section4(data, n, text) -> None: ...
def section5(data, n, etc) -> None: ...
def section6(data, n, etc) -> None: ...
def section7(data, n, room_n, etc) -> None: ...
def section8(data, word_n, message_n) -> None: ...
def section9(data, bit, nlist) -> None: ...
