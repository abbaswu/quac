from typing import Dict, List, Tuple, Union, Any
long_words = { w[:5]: w for w in """upstream downstream forest
forward continue onward return retreat valley staircase outside building stream
cobble inward inside surface nowhere passage tunnel canyon awkward
upward ascend downward descend outdoors barren across debris broken
examine describe slabroom depression entrance secret bedquilt plover
oriental cavern reservoir office headlamp lantern pillow velvet fissure tablet
oyster magazine spelunker dwarves knives rations bottle mirror beanstalk
stalactite shadow figure drawings pirate dragon message volcano geyser
machine vending batteries carpet nuggets diamonds silver jewelry treasure
trident shards pottery emerald platinum pyramid pearl persian spices capture
release discard mumble unlock nothing extinguish placate travel proceed
continue explore follow attack strike devour inventory detonate ignite
blowup peruse shatter disturb suspend sesame opensesame abracadabra
shazam excavate information""".split() }

class HasN:
    n:int
    def __init__(self):
        self.n:int = 0
class Move(HasN):
    """An entry in the travel table."""

    n:int = 0
    is_forced:bool = False
    verbs:List['Word'] = []
    condition:str = None
    action:Union['Room', 'Message', int] = None
    text:str
    synonyms:List['Word']

    def __repr__(self):
        verblist = [ verb.text for verb in self.verbs ]

        c = self.condition[0]
        condition = ''
        if c == '%':
            condition = ' %d%% of the time' % self.condition[1]
        elif c == 'not_dwarf':
            condition = ' if not a dwarf'
        elif c == 'carrying':
            condition = ' if carrying %s' % self.condition[1]
        elif c == 'carrying_or_in_room_with':
            condition = ' if carrying or in room with %s' % self.condition[1]
        elif c == 'prop!=':
            condition = ' if prop %d != %d' % self.condition[1:]

        if isinstance(self.action, Room):
            action = 'moves to %r' % (self.action.short_description or self.action.long_description[:20]).strip()
        elif isinstance(self.action, Message):
            action = 'prints %r' % self.action.text
        else:
            action = 'special %d' % self.action

        return '<{}{} {}>'.format('|'.join(verblist), condition, action)


class Room(HasN):
    """A location in the game."""
    travel_table:List['Move'] = []
    n:int
    long_description:str = ''
    short_description:str = ''
    times_described:int = 0
    visited:bool = False

    is_light:bool = False
    is_forbidden_to_pirate:bool = False
    liquid:Any = None
    trying_to_get_into_cave:bool = False
    trying_to_catch_bird:bool = False
    trying_to_deal_with_snake:bool = False
    lost_in_maze:bool = False
    pondering_dark_room:bool = False
    at_witts_end:bool = False
    def __init__(self):
        self.travel_table = []
        self.n = 0
        self.long_description = ''
        self.short_description = ''
        self.times_described = 0
        self.visited = False

        self.is_light = False
        self.is_forbidden_to_pirate = False
        self.liquid = None
        self.trying_to_get_into_cave = False
        self.trying_to_catch_bird = False
        self.trying_to_deal_with_snake = False
        self.lost_in_maze = False
        self.pondering_dark_room = False
        self.at_witts_end = False

    def __repr__(self):
        return '<room {} at {}>'.format(self.n, hex(id(self)))
    # Edit: property
    # @property
    def is_forced(self):
        return self.travel_table and self.travel_table[0].is_forced

    # @property
    def is_aboveground(self):
        return 1 <= self.n <= 8

    # @property
    def is_before_hall_of_mists(self):
        return self.n < 15

    # @property
    def is_after_hall_of_mists(self):
        return self.n >= 15

    # @property
    def is_dark(self):
        return not self.is_light

class Word(HasN):
    """A word that can be used as part of a command."""
    synonyms:List['Word']
    n:int
    text:str
    kind:str 
    default_message:'Message'

    def __init__(self):
        self.synonyms = [ self ]
        self.n = 0
    
    def __repr__(self):
        return '<Word {}>'.format(self.text)

    def __eq__(self, text):
        return any( [word.text == text for word in self.synonyms] )
    
    # need word as type seeds
    def add_synonym(self, other):
        """Every word in a group of synonyms shares the same list."""
        self.synonyms.extend(other.synonyms)
        other.synonyms = self.synonyms
    

class Object(HasN):
    """An object in the game, like a grate, or a rod with a rusty star."""
    is_fixed:bool = False
    is_treasure:bool
    inventory_message:str = ''
    messages:Dict[int,str] = {}
    names:List[str] = []
    prop:int = 0
    rooms:List[Room] = []
    starting_rooms:List[Room] = []
    is_toting:bool = False
    contents:Any = None  # so the bottle can hold things
    n:int = 0

    def __init__(self):
        self.is_fixed = False
        self.is_treasure = False
        self.inventory_message = ''
        self.messages = {}
        self.names = []
        self.prop = 0
        self.rooms = []
        self.starting_rooms = []
        self.is_toting = False
        self.contents = None  # so the bottle can hold things
        self.n = 0

    def __repr__(self):
        return '<Object %d %s %x>' % (self.n, '/'.join(self.names), id(self))

    def __hash__(self):
        return self.n

    def __eq__(self, other):
        return any([text == other for text in self.names])

    def is_at(self, room):
        return room in self.rooms

    def carry(self):
        self.rooms[:] = []
        self.is_toting = True
    # need room in type seeds
    def drop(self, room):
        self.rooms[:] = [ room ]
        self.is_toting = False

    def hide(self):
        self.rooms[:] = []
        self.is_toting = False

    def destroy(self):
        self.hide()

class Message(HasN):
    """A message for printing."""
    n:int = 0
    text:str = ''

    def __str__(self):
        return self.text


class Hint(HasN):
    """A hint offered if the player loiters in one area too long."""

    rooms:List[Room] = []
    n:int = 0
    turns_needed:int = 0
    turn_counter:int = 0
    penalty:int = 0
    question:Message = None
    message:Message = None
    used:bool = False

    def __init__(self):
        self.rooms = []
        self.n = 0
        self.turns_needed = 0
        self.turn_counter = 0
        self.penalty = 0
        self.question = None
        self.message = None
        self.used = False

class Dwarf:
    is_dwarf:bool = True
    is_pirate:bool = False
    room:Room
    old_room:Room
    move:Move
    def __init__(self, room):
        self.start_at(room)
        self.has_seen_adventurer = False

    def start_at(self, room):
        self.room = room
        self.old_room = room

    def can_move(self, move):
        if isinstance(move.action, Room):
            room = move.action
            return (room.is_after_hall_of_mists()
                    and not room.is_forced()
                    and not move.condition == ('%', 100))
        else:
            return False

class Pirate(Dwarf):
    is_dwarf:bool = False
    is_pirate:bool = True


class Data(object):
    rooms:Dict[int, Room] = {}
    vocabulary:Dict[int, Word] = {}
    objects:Dict[int,Object] = {}
    messages:Dict[int, Message] = {}
    class_messages:List[Tuple[int,str]] = []
    hints:Dict[int,Hint] = {}
    magic_messages:Dict[int, str] = {}
    _last_travel_first:int = 0
    _last_travel_second:List[int] = []
    _object:Object = None
    def __init__(self):
        self.rooms = {}
        self.vocabulary = {}
        self.objects = {}
        self.messages = {}
        self.class_messages = []
        self.hints = {}
        self.magic_messages = {}
        self._last_travel_first = 0
        self._last_travel_second = []
        self._object = None

    def referent(self, word):
        if word.kind == 'noun':
            return self.objects[word.n % 1000]
def make_object(dictionary, klass, n):
    if n not in dictionary:
        dictionary[n] = obj = klass()
        obj.n = n
    return dictionary[n]

def expand_tabs(segments):
    it = iter(segments)
    line = next(it)
    for segment in list(it):
        spaces = 8 - len(line) % 8
        line = line + ' ' * spaces + segment
    return line


def accumulate_message(dictionary, n, line):
    dictionary[n] = dictionary.get(n, '') + line + '\n'

def section1(data, n, etc):
    room = make_object(data.rooms, Room, n)
    if not etc[0].startswith('>$<'):
        room.long_description += expand_tabs(etc) + '\n'


def section2(data, n, line):
    make_object(data.rooms, Room, n).short_description += line + '\n'

def section3(data, x, y, verbs):
    last_travel_first = data._last_travel_first
    last_travel_second = data._last_travel_second
    if last_travel_first == x and last_travel_second[0] == verbs[0]:
        verbs = last_travel_second  # same first verb implies use whole list
    else:
        data._last_travel_first = x
        data._last_travel_second = verbs

    m, n = divmod(y, 1000)
    mh, mm = divmod(m, 100)

    condition = (None, None, None)
    if m == 0:
        condition = (None, None, None)
    elif 0 < m < 100:
        condition = ('%', m, None)
    elif m == 100:
        condition = ('not_dwarf', None, None)
    elif 100 < m <= 200:
        condition = ('carrying', mm, None)
    elif 200 < m <= 300:
        condition = ('carrying_or_in_room_with', mm, None)
    elif 300 < m:
        condition = ('prop!=', mm, mh - 3)

    if n <= 300:
        action = make_object(data.rooms, Room, n)
    elif 300 < n <= 500:
        action = n  # special computed goto
    else:
        action = make_object(data.rooms, Room, n - 500)

    move = Move()
    if len(verbs) == 1 and verbs[0] == 1:
        move.is_forced = True
    else:
        move.verbs = [ make_object(data.vocabulary, Word, verb_n)
                       for verb_n in verbs if verb_n < 100 ] # skip bad "109"
    move.condition = condition
    move.action = action
    data.rooms[x].travel_table.append(move)


def section4(data, n, text):
    text = text.lower()
    text = long_words.get(text, text)
    word = make_object(data.vocabulary, Word, n)
    if word.text is None:  # this is the first word with index "n"
        word.text = text
    else:  # there is already a word sitting at "n", so create a synonym
        original = word
        word = Word()
        word.n = n
        word.text = text
        original.add_synonym(word)
    word.kind = ['travel', 'noun', 'verb', 'snappy_comeback'][n // 1000]
    if word.kind == 'noun':
        n %= 1000
        obj = make_object(data.objects, Object, n)
        obj.names.append(text)
        obj.is_treasure = (n >= 50)
        data.objects[n] = obj
    if text not in data.vocabulary:  # since duplicate names exist
        data.vocabulary[n] = word


def section5(data, n, etc):
    if 1 <= n <= 99:
        data._object = make_object(data.objects, Object, n)
        data._object.inventory_message = expand_tabs(etc)
    else:
        n //= 100
        messages = data._object.messages
        if etc[0].startswith('>$<'):
            more = ''
        else:
            more = expand_tabs(etc) + '\n'
        messages[n] = messages.get(n, '') + more

def section6(data, n, etc):
    message = make_object(data.messages, Message, n)
    message.text += expand_tabs(etc) + '\n'


def section7(data, n, room_n, etc):
    if not room_n:
        return
    obj = make_object(data.objects, Object, n)
    room = make_object(data.rooms, Room, room_n)
    obj.drop(room)
    if len(etc):
        if etc[0] == -1:
            obj.is_fixed = True
        else:
            room2 = make_object(data.rooms, Room, etc[0])
            obj.rooms.append(room2)  # exists two places, like grate
    obj.starting_rooms = obj.rooms  # remember where things started


def section8(data, word_n, message_n):
    if not message_n:
        return
    word = make_object(data.vocabulary, Word, word_n + 2000)
    message = make_object(data.messages, Message, message_n)
    for word2 in word.synonyms:
        word2.default_message = message

def section9(data, bit, nlist):
    for n in nlist:
        room = make_object(data.rooms, Room, n)
        if bit == 0:
            room.is_light = True
        elif bit == 1:
            room.liquid = make_object(data.objects, Object, 22) #oil
        elif bit == 2:
            room.liquid = make_object(data.objects, Object, 21) #water
        elif bit == 3:
            room.is_forbidden_to_pirate = True
        else:
            hint = make_object(data.hints, Hint, bit)
            hint.rooms.append(room)

def section10(data, score, line):
    data.class_messages.append((score, line))



def section11(data, n, turns_needed, penalty, question_n, message_n):
    hint = make_object(data.hints, Hint, n)
    hint.turns_needed = turns_needed
    hint.penalty = penalty
    hint.question = make_object(data.messages, Message, question_n)
    hint.message = make_object(data.messages, Message, message_n)

def section12(data, n, line):
    accumulate_message(data.magic_messages, n, line)

BUILTIN_OBJECT = object
BUILTIN_INT = int
BUILTIN_STR = str
CUSTOM_DATA = Data
CUSTOM_HASN = HasN

LIST_BUILTIN_INT = List[int]
LIST_BUILTIN_STR = List[str]
LIST_CUSTOM_DATA = List[Data]
LIST_CUSTOM_HASN = List[HasN]

