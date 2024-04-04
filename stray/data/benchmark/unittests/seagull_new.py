# -*- coding: utf-8 -*-

"""Rules determine how the evolution of the lifeforms will progress. In
Seagull, rules are implemented as a function that takes in a 2-dimensional
array of a given shape then returns the updated array with the rule applied"""
import abc
# Import standard library
import re
from typing import Any, Tuple, List

# Import modules
import numpy as np
from numpy import ndarray
# from scipy.signal import convolve2d
import scipy
from loguru import logger
from typing import Tuple

# Import modules
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.figure import Figure
from matplotlib.image import AxesImage
from loguru import logger

# Import from package

from typing import Callable, Union

# Import modules
import matplotlib.pyplot as plt
import numpy as np
from loguru import logger
from matplotlib import animation

from os.path import isfile
import re
from typing import Dict, List, Union
from urllib.parse import urlparse
from urllib.request import urlopen

# Import modules
import numpy as np
from loguru import logger



def cell_coverage(state): # div可解
    """Compute for the live cell coverage for the whole board

    """
    return np.sum(state) / np.product(state.shape)

def convolve2d(in1:np.ndarray, in2:np.ndarray, mode:str='full', boundary:str='fill', fillvalue:int=0)->np.ndarray:
    pass
def _count_neighbors(X):
    """Get the number of neighbors in a binary 2-dimensional matrix"""
    n = convolve2d(X, np.ones((3, 3)), mode="same", boundary="wrap") - X
    return n
def _parse_rulestring(r):
    """Parse a rulestring"""
    pattern = re.compile("B([0-8]+)?/S([0-8]+)?")
    if pattern.match(r):
        birth, survival = r.split("/")
        birth_neighbors = [int(s) for s in birth if s.isdigit()]
        survival_neighbors = [int(s) for s in survival if s.isdigit()]
    else:
        msg = f"Rulestring ({r}) must satisfy the pattern {pattern}"
        logger.error(msg)
        raise ValueError(msg)

    return birth_neighbors, survival_neighbors



def life_rule(X, rulestring):
    """A generalized life rule that accepts a rulestring in B/S notation

    Rulestrings are commonly expressed in the B/S notation where B (birth) is a
    list of all numbers of live neighbors that cause a dead cell to come alive,
    and S (survival) is a list of all the numbers of live neighbors that cause
    a live cell to remain alive.
    """
    birth_req, survival_req = _parse_rulestring(rulestring)
    neighbors = _count_neighbors(X)
    birth_rule = (X == 0) & (np.isin(neighbors, birth_req))
    survival_rule = (X == 1) & (np.isin(neighbors, survival_req))
    return birth_rule | survival_rule
def conway_classic(X):
    """The classic Conway's Rule for Game of Life (B3/S23)"""
    return life_rule(X, rulestring="B3/S23")




def shannon_entropy(state): # 无解 rsub
    """Compute for the shannon entropy for the whole board

    """
    zero_probs = np.count_nonzero(state) / np.product(state.shape)
    one_probs = 1 - zero_probs
    return -np.sum(np.log2([zero_probs, one_probs]))





def parse_plaintext_layout(plaintext_str):
    """Parse plaintext_str in Plaintext format into ndarray layout

    typical plaintext_str format:
    '''
    .O.O
    O.O
    O
    ......O
    '''


    """
    if isinstance(plaintext_str, list):
        # already line-split
        lines = plaintext_str
    else:
        # split lines, ignore comments
        lines = plaintext_str.strip().replace("\r\n", "\n").split("\n")
        lines = [line for line in lines if not line.startswith("!")]

    # check if only '.' and 'O' are present
    if set("".join(lines)) != {".", "O"}:
        raise ValueError("Invalid input cells_str : use only '.' and 'O'")

    layout = [[1 if c == "O" else 0 for c in line] for line in lines]

    max_width = max(len(line) for line in layout)
    # add zeroes so that all lines are of equal length
    [line.extend([0] * (max_width - len(line))) for line in layout]

    return np.array(layout)

# 异构container # Edit: dict
def _get_metadata(lines:List[str])->Dict[str, str]:
    """Parse meta-data stored in the comments of .cells file

    """
    meta = {"comments": []}
    for line in lines:
        if line.startswith("!"):
            # parsing commented lines
            # @TODO: prettify? or delete this todo
            if line.startswith("!Name: "):
                meta["name"] = line[len("!Name: ") :]
            elif line.startswith("!Author: "):
                meta["author"] = line[len("!Author: ") :]
            else:
                meta["comments"].append(line[1:])
        elif line.startswith("#"):
            # parsing commented lines
            # @TODO: prettify? or delete this todo
            if line.startswith("#N "):
                meta["name"] = line[len("#N ") :]
            elif line.startswith("#O "):
                meta["author"] = line[len("#O ") :]
            elif line.startswith(("#R ", "#P ", "#r ")):
                # @TODO: decide whether add R, P, r parsing?
                raise NotImplementedError("#R, #r , #P tags not implemented")
            else:
                meta["comments"].append(
                    line[3:]
                )  # 3: for proper "#C <comment>" format
        else:
            # not a comment line
            pass

    # meta["comments"] = "\n".join(meta["comments"])

    return meta




class Board:
    """Represents the environment where the lifeforms can grow and evolve"""
    size:Tuple[int, int]
    state:np.ndarray
    
    def __init__(self, size=(100, 100)):
        """Initialize the class


        """
        self.size = size
        self.state = np.zeros(size, dtype=bool)

    def add(self, lifeform, loc):
        """Add a lifeform to the board

        """
        try:
            row, col = loc
            height, width = lifeform.size()
            self.state[row : row + height, col : col + width] = lifeform.layout()
        except ValueError:
            logger.error("Lifeform is out-of-bounds!")
            raise

    def clear(self):
        """Clear the board and remove all lifeforms"""
        logger.debug("Board cleared!")
        self.state = np.zeros(self.size, dtype=bool)

    def view(self, figsize=(5, 5)):
        """View the current state of the board

        """
        fig = plt.figure(figsize=figsize)
        ax = fig.add_axes([0, 0, 1, 1], xticks=[], yticks=[], frameon=False)
        im = ax.imshow(self.state, cmap=plt.cm.binary, interpolation="nearest")
        im.set_clim(-0.05, 1)
        return fig, im


class Simulator:
    board:Board
    history:List[np.ndarray]
    stats:Dict[str,np.ndarray]
    def __init__(self, board):
        """Initialize the class

        """
        self.board = board
        self.history = []  # type: list
        self.stats = {}  # type: dict

    def run(self, rule, iters, **kwargs):
        layout = self.board.state.copy()

        # Append the initial state
        self.history.append(layout)

        # Run simulation
        for i in range(iters):
            layout = rule(layout, **kwargs)
            self.history.append(layout)

        self.stats = self.compute_statistics(self.get_history())
        return self.stats

    def compute_statistics(self, history):
        logger.info("Computing simulation statistics...")
        sim_stats = {
            "peak_cell_coverage": np.max(
                [cell_coverage(h) for h in history]
            ),
            "avg_cell_coverage": np.mean(
                [cell_coverage(h) for h in history]
            ),
            "avg_shannon_entropy": np.mean(
                [shannon_entropy(h) for h in history]
            ),
            "peak_shannon_entropy": np.max(
                [shannon_entropy(h) for h in history]
            ),
        }

        return sim_stats

    def get_history(self, exclude_init=False):

        history = self.history[1:] if exclude_init else self.history
        return np.asarray(history)

    def animate(self, figsize=(5, 5), interval=100)->Any: # Edit: nested
        """Animate the resulting simulation

        """
        if not self.history:
            msg = "The run() argument must be executed first"
            logger.error(msg)
            raise ValueError(msg)

        logger.info("Rendering animation...")
        fig = plt.figure(figsize=figsize)
        ax = fig.add_axes([0, 0, 1, 1], xticks=[], yticks=[], frameon=False)
        X_blank = np.zeros(self.board.size, dtype=bool)
        im = ax.imshow(X_blank, cmap=plt.cm.binary, interpolation="nearest")
        im.set_clim(-0.05, 1)

        def _animate(i, history):
            current_pos = history[i]
            im.set_data(current_pos)
            return (im,)

        def _init():
            im.set_data(X_blank)
            return (im,)

        history = self.get_history()
        anim = animation.FuncAnimation(
            fig,
            func=_animate,
            frames=range(history.shape[0]),
            init_func=_init,
            interval=interval,
            fargs=(history,),
            blit=True,
        )
        return anim

class Lifeform(abc.ABC):
    """Base class for all Lifeform implementation"""

    def layout(self)->np.ndarray: # Edit abc
        """:obj:`numpy.ndarray`: Lifeform layout or structure"""
        pass

    
    def size(self):
        """:obj:`tuple`: Size of the lifeform"""
        return self.layout().shape

    def view(self, figsize=(5, 5)):
        """View the lifeform

        """
        fig = plt.figure(figsize=figsize)
        ax = fig.add_axes([0, 0, 1, 1], xticks=[], yticks=[], frameon=False)
        im = ax.imshow(
            self.layout(), cmap=plt.cm.binary, interpolation="nearest"
        )
        im.set_clim(-0.05, 1)
        return fig


class Custom(Lifeform):
    """Create custom lifeforms"""
    X:np.ndarray
    meta:Dict[str,str]
    def __init__(self, X):
        """Initialize the class
        """
        self.validate_input_values(np.array(X))
        self.validate_input_shapes(np.array(X))
        self.X = X

    def validate_input_values(self, X): #s##
        """Check if all elements are binary"""
        if not ((X == 0) | (X == 1) | (X is True) | (X is False)).all():
            msg = "Input array should only contain {0,1} or {True,False}"
            logger.error(msg)
            raise ValueError(msg)

    def validate_input_shapes(self, X):
        """Check if input array is of size 2"""
        if X.ndim() != 2:
            msg = (
                "Input array should have 2 dimensions: {} != 2. "
                "For a 1-d lifeform, please add a new axis".format(X.ndim())
            )
            logger.error(msg)
            raise ValueError(msg)

    
    def layout(self):
        return np.array(self.X)


class Glider(Lifeform):
    def __init__(self):
        """Initialize the class"""
        super(Glider, self).__init__()

    
    def layout(self):
        return np.array([[1, 0, 0], [0, 1, 1], [1, 1, 0]])


class LightweightSpaceship(Lifeform):
    def __init__(self):
        super(LightweightSpaceship, self).__init__()

    
    def layout(self):
        return np.array(
            [
                [0, 1, 0, 0, 1],
                [1, 0, 0, 0, 0],
                [1, 0, 0, 0, 1],
                [1, 1, 1, 1, 0],
            ]
        )


class MiddleweightSpaceship(Lifeform):
    def __init__(self):
        super(MiddleweightSpaceship, self).__init__()

    
    def layout(self):
        return np.array(
            [
                [0, 0, 0, 1, 0, 0],
                [0, 1, 0, 0, 0, 1],
                [1, 0, 0, 0, 0, 0],
                [1, 0, 0, 0, 0, 1],
                [1, 1, 1, 1, 1, 0],
            ]
        )





class Unbounded(Lifeform):
    """A lifeform with asymptotically unbounded growth"""

    def __init__(self):
        """Initialize the class"""
        super(Unbounded, self).__init__()

    
    def layout(self):
        return np.array(
            [
                [1, 1, 1, 0, 1],
                [1, 0, 0, 0, 0],
                [0, 0, 0, 1, 1],
                [0, 1, 1, 0, 1],
                [1, 0, 1, 0, 1],
            ]
        )


class Century(Lifeform):
    """A Century Methuselah lifeform"""
    
    def ___init___(self):
        """Initialize the class"""
        super(Century, self).__init__()
        
    
    def layout(self): ###
        X = np.zeros((3,4))
        X[0,2:] = 1
        X[1,:3] = 1
        X[2,1] = 1
        return X

class Thunderbird(Lifeform):
    """A Thunderbird Methuselah lifeform"""
    
    def ___init___(self):
        """Initialize the class"""
        super(Thunderbird, self).__init__()
        
    
    def layout(self):
        X = np.zeros((5,3))
        X[0,:] = 1
        X[2:,1] = 1
        return X



class Blinker(Lifeform):
    """A horizontal Blinker lifeform"""
    length:int
    def __init__(self, length=3):
        """Initialize the class

        """
        super(Blinker, self).__init__()
        self.length = length

    
    def layout(self) :
        return np.ones(shape=(self.length, 1), dtype=int)


class Toad(Lifeform):
    """A Toad lifeform oscillator"""

    def __init__(self):
        """Initialize the class"""
        super(Toad, self).__init__()

    
    def layout(self) :
        return np.array([[1, 1, 1, 0], [0, 1, 1, 1]])


class Pulsar(Lifeform):
    """A Pulsar lifeform oscillator"""

    def __init__(self):
        """Initialize the class"""
        super(Pulsar, self).__init__()

    
    def layout(self) : ##
        X = np.zeros((17, 17))
        X[2, 4:7] = 1
        X[4:7, 7] = 1
        X += X.T
        X += X[:, ::-1]
        X += X[::-1, :]
        return X


class FigureEight(Lifeform):
    """A Figure eight lifeform oscillator"""

    def __init__(self):
        """Initialize the class"""
        super(FigureEight, self).__init__()

    
    def layout(self) : ##
        X = np.zeros((6, 6))
        X[0:3, 0:3] = 1
        X[3:6, 3:6] = 1
        return X


class Beacon(Lifeform):
    """A Beacon lifeform oscillator"""

    def __init__(self):
        """Initialize the class"""
        super(Beacon, self).__init__()

    
    def layout(self) : ##
        X = np.zeros((4, 4))
        X[0:2, 0:2] = 1
        X[2:4, 2:4] = 1
        return X


class Pentadecathlon(Lifeform):
    """ A Pentadecathlon lifeform oscillator"""

    def __init__(self):
        """Initialize the class"""
        super(Pentadecathlon, self).__init__()

    
    def layout(self) :
        X = np.ones(shape=(8, 3), dtype=int)
        X[1, 1] = 0
        X[6, 1] = 0
        return X


class ChaCha(Lifeform):
    """A Cha Cha lifeform oscillator"""
    
    def ___init___(self):
        """Initialize the class"""
        super(ChaCha, self).__init__()
        
    
    def layout(self) :
        X = np.zeros((6,8))
        X[0,4] = 1
        X[1,2::2] = 1
        X[2,::2] = 1
        X += np.rot90(X, 2)  ###
        return X


class RandomBox(Lifeform):
    """A random box with arbitrarily-set shape"""
    shape:Tuple[int,int]
    seed:int
    def __init__(self, shape=(3, 3), seed=None):
        """Initialize the class

        """
        super(RandomBox, self).__init__()
        self.shape = shape
        self.seed = seed

    
    def layout(self) :
        np.random.seed(self.seed)
        return np.random.choice([0, 1], size=self.shape)



class Box(Lifeform):
    """A static Box"""

    def __init__(self):
        """Initialize the class"""
        super(Box, self).__init__()

    
    def layout(self) :
        return np.ones(shape=(2, 2), dtype=int)


class Seed(Lifeform):
    """A static Seed"""

    def __init__(self):
        """Initialize the class"""
        super(Seed, self).__init__()

    
    def layout(self) :
        return np.array([[0, 1, 1, 0], [1, 0, 0, 1], [0, 1, 1, 0]])


class Moon(Lifeform):
    """A static Moon"""

    def __init__(self):
        """Initialize the class"""
        super(Moon, self).__init__()

    
    def layout(self) :
        return np.array(
            [[0, 1, 1, 0], [1, 0, 0, 1], [0, 1, 0, 1], [0, 0, 1, 0]]
        )


class Kite(Lifeform):
    """A static Kite"""

    def __init__(self):
        """Initialize the class"""
        super(Kite, self).__init__()

    
    def layout(self) :
        return np.array([[1, 1, 0], [1, 0, 1], [0, 1, 0]])


class Eater1(Lifeform):
    """A static Eater"""

    def __init__(self):
        """Initialize the class"""
        super(Eater1, self).__init__()

    
    def layout(self) :
        return np.array(
            [[1, 1, 0, 0], [1, 0, 1, 0], [0, 0, 1, 0], [0, 0, 1, 1]]
        )


class SwitchEngine(Lifeform):
    """A static Eater"""

    def __init__(self):
        """Initialize the class"""
        super(SwitchEngine, self).__init__()

    
    def layout(self) :
        return np.array(
            [
                [0, 1, 0, 1, 0, 0],
                [1, 0, 0, 0, 0, 0],
                [0, 1, 0, 0, 1, 0],
                [0, 0, 0, 1, 1, 1],
            ]
        )

def _load_file_of_url(path):
    """Detects if path is local or URL, loads file content

    """
    if isfile(path):
        logger.trace(f"reading from file [{path}]..", end="")
        with open(path, "r") as f:
            content = f.read()
        logger.trace("ok")
    elif urlparse(path).scheme in {"ftp", "http", "https"}:
        logger.trace(f"trying to download [{path}]..", end="")
        req = urlopen(path)
        if req.getcode() != 200:
            raise ValueError(
                f"Invalid input URL request returned {req.getcode()}"
            )
        logger.trace("ok")
        content = req.read().decode("utf-8")
    else:
        raise ValueError(f"Unrecognized input path {path}")

    return content


def parse_cells(cells_str):
    """Parse cell_str, stored in Plaintext format, into Lifeform
    
    Plaintext format description: https://conwaylife.com/wiki/Plaintext

    Usage
    -----
    You can enter a string directly into the function: 

    G = parse_cells(
        '''!Name: name of the Lifeform
! some comment
.O
..O
OOO
'''
        )
    # . (dot) for empty cell, O (capital O) for alive cell, no trailing .s

    Or you can parse cells immediately from Conway Life's website:

    G = parse_cells('http://www.conwaylife.com/patterns/glider.cells')
    


    """
    if not cells_str.startswith((".", "0", "!")):
        # not a proper .cells line, filename/URL?
        cells_str = _load_file_of_url(cells_str)

    # split lines, \r if (down)loaded and not copy-pasted
    lines = cells_str.strip().replace("\r\n", "\n").split("\n")

    metadata_lines = [l for l in lines if l.startswith("!")]
    layout_lines = [l for l in lines if not l.startswith("!")]

    layout = parse_plaintext_layout(layout_lines)

    lifeform = Custom(layout)  # to be returned

    # Setting custom fields parsed from comments
    lifeform.meta = _get_metadata(metadata_lines)

    return lifeform


def cells2rle(cells_str):
    """Convert plaintext coded lifeform into RLE, ignore comments

    Does not add "!" at the end, converts only commands
        (idea behind this is that it insures that you know what you're doing)

    """
    if isinstance(cells_str, str):
        cells_str = cells_str.replace("\r\n", "\n").split("\n")

    cells_str = "\n".join(l for l in cells_str if not l.startswith("!"))
    blocks = re.findall("(\n+|\\.+|O+)", cells_str)
    parse_dict = {"\n": "$", ".": "b", "O": "o"}
    blocks = [
        (str(len(b)) if len(b) > 1 else "") + parse_dict[b[0]] for b in blocks
    ]

    return "".join(blocks)


def rle2cells(rle_str):
    """Convert lifeform string in RLE encoding to PlainText

    """
    # drop the last part
    if "!" in rle_str:
        rle_str = rle_str[: rle_str.index("!")]
    else:
        raise ValueError('Incorrect input: no "!"')

    if not set(rle_str).issubset("0123456789bo$"):
        raise ValueError("Incorrect input: wrong character set")

    commands = re.findall("([0-9]*)(b|o|\\$)", rle_str)
    if len(commands) == 0:
        raise ValueError("Incorrect input: wrong pattern format")

    layout_string = ""
    parse_dict = {"b": ".", "o": "O", "$": "\n"}
    for com in commands:
        n = int(com[0]) if com[0] else 1
        layout_string += parse_dict[com[1]] * n

    return layout_string


def parse_rle(rle_str):
    """Parse rle_str, stored in RLE format, into Lifeform
    
    RLE format description: https://www.conwaylife.com/wiki/Run_Length_Encoded

    Usage
    -----
    You can enter a string directly into the function: 

    G = parse_rle(
        '''#N Gosper glider gun
#O Bill Gosper
#C A true period 30 glider gun.
#C The first known gun and the first known finite pattern with unbounded growth.
#C www.conwaylife.com/wiki/index.php?title=Gosper_glider_gun
x = 36, y = 9, rule = B3/S23
24bo11b$22bobo11b$12b2o6b2o12b2o$11bo3bo4b2o12b2o$2o8bo5bo3b2o14b$2o8b
o3bob2o4bobo11b$10bo5bo7bo11b$11bo3bo20b$12b2o!
'''
        )
    
    Or you can parse rle files immediately from Conway Life's website:

    G = parse_rle('http://www.conwaylife.com/patterns/gosperglidergun.rle')



    Notes
    -----
        - RLE content after `!` is ignored    
        - header line is currently parsed but not used
    """
    if not rle_str.startswith(("#", "x")):
        # not a proper .cells line, filename/URL?
        rle_str = _load_file_of_url(rle_str)

    # split lines, \r if (down)loaded and not copy-pasted
    lines = rle_str.strip().replace("\r\n", "\n").split("\n")

    metadata_lines = [l for l in lines if l.startswith("#")]
    layout_lines = [l for l in lines if not l.startswith("#")]

    # Parse size and rule, if present
    header_line = layout_lines[0]
    header_match = re.match(
        r"x = ([0-9]+), y = ([0-9]+)(, rule = ([^ ]+))?", header_line
    )
    if header_match is None:
        raise ValueError(
            f"Incorrect input: wrong header line format : [{header_line}]"
        )
    header_match = header_match.groups()

    width = int(header_match[0])
    height = int(header_match[1])

    if header_match[3] is None:
        # use default rulestring
        rulestring = "B3/S23"
    else:
        rulestring = header_match[3]

    # Parse layout, converting it to plaintext
    layout_string = "".join(layout_lines[1:])
    layout_string = rle2cells(layout_string)
    layout = parse_plaintext_layout(layout_string)

    if layout.shape != (height, width):
        raise ValueError(
            "Parsed layout width/height inconsistent with header"
            f": header: {width} {height} , layout: {layout.shape}"
        )

    lifeform = Custom(layout)  # to be returned

    # Setting custom fields parsed from comments
    lifeform.meta = _get_metadata(metadata_lines)

    return lifeform
