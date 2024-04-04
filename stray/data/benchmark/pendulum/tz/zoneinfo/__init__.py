from .reader import Reader
from .timezone import Timezone


def read(name, extend=True):  
    """
    Read the zoneinfo structure for a given timezone name.
    """
    return Reader(extend=extend).read_for(name)


def read_file(path, extend=True):  
    """
    Read the zoneinfo structure for a given path.
    """
    return Reader(extend=extend).read1(path)
