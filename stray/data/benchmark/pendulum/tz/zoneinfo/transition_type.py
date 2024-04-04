from datetime import timedelta

from data.benchmark.pendulum.utils._compat import PY2
from data.benchmark.pendulum.utils._compat import encode


class TransitionType:

    _offset:int
    _is_dst:bool
    _abbr:str
    _utcoffset:timedelta
    def __init__(self, offset, is_dst, abbr):
        self._offset = offset
        self._is_dst = is_dst
        self._abbr = abbr

        self._utcoffset = timedelta(seconds=offset)


    def offset(self):  
        return self._offset


    def abbreviation(self):  
        if PY2:
            return encode(self._abbr)

        return self._abbr

    def is_dst(self):  
        return self._is_dst

    def utcoffset(self):  
        return self._utcoffset

    def __repr__(self):  
        return "TransitionType({}, {}, {})".format(
            self._offset, self._is_dst, self._abbr
        )
