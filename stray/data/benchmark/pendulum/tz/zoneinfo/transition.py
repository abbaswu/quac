from datetime import timedelta
from typing import Optional

from .transition_type import TransitionType


class Transition:
    _at:int
    _ttype:TransitionType
    _previous:'Transition'
    _local:int
    _fix:int
    _to:int
    _to_utc:int
    _utcoffset:timedelta
    def __init__(
        self,
        at,  
        ttype,  
        previous,  
    ):
        self._at = at

        if previous:
            self._local = at + previous._ttype.offset()
        else:
            self._local = at + ttype.offset()


        self._previous = previous

        if self._previous:
            self._fix = self._ttype.offset() - self._previous._ttype.offset()
        else:
            self._fix = 0

        self._to = self._local + self._fix
        self._to_utc = self._at + self._fix
        self._utcoffset = timedelta(seconds=ttype.offset())


    def at(self):  
        return self._at


    def local(self):  
        return self._local


    def to(self):  
        return self._to


    def to_utc(self):  
        return self._to


    def ttype(self):  
        return self._ttype


    def previous(self):  
        return self._previous


    def fix(self):  
        return self._fix

    def is_ambiguous(self, stamp):  
        return self._to <= stamp < self._local

    def is_missing(self, stamp):  
        return self._local <= stamp < self._to

    def utcoffset(self):  
        return self._utcoffset

    def __contains__(self, stamp):  
        if self.previous() is None:
            return stamp < self.local()

        return self.previous().local() <= stamp < self.local()

    def __repr__(self):  
        return "Transition({} -> {}, {})".format(self._local, self._to, self._ttype)

