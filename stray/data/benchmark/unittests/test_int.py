
class ISD_AS():
    """
    Class for representing isd-as pair.
    """
    _isd:int
    _as:int
    def int(self):
        isd_as = self._isd << 20
        isd_as |= self._as & 0x000fffff
        return isd_as