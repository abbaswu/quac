
class ISD_AS():
    """
    Class for representing isd-as pair.
    """
    _isd:int
    _as:int


    @staticmethod
    def f():
        inst = ISD_AS()
        return inst

    def g(self):
        return ISD_AS.f()
    # def int(self):
    #     isd_as = self._isd << 20
    #     isd_as |= self._as & 0x000fffff
    #     return isd_as