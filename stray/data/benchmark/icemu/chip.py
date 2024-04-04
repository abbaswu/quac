from abc import ABCMeta
from typing import Dict, List, Any, Set, Union
from itertools import chain
class Pin:
    code:str
    high:bool
    chip:'Chip'
    output:bool
    low_means_enabled:bool
    wires:Set['Pin']
    def __init__(self, code, high=False, chip:Any=None, output=False):
        self.code = code.replace('~', '')
        self.high = high
        self.chip = chip
        self.output = output
        self.low_means_enabled = code.startswith('~')
        self.wires = set()

    def __str__(self):
        return '{}/{}'.format(self.code, 'H' if self.ishigh() else 'L')

    def ishigh(self):
        if not self.output and self.wires:
            wired_outputs = (p for p in self.wires if p.output)
            return any(p.ishigh() for p in wired_outputs)
        else:
            return self.high

    def propagate_to(self):
        if self.output:
            return {
                p.chip for p in self.wires
                if not p.output and p.chip is not self and p.chip is not None
            }
        else:
            return set()

    def set(self, val):
        if val == self.high:
            return

        self.high = val
        if not self.output and self.chip:
            self.chip.update()

        if self.output:
            wired_chips = self.propagate_to()
            for chip in wired_chips:
                chip.update()

    def sethigh(self):
        self.set(True)

    def setlow(self):
        self.set(False)

    def toggle(self):
        self.set(not self.ishigh())

    def enable(self):
        self.set(not self.low_means_enabled)

    def disable(self):
        self.set(self.low_means_enabled)

    def isenabled(self):
        return self.low_means_enabled != self.ishigh()
    def wire_to(self, output_pin):
        assert not self.output
        assert output_pin.output
        self.wires.add(output_pin)
        output_pin.wires.add(self)
        if self.chip:
            self.chip.update()


def pinrange(prefix, start, end):
    # pinrange('Y', 0, 3) -> ['Y0', 'Y1', 'Y2', 'Y3']
    return [prefix + str(i) for i in range(start, end+1)]


class Chip(metaclass=ABCMeta):
    OUTPUT_PINS:List[str]  = []
    INPUT_PINS:List[str]  = []
    STARTING_HIGH:List[str] = [] # pins that start high
    PIN_ORDER:List[str]  = []
    vcc:Pin
    pins:Dict[str, Pin]
    def __init__(self) -> None:
        for code in self.OUTPUT_PINS:
            pin = Pin(code, code in self.STARTING_HIGH, self, True)
            setattr(self, 'pin_{}'.format(pin.code), pin)
        for code in self.INPUT_PINS:
            pin = Pin(code, code in self.STARTING_HIGH, self)
            setattr(self, 'pin_{}'.format(pin.code), pin)
        self.vcc = Pin('VCC', True, self)
        self.update()


    def __str__(self):
        inputs = ' '.join([str(self.getpin(code)) for code in self.INPUT_PINS])
        outputs = ' '.join([str(self.getpin(code)) for code in self.OUTPUT_PINS])
        return '{} I: {} O: {}'.format(self.__class__.__name__, inputs, outputs)

    def asciiart(self):
        if self.PIN_ORDER:
            pin_order = self.PIN_ORDER
        else:
            pin_order = self.INPUT_PINS + self.OUTPUT_PINS
        pins = self.getpins(pin_order)
        if len(pins) % 2:
            pins.append(None)
        left_pins = pins[:len(pins) // 2]
        right_pins = list(reversed(pins[len(pins) // 2:]))
        lines = []
        lines.append('     _______     ')
        for index, (left, right) in enumerate(zip(left_pins, right_pins)):
            larrow = '<' if left.output else '>'
            lpol = '+' if left.ishigh() else '-'
            sleft = left.code.rjust(4) + larrow + '|' + lpol
            if right:
                rarrow = '>' if right.output else '<'
                rpol = '+' if right.ishigh() else '-'
                sright = rpol + '|' + rarrow + right.code.ljust(4)
            else:
                sright = ' |     '

            if index == len(left_pins) - 1:
                spacer = '_'
            else:
                spacer = ' '
            middle = 'U' if index == 0 else spacer
            line = sleft + spacer + middle + spacer + sright
            lines.append(line)
        return '\n'.join(lines)
    def ispowered(self):
        return self.vcc.ishigh()

    
    def getpin(self, code):
        # Edit: attr
        return self.pins['pin_{}'.format(code.replace('~', ''))]

    def getpins(self, codes):
        return [self.getpin(code) for code in codes]
    
    
    # Set multiple pins on the same chip and only update chips one all pins are updated.
    def setpins(self, low, high):
        
        updateself = False
        updatelist = set()
        for codes, val in [(low, False), (high, True)]:
            for pin in self.getpins(codes):
                if pin.high != val:
                    pin.high = val
                    if pin.output:
                        updatelist = updatelist.union(pin.propagate_to())
                    else:
                        updateself = True
        if updateself:
            self.update()
        for chip in updatelist:
            chip.update()

    
    def tick(self, us):
        pass
    def update(self):
        pass
    def wirepins(self, chip, inputs, outputs):
        for icode, ocode in zip(inputs, outputs):
           ipin = self.getpin(icode)
           opin = chip.getpin(ocode)
           assert opin.output
           assert not ipin.output
           ipin.wires.add(opin)
           opin.wires.add(ipin)
        self.update()


class ActivableChip(Chip):
    ENABLE_PINS:List[str] = [] # ~ means that low == enabled

    def is_enabled(self):
        for code in self.ENABLE_PINS:
            pin = self.getpin(code.replace('~', ''))
            enabled = pin.ishigh()
            if code.startswith('~'):
                enabled = not enabled
            if not enabled:
                return False
        return True

# first pin is the least significant bit
def set_binary_value(value, pins):
    for i, pin in enumerate(pins):
        pin.set(bool((value >> i) & 0x1))

def get_binary_value(pins):
    value = 0
    for index, pin in enumerate(pins):
        if pin.ishigh():
            value |= 1 << index
    return value

class BinaryCounter(ActivableChip):
    CLOCK_PIN:str = ''
    prev_clock_high:bool
    value:int
    def __init__(self, *args, **kwargs):
        self.value = 0
        self.prev_clock_high = False
        for code in self.OUTPUT_PINS:
            pin = Pin(code, code in self.STARTING_HIGH, self, True)
            setattr(self, 'pin_{}'.format(pin.code), pin)
        for code in self.INPUT_PINS:
            pin = Pin(code, code in self.STARTING_HIGH, self)
            setattr(self, 'pin_{}'.format(pin.code), pin)
        self.vcc = Pin('VCC', True, self)
        self.update()

    def maxvalue(self):
        return (1 << len(self.OUTPUT_PINS)) - 1

    def update(self):
        if not self.is_enabled():
            return

        clock = self.getpin(self.CLOCK_PIN)
        if clock.ishigh() and not self.prev_clock_high:
            self.value += 1
            if self.value > self.maxvalue():
                self.value = 0

            set_binary_value(self.value, self.getpins(self.OUTPUT_PINS))

        self.prev_clock_high = clock.ishigh()


class SN74F161AN(BinaryCounter):
    CLOCK_PIN = 'CLK'
    ENABLE_PINS = ['ENT', 'ENP']
    STARTING_HIGH = ENABLE_PINS
    INPUT_PINS = [CLOCK_PIN] + ENABLE_PINS
    OUTPUT_PINS = ['QA', 'QB', 'QC', 'QD']


class ShiftRegister(ActivableChip):
    SERIAL_PINS:List[str] = []
    CLOCK_PIN:str = ''
    BUFFER_PIN:str = '' # Pin that makes the SR buffer go to output pin. Leave blank if there's none
    RESET_PIN:str = ''
    RESULT_PINS:List[str] = [] # Data is pushed from first pin to last
    prev_clock_high:bool
    prev_buffer_high:bool
    buffer:int

    def __init__(self, *args, **kwargs):
        self.prev_clock_high = False
        self.prev_buffer_high = False
        self.buffer = 0
        for code in self.OUTPUT_PINS:
            pin = Pin(code, code in self.STARTING_HIGH, self, True)
            setattr(self, 'pin_{}'.format(pin.code), pin)
        for code in self.INPUT_PINS:
            pin = Pin(code, code in self.STARTING_HIGH, self)
            setattr(self, 'pin_{}'.format(pin.code), pin)
        self.vcc = Pin('VCC', True, self)
        self.update()

    def is_resetting(self):
        if self.RESET_PIN:
            return self.getpin(self.RESET_PIN).isenabled()
        else:
            return False

    def update(self):
        if (not self.is_enabled()) or self.is_resetting():
            self.setpins(self.RESULT_PINS, [])
            if self.is_resetting():
                self.buffer = 0
            return

        newbuffer = self.buffer

        clock = self.getpin(self.CLOCK_PIN)
        if clock.ishigh() and not self.prev_clock_high:
            newbuffer = newbuffer << 1
            if all([self.getpin(code).ishigh() for code in self.SERIAL_PINS]):
                newbuffer |= 0x1
        self.prev_clock_high = clock.ishigh()

        should_refresh_outputs = False
        if self.BUFFER_PIN:
            bufpin = self.getpin(self.BUFFER_PIN)
            should_refresh_outputs = bufpin.ishigh() and not self.prev_buffer_high
            self.prev_buffer_high = bufpin.ishigh()
            # we don't set self.buffer because, per design, buffered SRs suffer a delay
            # when the buffer pin is activated at the same time as the clock pin.
        else:
            # if there's not buffering, there's no delay
            self.buffer = newbuffer
            should_refresh_outputs = True
        if should_refresh_outputs:
            set_binary_value(self.buffer, self.getpins(self.RESULT_PINS))

        self.buffer = newbuffer


class CD74AC164(ShiftRegister):
    OUTPUT_PINS = ['Q0', 'Q1', 'Q2', 'Q3', 'Q4', 'Q5', 'Q6', 'Q7']
    INPUT_PINS = ['DS1', 'DS2', 'CP', '~MR']
    SERIAL_PINS = ['DS1', 'DS2']
    RESULT_PINS = OUTPUT_PINS
    RESET_PIN = '~MR'
    CLOCK_PIN = 'CP'
    STARTING_HIGH = ['~MR', 'DS2']


class SN74HC595(ShiftRegister):
    OUTPUT_PINS = ['QA', 'QB', 'QC', 'QD', 'QE', 'QF', 'QG', 'QH']
    INPUT_PINS = ['~OE', 'RCLK', 'SER', 'SRCLK', '~SRCLR']
    SERIAL_PINS = ['SER']
    RESULT_PINS = OUTPUT_PINS
    ENABLE_PINS = ['~OE']
    RESET_PIN = '~SRCLR'
    CLOCK_PIN = 'SRCLK'
    BUFFER_PIN = 'RCLK'
    STARTING_HIGH = ['~SRCLR']

# decoders.py
class Decoder(ActivableChip):
    SERIAL_PINS:List[str] = [] # LSB pin goes first
    RESULT_PINS:List[str] = [] # LSB pin goes first

    def update(self):
        selection = 0 if self.is_enabled() else 0xff
        for index, code in enumerate(self.SERIAL_PINS):
            pin = self.getpin(code)
            selection |= int(pin.ishigh()) << index
        for index, code in enumerate(self.RESULT_PINS):
            pin = self.getpin(code)
            pin.set(index != selection)


class SN74HC138(Decoder):
    OUTPUT_PINS = ['Y0', 'Y1', 'Y2', 'Y3', 'Y4', 'Y5', 'Y6', 'Y7']
    INPUT_PINS = ['A', 'B', 'C', 'G2A', 'G2B', 'G1']
    SERIAL_PINS = ['A', 'B', 'C']
    RESULT_PINS = OUTPUT_PINS
    ENABLE_PINS = ['G1', '~G2A', '~G2B']
    STARTING_HIGH = ['G1'] + RESULT_PINS

# seg7.py
class LED:
    vcc:Pin
    gnd:Pin
    fade_delay_us:int
    fade_counter_us:int
    def __init__(self, vcc, gnd, fade_delay_us=10000):
        self.vcc = vcc
        self.gnd = gnd
        self.fade_delay_us = fade_delay_us
        self.fade_counter_us = fade_delay_us + 1

    def tick(self, us):
        self.fade_counter_us += us
        self.ishigh()

    def ishigh(self):
        if self.vcc.ishigh() and not self.gnd.ishigh():
            self.fade_counter_us = 0
            return True
        else:
            return self.fade_counter_us <= self.fade_delay_us

def combine_repr(segs):
    """Combine and returns __str__ repr of multiple Segment7
    """
    outputs = [str(seg) for seg in segs]
    line1 = ' '.join([s[:3] for s in outputs])
    line2 = ' '.join([s[4:7] for s in outputs])
    line3 = ' '.join([s[8:] for s in outputs])
    return '\n'.join([line1, line2, line3])

class Segment7(Chip):
    INPUT_PINS:List[str] = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'DP']
    leds:Dict[str, LED]
    vcc:Pin
    pins:Dict[str,Pin]
    def __init__(self, *args, **kwargs):
        for code in self.OUTPUT_PINS:
            pin = Pin(code, code in self.STARTING_HIGH, self, True)
            self.pins['pin_{}'.format(pin.code)]= pin
        for code in self.INPUT_PINS:
            pin = Pin(code, code in self.STARTING_HIGH, self)
            self.pins['pin_{}'.format(pin.code)]= pin
        self.vcc = Pin('VCC', True, self)
        self.update()
        self.leds = {pin.code: LED(self.vcc, pin) for pin in self.getpins(self.INPUT_PINS)}

    def __str__(self):
        SEGMENTS = ["""
 _.
|_|
|_|""".strip('\n')]
        # Remember, each line is **4** chars long if we count the \n!
        SEGPOS = [
            '', 'A', 'DP', '',
            'F', 'G', 'B', '',
            'E', 'D', 'C'
        ]
        s = []
        for c, seg in zip(SEGMENTS, SEGPOS):
            s.append(c if seg and self.leds[seg].ishigh() else ' ')
        return ''.join(s)

    def tick(self, us):
        for led in self.leds.values():
            led.tick(us)




class Gate(Chip):
    IO_MAPPING:List[List[str]] = None # [(I1, I2, ..., IN, O)]

    # Edit: abstractmethod are not inferred
    # @abstractmethod
    # def _test(self, input_pins):
    #     raise NotImplementedError()

    def update(self):
        for l in self.IO_MAPPING:
            in_ = l[:-1]
            out = l[-1]
            pins_in = self.getpins(in_)
            pin_out = self.getpin(out)
            pin_out.set(self._test(pins_in))


class NOR(Gate):
    def _test(self, input_pins):
        return not any([p.ishigh() for p in input_pins])

class NAND(Gate):
    def _test(self, input_pins):
        return not all([p.ishigh() for p in input_pins])

class OR(Gate):
    def _test(self, input_pins):
        return any([p.ishigh() for p in input_pins])

class AND(Gate):
    def _test(self, input_pins):
        return all([p.ishigh() for p in input_pins])


class CD4001B(NOR):
    IO_MAPPING = [
        ['A', 'B', 'J'],
        ['C', 'D', 'K'],
        ['G', 'H', 'M'],
        ['E', 'F', 'L'],
    ]
    INPUT_PINS = list(chain(IO_MAPPING[0][:2], IO_MAPPING[1][:2], IO_MAPPING[2][:2], IO_MAPPING[3][:2]))
    OUTPUT_PINS = [t[2] for t in IO_MAPPING]

class CD4002B(NOR):
    IO_MAPPING = [
        ['A', 'B', 'C', 'D', 'J'],
        ['E', 'F', 'G', 'H', 'K'],
    ]
    INPUT_PINS = list(chain(IO_MAPPING[0][:4], IO_MAPPING[1][:4]))
    OUTPUT_PINS = [t[4] for t in IO_MAPPING]

class CD4025B(NOR):
    IO_MAPPING = [
        ['A', 'B', 'C', 'J'],
        ['D', 'E', 'F', 'K'],
        ['G', 'H', 'I', 'L'],
    ]
    INPUT_PINS = list(chain(IO_MAPPING[0][:3], IO_MAPPING[1][:3], IO_MAPPING[2][:3]))
    OUTPUT_PINS = [t[3] for t in IO_MAPPING]

class SN74LS02(NOR):
    IO_MAPPING = [
        ['A1', 'B1', 'Y1'],
        ['A2', 'B2', 'Y2'],
        ['A3', 'B3', 'Y3'],
        ['A4', 'B4', 'Y4'],
    ]
    INPUT_PINS = list(chain(IO_MAPPING[0][:2], IO_MAPPING[1][:2], IO_MAPPING[2][:2], IO_MAPPING[3][:2]))
    OUTPUT_PINS = [t[2] for t in IO_MAPPING]

class SN74LS27(NOR):
    IO_MAPPING = [
        ['A1', 'B1', 'C1', 'Y1'],
        ['A2', 'B2', 'C2', 'Y2'],
        ['A3', 'B3', 'C3', 'Y3'],
    ]
    INPUT_PINS = list(chain(IO_MAPPING[0][:3], IO_MAPPING[1][:3], IO_MAPPING[2][:3]))
    OUTPUT_PINS = [t[3] for t in IO_MAPPING]

class SN54ALS27A(SN74LS27):
    pass

class SN54AS27(SN74LS27):
    pass

class SN5427(SN74LS27):
    pass

class SN7427(SN74LS27):
    pass

class SN54LS27(SN74LS27):
    pass

class SN74ALS27A(SN74LS27):
    pass

class SN74AS27(SN74LS27):
    pass

class SN54S260(NOR):
    IO_MAPPING = [
        ['A1', 'B1', 'C1', 'D1', 'E1', 'Y1'],
        ['A2', 'B2', 'C2', 'D2', 'E2', 'Y2'],
    ]
    INPUT_PINS = list(chain(IO_MAPPING[0][:5], IO_MAPPING[1][:5]))
    OUTPUT_PINS = [t[5] for t in IO_MAPPING]

class SN74S260(SN54S260):
    pass

class SN74F260(SN54S260):
    pass

class Inverter(Chip):
    def update(self):
        for in_, out in zip(self.INPUT_PINS, self.OUTPUT_PINS):
            pin_in = self.getpin(in_)
            pin_out = self.getpin(out)
            pin_out.set(not pin_in.ishigh())


class SN74HC14(Inverter):
    INPUT_PINS = ['1A', '2A', '3A', '4A', '5A', '6A']
    OUTPUT_PINS = ['1Y', '2Y', '3Y', '4Y', '5Y', '6Y']

