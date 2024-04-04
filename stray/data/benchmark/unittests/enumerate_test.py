from typing import List, NamedTuple
class UnspentTxOut(NamedTuple):
    value: int
    to_address: str


def add_to_utxo(v, t):
    utxo = UnspentTxOut(v, t)
    