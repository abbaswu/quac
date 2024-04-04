import os
import random
import socket
class A:
    pass
peer_hostnames= {p for p in os.environ.get('TC_PEERS', '').split(',') if p}
PORT = int(os.environ.get('TC_PORT', 9999))
def f(data, peer):
    global peer_hostnames
    peer = peer or random.choice(list(peer_hostnames))
    with socket.create_connection((peer, PORT), timeout=1) as s:
        pass
    peer_hostnames = {x for x in peer_hostnames if x != peer}
    return peer_hostnames

