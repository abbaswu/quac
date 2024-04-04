import argparse
import socket
import sys


def is_port_in_use(port: int) -> bool:
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        return s.connect_ex(('localhost', port)) == 0


if __name__ == '__main__':
    # Parse command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('-p', '--port', type=int, required=True)
    args = parser.parse_args()

    port: int = args.port

    if is_port_in_use(port):
        sys.exit(0)
    else:
        sys.exit(1)
