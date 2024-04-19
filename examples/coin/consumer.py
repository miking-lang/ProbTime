# A consumer acting as the actuator output receiving data from task b.
import json
import signal
import struct
import sys
import time

import mmio

def sigint_handler(sig, frame):
    sys.exit(0)
signal.signal(signal.SIGINT, sigint_handler)

with open("system.json", "r") as f:
    data = json.load(f)
    buffer_size = data["compileopts"]["buffer-size"]

with mmio.probtime_open("bias", buffer_size) as f:
    while True:
        msgs = f.read_messages()
        for msg in msgs:
            _, mu, sigma = struct.unpack("=qdd", msg)
            print(f"Coin distribution: {mu} ± {sigma}")
        time.sleep(0.1)
