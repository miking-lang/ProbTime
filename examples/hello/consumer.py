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

with mmio.probtime_open("dst", buffer_size) as f:
    while True:
        msgs = f.read_messages()
        for msg in msgs:
            ts, payload = struct.unpack("=qd", msg)
            print(f"Received message with timestamp {ts} and payload {payload}")
        time.sleep(0.1)
