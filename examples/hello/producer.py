# A producer which acts as the sensor input to task a.
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

with mmio.probtime_open("a-in1", buffer_size) as f:
    i = 0
    while True:
        ts = time.time_ns()
        payload = float(i)
        msg = struct.pack("=qd", ts, payload)
        f.write_message(msg)
        i += 1
        time.sleep(1)
