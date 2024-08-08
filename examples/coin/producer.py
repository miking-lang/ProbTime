# A producer of artificial coin-flip outcomes written to the cf task.
import json
import random
import signal
import struct
import sys
import time

import mmio

# Models a biased coin which produces heads with probability 0.7
def biased_coin():
    r = random.randrange(0, 10)
    if r < 7:
        return 0.0
    else:
        return 1.0

def fair_coin():
    r = random.randrange(0, 2)
    if r == 0:
        return 0.0
    else:
        return 1.0

def sigint_handler(sig, frame):
    sys.exit(0)
signal.signal(signal.SIGINT, sigint_handler)

with open("system.json", "r") as f:
    data = json.load(f)
    buffer_size = data["compileopts"]["buffer-size"]

with mmio.probtime_open("cf-in1", buffer_size) as f:
    while True:
        ts = time.time_ns()
        payload = biased_coin()
        # payload = fair_coin()
        msg = struct.pack("=qd", ts, payload)
        f.write_message(msg)
        time.sleep(0.3)
