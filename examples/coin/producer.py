# A producer of artificial coin-flip outcomes written to the cf task.
import random
import signal
import struct
import sys
import time

fd = open("cf-in1", "wb")

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
    fd.close()
    sys.exit(0)

signal.signal(signal.SIGINT, sigint_handler)
while True:
    sz = 16
    ts = time.time_ns()
    payload = biased_coin()
    # payload = fair_coin()
    msg = struct.pack("=qqd", sz, ts, payload)
    fd.write(msg)
    fd.flush()
    time.sleep(0.3)
