# A producer which acts as the sensor input to task a.
import signal
import struct
import sys
import time

fd = open("a-in1", "wb")
i = 0

def sigint_handler(sig, frame):
    fd.close()
    sys.exit(0)

signal.signal(signal.SIGINT, sigint_handler)
while True:
    sz = 16
    ts = time.time_ns()
    payload = float(i)
    msg = struct.pack("=qqd", sz, ts, payload)
    fd.write(msg)
    fd.flush()
    i += 1
    time.sleep(1)
