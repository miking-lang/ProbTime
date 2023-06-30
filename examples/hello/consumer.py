# A consumer acting as the actuator output receiving data from task b.
import signal
import struct
import sys
import time

fd = open("b-out1", "rb")
i = 0

def sigint_handler(sig, frame):
    fd.close()
    sys.exit(0)

signal.signal(signal.SIGINT, sigint_handler)
while True:
    data = fd.read()
    ofs = 0
    while ofs < len(data):
        sz, ts, payload = struct.unpack("=qqd", data[ofs:ofs+24])
        print(f"Received message with timestamp {ts} and payload {payload}")
        ofs += 24
    time.sleep(0.1)
