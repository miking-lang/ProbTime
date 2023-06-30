# A relay passing data from the output of task a to the input of task b.
import signal
import sys
import time

infd = open("a-out1", "rb")
outfd = open("b-in1", "wb")

def sigint_handler(sig, frame):
    infd.close()
    outfd.close()
    sys.exit(0)

signal.signal(signal.SIGINT, sigint_handler)
while True:
    data = infd.read()
    outfd.write(data)
    outfd.flush()
    time.sleep(0.1)
