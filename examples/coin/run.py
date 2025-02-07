import json
import signal
import subprocess
import sys
import time

# Clear leftover data from all input/output files of the cf task.
files = ["cf.in1", "bias"]
for f in files:
    open(f, "w").close()

cmds = [
    ["python3", "producer.py"],
    ["python3", "consumer.py"],
    ["./cf"],
]
procs = []
for cmd in cmds:
    print(f"Launching command '{cmd}'")
    procs.append(subprocess.Popen(cmd))

def kill(sig, frame):
    print("Stopping all processes")
    for proc in procs:
        proc.send_signal(signal.SIGINT)
        try:
            proc.wait(0.5)
        except subprocess.TimeoutExpired:
            proc.send_signal(signal.SIGKILL)
            proc.terminate()
            proc.wait()
    sys.exit(0)

signal.signal(signal.SIGINT, kill)

# Keep running while waiting for the SIGINT
print("To interrupt, press CTRL+C")
while True:
    time.sleep(1)
