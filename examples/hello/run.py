import json
import signal
import subprocess
import sys
import time

# Clear leftover data from all input/output files of tasks a and b.
files = ["a.in1", "b.in1", "dst"]
for f in files:
    open(f, "w").close()

# Set the mindelay and maxdelay of the tasks
with open("system.json", "r+") as f:
    data = json.load(f)
    for t in data['tasks']:
        if t['id'] == 'a':
            delay = 500 * 10**6
        elif t['id'] == 'b':
            delay = 250 * 10**6
        t['minrate'] = delay
        t['maxrate'] = delay
    f.seek(0)
    json.dump(data, f)
    f.truncate()

cmds = [
    ["python3", "producer.py"],
    ["python3", "consumer.py"],
    ["./a"],
    ["./b"]
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
