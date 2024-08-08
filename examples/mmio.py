import mmap
import os
import struct
import sys
from multiprocessing import shared_memory
import contextlib

class ProbTimeIO:
    def __init__(self, fname, buffer_size):
        try:
            self.shm = shared_memory.SharedMemory(name=fname, create=True, size=buffer_size)
        except:
            # Assume the shared memory buffer has already been created by
            # another process using the correct buffer size.
            self.shm = shared_memory.SharedMemory(name=fname)
        self.pos = 0

    def __del__(self):
        self.close()

    def close(self):
        if hasattr(self, 'shm'):
            self.shm.close()

    def read_message(self):
        pos = self.pos
        shm = self.shm
        b = shm.buf[pos:pos+8]
        sz, = struct.unpack("=q", b)
        if sz <= 0:
            return None
        shm.buf[pos:pos+8] = bytearray(8)
        pos += 8
        if pos + sz >= len(shm.buf):
            n = len(shm.buf) - pos
            b1 = bytes(shm.buf[pos:])
            shm.buf[pos:] = bytearray(n)
            b2 = bytes(shm.buf[0:sz-n])
            shm.buf[0:sz-n] = bytearray(sz-n)
            self.pos = sz-n
            return b1 + b2
        else:
            b = bytes(shm.buf[pos:pos+sz])
            shm.buf[pos:pos+sz] = bytearray(sz)
            self.pos = pos+sz
            return b

    def read_messages(self):
        msgs = []
        while True:
            msg = self.read_message()
            if msg is None:
                break
            msgs.append(msg)
        return msgs

    def write_message(self, msg):
        sz_pos = self.pos
        shm = self.shm
        pos = sz_pos + 8
        if pos + len(msg) >= len(shm.buf):
            n = len(shm.buf) - pos
            shm.buf[pos:] = bytes(msg[:n])
            shm.buf[0:len(msg)-n] = bytes(msg[n:])
            self.pos = len(msg)-n
        else:
            shm.buf[pos:pos+len(msg)] = bytes(msg)
            self.pos = pos+len(msg)
        szbytes = struct.pack("=q", len(msg))
        shm.buf[sz_pos:sz_pos+8] = szbytes

@contextlib.contextmanager
def probtime_open(f, buffer_size):
    x = ProbTimeIO(f, buffer_size)
    try:
        yield x
    finally:
        x.close()

def main():
    with probtime_open("test") as w:
        with probtime_open("test") as r:
            for i in range(1000):
                b = bytearray(1024)
                for j in range(1024):
                    b[j] = j % 256
                w.write_message(b)
                w.write_message(b)
                msgs = r.read_messages()
                if len(msgs) != 2:
                    print("Invalid number of messages read")
                    sys.exit(1)
                if b != msgs[0] or b != msgs[1]:
                    print(f"Mismatching byte arrays in iteration i={i}")
                    print(b)
                    print(msgs[0])
                    print(msgs[1])
                    sys.exit(1)
    print("Tests passed")

if __name__ == "__main__":
    main()
