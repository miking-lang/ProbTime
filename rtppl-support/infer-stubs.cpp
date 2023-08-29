#include <atomic>
#include <csetjmp>
#include <csignal>
#include <ctime>
#include <thread>
#include <unistd.h>

#include <caml/alloc.h>
#include <caml/callback.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

#include "shared.h"

extern "C" {
  void raise_signal_after_deadline(struct timespec *deadline) {
    clock_nanosleep_abstime(deadline);
    kill(getpid(), SIGUSR1);
  }

  value rtppl_batched_inference_stub(value interruptible_model, value deadline) {
    CAMLparam2(interruptible_model, deadline);
    CAMLlocal1(out);
    struct timespec ts;
    ts.tv_sec = Long_val(Field(deadline, 0));
    ts.tv_nsec = Long_val(Field(deadline, 1));
    std::thread t(raise_signal_after_deadline, &ts);
    t.detach();
    out = caml_callback(interruptible_model, Val_int(0));
    CAMLreturn(out);
  }
}
