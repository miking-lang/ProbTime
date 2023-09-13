#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <caml/signals.h>

#include "shared.h"

value clock_monotonic_time_stub() {
  CAMLparam0();
  CAMLlocal1(out);
  struct timespec ts;
  clock_get_monotonic_timespec(&ts);
  out = caml_alloc(2, 0);
  Store_field(out, 0, Val_int(ts.tv_sec));
  Store_field(out, 1, Val_int(ts.tv_nsec));
  CAMLreturn(out);
}

value clock_wall_time_stub() {
  CAMLparam0();
  CAMLlocal1(out);
  struct timespec ts;
  clock_gettime(CLOCK_REALTIME, &ts);
  out = caml_alloc(2, 0);
  Store_field(out, 0, Val_int(ts.tv_sec));
  Store_field(out, 1, Val_int(ts.tv_nsec));
  CAMLreturn(out);
}

value clock_process_cpu_time_stub() {
  CAMLparam0();
  CAMLlocal1(out);
  struct timespec ts;
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts);
  out = caml_alloc(2, 0);
  Store_field(out, 0, Val_int(ts.tv_sec));
  Store_field(out, 1, Val_int(ts.tv_nsec));
  CAMLreturn(out);
}

void clock_nanosleep_stub(value t) {
  CAMLparam1(t);
  struct timespec ts;
  ts.tv_sec = Long_val(Field(t, 0));
  ts.tv_nsec = Long_val(Field(t, 1));
  caml_process_pending_actions();
  clock_nanosleep_abstime(&ts);
  CAMLreturn0;
}

value set_priority_stub(value priority) {
  CAMLparam1(priority);
  int policy;
  struct sched_param param;
  pthread_getschedparam(pthread_self(), &policy, &param);
  int old_priority = param.sched_priority;
  param.sched_priority = Int_val(priority);
  pthread_setschedparam(pthread_self(), policy, &param);
  CAMLreturn(Val_int(old_priority));
}
