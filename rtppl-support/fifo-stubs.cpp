#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <caml/signals.h>

#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>
#include <iostream>
#include <vector>

struct payload {
  char *data;
  int64_t size;
};

int min(int a, int b) {
  if (a < b) return a;
  return b;
}

int64_t read_message_size(int fd) {
  char buffer[sizeof(int64_t)];
  int64_t count = 0;
  while (count < sizeof(int64_t)) {
    int bytes = read(fd, (void*)&buffer[count], sizeof(int64_t)-count);
    if (bytes <= 0) {
      return -1;
    }
    count += bytes;
  }
  int64_t sz;
  memcpy((void*)&sz, buffer, sizeof(int64_t));
  return sz;
}

bool read_message(int fd, payload& p) {
  p.size = read_message_size(fd);
  if (p.size <= 0) {
    return false;
  }
  p.data = (char*)malloc(p.size);
  int64_t count = 0;
  while (count < p.size) {
    int bytes_read = read(fd, (void*)&p.data[count], p.size - count);
    if (bytes_read == -1) {
      fprintf(stderr, "Error reading message: %s\n", strerror(errno));
      exit(1);
    }
    count += bytes_read;
  }
  return true;
}

std::vector<payload> read_messages(int fd) {
  std::vector<payload> input_seq;
  payload p;
  while (read_message(fd, p)) {
    input_seq.emplace_back(p);
  }
  return input_seq;
}

void write_message_size(int fd, int64_t sz) {
  char buffer[sizeof(int64_t)];
  memcpy((void*)buffer, (void*)&sz, sizeof(int64_t));
  int64_t count = 0;
  while (count < sizeof(int64_t)) {
    int bytes = write(fd, (void*)&buffer[count], sizeof(int64_t)-count);
    if (bytes == -1) {
      fprintf(stderr, "Error writing message: %s\n", strerror(errno));
      exit(1);
    }
    count += bytes;
  }
}

void write_message(int fd, const payload& p) {
  write_message_size(fd, p.size);
  int64_t count = 0;
  while (count < p.size) {
    int bytes_written = write(fd, (void*)&p.data[count], p.size - count);
    if (bytes_written == -1) {
      fprintf(stderr, "Error writing message: %s\n", strerror(errno));
      exit(1);
    }
    count += bytes_written;
  }
  fsync(fd);
}

inline value to_timespec_value(int64_t ts) {
  int64_t sec = ts / (int64_t)1e9;
  int64_t nsec = ts % (int64_t)1e9;
  value timespec = caml_alloc(2, 0);
  Store_field(timespec, 0, Val_long(sec));
  Store_field(timespec, 1, Val_long(nsec));
  return timespec;
}

inline int64_t timespec_value_to_int64(value ts) {
  int64_t sec = Long_val(Field(ts, 0));
  int64_t nsec = Long_val(Field(ts, 1));
  return sec * (int64_t)1e9 + nsec;
}

extern "C" {

  value open_file_nonblocking_stub(value pipe) {
    CAMLparam1(pipe);
    const char *pipe_id = String_val(pipe);
    int fd = open(pipe_id, O_RDWR | O_NONBLOCK);
    if (fd == -1) {
      fprintf(stderr, "Could not open pipe %s: %s\n", pipe_id, strerror(errno));
      exit(1);
    }
    CAMLreturn(Val_int(fd));
  }

  void close_file_descriptor_stub(value fd) {
    CAMLparam1(fd);
    close(Int_val(fd));
    CAMLreturn0;
  }

  value read_float_named_pipe_stub(value fd) {
    CAMLparam1(fd);
    CAMLlocal2(out, tsv);
    std::vector<payload> input_seq = read_messages(Int_val(fd));
    out = caml_alloc(input_seq.size(), 0);
    for (size_t i = 0; i < input_seq.size(); i++) {
      caml_initialize(&Field(out, i), Val_unit);
    }
    for (size_t i = 0; i < input_seq.size(); i++) {
      const payload &p = input_seq[i];
      int64_t ts;
      memcpy(&ts, (char*)p.data, sizeof(int64_t));
      tsv = caml_alloc(2, 0);
      Store_field(tsv, 0, to_timespec_value(ts));
      double val;
      memcpy(&val, (char*)p.data + sizeof(int64_t), sizeof(double));
      Store_field(tsv, 1, caml_copy_double(val));
      free(p.data);
      Store_field(out, i, tsv);
    }
    CAMLreturn(out);
  }

  void write_float_named_pipe_stub(value fd, value tsv) {
    CAMLparam2(fd, tsv);
    payload p;
    p.size = sizeof(int64_t) + sizeof(double);
    p.data = (char*)malloc(p.size);
    value ts = Field(tsv, 0);
    int64_t timestamp = timespec_value_to_int64(ts);
    memcpy(p.data, (void*)&timestamp, sizeof(int64_t));
    value v = Field(tsv, 1);
    double data = Double_val(v);
    memcpy(p.data + sizeof(int64_t), (void*)&data, sizeof(double));
    write_message(Int_val(fd), p);
    free(p.data);
    CAMLreturn0;
  }

  value read_dist_float_named_pipe_stub(value fd) {
    CAMLparam1(fd);
    CAMLlocal4(out, dist_samples, entry, tsv);
    std::vector<payload> input_seq = read_messages(Int_val(fd));
    out = caml_alloc(input_seq.size(), 0);
    for (size_t i = 0; i < input_seq.size(); i++) {
      caml_initialize(&Field(out, i), Val_unit);
    }
    for (size_t i = 0; i < input_seq.size(); i++) {
      const payload &p = input_seq[i];
      int64_t nsamples = (p.size - sizeof(int64_t)) / (2 * sizeof(double));
      char *ptr = p.data;
      int64_t timestamp;
      memcpy((void*)&timestamp, ptr, sizeof(int64_t));
      ptr += sizeof(int64_t);
      tsv = caml_alloc(2, 0);
      Store_field(tsv, 0, to_timespec_value(timestamp));
      caml_initialize(&Field(tsv, 1), Val_unit);
      dist_samples = caml_alloc(nsamples, 0);
      for (size_t j = 0; j < nsamples; j++) {
        caml_initialize(&Field(dist_samples, j), Val_unit);
      }
      for (size_t j = 0; j < nsamples; j++) {
        entry = caml_alloc(2, 0);
        double weight;
        memcpy((void*)&weight, ptr, sizeof(double));
        Store_field(entry, 0, caml_copy_double(weight));
        ptr += sizeof(double);
        double sample;
        memcpy((void*)&sample, ptr, sizeof(double));
        Store_field(entry, 1, caml_copy_double(sample));
        ptr += sizeof(double);
        Store_field(dist_samples, j, entry);
      }
      Store_field(tsv, 1, dist_samples);
      Store_field(out, i, tsv);
    }
    CAMLreturn(out);
  }

  void write_dist_float_named_pipe_stub(value fd, value tsv) {
    CAMLparam2(fd, tsv);
    value ts = Field(tsv, 0);
    value d = Field(tsv, 1);
    value samples = Field(d, 0);
    value log_weights = Field(d, 1);
    int64_t nsamples = Wosize_val(samples);
    payload p;
    p.size = sizeof(int64_t) + 2 * nsamples * sizeof(double);
    p.data = (char*)malloc(p.size);
    char *ptr = p.data;
    int64_t timestamp = timespec_value_to_int64(ts);
    memcpy(ptr, (void*)&timestamp, sizeof(int64_t));
    ptr += sizeof(int64_t);
    for (size_t i = 0; i < nsamples; i++) {
      double tmp = Double_field(log_weights, i);
      memcpy(ptr, (void*)&tmp, sizeof(double));
      ptr += sizeof(double);
      tmp = Double_field(samples, i);
      memcpy(ptr, (void*)&tmp, sizeof(double));
      ptr += sizeof(double);
    }
    write_message(Int_val(fd), p);
    free(p.data);
    CAMLreturn0;
  }

  value read_dist_float_record_named_pipe_stub(value fd, value nfields_val) {
    CAMLparam2(fd, nfields_val);
    CAMLlocal5(out, dist_samples, sample, tsv, s);
    std::vector<payload> input_seq = read_messages(Int_val(fd));
    int64_t nfields = Long_val(nfields_val);
    out = caml_alloc(input_seq.size(), 0);
    for (size_t i = 0; i < input_seq.size(); i++) {
      caml_initialize(&Field(out, i), Val_unit);
    }
    for (size_t i = 0; i < input_seq.size(); i++) {
      const payload &p = input_seq[i];
      int64_t nsamples = (p.size - sizeof(int64_t)) / ((nfields + 1) * sizeof(double));
      char *ptr = p.data;
      int64_t timestamp;
      memcpy((void*)&timestamp, ptr, sizeof(int64_t));
      ptr += sizeof(int64_t);
      tsv = caml_alloc(2, 0);
      Store_field(tsv, 0, to_timespec_value(timestamp));
      caml_initialize(&Field(tsv, 1), Val_unit);
      dist_samples = caml_alloc(nsamples, 0);
      for (size_t j = 0; j < nsamples; j++) {
        caml_initialize(&Field(dist_samples, j), Val_unit);
      }
      for (size_t j = 0; j < nsamples; j++) {
        sample = caml_alloc(2, 0);
        double weight;
        memcpy((void*)&weight, ptr, sizeof(double));
        Store_field(sample, 0, caml_copy_double(weight));
        caml_initialize(&Field(sample, 1), Val_unit);
        ptr += sizeof(double);
        s = caml_alloc(nfields, 0);
        for (size_t k = 0; k < nfields; k++) {
          caml_initialize(&Field(s, k), Val_unit);
        }
        for (size_t k = 0; k < nfields; k++) {
          double tmp;
          memcpy((void*)&tmp, ptr, sizeof(double));
          Store_field(s, k, caml_copy_double(tmp));
          ptr += sizeof(double);
        }
        Store_field(sample, 1, s);
        Store_field(dist_samples, j, sample);
      }
      Store_field(tsv, 1, dist_samples);
      Store_field(out, i, tsv);
    }
    CAMLreturn(out);
  }

  void write_dist_float_record_named_pipe_stub(value fd, value nfields_val, value tsv) {
    CAMLparam3(fd, nfields_val, tsv);
    value ts = Field(tsv, 0);
    value d = Field(tsv, 1);
    value samples = Field(d, 0);
    value log_weights = Field(d, 1);
    int64_t nsamples = Wosize_val(samples);
    int64_t nfields = Long_val(nfields_val);
    payload p;
    // The payload consists of a timestamp, log weights, and sample data
    p.size = sizeof(int64_t) + nsamples * sizeof(double) + nsamples * nfields * sizeof(double);
    p.data = (char*)malloc(p.size);
    char *ptr = p.data;
    int64_t timestamp = timespec_value_to_int64(ts);
    memcpy(ptr, (void*)&timestamp, sizeof(int64_t));
    ptr += sizeof(int64_t);
    for (size_t i = 0; i < nsamples; i++) {
      double tmp = Double_field(log_weights, i);
      memcpy(ptr, (void*)&tmp, sizeof(double));
      ptr += sizeof(double);
      value rec = Field(samples, i);
      for (size_t j = 0; j < nfields; j++) {
        tmp = Double_val(Field(rec, j));
        memcpy(ptr, (void*)&tmp, sizeof(double));
        ptr += sizeof(double);
      }
    }
    write_message(Int_val(fd), p);
    free(p.data);
    CAMLreturn0;
  }

}
