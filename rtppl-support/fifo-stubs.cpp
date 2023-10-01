#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <caml/signals.h>

#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#include <string.h>
#include <unistd.h>
#include <iostream>
#include <map>
#include <vector>

struct file_buffer {
  char *id;
  char *start;
  char *pos;
  int64_t sz;
};

const int64_t BUFFER_SIZE = 1<<20;

std::map<int, file_buffer> buffers;

struct payload {
  char *data;
  int64_t size;
};

int min(int a, int b) {
  if (a < b) return a;
  return b;
}

bool read_message(file_buffer& b, payload& p) {
  p.size = *(int64_t*)b.pos;
  if (p.size <= 0) {
    return false;
  }
  memset(b.pos, 0, sizeof(int64_t));
  b.pos += sizeof(int64_t);
  p.data = (char*)malloc(p.size);
  if (b.pos + p.size >= b.start + b.sz) {
    int64_t n = b.sz - (b.pos - b.start);
    memcpy(p.data, b.pos, n);
    memset(b.pos, 0, n);
    memcpy(p.data + n, b.start, p.size - n);
    memset(b.start, 0, p.size - n);
    b.pos = b.start + p.size - n;
  } else {
    memcpy(p.data, b.pos, p.size);
    memset(b.pos, 0, p.size);
    b.pos += p.size;
  }
  return true;
}

std::vector<payload> read_messages(int fd) {
  std::vector<payload> input_seq;
  payload p;
  file_buffer& b = buffers[fd];
  while (read_message(b, p)) {
    input_seq.emplace_back(p);
  }
  return input_seq;
}

void write_message(int fd, const payload& p) {
  file_buffer& b = buffers[fd];
  int64_t *sz_ptr = (int64_t*)b.pos;
  b.pos += sizeof(int64_t);
  if (b.pos + p.size >= b.start + b.sz) {
    int64_t n = b.sz - (b.pos - b.start);
    memcpy(b.pos, p.data, n);
    memcpy(b.start, p.data + n, p.size - n);
    b.pos = b.start + p.size - n;
  } else {
    memcpy(b.pos, p.data, p.size);
    b.pos += p.size;
  }
  // NOTE(larshum, 2023-09-21): We write the size last to ensure it is
  // synchronized with the rest of the data we write.
  memcpy(sz_ptr, (int64_t*)&p.size, sizeof(int64_t));
  if (msync(b.start, b.sz, MS_ASYNC) == -1) {
    fprintf(stderr, "Syncing memory buffer failed: %s\n", strerror(errno));
    exit(1);
  }
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

  value open_file_nonblocking_stub(value file) {
    CAMLparam1(file);
    const char *name = String_val(file);
    int n = strlen(name) + 2;
    char *id = (char*)malloc(n);;
    snprintf(id, n, "/%s", name);
    umask(0);
    int fd = shm_open(id, O_RDWR | O_CREAT, 0666);
    if (fd == -1) {
      fprintf(stderr, "Could not open shared memory object %s: %s\n", id, strerror(errno));
      exit(1);
    }
    if (ftruncate(fd, BUFFER_SIZE) == -1) {
      fprintf(stderr, "Error while creating memory buffer for %s: %s\n", id, strerror(errno));
      exit(1);
    }
    void *ptr = mmap(NULL, BUFFER_SIZE, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    if (ptr == MAP_FAILED) {
      fprintf(stderr, "Error while mapping file %s to memory: %s\n", id, strerror(errno));
      exit(1);
    }
    file_buffer buf;
    buf.id = id;
    buf.start = (char*)ptr;
    buf.pos = (char*)ptr;
    buf.sz = BUFFER_SIZE;
    buffers[fd] = buf;
    CAMLreturn(Val_int(fd));
  }

  void close_file_descriptor_stub(value fd_val) {
    CAMLparam1(fd_val);
    int fd = Int_val(fd_val);
    shm_unlink(buffers[fd].id);
    munmap(buffers[fd].start, buffers[fd].sz);
    free(buffers[fd].id);
    buffers.erase(fd);
    CAMLreturn0;
  }

  value rtppl_read_int_stub(value fd) {
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
      int64_t val;
      memcpy(&val, (char*)p.data + sizeof(int64_t), sizeof(int64_t));
      Store_field(tsv, 1, Val_long(val));
      free(p.data);
      Store_field(out, i, tsv);
    }
    CAMLreturn(out);
  }

  void rtppl_write_int_stub(value fd, value tsv) {
    CAMLparam2(fd, tsv);
    payload p;
    p.size = sizeof(int64_t) + sizeof(int64_t);
    p.data = (char*)malloc(p.size);
    value ts = Field(tsv, 0);
    int64_t timestamp = timespec_value_to_int64(ts);
    memcpy(p.data, (void*)&timestamp, sizeof(int64_t));
    value v = Field(tsv, 1);
    int64_t data = Long_val(v);
    memcpy(p.data + sizeof(int64_t), (void*)&data, sizeof(int64_t));
    write_message(Int_val(fd), p);
    CAMLreturn0;
  }

  value rtppl_read_float_stub(value fd) {
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

  void rtppl_write_float_stub(value fd, value tsv) {
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

  value rtppl_read_int_record_stub(value fd, value nfields_val) {
    CAMLparam2(fd, nfields_val);
    CAMLlocal3(out, tsv, entry);
    int64_t nfields = Long_val(nfields_val);
    std::vector<payload> input_seq = read_messages(Int_val(fd));
    out = caml_alloc(input_seq.size(), 0);
    for (size_t i = 0; i < input_seq.size(); i++) {
      caml_initialize(&Field(out, i), Val_unit);
    }
    for (size_t i = 0; i < input_seq.size(); i++) {
      const payload &p = input_seq[i];
      int64_t ts;
      tsv = caml_alloc(2, 0);
      char *ptr = p.data;
      memcpy(&ts, ptr, sizeof(int64_t));
      ptr += sizeof(int64_t);
      Store_field(tsv, 0, to_timespec_value(ts));
      entry = caml_alloc(nfields, 0);
      for (size_t j = 0; j < nfields; j++) {
        caml_initialize(&Field(entry, j), Val_unit);
      }
      for (size_t j = 0; j < nfields; j++) {
        int64_t v;
        memcpy(&v, ptr, sizeof(int64_t));
        ptr += sizeof(int64_t);
        Store_field(entry, j, Val_long(v));
      }
      Store_field(tsv, 1, entry);
      Store_field(out, i, tsv);
    }
    CAMLreturn(out);
  }

  void rtppl_write_int_record_stub(value fd, value nfields_val, value tsv) {
    CAMLparam3(fd, nfields_val, tsv);
    int64_t nfields = Long_val(nfields_val);
    payload p;
    p.size = (nfields + 1) * sizeof(int64_t);
    p.data = (char*)malloc(p.size);
    char *ptr = p.data;
    value ts = Field(tsv, 0);
    int64_t timestamp = timespec_value_to_int64(ts);
    memcpy(ptr, (void*)&timestamp, sizeof(int64_t));
    ptr += sizeof(int64_t);
    value entry = Field(tsv, 1);
    for (size_t i = 0; i < nfields; i++) {
      int64_t v = Long_val(Field(entry, i));
      memcpy(ptr, (void*)&v, sizeof(int64_t));
      ptr += sizeof(int64_t);
    }
    write_message(Int_val(fd), p);
    free(p.data);
    CAMLreturn0;
  }

  value rtppl_read_dist_float_stub(value fd) {
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

  void rtppl_write_dist_float_stub(value fd, value tsv) {
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

  value rtppl_read_dist_float_record_stub(value fd, value nfields_val) {
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

  void rtppl_write_dist_float_record_stub(value fd, value nfields_val, value tsv) {
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
