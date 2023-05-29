type signal = int

let set_signal_handler (x : signal) (f : signal -> unit) : unit =
  Sys.set_signal x (Sys.Signal_handle f)

type timespec = int * int
type 'a tsv = timespec * 'a
type opaque

external get_monotonic_time : unit -> timespec = "clock_monotonic_time_stub"
external get_wall_clock_time : unit -> timespec = "clock_wall_time_stub"
external get_process_cpu_time : unit -> timespec = "clock_process_cpu_time_stub"
external clock_nanosleep : timespec -> unit = "clock_nanosleep_stub"

external set_priority : int -> int = "set_priority_stub"
let set_max_priority (_ : unit) : int = set_priority 255

external open_file_nonblocking : string -> int = "open_file_nonblocking_stub"
external close_file_descriptor : int -> unit = "close_file_descriptor_stub"

external read_float_named_pipe : int -> (float tsv) array = "read_float_named_pipe_stub"
external write_float_named_pipe : int -> float tsv -> unit = "write_float_named_pipe_stub"
external read_dist_float_named_pipe
  : int -> ((float * float) array tsv) array = "read_dist_float_named_pipe_stub"
external write_dist_float_named_pipe
  : int -> (float array * float array) tsv -> unit
  = "write_dist_float_named_pipe_stub"
external read_dist_float_record_named_pipe
  : int -> int -> ((float * opaque) array tsv) array
  = "read_dist_float_record_named_pipe_stub"
external write_dist_float_record_named_pipe
  : int -> int -> (opaque array * float array) tsv -> unit
  = "write_dist_float_record_named_pipe_stub"

external rtppl_batched_inference_stub
  : (opaque list -> opaque list) -> timespec -> opaque list
  = "rtppl_batched_inference_stub"

exception Rtppl_batched_infer_timeout

let rtppl_batched_inference infer_model deadline =
  let f _ = raise Rtppl_batched_infer_timeout in
  Sys.set_signal Sys.sigusr1 (Sys.Signal_handle f);
  let model _ =
    let acc = Atomic.make [] in
    let rec work _ =
      let upd = infer_model () :: Atomic.get acc in
      Atomic.set acc upd;
      work ()
    in
    (* NOTE(larshum, 2023-05-01): We have to catch all exceptions rather than
       just the exception we raise because the exception we raise may be
       captured by called code (and hopefully re-thrown). *)
    (try
      work ()
    with _ ->
      ());
    match Atomic.get acc with
    | [] -> failwith "Batched inference failed to produce any batches on time"
    | result -> result
  in
  rtppl_batched_inference_stub model deadline
