
type phase_t =
| Idle
| Loading of int
| Loaded
| Errored

type 'd state = { phase : phase_t; cache : 'd option; next_id : int;
                  retries : int; max_retries : int }

val phase : 'a1 state -> phase_t

val cache : 'a1 state -> 'a1 option

val next_id : 'a1 state -> int

val retries : 'a1 state -> int

type 'd event =
| Fetch
| GotResponse of int * 'd
| GotError of int
| TimedOut of int
| DoRetry

val mk_fetch : 'a1 event

val mk_got_response : int -> 'a1 -> 'a1 event

val mk_got_error : int -> 'a1 event

val mk_timed_out : int -> 'a1 event

val mk_do_retry : 'a1 event

val init_state : int -> 'a1 state

val step : 'a1 state -> 'a1 event -> 'a1 state

val is_idle : phase_t -> bool

val is_loading : phase_t -> bool

val loading_rid : phase_t -> int option

val is_loaded : phase_t -> bool

val is_errored : phase_t -> bool
