
type phase_t =
| Idle
| Loading of int
| Loaded
| Errored

type 'd state = { phase : phase_t; cache : 'd option; next_id : int;
                  retries : int; max_retries : int }

(** val phase : 'a1 state -> phase_t **)

let phase s =
  s.phase

(** val cache : 'a1 state -> 'a1 option **)

let cache s =
  s.cache

(** val next_id : 'a1 state -> int **)

let next_id s =
  s.next_id

(** val retries : 'a1 state -> int **)

let retries s =
  s.retries

type 'd event =
| Fetch
| GotResponse of int * 'd
| GotError of int
| TimedOut of int
| DoRetry

(** val mk_fetch : 'a1 event **)

let mk_fetch =
  Fetch

(** val mk_got_response : int -> 'a1 -> 'a1 event **)

let mk_got_response rid d =
  GotResponse (rid, d)

(** val mk_got_error : int -> 'a1 event **)

let mk_got_error rid =
  GotError rid

(** val mk_timed_out : int -> 'a1 event **)

let mk_timed_out rid =
  TimedOut rid

(** val mk_do_retry : 'a1 event **)

let mk_do_retry =
  DoRetry

(** val init_state : int -> 'a1 state **)

let init_state max_r =
  { phase = Idle; cache = None; next_id = 0; retries = 0; max_retries =
    max_r }

(** val step : 'a1 state -> 'a1 event -> 'a1 state **)

let step s = function
| Fetch ->
  (match s.phase with
   | Loading _ -> s
   | _ ->
     let rid = s.next_id in
     { phase = (Loading rid); cache = s.cache; next_id = ((fun x -> x + 1)
     rid); retries = 0; max_retries = s.max_retries })
| GotResponse (rid, data) ->
  (match s.phase with
   | Loading current_rid ->
     (fun fT fF b -> if b then fT () else fF ())
       (fun _ -> { phase = Loaded; cache = (Some data); next_id = s.next_id;
       retries = 0; max_retries = s.max_retries })
       (fun _ -> s)
       ((=) rid current_rid)
   | _ -> s)
| GotError rid ->
  (match s.phase with
   | Loading current_rid ->
     (fun fT fF b -> if b then fT () else fF ())
       (fun _ -> { phase = Errored; cache = s.cache; next_id = s.next_id;
       retries = s.retries; max_retries = s.max_retries })
       (fun _ -> s)
       ((=) rid current_rid)
   | _ -> s)
| TimedOut rid ->
  (match s.phase with
   | Loading current_rid ->
     (fun fT fF b -> if b then fT () else fF ())
       (fun _ -> { phase = Errored; cache = s.cache; next_id = s.next_id;
       retries = s.retries; max_retries = s.max_retries })
       (fun _ -> s)
       ((=) rid current_rid)
   | _ -> s)
| DoRetry ->
  (match s.phase with
   | Errored ->
     (fun fT fF b -> if b then fT () else fF ())
       (fun _ ->
       let rid = s.next_id in
       { phase = (Loading rid); cache = s.cache; next_id = ((fun x -> x + 1)
       rid); retries = ((fun x -> x + 1) s.retries); max_retries =
       s.max_retries })
       (fun _ -> s)
       ((<) s.retries s.max_retries)
   | _ -> s)

(** val is_idle : phase_t -> bool **)

let is_idle = function
| Idle -> true
| _ -> false

(** val is_loading : phase_t -> bool **)

let is_loading = function
| Loading _ -> true
| _ -> false

(** val loading_rid : phase_t -> int option **)

let loading_rid = function
| Loading rid -> Some rid
| _ -> None

(** val is_loaded : phase_t -> bool **)

let is_loaded = function
| Loaded -> true
| _ -> false

(** val is_errored : phase_t -> bool **)

let is_errored = function
| Errored -> true
| _ -> false
