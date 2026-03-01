
type 'st state =
| Hist of 'st * 'st list * 'st list
| Failed

type 'e event =
| Do of 'e
| Undo
| Redo

(** val current : 'a1 state -> 'a1 option **)

let current = function
| Hist (curr, _, _) -> Some curr
| Failed -> None

(** val past : 'a1 state -> 'a1 list **)

let past = function
| Hist (_, p, _) -> p
| Failed -> []

(** val future : 'a1 state -> 'a1 list **)

let future = function
| Hist (_, _, fut) -> fut
| Failed -> []

(** val flat_map :
    'a1 state -> ('a1 -> 'a1 list -> 'a1 list -> 'a1 state) -> 'a1 state **)

let flat_map hs f =
  match hs with
  | Hist (curr, p, fut) -> f curr p fut
  | Failed -> Failed

(** val init : 'a1 -> 'a1 state **)

let init s =
  Hist (s, [], [])

(** val step : ('a1 -> 'a2 -> 'a1) -> 'a1 state -> 'a2 event -> 'a1 state **)

let step inner hs e =
  flat_map hs (fun curr p fut ->
    match e with
    | Do ev -> Hist ((inner curr ev), (curr::p), [])
    | Undo ->
      (match p with
       | [] -> Failed
       | prev::rest -> Hist (prev, rest, (curr::fut)))
    | Redo ->
      (match fut with
       | [] -> Failed
       | next::rest -> Hist (next, (curr::p), rest)))

(** val is_failed : 'a1 state -> bool **)

let is_failed = function
| Hist (_, _, _) -> false
| Failed -> true

(** val can_undo : 'a1 state -> bool **)

let can_undo = function
| Hist (_, l, _) -> (match l with
                     | [] -> false
                     | _::_ -> true)
| Failed -> false

(** val can_redo : 'a1 state -> bool **)

let can_redo = function
| Hist (_, _, l0) -> (match l0 with
                      | [] -> false
                      | _::_ -> true)
| Failed -> false

(** val mk_do : 'a1 -> 'a1 event **)

let mk_do e =
  Do e

(** val mk_undo : 'a1 event **)

let mk_undo =
  Undo

(** val mk_redo : 'a1 event **)

let mk_redo =
  Redo
