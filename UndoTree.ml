
type 'st tree =
| Leaf of 'st
| Link of 'st * 'st tree
| Node of 'st tree * 'st tree

type 'st ctx =
| Top
| CLink of 'st * 'st ctx
| CLeft of 'st ctx * 'st tree
| CRight of 'st tree * 'st ctx

type 'st cursor =
| At of 'st tree * 'st ctx
| Failed

(** val cursor_flat_map :
    'a1 cursor -> ('a1 tree -> 'a1 ctx -> 'a1 cursor) -> 'a1 cursor **)

let cursor_flat_map c f =
  match c with
  | At (focus, k) -> f focus k
  | Failed -> Failed

(** val step_left : 'a1 tree -> 'a1 ctx -> 'a1 cursor **)

let step_left focus k =
  match focus with
  | Node (l, r) -> At (l, (CLeft (k, r)))
  | _ -> Failed

(** val step_right : 'a1 tree -> 'a1 ctx -> 'a1 cursor **)

let step_right focus k =
  match focus with
  | Node (l, r) -> At (r, (CRight (l, k)))
  | _ -> Failed

(** val step_link : 'a1 tree -> 'a1 ctx -> 'a1 cursor **)

let step_link focus k =
  match focus with
  | Link (s, t) -> At (t, (CLink (s, k)))
  | _ -> Failed

(** val step_up : 'a1 tree -> 'a1 ctx -> 'a1 cursor **)

let step_up focus = function
| Top -> Failed
| CLink (s, k') -> At ((Link (s, focus)), k')
| CLeft (k', r) -> At ((Node (focus, r)), k')
| CRight (l, k') -> At ((Node (l, focus)), k')

(** val zip_up : 'a1 tree -> 'a1 ctx -> 'a1 tree **)

let rec zip_up focus = function
| Top -> focus
| CLink (s, k') -> zip_up (Link (s, focus)) k'
| CLeft (k', r) -> zip_up (Node (focus, r)) k'
| CRight (l, k') -> zip_up (Node (l, focus)) k'

(** val reconstruct : 'a1 cursor -> 'a1 tree option **)

let reconstruct = function
| At (focus, k) -> Some (zip_up focus k)
| Failed -> None

(** val init : 'a1 tree -> 'a1 cursor **)

let init t =
  At (t, Top)

type 'e ut_event =
| Do of 'e
| GoLeft
| GoRight
| GoLink
| GoUp

(** val do_step :
    ('a1 -> 'a2 -> 'a1) -> 'a1 tree -> 'a1 ctx -> 'a2 -> 'a1 cursor **)

let do_step inner focus k e =
  match focus with
  | Leaf s -> At ((Leaf (inner s e)), (CLink (s, k)))
  | Link (s, t) -> At ((Leaf (inner s e)), (CRight (t, (CLink (s, k)))))
  | Node (_, _) -> Failed

(** val step :
    ('a1 -> 'a2 -> 'a1) -> 'a1 cursor -> 'a2 ut_event -> 'a1 cursor **)

let step inner c e =
  cursor_flat_map c (fun focus k ->
    match e with
    | Do ev -> do_step inner focus k ev
    | GoLeft -> step_left focus k
    | GoRight -> step_right focus k
    | GoLink -> step_link focus k
    | GoUp -> step_up focus k)

(** val is_failed : 'a1 cursor -> bool **)

let is_failed = function
| At (_, _) -> false
| Failed -> true

(** val can_go_left : 'a1 cursor -> bool **)

let can_go_left = function
| At (t, _) -> (match t with
                | Node (_, _) -> true
                | _ -> false)
| Failed -> false

(** val can_go_right : 'a1 cursor -> bool **)

let can_go_right = function
| At (t, _) -> (match t with
                | Node (_, _) -> true
                | _ -> false)
| Failed -> false

(** val can_go_link : 'a1 cursor -> bool **)

let can_go_link = function
| At (t, _) -> (match t with
                | Link (_, _) -> true
                | _ -> false)
| Failed -> false

(** val can_go_up : 'a1 cursor -> bool **)

let can_go_up = function
| At (_, c0) -> (match c0 with
                 | Top -> false
                 | _ -> true)
| Failed -> false

(** val ctx_depth : 'a1 ctx -> int **)

let rec ctx_depth = function
| Top -> 0
| CLink (_, k') -> (fun x -> x + 1) (ctx_depth k')
| CLeft (k', _) -> (fun x -> x + 1) (ctx_depth k')
| CRight (_, k') -> (fun x -> x + 1) (ctx_depth k')

(** val cursor_depth : 'a1 cursor -> int **)

let cursor_depth = function
| At (_, k) -> ctx_depth k
| Failed -> 0

(** val focus_kind : 'a1 cursor -> int **)

let focus_kind = function
| At (t, _) ->
  (match t with
   | Leaf _ -> 0
   | Link (_, _) -> (fun x -> x + 1) 0
   | Node (_, _) -> (fun x -> x + 1) ((fun x -> x + 1) 0))
| Failed -> (fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) 0))

(** val focus_value : 'a1 cursor -> 'a1 option **)

let focus_value = function
| At (t, _) ->
  (match t with
   | Leaf s -> Some s
   | Link (s, _) -> Some s
   | Node (_, _) -> None)
| Failed -> None
