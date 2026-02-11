
type 'a state = { picked : 'a list; suggestions : 'a list }

(** val picked : 'a1 state -> 'a1 list **)

let picked s =
  s.picked

(** val suggestions : 'a1 state -> 'a1 list **)

let suggestions s =
  s.suggestions

type event =
| DoPick of int
| DoUnpick of int

(** val nth : 'a1 list -> int -> 'a1 option **)

let rec nth l n =
  match l with
  | [] -> None
  | x::t ->
    ((fun fO fS n -> if n=0 then fO () else fS (n-1))
       (fun _ -> Some x)
       (fun n' -> nth t n')
       n)

(** val remove_at : int -> 'a1 list -> 'a1 list **)

let rec remove_at i = function
| [] -> []
| h::t ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> t)
     (fun i' -> h::(remove_at i' t))
     i)

(** val mk_do_pick : int -> event **)

let mk_do_pick i =
  DoPick i

(** val mk_do_unpick : int -> event **)

let mk_do_unpick i =
  DoUnpick i

(** val do_pick : 'a1 state -> int -> 'a1 state **)

let do_pick s i =
  match nth s.suggestions i with
  | Some x ->
    { picked = (x::s.picked); suggestions = (remove_at i s.suggestions) }
  | None -> s

(** val do_unpick : 'a1 state -> int -> 'a1 state **)

let do_unpick s i =
  match s.picked with
  | [] -> s
  | _::l ->
    (match l with
     | [] -> s
     | _::_ ->
       (match nth s.picked i with
        | Some x ->
          { picked = (remove_at i s.picked); suggestions =
            (x::s.suggestions) }
        | None -> s))

(** val reducer : 'a1 state -> event -> 'a1 state **)

let reducer s = function
| DoPick i -> do_pick s i
| DoUnpick i -> do_unpick s i

(** val init_state : 'a1 -> 'a1 list -> 'a1 state **)

let init_state default rest =
  { picked = (default::[]); suggestions = rest }
