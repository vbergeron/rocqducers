
type 'a state = { picked : 'a list; suggestions : 'a list }

val picked : 'a1 state -> 'a1 list

val suggestions : 'a1 state -> 'a1 list

type event =
| DoPick of int
| DoUnpick of int

val nth : 'a1 list -> int -> 'a1 option

val remove_at : int -> 'a1 list -> 'a1 list

val do_pick : 'a1 state -> int -> 'a1 state

val do_unpick : 'a1 state -> int -> 'a1 state

val reduce : 'a1 state -> event -> 'a1 state

val init : 'a1 -> 'a1 list -> 'a1 state
