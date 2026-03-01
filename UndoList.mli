
type 'st state =
| Hist of 'st * 'st list * 'st list
| Failed

type 'e event =
| Do of 'e
| Undo
| Redo

val current : 'a1 state -> 'a1 option

val past : 'a1 state -> 'a1 list

val future : 'a1 state -> 'a1 list

val flat_map :
  'a1 state -> ('a1 -> 'a1 list -> 'a1 list -> 'a1 state) -> 'a1 state

val init : 'a1 -> 'a1 state

val step : ('a1 -> 'a2 -> 'a1) -> 'a1 state -> 'a2 event -> 'a1 state

val is_failed : 'a1 state -> bool

val can_undo : 'a1 state -> bool

val can_redo : 'a1 state -> bool

val mk_do : 'a1 -> 'a1 event

val mk_undo : 'a1 event

val mk_redo : 'a1 event
