
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

val cursor_flat_map :
  'a1 cursor -> ('a1 tree -> 'a1 ctx -> 'a1 cursor) -> 'a1 cursor

val step_left : 'a1 tree -> 'a1 ctx -> 'a1 cursor

val step_right : 'a1 tree -> 'a1 ctx -> 'a1 cursor

val step_link : 'a1 tree -> 'a1 ctx -> 'a1 cursor

val step_up : 'a1 tree -> 'a1 ctx -> 'a1 cursor

val zip_up : 'a1 tree -> 'a1 ctx -> 'a1 tree

val reconstruct : 'a1 cursor -> 'a1 tree option

val init : 'a1 tree -> 'a1 cursor

type 'e ut_event =
| Do of 'e
| GoLeft
| GoRight
| GoLink
| GoUp

val do_step : ('a1 -> 'a2 -> 'a1) -> 'a1 tree -> 'a1 ctx -> 'a2 -> 'a1 cursor

val step : ('a1 -> 'a2 -> 'a1) -> 'a1 cursor -> 'a2 ut_event -> 'a1 cursor

val is_failed : 'a1 cursor -> bool

val can_go_left : 'a1 cursor -> bool

val can_go_right : 'a1 cursor -> bool

val can_go_link : 'a1 cursor -> bool

val can_go_up : 'a1 cursor -> bool

val ctx_depth : 'a1 ctx -> int

val cursor_depth : 'a1 cursor -> int

val focus_kind : 'a1 cursor -> int

val focus_value : 'a1 cursor -> 'a1 option
