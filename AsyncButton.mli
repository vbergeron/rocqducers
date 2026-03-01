
type state =
| Idle
| Loading

type event =
| Click
| Success
| Failure

val reducer : state -> event -> state
