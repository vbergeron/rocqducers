
type state =
| Idle
| Loading

type event =
| Click
| Success
| Failure

(** val reducer : state -> event -> state **)

let reducer s e =
  match s with
  | Idle -> (match e with
             | Click -> Loading
             | _ -> s)
  | Loading -> (match e with
                | Click -> s
                | _ -> Idle)
