From Stdlib Require Import List.

Import ListNotations.

Inductive state :=
| Idle
| Loading.

Inductive event :=
| Click
| Success
| Failure.

Definition reducer (s : state) (e : event) : state := 
  match s, e with
  | Idle, Click => Loading
  | Loading, Success => Idle
  | Loading, Failure => Idle
  | _, _ => s
  end.

Theorem click_on_loading_is_ignored :
  reducer Loading Click = Loading.
Proof.
  simpl. 
  reflexivity.
Qed.



