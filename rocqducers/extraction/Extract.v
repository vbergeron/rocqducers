From Stdlib Require Extraction.
From Stdlib Require Import PeanoNat.
From Rocqducers Require Import PickList.
From Rocqducers Require Loader.
From Rocqducers Require AsyncButton.
From Rocqducers Require NavHistory.

Extraction Language OCaml.

Extract Inductive nat => "int" ["0" "(fun x -> x + 1)"]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inductive list => "list" ["[]" "(::)"].
Extract Inductive option => "option" ["Some" "None"].
Extract Inductive bool => "bool" ["true" "false"]
  "(fun fT fF b -> if b then fT () else fF ())".

Extract Inlined Constant Nat.eqb => "(=)".
Extract Inlined Constant Nat.ltb => "(<)".

Separate Extraction
  PickList.reduce
  PickList.init
  PickList.do_pick
  PickList.do_unpick
  PickList.picked
  PickList.suggestions
  Loader.step Loader.init_state
  Loader.mk_fetch Loader.mk_got_response Loader.mk_got_error
  Loader.mk_timed_out Loader.mk_do_retry
  Loader.phase Loader.cache Loader.next_id Loader.retries
  Loader.is_idle Loader.is_loading Loader.loading_rid
  Loader.is_loaded Loader.is_errored
  AsyncButton.reducer
  NavHistory.step NavHistory.init
  NavHistory.mk_go_back NavHistory.mk_go_forward NavHistory.mk_navigate
  NavHistory.past NavHistory.present NavHistory.future.
