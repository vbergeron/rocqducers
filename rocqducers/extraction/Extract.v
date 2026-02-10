From Stdlib Require Extraction.
From Stdlib Require Import PeanoNat.
From Rocqducers Require Import PickList.
From Rocqducers Require Loader.

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
  reducer init_state mk_do_pick mk_do_unpick picked suggestions
  Loader.step Loader.init_state
  Loader.mk_fetch Loader.mk_got_response Loader.mk_got_error
  Loader.mk_timed_out Loader.mk_do_retry
  Loader.phase Loader.cache Loader.next_id Loader.retries
  Loader.is_idle Loader.is_loading Loader.loading_rid
  Loader.is_loaded Loader.is_errored.
