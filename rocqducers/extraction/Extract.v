From Stdlib Require Extraction.
From Rocqducers Require Import PickList.

Extraction Language OCaml.

Extract Inductive nat => "int" ["0" "(fun x -> x + 1)"]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inductive list => "list" ["[]" "(::)"].
Extract Inductive option => "option" ["Some" "None"].

Separate Extraction
  reducer init_state mk_do_pick mk_do_unpick picked suggestions.
