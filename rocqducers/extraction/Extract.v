From Stdlib Require Extraction.
From Stdlib Require Import PeanoNat.
From Rocqducers Require Import PickList.
From Rocqducers Require AsyncButton.
From Rocqducers Require UndoTree.
From Rocqducers Require UndoList.

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
  AsyncButton.reducer
  UndoTree.step
  UndoTree.init
  UndoTree.reconstruct
  UndoTree.is_failed
  UndoTree.can_go_left
  UndoTree.can_go_right
  UndoTree.can_go_link
  UndoTree.can_go_up
  UndoTree.focus_kind
  UndoTree.cursor_depth
  UndoTree.focus_value
  UndoList.step UndoList.init
  UndoList.mk_do UndoList.mk_undo UndoList.mk_redo
  UndoList.current UndoList.past UndoList.future
  UndoList.can_undo UndoList.can_redo UndoList.is_failed.
