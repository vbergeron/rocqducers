module PickList = struct
  let reduce = Extracted.PickList.reduce

  let pick i = Extracted.PickList.DoPick i
  let unpick i = Extracted.PickList.DoUnpick i

  let init default rest =
    Extracted.PickList.init default (Array.to_list rest)

  let picked s =
    Array.of_list (Extracted.PickList.picked s)

  let suggestions s =
    Array.of_list (Extracted.PickList.suggestions s)
end


module UndoTree = struct

  let step = Extracted.UndoTree.step
  let init = Extracted.UndoTree.init

  (* Tree constructors *)
  let leaf a   = Extracted.UndoTree.Leaf a
  let link a t = Extracted.UndoTree.Link (a, t)
  let node l r = Extracted.UndoTree.Node (l, r)

  (* Event constructors — [do_ ev] applies the inner reducer *)
  let do_ ev      = Extracted.UndoTree.Do ev
  let ev_go_left  = Extracted.UndoTree.GoLeft
  let ev_go_right = Extracted.UndoTree.GoRight
  let ev_go_link  = Extracted.UndoTree.GoLink
  let ev_go_up    = Extracted.UndoTree.GoUp

  (* Cursor inspection (bool / int, safe from JS) *)
  let is_failed    = Extracted.UndoTree.is_failed
  let can_go_left  = Extracted.UndoTree.can_go_left
  let can_go_right = Extracted.UndoTree.can_go_right
  let can_go_link  = Extracted.UndoTree.can_go_link
  let can_go_up    = Extracted.UndoTree.can_go_up
  let focus_kind   = Extracted.UndoTree.focus_kind   (* 0=Leaf 1=Link 2=Node 3=Failed *)
  let cursor_depth = Extracted.UndoTree.cursor_depth
  let focus_value  = Extracted.UndoTree.focus_value  (* option St: None=0, Some s={TAG:0,_0:s} *)

  (* String-specific label for the focused node (for demo display) *)
  let focus_label c =
    match c with
    | Extracted.UndoTree.At (Extracted.UndoTree.Leaf s, _)      -> s
    | Extracted.UndoTree.At (Extracted.UndoTree.Link (s, _), _) -> s
    | _                                                          -> ""

end

module AsyncButton = struct

  let idle = Extracted.AsyncButton.Idle
  let loading = Extracted.AsyncButton.Loading

  let click = Extracted.AsyncButton.Click
  let success = Extracted.AsyncButton.Success
  let failure = Extracted.AsyncButton.Failure

  let reducer = Extracted.AsyncButton.reducer
end

module UndoList = struct
  (** [step inner hs e] is the verified history reducer.
      [inner] is the wrapped pure reducer (St -> E -> St).
      [e] is a history event: [do_ ev], [undo], or [redo].
      Returns [Failed] when [undo] or [redo] is impossible. *)
  let step   = Extracted.UndoList.step
  let init s = Extracted.UndoList.init s

  (** Event constructors *)
  let do_ e = Extracted.UndoList.mk_do e
  let undo  = Extracted.UndoList.mk_undo
  let redo  = Extracted.UndoList.mk_redo

  (** State accessors — [current] returns [option St]; [None] when [Failed]. *)
  let current  hs = Extracted.UndoList.current hs
  let past     hs = Array.of_list (Extracted.UndoList.past hs)
  let future   hs = Array.of_list (Extracted.UndoList.future hs)

  (** Boolean helpers *)
  let is_failed hs = Extracted.UndoList.is_failed hs
  let can_undo  hs = Extracted.UndoList.can_undo hs
  let can_redo  hs = Extracted.UndoList.can_redo hs
end