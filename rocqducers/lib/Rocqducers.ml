module PickList = struct
  let reduce = Extracted.PickList.reduce

  let pick = Extracted.PickList.do_pick
  let unpick = Extracted.PickList.do_unpick

  let init default rest =
    Extracted.PickList.init default (Array.to_list rest)

  let picked s =
    Array.of_list (Extracted.PickList.picked s)

  let suggestions s =
    Array.of_list (Extracted.PickList.suggestions s)
end

module Loader = struct
  let step = Extracted.Loader.step
  let init = Extracted.Loader.init_state

  let fetch = Extracted.Loader.mk_fetch
  let got_response = Extracted.Loader.mk_got_response
  let got_error = Extracted.Loader.mk_got_error
  let timed_out = Extracted.Loader.mk_timed_out
  let do_retry = Extracted.Loader.mk_do_retry

  let phase s = Extracted.Loader.phase s
  let cache s = Extracted.Loader.cache s
  let next_id s = Extracted.Loader.next_id s
  let retries s = Extracted.Loader.retries s

  let is_idle = Extracted.Loader.is_idle
  let is_loading = Extracted.Loader.is_loading
  let loading_rid = Extracted.Loader.loading_rid
  let is_loaded = Extracted.Loader.is_loaded
  let is_errored = Extracted.Loader.is_errored
end

module UndoTree = struct

  let step        = Extracted.UndoTree.step
  let root_cursor = Extracted.UndoTree.root_cursor

  (* Tree constructors *)
  let leaf a   = Extracted.UndoTree.Leaf a
  let link a t = Extracted.UndoTree.Link (a, t)
  let node l r = Extracted.UndoTree.Node (l, r)

  (* Event values *)
  let ev_go_left  = Extracted.UndoTree.EvGoLeft
  let ev_go_right = Extracted.UndoTree.EvGoRight
  let ev_go_link  = Extracted.UndoTree.EvGoLink
  let ev_go_up    = Extracted.UndoTree.EvGoUp

  (* Cursor inspection (bool / int, safe from JS) *)
  let is_failed    = Extracted.UndoTree.is_failed
  let can_go_left  = Extracted.UndoTree.can_go_left
  let can_go_right = Extracted.UndoTree.can_go_right
  let can_go_link  = Extracted.UndoTree.can_go_link
  let can_go_up    = Extracted.UndoTree.can_go_up
  let focus_kind   = Extracted.UndoTree.focus_kind   (* 0=Leaf 1=Link 2=Node 3=Failed *)
  let cursor_depth = Extracted.UndoTree.cursor_depth
  let focus_value  = Extracted.UndoTree.focus_value  (* option A: None=0, Some a={TAG:0,_0:a} *)
  let commit       = Extracted.UndoTree.commit

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

module StateHistory = struct
  (** [step inner hs e] is the verified history reducer.
      [inner] is the wrapped pure reducer (S -> E -> S).
      [e] is a history event: [do_ ev], [undo], or [redo]. *)
  let step   = Extracted.StateHistory.history_step
  let init s = Extracted.StateHistory.history_init s

  (** Event constructors *)
  let do_ e = Extracted.StateHistory.mk_do e
  let undo  = Extracted.StateHistory.mk_undo
  let redo  = Extracted.StateHistory.mk_redo

  (** State accessors *)
  let current  hs = Extracted.StateHistory.current hs
  let past     hs = Array.of_list (Extracted.StateHistory.past hs)
  let future   hs = Array.of_list (Extracted.StateHistory.future hs)

  (** Boolean helpers *)
  let can_undo hs = Extracted.StateHistory.can_undo hs
  let can_redo hs = Extracted.StateHistory.can_redo hs
end