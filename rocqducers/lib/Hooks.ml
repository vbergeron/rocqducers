(* Bind to React.useReducer.

   [@mel.uncurry] is required because OCaml functions are curried by default:
   `reducer state action` compiles to two nested single-argument JS functions.
   React calls the reducer as reducer(state, action) — a 2-argument call —
   so we annotate the callback type to force Melange to emit an uncurried
   2-argument JS function instead. *)
external use_reducer :
  (('state -> 'action -> 'state)[@mel.uncurry]) ->
  'state ->
  'state * ('action -> unit)
  = "useReducer"
  [@@mel.module "react"]

(* useSafeAsyncButton: equivalent of src/hooks/useSafeAsyncButton.js.
   Side-effect handling (async call, try/catch) stays in the JS wrapper;
   this hook manages only the reducer state. *)
let use_safe_async_button () =
  let (state, dispatch) =
    use_reducer Extracted.AsyncButton.reducer Extracted.AsyncButton.Idle
  in
  [%mel.obj
    { isIdle    = state = Extracted.AsyncButton.Idle
    ; isLoading = state = Extracted.AsyncButton.Loading
    ; click     = (fun () -> dispatch Extracted.AsyncButton.Click)
    ; succeed   = (fun () -> dispatch Extracted.AsyncButton.Success)
    ; fail      = (fun () -> dispatch Extracted.AsyncButton.Failure)
    }]

(* useLinearHistory: wraps any inner reducer with proven-correct undo/redo.
   [inner_reducer] is the wrapped pure reducer ('st -> 'ev -> 'st).
   [initial_state] is the initial inner state.
   Returns { state, past, future, canUndo, canRedo, dispatch, undo, redo }. *)
let use_linear_history inner_reducer initial_state =
  let init_state = Extracted.UndoList.init initial_state in
  let (hs, raw_dispatch) =
    use_reducer
      (fun hs e -> Extracted.UndoList.step inner_reducer hs e)
      init_state
  in
  let dispatch ev = raw_dispatch (Extracted.UndoList.mk_do ev) in
  let undo () = raw_dispatch Extracted.UndoList.mk_undo in
  let redo () = raw_dispatch Extracted.UndoList.mk_redo in
  [%mel.obj
    { state   = Extracted.UndoList.current hs
    ; past    = Array.of_list (Extracted.UndoList.past hs)
    ; future  = Array.of_list (Extracted.UndoList.future hs)
    ; canUndo = Extracted.UndoList.can_undo hs
    ; canRedo = Extracted.UndoList.can_redo hs
    ; dispatch
    ; undo
    ; redo
    }]

(* A no-op inner reducer — useful when a tree cursor is used for pure
   navigation and no Do events are dispatched. *)
let noop_reducer s _ = s

(* ── Cursor-to-JS tree reconstruction ──
   Converts a zipper cursor into a plain JS object tree for rendering.
   Each node: { kind: "leaf"|"link"|"node"|"failed", focused: bool,
                children: js_node array }. *)

type js_node

external mk_js_node :
  kind:string -> focused:bool -> children:js_node array -> js_node = ""
  [@@mel.obj]

let rec tree_to_js t =
  match t with
  | Extracted.UndoTree.Leaf _ ->
    mk_js_node ~kind:"leaf" ~focused:false ~children:[||]
  | Extracted.UndoTree.Link (_, sub) ->
    mk_js_node ~kind:"link" ~focused:false ~children:[| tree_to_js sub |]
  | Extracted.UndoTree.Node (l, r) ->
    mk_js_node ~kind:"node" ~focused:false ~children:[| tree_to_js l; tree_to_js r |]

let tree_to_js_focused t =
  match t with
  | Extracted.UndoTree.Leaf _ ->
    mk_js_node ~kind:"leaf" ~focused:true ~children:[||]
  | Extracted.UndoTree.Link (_, sub) ->
    mk_js_node ~kind:"link" ~focused:true ~children:[| tree_to_js sub |]
  | Extracted.UndoTree.Node (l, r) ->
    mk_js_node ~kind:"node" ~focused:true ~children:[| tree_to_js l; tree_to_js r |]

let rec ctx_to_js focus_js ctx =
  match ctx with
  | Extracted.UndoTree.Top -> focus_js
  | Extracted.UndoTree.CLink (_, k') ->
    ctx_to_js (mk_js_node ~kind:"link" ~focused:false ~children:[| focus_js |]) k'
  | Extracted.UndoTree.CLeft (k', r) ->
    ctx_to_js (mk_js_node ~kind:"node" ~focused:false ~children:[| focus_js; tree_to_js r |]) k'
  | Extracted.UndoTree.CRight (l, k') ->
    ctx_to_js (mk_js_node ~kind:"node" ~focused:false ~children:[| tree_to_js l; focus_js |]) k'

let cursor_to_js cursor =
  match cursor with
  | Extracted.UndoTree.At (focus, ctx) ->
    ctx_to_js (tree_to_js_focused focus) ctx
  | Extracted.UndoTree.Failed ->
    mk_js_node ~kind:"failed" ~focused:true ~children:[||]

(* useBranchingHistory: manages an UndoTree cursor with zipper navigation.
   [inner_reducer] handles Do events applied to focused node values.
   [initial_state] is the initial inner state (wrapped in a Leaf cursor).
   Returns { state, tree, isFailed, canGoLeft/Right/Link/Up, depth, focusKind,
             do_, goLeft, goRight, goLink, goUp }. *)
let use_branching_history inner_reducer initial_state =
  let initial_cursor =
    Extracted.UndoTree.init (Extracted.UndoTree.Leaf initial_state)
  in
  let (cursor, raw_dispatch) =
    use_reducer
      (fun cursor event -> Extracted.UndoTree.step inner_reducer cursor event)
      initial_cursor
  in
  let do_      ev = raw_dispatch (Extracted.UndoTree.Do ev) in
  let go_left  () = raw_dispatch Extracted.UndoTree.GoLeft in
  let go_right () = raw_dispatch Extracted.UndoTree.GoRight in
  let go_link  () = raw_dispatch Extracted.UndoTree.GoLink in
  let go_up    () = raw_dispatch Extracted.UndoTree.GoUp in
  [%mel.obj
    { state      = Extracted.UndoTree.focus_value cursor
    ; tree       = cursor_to_js cursor
    ; isFailed   = Extracted.UndoTree.is_failed cursor
    ; canGoLeft  = Extracted.UndoTree.can_go_left cursor
    ; canGoRight = Extracted.UndoTree.can_go_right cursor
    ; canGoLink  = Extracted.UndoTree.can_go_link cursor
    ; canGoUp    = Extracted.UndoTree.can_go_up cursor
    ; depth      = Extracted.UndoTree.cursor_depth cursor
    ; focusKind  = Extracted.UndoTree.focus_kind cursor
    ; do_
    ; goLeft  = go_left
    ; goRight = go_right
    ; goLink  = go_link
    ; goUp    = go_up
    }]

let pick_list_reduce = Extracted.PickList.reduce

let pick_list_init items default_index =
  let default_item = items.(default_index) in
  let rest =
    List.filteri (fun i _ -> i <> default_index) (Array.to_list items)
  in
  Extracted.PickList.init default_item rest

let pick_list_props state dispatch =
  [%mel.obj
    { picked      = Array.of_list (Extracted.PickList.picked state)
    ; suggestions = Array.of_list (Extracted.PickList.suggestions state)
    ; pick        = (fun i -> Extracted.PickList.DoPick i |> dispatch)
    ; unpick      = (fun i -> Extracted.PickList.DoUnpick i |> dispatch)
    }]

let use_safe_pick_list items default_index =
  let (state, dispatch) =
    use_reducer pick_list_reduce (pick_list_init items default_index)
  in
  pick_list_props state dispatch
