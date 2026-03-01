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
    ; dispatch  = dispatch
    }]

(* useSafePickList: equivalent of src/hooks/useSafePickList.js.
   [items] is a JS array; [default_index] is the initially-picked index.
   [PickList.init] is cheap so the initial state is passed directly
   to the 2-argument form of useReducer. *)
let use_safe_pick_list items default_index =
  let default_item = items.(default_index) in
  let rest =
    List.filteri (fun i _ -> i <> default_index) (Array.to_list items)
  in
  let (state, dispatch) =
    use_reducer Extracted.PickList.reduce (Extracted.PickList.init default_item rest)
  in
  [%mel.obj
    { picked      = Array.of_list (Extracted.PickList.picked state)
    ; suggestions = Array.of_list (Extracted.PickList.suggestions state)
    ; pick        = (fun i -> Extracted.PickList.DoPick i |> dispatch)
    ; unpick      = (fun i -> Extracted.PickList.DoUnpick i |> dispatch)
    }]
