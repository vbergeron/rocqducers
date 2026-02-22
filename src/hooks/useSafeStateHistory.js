import { useReducer, useCallback, useRef } from "react";
import { UndoTree, StateHistory } from "@rocqducers/lib/Rocqducers.js";

// In Melange, OCaml's option is: None → 0 (falsy), Some a → { TAG: 0, _0: a } (truthy).
function unwrap(opt, fallback) {
  return opt ? opt._0 : fallback;
}

/**
 * useSafeStateHistory — wraps any reducer with linear undo/redo history.
 *
 * The history is stored as a UndoTree cursor whose node values are inner
 * states. Navigation maps to undo/redo:
 *
 *   go_up   → undo (move to the CLink breadcrumb holding the previous state)
 *   go_link → redo (descend to the Leaf holding the next state)
 *   sh_commit → record a new state, discarding forward history (linear)
 *
 * Proved invariants from StateHistory.v:
 *   - sh_commit_can_undo:      every commit creates a reachable undo point
 *   - sh_commit_clears_redo:   committing always clears the redo stack
 *   - sh_undo_after_commit:    undo after commit recovers the previous state
 *   - sh_undo_redo:            undo + redo is the identity
 *
 * @param {function} innerReducer  (state, action) => state
 * @param {*}        initialState  initial inner state
 */
export default function useSafeStateHistory(innerReducer, initialState) {
  // Keep innerReducer in a ref so the dispatch closure never goes stale.
  const innerRef = useRef(innerReducer);
  innerRef.current = innerReducer;

  const [cursor, dispatch] = useReducer(
    (cursor, action) => {
      if (action.type === "UNDO") return UndoTree.step(cursor, UndoTree.ev_go_up);
      if (action.type === "REDO") return UndoTree.step(cursor, UndoTree.ev_go_link);
      // INNER: advance the inner reducer and commit with linear (clearing) history.
      const current = unwrap(UndoTree.focus_value(cursor), initialState);
      const next    = innerRef.current(current, action.event);
      return StateHistory.commit(next, cursor);
    },
    initialState,
    (s) => UndoTree.root_cursor(UndoTree.leaf(s)),
  );

  const state   = unwrap(UndoTree.focus_value(cursor), initialState);
  const canUndo = UndoTree.can_go_up(cursor);
  const canRedo = UndoTree.can_go_link(cursor);

  // Build arrays whose length encodes timeline depth (values unused by view).
  const past   = Array.from({ length: UndoTree.cursor_depth(cursor) });
  const future = Array.from({ length: StateHistory.future_depth(cursor) });

  const undo  = useCallback(() => dispatch({ type: "UNDO" }), []);
  const redo  = useCallback(() => dispatch({ type: "REDO" }), []);
  const inner = useCallback((event) => dispatch({ type: "INNER", event }), []);

  return { state, canUndo, canRedo, undo, redo, inner, past, future };
}
