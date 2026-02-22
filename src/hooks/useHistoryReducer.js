import { useReducer, useCallback, useRef } from "react";
import { UndoTree } from "@rocqducers/lib/Rocqducers.js";

// In Melange, OCaml's option is: None → 0 (falsy), Some a → { TAG: 0, _0: a } (truthy).
function unwrap(opt, fallback) {
  return opt ? opt._0 : fallback;
}

/**
 * useHistoryReducer — wraps any reducer with branching undo/redo history.
 *
 * The full history is stored as a UndoTree cursor whose node values are
 * states of the inner reducer. Navigation maps to undo/redo:
 *
 *   go_up   → undo (move to the Link node that holds the previous state)
 *   go_link → redo (descend back to the Leaf that holds the next state)
 *   commit  → record a new state as a fresh Leaf, archiving the current one
 *
 * Proved invariants inherited from UndoTree.v:
 *   - commit_undo_leaf:      undo after commit recovers the previous state
 *   - commit_undo_redo_leaf: undo + redo is the identity
 *   - commit_can_go_up:      every commit creates a reachable undo point
 *
 * @param {function} innerReducer  (state, action) => state
 * @param {*}        initialState  initial inner reducer state
 */
export default function useHistoryReducer(innerReducer, initialState) {
  // Keep innerReducer in a ref so the dispatch closure never goes stale.
  const innerRef = useRef(innerReducer);
  innerRef.current = innerReducer;

  const [cursor, dispatch] = useReducer(
    (cursor, action) => {
      if (action.type === "UNDO") return UndoTree.step(cursor, UndoTree.ev_go_up);
      if (action.type === "REDO") return UndoTree.step(cursor, UndoTree.ev_go_link);
      // INNER: advance the inner reducer and commit the new state into history.
      const current = unwrap(UndoTree.focus_value(cursor), initialState);
      const next    = innerRef.current(current, action.event);
      return UndoTree.commit(next, cursor);
    },
    initialState,
    (s) => UndoTree.root_cursor(UndoTree.leaf(s)),
  );

  const state   = unwrap(UndoTree.focus_value(cursor), initialState);
  const canUndo = UndoTree.can_go_up(cursor);
  const canRedo = UndoTree.can_go_link(cursor);
  const depth   = UndoTree.cursor_depth(cursor);

  const undo  = useCallback(() => dispatch({ type: "UNDO" }), []);
  const redo  = useCallback(() => dispatch({ type: "REDO" }), []);
  const inner = useCallback((event) => dispatch({ type: "INNER", event }), []);

  return { state, canUndo, canRedo, undo, redo, inner, depth };
}
