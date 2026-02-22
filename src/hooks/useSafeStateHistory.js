import { useReducer, useCallback } from "react";
import { StateHistory } from "@rocqducers/lib/Rocqducers.js";

/**
 * useSafeStateHistory — wraps any verified Rocq reducer with undo/redo.
 *
 * The history management itself is proved correct in StateHistory.v:
 *   - Undo after Do always restores the previous current state.
 *   - Redo after Undo always restores the state before the undo.
 *   - Do always clears the future (branching timeline).
 *   - Undo/Redo are no-ops at the edges of the timeline.
 *
 * @param {function} innerReducer  - The inner pure reducer (state, event) => state
 * @param {*}        initialState  - The initial inner state
 * @returns {{ state, past, future, canUndo, canRedo, dispatch, undo, redo }}
 */
export default function useSafeStateHistory(innerReducer, initialState) {
  // The React reducer drives the history_step with the inner reducer curried in.
  const historyReducer = useCallback(
    (hs, e) => StateHistory.step(innerReducer, hs, e),
    [innerReducer]
  );

  const [histState, dispatch] = useReducer(
    historyReducer,
    initialState,
    StateHistory.init
  );

  const state    = StateHistory.current(histState);
  const past     = StateHistory.past(histState);    // Array, most-recent-first
  const future   = StateHistory.future(histState);  // Array, most-recent-first
  const canUndo  = StateHistory.can_undo(histState);
  const canRedo  = StateHistory.can_redo(histState);

  return {
    state,
    past,
    future,
    canUndo,
    canRedo,
    /** Dispatch an inner event, wrapped in a Do history event. */
    dispatch: useCallback((ev) => dispatch(StateHistory.do_(ev)), []),
    undo:     useCallback(() => dispatch(StateHistory.undo), []),
    redo:     useCallback(() => dispatch(StateHistory.redo), []),
  };
}
