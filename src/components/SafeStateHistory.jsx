import { useMemo } from "react";
import { PickList } from "@rocqducers/lib/Rocqducers.js";
import useSafeStateHistory from "../hooks/useSafeStateHistory";
import PickListView from "./PickListView";
import StateHistoryView from "./StateHistoryView";

const FRUITS = ["Apple", "Banana", "Cherry", "Date", "Elderberry", "Fig", "Grape"];

/**
 * SafeStateHistory — demonstrates the verified StateHistory wrapper
 * applied to the PickList reducer.
 *
 * The history invariants proved in StateHistory.v guarantee:
 *   - Undo after Do always restores the previous state exactly.
 *   - Redo after Undo always restores the state before the undo.
 *   - Doing a new action always clears the redo stack.
 *   - Undo/Redo are no-ops at the edges of the timeline.
 */
export default function SafeStateHistory() {
  const initialState = useMemo(() => {
    const [head, ...rest] = FRUITS;
    return PickList.init(head, rest);
  }, []);

  const {
    state,
    past,
    future,
    canUndo,
    canRedo,
    dispatch,
    undo,
    redo,
  } = useSafeStateHistory(PickList.reducer, initialState);

  const pickedItems      = PickList.picked(state);
  const suggestionItems  = PickList.suggestions(state);

  return (
    <StateHistoryView
      canUndo={canUndo}
      canRedo={canRedo}
      onUndo={undo}
      onRedo={redo}
      past={past}
      future={future}
    >
      <PickListView
        pickedItems={pickedItems}
        suggestionItems={suggestionItems}
        onPick={(i)   => dispatch(PickList.pick(i))}
        onUnpick={(i) => dispatch(PickList.unpick(i))}
      />
    </StateHistoryView>
  );
}
