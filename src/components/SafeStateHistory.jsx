import { useMemo } from "react";
import { PickList } from "@rocqducers/lib/Rocqducers.js";
import useSafeStateHistory from "../hooks/useSafeStateHistory";
import PickListView from "./PickListView";
import StateHistoryView from "./StateHistoryView";

const FRUITS = ["Apple", "Banana", "Cherry", "Date", "Elderberry", "Fig", "Grape"];

// A plain JS reducer wrapping PickList's state-transition functions.
function pickListReducer(state, action) {
  if (action.type === "PICK")   return PickList.pick(state, action.index);
  if (action.type === "UNPICK") return PickList.unpick(state, action.index);
  return state;
}

/**
 * SafeStateHistory — demonstrates the verified StateHistory wrapper
 * applied to the PickList reducer.
 *
 * The history is backed by UndoTree.cursor, with linear commit semantics
 * proved in StateHistory.v:
 *   - Every action creates a reachable undo point.
 *   - Committing always clears the redo stack.
 *   - Undo after Do recovers the previous state exactly.
 *   - Undo followed by Redo is the identity.
 */
export default function SafeStateHistory() {
  const initialState = useMemo(() => {
    const [head, ...rest] = FRUITS;
    return PickList.init(head, rest);
  }, []);

  const { state, past, future, canUndo, canRedo, undo, redo, inner } =
    useSafeStateHistory(pickListReducer, initialState);

  const pickedItems     = PickList.picked(state);
  const suggestionItems = PickList.suggestions(state);

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
        onPick={(i)   => inner({ type: "PICK",   index: i })}
        onUnpick={(i) => inner({ type: "UNPICK", index: i })}
      />
    </StateHistoryView>
  );
}
