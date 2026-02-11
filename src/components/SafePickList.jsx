import { useReducer, useMemo } from "react";
import { PickList } from "@rocqducers/lib/Rocqducers.js";
import PickListView from "./PickListView";

export default function SafePickList({ items, defaultIndex = 0 }) {
  const initial = useMemo(() => {
    const defaultItem = items[defaultIndex];
    const rest = items.filter((_, i) => i !== defaultIndex);
    return PickList.init(defaultItem, rest);
  }, [items, defaultIndex]);

  const [state, dispatch] = useReducer(PickList.reducer, initial);

  return (
    <PickListView
      pickedItems={PickList.picked(state)}
      suggestionItems={PickList.suggestions(state)}
      onPick={(i) => dispatch(PickList.pick(i))}
      onUnpick={(i) => dispatch(PickList.unpick(i))}
    />
  );
}
