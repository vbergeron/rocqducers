import { useReducer, useMemo } from "react";
import { PickList } from "@rocqducers/lib/Rocqducers.js";

export default function useSafePickList(items, defaultIndex = 0) {
  const initial = useMemo(() => {
    const defaultItem = items[defaultIndex];
    const rest = items.filter((_, i) => i !== defaultIndex);
    return PickList.init(defaultItem, rest);
  }, [items, defaultIndex]);

  const [state, dispatch] = useReducer(PickList.reducer, initial);

  return {
    pickedItems: PickList.picked(state),
    suggestionItems: PickList.suggestions(state),
    pick: (i) => dispatch(PickList.pick(i)),
    unpick: (i) => dispatch(PickList.unpick(i)),
  };
}
