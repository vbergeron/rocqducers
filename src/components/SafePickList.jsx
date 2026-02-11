import useSafePickList from "../hooks/useSafePickList";
import PickListView from "./PickListView";

export default function SafePickList({ items, defaultIndex = 0 }) {
  const { pickedItems, suggestionItems, pick, unpick } = useSafePickList(items, defaultIndex);

  return (
    <PickListView
      pickedItems={pickedItems}
      suggestionItems={suggestionItems}
      onPick={pick}
      onUnpick={unpick}
    />
  );
}
