import { use_safe_pick_list } from "@rocqducers/lib/Hooks.js";
import PickListView from "./PickListView";

export default function SafePickList({ items, defaultIndex = 0 }) {
  const { picked, suggestions, pick, unpick } = use_safe_pick_list(items, defaultIndex);

  return (
    <PickListView
      pickedItems={picked}
      suggestionItems={suggestions}
      onPick={pick}
      onUnpick={unpick}
    />
  );
}
