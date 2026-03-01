import { use_safe_pick_list } from "@rocqducers/lib/Hooks.js";
import PickListView from "./PickListView";

export default function SafePickList({ items, defaultIndex = 0 }) {
  return <PickListView {...use_safe_pick_list(items, defaultIndex)} />;
}
