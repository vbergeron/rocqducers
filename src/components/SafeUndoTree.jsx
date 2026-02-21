import { UndoTree } from "@rocqducers/lib/Rocqducers.js";
import useSafeUndoTree from "../hooks/useSafeUndoTree";
import UndoTreeView from "./UndoTreeView";

// Demo tree:
//
//           Node
//          /    \
//     Link "A"  Leaf "D"
//         |
//       Node
//      /    \
//  Leaf "B"  Leaf "C"

const DEMO_TREE = UndoTree.node(
  UndoTree.link("A", UndoTree.node(UndoTree.leaf("B"), UndoTree.leaf("C"))),
  UndoTree.leaf("D"),
);

const INITIAL_CURSOR = UndoTree.root_cursor(DEMO_TREE);

export default function SafeUndoTree() {
  const state = useSafeUndoTree(INITIAL_CURSOR);
  return <UndoTreeView {...state} />;
}
