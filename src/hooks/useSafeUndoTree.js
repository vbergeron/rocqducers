import { useReducer, useCallback } from "react";
import { UndoTree } from "@rocqducers/lib/Rocqducers.js";

export default function useSafeUndoTree(initialCursor) {
  const [cursor, dispatch] = useReducer(UndoTree.step, initialCursor);

  const isFailed    = UndoTree.is_failed(cursor);
  const canGoLeft   = UndoTree.can_go_left(cursor);
  const canGoRight  = UndoTree.can_go_right(cursor);
  const canGoLink   = UndoTree.can_go_link(cursor);
  const canGoUp     = UndoTree.can_go_up(cursor);
  const depth       = UndoTree.cursor_depth(cursor);
  const focusKind   = UndoTree.focus_kind(cursor); // 0=Leaf 1=Link 2=Node 3=Failed
  const focusLabel  = UndoTree.focus_label(cursor);

  const goLeft  = useCallback(() => dispatch(UndoTree.ev_go_left),  []);
  const goRight = useCallback(() => dispatch(UndoTree.ev_go_right), []);
  const goLink  = useCallback(() => dispatch(UndoTree.ev_go_link),  []);
  const goUp    = useCallback(() => dispatch(UndoTree.ev_go_up),    []);

  return {
    isFailed,
    canGoLeft,
    canGoRight,
    canGoLink,
    canGoUp,
    depth,
    focusKind,
    focusLabel,
    goLeft,
    goRight,
    goLink,
    goUp,
  };
}
