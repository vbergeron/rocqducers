import { useReducer, useCallback } from "react";
import { UndoTree } from "@rocqducers/lib/Rocqducers.js";
import styles from "./TreeHistoryWrapper.module.css";

/**
 * TreeHistoryWrapper — wraps an UndoTree cursor with tree-zipper navigation
 * (UndoTree.v).
 *
 * Props:
 *   initialCursor {cursor}  initial UndoTree cursor (e.g. UndoTree.root_cursor(...))
 *
 * Proved invariants (UndoTree.v):
 *   - go_left + go_up is a round-trip.
 *   - Failed absorbs all navigation.
 *   - cursor depth is non-negative.
 */
export default function TreeHistoryWrapper({ initialCursor }) {
  const [cursor, dispatch] = useReducer(UndoTree.step, initialCursor);

  const isFailed   = UndoTree.is_failed(cursor);
  const canGoLeft  = UndoTree.can_go_left(cursor);
  const canGoRight = UndoTree.can_go_right(cursor);
  const canGoLink  = UndoTree.can_go_link(cursor);
  const canGoUp    = UndoTree.can_go_up(cursor);
  const depth      = UndoTree.cursor_depth(cursor);
  const focusKind  = UndoTree.focus_kind(cursor);
  const focusLabel = UndoTree.focus_label(cursor);

  const goLeft  = useCallback(() => dispatch(UndoTree.ev_go_left),  []);
  const goRight = useCallback(() => dispatch(UndoTree.ev_go_right), []);
  const goLink  = useCallback(() => dispatch(UndoTree.ev_go_link),  []);
  const goUp    = useCallback(() => dispatch(UndoTree.ev_go_up),    []);

  const KIND_LABELS  = ["Leaf", "Link", "Node", "Failed"];
  const KIND_CLASSES = ["leaf", "link", "node", "failed"];
  const KIND_COLORS  = ["#16a34a", "#2563eb", "#7c3aed", "#dc2626"];

  const kindName  = KIND_LABELS[focusKind]  ?? "?";
  const kindClass = KIND_CLASSES[focusKind] ?? "failed";
  const kindColor = KIND_COLORS[focusKind]  ?? "#9ca3af";

  const focusText =
    focusKind === 0 ? `Leaf "${focusLabel}"` :
    focusKind === 1 ? `Link "${focusLabel}"` :
    focusKind === 2 ? "Node" :
    "Failed";

  return (
    <div>
      <div className={styles.inspector}>
        <span>
          focus: <b style={{ color: kindColor }}>{kindName}</b>
        </span>
        {focusKind !== 2 && focusKind !== 3 && (
          <span>
            value: <b style={{ color: kindColor }}>&ldquo;{focusLabel}&rdquo;</b>
          </span>
        )}
        <span>
          depth: <b>{depth}</b>
        </span>
        <span>
          failed: <b style={{ color: isFailed ? "#dc2626" : "#6b7280" }}>
            {isFailed ? "true" : "false"}
          </b>
        </span>
      </div>

      <div className={styles.controls}>
        <button className={styles.navButton} onClick={goUp} disabled={!canGoUp}>
          ↑ Up
        </button>
        <button className={styles.navButton} onClick={goLeft} disabled={!canGoLeft}>
          ← Left
        </button>
        <button className={styles.navButton} onClick={goRight} disabled={!canGoRight}>
          Right →
        </button>
        <button className={styles.navButton} onClick={goLink} disabled={!canGoLink}>
          ↓ Into link
        </button>
      </div>

      <div className={`${styles.focusBox} ${styles[kindClass]}`}>
        {focusText}
      </div>
    </div>
  );
}
