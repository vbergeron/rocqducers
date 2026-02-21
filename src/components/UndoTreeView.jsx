import styles from "./UndoTreeView.module.css";

const KIND_LABELS = ["Leaf", "Link", "Node", "Failed"];
const KIND_CLASSES = ["leaf", "link", "node", "failed"];
const KIND_COLORS  = ["#16a34a", "#2563eb", "#7c3aed", "#dc2626"];

export default function UndoTreeView({
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
}) {
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
      {/* State inspector */}
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

      {/* Navigation buttons */}
      <div className={styles.controls}>
        <button
          className={styles.navButton}
          onClick={goUp}
          disabled={!canGoUp}
        >
          ↑ Up
        </button>
        <button
          className={styles.navButton}
          onClick={goLeft}
          disabled={!canGoLeft}
        >
          ← Left
        </button>
        <button
          className={styles.navButton}
          onClick={goRight}
          disabled={!canGoRight}
        >
          Right →
        </button>
        <button
          className={styles.navButton}
          onClick={goLink}
          disabled={!canGoLink}
        >
          ↓ Into link
        </button>
      </div>

      {/* Current focus display */}
      <div className={`${styles.focusBox} ${styles[kindClass]}`}>
        {focusText}
      </div>
    </div>
  );
}
