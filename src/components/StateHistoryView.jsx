import styles from "./StateHistoryView.module.css";

/**
 * StateHistoryView — renders the undo/redo controls and a visual
 * timeline on top of any child component.
 *
 * Props:
 *   canUndo  {boolean}
 *   canRedo  {boolean}
 *   onUndo   {function}
 *   onRedo   {function}
 *   past     {Array}   — history of past states, most-recent-first
 *   future   {Array}   — history of future states, most-recent-first
 *   children {node}    — the wrapped inner component
 */
export default function StateHistoryView({
  canUndo,
  canRedo,
  onUndo,
  onRedo,
  past,
  future,
  children,
}) {
  // Build the timeline: [oldest-past, ..., most-recent-past, CURRENT, next-future, ..., furthest-future]
  const pastSlots   = [...past].reverse();   // oldest first
  const futureSlots = [...future];           // next-to-redo first

  const totalSteps  = past.length + 1 + future.length;
  const currentIdx  = past.length;           // 0-based index of the current state

  return (
    <div className={styles.container}>

      {/* Controls */}
      <div className={styles.controls}>
        <button
          className={styles.btn}
          onClick={onUndo}
          disabled={!canUndo}
          title="Undo"
        >
          ← Undo
        </button>
        <button
          className={styles.btn}
          onClick={onRedo}
          disabled={!canRedo}
          title="Redo"
        >
          Redo →
        </button>
        <span className={styles.stepCount}>
          step {currentIdx + 1} / {totalSteps}
        </span>
      </div>

      {/* Timeline */}
      <div className={styles.timeline}>
        {pastSlots.map((_, i) => (
          <TimelineEntry
            key={`past-${i}`}
            kind="past"
            label={`-${past.length - i}`}
            isFirst={i === 0}
          />
        ))}

        {/* Current state */}
        <TimelineEntry
          kind="current"
          label="now"
          isFirst={past.length === 0}
        />

        {futureSlots.map((_, i) => (
          <TimelineEntry
            key={`future-${i}`}
            kind="future"
            label={`+${i + 1}`}
            isFirst={false}
          />
        ))}
      </div>

      {/* Inner component */}
      {children}
    </div>
  );
}

function TimelineEntry({ kind, label, isFirst }) {
  const dotClass = [
    styles.timelineDot,
    kind === "past"    ? styles.past    : "",
    kind === "current" ? styles.current : "",
    kind === "future"  ? styles.future  : "",
  ].join(" ");

  const labelClass = [
    styles.timelineLabel,
    kind === "current" ? styles.currentLabel : "",
    kind === "future"  ? styles.futureLabel  : "",
  ].join(" ");

  return (
    <>
      {!isFirst && <div className={styles.timelineConnector} />}
      <div className={styles.timelineCell}>
        <div className={dotClass} />
        <span className={labelClass}>{label}</span>
      </div>
    </>
  );
}
