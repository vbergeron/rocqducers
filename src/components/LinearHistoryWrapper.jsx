import { useReducer, useCallback } from "react";
import { StateHistory } from "@rocqducers/lib/Rocqducers.js";
import styles from "./LinearHistoryWrapper.module.css";

/**
 * LinearHistoryWrapper — wraps any reducer with proven-correct linear
 * undo/redo history (StateHistory.v).
 *
 * Props:
 *   reducer      {function}  (state, event) => state
 *   initialState {*}
 *   children     {function}  render prop: (state, dispatch) => node
 *
 * Proved invariants (StateHistory.v):
 *   - Undo after Do always restores the previous state.
 *   - Redo after Undo always restores the state before the undo.
 *   - Do always clears the future (branching timeline).
 *   - Undo/Redo are no-ops at the edges of the timeline.
 */
export default function LinearHistoryWrapper({ reducer, initialState, children }) {
  const historyReducer = useCallback(
    (hs, e) => StateHistory.step(reducer, hs, e),
    [reducer],
  );

  const [histState, dispatch] = useReducer(
    historyReducer,
    initialState,
    StateHistory.init,
  );

  const state   = StateHistory.current(histState);
  const past    = StateHistory.past(histState);
  const future  = StateHistory.future(histState);
  const canUndo = StateHistory.can_undo(histState);
  const canRedo = StateHistory.can_redo(histState);

  const doDispatch = useCallback((ev) => dispatch(StateHistory.do_(ev)), []);
  const undo = useCallback(() => dispatch(StateHistory.undo), []);
  const redo = useCallback(() => dispatch(StateHistory.redo), []);

  const pastSlots  = [...past].reverse();
  const futureSlots = [...future];
  const totalSteps  = past.length + 1 + future.length;
  const currentIdx  = past.length;

  return (
    <div className={styles.container}>
      <div className={styles.controls}>
        <button className={styles.btn} onClick={undo} disabled={!canUndo} title="Undo">
          ← Undo
        </button>
        <button className={styles.btn} onClick={redo} disabled={!canRedo} title="Redo">
          Redo →
        </button>
        <span className={styles.stepCount}>
          step {currentIdx + 1} / {totalSteps}
        </span>
      </div>

      <div className={styles.timeline}>
        {pastSlots.map((_, i) => (
          <TimelineEntry
            key={`past-${i}`}
            kind="past"
            label={`-${past.length - i}`}
            isFirst={i === 0}
          />
        ))}
        <TimelineEntry kind="current" label="now" isFirst={past.length === 0} />
        {futureSlots.map((_, i) => (
          <TimelineEntry
            key={`future-${i}`}
            kind="future"
            label={`+${i + 1}`}
            isFirst={false}
          />
        ))}
      </div>

      {children(state, doDispatch)}
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
