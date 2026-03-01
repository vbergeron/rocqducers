import { use_linear_history } from "@rocqducers/lib/Hooks.js";

/**
 * LinearHistoryWrapper — wraps any reducer with proven-correct linear
 * undo/redo history (UndoList.v).
 *
 * Props:
 *   reducer      {function}  (state, event) => state
 *   initialState {*}
 *   children     {function}  render prop: (state, dispatch) => node
 *
 * Proved invariants (UndoList.v):
 *   - Undo after Do always restores the previous state.
 *   - Redo after Undo always restores the state before the undo.
 *   - Do always clears the future (branching timeline).
 *   - Undo/Redo at the edges of the timeline return Failed.
 */
export default function LinearHistoryWrapper({ reducer, initialState, children }) {
  const { state, past, future, canUndo, canRedo, dispatch, undo, redo } =
    use_linear_history(reducer, initialState);

  const pastSlots   = [...past].reverse();
  const futureSlots = [...future];
  const totalSteps  = past.length + 1 + future.length;
  const currentIdx  = past.length;

  return (
    <div>
      <div className="controls">
        <button className="nav-btn" onClick={undo} disabled={!canUndo} title="Undo">
          ← Undo
        </button>
        <button className="nav-btn" onClick={redo} disabled={!canRedo} title="Redo">
          Redo →
        </button>
        <span className="ml-auto text-xs text-gray-400">
          step {currentIdx + 1} / {totalSteps}
        </span>
      </div>

      <div className="flex items-center mb-5 overflow-x-auto pb-1">
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

      {children(state, dispatch)}
    </div>
  );
}

const DOT = {
  past: "dot w-3 h-3 bg-indigo-200 border-2 border-indigo-400",
  current: "dot w-4 h-4 bg-indigo-500 border-2 border-indigo-700 shadow-[0_0_0_3px_#e0e7ff]",
  future: "dot w-3 h-3 bg-amber-100 border-2 border-amber-400",
};

const LABEL = {
  base: "text-[0.6rem] whitespace-nowrap",
  past: "text-gray-400",
  current: "text-indigo-500 font-bold",
  future: "text-amber-600",
};

function TimelineEntry({ kind, label, isFirst }) {
  return (
    <>
      {!isFirst && <div className="w-5 h-0.5 bg-gray-300 shrink-0" />}
      <div className="flex flex-col items-center gap-1 min-w-10">
        <div className={DOT[kind]} />
        <span className={`${LABEL.base} ${LABEL[kind]}`}>{label}</span>
      </div>
    </>
  );
}
