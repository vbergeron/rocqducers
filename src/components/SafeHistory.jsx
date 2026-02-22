import { PickList } from "@rocqducers/lib/Rocqducers.js";
import useHistoryReducer from "../hooks/useHistoryReducer";
import styles from "./SafeHistory.module.css";

const FRUITS = ["Apple", "Banana", "Cherry", "Date", "Elderberry"];

// Initial PickList state: "Apple" picked, rest as suggestions.
const INITIAL_STATE = PickList.init(FRUITS[0], FRUITS.slice(1));

// A plain JS reducer that wraps PickList's state-transition functions.
// useHistoryReducer accepts any (state, action) => state function here.
function pickListReducer(state, action) {
  if (action.type === "PICK")   return PickList.pick(state, action.index);
  if (action.type === "UNPICK") return PickList.unpick(state, action.index);
  return state;
}

export default function SafeHistory() {
  const { state, canUndo, canRedo, undo, redo, inner, depth } =
    useHistoryReducer(pickListReducer, INITIAL_STATE);

  const picked      = PickList.picked(state);
  const suggestions = PickList.suggestions(state);

  return (
    <div>
      {/* State inspector */}
      <div className={styles.inspector}>
        <span>history depth: <b>{depth}</b></span>
        <span>picked: <b>{picked.length}</b></span>
        <span>suggestions: <b>{suggestions.length}</b></span>
      </div>

      {/* Undo / redo */}
      <div className={styles.controls}>
        <button className={styles.historyButton} onClick={undo} disabled={!canUndo}>
          ↩ Undo
        </button>
        <button className={styles.historyButton} onClick={redo} disabled={!canRedo}>
          ↪ Redo
        </button>
      </div>

      {/* Picked / suggestions */}
      <div className={styles.lists}>
        <div className={styles.listSection}>
          <p className={styles.listTitle}>Picked</p>
          <ul className={styles.list}>
            {picked.map((item, i) => (
              <li
                key={i}
                className={styles.item}
                onClick={() => inner({ type: "UNPICK", index: i })}
              >
                {item} <span className={styles.action}>✕</span>
              </li>
            ))}
          </ul>
        </div>

        <div className={styles.listSection}>
          <p className={styles.listTitle}>Suggestions</p>
          <ul className={styles.list}>
            {suggestions.map((item, i) => (
              <li
                key={i}
                className={styles.item}
                onClick={() => inner({ type: "PICK", index: i })}
              >
                {item} <span className={styles.action}>+</span>
              </li>
            ))}
          </ul>
        </div>
      </div>
    </div>
  );
}
