import SafePickList from "./components/SafePickList";
import SafeLoader from "./components/SafeLoader";
import SafeAsyncButton from "./components/SafeAsyncButton";
import SafeUndoTree from "./components/SafeUndoTree";
import SafeHistory from "./components/SafeHistory";
import SafeStateHistory from "./components/SafeStateHistory";
import styles from "./App.module.css";

const FRUITS = ["Apple", "Banana", "Cherry", "Date", "Elderberry", "Fig", "Grape"];

export default function App() {
  return (
    <div className={styles.container}>
      <h1 className={styles.title}>Rocqducers</h1>
      <p className={styles.subtitle}>
        React components powered by verified Rocq reducers.
      </p>

      <div className={styles.card}>
        <h3 className={styles.cardTitle}>Pick your fruits</h3>
        <p className={styles.cardDescription}>
          Invariants: at least one fruit is always picked, and the total count never changes.
        </p>
        <SafePickList items={FRUITS} defaultIndex={0} />
      </div>

      <div className={styles.card}>
        <h3 className={styles.cardTitle}>Network loader</h3>
        <p className={styles.cardDescription}>
          Invariants: loaded implies data present, error preserves cache, stale responses ignored, retry bounded.
        </p>
        <SafeLoader />
      </div>

      <div className={styles.card}>
        <h3 className={styles.cardTitle}>Async button</h3>
        <p className={styles.cardDescription}>
          Invariants: clicks are ignored while loading, success and failure always return to idle.
        </p>
        <SafeAsyncButton />
      </div>

      <div className={styles.card}>
        <h3 className={styles.cardTitle}>Undo tree</h3>
        <p className={styles.cardDescription}>
          Invariants: go_left + go_up is a round-trip, Failed absorbs all navigation, cursor depth is non-negative.
        </p>
        <SafeUndoTree />
      </div>

      <div className={styles.card}>
        <h3 className={styles.cardTitle}>History reducer</h3>
        <p className={styles.cardDescription}>
          Any reducer wrapped with UndoTree history. Pick and unpick fruits — every action is a commit you can undo and redo.
        </p>
        <SafeHistory />
      </div>

      <div className={styles.card}>
        <h3 className={styles.cardTitle}>State history (undo / redo)</h3>
        <p className={styles.cardDescription}>
          Invariants: Undo after Do always restores the previous state; Redo after Undo restores
          the undone state; a new Do always clears the redo stack; Undo/Redo are no-ops at the
          edges of the timeline.
        </p>
        <SafeStateHistory />
      </div>
    </div>
  );
}
