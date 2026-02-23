import SafePickList from "./components/SafePickList";
import SafeLoader from "./components/SafeLoader";
import SafeAsyncButton from "./components/SafeAsyncButton";
import LinearHistoryWrapper from "./components/LinearHistoryWrapper";
import TreeHistoryWrapper from "./components/TreeHistoryWrapper";
import PickListView from "./components/PickListView";
import { PickList, UndoTree } from "@rocqducers/lib/Rocqducers.js";
import styles from "./App.module.css";

const FRUITS = ["Apple", "Banana", "Cherry", "Date", "Elderberry", "Fig", "Grape"];

const INITIAL_PICK_STATE = PickList.init(FRUITS[0], FRUITS.slice(1));

const DEMO_CURSOR = UndoTree.root_cursor(
  UndoTree.node(
    UndoTree.link("A", UndoTree.node(UndoTree.leaf("B"), UndoTree.leaf("C"))),
    UndoTree.leaf("D"),
  ),
);

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
        <TreeHistoryWrapper initialCursor={DEMO_CURSOR} />
      </div>

      <div className={styles.card}>
        <h3 className={styles.cardTitle}>State history (undo / redo)</h3>
        <p className={styles.cardDescription}>
          Invariants: Undo after Do always restores the previous state; Redo after Undo restores
          the undone state; a new Do always clears the redo stack; Undo/Redo are no-ops at the
          edges of the timeline.
        </p>
        <LinearHistoryWrapper reducer={PickList.reducer} initialState={INITIAL_PICK_STATE}>
          {(state, dispatch) => (
            <PickListView
              pickedItems={PickList.picked(state)}
              suggestionItems={PickList.suggestions(state)}
              onPick={(i) => dispatch(PickList.pick(i))}
              onUnpick={(i) => dispatch(PickList.unpick(i))}
            />
          )}
        </LinearHistoryWrapper>
      </div>
    </div>
  );
}
