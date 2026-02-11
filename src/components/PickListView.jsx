import styles from "./PickListView.module.css";

export default function PickListView({ pickedItems, suggestionItems, onPick, onUnpick }) {
  const canUnpick = pickedItems.length > 1;

  return (
    <div className={styles.container}>
      <div className={styles.section}>
        <h4 className={styles.pickedTitle}>
          Picked ({pickedItems.length})
        </h4>
        <div className={styles.chipRow}>
          {pickedItems.map((item, i) => (
            <button
              key={item}
              onClick={() => onUnpick(i)}
              className={`${styles.pickedChip} ${canUnpick ? styles.canUnpick : styles.locked}`}
              title={canUnpick ? "Click to remove" : "Cannot remove last item"}
            >
              {item} ✕
            </button>
          ))}
        </div>
      </div>
      <div>
        <h4 className={styles.suggestionsTitle}>
          Suggestions ({suggestionItems.length})
        </h4>
        <div className={styles.chipRow}>
          {suggestionItems.map((item, i) => (
            <button
              key={item}
              onClick={() => onPick(i)}
              className={styles.suggestionChip}
            >
              + {item}
            </button>
          ))}
        </div>
      </div>
    </div>
  );
}
