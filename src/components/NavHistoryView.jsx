import styles from "./NavHistoryView.module.css";

export default function NavHistoryView({
  past,
  present,
  future,
  destinations,
  onGoBack,
  onGoForward,
  onNavigate,
}) {
  const canGoBack    = past.length > 0;
  const canGoForward = future.length > 0;

  return (
    <div className={styles.container}>

      {/* Navigation bar */}
      <div className={styles.navbar}>
        <button
          className={styles.navBtn}
          onClick={onGoBack}
          disabled={!canGoBack}
          title={canGoBack ? `Back to "${past[0]}"` : "Nothing to go back to"}
        >
          ←
        </button>

        <div className={styles.location}>{present}</div>

        <button
          className={styles.navBtn}
          onClick={onGoForward}
          disabled={!canGoForward}
          title={canGoForward ? `Forward to "${future[0]}"` : "Nothing to go forward to"}
        >
          →
        </button>
      </div>

      {/* History stacks */}
      <div className={styles.stacks}>
        <div className={styles.stack}>
          <div className={styles.stackLabel}>Past ({past.length})</div>
          {past.length === 0 ? (
            <div className={styles.empty}>—</div>
          ) : (
            past.map((item, i) => (
              <div key={i} className={styles.historyItem} style={{ opacity: 1 - i * 0.15 }}>
                {item}
              </div>
            ))
          )}
        </div>

        <div className={styles.stack}>
          <div className={styles.stackLabel}>Future ({future.length})</div>
          {future.length === 0 ? (
            <div className={styles.empty}>—</div>
          ) : (
            future.map((item, i) => (
              <div key={i} className={styles.futureItem} style={{ opacity: 1 - i * 0.15 }}>
                {item}
              </div>
            ))
          )}
        </div>
      </div>

      {/* Destinations */}
      <div className={styles.destinations}>
        <div className={styles.stackLabel}>Navigate to</div>
        <div className={styles.destRow}>
          {destinations.map((dest) => (
            <button
              key={dest}
              className={`${styles.destBtn} ${dest === present ? styles.destActive : ""}`}
              onClick={() => onNavigate(dest)}
              disabled={dest === present}
            >
              {dest}
            </button>
          ))}
        </div>
      </div>

    </div>
  );
}
