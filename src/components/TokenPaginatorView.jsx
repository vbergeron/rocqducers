import styles from "./TokenPaginatorView.module.css";

export default function TokenPaginatorView({
  phaseLabel, phaseColor,
  data, backDepth,
  isIdle, isLoading, isLoaded, isErrored,
  hasNext, canGoBack,
  onFetch, onNext, onPrev,
}) {
  const pageNum = backDepth + 1;

  return (
    <div>
      {/* State inspector */}
      <div className={styles.inspector}>
        <span>phase: <b style={{ color: phaseColor }}>{phaseLabel}</b></span>
        <span>page: <b>{isLoaded || isLoading ? pageNum : "—"}</b></span>
        <span>back_stack: <b>[{Array(backDepth).fill("·").join(", ")}]</b></span>
        <span>has_next: <b>{String(hasNext)}</b></span>
        <span>can_go_back: <b>{String(canGoBack)}</b></span>
      </div>

      {/* Navigation controls */}
      <div className={styles.actions}>
        <button
          onClick={onPrev}
          disabled={!canGoBack}
          className={`${styles.navButton} ${canGoBack ? styles.active : styles.disabled}`}
        >
          ← Prev
        </button>
        <button
          onClick={onNext}
          disabled={!hasNext}
          className={`${styles.navButton} ${hasNext ? styles.active : styles.disabled}`}
        >
          Next →
        </button>
        <button
          onClick={onFetch}
          disabled={isLoading}
          className={`${styles.fetchButton} ${isLoading ? styles.disabled : styles.active}`}
        >
          Reload
        </button>
        {(isLoaded || isLoading) && (
          <span className={styles.pageIndicator}>
            page {pageNum}{!hasNext && isLoaded ? " (last)" : ""}
          </span>
        )}
      </div>

      {/* Content area */}
      <div
        className={styles.content}
        style={{ border: `2px solid ${phaseColor}22` }}
      >
        {isIdle && (
          <p className={styles.idleText}>Press Reload to load the first page.</p>
        )}

        {isLoading && (
          <div className={styles.loadingWrapper}>
            <div className={styles.spinner} />
            <p className={styles.loadingText}>Loading page {pageNum}…</p>
          </div>
        )}

        {isLoaded && data && (
          <div className={styles.loadedWrapper}>
            <p className={styles.loadedTitle}>{data.category}</p>
            <div className={styles.chipRow}>
              {data.items.map(item => (
                <span key={item} className={styles.chip}>{item}</span>
              ))}
            </div>
          </div>
        )}

        {isErrored && (
          <div className={styles.erroredWrapper}>
            <p className={styles.errorTitle}>Request failed</p>
          </div>
        )}
      </div>
    </div>
  );
}
