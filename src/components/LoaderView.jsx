import styles from "./LoaderView.module.css";

export default function LoaderView({
  phaseLabel, phaseColor, nextId, cached, retryCount, maxRetries,
  isLoading, isIdle, isLoaded, isErrored,
  onFetch, onRetry,
  delay, onDelayChange, shouldFail, onShouldFailChange,
}) {
  return (
    <div>
      {/* State inspector */}
      <div className={styles.inspector}>
        <span>phase: <b style={{ color: phaseColor }}>{phaseLabel}</b></span>
        <span>rid: <b>{nextId}</b></span>
        <span>cache: <b>{cached ? "Some" : "None"}</b></span>
        <span>retries: <b>{retryCount}/{maxRetries}</b></span>
      </div>

      {/* Controls */}
      <div className={styles.controls}>
        <label className={styles.controlLabel}>
          Delay
          <input type="range" min={200} max={4000} step={200} value={delay}
            onChange={e => onDelayChange(Number(e.target.value))}
            className={styles.rangeInput} />
          <span className={styles.delayValue}>
            {delay}ms
          </span>
        </label>
        <label className={styles.controlLabel}>
          <input type="checkbox" checked={shouldFail}
            onChange={e => onShouldFailChange(e.target.checked)} />
          Force error
        </label>
      </div>

      {/* Actions */}
      <div className={styles.actions}>
        <button
          onClick={onFetch}
          disabled={isLoading}
          className={`${styles.fetchButton} ${isLoading ? styles.disabled : styles.active}`}
        >
          {isIdle ? "Load Data" : "Refresh"}
        </button>
        {isErrored && (
          <button
            onClick={onRetry}
            disabled={retryCount >= maxRetries}
            className={`${styles.retryButton} ${retryCount >= maxRetries ? styles.disabled : styles.active}`}
          >
            Retry ({maxRetries - retryCount} left)
          </button>
        )}
      </div>

      {/* Content */}
      <div
        className={styles.content}
        style={{ border: `2px solid ${phaseColor}22` }}
      >
        {isIdle && (
          <p className={styles.idleText}>No data loaded yet.</p>
        )}

        {isLoading && (
          <div className={styles.loadingWrapper}>
            <div className={styles.spinner} />
            <p className={styles.loadingText}>
              Loading{retryCount > 0 ? ` (attempt ${retryCount + 1})` : ""}...
            </p>
          </div>
        )}

        {isLoaded && cached && (
          <div className={styles.loadedWrapper}>
            <h4 className={styles.loadedTitle}>{cached.title}</h4>
            <div className={styles.chipRow}>
              {cached.items.map(item => (
                <span key={item} className={styles.loadedChip}>{item}</span>
              ))}
            </div>
            <p className={styles.fetchTime}>
              Fetched at {cached.time}
            </p>
          </div>
        )}

        {isErrored && (
          <div className={styles.erroredWrapper}>
            <p className={styles.errorTitle}>
              Request failed
            </p>
            {cached ? (
              <div>
                <p className={styles.cachedLabel}>
                  Showing cached data (preserved by verified reducer):
                </p>
                <div className={styles.chipRowCenter}>
                  {cached.items.map(item => (
                    <span key={item} className={styles.erroredChip}>{item}</span>
                  ))}
                </div>
              </div>
            ) : (
              <p className={styles.noCacheText}>
                No cached data available.
              </p>
            )}
          </div>
        )}
      </div>
    </div>
  );
}
