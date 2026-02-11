import styles from "./AsyncButtonView.module.css";

export default function AsyncButtonView({
  isIdle,
  isLoading,
  lastResult,
  onClick,
  delay,
  onDelayChange,
  shouldFail,
  onShouldFailChange,
}) {
  const stateLabel = isIdle ? "Idle" : "Loading";
  const stateColor = isIdle ? "#6b7280" : "#2563eb";

  return (
    <div>
      {/* State inspector */}
      <div className={styles.inspector}>
        <span>
          state: <b style={{ color: stateColor }}>{stateLabel}</b>
        </span>
        {lastResult && (
          <span>
            last:{" "}
            <b
              style={{
                color: lastResult === "success" ? "#16a34a" : "#dc2626",
              }}
            >
              {lastResult}
            </b>
          </span>
        )}
      </div>

      {/* Controls */}
      <div className={styles.controls}>
        <label className={styles.controlLabel}>
          Delay
          <input
            type="range"
            min={200}
            max={4000}
            step={200}
            value={delay}
            onChange={(e) => onDelayChange(Number(e.target.value))}
            className={styles.rangeInput}
          />
          <span className={styles.delayValue}>{delay}ms</span>
        </label>
        <label className={styles.controlLabel}>
          <input
            type="checkbox"
            checked={shouldFail}
            onChange={(e) => onShouldFailChange(e.target.checked)}
          />
          Force error
        </label>
      </div>

      {/* Button */}
      <button
        onClick={onClick}
        disabled={isLoading}
        className={`${styles.asyncButton} ${isLoading ? styles.loading : styles.idle}`}
      >
        <span className={styles.buttonContent}>
          {isLoading && <span className={styles.spinner} />}
          {isLoading ? "Working…" : "Submit"}
        </span>
      </button>

      {/* Result feedback */}
      {lastResult && isIdle && (
        <p
          className={styles.resultText}
          style={{
            color: lastResult === "success" ? "#16a34a" : "#dc2626",
          }}
        >
          {lastResult === "success"
            ? "Action completed successfully."
            : "Action failed — button returned to Idle."}
        </p>
      )}
    </div>
  );
}
