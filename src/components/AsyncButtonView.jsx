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
  const stateColor = isIdle ? "text-gray-500" : "text-blue-600";

  return (
    <div>
      <div className="controls px-3 py-2.5 bg-gray-50 rounded-lg text-xs font-mono">
        <span>
          state: <b className={stateColor}>{stateLabel}</b>
        </span>
        {lastResult && (
          <span>
            last:{" "}
            <b className={lastResult === "success" ? "text-green-600" : "text-red-600"}>
              {lastResult}
            </b>
          </span>
        )}
      </div>

      <div className="controls">
        <label className="text-xs flex items-center gap-1">
          Delay
          <input
            type="range"
            min={200}
            max={4000}
            step={200}
            value={delay}
            onChange={(e) => onDelayChange(Number(e.target.value))}
            className="w-20"
          />
          <span className="font-mono text-xs min-w-14">{delay}ms</span>
        </label>
        <label className="text-xs flex items-center gap-1">
          <input
            type="checkbox"
            checked={shouldFail}
            onChange={(e) => onShouldFailChange(e.target.checked)}
          />
          Force error
        </label>
      </div>

      <button
        onClick={onClick}
        disabled={isLoading}
        className={`px-6 py-2 rounded-lg border-none text-white font-medium text-sm min-w-36 transition-all ${
          isLoading
            ? "bg-gray-300 cursor-not-allowed"
            : "bg-blue-600 cursor-pointer hover:bg-blue-700"
        }`}
      >
        <span className="inline-flex items-center gap-1.5">
          {isLoading && (
            <span className="inline-block w-3.5 h-3.5 border-2 border-gray-400 border-t-white rounded-full animate-spin" />
          )}
          {isLoading ? "Working…" : "Submit"}
        </span>
      </button>

      {lastResult && isIdle && (
        <p className={`text-sm mt-3 ${lastResult === "success" ? "text-green-600" : "text-red-600"}`}>
          {lastResult === "success"
            ? "Action completed successfully."
            : "Action failed — button returned to Idle."}
        </p>
      )}
    </div>
  );
}
