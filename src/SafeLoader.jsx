import { useReducer, useEffect, useRef, useState } from "react";
import { Loader } from "@rocqducers/lib/Rocqducers.js";

const MAX_RETRIES = 3;
const TIMEOUT_MS = 5000;

const DATASETS = [
  { title: "Computer Science", items: ["Algorithms", "Data Structures", "Operating Systems", "Networks"] },
  { title: "Mathematics", items: ["Algebra", "Topology", "Analysis", "Combinatorics"] },
  { title: "Physics", items: ["Quantum Mechanics", "Relativity", "Thermodynamics", "Optics"] },
];

function simulatedFetch({ delay, shouldFail }) {
  const dataset = DATASETS[Math.floor(Math.random() * DATASETS.length)];
  return new Promise((resolve, reject) => {
    setTimeout(() => {
      if (shouldFail) reject(new Error("Network error"));
      else resolve({ ...dataset, time: new Date().toLocaleTimeString() });
    }, delay);
  });
}

export default function SafeLoader() {
  const [state, dispatch] = useReducer(Loader.step, Loader.init(MAX_RETRIES));
  const [delay, setDelay] = useState(1000);
  const [shouldFail, setShouldFail] = useState(false);
  const settingsRef = useRef({ delay: 1000, shouldFail: false });
  settingsRef.current = { delay, shouldFail };

  const ph = Loader.phase(state);
  const cached = Loader.cache(state);
  const isLoading = Loader.is_loading(ph);
  const loadingRid = Loader.loading_rid(ph);
  const retryCount = Loader.retries(state);

  // Side-effects: start fetch + timeout when phase becomes Loading
  useEffect(() => {
    if (!isLoading || loadingRid === undefined) return;
    const rid = loadingRid;
    let cancelled = false;

    const timer = setTimeout(() => {
      if (!cancelled) dispatch(Loader.timed_out(rid));
    }, TIMEOUT_MS);

    simulatedFetch(settingsRef.current)
      .then(data => { if (!cancelled) dispatch(Loader.got_response(rid, data)); })
      .catch(() => { if (!cancelled) dispatch(Loader.got_error(rid)); });

    return () => { cancelled = true; clearTimeout(timer); };
  }, [isLoading, loadingRid]);

  const phaseLabel = Loader.is_idle(ph) ? "Idle"
    : isLoading ? "Loading"
    : Loader.is_loaded(ph) ? "Loaded"
    : "Errored";

  const phaseColor = { Idle: "#6b7280", Loading: "#2563eb", Loaded: "#16a34a", Errored: "#dc2626" };

  return (
    <div>
      {/* State inspector */}
      <div style={{
        display: "flex", gap: "1rem", flexWrap: "wrap",
        marginBottom: "1rem", padding: "0.6rem 0.75rem",
        background: "#f9fafb", borderRadius: "0.5rem",
        fontSize: "0.78rem", fontFamily: "monospace",
      }}>
        <span>phase: <b style={{ color: phaseColor[phaseLabel] }}>{phaseLabel}</b></span>
        <span>rid: <b>{Loader.next_id(state)}</b></span>
        <span>cache: <b>{cached ? "Some" : "None"}</b></span>
        <span>retries: <b>{retryCount}/{MAX_RETRIES}</b></span>
      </div>

      {/* Controls */}
      <div style={{
        display: "flex", gap: "1rem", marginBottom: "1rem",
        alignItems: "center", flexWrap: "wrap",
      }}>
        <label style={{ fontSize: "0.8rem", display: "flex", alignItems: "center", gap: "0.3rem" }}>
          Delay
          <input type="range" min={200} max={4000} step={200} value={delay}
            onChange={e => setDelay(Number(e.target.value))}
            style={{ width: "80px" }} />
          <span style={{ fontFamily: "monospace", fontSize: "0.75rem", minWidth: "3.5em" }}>
            {delay}ms
          </span>
        </label>
        <label style={{ fontSize: "0.8rem", display: "flex", alignItems: "center", gap: "0.3rem" }}>
          <input type="checkbox" checked={shouldFail}
            onChange={e => setShouldFail(e.target.checked)} />
          Force error
        </label>
      </div>

      {/* Actions */}
      <div style={{ display: "flex", gap: "0.5rem", marginBottom: "1rem" }}>
        <button
          onClick={() => dispatch(Loader.$$fetch)}
          disabled={isLoading}
          style={{
            padding: "0.45rem 1rem", borderRadius: "0.5rem",
            border: "none",
            background: isLoading ? "#d1d5db" : "#2563eb",
            color: "white",
            cursor: isLoading ? "not-allowed" : "pointer",
            fontWeight: 500, fontSize: "0.875rem",
          }}
        >
          {Loader.is_idle(ph) ? "Load Data" : "Refresh"}
        </button>
        {Loader.is_errored(ph) && (
          <button
            onClick={() => dispatch(Loader.do_retry)}
            disabled={retryCount >= MAX_RETRIES}
            style={{
              padding: "0.45rem 1rem", borderRadius: "0.5rem",
              border: "2px solid #dc2626", background: "white",
              color: "#dc2626",
              cursor: retryCount >= MAX_RETRIES ? "not-allowed" : "pointer",
              fontWeight: 500, fontSize: "0.875rem",
              opacity: retryCount >= MAX_RETRIES ? 0.5 : 1,
            }}
          >
            Retry ({MAX_RETRIES - retryCount} left)
          </button>
        )}
      </div>

      {/* Content */}
      <div style={{
        minHeight: "120px", padding: "1rem",
        border: `2px solid ${phaseColor[phaseLabel]}22`,
        borderRadius: "0.5rem",
        display: "flex", alignItems: "center", justifyContent: "center",
        transition: "border-color 0.2s",
      }}>
        {Loader.is_idle(ph) && (
          <p style={{ color: "#9ca3af", margin: 0 }}>No data loaded yet.</p>
        )}

        {isLoading && (
          <div style={{ textAlign: "center" }}>
            <div className="loader-spin" style={{
              width: "24px", height: "24px",
              border: "3px solid #e5e7eb", borderTopColor: "#2563eb",
              borderRadius: "50%", margin: "0 auto 0.5rem",
            }} />
            <p style={{ color: "#6b7280", margin: 0, fontSize: "0.875rem" }}>
              Loading{retryCount > 0 ? ` (attempt ${retryCount + 1})` : ""}...
            </p>
          </div>
        )}

        {Loader.is_loaded(ph) && cached && (
          <div style={{ width: "100%" }}>
            <h4 style={{ margin: "0 0 0.5rem", color: "#16a34a" }}>{cached.title}</h4>
            <div style={{ display: "flex", flexWrap: "wrap", gap: "0.5rem" }}>
              {cached.items.map(item => (
                <span key={item} style={{
                  padding: "0.3rem 0.7rem", background: "#f0fdf4",
                  border: "1px solid #bbf7d0", borderRadius: "999px",
                  fontSize: "0.8rem", color: "#166534",
                }}>{item}</span>
              ))}
            </div>
            <p style={{ fontSize: "0.7rem", color: "#9ca3af", margin: "0.5rem 0 0" }}>
              Fetched at {cached.time}
            </p>
          </div>
        )}

        {Loader.is_errored(ph) && (
          <div style={{ textAlign: "center", width: "100%" }}>
            <p style={{ color: "#dc2626", margin: "0 0 0.5rem", fontWeight: 500 }}>
              Request failed
            </p>
            {cached ? (
              <div>
                <p style={{ fontSize: "0.75rem", color: "#6b7280", margin: "0 0 0.5rem" }}>
                  Showing cached data (preserved by verified reducer):
                </p>
                <div style={{ display: "flex", flexWrap: "wrap", gap: "0.5rem", justifyContent: "center" }}>
                  {cached.items.map(item => (
                    <span key={item} style={{
                      padding: "0.3rem 0.7rem", background: "#fef2f2",
                      border: "1px solid #fecaca", borderRadius: "999px",
                      fontSize: "0.8rem", color: "#991b1b",
                    }}>{item}</span>
                  ))}
                </div>
              </div>
            ) : (
              <p style={{ fontSize: "0.75rem", color: "#9ca3af", margin: 0 }}>
                No cached data available.
              </p>
            )}
          </div>
        )}
      </div>

      <style>{`@keyframes spin { to { transform: rotate(360deg) } }
.loader-spin { animation: spin 0.8s linear infinite; }`}</style>
    </div>
  );
}
