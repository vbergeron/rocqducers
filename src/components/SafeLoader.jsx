import { useReducer, useEffect, useRef, useState } from "react";
import { Loader } from "@rocqducers/lib/Rocqducers.js";
import LoaderView from "./LoaderView";

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
    <LoaderView
      phaseLabel={phaseLabel} phaseColor={phaseColor[phaseLabel]}
      nextId={Loader.next_id(state)} cached={cached}
      retryCount={retryCount} maxRetries={MAX_RETRIES}
      isLoading={isLoading} isIdle={Loader.is_idle(ph)}
      isLoaded={Loader.is_loaded(ph)} isErrored={Loader.is_errored(ph)}
      onFetch={() => dispatch(Loader.$$fetch)}
      onRetry={() => dispatch(Loader.do_retry)}
      delay={delay} onDelayChange={setDelay}
      shouldFail={shouldFail} onShouldFailChange={setShouldFail}
    />
  );
}
