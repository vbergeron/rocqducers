import { useState } from "react";
import useSafeLoader from "../hooks/useSafeLoader";
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
  const [delay, setDelay] = useState(1000);
  const [shouldFail, setShouldFail] = useState(false);

  const {
    cached, retryCount, maxRetries, nextId,
    isIdle, isLoading, isLoaded, isErrored,
    fetch: doFetch, retry,
  } = useSafeLoader(
    () => simulatedFetch({ delay, shouldFail }),
    { maxRetries: MAX_RETRIES, timeoutMs: TIMEOUT_MS },
  );

  const phaseLabel = isIdle ? "Idle"
    : isLoading ? "Loading"
    : isLoaded ? "Loaded"
    : "Errored";

  const phaseColor = { Idle: "#6b7280", Loading: "#2563eb", Loaded: "#16a34a", Errored: "#dc2626" };

  return (
    <LoaderView
      phaseLabel={phaseLabel} phaseColor={phaseColor[phaseLabel]}
      nextId={nextId} cached={cached}
      retryCount={retryCount} maxRetries={maxRetries}
      isLoading={isLoading} isIdle={isIdle}
      isLoaded={isLoaded} isErrored={isErrored}
      onFetch={doFetch}
      onRetry={retry}
      delay={delay} onDelayChange={setDelay}
      shouldFail={shouldFail} onShouldFailChange={setShouldFail}
    />
  );
}
