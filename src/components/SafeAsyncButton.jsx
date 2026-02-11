import { useState, useCallback } from "react";
import useSafeAsyncButton from "../hooks/useSafeAsyncButton";
import AsyncButtonView from "./AsyncButtonView";

function simulatedAction({ delay, shouldFail }) {
  return new Promise((resolve, reject) => {
    setTimeout(() => {
      if (shouldFail) reject(new Error("Simulated failure"));
      else resolve();
    }, delay);
  });
}

export default function SafeAsyncButton() {
  const [delay, setDelay] = useState(1500);
  const [shouldFail, setShouldFail] = useState(false);

  const action = useCallback(
    () => simulatedAction({ delay, shouldFail }),
    [delay, shouldFail],
  );

  const { isIdle, isLoading, click } = useSafeAsyncButton(action);
  const [lastResult, setLastResult] = useState(null);

  const handleClick = useCallback(async () => {
    setLastResult(null);
    const result = await click();
    setLastResult(result);
  }, [click]);

  return (
    <AsyncButtonView
      isIdle={isIdle}
      isLoading={isLoading}
      lastResult={lastResult}
      onClick={handleClick}
      delay={delay}
      onDelayChange={setDelay}
      shouldFail={shouldFail}
      onShouldFailChange={setShouldFail}
    />
  );
}
