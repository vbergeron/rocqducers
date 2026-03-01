import { useState, useCallback } from "react";
import { use_safe_async_button } from "@rocqducers/lib/Hooks.js";
import { AsyncButton } from "@rocqducers/lib/Rocqducers.js";
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

  const { isIdle, isLoading, dispatch } = use_safe_async_button();
  const [lastResult, setLastResult] = useState(null);

  const handleClick = useCallback(async () => {
    setLastResult(null);
    dispatch(AsyncButton.click);
    if (isIdle) {
      try {
        await action();
        dispatch(AsyncButton.success);
        setLastResult("success");
      } catch {
        dispatch(AsyncButton.failure);
        setLastResult("failure");
      }
    }
  }, [action, isIdle, dispatch]);

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
