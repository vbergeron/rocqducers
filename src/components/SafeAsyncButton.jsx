import { useState, useCallback } from "react";
import { use_safe_async_button } from "@rocqducers/lib/Hooks.js";
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

  const { isIdle, isLoading, click, succeed, fail } = use_safe_async_button();
  const [lastResult, setLastResult] = useState(null);

  const handleClick = useCallback(async () => {
    setLastResult(null);
    click();
    if (isIdle) {
      try {
        await action();
        succeed();
        setLastResult("success");
      } catch {
        fail();
        setLastResult("failure");
      }
    }
  }, [action, isIdle, click, succeed, fail]);

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
