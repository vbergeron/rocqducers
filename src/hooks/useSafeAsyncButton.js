import { useReducer, useCallback } from "react";
import { AsyncButton } from "@rocqducers/lib/Rocqducers.js";

export default function useSafeAsyncButton(action) {
  const [state, dispatch] = useReducer(AsyncButton.reducer, AsyncButton.idle);

  const isIdle = state === AsyncButton.idle;
  const isLoading = state === AsyncButton.loading;

  const click = useCallback(async () => {
    dispatch(AsyncButton.click);
    if (state === AsyncButton.idle) {
      try {
        await action();
        dispatch(AsyncButton.success);
        return "success";
      } catch {
        dispatch(AsyncButton.failure);
        return "failure";
      }
    }
  }, [action, state]);

  return { isIdle, isLoading, click };
}
