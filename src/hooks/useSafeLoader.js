import { useReducer, useEffect, useRef } from "react";
import { Loader } from "@rocqducers/lib/Rocqducers.js";

export default function useSafeLoader(fetchFn, { maxRetries = 3, timeoutMs = 5000 } = {}) {
  const [state, dispatch] = useReducer(Loader.step, Loader.init(maxRetries));
  const fetchFnRef = useRef(fetchFn);
  fetchFnRef.current = fetchFn;

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
    }, timeoutMs);

    fetchFnRef.current()
      .then(data => { if (!cancelled) dispatch(Loader.got_response(rid, data)); })
      .catch(() => { if (!cancelled) dispatch(Loader.got_error(rid)); });

    return () => { cancelled = true; clearTimeout(timer); };
  }, [isLoading, loadingRid, timeoutMs]);

  return {
    cached,
    retryCount,
    maxRetries,
    nextId: Loader.next_id(state),
    isIdle: Loader.is_idle(ph),
    isLoading,
    isLoaded: Loader.is_loaded(ph),
    isErrored: Loader.is_errored(ph),
    fetch: () => dispatch(Loader.$$fetch),
    retry: () => dispatch(Loader.do_retry),
  };
}
