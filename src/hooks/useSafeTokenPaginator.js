import { useReducer, useEffect, useRef } from "react";
import { TokenPaginator } from "@rocqducers/lib/Rocqducers.js";

/**
 * useSafeTokenPaginator — React hook backed by the verified TokenPaginator reducer.
 *
 * fetchFn(token) receives the pending token (undefined = first page, number =
 * opaque cursor) and must return a Promise that resolves to { data, nextToken }
 * where nextToken is undefined (last page) or a number.
 *
 * Invariants enforced by the Rocq reducer:
 *   I1  Loaded ⟹ data is present (no null-dereference on the happy path)
 *   I2  Stale responses / errors are silently dropped (race-condition safety)
 *   I3  Next is a no-op on the last page (next_tok = None)
 *   I4  Next is a no-op while a request is in-flight
 *   I5  Prev is a no-op at the first page (back_stack = [])
 *   I7  GotError never corrupts back_stack
 *   I8  Prev pops exactly one level off the navigation stack
 *   I9  Fetch resets back_stack and next_tok to [] / None
 */
export default function useSafeTokenPaginator(fetchFn) {
  const [state, dispatch] = useReducer(TokenPaginator.step, TokenPaginator.init);
  const fetchFnRef = useRef(fetchFn);
  fetchFnRef.current = fetchFn;

  const ph        = TokenPaginator.phase(state);
  const isLoading = TokenPaginator.is_loading(ph);
  const loadingRid = TokenPaginator.loading_rid(ph);

  // Side-effect: when the phase becomes Loading, read cur_tok from the
  // verified state (the token the reducer has decided to fetch with) and
  // start the async fetch.  Stale cancellations are handled by the `cancelled`
  // flag; the reducer also silently drops any response with a wrong rid (I2).
  useEffect(() => {
    if (!isLoading || loadingRid === undefined) return;
    const rid = loadingRid;
    let cancelled = false;

    // cur_tok is the option nat the reducer set for this request:
    //   undefined  → first page (no cursor)
    //   number     → opaque cursor from a previous response
    const tok = TokenPaginator.cur_tok(state);

    fetchFnRef.current(tok)
      .then(({ data, nextToken }) => {
        if (!cancelled) {
          // Convert JS nextToken to option nat:
          //   undefined / null → None   (last page)
          //   number           → Some t  (more pages)
          const nxt = (nextToken != null)
            ? TokenPaginator.some_token(nextToken)
            : TokenPaginator.no_token;
          dispatch(TokenPaginator.got_response(rid, data, nxt));
        }
      })
      .catch(() => {
        if (!cancelled) dispatch(TokenPaginator.got_error(rid));
      });

    return () => { cancelled = true; };
  }, [isLoading, loadingRid]); // eslint-disable-line react-hooks/exhaustive-deps

  return {
    data:       TokenPaginator.data(state),
    isIdle:     TokenPaginator.is_idle(ph),
    isLoading,
    isLoaded:   TokenPaginator.is_loaded(ph),
    isErrored:  TokenPaginator.is_errored(ph),
    hasNext:    TokenPaginator.has_next(state),
    canGoBack:  TokenPaginator.can_go_back(state),
    backDepth:  TokenPaginator.back_depth(state),   // 0 = first page
    fetch:  () => dispatch(TokenPaginator.fetch),
    next:   () => dispatch(TokenPaginator.next_),
    prev:   () => dispatch(TokenPaginator.prev_),
  };
}
