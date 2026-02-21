import { useReducer, useMemo } from "react";
import { NavHistory } from "@rocqducers/lib/Rocqducers.js";

export default function useSafeNavHistory(initial) {
  const initState = useMemo(() => NavHistory.init(initial), [initial]);

  const [state, dispatch] = useReducer(NavHistory.step, initState);

  return {
    past:    NavHistory.past(state),
    present: NavHistory.present(state),
    future:  NavHistory.future(state),
    goBack:    () => dispatch(NavHistory.go_back),
    goForward: () => dispatch(NavHistory.go_forward),
    navigate:  (x) => dispatch(NavHistory.navigate(x)),
  };
}
