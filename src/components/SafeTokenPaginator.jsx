import useSafeTokenPaginator from "../hooks/useSafeTokenPaginator";
import TokenPaginatorView from "./TokenPaginatorView";

// Simulated dataset: 3 pages of items.
// Tokens are just page indices — opaque to the reducer (any nat would do).
const PAGES = [
  { category: "Inner planets",  items: ["Mercury", "Venus", "Earth", "Mars"],           nextToken: 1 },
  { category: "Gas giants",     items: ["Jupiter", "Saturn", "Uranus", "Neptune"],       nextToken: 2 },
  { category: "Dwarf planets",  items: ["Ceres", "Pluto", "Eris", "Makemake", "Haumea"], nextToken: undefined },
];

function simulatedFetch(token) {
  // token is the option nat from the verified state:
  //   undefined → first page (Fetch / Prev back to start)
  //   number    → opaque cursor returned by a previous response
  const idx = token === undefined ? 0 : token;
  return new Promise((resolve, reject) => {
    setTimeout(() => {
      const page = PAGES[idx];
      if (!page) { reject(new Error("invalid token")); return; }
      resolve({ data: page, nextToken: page.nextToken });
    }, 600);
  });
}

const PHASE_COLOR = {
  Idle:    "#6b7280",
  Loading: "#2563eb",
  Loaded:  "#16a34a",
  Errored: "#dc2626",
};

export default function SafeTokenPaginator() {
  const {
    data, backDepth,
    isIdle, isLoading, isLoaded, isErrored,
    hasNext, canGoBack,
    fetch: doFetch, next, prev,
  } = useSafeTokenPaginator(simulatedFetch);

  const phaseLabel = isIdle ? "Idle"
    : isLoading ? "Loading"
    : isLoaded  ? "Loaded"
    : "Errored";

  return (
    <TokenPaginatorView
      phaseLabel={phaseLabel}
      phaseColor={PHASE_COLOR[phaseLabel]}
      data={data}
      backDepth={backDepth}
      isIdle={isIdle}
      isLoading={isLoading}
      isLoaded={isLoaded}
      isErrored={isErrored}
      hasNext={hasNext}
      canGoBack={canGoBack}
      onFetch={doFetch}
      onNext={next}
      onPrev={prev}
    />
  );
}
