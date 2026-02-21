import useSafeNavHistory from "../hooks/useSafeNavHistory";
import NavHistoryView from "./NavHistoryView";

const PLANETS = [
  "Mercury", "Venus", "Earth", "Mars",
  "Jupiter", "Saturn", "Uranus", "Neptune",
];

export default function SafeNavHistory() {
  const { past, present, future, goBack, goForward, navigate } =
    useSafeNavHistory("Earth");

  return (
    <NavHistoryView
      past={past}
      present={present}
      future={future}
      destinations={PLANETS}
      onGoBack={goBack}
      onGoForward={goForward}
      onNavigate={navigate}
    />
  );
}
