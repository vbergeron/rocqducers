import SafePickList from "./SafePickList";
import SafeLoader from "./SafeLoader";

const FRUITS = ["Apple", "Banana", "Cherry", "Date", "Elderberry", "Fig", "Grape"];

export default function App() {
  return (
    <div style={{
      maxWidth: "600px",
      margin: "2rem auto",
      padding: "2rem",
      fontFamily: "system-ui, sans-serif",
    }}>
      <h1 style={{ marginBottom: "0.5rem" }}>Rocqducers</h1>
      <p style={{ color: "#6b7280", marginBottom: "2rem" }}>
        React components powered by verified Rocq reducers.
      </p>

      <div style={{
        border: "1px solid #e5e7eb",
        borderRadius: "0.75rem",
        padding: "1.5rem",
        marginBottom: "1.5rem",
      }}>
        <h3 style={{ margin: "0 0 0.25rem 0" }}>Pick your fruits</h3>
        <p style={{ color: "#6b7280", fontSize: "0.875rem", margin: "0 0 1rem 0" }}>
          Invariants: at least one fruit is always picked, and the total count never changes.
        </p>
        <SafePickList items={FRUITS} defaultIndex={0} />
      </div>

      <div style={{
        border: "1px solid #e5e7eb",
        borderRadius: "0.75rem",
        padding: "1.5rem",
      }}>
        <h3 style={{ margin: "0 0 0.25rem 0" }}>Network loader</h3>
        <p style={{ color: "#6b7280", fontSize: "0.875rem", margin: "0 0 1rem 0" }}>
          Invariants: loaded implies data present, error preserves cache, stale responses ignored, retry bounded.
        </p>
        <SafeLoader />
      </div>
    </div>
  );
}
