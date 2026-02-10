import { useReducer, useMemo } from "react";
import { PickList } from "@rocqducers/lib/Rocqducers.js";

export default function SafePickList({ items, defaultIndex = 0 }) {
  const initial = useMemo(() => {
    const defaultItem = items[defaultIndex];
    const rest = items.filter((_, i) => i !== defaultIndex);
    return PickList.init(defaultItem, rest);
  }, [items, defaultIndex]);

  const [state, dispatch] = useReducer(PickList.reducer, initial);

  const pickedItems = PickList.picked(state);
  const suggestionItems = PickList.suggestions(state);

  return (
    <div style={{ fontFamily: "system-ui, sans-serif" }}>
      <div style={{ marginBottom: "1rem" }}>
        <h4 style={{ margin: "0 0 0.5rem 0", color: "#2563eb" }}>
          Picked ({pickedItems.length})
        </h4>
        <div style={{ display: "flex", flexWrap: "wrap", gap: "0.5rem" }}>
          {pickedItems.map((item, i) => (
            <button
              key={item}
              onClick={() => dispatch(PickList.unpick(i))}
              style={{
                padding: "0.4rem 0.8rem",
                borderRadius: "999px",
                border: "2px solid #2563eb",
                background: "#2563eb",
                color: "white",
                cursor: pickedItems.length > 1 ? "pointer" : "not-allowed",
                opacity: pickedItems.length > 1 ? 1 : 0.7,
                fontSize: "0.875rem",
                fontWeight: 500,
                transition: "all 0.15s ease",
              }}
              title={
                pickedItems.length > 1
                  ? "Click to remove"
                  : "Cannot remove last item"
              }
            >
              {item} ✕
            </button>
          ))}
        </div>
      </div>
      <div>
        <h4 style={{ margin: "0 0 0.5rem 0", color: "#6b7280" }}>
          Suggestions ({suggestionItems.length})
        </h4>
        <div style={{ display: "flex", flexWrap: "wrap", gap: "0.5rem" }}>
          {suggestionItems.map((item, i) => (
            <button
              key={item}
              onClick={() => dispatch(PickList.pick(i))}
              style={{
                padding: "0.4rem 0.8rem",
                borderRadius: "999px",
                border: "2px solid #e5e7eb",
                background: "white",
                color: "#374151",
                cursor: "pointer",
                fontSize: "0.875rem",
                fontWeight: 500,
                transition: "all 0.15s ease",
              }}
            >
              + {item}
            </button>
          ))}
        </div>
      </div>
    </div>
  );
}
