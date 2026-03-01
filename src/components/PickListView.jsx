export default function PickListView({ picked, suggestions, pick, unpick }) {
  const canUnpick = picked.length > 1;

  return (
    <div>
      <div className="mb-4">
        <h4 className="mt-0 mb-2 text-blue-600">
          Picked ({picked.length})
        </h4>
        <div className="chip-row">
          {picked.map((item, i) => (
            <button
              key={item}
              onClick={() => unpick(i)}
              className={`chip border-blue-600 bg-blue-600 text-white ${
                canUnpick ? "cursor-pointer opacity-100" : "cursor-not-allowed opacity-70"
              }`}
              title={canUnpick ? "Click to remove" : "Cannot remove last item"}
            >
              {item} ✕
            </button>
          ))}
        </div>
      </div>
      <div>
        <h4 className="mt-0 mb-2 text-gray-500">
          Suggestions ({suggestions.length})
        </h4>
        <div className="chip-row">
          {suggestions.map((item, i) => (
            <button
              key={item}
              onClick={() => pick(i)}
              className="chip border-gray-200 bg-white text-gray-700 cursor-pointer hover:border-gray-400"
            >
              + {item}
            </button>
          ))}
        </div>
      </div>
    </div>
  );
}
