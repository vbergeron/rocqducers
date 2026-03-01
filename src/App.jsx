import { useState } from "react";
import { pick_list_reduce, pick_list_init, pick_list_props } from "@rocqducers/lib/Hooks.js";
import SafePickList from "./components/SafePickList";
import SafeAsyncButton from "./components/SafeAsyncButton";
import LinearHistoryWrapper from "./components/LinearHistoryWrapper";
import TreeHistoryWrapper from "./components/TreeHistoryWrapper";
import PickListView from "./components/PickListView";

const FRUITS = ["Apple", "Banana", "Cherry", "Date", "Elderberry", "Fig", "Grape"];

const INITIAL_PICK_STATE = pick_list_init(FRUITS, 0);

const TABS = [
  {
    id: "picklist",
    label: "Pick list",
    title: "Pick your fruits",
    description:
      "Invariants: at least one fruit is always picked, and the total count never changes.",
  },
  {
    id: "async",
    label: "Async button",
    title: "Async button",
    description:
      "Invariants: clicks are ignored while loading, success and failure always return to idle.",
  },
  {
    id: "tree",
    label: "Branching history",
    title: "Branching history (undo tree)",
    description:
      "Invariants: go_left + go_up is a round-trip, Failed absorbs all navigation, cursor depth is non-negative.",
  },
  {
    id: "linear",
    label: "Linear history",
    title: "State history (undo / redo)",
    description:
      "Invariants: Undo after Do always restores the previous state; Redo after Undo restores the undone state; a new Do always clears the redo stack; Undo/Redo are no-ops at the edges of the timeline.",
  },
];

function PickListTab() {
  return <SafePickList items={FRUITS} defaultIndex={0} />;
}

function AsyncButtonTab() {
  return <SafeAsyncButton />;
}

function BranchingHistoryTab() {
  return (
    <TreeHistoryWrapper
      reducer={pick_list_reduce}
      initialState={INITIAL_PICK_STATE}
    >
      {(state, dispatch) => (
        <PickListView {...pick_list_props(state, dispatch)} />
      )}
    </TreeHistoryWrapper>
  );
}

function LinearHistoryTab() {
  return (
    <LinearHistoryWrapper
      reducer={pick_list_reduce}
      initialState={INITIAL_PICK_STATE}
    >
      {(state, dispatch) => (
        <PickListView {...pick_list_props(state, dispatch)} />
      )}
    </LinearHistoryWrapper>
  );
}

const TAB_CONTENT = {
  picklist: PickListTab,
  async: AsyncButtonTab,
  tree: BranchingHistoryTab,
  linear: LinearHistoryTab,
};

export default function App() {
  const [activeTab, setActiveTab] = useState("picklist");
  const tab = TABS.find((t) => t.id === activeTab);
  const TabContent = TAB_CONTENT[activeTab];

  return (
    <div className="max-w-xl mx-auto p-8 font-sans">
      <h1 className="text-3xl font-bold tracking-tight mb-1">Rocqducers</h1>
      <p className="text-gray-400 text-lg mb-8">
        React components powered by verified Rocq reducers.
      </p>

      <div className="flex border-b border-gray-200">
        {TABS.map((t) => (
          <button
            key={t.id}
            className={`px-4 py-2 bg-transparent border-none text-sm font-medium cursor-pointer border-b-2 -mb-px transition-colors ${
              t.id === activeTab
                ? "text-indigo-500 border-b-indigo-500"
                : "text-gray-500 border-b-transparent hover:text-gray-700"
            }`}
            onClick={() => setActiveTab(t.id)}
          >
            {t.label}
          </button>
        ))}
      </div>

      <div className="border border-gray-200 border-t-0 rounded-b-xl p-6">
        <h3 className="mt-0 mb-1">{tab.title}</h3>
        <p className="text-gray-500 text-sm mt-0 mb-4">{tab.description}</p>
        <TabContent />
      </div>
    </div>
  );
}
