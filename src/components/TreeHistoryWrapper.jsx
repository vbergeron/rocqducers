import { use_branching_history } from "@rocqducers/lib/Hooks.js";

const KIND_LABELS = ["Leaf", "Link", "Node", "Failed"];

/**
 * TreeHistoryWrapper — wraps any reducer with proven-correct branching
 * undo history (UndoTree.v).
 *
 * Props:
 *   reducer      {function}  (state, event) => state
 *   initialState {*}
 *   children     {function}  render prop: (state, dispatch) => node
 */
export default function TreeHistoryWrapper({ reducer, initialState, children }) {
  const {
    state, tree, isFailed,
    canGoLeft, canGoRight, canGoLink, canGoUp,
    depth, focusKind,
    do_, goLeft, goRight, goLink, goUp,
  } = use_branching_history(reducer, initialState);

  return (
    <div>
      <div className="controls">
        <button className="nav-btn" onClick={goUp} disabled={!canGoUp}>
          ↑ Up
        </button>
        <button className="nav-btn" onClick={goLeft} disabled={!canGoLeft}>
          ← Left
        </button>
        <button className="nav-btn" onClick={goRight} disabled={!canGoRight}>
          Right →
        </button>
        <button className="nav-btn" onClick={goLink} disabled={!canGoLink}>
          ↓ Link
        </button>
        <span className="ml-auto text-xs text-gray-400 font-mono">
          depth {depth} · {KIND_LABELS[focusKind] ?? "?"}
          {isFailed && <b className="text-red-600"> FAILED</b>}
        </span>
      </div>

      <div className="flex justify-center p-4 mb-4 overflow-x-auto border-[1.5px] border-gray-200 rounded-lg bg-gray-50">
        <TreeNode node={tree} />
      </div>

      {state != null && children(state, do_)}
    </div>
  );
}

const DOT_KIND = {
  leaf:   "bg-green-200 border-green-600",
  link:   "bg-blue-200 border-blue-600",
  node:   "bg-violet-200 border-violet-600",
  failed: "bg-red-200 border-red-600",
};

function TreeNode({ node }) {
  if (!node) return null;

  const dotCls = node.focused
    ? "dot w-4 h-4 bg-indigo-500 border-2 border-indigo-700 shadow-[0_0_0_3px_#c7d2fe]"
    : `dot w-3 h-3 border-2 ${DOT_KIND[node.kind] ?? ""}`;

  if (node.children.length === 0) {
    return (
      <div className="tree-col">
        <div className={dotCls} />
      </div>
    );
  }

  if (node.children.length === 1) {
    return (
      <div className="tree-col">
        <div className={dotCls} />
        <div className="vline" />
        <TreeNode node={node.children[0]} />
      </div>
    );
  }

  return (
    <div className="tree-col">
      <div className={dotCls} />
      <div className="vline" />
      <div className="fork">
        <div className="fork-child">
          <TreeNode node={node.children[0]} />
        </div>
        <div className="fork-child">
          <TreeNode node={node.children[1]} />
        </div>
      </div>
    </div>
  );
}
