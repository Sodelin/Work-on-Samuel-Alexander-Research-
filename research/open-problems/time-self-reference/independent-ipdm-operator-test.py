"""Bounded operator test of pinned IPDm merge/split; no full simulation.

Only named, inspected function ASTs are executed. Agent/Tree construction and
NumPy's two scalar helpers are replaced by explicit mocks. All tested scores are
zero, so no floating point rounding convention affects the witness.
"""
from __future__ import annotations
import ast
import copy
import hashlib
import json
from pathlib import Path
from types import SimpleNamespace
from urllib.request import urlopen

COMMIT = "eca9b122480b8c654081d6a844176417aefbbcae"
EXPECTED = {
    "core/helperfunctions.py": "edaacacbb6f09810c0acd9fcbf7642610695501952b04eb59fb0d6a7a2e7a5a4",
    "core/env.py": "ecabd348002af771e7b07f6ba70aca281efd7f978e9643e33a896ad226cec886",
}

def fetch(path):
    data = urlopen(f"https://raw.githubusercontent.com/lksshw/IPDm/{COMMIT}/{path}", timeout=30).read()
    assert hashlib.sha256(data).hexdigest() == EXPECTED[path], path
    return ast.parse(data.decode("utf-8"), filename=path)

class MockPolicy:
    def __init__(self):
        self.payload = {"fixed-witness-policy": [0, 0, 0, 0]}
    def copy(self):
        return copy.deepcopy(self)

class MockAgent:
    def __init__(self, rng, hyperParams, agent_id, memory_length):
        self.rng, self.hp = rng, hyperParams
        self.agent_id = agent_id
        self.memory_length = memory_length
        self.avg_score = 0.0
        self.memory = ""
        self.acts_played = 0
        self.policy = MockPolicy()
    def get_score(self):
        return self.avg_score / self.acts_played if self.acts_played else self.avg_score

class MockTree:
    def __init__(self, agent, parents, children, neighbors):
        self.agent = agent
        self.parents = parents
        self.children = children
        self.neighbors = neighbors

np_mock = SimpleNamespace(
    argmax=lambda values: max(range(len(values)), key=values.__getitem__),
    round=lambda value, decimals: round(value, decimals),
)
ns = {"np": np_mock, "env": SimpleNamespace(Tree=MockTree), "Agent": MockAgent}
helper_ast = fetch("core/helperfunctions.py")
helper_names = {
    "get_superAgentNeighbors", "merge", "split", "is_superAgent",
    "get_leaf", "get_root", "accumulate_neighbors", "update_neighbors",
}
selected = [n for n in helper_ast.body if isinstance(n, ast.FunctionDef) and n.name in helper_names]
assert {n.name for n in selected} == helper_names
exec(compile(ast.Module(body=selected, type_ignores=[]), "pinned-helperfunctions.py", "exec"), ns)
ns["hf"] = SimpleNamespace(**{name: ns[name] for name in helper_names})

env_ast = fetch("core/env.py")
board = next(n for n in env_ast.body if isinstance(n, ast.ClassDef) and n.name == "BoardState")
board_names = {"_getBoardPos", "_board2index", "getNeighbors", "getTurnOrder"}
board.body = [n for n in board.body if isinstance(n, ast.FunctionDef) and n.name in board_names]
assert {n.name for n in board.body} == board_names
exec(compile(ast.fix_missing_locations(ast.Module(body=[board], type_ignores=[])), "pinned-env.py", "exec"), ns)


def new_world():
    b = ns["BoardState"]()
    b.board_size = 2
    b.rng, b.hp = None, None
    b.uuid_pointer = 4
    b.tree_size = 4
    b.tree = {
        i: MockTree(MockAgent(None, None, i, 1), set(), set(), set(b.getNeighbors(i)))
        for i in range(4)
    }
    return b


def partition(b):
    return sorted(sorted(ns["get_root"](i, b)) for i in b.getTurnOrder())


def check_world(b):
    live = b.getTurnOrder()
    blocks = [ns["get_root"](i, b) for i in live]
    assert sorted(x for block in blocks for x in block) == [0, 1, 2, 3]
    assert len(set(live)) == len(live)
    assert b.tree_size == len(b.tree)
    for key, node in b.tree.items():
        assert node.agent.agent_id == key
        assert len(node.parents) in (0, 2)
        assert len(node.children) in (0, 1)
        assert (not node.children) == (key in live)
        for parent in node.parents:
            assert key in b.tree[parent].children
        for child in node.children:
            assert key in b.tree[child].parents
    ns["update_neighbors"](live, b)
    for i in live:
        assert i not in b.tree[i].neighbors
        for j in b.tree[i].neighbors:
            assert j in live
            assert i in b.tree[j].neighbors


def legal_merge(b, i, j):
    check_world(b)
    assert i != j and i in b.getTurnOrder() and j in b.getTurnOrder()
    assert j in b.tree[i].neighbors
    new_id = b.uuid_pointer
    ns["merge"](b.tree[i], b.tree[j], b)
    check_world(b)
    return new_id


def visible(b):
    return {
        "partition": partition(b),
        "active": [
            {"id": i, "members": sorted(ns["get_root"](i, b)),
             "memory": b.tree[i].agent.memory,
             "memory_length": b.tree[i].agent.memory_length,
             "score": b.tree[i].agent.get_score(),
             "avg_score": b.tree[i].agent.avg_score,
             "acts_played": b.tree[i].agent.acts_played,
             "policy": b.tree[i].agent.policy.payload,
             "neighbors": sorted(b.tree[i].neighbors)}
            for i in sorted(b.getTurnOrder())
        ],
        "uuid_pointer": b.uuid_pointer,
        "tree_size": b.tree_size,
    }


def run():
    left, right = new_world(), new_world()
    assert legal_merge(left, 0, 1) == 4
    assert legal_merge(left, 4, 2) == 5
    assert legal_merge(right, 1, 2) == 4
    assert legal_merge(right, 0, 4) == 5
    before_left, before_right = visible(left), visible(right)
    assert before_left == before_right
    assert before_left["partition"] == [[0, 1, 2], [3]]
    assert set(left.getTurnOrder()) == set(right.getTurnOrder()) == {3, 5}
    for b in (left, right):
        assert ns["is_superAgent"](b.tree[5]) == 1
        assert b.tree[5].neighbors == {3}
    left_parents = sorted(left.tree[5].parents)
    right_parents = sorted(right.tree[5].parents)
    left_info = ns["split"](left.tree[5], left)
    right_info = ns["split"](right.tree[5], right)
    check_world(left)
    check_world(right)
    after_left, after_right = partition(left), partition(right)
    assert after_left == [[0, 1], [2], [3]]
    assert after_right == [[0], [1, 2], [3]]
    assert after_left != after_right
    assert set(left_info[5]) == set(left_parents)
    assert set(right_info[5]) == set(right_parents)
    result = {
        "status": "PASS_PINNED_OPERATOR_TEST_WITH_EXPLICIT_MOCKS",
        "commit": COMMIT,
        "source_sha256": EXPECTED,
        "executed_original_functions": sorted(helper_names),
        "executed_original_board_methods": sorted(board_names),
        "mocks": ["Agent constructor and get_score", "Tree constructor", "np.argmax", "np.round"],
        "equal_visible_input": before_left,
        "hidden_immediate_parents": {"left": left_parents, "right": right_parents},
        "left_output_partition": after_left,
        "right_output_partition": after_right,
        "scope": "Admissible merge/split operator histories with actual 2x2 board adjacency; no policy scheduler, q-learning, probability reachability, paper version equivalence or full simulation claim.",
    }
    out = Path(__file__).with_suffix(".json")
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    run()
