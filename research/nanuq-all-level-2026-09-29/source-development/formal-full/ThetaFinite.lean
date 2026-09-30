import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.List.Range

/-!
Executable canonical-theta switching specification. No precomputed quartet
answers occur in this file. Four-point quartets are calculated from explicit
root-to-terminal paths in each of the four switching trees, then deduplicated.
The finite certificate and its generic soundness theorems are separate below.
-/
namespace Nanuq.Theta

structure Counts where
  a1 : Nat
  b1 : Nat
  a2 : Nat
  b2 : Nat
  deriving DecidableEq, BEq, Repr

def Counts.total (t : Counts) : Nat := t.a1 + t.b1 + t.a2 + t.b2

def Counts.armLength (t : Counts) (k : Fin 4) : Nat :=
  if k = 0 then t.a1 else if k = 1 then t.b1 else if k = 2 then t.a2 else t.b2

inductive Leaf where
  | c1
  | c2
  | arm (k : Fin 4) (j : Nat)
  deriving DecidableEq, BEq, Repr

inductive Vertex where
  | u
  | v
  | arm (k : Fin 4) (j : Nat)
  | terminal (x : Leaf)
  deriving DecidableEq, BEq, Repr

abbrev Switching := Bool × Bool

def switchings : List Switching := [(false, false), (false, true), (true, false), (true, true)]

def circular (t : Counts) : List Leaf :=
  [Leaf.c1] ++ ((List.range t.b1).reverse.map (Leaf.arm 1)) ++
  ((List.range t.b2).map (Leaf.arm 3)) ++ [Leaf.c2] ++
  ((List.range t.a2).reverse.map (Leaf.arm 2)) ++ ((List.range t.a1).map (Leaf.arm 0))

/-- Vertices on the path from junction u to an arm position. The path contains
u, optionally v across the central edge, and then the requested arm prefix. -/
def armPath (k : Fin 4) (depth : Nat) : List Vertex :=
  [Vertex.u] ++ (if k.val % 2 = 1 then [Vertex.v] else []) ++
    (List.range depth).map (Vertex.arm k)

/-- The four genuine switching trees, represented by all their terminal paths.
Internal degree-two vertices and unlabeled pendant tips need not be suppressed:
that operation preserves every quartet read by the four-point test. -/
def terminalPath (t : Counts) (s : Switching) : Leaf → List Vertex
  | Leaf.c1 =>
      let k : Fin 4 := if s.1 then 1 else 0
      armPath k (t.armLength k) ++ [Vertex.terminal Leaf.c1]
  | Leaf.c2 =>
      let k : Fin 4 := if s.2 then 3 else 2
      armPath k (t.armLength k) ++ [Vertex.terminal Leaf.c2]
  | Leaf.arm k j => armPath k (j + 1) ++ [Vertex.terminal (Leaf.arm k j)]

/-- Edge list of the represented switched tree, obtained from adjacent vertices
in its root paths. The quartet evaluator uses these same paths directly. -/
def switchingEdges (t : Counts) (s : Switching) : List (Vertex × Vertex) :=
  ((circular t).flatMap fun x =>
    let p := terminalPath t s x
    p.zip p.tail).eraseDups

def commonPrefixLength : List Vertex → List Vertex → Nat
  | x :: xs, y :: ys => if x = y then 1 + commonPrefixLength xs ys else 0
  | _, _ => 0

def treeDistance (t : Counts) (s : Switching) (x y : Leaf) : Nat :=
  let px := terminalPath t s x
  let py := terminalPath t s y
  px.length + py.length - 2 * commonPrefixLength px py

inductive Pairing where
  | ab_cd
  | ac_bd
  | ad_bc
  deriving DecidableEq, BEq, Repr

/-- `none` is an explicit failure of the strict four-point test. The finite
certificate checks that this never occurs for a valid quartet. -/
def quartet (t : Counts) (s : Switching) (a b c d : Leaf) : Option Pairing :=
  let v0 := treeDistance t s a b + treeDistance t s c d
  let v1 := treeDistance t s a c + treeDistance t s b d
  let v2 := treeDistance t s a d + treeDistance t s b c
  if v0 < v1 ∧ v0 < v2 then some Pairing.ab_cd
  else if v1 < v0 ∧ v1 < v2 then some Pairing.ac_bd
  else if v2 < v0 ∧ v2 < v1 then some Pairing.ad_bc
  else none

/-- Source normalization: the set of distinct displayed quartet topologies. -/
def distinctQuartets (t : Counts) (a b c d : Leaf) : List Pairing :=
  (switchings.filterMap fun s => quartet t s a b c d).eraseDups

/-- Twice the uniform-distinct-quartet cherry-separation average. Division is
rational, with no integral truncation or multiplicity weighting. -/
def rho2 (t : Counts) (a b c d : Leaf) : ℚ :=
  let qs := distinctQuartets t a b c d
  ((2 * (qs.filter fun z => z != Pairing.ab_cd).length : Nat) : ℚ) / (qs.length : ℚ)

def anchor (t : Counts) (p q x y : Leaf) : ℚ :=
  if x = y then 0
  else if (x = p ∧ y = q) ∨ (x = q ∧ y = p) then 0
  else if x = p ∨ x = q ∨ y = p ∨ y = q then 1
  else rho2 t x y p q

def leafAt (t : Counts) (i : Nat) : Leaf := (circular t).getD i Leaf.c1

def next (t : Counts) (i : Nat) : Nat := (i + 1) % (circular t).length

/-- Twice the circular split weight, in the source's normalization. -/
def alpha (t : Counts) (p q i j : Nat) : ℚ :=
  anchor t (leafAt t p) (leafAt t q) (leafAt t i) (leafAt t j) +
  anchor t (leafAt t p) (leafAt t q) (leafAt t (next t i)) (leafAt t (next t j)) -
  anchor t (leafAt t p) (leafAt t q) (leafAt t i) (leafAt t (next t j)) -
  anchor t (leafAt t p) (leafAt t q) (leafAt t (next t i)) (leafAt t j)

def pairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap fun i =>
    (List.range n).filterMap fun j => if i < j then some (i,j) else none

def checkAnchors (t : Counts) : Bool :=
  let ps := pairs (circular t).length
  ps.all fun pq => ps.all fun ij => decide (0 ≤ alpha t pq.1 pq.2 ij.1 ij.2)

def checkQuartets (t : Counts) : Bool :=
  let ps := pairs (circular t).length
  ps.all fun ab => ps.all fun cd =>
    if ab.2 < cd.1 then
      let a := leafAt t ab.1
      let b := leafAt t ab.2
      let c := leafAt t cd.1
      let d := leafAt t cd.2
      (switchings.all fun s => (quartet t s a b c d).isSome) &&
        decide (1 ≤ (distinctQuartets t a b c d).length ∧
          (distinctQuartets t a b c d).length ≤ 2)
    else true

def checkTemplate (t : Counts) : Bool := checkQuartets t && checkAnchors t

/-- Every arm-count tuple that can arise in the six-witness reduction. -/
def templates : List Counts :=
  (List.range 7).flatMap fun a1 =>
  (List.range 7).flatMap fun b1 =>
  (List.range 7).flatMap fun a2 =>
  (List.range 7).filterMap fun b2 =>
    let t : Counts := ⟨a1,b1,a2,b2⟩
    if 1 ≤ t.total ∧ t.total ≤ 6 then some t else none

end Nanuq.Theta
