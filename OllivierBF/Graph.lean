/-
  The distances for which the results hold (`GraphMetric`, Appendix C) and the neighborhoods of an
  edge `(i, j)` (Section 3): `C`, `U_i`, `U_j`, and `S`.
-/
module

public import OllivierBF.Transport

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The properties of the distance that the results use: `0` on the diagonal, `1` on edges, at
least `1` between distinct vertices and at least `2` between distinct non-adjacent ones, the
triangle inequality, and symmetry. The shortest-path distance of a connected graph has them
(`graphMetric_dist`). -/
structure GraphMetric (d : V → V → ℝ) : Prop where
  self : ∀ x, d x x = 0
  adj : ∀ {x y}, G.Adj x y → d x y = 1
  one_le : ∀ {x y}, x ≠ y → 1 ≤ d x y
  two_le : ∀ {x y}, x ≠ y → ¬ G.Adj x y → 2 ≤ d x y
  tri : ∀ x y z, d x z ≤ d x y + d y z
  symm : ∀ x y, d x y = d y x

variable {G}

lemma GraphMetric.nonneg {d : V → V → ℝ} (hd : GraphMetric G d) (x y : V) : 0 ≤ d x y := by
  by_cases hxy : x = y
  · subst hxy; rw [hd.self]
  · linarith [hd.one_le hxy]

lemma GraphMetric.le_two {d : V → V → ℝ} (hd : GraphMetric G d) {x k y : V}
    (h₁ : G.Adj x k) (h₂ : G.Adj k y) : d x y ≤ 2 := by
  have := hd.tri x k y; rw [hd.adj h₁, hd.adj h₂] at this; linarith

lemma GraphMetric.le_three {d : V → V → ℝ} (hd : GraphMetric G d) {x a b y : V}
    (h₁ : G.Adj x a) (h₂ : G.Adj a b) (h₃ : G.Adj b y) : d x y ≤ 3 := by
  have h := hd.tri x a y
  have h' := hd.le_two h₂ h₃
  rw [hd.adj h₁] at h; linarith

/-- The shortest-path distance of a connected graph is a `GraphMetric`. -/
lemma graphMetric_dist (hG : G.Connected) : GraphMetric G (fun x y => (G.dist x y : ℝ)) where
  self x := by simp
  adj h := by simp [SimpleGraph.dist_eq_one_iff_adj.mpr h]
  one_le {x y} hxy := by
    have := hG.pos_dist_of_ne hxy
    exact_mod_cast this
  two_le {x y} hxy hna := by
    have h0 := hG.pos_dist_of_ne hxy
    have h1 : G.dist x y ≠ 1 := fun h => hna (SimpleGraph.dist_eq_one_iff_adj.mp h)
    have : 2 ≤ G.dist x y := by omega
    exact_mod_cast this
  tri x y z := by exact_mod_cast hG.dist_triangle
  symm x y := by rw [SimpleGraph.dist_comm]

variable (G)

/-- `C = N(i) ∩ N(j)`, the common neighbors of `i` and `j`; `t = |C|` counts the triangles on
`(i, j)`. -/
def common (i j : V) : Finset V := G.neighborFinset i ∩ G.neighborFinset j

/-- `U_u = N(u) \ N[v]` for the edge `(u, v)`: the neighbors of `u` other than `v` that are not
adjacent to `v`. -/
def uniq (u v : V) : Finset V := (G.neighborFinset u \ G.neighborFinset v).erase v

/-- `S = {i, j} ∪ C`, which is `N[i] ∩ N[j]` for an edge: the vertices where both measures may
have mass. -/
def overlap (i j : V) : Finset V := insert i (insert j (common G i j))

variable {G}

lemma mem_common {i j k : V} : k ∈ common G i j ↔ G.Adj i k ∧ G.Adj j k := by
  simp [common, SimpleGraph.mem_neighborFinset]

lemma mem_uniq {u v k : V} : k ∈ uniq G u v ↔ k ≠ v ∧ G.Adj u k ∧ ¬ G.Adj v k := by
  simp [uniq, SimpleGraph.mem_neighborFinset]

end OllivierBF
