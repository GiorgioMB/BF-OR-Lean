/-
  Local structure of an edge `(i, j)`: common neighbours `C`, unique neighbours
  `U_i`, `U_j`, cross-edge vertices `ξ`, 4-cycle closers, cross matchings.
-/
module

public import OllivierBF.Transport

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The facts about the graph distance that the paper uses. Any `d` satisfying them
works; `graphMetric_dist` shows that the shortest-path distance does. -/
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

/-- The shortest-path distance of a connected graph is a `GraphMetric`.
(Mathlib API names may need adjusting to your Mathlib version.) -/
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

/-- Degree as a real number. -/
noncomputable def ρ (u : V) : ℝ := (G.degree u : ℝ)

/-- Common neighbours `C = N(i) ∩ N(j)`. -/
def common (i j : V) : Finset V := G.neighborFinset i ∩ G.neighborFinset j

/-- Unique neighbours `U_u = N(u) \ N(v) \ {v}` of `u` with respect to the edge `(u, v)`. -/
def uniq (u v : V) : Finset V := (G.neighborFinset u \ G.neighborFinset v).erase v

/-- Number of triangles on the edge. -/
def tri (i j : V) : ℕ := (common G i j).card

/-- `ξ_u`: unique neighbours of `u` incident to a cross edge. -/
def xi (u v : V) : Finset V := (uniq G u v).filter fun k => ∃ w ∈ uniq G v u, G.Adj k w

/-- `Ξ_{ij} = |ξ_i| + |ξ_j|`. -/
def Xi (i j : V) : ℕ := (xi G i j).card + (xi G j i).card

/-- 4-cycle closers `\tilde□(k, u, v) = |N(k) ∩ U_v|`. -/
def boxClose (k u v : V) : ℕ := (G.neighborFinset k ∩ uniq G v u).card

/-- `ϖ_max(i, j)`. -/
def varpi (i j : V) : ℕ :=
  max ((uniq G i j).sup fun k => boxClose G k i j) ((uniq G j i).sup fun w => boxClose G w j i)

/-- A matching of the cross-edge graph `B_{ij}`, as a set of oriented pairs `(u, w)`
with `u ∈ U_i`, `w ∈ U_j`. -/
def IsCrossMatching (i j : V) (M : Finset (V × V)) : Prop :=
  (∀ e ∈ M, e.1 ∈ uniq G i j ∧ e.2 ∈ uniq G j i ∧ G.Adj e.1 e.2) ∧
  (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧
  (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e')

open Classical in
/-- Matching number `𝔪(i, j)` of the cross-edge graph. -/
noncomputable def matchNum (i j : V) : ℕ :=
  ((Finset.univ : Finset (Finset (V × V))).filter (IsCrossMatching G i j)).sup Finset.card

variable {G}

/-! ### Membership -/

lemma mem_common {i j k : V} : k ∈ common G i j ↔ G.Adj i k ∧ G.Adj j k := by
  simp [common, SimpleGraph.mem_neighborFinset]

lemma mem_uniq {u v k : V} : k ∈ uniq G u v ↔ k ≠ v ∧ G.Adj u k ∧ ¬ G.Adj v k := by
  simp [uniq, SimpleGraph.mem_neighborFinset]

lemma common_comm (i j : V) : common G i j = common G j i := by
  simp [common, Finset.inter_comm]

lemma tri_comm (i j : V) : tri G i j = tri G j i := by
  simp [tri, common_comm]

lemma xi_subset (u v : V) : xi G u v ⊆ uniq G u v := Finset.filter_subset _ _

/-! ### Counting -/

/-- `|U_u| + 1 + △ = deg u` (as natural numbers). -/
lemma card_uniq_add {u v : V} (huv : G.Adj u v) :
    (uniq G u v).card + 1 + tri G u v = G.degree u := by
  have hv : v ∈ G.neighborFinset u \ G.neighborFinset v := by
    simp [SimpleGraph.mem_neighborFinset, huv]
  have h1 := Finset.card_erase_add_one hv
  have h2 := Finset.card_sdiff_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h2
  simp only [uniq, tri, common]
  omega

/-- Real version: `|U_u| = ρ_u − 1 − △`. -/
lemma card_uniq_real {u v : V} (huv : G.Adj u v) :
    ((uniq G u v).card : ℝ) = ρ G u - 1 - tri G u v := by
  have := card_uniq_add huv
  simp only [ρ]
  rw [← this]; push_cast; ring

/-- Triangles are at most `ρ_min − 1`. -/
lemma tri_le {u v : V} (huv : G.Adj u v) : (tri G u v : ℝ) ≤ ρ G u - 1 := by
  have := card_uniq_real huv
  have h0 : (0 : ℝ) ≤ (uniq G u v).card := by positivity
  linarith

/-- **Lemma `xi_bound`**: `Ξ ≤ ρ_u + ρ_v − 2 − 2△`. -/
theorem Xi_le {u v : V} (huv : G.Adj u v) :
    (Xi G u v : ℝ) ≤ ρ G u + ρ G v - 2 - 2 * tri G u v := by
  have h1 : ((xi G u v).card : ℝ) ≤ (uniq G u v).card := by
    exact_mod_cast Finset.card_le_card (xi_subset u v)
  have h2 : ((xi G v u).card : ℝ) ≤ (uniq G v u).card := by
    exact_mod_cast Finset.card_le_card (xi_subset v u)
  rw [card_uniq_real huv] at h1
  rw [card_uniq_real huv.symm, tri_comm] at h2
  simp only [Xi]; push_cast; linarith

/-- 4-cycle closers are bounded by the opposite unique neighbourhood. -/
lemma boxClose_le (k u v : V) : boxClose G k u v ≤ (uniq G v u).card :=
  Finset.card_le_card Finset.inter_subset_right

/-- **Lemma `box_count`**: `ϖ_max ≤ ρ_max − 1`. -/
theorem varpi_le {i j : V} (hij : G.Adj i j) :
    (varpi G i j : ℝ) ≤ max (ρ G i) (ρ G j) - 1 := by
  have hA : (uniq G i j).sup (fun k => boxClose G k i j) ≤ (uniq G j i).card :=
    Finset.sup_le fun k _ => boxClose_le k i j
  have hB : (uniq G j i).sup (fun w => boxClose G w j i) ≤ (uniq G i j).card :=
    Finset.sup_le fun w _ => boxClose_le w j i
  have hUi := card_uniq_add hij
  have hUj := card_uniq_add hij.symm
  have : varpi G i j + 1 ≤ max (G.degree i) (G.degree j) := by
    simp only [varpi]; omega
  have h' : ((varpi G i j : ℕ) : ℝ) + 1 ≤ ((max (G.degree i) (G.degree j) : ℕ) : ℝ) := by
    exact_mod_cast this
  simp only [ρ]; push_cast at h'; linarith

/-! ### Splitting sums over a neighbourhood -/

/-- `N(i) = {j} ⊔ C ⊔ U_i`, at the level of sums. -/
lemma sum_nbr_split {i j : V} (hij : G.Adj i j) (f : V → ℝ) :
    ∑ k ∈ G.neighborFinset i, f k = f j + ∑ k ∈ common G i j, f k + ∑ k ∈ uniq G i j, f k := by
  have hj : j ∈ G.neighborFinset i \ G.neighborFinset j := by
    simp [SimpleGraph.mem_neighborFinset, hij]
  rw [← Finset.sum_inter_add_sum_sdiff (G.neighborFinset i) (G.neighborFinset j),
    ← Finset.add_sum_erase _ f hj]
  simp only [common, uniq]; ring

/-! ### Matchings -/

lemma isCrossMatching_empty (i j : V) : IsCrossMatching G i j ∅ := by
  simp [IsCrossMatching]

lemma exists_max_matching (i j : V) :
    ∃ M, IsCrossMatching G i j M ∧ M.card = matchNum G i j := by
  classical
  have hne : ((Finset.univ : Finset (Finset (V × V))).filter (IsCrossMatching G i j)).Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, isCrossMatching_empty i j⟩⟩
  obtain ⟨M, hM, hsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  refine ⟨M, (Finset.mem_filter.1 hM).2, ?_⟩
  unfold matchNum
  convert hsup.symm

lemma IsCrossMatching.swap {i j : V} {M : Finset (V × V)} (h : IsCrossMatching G i j M) :
    IsCrossMatching G j i (M.image Prod.swap) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨h1, h2, h3⟩ := h.1 e₀ he₀
    exact ⟨h2, h1, h3.symm⟩
  · intro e he e' he' hfst
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨e₀', he₀', rfl⟩ := Finset.mem_image.1 he'
    rw [h.2.2 e₀ he₀ e₀' he₀' hfst]
  · intro e he e' he' hsnd
    obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨e₀', he₀', rfl⟩ := Finset.mem_image.1 he'
    rw [h.2.1 e₀ he₀ e₀' he₀' hsnd]

lemma matchNum_le_swap (i j : V) : matchNum G i j ≤ matchNum G j i := by
  classical
  obtain ⟨M, hM, hcard⟩ := exists_max_matching (G := G) i j
  rw [← hcard, ← Finset.card_image_of_injective M Prod.swap_injective]
  unfold matchNum
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hM.swap⟩)

lemma matchNum_comm (i j : V) : matchNum G i j = matchNum G j i :=
  le_antisymm (matchNum_le_swap i j) (matchNum_le_swap j i)

/-- A cross matching uses at most `|U_i|` pairs. -/
lemma IsCrossMatching.card_le {i j : V} {M : Finset (V × V)} (h : IsCrossMatching G i j M) :
    M.card ≤ (uniq G i j).card := by
  have hinj : Set.InjOn Prod.fst (M : Set (V × V)) := fun e he e' he' hfst => h.2.1 e he e' he' hfst
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card fun x hx => by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx; exact (h.1 e he).1

lemma matchNum_le_uniq {i j : V} : matchNum G i j ≤ (uniq G i j).card := by
  obtain ⟨M, hM, hcard⟩ := exists_max_matching (G := G) i j
  rw [← hcard]; exact hM.card_le

end OllivierBF
