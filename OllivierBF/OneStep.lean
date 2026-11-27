/-
  One-step measures (Section 3 of the paper): `μ u` is a probability measure on the closed
  neighbourhood `N[u]`. For an edge `(i, j)` the residual supply `r₊ = μ_i − min(μ_i, μ_j)` and the
  residual demand `r₋ = μ_j − min(μ_i, μ_j)` satisfy Lemma 4.1: no demand on `U_i`, no supply on
  `U_j`, and every supply–demand pair is within distance `3`, and within distance `2` unless it lies
  in `U_i × U_j`. The curvature is `1 − W₁(r₊, r₋)`, and the cost of a coupling of the residuals is
  `3τ` minus its savings (Proposition 4.2).
-/
module

public import OllivierBF.Residual
public import OllivierBF.Graph

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `μ u` is a probability measure on the closed neighbourhood of `u`. -/
structure OneStepAt (G : SimpleGraph V) (μ : V → V → ℝ) (u : V) : Prop where
  nonneg : ∀ k, 0 ≤ μ u k
  mass : ∑ k, μ u k = 1
  supp : ∀ k, k ≠ u → ¬ G.Adj u k → μ u k = 0

/-- OR curvature of `(i, j)` for the one-step measure `μ`. -/
noncomputable def cORm (d : V → V → ℝ) (μ : V → V → ℝ) (i j : V) : ℝ := 1 - W1 d (μ i) (μ j)

/-- Residual supply `r₊ = μ_i − min(μ_i, μ_j)`. -/
noncomputable def resP (μ : V → V → ℝ) (i j k : V) : ℝ := μ i k - min (μ i k) (μ j k)

/-- Residual demand `r₋ = μ_j − min(μ_i, μ_j)`. -/
noncomputable def resN (μ : V → V → ℝ) (i j k : V) : ℝ := μ j k - min (μ i k) (μ j k)

/-- Residual mass `τ`. -/
noncomputable def resMass (μ : V → V → ℝ) (i j : V) : ℝ := ∑ k, resP μ i j k

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ}
variable {μ : V → V → ℝ} {i j : V}

/-! ### Basic facts -/

lemma resP_nonneg (μ : V → V → ℝ) (i j k : V) : 0 ≤ resP μ i j k :=
  sub_nonneg.2 (min_le_left _ _)

lemma resN_nonneg (μ : V → V → ℝ) (i j k : V) : 0 ≤ resN μ i j k :=
  sub_nonneg.2 (min_le_right _ _)

/-- At every vertex, the residual supply or the residual demand vanishes. -/
lemma resP_eq_zero_or_resN_eq_zero (μ : V → V → ℝ) (i j k : V) :
    resP μ i j k = 0 ∨ resN μ i j k = 0 := by
  rcases le_total (μ i k) (μ j k) with h | h
  · left; unfold resP; rw [min_eq_left h]; ring
  · right; unfold resN; rw [min_eq_right h]; ring

lemma resP_sum_eq_resN_sum (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) :
    ∑ k, resP μ i j k = ∑ k, resN μ i j k := by
  unfold resP resN
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hi.mass, hj.mass]

/-! ### Lemma 4.1: where the residuals live -/

lemma mem_closed_of_resP_pos (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {x : V}
    (hx : 0 < resP μ i j x) : x = i ∨ G.Adj i x := by
  by_contra h'
  have h := not_or.mp h'
  have h0 : μ i x = 0 := hi.supp x h.1 h.2
  have : resP μ i j x = 0 := by
    unfold resP; rw [h0, min_eq_left (hj.nonneg x)]; ring
  linarith

lemma mem_closed_of_resN_pos (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {y : V}
    (hy : 0 < resN μ i j y) : y = j ∨ G.Adj j y := by
  by_contra h'
  have h := not_or.mp h'
  have h0 : μ j y = 0 := hj.supp y h.1 h.2
  have : resN μ i j y = 0 := by
    unfold resN; rw [h0, min_eq_right (hi.nonneg y)]; ring
  linarith

/-- No residual demand on `U_i`. -/
lemma resN_eq_zero_of_uniq (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {x : V}
    (hx : x ∈ uniq G i j) : resN μ i j x = 0 := by
  obtain ⟨hxj, -, hjx⟩ := mem_uniq.1 hx
  have h0 : μ j x = 0 := hj.supp x hxj hjx
  unfold resN; rw [h0, min_eq_right (hi.nonneg x)]; ring

/-- No residual supply on `U_j`. -/
lemma resP_eq_zero_of_uniq (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {y : V}
    (hy : y ∈ uniq G j i) : resP μ i j y = 0 := by
  obtain ⟨hyi, -, hiy⟩ := mem_uniq.1 hy
  have h0 : μ i y = 0 := hi.supp y hyi hiy
  unfold resP; rw [h0, min_eq_left (hj.nonneg y)]; ring

/-- Residual supply outside `S = {i, j} ∪ C` lies in `U_i`. -/
lemma mem_uniq_of_resP_pos (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {x : V}
    (hx : 0 < resP μ i j x) (hxS : x ∉ overlap (G := G) i j) : x ∈ uniq G i j := by
  have hxi := mem_closed_of_resP_pos hi hj hx
  simp only [overlap, Finset.mem_insert, mem_common, not_or] at hxS
  obtain ⟨hxi', hxj', hC⟩ := hxS
  rcases hxi with h | hix
  · exact absurd h hxi'
  · exact mem_uniq.2 ⟨hxj', hix, fun hjx => hC ⟨hix, hjx⟩⟩

/-- Residual demand outside `S = {i, j} ∪ C` lies in `U_j`. -/
lemma mem_uniq_of_resN_pos (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {y : V}
    (hy : 0 < resN μ i j y) (hyS : y ∉ overlap (G := G) i j) : y ∈ uniq G j i := by
  have hyj := mem_closed_of_resN_pos hi hj hy
  simp only [overlap, Finset.mem_insert, mem_common, not_or] at hyS
  obtain ⟨hyi', hyj', hC⟩ := hyS
  rcases hyj with h | hjy
  · exact absurd h hyj'
  · exact mem_uniq.2 ⟨hyi', hjy, fun hiy => hC ⟨hiy, hjy⟩⟩

lemma d_le_one_of (hd : GraphMetric G d) {u v : V} (h : v = u ∨ G.Adj u v) : d u v ≤ 1 := by
  rcases h with rfl | h
  · rw [hd.self]; norm_num
  · rw [hd.adj h]

/-- **Lemma 4.1 (distances).** Every supply–demand pair is within distance `3`. -/
theorem resid_dist_le_three (hd : GraphMetric G d) (hij : G.Adj i j)
    (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {x y : V}
    (hx : 0 < resP μ i j x) (hy : 0 < resN μ i j y) : d x y ≤ 3 := by
  have h1 : d x i ≤ 1 := by
    rw [hd.symm]; exact d_le_one_of hd (mem_closed_of_resP_pos hi hj hx)
  have h2 : d j y ≤ 1 := d_le_one_of hd (mem_closed_of_resN_pos hi hj hy)
  have h3 : d i j = 1 := hd.adj hij
  have t1 := hd.tri x i y
  have t2 := hd.tri i j y
  linarith

/-- **Lemma 4.1 (distances).** A supply–demand pair outside `U_i × U_j` is within distance `2`. -/
theorem resid_dist_le_two (hd : GraphMetric G d) (hij : G.Adj i j)
    (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {x y : V}
    (hx : 0 < resP μ i j x) (hy : 0 < resN μ i j y)
    (hxy : ¬ (x ∈ uniq G i j ∧ y ∈ uniq G j i)) : d x y ≤ 2 := by
  have hxi := mem_closed_of_resP_pos hi hj hx
  have hyj := mem_closed_of_resN_pos hi hj hy
  by_cases hxU : x ∈ uniq G i j
  · have hyU : y ∉ uniq G j i := fun h => hxy ⟨hxU, h⟩
    have hyi : y = i ∨ G.Adj i y := by
      rcases hyj with h | hjy
      · exact Or.inr (h ▸ hij)
      · by_cases hiy : G.Adj i y
        · exact Or.inr hiy
        · by_cases hyi : y = i
          · exact Or.inl hyi
          · exact absurd (mem_uniq.2 ⟨hyi, hjy, hiy⟩) hyU
    have h1 : d x i ≤ 1 := by rw [hd.symm]; exact d_le_one_of hd hxi
    have h2 : d i y ≤ 1 := d_le_one_of hd hyi
    linarith [hd.tri x i y]
  · have hxj : x = j ∨ G.Adj j x := by
      rcases hxi with h | hix
      · exact Or.inr (h ▸ hij.symm)
      · by_cases hjx : G.Adj j x
        · exact Or.inr hjx
        · by_cases hxj : x = j
          · exact Or.inl hxj
          · exact absurd (mem_uniq.2 ⟨hxj, hix, hjx⟩) hxU
    have h1 : d x j ≤ 1 := by rw [hd.symm]; exact d_le_one_of hd hxj
    have h2 : d j y ≤ 1 := d_le_one_of hd hyj
    linarith [hd.tri x j y]

/-! ### Proposition 4.2: the residual form and the savings identity -/

/-- **The curvature is `1 − W₁(r₊, r₋)`.** -/
theorem cORm_eq_resid (hd : GraphMetric G d) (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) :
    cORm d μ i j = 1 - W1 d (resP μ i j) (resN μ i j) := by
  unfold cORm
  rw [W1_eq_W1_resid hi.nonneg hj.nonneg (by rw [hi.mass, hj.mass]) hd.nonneg hd.self hd.tri]
  rfl

/-- **Proposition 4.2 (savings).** A coupling of the residuals costs `3τ` minus its savings. -/
theorem savings_identity {ρ : V → V → ℝ} (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) :
    cost d ρ = 3 * resMass μ i j - savings d ρ := by
  rw [cost_eq_three_mass_sub_savings, hρ.mass_eq]
  rfl

lemma exists_resid_coupling_of (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) :
    ∃ ρ, IsCoupling (resP μ i j) (resN μ i j) ρ :=
  exists_resid_coupling (μ := μ i) (ν := μ j) (by rw [hi.mass, hj.mass])

end OllivierBF
