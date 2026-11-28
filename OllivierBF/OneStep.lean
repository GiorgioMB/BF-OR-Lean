/- One-step measures, OR curvature, and the residuals. -/
module

public import OllivierBF.Residual
public import OllivierBF.Graph

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `μ u` is a probability measure on `N[u]`. -/
structure OneStepAt (G : SimpleGraph V) (μ : V → V → ℝ) (u : V) : Prop where
  nonneg : ∀ k, 0 ≤ μ u k
  mass : ∑ k, μ u k = 1
  supp : ∀ k, k ≠ u → ¬ G.Adj u k → μ u k = 0

/-- `κ_μ(i, j) = 1 − W₁(μ_i, μ_j)`. -/
noncomputable def cORm (d : V → V → ℝ) (μ : V → V → ℝ) (i j : V) : ℝ := 1 - W1 d (μ i) (μ j)

/-- `r₊ = μ_i − min(μ_i, μ_j)`. -/
noncomputable def resP (μ : V → V → ℝ) (i j k : V) : ℝ := μ i k - min (μ i k) (μ j k)

/-- `r₋ = μ_j − min(μ_i, μ_j)`. -/
noncomputable def resN (μ : V → V → ℝ) (i j k : V) : ℝ := μ j k - min (μ i k) (μ j k)

/-- `τ = Σ r₊`. -/
noncomputable def resMass (μ : V → V → ℝ) (i j : V) : ℝ := ∑ k, resP μ i j k

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ}
variable {μ : V → V → ℝ} {i j : V}

lemma resP_nonneg (μ : V → V → ℝ) (i j k : V) : 0 ≤ resP μ i j k :=
  sub_nonneg.2 (min_le_left _ _)

lemma resN_nonneg (μ : V → V → ℝ) (i j k : V) : 0 ≤ resN μ i j k :=
  sub_nonneg.2 (min_le_right _ _)

lemma resP_eq_zero_or_resN_eq_zero (μ : V → V → ℝ) (i j k : V) :
    resP μ i j k = 0 ∨ resN μ i j k = 0 := by
  rcases le_total (μ i k) (μ j k) with h | h
  · left; unfold resP; rw [min_eq_left h]; ring
  · right; unfold resN; rw [min_eq_right h]; ring

lemma resP_sum_eq_resN_sum (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) :
    ∑ k, resP μ i j k = ∑ k, resN μ i j k := by
  unfold resP resN
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hi.mass, hj.mass]

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

lemma mem_uniq_of_resP_pos (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {x : V}
    (hx : 0 < resP μ i j x) (hxS : x ∉ overlap (G := G) i j) : x ∈ uniq G i j := by
  have hxi := mem_closed_of_resP_pos hi hj hx
  simp only [overlap, Finset.mem_insert, mem_common, not_or] at hxS
  obtain ⟨hxi', hxj', hC⟩ := hxS
  rcases hxi with h | hix
  · exact absurd h hxi'
  · exact mem_uniq.2 ⟨hxj', hix, fun hjx => hC ⟨hix, hjx⟩⟩

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

theorem cORm_eq_resid (hd : GraphMetric G d) (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) :
    cORm d μ i j = 1 - W1 d (resP μ i j) (resN μ i j) := by
  unfold cORm
  rw [W1_eq_W1_resid hi.nonneg hj.nonneg (by rw [hi.mass, hj.mass]) hd.nonneg hd.self
    fun x z w _ _ _ => hd.tri x z w]
  rfl

lemma exists_resid_coupling_of (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) :
    ∃ ρ, IsCoupling (resP μ i j) (resN μ i j) ρ :=
  exists_resid_coupling (μ := μ i) (ν := μ j) (by rw [hi.mass, hj.mass])

end OllivierBF
