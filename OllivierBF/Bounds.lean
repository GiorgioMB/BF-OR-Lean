/-
  Main transport bounds on OR curvature.

  Status: no `sorry`s; every coupling is constructed explicitly. See README.md for the
  build and for the published results that enter as hypotheses (`CitedFacts`).
-/
module

public import OllivierBF.Curvature
public import OllivierBF.Algebra

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ}

/-! ### Small coupling utilities -/

lemma IsCoupling.congr {μ ν μ' ν' : V → ℝ} {π : V → V → ℝ} (h : IsCoupling μ ν π)
    (hμ : ∀ x, μ x = μ' x) (hν : ∀ y, ν y = ν' y) : IsCoupling μ' ν' π :=
  ⟨h.1, fun x => (h.2.1 x).trans (hμ x), fun y => (h.2.2 y).trans (hν y)⟩

/-- Every coupling costs at least `2 · (off-diagonal mass) − (mass moved along edges)`. -/
lemma cost_ge_two_offdiag_sub_unit (hd : GraphMetric G d) {μ ν : V → ℝ} {π : V → V → ℝ}
    (h : IsCoupling μ ν π) :
    2 * ∑ x, (μ x - π x x) - ∑ x, ∑ y, (if G.Adj x y then π x y else 0) ≤ cost d π := by
  have hrow : ∀ x, μ x - π x x = ∑ y, (if x = y then 0 else π x y) := by
    intro x
    rw [← h.2.1 x, ← Finset.add_sum_erase _ (fun y => π x y) (Finset.mem_univ x)]
    rw [← Finset.add_sum_erase _ (fun y => if x = y then 0 else π x y) (Finset.mem_univ x)]
    simp only [ite_true, zero_add, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [ite_eq_right (fun e => (Finset.mem_erase.1 hy).1 e.symm)]
  simp only [hrow, Finset.mul_sum, ← Finset.sum_sub_distrib]
  unfold cost
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  by_cases hxy : x = y
  · subst hxy; simp [SimpleGraph.irrefl, hd.self]
  · by_cases ha : G.Adj x y
    · rw [ite_eq_right hxy, ite_eq_left ha, hd.adj ha]; linarith
    · rw [ite_eq_right hxy, ite_eq_right ha]
      nlinarith [hd.two_le hxy ha, h.1 x y]

/-! ### Theorem `thm:lazy-quadrangle` -/

section lazyQuadrangle

variable {i j : V}

/-- The matching part of the coupling (bookkeeping). -/
lemma matching_coupling {M : Finset (V × V)} (hM : IsCrossMatching G i j M) (c : ℝ) (hc : 0 ≤ c) :
    IsCoupling (fun x => if x ∈ M.image Prod.fst then c else 0)
      (fun y => if y ∈ M.image Prod.snd then c else 0)
      (fun x y => if (x, y) ∈ M then c else 0) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun y => ?_⟩
  · show 0 ≤ (if (x, y) ∈ M then c else 0)
    split_ifs
    · exact hc
    · exact le_rfl
  · show ∑ y, (if (x, y) ∈ M then c else 0) = (if x ∈ M.image Prod.fst then c else 0)
    by_cases hx : x ∈ M.image Prod.fst
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
      rw [ite_eq_left hx, Finset.sum_eq_single e.2]
      · simp [he]
      · intro y _ hy
        rw [ite_eq_right]
        intro hmem
        exact hy (congrArg Prod.snd (hM.2.1 e he (e.1, y) hmem rfl)).symm
      · simp
    · rw [ite_eq_right hx]
      refine Finset.sum_eq_zero fun y _ => ite_eq_right fun hmem => hx ?_
      exact Finset.mem_image.2 ⟨(x, y), hmem, rfl⟩
  · show ∑ x, (if (x, y) ∈ M then c else 0) = (if y ∈ M.image Prod.snd then c else 0)
    by_cases hy : y ∈ M.image Prod.snd
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy
      rw [ite_eq_left hy, Finset.sum_eq_single e.1]
      · simp [he]
      · intro x _ hx
        rw [ite_eq_right]
        intro hmem
        exact hx (congrArg Prod.fst (hM.2.2 e he (x, e.2) hmem rfl)).symm
      · simp
    · rw [ite_eq_right hy]
      refine Finset.sum_eq_zero fun x _ => ite_eq_right fun hmem => hy ?_
      exact Finset.mem_image.2 ⟨(x, y), hmem, rfl⟩

lemma matching_cost (hd : GraphMetric G d) {M : Finset (V × V)} (hM : IsCrossMatching G i j M)
    (c : ℝ) (hc : 0 ≤ c) :
    cost d (fun x y => if (x, y) ∈ M then c else 0) ≤ M.card * c := by
  have hrow := (matching_coupling hM c hc).2.1
  have hinj : Set.InjOn Prod.fst (M : Set (V × V)) := fun e he e' he' h => hM.2.1 e he e' he' h
  calc cost d (fun x y => if (x, y) ∈ M then c else 0)
      ≤ ∑ x, ∑ y, (if (x, y) ∈ M then c else 0) := by
        unfold cost
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        show d x y * (if (x, y) ∈ M then c else 0) ≤ (if (x, y) ∈ M then c else 0)
        split_ifs with hmem
        · have hadj : G.Adj x y := (hM.1 _ hmem).2.2
          rw [hd.adj hadj]; linarith
        · simp
    _ = ∑ x, (if x ∈ M.image Prod.fst then c else 0) := Finset.sum_congr rfl fun x _ => hrow x
    _ = M.card * c := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
          Finset.card_image_of_injOn hinj]

/-- Proportional splitting: `x / D * D = x` whenever `D = 0` forces `x = 0`. -/
lemma div_mul_of_zero_imp {x D : ℝ} (h : D = 0 → x = 0) : x / D * D = x := by
  by_cases hD : D = 0
  · rw [hD, h hD]; simp
  · exact div_mul_cancel₀ x hD

/-- The four-piece coupling of the residuals in the proof of Theorem `thm:lazy-quadrangle`:
matching edges (cost 1), `j → U_j` (cost 1), `{i} ∪ C → U_j` through `j` (cost 2), and the
rest of `U_i → U_j` through `i, j` (cost 3), the unmatched demand being split in proportion. -/
lemma exists_residual_coupling (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j)
    {M : Finset (V × V)} (hM : IsCrossMatching G i j M) :
    ∃ π, IsCoupling (fun k => mLazy G i k - min (mLazy G i k) (mLazy G j k))
        (fun k => mLazy G j k - min (mLazy G i k) (mLazy G j k)) π ∧
      cost d π ≤ (w G i - w G j) + M.card * w G j + 2 * (1 + tri G i j) * (w G i - w G j)
        + 3 * ((uniq G i j).card * w G i - M.card * w G j) := by
  classical
  have hwi := w_pos (G := G) i
  have hwj := w_pos (G := G) j
  have hwle : w G j ≤ w G i := w_anti hle
  have hδ0 : 0 ≤ w G i - w G j := by linarith
  have ht0 : (0 : ℝ) ≤ tri G i j := Nat.cast_nonneg _
  -- matched vertices
  have hinj1 : Set.InjOn Prod.fst (M : Set (V × V)) := fun e he e' he' h => hM.2.1 e he e' he' h
  have hinj2 : Set.InjOn Prod.snd (M : Set (V × V)) := fun e he e' he' h => hM.2.2 e he e' he' h
  have hMU : M.image Prod.fst ⊆ uniq G i j := fun x hx => by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx; exact (hM.1 e he).1
  have hMW : M.image Prod.snd ⊆ uniq G j i := fun y hy => by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy; exact (hM.1 e he).2.1
  have hcMU : (M.image Prod.fst).card = M.card := Finset.card_image_of_injOn hinj1
  have hcMW : (M.image Prod.snd).card = M.card := Finset.card_image_of_injOn hinj2
  -- the unmatched part `W'` of `U_j`
  have hcW : ((uniq G j i \ M.image Prod.snd).card : ℝ) = (uniq G j i).card - M.card := by
    have h := Finset.card_sdiff_add_card_eq_card hMW
    rw [hcMW] at h
    have h' : ((uniq G j i \ M.image Prod.snd).card : ℝ) + M.card = (uniq G j i).card := by
      exact_mod_cast h
    linarith
  have hR0 : 0 ≤ ((uniq G i j).card : ℝ) * w G i - M.card * w G j := by
    have h : (M.card : ℝ) ≤ (uniq G i j).card := by exact_mod_cast hM.card_le
    nlinarith
  -- balance identity: unmatched demand `D' = (2 + △) δ + R`
  have hbal : ((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j
      = (2 + tri G i j) * (w G i - w G j) + (((uniq G i j).card : ℝ) * w G i - M.card * w G j) := by
    have hρi := ρ_pos hij
    have hρj := ρ_pos hij.symm
    have h1 : ρ G i + 1 ≠ 0 := by linarith
    have h2 : ρ G j + 1 ≠ 0 := by linarith
    rw [hcW, card_uniq_real hij, card_uniq_real hij.symm, tri_comm j i]
    simp only [w]
    field_simp; ring
  have hzero : ((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j = 0 →
      w G i - w G j = 0 ∧ ((uniq G i j).card : ℝ) * w G i - M.card * w G j = 0 := by
    intro h
    rw [hbal] at h
    have hm := mul_nonneg ht0 hδ0
    constructor <;> nlinarith
  have hD0 : 0 ≤ ((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j :=
    mul_nonneg (Nat.cast_nonneg _) hwj.le
  -- the unmatched-demand measure, scaled to a given mass `x`
  have hνmass : ∀ x : ℝ, (((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j = 0 → x = 0) →
      ∑ y, (if y ∈ uniq G j i \ M.image Prod.snd then
        x / (((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j) * w G j else 0) = x := by
    intro x hx
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    calc ((uniq G j i \ M.image Prod.snd).card : ℝ)
          * (x / (((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j) * w G j)
        = x / (((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j)
          * (((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j) := by ring
      _ = x := div_mul_of_zero_imp hx
  have hνnn : ∀ x : ℝ, 0 ≤ x → ∀ y, 0 ≤ (if y ∈ uniq G j i \ M.image Prod.snd then
      x / (((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j) * w G j else 0) := by
    intro x hx y
    split_ifs
    · exact mul_nonneg (div_nonneg hx hD0) hwj.le
    · exact le_rfl
  have hνpos : ∀ x : ℝ, ∀ y, 0 < (if y ∈ uniq G j i \ M.image Prod.snd then
      x / (((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j) * w G j else 0) →
      y ∈ uniq G j i \ M.image Prod.snd := by
    intro x y h
    by_contra hy
    rw [ite_eq_right hy] at h
    exact lt_irrefl _ h
  have hadjU : ∀ y, y ∈ uniq G j i \ M.image Prod.snd → G.Adj j y :=
    fun y hy => (mem_uniq.1 (Finset.mem_sdiff.1 hy).1).2.1
  -- piece 1: the matching
  have hP1 := matching_coupling hM (w G j) hwj.le
  have hC1 := matching_cost hd hM (w G j) hwj.le
  -- piece 2: `j → W'`, cost 1
  obtain ⟨π2, hP2, hC2⟩ := exists_piece_coupling (d := d)
    (μ := fun x => if x = j then w G i - w G j else 0)
    (ν := fun y => if y ∈ uniq G j i \ M.image Prod.snd then
      (w G i - w G j) / (((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j) * w G j else 0)
    (M := w G i - w G j) (D := 1)
    (fun x => by split_ifs <;> linarith) (hνnn _ hδ0)
    (by simp [Finset.sum_ite_eq']) (hνmass _ fun h => (hzero h).1) zero_le_one
    (fun x y hx hy => by
      have hxj : x = j := by
        by_contra h; rw [ite_eq_right h] at hx; exact lt_irrefl _ hx
      rw [hxj]; exact (hd.adj (hadjU y (hνpos _ y hy))).le)
  -- piece 3: `{i} ∪ C → W'` through `j`, cost 2
  have hjO : j ∈ overlap (G := G) i j := by simp [overlap]
  have hcO : (((overlap (G := G) i j).erase j).card : ℝ) = 1 + tri G i j := by
    have h := Finset.card_erase_add_one hjO
    have h' : (((overlap (G := G) i j).erase j).card : ℝ) + 1 = (overlap (G := G) i j).card := by
      exact_mod_cast h
    rw [card_overlap hij] at h'; linarith
  obtain ⟨π3, hP3, hC3⟩ := exists_piece_coupling (d := d)
    (μ := fun x => if x ∈ (overlap (G := G) i j).erase j then w G i - w G j else 0)
    (ν := fun y => if y ∈ uniq G j i \ M.image Prod.snd then
      ((1 + tri G i j) * (w G i - w G j)) / (((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j)
        * w G j else 0)
    (M := (1 + tri G i j) * (w G i - w G j)) (D := 2)
    (fun x => by split_ifs <;> linarith) (hνnn _ (mul_nonneg (by linarith) hδ0))
    (by rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, hcO])
    (hνmass _ fun h => by rw [(hzero h).1, mul_zero]) (by norm_num : (0 : ℝ) ≤ 2)
    (fun x y hx hy => by
      have hxO : x ∈ (overlap (G := G) i j).erase j := by
        by_contra h; rw [ite_eq_right h] at hx; exact lt_irrefl _ hx
      obtain ⟨hxj, hx'⟩ := Finset.mem_erase.1 hxO
      have hadj : G.Adj x j := by
        simp only [overlap, Finset.mem_insert, mem_common] at hx'
        rcases hx' with h | h | h
        · rw [h]; exact hij
        · exact absurd h hxj
        · exact h.2.symm
      exact hd.le_two hadj (hadjU y (hνpos _ y hy)))
  -- piece 4: the rest of `U_i → W'` through `i` and `j`, cost 3
  obtain ⟨π4, hP4, hC4⟩ := exists_piece_coupling (d := d)
    (μ := fun x => (if x ∈ uniq G i j then w G i else 0) - (if x ∈ M.image Prod.fst then w G j else 0))
    (ν := fun y => if y ∈ uniq G j i \ M.image Prod.snd then
      (((uniq G i j).card : ℝ) * w G i - M.card * w G j)
        / (((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j) * w G j else 0)
    (M := ((uniq G i j).card : ℝ) * w G i - M.card * w G j) (D := 3)
    (fun x => by
      by_cases hx : x ∈ M.image Prod.fst
      · rw [ite_eq_left (hMU hx), ite_eq_left hx]; linarith
      · rw [ite_eq_right hx, sub_zero]; split_ifs <;> linarith)
    (hνnn _ hR0)
    (by
        rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.univ_inter, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hcMU])
    (hνmass _ fun h => (hzero h).2) (by norm_num : (0 : ℝ) ≤ 3)
    (fun x y hx hy => by
      have hxU : x ∈ uniq G i j := by
        by_contra h
        have h' : x ∉ M.image Prod.fst := fun h'' => h (hMU h'')
        rw [ite_eq_right h, ite_eq_right h', sub_zero] at hx; exact lt_irrefl _ hx
      exact hd.le_three (mem_uniq.1 hxU).2.1.symm hij (hadjU y (hνpos _ y hy)))
  -- glue the four pieces
  have hall := hP1.add (hP2.add (hP3.add hP4))
  refine ⟨_, hall.congr (fun x => ?_) (fun y => ?_), ?_⟩
  · -- the supplies add up to the residual of `m_i`
    rw [lazy_resid_i hij hle x]
    by_cases hxj : x = j
    · have h1 : x ∉ (overlap (G := G) i j).erase j := by simp [hxj]
      have h2 : x ∈ overlap (G := G) i j := by rw [hxj]; exact hjO
      rw [ite_eq_left hxj, ite_eq_right h1, ite_eq_left h2]; ring
    · have h1 : (x ∈ (overlap (G := G) i j).erase j) ↔ x ∈ overlap (G := G) i j := by
        simp [Finset.mem_erase, hxj]
      rw [ite_eq_right hxj]
      by_cases hO : x ∈ overlap (G := G) i j
      · rw [ite_eq_left (h1.2 hO), ite_eq_left hO]; ring
      · rw [ite_eq_right (fun h => hO (h1.1 h)), ite_eq_right hO]; ring
  · -- the demands add up to the residual of `m_j`
    rw [lazy_resid_j hij hle y]
    by_cases hy : y ∈ uniq G j i \ M.image Prod.snd
    · obtain ⟨hyU, hyM⟩ := Finset.mem_sdiff.1 hy
      have hpos : 0 < ((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j :=
        mul_pos (by exact_mod_cast Finset.card_pos.2 ⟨y, hy⟩) hwj
      simp only [ite_eq_left hy, ite_eq_right hyM, ite_eq_left hyU, zero_add]
      have key : (w G i - w G j) / (((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j) * w G j
          + ((1 + tri G i j) * (w G i - w G j)) / (((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j)
            * w G j
          + (((uniq G i j).card : ℝ) * w G i - M.card * w G j)
            / (((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j) * w G j
          = ((2 + tri G i j) * (w G i - w G j) + (((uniq G i j).card : ℝ) * w G i - M.card * w G j))
            / (((uniq G j i \ M.image Prod.snd).card : ℝ) * w G j) * w G j := by ring
      rw [← hbal, div_self hpos.ne', one_mul] at key
      linarith
    · simp only [ite_eq_right hy, add_zero]
      by_cases hyM : y ∈ M.image Prod.snd
      · rw [ite_eq_left hyM, ite_eq_left (hMW hyM)]
      · have hyU : y ∉ uniq G j i := fun h => hy (Finset.mem_sdiff.2 ⟨h, hyM⟩)
        rw [ite_eq_right hyM, ite_eq_right hyU]
  · -- total cost
    rw [cost_add, cost_add, cost_add]
    nlinarith [hC1, hC2, hC3, hC4]

/-- **Theorem `thm:lazy-quadrangle` (lazy quadrangle bound).** For `ρ_i ≤ ρ_j`,
`𝔠_OR(i,j) ≥ (3 + △)/(ρ_min + 1) + (3 + 2△ + 2𝔪)/(ρ_max + 1) − 2`. -/
theorem lazy_quadrangle (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) :
    Llazy (ρ G i) (ρ G j) (tri G i j) (matchNum G i j) ≤ cOR G d i j := by
  obtain ⟨M, hM, hMcard⟩ := exists_max_matching (G := G) i j
  obtain ⟨π, hπ, hcost⟩ := exists_residual_coupling hd hij hle hM
  -- glue the diagonal on `min(m_i, m_j)` with the residual coupling
  have hκ : ∀ k, 0 ≤ min (mLazy G i k) (mLazy G j k) :=
    fun k => le_min (mLazy_nonneg i k) (mLazy_nonneg j k)
  have hfull := (isCoupling_diag hκ).add hπ
  have hfull' : IsCoupling (mLazy G i) (mLazy G j) _ :=
    hfull.congr (fun x => by simp) (fun y => by simp)
  have hW : W1 d (mLazy G i) (mLazy G j) ≤ (w G i - w G j) + M.card * w G j
      + 2 * (1 + tri G i j) * (w G i - w G j)
      + 3 * ((uniq G i j).card * w G i - M.card * w G j) := by
    refine (W1_le_cost hd.nonneg hfull').trans ?_
    rw [cost_add, cost_diag hd.self, zero_add]; exact hcost
  -- algebra
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  have hU := card_uniq_real hij
  rw [hMcard] at hW
  unfold cOR
  unfold Llazy
  simp only [w] at hW
  rw [hU] at hW
  have h1 : ρ G i + 1 ≠ 0 := by linarith
  have h2 : ρ G j + 1 ≠ 0 := by linarith
  have key : 1 - ((1 / (ρ G i + 1) - 1 / (ρ G j + 1)) + matchNum G i j * (1 / (ρ G j + 1))
      + 2 * (1 + tri G i j) * (1 / (ρ G i + 1) - 1 / (ρ G j + 1))
      + 3 * ((ρ G i - 1 - tri G i j) * (1 / (ρ G i + 1)) - matchNum G i j * (1 / (ρ G j + 1))))
      = (3 + tri G i j) / (ρ G i + 1) + (3 + 2 * tri G i j + 2 * matchNum G i j) / (ρ G j + 1) - 2 := by
    field_simp; ring
  linarith

end lazyQuadrangle

/-! ### Proposition `prop:lazy-envelope-tight` -/

section envelope

variable {i j : V}

/-- For a coupling of `m_i, m_j` that saturates the diagonal, with `ρ_i ≤ ρ_j`, the mass moved
along edges is at most `τ` and at most `δ + min(△ δ, τ) + min(|ξ_i| w_i, |ξ_j| w_j)`: every
off-diagonal unit ends in `U_j` (`lazy_resid_j`), and a unit-distance move into `U_j` starts at
`j`, at a common neighbour, or in `ξ_i` along a cross edge, never at `i`. -/
lemma unit_mass_le (_hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j)
    {π : V → V → ℝ} (hπ : IsCoupling (mLazy G i) (mLazy G j) π)
    (hsat : ∀ k, π k k = min (mLazy G i k) (mLazy G j k)) :
    ∑ x, ∑ y, (if G.Adj x y then π x y else 0) ≤
      min ((uniq G j i).card * w G j)
        ((w G i - w G j) + min (tri G i j * (w G i - w G j)) ((uniq G j i).card * w G j)
          + min ((xi G i j).card * w G i) ((xi G j i).card * w G j)) := by
  classical
  have hwj := w_pos (G := G) j
  -- off-diagonal row and column sums are the residuals
  have hrow : ∀ x, ∑ y ∈ univ.erase x, π x y = mLazy G i x - min (mLazy G i x) (mLazy G j x) := by
    intro x
    have h := Finset.add_sum_erase _ (fun y => π x y) (Finset.mem_univ x)
    have h' : π x x + ∑ y ∈ univ.erase x, π x y = ∑ y, π x y := h
    rw [hπ.2.1 x, hsat x] at h'; linarith
  have hcol : ∀ y, ∑ x ∈ univ.erase y, π x y = mLazy G j y - min (mLazy G i y) (mLazy G j y) := by
    intro y
    have h := Finset.add_sum_erase _ (fun x => π x y) (Finset.mem_univ y)
    have h' : π y y + ∑ x ∈ univ.erase y, π x y = ∑ x, π x y := h
    rw [hπ.2.2 y, hsat y] at h'; linarith
  -- (a) off-diagonal mass only enters `U_j`
  have hzero_col : ∀ x y, x ≠ y → y ∉ uniq G j i → π x y = 0 := by
    intro x y hxy hy
    have hc := hcol y
    rw [lazy_resid_j hij hle y, ite_eq_right hy] at hc
    exact (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hπ.1 x y).1 hc x
      (Finset.mem_erase.2 ⟨hxy, Finset.mem_univ x⟩)
  -- (b) off-diagonal mass only leaves the support of the residual of `m_i`
  have hzero_row : ∀ x y, x ≠ y → x ∉ overlap (G := G) i j → x ∉ uniq G i j → π x y = 0 := by
    intro x y hxy hO hU
    have hr := hrow x
    rw [lazy_resid_i hij hle x, ite_eq_right hO, ite_eq_right hU, add_zero] at hr
    exact (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hπ.1 x y).1 hr y
      (Finset.mem_erase.2 ⟨hxy.symm, Finset.mem_univ y⟩)
  -- unit-distance mass leaving `x`, and entering `y`
  set F : V → ℝ := fun x => ∑ y, (if G.Adj x y then π x y else 0) with hF
  have hF0 : ∀ x, 0 ≤ F x := fun x =>
    Finset.sum_nonneg fun y _ => by split_ifs <;> first | exact hπ.1 x y | exact le_rfl
  have hFrow : ∀ x, F x ≤ mLazy G i x - min (mLazy G i x) (mLazy G j x) := by
    intro x
    rw [← hrow x, hF]
    (try dsimp only)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x), ite_eq_right (SimpleGraph.irrefl G), zero_add]
    exact Finset.sum_le_sum fun y _ => by split_ifs <;> first | exact le_rfl | exact hπ.1 x y
  have hFcol : ∀ y, ∑ x, (if G.Adj x y then π x y else 0) ≤
      mLazy G j y - min (mLazy G i y) (mLazy G j y) := by
    intro y
    rw [← hcol y, ← Finset.add_sum_erase _ _ (Finset.mem_univ y), ite_eq_right (SimpleGraph.irrefl G),
      zero_add]
    exact Finset.sum_le_sum fun x _ => by split_ifs <;> first | exact le_rfl | exact hπ.1 x y
  -- the total is `∑ x, F x`
  -- bound by `τ`
  have hτ : ∑ x, F x ≤ (uniq G j i).card * w G j := by
    calc ∑ x, F x = ∑ y, ∑ x, (if G.Adj x y then π x y else 0) := Finset.sum_comm
      _ ≤ ∑ y, (if y ∈ uniq G j i then w G j else 0) :=
          Finset.sum_le_sum fun y _ => (hFcol y).trans (le_of_eq (lazy_resid_j hij hle y))
      _ = (uniq G j i).card * w G j := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  refine le_min hτ ?_
  -- `F` vanishes outside `{j} ∪ C ∪ U_i`
  have hFi : F i = 0 := by
    show ∑ y, (if G.Adj i y then π i y else 0) = 0
    refine Finset.sum_eq_zero fun y _ => ?_
    split_ifs with ha
    · by_cases hy : y ∈ uniq G j i
      · exact absurd ha (mem_uniq.1 hy).2.2
      · exact hzero_col i y ha.ne hy
    · rfl
  have hFout : ∀ x, x ∉ overlap (G := G) i j → x ∉ uniq G i j → F x = 0 := by
    intro x hO hUx
    show ∑ y, (if G.Adj x y then π x y else 0) = 0
    refine Finset.sum_eq_zero fun y _ => ?_
    split_ifs with ha
    · exact hzero_row x y ha.ne hO hUx
    · rfl
  have hS : ∑ x, F x = F j + ∑ x ∈ common G i j, F x + ∑ x ∈ uniq G i j, F x := by
    have hsub : ∀ x, x ∉ insert j (common G i j ∪ uniq G i j) → F x = 0 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_union, not_or] at hx
      by_cases hxi : x = i
      · rw [hxi]; exact hFi
      · refine hFout x ?_ hx.2.2
        simp only [overlap, Finset.mem_insert, not_or]
        exact ⟨hxi, hx.1, hx.2.1⟩
    have hdisj : Disjoint (common G i j) (uniq G i j) := by
      rw [Finset.disjoint_left]
      intro x hC hU'
      exact (mem_uniq.1 hU').2.2 (mem_common.1 hC).2
    have hjn : j ∉ common G i j ∪ uniq G i j := by
      simp [mem_common, mem_uniq, SimpleGraph.irrefl]
    rw [← Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => hsub x hx),
      Finset.sum_insert hjn, Finset.sum_union hdisj, add_assoc]
  rw [hS]
  -- the three contributions
  have hFj : F j ≤ w G i - w G j := by
    have h := hFrow j
    rw [lazy_resid_i hij hle j] at h
    have hjO : j ∈ overlap (G := G) i j := by simp [overlap]
    have hjU : j ∉ uniq G i j := by simp [mem_uniq]
    rwa [ite_eq_left hjO, ite_eq_right hjU, add_zero] at h
  have hFC1 : ∑ x ∈ common G i j, F x ≤ tri G i j * (w G i - w G j) := by
    calc ∑ x ∈ common G i j, F x ≤ ∑ x ∈ common G i j, (w G i - w G j) := by
          refine Finset.sum_le_sum fun x hx => ?_
          have h := hFrow x
          rw [lazy_resid_i hij hle x] at h
          have hxO : x ∈ overlap (G := G) i j := by simp [overlap, hx]
          have hxU : x ∉ uniq G i j := fun h' => (mem_uniq.1 h').2.2 (mem_common.1 hx).2
          rwa [ite_eq_left hxO, ite_eq_right hxU, add_zero] at h
      _ = tri G i j * (w G i - w G j) := by simp [Finset.sum_const, tri]; ring
  have hFC2 : ∑ x ∈ common G i j, F x ≤ (uniq G j i).card * w G j :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => hF0 x).trans hτ
  have hFU1 : ∑ x ∈ uniq G i j, F x ≤ (xi G i j).card * w G i := by
    have hvan : ∀ x ∈ uniq G i j, x ∉ xi G i j → F x = 0 := by
      intro x hx hxi
      show ∑ y, (if G.Adj x y then π x y else 0) = 0
      refine Finset.sum_eq_zero fun y _ => ?_
      split_ifs with ha
      · by_cases hy : y ∈ uniq G j i
        · exact absurd (Finset.mem_filter.2 ⟨hx, y, hy, ha⟩) hxi
        · exact hzero_col x y ha.ne hy
      · rfl
    rw [← Finset.sum_subset (xi_subset i j) (fun x hx hxi => hvan x hx hxi)]
    calc ∑ x ∈ xi G i j, F x ≤ ∑ x ∈ xi G i j, w G i := by
          refine Finset.sum_le_sum fun x hx => ?_
          have hxU := xi_subset i j hx
          have h := hFrow x
          rw [lazy_resid_i hij hle x] at h
          have hxO : x ∉ overlap (G := G) i j := by
            simp only [overlap, Finset.mem_insert, mem_common, not_or]
            obtain ⟨h1, h2, h3⟩ := mem_uniq.1 hxU
            exact ⟨fun e => by rw [e] at h2; exact SimpleGraph.irrefl G h2, h1, fun h' => h3 h'.2⟩
          rwa [ite_eq_right hxO, ite_eq_left hxU, zero_add] at h
      _ = (xi G i j).card * w G i := by rw [Finset.sum_const, nsmul_eq_mul]
  have hFU2 : ∑ x ∈ uniq G i j, F x ≤ (xi G j i).card * w G j := by
    have hswap : ∑ x ∈ uniq G i j, F x
        = ∑ y, ∑ x ∈ uniq G i j, (if G.Adj x y then π x y else 0) := by
      rw [hF]; exact Finset.sum_comm
    rw [hswap]
    have hvan : ∀ y, y ∉ xi G j i → ∑ x ∈ uniq G i j, (if G.Adj x y then π x y else 0) = 0 := by
      intro y hy
      refine Finset.sum_eq_zero fun x hx => ?_
      split_ifs with ha
      · by_cases hyU : y ∈ uniq G j i
        · exact absurd (Finset.mem_filter.2 ⟨hyU, x, hx, ha.symm⟩) hy
        · exact hzero_col x y ha.ne hyU
      · rfl
    rw [← Finset.sum_subset (Finset.subset_univ (xi G j i)) (fun y _ hy => hvan y hy)]
    calc ∑ y ∈ xi G j i, ∑ x ∈ uniq G i j, (if G.Adj x y then π x y else 0)
        ≤ ∑ y ∈ xi G j i, w G j := by
          refine Finset.sum_le_sum fun y hy => ?_
          have hyU := xi_subset j i hy
          refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun x _ _ => by split_ifs <;> first | exact hπ.1 x y | exact le_rfl).trans ?_
          refine (hFcol y).trans (le_of_eq ?_)
          rw [lazy_resid_j hij hle y, ite_eq_left hyU]
      _ = (xi G j i).card * w G j := by rw [Finset.sum_const, nsmul_eq_mul]
  have h1 := le_min hFC1 hFC2
  have h2 := le_min hFU1 hFU2
  linarith

/-- **Proposition `prop:lazy-envelope-tight` (lazy transport envelope).** -/
theorem lazy_envelope (hd : GraphMetric G d) (cited : CitedFacts G d) (hij : G.Adj i j)
    (hle : ρ G i ≤ ρ G j) :
    cOR G d i j ≤ min ((2 + tri G i j) * w G j)
      (-1 + 2 * ((2 + tri G i j) * w G j) + (w G i - w G j)
        + min (tri G i j * (w G i - w G j)) ((uniq G j i).card * w G j)
        + min ((xi G i j).card * w G i) ((xi G j i).card * w G j)) := by
  -- off-diagonal mass of a saturated coupling: `Σ_k (m_i k − min) = |U_j| w_j`
  have hoff : ∑ k, (mLazy G i k - min (mLazy G i k) (mLazy G j k))
      = ((uniq G j i).card : ℝ) * w G j := by
    have hres := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => lazy_resid_j hij hle k)
    have hsum : ∑ k, (mLazy G i k - min (mLazy G i k) (mLazy G j k))
        = ∑ k, (mLazy G j k - min (mLazy G i k) (mLazy G j k)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, mLazy_sum hij, mLazy_sum hij.symm]
    rw [hsum, hres, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  -- `|U_j| w_j = 1 − (2 + △) w_j`
  have hτm0 : ((uniq G j i).card : ℝ) * w G j = 1 - (2 + (tri G i j : ℝ)) * w G j := by
    have hU := card_uniq_real hij.symm
    have hρj := ρ_pos hij.symm
    have h1 : ρ G j + 1 ≠ 0 := by linarith
    rw [hU, tri_comm]
    simp only [w]; field_simp; ring
  have hW : max (1 - (2 + (tri G i j : ℝ)) * w G j)
      (2 - 2 * ((2 + (tri G i j : ℝ)) * w G j) - ((w G i - w G j)
        + min (tri G i j * (w G i - w G j)) ((uniq G j i).card * w G j)
        + min ((xi G i j).card * w G i) ((xi G j i).card * w G j)))
      ≤ W1 d (mLazy G i) (mLazy G j) := by
    apply le_W1 (exists_coupling_lazy hij)
    intro π hπ
    obtain ⟨π', hπ', hsat, hle'⟩ := cited.saturate _ _ π hπ
    have hlow := cost_ge_two_offdiag_sub_unit hd hπ'
    have hum := unit_mass_le hd hij hle hπ' hsat
    have hoff' : ∑ x, (mLazy G i x - π' x x) = ((uniq G j i).card : ℝ) * w G j := by
      simp only [hsat]; exact hoff
    rw [hoff'] at hlow
    have hu1 := (min_le_left _ _).trans' hum
    have hu2 := (min_le_right _ _).trans' hum
    refine le_trans (max_le ?_ ?_) hle'
    · linarith
    · linarith
  unfold cOR
  rw [le_min_iff]
  constructor
  · linarith [le_max_left (1 - (2 + (tri G i j : ℝ)) * w G j)
      (2 - 2 * ((2 + (tri G i j : ℝ)) * w G j) - ((w G i - w G j)
        + min (tri G i j * (w G i - w G j)) ((uniq G j i).card * w G j)
        + min ((xi G i j).card * w G i) ((xi G j i).card * w G j)))]
  · linarith [le_max_right (1 - (2 + (tri G i j : ℝ)) * w G j)
      (2 - 2 * ((2 + (tri G i j : ℝ)) * w G j) - ((w G i - w G j)
        + min (tri G i j * (w G i - w G j)) ((uniq G j i).card * w G j)
        + min ((xi G i j).card * w G i) ((xi G j i).card * w G j)))]

end envelope

/-! ### Theorem `thm:JL-plus-squares` (non-lazy) -/

section jl

variable {i j : V}

/-- The JL quantities. -/
noncomputable def jlK (i j : V) : ℝ := 1 - 1 / ρ G i - 1 / ρ G j
noncomputable def jlZmax (i j : V) : ℝ := tri G i j / ρmax G i j
noncomputable def jlZmin (i j : V) : ℝ := tri G i j / ρmin G i j

/-- Right-hand side of `eq:JL-aug`. -/
noncomputable def Lsq (i j : V) : ℝ :=
  -max (jlK (G := G) i j - jlZmax (G := G) i j - matchStat G i j) 0
  - max (jlK (G := G) i j - jlZmin (G := G) i j - matchStat G i j) 0 + jlZmax (G := G) i j

/-- The non-lazy measure: `ν_u(k) = 1/ρ_u` on `N(u)`. -/
lemma mp0_apply (u k : V) : mp G 0 u k = if G.Adj u k then 1 / ρ G u else 0 := by
  unfold mp
  by_cases h : k = u
  · subst h; simp [SimpleGraph.irrefl]
  · simp [h]

lemma pos_part_sub_le {A B : ℝ} (h : B ≤ A) : max A 0 - max B 0 ≤ A - B := by
  rcases le_total A 0 with hA | hA <;> rcases le_total B 0 with hB | hB
  · rw [max_eq_right hA, max_eq_right hB]; linarith
  · rw [max_eq_right hA, max_eq_left hB]; linarith
  · rw [max_eq_left hA, max_eq_right hB]; linarith
  · rw [max_eq_left hA, max_eq_left hB]

set_option maxHeartbeats 1000000 in
/-- The greedy coupling of `ν_i, ν_j` for `ρ_i ≤ ρ_j` (proof of Theorem `thm:JL-plus-squares`):
keep `v_j` on `C`, move `v_j` along a maximum matching, fill the unmatched part `W'` of `U_j`
from `j`, then `C`, then `U_i`, and send everything else to `i`. -/
lemma exists_jl_coupling_le (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j)
    {M : Finset (V × V)} (hM : IsCrossMatching G i j M) :
    ∃ π, IsCoupling (mp G 0 i) (mp G 0 j) π ∧
      cost d π ≤ 1 - (-max (1 - 1 / ρ G i - 1 / ρ G j - tri G i j * (1 / ρ G j) - M.card * (1 / ρ G j)) 0
        - max (1 - 1 / ρ G i - 1 / ρ G j - tri G i j * (1 / ρ G i) - M.card * (1 / ρ G j)) 0
        + tri G i j * (1 / ρ G j)) := by
  classical
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  -- opaque names for the weights and the two arguments of the positive parts
  obtain ⟨vi, hvi⟩ : ∃ x : ℝ, x = 1 / ρ G i := ⟨_, rfl⟩
  obtain ⟨vj, hvj⟩ : ∃ x : ℝ, x = 1 / ρ G j := ⟨_, rfl⟩
  rw [← hvi, ← hvj]
  have hvi0 : 0 < vi := by rw [hvi]; exact one_div_pos.2 hρi
  have hvj0 : 0 < vj := by rw [hvj]; exact one_div_pos.2 hρj
  have hvle : vj ≤ vi := by rw [hvi, hvj]; exact one_div_le_one_div_of_le hρi hle
  have hν : ∀ u k, mp G 0 u k = if G.Adj u k then 1 / ρ G u else 0 := mp0_apply
  -- sets
  have hinj1 : Set.InjOn Prod.fst (M : Set (V × V)) := fun e he e' he' h => hM.2.1 e he e' he' h
  have hinj2 : Set.InjOn Prod.snd (M : Set (V × V)) := fun e he e' he' h => hM.2.2 e he e' he' h
  have hMU : M.image Prod.fst ⊆ uniq G i j := fun x hx => by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx; exact (hM.1 e he).1
  have hMW : M.image Prod.snd ⊆ uniq G j i := fun y hy => by
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hy; exact (hM.1 e he).2.1
  have hcMU : (M.image Prod.fst).card = M.card := Finset.card_image_of_injOn hinj1
  have hcMW : (M.image Prod.snd).card = M.card := Finset.card_image_of_injOn hinj2
  have hcW : ((uniq G j i \ M.image Prod.snd).card : ℝ) = (uniq G j i).card - M.card := by
    have h := Finset.card_sdiff_add_card_eq_card hMW
    rw [hcMW] at h
    have h' : ((uniq G j i \ M.image Prod.snd).card : ℝ) + M.card = (uniq G j i).card := by
      exact_mod_cast h
    linarith only [h']
  have hUi := card_uniq_real hij
  have hUj := card_uniq_real hij.symm
  rw [tri_comm j i] at hUj
  have hm : (M.card : ℝ) ≤ (uniq G i j).card := by exact_mod_cast hM.card_le
  have ht0 : (0 : ℝ) ≤ tri G i j := Nat.cast_nonneg _
  have hρvi : ρ G i * vi = 1 := by rw [hvi]; field_simp
  have hρvj : ρ G j * vj = 1 := by rw [hvj]; field_simp
  obtain ⟨A, hA⟩ : ∃ x : ℝ, x = 1 - vi - vj - tri G i j * vj - M.card * vj := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ x : ℝ, x = 1 - vi - vj - tri G i j * vi - M.card * vj := ⟨_, rfl⟩
  rw [← hA, ← hB]
  obtain ⟨D, hD⟩ : ∃ x : ℝ, x = ((uniq G j i \ M.image Prod.snd).card : ℝ) * vj := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ x : ℝ, x = ((uniq G i j).card : ℝ) * vi - M.card * vj := ⟨_, rfl⟩
  -- identities (I1)–(I4)
  have hDA : D = A + vi := by
    rw [hD, hcW, hUj, hA]; linear_combination hρvj
  have hRB : R = B + vj := by
    rw [hR, hUi, hB]; linear_combination hρvi
  have hAB : A - B = tri G i j * (vi - vj) := by rw [hA, hB]; ring
  have hBA : B ≤ A := by
    have h := mul_nonneg ht0 (sub_nonneg.2 hvle)
    linarith only [hAB, h]
  have hD0 : 0 ≤ D := by rw [hD]; exact mul_nonneg (Nat.cast_nonneg _) hvj0.le
  have hR0 : 0 ≤ R := by
    rw [hR]
    linarith only [mul_le_mul_of_nonneg_right hm hvi0.le,
      mul_le_mul_of_nonneg_left hvle (Nat.cast_nonneg M.card : (0 : ℝ) ≤ M.card)]
  have hD' : D = 1 - vj - tri G i j * vj - M.card * vj := by rw [hDA, hA]; ring
  -- the three amounts sent into `W'`
  obtain ⟨a2, ha2⟩ : ∃ x : ℝ, x = D - max A 0 := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ x : ℝ, x = max A 0 - max B 0 := ⟨_, rfl⟩
  obtain ⟨a4, ha4⟩ : ∃ x : ℝ, x = max B 0 := ⟨_, rfl⟩
  have hsum234 : a2 + a3 + a4 = D := by rw [ha2, ha3, ha4]; ring
  have ha2le : a2 ≤ vi := by rw [ha2, hDA]; linarith only [le_max_left A 0]
  have ha20 : 0 ≤ a2 := by
    rw [ha2]; rcases le_total A 0 with h | h
    · rw [max_eq_right h]; linarith only [hD0]
    · rw [max_eq_left h, hDA]; linarith only [hvi0]
  have ha30 : 0 ≤ a3 := by rw [ha3]; linarith only [max_le_max hBA (le_refl (0 : ℝ))]
  have ha3le : a3 ≤ A - B := by rw [ha3]; exact pos_part_sub_le hBA
  have ha40 : 0 ≤ a4 := by rw [ha4]; exact le_max_right _ _
  have ha4le : a4 ≤ R := by
    rw [ha4, hRB]; rcases le_total B 0 with h | h
    · rw [max_eq_right h]; linarith only [hR0, hRB]
    · rw [max_eq_left h]; linarith only [hvj0]
  -- zero cases for the proportional splits
  have hDz : D = 0 → a2 = 0 ∧ a3 = 0 ∧ a4 = 0 := by
    intro h
    have hA' : A < 0 := by linarith only [h, hDA, hvi0]
    have hB' : B < 0 := by linarith only [hBA, hA']
    rw [ha2, ha3, ha4, max_eq_right hA'.le, max_eq_right hB'.le, h]
    exact ⟨by ring, by ring, rfl⟩
  have hABz : A - B = 0 → a3 = 0 := by
    intro h; rw [ha3, show A = B by linarith only [h]]; ring
  have hRz : R = 0 → a4 = 0 := by
    intro h; rw [ha4, max_eq_right (by linarith only [h, hRB, hvj0] : B ≤ 0)]
  -- membership helpers
  have hadjU : ∀ y, y ∈ uniq G j i \ M.image Prod.snd → G.Adj j y :=
    fun y hy => (mem_uniq.1 (Finset.mem_sdiff.1 hy).1).2.1
  have hWmass : ∀ x : ℝ, (D = 0 → x = 0) →
      ∑ y, (if y ∈ uniq G j i \ M.image Prod.snd then x / D * vj else 0) = x := by
    intro x hx
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    calc ((uniq G j i \ M.image Prod.snd).card : ℝ) * (x / D * vj) = x / D * D := by rw [hD]; ring
      _ = x := div_mul_of_zero_imp hx
  have hWnn : ∀ x : ℝ, 0 ≤ x → ∀ y,
      0 ≤ (if y ∈ uniq G j i \ M.image Prod.snd then x / D * vj else 0) := by
    intro x hx y; split_ifs
    · exact mul_nonneg (div_nonneg hx hD0) hvj0.le
    · exact le_rfl
  have hWpos : ∀ x : ℝ, ∀ y, 0 < (if y ∈ uniq G j i \ M.image Prod.snd then x / D * vj else 0) →
      y ∈ uniq G j i \ M.image Prod.snd := by
    intro x y h; by_contra hy; rw [ite_eq_right hy] at h; exact lt_irrefl _ h
  -- piece 0: keep `v_j` on `C`; piece 1: the matching
  have hκ0 : ∀ k, 0 ≤ (if k ∈ common G i j then vj else 0) := fun k => by
    split_ifs
    · exact hvj0.le
    · exact le_rfl
  have hP0 := isCoupling_diag hκ0
  have hP1 := matching_coupling hM vj hvj0.le
  have hC1 := matching_cost hd hM vj hvj0.le
  -- piece 2: `j → W'`
  obtain ⟨π2, hP2, hC2⟩ := exists_piece_coupling (d := d) (M := a2) (D := 1)
    (μ := fun x => if x = j then a2 else 0)
    (ν := fun y => if y ∈ uniq G j i \ M.image Prod.snd then a2 / D * vj else 0)
    (fun x => by split_ifs <;> first | exact ha20 | exact le_rfl) (hWnn _ ha20)
    (by simp [Finset.sum_ite_eq']) (hWmass _ fun h => (hDz h).1) zero_le_one
    (fun x y hx hy => by
      have hxj : x = j := by by_contra h; rw [ite_eq_right h] at hx; exact lt_irrefl _ hx
      rw [hxj]; exact (hd.adj (hadjU y (hWpos _ y hy))).le)
  -- piece 3: `C → W'` through `j`, in proportion to the residuals on `C`
  obtain ⟨π3, hP3, hC3⟩ := exists_piece_coupling (d := d) (M := a3) (D := 2)
    (μ := fun x => if x ∈ common G i j then a3 / (A - B) * (vi - vj) else 0)
    (ν := fun y => if y ∈ uniq G j i \ M.image Prod.snd then a3 / D * vj else 0)
    (fun x => by
      split_ifs
      · exact mul_nonneg (div_nonneg ha30 (by linarith only [hBA])) (by linarith only [hvle])
      · exact le_rfl)
    (hWnn _ ha30)
    (by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      calc ((common G i j).card : ℝ) * (a3 / (A - B) * (vi - vj)) = a3 / (A - B) * (A - B) := by
            rw [hAB, tri]; ring
        _ = a3 := div_mul_of_zero_imp hABz)
    (hWmass _ fun h => (hDz h).2.1) (by norm_num)
    (fun x y hx hy => by
      have hxC : x ∈ common G i j := by
        by_contra h; rw [ite_eq_right h] at hx; exact lt_irrefl _ hx
      exact hd.le_two (mem_common.1 hxC).2.symm (hadjU y (hWpos _ y hy)))
  -- piece 4: `U_i → W'` through `i, j`, in proportion to the residuals on `U_i`
  obtain ⟨π4, hP4, hC4⟩ := exists_piece_coupling (d := d) (M := a4) (D := 3)
    (μ := fun x => a4 / R * ((if x ∈ uniq G i j then vi else 0)
      - (if x ∈ M.image Prod.fst then vj else 0)))
    (ν := fun y => if y ∈ uniq G j i \ M.image Prod.snd then a4 / D * vj else 0)
    (fun x => by
      refine mul_nonneg (div_nonneg ha40 hR0) ?_
      by_cases hx : x ∈ M.image Prod.fst
      · rw [ite_eq_left (hMU hx), ite_eq_left hx]; linarith only [hvle]
      · rw [ite_eq_right hx, sub_zero]; split_ifs
        · exact hvi0.le
        · exact le_rfl)
    (hWnn _ ha40)
    (by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
        Finset.univ_inter, Finset.univ_inter, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
        nsmul_eq_mul, hcMU, ← hR]
      exact div_mul_of_zero_imp hRz)
    (hWmass _ fun h => (hDz h).2.2) (by norm_num)
    (fun x y hx hy => by
      have hxU : x ∈ uniq G i j := by
        by_contra h
        have h' : x ∉ M.image Prod.fst := fun h'' => h (hMU h'')
        rw [ite_eq_right h, ite_eq_right h', sub_zero, mul_zero] at hx
        exact lt_irrefl _ hx
      exact hd.le_three (mem_uniq.1 hxU).2.1.symm hij (hadjU y (hWpos _ y hy)))
  -- piece 5: everything left, into `i`
  have hrest : ∀ k, mp G 0 i k - (if k ∈ common G i j then vj else 0)
      - (if k ∈ M.image Prod.fst then vj else 0) - (if k = j then a2 else 0)
      - (if k ∈ common G i j then a3 / (A - B) * (vi - vj) else 0)
      - a4 / R * ((if k ∈ uniq G i j then vi else 0) - (if k ∈ M.image Prod.fst then vj else 0))
      = (if k = j then vi - a2 else 0)
        + (if k ∈ common G i j then (vi - vj) - a3 / (A - B) * (vi - vj) else 0)
        + (if k ∈ uniq G i j then (vi - (if k ∈ M.image Prod.fst then vj else 0))
            - a4 / R * (vi - (if k ∈ M.image Prod.fst then vj else 0)) else 0) := by
    intro k
    rw [hν, ← hvi]
    by_cases hkj : k = j
    · rw [hkj]
      have h1 : j ∉ common G i j := by simp [mem_common, SimpleGraph.irrefl]
      have h2 : j ∉ uniq G i j := by simp [mem_uniq]
      have h3 : j ∉ M.image Prod.fst := fun h => h2 (hMU h)
      simp only [ite_eq_left hij, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_true]; ring
    · by_cases hC : k ∈ common G i j
      · have h2 : k ∉ uniq G i j := fun h => (mem_uniq.1 h).2.2 (mem_common.1 hC).2
        have h3 : k ∉ M.image Prod.fst := fun h => h2 (hMU h)
        rw [ite_eq_left (mem_common.1 hC).1, ite_eq_left hC, ite_eq_right h3, ite_eq_right hkj, ite_eq_left hC, ite_eq_right h2,
          ite_eq_right hkj, ite_eq_left hC, ite_eq_right h2]; ring
      · by_cases hU : k ∈ uniq G i j
        · rw [ite_eq_left (mem_uniq.1 hU).2.1, ite_eq_right hC, ite_eq_right hkj, ite_eq_right hC, ite_eq_left hU,
            ite_eq_right hkj, ite_eq_right hC, ite_eq_left hU]; ring
        · have hna : ¬ G.Adj i k := fun ha => by
            by_cases hb : G.Adj j k
            · exact hC (mem_common.2 ⟨ha, hb⟩)
            · exact hU (mem_uniq.2 ⟨hkj, ha, hb⟩)
          have h3 : k ∉ M.image Prod.fst := fun h => hU (hMU h)
          rw [ite_eq_right hna, ite_eq_right hC, ite_eq_right h3, ite_eq_right hkj, ite_eq_right hC, ite_eq_right hU, ite_eq_right hkj,
            ite_eq_right hC, ite_eq_right hU]; ring
  have hfrac : ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → (y = 0 → x = 0) → x / y ≤ 1 := by
    intro x y hx hxy hz
    by_cases hy : y = 0
    · rw [hy, hz hy]; simp
    · rw [div_le_one (lt_of_le_of_ne (hx.trans hxy) (Ne.symm hy))]; exact hxy
  have hfr3 := hfrac ha30 ha3le hABz
  have hfr4 := hfrac ha40 ha4le hRz
  obtain ⟨π5, hP5, hC5⟩ := exists_piece_coupling (d := d) (M := vj) (D := 1)
    (μ := fun k => (if k = j then vi - a2 else 0)
        + (if k ∈ common G i j then (vi - vj) - a3 / (A - B) * (vi - vj) else 0)
        + (if k ∈ uniq G i j then (vi - (if k ∈ M.image Prod.fst then vj else 0))
            - a4 / R * (vi - (if k ∈ M.image Prod.fst then vj else 0)) else 0))
    (ν := fun y => if y = i then vj else 0)
    (fun k => by
      have e1 : 0 ≤ (if k = j then vi - a2 else 0) := by
        split_ifs
        · linarith only [ha2le]
        · exact le_rfl
      have e2 : 0 ≤ (if k ∈ common G i j then (vi - vj) - a3 / (A - B) * (vi - vj) else 0) := by
        split_ifs
        · linarith only [mul_le_mul_of_nonneg_right hfr3 (sub_nonneg.2 hvle)]
        · exact le_rfl
      have e3 : 0 ≤ (if k ∈ uniq G i j then (vi - (if k ∈ M.image Prod.fst then vj else 0))
          - a4 / R * (vi - (if k ∈ M.image Prod.fst then vj else 0)) else 0) := by
        have hres : 0 ≤ vi - (if k ∈ M.image Prod.fst then vj else 0) := by
          by_cases hk : k ∈ M.image Prod.fst
          · rw [ite_eq_left hk]; linarith only [hvle]
          · rw [ite_eq_right hk]; linarith only [hvi0]
        by_cases h1 : k ∈ uniq G i j
        · rw [ite_eq_left h1]
          linarith only [mul_le_mul_of_nonneg_right hfr4 hres]
        · simp only [ite_eq_right h1, le_refl]
      linarith only [e1, e2, e3])
    (fun y => by split_ifs <;> first | exact hvj0.le | exact le_rfl)
    (by
      -- total leftover mass equals `v_j`
      have htot : ∑ k, (mp G 0 i k - (if k ∈ common G i j then vj else 0)
          - (if k ∈ M.image Prod.fst then vj else 0) - (if k = j then a2 else 0)
          - (if k ∈ common G i j then a3 / (A - B) * (vi - vj) else 0)
          - a4 / R * ((if k ∈ uniq G i j then vi else 0) - (if k ∈ M.image Prod.fst then vj else 0)))
          = vj := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter,
          Finset.sum_const, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mp_sum hij]
        have hc : ((common G i j).card : ℝ) = tri G i j := rfl
        have e3 : a3 / (A - B) * (((common G i j).card : ℝ) * vi - ((common G i j).card : ℝ) * vj)
            = a3 := by
          rw [← mul_sub, hc, ← hAB]; exact div_mul_of_zero_imp hABz
        have e4 : a4 / R * (((uniq G i j).card : ℝ) * vi - ((M.image Prod.fst).card : ℝ) * vj) = a4 := by
          rw [hcMU, ← hR]; exact div_mul_of_zero_imp hRz
        rw [e3, e4, hcMU, hc]
        linarith only [hsum234, hD']
      exact (Finset.sum_congr rfl fun k _ => (hrest k).symm).trans htot)
    (by simp [Finset.sum_ite_eq']) zero_le_one
    (fun x y hx hy => by
      have hyi : y = i := by by_contra h; rw [ite_eq_right h] at hy; exact lt_irrefl _ hy
      rw [hyi]
      have hxa : G.Adj i x := by
        by_contra hna
        have hxj : x ≠ j := fun h => hna (by rw [h]; exact hij)
        have hxC : x ∉ common G i j := fun h => hna (mem_common.1 h).1
        have hxU : x ∉ uniq G i j := fun h => hna (mem_uniq.1 h).2.1
        rw [ite_eq_right hxj, ite_eq_right hxC, ite_eq_right hxU] at hx
        linarith only [hx]
      exact (hd.adj hxa.symm).le)
  -- glue the six pieces
  have hall := hP0.add (hP1.add (hP2.add (hP3.add (hP4.add hP5))))
  refine ⟨_, hall.congr (fun x => ?_) (fun y => ?_), ?_⟩
  · have := hrest x
    linarith only [this]
  · rw [hν, ← hvj]
    by_cases hyi : y = i
    · rw [hyi]
      have h1 : i ∉ common G i j := by simp [mem_common, SimpleGraph.irrefl]
      have h2 : i ∉ uniq G j i := by simp [mem_uniq]
      have h3 : i ∉ M.image Prod.snd := fun h => h2 (hMW h)
      have h4 : i ∉ uniq G j i \ M.image Prod.snd := fun h => h2 (Finset.mem_sdiff.1 h).1
      simp only [ite_eq_left hij.symm, ite_eq_right h1, ite_eq_right h3, ite_eq_right h4, ite_true]; ring
    · by_cases hC : y ∈ common G i j
      · have h2 : y ∉ uniq G j i := fun h => (mem_uniq.1 h).2.2 (mem_common.1 hC).1
        have h3 : y ∉ M.image Prod.snd := fun h => h2 (hMW h)
        have h4 : y ∉ uniq G j i \ M.image Prod.snd := fun h => h2 (Finset.mem_sdiff.1 h).1
        simp only [ite_eq_left (mem_common.1 hC).2, ite_eq_left hC, ite_eq_right h3, ite_eq_right h4, ite_eq_right hyi]; ring
      · by_cases hMy : y ∈ M.image Prod.snd
        · have h4 : y ∉ uniq G j i \ M.image Prod.snd := fun h => (Finset.mem_sdiff.1 h).2 hMy
          simp only [ite_eq_left (mem_uniq.1 (hMW hMy)).2.1, ite_eq_right hC, ite_eq_left hMy, ite_eq_right h4,
            ite_eq_right hyi]; ring
        · by_cases hW : y ∈ uniq G j i \ M.image Prod.snd
          · have hDpos : 0 < D := by
              rw [hD]; exact mul_pos (by exact_mod_cast Finset.card_pos.2 ⟨y, hW⟩) hvj0
            simp only [ite_eq_left (hadjU y hW), ite_eq_right hC, ite_eq_right hMy, ite_eq_left hW, ite_eq_right hyi]
            have key : a2 / D * vj + (a3 / D * vj + (a4 / D * vj + 0)) = (a2 + a3 + a4) / D * vj := by
              ring
            rw [zero_add, zero_add, key, hsum234, div_self hDpos.ne', one_mul]
          · have hna : ¬ G.Adj j y := fun ha => by
              by_cases hb : G.Adj i y
              · exact hC (mem_common.2 ⟨hb, ha⟩)
              · exact hW (Finset.mem_sdiff.2 ⟨mem_uniq.2 ⟨hyi, ha, hb⟩, hMy⟩)
            simp only [ite_eq_right hna, ite_eq_right hC, ite_eq_right hMy, ite_eq_right hW, ite_eq_right hyi]; ring
  · rw [cost_add, cost_diag hd.self, cost_add, cost_add, cost_add, cost_add]
    have hcard : (M.card : ℝ) * vj + D + vj = 1 - tri G i j * vj := by
      rw [hD']; ring
    linarith only [hC1, hC2, hC3, hC4, hC5, ha2, ha3, ha4, hcard]

lemma Lsq_comm (i j : V) : Lsq (G := G) i j = Lsq (G := G) j i := by
  unfold Lsq jlK jlZmax jlZmin matchStat ρmax ρmin
  rw [tri_comm i j, matchNum_comm i j, max_comm (ρ G i), min_comm (ρ G i)]
  ring_nf

/-- The greedy coupling of `ν_i, ν_j` from the proof of Theorem `thm:JL-plus-squares`. -/
lemma exists_jl_coupling (hd : GraphMetric G d) (hij : G.Adj i j) :
    ∃ π, IsCoupling (mp G 0 i) (mp G 0 j) π ∧ cost d π ≤ 1 - Lsq (G := G) i j := by
  -- the statement of `exists_jl_coupling_le` is `L^□` written out for `ρ_i ≤ ρ_j`
  have key : ∀ {a b : V}, G.Adj a b → ρ G a ≤ ρ G b →
      ∃ π, IsCoupling (mp G 0 a) (mp G 0 b) π ∧ cost d π ≤ 1 - Lsq (G := G) a b := by
    intro a b hab hle
    obtain ⟨M, hM, hMcard⟩ := exists_max_matching (G := G) a b
    obtain ⟨π, hπ, hc⟩ := exists_jl_coupling_le hd hab hle hM
    refine ⟨π, hπ, hc.trans (le_of_eq ?_)⟩
    unfold Lsq jlK jlZmax jlZmin matchStat ρmax ρmin
    rw [max_eq_right hle, min_eq_left hle, hMcard]
    ring_nf
  rcases le_total (ρ G i) (ρ G j) with hle | hle
  · exact key hij hle
  · obtain ⟨π, hπ, hc⟩ := key hij.symm hle
    refine ⟨fun x y => π y x, hπ.swap, ?_⟩
    rw [cost_swap hd.symm, Lsq_comm]
    exact hc

/-- **Theorem `thm:JL-plus-squares`.** -/
theorem jl_aug (hd : GraphMetric G d) (hij : G.Adj i j) : Lsq (G := G) i j ≤ cOR0 G d i j := by
  obtain ⟨π, hπ, hc⟩ := exists_jl_coupling hd hij
  have := W1_le_cost hd.nonneg hπ
  unfold cOR0 cORp; linarith

/-- `L^□` as the minimum of its three affine pieces. -/
lemma Lsq_eq_min (i j : V) (hle : ρmax G i j ≥ ρmin G i j) (hpos : 0 < ρmin G i j) :
    Lsq (G := G) i j = min (jlZmax (G := G) i j)
      (min (jlZmax (G := G) i j - (jlK (G := G) i j - jlZmax (G := G) i j - matchStat G i j))
        (jlZmax (G := G) i j - (jlK (G := G) i j - jlZmax (G := G) i j - matchStat G i j)
          - (jlK (G := G) i j - jlZmin (G := G) i j - matchStat G i j))) := by
  unfold Lsq
  apply neg_pos_parts_eq_min
  have : jlZmax (G := G) i j ≤ jlZmin (G := G) i j := by
    unfold jlZmax jlZmin
    exact div_le_div_of_nonneg_left (by positivity) hpos hle
  linarith

end jl

/-! ### Proposition `prop:bf-unclipped` (i): BF is the third affine piece -/

/-- With `𝒮` replaced by `𝔠₄/2`, the third piece of `L^□` is exactly `𝔠_BF`. -/
theorem bf_is_third_piece {i j : V} (hij : G.Adj i j) (h2 : ¬ ρmin G i j ≤ 1) :
    cBF G i j = jlZmax (G := G) i j
      - (jlK (G := G) i j - jlZmax (G := G) i j - C4 G i j / 2)
      - (jlK (G := G) i j - jlZmin (G := G) i j - C4 G i j / 2) := by
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  unfold cBF jlZmax jlZmin jlK bfS bfT
  rw [ite_eq_right h2]
  have e : (tri G i j : ℝ) / ρmax G i j + tri G i j / ρmax G i j + tri G i j / ρmin G i j
      = (2 / ρmax G i j + 1 / ρmin G i j) * tri G i j := by ring
  have e' : 2 / ρ G i + 2 / ρ G j = 2 * (1 / ρ G i + 1 / ρ G j) := by ring
  linarith [e, e']

/-! ### Proposition `prop:mixing-transfer` (B1) and its triangle-free corollary -/

section mixing

variable {i j : V}

/-- With `p = w_i` (`i` of larger degree) and `θ = (w_j − w_i)/(1 − w_i)`,
`m_j = (1 − θ) m_j^p + θ δ_j` pointwise. -/
lemma mLazy_mix (hij : G.Adj i j) (_hle : ρ G j ≤ ρ G i) (k : V) :
    mLazy G j k = (1 - (w G j - w G i) / (1 - w G i)) * mp G (w G i) j k
      + (w G j - w G i) / (1 - w G i) * dirac j k := by
  have h1w : 1 - w G i ≠ 0 := by linarith [w_lt_one (G := G) hij]
  have hθ : (1 - (w G j - w G i) / (1 - w G i)) * (1 - w G i) = 1 - w G j := by
    field_simp; ring
  rw [mLazy_apply hij.symm]
  unfold mp dirac
  by_cases hk : k = j
  · rw [ite_eq_left (Or.inl hk), ite_eq_left hk, ite_eq_left hk]
    field_simp; ring
  · rw [ite_eq_right hk, ite_eq_right hk]
    by_cases ha : G.Adj j k
    · rw [ite_eq_left (Or.inr ha), ite_eq_left ha, mul_zero, add_zero, mul_div_assoc', hθ]
      exact (lazy_nbr_weight hij.symm).symm
    · rw [ite_eq_right (not_or.2 ⟨hk, ha⟩), ite_eq_right ha, mul_zero, mul_zero, add_zero]

/-- `W₁(m_i^p, δ_j) ≤ p + (1 − p)(2 − q)` with `q = (2 + △)/ρ_i`, via the product coupling
with `δ_j` and the split `N(i) = {j} ⊔ C ⊔ U_i`. -/
lemma W1_to_dirac_le (hd : GraphMetric G d) (hij : G.Adj i j) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    W1 d (mp G p i) (dirac j) ≤ p + (1 - p) * (2 - (2 + tri G i j) / ρ G i) := by
  have hρ := ρ_pos hij
  have hρ0 : ρ G i ≠ 0 := hρ.ne'
  have hμ : ∀ x, 0 ≤ mp G p i x := mp_nonneg hp0 hp1 i
  have hπ : IsCoupling (mp G p i) (dirac j) (fun x y => mp G p i x * dirac j y) := by
    refine ⟨fun x y => mul_nonneg (hμ x) (by simp only [dirac]; split_ifs <;> norm_num),
      fun x => ?_, fun y => ?_⟩
    · simp [dirac, Finset.sum_ite_eq']
    · rw [← Finset.sum_mul, mp_sum hij, one_mul]
  refine (W1_le_cost hd.nonneg hπ).trans ?_
  have hcost : cost d (fun x y => mp G p i x * dirac j y) = ∑ x, mp G p i x * d x j := by
    unfold cost
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [dirac, mul_ite, Finset.sum_ite_eq', mul_comm]
  rw [hcost]
  have hsplit : ∀ x, mp G p i x * d x j =
      (if x = i then p * d i j else 0) + (if G.Adj i x then (1 - p) / ρ G i * d x j else 0) := by
    intro x
    by_cases h1 : x = i
    · rw [h1]; simp [mp, SimpleGraph.irrefl]
    · by_cases h2 : G.Adj i x <;> simp [mp, h1, h2]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_filter, ← SimpleGraph.neighborFinset_eq_filter, ← Finset.mul_sum,
    sum_nbr_split hij (fun k => d k j), hd.adj hij, hd.self]
  have hC : ∑ k ∈ common G i j, d k j = tri G i j := by
    rw [Finset.sum_congr rfl fun k hk => hd.adj (mem_common.1 hk).2.symm]
    simp [tri]
  have hU : ∑ k ∈ uniq G i j, d k j ≤ 2 * (uniq G i j).card := by
    calc ∑ k ∈ uniq G i j, d k j ≤ ∑ k ∈ uniq G i j, (2 : ℝ) :=
          Finset.sum_le_sum fun k hk => hd.le_two (mem_uniq.1 hk).2.1.symm hij
      _ = 2 * (uniq G i j).card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hcard := card_uniq_real hij
  have hc0 : 0 ≤ (1 - p) / ρ G i := div_nonneg (by linarith) hρ.le
  have hS : 0 + ∑ k ∈ common G i j, d k j + ∑ k ∈ uniq G i j, d k j
      ≤ 0 + tri G i j + 2 * (ρ G i - 1 - tri G i j) := by rw [hC]; linarith [hU, hcard]
  have key : (1 - p) / ρ G i * (0 + tri G i j + 2 * (ρ G i - 1 - tri G i j))
      = (1 - p) * (2 - (2 + tri G i j) / ρ G i) := by
    field_simp; ring
  linarith [mul_le_mul_of_nonneg_left hS hc0]

/-- `𝔠_LLY ≤ q = (2 + △)/ρ_max`: by Bourne et al. at `p₀ = w_i` and the overlap bound,
since `Σ min(m_i^{p₀}, m_j^{p₀}) ≤ (2 + △) p₀`. -/
lemma cLLY_le_q (hd : GraphMetric G d) (hB : BourneFact G d) (hij : G.Adj i j)
    (hle : ρ G j ≤ ρ G i) : cLLY G d i j ≤ (2 + tri G i j) / ρ G i := by
  classical
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  have hwi := w_pos (G := G) i
  have hwi1 : w G i < 1 := w_lt_one hij
  have hb := hB i j hij
  have hρmax : ρmax G i j = ρ G i := max_eq_left hle
  rw [hρmax] at hb
  have hp : (1 : ℝ) / (ρ G i + 1) = w G i := rfl
  rw [hp] at hb
  -- pointwise: `min(m_i^{p₀}, m_j^{p₀}) ≤ p₀ · 1_{overlap}`
  have hmem : ∀ k, k ∈ overlap (G := G) i j ↔ k = i ∨ k = j ∨ (G.Adj i k ∧ G.Adj j k) := by
    intro k; simp [overlap, mem_common]
  have hpt : ∀ k, min (mp G (w G i) i k) (mp G (w G i) j k)
      ≤ if k ∈ overlap (G := G) i j then w G i else 0 := by
    intro k
    have hmi : mp G (w G i) i k = mLazy G i k := rfl
    split_ifs with hk
    · refine (min_le_left _ _).trans (le_of_eq ?_)
      rw [hmi, mLazy_apply hij]
      have hk' : k = i ∨ G.Adj i k := by
        rcases (hmem k).1 hk with h | h | h
        · exact Or.inl h
        · exact Or.inr (by rw [h]; exact hij)
        · exact Or.inr h.1
      rw [ite_eq_left hk']
    · by_cases ha : G.Adj i k
      · have hj : ¬ G.Adj j k := fun hb' => hk ((hmem k).2 (Or.inr (Or.inr ⟨ha, hb'⟩)))
        have hkj : k ≠ j := fun h => hk ((hmem k).2 (Or.inr (Or.inl h)))
        refine (min_le_right _ _).trans (le_of_eq ?_)
        simp [mp, hkj, hj]
      · have hki : k ≠ i := fun h => hk ((hmem k).2 (Or.inl h))
        refine (min_le_left _ _).trans (le_of_eq ?_)
        rw [hmi, mLazy_apply hij, ite_eq_right (not_or.2 ⟨hki, ha⟩)]
  have hsum : ∑ k, min (mp G (w G i) i k) (mp G (w G i) j k) ≤ (2 + tri G i j) * w G i := by
    calc ∑ k, min (mp G (w G i) i k) (mp G (w G i) j k)
        ≤ ∑ k, (if k ∈ overlap (G := G) i j then w G i else 0) := Finset.sum_le_sum fun k _ => hpt k
      _ = (2 + tri G i j) * w G i := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, card_overlap hij]
  -- overlap bound on `W₁`
  have hne : ∃ π, IsCoupling (mp G (w G i) i) (mp G (w G i) j) π :=
    exists_coupling_prob (mp_nonneg hwi.le hwi1.le i) (mp_nonneg hwi.le hwi1.le j)
      (mp_sum hij) (mp_sum hij.symm)
  have hov := W1_ge_overlap (d := d) hne hd.self (fun x y h => hd.one_le h)
  rw [mp_sum hij] at hov
  unfold cORp at hb
  -- `(1 − w_i) 𝔠_LLY ≤ (2 + △) w_i`, and `1 − w_i = ρ_i w_i`
  have h1w : 1 - w G i = ρ G i * w G i := by
    have h1 : ρ G i + 1 ≠ 0 := by linarith
    simp only [w]; field_simp; ring
  have hineq : ρ G i * w G i * cLLY G d i j ≤ (2 + tri G i j) * w G i := by
    rw [← h1w]; linarith
  rw [le_div_iff₀ hρi]
  nlinarith

/-- **Proposition `prop:mixing-transfer` (B1).** For `ρ_i ≥ ρ_j`,
`𝔠_OR ≥ (1 − α_max) 𝔠_LLY − Δ(α)(1 − q)`. -/
theorem mixing_transfer (hd : GraphMetric G d) (hB : BourneFact G d) (hij : G.Adj i j)
    (hle : ρ G j ≤ ρ G i) :
    lamMix (w G j) (w G j - w G i) ((2 + tri G i j) / ρ G i) (cLLY G d i j) ≤ cOR G d i j := by
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  set p := w G i with hp
  set θ := (w G j - w G i) / (1 - w G i) with hθ
  have hwi := w_pos (G := G) i
  have hwle : w G i ≤ w G j := w_anti hle
  have hwi1 : w G i < 1 := by simp only [w]; rw [div_lt_one (by linarith)]; linarith
  have hwj1 : w G j ≤ 1 := by
    simp only [w]; rw [div_le_one (by linarith)]; linarith
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one (by linarith)]; linarith
  have hp1 : p ≤ 1 := hwi1.le
  -- couplings exist
  have h₁ : ∃ π, IsCoupling (mp G p i) (mp G p j) π :=
    exists_coupling_prob (mp_nonneg hwi.le hp1 i) (mp_nonneg hwi.le hp1 j) (mp_sum hij) (mp_sum hij.symm)
  have h₂ : ∃ π, IsCoupling (mp G p i) (dirac j) π := by
    refine exists_coupling_prob (mp_nonneg hwi.le hp1 i) (fun y => ?_) (mp_sum hij) ?_
    · simp only [dirac]; split_ifs <;> norm_num
    · simp [dirac]
  have hmix := W1_mix_le hd.nonneg hθ0 hθ1 h₁ h₂
  -- rewrite the mixtures
  have eμ : (fun x => (1 - θ) * mp G p i x + θ * mp G p i x) = mLazy G i := by
    funext x; simp only [mLazy, hp]; ring
  have eν : (fun y => (1 - θ) * mp G p j y + θ * dirac j y) = mLazy G j := by
    funext y; rw [mLazy_mix hij hle y]
  rw [eμ, eν] at hmix
  -- Bourne: `W₁(m_i^p, m_j^p) = 1 − (1 − p) 𝔠_LLY`, with `p = 1/(ρ_max + 1)`
  have hρmax : ρmax G i j = ρ G i := max_eq_left hle
  have hb := hB i j hij
  rw [hρmax] at hb
  have hW1p : W1 d (mp G p i) (mp G p j) = 1 - (1 - p) * cLLY G d i j := by
    have : p = 1 / (ρ G i + 1) := rfl
    rw [this]; unfold cORp at hb; linarith
  have hdir := W1_to_dirac_le hd hij p hwi.le hp1
  rw [hW1p] at hmix
  -- algebra
  have h1w : 1 - w G i ≠ 0 := by linarith
  have hkey2 : θ * (1 - p) = w G j - w G i := by
    rw [hθ, hp]; exact div_mul_cancel₀ _ h1w
  have hkey1 : (1 - θ) * (1 - p) = 1 - w G j := by
    rw [sub_mul, one_mul, hkey2, hp]; ring
  have hA : (1 - θ) * (1 - (1 - p) * cLLY G d i j) = (1 - θ) - (1 - w G j) * cLLY G d i j := by
    rw [← hkey1]; ring
  have hB : θ * (p + (1 - p) * (2 - (2 + tri G i j) / ρ G i))
      = θ * p + (w G j - w G i) * (2 - (2 + tri G i j) / ρ G i) := by
    rw [← hkey2]; ring
  have hC : (1 - θ) + θ * p = 1 - (w G j - w G i) := by
    rw [← hkey2]; ring
  have hdirθ := mul_le_mul_of_nonneg_left hdir hθ0
  unfold cOR lamMix
  nlinarith [hmix, hdirθ, hA, hB, hC]

/-- The mixing lift dominates the current lift on every valid input
(last sentence of Proposition `prop:mixing-transfer`). -/
theorem mixing_dominates (hd : GraphMetric G d) (hB : BourneFact G d) (hij : G.Adj i j)
    (hle : ρ G j ≤ ρ G i) {L : ℝ} (hL : L ≤ cLLY G d i j) :
    lamOld (w G i) (w G j) (w G j - w G i) L ≤
      lamMix (w G j) (w G j - w G i) ((2 + tri G i j) / ρ G i) L := by
  have hq := cLLY_le_q hd hB hij hle
  have hwle : w G i ≤ w G j := w_anti hle
  have hρi := ρ_pos hij
  have hq0 : 0 ≤ (2 + tri G i j) / ρ G i :=
    div_nonneg (by linarith [(Nat.cast_nonneg (tri G i j) : (0 : ℝ) ≤ tri G i j)]) hρi.le
  unfold lamOld lamMix
  split_ifs with h
  · -- `L ≥ 0`: the gain is `Δ (q − L) ≥ 0`
    nlinarith [mul_le_mul_of_nonneg_left (hL.trans hq) (by linarith : (0 : ℝ) ≤ w G j - w G i)]
  · -- `L < 0`: the gain is `Δ q ≥ 0`
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ w G j - w G i) hq0]

/-- **Corollary `cor:mixing-triangle-free`.** The triangle-free version: the mixing
transfer with `q` replaced by `2/ρ_max`, which needs no triangle count. -/
theorem mixing_triangle_free (hd : GraphMetric G d) (hB : BourneFact G d) (hij : G.Adj i j)
    (hle : ρ G j ≤ ρ G i) {L : ℝ} (hL : L ≤ cLLY G d i j) :
    lamMix (w G j) (w G j - w G i) (2 / ρ G i) L ≤ cOR G d i j := by
  refine le_trans ?_ (mixing_transfer hd hB hij hle)
  have hρi := ρ_pos hij
  have hwle : w G i ≤ w G j := w_anti hle
  have hwj1 : w G j ≤ 1 := by
    simp only [w]; rw [div_le_one (by linarith [ρ_pos (G := G) hij.symm])]
    linarith [ρ_pos (G := G) hij.symm]
  have hq : 2 / ρ G i ≤ (2 + tri G i j) / ρ G i :=
    div_le_div_of_nonneg_right (by linarith [(Nat.cast_nonneg (tri G i j) : (0 : ℝ) ≤ tri G i j)])
      hρi.le
  unfold lamMix
  nlinarith [mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ 1 - w G j),
    mul_le_mul_of_nonneg_left hq (by linarith : (0 : ℝ) ≤ w G j - w G i)]

end mixing

end OllivierBF
