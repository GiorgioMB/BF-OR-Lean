/-
  Real-number lemmas used by the main results. Nothing here mentions graphs:
  `a = ρ_min`, `b = ρ_max`, `t = △(i,j)`, `m = 𝔪(i,j)`, `s = 𝔪/ρ_max`.
-/
import Mathlib

set_option linter.unusedSectionVars false

namespace OllivierBF

/-! ### Closed forms -/

/-- The lazy quadrangle bound `L^lazy` (Theorem `thm:lazy-quadrangle`). -/
noncomputable def Llazy (a b t m : ℝ) : ℝ := (3 + t) / (a + 1) + (3 + 2 * t + 2 * m) / (b + 1) - 2

/-- Its tree value `L^0`. -/
noncomputable def L0 (a b : ℝ) : ℝ := 3 / (a + 1) + 3 / (b + 1) - 2

noncomputable def bS (a b : ℝ) : ℝ := 2 / a + 2 / b - 2
noncomputable def bT (a b : ℝ) : ℝ := 2 / b + 1 / a
noncomputable def kappa1 (a b : ℝ) : ℝ := (1 / (a + 1) + 2 / (b + 1)) / bT a b
noncomputable def kappa2 (b : ℝ) : ℝ := b / (b + 1)

/-- The unclipped piece `𝔖 + 𝔗 t + 2 s` (`= 𝔷_max − A − B`). -/
noncomputable def piece3 (a b t s : ℝ) : ℝ := bS a b + bT a b * t + 2 * s

/-- The elementary lower modulus (Theorem `thm:bf-lower-elementary`), for `a ≥ 2`. -/
noncomputable def phiElem (a b ζ : ℝ) : ℝ :=
  let z := max (ζ - bS a b) 0
  L0 a b + kappa1 a b * min z (bT a b * (a - 1)) + kappa2 b * max (z - bT a b * (a - 1)) 0

/-- The current lift `Λ_ij` (Corollary `cor:symm-bound` (ii)), with `amin ≤ amax`. -/
noncomputable def lamOld (amin amax Δ L : ℝ) : ℝ :=
  if 0 ≤ L then (1 - amin) * L - Δ else (1 - amax) * L - Δ

/-- The mixing lift `Λ^mix` (Proposition `prop:mixing-transfer`). -/
noncomputable def lamMix (amax Δ q L : ℝ) : ℝ := (1 - amax) * L - Δ * (1 - q)

/-- The triangle-free version `Λ^tf` (Corollary `cor:mixing-triangle-free`). -/
noncomputable def lamTF (amin amax Δ b L : ℝ) : ℝ := max (lamOld amin amax Δ L) (lamMix amax Δ (2 / b) L)

section lemmas

variable {a b : ℝ}

lemma bT_pos (ha : 0 < a) (hb : 0 < b) : 0 < bT a b := by unfold bT; positivity

lemma Llazy_eq (ha : 0 < a) (hb : 0 < b) (t m : ℝ) :
    Llazy a b t m = L0 a b + kappa1 a b * bT a b * t + 2 * kappa2 b * (m / b) := by
  have hT := bT_pos ha hb
  have hT0 : bT a b ≠ 0 := hT.ne'
  have h1 : a + 1 ≠ 0 := by linarith
  have h2 : b + 1 ≠ 0 := by linarith
  have h3 : b ≠ 0 := hb.ne'
  unfold Llazy L0 kappa1 kappa2
  field_simp; ring

lemma kappa1_nonneg (ha : 0 < a) (hb : 0 < b) : 0 ≤ kappa1 a b := by
  have hT := bT_pos ha hb
  unfold kappa1
  exact div_nonneg (add_nonneg (div_nonneg zero_le_one (by linarith))
    (div_nonneg zero_le_two (by linarith))) hT.le

/-- `κ₁ ≤ κ₂`, i.e. triangles are the cheapest way to explain a BF value. -/
lemma kappa1_le_kappa2 (ha : 0 < a) (hab : a ≤ b) : kappa1 a b ≤ kappa2 b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hT := bT_pos ha hb
  have h0 : a ≠ 0 := ha.ne'
  have h1 : a + 1 ≠ 0 := by linarith
  have h2 : b + 1 ≠ 0 := by linarith
  have h3 : b ≠ 0 := hb.ne'
  have key : kappa2 b * bT a b - (1 / (a + 1) + 2 / (b + 1)) = (b - a) / (a * (a + 1) * (b + 1)) := by
    unfold kappa2 bT; field_simp; ring
  have hnn : 0 ≤ (b - a) / (a * (a + 1) * (b + 1)) := div_nonneg (by linarith) (by positivity)
  unfold kappa1
  rw [div_le_iff₀ hT]
  linarith

/-- The linear program behind the elementary modulus. -/
theorem phiElem_le (ha : 1 ≤ a) (hab : a ≤ b) {ζ t s : ℝ}
    (ht0 : 0 ≤ t) (hta : t ≤ a - 1) (hs : 0 ≤ s) (hc : ζ ≤ piece3 a b t s) :
    phiElem a b ζ ≤ L0 a b + kappa1 a b * bT a b * t + 2 * kappa2 b * s := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hT := bT_pos ha0 hb0
  have hk1 := kappa1_nonneg ha0 hb0
  have hk12 := kappa1_le_kappa2 ha0 hab
  have hk2 : 0 ≤ kappa2 b := by unfold kappa2; exact div_nonneg hb0.le (by linarith)
  have hcap : 0 ≤ bT a b * (a - 1) := mul_nonneg hT.le (by linarith)
  unfold phiElem piece3 at *
  simp only
  set c := ζ - bS a b with hcdef
  have hc' : c ≤ bT a b * t + 2 * s := by linarith
  rcases le_total (max c 0) (bT a b * (a - 1)) with hz | hz
  · rw [min_eq_left hz, max_eq_right (show max c 0 - bT a b * (a - 1) ≤ 0 by linarith)]
    have h1 : kappa1 a b * max c 0 ≤ kappa1 a b * (bT a b * t + 2 * s) := by
      apply mul_le_mul_of_nonneg_left _ hk1
      exact max_le hc' (add_nonneg (mul_nonneg hT.le ht0) (by linarith))
    have h2 : kappa1 a b * (2 * s) ≤ kappa2 b * (2 * s) :=
      mul_le_mul_of_nonneg_right hk12 (by linarith)
    nlinarith
  · rw [min_eq_right hz, max_eq_left (show 0 ≤ max c 0 - bT a b * (a - 1) by linarith)]
    have e1 : 0 ≤ (kappa2 b - kappa1 a b) * (bT a b * (a - 1 - t)) :=
      mul_nonneg (by linarith) (mul_nonneg hT.le (by linarith))
    have e3 : 0 ≤ kappa1 a b * (bT a b * t) := mul_nonneg hk1 (mul_nonneg hT.le ht0)
    have e4 : 0 ≤ kappa2 b * s := mul_nonneg hk2 hs
    rcases le_total c 0 with h | h
    · rw [max_eq_right h] at hz ⊢
      have hcap0 : bT a b * (a - 1) = 0 := le_antisymm hz hcap
      rw [hcap0]; nlinarith
    · rw [max_eq_left h] at hz ⊢
      have e2 : 0 ≤ kappa2 b * (bT a b * t + 2 * s - c) := mul_nonneg hk2 (by linarith)
      nlinarith

end lemmas

/-! ### Dominance identities (Theorems `thm:lazy-quadrangle`, `thm:bf-lower-elementary`) -/

section dominance

variable {a b t m : ℝ}

/-- `L^lazy − Λ^+(piece₃) = (b − a)(2a − 2 − t)/(a(a+1)(b+1))`. -/
lemma Llazy_sub_lamPlus (ha : 0 < a) (hb : 0 < b) :
    Llazy a b t m - ((1 - 1 / (b + 1)) * piece3 a b t (m / b) - (1 / (a + 1) - 1 / (b + 1)))
      = (b - a) * (2 * a - 2 - t) / (a * (a + 1) * (b + 1)) := by
  have h0 : a ≠ 0 := ha.ne'
  have h1 : a + 1 ≠ 0 := by linarith
  have h2 : b + 1 ≠ 0 := by linarith
  have h3 : b ≠ 0 := hb.ne'
  unfold Llazy piece3 bS bT; field_simp; ring

/-- `L^lazy − Λ^−(piece₃) = 2(b − a)(m + t + 1)/(b(a+1)(b+1))`. -/
lemma Llazy_sub_lamMinus (ha : 0 < a) (hb : 0 < b) :
    Llazy a b t m - ((1 - 1 / (a + 1)) * piece3 a b t (m / b) - (1 / (a + 1) - 1 / (b + 1)))
      = 2 * (b - a) * (m + t + 1) / (b * (a + 1) * (b + 1)) := by
  have h0 : a ≠ 0 := ha.ne'
  have h1 : a + 1 ≠ 0 := by linarith
  have h2 : b + 1 ≠ 0 := by linarith
  have h3 : b ≠ 0 := hb.ne'
  unfold Llazy piece3 bS bT; field_simp; ring

/-- `L^lazy − Λ^{tf,2}(piece₃) = 2(b − a)(m + t)/(b(a+1)(b+1))`. -/
lemma Llazy_sub_lamTF2 (ha : 0 < a) (hb : 0 < b) :
    Llazy a b t m - lamMix (1 / (a + 1)) (1 / (a + 1) - 1 / (b + 1)) (2 / b) (piece3 a b t (m / b))
      = 2 * (b - a) * (m + t) / (b * (a + 1) * (b + 1)) := by
  have h0 : a ≠ 0 := ha.ne'
  have h1 : a + 1 ≠ 0 := by linarith
  have h2 : b + 1 ≠ 0 := by linarith
  have h3 : b ≠ 0 := hb.ne'
  unfold Llazy lamMix piece3 bS bT; field_simp; ring

/-- `L^lazy − Λ^mix(piece₃) = (b − a)(2m + t)/(b(a+1)(b+1))`. -/
lemma Llazy_sub_lamMix (ha : 0 < a) (hb : 0 < b) :
    Llazy a b t m - lamMix (1 / (a + 1)) (1 / (a + 1) - 1 / (b + 1)) ((2 + t) / b) (piece3 a b t (m / b))
      = (b - a) * (2 * m + t) / (b * (a + 1) * (b + 1)) := by
  have h0 : a ≠ 0 := ha.ne'
  have h1 : a + 1 ≠ 0 := by linarith
  have h2 : b + 1 ≠ 0 := by linarith
  have h3 : b ≠ 0 := hb.ne'
  unfold Llazy lamMix piece3 bS bT; field_simp; ring

lemma lamOld_mono {amin amax Δ : ℝ} (h1 : amin ≤ amax) (h2 : amax ≤ 1) {x y : ℝ} (hxy : x ≤ y) :
    lamOld amin amax Δ x ≤ lamOld amin amax Δ y := by
  unfold lamOld
  split_ifs with hx hy hy
  · nlinarith
  · linarith
  · nlinarith
  · nlinarith

lemma lamMix_mono {amax Δ q : ℝ} (h : amax ≤ 1) {x y : ℝ} (hxy : x ≤ y) :
    lamMix amax Δ q x ≤ lamMix amax Δ q y := by
  unfold lamMix; nlinarith

lemma lamOld_eq_max {amin amax Δ L : ℝ} (h1 : amin ≤ amax) :
    lamOld amin amax Δ L = max ((1 - amin) * L - Δ) ((1 - amax) * L - Δ) := by
  unfold lamOld
  split_ifs with h
  · rw [max_eq_left]; nlinarith
  · rw [max_eq_right]; nlinarith

/-- `L^lazy` dominates the current lift of `piece₃`, for `a ≤ b` and `t ≤ a − 1`. -/
theorem lamOld_piece3_le (ha : 1 ≤ a) (hab : a ≤ b) (ht0 : 0 ≤ t) (hta : t ≤ a - 1) (hm : 0 ≤ m) :
    lamOld (1 / (b + 1)) (1 / (a + 1)) (1 / (a + 1) - 1 / (b + 1)) (piece3 a b t (m / b))
      ≤ Llazy a b t m := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hmin : 1 / (b + 1) ≤ 1 / (a + 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
  rw [lamOld_eq_max hmin]
  have e1 := Llazy_sub_lamPlus (t := t) (m := m) ha0 hb0
  have e2 := Llazy_sub_lamMinus (t := t) (m := m) ha0 hb0
  have n1 : 0 ≤ (b - a) * (2 * a - 2 - t) / (a * (a + 1) * (b + 1)) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  have n2 : 0 ≤ 2 * (b - a) * (m + t + 1) / (b * (a + 1) * (b + 1)) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) (by positivity)
  exact max_le (by linarith) (by linarith)

theorem lamTF_piece3_le (ha : 1 ≤ a) (hab : a ≤ b) (ht0 : 0 ≤ t) (hta : t ≤ a - 1) (hm : 0 ≤ m) :
    lamTF (1 / (b + 1)) (1 / (a + 1)) (1 / (a + 1) - 1 / (b + 1)) b (piece3 a b t (m / b))
      ≤ Llazy a b t m := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have e := Llazy_sub_lamTF2 (t := t) (m := m) ha0 hb0
  have n : 0 ≤ 2 * (b - a) * (m + t) / (b * (a + 1) * (b + 1)) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) (by positivity)
  exact max_le (lamOld_piece3_le ha hab ht0 hta hm) (by linarith)

theorem lamMix_piece3_le (ha : 1 ≤ a) (hab : a ≤ b) (ht0 : 0 ≤ t) (hm : 0 ≤ m) :
    lamMix (1 / (a + 1)) (1 / (a + 1) - 1 / (b + 1)) ((2 + t) / b) (piece3 a b t (m / b))
      ≤ Llazy a b t m := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have e := Llazy_sub_lamMix (t := t) (m := m) ha0 hb0
  have n : 0 ≤ (b - a) * (2 * m + t) / (b * (a + 1) * (b + 1)) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  linarith

end dominance

/-! ### The augmented JL bound as a minimum of three affine pieces -/

lemma neg_pos_parts_eq_min {Z A B : ℝ} (hAB : B ≤ A) :
    -max A 0 - max B 0 + Z = min Z (min (Z - A) (Z - A - B)) := by
  rcases le_total A 0 with hA | hA
  · have hB : B ≤ 0 := le_trans hAB hA
    rw [max_eq_right hA, max_eq_right hB, min_eq_left (le_min (by linarith) (by linarith))]
    ring
  · rcases le_total B 0 with hB | hB
    · rw [max_eq_left hA, max_eq_right hB, min_eq_right ((min_le_left _ _).trans (by linarith)),
        min_eq_left (by linarith)]
      ring
    · rw [max_eq_left hA, max_eq_left hB, min_eq_right ((min_le_left _ _).trans (by linarith)),
        min_eq_right (by linarith)]
      ring

/-- `[x]_+ − [x − S]_+ = min{S, [x]_+}` for `S ≥ 0` (Remark `rem:coarse-C4`). -/
lemma pos_part_sub_pos_part {x S : ℝ} (hS : 0 ≤ S) :
    max x 0 - max (x - S) 0 = min S (max x 0) := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_right (by linarith), min_eq_right hS]; ring
  · rw [max_eq_left h]
    rcases le_total (x - S) 0 with h' | h'
    · rw [max_eq_right h', min_eq_right (by linarith)]; ring
    · rw [max_eq_left h', min_eq_left (by linarith)]; ring

/-! ### Inverting the minimum of three increasing affine functions (Appendix C) -/

/-- If `min{ℓ₁, ℓ₂, ℓ₃}(t) ≤ s` with positive slopes, then `t` is at most the largest
of the three solutions. -/
lemma le_max_solutions {t s c₁ c₂ c₃ k₁ k₂ k₃ : ℝ} (h₁ : 0 < k₁) (h₂ : 0 < k₂) (h₃ : 0 < k₃)
    (h : min (c₁ + k₁ * t) (min (c₂ + k₂ * t) (c₃ + k₃ * t)) ≤ s) :
    t ≤ max ((s - c₁) / k₁) (max ((s - c₂) / k₂) ((s - c₃) / k₃)) := by
  rcases min_le_iff.1 h with h | h
  · exact le_max_of_le_left (by rw [le_div_iff₀ h₁]; nlinarith)
  · rcases min_le_iff.1 h with h | h
    · exact le_max_of_le_right (le_max_of_le_left (by rw [le_div_iff₀ h₂]; nlinarith))
    · exact le_max_of_le_right (le_max_of_le_right (by rw [le_div_iff₀ h₃]; nlinarith))

end OllivierBF
