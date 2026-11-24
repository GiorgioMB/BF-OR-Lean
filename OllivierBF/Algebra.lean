/-
  Real-number lemmas used by the main results. Nothing here mentions graphs:
  `a = min(d_i, d_j)`, `b = max(d_i, d_j)`, `t = t_{ij}`, `m = M_{ij}`, `s = σ_{ij} = M_{ij}/b`.
  `bS` and `bT` are `S` and `T` of the paper, `kappa1` and `kappa2` its slopes `λ₁` and `λ₂`.
-/
module

public import Mathlib

@[expose] public section

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

/-- The unclipped piece `S + T t + 2 s` (`= t/b − A − B`). -/
noncomputable def piece3 (a b t s : ℝ) : ℝ := bS a b + bT a b * t + 2 * s

/-- The mixing lift `Λ^mix` (Proposition `prop:mixing-transfer`). -/
noncomputable def lamMix (amax Δ q L : ℝ) : ℝ := (1 - amax) * L - Δ * (1 - q)

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

/-- `λ₁ ≤ λ₂`, i.e. triangles are the cheapest way to explain a BF value. -/
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

end lemmas

end OllivierBF
