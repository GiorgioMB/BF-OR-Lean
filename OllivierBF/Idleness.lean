/-
  Corollary 5.4 of the paper (uniform idleness). By Theorems 1.1 and 5.5 of Bourne et al. (2018),
  `κ_p = (1 − p) κ_LLY` for `p ∈ [1/(b + 1), 1]`, so `κ_p = (1 − p)/(1 − w_j) · κ_{w_j}` there
  (`idleness_lift`); at idleness `w_j = 1/(b + 1)` the residual vanishes at `i` and has no demand on
  `S = {i, j} ∪ C` (`resid_idle_at_i`, `resid_idle_overlap`), and bounds and signs transfer
  (`idleness_bounds`, `idleness_sign`).

  The published result is the hypothesis `BourneLinear`; it contains `BourneFact`, the case
  `p = 1/(b + 1)` used by the previous version (`BourneLinear.bourneFact`).
-/
module

public import OllivierBF.TQ

@[expose] public section

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Bourne et al. (2018), Theorems 1.1 and 5.5: on `[1/(b + 1), 1]`, `κ_p = (1 − p) κ_LLY`. -/
def BourneLinear (G : SimpleGraph V) [DecidableRel G.Adj] (d : V → V → ℝ) : Prop :=
  ∀ i j, G.Adj i j → ∀ p, 1 / (ρmax G i j + 1) ≤ p → p ≤ 1 →
    cORp G d p i j = (1 - p) * cLLY G d i j

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ} {i j : V}

lemma one_div_ρmax_lt_one (hij : G.Adj i j) : 1 / (ρmax G i j + 1) < 1 := by
  have hρ : 0 < ρmax G i j := lt_of_lt_of_le (ρ_pos hij) (le_max_left _ _)
  rw [div_lt_one (by linarith)]
  linarith

/-- `BourneLinear` contains `BourneFact`. -/
lemma BourneLinear.bourneFact (hB : BourneLinear G d) : BourneFact G d := by
  intro i j hij
  exact hB i j hij _ le_rfl (one_div_ρmax_lt_one hij).le

/-- **The lift.** On `[1/(b + 1), 1]`, `κ_p = (1 − p)/(1 − w_j) · κ_{w_j}`. -/
theorem idleness_lift (hB : BourneLinear G d) (hij : G.Adj i j) {p : ℝ}
    (hp0 : 1 / (ρmax G i j + 1) ≤ p) (hp1 : p ≤ 1) :
    cORp G d p i j
      = (1 - p) / (1 - 1 / (ρmax G i j + 1)) * cORp G d (1 / (ρmax G i j + 1)) i j := by
  have hne : 1 - 1 / (ρmax G i j + 1) ≠ 0 := by
    have := one_div_ρmax_lt_one hij
    linarith
  rw [hB i j hij p hp0 hp1, hB i j hij _ le_rfl (one_div_ρmax_lt_one hij).le, ← mul_assoc,
    div_mul_cancel₀ _ hne]

lemma w_eq_one_div_ρmax (hle : ρ G i ≤ ρ G j) : w G j = 1 / (ρmax G i j + 1) := by
  simp only [w, ρmax, max_eq_right hle]

/-- At idleness `w_j` the residual vanishes at `i`. -/
lemma resid_idle_at_i (hij : G.Adj i j) :
    resP (mp G (w G j)) i j i = 0 ∧ resN (mp G (w G j)) i j i = 0 := by
  have h1 : mp G (w G j) j i = w G j := by
    simp only [mp, if_neg hij.ne, if_pos hij.symm]
    exact lazy_nbr_weight hij.symm
  have h2 : mp G (w G j) i i = w G j := by simp [mp]
  unfold resP resN
  rw [h1, h2, min_self]
  constructor <;> ring

/-- At idleness `w_j`, with `d_i ≤ d_j`, the residual has no demand on `S = {i, j} ∪ C`. -/
lemma resid_idle_overlap (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) {k : V}
    (hk : k ∈ overlap (G := G) i j) : resN (mp G (w G j)) i j k = 0 := by
  have hρi := ρ_pos hij
  have hw1 : 0 ≤ 1 - w G j := by linarith [w_lt_one hij.symm]
  have hdiv : (1 - w G j) / ρ G j ≤ (1 - w G j) / ρ G i := by
    rw [div_eq_mul_one_div (1 - w G j) (ρ G j), div_eq_mul_one_div (1 - w G j) (ρ G i)]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hρi hle) hw1
  have hjj : (1 - w G j) / ρ G j = w G j := lazy_nbr_weight hij.symm
  suffices h : mp G (w G j) j k ≤ mp G (w G j) i k by
    unfold resN
    rw [min_eq_right h]
    ring
  simp only [overlap, Finset.mem_insert, mem_common] at hk
  rcases hk with hki | hkj | ⟨hik, hjk⟩
  · rw [hki]
    have e1 : mp G (w G j) j i = (1 - w G j) / ρ G j := by
      simp only [mp, if_neg hij.ne, if_pos hij.symm]
    have e2 : mp G (w G j) i i = w G j := by simp [mp]
    rw [e1, e2, hjj]
  · rw [hkj]
    have e3 : mp G (w G j) i j = (1 - w G j) / ρ G i := by
      simp only [mp, if_neg hij.ne', if_pos hij]
    have e4 : mp G (w G j) j j = w G j := by simp [mp]
    rw [e3, e4]
    linarith
  · have e5 : mp G (w G j) i k = (1 - w G j) / ρ G i := by
      simp only [mp, if_neg hik.ne', if_pos hik]
    have e6 : mp G (w G j) j k = (1 - w G j) / ρ G j := by
      simp only [mp, if_neg hjk.ne', if_pos hjk]
    rw [e5, e6]
    exact hdiv

/-- **Corollary 5.4 (bounds).** Bounds on `κ_{w_j}` transfer to every `p ∈ [w_j, 1]`. -/
theorem idleness_bounds (hB : BourneLinear G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j)
    {p lo up : ℝ} (hp0 : w G j ≤ p) (hp1 : p ≤ 1)
    (hlo : lo ≤ cORp G d (w G j) i j) (hup : cORp G d (w G j) i j ≤ up) :
    (1 - p) / (1 - w G j) * lo ≤ cORp G d p i j ∧
      cORp G d p i j ≤ (1 - p) / (1 - w G j) * up := by
  have hw := w_eq_one_div_ρmax (G := G) hle
  have hlift := idleness_lift hB hij (p := p) (by rw [← hw]; exact hp0) hp1
  rw [← hw] at hlift
  have hw1 : w G j < 1 := w_lt_one hij.symm
  have hc : 0 ≤ (1 - p) / (1 - w G j) := div_nonneg (by linarith) (by linarith)
  rw [hlift]
  exact ⟨mul_le_mul_of_nonneg_left hlo hc, mul_le_mul_of_nonneg_left hup hc⟩

/-- **Corollary 5.4 (sign).** For `p ∈ [w_j, 1)`, `κ_p` has the sign of `κ_{w_j}`. -/
theorem idleness_sign (hB : BourneLinear G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j)
    {p : ℝ} (hp0 : w G j ≤ p) (hp1 : p < 1) :
    cORp G d p i j < 0 ↔ cORp G d (w G j) i j < 0 := by
  have hw := w_eq_one_div_ρmax (G := G) hle
  have hlift := idleness_lift hB hij (p := p) (by rw [← hw]; exact hp0) hp1.le
  rw [← hw] at hlift
  have hw1 : w G j < 1 := w_lt_one hij.symm
  have hc : 0 < (1 - p) / (1 - w G j) := div_pos (by linarith) (by linarith)
  rw [hlift]
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    have := mul_nonneg hc.le h'
    linarith
  · intro h
    exact mul_neg_of_pos_of_neg hc h

end OllivierBF
