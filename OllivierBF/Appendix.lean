/-
  Appendix B (comparison with Bhattacharya–Mukherjee) and Appendix C (reverse direction:
  what an OR value certifies about BF), rebuilt on the bounds of `Bounds.lean`.
-/
module

public import OllivierBF.Interval

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ} {i j : V}

/-! ### Appendix B -/

/-- The bound of Bhattacharya and Mukherjee (2015, Thm 5.1), with their matching number
between the non-common neighbourhoods written as `min{|U_i| + 1, |U_j| + 1, 𝔪 + 2}`
(Remark `rem:bm-comparison`). -/
noncomputable def LBM (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) : ℝ :=
  let M : ℝ := min (min (((uniq G i j).card : ℝ) + 1) (((uniq G j i).card : ℝ) + 1))
    ((matchNum G i j : ℝ) + 2)
  jlZmax (G := G) i j - 2 * (1 - (M + tri G i j) / ρmax G i j)

section bmCore

variable {a b t m : ℝ}

/-- Algebraic core of Appendix B, with `a = ρ_min`, `b = ρ_max`, `t = △`, `m = 𝔪`, and the
integrality alternative `m < |U_min|` or `m = |U_min| = a − 1 − t`. -/
lemma bm_core (ha : 1 ≤ a) (hab : a ≤ b) (ht : 0 ≤ t) (hm : 0 ≤ m)
    (hint : m + 1 ≤ a - 1 - t ∨ m = a - 1 - t) :
    t / b - 2 * (1 - (min (a - t) (m + 2) + t) / b)
      ≤ -max (1 - 1 / a - 1 / b - t / b - m / b) 0 - max (1 - 1 / a - 1 / b - t / a - m / b) 0
        + t / b := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have ha0' : a ≠ 0 := ha0.ne'
  have hb0' : b ≠ 0 := hb0.ne'
  have hx : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0.ne'
  have hy : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0.ne'
  have hx0 : 0 < a⁻¹ := inv_pos.2 ha0
  have hy0 : 0 < b⁻¹ := inv_pos.2 hb0
  have hyx : b⁻¹ ≤ a⁻¹ := inv_anti₀ ha0 hab
  have hAB : 1 - 1 / a - 1 / b - t / a - m / b ≤ 1 - 1 / a - 1 / b - t / b - m / b := by
    have : t / b ≤ t / a := div_le_div_of_nonneg_left ht ha0 hab
    linarith
  rw [neg_pos_parts_eq_min hAB]
  rcases hint with h | h
  · rw [min_eq_right (by linarith : m + 2 ≤ a - t)]
    refine le_min ?_ (le_min ?_ ?_) <;> simp only [div_eq_mul_inv, one_mul]
    · nlinarith [mul_le_mul_of_nonneg_right (by linarith : m + 2 + t ≤ b) hy0.le]
    · nlinarith [mul_le_mul_of_nonneg_right (by linarith : m + t + 3 ≤ a + 1) hy0.le,
        mul_le_mul_of_nonneg_left hyx ha0.le]
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 + t) (sub_nonneg.2 hyx)]
  · subst h
    rw [min_eq_left (by linarith : a - t ≤ a - 1 - t + 2)]
    refine le_min ?_ (le_min ?_ ?_) <;> simp only [div_eq_mul_inv, one_mul]
    · nlinarith [mul_le_mul_of_nonneg_right hab hy0.le]
    · nlinarith [mul_le_mul_of_nonneg_right hab hy0.le]
    · nlinarith [mul_nonneg ht (sub_nonneg.2 hyx)]

/-- Equality in `bm_core` holds exactly when `a = b`. -/
lemma bm_core_eq_iff (ha : 1 ≤ a) (hab : a ≤ b) (ht : 0 ≤ t) (hm : 0 ≤ m)
    (hint : m + 1 ≤ a - 1 - t ∨ m = a - 1 - t) :
    t / b - 2 * (1 - (min (a - t) (m + 2) + t) / b)
      = -max (1 - 1 / a - 1 / b - t / b - m / b) 0 - max (1 - 1 / a - 1 / b - t / a - m / b) 0
        + t / b ↔ a = b := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have ha0' : a ≠ 0 := ha0.ne'
  have hb0' : b ≠ 0 := hb0.ne'
  have hx : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0.ne'
  have hy : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0.ne'
  have hx0 : 0 < a⁻¹ := inv_pos.2 ha0
  have hy0 : 0 < b⁻¹ := inv_pos.2 hb0
  have hAB : 1 - 1 / a - 1 / b - t / a - m / b ≤ 1 - 1 / a - 1 / b - t / b - m / b := by
    have : t / b ≤ t / a := div_le_div_of_nonneg_left ht ha0 hab
    linarith
  have hle := bm_core ha hab ht hm hint
  rw [neg_pos_parts_eq_min hAB] at hle ⊢
  constructor
  · -- if `a < b`, every piece is strictly above the BM bound
    intro heq
    by_contra hne
    have hlt : a < b := lt_of_le_of_ne hab hne
    have hyx : b⁻¹ < a⁻¹ := inv_strictAnti₀ ha0 hlt
    have hstrict : t / b - 2 * (1 - (min (a - t) (m + 2) + t) / b) <
        min (t / b) (min (t / b - (1 - 1 / a - 1 / b - t / b - m / b))
          (t / b - (1 - 1 / a - 1 / b - t / b - m / b) - (1 - 1 / a - 1 / b - t / a - m / b))) := by
      rcases hint with h | h
      · rw [min_eq_right (by linarith : m + 2 ≤ a - t)]
        refine lt_min ?_ (lt_min ?_ ?_) <;> simp only [div_eq_mul_inv, one_mul]
        · nlinarith [mul_lt_mul_of_pos_right hlt hy0,
            mul_le_mul_of_nonneg_right (by linarith : m + 2 + t ≤ a) hy0.le]
        · nlinarith [mul_le_mul_of_nonneg_right (by linarith : m + t + 3 ≤ a + 1) hy0.le,
            mul_lt_mul_of_pos_left hyx ha0]
        · nlinarith [mul_pos (by linarith : (0 : ℝ) < 2 + t) (sub_pos.2 hyx)]
      · subst h
        rw [min_eq_left (by linarith : a - t ≤ a - 1 - t + 2)]
        refine lt_min ?_ (lt_min ?_ ?_) <;> simp only [div_eq_mul_inv, one_mul]
        · nlinarith [mul_lt_mul_of_pos_right hlt hy0]
        · nlinarith [mul_lt_mul_of_pos_right hlt hy0]
        · nlinarith [mul_nonneg ht (sub_nonneg.2 hyx.le)]
    exact absurd heq hstrict.ne
  · -- if `a = b`, one piece coincides with the BM bound
    intro hab'
    subst hab'
    refine le_antisymm hle ?_
    rcases hint with h | h
    · rw [min_eq_right (by linarith : m + 2 ≤ a - t)]
      refine (min_le_right _ _).trans ((min_le_right _ _).trans (le_of_eq ?_))
      field_simp; ring
    · subst h
      rw [min_eq_left (by linarith : a - t ≤ a - 1 - t + 2)]
      refine (min_le_left _ _).trans (le_of_eq ?_)
      field_simp; ring

end bmCore

/-- Reduce `L^BM` and `L^□` to the algebraic core. -/
lemma LBM_Lsq_reduce (hij : G.Adj i j) :
    ∃ a b t m : ℝ, 1 ≤ a ∧ a ≤ b ∧ 0 ≤ t ∧ 0 ≤ m ∧ (m + 1 ≤ a - 1 - t ∨ m = a - 1 - t) ∧
      (a = b ↔ ρ G i = ρ G j) ∧
      LBM G i j = t / b - 2 * (1 - (min (a - t) (m + 2) + t) / b) ∧
      Lsq (G := G) i j = -max (1 - 1 / a - 1 / b - t / b - m / b) 0
        - max (1 - 1 / a - 1 / b - t / a - m / b) 0 + t / b := by
  have hUi := card_uniq_add hij
  have hUj := card_uniq_add hij.symm
  rw [tri_comm j i] at hUj
  have hmi : matchNum G i j ≤ (uniq G i j).card := matchNum_le_uniq
  have hmj : matchNum G i j ≤ (uniq G j i).card := by
    rw [matchNum_comm]; exact matchNum_le_uniq
  -- real versions
  have hρi : ρ G i = ((uniq G i j).card : ℝ) + 1 + tri G i j := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hUi
    simp only [ρ]; push_cast at h; linarith
  have hρj : ρ G j = ((uniq G j i).card : ℝ) + 1 + tri G i j := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hUj
    simp only [ρ]; push_cast at h; linarith
  refine ⟨ρmin G i j, ρmax G i j, tri G i j, matchNum G i j, ?_, min_le_max, Nat.cast_nonneg _,
    Nat.cast_nonneg _, ?_, ?_, ?_, ?_⟩
  · unfold ρmin; rw [hρi, hρj]
    exact le_min (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ (uniq G i j).card),
      (Nat.cast_nonneg _ : (0 : ℝ) ≤ tri G i j)])
      (by linarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ (uniq G j i).card),
      (Nat.cast_nonneg _ : (0 : ℝ) ≤ tri G i j)])
  · -- integrality: `𝔪 < |U_min|` or `𝔪 = |U_min|`
    have hu : (ρmin G i j) - 1 - tri G i j
        = ((min (uniq G i j).card (uniq G j i).card : ℕ) : ℝ) := by
      unfold ρmin; rw [hρi, hρj]; push_cast
      rw [min_add_add_right, min_add_add_right]; ring
    rw [hu]
    have : matchNum G i j + 1 ≤ min (uniq G i j).card (uniq G j i).card ∨
        matchNum G i j = min (uniq G i j).card (uniq G j i).card := by omega
    rcases this with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  · unfold ρmin ρmax
    constructor
    · intro h
      rcases le_total (ρ G i) (ρ G j) with h' | h'
      · rw [min_eq_left h', max_eq_right h'] at h; exact h
      · rw [min_eq_right h', max_eq_left h'] at h; exact h.symm
    · intro h; rw [h, min_self, max_self]
  · unfold LBM jlZmax
    simp only
    have : min (min (((uniq G i j).card : ℝ) + 1) (((uniq G j i).card : ℝ) + 1))
        ((matchNum G i j : ℝ) + 2) = min (ρmin G i j - tri G i j) ((matchNum G i j : ℝ) + 2) := by
      congr 1
      unfold ρmin; rw [hρi, hρj, ← min_sub_sub_right]; congr 1 <;> ring
    rw [this]
  · unfold Lsq jlK jlZmax jlZmin matchStat
    have hsum : 1 / ρ G i + 1 / ρ G j = 1 / ρmin G i j + 1 / ρmax G i j := by
      unfold ρmin ρmax
      rcases le_total (ρ G i) (ρ G j) with h | h
      · rw [min_eq_left h, max_eq_right h]
      · rw [min_eq_right h, max_eq_left h]; ring
    have e1 : 1 - 1 / ρ G i - 1 / ρ G j = 1 - 1 / ρmin G i j - 1 / ρmax G i j := by linarith
    rw [e1]

/-- **Appendix B: `L^□ ≥ L^BM`.** -/
theorem LBM_le_Lsq (hij : G.Adj i j) : LBM G i j ≤ Lsq (G := G) i j := by
  obtain ⟨a, b, t, m, ha, hab, ht, hm, hint, -, hL, hR⟩ := LBM_Lsq_reduce hij
  rw [hL, hR]; exact bm_core ha hab ht hm hint

/-- **Appendix B: equality holds exactly on edges with equal degrees.** -/
theorem LBM_eq_Lsq_iff (hij : G.Adj i j) : LBM G i j = Lsq (G := G) i j ↔ ρ G i = ρ G j := by
  obtain ⟨a, b, t, m, ha, hab, ht, hm, hint, hiff, hL, hR⟩ := LBM_Lsq_reduce hij
  rw [hL, hR, ← hiff]; exact bm_core_eq_iff ha hab ht hm hint

/-! ### Appendix C: the reverse direction -/

/-- **OR → BF, via the triangle-free mixing transfer and Topping et al.** For `ρ_i ≥ ρ_j`,
`𝔠_OR ≤ ϑ` implies `𝔠_BF ≤ (ϑ + Δ(α)(1 − 2/ρ_max))/(1 − α_max)`. -/
theorem or_to_bf_mixing (hd : GraphMetric G d) (cited : CitedFacts G d) (hij : G.Adj i j)
    (hle : ρ G j ≤ ρ G i) {ϑ : ℝ} (h : cOR G d i j ≤ ϑ) :
    cBF G i j ≤ (ϑ + (w G j - w G i) * (1 - 2 / ρ G i)) / (1 - w G j) := by
  have hmix := mixing_transfer hd cited.bourne hij hle
  have htop := cited.topping i j hij
  have hρi := ρ_pos hij
  have hwle : w G i ≤ w G j := w_anti hle
  have hwj1 : w G j < 1 := w_lt_one hij.symm
  have hq : 2 / ρ G i ≤ (2 + tri G i j) / ρ G i :=
    div_le_div_of_nonneg_right (by linarith [(Nat.cast_nonneg (tri G i j) : (0 : ℝ) ≤ tri G i j)])
      hρi.le
  unfold lamMix at hmix
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hq (by linarith : (0 : ℝ) ≤ w G j - w G i),
    mul_le_mul_of_nonneg_left htop (by linarith : (0 : ℝ) ≤ 1 - w G j), h, hmix]

/-- `L^lazy = L⁰ + c_△ △ + 2𝔪/(ρ_max + 1)`, with `c_△ = 1/(ρ_min + 1) + 2/(ρ_max + 1)`. -/
lemma Llazy_affine (a b t m : ℝ) :
    Llazy a b t m = L0 a b + (1 / (a + 1) + 2 / (b + 1)) * t + 2 * m / (b + 1) := by
  unfold Llazy L0; ring

/-- **OR → BF, elementary (from the lazy quadrangle bound).** For `2 ≤ ρ_i ≤ ρ_j`,
`𝔠_OR ≤ ϑ` caps the triangle count and hence `𝔠_BF`. -/
theorem or_to_bf_elementary (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j)
    (h2 : 2 ≤ ρ G i) {ϑ : ℝ} (h : cOR G d i j ≤ ϑ) :
    cBF G i j ≤ bfS G i j + bfT G i j * min (ρ G i - 1)
      (max (ϑ - L0 (ρ G i) (ρ G j) - 2 * matchNum G i j / (ρ G j + 1)) 0
        / (1 / (ρ G i + 1) + 2 / (ρ G j + 1))) + C4 G i j := by
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  have hq := lazy_quadrangle hd hij hle
  rw [Llazy_affine] at hq
  have hc : 0 < 1 / (ρ G i + 1) + 2 / (ρ G j + 1) :=
    add_pos (div_pos one_pos (by linarith)) (div_pos two_pos (by linarith))
  have ht : (tri G i j : ℝ) ≤ max (ϑ - L0 (ρ G i) (ρ G j) - 2 * matchNum G i j / (ρ G j + 1)) 0
      / (1 / (ρ G i + 1) + 2 / (ρ G j + 1)) := by
    rw [le_div_iff₀ hc]
    have := le_max_left (ϑ - L0 (ρ G i) (ρ G j) - 2 * matchNum G i j / (ρ G j + 1)) 0
    nlinarith [h, hq, this]
  have hmin : ¬ ρmin G i j ≤ 1 := by rw [ρmin_eq hle]; linarith
  unfold cBF
  rw [ite_eq_right hmin]
  have hT := bfT_pos' hij
  nlinarith [mul_le_mul_of_nonneg_left (le_min (tri_le hij) ht) hT.le]

/-- **OR → BF, lower direction (from the zero-cost cap of the envelope).** For
`2 ≤ ρ_i ≤ ρ_j`, `𝔠_OR ≥ ϑ` forces `△ ≥ ϑ(ρ_max + 1) − 2`, hence a lower bound on BF. -/
theorem or_to_bf_lower (hd : GraphMetric G d) (cited : CitedFacts G d) (hij : G.Adj i j)
    (hle : ρ G i ≤ ρ G j) (h2 : 2 ≤ ρ G i) {ϑ : ℝ} (h : ϑ ≤ cOR G d i j) :
    bfS G i j + bfT G i j * max (ϑ * (ρ G j + 1) - 2) 0 ≤ cBF G i j := by
  have hρj := ρ_pos hij.symm
  have henv := lazy_envelope hd cited hij hle
  have hcap := henv.trans (min_le_left _ _)
  have hwj : w G j = 1 / (ρ G j + 1) := rfl
  have ht : max (ϑ * (ρ G j + 1) - 2) 0 ≤ tri G i j := by
    refine max_le ?_ (Nat.cast_nonneg _)
    have h' : ϑ ≤ (2 + tri G i j) * (1 / (ρ G j + 1)) := by
      have := h.trans hcap; rwa [hwj] at this
    rw [mul_one_div, le_div_iff₀ (by linarith)] at h'
    linarith
  have hmin : ¬ ρmin G i j ≤ 1 := by rw [ρmin_eq hle]; linarith
  unfold cBF
  rw [ite_eq_right hmin]
  have hT := bfT_pos' hij
  nlinarith [mul_le_mul_of_nonneg_left ht hT.le, C4_nonneg (G := G) hij]


/-! ### Appendix C: the coverage envelope and the remaining reverse bounds -/

/-- The coverage envelope `Θ_ij(t)` of Proposition `prop:coverage-envelope-monotone`
(for `ρ_i ≤ ρ_j`). -/
noncomputable def Theta (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (t : ℝ) : ℝ :=
  min ((2 + t) * w G j)
    (-1 + 2 * ((2 + t) * w G j) + (w G i - w G j) + min (t * (w G i - w G j)) ((ρ G j - 1 - t) * w G j)
      + min (min ((ρ G i - 1 - t) * w G i) ((ρ G j - 1 - t) * w G j))
          ((ρ G i + ρ G j - 2 - 2 * t) / (1 / w G i + 1 / w G j)))

/-- The cross-edge caps without the BF budget. -/
lemma xi_caps_le_noBF (hij : G.Adj i j) :
    min ((xi G i j).card * w G i) ((xi G j i).card * w G j) ≤
      min (min ((ρ G i - 1 - tri G i j) * w G i) ((ρ G j - 1 - tri G i j) * w G j))
        ((ρ G i + ρ G j - 2 - 2 * tri G i j) / (1 / w G i + 1 / w G j)) := by
  have hwi := w_pos (G := G) i
  have hwj := w_pos (G := G) j
  have hsig : 0 < 1 / w G i + 1 / w G j := add_pos (one_div_pos.2 hwi) (one_div_pos.2 hwj)
  have hX : ((xi G i j).card : ℝ) ≤ ρ G i - 1 - tri G i j := by
    rw [← card_uniq_real hij]; exact_mod_cast Finset.card_le_card (xi_subset i j)
  have hY : ((xi G j i).card : ℝ) ≤ ρ G j - 1 - tri G i j := by
    rw [tri_comm, ← card_uniq_real hij.symm]; exact_mod_cast Finset.card_le_card (xi_subset j i)
  have hm1 := min_le_left ((xi G i j).card * w G i) ((xi G j i).card * w G j)
  have hm2 := min_le_right ((xi G i j).card * w G i) ((xi G j i).card * w G j)
  have hharm : min ((xi G i j).card * w G i) ((xi G j i).card * w G j)
      ≤ (Xi G i j : ℝ) / (1 / w G i + 1 / w G j) := by
    rw [le_div_iff₀ hsig]
    have e1 : min ((xi G i j).card * w G i) ((xi G j i).card * w G j) * (1 / w G i)
        ≤ (xi G i j).card := by rw [mul_one_div, div_le_iff₀ hwi]; exact hm1
    have e2 : min ((xi G i j).card * w G i) ((xi G j i).card * w G j) * (1 / w G j)
        ≤ (xi G j i).card := by rw [mul_one_div, div_le_iff₀ hwj]; exact hm2
    simp only [Xi]; push_cast
    rw [mul_add]; linarith
  refine le_min (le_min ?_ ?_) ?_
  · exact hm1.trans (mul_le_mul_of_nonneg_right hX hwi.le)
  · exact hm2.trans (mul_le_mul_of_nonneg_right hY hwj.le)
  · exact hharm.trans (div_le_div_of_nonneg_right (Xi_le hij) hsig.le)

/-- **Proposition `prop:coverage-envelope-monotone`.** -/
theorem coverage_envelope (hd : GraphMetric G d) (cited : CitedFacts G d) (hij : G.Adj i j)
    (hle : ρ G i ≤ ρ G j) : cOR G d i j ≤ Theta G i j (tri G i j) := by
  have henv := lazy_envelope hd cited hij hle
  have hcaps := xi_caps_le_noBF hij
  have hτ : ((uniq G j i).card : ℝ) * w G j = (ρ G j - 1 - tri G i j) * w G j := by
    rw [card_uniq_real hij.symm, tri_comm]
  rw [hτ] at henv
  unfold Theta
  refine henv.trans (min_le_min le_rfl ?_)
  linarith [hcaps]

/-- **Corollary `cor:OR-to-BF-lower`.** If `𝔠_OR ≥ ϑ` and `Θ_ij(t) < ϑ` for every integer
`t < t₀`, then `△ ≥ t₀` and `𝔠_BF ≥ 𝔖 + 𝔗 t₀`. -/
theorem or_to_bf_lower_env (hd : GraphMetric G d) (cited : CitedFacts G d) (hij : G.Adj i j)
    (hle : ρ G i ≤ ρ G j) (h2 : 2 ≤ ρ G i) {ϑ : ℝ} (h : ϑ ≤ cOR G d i j) {t₀ : ℕ}
    (ht₀ : ∀ t : ℕ, t < t₀ → Theta G i j t < ϑ) :
    t₀ ≤ tri G i j ∧ bfS G i j + bfT G i j * t₀ ≤ cBF G i j := by
  have htri : t₀ ≤ tri G i j := by
    by_contra hlt
    push Not at hlt
    have := ht₀ (tri G i j) hlt
    linarith [coverage_envelope hd cited hij hle]
  refine ⟨htri, ?_⟩
  have hmin : ¬ ρmin G i j ≤ 1 := by rw [ρmin_eq hle]; linarith
  unfold cBF
  rw [ite_eq_right hmin]
  have hT := bfT_pos' hij
  have ht : (t₀ : ℝ) ≤ tri G i j := by exact_mod_cast htri
  nlinarith [mul_le_mul_of_nonneg_left ht hT.le, C4_nonneg (G := G) hij]

/-- **Corollary `cor:or-to-bf`, first term of `𝔰`.** For `ρ_i ≥ ρ_j`, inverting the two affine
pieces of `Λ_ij` (via `mixing_dominates`) gives
`𝔠_BF ≤ min{(ϑ + Δ)/(1 − α_min), (ϑ + Δ)/(1 − α_max)} = (ϑ + Δ)/(1 − α̌(ϑ))`. -/
theorem or_to_bf_old (hd : GraphMetric G d) (cited : CitedFacts G d) (hij : G.Adj i j)
    (hle : ρ G j ≤ ρ G i) {ϑ : ℝ} (h : cOR G d i j ≤ ϑ) :
    cBF G i j ≤ min ((ϑ + (w G j - w G i)) / (1 - w G i)) ((ϑ + (w G j - w G i)) / (1 - w G j)) := by
  have hwle : w G i ≤ w G j := w_anti hle
  have hwi1 : w G i < 1 := w_lt_one hij
  have hwj1 : w G j < 1 := w_lt_one hij.symm
  have hdom := mixing_dominates hd cited.bourne hij hle (L := cLLY G d i j) le_rfl
  have hmix := mixing_transfer hd cited.bourne hij hle
  have htop := cited.topping i j hij
  have hmono := lamOld_mono (Δ := w G j - w G i) hwle hwj1.le htop
  have hall : lamOld (w G i) (w G j) (w G j - w G i) (cBF G i j) ≤ ϑ :=
    hmono.trans (hdom.trans (hmix.trans h))
  rw [lamOld_eq_max hwle, max_le_iff] at hall
  refine le_min ?_ ?_
  · rw [le_div_iff₀ (by linarith)]; nlinarith [hall.1]
  · rw [le_div_iff₀ (by linarith)]; nlinarith [hall.2]

end OllivierBF
