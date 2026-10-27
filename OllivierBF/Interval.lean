/-
  The BF interval (Section 5) and the sharpened interval.
  Convention throughout: `ρ_i ≤ ρ_j`, so `a = ρ_i = ρ_min`, `b = ρ_j = ρ_max`.
-/
module

public import OllivierBF.Bounds

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ} {i j : V}

/-! ### Identifying the BF components with the abstract ones -/

lemma ρmax_eq (hle : ρ G i ≤ ρ G j) : ρmax G i j = ρ G j := max_eq_right hle
lemma ρmin_eq (hle : ρ G i ≤ ρ G j) : ρmin G i j = ρ G i := min_eq_left hle

lemma bfS_eq : bfS G i j = bS (ρ G i) (ρ G j) := rfl

lemma bfT_eq (hle : ρ G i ≤ ρ G j) : bfT G i j = bT (ρ G i) (ρ G j) := by
  unfold bfT bT; rw [ρmax_eq hle, ρmin_eq hle]

lemma ρmax_pos (hij : G.Adj i j) : 0 < ρmax G i j := lt_max_of_lt_left (ρ_pos hij)
lemma ρmin_pos (hij : G.Adj i j) : 0 < ρmin G i j := lt_min (ρ_pos hij) (ρ_pos hij.symm)

lemma bfT_pos' (hij : G.Adj i j) : 0 < bfT G i j :=
  add_pos (div_pos two_pos (ρmax_pos hij)) (div_pos one_pos (ρmin_pos hij))

lemma C4_nonneg (hij : G.Adj i j) : 0 ≤ C4 G i j := by
  unfold C4
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (ρmax_pos hij).le)

/-- `𝔠_BF ≤ piece₃` with `s = 𝔪/ρ_max` (uses Topping et al., Lemma 11). -/
lemma cBF_le_piece3 (cited : CitedFacts G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j)
    (h2 : 2 ≤ ρ G i) :
    cBF G i j ≤ piece3 (ρ G i) (ρ G j) (tri G i j) (matchNum G i j / ρ G j) := by
  have hmin : ¬ ρmin G i j ≤ 1 := by rw [ρmin_eq hle]; linarith
  have h11 := cited.topping11 i j hij (by rw [ρmin_eq hle]; exact h2)
  unfold cBF piece3
  rw [ite_eq_right hmin, bfS_eq, bfT_eq hle]
  unfold matchStat at h11
  rw [ρmax_eq hle] at h11
  linarith

/-! ### Theorem `thm:bf-lower-elementary` -/

/-- **Theorem `thm:bf-lower-elementary` (lower modulus), case `ρ_min ≥ 2`.** -/
theorem bf_lower (hd : GraphMetric G d) (cited : CitedFacts G d) (hij : G.Adj i j)
    (hle : ρ G i ≤ ρ G j) (h2 : 2 ≤ ρ G i) {ζ : ℝ} (hζ : ζ ≤ cBF G i j) :
    phiElem (ρ G i) (ρ G j) ζ ≤ cOR G d i j := by
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  have hq := lazy_quadrangle hd hij hle
  rw [Llazy_eq hρi hρj] at hq
  refine le_trans ?_ hq
  exact phiElem_le (by linarith) hle (Nat.cast_nonneg _) (tri_le hij)
    (div_nonneg (Nat.cast_nonneg _) hρj.le) (hζ.trans (cBF_le_piece3 cited hij hle h2))

/-- **Theorem `thm:bf-lower-elementary`, leaf case `ρ_min = 1`:** the bound is the exact
tree value `L⁰`. -/
theorem bf_lower_leaf (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j)
    (h1 : ρ G i = 1) : L0 (ρ G i) (ρ G j) ≤ cOR G d i j := by
  have hq := lazy_quadrangle hd hij hle
  have ht : (tri G i j : ℝ) = 0 := by
    have := tri_le hij; rw [h1] at this
    exact le_antisymm (by linarith) (Nat.cast_nonneg _)
  have hm : (matchNum G i j : ℝ) = 0 := by
    have h := matchNum_le_uniq (G := G) (i := i) (j := j)
    have hU := card_uniq_real hij
    rw [h1, ht] at hU
    have : ((uniq G i j).card : ℝ) = 0 := by linarith
    have hc : (uniq G i j).card = 0 := by exact_mod_cast this
    have : matchNum G i j = 0 := Nat.le_zero.1 (hc ▸ h)
    simp [this]
  unfold Llazy at hq; unfold L0
  rw [ht, hm] at hq
  simp only [add_zero, mul_zero] at hq
  exact hq

/-- The minimiser of the linear program attains `phiElem`. -/
lemma phiElem_attained {a b ζ : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∃ t s, 0 ≤ t ∧ t ≤ a - 1 ∧ 0 ≤ s ∧ ζ ≤ piece3 a b t s ∧
      phiElem a b ζ = L0 a b + kappa1 a b * bT a b * t + 2 * kappa2 b * s := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hT := bT_pos ha0 hb0
  have hT0 : bT a b ≠ 0 := hT.ne'
  set z := max (ζ - bS a b) 0 with hz
  have hz0 : 0 ≤ z := le_max_right _ _
  have hzT : bT a b * (z / bT a b) = z := by field_simp
  have h1 : bT a b * min (z / bT a b) (a - 1) = min z (bT a b * (a - 1)) := by
    rw [mul_min_of_nonneg _ _ hT.le, hzT]
  refine ⟨min (z / bT a b) (a - 1), max (z - bT a b * (a - 1)) 0 / 2, ?_, min_le_right _ _,
    div_nonneg (le_max_right _ _) two_pos.le, ?_, ?_⟩
  · exact le_min (div_nonneg hz0 hT.le) (by linarith)
  · unfold piece3
    rw [h1]
    rcases le_total z (bT a b * (a - 1)) with h | h
    · rw [min_eq_left h]
      have : 0 ≤ max (z - bT a b * (a - 1)) 0 / 2 := div_nonneg (le_max_right _ _) two_pos.le
      linarith [le_max_left (ζ - bS a b) 0]
    · rw [min_eq_right h, max_eq_left (show 0 ≤ z - bT a b * (a - 1) by linarith)]
      linarith [le_max_left (ζ - bS a b) 0]
  · unfold phiElem
    simp only [← hz]
    have h2 : kappa1 a b * bT a b * min (z / bT a b) (a - 1)
        = kappa1 a b * min z (bT a b * (a - 1)) := by rw [mul_assoc, h1]
    rw [h2]; ring

/-- **Dominance:** `φ ≥ Λ^tf ≥ Λ` (Theorem `thm:bf-lower-elementary`). -/
theorem phiElem_ge_lamTF {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (ζ : ℝ) :
    lamTF (1 / (b + 1)) (1 / (a + 1)) (1 / (a + 1) - 1 / (b + 1)) b ζ ≤ phiElem a b ζ := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  obtain ⟨t, s, ht0, hta, hs, hζ, heq⟩ := phiElem_attained (ζ := ζ) ha hab
  have hmin : 1 / (b + 1) ≤ 1 / (a + 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
  have hmax1 : 1 / (a + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hmono : lamTF (1 / (b + 1)) (1 / (a + 1)) (1 / (a + 1) - 1 / (b + 1)) b ζ ≤
      lamTF (1 / (b + 1)) (1 / (a + 1)) (1 / (a + 1) - 1 / (b + 1)) b (piece3 a b t s) := by
    unfold lamTF
    exact max_le_max (lamOld_mono hmin hmax1 hζ) (lamMix_mono hmax1 hζ)
  have hdom := lamTF_piece3_le (m := b * s) ha hab ht0 hta (mul_nonneg hb0.le hs)
  have hbs : b * s / b = s := mul_div_cancel_left₀ s hb0.ne'
  rw [hbs] at hdom
  have hL := Llazy_eq ha0 hb0 t (b * s)
  rw [hbs] at hL
  linarith [hmono, hdom, hL, heq]

/-! ### Theorem `thm:BF-to-OR-lazy` (upper modulus) -/

/-- The concave envelope `Ψ̂(t)` for the lazy measure (`eq:widehat-Psi-tight`). -/
noncomputable def psiHat (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (ζ t : ℝ) : ℝ :=
  let wi := w G i; let wj := w G j; let δ := wi - wj
  let bud := max (ζ - bfS G i j) 0
  let sig := 1 / wi + 1 / wj
  let sho := ρ G j * (ρ G j - 1)
  let Ai := (ρ G i - 1 - t) * wi; let Aj := (ρ G j - 1 - t) * wj
  let B := sho * (bud - bfT G i j * t) / sig
  let D := (ρ G i + ρ G j - 2 - 2 * t) / sig
  min ((2 + t) * wj) (-1 + 2 * ((2 + t) * wj) + δ + min (t * δ) Aj + min (min Ai Aj) (min B D))

/-- `△_max(ζ)`. -/
noncomputable def triMax (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (ζ : ℝ) : ℝ :=
  min (ρ G i - 1) (max (ζ - bfS G i j) 0 / bfT G i j)

/-- The upper modulus `ψ(ζ) = max_{t ∈ [0, △_max]} Ψ̂(t)`. -/
noncomputable def psiUp (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (ζ : ℝ) : ℝ :=
  sSup (psiHat G i j ζ '' Set.Icc 0 (triMax G i j ζ))

/-- If `ϖ_max = 0` there are no cross edges, so `Ξ = 0`. -/
lemma Xi_eq_zero_of_varpi (h : varpi G i j = 0) : Xi G i j = 0 := by
  have h1 : (uniq G i j).sup (fun k => boxClose G k i j) = 0 := by
    have := le_max_left ((uniq G i j).sup fun k => boxClose G k i j)
      ((uniq G j i).sup fun w => boxClose G w j i)
    unfold varpi at h; omega
  have h2 : (uniq G j i).sup (fun w => boxClose G w j i) = 0 := by
    have := le_max_right ((uniq G i j).sup fun k => boxClose G k i j)
      ((uniq G j i).sup fun w => boxClose G w j i)
    unfold varpi at h; omega
  have e1 : (xi G i j).card = 0 := by
    by_contra hne
    obtain ⟨k, hk⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
    obtain ⟨hkU, w, hw, hadj⟩ := Finset.mem_filter.1 hk
    have hle : boxClose G k i j ≤ 0 := h1 ▸ Finset.le_sup (f := fun k => boxClose G k i j) hkU
    have hpos : 0 < boxClose G k i j :=
      Finset.card_pos.2 ⟨w, Finset.mem_inter.2 ⟨(G.mem_neighborFinset k w).2 hadj, hw⟩⟩
    omega
  have e2 : (xi G j i).card = 0 := by
    by_contra hne
    obtain ⟨k, hk⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
    obtain ⟨hkU, w, hw, hadj⟩ := Finset.mem_filter.1 hk
    have hle : boxClose G k j i ≤ 0 := h2 ▸ Finset.le_sup (f := fun w => boxClose G w j i) hkU
    have hpos : 0 < boxClose G k j i :=
      Finset.card_pos.2 ⟨w, Finset.mem_inter.2 ⟨(G.mem_neighborFinset k w).2 hadj, hw⟩⟩
    omega
  unfold Xi; rw [e1, e2]

/-- `Ξ ≤ ♯*(b − 𝔗 t)` under the BF hypothesis (from `𝔠_4 ≥ Ξ/♯*`). -/
lemma Xi_le_budget (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) (h2 : 2 ≤ ρ G i) {ζ : ℝ}
    (hζ : cBF G i j ≤ ζ) :
    (Xi G i j : ℝ) ≤ ρ G j * (ρ G j - 1) * (max (ζ - bfS G i j) 0 - bfT G i j * tri G i j) := by
  have hmin : ¬ ρmin G i j ≤ 1 := by rw [ρmin_eq hle]; linarith
  have hbf : bfS G i j + bfT G i j * tri G i j + C4 G i j ≤ ζ := by
    unfold cBF at hζ; rwa [ite_eq_right hmin] at hζ
  have hsho : 0 ≤ ρ G j * (ρ G j - 1) := mul_nonneg (by linarith) (by linarith)
  by_cases hv : varpi G i j = 0
  · rw [Xi_eq_zero_of_varpi hv]
    have hC : C4 G i j = 0 := by unfold C4; rw [ite_eq_left hv]
    rw [hC] at hbf
    have : 0 ≤ max (ζ - bfS G i j) 0 - bfT G i j * tri G i j := by
      have := le_max_left (ζ - bfS G i j) 0; linarith
    push_cast; exact mul_nonneg hsho this
  · have hv1 : (1 : ℝ) ≤ varpi G i j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hv
    have hvle := varpi_le hij
    rw [show max (ρ G i) (ρ G j) = ρ G j from max_eq_right hle] at hvle
    have hden : 0 < (varpi G i j : ℝ) * ρmax G i j :=
      mul_pos (by linarith) (ρmax_pos hij)
    have hC : C4 G i j = (Xi G i j : ℝ) / ((varpi G i j : ℝ) * ρmax G i j) := by
      unfold C4; rw [ite_eq_right hv]
    -- `Ξ = 𝔠₄ ϖ ρ_max ≤ 𝔠₄ ♯*`
    have hXi : (Xi G i j : ℝ) = C4 G i j * ((varpi G i j : ℝ) * ρmax G i j) := by
      rw [hC, div_mul_cancel₀ _ hden.ne']
    have hC0 : 0 ≤ C4 G i j := C4_nonneg hij
    have hle' : (varpi G i j : ℝ) * ρmax G i j ≤ ρ G j * (ρ G j - 1) := by
      rw [ρmax_eq hle]
      have := ρ_pos (G := G) hij.symm
      nlinarith [mul_le_mul_of_nonneg_right hvle this.le]
    have hbud : C4 G i j ≤ max (ζ - bfS G i j) 0 - bfT G i j * tri G i j := by
      have := le_max_left (ζ - bfS G i j) 0; linarith
    rw [hXi]
    calc C4 G i j * ((varpi G i j : ℝ) * ρmax G i j) ≤ C4 G i j * (ρ G j * (ρ G j - 1)) :=
          mul_le_mul_of_nonneg_left hle' hC0
      _ ≤ (max (ζ - bfS G i j) 0 - bfT G i j * tri G i j) * (ρ G j * (ρ G j - 1)) :=
          mul_le_mul_of_nonneg_right hbud hsho
      _ = _ := by ring

/-- `min(|ξ_i| w_i, |ξ_j| w_j) ≤ min{A_i, A_j, B, D}` at `t = △(i,j)`: from `ξ_u ⊆ U_u`,
the harmonic bound `min{x a, y b} ≤ (x + y)/(1/a + 1/b)`, `Xi_le_budget`, and `Xi_le`. -/
lemma xi_caps_le (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) (h2 : 2 ≤ ρ G i) {ζ : ℝ}
    (hζ : cBF G i j ≤ ζ) :
    min ((xi G i j).card * w G i) ((xi G j i).card * w G j) ≤
      min (min ((ρ G i - 1 - tri G i j) * w G i) ((ρ G j - 1 - tri G i j) * w G j))
        (min (ρ G j * (ρ G j - 1) * (max (ζ - bfS G i j) 0 - bfT G i j * tri G i j)
              / (1 / w G i + 1 / w G j))
             ((ρ G i + ρ G j - 2 - 2 * tri G i j) / (1 / w G i + 1 / w G j))) := by
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
        ≤ (xi G i j).card := by
      rw [mul_one_div, div_le_iff₀ hwi]; exact hm1
    have e2 : min ((xi G i j).card * w G i) ((xi G j i).card * w G j) * (1 / w G j)
        ≤ (xi G j i).card := by
      rw [mul_one_div, div_le_iff₀ hwj]; exact hm2
    simp only [Xi]; push_cast
    rw [mul_add]; linarith
  have hB := Xi_le_budget hij hle h2 hζ
  have hD := Xi_le hij
  refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
  · exact hm1.trans (mul_le_mul_of_nonneg_right hX hwi.le)
  · exact hm2.trans (mul_le_mul_of_nonneg_right hY hwj.le)
  · exact hharm.trans (div_le_div_of_nonneg_right hB hsig.le)
  · exact hharm.trans (div_le_div_of_nonneg_right hD hsig.le)

lemma triMax_nonneg (hij : G.Adj i j) (ζ : ℝ) : 0 ≤ triMax G i j ζ := by
  have h1 : (1 : ℝ) ≤ ρ G i := by
    have : 0 < G.degree i := (G.degree_pos_iff_exists_adj i).2 ⟨j, hij⟩
    simp only [ρ]; exact_mod_cast this
  unfold triMax
  exact le_min (by linarith) (div_nonneg (le_max_right _ _) (bfT_pos' hij).le)

lemma psiHat_le_bound (_hij : G.Adj i j) (ζ t : ℝ) (ht : t ≤ ρ G i) :
    psiHat G i j ζ t ≤ (2 + ρ G i) * w G j := by
  unfold psiHat
  simp only
  exact (min_le_left _ _).trans (by nlinarith [w_pos (G := G) j])

/-- **Theorem `thm:BF-to-OR-lazy` (upper modulus), case `ρ_min ≥ 2`.** -/
theorem bf_upper (hd : GraphMetric G d) (cited : CitedFacts G d) (hij : G.Adj i j)
    (hle : ρ G i ≤ ρ G j) (h2 : 2 ≤ ρ G i) {ζ : ℝ} (hζ : cBF G i j ≤ ζ) :
    cOR G d i j ≤ psiUp G i j ζ := by
  have henv := lazy_envelope hd cited hij hle
  have hcaps := xi_caps_le hij hle h2 hζ
  have hτ : ((uniq G j i).card : ℝ) * w G j = (ρ G j - 1 - tri G i j) * w G j := by
    rw [card_uniq_real hij.symm, tri_comm]
  rw [hτ] at henv
  -- `t = △(i,j)` is admissible
  have hmin : ¬ ρmin G i j ≤ 1 := by rw [ρmin_eq hle]; linarith
  have hT : 0 < bfT G i j := bfT_pos' hij
  have hbf : bfS G i j + bfT G i j * tri G i j + C4 G i j ≤ ζ := by
    unfold cBF at hζ; rwa [ite_eq_right hmin] at hζ
  have hC0 : 0 ≤ C4 G i j := C4_nonneg hij
  have hmem : (tri G i j : ℝ) ∈ Set.Icc 0 (triMax G i j ζ) := by
    refine ⟨Nat.cast_nonneg _, le_min (tri_le hij) ?_⟩
    rw [le_div_iff₀ hT]
    have := le_max_left (ζ - bfS G i j) 0
    nlinarith
  have hval : cOR G d i j ≤ psiHat G i j ζ (tri G i j) := by
    unfold psiHat; simp only
    refine henv.trans (min_le_min le_rfl ?_)
    linarith [hcaps]
  have hbdd : BddAbove (psiHat G i j ζ '' Set.Icc 0 (triMax G i j ζ)) := by
    refine ⟨(2 + ρ G i) * w G j, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact psiHat_le_bound hij ζ t (ht.2.trans (min_le_left _ _) |>.trans (by linarith))
  exact hval.trans (le_csSup hbdd ⟨_, hmem, rfl⟩)

/-- **The upper modulus is nondecreasing** (missing from the current draft). -/
theorem psiUp_mono (hij : G.Adj i j) {ζ ζ' : ℝ} (h : ζ ≤ ζ') :
    psiUp G i j ζ ≤ psiUp G i j ζ' := by
  have hT : 0 < bfT G i j := bfT_pos' hij
  have hbud : max (ζ - bfS G i j) 0 ≤ max (ζ' - bfS G i j) 0 := max_le_max (by linarith) le_rfl
  have hsub : Set.Icc 0 (triMax G i j ζ) ⊆ Set.Icc 0 (triMax G i j ζ') := by
    intro t ht
    refine ⟨ht.1, ht.2.trans (min_le_min le_rfl (div_le_div_of_nonneg_right hbud hT.le))⟩
  have hbdd : BddAbove (psiHat G i j ζ' '' Set.Icc 0 (triMax G i j ζ')) := by
    refine ⟨(2 + ρ G i) * w G j, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact psiHat_le_bound hij ζ' t (ht.2.trans (min_le_left _ _) |>.trans (by linarith))
  have hne : (psiHat G i j ζ '' Set.Icc 0 (triMax G i j ζ)).Nonempty :=
    ⟨_, 0, ⟨le_rfl, triMax_nonneg hij ζ⟩, rfl⟩
  apply csSup_le hne
  rintro _ ⟨t, ht, rfl⟩
  have hpt : psiHat G i j ζ t ≤ psiHat G i j ζ' t := by
    unfold psiHat; simp only
    have hsho : 0 ≤ ρ G j * (ρ G j - 1) := by
      have h1 : (1 : ℝ) ≤ ρ G j := by
        have : 0 < G.degree j := (G.degree_pos_iff_exists_adj j).2 ⟨i, hij.symm⟩
        simp only [ρ]; exact_mod_cast this
      nlinarith
    have hsig : 0 < 1 / w G i + 1 / w G j :=
      add_pos (one_div_pos.2 (w_pos (G := G) i)) (one_div_pos.2 (w_pos (G := G) j))
    refine min_le_min le_rfl (add_le_add le_rfl (min_le_min le_rfl (min_le_min ?_ le_rfl)))
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hsho) hsig.le
  exact hpt.trans (le_csSup hbdd ⟨t, hsub ht, rfl⟩)

/-! ### Corollary `cor:bf-interval` and the sharpened interval -/

/-- **Corollary `cor:bf-interval`.** -/
theorem bf_interval (hd : GraphMetric G d) (cited : CitedFacts G d) (hij : G.Adj i j)
    (hle : ρ G i ≤ ρ G j) (h2 : 2 ≤ ρ G i) :
    phiElem (ρ G i) (ρ G j) (cBF G i j) ≤ cOR G d i j ∧ cOR G d i j ≤ psiUp G i j (cBF G i j) :=
  ⟨bf_lower hd cited hij hle h2 le_rfl, bf_upper hd cited hij hle h2 le_rfl⟩

/-- **Proposition `sharpened-interval`.** `φ(𝔠_BF) ≤ L^lazy ≤ 𝔠_OR ≤ Ψ̂(△) ≤ ψ(𝔠_BF)`: the lower
end of the sharpened interval lies inside the BF interval, and the envelope evaluated at the
true triangle count `△` bounds `𝔠_OR` from above and lies below the upper modulus. -/
theorem sharpened_interval (hd : GraphMetric G d) (cited : CitedFacts G d) (hij : G.Adj i j)
    (hle : ρ G i ≤ ρ G j) (h2 : 2 ≤ ρ G i) :
    phiElem (ρ G i) (ρ G j) (cBF G i j) ≤ Llazy (ρ G i) (ρ G j) (tri G i j) (matchNum G i j) ∧
    Llazy (ρ G i) (ρ G j) (tri G i j) (matchNum G i j) ≤ cOR G d i j ∧
    cOR G d i j ≤ psiHat G i j (cBF G i j) (tri G i j) ∧
    psiHat G i j (cBF G i j) (tri G i j) ≤ psiUp G i j (cBF G i j) := by
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  refine ⟨?_, lazy_quadrangle hd hij hle, ?_, ?_⟩
  · rw [Llazy_eq hρi hρj]
    exact phiElem_le (by linarith) hle (Nat.cast_nonneg _) (tri_le hij)
      (div_nonneg (Nat.cast_nonneg _) hρj.le) (cBF_le_piece3 cited hij hle h2)
  · -- the envelope evaluated at the true `△`, as in `bf_upper`
    have henv := lazy_envelope hd cited hij hle
    have hcaps := xi_caps_le hij hle h2 (le_refl (cBF G i j))
    have hτ : ((uniq G j i).card : ℝ) * w G j = (ρ G j - 1 - tri G i j) * w G j := by
      rw [card_uniq_real hij.symm, tri_comm]
    rw [hτ] at henv
    unfold psiHat; simp only
    refine henv.trans (min_le_min le_rfl ?_)
    linarith [hcaps]
  · have hmin : ¬ ρmin G i j ≤ 1 := by rw [ρmin_eq hle]; linarith
    have hT : 0 < bfT G i j := bfT_pos' hij
    have hbf : bfS G i j + bfT G i j * tri G i j + C4 G i j ≤ cBF G i j := by
      unfold cBF; simp only [ite_eq_right hmin, le_refl]
    have hC0 : 0 ≤ C4 G i j := C4_nonneg hij
    have hmem : (tri G i j : ℝ) ∈ Set.Icc 0 (triMax G i j (cBF G i j)) := by
      refine ⟨Nat.cast_nonneg _, le_min (tri_le hij) ?_⟩
      rw [le_div_iff₀ hT]
      have := le_max_left (cBF G i j - bfS G i j) 0
      nlinarith
    have hbdd : BddAbove (psiHat G i j (cBF G i j) '' Set.Icc 0 (triMax G i j (cBF G i j))) := by
      refine ⟨(2 + ρ G i) * w G j, ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      exact psiHat_le_bound hij _ t (ht.2.trans (min_le_left _ _) |>.trans (by linarith))
    exact le_csSup hbdd ⟨_, hmem, rfl⟩

end OllivierBF
