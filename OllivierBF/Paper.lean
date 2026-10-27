/-
  The results of the manuscript in the form in which the paper states them (Appendix E of the
  paper lists the correspondence).

  The other files prove the building blocks. Several of them follow an earlier version of the
  paper and state longer or weaker forms (`phiElem`, `psiHat`, `psiUp`, `Theta`, and
  `lazy_envelope` with two caps that are never active); this file derives the current
  statements from them and from `Cover.lean`.

  Only Proposition 4.1 and Corollary 4.2 take a published result as a hypothesis: Lemma 3.3 of
  the paper (Bourne et al., `BourneFact`). Every other statement here, including the BF interval
  and the 2-hop interval, is proved from the definitions.

  Convention: the endpoints are labelled so that `ρ_i ≤ ρ_j`.
-/
module

public import OllivierBF.Appendix
public import OllivierBF.Cover

@[expose] public section

set_option linter.unusedSectionVars false

namespace OllivierBF

/-! ### Real-number forms of the moduli -/

/-- The lower modulus of Theorem 5.4: `φ_{a,b}(ζ) = L⁰ + κ₁ [ζ − 𝔖]₊`. -/
noncomputable def phiAff (a b ζ : ℝ) : ℝ := L0 a b + kappa1 a b * max (ζ - bS a b) 0

/-- `t⋆ = min{a − 1, ⌊[ζ − 𝔖]₊/𝔗⌋}` of Corollary 5.8. -/
noncomputable def tStar (a b ζ : ℝ) : ℝ :=
  min (a - 1) (Nat.floor (max (ζ - bS a b) 0 / bT a b) : ℝ)

/-- The lower end `φ^ℤ_{a,b}` of the BF interval (Corollary 5.8). -/
noncomputable def phiInt (a b ζ : ℝ) : ℝ :=
  L0 a b + kappa1 a b * bT a b * tStar a b ζ
    + kappa2 b * (max (ζ - bS a b) 0 - bT a b * tStar a b ζ)

section modulus

variable {a b : ℝ}

/-- `phiElem` adds a second slope `κ₂ ≥ κ₁` beyond `𝔖 + 𝔗 (a − 1)`, so it is never below `φ`. -/
lemma phiAff_le_phiElem (ha : 1 ≤ a) (hab : a ≤ b) (ζ : ℝ) : phiAff a b ζ ≤ phiElem a b ζ := by
  have ha0 : 0 < a := by linarith
  have hk12 := kappa1_le_kappa2 ha0 hab
  unfold phiAff phiElem
  simp only
  set z := max (ζ - bS a b) 0
  rcases le_total z (bT a b * (a - 1)) with h | h
  · rw [min_eq_left h, max_eq_right (by linarith : z - bT a b * (a - 1) ≤ 0)]
    linarith
  · rw [min_eq_right h, max_eq_left (by linarith : 0 ≤ z - bT a b * (a - 1))]
    nlinarith [mul_le_mul_of_nonneg_right hk12 (by linarith : (0 : ℝ) ≤ z - bT a b * (a - 1))]

/-- On the attainable range `ζ ≤ 𝔖 + 𝔗 (a − 1)` the two lower moduli coincide. -/
lemma phiAff_eq_phiElem (ha : 1 ≤ a) (hab : a ≤ b) {ζ : ℝ}
    (hζ : ζ ≤ bS a b + bT a b * (a - 1)) : phiAff a b ζ = phiElem a b ζ := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hT := bT_pos ha0 hb0
  have hcap : 0 ≤ bT a b * (a - 1) := mul_nonneg hT.le (by linarith)
  have hz : max (ζ - bS a b) 0 ≤ bT a b * (a - 1) := max_le (by linarith) hcap
  unfold phiAff phiElem
  simp only
  rw [min_eq_left hz, max_eq_right (by linarith : max (ζ - bS a b) 0 - bT a b * (a - 1) ≤ 0)]
  ring

/-- **Theorem 5.4**: the lower modulus is nondecreasing. -/
lemma phiAff_mono (ha : 0 < a) (hb : 0 < b) {ζ ζ' : ℝ} (h : ζ ≤ ζ') :
    phiAff a b ζ ≤ phiAff a b ζ' := by
  have hk1 := kappa1_nonneg ha hb
  have hm : max (ζ - bS a b) 0 ≤ max (ζ' - bS a b) 0 := max_le_max (by linarith) le_rfl
  unfold phiAff
  nlinarith [mul_le_mul_of_nonneg_left hm hk1]

/-- **Theorem 5.4, the virtual edge**: `φ_{a,b}(ζ)` is `L^lazy` at `△ = [ζ − 𝔖]₊/𝔗`, `𝔪 = 0`. -/
lemma phiAff_virtual (ha : 0 < a) (hb : 0 < b) (ζ : ℝ) :
    phiAff a b ζ = Llazy a b (max (ζ - bS a b) 0 / bT a b) 0 := by
  have hT := bT_pos ha hb
  have hT0 : bT a b ≠ 0 := hT.ne'
  have hc : bT a b * (max (ζ - bS a b) 0 / bT a b) = max (ζ - bS a b) 0 := by
    rw [mul_comm (bT a b)]; exact div_mul_cancel₀ _ hT0
  rw [Llazy_eq ha hb]
  unfold phiAff
  rw [mul_assoc (kappa1 a b), hc]
  ring

/-- **Proposition 5.5, comparison with the lifts**: `Λ ≤ Λ^tf ≤ φ` on the attainable range. -/
theorem phiAff_ge_lamTF (ha : 1 ≤ a) (hab : a ≤ b) {ζ : ℝ}
    (hζ : ζ ≤ bS a b + bT a b * (a - 1)) :
    lamOld (1 / (b + 1)) (1 / (a + 1)) (1 / (a + 1) - 1 / (b + 1)) ζ
        ≤ lamTF (1 / (b + 1)) (1 / (a + 1)) (1 / (a + 1) - 1 / (b + 1)) b ζ ∧
      lamTF (1 / (b + 1)) (1 / (a + 1)) (1 / (a + 1) - 1 / (b + 1)) b ζ ≤ phiAff a b ζ := by
  refine ⟨by unfold lamTF; exact le_max_left _ _, ?_⟩
  rw [phiAff_eq_phiElem ha hab hζ]
  exact phiElem_ge_lamTF ha hab ζ

/-- **Corollary 4.2, closed form**: `Λ^tf(L) = (1 − α_max) L − Δ_α (1 − max{L, 2/ρ_max})`. -/
lemma lamTF_closed (ha : 0 < a) (hab : a ≤ b) (L : ℝ) :
    lamTF (1 / (b + 1)) (1 / (a + 1)) (1 / (a + 1) - 1 / (b + 1)) b L
      = (1 - 1 / (a + 1)) * L - (1 / (a + 1) - 1 / (b + 1)) * (1 - max L (2 / b)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hmin : 1 / (b + 1) ≤ 1 / (a + 1) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  have hD : 0 ≤ 1 / (a + 1) - 1 / (b + 1) := sub_nonneg.2 hmin
  have h2b : 0 < 2 / b := div_pos two_pos hb
  unfold lamTF lamMix
  rw [lamOld_eq_max hmin]
  rcases le_total L (2 / b) with h | h
  · rw [max_eq_right h]
    apply max_eq_right
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left h hD]
    · nlinarith [mul_nonneg hD h2b.le]
  · rw [max_eq_left h]
    have e : (1 - 1 / (a + 1)) * L - (1 / (a + 1) - 1 / (b + 1)) * (1 - L)
        = (1 - 1 / (b + 1)) * L - (1 / (a + 1) - 1 / (b + 1)) := by ring
    rw [e]
    have hL0 : 0 ≤ L := le_trans h2b.le h
    apply le_antisymm
    · apply max_le (max_le le_rfl ?_) ?_
      · nlinarith [mul_le_mul_of_nonneg_right hmin hL0]
      · nlinarith [mul_le_mul_of_nonneg_left h hD]
    · exact (le_max_left _ _).trans (le_max_left _ _)

/-- **Theorem 4.7, deficit form**: `L^lazy = Θ − △ Δ_α − 2R` with `Θ = (3 + △)/(b + 1) − 1/(a + 1)`
and `R = (a − 1 − △)/(a + 1) − 𝔪/(b + 1)`. -/
lemma Llazy_deficit (ha : 0 < a) (hb : 0 < b) (t m : ℝ) :
    Llazy a b t m = ((3 + t) / (b + 1) - 1 / (a + 1)) - t * (1 / (a + 1) - 1 / (b + 1))
      - 2 * ((a - 1 - t) / (a + 1) - m / (b + 1)) := by
  have h1 : a + 1 ≠ 0 := by linarith
  have h2 : b + 1 ≠ 0 := by linarith
  unfold Llazy
  first
    | (field_simp; ring)
    | field_simp

/-- **Corollary 5.8**: `φ^ℤ_{a,b} ≥ φ_{a,b}`. -/
lemma phiInt_ge_phiAff (ha : 1 ≤ a) (hab : a ≤ b) (ζ : ℝ) : phiAff a b ζ ≤ phiInt a b ζ := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hT := bT_pos ha0 hb0
  have hT0 : bT a b ≠ 0 := hT.ne'
  have hk12 := kappa1_le_kappa2 ha0 hab
  have hts : bT a b * tStar a b ζ ≤ max (ζ - bS a b) 0 := by
    have h1 : tStar a b ζ ≤ max (ζ - bS a b) 0 / bT a b := by
      unfold tStar
      exact (min_le_right _ _).trans (Nat.floor_le (div_nonneg (le_max_right _ _) hT.le))
    have h3 := mul_le_mul_of_nonneg_left h1 hT.le
    have h4 : bT a b * (max (ζ - bS a b) 0 / bT a b) = max (ζ - bS a b) 0 := by
      rw [mul_comm (bT a b)]; exact div_mul_cancel₀ _ hT0
    linarith
  have h := mul_nonneg (sub_nonneg.2 hk12) (sub_nonneg.2 hts)
  unfold phiAff phiInt
  nlinarith [h]

end modulus

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ} {i j : V}

/-! ### Edges with an endpoint of degree one -/

/-- An endpoint of degree below `2` has degree `1`. -/
lemma rho_eq_one_of_lt_two (hij : G.Adj i j) (h : ¬ 2 ≤ ρ G i) : ρ G i = 1 := by
  have hpos : 0 < G.degree i := (G.degree_pos_iff_exists_adj i).2 ⟨j, hij⟩
  have hlt : (G.degree i : ℝ) < 2 := not_le.mp h
  have hlt' : G.degree i < 2 := by exact_mod_cast hlt
  have h1 : G.degree i = 1 := by omega
  simp only [ρ, h1, Nat.cast_one]

lemma cBF_eq_zero_of_leaf (hle : ρ G i ≤ ρ G j) (h1 : ρ G i = 1) : cBF G i j = 0 := by
  have hmin : ρmin G i j ≤ 1 := by rw [ρmin_eq hle]; exact h1.le
  unfold cBF
  simp [hmin]

lemma leaf_tri (hij : G.Adj i j) (h1 : ρ G i = 1) : (tri G i j : ℝ) = 0 := by
  have h := tri_le hij
  rw [h1] at h
  exact le_antisymm (by linarith) (Nat.cast_nonneg _)

lemma leaf_uniq (hij : G.Adj i j) (h1 : ρ G i = 1) : ((uniq G i j).card : ℝ) = 0 := by
  have hU := card_uniq_real hij
  rw [h1, leaf_tri hij h1] at hU
  linarith

lemma leaf_matchNum (hij : G.Adj i j) (h1 : ρ G i = 1) : (matchNum G i j : ℝ) = 0 := by
  have h := matchNum_le_uniq (G := G) (i := i) (j := j)
  have hc : (uniq G i j).card = 0 := by exact_mod_cast leaf_uniq hij h1
  have : matchNum G i j = 0 := Nat.le_zero.1 (hc ▸ h)
  simp [this]

lemma leaf_Xi (hij : G.Adj i j) (h1 : ρ G i = 1) : Xi G i j = 0 := by
  have hU : (uniq G i j).card = 0 := by exact_mod_cast leaf_uniq hij h1
  have hUe : uniq G i j = ∅ := Finset.card_eq_zero.1 hU
  have e1 : (xi G i j).card = 0 := by simp [xi, hUe]
  have e2 : (xi G j i).card = 0 := by simp [xi, hUe]
  unfold Xi
  rw [e1, e2]

/-! ### Symmetry, and Proposition 4.1 and Corollary 4.2 in the labelling of the paper -/

lemma cORp_comm (hd : GraphMetric G d) (p : ℝ) (i j : V) : cORp G d p i j = cORp G d p j i := by
  unfold cORp; rw [W1_comm hd.nonneg hd.symm]

lemma cOR_comm (hd : GraphMetric G d) (i j : V) : cOR G d i j = cOR G d j i := by
  unfold cOR; rw [W1_comm hd.nonneg hd.symm]

lemma cLLY_comm (hd : GraphMetric G d) (i j : V) : cLLY G d i j = cLLY G d j i := by
  unfold cLLY
  congr 1
  funext p
  rw [cORp_comm hd p i j]

/-- **Proposition 4.1**: `𝔠_OR ≥ (1 − α_max) 𝔠_LLY − Δ_α (1 − q)`, with `q = (2 + △)/ρ_max`, for
`ρ_i ≤ ρ_j`. The only hypothesis beyond the definitions is Lemma 3.3 (`BourneFact`). -/
theorem mixing_transfer_paper (hd : GraphMetric G d) (hB : BourneFact G d) (hij : G.Adj i j)
    (hle : ρ G i ≤ ρ G j) :
    lamMix (w G i) (w G i - w G j) ((2 + tri G i j) / ρ G j) (cLLY G d i j) ≤ cOR G d i j := by
  have h := mixing_transfer hd hB hij.symm hle
  rwa [tri_comm j i, cLLY_comm hd j i, cOR_comm hd j i] at h

/-- **Proposition 4.1**: `𝔠_LLY ≤ q = (2 + △)/ρ_max`, for `ρ_i ≤ ρ_j`. -/
theorem cLLY_le_q_paper (hd : GraphMetric G d) (hB : BourneFact G d) (hij : G.Adj i j)
    (hle : ρ G i ≤ ρ G j) : cLLY G d i j ≤ (2 + tri G i j) / ρ G j := by
  have h := cLLY_le_q hd hB hij.symm hle
  rwa [tri_comm j i, cLLY_comm hd j i] at h

/-- **Corollary 4.2**: `𝔠_OR ≥ (1 − α_max) L − Δ_α (1 − max{L, 2/ρ_max})` for every
`L ≤ 𝔠_LLY`, for `ρ_i ≤ ρ_j`. -/
theorem mixing_tf_paper (hd : GraphMetric G d) (hB : BourneFact G d) (hij : G.Adj i j)
    (hle : ρ G i ≤ ρ G j) {L : ℝ} (hL : L ≤ cLLY G d i j) :
    (1 - w G i) * L - (w G i - w G j) * (1 - max L (2 / ρ G j)) ≤ cOR G d i j := by
  have hmix := mixing_transfer_paper hd hB hij hle
  have hq := cLLY_le_q_paper hd hB hij hle
  have hρj := ρ_pos hij.symm
  have hw := w_anti (G := G) hle
  have hw1 : w G i < 1 := w_lt_one hij
  have h2q : 2 / ρ G j ≤ (2 + tri G i j) / ρ G j :=
    div_le_div_of_nonneg_right
      (by linarith [(Nat.cast_nonneg (tri G i j) : (0 : ℝ) ≤ tri G i j)]) hρj.le
  have hmax : max L (2 / ρ G j) ≤ (2 + tri G i j) / ρ G j := max_le (hL.trans hq) h2q
  unfold lamMix at hmix
  nlinarith [mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ 1 - w G i),
    mul_le_mul_of_nonneg_left hmax (by linarith : (0 : ℝ) ≤ w G i - w G j)]

/-! ### Proposition 4.10 -/

/-- `1/w_i + 1/w_j = ρ_i + ρ_j + 2`. -/
lemma sig_eq (i j : V) : 1 / w G i + 1 / w G j = ρ G i + ρ G j + 2 := by
  simp only [w, one_div_one_div]
  ring

/-- `U^lazy = −1 + 2m⁰ + (1 + △)Δ_α + m^UU` of Proposition 4.10, with
`m^UU = min{𝔪 w_i, |ξ_j| w_j}`. -/
noncomputable def Ulazy (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) : ℝ :=
  -1 + 2 * ((2 + tri G i j) * w G j) + (1 + tri G i j) * (w G i - w G j)
    + min (matchNum G i j * w G i) ((xi G j i).card * w G j)

/-- `min{|ξ_i| w_i, |ξ_j| w_j} ≤ |U_i| w_i` and `≤ Ξ/(ρ_i + ρ_j + 2)`. -/
lemma mUU_xi_le (hij : G.Adj i j) :
    min ((xi G i j).card * w G i) ((xi G j i).card * w G j) ≤ (ρ G i - 1 - tri G i j) * w G i ∧
      min ((xi G i j).card * w G i) ((xi G j i).card * w G j)
        ≤ (Xi G i j : ℝ) / (ρ G i + ρ G j + 2) := by
  have hwi := w_pos (G := G) i
  have hwj := w_pos (G := G) j
  have hsig : 0 < 1 / w G i + 1 / w G j := add_pos (one_div_pos.2 hwi) (one_div_pos.2 hwj)
  have hX : ((xi G i j).card : ℝ) ≤ ρ G i - 1 - tri G i j := by
    rw [← card_uniq_real hij]; exact_mod_cast Finset.card_le_card (xi_subset i j)
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
  rw [sig_eq i j] at hharm
  exact ⟨hm1.trans (mul_le_mul_of_nonneg_right hX hwi.le), hharm⟩

/-- **Proposition 4.10**: the bounds on `m^UU = min{𝔪 w_i, |ξ_j| w_j}`. -/
lemma mUU_le (hij : G.Adj i j) :
    min (matchNum G i j * w G i) ((xi G j i).card * w G j) ≤ (ρ G i - 1 - tri G i j) * w G i ∧
      min (matchNum G i j * w G i) ((xi G j i).card * w G j)
        ≤ (Xi G i j : ℝ) / (ρ G i + ρ G j + 2) := by
  have hmx : (matchNum G i j : ℝ) ≤ (xi G i j).card := by exact_mod_cast matchNum_le_xi
  have hle : min (matchNum G i j * w G i) ((xi G j i).card * w G j)
      ≤ min ((xi G i j).card * w G i) ((xi G j i).card * w G j) :=
    min_le_min (mul_le_mul_of_nonneg_right hmx (w_pos (G := G) i).le) le_rfl
  obtain ⟨h1, h2⟩ := mUU_xi_le hij
  exact ⟨hle.trans h1, hle.trans h2⟩

/-- **Proposition 4.10**: `𝔠_OR ≤ U^lazy ≤ (2 + △) w_j − Δ_α`. Proved by the vertex-cover
potentials of `Cover.lean`, with the covers `ξ_j` and a König cover of `𝔪` vertices. -/
theorem lazy_envelope_paper (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) :
    cOR G d i j ≤ Ulazy G i j ∧ Ulazy G i j ≤ (2 + tri G i j) * w G j - (w G i - w G j) := by
  have hwi := w_pos (G := G) i
  have hw := w_anti (G := G) hle
  have key := lazy_identity (G := G) hij
  have h1 := lazy_envelope_cover hd hij hle (coversCross_xi (G := G) (i := i) (j := j))
  rw [card_filter_xi_left, card_filter_xi_right] at h1
  simp only [Nat.cast_zero, zero_mul, zero_add] at h1
  obtain ⟨K, hK, hKc⟩ := exists_cover_le_matchNum (G := G) i j
  have h2 := lazy_envelope_cover hd hij hle hK
  have hKc' : (((uniq G i j).filter (· ∈ K)).card : ℝ) + ((uniq G j i).filter (· ∈ K)).card
      ≤ matchNum G i j := by exact_mod_cast hKc
  have hb' := mul_le_mul_of_nonneg_left hw
    (Nat.cast_nonneg (α := ℝ) ((uniq G j i).filter (· ∈ K)).card)
  have ha' := mul_le_mul_of_nonneg_right hKc' hwi.le
  have hm : (matchNum G i j : ℝ) ≤ (uniq G i j).card := by exact_mod_cast matchNum_le_uniq
  have hmU := mul_le_mul_of_nonneg_right hm hwi.le
  unfold Ulazy
  constructor
  · rcases le_total ((matchNum G i j : ℝ) * w G i) ((xi G j i).card * w G j) with h | h
    · rw [min_eq_left h]; linarith [h2, hb', ha']
    · rw [min_eq_right h]; linarith [h1]
  · have := min_le_left ((matchNum G i j : ℝ) * w G i) ((xi G j i).card * w G j)
    linarith [hmU, key]

/-! ### Lemma 3.6 in the form used by Section 5 -/

/-- `𝔠_BF ≤ 𝔖 + 𝔗 △ + 2σ` for `ρ_min ≥ 2` (Definition 3.2 and Lemma 3.6). -/
lemma cBF_le_piece3_paper (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) (h2 : 2 ≤ ρ G i) :
    cBF G i j ≤ piece3 (ρ G i) (ρ G j) (tri G i j) (matchNum G i j / ρ G j) := by
  have hmin : ¬ ρmin G i j ≤ 1 := by rw [ρmin_eq hle]; linarith
  have h11 := C4_le_two_matchStat (G := G) hij
  unfold cBF piece3
  rw [ite_eq_right hmin, bfS_eq, bfT_eq hle]
  unfold matchStat at h11
  rw [ρmax_eq hle] at h11
  linarith

/-! ### Theorem 5.4 and Proposition 5.5 -/

/-- **Theorem 5.4**: `𝔠_BF ≥ ζ` implies `𝔠_OR ≥ φ_{a,b}(ζ)`, for every edge with `ρ_i ≤ ρ_j`. -/
theorem bf_lower_paper (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) {ζ : ℝ}
    (hζ : ζ ≤ cBF G i j) : phiAff (ρ G i) (ρ G j) ζ ≤ cOR G d i j := by
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  by_cases h2 : 2 ≤ ρ G i
  · have hq := lazy_quadrangle hd hij hle
    rw [Llazy_eq hρi hρj] at hq
    refine le_trans ?_ hq
    exact (phiAff_le_phiElem (by linarith) hle ζ).trans
      (phiElem_le (by linarith) hle (Nat.cast_nonneg _) (tri_le hij)
        (div_nonneg (Nat.cast_nonneg _) hρj.le) (hζ.trans (cBF_le_piece3_paper hij hle h2)))
  · have h1 := rho_eq_one_of_lt_two hij h2
    have hS : bS (ρ G i) (ρ G j) = 2 / ρ G j := by unfold bS; rw [h1]; ring
    have hSpos : 0 < 2 / ρ G j := div_pos two_pos hρj
    have hbf := cBF_eq_zero_of_leaf hle h1
    have hz : max (ζ - bS (ρ G i) (ρ G j)) 0 = 0 := max_eq_right (by linarith)
    unfold phiAff
    rw [hz, mul_zero, add_zero]
    exact bf_lower_leaf hd hij hle h1

/-- **Proposition 5.5, range of BF**: `𝔠_BF ≤ 𝔖 + 𝔗 (ρ_min − 1)` on every edge. -/
theorem cBF_le_range (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) :
    cBF G i j ≤ bS (ρ G i) (ρ G j) + bT (ρ G i) (ρ G j) * (ρ G i - 1) := by
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  by_cases h2 : 2 ≤ ρ G i
  · have hp := cBF_le_piece3_paper hij hle h2
    unfold piece3 at hp
    have hm : (matchNum G i j : ℝ) ≤ ρ G i - 1 - tri G i j := by
      rw [← card_uniq_real hij]; exact_mod_cast matchNum_le_uniq
    have e1 : (matchNum G i j : ℝ) / ρ G j ≤ (ρ G i - 1 - tri G i j) / ρ G j :=
      div_le_div_of_nonneg_right hm hρj.le
    have e2 : bT (ρ G i) (ρ G j) * (ρ G i - 1) - bT (ρ G i) (ρ G j) * tri G i j
        = 2 * ((ρ G i - 1 - tri G i j) / ρ G j) + (ρ G i - 1 - tri G i j) / ρ G i := by
      unfold bT; ring
    have e3 : 0 ≤ (ρ G i - 1 - tri G i j) / ρ G i := by
      have ht := tri_le hij
      exact div_nonneg (by linarith) hρi.le
    linarith
  · have h1 := rho_eq_one_of_lt_two hij h2
    have hS : bS (ρ G i) (ρ G j) = 2 / ρ G j := by unfold bS; rw [h1]; ring
    rw [cBF_eq_zero_of_leaf hle h1, hS, h1, sub_self, mul_zero, add_zero]
    exact (div_pos two_pos hρj).le

/-! ### Lemma 5.6 and Theorem 5.7 -/

/-- The envelope `Ψ̂(t)` of Theorem 5.7, a minimum of two affine functions of `t`. -/
noncomputable def psiTwo (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (ζ t : ℝ) : ℝ :=
  min ((2 + t) * w G j - (w G i - w G j))
    (-1 + 2 * ((2 + t) * w G j) + (1 + t) * (w G i - w G j)
      + ρ G j * (ρ G j - 1) * (max (ζ - bfS G i j) 0 - bfT G i j * t) / (ρ G i + ρ G j + 2))

/-- The upper modulus `ψ_{a,b}(ζ)` of Theorem 5.7: the maximum of `Ψ̂` over the integers
`0, 1, …, ⌊△_max(ζ)⌋`. -/
noncomputable def psiInt (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (ζ : ℝ) : ℝ :=
  (Finset.range (Nat.floor (triMax G i j ζ) + 1)).sup'
    ⟨0, Finset.mem_range.2 (Nat.zero_lt_succ _)⟩ (fun n : ℕ => psiTwo G i j ζ n)

/-- **Theorem 5.7, deficit form**: `Ψ̂(t) = Θ(t) − [(ρ_i − 1 − t) w_i − ♯*(𝓫 − 𝔗 t)/(ρ_i + ρ_j + 2)]₊`
with `Θ(t) = (3 + t) w_j − w_i`. -/
lemma psiTwo_deficit (hij : G.Adj i j) (ζ t : ℝ) :
    psiTwo G i j ζ t = ((3 + t) * w G j - w G i)
      - max ((ρ G i - 1 - t) * w G i
          - ρ G j * (ρ G j - 1) * (max (ζ - bfS G i j) 0 - bfT G i j * t)
            / (ρ G i + ρ G j + 2)) 0 := by
  have hρw : ρ G i * w G i = 1 - w G i := by
    have h := lazy_nbr_weight hij
    rw [div_eq_iff (ρ_pos hij).ne'] at h
    linarith
  unfold psiTwo
  generalize ρ G j * (ρ G j - 1) * (max (ζ - bfS G i j) 0 - bfT G i j * t)
    / (ρ G i + ρ G j + 2) = B
  rcases le_total ((ρ G i - 1 - t) * w G i - B) 0 with h | h
  · rw [max_eq_right h, min_eq_left (by nlinarith [hρw])]
    ring
  · rw [max_eq_left h, min_eq_right (by nlinarith [hρw])]
    linarith [hρw]

/-- The triangle count is admissible: `△ ≤ △_max(ζ)`. -/
lemma tri_le_triMax (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) {ζ : ℝ} (hζ : cBF G i j ≤ ζ) :
    (tri G i j : ℝ) ≤ triMax G i j ζ := by
  have hT : 0 < bfT G i j := bfT_pos' hij
  unfold triMax
  refine le_min (tri_le hij) ?_
  rw [le_div_iff₀ hT]
  by_cases h2 : 2 ≤ ρ G i
  · have hmin : ¬ ρmin G i j ≤ 1 := by rw [ρmin_eq hle]; linarith
    have hbf : bfS G i j + bfT G i j * tri G i j + C4 G i j ≤ ζ := by
      unfold cBF at hζ; rwa [ite_eq_right hmin] at hζ
    have hC0 := C4_nonneg (G := G) hij
    have hmx := le_max_left (ζ - bfS G i j) 0
    nlinarith
  · rw [leaf_tri hij (rho_eq_one_of_lt_two hij h2), zero_mul]
    exact le_max_right _ _

/-- **Lemma 5.6**: `△ ≤ △_max(ζ)` and `Ξ ≤ ♯*(𝓫(ζ) − 𝔗 △)`. -/
lemma budget_region (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) {ζ : ℝ} (hζ : cBF G i j ≤ ζ) :
    (tri G i j : ℝ) ≤ triMax G i j ζ ∧
      (Xi G i j : ℝ) ≤ ρ G j * (ρ G j - 1) * (max (ζ - bfS G i j) 0 - bfT G i j * tri G i j) := by
  refine ⟨tri_le_triMax hij hle hζ, ?_⟩
  by_cases h2 : 2 ≤ ρ G i
  · exact Xi_le_budget hij hle h2 hζ
  · have h1 := rho_eq_one_of_lt_two hij h2
    have hρj : (1 : ℝ) ≤ ρ G j := by linarith
    rw [leaf_Xi hij h1, leaf_tri hij h1, mul_zero, sub_zero, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (le_max_right _ _)

/-- `U^lazy ≤ Ψ̂(△)`: the two bounds on `m^UU` give the two pieces of `Ψ̂`. -/
lemma Ulazy_le_psiTwo (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) {ζ : ℝ}
    (hζ : cBF G i j ≤ ζ) : Ulazy G i j ≤ psiTwo G i j ζ (tri G i j) := by
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  obtain ⟨hm1, hm2⟩ := mUU_le hij
  have hB := (budget_region hij hle hζ).2
  have hm2' : min (matchNum G i j * w G i) ((xi G j i).card * w G j)
      ≤ ρ G j * (ρ G j - 1) * (max (ζ - bfS G i j) 0 - bfT G i j * tri G i j)
          / (ρ G i + ρ G j + 2) :=
    hm2.trans (div_le_div_of_nonneg_right hB (by linarith))
  have hρw : ρ G i * w G i = 1 - w G i := by
    have h := lazy_nbr_weight hij
    rw [div_eq_iff hρi.ne'] at h
    linarith
  unfold Ulazy psiTwo
  refine le_min ?_ ?_
  · nlinarith [hm1, hρw]
  · linarith [hm2']

lemma psiTwo_le_psiInt {ζ : ℝ} {n : ℕ} (hn : (n : ℝ) ≤ triMax G i j ζ) :
    psiTwo G i j ζ n ≤ psiInt G i j ζ := by
  have hmem : n ∈ Finset.range (Nat.floor (triMax G i j ζ) + 1) :=
    Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hn))
  unfold psiInt
  exact Finset.le_sup' (fun m : ℕ => psiTwo G i j ζ m) hmem

/-- **Theorem 5.7**: `𝔠_BF ≤ ζ` implies `𝔠_OR ≤ ψ_{a,b}(ζ)`, for every edge with `ρ_i ≤ ρ_j`. -/
theorem bf_upper_paper (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) {ζ : ℝ}
    (hζ : cBF G i j ≤ ζ) : cOR G d i j ≤ psiInt G i j ζ :=
  ((lazy_envelope_paper hd hij hle).1.trans (Ulazy_le_psiTwo hij hle hζ)).trans
    (psiTwo_le_psiInt (tri_le_triMax hij hle hζ))

/-- **Theorem 5.7**: the upper modulus is nondecreasing. -/
theorem psiInt_mono (hij : G.Adj i j) {ζ ζ' : ℝ} (h : ζ ≤ ζ') :
    psiInt G i j ζ ≤ psiInt G i j ζ' := by
  have hT : 0 < bfT G i j := bfT_pos' hij
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  have hbud : max (ζ - bfS G i j) 0 ≤ max (ζ' - bfS G i j) 0 := max_le_max (by linarith) le_rfl
  have htm : triMax G i j ζ ≤ triMax G i j ζ' := by
    unfold triMax
    exact min_le_min le_rfl (div_le_div_of_nonneg_right hbud hT.le)
  have hsho : 0 ≤ ρ G j * (ρ G j - 1) := by
    have h1 : (1 : ℝ) ≤ ρ G j := by
      have : 0 < G.degree j := (G.degree_pos_iff_exists_adj j).2 ⟨i, hij.symm⟩
      simp only [ρ]; exact_mod_cast this
    nlinarith
  unfold psiInt
  refine Finset.sup'_le _ _ (fun n hn => ?_)
  have hn' : (n : ℝ) ≤ triMax G i j ζ' := by
    have hfl : n ≤ Nat.floor (triMax G i j ζ) := by
      have := Finset.mem_range.1 hn; omega
    have h0 : 0 ≤ triMax G i j ζ := triMax_nonneg hij ζ
    have := (Nat.le_floor_iff h0).1 hfl
    linarith
  have hpt : psiTwo G i j ζ n ≤ psiTwo G i j ζ' n := by
    unfold psiTwo
    refine min_le_min le_rfl (add_le_add le_rfl ?_)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hsho) (by linarith)
  exact hpt.trans (psiTwo_le_psiInt hn')

/-! ### Corollary 5.8 and Proposition 5.9 -/

/-- **Corollary 5.8, the key inequality**: `φ^ℤ_{a,b}(𝔠_BF) ≤ L^lazy`, for `ρ_i ≤ ρ_j`. -/
theorem phiInt_le_Llazy (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) :
    phiInt (ρ G i) (ρ G j) (cBF G i j) ≤ Llazy (ρ G i) (ρ G j) (tri G i j) (matchNum G i j) := by
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  have hT := bT_pos hρi hρj
  by_cases h2 : 2 ≤ ρ G i
  · have hk12 := kappa1_le_kappa2 hρi hle
    have hk2 : 0 ≤ kappa2 (ρ G j) := by unfold kappa2; exact div_nonneg hρj.le (by linarith)
    have hmin : ¬ ρmin G i j ≤ 1 := by rw [ρmin_eq hle]; linarith
    have hC0 := C4_nonneg (G := G) hij
    have hz : cBF G i j - bS (ρ G i) (ρ G j) = bT (ρ G i) (ρ G j) * tri G i j + C4 G i j := by
      unfold cBF; rw [ite_eq_right hmin, bfS_eq, bfT_eq hle]; ring
    have hzmax : max (cBF G i j - bS (ρ G i) (ρ G j)) 0
        = bT (ρ G i) (ρ G j) * tri G i j + C4 G i j := by
      rw [hz]; exact max_eq_left (add_nonneg (mul_nonneg hT.le (Nat.cast_nonneg _)) hC0)
    -- the triangle count is admissible: `△ ≤ t⋆`
    have htle : (tri G i j : ℝ) ≤ tStar (ρ G i) (ρ G j) (cBF G i j) := by
      unfold tStar
      refine le_min (tri_le hij) ?_
      rw [hzmax]
      have hq : (tri G i j : ℝ)
          ≤ (bT (ρ G i) (ρ G j) * tri G i j + C4 G i j) / bT (ρ G i) (ρ G j) := by
        rw [le_div_iff₀ hT]; nlinarith
      exact_mod_cast Nat.le_floor hq
    -- the 4-cycle term is at most `2σ` (Lemma 3.6)
    have hC4 : C4 G i j ≤ 2 * (matchNum G i j / ρ G j) := by
      have h := C4_le_two_matchStat (G := G) hij
      unfold matchStat at h; rwa [ρmax_eq hle] at h
    have e1 := mul_le_mul_of_nonneg_left hC4 hk2
    have e2 : 0 ≤ (kappa2 (ρ G j) - kappa1 (ρ G i) (ρ G j))
        * (bT (ρ G i) (ρ G j) * (tStar (ρ G i) (ρ G j) (cBF G i j) - tri G i j)) :=
      mul_nonneg (by linarith) (mul_nonneg hT.le (by linarith))
    rw [Llazy_eq hρi hρj]
    unfold phiInt
    rw [hzmax]
    linarith [e1, e2]
  · have h1 := rho_eq_one_of_lt_two hij h2
    have hS : bS (ρ G i) (ρ G j) = 2 / ρ G j := by unfold bS; rw [h1]; ring
    have hSpos : 0 < 2 / ρ G j := div_pos two_pos hρj
    have hbf := cBF_eq_zero_of_leaf hle h1
    have hz : max (cBF G i j - bS (ρ G i) (ρ G j)) 0 = 0 :=
      max_eq_right (by rw [hbf, hS]; linarith)
    have hts : tStar (ρ G i) (ρ G j) (cBF G i j) = 0 := by
      unfold tStar; rw [hz, h1]; simp
    have ht := leaf_tri hij h1
    have hm := leaf_matchNum hij h1
    unfold phiInt
    rw [hz, hts, ht, hm]
    apply le_of_eq
    unfold Llazy L0
    ring

/-- **Corollary 5.8**: the BF interval `𝔠_OR ∈ [φ^ℤ_{a,b}(𝔠_BF), ψ_{a,b}(𝔠_BF)]`, for every edge
with `ρ_i ≤ ρ_j`. -/
theorem bf_interval_paper (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) :
    phiInt (ρ G i) (ρ G j) (cBF G i j) ≤ cOR G d i j ∧ cOR G d i j ≤ psiInt G i j (cBF G i j) :=
  ⟨(phiInt_le_Llazy hij hle).trans (lazy_quadrangle hd hij hle),
    bf_upper_paper hd hij hle le_rfl⟩

/-- **Proposition 5.9**: the 2-hop interval
`φ^ℤ(𝔠_BF) ≤ L^lazy ≤ 𝔠_OR ≤ U^lazy ≤ Ψ̂(△) ≤ ψ(𝔠_BF)`, for every edge with `ρ_i ≤ ρ_j`. -/
theorem two_hop_interval_paper (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) :
    phiInt (ρ G i) (ρ G j) (cBF G i j) ≤ Llazy (ρ G i) (ρ G j) (tri G i j) (matchNum G i j) ∧
      Llazy (ρ G i) (ρ G j) (tri G i j) (matchNum G i j) ≤ cOR G d i j ∧
      cOR G d i j ≤ Ulazy G i j ∧
      Ulazy G i j ≤ psiTwo G i j (cBF G i j) (tri G i j) ∧
      psiTwo G i j (cBF G i j) (tri G i j) ≤ psiInt G i j (cBF G i j) :=
  ⟨phiInt_le_Llazy hij hle, lazy_quadrangle hd hij hle, (lazy_envelope_paper hd hij hle).1,
    Ulazy_le_psiTwo hij hle le_rfl, psiTwo_le_psiInt (tri_le_triMax hij hle le_rfl)⟩

/-! ### Appendix C -/

/-- The coverage bound (Proposition 4.10, last inequality; equation (C.1)):
`𝔠_OR ≤ (2 + △) w_j − Δ_α`. -/
theorem coverage_bound (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) :
    cOR G d i j ≤ (2 + tri G i j) * w G j - (w G i - w G j) :=
  (lazy_envelope_paper hd hij hle).1.trans (lazy_envelope_paper hd hij hle).2

/-- The closed form in (C.1): `(2 + t) w_j − Δ_α = (3 + t)/(ρ_j + 1) − 1/(ρ_i + 1)`. -/
lemma coverage_bound_eq (t : ℝ) :
    (2 + t) * w G j - (w G i - w G j) = (3 + t) / (ρ G j + 1) - 1 / (ρ G i + 1) := by
  simp only [w]
  ring

/-- **Corollary C.1**, with the closed-form threshold `t_min(ϑ) = ⌈(ϑ + Δ_α)(ρ_j + 1) − 2⌉₊`.
The last conjunct says that no edge with these degrees has `𝔠_OR ≥ ϑ` unless
`t_min(ϑ) ≤ ρ_i − 1`. -/
theorem or_to_bf_lower_paper (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j)
    (h2 : 2 ≤ ρ G i) {ϑ : ℝ} (h : ϑ ≤ cOR G d i j) :
    Nat.ceil ((ϑ + (w G i - w G j)) * (ρ G j + 1) - 2) ≤ tri G i j ∧
      bfS G i j + bfT G i j * (Nat.ceil ((ϑ + (w G i - w G j)) * (ρ G j + 1) - 2) : ℝ)
        ≤ cBF G i j ∧
      (Nat.ceil ((ϑ + (w G i - w G j)) * (ρ G j + 1) - 2) : ℝ) ≤ ρ G i - 1 := by
  have hρj := ρ_pos hij.symm
  have hpos : 0 < ρ G j + 1 := by linarith
  have hcov := h.trans (coverage_bound hd hij hle)
  have e : (2 + (tri G i j : ℝ)) * w G j * (ρ G j + 1) = 2 + tri G i j := by
    show (2 + (tri G i j : ℝ)) * (1 / (ρ G j + 1)) * (ρ G j + 1) = 2 + tri G i j
    rw [mul_one_div, div_mul_cancel₀ _ hpos.ne']
  have ht : (ϑ + (w G i - w G j)) * (ρ G j + 1) - 2 ≤ tri G i j := by
    nlinarith [mul_le_mul_of_nonneg_right hcov hpos.le, e]
  have hceil : Nat.ceil ((ϑ + (w G i - w G j)) * (ρ G j + 1) - 2) ≤ tri G i j :=
    Nat.ceil_le.2 ht
  have hc : (Nat.ceil ((ϑ + (w G i - w G j)) * (ρ G j + 1) - 2) : ℝ) ≤ tri G i j := by
    exact_mod_cast hceil
  refine ⟨hceil, ?_, hc.trans (tri_le hij)⟩
  have hmin : ¬ ρmin G i j ≤ 1 := by rw [ρmin_eq hle]; linarith
  have hT := bfT_pos' hij
  unfold cBF
  rw [ite_eq_right hmin]
  nlinarith [mul_le_mul_of_nonneg_left hc hT.le, C4_nonneg (G := G) hij]

/-- **Corollary C.2**: inverting the lower modulus, `𝔠_OR ≤ ϑ` implies
`𝔠_BF ≤ 𝔖 + min{𝔗(ρ_i − 1), (ϑ − L⁰)/κ₁}`. -/
theorem or_to_bf_upper_paper (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j)
    (h2 : 2 ≤ ρ G i) {ϑ : ℝ} (h : cOR G d i j ≤ ϑ) :
    cBF G i j ≤ bS (ρ G i) (ρ G j) + min (bT (ρ G i) (ρ G j) * (ρ G i - 1))
      ((ϑ - L0 (ρ G i) (ρ G j)) / kappa1 (ρ G i) (ρ G j)) := by
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  have hk1 : 0 < kappa1 (ρ G i) (ρ G j) := by
    unfold kappa1
    exact div_pos (add_pos (div_pos one_pos (by linarith)) (div_pos two_pos (by linarith)))
      (bT_pos hρi hρj)
  have hS : bS (ρ G i) (ρ G j) ≤ cBF G i j := by
    have hmin : ¬ ρmin G i j ≤ 1 := by rw [ρmin_eq hle]; linarith
    have hT := bfT_pos' hij
    have e : bfS G i j = bS (ρ G i) (ρ G j) := bfS_eq
    unfold cBF
    rw [ite_eq_right hmin]
    nlinarith [C4_nonneg (G := G) hij,
      mul_nonneg hT.le (Nat.cast_nonneg (tri G i j) : (0 : ℝ) ≤ tri G i j), e]
  have hφ : phiAff (ρ G i) (ρ G j) (cBF G i j)
      = L0 (ρ G i) (ρ G j) + kappa1 (ρ G i) (ρ G j) * (cBF G i j - bS (ρ G i) (ρ G j)) := by
    unfold phiAff
    rw [max_eq_left (by linarith)]
  have hlow := bf_lower_paper hd hij hle (le_refl (cBF G i j))
  have hinv : cBF G i j - bS (ρ G i) (ρ G j)
      ≤ (ϑ - L0 (ρ G i) (ρ G j)) / kappa1 (ρ G i) (ρ G j) := by
    rw [le_div_iff₀ hk1]
    nlinarith [hlow, h, hφ]
  have hrange := cBF_le_range hij hle
  have hmin2 := le_min (show cBF G i j - bS (ρ G i) (ρ G j)
      ≤ bT (ρ G i) (ρ G j) * (ρ G i - 1) by linarith) hinv
  linarith

/-- The second bound of Corollary C.3 of an earlier version (dropped from the paper: computing
`𝔪` and `𝔠₄` already determines `𝔠_BF`), kept for reference. -/
theorem or_to_bf_upper_matching (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j)
    (h2 : 2 ≤ ρ G i) {ϑ : ℝ} (h : cOR G d i j ≤ ϑ) :
    cBF G i j ≤ bS (ρ G i) (ρ G j) + min (bT (ρ G i) (ρ G j) * (ρ G i - 1))
      (max (ϑ - L0 (ρ G i) (ρ G j) - 2 * matchNum G i j / (ρ G j + 1)) 0
        / kappa1 (ρ G i) (ρ G j)) + C4 G i j := by
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  have hT := bT_pos hρi hρj
  have hold := or_to_bf_elementary hd hij hle h2 h
  have e1 : bfT G i j * min (ρ G i - 1)
      (max (ϑ - L0 (ρ G i) (ρ G j) - 2 * matchNum G i j / (ρ G j + 1)) 0
        / (1 / (ρ G i + 1) + 2 / (ρ G j + 1)))
      = min (bT (ρ G i) (ρ G j) * (ρ G i - 1))
          (max (ϑ - L0 (ρ G i) (ρ G j) - 2 * matchNum G i j / (ρ G j + 1)) 0
            / kappa1 (ρ G i) (ρ G j)) := by
    rw [bfT_eq hle, mul_min_of_nonneg _ _ hT.le]
    congr 1
    unfold kappa1
    rw [div_div_eq_mul_div]
    ring
  have e2 : bfS G i j = bS (ρ G i) (ρ G j) := bfS_eq
  linarith [hold, e1, e2]

end OllivierBF
