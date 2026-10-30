/-
  Proposition B.1 of the paper (Appendix B): an upper envelope for OR curvature at arbitrary
  idleness `α_i, α_j ∈ [0, 1)`, and, for the lazy measure, its comparison with `U^lazy` of
  Proposition 4.8.
  The paper derives B.1 from a coupling that saturates the diagonal (Villani, Cor. 1.16). Here it
  follows from weak duality alone, with two pairs of potentials: for a vertex cover `K` of the
  cross-edge graph, `f = 2` on `U_i \ K` and `g = 0` on `U_j \ K` (the branch
  `m^{(α)}_△ = △ |w_i − w_j|`), and `f = g = c₀ ∈ {0, 2}` on the common neighbours (the branch
  `m^{(α)}_△ = |U_i| w_i + |U_j| w_j`). Nothing in this file takes a published result as a
  hypothesis.
-/

module

public import OllivierBF.Paper

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ} {i j : V}

/-! ### Weak duality with two potentials -/

/-- **Weak duality**: potentials with `f x − g y ≤ d x y` bound every coupling from below. -/
lemma cost_ge_two_potentials {μ ν : V → ℝ} {π : V → V → ℝ} (f g : V → ℝ)
    (hfg : ∀ x y, f x - g y ≤ d x y) (hπ : IsCoupling μ ν π) :
    ∑ x, f x * μ x - ∑ y, g y * ν y ≤ cost d π := by
  have h1 : ∑ x, f x * μ x = ∑ x, ∑ y, f x * π x y := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum, hπ.2.1 x]
  have h2 : ∑ y, g y * ν y = ∑ x, ∑ y, g y * π x y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, hπ.2.2 y]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  unfold cost
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have e : f x * π x y - g y * π x y = (f x - g y) * π x y := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (hfg x y) (hπ.1 x y)

/-- `Σ_k f(k) m^p_u(k) = f(u) p + (1 − p)/ρ_u · Σ_{k ∈ N(u)} f(k)`. -/
lemma sum_mul_mp (p : ℝ) (u : V) (f : V → ℝ) :
    ∑ k, f k * mp G p u k = f u * p + (1 - p) / ρ G u * ∑ k ∈ G.neighborFinset u, f k := by
  have hsplit : ∀ k, f k * mp G p u k =
      (if k = u then f u * p else 0) + (if G.Adj u k then f k * ((1 - p) / ρ G u) else 0) := by
    intro k
    by_cases h1 : k = u
    · subst h1
      simp [mp, SimpleGraph.irrefl]
    · by_cases h2 : G.Adj u k
      · simp [mp, h1, h2]
      · simp [mp, h1, h2]
  rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_univ u), ← Finset.sum_filter, ← SimpleGraph.neighborFinset_eq_filter,
    ← Finset.sum_mul]
  ring

/-! ### Elementary identities -/

/-- `2 min{x, y} + [x − y]₊ + [y − x]₊ = x + y`, which gives `2 z_i + r_i + r̄_i = α_i + w_j`. -/
lemma two_min_add_parts (x y : ℝ) : 2 * min x y + (max (x - y) 0 + max (y - x) 0) = x + y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_right (show x - y ≤ 0 by linarith),
      max_eq_left (show 0 ≤ y - x by linarith)]
    ring
  · rw [min_eq_right h, max_eq_left (show 0 ≤ x - y by linarith),
      max_eq_right (show y - x ≤ 0 by linarith)]
    ring

/-- `2 min{x, y} + |x − y| = x + y`. -/
lemma two_min_add_abs (x y : ℝ) : 2 * min x y + |x - y| = x + y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (show x - y ≤ 0 by linarith)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (show 0 ≤ x - y by linarith)]
    ring

/-- `min{|ξ_i| w_i, |ξ_j| w_j} ≤ m^{(α)}_UU = min{|U_i| w_i, |U_j| w_j, Ξ/Σ}` for positive weights:
the cap `Ξ/Σ` is a weighted average of `|ξ_i| w_i` and `|ξ_j| w_j`. -/
lemma mUU_ge {wi wj : ℝ} (hwi : 0 < wi) (hwj : 0 < wj) :
    min ((xi G i j).card * wi) ((xi G j i).card * wj)
      ≤ min (min ((uniq G i j).card * wi) ((uniq G j i).card * wj))
          (Xi G i j / (1 / wi + 1 / wj)) := by
  have hξi : ((xi G i j).card : ℝ) ≤ (uniq G i j).card := by
    exact_mod_cast Finset.card_le_card (xi_subset i j)
  have hξj : ((xi G j i).card : ℝ) ≤ (uniq G j i).card := by
    exact_mod_cast Finset.card_le_card (xi_subset j i)
  have hs : 0 < 1 / wi + 1 / wj := add_pos (one_div_pos.2 hwi) (one_div_pos.2 hwj)
  refine le_min (le_min ?_ ?_) ?_
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hξi hwi.le)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right hξj hwj.le)
  · rw [le_div_iff₀ hs]
    have h1 : min ((xi G i j).card * wi) ((xi G j i).card * wj) / wi ≤ (xi G i j).card := by
      rw [div_le_iff₀ hwi]
      exact min_le_left _ _
    have h2 : min ((xi G i j).card * wi) ((xi G j i).card * wj) / wj ≤ (xi G j i).card := by
      rw [div_le_iff₀ hwj]
      exact min_le_right _ _
    have e : (Xi G i j : ℝ) = (xi G i j).card + (xi G j i).card := by simp [Xi]
    rw [e]
    calc min ((xi G i j).card * wi) ((xi G j i).card * wj) * (1 / wi + 1 / wj)
        = min ((xi G i j).card * wi) ((xi G j i).card * wj) / wi
          + min ((xi G i j).card * wi) ((xi G j i).card * wj) / wj := by ring
      _ ≤ (xi G i j).card + (xi G j i).card := add_le_add h1 h2

/-! ### The envelope -/

/-- The weight `w^{(α)}_u = (1 − α)/ρ_u` that the measure with idleness `α` puts on each
neighbour of `u`. -/
noncomputable def wα (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (u : V) : ℝ :=
  (1 - α) / ρ G u

/-- `U^env` of Proposition B.1, with `z_i = min{α_i, w_j}`, `r_i = [α_i − w_j]₊`,
`r̄_i = [w_j − α_i]₊` (and symmetrically for `j`), `w_∧ = min{w_i, w_j}`,
`m^{(α)}_UU = min{|U_i| w_i, |U_j| w_j, Ξ/Σ}` with `Σ = 1/w_i + 1/w_j`, and
`m^{(α)}_△ = min{△ |w_i − w_j|, |U_i| w_i + |U_j| w_j}`. -/
noncomputable def Uenv (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (αi αj : ℝ) : ℝ :=
  -1 + 2 * (min αi (wα G αj j) + min αj (wα G αi i))
    + (max (αi - wα G αj j) 0 + max (wα G αj j - αi) 0
      + (max (αj - wα G αi i) 0 + max (wα G αi i - αj) 0))
    + 2 * tri G i j * min (wα G αi i) (wα G αj j)
    + min (min ((uniq G i j).card * wα G αi i) ((uniq G j i).card * wα G αj j))
        (Xi G i j / (1 / wα G αi i + 1 / wα G αj j))
    + min (tri G i j * |wα G αi i - wα G αj j|)
        ((uniq G i j).card * wα G αi i + (uniq G j i).card * wα G αj j)

/-! #### First pair of potentials: a vertex cover `K` of the cross-edge graph -/

/-- `f = 2` on `U_i \ K`, `1` elsewhere on `{i} ∪ N(i)`, and `0` off it. -/
noncomputable def envF (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (K : Finset V)
    (x : V) : ℝ :=
  if x ∈ uniq G i j ∧ x ∉ K then 2 else if x = i ∨ G.Adj i x then 1 else 0

/-- `g = 0` on `U_j \ K`, `1` elsewhere on `{j} ∪ N(j)`, and `2` off it. -/
noncomputable def envG (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (K : Finset V)
    (y : V) : ℝ :=
  if y ∈ uniq G j i ∧ y ∉ K then 0 else if y = j ∨ G.Adj j y then 1 else 2

lemma envPot_lip (hd : GraphMetric G d) {K : Finset V} (hK : CoversCross G i j K) (x y : V) :
    envF G i j K x - envG G i j K y ≤ d x y := by
  by_cases hxy : x = y
  · rw [← hxy, hd.self]
    by_cases hX : x ∈ uniq G i j ∧ x ∉ K
    · obtain ⟨hxj, -, hnadj⟩ := mem_uniq.1 hX.1
      have hY : ¬ (x ∈ uniq G j i ∧ x ∉ K) := fun h => uniq_not_mem_swap hX.1 h.1
      have hN : ¬ (x = j ∨ G.Adj j x) := by
        rintro (h | h)
        · exact hxj h
        · exact hnadj h
      simp only [envF, envG, ite_eq_left hX, ite_eq_right hY, ite_eq_right hN]
      norm_num
    · by_cases hY : x ∈ uniq G j i ∧ x ∉ K
      · obtain ⟨hxi, -, hnadj⟩ := mem_uniq.1 hY.1
        have hN : ¬ (x = i ∨ G.Adj i x) := by
          rintro (h | h)
          · exact hxi h
          · exact hnadj h
        simp only [envF, envG, ite_eq_right hX, ite_eq_left hY, ite_eq_right hN]
        norm_num
      · simp only [envF, envG, ite_eq_right hX, ite_eq_right hY]
        split_ifs <;> norm_num
  · have h1 := hd.one_le hxy
    have hf2 : envF G i j K x ≤ 2 := by
      unfold envF
      split_ifs <;> norm_num
    have hg0 : 0 ≤ envG G i j K y := by
      unfold envG
      split_ifs <;> norm_num
    by_cases hX : x ∈ uniq G i j ∧ x ∉ K
    · by_cases hY : y ∈ uniq G j i ∧ y ∉ K
      · -- the only pairs at potential difference `2` are not adjacent
        have hnadj : ¬ G.Adj x y := by
          intro hadj
          rcases hK x hX.1 y hY.1 hadj with h | h
          · exact hX.2 h
          · exact hY.2 h
        have h2 := hd.two_le hxy hnadj
        linarith
      · have hg1 : 1 ≤ envG G i j K y := by
          unfold envG
          rw [ite_eq_right hY]
          split_ifs <;> norm_num
        linarith
    · have hf1 : envF G i j K x ≤ 1 := by
        unfold envF
        rw [ite_eq_right hX]
        split_ifs <;> norm_num
      linarith

lemma envF_self (K : Finset V) : envF G i j K i = 1 := by
  have hi : i ∉ uniq G i j := fun h => G.irrefl (mem_uniq.1 h).2.1
  simp [envF, hi]

lemma envF_j (hij : G.Adj i j) (K : Finset V) : envF G i j K j = 1 := by
  have hj : j ∉ uniq G i j := fun h => (mem_uniq.1 h).1 rfl
  simp [envF, hj, hij]

lemma envF_common (K : Finset V) {k : V} (hk : k ∈ common G i j) : envF G i j K k = 1 := by
  obtain ⟨hik, hjk⟩ := mem_common.1 hk
  have hkU : k ∉ uniq G i j := fun h => (mem_uniq.1 h).2.2 hjk
  simp [envF, hkU, hik]

lemma envF_Ui (K : Finset V) {x : V} (hx : x ∈ uniq G i j) :
    envF G i j K x = if x ∈ K then 1 else 2 := by
  have hix : G.Adj i x := (mem_uniq.1 hx).2.1
  by_cases hK : x ∈ K <;> simp [envF, hx, hK, hix]

lemma envF_sum_nbr (hij : G.Adj i j) (K : Finset V) :
    ∑ k ∈ G.neighborFinset i, envF G i j K k
      = 1 + ((common G i j).card : ℝ)
        + (2 * ((uniq G i j).card : ℝ) - ((uniq G i j).filter (· ∈ K)).card) := by
  rw [sum_nbr_split hij, envF_j hij, Finset.sum_congr rfl fun k hk => envF_common K hk,
    Finset.sum_congr rfl fun x hx => envF_Ui K hx, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h : ∀ x ∈ uniq G i j, (if x ∈ K then (1 : ℝ) else 2) = 2 - (if x ∈ K then 1 else 0) := by
    intro x _
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_boole]
  ring

lemma envG_self (K : Finset V) : envG G i j K j = 1 := by
  have hj : j ∉ uniq G j i := fun h => G.irrefl (mem_uniq.1 h).2.1
  simp [envG, hj]

lemma envG_i (hij : G.Adj i j) (K : Finset V) : envG G i j K i = 1 := by
  have hi : i ∉ uniq G j i := fun h => (mem_uniq.1 h).1 rfl
  simp [envG, hi, hij.symm]

lemma envG_common (K : Finset V) {k : V} (hk : k ∈ common G j i) : envG G i j K k = 1 := by
  obtain ⟨hjk, hik⟩ := mem_common.1 hk
  have hkU : k ∉ uniq G j i := fun h => (mem_uniq.1 h).2.2 hik
  simp [envG, hkU, hjk]

lemma envG_Uj (K : Finset V) {y : V} (hy : y ∈ uniq G j i) :
    envG G i j K y = if y ∈ K then 1 else 0 := by
  have hjy : G.Adj j y := (mem_uniq.1 hy).2.1
  by_cases hK : y ∈ K <;> simp [envG, hy, hK, hjy]

lemma envG_sum_nbr (hij : G.Adj i j) (K : Finset V) :
    ∑ k ∈ G.neighborFinset j, envG G i j K k
      = 1 + ((common G j i).card : ℝ) + (((uniq G j i).filter (· ∈ K)).card : ℝ) := by
  rw [sum_nbr_split hij.symm, envG_i hij, Finset.sum_congr rfl fun k hk => envG_common K hk,
    Finset.sum_congr rfl fun y hy => envG_Uj K hy, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.sum_boole]

/-! #### Second pair of potentials: `c₀ ∈ {0, 2}` on the common neighbours -/

/-- `f = c₀` on `C`, `1` elsewhere on `{i} ∪ N(i)`, and `0` off it. -/
noncomputable def envF2 (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (c₀ : ℝ) (x : V) : ℝ :=
  if x ∈ common G i j then c₀ else if x = i ∨ G.Adj i x then 1 else 0

/-- `g = c₀` on `C`, `1` elsewhere on `{j} ∪ N(j)`, and `2` off it. -/
noncomputable def envG2 (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (c₀ : ℝ) (y : V) : ℝ :=
  if y ∈ common G i j then c₀ else if y = j ∨ G.Adj j y then 1 else 2

lemma envPot2_lip (hd : GraphMetric G d) {c₀ : ℝ} (hc : c₀ = 0 ∨ c₀ = 2) (x y : V) :
    envF2 G i j c₀ x - envG2 G i j c₀ y ≤ d x y := by
  by_cases hxy : x = y
  · rw [← hxy, hd.self]
    by_cases hC : x ∈ common G i j
    · simp only [envF2, envG2, ite_eq_left hC]
      linarith
    · simp only [envF2, envG2, ite_eq_right hC]
      split_ifs <;> norm_num
  · have h1 := hd.one_le hxy
    -- `f − g ≤ 1` everywhere
    have key : envF2 G i j c₀ x - envG2 G i j c₀ y ≤ 1 := by
      rcases hc with rfl | rfl
      · have hf : envF2 G i j 0 x ≤ 1 := by
          unfold envF2
          split_ifs <;> norm_num
        have hg : 0 ≤ envG2 G i j 0 y := by
          unfold envG2
          split_ifs <;> norm_num
        linarith
      · have hf : envF2 G i j 2 x ≤ 2 := by
          unfold envF2
          split_ifs <;> norm_num
        have hg : 1 ≤ envG2 G i j 2 y := by
          unfold envG2
          split_ifs <;> norm_num
        linarith
    linarith

lemma envF2_self (c₀ : ℝ) : envF2 G i j c₀ i = 1 := by
  have hi : i ∉ common G i j := fun h => G.irrefl (mem_common.1 h).1
  simp [envF2, hi]

lemma envG2_self (c₀ : ℝ) : envG2 G i j c₀ j = 1 := by
  have hj : j ∉ common G i j := fun h => G.irrefl (mem_common.1 h).2
  simp [envG2, hj]

lemma envF2_sum (hij : G.Adj i j) (c₀ : ℝ) :
    ∑ k ∈ G.neighborFinset i, envF2 G i j c₀ k
      = 1 + ((common G i j).card : ℝ) * c₀ + (uniq G i j).card := by
  have hj : envF2 G i j c₀ j = 1 := by
    have : j ∉ common G i j := fun h => G.irrefl (mem_common.1 h).2
    simp [envF2, this, hij]
  have hC : ∀ k ∈ common G i j, envF2 G i j c₀ k = c₀ := fun k hk => by simp [envF2, hk]
  have hU : ∀ x ∈ uniq G i j, envF2 G i j c₀ x = 1 := by
    intro x hx
    obtain ⟨-, hix, hjx⟩ := mem_uniq.1 hx
    have : x ∉ common G i j := fun h => hjx (mem_common.1 h).2
    simp [envF2, this, hix]
  rw [sum_nbr_split hij, hj, Finset.sum_congr rfl hC, Finset.sum_congr rfl hU,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]

lemma envG2_sum (hij : G.Adj i j) (c₀ : ℝ) :
    ∑ k ∈ G.neighborFinset j, envG2 G i j c₀ k
      = 1 + ((common G i j).card : ℝ) * c₀ + (uniq G j i).card := by
  have hi : envG2 G i j c₀ i = 1 := by
    have : i ∉ common G i j := fun h => G.irrefl (mem_common.1 h).1
    simp [envG2, this, hij.symm]
  have hC : ∀ k ∈ common G j i, envG2 G i j c₀ k = c₀ := fun k hk => by
    rw [common_comm] at hk
    simp [envG2, hk]
  have hU : ∀ y ∈ uniq G j i, envG2 G i j c₀ y = 1 := by
    intro y hy
    obtain ⟨-, hjy, hiy⟩ := mem_uniq.1 hy
    have : y ∉ common G i j := fun h => hiy (mem_common.1 h).1
    simp [envG2, this, hjy]
  rw [sum_nbr_split hij.symm, hi, Finset.sum_congr rfl hC, Finset.sum_congr rfl hU,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, common_comm j i]

/-! #### Proposition B.1 -/

/-- **Proposition B.1**: for every edge and all idleness parameters `α_i, α_j ∈ [0, 1)`,
`1 − W₁(m_i, m_j) ≤ U^env`, where `m_u = α_u δ_u + (1 − α_u) ν_u`. -/
theorem envelope_arbitrary_idleness (hd : GraphMetric G d) (hij : G.Adj i j)
    {αi αj : ℝ} (hi0 : 0 ≤ αi) (hi1 : αi < 1) (hj0 : 0 ≤ αj) (hj1 : αj < 1) :
    1 - W1 d (mp G αi i) (mp G αj j) ≤ Uenv G i j αi αj := by
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  have hwi : 0 < wα G αi i := div_pos (by linarith) hρi
  have hwj : 0 < wα G αj j := div_pos (by linarith) hρj
  -- the two measures have mass one
  have hri : ρ G i / ρ G i = 1 := div_self hρi.ne'
  have hrj : ρ G j / ρ G j = 1 := div_self hρj.ne'
  have hmi : ρ G i * wα G αi i = 1 - αi := by
    unfold wα
    linear_combination (1 - αi) * hri
  have hmj : ρ G j * wα G αj j = 1 - αj := by
    unfold wα
    linear_combination (1 - αj) * hrj
  have hUi := card_uniq_real hij
  have hUj := card_uniq_real hij.symm
  have htri : (tri G j i : ℝ) = tri G i j := by rw [tri_comm]
  have hmassi : αi + wα G αi i * (1 + tri G i j + (uniq G i j).card) = 1 := by
    rw [hUi]
    linarith
  have hmassj : αj + wα G αj j * (1 + tri G i j + (uniq G j i).card) = 1 := by
    rw [hUj, htri]
    linarith
  -- weak duality with the two families of potentials
  have hne : ∃ π, IsCoupling (mp G αi i) (mp G αj j) π :=
    exists_coupling_prob (fun x => mp_nonneg hi0 hi1.le i x) (fun x => mp_nonneg hj0 hj1.le j x)
      (mp_sum hij) (mp_sum hij.symm)
  have bound1 : ∀ K, CoversCross G i j K →
      ∑ x, envF G i j K x * mp G αi i x - ∑ y, envG G i j K y * mp G αj j y
        ≤ W1 d (mp G αi i) (mp G αj j) := fun K hK =>
    le_W1 hne fun π hπ => cost_ge_two_potentials _ _ (envPot_lip hd hK) hπ
  have bound2 : ∀ c₀ : ℝ, (c₀ = 0 ∨ c₀ = 2) →
      ∑ x, envF2 G i j c₀ x * mp G αi i x - ∑ y, envG2 G i j c₀ y * mp G αj j y
        ≤ W1 d (mp G αi i) (mp G αj j) := fun c₀ hc =>
    le_W1 hne fun π hπ => cost_ge_two_potentials _ _ (envPot2_lip (i := i) (j := j) hd hc) hπ
  -- the potentials against the measures
  have hF : ∀ K : Finset V, ∑ x, envF G i j K x * mp G αi i x
      = αi + wα G αi i * (1 + tri G i j
        + (2 * ((uniq G i j).card : ℝ) - ((uniq G i j).filter (· ∈ K)).card)) := by
    intro K
    rw [sum_mul_mp, envF_self, envF_sum_nbr hij]
    simp only [wα, tri]
    ring
  have hG : ∀ K : Finset V, ∑ y, envG G i j K y * mp G αj j y
      = αj + wα G αj j * (1 + tri G i j + ((uniq G j i).filter (· ∈ K)).card) := by
    intro K
    rw [sum_mul_mp, envG_self, envG_sum_nbr hij, common_comm j i]
    simp only [wα, tri]
    ring
  have hF2 : ∀ c₀ : ℝ, ∑ x, envF2 G i j c₀ x * mp G αi i x
      = αi + wα G αi i * (1 + tri G i j * c₀ + (uniq G i j).card) := by
    intro c₀
    rw [sum_mul_mp, envF2_self, envF2_sum hij]
    simp only [wα, tri]
    ring
  have hG2 : ∀ c₀ : ℝ, ∑ y, envG2 G i j c₀ y * mp G αj j y
      = αj + wα G αj j * (1 + tri G i j * c₀ + (uniq G j i).card) := by
    intro c₀
    rw [sum_mul_mp, envG2_self, envG2_sum hij]
    simp only [wα, tri]
    ring
  -- the identities behind `U^env`
  have hb := two_min_add_parts αi (wα G αj j)
  have hb' := two_min_add_parts αj (wα G αi i)
  have hab := two_min_add_abs (wα G αi i) (wα G αj j)
  have hmUU := mUU_ge (G := G) (i := i) (j := j) hwi hwj
  have hs0 : 0 ≤ min ((xi G i j).card * wα G αi i) ((xi G j i).card * wα G αj j) :=
    le_min (mul_nonneg (Nat.cast_nonneg _) hwi.le) (mul_nonneg (Nat.cast_nonneg _) hwj.le)
  have hcov_i : CoversCross G i j (xi G i j) := fun x hx y hy hxy =>
    Or.inl (mem_xi.2 ⟨hx, y, hy, hxy⟩)
  unfold Uenv
  rcases le_total ((tri G i j : ℝ) * |wα G αi i - wα G αj j|)
      ((uniq G i j).card * wα G αi i + (uniq G j i).card * wα G αj j) with hT | hT
  · -- `m^{(α)}_△ = △ |w_i − w_j|`: the cover potentials, with `K = ξ_i` or `K = ξ_j`
    rw [min_eq_left hT]
    have htt : 2 * (tri G i j : ℝ) * min (wα G αi i) (wα G αj j)
        + tri G i j * |wα G αi i - wα G αj j| = tri G i j * (wα G αi i + wα G αj j) := by
      linear_combination (tri G i j : ℝ) * hab
    rcases le_total ((xi G i j).card * wα G αi i) ((xi G j i).card * wα G αj j) with hs | hs
    · have h := bound1 (xi G i j) hcov_i
      have e1 : (((uniq G i j).filter (· ∈ xi G i j)).card : ℝ) = (xi G i j).card := by
        exact_mod_cast card_filter_xi_right (G := G) (i := j) (j := i)
      have e2 : (((uniq G j i).filter (· ∈ xi G i j)).card : ℝ) = 0 := by
        exact_mod_cast card_filter_xi_left (G := G) (i := j) (j := i)
      rw [hF, hG, e1, e2] at h
      rw [min_eq_left hs] at hmUU
      linarith
    · have h := bound1 (xi G j i) coversCross_xi
      have e1 : (((uniq G i j).filter (· ∈ xi G j i)).card : ℝ) = 0 := by
        exact_mod_cast card_filter_xi_left (G := G) (i := i) (j := j)
      have e2 : (((uniq G j i).filter (· ∈ xi G j i)).card : ℝ) = (xi G j i).card := by
        exact_mod_cast card_filter_xi_right (G := G) (i := i) (j := j)
      rw [hF, hG, e1, e2] at h
      rw [min_eq_right hs] at hmUU
      linarith
  · -- `m^{(α)}_△ = |U_i| w_i + |U_j| w_j`: the potentials `c₀` on `C`, on the lighter side
    rw [min_eq_right hT]
    have hmUU0 := hs0.trans hmUU
    rcases le_total (wα G αj j) (wα G αi i) with hw | hw
    · have h := bound2 2 (Or.inr rfl)
      rw [hF2, hG2] at h
      rw [min_eq_right hw]
      linarith
    · have h := bound2 0 (Or.inl rfl)
      rw [hF2, hG2] at h
      rw [min_eq_left hw]
      linarith

/-- **Proposition B.1, lazy case**: `U^lazy ≤ U^env` at `α_u = w_u`, the endpoint term of
`U^lazy` being `Δ_α` instead of `2 Δ_α` and its cross-edge term using the matching number. -/
theorem Ulazy_le_Uenv (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) :
    Ulazy G i j ≤ Uenv G i j (w G i) (w G j) := by
  have hwa_i : wα G (w G i) i = w G i := lazy_nbr_weight hij
  have hwa_j : wα G (w G j) j = w G j := lazy_nbr_weight hij.symm
  have hwle : w G j ≤ w G i := w_anti hle
  have hwi : 0 < w G i := w_pos i
  have hwj : 0 < w G j := w_pos j
  have hb := two_min_add_parts (w G i) (w G j)
  have hb' := two_min_add_parts (w G j) (w G i)
  have hmin : min (w G i) (w G j) = w G j := min_eq_right hwle
  have habs : |w G i - w G j| = w G i - w G j := abs_of_nonneg (by linarith)
  have hmUU := mUU_ge (G := G) (i := i) (j := j) hwi hwj
  have hm : (matchNum G i j : ℝ) * w G i ≤ (xi G i j).card * w G i :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast matchNum_le_xi) hwi.le
  have hmUU' : min ((matchNum G i j : ℝ) * w G i) ((xi G j i).card * w G j)
      ≤ min (min ((uniq G i j).card * w G i) ((uniq G j i).card * w G j))
          (Xi G i j / (1 / w G i + 1 / w G j)) :=
    (min_le_min hm le_rfl).trans hmUU
  have hLi := lazy_identity (G := G) hij
  have hLj := lazy_identity (G := G) hij.symm
  have htri : (tri G j i : ℝ) = tri G i j := by rw [tri_comm]
  rw [htri] at hLj
  have h0 : 0 ≤ ((uniq G i j).card : ℝ) * w G i := mul_nonneg (Nat.cast_nonneg _) hwi.le
  have hT : (tri G i j : ℝ) * (w G i - w G j)
      ≤ (uniq G i j).card * w G i + (uniq G j i).card * w G j := by
    linarith
  unfold Uenv Ulazy
  rw [hwa_i, hwa_j, hmin, habs, min_eq_left hT]
  linarith [hb, hb', hmin, hmUU', hwle]

end OllivierBF
