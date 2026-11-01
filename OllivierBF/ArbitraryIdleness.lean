/-
  Proposition B.1 of the paper: the envelope `U^env_{ij}` for arbitrary idleness `α_i, α_j ∈ [0, 1)`,
  and `U^lazy_{ij} ≤ U^env_{ij}` for the lazy measure.

  The proof takes a different route from the paper. It uses weak duality (`cost_ge_potential`)
  with two pairs of explicit 1-Lipschitz potentials, one pair for each branch of the minimum that
  defines `m̃^CU_{ij}` (`mCUenv`), so it needs no coupling that saturates the diagonal:
  * `commonPot`, equal to `1 ± 1` on the common neighbours and `1` elsewhere, gives
    `t_{ij} |w_i − w_j| ≤ W₁`;
  * `envPot K`, equal to `2` on `U_i \ K`, `0` on `U_j \ K`, and `1` elsewhere, for the vertex
    covers `K = ξ_i` and `K = ξ_j` of the cross-edge graph, gives
    `|U_i| w_i + |U_j| w_j − |ξ_i| w_i ≤ W₁` and `|U_i| w_i + |U_j| w_j − |ξ_j| w_j ≤ W₁`.
  Here `w_u = (1 − α_u)/d_u` (`nbrW`) is the mass that `m_u = mp G α_u u` puts on each neighbour
  of `u`. Nothing in this file takes a published result as a hypothesis.
-/
module

public import OllivierBF.Paper

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ} {i j : V}

/-! ### Definitions -/

/-- `w_u = (1 − α)/d_u`, the mass that `mp G α u` puts on each neighbour of `u`. -/
noncomputable def nbrW (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (u : V) : ℝ :=
  (1 - α) / ρ G u

/-- `m̃^UU_{ij} = min{|U_i| w_i, |U_j| w_j, Ξ_{ij}/(1/w_i + 1/w_j)}` of Proposition B.1. -/
noncomputable def mUUenv (G : SimpleGraph V) [DecidableRel G.Adj] (αi αj : ℝ) (i j : V) : ℝ :=
  min (min ((uniq G i j).card * nbrW G αi i) ((uniq G j i).card * nbrW G αj j))
    ((Xi G i j : ℝ) / (1 / nbrW G αi i + 1 / nbrW G αj j))

/-- `m̃^CU_{ij} = min{t_{ij} |w_i − w_j|, |U_i| w_i + |U_j| w_j}` of Proposition B.1. -/
noncomputable def mCUenv (G : SimpleGraph V) [DecidableRel G.Adj] (αi αj : ℝ) (i j : V) : ℝ :=
  min (tri G i j * |nbrW G αi i - nbrW G αj j|)
    ((uniq G i j).card * nbrW G αi i + (uniq G j i).card * nbrW G αj j)

/-- `U^env_{ij}` of Proposition B.1, with `z_i = min{α_i, w_j}`, `r_i = [α_i − w_j]₊`,
`r̄_i = [w_j − α_i]₊`, the same at `j`, and `w_min = min{w_i, w_j}` written out. -/
noncomputable def Uenv (G : SimpleGraph V) [DecidableRel G.Adj] (αi αj : ℝ) (i j : V) : ℝ :=
  -1 + 2 * (min αi (nbrW G αj j) + min αj (nbrW G αi i))
    + (max (αi - nbrW G αj j) 0 + max (nbrW G αj j - αi) 0
      + max (αj - nbrW G αi i) 0 + max (nbrW G αi i - αj) 0)
    + 2 * tri G i j * min (nbrW G αi i) (nbrW G αj j)
    + mUUenv G αi αj i j + mCUenv G αi αj i j

/-- `1 + s` on the common neighbours and `1` elsewhere. -/
noncomputable def commonPot (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (s : ℝ)
    (x : V) : ℝ :=
  if x ∈ common G i j then 1 + s else 1

/-- `2` on `U_i \ K`, `0` on `U_j \ K`, and `1` elsewhere (the endpoints included). -/
noncomputable def envPot (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (K : Finset V)
    (x : V) : ℝ :=
  if x ∈ uniq G i j ∧ x ∉ K then 2 else if x ∈ uniq G j i ∧ x ∉ K then 0 else 1

/-! ### Real-number facts -/

/-- `2 min{x, y} + [x − y]₊ + [y − x]₊ = x + y`. -/
lemma two_min_add_max_add_max (x y : ℝ) :
    2 * min x y + max (x - y) 0 + max (y - x) 0 = x + y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_right (show x - y ≤ 0 by linarith),
      max_eq_left (show (0 : ℝ) ≤ y - x by linarith)]
    ring
  · rw [min_eq_right h, max_eq_left (show (0 : ℝ) ≤ x - y by linarith),
      max_eq_right (show y - x ≤ 0 by linarith)]
    ring

/-- `2 min{x, y} = x + y − |x − y|`. -/
lemma two_min_eq (x y : ℝ) : 2 * min x y = x + y - |x - y| := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (show x - y ≤ 0 by linarith)]; ring
  · rw [min_eq_right h, abs_of_nonneg (show (0 : ℝ) ≤ x - y by linarith)]; ring

/-- The harmonic bound `min{x p, y q} ≤ (x + y)/(1/p + 1/q)` for `p, q > 0`. -/
lemma min_mul_le_harmonic {x y p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    min (x * p) (y * q) ≤ (x + y) / (1 / p + 1 / q) := by
  have hsig : 0 < 1 / p + 1 / q := add_pos (one_div_pos.2 hp) (one_div_pos.2 hq)
  have hm1 := min_le_left (x * p) (y * q)
  have hm2 := min_le_right (x * p) (y * q)
  rw [le_div_iff₀ hsig]
  have e1 : min (x * p) (y * q) * (1 / p) ≤ x := by rw [mul_one_div, div_le_iff₀ hp]; exact hm1
  have e2 : min (x * p) (y * q) * (1 / q) ≤ y := by rw [mul_one_div, div_le_iff₀ hq]; exact hm2
  rw [mul_add]
  linarith

/-! ### Sums against the measures -/

/-- `Σ_x f(x) m_u^p(x) = p f(u) + w Σ_{x ∈ N(u)} f(x)` with `w = (1 − p)/d_u`. -/
lemma sum_mul_mp (f : V → ℝ) (p : ℝ) (u : V) :
    ∑ x, f x * mp G p u x = p * f u + nbrW G p u * ∑ x ∈ G.neighborFinset u, f x := by
  have hsplit : ∀ x, f x * mp G p u x =
      (if x = u then f u * p else 0) + (if G.Adj u x then f x * ((1 - p) / ρ G u) else 0) := by
    intro x
    by_cases h1 : x = u
    · subst h1; simp [mp, SimpleGraph.irrefl]
    · by_cases h2 : G.Adj u x
      · simp [mp, h1, h2]
      · simp [mp, h1, h2]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_filter, ← SimpleGraph.neighborFinset_eq_filter, ← Finset.sum_mul]
  unfold nbrW
  ring

/-- `w_u d_u = 1 − α` at an edge endpoint. -/
lemma nbrW_mul_ρ {u v : V} (huv : G.Adj u v) (α : ℝ) : nbrW G α u * ρ G u = 1 - α := by
  unfold nbrW
  exact div_mul_cancel₀ _ (ρ_pos huv).ne'

/-- Couplings of `mp G αi i` and `mp G αj j` exist. -/
lemma exists_coupling_mp (hij : G.Adj i j) {αi αj : ℝ} (hαi0 : 0 ≤ αi) (hαi1 : αi ≤ 1)
    (hαj0 : 0 ≤ αj) (hαj1 : αj ≤ 1) : ∃ π, IsCoupling (mp G αi i) (mp G αj j) π :=
  exists_coupling_prob (mp_nonneg hαi0 hαi1 i) (mp_nonneg hαj0 hαj1 j)
    (mp_sum hij) (mp_sum hij.symm)

lemma not_mem_common_of_uniq {x : V} (h : x ∈ uniq G i j) : x ∉ common G i j :=
  fun hc => (mem_uniq.1 h).2.2 (mem_common.1 hc).2

lemma not_mem_common_of_uniq' {x : V} (h : x ∈ uniq G j i) : x ∉ common G i j :=
  fun hc => (mem_uniq.1 h).2.2 (mem_common.1 hc).1

/-! ### The potential `commonPot` -/

lemma commonPot_lip (hd : GraphMetric G d) {s : ℝ} (hs1 : s ≤ 1) (hs2 : -1 ≤ s) (x y : V) :
    commonPot G i j s x - commonPot G i j s y ≤ d x y := by
  by_cases hxy : x = y
  · subst hxy; rw [hd.self]; simp
  have h1 := hd.one_le hxy
  unfold commonPot
  split_ifs <;> linarith

lemma commonPot_of_not_mem {s : ℝ} {x : V} (h : x ∉ common G i j) : commonPot G i j s x = 1 := by
  unfold commonPot
  rw [if_neg h]

lemma commonPot_left (s : ℝ) : commonPot G i j s i = 1 :=
  commonPot_of_not_mem (fun h => G.irrefl (mem_common.1 h).1)

lemma commonPot_right (s : ℝ) : commonPot G i j s j = 1 :=
  commonPot_of_not_mem (fun h => G.irrefl (mem_common.1 h).2)

lemma commonPot_sum_common (s : ℝ) :
    ∑ x ∈ common G i j, commonPot G i j s x = tri G i j * (1 + s) := by
  rw [Finset.sum_congr rfl fun x hx =>
      (show commonPot G i j s x = 1 + s by unfold commonPot; rw [if_pos hx]),
    Finset.sum_const, nsmul_eq_mul]
  simp only [tri]

lemma commonPot_sum_of_disjoint (s : ℝ) {A : Finset V} (hA : ∀ x ∈ A, x ∉ common G i j) :
    ∑ x ∈ A, commonPot G i j s x = A.card := by
  rw [Finset.sum_congr rfl fun x hx => commonPot_of_not_mem (s := s) (hA x hx),
    Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The first pair of potentials**: `s t_{ij} (w_i − w_j) ≤ W₁` for `s = ±1`. -/
theorem W1_ge_commonPot (hd : GraphMetric G d) (hij : G.Adj i j) {αi αj : ℝ}
    (hαi0 : 0 ≤ αi) (hαi1 : αi ≤ 1) (hαj0 : 0 ≤ αj) (hαj1 : αj ≤ 1) {s : ℝ}
    (hs1 : s ≤ 1) (hs2 : -1 ≤ s) :
    s * (tri G i j * (nbrW G αi i - nbrW G αj j)) ≤ W1 d (mp G αi i) (mp G αj j) := by
  have hmi := nbrW_mul_ρ hij αi
  have hmj := nbrW_mul_ρ hij.symm αj
  have hUi : ((uniq G i j).card : ℝ) = ρ G i - 1 - tri G i j := card_uniq_real hij
  have hUj : ((uniq G j i).card : ℝ) = ρ G j - 1 - tri G i j := by
    rw [card_uniq_real hij.symm, tri_comm j i]
  have hsum : ∑ x, commonPot G i j s x * mp G αi i x - ∑ x, commonPot G i j s x * mp G αj j x
      = s * (tri G i j * (nbrW G αi i - nbrW G αj j)) := by
    rw [sum_mul_mp (commonPot G i j s), sum_mul_mp (commonPot G i j s),
      sum_nbr_split hij (commonPot G i j s), sum_nbr_split hij.symm (commonPot G i j s),
      common_comm j i, commonPot_left, commonPot_right, commonPot_sum_common,
      commonPot_sum_of_disjoint s (A := uniq G i j) (fun x hx => not_mem_common_of_uniq hx),
      commonPot_sum_of_disjoint s (A := uniq G j i) (fun x hx => not_mem_common_of_uniq' hx)]
    linear_combination hmi + nbrW G αi i * hUi - hmj - nbrW G αj j * hUj
  apply le_W1 (exists_coupling_mp hij hαi0 hαi1 hαj0 hαj1)
  intro π hπ
  have hval := cost_ge_potential (commonPot G i j s) (commonPot_lip hd hs1 hs2) hπ
  linarith

/-! ### The potential `envPot` -/

lemma envPot_lip (hd : GraphMetric G d) {K : Finset V} (hK : CoversCross G i j K) (x y : V) :
    envPot G i j K x - envPot G i j K y ≤ d x y := by
  by_cases hxy : x = y
  · subst hxy; rw [hd.self]; simp
  have h1 := hd.one_le hxy
  have hx2 : envPot G i j K x ≤ 2 := by unfold envPot; split_ifs <;> norm_num
  have hy0 : 0 ≤ envPot G i j K y := by unfold envPot; split_ifs <;> norm_num
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
    · have hy1 : 1 ≤ envPot G i j K y := by
        unfold envPot
        rw [if_neg hY]
        split_ifs <;> norm_num
      linarith
  · have hx1 : envPot G i j K x ≤ 1 := by
      unfold envPot
      rw [if_neg hX]
      split_ifs <;> norm_num
    linarith

lemma envPot_of_not_mem {K : Finset V} {x : V} (h1 : x ∉ uniq G i j) (h2 : x ∉ uniq G j i) :
    envPot G i j K x = 1 := by
  unfold envPot
  rw [if_neg (show ¬(x ∈ uniq G i j ∧ x ∉ K) from fun h => h1 h.1),
    if_neg (show ¬(x ∈ uniq G j i ∧ x ∉ K) from fun h => h2 h.1)]

lemma envPot_left (K : Finset V) : envPot G i j K i = 1 :=
  envPot_of_not_mem (fun h => G.irrefl (mem_uniq.1 h).2.1) (fun h => (mem_uniq.1 h).1 rfl)

lemma envPot_right (K : Finset V) : envPot G i j K j = 1 :=
  envPot_of_not_mem (fun h => (mem_uniq.1 h).1 rfl) (fun h => G.irrefl (mem_uniq.1 h).2.1)

lemma envPot_Ui {K : Finset V} {x : V} (hx : x ∈ uniq G i j) :
    envPot G i j K x = if x ∈ K then 1 else 2 := by
  have hxUj : x ∉ uniq G j i := uniq_not_mem_swap hx
  by_cases hK : x ∈ K <;> simp [envPot, hx, hxUj, hK]

lemma envPot_Uj {K : Finset V} {x : V} (hx : x ∈ uniq G j i) :
    envPot G i j K x = if x ∈ K then 1 else 0 := by
  have hxUi : x ∉ uniq G i j := uniq_not_mem_swap hx
  by_cases hK : x ∈ K <;> simp [envPot, hxUi, hx, hK]

lemma envPot_sum_Ui (K : Finset V) :
    ∑ x ∈ uniq G i j, envPot G i j K x
      = 2 * ((uniq G i j).card : ℝ) - (((uniq G i j).filter (· ∈ K)).card : ℝ) := by
  rw [Finset.sum_congr rfl fun x hx => envPot_Ui (K := K) hx]
  have h : ∀ x ∈ uniq G i j, (if x ∈ K then (1 : ℝ) else 2) = 2 - (if x ∈ K then 1 else 0) := by
    intro x _; split_ifs <;> norm_num
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_boole]
  ring

lemma envPot_sum_Uj (K : Finset V) :
    ∑ x ∈ uniq G j i, envPot G i j K x = (((uniq G j i).filter (· ∈ K)).card : ℝ) := by
  rw [Finset.sum_congr rfl fun x hx => envPot_Uj (K := K) hx, Finset.sum_boole]

lemma envPot_sum_common (K : Finset V) :
    ∑ x ∈ common G i j, envPot G i j K x = tri G i j := by
  rw [Finset.sum_congr rfl fun x hx => envPot_of_not_mem (K := K)
      (fun h => not_mem_common_of_uniq h hx) (fun h => not_mem_common_of_uniq' h hx),
    Finset.sum_const, nsmul_eq_mul, mul_one]
  simp only [tri]

/-- **The second pair of potentials**: for every vertex cover `K` of the cross-edge graph,
`w_i (|U_i| − |U_i ∩ K|) + w_j (|U_j| − |U_j ∩ K|) ≤ W₁`. -/
theorem W1_ge_envPot (hd : GraphMetric G d) (hij : G.Adj i j) {αi αj : ℝ}
    (hαi0 : 0 ≤ αi) (hαi1 : αi ≤ 1) (hαj0 : 0 ≤ αj) (hαj1 : αj ≤ 1)
    {K : Finset V} (hK : CoversCross G i j K) :
    nbrW G αi i * (((uniq G i j).card : ℝ) - ((uniq G i j).filter (· ∈ K)).card)
      + nbrW G αj j * (((uniq G j i).card : ℝ) - ((uniq G j i).filter (· ∈ K)).card)
      ≤ W1 d (mp G αi i) (mp G αj j) := by
  have hmi := nbrW_mul_ρ hij αi
  have hmj := nbrW_mul_ρ hij.symm αj
  have hUi : ((uniq G i j).card : ℝ) = ρ G i - 1 - tri G i j := card_uniq_real hij
  have hUj : ((uniq G j i).card : ℝ) = ρ G j - 1 - tri G i j := by
    rw [card_uniq_real hij.symm, tri_comm j i]
  have hsum : ∑ x, envPot G i j K x * mp G αi i x - ∑ x, envPot G i j K x * mp G αj j x
      = nbrW G αi i * (((uniq G i j).card : ℝ) - ((uniq G i j).filter (· ∈ K)).card)
        + nbrW G αj j * (((uniq G j i).card : ℝ) - ((uniq G j i).filter (· ∈ K)).card) := by
    rw [sum_mul_mp (envPot G i j K), sum_mul_mp (envPot G i j K),
      sum_nbr_split hij (envPot G i j K), sum_nbr_split hij.symm (envPot G i j K),
      common_comm j i, envPot_left, envPot_right, envPot_sum_common, envPot_sum_Ui,
      envPot_sum_Uj]
    linear_combination hmi + nbrW G αi i * hUi - hmj - nbrW G αj j * hUj
  apply le_W1 (exists_coupling_mp hij hαi0 hαi1 hαj0 hαj1)
  intro π hπ
  have hval := cost_ge_potential (envPot G i j K) (envPot_lip hd hK) hπ
  linarith

/-! ### The covers `ξ_i` and `ξ_j` -/

/-- `ξ_i` is a vertex cover of the cross-edge graph (`coversCross_xi` is the one for `ξ_j`). -/
lemma coversCross_xi_self : CoversCross G i j (xi G i j) := by
  intro x hx y hy hxy
  exact Or.inl (mem_xi.2 ⟨hx, y, hy, hxy⟩)

lemma card_filter_xi_self : ((uniq G i j).filter (· ∈ xi G i j)).card = (xi G i j).card := by
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨xi_subset i j h, h⟩⟩

lemma card_filter_xi_other : ((uniq G j i).filter (· ∈ xi G i j)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx hxi
  exact uniq_not_mem_swap hx (xi_subset i j hxi)

/-- `min{|ξ_i| w_i, |ξ_j| w_j} ≤ m̃^UU_{ij}`. -/
lemma min_xi_le_mUUenv {αi αj : ℝ} (hwi : 0 < nbrW G αi i) (hwj : 0 < nbrW G αj j) :
    min ((xi G i j).card * nbrW G αi i) ((xi G j i).card * nbrW G αj j)
      ≤ mUUenv G αi αj i j := by
  unfold mUUenv
  refine le_min (le_min ?_ ?_) ?_
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card (xi_subset i j)) hwi.le)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_le_card (xi_subset j i)) hwj.le)
  · have h := min_mul_le_harmonic (x := ((xi G i j).card : ℝ)) (y := ((xi G j i).card : ℝ))
      hwi hwj
    simp only [Xi]
    push_cast
    exact h

/-! ### Proposition B.1 -/

/-- **Proposition B.1**: for every edge and all idleness `α_i, α_j ∈ [0, 1)`,
`1 − W₁(m_i, m_j) ≤ U^env_{ij}`, where `m_u = mp G α_u u`. -/
theorem envelope_arbitrary_idleness (hd : GraphMetric G d) (hij : G.Adj i j) {αi αj : ℝ}
    (hαi0 : 0 ≤ αi) (hαi1 : αi < 1) (hαj0 : 0 ≤ αj) (hαj1 : αj < 1) :
    1 - W1 d (mp G αi i) (mp G αj j) ≤ Uenv G αi αj i j := by
  have hwi : 0 < nbrW G αi i := div_pos (by linarith) (ρ_pos hij)
  have hwj : 0 < nbrW G αj j := div_pos (by linarith) (ρ_pos hij.symm)
  have hmi := nbrW_mul_ρ hij αi
  have hmj := nbrW_mul_ρ hij.symm αj
  have hUi : ((uniq G i j).card : ℝ) = ρ G i - 1 - tri G i j := card_uniq_real hij
  have hUj : ((uniq G j i).card : ℝ) = ρ G j - 1 - tri G i j := by
    rw [card_uniq_real hij.symm, tri_comm j i]
  -- the three lower bounds on `W₁`
  have hB1 : tri G i j * |nbrW G αi i - nbrW G αj j| ≤ W1 d (mp G αi i) (mp G αj j) := by
    have h1 := W1_ge_commonPot hd hij hαi0 hαi1.le hαj0 hαj1.le (s := 1) le_rfl (by norm_num)
    have h2 := W1_ge_commonPot hd hij hαi0 hαi1.le hαj0 hαj1.le (s := -1) (by norm_num) le_rfl
    rcases le_total (nbrW G αj j) (nbrW G αi i) with h | h
    · rw [abs_of_nonneg (show (0 : ℝ) ≤ nbrW G αi i - nbrW G αj j by linarith)]
      linarith
    · rw [abs_of_nonpos (show nbrW G αi i - nbrW G αj j ≤ 0 by linarith)]
      linarith
  have hB2 := W1_ge_envPot hd hij hαi0 hαi1.le hαj0 hαj1.le
    (coversCross_xi_self (G := G) (i := i) (j := j))
  rw [card_filter_xi_self, card_filter_xi_other, Nat.cast_zero, sub_zero] at hB2
  have hB3 := W1_ge_envPot hd hij hαi0 hαi1.le hαj0 hαj1.le
    (coversCross_xi (G := G) (i := i) (j := j))
  rw [card_filter_xi_left, card_filter_xi_right, Nat.cast_zero, sub_zero] at hB3
  -- `m̃^UU_{ij} ≥ min{|ξ_i| w_i, |ξ_j| w_j} ≥ 0`
  have hUU := min_xi_le_mUUenv hwi hwj
  have hUU0 : 0 ≤ min (((xi G i j).card : ℝ) * nbrW G αi i) (((xi G j i).card : ℝ) * nbrW G αj j) :=
    le_min (mul_nonneg (Nat.cast_nonneg _) hwi.le) (mul_nonneg (Nat.cast_nonneg _) hwj.le)
  -- `1 − U^env = |U_i| w_i + |U_j| w_j + t |w_i − w_j| − m̃^UU − m̃^CU`
  have hF1 := two_min_add_max_add_max αi (nbrW G αj j)
  have hF2 := two_min_add_max_add_max αj (nbrW G αi i)
  have hF3 : 2 * tri G i j * min (nbrW G αi i) (nbrW G αj j)
      = tri G i j * (nbrW G αi i + nbrW G αj j - |nbrW G αi i - nbrW G αj j|) := by
    linear_combination (tri G i j : ℝ) * two_min_eq (nbrW G αi i) (nbrW G αj j)
  have hXi : ((uniq G i j).card : ℝ) * nbrW G αi i
      = 1 - αi - nbrW G αi i - tri G i j * nbrW G αi i := by
    linear_combination hmi + nbrW G αi i * hUi
  have hXj : ((uniq G j i).card : ℝ) * nbrW G αj j
      = 1 - αj - nbrW G αj j - tri G i j * nbrW G αj j := by
    linear_combination hmj + nbrW G αj j * hUj
  have key : 1 - Uenv G αi αj i j
      = ((uniq G i j).card * nbrW G αi i + (uniq G j i).card * nbrW G αj j)
        + tri G i j * |nbrW G αi i - nbrW G αj j| - mUUenv G αi αj i j - mCUenv G αi αj i j := by
    unfold Uenv
    linear_combination -hF1 - hF2 - hF3 - hXi - hXj
  have hCU : mCUenv G αi αj i j = min (tri G i j * |nbrW G αi i - nbrW G αj j|)
      ((uniq G i j).card * nbrW G αi i + (uniq G j i).card * nbrW G αj j) := rfl
  suffices h : 1 - Uenv G αi αj i j ≤ W1 d (mp G αi i) (mp G αj j) by linarith
  rw [key, hCU]
  rcases le_total (tri G i j * |nbrW G αi i - nbrW G αj j|)
      ((uniq G i j).card * nbrW G αi i + (uniq G j i).card * nbrW G αj j) with h | h
  · -- branch `m̃^CU = t |w_i − w_j|`: the pair `envPot ξ_i`, `envPot ξ_j`
    rw [min_eq_left h]
    rcases le_total (((xi G i j).card : ℝ) * nbrW G αi i) (((xi G j i).card : ℝ) * nbrW G αj j)
      with h' | h'
    · rw [min_eq_left h'] at hUU
      linarith
    · rw [min_eq_right h'] at hUU
      linarith
  · -- branch `m̃^CU = |U_i| w_i + |U_j| w_j`: the pair `commonPot (±1)`
    rw [min_eq_right h]
    linarith

/-- **Proposition B.1, the lazy measure**: with the endpoints labelled so that `d_i ≤ d_j`,
`U^lazy_{ij} ≤ U^env_{ij}` for `α_u = w_u = 1/(d_u + 1)`. -/
theorem Ulazy_le_Uenv (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) :
    Ulazy G i j ≤ Uenv G (w G i) (w G j) i j := by
  have hwi : nbrW G (w G i) i = w G i := lazy_nbr_weight hij
  have hwj : nbrW G (w G j) j = w G j := lazy_nbr_weight hij.symm
  have hw := w_anti (G := G) hle
  have hwip := w_pos (G := G) i
  have hwjp := w_pos (G := G) j
  have key := lazy_identity (G := G) hij
  have hρw : w G j * ρ G j = 1 - w G j := by
    have h := lazy_nbr_weight (G := G) hij.symm
    rw [div_eq_iff (ρ_pos hij.symm).ne'] at h
    linarith
  have hUjw : ((uniq G j i).card : ℝ) * w G j = 1 - (2 + tri G i j) * w G j := by
    rw [card_uniq_real hij.symm, tri_comm j i]
    linear_combination hρw
  have hUiw : 0 ≤ ((uniq G i j).card : ℝ) * w G i := mul_nonneg (Nat.cast_nonneg _) hwip.le
  have hX : tri G i j * (w G i - w G j)
      ≤ (uniq G i j).card * w G i + (uniq G j i).card * w G j := by
    linarith
  have hUU : min (matchNum G i j * w G i) ((xi G j i).card * w G j)
      ≤ mUUenv G (w G i) (w G j) i j := by
    have hp1 : 0 < nbrW G (w G i) i := by rw [hwi]; exact hwip
    have hp2 : 0 < nbrW G (w G j) j := by rw [hwj]; exact hwjp
    have h1 := min_xi_le_mUUenv hp1 hp2
    rw [hwi, hwj] at h1
    have hmx : (matchNum G i j : ℝ) ≤ (xi G i j).card := by exact_mod_cast matchNum_le_xi
    exact (min_le_min (mul_le_mul_of_nonneg_right hmx hwip.le) le_rfl).trans h1
  unfold Uenv mCUenv
  rw [hwi, hwj, min_eq_right hw, min_eq_left hw,
    max_eq_left (show (0 : ℝ) ≤ w G i - w G j by linarith),
    max_eq_right (show w G j - w G i ≤ 0 by linarith),
    abs_of_nonneg (show (0 : ℝ) ≤ w G i - w G j by linarith), min_eq_left hX]
  unfold Ulazy
  linarith

end OllivierBF
