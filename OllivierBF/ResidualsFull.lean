/-
  Lemma 4.1 of the paper in full.

  * `residuals_full_paper`, for every one-step measure: the residual vanishes outside `N[i] ∪ N[j]`,
    has no demand on `U_i` and no supply on `U_j`; two vertices of `N[i] ∪ N[j]` are within
    distance `2` unless one lies in `U_i` and the other in `U_j`; and a pair of `U_i × U_j` is at
    distance `1` if it is a cross edge, `2` if it is not but has a common neighbour, and `3`
    otherwise, along `x, i, j, y` (`dist_cross_cases`, which uses `ThreeApart`).
  * `lazy_residuals_paper`, for the lazy measure `m_u`, uniform on `N[u]` with mass
    `w_u = 1/(d_u + 1)` (`lazyM`, a one-step measure), and `d_i ≤ d_j`: `r = Δ` on `S`, `r = w_i` on
    `U_i`, `r = −w_j` on `U_j`, and `τ = 1 − (2 + t) w_j`.

  The part of the lemma that the other results use is `residuals_paper` (`PaperTQ`).
-/
module

public import OllivierBF.TQ

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The lazy weight `w_u = 1/(d_u + 1)`. -/
noncomputable def lazyW (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : ℝ :=
  1 / ((G.degree u : ℝ) + 1)

/-- The lazy measure `m_u` of Section 3: uniform on `N[u]`, with mass `w_u` on each vertex. -/
noncomputable def lazyM (G : SimpleGraph V) [DecidableRel G.Adj] (u k : V) : ℝ :=
  if k = u ∨ G.Adj u k then lazyW G u else 0

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ}
variable {μ : V → V → ℝ} {i j : V}

/-! ### Where the measures and the residuals live -/

/-- A vertex with positive mass under `μ_u` lies in `N[u]`. -/
lemma mem_closed_of_mu_pos {u x : V} (hu : OneStepAt G μ u) (hx : 0 < μ u x) :
    x = u ∨ G.Adj u x := by
  by_contra h
  have h' := not_or.mp h
  have h0 := hu.supp x h'.1 h'.2
  linarith

/-- A vertex of `N[i] ∩ N[j]` lies in `S = {i, j} ∪ C`. -/
lemma mem_overlap_of_closed {k : V} (hki : k = i ∨ G.Adj i k) (hkj : k = j ∨ G.Adj j k) :
    k ∈ overlap G i j := by
  simp only [overlap, Finset.mem_insert]
  rcases hki with h | h
  · exact Or.inl h
  rcases hkj with h' | h'
  · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr (mem_common.2 ⟨h, h'⟩))

/-- A vertex of `S` lies in `N[i] ∩ N[j]`. -/
lemma closed_of_mem_overlap (hij : G.Adj i j) {k : V} (hk : k ∈ overlap G i j) :
    (k = i ∨ G.Adj i k) ∧ (k = j ∨ G.Adj j k) := by
  simp only [overlap, Finset.mem_insert] at hk
  rcases hk with h | h | h
  · refine ⟨Or.inl h, Or.inr ?_⟩
    rw [h]
    exact hij.symm
  · refine ⟨Or.inr ?_, Or.inl h⟩
    rw [h]
    exact hij
  · exact ⟨Or.inr (mem_common.mp h).1, Or.inr (mem_common.mp h).2⟩

/-- A vertex with positive mass under both `μ_i` and `μ_j` lies in `S`. -/
lemma mem_overlap_of_min_pos (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {z : V}
    (hz : 0 < min (μ i z) (μ j z)) : z ∈ overlap G i j :=
  mem_overlap_of_closed (mem_closed_of_mu_pos hi (lt_of_lt_of_le hz (min_le_left _ _)))
    (mem_closed_of_mu_pos hj (lt_of_lt_of_le hz (min_le_right _ _)))

/-- **Lemma 4.1 (support).** The residual vanishes outside `N[i] ∪ N[j]`. -/
lemma resid_eq_zero_outside (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {x : V}
    (hxi : x ≠ i) (hix : ¬ G.Adj i x) (hxj : x ≠ j) (hjx : ¬ G.Adj j x) :
    resP μ i j x = 0 ∧ resN μ i j x = 0 := by
  have h1 : μ i x = 0 := hi.supp x hxi hix
  have h2 : μ j x = 0 := hj.supp x hxj hjx
  unfold resP resN
  rw [h1, h2]
  simp

/-! ### Distances between the neighbourhoods -/

/-- **Lemma 4.1 (distances).** Two vertices of `N[i] ∪ N[j]` are within distance `2`, unless one lies
in `U_i` and the other in `U_j`. -/
theorem dist_le_two_of_closed (hd : GraphMetric G d) (hij : G.Adj i j) {x y : V}
    (hx : (x = i ∨ G.Adj i x) ∨ (x = j ∨ G.Adj j x))
    (hy : (y = i ∨ G.Adj i y) ∨ (y = j ∨ G.Adj j y))
    (hxy : ¬ (x ∈ uniq G i j ∧ y ∈ uniq G j i)) (hyx : ¬ (y ∈ uniq G i j ∧ x ∈ uniq G j i)) :
    d x y ≤ 2 := by
  -- two vertices of one closed neighbourhood
  have via : ∀ u, (x = u ∨ G.Adj u x) → (y = u ∨ G.Adj u y) → d x y ≤ 2 := by
    intro u h1 h2
    have hux := d_le_one_of hd h1
    have huy := d_le_one_of hd h2
    have t := hd.tri x u y
    rw [hd.symm x u] at t
    linarith
  -- for an edge `(u, v)`, a vertex of `N[u]` outside `N[v]` is a unique neighbour of `u`
  have hU : ∀ {u v w : V}, G.Adj u v → (w = u ∨ G.Adj u w) → ¬ (w = v ∨ G.Adj v w) →
      w ∈ uniq G u v := by
    intro u v w huv h1 h2
    rw [mem_uniq]
    refine ⟨fun h => h2 (Or.inl h), ?_, fun h => h2 (Or.inr h)⟩
    rcases h1 with h | h
    · exact (h2 (Or.inr (by rw [h]; exact huv.symm))).elim
    · exact h
  by_cases hxi : x = i ∨ G.Adj i x
  · by_cases hyi : y = i ∨ G.Adj i y
    · exact via i hxi hyi
    · have hyj : y = j ∨ G.Adj j y := hy.resolve_left hyi
      by_cases hxj : x = j ∨ G.Adj j x
      · exact via j hxj hyj
      · exact (hxy ⟨hU hij hxi hxj, hU hij.symm hyj hyi⟩).elim
  · have hxj : x = j ∨ G.Adj j x := hx.resolve_left hxi
    by_cases hyj : y = j ∨ G.Adj j y
    · exact via j hxj hyj
    · have hyi : y = i ∨ G.Adj i y := hy.resolve_right hyj
      exact (hyx ⟨hU hij hyi hyj, hU hij.symm hxj hxi⟩).elim

/-- **Lemma 4.1 (distances in `U_i × U_j`).** A pair of `U_i × U_j` is at distance `1` if it is a
cross edge, at distance `2` if it is not but has a common neighbour, and at distance `3` otherwise,
along the path `x, i, j, y`. -/
theorem dist_cross_cases (hd : GraphMetric G d) (h3 : ThreeApart G d) (hij : G.Adj i j)
    {x y : V} (hx : x ∈ uniq G i j) (hy : y ∈ uniq G j i) :
    (G.Adj x y → d x y = 1) ∧ (¬ G.Adj x y → (∃ w, G.Adj x w ∧ G.Adj w y) → d x y = 2) ∧
      (¬ G.Adj x y → (¬ ∃ w, G.Adj x w ∧ G.Adj w y) → d x y = 3) := by
  have hxy : x ≠ y := by
    rintro rfl
    exact (mem_uniq.mp hy).2.2 (mem_uniq.mp hx).2.1
  refine ⟨fun h => hd.adj h, fun hna hw => ?_, fun hna hno => ?_⟩
  · obtain ⟨w, hxw, hwy⟩ := hw
    exact le_antisymm (hd.le_two hxw hwy) (hd.two_le hxy hna)
  · refine le_antisymm ?_ (h3 x y hxy hna fun w hw => hno ⟨w, hw⟩)
    exact hd.le_three (mem_uniq.mp hx).2.1.symm hij (mem_uniq.mp hy).2.1

/-- **Lemma 4.1**, for every one-step measure, as the paper states it: the residual vanishes outside
`N[i] ∪ N[j]`, is nonnegative on `U_i` (no demand) and nonpositive on `U_j` (no supply); two vertices
of `N[i] ∪ N[j]` are within distance `2` unless one is in `U_i` and the other in `U_j`; and a pair of
`U_i × U_j` is at distance `1`, `2` or `3` as it is a cross edge, has a common neighbour, or neither. -/
theorem residuals_full_paper (hd : GraphMetric G d) (h3 : ThreeApart G d) (hij : G.Adj i j)
    (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) :
    (∀ x, x ≠ i → ¬ G.Adj i x → x ≠ j → ¬ G.Adj j x → resP μ i j x = 0 ∧ resN μ i j x = 0) ∧
    (∀ x ∈ uniq G i j, resN μ i j x = 0) ∧ (∀ y ∈ uniq G j i, resP μ i j y = 0) ∧
    (∀ x y, ((x = i ∨ G.Adj i x) ∨ (x = j ∨ G.Adj j x)) →
      ((y = i ∨ G.Adj i y) ∨ (y = j ∨ G.Adj j y)) →
      ¬ (x ∈ uniq G i j ∧ y ∈ uniq G j i) → ¬ (y ∈ uniq G i j ∧ x ∈ uniq G j i) → d x y ≤ 2) ∧
    (∀ x ∈ uniq G i j, ∀ y ∈ uniq G j i,
      (G.Adj x y → d x y = 1) ∧ (¬ G.Adj x y → (∃ w, G.Adj x w ∧ G.Adj w y) → d x y = 2) ∧
        (¬ G.Adj x y → (¬ ∃ w, G.Adj x w ∧ G.Adj w y) → d x y = 3)) :=
  ⟨fun _ hxi hix hxj hjx => resid_eq_zero_outside hi hj hxi hix hxj hjx,
    fun _ hx => resN_eq_zero_of_uniq hi hj hx, fun _ hy => resP_eq_zero_of_uniq hi hj hy,
    fun _ _ hx hy hxy hyx => dist_le_two_of_closed hd hij hx hy hxy hyx,
    fun _ hx _ hy => dist_cross_cases hd h3 hij hx hy⟩

/-! ### The lazy measure -/

lemma lazyW_pos (u : V) : 0 < lazyW G u := by
  unfold lazyW
  positivity

/-- `w_v ≤ w_u` when `d_u ≤ d_v`. -/
lemma lazyW_anti {u v : V} (h : G.degree u ≤ G.degree v) : lazyW G v ≤ lazyW G u := by
  unfold lazyW
  have h' : (G.degree u : ℝ) ≤ G.degree v := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ G.degree u := by positivity
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma lazyM_nonneg (u k : V) : 0 ≤ lazyM G u k := by
  unfold lazyM
  split_ifs
  · exact (lazyW_pos u).le
  · exact le_rfl

/-- The lazy measure has mass `(d_u + 1) w_u = 1`. -/
lemma lazyM_sum (u : V) : ∑ k, lazyM G u k = 1 := by
  have hsplit : ∀ k, lazyM G u k =
      (if k = u then lazyW G u else 0) + (if G.Adj u k then lazyW G u else 0) := by
    intro k
    unfold lazyM
    by_cases h1 : k = u
    · have h2 : ¬ G.Adj u k := by
        rw [h1]
        exact G.irrefl
      rw [ite_eq_left (Or.inl h1 : k = u ∨ G.Adj u k), ite_eq_left h1, ite_eq_right h2, add_zero]
    · by_cases h2 : G.Adj u k
      · rw [ite_eq_left (Or.inr h2 : k = u ∨ G.Adj u k), ite_eq_right h1, ite_eq_left h2,
          zero_add]
      · rw [ite_eq_right (not_or.mpr ⟨h1, h2⟩), ite_eq_right h1, ite_eq_right h2, add_zero]
  rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_univ u), ← Finset.sum_filter, ← SimpleGraph.neighborFinset_eq_filter,
    Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  have h : (G.degree u : ℝ) + 1 ≠ 0 := by positivity
  rw [show lazyW G u + (G.degree u : ℝ) * lazyW G u
      = 1 / ((G.degree u : ℝ) + 1) * ((G.degree u : ℝ) + 1) by unfold lazyW; ring]
  exact div_mul_cancel₀ (1 : ℝ) h

/-- The lazy measure is a one-step measure. -/
lemma lazyM_oneStep (u : V) : OneStepAt G (lazyM G) u where
  nonneg k := lazyM_nonneg u k
  mass := lazyM_sum u
  supp k hk hadj := by
    unfold lazyM
    rw [ite_eq_right (not_or.mpr ⟨hk, hadj⟩)]

/-- For `d_i ≤ d_j`, the mass that `m_i` and `m_j` share is `w_j` on `S` and nothing elsewhere. -/
lemma lazyM_min (hij : G.Adj i j) (hle : G.degree i ≤ G.degree j) (k : V) :
    min (lazyM G i k) (lazyM G j k) = if k ∈ overlap G i j then lazyW G j else 0 := by
  by_cases hk : k ∈ overlap G i j
  · rw [ite_eq_left hk]
    obtain ⟨hki, hkj⟩ := closed_of_mem_overlap hij hk
    unfold lazyM
    rw [ite_eq_left hki, ite_eq_left hkj]
    exact min_eq_right (lazyW_anti hle)
  · rw [ite_eq_right hk]
    by_cases hki : k = i ∨ G.Adj i k
    · have hkj : ¬ (k = j ∨ G.Adj j k) := fun hkj => hk (mem_overlap_of_closed hki hkj)
      have h0 : lazyM G j k = 0 := by
        unfold lazyM
        rw [ite_eq_right hkj]
      rw [h0]
      exact min_eq_right (lazyM_nonneg i k)
    · have h0 : lazyM G i k = 0 := by
        unfold lazyM
        rw [ite_eq_right hki]
      rw [h0]
      exact min_eq_left (lazyM_nonneg j k)

/-- `|S| = 2 + t`. -/
lemma card_overlap_eq (hij : G.Adj i j) :
    ((overlap G i j).card : ℝ) = 2 + (common G i j).card := by
  have hi : i ∉ insert j (common G i j) := by
    simp [mem_common, hij.ne, SimpleGraph.irrefl]
  have hj : j ∉ common G i j := by simp [mem_common, SimpleGraph.irrefl]
  simp only [overlap, Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hj]
  push_cast
  ring

/-- **Lemma 4.1, the lazy measure.** The lazy measures are one-step measures, and for `d_i ≤ d_j`
the residual `r = m_i − m_j` is `Δ = w_i − w_j` on `S`, `w_i` on `U_i` and `−w_j` on `U_j`, with
mass `τ = 1 − (2 + t) w_j`. -/
theorem lazy_residuals_paper (hij : G.Adj i j) (hle : G.degree i ≤ G.degree j) :
    (∀ u, OneStepAt G (lazyM G) u) ∧
    (∀ k ∈ overlap G i j, lazyM G i k - lazyM G j k = lazyW G i - lazyW G j) ∧
    (∀ k ∈ uniq G i j, lazyM G i k - lazyM G j k = lazyW G i) ∧
    (∀ k ∈ uniq G j i, lazyM G i k - lazyM G j k = - lazyW G j) ∧
    resMass (lazyM G) i j = 1 - (2 + ((common G i j).card : ℝ)) * lazyW G j := by
  refine ⟨lazyM_oneStep, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, ?_⟩
  · obtain ⟨hki, hkj⟩ := closed_of_mem_overlap hij hk
    unfold lazyM
    rw [ite_eq_left hki, ite_eq_left hkj]
  · obtain ⟨hkj, hik, hjk⟩ := mem_uniq.mp hk
    unfold lazyM
    rw [ite_eq_left (Or.inr hik : k = i ∨ G.Adj i k), ite_eq_right (not_or.mpr ⟨hkj, hjk⟩),
      sub_zero]
  · obtain ⟨hki, hjk, hik⟩ := mem_uniq.mp hk
    unfold lazyM
    rw [ite_eq_right (not_or.mpr ⟨hki, hik⟩), ite_eq_left (Or.inr hjk : k = j ∨ G.Adj j k),
      zero_sub]
  · unfold resMass resP
    rw [Finset.sum_sub_distrib, lazyM_sum i, Finset.sum_congr rfl fun k _ => lazyM_min hij hle k,
      Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, card_overlap_eq hij]

end OllivierBF
