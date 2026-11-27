/-
  Theorem 5.3 (iii) of the paper: the triangle–quadrangle bound brackets the attainable range of
  Theorem 5.2, `κ_TQ ≤ κ_*` and `κ̄* ≤ κ̄_TQ` (`tq_range_paper`).

  The ends of the range are `kappaF ∅` and `kappaMax`, `1 − W₁` with the charged distance, so the
  arguments of (i) and (ii) are run with the charged distance in place of the true one.

  * Lower end: a partial plan with charged distances at least `chargedDist ∅` gives
    `1 − 3τ + Σ (3 − c) π ≤ κ_*` (`tq_lower_le_kappaF_empty`, through `kappaF_eq_sigmaStar`). On the
    supports the true distance is at most `chargedDist ∅` (`dist_le_chargedDist_empty`), so the same
    plan satisfies the hypothesis of (i).
  * Upper end: for each admissible `F`, the charged distance is `1` on edges, at least `2` between
    other distinct vertices, and at least `3` from `X₃` to the demand outside `S` and from the supply
    outside `S` to `Y₃`; the counting of (ii) (`cost_ge_of_far`) then bounds `kappaF F`
    (`kappaF_le_tq_upper`), hence `kappaMax` (`kappaMax_le_tq_upper`).

  This needs `X₃` as the paper defines it from the local data (`IsFarXLocal`, which implies the
  `IsFarX` of (ii)). `IsFarX` allows a neighbour `w ∈ Z` of `x`, and an admissible `F` may pair `w`
  with a vertex `y` of `U_j`, which puts `x` and `y` at charged distance `2`. For `Y₃`, the degree
  condition leaves `y` no free degree (`freeDeg_eq_zero_of_farY`), so no pair of `F` contains it.
-/
module

public import OllivierBF.RangeSavings
public import OllivierBF.MaxFlow

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `X₃` of Theorem 5.3 (ii) as the paper defines it from the local data: the vertices of `U_i`
without cross edges whose neighbours are all `i`, vertices of `C` without neighbours in `U_j`, or
vertices of `U_i` without cross edges. -/
def IsFarXLocal (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (X : Finset V) : Prop :=
  ∀ x ∈ X, x ∈ uniq G i j ∧ (∀ y ∈ uniq G j i, ¬ G.Adj x y) ∧
    ∀ w, G.Adj x w → w = i ∨ (w ∈ common G i j ∧ ∀ y ∈ uniq G j i, ¬ G.Adj w y) ∨
      (w ∈ uniq G i j ∧ ∀ y ∈ uniq G j i, ¬ G.Adj w y)

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ} {μ : V → V → ℝ} {i j : V}
variable {ρ : V → V → ℝ}

/-- The paper's `X₃` satisfies the condition of Theorem 5.3 (ii). -/
lemma IsFarXLocal.isFarX {X : Finset V} (h : IsFarXLocal G i j X) : IsFarX G i j X :=
  fun x hx => by
    obtain ⟨hxU, hnc, hnb⟩ := h x hx
    refine ⟨hxU, hnc, fun w hw => ?_⟩
    rcases hnb w hw with hwi | ⟨-, hw'⟩ | ⟨-, hw'⟩
    · exact Or.inl hwi
    · exact Or.inr hw'
    · exact Or.inr hw'

/-! ### The lower end -/

/-- On the supports, the true distance is at most the charged distance of the lower end of
Theorem 5.2. -/
lemma dist_le_chargedDist_empty (hd : GraphMetric G d) (hij : G.Adj i j) (hi : OneStepAt G μ i)
    (hj : OneStepAt G μ j) {x y : V} (hx : 0 < resP μ i j x) (hy : 0 < resN μ i j y) :
    d x y ≤ chargedDist G i j ∅ x y := by
  unfold chargedDist
  split_ifs with h1 h2 h3 h4
  · rw [h1]
    exact (hd.self y).le
  · unfold crossDist
    split_ifs with h5 h6
    · exact (hd.adj h5).le
    · rcases h6 with ⟨w, -, hxw, hwy⟩ | ⟨w, -, hw⟩
      · exact hd.le_two hxw hwy
      · simp at hw
    · exact resid_dist_le_three hd hij hi hj hx hy
  · exfalso
    have := resP_eq_zero_of_uniq hi hj h3.2
    linarith
  · exact (hd.adj h4).le
  · exact resid_dist_le_two hd hij hi hj hx hy h2

/-- **Theorem 5.3 (iii), lower end.** A partial plan of the residuals whose charged distances are at
least those of the lower end of Theorem 5.2 gives a lower bound on `κ_*`. -/
theorem tq_lower_le_kappaF_empty (hi : OneStepAt G μ i) (hj : OneStepAt G μ j)
    {π : V → V → ℝ} (hπ : IsSubPlan (resP μ i j) (resN μ i j) π) {c : V → V → ℝ}
    (hc : ∀ x y, 0 < π x y → chargedDist G i j ∅ x y ≤ c x y) :
    1 - 3 * resMass μ i j + ∑ x, ∑ y, (3 - c x y) * π x y ≤ kappaF G i j μ ∅ := by
  rw [kappaF_eq_sigmaStar hi hj ∅]
  have hσ : savings (chargedDist G i j ∅) π
      ≤ sigmaStar (chargedDist G i j ∅) (resP μ i j) (resN μ i j) := by
    unfold sigmaStar
    exact le_csSup (bddAbove_savings (chargedDist_nonneg ∅)) ⟨π, hπ, rfl⟩
  have hcs : ∑ x, ∑ y, (3 - c x y) * π x y ≤ savings (chargedDist G i j ∅) π := by
    unfold savings
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
    rcases (hπ.1 x y).eq_or_lt with h0 | h0
    · rw [← h0]
      simp
    · exact mul_le_mul_of_nonneg_right (by linarith [hc x y h0]) h0.le
  linarith

/-! ### The upper end -/

/-- `pair_bound_X` for any cost that is `1` on edges and at least `2` between other distinct
vertices. -/
lemma pair_bound_X_of {c : V → V → ℝ} (hc1 : ∀ {x y}, G.Adj x y → c x y = 1)
    (hc2 : ∀ {x y}, x ≠ y → ¬ G.Adj x y → 2 ≤ c x y) (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ)
    {X : Finset V}
    (hX : ∀ x ∈ X, ∀ y, 0 < resN μ i j y → y ∉ overlap (G := G) i j → 3 ≤ c x y) (x y : V) :
    (2 - (if G.Adj x y then 1 else 0) + (if x ∈ X ∧ y ∉ overlap (G := G) i j then 1 else 0))
        * ρ x y ≤ c x y * ρ x y := by
  rcases (hρ.1 x y).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  obtain ⟨-, hyN⟩ := resid_pos_of_plan_pos hρ h0
  have hxy : x ≠ y := by
    rintro rfl
    have := resid_plan_diag hρ x
    linarith
  refine mul_le_mul_of_nonneg_right ?_ h0.le
  by_cases hadj : G.Adj x y
  · have hnf : ¬ (x ∈ X ∧ y ∉ overlap (G := G) i j) := by
      rintro ⟨hx, hy⟩
      have h3 := hX x hx y hyN hy
      rw [hc1 hadj] at h3
      linarith
    rw [ite_eq_left hadj, ite_eq_right hnf, hc1 hadj]
    norm_num
  · have hd2 := hc2 hxy hadj
    rw [ite_eq_right hadj]
    by_cases hf : x ∈ X ∧ y ∉ overlap (G := G) i j
    · rw [ite_eq_left hf]
      have h3 := hX x hf.1 y hyN hf.2
      linarith
    · rw [ite_eq_right hf]
      linarith

/-- `pair_bound_Y` for the same costs. -/
lemma pair_bound_Y_of {c : V → V → ℝ} (hc1 : ∀ {x y}, G.Adj x y → c x y = 1)
    (hc2 : ∀ {x y}, x ≠ y → ¬ G.Adj x y → 2 ≤ c x y) (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ)
    {Y : Finset V}
    (hY : ∀ y ∈ Y, ∀ x, 0 < resP μ i j x → x ∉ overlap (G := G) i j → 3 ≤ c x y) (x y : V) :
    (2 - (if G.Adj x y then 1 else 0) + (if y ∈ Y ∧ x ∉ overlap (G := G) i j then 1 else 0))
        * ρ x y ≤ c x y * ρ x y := by
  rcases (hρ.1 x y).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  obtain ⟨hxP, -⟩ := resid_pos_of_plan_pos hρ h0
  have hxy : x ≠ y := by
    rintro rfl
    have := resid_plan_diag hρ x
    linarith
  refine mul_le_mul_of_nonneg_right ?_ h0.le
  by_cases hadj : G.Adj x y
  · have hnf : ¬ (y ∈ Y ∧ x ∉ overlap (G := G) i j) := by
      rintro ⟨hy, hx⟩
      have h3 := hY y hy x hxP hx
      rw [hc1 hadj] at h3
      linarith
    rw [ite_eq_left hadj, ite_eq_right hnf, hc1 hadj]
    norm_num
  · have hd2 := hc2 hxy hadj
    rw [ite_eq_right hadj]
    by_cases hf : y ∈ Y ∧ x ∉ overlap (G := G) i j
    · rw [ite_eq_left hf]
      have h3 := hY y hf.1 x hxP hf.2
      linarith
    · rw [ite_eq_right hf]
      linarith

/-- The counting behind Theorem 5.3 (ii), for any cost that is `1` on edges and at least `2`
between other distinct vertices: a coupling of the residuals that moves at most `η` along edges
costs at least `2τ − η + D₃`. -/
lemma cost_ge_of_far {c : V → V → ℝ} (hc1 : ∀ {x y}, G.Adj x y → c x y = 1)
    (hc2 : ∀ {x y}, x ≠ y → ¬ G.Adj x y → 2 ≤ c x y) {X Y : Finset V}
    (hX : ∀ x ∈ X, ∀ y, 0 < resN μ i j y → y ∉ overlap (G := G) i j → 3 ≤ c x y)
    (hY : ∀ y ∈ Y, ∀ x, 0 < resP μ i j x → x ∉ overlap (G := G) i j → 3 ≤ c x y)
    (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) {η : ℝ} (hA : adjMass G ρ ≤ η) :
    2 * resMass μ i j - η
        + max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap (G := G) i j, resN μ i j y)
          (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap (G := G) i j, resP μ i j x))
      ≤ cost c ρ := by
  have hm : mass ρ = resMass μ i j := hρ.mass_eq
  have hXc : 2 * mass ρ - adjMass G ρ
      + ∑ x, ∑ y, (if x ∈ X ∧ y ∉ overlap (G := G) i j then ρ x y else 0) ≤ cost c ρ := by
    rw [← sum_weight_X (G := G) ρ X (overlap (G := G) i j)]
    unfold cost
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      pair_bound_X_of hc1 hc2 hρ hX x y
  have hYc : 2 * mass ρ - adjMass G ρ
      + ∑ x, ∑ y, (if y ∈ Y ∧ x ∉ overlap (G := G) i j then ρ x y else 0) ≤ cost c ρ := by
    rw [← sum_weight_Y (G := G) ρ Y (overlap (G := G) i j)]
    unfold cost
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      pair_bound_Y_of hc1 hc2 hρ hY x y
  have hfx := far_ge hρ X (overlap (G := G) i j)
  have hfy := far_ge' hρ Y (overlap (G := G) i j)
  have hfx0 : 0 ≤ ∑ x, ∑ y, (if x ∈ X ∧ y ∉ overlap (G := G) i j then ρ x y else 0) :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
      split_ifs
      · exact hρ.1 x y
      · exact le_rfl
  have hfy0 : 0 ≤ ∑ x, ∑ y, (if y ∈ Y ∧ x ∉ overlap (G := G) i j then ρ x y else 0) :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
      split_ifs
      · exact hρ.1 x y
      · exact le_rfl
  have hmax : max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap (G := G) i j, resN μ i j y)
      (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap (G := G) i j, resP μ i j x))
      ≤ cost c ρ - (2 * resMass μ i j - η) :=
    max_le (by linarith) (max_le (by linarith) (by linarith))
  linarith

/-- With the local `X₃`, the pairs of an admissible `F` never shorten a distance from `X₃` to
`U_j`: every neighbour of `x` is listed, and the pairs of `F` contain no listed vertex. -/
lemma three_le_chargedDist_of_farX {F : Finset (Sym2 V)} (hF : Admissible G i j F)
    {X : Finset V} (hX : IsFarXLocal G i j X) {x y : V} (hx : x ∈ X) (hy : y ∈ uniq G j i) :
    3 ≤ chargedDist G i j F x y := by
  obtain ⟨hxU, hnc, hnb⟩ := hX x hx
  have h3 : crossDist G i j F x y = 3 := by
    refine crossDist_eq_three (hnc y hy) ?_ ?_
    · rintro ⟨w, -, hxw, hwy⟩
      rcases hnb w hxw with hwi | ⟨-, hw'⟩ | ⟨-, hw'⟩
      · rw [hwi] at hwy
        exact (mem_uniq.mp hy).2.2 hwy
      · exact hw' y hy hwy
      · exact hw' y hy hwy
    · rintro ⟨w, hxw, hwF⟩
      have hwL : w ∈ listed G i j := by
        rcases hnb w hxw with hwi | ⟨hwC, -⟩ | ⟨hwU, -⟩
        · rw [hwi]
          exact i_listed
        · exact common_listed hwC
        · exact uniq_listed hwU
      exact (cand_vertices (hF.1 hwF)).2.1 hwL
  have hcd := chargedDist_cross (G := G) (i := i) (j := j) (F := F) hxU hy
  linarith

/-- The degree condition of `Y₃` leaves `y` no free degree. -/
lemma freeDeg_eq_zero_of_farY {Y : Finset V} (hY : IsFarY G i j Y) {y : V} (hy : y ∈ Y) :
    freeDeg G i j y = 0 := by
  obtain ⟨hyU, hnc, hdeg, -⟩ := hY y hy
  obtain ⟨-, hjy, hiy⟩ := mem_uniq.mp hyU
  have hset : (listed G i j).filter (G.Adj y) = insert j (G.neighborFinset y ∩ common G i j) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hvL, hyv⟩
      rcases mem_listed.mp hvL with hvi | hvj | hvU | hvC
      · rw [hvi] at hyv
        exact absurd hyv.symm hiy
      · exact Or.inl hvj
      · exact absurd hyv.symm (hnc v hvU)
      · exact Or.inr ⟨hyv, hvC⟩
    · rintro (hvj | ⟨hyv, hvC⟩)
      · rw [hvj]
        exact ⟨j_listed, hjy.symm⟩
      · exact ⟨common_listed hvC, hyv⟩
  have hj_notin : j ∉ G.neighborFinset y ∩ common G i j := by
    simp [mem_common, SimpleGraph.irrefl]
  unfold freeDeg listedDeg
  rw [hset, Finset.card_insert_of_notMem hj_notin]
  omega

/-- No pair of an admissible `F` contains a vertex of `Y₃`. -/
lemma no_pair_of_farY {F : Finset (Sym2 V)} (hF : Admissible G i j F) {Y : Finset V}
    (hY : IsFarY G i j Y) {y : V} (hy : y ∈ Y) (w : V) : s(w, y) ∉ F := by
  intro hw
  have h0 := freeDeg_eq_zero_of_farY hY hy
  have hle := hF.2 y
  have hpos : 0 < pairDeg F y := by
    unfold pairDeg
    refine Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, ?_⟩⟩
    show s(y, w) ∈ F
    rw [Sym2.eq_swap]
    exact hw
  omega

/-- With `Y₃`, the pairs of an admissible `F` never shorten a distance from `U_i` to `Y₃`. -/
lemma three_le_chargedDist_of_farY {F : Finset (Sym2 V)} (hF : Admissible G i j F)
    {Y : Finset V} (hY : IsFarY G i j Y) {x y : V} (hy : y ∈ Y) (hx : x ∈ uniq G i j) :
    3 ≤ chargedDist G i j F x y := by
  obtain ⟨hyU, hnc, -, hCk⟩ := hY y hy
  have h3 : crossDist G i j F x y = 3 := by
    refine crossDist_eq_three (hnc x hx) ?_ ?_
    · rintro ⟨w, hw, hxw, hwy⟩
      rcases Finset.mem_union.mp hw with hwU | hwC
      · exact hnc w hwU hwy
      · exact hCk w hwC hwy.symm x hx hxw.symm
    · rintro ⟨w, -, hwF⟩
      exact no_pair_of_farY hF hY hy w hwF
  have hcd := chargedDist_cross (G := G) (i := i) (j := j) (F := F) hx hyU
  linarith

/-- **Theorem 5.3 (iii), upper end, for one admissible `F`.** -/
theorem kappaF_le_tq_upper (hi : OneStepAt G μ i) (hj : OneStepAt G μ j)
    {F : Finset (Sym2 V)} (hF : Admissible G i j F) {η : ℝ}
    (hη : ∀ ρ, IsCoupling (resP μ i j) (resN μ i j) ρ → adjMass G ρ ≤ η)
    {X Y : Finset V} (hX : IsFarXLocal G i j X) (hY : IsFarY G i j Y) :
    kappaF G i j μ F ≤ 1 - 2 * resMass μ i j + η
      - max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap (G := G) i j, resN μ i j y)
        (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap (G := G) i j, resP μ i j x)) := by
  have key : ∀ ρ, IsCoupling (resP μ i j) (resN μ i j) ρ →
      2 * resMass μ i j - η
          + max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap (G := G) i j, resN μ i j y)
            (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap (G := G) i j, resP μ i j x))
        ≤ cost (chargedDist G i j F) ρ := fun ρ hρ =>
    cost_ge_of_far (c := chargedDist G i j F) (fun h => chargedDist_of_adj h)
      (fun hxy hna => two_le_chargedDist hxy hna)
      (fun x hx y hy hyS =>
        three_le_chargedDist_of_farX hF hX hx (mem_uniq_of_resN_pos hi hj hy hyS))
      (fun y hy x hx hxS =>
        three_le_chargedDist_of_farY hF hY hy (mem_uniq_of_resP_pos hi hj hx hxS))
      hρ (hη ρ hρ)
  have hW := le_W1 (exists_resid_coupling_of hi hj) key
  unfold kappaF cORm
  rw [W1_chargedDist_eq_resid hi hj F]
  linarith

/-- **Theorem 5.3 (iii), upper end.** The upper end of (ii), with `X₃` from the local data, bounds
`κ̄*`, the largest curvature of a graph consistent with the local data. -/
theorem kappaMax_le_tq_upper (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {η : ℝ}
    (hη : ∀ ρ, IsCoupling (resP μ i j) (resN μ i j) ρ → adjMass G ρ ≤ η)
    {X Y : Finset V} (hX : IsFarXLocal G i j X) (hY : IsFarY G i j Y) :
    kappaMax G i j μ ≤ 1 - 2 * resMass μ i j + η
      - max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap (G := G) i j, resN μ i j y)
        (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap (G := G) i j, resP μ i j x)) := by
  unfold kappaMax
  exact Finset.sup'_le _ _ fun F hF =>
    kappaF_le_tq_upper hi hj (mem_admissibleSets.mp hF) hη hX hY

/-- **Theorem 5.3 (iii).** `κ_TQ ≤ κ_*` and `κ̄* ≤ κ̄_TQ`: a partial plan charged at least the
distance of the lower end of Theorem 5.2 bounds `κ_*` from below, and the upper end of (ii), with
`η' ≥ η` the maximum flow and `X₃`, `Y₃` defined from the local data, bounds `κ̄*` from above. -/
theorem tq_range_paper (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) :
    (∀ π c : V → V → ℝ, IsSubPlan (resP μ i j) (resN μ i j) π →
        (∀ x y, 0 < π x y → chargedDist G i j ∅ x y ≤ c x y) →
        1 - 3 * resMass μ i j + ∑ x, ∑ y, (3 - c x y) * π x y ≤ kappaF G i j μ ∅) ∧
    (∀ (η' : ℝ) (X Y : Finset V), maxFlow G (resP μ i j) (resN μ i j) ≤ η' →
        IsFarXLocal G i j X → IsFarY G i j Y →
        kappaMax G i j μ ≤ 1 - 2 * resMass μ i j + η'
          - max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap (G := G) i j, resN μ i j y)
            (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap (G := G) i j, resP μ i j x))) :=
  ⟨fun _ _ hπ hc => tq_lower_le_kappaF_empty hi hj hπ hc,
    fun _ _ _ hη' hX hY => kappaMax_le_tq_upper hi hj
      (fun _ hρ => (adjMass_le_maxFlow (G := G) hρ).trans hη') hX hY⟩

end OllivierBF
