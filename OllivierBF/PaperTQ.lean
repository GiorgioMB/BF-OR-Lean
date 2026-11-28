/- Proposition 4.2 and Theorem 5.3 as the paper states them. -/
module

public import OllivierBF.AttainableRange

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `X₃`: the vertices of `U_i` without cross edges whose neighbours are all `i`, vertices of
`C` without neighbours in `U_j`, or vertices of `U_i` without cross edges. -/
def IsFarX (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (X : Finset V) : Prop :=
  ∀ x ∈ X, x ∈ uniq G i j ∧ (∀ y ∈ uniq G j i, ¬ G.Adj x y) ∧
    ∀ w, G.Adj x w → w = i ∨ (w ∈ common G i j ∧ ∀ y ∈ uniq G j i, ¬ G.Adj w y) ∨
      (w ∈ uniq G i j ∧ ∀ y ∈ uniq G j i, ¬ G.Adj w y)

/-- `Y₃`: the vertices `y` of `U_j` without cross edges, with `d_y = 1 + |N(y) ∩ C|`, and with
no neighbour in `C` adjacent to `U_i`. -/
def IsFarY (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (Y : Finset V) : Prop :=
  ∀ y ∈ Y, y ∈ uniq G j i ∧ (∀ x ∈ uniq G i j, ¬ G.Adj x y) ∧
    G.degree y = 1 + (G.neighborFinset y ∩ common G i j).card ∧
    ∀ k ∈ common G i j, G.Adj y k → ∀ x ∈ uniq G i j, ¬ G.Adj k x

/-- A flow along the edges of `G` with capacities `α`, `β`: a partial plan that moves mass
only along edges. -/
def IsEdgeFlow (G : SimpleGraph V) [DecidableRel G.Adj] (α β : V → ℝ) (f : V → V → ℝ) : Prop :=
  IsSubPlan α β f ∧ ∀ x y, ¬ G.Adj x y → f x y = 0

/-- `η`: the maximum value of a flow along the edges of `G` with capacities `α`, `β`. -/
noncomputable def maxFlow (G : SimpleGraph V) [DecidableRel G.Adj] (α β : V → ℝ) : ℝ :=
  sSup (mass '' {f | IsEdgeFlow G α β f})

lemma isClosed_edgeSupported (G : SimpleGraph V) [DecidableRel G.Adj] :
    IsClosed {f : V → V → ℝ | ∀ x y, ¬ G.Adj x y → f x y = 0} := by
  have hset : {f : V → V → ℝ | ∀ x y, ¬ G.Adj x y → f x y = 0} =
      ⋂ x, ⋂ y, (if G.Adj x y then Set.univ else {f : V → V → ℝ | f x y = 0}) := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    refine forall_congr' fun x => forall_congr' fun y => ?_
    by_cases h : G.Adj x y
    · rw [ite_eq_left h]
      exact ⟨fun _ => Set.mem_univ f, fun _ hn => absurd h hn⟩
    · rw [ite_eq_right h]
      exact ⟨fun hf => hf h, fun hf _ => hf⟩
  rw [hset]
  refine isClosed_iInter fun x => isClosed_iInter fun y => ?_
  by_cases h : G.Adj x y
  · rw [ite_eq_left h]
    exact isClosed_univ
  · rw [ite_eq_right h]
    exact isClosed_eq (by fun_prop) continuous_const

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ}
variable {μ : V → V → ℝ} {i j : V} {ρ : V → V → ℝ}

/-- **Proposition 4.2.** `κ_μ = 1 − 3τ + σ*`: `κ_μ − (1 − 3τ)` is the maximum `σ*` of the
savings over the partial plans of the residuals. -/
theorem savings_paper (hd : GraphMetric G d) (hij : G.Adj i j) (hi : OneStepAt G μ i)
    (hj : OneStepAt G μ j) :
    IsGreatest (savings d '' {π | IsSubPlan (resP μ i j) (resN μ i j) π})
      (cORm d μ i j - (1 - 3 * resMass μ i j)) := by
  refine isGreatest_of_isLUB (resP_nonneg μ i j) (resN_nonneg μ i j) (continuous_savings d) ?_
  have e : cORm d μ i j - (1 - 3 * resMass μ i j)
      = 3 * ∑ x, resP μ i j x - W1 d (resP μ i j) (resN μ i j) := by
    rw [cORm_eq_resid hd hi hj]
    unfold resMass
    ring
  rw [e]
  exact isLUB_savings (resP_sum_eq_resN_sum hi hj) hd.nonneg
    (fun x y hx hy => resid_dist_le_three hd hij hi hj hx hy) (exists_resid_coupling_of hi hj)

/-- **Theorem 5.3 (i).** -/
theorem tq_lower_paper (hd : GraphMetric G d) (hij : G.Adj i j)
    (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {π : V → V → ℝ}
    (hπ : IsSubPlan (resP μ i j) (resN μ i j) π) {c : V → V → ℝ}
    (hc : ∀ x y, 0 < π x y → d x y ≤ c x y) :
    1 - 3 * resMass μ i j + ∑ x, ∑ y, (3 - c x y) * π x y ≤ cORm d μ i j := by
  have h1 := (savings_paper hd hij hi hj).2 ⟨π, hπ, rfl⟩
  have h2 := sum_le_savings_of_le hπ.1 hc
  linarith

theorem isGreatest_maxFlow {α β : V → ℝ} (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y) :
    IsGreatest (mass '' {f | IsEdgeFlow G α β f}) (maxFlow G α β) := by
  have hcont : Continuous (mass : (V → V → ℝ) → ℝ) := by
    show Continuous fun f : V → V → ℝ => ∑ x, ∑ y, f x y
    fun_prop
  obtain ⟨f, hf, hfP, hmax⟩ := exists_max_subPlan hα hβ
    (fun f => ∀ x y, ¬ G.Adj x y → f x y = 0) (isClosed_edgeSupported G) (fun _ _ _ => rfl)
    mass hcont
  have hG : IsGreatest (mass '' {f | IsEdgeFlow G α β f}) (mass f) :=
    ⟨⟨f, ⟨hf, hfP⟩, rfl⟩, by
      rintro _ ⟨g, hg, rfl⟩
      have hg' : IsEdgeFlow G α β g := hg
      exact hmax g hg'.1 hg'.2⟩
  unfold maxFlow
  rw [hG.csSup_eq]
  exact hG

section flows

variable {α β : V → ℝ}

lemma IsSubPlan.mass_le {π : V → V → ℝ} (hπ : IsSubPlan α β π) : mass π ≤ ∑ x, α x := by
  unfold mass
  exact Finset.sum_le_sum fun x _ => hπ.2.1 x

lemma isEdgeFlow_zero (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y) :
    IsEdgeFlow G α β (fun _ _ => 0) :=
  ⟨isSubPlan_zero hα hβ, fun _ _ _ => rfl⟩

lemma bddAbove_flows : BddAbove (mass '' {f | IsEdgeFlow G α β f}) :=
  ⟨∑ x, α x, by
    rintro _ ⟨f, hf, rfl⟩
    have hf' : IsEdgeFlow G α β f := hf
    exact IsSubPlan.mass_le hf'.1⟩

/-- The edges of a coupling carry a flow, so a coupling moves at most `η` along edges. -/
lemma adjMass_le_maxFlow {ρ : V → V → ℝ} (hρ : IsCoupling α β ρ) :
    adjMass G ρ ≤ maxFlow G α β := by
  have hf : IsEdgeFlow G α β (fun x y => if G.Adj x y then ρ x y else 0) := by
    refine ⟨⟨fun x y => ?_, fun x => ?_, fun y => ?_⟩, fun x y h => ?_⟩
    · show 0 ≤ (if G.Adj x y then ρ x y else 0)
      split_ifs
      · exact hρ.1 x y
      · exact le_rfl
    · show ∑ y, (if G.Adj x y then ρ x y else 0) ≤ α x
      calc ∑ y, (if G.Adj x y then ρ x y else 0) ≤ ∑ y, ρ x y :=
            Finset.sum_le_sum fun y _ => by
              split_ifs
              · exact le_rfl
              · exact hρ.1 x y
        _ = α x := hρ.2.1 x
    · show ∑ x, (if G.Adj x y then ρ x y else 0) ≤ β y
      calc ∑ x, (if G.Adj x y then ρ x y else 0) ≤ ∑ x, ρ x y :=
            Finset.sum_le_sum fun x _ => by
              split_ifs
              · exact le_rfl
              · exact hρ.1 x y
        _ = β y := hρ.2.2 y
    · show (if G.Adj x y then ρ x y else 0) = 0
      rw [ite_eq_right h]
  calc adjMass G ρ = mass (fun x y => if G.Adj x y then ρ x y else 0) := rfl
    _ ≤ maxFlow G α β := le_csSup (bddAbove_flows (G := G) (α := α) (β := β)) ⟨_, hf, rfl⟩

/-- A partial plan extends to a coupling that dominates it. -/
lemma exists_coupling_ge {π : V → V → ℝ} (hπ : IsSubPlan α β π)
    (hmass : ∑ x, α x = ∑ y, β y) :
    ∃ ρ, IsCoupling α β ρ ∧ ∀ x y, π x y ≤ ρ x y := by
  have hαr : ∀ x, 0 ≤ α x - ∑ y, π x y := fun x => sub_nonneg.2 (hπ.2.1 x)
  have hβr : ∀ y, 0 ≤ β y - ∑ x, π x y := fun y => sub_nonneg.2 (hπ.2.2 y)
  have hM : ∑ y, (β y - ∑ x, π x y) = ∑ x, (α x - ∑ y, π x y) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hmass, Finset.sum_comm]
  obtain ⟨σ, hσ, -⟩ := exists_piece_coupling (d := fun _ _ => (0 : ℝ)) hαr hβr rfl hM le_rfl
    (fun _ _ _ _ => le_rfl)
  refine ⟨fun x y => π x y + σ x y,
    ⟨fun x y => add_nonneg (hπ.1 x y) (hσ.1 x y), fun x => ?_, fun y => ?_⟩,
    fun x y => ?_⟩
  · show ∑ y, (π x y + σ x y) = α x
    calc ∑ y, (π x y + σ x y) = ∑ y, π x y + ∑ y, σ x y := Finset.sum_add_distrib
      _ = ∑ y, π x y + (α x - ∑ y, π x y) := by rw [hσ.2.1 x]
      _ = α x := by ring
  · show ∑ x, (π x y + σ x y) = β y
    calc ∑ x, (π x y + σ x y) = ∑ x, π x y + ∑ x, σ x y := Finset.sum_add_distrib
      _ = ∑ x, π x y + (β y - ∑ x, π x y) := by rw [hσ.2.2 y]
      _ = β y := by ring
  · show π x y ≤ π x y + σ x y
    linarith [hσ.1 x y]

/-- Every bound on the mass that the couplings move along edges is at least `η`. -/
lemma maxFlow_le (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y) (hmass : ∑ x, α x = ∑ y, β y)
    {η : ℝ} (hη : ∀ ρ, IsCoupling α β ρ → adjMass G ρ ≤ η) : maxFlow G α β ≤ η := by
  unfold maxFlow
  refine csSup_le ⟨_, _, isEdgeFlow_zero hα hβ, rfl⟩ ?_
  rintro _ ⟨f, hf, rfl⟩
  have hf' : IsEdgeFlow G α β f := hf
  obtain ⟨ρ, hρ, hge⟩ := exists_coupling_ge hf'.1 hmass
  calc mass f = ∑ x, ∑ y, (if G.Adj x y then f x y else 0) := by
        unfold mass
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        split_ifs with h
        · rfl
        · exact hf'.2 x y h
    _ ≤ adjMass G ρ := by
        unfold adjMass
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        split_ifs
        · exact hge x y
        · exact le_rfl
    _ ≤ η := hη ρ hρ

end flows

/-- **Theorem 5.3 (ii).** The maximum flow `η` is attained, and the bound holds for every
`η' ≥ η`. -/
theorem tq_upper_paper (hd : GraphMetric G d) (h3 : ThreeApart G d)
    (hi : OneStepAt G μ i) (hj : OneStepAt G μ j)
    {X Y : Finset V} (hX : IsFarX G i j X) (hY : IsFarY G i j Y) :
    IsGreatest (mass '' {f | IsEdgeFlow G (resP μ i j) (resN μ i j) f})
        (maxFlow G (resP μ i j) (resN μ i j)) ∧
      ∀ η', maxFlow G (resP μ i j) (resN μ i j) ≤ η' →
        cORm d μ i j ≤ 1 - 2 * resMass μ i j + η'
          - max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap (G := G) i j, resN μ i j y)
            (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap (G := G) i j, resP μ i j x)) := by
  refine ⟨isGreatest_maxFlow (resP_nonneg μ i j) (resN_nonneg μ i j), fun η hη => ?_⟩
  refine tq_upper hd hi hj (fun _ hρ => (adjMass_le_maxFlow (G := G) hρ).trans hη)
    (fun x hx y hy hyS => ?_) (fun y hy x hx hxS => ?_)
  · obtain ⟨hxU, hnc, hnb⟩ := hX x hx
    exact far_of_closedX h3 hxU hnc
      (fun w hw => (hnb w hw).imp_right fun h => h.elim And.right And.right)
      (mem_uniq_of_resN_pos hi hj hy hyS)
  · obtain ⟨hyU, hnc, hdeg, hCk⟩ := hY y hy
    have hyj : G.Adj j y := (mem_uniq.1 hyU).2.1
    refine far_of_closedY h3 hyU hnc (fun w hw => ?_) (mem_uniq_of_resP_pos hi hj hx hxS)
    rcases nbr_of_degree_eq hyj hdeg w hw with h | h
    · exact Or.inl h
    · exact Or.inr (hCk w h hw)

lemma three_le_chargedDist_of_farX {F : Finset (Sym2 V)} (hF : Admissible G i j F)
    {X : Finset V} (hX : IsFarX G i j X) {x y : V} (hx : x ∈ X) (hy : y ∈ uniq G j i) :
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

theorem kappaF_le_tq_upper (hi : OneStepAt G μ i) (hj : OneStepAt G μ j)
    {F : Finset (Sym2 V)} (hF : Admissible G i j F) {η : ℝ}
    (hη : ∀ ρ, IsCoupling (resP μ i j) (resN μ i j) ρ → adjMass G ρ ≤ η)
    {X Y : Finset V} (hX : IsFarX G i j X) (hY : IsFarY G i j Y) :
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

/-- **Theorem 5.3 (iii).** `κ_TQ ≤ κ_*` and `κ̄* ≤ κ̄_TQ`. -/
theorem tq_range_paper (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) :
    (∀ π c : V → V → ℝ, IsSubPlan (resP μ i j) (resN μ i j) π →
        (∀ x y, 0 < π x y → chargedDist G i j ∅ x y ≤ c x y) →
        1 - 3 * resMass μ i j + ∑ x, ∑ y, (3 - c x y) * π x y ≤ kappaF G i j μ ∅) ∧
    (∀ (η : ℝ) (X Y : Finset V),
        maxFlow G (resP μ i j) (resN μ i j) ≤ η →
        IsFarX G i j X → IsFarY G i j Y →
        kappaMax G i j μ ≤ 1 - 2 * resMass μ i j + η
          - max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap (G := G) i j, resN μ i j y)
            (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap (G := G) i j, resP μ i j x))) := by
  refine ⟨fun π c hπ hc => ?_, fun η X Y hη hX hY => ?_⟩
  · have h1 := (kappaF_isLUB hi hj ∅).1 ⟨π, hπ, rfl⟩
    have h2 := sum_le_savings_of_le hπ.1 hc
    linarith
  · unfold kappaMax
    exact Finset.sup'_le _ _ fun F hF =>
      kappaF_le_tq_upper hi hj (mem_admissibleSets.mp hF)
        (fun _ hρ => (adjMass_le_maxFlow (G := G) hρ).trans hη) hX hY

/-- A coupling of the residuals moves at most `η'` along edges: any
`B ≥ F + min{O_i, |r(i)| − F} + min{O_j, |r(j)| − F}` on `[0, F_ij]`, plus, over blocks that no
supply–demand edge outside `{i, j}` crosses, the smaller of the capped supply and demand. -/
theorem adjMass_le_blocks {β : Type*} [DecidableEq β] (hij : i ≠ j)
    (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) (b : V → β)
    (hb : ∀ x y, 0 < resP μ i j x → 0 < resN μ i j y → G.Adj x y →
      x ∉ ({i, j} : Finset V) → y ∉ ({i, j} : Finset V) → b x = b y)
    {B : ℝ} (hB : ∀ F, 0 ≤ F → F ≤ flowIJ μ i j →
      F + min (oppNbr G μ i j i) (resAbs μ i j i - F)
        + min (oppNbr G μ i j j) (resAbs μ i j j - F) ≤ B) :
    adjMass G ρ ≤ B + ∑ l ∈ Finset.univ.image b,
        min (∑ x ∈ Finset.univ.filter (fun x => b x = l ∧ x ∉ ({i, j} : Finset V)), capS G μ i j x)
          (∑ y ∈ Finset.univ.filter (fun y => b y = l ∧ y ∉ ({i, j} : Finset V)), capD G μ i j y) := by
  have hiI : i ∈ ({i, j} : Finset V) := by simp
  have hjI : j ∈ ({i, j} : Finset V) := by simp
  have hsplit : adjMass G ρ ≤
      ∑ x, ∑ y, (if G.Adj x y ∧ (x ∈ ({i, j} : Finset V) ∨ y ∈ ({i, j} : Finset V))
          then ρ x y else 0)
      + ∑ x, ∑ y, (if G.Adj x y ∧ x ∉ ({i, j} : Finset V) ∧ y ∉ ({i, j} : Finset V)
          then ρ x y else 0) := by
    unfold adjMass
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y _ => ?_
    have h0 := hρ.1 x y
    by_cases hadj : G.Adj x y
    · by_cases hc : x ∈ ({i, j} : Finset V) ∨ y ∈ ({i, j} : Finset V)
      · have hcond : G.Adj x y ∧ (x ∈ ({i, j} : Finset V) ∨ y ∈ ({i, j} : Finset V)) := ⟨hadj, hc⟩
        have hn : ¬ (G.Adj x y ∧ x ∉ ({i, j} : Finset V) ∧ y ∉ ({i, j} : Finset V)) := by
          rintro ⟨-, hx, hy⟩
          rcases hc with hc | hc
          · exact hx hc
          · exact hy hc
        rw [ite_eq_left hadj, ite_eq_left hcond, ite_eq_right hn]
        linarith
      · have hcond : G.Adj x y ∧ x ∉ ({i, j} : Finset V) ∧ y ∉ ({i, j} : Finset V) :=
          ⟨hadj, fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩
        have hn : ¬ (G.Adj x y ∧ (x ∈ ({i, j} : Finset V) ∨ y ∈ ({i, j} : Finset V))) :=
          fun h => hc h.2
        rw [ite_eq_left hadj, ite_eq_right hn, ite_eq_left hcond]
        linarith
    · have hn1 : ¬ (G.Adj x y ∧ (x ∈ ({i, j} : Finset V) ∨ y ∈ ({i, j} : Finset V))) :=
        fun h => hadj h.1
      have hn2 : ¬ (G.Adj x y ∧ x ∉ ({i, j} : Finset V) ∧ y ∉ ({i, j} : Finset V)) :=
        fun h => hadj h.1
      rw [ite_eq_right hadj, ite_eq_right hn1, ite_eq_right hn2]
      linarith
  have hid : ∑ x, ∑ y, (if G.Adj x y ∧ (x ∈ ({i, j} : Finset V) ∨ y ∈ ({i, j} : Finset V))
        then ρ x y else 0)
      = (if G.Adj i j then ρ i j else 0) + (if G.Adj j i then ρ j i else 0)
        + ∑ y, (if y ∉ ({i, j} : Finset V) ∧ G.Adj i y then ρ i y else 0)
        + ∑ x, (if x ∉ ({i, j} : Finset V) ∧ G.Adj x i then ρ x i else 0)
        + ∑ y, (if y ∉ ({i, j} : Finset V) ∧ G.Adj j y then ρ j y else 0)
        + ∑ x, (if x ∉ ({i, j} : Finset V) ∧ G.Adj x j then ρ x j else 0) := by
    simp only [ite_at_ij (G := G) hij ρ, Finset.sum_add_distrib]
    rw [sum_sum_pair_eq, sum_sum_pair_eq, sum_sum_fst_eq, sum_sum_snd_eq, sum_sum_fst_eq,
      sum_sum_snd_eq]
  have hf1 : (if G.Adj i j then ρ i j else 0) ≤ ρ i j := by
    split_ifs
    · exact le_rfl
    · exact hρ.1 i j
  have hf2 : (if G.Adj j i then ρ j i else 0) ≤ ρ j i := by
    split_ifs
    · exact le_rfl
    · exact hρ.1 j i
  have hf1n : 0 ≤ (if G.Adj i j then ρ i j else 0) := by
    split_ifs
    · exact hρ.1 i j
    · exact le_rfl
  have hf2n : 0 ≤ (if G.Adj j i then ρ j i else 0) := by
    split_ifs
    · exact hρ.1 j i
    · exact le_rfl
  have hF : (if G.Adj i j then ρ i j else 0) + (if G.Adj j i then ρ j i else 0) ≤ flowIJ μ i j := by
    unfold flowIJ
    exact add_le_add (le_min (hf1.trans (plan_le_resP hρ i j)) (hf1.trans (plan_le_resN hρ i j)))
      (le_min (hf2.trans (plan_le_resP hρ j i)) (hf2.trans (plan_le_resN hρ j i)))
  have hri := row_at_le (G := G) hρ ({i, j} : Finset V) (u := i) hjI
  have hci := col_at_le (G := G) hρ ({i, j} : Finset V) (u := i) hjI
  have hrj := row_at_le (G := G) hρ ({i, j} : Finset V) (u := j) hiI
  have hcj := col_at_le (G := G) hρ ({i, j} : Finset V) (u := j) hiI
  have hOi : ∑ y, (if y ∉ ({i, j} : Finset V) ∧ G.Adj i y then ρ i y else 0)
      + ∑ x, (if x ∉ ({i, j} : Finset V) ∧ G.Adj x i then ρ x i else 0) ≤ oppNbr G μ i j i := by
    unfold oppNbr
    exact add_le_add (rowpart_le_opp hρ _ i) (colpart_le_opp hρ _ i)
  have hOj : ∑ y, (if y ∉ ({i, j} : Finset V) ∧ G.Adj j y then ρ j y else 0)
      + ∑ x, (if x ∉ ({i, j} : Finset V) ∧ G.Adj x j then ρ x j else 0) ≤ oppNbr G μ i j j := by
    unfold oppNbr
    exact add_le_add (rowpart_le_opp hρ _ j) (colpart_le_opp hρ _ j)
  have hmi : ∑ y, (if y ∉ ({i, j} : Finset V) ∧ G.Adj i y then ρ i y else 0)
      + ∑ x, (if x ∉ ({i, j} : Finset V) ∧ G.Adj x i then ρ x i else 0)
      ≤ min (oppNbr G μ i j i)
          (resAbs μ i j i - ((if G.Adj i j then ρ i j else 0) + (if G.Adj j i then ρ j i else 0))) := by
    refine le_min hOi ?_
    unfold resAbs
    linarith
  have hmj : ∑ y, (if y ∉ ({i, j} : Finset V) ∧ G.Adj j y then ρ j y else 0)
      + ∑ x, (if x ∉ ({i, j} : Finset V) ∧ G.Adj x j then ρ x j else 0)
      ≤ min (oppNbr G μ i j j)
          (resAbs μ i j j - ((if G.Adj i j then ρ i j else 0) + (if G.Adj j i then ρ j i else 0))) := by
    refine le_min hOj ?_
    unfold resAbs
    linarith
  have hBF := hB _ (add_nonneg hf1n hf2n) hF
  have hat : ∑ x, ∑ y, (if G.Adj x y ∧ (x ∈ ({i, j} : Finset V) ∨ y ∈ ({i, j} : Finset V))
      then ρ x y else 0) ≤ B := by
    rw [hid]
    linarith
  calc adjMass G ρ ≤ _ := hsplit
    _ ≤ B + ∑ l ∈ Finset.univ.image b,
          min (∑ x ∈ Finset.univ.filter (fun x => b x = l ∧ x ∉ ({i, j} : Finset V)), capS G μ i j x)
            (∑ y ∈ Finset.univ.filter (fun y => b y = l ∧ y ∉ ({i, j} : Finset V)), capD G μ i j y) :=
        add_le_add hat (outside_le_blocks hρ ({i, j} : Finset V) b hb)

/-- **Theorem 5.3 (iv).** The bound `η'` is at least the maximum flow `η`, so it can be taken for
`η'` in (ii) and (iii). -/
theorem tq_upper_blocks_paper {β : Type*} [DecidableEq β] (hi : OneStepAt G μ i)
    (hj : OneStepAt G μ j) (hij : i ≠ j) (b : V → β)
    (hb : ∀ x y, 0 < resP μ i j x → 0 < resN μ i j y → G.Adj x y →
      x ∉ ({i, j} : Finset V) → y ∉ ({i, j} : Finset V) → b x = b y)
    {B : ℝ} (hB : ∀ F, 0 ≤ F → F ≤ flowIJ μ i j →
      F + min (oppNbr G μ i j i) (resAbs μ i j i - F)
        + min (oppNbr G μ i j j) (resAbs μ i j j - F) ≤ B) :
    maxFlow G (resP μ i j) (resN μ i j) ≤ B + ∑ l ∈ Finset.univ.image b,
        min (∑ x ∈ Finset.univ.filter (fun x => b x = l ∧ x ∉ ({i, j} : Finset V)), capS G μ i j x)
          (∑ y ∈ Finset.univ.filter (fun y => b y = l ∧ y ∉ ({i, j} : Finset V)), capD G μ i j y) :=
  maxFlow_le (resP_nonneg μ i j) (resN_nonneg μ i j) (resP_sum_eq_resN_sum hi hj)
    fun _ hρ => adjMass_le_blocks hij hρ b hb hB

end OllivierBF
