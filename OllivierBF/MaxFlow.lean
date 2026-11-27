/-
  The `η` of Theorem 5.3 (ii) as the paper defines it: the maximum value of a flow from the vertices
  with `r > 0` to those with `r < 0` along edges of `G`, with capacities `r₊` and `r₋`.

  * `maxFlow G α β`: the supremum of the values of the flows along edges with capacities `α` and
    `β` (the partial plans that move mass only along edges, `IsEdgeFlow`); it is attained
    (`isGreatest_maxFlow`, by the compactness of `SavingsMax`);
  * `adjMass_le_maxFlow`: the edges of a coupling carry such a flow, so Theorem 5.3 (ii) holds with
    every `η' ≥ η` (`tq_upper_maxFlow_paper`);
  * `maxFlow_le`: a flow extends to a coupling that dominates it (`exists_coupling_ge`), so every
    bound on the mass that couplings move along edges is at least `η`; in particular the `η'` of
    (iv) is (`maxFlow_le_blocks_paper`).

  `tq_upper_paper` and `tq_upper_blocks_paper` (`PaperTQ`) take for `η` any bound on the mass that
  the couplings of the residuals move along edges.
-/
module

public import OllivierBF.PaperTQ
public import OllivierBF.SavingsMax

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A flow along the edges of `G` with capacities `α` and `β`: a partial plan of `α` and `β` that
moves mass only along edges. -/
def IsEdgeFlow (G : SimpleGraph V) [DecidableRel G.Adj] (α β : V → ℝ) (f : V → V → ℝ) : Prop :=
  IsSubPlan α β f ∧ ∀ x y, ¬ G.Adj x y → f x y = 0

/-- `η`: the largest value of a flow along the edges of `G` with capacities `α` and `β`. -/
noncomputable def maxFlow (G : SimpleGraph V) [DecidableRel G.Adj] (α β : V → ℝ) : ℝ :=
  sSup (mass '' {f | IsEdgeFlow G α β f})

/-- The plans that move mass only along edges form a closed set. -/
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

section flows

variable {G : SimpleGraph V} [DecidableRel G.Adj] {α β : V → ℝ}

lemma isEdgeFlow_zero (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y) :
    IsEdgeFlow G α β (fun _ _ => 0) :=
  ⟨isSubPlan_zero hα hβ, fun _ _ _ => rfl⟩

lemma bddAbove_flows : BddAbove (mass '' {f | IsEdgeFlow G α β f}) :=
  ⟨∑ x, α x, by
    rintro _ ⟨f, hf, rfl⟩
    have hf' : IsEdgeFlow G α β f := hf
    exact IsSubPlan.mass_le hf'.1⟩

/-- **`η` is a maximum**: some flow along edges has the largest value. -/
theorem isGreatest_maxFlow (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y) :
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

/-- The edges of a coupling carry a flow, so a coupling moves at most `maxFlow` along edges. -/
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

/-- Every bound on the mass that couplings move along edges is at least `maxFlow`. -/
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

/-! ### Theorem 5.3 (ii) and (iv) with `η` the maximum flow -/

section paper

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ} {μ : V → V → ℝ} {i j : V}

/-- **Theorem 5.3 (ii)**, with `η` as the paper defines it: the maximum value of a flow from the
vertices with `r > 0` to those with `r < 0` along edges, with capacities `r₊` and `r₋`, is attained,
and for every `η' ≥ η`, `κ_μ ≤ 1 − 2τ + η' − D₃`. -/
theorem tq_upper_maxFlow_paper (hd : GraphMetric G d) (h3 : ThreeApart G d)
    (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {η' : ℝ}
    (hη' : maxFlow G (resP μ i j) (resN μ i j) ≤ η') {X Y : Finset V}
    (hX : IsFarX G i j X) (hY : IsFarY G i j Y) :
    IsGreatest (mass '' {f | IsEdgeFlow G (resP μ i j) (resN μ i j) f})
        (maxFlow G (resP μ i j) (resN μ i j)) ∧
      cORm d μ i j ≤ 1 - 2 * resMass μ i j + η'
        - max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap (G := G) i j, resN μ i j y)
          (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap (G := G) i j, resP μ i j x)) :=
  ⟨isGreatest_maxFlow (resP_nonneg μ i j) (resN_nonneg μ i j),
    tq_upper_paper hd h3 hi hj (fun _ hρ => (adjMass_le_maxFlow (G := G) hρ).trans hη') hX hY⟩

/-- **Theorem 5.3 (iv)**: the `η'` of (iv), from the flow along `(i, j)`, the capacities left at `i`
and `j`, and the capped supply and demand of the blocks, is at least the maximum flow `η`. -/
theorem maxFlow_le_blocks_paper {β : Type*} [DecidableEq β] (hij : G.Adj i j)
    (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) (b : V → β)
    (hb : ∀ x y, 0 < resP μ i j x → 0 < resN μ i j y → G.Adj x y →
      x ∉ ({i, j} : Finset V) → y ∉ ({i, j} : Finset V) → b x = b y)
    {B : ℝ} (hB : ∀ F, 0 ≤ F → F ≤ flowIJ μ i j →
      F + min (oppNbr G μ i j i) (resAbs μ i j i - F)
        + min (oppNbr G μ i j j) (resAbs μ i j j - F) ≤ B) :
    maxFlow G (resP μ i j) (resN μ i j) ≤ B + ∑ l ∈ Finset.univ.image b,
        min (∑ x ∈ Finset.univ.filter (fun x => b x = l ∧ x ∉ ({i, j} : Finset V)),
            capS G μ i j x)
          (∑ y ∈ Finset.univ.filter (fun y => b y = l ∧ y ∉ ({i, j} : Finset V)),
            capD G μ i j y) :=
  maxFlow_le (resP_nonneg μ i j) (resN_nonneg μ i j) (resP_sum_eq_resN_sum hi hj)
    fun _ hρ => adjMass_le_blocks_ij hij.ne hρ b hb hB

end paper

end OllivierBF
