/-
  Proposition 4.2 of the paper as it is displayed: `κ_μ = 1 − 3τ + σ*`, where `σ*` is the maximum of
  the savings `Σ (3 − d) π` over the partial plans `π` of the residuals (nonnegative, with row sums
  at most `r₊` and column sums at most `r₋`).

  * `sigmaStar c α β`: the supremum of the savings over the partial plans of `α` and `β`;
  * `W1_eq_three_mul_sub_sigmaStar`: for any nonnegative cost that is at most `3` between the
    supports, `W₁(α, β) = 3 m − σ*`. Every partial plan extends to a coupling without losing
    savings (`exists_extension`), and every coupling is a partial plan;
  * `isGreatest_sigmaStar`: the supremum is attained, since the partial plans form a compact set
    (`exists_max_subPlan`, which `MaxFlow` uses as well);
  * `savings_max_paper`: Proposition 4.2.

  `savings_paper` (`PaperTQ`) keeps the two facts that the other results use: `κ_μ = 1 − W₁(r₊, r₋)`
  and `cost ρ = 3τ − savings ρ` for every coupling `ρ` of the residuals.
-/
module

public import OllivierBF.OneStep

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `σ*`: the supremum of the savings `Σ (3 − c) π` over the partial plans `π` of `α` and `β`. -/
noncomputable def sigmaStar (c : V → V → ℝ) (α β : V → ℝ) : ℝ :=
  sSup (savings c '' {π | IsSubPlan α β π})

section generic

variable {c : V → V → ℝ} {α β : V → ℝ}

lemma isSubPlan_zero (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y) :
    IsSubPlan α β (fun _ _ => 0) :=
  ⟨fun _ _ => le_rfl, fun x => by simpa using hα x, fun y => by simpa using hβ y⟩

lemma IsSubPlan.le_row {π : V → V → ℝ} (hπ : IsSubPlan α β π) (x y : V) : π x y ≤ α x :=
  (Finset.single_le_sum (f := fun y' => π x y') (fun y' _ => hπ.1 x y') (Finset.mem_univ y)).trans
    (hπ.2.1 x)

lemma IsSubPlan.mass_le {π : V → V → ℝ} (hπ : IsSubPlan α β π) : mass π ≤ ∑ x, α x := by
  unfold mass
  exact Finset.sum_le_sum fun x _ => hπ.2.1 x

lemma savings_le_three_mass (hc : ∀ x y, 0 ≤ c x y) {π : V → V → ℝ} (hπ : ∀ x y, 0 ≤ π x y) :
    savings c π ≤ 3 * mass π := by
  unfold savings mass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  have h := mul_nonneg (hc x y) (hπ x y)
  have e : (3 - c x y) * π x y = 3 * π x y - c x y * π x y := by ring
  rw [e]
  linarith

lemma bddAbove_savings (hc : ∀ x y, 0 ≤ c x y) :
    BddAbove (savings c '' {π | IsSubPlan α β π}) :=
  ⟨3 * ∑ x, α x, by
    rintro _ ⟨π, hπ, rfl⟩
    have hπ' : IsSubPlan α β π := hπ
    have h1 := savings_le_three_mass hc hπ'.1
    have h2 := IsSubPlan.mass_le hπ'
    linarith⟩

/-- **The savings form, for any cost.** If the cost is nonnegative and at most `3` between the
supports, `W₁(α, β) = 3 m − σ*`, with `m` the common mass. -/
theorem W1_eq_three_mul_sub_sigmaStar (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y)
    (hmass : ∑ x, α x = ∑ y, β y) (hc : ∀ x y, 0 ≤ c x y)
    (h3 : ∀ x y, 0 < α x → 0 < β y → c x y ≤ 3) :
    W1 c α β = 3 * ∑ x, α x - sigmaStar c α β := by
  obtain ⟨ρ₀, hρ₀, -⟩ := exists_piece_coupling (d := fun _ _ => (0 : ℝ)) hα hβ rfl hmass.symm
    le_rfl (fun _ _ _ _ => le_rfl)
  have hne : (savings c '' {π | IsSubPlan α β π}).Nonempty :=
    ⟨_, fun _ _ => 0, isSubPlan_zero hα hβ, rfl⟩
  unfold sigmaStar
  apply le_antisymm
  · -- a partial plan extends to a coupling that saves at least as much
    have key : ∀ s ∈ savings c '' {π | IsSubPlan α β π}, s ≤ 3 * ∑ x, α x - W1 c α β := by
      rintro _ ⟨π, hπ, rfl⟩
      have hπ' : IsSubPlan α β π := hπ
      obtain ⟨ρ, hρ, hsav⟩ := exists_extension (d := c) hπ' hmass h3
      have hW := W1_le_cost hc hρ
      have hcost := cost_eq_three_mass_sub_savings (d := c) ρ
      rw [hρ.mass_eq] at hcost
      linarith
    have := csSup_le hne key
    linarith
  · -- a coupling is a partial plan
    refine le_W1 ⟨ρ₀, hρ₀⟩ fun ρ hρ => ?_
    have hsub : IsSubPlan α β ρ := ⟨hρ.1, fun x => (hρ.2.1 x).le, fun y => (hρ.2.2 y).le⟩
    have hle := le_csSup (bddAbove_savings (α := α) (β := β) hc) ⟨ρ, hsub, rfl⟩
    have hcost := cost_eq_three_mass_sub_savings (d := c) ρ
    rw [hρ.mass_eq] at hcost
    linarith

/-! ### The supremum is attained -/

/-- The partial plans form a closed set. -/
lemma isClosed_subPlan : IsClosed {π : V → V → ℝ | IsSubPlan α β π} := by
  have hset : {π : V → V → ℝ | IsSubPlan α β π} =
      (⋂ x, ⋂ y, {π : V → V → ℝ | 0 ≤ π x y}) ∩
        ((⋂ x, {π : V → V → ℝ | ∑ y, π x y ≤ α x}) ∩ ⋂ y, {π : V → V → ℝ | ∑ x, π x y ≤ β y}) := by
    ext π
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact Iff.rfl
  rw [hset]
  exact (isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const (by fun_prop)).inter
    ((isClosed_iInter fun x => isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_iInter fun y => isClosed_le (by fun_prop) continuous_const))

/-- **Compactness.** The partial plans that satisfy a closed condition `P`, which the zero plan
satisfies, form a nonempty compact set, so a continuous function attains its maximum on them. -/
theorem exists_max_subPlan (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y)
    (P : (V → V → ℝ) → Prop) (hP : IsClosed {π | P π}) (hP0 : P fun _ _ => 0)
    (f : (V → V → ℝ) → ℝ) (hf : Continuous f) :
    ∃ π, IsSubPlan α β π ∧ P π ∧ ∀ π', IsSubPlan α β π' → P π' → f π' ≤ f π := by
  have hsub : ({π : V → V → ℝ | IsSubPlan α β π} ∩ {π | P π}) ⊆
      Set.univ.pi fun x => Set.univ.pi fun _ : V => Set.Icc (0 : ℝ) (α x) := by
    intro π hπ
    have hπS : IsSubPlan α β π := hπ.1
    rw [Set.mem_univ_pi]
    intro x
    rw [Set.mem_univ_pi]
    intro y
    exact ⟨hπS.1 x y, hπS.le_row x y⟩
  have hcomp : IsCompact ({π : V → V → ℝ | IsSubPlan α β π} ∩ {π | P π}) :=
    (isCompact_univ_pi fun x => isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset
      ((isClosed_subPlan (α := α) (β := β)).inter hP) hsub
  have hne : ({π : V → V → ℝ | IsSubPlan α β π} ∩ {π | P π}).Nonempty :=
    ⟨fun _ _ => 0, isSubPlan_zero hα hβ, hP0⟩
  obtain ⟨π, hπ, hmax⟩ := hcomp.exists_isMaxOn hne hf.continuousOn
  exact ⟨π, hπ.1, hπ.2, fun π' h1 h2 => isMaxOn_iff.mp hmax π' ⟨h1, h2⟩⟩

/-- **`σ*` is a maximum**: some partial plan has the largest savings. -/
theorem isGreatest_sigmaStar (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y) :
    IsGreatest (savings c '' {π | IsSubPlan α β π}) (sigmaStar c α β) := by
  have hcont : Continuous (savings c) := by
    show Continuous fun π : V → V → ℝ => ∑ x, ∑ y, (3 - c x y) * π x y
    fun_prop
  have hP : IsClosed {π : V → V → ℝ | True} := by
    rw [Set.ofPred_true]
    exact isClosed_univ
  obtain ⟨π, hπ, -, hmax⟩ := exists_max_subPlan hα hβ (fun _ => True) hP trivial (savings c) hcont
  have hG : IsGreatest (savings c '' {π | IsSubPlan α β π}) (savings c π) :=
    ⟨⟨π, hπ, rfl⟩, by
      rintro _ ⟨π', hπ', rfl⟩
      exact hmax π' hπ' trivial⟩
  unfold sigmaStar
  rw [hG.csSup_eq]
  exact hG

end generic

/-! ### Proposition 4.2 -/

section paper

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ} {μ : V → V → ℝ} {i j : V}

/-- `κ_μ = 1 − 3τ + σ*` for every one-step measure. -/
theorem cORm_eq_sigmaStar (hd : GraphMetric G d) (hij : G.Adj i j) (hi : OneStepAt G μ i)
    (hj : OneStepAt G μ j) :
    cORm d μ i j = 1 - 3 * resMass μ i j + sigmaStar d (resP μ i j) (resN μ i j) := by
  rw [cORm_eq_resid hd hi hj, W1_eq_three_mul_sub_sigmaStar (resP_nonneg μ i j)
    (resN_nonneg μ i j) (resP_sum_eq_resN_sum hi hj) hd.nonneg
    (fun x y hx hy => resid_dist_le_three hd hij hi hj hx hy)]
  unfold resMass
  ring

/-- **Proposition 4.2**, as the paper displays it: for every one-step measure, `σ*` is the maximum
of `Σ (3 − d) π` over the `π ≥ 0` with row sums at most `r₊` and column sums at most `r₋`, and
`κ_μ = 1 − 3τ + σ*`. -/
theorem savings_max_paper (hd : GraphMetric G d) (hij : G.Adj i j) (hi : OneStepAt G μ i)
    (hj : OneStepAt G μ j) :
    IsGreatest (savings d '' {π | IsSubPlan (resP μ i j) (resN μ i j) π})
        (sigmaStar d (resP μ i j) (resN μ i j)) ∧
      cORm d μ i j = 1 - 3 * resMass μ i j + sigmaStar d (resP μ i j) (resN μ i j) :=
  ⟨isGreatest_sigmaStar (resP_nonneg μ i j) (resN_nonneg μ i j), cORm_eq_sigmaStar hd hij hi hj⟩

end paper

end OllivierBF
