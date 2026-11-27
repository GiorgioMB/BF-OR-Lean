/-
  The results of *From Proxy to Certificate: Ollivier–Ricci Bounds from the Building Blocks of
  Balanced Forman Curvature* in the form in which the paper states them, with the endpoints labelled
  so that `d_i ≤ d_j` where it matters: Proposition 4.2 and Theorem 5.3 (Theorem 5.2 is in
  `ExactRange`). Appendix B of the paper lists the correspondence. The distance-`3` certificates take
  `ThreeApart`, a property of the metric that the shortest-path distance has (`threeApart_dist`).
-/
module

public import OllivierBF.TQ

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices `X₃` of Theorem 5.3 (ii): vertices of `U_i` without cross edges, all of whose
neighbours are `i` or have no neighbour in `U_j`. (The paper's `X₃`, defined from the building
blocks, satisfies this.) -/
def IsFarX (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (X : Finset V) : Prop :=
  ∀ x ∈ X, x ∈ uniq G i j ∧ (∀ y ∈ uniq G j i, ¬ G.Adj x y) ∧
    ∀ w, G.Adj x w → w = i ∨ ∀ y ∈ uniq G j i, ¬ G.Adj w y

/-- The vertices `Y₃` of Theorem 5.3 (ii): vertices `y` of `U_j` without cross edges with
`d_y = 1 + |N(y) ∩ C|` and no neighbour in `C` adjacent to `U_i`. -/
def IsFarY (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (Y : Finset V) : Prop :=
  ∀ y ∈ Y, y ∈ uniq G j i ∧ (∀ x ∈ uniq G i j, ¬ G.Adj x y) ∧
    G.degree y = 1 + (G.neighborFinset y ∩ common G i j).card ∧
    ∀ k ∈ common G i j, G.Adj y k → ∀ x ∈ uniq G i j, ¬ G.Adj k x

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ}
variable {μ : V → V → ℝ} {i j : V}

/-- **Lemma 4.1.** For every one-step measure: no residual demand on `U_i`, no residual supply on
`U_j`, every supply–demand pair within distance `3`, and within distance `2` outside
`U_i × U_j`. -/
theorem residuals_paper (hd : GraphMetric G d) (hij : G.Adj i j)
    (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) :
    (∀ x ∈ uniq G i j, resN μ i j x = 0) ∧ (∀ y ∈ uniq G j i, resP μ i j y = 0) ∧
      (∀ x y, 0 < resP μ i j x → 0 < resN μ i j y → d x y ≤ 3) ∧
      (∀ x y, 0 < resP μ i j x → 0 < resN μ i j y →
        ¬ (x ∈ uniq G i j ∧ y ∈ uniq G j i) → d x y ≤ 2) :=
  ⟨fun _ hx => resN_eq_zero_of_uniq hi hj hx, fun _ hy => resP_eq_zero_of_uniq hi hj hy,
    fun _ _ hx hy => resid_dist_le_three hd hij hi hj hx hy,
    fun _ _ hx hy hxy => resid_dist_le_two hd hij hi hj hx hy hxy⟩

/-- **Proposition 4.2.** `κ_μ = 1 − W₁(r₊, r₋)`, and every coupling of the residuals costs `3τ` minus
its savings, so `κ_μ = 1 − 3τ + σ*`. -/
theorem savings_paper (hd : GraphMetric G d) (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) :
    cORm d μ i j = 1 - W1 d (resP μ i j) (resN μ i j) ∧
      ∀ ρ, IsCoupling (resP μ i j) (resN μ i j) ρ →
        cost d ρ = 3 * resMass μ i j - savings d ρ :=
  ⟨cORm_eq_resid hd hi hj, fun _ hρ => savings_identity hρ⟩

/-- **Theorem 5.3 (i).** -/
theorem tq_lower_paper (hd : GraphMetric G d) (hij : G.Adj i j)
    (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {π : V → V → ℝ}
    (hπ : IsSubPlan (resP μ i j) (resN μ i j) π) {c : V → V → ℝ}
    (hc : ∀ x y, 0 < π x y → d x y ≤ c x y) :
    1 - 3 * resMass μ i j + ∑ x, ∑ y, (3 - c x y) * π x y ≤ cORm d μ i j :=
  tq_lower hd hij hi hj hπ hc

/-- **Theorem 5.3 (ii)**, with `X₃` and `Y₃` given by the neighbourhoods. -/
theorem tq_upper_paper (hd : GraphMetric G d) (h3 : ThreeApart G d)
    (hi : OneStepAt G μ i) (hj : OneStepAt G μ j)
    {η : ℝ} (hη : ∀ ρ, IsCoupling (resP μ i j) (resN μ i j) ρ → adjMass G ρ ≤ η)
    {X Y : Finset V} (hX : IsFarX G i j X) (hY : IsFarY G i j Y) :
    cORm d μ i j ≤ 1 - 2 * resMass μ i j + η
      - max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap (G := G) i j, resN μ i j y)
        (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap (G := G) i j, resP μ i j x)) := by
  refine tq_upper hd hi hj hη (fun x hx y hy hyS => ?_) (fun y hy x hx hxS => ?_)
  · obtain ⟨hxU, hnc, hnb⟩ := hX x hx
    exact far_of_closedX h3 hxU hnc hnb (mem_uniq_of_resN_pos hi hj hy hyS)
  · obtain ⟨hyU, hnc, hdeg, hCk⟩ := hY y hy
    have hyj : G.Adj j y := (mem_uniq.1 hyU).2.1
    refine far_of_closedY h3 hyU hnc (fun w hw => ?_) (mem_uniq_of_resP_pos hi hj hx hxS)
    rcases nbr_of_degree_eq hyj hdeg w hw with h | h
    · exact Or.inl h
    · exact Or.inr (hCk w h hw)

/-- **Theorem 5.3 (ii) and (iv)** with the componentwise bound for `η`: for every `B` that bounds
`F + min{O_i, |r(i)| − F} + min{O_j, |r(j)| − F}` on `[0, F_ij]`, in particular its maximum, `B` plus,
over blocks that no supply–demand edge outside `{i, j}` crosses, the smaller of the capped supply and the
capped demand. -/
theorem tq_upper_blocks_paper {β : Type*} [DecidableEq β] (hd : GraphMetric G d)
    (h3 : ThreeApart G d) (hij : G.Adj i j) (hi : OneStepAt G μ i) (hj : OneStepAt G μ j)
    (b : V → β)
    (hb : ∀ x y, 0 < resP μ i j x → 0 < resN μ i j y → G.Adj x y →
      x ∉ ({i, j} : Finset V) → y ∉ ({i, j} : Finset V) → b x = b y)
    {B : ℝ} (hB : ∀ F, 0 ≤ F → F ≤ flowIJ μ i j →
      F + min (oppNbr G μ i j i) (resAbs μ i j i - F)
        + min (oppNbr G μ i j j) (resAbs μ i j j - F) ≤ B)
    {X Y : Finset V} (hX : IsFarX G i j X) (hY : IsFarY G i j Y) :
    cORm d μ i j ≤ 1 - 2 * resMass μ i j
      + (B + ∑ l ∈ Finset.univ.image b,
            min (∑ x ∈ Finset.univ.filter (fun x => b x = l ∧ x ∉ ({i, j} : Finset V)),
                capS G μ i j x)
              (∑ y ∈ Finset.univ.filter (fun y => b y = l ∧ y ∉ ({i, j} : Finset V)),
                capD G μ i j y))
      - max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap (G := G) i j, resN μ i j y)
        (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap (G := G) i j, resP μ i j x)) :=
  tq_upper_paper hd h3 hi hj (fun _ hρ => adjMass_le_blocks_ij hij.ne hρ b hb hB) hX hY

end OllivierBF
