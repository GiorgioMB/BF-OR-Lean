/-
  The triangle–quadrangle certificate (Theorem 5.3 of the paper), for every one-step measure.

  * (i) `tq_lower`: every partial plan of the residuals, with charged distances at least the true
    ones on its support, gives `κ ≥ 1 − 3τ + Σ (3 − c) π`.
  * (ii) `tq_upper`: if `η` bounds the mass that couplings of the residuals move along edges, and
    `X₃`, `Y₃` are certified at distance `3` from the opposite residual outside `S`, then
    `κ ≤ 1 − 2τ + η − D₃`. The bound `η` can be the weight of any vertex cover of the edges between
    supply and demand (`adjMass_le_cover`), or the componentwise bound of the paper
    (`adjMass_le_blocks`). `far_of_closedX` and `far_of_closedY` certify `X₃` and `Y₃` from the
    neighbourhoods, using `ThreeApart`, which the shortest-path distance satisfies
    (`threeApart_dist`).
  * Algorithm 1 with the certificate: `certifyThenSolve_tq`.
-/
module

public import OllivierBF.OneStep
public import OllivierBF.Screening

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Mass that a plan moves along edges. -/
noncomputable def adjMass (G : SimpleGraph V) [DecidableRel G.Adj] (π : V → V → ℝ) : ℝ :=
  ∑ x, ∑ y, if G.Adj x y then π x y else 0

/-- Distinct vertices with no edge and no common neighbour are at distance at least `3`. -/
def ThreeApart (G : SimpleGraph V) (d : V → V → ℝ) : Prop :=
  ∀ x y, x ≠ y → ¬ G.Adj x y → (∀ w, ¬ (G.Adj x w ∧ G.Adj w y)) → 3 ≤ d x y

/-- `K` meets every edge between a vertex with residual supply and one with residual demand. -/
def CoversResid (G : SimpleGraph V) (μ : V → V → ℝ) (i j : V) (K : Finset V) : Prop :=
  ∀ x y, 0 < resP μ i j x → 0 < resN μ i j y → G.Adj x y → x ∈ K ∨ y ∈ K

/-- Capped supply: at most the residual supply and the residual demand of the neighbours. -/
noncomputable def capS (G : SimpleGraph V) [DecidableRel G.Adj] (μ : V → V → ℝ) (i j x : V) : ℝ :=
  min (resP μ i j x) (∑ y, if G.Adj x y then resN μ i j y else 0)

/-- Capped demand: at most the residual demand and the residual supply of the neighbours. -/
noncomputable def capD (G : SimpleGraph V) [DecidableRel G.Adj] (μ : V → V → ℝ) (i j y : V) : ℝ :=
  min (resN μ i j y) (∑ x, if G.Adj x y then resP μ i j x else 0)

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ}
variable {μ : V → V → ℝ} {i j : V} {ρ : V → V → ℝ}

/-! ### The shortest-path distance separates vertices without short paths -/

lemma threeApart_dist (hG : G.Connected) : ThreeApart G (fun x y => (G.dist x y : ℝ)) := by
  intro x y hxy hadj hcn
  obtain ⟨p, hp⟩ := (hG.preconnected x y).exists_walk_length_eq_dist
  have h3 : 3 ≤ G.dist x y := by
    by_contra h'
    have h : G.dist x y < 3 := not_le.mp h'
    rw [← hp] at h
    rcases p with _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, q⟩⟩⟩
    · exact hxy rfl
    · exact hadj h1
    · exact hcn _ ⟨h1, h2⟩
    · simp only [SimpleGraph.Walk.length_cons] at h
      omega
  show (3 : ℝ) ≤ (G.dist x y : ℝ)
  exact_mod_cast h3

/-! ### Couplings of the residuals -/

lemma resid_pos_of_plan_pos (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) {x y : V}
    (h : 0 < ρ x y) : 0 < resP μ i j x ∧ 0 < resN μ i j y := by
  constructor
  · have hle : ρ x y ≤ ∑ y', ρ x y' :=
      Finset.single_le_sum (f := fun y' => ρ x y') (fun y' _ => hρ.1 x y') (Finset.mem_univ y)
    rw [hρ.2.1 x] at hle
    linarith
  · have hle : ρ x y ≤ ∑ x', ρ x' y :=
      Finset.single_le_sum (f := fun x' => ρ x' y) (fun x' _ => hρ.1 x' y) (Finset.mem_univ x)
    rw [hρ.2.2 y] at hle
    linarith

/-- A coupling of the residuals keeps no mass in place. -/
lemma resid_plan_diag (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) (x : V) : ρ x x = 0 := by
  have h1 := hρ.diag_le x
  have h0 := hρ.1 x x
  have hmin : min (resP μ i j x) (resN μ i j x) = 0 := by
    rcases resP_eq_zero_or_resN_eq_zero μ i j x with h | h
    · rw [h]; exact min_eq_left (resN_nonneg μ i j x)
    · rw [h]; exact min_eq_right (resP_nonneg μ i j x)
  linarith

lemma sum_row_ind {α β : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling α β π) (A : Finset V) :
    ∑ x, ∑ y, (if x ∈ A then π x y else 0) = ∑ x ∈ A, α x := by
  have h : ∀ x, ∑ y, (if x ∈ A then π x y else 0) = if x ∈ A then α x else 0 := by
    intro x
    by_cases hx : x ∈ A
    · simp only [hx, ite_true]
      exact hπ.2.1 x
    · simp [hx]
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_ite_mem, Finset.univ_inter]

lemma sum_col_ind {α β : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling α β π) (B : Finset V) :
    ∑ x, ∑ y, (if y ∈ B then π x y else 0) = ∑ y ∈ B, β y := by
  rw [Finset.sum_comm]
  have h : ∀ y, ∑ x, (if y ∈ B then π x y else 0) = if y ∈ B then β y else 0 := by
    intro y
    by_cases hy : y ∈ B
    · simp only [hy, ite_true]
      exact hπ.2.2 y
    · simp [hy]
  rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_ite_mem, Finset.univ_inter]

/-- The mass from `A` that does not go to `B` is at least `α(A) − β(B)`. -/
lemma far_ge {α β : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling α β π) (A B : Finset V) :
    ∑ x ∈ A, α x - ∑ y ∈ B, β y ≤ ∑ x, ∑ y, (if x ∈ A ∧ y ∉ B then π x y else 0) := by
  rw [← sum_row_ind hπ A, ← sum_col_ind hπ B, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have h0 := hπ.1 x y
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ B <;> simp [hx, hy, h0]

/-- The mass into `A` that does not come from `B` is at least `β(A) − α(B)`. -/
lemma far_ge' {α β : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling α β π) (A B : Finset V) :
    ∑ y ∈ A, β y - ∑ x ∈ B, α x ≤ ∑ x, ∑ y, (if y ∈ A ∧ x ∉ B then π x y else 0) := by
  rw [← sum_col_ind hπ A, ← sum_row_ind hπ B, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have h0 := hπ.1 x y
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ A <;> simp [hx, hy, h0]

/-! ### Theorem 5.3 (i): the lower end -/

/-- **Theorem 5.3 (i).** Every partial plan `π` of the residuals, with charged distances `c` at least
the true ones on its support, gives `κ_μ ≥ 1 − 3τ + Σ (3 − c) π`. -/
theorem tq_lower (hd : GraphMetric G d) (hij : G.Adj i j)
    (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {π : V → V → ℝ}
    (hπ : IsSubPlan (resP μ i j) (resN μ i j) π) {c : V → V → ℝ}
    (hc : ∀ x y, 0 < π x y → d x y ≤ c x y) :
    1 - 3 * resMass μ i j + ∑ x, ∑ y, (3 - c x y) * π x y ≤ cORm d μ i j := by
  obtain ⟨ρ, hρ, hsav⟩ := exists_extension (d := d) hπ (resP_sum_eq_resN_sum hi hj)
    (fun x y hx hy => resid_dist_le_three hd hij hi hj hx hy)
  have hcs : ∑ x, ∑ y, (3 - c x y) * π x y ≤ savings d π := by
    unfold savings
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
    rcases (hπ.1 x y).eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · exact mul_le_mul_of_nonneg_right (by linarith [hc x y h0]) h0.le
  have hm : ∀ x, 0 ≤ min (μ i x) (μ j x) := fun x => le_min (hi.nonneg x) (hj.nonneg x)
  have hfull : IsCoupling (μ i) (μ j)
      (fun x y => (if x = y then min (μ i x) (μ j x) else 0) + ρ x y) :=
    ((isCoupling_diag hm).add hρ).of_marg_eq (fun x => by simp [resP]) (fun y => by simp [resN])
  have hW : W1 d (μ i) (μ j) ≤ cost d ρ := by
    calc W1 d (μ i) (μ j)
        ≤ cost d (fun x y => (if x = y then min (μ i x) (μ j x) else 0) + ρ x y) :=
          W1_le_cost hd.nonneg hfull
      _ = cost d ρ := by rw [cost_add, cost_diag hd.self, zero_add]
  have hid := savings_identity (d := d) hρ
  unfold cORm
  linarith

/-! ### Theorem 5.3 (ii): the upper end -/

/-- Pointwise bound behind the upper end: each unit costs at least `2`, `1` along an edge, and `3`
from a vertex of `X` to a demand vertex outside `S`. -/
lemma pair_bound_X (hd : GraphMetric G d) (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ)
    {X : Finset V}
    (hX : ∀ x ∈ X, ∀ y, 0 < resN μ i j y → y ∉ overlap (G := G) i j → 3 ≤ d x y) (x y : V) :
    (2 - (if G.Adj x y then 1 else 0) + (if x ∈ X ∧ y ∉ overlap (G := G) i j then 1 else 0))
        * ρ x y ≤ d x y * ρ x y := by
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
      rw [hd.adj hadj] at h3
      linarith
    rw [ite_eq_left hadj, ite_eq_right hnf, hd.adj hadj]
    norm_num
  · have hd2 := hd.two_le hxy hadj
    rw [ite_eq_right hadj]
    by_cases hf : x ∈ X ∧ y ∉ overlap (G := G) i j
    · rw [ite_eq_left hf]
      have h3 := hX x hf.1 y hyN hf.2
      linarith
    · rw [ite_eq_right hf]
      linarith

/-- The same, with the far set on the demand side. -/
lemma pair_bound_Y (hd : GraphMetric G d) (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ)
    {Y : Finset V}
    (hY : ∀ y ∈ Y, ∀ x, 0 < resP μ i j x → x ∉ overlap (G := G) i j → 3 ≤ d x y) (x y : V) :
    (2 - (if G.Adj x y then 1 else 0) + (if y ∈ Y ∧ x ∉ overlap (G := G) i j then 1 else 0))
        * ρ x y ≤ d x y * ρ x y := by
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
      rw [hd.adj hadj] at h3
      linarith
    rw [ite_eq_left hadj, ite_eq_right hnf, hd.adj hadj]
    norm_num
  · have hd2 := hd.two_le hxy hadj
    rw [ite_eq_right hadj]
    by_cases hf : y ∈ Y ∧ x ∉ overlap (G := G) i j
    · rw [ite_eq_left hf]
      have h3 := hY y hf.1 x hxP hf.2
      linarith
    · rw [ite_eq_right hf]
      linarith

/-- Summing the pointwise weights: `2·mass − (mass along edges) + (far mass)`. -/
lemma sum_weight_X (π : V → V → ℝ) (X S : Finset V) :
    ∑ x, ∑ y, (2 - (if G.Adj x y then 1 else 0) + (if x ∈ X ∧ y ∉ S then 1 else 0)) * π x y
      = 2 * mass π - adjMass G π + ∑ x, ∑ y, (if x ∈ X ∧ y ∉ S then π x y else 0) := by
  unfold mass adjMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

lemma sum_weight_Y (π : V → V → ℝ) (Y S : Finset V) :
    ∑ x, ∑ y, (2 - (if G.Adj x y then 1 else 0) + (if y ∈ Y ∧ x ∉ S then 1 else 0)) * π x y
      = 2 * mass π - adjMass G π + ∑ x, ∑ y, (if y ∈ Y ∧ x ∉ S then π x y else 0) := by
  unfold mass adjMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

/-- **Theorem 5.3 (ii).** If every coupling of the residuals moves at most `η` along edges, and the
sets `X`, `Y` are at distance `3` from the opposite residual outside `S`, then
`κ_μ ≤ 1 − 2τ + η − D₃` with `D₃ = max{0, r₊(X) − r₋(S), r₋(Y) − r₊(S)}`. -/
theorem tq_upper (hd : GraphMetric G d) (hi : OneStepAt G μ i) (hj : OneStepAt G μ j)
    {η : ℝ} (hη : ∀ ρ, IsCoupling (resP μ i j) (resN μ i j) ρ → adjMass G ρ ≤ η)
    {X Y : Finset V}
    (hX : ∀ x ∈ X, ∀ y, 0 < resN μ i j y → y ∉ overlap (G := G) i j → 3 ≤ d x y)
    (hY : ∀ y ∈ Y, ∀ x, 0 < resP μ i j x → x ∉ overlap (G := G) i j → 3 ≤ d x y) :
    cORm d μ i j ≤ 1 - 2 * resMass μ i j + η
      - max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap (G := G) i j, resN μ i j y)
        (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap (G := G) i j, resP μ i j x)) := by
  have key : ∀ ρ, IsCoupling (resP μ i j) (resN μ i j) ρ →
      2 * resMass μ i j - η
        + max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap (G := G) i j, resN μ i j y)
          (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap (G := G) i j, resP μ i j x))
        ≤ cost d ρ := by
    intro ρ hρ
    have hA := hη ρ hρ
    have hm : mass ρ = resMass μ i j := hρ.mass_eq
    have hXc : 2 * mass ρ - adjMass G ρ
        + ∑ x, ∑ y, (if x ∈ X ∧ y ∉ overlap (G := G) i j then ρ x y else 0) ≤ cost d ρ := by
      rw [← sum_weight_X (G := G) ρ X (overlap (G := G) i j)]
      unfold cost
      exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => pair_bound_X hd hρ hX x y
    have hYc : 2 * mass ρ - adjMass G ρ
        + ∑ x, ∑ y, (if y ∈ Y ∧ x ∉ overlap (G := G) i j then ρ x y else 0) ≤ cost d ρ := by
      rw [← sum_weight_Y (G := G) ρ Y (overlap (G := G) i j)]
      unfold cost
      exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => pair_bound_Y hd hρ hY x y
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
        ≤ cost d ρ - (2 * resMass μ i j - η) :=
      max_le (by linarith) (max_le (by linarith) (by linarith))
    linarith
  have hW := le_W1 (exists_resid_coupling_of hi hj) key
  rw [cORm_eq_resid hd hi hj]
  linarith

/-! ### Bounds on the mass moved along edges -/

lemma row_adj_le_capS (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) (x : V) :
    ∑ y, (if G.Adj x y then ρ x y else 0) ≤ capS G μ i j x := by
  unfold capS
  apply le_min
  · calc ∑ y, (if G.Adj x y then ρ x y else 0) ≤ ∑ y, ρ x y :=
          Finset.sum_le_sum fun y _ => by
            split_ifs
            · exact le_rfl
            · exact hρ.1 x y
      _ = resP μ i j x := hρ.2.1 x
  · refine Finset.sum_le_sum fun y _ => ?_
    split_ifs
    · calc ρ x y ≤ ∑ x', ρ x' y :=
            Finset.single_le_sum (f := fun x' => ρ x' y) (fun x' _ => hρ.1 x' y)
              (Finset.mem_univ x)
        _ = resN μ i j y := hρ.2.2 y
    · exact le_rfl

lemma col_adj_le_capD (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) (y : V) :
    ∑ x, (if G.Adj x y then ρ x y else 0) ≤ capD G μ i j y := by
  unfold capD
  apply le_min
  · calc ∑ x, (if G.Adj x y then ρ x y else 0) ≤ ∑ x, ρ x y :=
          Finset.sum_le_sum fun x _ => by
            split_ifs
            · exact le_rfl
            · exact hρ.1 x y
      _ = resN μ i j y := hρ.2.2 y
  · refine Finset.sum_le_sum fun x _ => ?_
    split_ifs
    · calc ρ x y ≤ ∑ y', ρ x y' :=
            Finset.single_le_sum (f := fun y' => ρ x y') (fun y' _ => hρ.1 x y')
              (Finset.mem_univ y)
        _ = resP μ i j x := hρ.2.1 x
    · exact le_rfl

/-- **A vertex cover bounds the mass along edges.** -/
theorem adjMass_le_cover (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) {K : Finset V}
    (hK : CoversResid G μ i j K) :
    adjMass G ρ ≤ ∑ x ∈ K, resP μ i j x + ∑ y ∈ K, resN μ i j y := by
  rw [← sum_row_ind hρ K, ← sum_col_ind hρ K, ← Finset.sum_add_distrib]
  unfold adjMass
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have h0 := hρ.1 x y
  by_cases hadj : G.Adj x y
  · rw [ite_eq_left hadj]
    rcases h0.eq_or_lt with h | h
    · rw [← h]
      split_ifs <;> linarith
    · obtain ⟨hx, hy⟩ := resid_pos_of_plan_pos hρ h
      rcases hK x y hx hy hadj with hxK | hyK
      · rw [ite_eq_left hxK]
        split_ifs <;> linarith
      · rw [ite_eq_left hyK]
        split_ifs <;> linarith
  · rw [ite_eq_right hadj]
    split_ifs <;> linarith

/-- **The componentwise bound.** Remove a set `I` of hubs (in the paper, `I = {i, j}`); if every edge
between supply and demand outside `I` joins vertices of the same block, then the mass along edges is
at most the capped flows at `I` plus, block by block, the smaller of the capped supply and the
capped demand. -/
theorem adjMass_le_blocks {β : Type*} [DecidableEq β]
    (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) (I : Finset V) (b : V → β)
    (hb : ∀ x y, 0 < resP μ i j x → 0 < resN μ i j y → G.Adj x y → x ∉ I → y ∉ I → b x = b y) :
    adjMass G ρ ≤ ∑ x ∈ I, capS G μ i j x + ∑ y ∈ I, capD G μ i j y
      + ∑ l ∈ Finset.univ.image b,
          min (∑ x ∈ Finset.univ.filter (fun x => b x = l ∧ x ∉ I), capS G μ i j x)
            (∑ y ∈ Finset.univ.filter (fun y => b y = l ∧ y ∉ I), capD G μ i j y) := by
  -- split every edge term into the parts at `I` and the part outside
  have hsplit : adjMass G ρ ≤ ∑ x, ∑ y, (if x ∈ I ∧ G.Adj x y then ρ x y else 0)
      + ∑ x, ∑ y, (if y ∈ I ∧ G.Adj x y then ρ x y else 0)
      + ∑ x, ∑ y, (if G.Adj x y ∧ x ∉ I ∧ y ∉ I then ρ x y else 0) := by
    unfold adjMass
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y _ => ?_
    have h0 := hρ.1 x y
    by_cases hadj : G.Adj x y <;> by_cases hx : x ∈ I <;> by_cases hy : y ∈ I <;>
      simp [hadj, hx, hy, h0]
  -- the parts at `I`
  have hI1 : ∑ x, ∑ y, (if x ∈ I ∧ G.Adj x y then ρ x y else 0) ≤ ∑ x ∈ I, capS G μ i j x := by
    have h : ∀ x, ∑ y, (if x ∈ I ∧ G.Adj x y then ρ x y else 0)
        ≤ if x ∈ I then capS G μ i j x else 0 := by
      intro x
      by_cases hx : x ∈ I
      · simp only [hx, true_and, ite_true]
        exact row_adj_le_capS hρ x
      · simp [hx]
    calc _ ≤ ∑ x, (if x ∈ I then capS G μ i j x else 0) := Finset.sum_le_sum fun x _ => h x
      _ = ∑ x ∈ I, capS G μ i j x := by rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hI2 : ∑ x, ∑ y, (if y ∈ I ∧ G.Adj x y then ρ x y else 0) ≤ ∑ y ∈ I, capD G μ i j y := by
    rw [Finset.sum_comm]
    have h : ∀ y, ∑ x, (if y ∈ I ∧ G.Adj x y then ρ x y else 0)
        ≤ if y ∈ I then capD G μ i j y else 0 := by
      intro y
      by_cases hy : y ∈ I
      · simp only [hy, true_and, ite_true]
        exact col_adj_le_capD hρ y
      · simp [hy]
    calc _ ≤ ∑ y, (if y ∈ I then capD G μ i j y else 0) := Finset.sum_le_sum fun y _ => h y
      _ = ∑ y ∈ I, capD G μ i j y := by rw [Finset.sum_ite_mem, Finset.univ_inter]
  -- the part outside `I`, block by block
  have hblock : ∀ x y, (if G.Adj x y ∧ x ∉ I ∧ y ∉ I then ρ x y else 0)
      = ∑ l ∈ Finset.univ.image b,
          if b x = l then (if G.Adj x y ∧ x ∉ I ∧ y ∉ I then ρ x y else 0) else 0 := by
    intro x y
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_image_of_mem b (Finset.mem_univ x)]
  have hout : ∑ x, ∑ y, (if G.Adj x y ∧ x ∉ I ∧ y ∉ I then ρ x y else 0)
      = ∑ l ∈ Finset.univ.image b, ∑ x, ∑ y,
          if b x = l then (if G.Adj x y ∧ x ∉ I ∧ y ∉ I then ρ x y else 0) else 0 := by
    calc ∑ x, ∑ y, (if G.Adj x y ∧ x ∉ I ∧ y ∉ I then ρ x y else 0)
        = ∑ x, ∑ y, ∑ l ∈ Finset.univ.image b,
            (if b x = l then (if G.Adj x y ∧ x ∉ I ∧ y ∉ I then ρ x y else 0) else 0) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hblock x y
      _ = ∑ x, ∑ l ∈ Finset.univ.image b, ∑ y,
            (if b x = l then (if G.Adj x y ∧ x ∉ I ∧ y ∉ I then ρ x y else 0) else 0) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hl : ∀ l, ∑ x, ∑ y,
      (if b x = l then (if G.Adj x y ∧ x ∉ I ∧ y ∉ I then ρ x y else 0) else 0)
      ≤ min (∑ x ∈ Finset.univ.filter (fun x => b x = l ∧ x ∉ I), capS G μ i j x)
          (∑ y ∈ Finset.univ.filter (fun y => b y = l ∧ y ∉ I), capD G μ i j y) := by
    intro l
    apply le_min
    · -- through the supply side
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun x _ => ?_
      by_cases hx : b x = l ∧ x ∉ I
      · rw [ite_eq_left hx]
        refine le_trans ?_ (row_adj_le_capS hρ x)
        refine Finset.sum_le_sum fun y _ => ?_
        have h0 := hρ.1 x y
        by_cases hc : G.Adj x y ∧ x ∉ I ∧ y ∉ I
        · simp only [ite_eq_left hx.1, ite_eq_left hc, ite_eq_left hc.1, le_refl]
        · rw [ite_eq_left hx.1, ite_eq_right hc]
          split_ifs <;> linarith
      · rw [ite_eq_right hx]
        refine le_of_eq (Finset.sum_eq_zero fun y _ => ?_)
        by_cases hbx : b x = l
        · rw [ite_eq_left hbx]
          have hxI : x ∈ I := by
            by_contra hxI
            exact hx ⟨hbx, hxI⟩
          rw [ite_eq_right (fun hc => hc.2.1 hxI)]
        · rw [ite_eq_right hbx]
    · -- through the demand side: edges outside `I` with mass stay in the block
      rw [Finset.sum_comm, Finset.sum_filter]
      refine Finset.sum_le_sum fun y _ => ?_
      by_cases hy : b y = l ∧ y ∉ I
      · rw [ite_eq_left hy]
        refine le_trans ?_ (col_adj_le_capD hρ y)
        refine Finset.sum_le_sum fun x _ => ?_
        have h0 := hρ.1 x y
        by_cases hbx : b x = l
        · rw [ite_eq_left hbx]
          by_cases hc : G.Adj x y ∧ x ∉ I ∧ y ∉ I
          · simp only [ite_eq_left hc, ite_eq_left hc.1, le_refl]
          · rw [ite_eq_right hc]
            split_ifs <;> linarith
        · rw [ite_eq_right hbx]
          split_ifs <;> linarith
      · rw [ite_eq_right hy]
        refine le_of_eq (Finset.sum_eq_zero fun x _ => ?_)
        by_cases hbx : b x = l
        · rw [ite_eq_left hbx]
          by_cases hc : G.Adj x y ∧ x ∉ I ∧ y ∉ I
          · rw [ite_eq_left hc]
            -- an edge with mass outside `I` joins vertices of one block
            rcases (hρ.1 x y).eq_or_lt with h | h
            · exact h.symm
            · obtain ⟨hx, hy'⟩ := resid_pos_of_plan_pos hρ h
              have hbb := hb x y hx hy' hc.1 hc.2.1 hc.2.2
              exact (hy ⟨hbb ▸ hbx, hc.2.2⟩).elim
          · rw [ite_eq_right hc]
        · rw [ite_eq_right hbx]
  calc adjMass G ρ
      ≤ _ := hsplit
    _ ≤ ∑ x ∈ I, capS G μ i j x + ∑ y ∈ I, capD G μ i j y
          + ∑ l ∈ Finset.univ.image b,
              min (∑ x ∈ Finset.univ.filter (fun x => b x = l ∧ x ∉ I), capS G μ i j x)
                (∑ y ∈ Finset.univ.filter (fun y => b y = l ∧ y ∉ I), capD G μ i j y) := by
        rw [hout]
        exact add_le_add (add_le_add hI1 hI2) (Finset.sum_le_sum fun l _ => hl l)

/-! ### Certifying distance `3` from the neighbourhoods -/

/-- A vertex of `U_i` without cross edges, all of whose neighbours are `i` or have no neighbour in
`U_j`, is at distance `3` from every vertex of `U_j`. -/
theorem far_of_closedX (h3 : ThreeApart G d) {x : V} (hx : x ∈ uniq G i j)
    (hnc : ∀ y ∈ uniq G j i, ¬ G.Adj x y)
    (hnb : ∀ w, G.Adj x w → w = i ∨ ∀ y ∈ uniq G j i, ¬ G.Adj w y)
    {y : V} (hy : y ∈ uniq G j i) : 3 ≤ d x y := by
  apply h3 x y
  · intro hxy
    subst hxy
    exact (mem_uniq.1 hx).2.2 (mem_uniq.1 hy).2.1
  · exact hnc y hy
  · rintro w ⟨hxw, hwy⟩
    rcases hnb w hxw with rfl | hw
    · exact (mem_uniq.1 hy).2.2 hwy
    · exact hw y hy hwy

/-- A vertex of `U_j` without cross edges, all of whose neighbours are `j` or have no neighbour in
`U_i`, is at distance `3` from every vertex of `U_i`. -/
theorem far_of_closedY (h3 : ThreeApart G d) {y : V} (hy : y ∈ uniq G j i)
    (hnc : ∀ x ∈ uniq G i j, ¬ G.Adj x y)
    (hnb : ∀ w, G.Adj y w → w = j ∨ ∀ x ∈ uniq G i j, ¬ G.Adj w x)
    {x : V} (hx : x ∈ uniq G i j) : 3 ≤ d x y := by
  apply h3 x y
  · intro hxy
    subst hxy
    exact (mem_uniq.1 hx).2.2 (mem_uniq.1 hy).2.1
  · exact hnc x hx
  · rintro w ⟨hxw, hwy⟩
    rcases hnb w hwy.symm with rfl | hw
    · exact (mem_uniq.1 hx).2.2 hxw.symm
    · exact hw x hx hxw.symm

/-- The degree certificate for `Y₃`: if `d_y = 1 + |N(y) ∩ C|` and `y ∼ j`, every neighbour of `y`
is `j` or a common neighbour. -/
lemma nbr_of_degree_eq {y : V} (hyj : G.Adj j y)
    (hdeg : G.degree y = 1 + (G.neighborFinset y ∩ common G i j).card) :
    ∀ w, G.Adj y w → w = j ∨ w ∈ common G i j := by
  intro w hw
  by_contra h'
  have h := not_or.mp h'
  have hsub : insert w (insert j (G.neighborFinset y ∩ common G i j)) ⊆ G.neighborFinset y := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hv ⊢
    rcases hv with rfl | rfl | ⟨hv, -⟩
    · exact hw
    · exact hyj.symm
    · exact hv
  have hj_notin : j ∉ G.neighborFinset y ∩ common G i j := by
    simp [mem_common, SimpleGraph.irrefl]
  have hw_notin : w ∉ insert j (G.neighborFinset y ∩ common G i j) := by
    simp only [Finset.mem_insert, Finset.mem_inter, not_or]
    exact ⟨h.1, fun hc => h.2 hc.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hw_notin, Finset.card_insert_of_notMem hj_notin,
    SimpleGraph.card_neighborFinset_eq_degree] at hcard
  omega

/-! ### Algorithm 1 with the certificate -/

/-- **Algorithm 1 with the certificate**: with any valid interval on every edge (for instance the
certificate of Theorem 5.3) and the exact curvature on the edges it leaves undecided,
certify-then-solve returns exactly the edges below the threshold. -/
theorem certifyThenSolve_tq {ι : Type*} (E : Finset ι) (lo up κ : ι → ℝ) (ϑ : ℝ)
    (hlo : ∀ e ∈ E, lo e ≤ κ e) (hup : ∀ e ∈ E, κ e ≤ up e) :
    certifyThenSolve E lo up up κ ϑ = E.filter fun e => κ e < ϑ :=
  certifyThenSolve_eq E lo up up κ ϑ hlo hup hup

end OllivierBF
