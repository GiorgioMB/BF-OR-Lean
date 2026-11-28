/- The counting behind Theorem 5.3. -/
module

public import OllivierBF.OneStep

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The mass that a plan moves along edges. -/
noncomputable def adjMass (G : SimpleGraph V) [DecidableRel G.Adj] (π : V → V → ℝ) : ℝ :=
  ∑ x, ∑ y, if G.Adj x y then π x y else 0

/-- Distinct non-adjacent vertices without a common neighbour are at distance at least `3`. -/
def ThreeApart (G : SimpleGraph V) (d : V → V → ℝ) : Prop :=
  ∀ x y, x ≠ y → ¬ G.Adj x y → (∀ w, ¬ (G.Adj x w ∧ G.Adj w y)) → 3 ≤ d x y

/-- Capped supply: the smaller of `r₊(x)` and the demand on the neighbours of `x`. -/
noncomputable def capS (G : SimpleGraph V) [DecidableRel G.Adj] (μ : V → V → ℝ) (i j x : V) : ℝ :=
  min (resP μ i j x) (∑ y, if G.Adj x y then resN μ i j y else 0)

/-- Capped demand: the smaller of `r₋(y)` and the supply on the neighbours of `y`. -/
noncomputable def capD (G : SimpleGraph V) [DecidableRel G.Adj] (μ : V → V → ℝ) (i j y : V) : ℝ :=
  min (resN μ i j y) (∑ x, if G.Adj x y then resP μ i j x else 0)

/-- `|r(u)| = r₊(u) + r₋(u)`. -/
noncomputable def resAbs (μ : V → V → ℝ) (i j u : V) : ℝ := resP μ i j u + resN μ i j u

/-- `O_u`: the residual of the sign opposite to `r(u)` on `N(u) \ {i, j}`. -/
noncomputable def oppNbr (G : SimpleGraph V) [DecidableRel G.Adj] (μ : V → V → ℝ) (i j u : V) : ℝ :=
  (if 0 < resP μ i j u then
      ∑ y, (if y ∉ ({i, j} : Finset V) ∧ G.Adj u y then resN μ i j y else 0) else 0)
    + (if 0 < resN μ i j u then
      ∑ x, (if x ∉ ({i, j} : Finset V) ∧ G.Adj x u then resP μ i j x else 0) else 0)

/-- `F_ij = min{r₊(i), r₋(j)} + min{r₊(j), r₋(i)}`. -/
noncomputable def flowIJ (μ : V → V → ℝ) (i j : V) : ℝ :=
  min (resP μ i j i) (resN μ i j j) + min (resP μ i j j) (resN μ i j i)

variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ}
variable {μ : V → V → ℝ} {i j : V} {ρ : V → V → ℝ}

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

lemma far_ge {α β : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling α β π) (A B : Finset V) :
    ∑ x ∈ A, α x - ∑ y ∈ B, β y ≤ ∑ x, ∑ y, (if x ∈ A ∧ y ∉ B then π x y else 0) := by
  rw [← sum_row_ind hπ A, ← sum_col_ind hπ B, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have h0 := hπ.1 x y
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ B <;> simp [hx, hy, h0]

lemma far_ge' {α β : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling α β π) (A B : Finset V) :
    ∑ y ∈ A, β y - ∑ x ∈ B, α x ≤ ∑ x, ∑ y, (if y ∈ A ∧ x ∉ B then π x y else 0) := by
  rw [← sum_col_ind hπ A, ← sum_row_ind hπ B, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have h0 := hπ.1 x y
  by_cases hx : x ∈ B <;> by_cases hy : y ∈ A <;> simp [hx, hy, h0]

lemma pair_bound_X {c : V → V → ℝ} (hc1 : ∀ {x y}, G.Adj x y → c x y = 1)
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

lemma pair_bound_Y {c : V → V → ℝ} (hc1 : ∀ {x y}, G.Adj x y → c x y = 1)
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
      pair_bound_X hc1 hc2 hρ hX x y
  have hYc : 2 * mass ρ - adjMass G ρ
      + ∑ x, ∑ y, (if y ∈ Y ∧ x ∉ overlap (G := G) i j then ρ x y else 0) ≤ cost c ρ := by
    rw [← sum_weight_Y (G := G) ρ Y (overlap (G := G) i j)]
    unfold cost
    exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
      pair_bound_Y hc1 hc2 hρ hY x y
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

theorem tq_upper (hd : GraphMetric G d) (hi : OneStepAt G μ i) (hj : OneStepAt G μ j)
    {η : ℝ} (hη : ∀ ρ, IsCoupling (resP μ i j) (resN μ i j) ρ → adjMass G ρ ≤ η)
    {X Y : Finset V}
    (hX : ∀ x ∈ X, ∀ y, 0 < resN μ i j y → y ∉ overlap (G := G) i j → 3 ≤ d x y)
    (hY : ∀ y ∈ Y, ∀ x, 0 < resP μ i j x → x ∉ overlap (G := G) i j → 3 ≤ d x y) :
    cORm d μ i j ≤ 1 - 2 * resMass μ i j + η
      - max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap (G := G) i j, resN μ i j y)
        (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap (G := G) i j, resP μ i j x)) := by
  have hW := le_W1 (exists_resid_coupling_of hi hj) fun ρ hρ =>
    cost_ge_of_far (fun h => hd.adj h) (fun h h' => hd.two_le h h') hX hY hρ (hη ρ hρ)
  rw [cORm_eq_resid hd hi hj]
  linarith

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

lemma outside_le_blocks {β : Type*} [DecidableEq β]
    (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) (I : Finset V) (b : V → β)
    (hb : ∀ x y, 0 < resP μ i j x → 0 < resN μ i j y → G.Adj x y → x ∉ I → y ∉ I → b x = b y) :
    ∑ x, ∑ y, (if G.Adj x y ∧ x ∉ I ∧ y ∉ I then ρ x y else 0)
      ≤ ∑ l ∈ Finset.univ.image b,
          min (∑ x ∈ Finset.univ.filter (fun x => b x = l ∧ x ∉ I), capS G μ i j x)
            (∑ y ∈ Finset.univ.filter (fun y => b y = l ∧ y ∉ I), capD G μ i j y) := by
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
    ·
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
    ·
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
            rcases (hρ.1 x y).eq_or_lt with h | h
            · exact h.symm
            · obtain ⟨hx, hy'⟩ := resid_pos_of_plan_pos hρ h
              have hbb := hb x y hx hy' hc.1 hc.2.1 hc.2.2
              exact (hy ⟨hbb ▸ hbx, hc.2.2⟩).elim
          · rw [ite_eq_right hc]
        · rw [ite_eq_right hbx]
  rw [hout]
  exact Finset.sum_le_sum fun l _ => hl l

lemma plan_le_resP (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) (x y : V) :
    ρ x y ≤ resP μ i j x := by
  have hle : ρ x y ≤ ∑ y', ρ x y' :=
    Finset.single_le_sum (f := fun y' => ρ x y') (fun y' _ => hρ.1 x y') (Finset.mem_univ y)
  rw [hρ.2.1 x] at hle
  exact hle

lemma plan_le_resN (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) (x y : V) :
    ρ x y ≤ resN μ i j y := by
  have hle : ρ x y ≤ ∑ x', ρ x' y :=
    Finset.single_le_sum (f := fun x' => ρ x' y) (fun x' _ => hρ.1 x' y) (Finset.mem_univ x)
  rw [hρ.2.2 y] at hle
  exact hle

lemma row_at_le (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) (I : Finset V) {u w : V}
    (hw : w ∈ I) :
    (if G.Adj u w then ρ u w else 0) + ∑ y, (if y ∉ I ∧ G.Adj u y then ρ u y else 0)
      ≤ resP μ i j u := by
  have hsum : (if G.Adj u w then ρ u w else 0) = ∑ y, (if y = w ∧ G.Adj u y then ρ u y else 0) := by
    rw [Finset.sum_eq_single w]
    · simp
    · intro y _ hy
      rw [ite_eq_right (fun h : y = w ∧ G.Adj u y => hy h.1)]
    · intro h
      exact absurd (Finset.mem_univ w) h
  rw [hsum, ← Finset.sum_add_distrib, ← hρ.2.1 u]
  refine Finset.sum_le_sum fun y _ => ?_
  have h0 := hρ.1 u y
  by_cases hy : y = w
  · have hyI : y ∈ I := by rw [hy]; exact hw
    rw [ite_eq_right (fun h : y ∉ I ∧ G.Adj u y => h.1 hyI)]
    split_ifs <;> linarith
  · rw [ite_eq_right (fun h : y = w ∧ G.Adj u y => hy h.1)]
    split_ifs <;> linarith

lemma col_at_le (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) (I : Finset V) {u w : V}
    (hw : w ∈ I) :
    (if G.Adj w u then ρ w u else 0) + ∑ x, (if x ∉ I ∧ G.Adj x u then ρ x u else 0)
      ≤ resN μ i j u := by
  have hsum : (if G.Adj w u then ρ w u else 0) = ∑ x, (if x = w ∧ G.Adj x u then ρ x u else 0) := by
    rw [Finset.sum_eq_single w]
    · simp
    · intro x _ hx
      rw [ite_eq_right (fun h : x = w ∧ G.Adj x u => hx h.1)]
    · intro h
      exact absurd (Finset.mem_univ w) h
  rw [hsum, ← Finset.sum_add_distrib, ← hρ.2.2 u]
  refine Finset.sum_le_sum fun x _ => ?_
  have h0 := hρ.1 x u
  by_cases hx : x = w
  · have hxI : x ∈ I := by rw [hx]; exact hw
    rw [ite_eq_right (fun h : x ∉ I ∧ G.Adj x u => h.1 hxI)]
    split_ifs <;> linarith
  · rw [ite_eq_right (fun h : x = w ∧ G.Adj x u => hx h.1)]
    split_ifs <;> linarith

lemma rowpart_le_opp (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) (I : Finset V) (u : V) :
    ∑ y, (if y ∉ I ∧ G.Adj u y then ρ u y else 0)
      ≤ if 0 < resP μ i j u then ∑ y, (if y ∉ I ∧ G.Adj u y then resN μ i j y else 0) else 0 := by
  by_cases hp : 0 < resP μ i j u
  · rw [ite_eq_left hp]
    refine Finset.sum_le_sum fun y _ => ?_
    split_ifs
    · exact plan_le_resN hρ u y
    · exact le_rfl
  · rw [ite_eq_right hp]
    have hz : resP μ i j u = 0 := le_antisymm (not_lt.mp hp) (resP_nonneg μ i j u)
    refine le_of_eq (Finset.sum_eq_zero fun y _ => ?_)
    have h0 : ρ u y = 0 := le_antisymm (by have := plan_le_resP hρ u y; linarith) (hρ.1 u y)
    rw [h0]
    simp

lemma colpart_le_opp (hρ : IsCoupling (resP μ i j) (resN μ i j) ρ) (I : Finset V) (u : V) :
    ∑ x, (if x ∉ I ∧ G.Adj x u then ρ x u else 0)
      ≤ if 0 < resN μ i j u then ∑ x, (if x ∉ I ∧ G.Adj x u then resP μ i j x else 0) else 0 := by
  by_cases hn : 0 < resN μ i j u
  · rw [ite_eq_left hn]
    refine Finset.sum_le_sum fun x _ => ?_
    split_ifs
    · exact plan_le_resP hρ x u
    · exact le_rfl
  · rw [ite_eq_right hn]
    have hz : resN μ i j u = 0 := le_antisymm (not_lt.mp hn) (resN_nonneg μ i j u)
    refine le_of_eq (Finset.sum_eq_zero fun x _ => ?_)
    have h0 : ρ x u = 0 := le_antisymm (by have := plan_le_resN hρ x u; linarith) (hρ.1 x u)
    rw [h0]
    simp

lemma sum_sum_pair_eq (g : V → V → ℝ) (a c : V) :
    ∑ x, ∑ y, (if x = a ∧ (y = c ∧ G.Adj x y) then g x y else 0)
      = if G.Adj a c then g a c else 0 := by
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single c]
    · simp
    · intro y _ hy
      rw [ite_eq_right (fun h : a = a ∧ (y = c ∧ G.Adj a y) => hy h.2.1)]
    · intro h
      exact absurd (Finset.mem_univ c) h
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [ite_eq_right (fun h : x = a ∧ (y = c ∧ G.Adj x y) => hx h.1)]
  · intro h
    exact absurd (Finset.mem_univ a) h

lemma sum_sum_fst_eq (g : V → V → ℝ) (a : V) (A : Finset V) :
    ∑ x, ∑ y, (if x = a ∧ (y ∉ A ∧ G.Adj x y) then g x y else 0)
      = ∑ y, (if y ∉ A ∧ G.Adj a y then g a y else 0) := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [ite_eq_right (fun h : x = a ∧ (y ∉ A ∧ G.Adj x y) => hx h.1)]
  · intro h
    exact absurd (Finset.mem_univ a) h

lemma sum_sum_snd_eq (g : V → V → ℝ) (a : V) (A : Finset V) :
    ∑ x, ∑ y, (if y = a ∧ (x ∉ A ∧ G.Adj x y) then g x y else 0)
      = ∑ x, (if x ∉ A ∧ G.Adj x a then g x a else 0) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single a]
  · simp
  · intro y _ hy
    rw [ite_eq_right (fun h : y = a ∧ (x ∉ A ∧ G.Adj x y) => hy h.1)]
  · intro h
    exact absurd (Finset.mem_univ a) h

lemma ite_at_ij (hij : i ≠ j) (g : V → V → ℝ) (x y : V) :
    (if G.Adj x y ∧ (x ∈ ({i, j} : Finset V) ∨ y ∈ ({i, j} : Finset V)) then g x y else 0)
      = (if x = i ∧ (y = j ∧ G.Adj x y) then g x y else 0)
        + (if x = j ∧ (y = i ∧ G.Adj x y) then g x y else 0)
        + (if x = i ∧ (y ∉ ({i, j} : Finset V) ∧ G.Adj x y) then g x y else 0)
        + (if y = i ∧ (x ∉ ({i, j} : Finset V) ∧ G.Adj x y) then g x y else 0)
        + (if x = j ∧ (y ∉ ({i, j} : Finset V) ∧ G.Adj x y) then g x y else 0)
        + (if y = j ∧ (x ∉ ({i, j} : Finset V) ∧ G.Adj x y) then g x y else 0) := by
  have hji : j ≠ i := fun h => hij h.symm
  by_cases hxi : x = i <;> by_cases hxj : x = j <;> by_cases hyi : y = i <;> by_cases hyj : y = j <;>
    by_cases hadj : G.Adj x y <;> simp_all [Finset.mem_insert, Finset.mem_singleton]

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

end OllivierBF
