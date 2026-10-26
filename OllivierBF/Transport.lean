/-
  Finite optimal transport on a finite type `V` with an arbitrary cost `d`.

  `W1 d μ ν` is the infimum of `cost d π` over couplings `π` of `μ` and `ν`.
  We never need existence of optimal couplings: every result in the paper is an
  inequality, obtained either from an explicit coupling (`W1_le_cost`) or from a
  bound valid for every coupling (`le_W1`).
-/
import Mathlib

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `π` is a coupling (transport plan) of `μ` and `ν`. Masses need not be one. -/
def IsCoupling (μ ν : V → ℝ) (π : V → V → ℝ) : Prop :=
  (∀ x y, 0 ≤ π x y) ∧ (∀ x, ∑ y, π x y = μ x) ∧ (∀ y, ∑ x, π x y = ν y)

/-- Transport cost of a plan. -/
def cost (d : V → V → ℝ) (π : V → V → ℝ) : ℝ := ∑ x, ∑ y, d x y * π x y

/-- Wasserstein-1 distance (infimum of costs over couplings). -/
noncomputable def W1 (d : V → V → ℝ) (μ ν : V → ℝ) : ℝ :=
  sInf (cost d '' {π | IsCoupling μ ν π})

section basic

variable {d : V → V → ℝ} {μ ν : V → ℝ} {π : V → V → ℝ}

lemma cost_nonneg (hd : ∀ x y, 0 ≤ d x y) (hπ : ∀ x y, 0 ≤ π x y) : 0 ≤ cost d π :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => mul_nonneg (hd x y) (hπ x y)

lemma bddBelow_costs (hd : ∀ x y, 0 ≤ d x y) :
    BddBelow (cost d '' {π | IsCoupling μ ν π}) :=
  ⟨0, by rintro _ ⟨π, hπ, rfl⟩; exact cost_nonneg hd hπ.1⟩

/-- Any explicit coupling bounds `W1` from above. -/
theorem W1_le_cost (hd : ∀ x y, 0 ≤ d x y) (hπ : IsCoupling μ ν π) : W1 d μ ν ≤ cost d π :=
  csInf_le (bddBelow_costs hd) ⟨π, hπ, rfl⟩

/-- A bound valid for every coupling bounds `W1` from below. -/
theorem le_W1 {b : ℝ} (hne : ∃ π, IsCoupling μ ν π)
    (h : ∀ π, IsCoupling μ ν π → b ≤ cost d π) : b ≤ W1 d μ ν := by
  obtain ⟨π₀, h₀⟩ := hne
  exact le_csInf ⟨_, π₀, h₀, rfl⟩ (by rintro _ ⟨π, hπ, rfl⟩; exact h π hπ)

lemma W1_nonneg (hd : ∀ x y, 0 ≤ d x y) (hne : ∃ π, IsCoupling μ ν π) : 0 ≤ W1 d μ ν :=
  le_W1 hne fun _ hπ => cost_nonneg hd hπ.1

/-- Transposed couplings. -/
lemma IsCoupling.swap (h : IsCoupling μ ν π) : IsCoupling ν μ (fun x y => π y x) :=
  ⟨fun x y => h.1 y x, fun x => h.2.2 x, fun y => h.2.1 y⟩

lemma cost_swap (hds : ∀ x y, d x y = d y x) :
    cost d (fun x y => π y x) = cost d π := by
  unfold cost
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hds]

theorem W1_comm (hd : ∀ x y, 0 ≤ d x y) (hds : ∀ x y, d x y = d y x) :
    W1 d μ ν = W1 d ν μ := by
  have aux : ∀ μ ν : V → ℝ, (∃ π, IsCoupling μ ν π) → W1 d ν μ ≤ W1 d μ ν := by
    intro μ ν hne
    apply le_W1 hne
    intro π hπ
    calc W1 d ν μ ≤ cost d (fun x y => π y x) := W1_le_cost hd hπ.swap
      _ = cost d π := cost_swap hds
  by_cases h1 : ∃ π, IsCoupling μ ν π
  · have h2 : ∃ π, IsCoupling ν μ π := by
      obtain ⟨π, hπ⟩ := h1; exact ⟨_, hπ.swap⟩
    exact le_antisymm (aux ν μ h2) (aux μ ν h1)
  · have h2 : ¬ ∃ π, IsCoupling ν μ π := by
      rintro ⟨π, hπ⟩; exact h1 ⟨_, hπ.swap⟩
    have e1 : {π | IsCoupling μ ν π} = ∅ := by
      ext π; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => h1 ⟨π, h⟩
    have e2 : {π | IsCoupling ν μ π} = ∅ := by
      ext π; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => h2 ⟨π, h⟩
    simp only [W1, e1, e2, Set.image_empty]

end basic

/-! ## Building couplings -/

section build

variable {d : V → V → ℝ}

/-- Nonnegative combination of couplings. -/
lemma IsCoupling.combo {μ₁ ν₁ μ₂ ν₂ : V → ℝ} {π₁ π₂ : V → V → ℝ} {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (h₁ : IsCoupling μ₁ ν₁ π₁) (h₂ : IsCoupling μ₂ ν₂ π₂) :
    IsCoupling (fun x => s * μ₁ x + t * μ₂ x) (fun y => s * ν₁ y + t * ν₂ y)
      (fun x y => s * π₁ x y + t * π₂ x y) := by
  refine ⟨fun x y => add_nonneg (mul_nonneg hs (h₁.1 x y)) (mul_nonneg ht (h₂.1 x y)), ?_, ?_⟩
  · intro x
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h₁.2.1 x, h₂.2.1 x]
  · intro y
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h₁.2.2 y, h₂.2.2 y]

lemma cost_combo (π₁ π₂ : V → V → ℝ) (s t : ℝ) :
    cost d (fun x y => s * π₁ x y + t * π₂ x y) = s * cost d π₁ + t * cost d π₂ := by
  unfold cost
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- Sum of couplings (the `s = t = 1` case, stated with plain addition). -/
lemma IsCoupling.add {μ₁ ν₁ μ₂ ν₂ : V → ℝ} {π₁ π₂ : V → V → ℝ}
    (h₁ : IsCoupling μ₁ ν₁ π₁) (h₂ : IsCoupling μ₂ ν₂ π₂) :
    IsCoupling (fun x => μ₁ x + μ₂ x) (fun y => ν₁ y + ν₂ y) (fun x y => π₁ x y + π₂ x y) := by
  simpa using IsCoupling.combo zero_le_one zero_le_one h₁ h₂

lemma cost_add (π₁ π₂ : V → V → ℝ) :
    cost d (fun x y => π₁ x y + π₂ x y) = cost d π₁ + cost d π₂ := by
  simpa using cost_combo (d := d) π₁ π₂ 1 1

/-- Measures with nonnegative entries and zero mass vanish. -/
lemma eq_zero_of_sum_eq_zero {μ : V → ℝ} (hμ : ∀ x, 0 ≤ μ x) (h : ∑ x, μ x = 0) (x : V) :
    μ x = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hμ x)).1 h x (Finset.mem_univ x)

/-- Product coupling of two pieces of equal mass `M`, with a cost bound by the
largest distance between their supports. Works also for `M = 0`. -/
theorem exists_piece_coupling {μ ν : V → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    {M D : ℝ} (hμM : ∑ x, μ x = M) (hνM : ∑ y, ν y = M) (_hD : 0 ≤ D)
    (hdist : ∀ x y, 0 < μ x → 0 < ν y → d x y ≤ D) :
    ∃ π, IsCoupling μ ν π ∧ cost d π ≤ D * M := by
  rcases (show 0 ≤ M from hμM ▸ Finset.sum_nonneg fun x _ => hμ x).eq_or_lt with hM | hM
  · -- zero mass: the zero plan
    subst hM
    refine ⟨fun _ _ => 0, ⟨fun _ _ => le_rfl, fun x => ?_, fun y => ?_⟩, ?_⟩
    · simp [eq_zero_of_sum_eq_zero hμ hμM x]
    · simp [eq_zero_of_sum_eq_zero hν hνM y]
    · simp [cost]
  · have hM0 : M ≠ 0 := hM.ne'
    refine ⟨fun x y => μ x * ν y / M,
      ⟨fun x y => div_nonneg (mul_nonneg (hμ x) (hν y)) hM.le, fun x => ?_, fun y => ?_⟩, ?_⟩
    · calc ∑ y, μ x * ν y / M = μ x * (∑ y, ν y) / M := by
              rw [Finset.mul_sum, Finset.sum_div]
        _ = μ x := by rw [hνM]; field_simp
    · calc ∑ x, μ x * ν y / M = (∑ x, μ x) * ν y / M := by
              rw [Finset.sum_mul, Finset.sum_div]
        _ = ν y := by rw [hμM]; field_simp
    · unfold cost
      calc ∑ x, ∑ y, d x y * (μ x * ν y / M)
          ≤ ∑ x, ∑ y, D * (μ x * ν y / M) := by
            refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
            rcases (hμ x).eq_or_lt with h0 | h0
            · rw [← h0]; simp
            rcases (hν y).eq_or_lt with h1 | h1
            · rw [← h1]; simp
            exact mul_le_mul_of_nonneg_right (hdist x y h0 h1) (by positivity)
        _ = D / M * ((∑ x, μ x) * (∑ y, ν y)) := by
            rw [Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            ring
        _ = D * M := by rw [hμM, hνM]; field_simp

/-- Identity (diagonal) coupling of `κ` with itself: zero cost when `d x x = 0`. -/
lemma isCoupling_diag {κ : V → ℝ} (hκ : ∀ x, 0 ≤ κ x) :
    IsCoupling κ κ (fun x y => if x = y then κ x else 0) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun y => ?_⟩
  · show 0 ≤ (if x = y then κ x else 0)
    split_ifs
    · exact hκ x
    · exact le_rfl
  · simp [Finset.sum_ite_eq]
  · simp [Finset.sum_ite_eq']

lemma cost_diag {κ : V → ℝ} (hself : ∀ x, d x x = 0) :
    cost d (fun x y => if x = y then κ x else 0) = 0 := by
  unfold cost
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
  show d x y * (if x = y then κ x else 0) = 0
  split_ifs with h
  · subst h; simp [hself]
  · simp

end build

/-! ## Joint convexity -/

section mix

variable {d : V → V → ℝ}

/-- `W1` is jointly convex (convex combination of two pairs). -/
theorem W1_mix_le (hd : ∀ x y, 0 ≤ d x y) {μ₁ ν₁ μ₂ ν₂ : V → ℝ} {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h₁ : ∃ π, IsCoupling μ₁ ν₁ π) (h₂ : ∃ π, IsCoupling μ₂ ν₂ π) :
    W1 d (fun x => (1 - θ) * μ₁ x + θ * μ₂ x) (fun y => (1 - θ) * ν₁ y + θ * ν₂ y)
      ≤ (1 - θ) * W1 d μ₁ ν₁ + θ * W1 d μ₂ ν₂ := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  have hne₁ : (cost d '' {π | IsCoupling μ₁ ν₁ π}).Nonempty := by
    obtain ⟨π, hπ⟩ := h₁; exact ⟨_, π, hπ, rfl⟩
  have hne₂ : (cost d '' {π | IsCoupling μ₂ ν₂ π}).Nonempty := by
    obtain ⟨π, hπ⟩ := h₂; exact ⟨_, π, hπ, rfl⟩
  obtain ⟨_, ⟨π₁, hπ₁, rfl⟩, hlt₁⟩ := exists_lt_of_csInf_lt hne₁ (lt_add_of_pos_right (W1 d μ₁ ν₁) hε)
  obtain ⟨_, ⟨π₂, hπ₂, rfl⟩, hlt₂⟩ := exists_lt_of_csInf_lt hne₂ (lt_add_of_pos_right (W1 d μ₂ ν₂) hε)
  have hc := IsCoupling.combo (sub_nonneg.2 hθ1) hθ0 hπ₁ hπ₂
  calc W1 d _ _ ≤ cost d (fun x y => (1 - θ) * π₁ x y + θ * π₂ x y) := W1_le_cost hd hc
    _ = (1 - θ) * cost d π₁ + θ * cost d π₂ := cost_combo π₁ π₂ _ _
    _ < (1 - θ) * W1 d μ₁ ν₁ + θ * W1 d μ₂ ν₂ + ε := by
      rcases hθ0.eq_or_lt with h0 | h0
      · subst h0; simp only [sub_zero, one_mul, zero_mul, add_zero]; linarith
      rcases hθ1.eq_or_lt with h1 | h1
      · subst h1; simp only [sub_self, zero_mul, zero_add, one_mul]; linarith
      nlinarith [mul_lt_mul_of_pos_left hlt₁ (sub_pos.2 h1), mul_lt_mul_of_pos_left hlt₂ h0]

end mix

/-! ## The overlap lower bound (`W1 ≥ mass not shared`) -/

section overlap

variable {d : V → V → ℝ}

/-- Diagonal entries of a coupling are bounded by both marginals. -/
lemma IsCoupling.diag_le {μ ν : V → ℝ} {π : V → V → ℝ} (h : IsCoupling μ ν π) (x : V) :
    π x x ≤ min (μ x) (ν x) := by
  refine le_min ?_ ?_
  · rw [← h.2.1 x]
    exact Finset.single_le_sum (f := fun y => π x y) (fun y _ => h.1 x y) (Finset.mem_univ x)
  · rw [← h.2.2 x]
    exact Finset.single_le_sum (f := fun y => π y x) (fun y _ => h.1 y x) (Finset.mem_univ x)

/-- Every coupling costs at least its off-diagonal mass when distinct points are at
distance at least one. -/
lemma cost_ge_offdiag {μ ν : V → ℝ} {π : V → V → ℝ} (h : IsCoupling μ ν π)
    (hself : ∀ x, d x x = 0) (hone : ∀ x y, x ≠ y → 1 ≤ d x y) :
    ∑ x, (μ x - π x x) ≤ cost d π := by
  unfold cost
  refine Finset.sum_le_sum fun x _ => ?_
  have h1 : π x x + ∑ y ∈ univ.erase x, π x y = ∑ y, π x y :=
    Finset.add_sum_erase _ (fun y => π x y) (Finset.mem_univ x)
  have h2 : d x x * π x x + ∑ y ∈ univ.erase x, d x y * π x y = ∑ y, d x y * π x y :=
    Finset.add_sum_erase _ (fun y => d x y * π x y) (Finset.mem_univ x)
  have h3 : ∑ y ∈ univ.erase x, π x y ≤ ∑ y ∈ univ.erase x, d x y * π x y :=
    Finset.sum_le_sum fun y hy => by
      have hxy : x ≠ y := fun e => (Finset.mem_erase.1 hy).1 e.symm
      nlinarith [hone x y hxy, h.1 x y]
  rw [hself x, zero_mul, zero_add] at h2
  linarith [h.2.1 x]

/-- `W1(μ,ν) ≥ m − Σ min(μ,ν)` for measures of mass `m` (here `m = Σ μ`). -/
theorem W1_ge_overlap {μ ν : V → ℝ} (hne : ∃ π, IsCoupling μ ν π)
    (hself : ∀ x, d x x = 0) (hone : ∀ x y, x ≠ y → 1 ≤ d x y) :
    ∑ x, μ x - ∑ x, min (μ x) (ν x) ≤ W1 d μ ν := by
  apply le_W1 hne
  intro π hπ
  calc ∑ x, μ x - ∑ x, min (μ x) (ν x) = ∑ x, (μ x - min (μ x) (ν x)) := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ x, (μ x - π x x) := Finset.sum_le_sum fun x _ => by linarith [hπ.diag_le x]
    _ ≤ cost d π := cost_ge_offdiag hπ hself hone

end overlap

/-! ## Couplings of probability measures exist -/

lemma exists_coupling_prob {μ ν : V → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (hμ1 : ∑ x, μ x = 1) (hν1 : ∑ y, ν y = 1) : ∃ π, IsCoupling μ ν π := by
  obtain ⟨π, hπ, -⟩ := exists_piece_coupling (d := fun _ _ => (0 : ℝ)) hμ hν hμ1 hν1 le_rfl
    (fun _ _ _ _ => le_rfl)
  exact ⟨π, hπ⟩

end OllivierBF
