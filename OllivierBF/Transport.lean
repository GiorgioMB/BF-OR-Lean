/-
  Finite optimal transport on a finite type `V` with an arbitrary cost `d`.

  `W1 d μ ν` is the infimum of `cost d π` over couplings `π` of `μ` and `ν`.
  We never need existence of optimal couplings: every result in the paper is an
  inequality, obtained either from an explicit coupling (`W1_le_cost`) or from a
  bound valid for every coupling (`le_W1`).
-/
module

public import Mathlib

@[expose] public section

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

/-! ## Diagonal entries -/

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

end overlap

/-! ## Couplings of probability measures exist -/

lemma exists_coupling_prob {μ ν : V → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ y, 0 ≤ ν y)
    (hμ1 : ∑ x, μ x = 1) (hν1 : ∑ y, ν y = 1) : ∃ π, IsCoupling μ ν π := by
  obtain ⟨π, hπ, -⟩ := exists_piece_coupling (d := fun _ _ => (0 : ℝ)) hμ hν hμ1 hν1 le_rfl
    (fun _ _ _ _ => le_rfl)
  exact ⟨π, hπ⟩

end OllivierBF
