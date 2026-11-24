/-
  The BF quantities `S`, `T`, `□_{ij}` in the notation of `Algebra.lean`, and the budget behind
  Lemma 5.6. Convention throughout: `d_i ≤ d_j`, so `a = d_i` and `b = d_j`.
-/
module

public import OllivierBF.Bounds

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ} {i j : V}

/-! ### Identifying the BF components with the abstract ones -/

lemma ρmax_eq (hle : ρ G i ≤ ρ G j) : ρmax G i j = ρ G j := max_eq_right hle
lemma ρmin_eq (hle : ρ G i ≤ ρ G j) : ρmin G i j = ρ G i := min_eq_left hle

lemma bfS_eq : bfS G i j = bS (ρ G i) (ρ G j) := rfl

lemma bfT_eq (hle : ρ G i ≤ ρ G j) : bfT G i j = bT (ρ G i) (ρ G j) := by
  unfold bfT bT; rw [ρmax_eq hle, ρmin_eq hle]

lemma ρmax_pos (hij : G.Adj i j) : 0 < ρmax G i j := lt_max_of_lt_left (ρ_pos hij)
lemma ρmin_pos (hij : G.Adj i j) : 0 < ρmin G i j := lt_min (ρ_pos hij) (ρ_pos hij.symm)

lemma bfT_pos' (hij : G.Adj i j) : 0 < bfT G i j :=
  add_pos (div_pos two_pos (ρmax_pos hij)) (div_pos one_pos (ρmin_pos hij))

lemma C4_nonneg (hij : G.Adj i j) : 0 ≤ C4 G i j := by
  unfold C4
  split_ifs
  · exact le_rfl
  · exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (ρmax_pos hij).le)

/-! ### Lemma 5.6: the triangle cap `t_max` and the 4-cycle budget -/

/-- `min{a − 1, β(ζ)/T}`, the real bound on the triangle count; its floor is `t_max(ζ)`. -/
noncomputable def triMax (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (ζ : ℝ) : ℝ :=
  min (ρ G i - 1) (max (ζ - bfS G i j) 0 / bfT G i j)

/-- If `γ_max = 0` there are no cross edges, so `Ξ = 0`. -/
lemma Xi_eq_zero_of_varpi (h : varpi G i j = 0) : Xi G i j = 0 := by
  have h1 : (uniq G i j).sup (fun k => boxClose G k i j) = 0 := by
    have := le_max_left ((uniq G i j).sup fun k => boxClose G k i j)
      ((uniq G j i).sup fun w => boxClose G w j i)
    unfold varpi at h; omega
  have h2 : (uniq G j i).sup (fun w => boxClose G w j i) = 0 := by
    have := le_max_right ((uniq G i j).sup fun k => boxClose G k i j)
      ((uniq G j i).sup fun w => boxClose G w j i)
    unfold varpi at h; omega
  have e1 : (xi G i j).card = 0 := by
    by_contra hne
    obtain ⟨k, hk⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
    obtain ⟨hkU, w, hw, hadj⟩ := Finset.mem_filter.1 hk
    have hle : boxClose G k i j ≤ 0 := h1 ▸ Finset.le_sup (f := fun k => boxClose G k i j) hkU
    have hpos : 0 < boxClose G k i j :=
      Finset.card_pos.2 ⟨w, Finset.mem_inter.2 ⟨(G.mem_neighborFinset k w).2 hadj, hw⟩⟩
    omega
  have e2 : (xi G j i).card = 0 := by
    by_contra hne
    obtain ⟨k, hk⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hne)
    obtain ⟨hkU, w, hw, hadj⟩ := Finset.mem_filter.1 hk
    have hle : boxClose G k j i ≤ 0 := h2 ▸ Finset.le_sup (f := fun w => boxClose G w j i) hkU
    have hpos : 0 < boxClose G k j i :=
      Finset.card_pos.2 ⟨w, Finset.mem_inter.2 ⟨(G.mem_neighborFinset k w).2 hadj, hw⟩⟩
    omega
  unfold Xi; rw [e1, e2]

/-- `Ξ ≤ b(b − 1)(β(ζ) − T t_{ij})` under the BF hypothesis (from `□_{ij} ≥ Ξ/(b(b − 1))`). -/
lemma Xi_le_budget (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) (h2 : 2 ≤ ρ G i) {ζ : ℝ}
    (hζ : cBF G i j ≤ ζ) :
    (Xi G i j : ℝ) ≤ ρ G j * (ρ G j - 1) * (max (ζ - bfS G i j) 0 - bfT G i j * tri G i j) := by
  have hmin : ¬ ρmin G i j ≤ 1 := by rw [ρmin_eq hle]; linarith
  have hbf : bfS G i j + bfT G i j * tri G i j + C4 G i j ≤ ζ := by
    unfold cBF at hζ; rwa [ite_eq_right hmin] at hζ
  have hsho : 0 ≤ ρ G j * (ρ G j - 1) := mul_nonneg (by linarith) (by linarith)
  by_cases hv : varpi G i j = 0
  · rw [Xi_eq_zero_of_varpi hv]
    have hC : C4 G i j = 0 := by unfold C4; rw [ite_eq_left hv]
    rw [hC] at hbf
    have : 0 ≤ max (ζ - bfS G i j) 0 - bfT G i j * tri G i j := by
      have := le_max_left (ζ - bfS G i j) 0; linarith
    push_cast; exact mul_nonneg hsho this
  · have hv1 : (1 : ℝ) ≤ varpi G i j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hv
    have hvle := varpi_le hij
    rw [show max (ρ G i) (ρ G j) = ρ G j from max_eq_right hle] at hvle
    have hden : 0 < (varpi G i j : ℝ) * ρmax G i j :=
      mul_pos (by linarith) (ρmax_pos hij)
    have hC : C4 G i j = (Xi G i j : ℝ) / ((varpi G i j : ℝ) * ρmax G i j) := by
      unfold C4; rw [ite_eq_right hv]
    -- `Ξ = □_{ij} γ_max b ≤ □_{ij} b(b − 1)`
    have hXi : (Xi G i j : ℝ) = C4 G i j * ((varpi G i j : ℝ) * ρmax G i j) := by
      rw [hC, div_mul_cancel₀ _ hden.ne']
    have hC0 : 0 ≤ C4 G i j := C4_nonneg hij
    have hle' : (varpi G i j : ℝ) * ρmax G i j ≤ ρ G j * (ρ G j - 1) := by
      rw [ρmax_eq hle]
      have := ρ_pos (G := G) hij.symm
      nlinarith [mul_le_mul_of_nonneg_right hvle this.le]
    have hbud : C4 G i j ≤ max (ζ - bfS G i j) 0 - bfT G i j * tri G i j := by
      have := le_max_left (ζ - bfS G i j) 0; linarith
    rw [hXi]
    calc C4 G i j * ((varpi G i j : ℝ) * ρmax G i j) ≤ C4 G i j * (ρ G j * (ρ G j - 1)) :=
          mul_le_mul_of_nonneg_left hle' hC0
      _ ≤ (max (ζ - bfS G i j) 0 - bfT G i j * tri G i j) * (ρ G j * (ρ G j - 1)) :=
          mul_le_mul_of_nonneg_right hbud hsho
      _ = _ := by ring

end OllivierBF
