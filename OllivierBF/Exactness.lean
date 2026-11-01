/-
  The Jost–Liu upper bound `κ_0 ≤ t_{ij}/b`, and the exactness of Theorems 4.3 and 4.7 on every
  edge with `a = b` whose cross-edge graph has a perfect matching (`M_{ij} = |U_i|`).

  The exactness on edges that lie on no cycle of length at most 5 is not formalized: its proof
  needs lower bounds of 3 on distances, which `GraphMetric` does not record. Nothing in this file
  takes a published result as a hypothesis.
-/
module

public import OllivierBF.Paper

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ} {i j : V}

/-- **Theorem 4.3, the Jost–Liu upper bound**: `κ_0 ≤ t_{ij}/d_j`, which is `t_{ij}/b` for
`d_i ≤ d_j`. The measures `ν_i` and `ν_j` share at most `1/d_j` at each common neighbour and
nothing elsewhere, and every unit that is not shared travels a distance of at least 1. -/
theorem cOR0_le_tri_div (hd : GraphMetric G d) (hij : G.Adj i j) :
    cOR0 G d i j ≤ tri G i j / ρ G j := by
  have hne : ∃ π, IsCoupling (mp G 0 i) (mp G 0 j) π :=
    exists_coupling_prob (mp_nonneg le_rfl zero_le_one i) (mp_nonneg le_rfl zero_le_one j)
      (mp_sum hij) (mp_sum hij.symm)
  have hW := W1_ge_overlap hne hd.self (fun x y h => hd.one_le h)
  rw [mp_sum hij] at hW
  have hpt : ∀ x, min (mp G 0 i x) (mp G 0 j x)
      ≤ if x ∈ common G i j then 1 / ρ G j else 0 := by
    intro x
    rw [mp0_apply, mp0_apply]
    by_cases hx : x ∈ common G i j
    · rw [ite_eq_left hx, ite_eq_left (mem_common.1 hx).2]
      exact min_le_right _ _
    · rw [ite_eq_right hx]
      by_cases hix : G.Adj i x
      · rw [ite_eq_right (show ¬ G.Adj j x from fun hjx => hx (mem_common.2 ⟨hix, hjx⟩))]
        exact min_le_right _ _
      · rw [ite_eq_right hix]
        exact min_le_left _ _
  have hsum : ∑ x, min (mp G 0 i x) (mp G 0 j x) ≤ tri G i j / ρ G j := by
    calc ∑ x, min (mp G 0 i x) (mp G 0 j x)
        ≤ ∑ x, (if x ∈ common G i j then 1 / ρ G j else 0) :=
          Finset.sum_le_sum fun x _ => hpt x
      _ = tri G i j / ρ G j := by
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
          simp only [tri]
          ring
  unfold cOR0 cORp
  linarith

/-- **Theorem 4.3, exactness**: on an edge with `a = b` whose cross-edge graph has a perfect
matching, both arguments of the positive parts in `L^□_{ij}` equal `−1/a`, so
`κ_0 = L^□_{ij} = t_{ij}/b`, the Jost–Liu upper bound. -/
theorem jl_aug_exact_of_perfect (hd : GraphMetric G d) (hij : G.Adj i j)
    (heq : ρ G i = ρ G j) (hM : matchNum G i j = (uniq G i j).card) :
    cOR0 G d i j = Lsq (G := G) i j ∧ Lsq (G := G) i j = tri G i j / ρ G j := by
  have hρj := ρ_pos hij.symm
  have hr : ρ G j * (ρ G j)⁻¹ = 1 := mul_inv_cancel₀ hρj.ne'
  have hMr : (matchNum G i j : ℝ) = ρ G i - 1 - tri G i j := by
    rw [hM]; exact card_uniq_real hij
  have hmax : ρmax G i j = ρ G j := ρmax_eq heq.le
  have hmin : ρmin G i j = ρ G i := ρmin_eq heq.le
  have hA : jlK (G := G) i j - jlZmax (G := G) i j - matchStat G i j = -(1 / ρ G j) := by
    unfold jlK jlZmax matchStat
    rw [hmax, hMr, heq]
    simp only [div_eq_mul_inv]
    linear_combination -hr
  have hB : jlK (G := G) i j - jlZmin (G := G) i j - matchStat G i j = -(1 / ρ G j) := by
    unfold jlK jlZmin matchStat
    rw [hmax, hmin, hMr, heq]
    simp only [div_eq_mul_inv]
    linear_combination -hr
  have hneg : -(1 / ρ G j) ≤ 0 := by
    have := one_div_pos.2 hρj
    linarith
  have hL : Lsq (G := G) i j = tri G i j / ρ G j := by
    unfold Lsq
    rw [hA, hB, max_eq_right hneg]
    unfold jlZmax
    rw [hmax]
    ring
  exact ⟨le_antisymm ((cOR0_le_tri_div hd hij).trans hL.symm.le) (jl_aug hd hij), hL⟩

/-- **Theorem 4.7, exactness**: on an edge with `a = b` whose cross-edge graph has a perfect
matching, `Δ = R_{ij} = 0`, so `L^lazy_{ij}` equals the coverage bound `Θ_{ij}` of
Proposition 4.10, and `κ_OR = L^lazy_{ij}`. -/
theorem lazy_quadrangle_exact_of_perfect (hd : GraphMetric G d) (hij : G.Adj i j)
    (heq : ρ G i = ρ G j) (hM : matchNum G i j = (uniq G i j).card) :
    cOR G d i j = Llazy (ρ G i) (ρ G j) (tri G i j) (matchNum G i j) := by
  have hρj := ρ_pos hij.symm
  have hr : (ρ G j + 1) * (ρ G j + 1)⁻¹ = 1 :=
    mul_inv_cancel₀ (show (0 : ℝ) < ρ G j + 1 by linarith).ne'
  have hMr : (matchNum G i j : ℝ) = ρ G i - 1 - tri G i j := by
    rw [hM]; exact card_uniq_real hij
  have hval : Llazy (ρ G i) (ρ G j) (tri G i j) (matchNum G i j)
      = (2 + tri G i j) * w G j - (w G i - w G j) := by
    rw [hMr]
    unfold Llazy w
    rw [heq]
    simp only [div_eq_mul_inv]
    linear_combination 2 * hr
  have hlo := lazy_quadrangle hd hij heq.le
  have hup := coverage_bound hd hij heq.le
  rw [hval] at hlo ⊢
  exact le_antisymm hup hlo

end OllivierBF
