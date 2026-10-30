/-
  Exactness statements of Theorems 4.3 and 4.7 on edges with `ρ_i = ρ_j` whose cross-edge graph
  has a perfect matching (in particular on complete graphs and hypercubes). The non-lazy case
  uses the upper bound `𝔠_{OR-0} ≤ △/ρ_max` of Jost and Liu, proved here from the overlap bound,
  and the lazy case uses the coverage bound of Proposition 4.8.
  The exactness on edges that lie on no cycle of length at most five needs `d ≥ 3` between the
  two unique neighbourhoods, which `GraphMetric` does not record, and is not formalized here.
  Nothing in this file takes a published result as a hypothesis.
-/

module

public import OllivierBF.Paper

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ} {i j : V}

/-- The upper bound of Jost and Liu, `𝔠_{OR-0} ≤ △/ρ_max`: `ν_i` and `ν_j` share only the mass
`1/ρ_max` on each common neighbour, and every other unit moves at cost at least `1`. -/
theorem cOR0_le_tri_div (hd : GraphMetric G d) (hij : G.Adj i j) :
    cOR0 G d i j ≤ tri G i j / ρmax G i j := by
  have hρi := ρ_pos hij
  have hρj := ρ_pos hij.symm
  have hne : ∃ π, IsCoupling (mp G 0 i) (mp G 0 j) π :=
    exists_coupling_prob (fun x => mp_nonneg le_rfl zero_le_one i x)
      (fun x => mp_nonneg le_rfl zero_le_one j x) (mp_sum hij) (mp_sum hij.symm)
  have hov := W1_ge_overlap (d := d) hne hd.self (fun x y h => hd.one_le h)
  have hcmin : min (1 / ρ G i) (1 / ρ G j) = 1 / ρmax G i j := by
    unfold ρmax
    rcases le_total (ρ G i) (ρ G j) with h | h
    · rw [max_eq_right h, min_eq_right (one_div_le_one_div_of_le hρi h)]
    · rw [max_eq_left h, min_eq_left (one_div_le_one_div_of_le hρj h)]
  have hmin : ∀ x, min (mp G 0 i x) (mp G 0 j x)
      = if x ∈ common G i j then 1 / ρmax G i j else 0 := by
    intro x
    rw [mp0_apply, mp0_apply]
    by_cases hi : G.Adj i x
    · by_cases hj : G.Adj j x
      · have hx : x ∈ common G i j := mem_common.2 ⟨hi, hj⟩
        rw [ite_eq_left hi, ite_eq_left hj, ite_eq_left hx]
        exact hcmin
      · have hx : x ∉ common G i j := fun h => hj (mem_common.1 h).2
        rw [ite_eq_left hi, ite_eq_right hj, ite_eq_right hx]
        exact min_eq_right (one_div_nonneg.2 hρi.le)
    · have hx : x ∉ common G i j := fun h => hi (mem_common.1 h).1
      rw [ite_eq_right hi, ite_eq_right hx]
      by_cases hj : G.Adj j x
      · rw [ite_eq_left hj]
        exact min_eq_left (one_div_nonneg.2 hρj.le)
      · rw [ite_eq_right hj]
        exact min_self 0
  have hsum : ∑ x, min (mp G 0 i x) (mp G 0 j x) = tri G i j / ρmax G i j := by
    rw [Finset.sum_congr rfl (fun x _ => hmin x), Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul]
    simp only [tri]
    ring
  have hmass : ∑ x, mp G 0 i x = 1 := mp_sum hij
  unfold cOR0 cORp
  linarith

/-- **Theorem 4.3, exactness**: on an edge with `ρ_i = ρ_j` whose cross-edge graph has a perfect
matching, `𝔠_{OR-0} = L^□`. -/
theorem jl_aug_exact_of_perfect (hd : GraphMetric G d) (hij : G.Adj i j) (heq : ρ G i = ρ G j)
    (hm : matchNum G i j = (uniq G i j).card) : cOR0 G d i j = Lsq (G := G) i j := by
  have hρ := ρ_pos hij
  have hr : ρ G i / ρ G i = 1 := div_self hρ.ne'
  have hm' : (matchNum G i j : ℝ) = (uniq G i j).card := by exact_mod_cast hm
  have hU := card_uniq_real hij
  have hmax : ρmax G i j = ρ G i := by
    unfold ρmax
    rw [heq, max_self]
  have hmin : ρmin G i j = ρ G i := by
    unfold ρmin
    rw [heq, min_self]
  have hneg : jlK (G := G) i j - jlZmax (G := G) i j - matchStat G i j = -(1 / ρ G i) := by
    unfold jlK jlZmax matchStat
    rw [hmax, hm', hU, ← heq]
    linear_combination (-1 : ℝ) * hr
  have hZ : jlZmin (G := G) i j = jlZmax (G := G) i j := by
    unfold jlZmin jlZmax
    rw [hmax, hmin]
  have hneg' : jlK (G := G) i j - jlZmin (G := G) i j - matchStat G i j = -(1 / ρ G i) := by
    rw [hZ, hneg]
  have h0 : -(1 / ρ G i) ≤ 0 := by
    have := one_div_pos.2 hρ
    linarith
  have hL : Lsq (G := G) i j = tri G i j / ρmax G i j := by
    unfold Lsq
    rw [hneg, hneg', max_eq_right h0]
    unfold jlZmax
    ring
  have h1 := jl_aug hd hij
  have h2 := cOR0_le_tri_div hd hij
  linarith

/-- **Theorem 4.7, exactness**: on an edge with `ρ_i = ρ_j` whose cross-edge graph has a perfect
matching, `𝔠_OR = L^lazy`, which then equals the coverage bound `Θ`. -/
theorem lazy_quadrangle_exact_of_perfect (hd : GraphMetric G d) (hij : G.Adj i j)
    (heq : ρ G i = ρ G j) (hm : matchNum G i j = (uniq G i j).card) :
    cOR G d i j = Llazy (ρ G i) (ρ G j) (tri G i j) (matchNum G i j) := by
  have hle : ρ G i ≤ ρ G j := heq.le
  have hρ := ρ_pos hij.symm
  have hr : (ρ G j + 1) / (ρ G j + 1) = 1 := div_self (by linarith)
  have hm' : (matchNum G i j : ℝ) = (uniq G i j).card := by exact_mod_cast hm
  have hU := card_uniq_real hij
  have h1 := lazy_quadrangle hd hij hle
  have h2 := coverage_bound hd hij hle
  have key : Llazy (ρ G i) (ρ G j) (tri G i j) (matchNum G i j)
      = (2 + tri G i j) * w G j - (w G i - w G j) := by
    rw [coverage_bound_eq, hm', hU, heq]
    unfold Llazy
    linear_combination (2 : ℝ) * hr
  linarith

end OllivierBF
