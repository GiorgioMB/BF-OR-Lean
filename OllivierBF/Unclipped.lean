/-
  Proposition 5.1 of the paper (BF as an unclipped Jost–Liu bound), parts (ii) and (iii). Part (i)
  is `bf_is_third_piece` in `Bounds.lean`.

  `bfA` and `bfB` are the BF deficits `A^BF_{ij}` and `B^BF_{ij}`: the arguments `A^□_{ij}` and
  `B^□_{ij}` of the positive parts in `L^□_{ij}` (`Lsq`) with `σ_{ij}` replaced by `□_{ij}/2`.
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

/-- The BF deficit `A^BF_{ij} = 1 − 1/a − 1/b − t_{ij}/b − □_{ij}/2`. -/
noncomputable def bfA (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) : ℝ :=
  jlK (G := G) i j - jlZmax (G := G) i j - C4 G i j / 2

/-- The BF deficit `B^BF_{ij} = 1 − 1/a − 1/b − t_{ij}/a − □_{ij}/2`. -/
noncomputable def bfB (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) : ℝ :=
  jlK (G := G) i j - jlZmin (G := G) i j - C4 G i j / 2

/-- `L^BF_{ij} = t_{ij}/b − [A^BF_{ij}]₊ − [B^BF_{ij}]₊` of Proposition 5.1 (ii). -/
noncomputable def LBF (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) : ℝ :=
  jlZmax (G := G) i j - max (bfA G i j) 0 - max (bfB G i j) 0

/-- `[x]₊ − [−x]₊ = x`. -/
lemma pos_part_sub_neg_part (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (show (0 : ℝ) ≤ -x by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (show -x ≤ 0 by linarith)]; ring

/-- **Proposition 5.1 (ii), the identity**: for `a ≥ 2`,
`L^BF_{ij} = κ_BF − [−A^BF_{ij}]₊ − [−B^BF_{ij}]₊`. -/
theorem LBF_eq (hij : G.Adj i j) (h2 : 2 ≤ ρmin G i j) :
    LBF G i j = cBF G i j - max (-bfA G i j) 0 - max (-bfB G i j) 0 := by
  have h := bf_is_third_piece hij (fun h1 => by linarith)
  have hA := pos_part_sub_neg_part (bfA G i j)
  have hB := pos_part_sub_neg_part (bfB G i j)
  have eA : bfA G i j = jlK (G := G) i j - jlZmax (G := G) i j - C4 G i j / 2 := rfl
  have eB : bfB G i j = jlK (G := G) i j - jlZmin (G := G) i j - C4 G i j / 2 := rfl
  have eL : LBF G i j = jlZmax (G := G) i j - max (bfA G i j) 0 - max (bfB G i j) 0 := rfl
  linarith

/-- **Proposition 5.1 (ii)**: `L^BF_{ij} ≤ L^□_{ij}`, because `□_{ij}/2 ≤ σ_{ij}` (Lemma 3.6) and
`L^□_{ij}` is nondecreasing in `σ_{ij}`. -/
theorem LBF_le_Lsq (hij : G.Adj i j) : LBF G i j ≤ Lsq (G := G) i j := by
  have h4 := C4_le_two_matchStat hij
  have e1 : max (jlK (G := G) i j - jlZmax (G := G) i j - matchStat G i j) 0
      ≤ max (bfA G i j) 0 :=
    max_le_max (by unfold bfA; linarith) le_rfl
  have e2 : max (jlK (G := G) i j - jlZmin (G := G) i j - matchStat G i j) 0
      ≤ max (bfB G i j) 0 :=
    max_le_max (by unfold bfB; linarith) le_rfl
  have eL : LBF G i j = jlZmax (G := G) i j - max (bfA G i j) 0 - max (bfB G i j) 0 := rfl
  have eS : Lsq (G := G) i j =
      -max (jlK (G := G) i j - jlZmax (G := G) i j - matchStat G i j) 0
      - max (jlK (G := G) i j - jlZmin (G := G) i j - matchStat G i j) 0
      + jlZmax (G := G) i j := rfl
  linarith

/-- **Proposition 5.1 (ii), the excess bound** (eq. `bf-excess`): for `a ≥ 2`,
`κ_BF − κ_0 ≤ [−A^BF_{ij}]₊ + [−B^BF_{ij}]₊`. -/
theorem bf_excess (hd : GraphMetric G d) (hij : G.Adj i j) (h2 : 2 ≤ ρmin G i j) :
    cBF G i j - cOR0 G d i j ≤ max (-bfA G i j) 0 + max (-bfB G i j) 0 := by
  have h1 := LBF_eq hij h2
  have h3 := LBF_le_Lsq hij
  have h4 := jl_aug hd hij
  linarith

/-- **Proposition 5.1 (iii)**: `B^BF_{ij} ≤ A^BF_{ij}`, since `t_{ij}/b ≤ t_{ij}/a`. -/
theorem bfB_le_bfA (hij : G.Adj i j) : bfB G i j ≤ bfA G i j := by
  have hZ : jlZmax (G := G) i j ≤ jlZmin (G := G) i j := by
    unfold jlZmax jlZmin
    exact div_le_div_of_nonneg_left (by positivity) (ρmin_pos hij)
      (by unfold ρmin ρmax; exact min_le_max)
  have eA : bfA G i j = jlK (G := G) i j - jlZmax (G := G) i j - C4 G i j / 2 := rfl
  have eB : bfB G i j = jlK (G := G) i j - jlZmin (G := G) i j - C4 G i j / 2 := rfl
  linarith

/-- **Proposition 5.1 (iii)**: for `a ≥ 2`, if `B^BF_{ij} ≥ 0`, then `κ_BF ≤ κ_0`. -/
theorem bf_le_cOR0_of_bfB_nonneg (hd : GraphMetric G d) (hij : G.Adj i j)
    (h2 : 2 ≤ ρmin G i j) (hB : 0 ≤ bfB G i j) : cBF G i j ≤ cOR0 G d i j := by
  have hA : 0 ≤ bfA G i j := hB.trans (bfB_le_bfA hij)
  have h := bf_excess hd hij h2
  rw [max_eq_right (show -bfA G i j ≤ 0 by linarith),
    max_eq_right (show -bfB G i j ≤ 0 by linarith)] at h
  linarith

end OllivierBF
