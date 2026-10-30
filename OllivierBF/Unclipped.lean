/-
  Proposition 5.1 (ii) and (iii) of the paper: BF exceeds the non-lazy curvature by at most the
  negative parts of the two BF deficits, and the deficits are ordered, so that `B^BF ≥ 0` makes
  BF a lower bound on the non-lazy curvature.
  Part (i) is `bf_is_third_piece` in `Bounds.lean`. Nothing in this file takes a published result
  as a hypothesis.
-/

module

public import OllivierBF.Paper

@[expose] public section

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ} {i j : V}

/-- The BF deficit `A^BF = 𝔎 − 𝔷_max − 𝔠₄/2` of Proposition 5.1. -/
noncomputable def bfA (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) : ℝ :=
  jlK (G := G) i j - jlZmax (G := G) i j - C4 G i j / 2

/-- The BF deficit `B^BF = 𝔎 − 𝔷_min − 𝔠₄/2` of Proposition 5.1. -/
noncomputable def bfB (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) : ℝ :=
  jlK (G := G) i j - jlZmin (G := G) i j - C4 G i j / 2

/-- `L^BF = 𝔷_max − [A^BF]₊ − [B^BF]₊` of Proposition 5.1 (ii). -/
noncomputable def LBF (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) : ℝ :=
  jlZmax (G := G) i j - max (bfA G i j) 0 - max (bfB G i j) 0

/-- `x = [x]₊ − [−x]₊`. -/
lemma eq_pos_sub_neg_part (x : ℝ) : x = max x 0 - max (-x) 0 := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (show 0 ≤ -x by linarith)]
    ring
  · rw [max_eq_left h, max_eq_right (show -x ≤ 0 by linarith)]
    ring

/-- **Proposition 5.1 (ii)**, the identity `L^BF = 𝔠_BF − [−A^BF]₊ − [−B^BF]₊`. -/
theorem LBF_eq (hij : G.Adj i j) (h2 : ¬ ρmin G i j ≤ 1) :
    LBF G i j = cBF G i j - max (-bfA G i j) 0 - max (-bfB G i j) 0 := by
  have h := bf_is_third_piece hij h2
  have hA := eq_pos_sub_neg_part (bfA G i j)
  have hB := eq_pos_sub_neg_part (bfB G i j)
  have eA : bfA G i j = jlK (G := G) i j - jlZmax (G := G) i j - C4 G i j / 2 := rfl
  have eB : bfB G i j = jlK (G := G) i j - jlZmin (G := G) i j - C4 G i j / 2 := rfl
  have eL : LBF G i j = jlZmax (G := G) i j - max (bfA G i j) 0 - max (bfB G i j) 0 := rfl
  linarith

/-- **Proposition 5.1 (ii)**: `L^BF ≤ L^□`, because `𝔠₄/2 ≤ 𝒮` (Lemma 3.6). -/
theorem LBF_le_Lsq (hij : G.Adj i j) : LBF G i j ≤ Lsq (G := G) i j := by
  have h4 := C4_le_two_matchStat hij
  have hA : max (jlK (G := G) i j - jlZmax (G := G) i j - matchStat G i j) 0
      ≤ max (bfA G i j) 0 :=
    max_le_max (by unfold bfA; linarith) le_rfl
  have hB : max (jlK (G := G) i j - jlZmin (G := G) i j - matchStat G i j) 0
      ≤ max (bfB G i j) 0 :=
    max_le_max (by unfold bfB; linarith) le_rfl
  unfold LBF Lsq
  linarith

/-- **Proposition 5.1 (ii)**, the excess bound `(5.1)`:
`𝔠_BF − 𝔠_{OR-0} ≤ [−A^BF]₊ + [−B^BF]₊`. -/
theorem bf_excess (hd : GraphMetric G d) (hij : G.Adj i j) (h2 : ¬ ρmin G i j ≤ 1) :
    cBF G i j - cOR0 G d i j ≤ max (-bfA G i j) 0 + max (-bfB G i j) 0 := by
  have h1 := LBF_eq hij h2
  have h3 := LBF_le_Lsq hij
  have h4 := jl_aug hd hij
  linarith

/-- **Proposition 5.1 (iii)**: `A^BF ≥ B^BF`. -/
theorem bfB_le_bfA (hij : G.Adj i j) : bfB G i j ≤ bfA G i j := by
  have hpos := ρmin_pos hij
  have hle : ρmin G i j ≤ ρmax G i j := by
    unfold ρmin ρmax
    exact min_le_max
  have hZ : jlZmax (G := G) i j ≤ jlZmin (G := G) i j := by
    unfold jlZmax jlZmin
    exact div_le_div_of_nonneg_left (by positivity) hpos hle
  unfold bfA bfB
  linarith

/-- **Proposition 5.1 (iii)**: if `B^BF ≥ 0`, then `𝔠_BF ≤ 𝔠_{OR-0}`. -/
theorem bf_le_cOR0_of_bfB_nonneg (hd : GraphMetric G d) (hij : G.Adj i j)
    (h2 : ¬ ρmin G i j ≤ 1) (hB : 0 ≤ bfB G i j) : cBF G i j ≤ cOR0 G d i j := by
  have hA : 0 ≤ bfA G i j := hB.trans (bfB_le_bfA hij)
  have h := bf_excess hd hij h2
  rw [max_eq_right (show -bfA G i j ≤ 0 by linarith),
    max_eq_right (show -bfB G i j ≤ 0 by linarith)] at h
  linarith

end OllivierBF
