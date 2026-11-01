/-
  Regularity of the lower modulus `φ_{a,b}` of Theorem 5.4 (`phiAff`): it is continuous, convex,
  and piecewise linear with two pieces, `L⁰` below `S` and slope `λ₁` above it. Monotonicity is
  `phiAff_mono` in `Paper.lean`.
-/
module

public import OllivierBF.Paper

@[expose] public section

set_option linter.unusedSectionVars false

namespace OllivierBF

/-- **Theorem 5.4**: the lower modulus is continuous. -/
theorem phiAff_continuous (a b : ℝ) : Continuous (phiAff a b) := by
  show Continuous fun ζ => L0 a b + kappa1 a b * max (ζ - bS a b) 0
  fun_prop

/-- **Theorem 5.4**: the lower modulus is convex. -/
theorem phiAff_convexOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ConvexOn ℝ Set.univ (phiAff a b) := by
  have hk := kappa1_nonneg ha hb
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ p q hp hq hpq
  simp only [smul_eq_mul]
  unfold phiAff
  have hm : max (p * x + q * y - bS a b) 0
      ≤ p * max (x - bS a b) 0 + q * max (y - bS a b) 0 := by
    apply max_le
    · have hx := mul_le_mul_of_nonneg_left (le_max_left (x - bS a b) 0) hp
      have hy := mul_le_mul_of_nonneg_left (le_max_left (y - bS a b) 0) hq
      have e : p * x + q * y - bS a b = p * (x - bS a b) + q * (y - bS a b) := by
        linear_combination bS a b * hpq
      linarith
    · exact add_nonneg (mul_nonneg hp (le_max_right _ _)) (mul_nonneg hq (le_max_right _ _))
  have hkm := mul_le_mul_of_nonneg_left hm hk
  have e2 : p * L0 a b + q * L0 a b = L0 a b := by rw [← add_mul, hpq, one_mul]
  linarith

/-- **Theorem 5.4**: below `S` the lower modulus is the constant `L⁰`. -/
theorem phiAff_of_le {a b ζ : ℝ} (h : ζ ≤ bS a b) : phiAff a b ζ = L0 a b := by
  unfold phiAff
  rw [max_eq_right (show ζ - bS a b ≤ 0 by linarith), mul_zero, add_zero]

/-- **Theorem 5.4**: above `S` the lower modulus is affine with slope `λ₁` (`kappa1`). -/
theorem phiAff_of_ge {a b ζ : ℝ} (h : bS a b ≤ ζ) :
    phiAff a b ζ = L0 a b + kappa1 a b * (ζ - bS a b) := by
  unfold phiAff
  rw [max_eq_left (show (0 : ℝ) ≤ ζ - bS a b by linarith)]

end OllivierBF
