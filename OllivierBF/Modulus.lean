/-
  Regularity of the lower modulus `φ_{a,b}(ζ) = L⁰ + κ₁ [ζ − 𝔖]₊` of Theorem 5.4: it is
  continuous, convex, and affine on each side of `𝔖`.
  Nothing in this file takes a published result as a hypothesis.
-/

module

public import OllivierBF.Paper

@[expose] public section

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {a b : ℝ}

/-- **Theorem 5.4**: `φ_{a,b}` is continuous. -/
theorem phiAff_continuous (a b : ℝ) : Continuous (phiAff a b) := by
  show Continuous fun ζ => L0 a b + kappa1 a b * max (ζ - bS a b) 0
  exact continuous_const.add
    (continuous_const.mul ((continuous_id.sub continuous_const).max continuous_const))

/-- **Theorem 5.4**: `φ_{a,b}` is the constant `L⁰` up to `𝔖`. -/
lemma phiAff_of_le (a b : ℝ) {ζ : ℝ} (h : ζ ≤ bS a b) : phiAff a b ζ = L0 a b := by
  unfold phiAff
  rw [max_eq_right (show ζ - bS a b ≤ 0 by linarith)]
  ring

/-- **Theorem 5.4**: `φ_{a,b}` is affine with slope `κ₁` from `𝔖` on. -/
lemma phiAff_of_ge (a b : ℝ) {ζ : ℝ} (h : bS a b ≤ ζ) :
    phiAff a b ζ = L0 a b + kappa1 a b * (ζ - bS a b) := by
  unfold phiAff
  rw [max_eq_left (show 0 ≤ ζ - bS a b by linarith)]

/-- **Theorem 5.4**: `φ_{a,b}` is convex, since `κ₁ ≥ 0`. -/
theorem phiAff_convexOn (ha : 0 < a) (hb : 0 < b) : ConvexOn ℝ Set.univ (phiAff a b) := by
  refine ⟨convex_univ, fun x _ y _ s t hs ht hst => ?_⟩
  obtain rfl : t = 1 - s := by linarith
  have hk := kappa1_nonneg ha hb
  have h1 : s * (x - bS a b) ≤ s * max (x - bS a b) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hs
  have h2 : (1 - s) * (y - bS a b) ≤ (1 - s) * max (y - bS a b) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) ht
  have h3 : 0 ≤ s * max (x - bS a b) 0 := mul_nonneg hs (le_max_right _ _)
  have h4 : 0 ≤ (1 - s) * max (y - bS a b) 0 := mul_nonneg ht (le_max_right _ _)
  have hmax : max (s * x + (1 - s) * y - bS a b) 0
      ≤ s * max (x - bS a b) 0 + (1 - s) * max (y - bS a b) 0 :=
    max_le (by linarith) (by linarith)
  have key := mul_le_mul_of_nonneg_left hmax hk
  simp only [phiAff, smul_eq_mul]
  nlinarith [key]

end OllivierBF
