/-
  Theorem 5.2 of the paper with its ends as the paper writes them: over the graphs consistent with
  the local data, the minimum and the maximum of the curvature are `1 − 3τ + σ*_∅` and
  `1 − 3τ + max_F σ*_F`, where `σ*_F` is the maximum savings with the distance of the theorem
  (`attainable_range_savings_paper`).

  `AttainableRange` states the ends as `kappaF ∅` and `kappaMax`, `1 − W₁(μ_i, μ_j)` with the charged
  distance `chargedDist F`. The two forms agree because `W₁` with the charged distance also depends
  only on the residuals (`W1_chargedDist_eq_resid`), although `chargedDist F` need not be a metric:
  on the 5-cycle `i, x, z, y, j` with `F = ∅`, `chargedDist ∅ x y = 3` while `x ∼ z ∼ y`. The
  splicing of `Residual` only routes mass through the vertices where both measures are positive,
  which lie in `S`, and from `N[i]` through `S` the charged distance does satisfy the triangle
  inequality (`chargedDist_tri_overlap`). So the residual reduction goes through with the triangle
  inequality assumed only there (`W1_eq_W1_resid_on`), and `kappaF F = 1 − 3τ + σ*_F`
  (`kappaF_eq_sigmaStar`).
-/
module

public import OllivierBF.AttainableRange
public import OllivierBF.SavingsMax
public import OllivierBF.ResidualsFull

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ### The residual reduction with the triangle inequality through the shared support -/

section splice

variable {d : V → V → ℝ}

/-- `splice_core` with the triangle inequality only through `z`, from the support of the first
marginal to the support of the second. -/
lemma splice_core_on {α β : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling α β π)
    (z : V) (htri : ∀ u w, 0 < α u → 0 < β w → d u w ≤ d u z + d z w) (hzz : π z z = 0)
    {c : ℝ} (hc0 : 0 < c) (hcα : c ≤ α z) (hcβ : c ≤ β z) :
    ∃ π', IsCoupling (fun x => α x - if x = z then c else 0)
        (fun y => β y - if y = z then c else 0) π' ∧ cost d π' ≤ cost d π := by
  have hA : 0 < α z := lt_of_lt_of_le hc0 hcα
  have hB : 0 < β z := lt_of_lt_of_le hc0 hcβ
  have hAne : α z ≠ 0 := hA.ne'
  have hBne : β z ≠ 0 := hB.ne'
  have hs1 : c / β z ≤ 1 := (div_le_one hB).2 hcβ
  have ht1 : c / α z ≤ 1 := (div_le_one hA).2 hcα
  have hk0 : 0 ≤ c / (β z * α z) := div_nonneg hc0.le (mul_pos hB hA).le
  have hkA : c / (β z * α z) * α z = c / β z := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hAne]
  have hkB : c / (β z * α z) * β z = c / α z := by
    rw [div_mul_eq_mul_div, mul_comm (β z) (α z), mul_div_mul_right _ _ hBne]
  have htA : c / α z * α z = c := div_mul_cancel₀ c hAne
  have hsB : c / β z * β z = c := div_mul_cancel₀ c hBne
  have hrow : ∑ v, π z v = α z := hπ.2.1 z
  have hcol : ∑ u, π u z = β z := hπ.2.2 z
  refine ⟨fun u v => π u v - (if v = z then c / β z * π u z else 0)
      - (if u = z then c / α z * π z v else 0) + c / (β z * α z) * (π u z * π z v),
    ⟨fun u v => ?_, fun u => ?_, fun v => ?_⟩, ?_⟩
  · -- nonnegativity
    show 0 ≤ π u v - (if v = z then c / β z * π u z else 0)
      - (if u = z then c / α z * π z v else 0) + c / (β z * α z) * (π u z * π z v)
    have h1 := hπ.1 u v
    have h2 := hπ.1 u z
    have h3 := hπ.1 z v
    have h4 : 0 ≤ c / (β z * α z) * (π u z * π z v) := mul_nonneg hk0 (mul_nonneg h2 h3)
    by_cases hv : v = z
    · by_cases hu : u = z
      · rw [ite_eq_left hv, ite_eq_left hu, hu, hv, hzz]
        simp
      · rw [ite_eq_left hv, ite_eq_right hu, hv, hzz]
        have h5 : c / β z * π u z ≤ π u z := by
          calc c / β z * π u z ≤ 1 * π u z := mul_le_mul_of_nonneg_right hs1 h2
            _ = π u z := one_mul _
        simp only [mul_zero, sub_zero, add_zero]
        linarith
    · by_cases hu : u = z
      · rw [ite_eq_right hv, ite_eq_left hu, hu, hzz]
        have h5 : c / α z * π z v ≤ π z v := by
          calc c / α z * π z v ≤ 1 * π z v := mul_le_mul_of_nonneg_right ht1 h3
            _ = π z v := one_mul _
        simp only [zero_mul, mul_zero, sub_zero, add_zero]
        linarith
      · rw [ite_eq_right hv, ite_eq_right hu]
        linarith
  · -- row sums
    show ∑ v, (π u v - (if v = z then c / β z * π u z else 0)
        - (if u = z then c / α z * π z v else 0) + c / (β z * α z) * (π u z * π z v))
        = α u - if u = z then c else 0
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hπ.2.1 u]
    have e1 : ∑ v, (if v = z then c / β z * π u z else 0) = c / β z * π u z := by simp
    have e3 : ∑ v, c / (β z * α z) * (π u z * π z v) = c / β z * π u z := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, hrow, ← hkA]
      ring
    rw [e1, e3]
    by_cases hu : u = z
    · have e2 : ∑ v, (if u = z then c / α z * π z v else 0) = c := by
        simp only [ite_eq_left hu]
        rw [← Finset.mul_sum, hrow, htA]
      rw [e2, ite_eq_left hu]
      ring
    · have e2 : ∑ v, (if u = z then c / α z * π z v else 0) = 0 := by simp [hu]
      rw [e2, ite_eq_right hu]
      ring
  · -- column sums
    show ∑ u, (π u v - (if v = z then c / β z * π u z else 0)
        - (if u = z then c / α z * π z v else 0) + c / (β z * α z) * (π u z * π z v))
        = β v - if v = z then c else 0
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, hπ.2.2 v]
    have e2 : ∑ u, (if u = z then c / α z * π z v else 0) = c / α z * π z v := by simp
    have e3 : ∑ u, c / (β z * α z) * (π u z * π z v) = c / α z * π z v := by
      rw [← Finset.mul_sum, ← Finset.sum_mul, hcol, ← hkB]
      ring
    rw [e2, e3]
    by_cases hv : v = z
    · have e1 : ∑ u, (if v = z then c / β z * π u z else 0) = c := by
        simp only [ite_eq_left hv]
        rw [← Finset.mul_sum, hcol, hsB]
      rw [e1, ite_eq_left hv]
      ring
    · have e1 : ∑ u, (if v = z then c / β z * π u z else 0) = 0 := by simp [hv]
      rw [e1, ite_eq_right hv]
      ring
  · -- cost
    have hlin : cost d (fun u v => π u v - (if v = z then c / β z * π u z else 0)
        - (if u = z then c / α z * π z v else 0) + c / (β z * α z) * (π u z * π z v))
        = cost d π - cost d (fun u v => if v = z then c / β z * π u z else 0)
          - cost d (fun u v => if u = z then c / α z * π z v else 0)
          + c / (β z * α z) * cost d (fun u v => π u z * π z v) :=
      cost_lin (d := d) π (fun u v => if v = z then c / β z * π u z else 0)
        (fun u v => if u = z then c / α z * π z v else 0) (fun u v => π u z * π z v)
        (c / (β z * α z))
    rw [hlin]
    have hP1 : cost d (fun u v => if v = z then c / β z * π u z else 0)
        = c / β z * ∑ u, d u z * π u z := by
      unfold cost
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    have hP2 : cost d (fun u v => if u = z then c / α z * π z v else 0)
        = c / α z * ∑ v, d z v * π z v := by
      unfold cost
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
    have hP3 : cost d (fun u v => π u z * π z v)
        ≤ (∑ u, d u z * π u z) * α z + β z * ∑ v, d z v * π z v := by
      unfold cost
      calc ∑ u, ∑ v, d u v * (π u z * π z v)
          ≤ ∑ u, ∑ v, (d u z + d z v) * (π u z * π z v) := by
            refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => ?_
            rcases (hπ.1 u z).eq_or_lt with hu | hu
            · rw [← hu]; simp
            rcases (hπ.1 z v).eq_or_lt with hv | hv
            · rw [← hv]; simp
            have hαu : 0 < α u := by
              rw [← hπ.2.1 u]
              exact lt_of_lt_of_le hu (Finset.single_le_sum (f := fun v' => π u v')
                (fun v' _ => hπ.1 u v') (Finset.mem_univ z))
            have hβv : 0 < β v := by
              rw [← hπ.2.2 v]
              exact lt_of_lt_of_le hv (Finset.single_le_sum (f := fun u' => π u' v)
                (fun u' _ => hπ.1 u' v) (Finset.mem_univ z))
            exact mul_le_mul_of_nonneg_right (htri u v hαu hβv) (mul_nonneg (hπ.1 u z) (hπ.1 z v))
        _ = (∑ u, d u z * π u z) * α z + β z * ∑ v, d z v * π z v := by
            rw [← hrow, ← hcol, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun v _ => ?_
            ring
    rw [hP1, hP2]
    have hk3 := mul_le_mul_of_nonneg_left hP3 hk0
    have e : c / (β z * α z) * ((∑ u, d u z * π u z) * α z + β z * ∑ v, d z v * π z v)
        = c / β z * ∑ u, d u z * π u z + c / α z * ∑ v, d z v * π z v := by
      rw [← hkA, ← hkB]
      ring
    linarith

/-- `splice_vertex` with the triangle inequality only through `z`, and only when mass has to be
routed past `z` (`0 < c`). -/
theorem splice_vertex_on {α β : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling α β π)
    (hself : ∀ x, d x x = 0) (z : V) {c : ℝ}
    (htri : 0 < c → ∀ u w, 0 < α u → 0 < β w → d u w ≤ d u z + d z w)
    (hcα : c ≤ α z) (hcβ : c ≤ β z) :
    ∃ π', IsCoupling (fun x => α x - if x = z then c else 0)
        (fun y => β y - if y = z then c else 0) π' ∧ cost d π' ≤ cost d π := by
  by_cases hle : c ≤ π z z
  · obtain ⟨h1, h2⟩ := hπ.dropDiag (d := d) hself z hle
    exact ⟨_, h1, h2.le⟩
  · have hlt : π z z < c := not_le.mp hle
    obtain ⟨h1, h2⟩ := hπ.dropDiag (d := d) hself z (le_refl (π z z))
    have hz1 : (fun u v => π u v - if u = z ∧ v = z then π z z else 0) z z = 0 := by simp
    have hc' : 0 < c - π z z := by linarith
    have hα' : c - π z z ≤ (fun x => α x - if x = z then π z z else 0) z := by
      show c - π z z ≤ α z - (if z = z then π z z else 0)
      rw [ite_eq_left rfl]; linarith
    have hβ' : c - π z z ≤ (fun y => β y - if y = z then π z z else 0) z := by
      show c - π z z ≤ β z - (if z = z then π z z else 0)
      rw [ite_eq_left rfl]; linarith
    have hcpos : 0 < c := by linarith [hπ.1 z z]
    have htri' : ∀ u w, 0 < (fun x => α x - if x = z then π z z else 0) u →
        0 < (fun y => β y - if y = z then π z z else 0) w → d u w ≤ d u z + d z w := by
      intro u w hu hw
      have hu2 : 0 < α u - (if u = z then π z z else 0) := hu
      have hw2 : 0 < β w - (if w = z then π z z else 0) := hw
      have hzz0 := hπ.1 z z
      have hu3 : 0 < α u := by split_ifs at hu2 <;> linarith
      have hw3 : 0 < β w := by split_ifs at hw2 <;> linarith
      exact htri hcpos u w hu3 hw3
    obtain ⟨π', hπ', hcost⟩ := splice_core_on (d := d) h1 z htri' hz1 hc' hα' hβ'
    refine ⟨π', hπ'.of_marg_eq (fun x => ?_) (fun y => ?_), hcost.trans h2.le⟩
    · show α x - (if x = z then π z z else 0) - (if x = z then c - π z z else 0)
          = α x - if x = z then c else 0
      split_ifs <;> ring
    · show β y - (if y = z then π z z else 0) - (if y = z then c - π z z else 0)
          = β y - if y = z then c else 0
      split_ifs <;> ring

/-- `exists_resid_coupling_le` with the triangle inequality only through the vertices where both
measures are positive. -/
theorem exists_resid_coupling_le_on {μ ν : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling μ ν π)
    (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x) (hself : ∀ x, d x x = 0)
    (hT : ∀ x z w, 0 < μ x → 0 < min (μ z) (ν z) → 0 < ν w → d x w ≤ d x z + d z w) :
    ∃ ρ, IsCoupling (fun x => μ x - min (μ x) (ν x)) (fun y => ν y - min (μ y) (ν y)) ρ ∧
      cost d ρ ≤ cost d π := by
  have key : ∀ s : Finset V, ∃ ρ,
      IsCoupling (fun x => μ x - if x ∈ s then min (μ x) (ν x) else 0)
        (fun y => ν y - if y ∈ s then min (μ y) (ν y) else 0) ρ ∧ cost d ρ ≤ cost d π := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · exact ⟨π, hπ.of_marg_eq (fun x => by simp) (fun y => by simp), le_rfl⟩
    · intro a s ha ih
      obtain ⟨ρ, hρ, hcost⟩ := ih
      have hα : min (μ a) (ν a) ≤ (fun x => μ x - if x ∈ s then min (μ x) (ν x) else 0) a := by
        show min (μ a) (ν a) ≤ μ a - (if a ∈ s then min (μ a) (ν a) else 0)
        rw [ite_eq_right ha, sub_zero]
        exact min_le_left _ _
      have hβ : min (μ a) (ν a) ≤ (fun y => ν y - if y ∈ s then min (μ y) (ν y) else 0) a := by
        show min (μ a) (ν a) ≤ ν a - (if a ∈ s then min (μ a) (ν a) else 0)
        rw [ite_eq_right ha, sub_zero]
        exact min_le_right _ _
      have htri_a : 0 < min (μ a) (ν a) → ∀ u w,
          0 < (fun x => μ x - if x ∈ s then min (μ x) (ν x) else 0) u →
          0 < (fun y => ν y - if y ∈ s then min (μ y) (ν y) else 0) w →
          d u w ≤ d u a + d a w := by
        intro hm u w hu hw
        have hu2 : 0 < μ u - (if u ∈ s then min (μ u) (ν u) else 0) := hu
        have hw2 : 0 < ν w - (if w ∈ s then min (μ w) (ν w) else 0) := hw
        have hmu : 0 ≤ min (μ u) (ν u) := le_min (hμ u) (hν u)
        have hmw : 0 ≤ min (μ w) (ν w) := le_min (hμ w) (hν w)
        have hu3 : 0 < μ u := by split_ifs at hu2 <;> linarith
        have hw3 : 0 < ν w := by split_ifs at hw2 <;> linarith
        exact hT u a w hu3 hm hw3
      obtain ⟨ρ', hρ', hcost'⟩ := splice_vertex_on (d := d) hρ hself a htri_a hα hβ
      refine ⟨ρ', hρ'.of_marg_eq (fun x => ?_) (fun y => ?_), hcost'.trans hcost⟩
      · show μ x - (if x ∈ s then min (μ x) (ν x) else 0) - (if x = a then min (μ a) (ν a) else 0)
            = μ x - if x ∈ insert a s then min (μ x) (ν x) else 0
        by_cases hxa : x = a
        · subst hxa
          simp [ha]
        · simp [hxa]
      · show ν y - (if y ∈ s then min (μ y) (ν y) else 0) - (if y = a then min (μ a) (ν a) else 0)
            = ν y - if y ∈ insert a s then min (μ y) (ν y) else 0
        by_cases hya : y = a
        · subst hya
          simp [ha]
        · simp [hya]
  obtain ⟨ρ, hρ, hcost⟩ := key Finset.univ
  exact ⟨ρ, hρ.of_marg_eq (fun x => by simp) (fun y => by simp), hcost⟩

/-- **`W₁` depends only on the residual**, with the triangle inequality only through the vertices
where both measures are positive. -/
theorem W1_eq_W1_resid_on {μ ν : V → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
    (hmass : ∑ x, μ x = ∑ x, ν x) (hd0 : ∀ x y, 0 ≤ d x y) (hself : ∀ x, d x x = 0)
    (hT : ∀ x z w, 0 < μ x → 0 < min (μ z) (ν z) → 0 < ν w → d x w ≤ d x z + d z w) :
    W1 d μ ν = W1 d (fun x => μ x - min (μ x) (ν x)) (fun y => ν y - min (μ y) (ν y)) := by
  obtain ⟨ρ₀, hρ₀⟩ := exists_resid_coupling hmass
  have hm : ∀ x, 0 ≤ min (μ x) (ν x) := fun x => le_min (hμ x) (hν x)
  have hglue : ∀ ρ, IsCoupling (fun x => μ x - min (μ x) (ν x))
      (fun y => ν y - min (μ y) (ν y)) ρ →
      IsCoupling μ ν (fun x y => (if x = y then min (μ x) (ν x) else 0) + ρ x y) := by
    intro ρ hρ
    exact ((isCoupling_diag hm).add hρ).of_marg_eq (fun x => by simp) (fun y => by simp)
  apply le_antisymm
  · apply le_W1 ⟨ρ₀, hρ₀⟩
    intro ρ hρ
    calc W1 d μ ν ≤ cost d (fun x y => (if x = y then min (μ x) (ν x) else 0) + ρ x y) :=
          W1_le_cost hd0 (hglue ρ hρ)
      _ = cost d ρ := by rw [cost_add, cost_diag hself, zero_add]
  · apply le_W1 ⟨_, hglue ρ₀ hρ₀⟩
    intro π hπ
    obtain ⟨ρ, hρ, hcost⟩ := exists_resid_coupling_le_on (d := d) hπ hμ hν hself hT
    exact (W1_le_cost hd0 hρ).trans hcost

end splice

/-! ### The charged distance -/

section charged

variable {G : SimpleGraph V} [DecidableRel G.Adj] {i j : V}

lemma chargedDist_self (F : Finset (Sym2 V)) (p : V) : chargedDist G i j F p p = 0 := by
  unfold chargedDist
  rw [ite_eq_left rfl]

lemma crossDist_le_three (F : Finset (Sym2 V)) (x y : V) : crossDist G i j F x y ≤ 3 := by
  unfold crossDist
  split_ifs <;> norm_num

lemma one_le_crossDist (F : Finset (Sym2 V)) (x y : V) : 1 ≤ crossDist G i j F x y := by
  unfold crossDist
  split_ifs <;> norm_num

lemma chargedDist_le_three (F : Finset (Sym2 V)) (p q : V) : chargedDist G i j F p q ≤ 3 := by
  unfold chargedDist
  split_ifs
  · norm_num
  · exact crossDist_le_three F p q
  · exact crossDist_le_three F q p
  · norm_num
  · norm_num

lemma one_le_chargedDist {F : Finset (Sym2 V)} {p q : V} (hpq : p ≠ q) :
    1 ≤ chargedDist G i j F p q := by
  unfold chargedDist
  rw [ite_eq_right hpq]
  split_ifs
  · exact one_le_crossDist F p q
  · exact one_le_crossDist F q p
  · norm_num
  · norm_num

lemma adj_of_crossDist_lt_two {F : Finset (Sym2 V)} {x y : V} (h : crossDist G i j F x y < 2) :
    G.Adj x y := by
  unfold crossDist at h
  split_ifs at h with h1
  · exact h1
  · norm_num at h
  · norm_num at h

/-- Distinct vertices at charged distance less than `2` are adjacent. -/
lemma adj_of_chargedDist_lt_two {F : Finset (Sym2 V)} {p q : V} (hpq : p ≠ q)
    (h : chargedDist G i j F p q < 2) : G.Adj p q := by
  unfold chargedDist at h
  rw [ite_eq_right hpq] at h
  split_ifs at h with h1 h2 h3
  · exact adj_of_crossDist_lt_two h
  · exact (adj_of_crossDist_lt_two h).symm
  · exact h3
  · norm_num at h

lemma two_le_chargedDist {F : Finset (Sym2 V)} {p q : V} (hpq : p ≠ q) (hna : ¬ G.Adj p q) :
    2 ≤ chargedDist G i j F p q := by
  by_contra h
  exact hna (adj_of_chargedDist_lt_two hpq (not_le.mp h))

lemma chargedDist_of_adj {F : Finset (Sym2 V)} {p q : V} (h : G.Adj p q) :
    chargedDist G i j F p q = 1 := by
  unfold chargedDist
  rw [ite_eq_right (G.ne_of_adj h)]
  -- `split_ifs` discharges the condition `G.Adj p q` with `h`, so three goals remain
  split_ifs
  · unfold crossDist
    rw [ite_eq_left h]
  · unfold crossDist
    rw [ite_eq_left h.symm]
  · rfl

lemma chargedDist_cross {F : Finset (Sym2 V)} {x y : V} (hx : x ∈ uniq G i j)
    (hy : y ∈ uniq G j i) : chargedDist G i j F x y = crossDist G i j F x y := by
  have hxy : x ≠ y := by
    rintro rfl
    exact (mem_uniq.mp hy).2.2 (mem_uniq.mp hx).2.1
  unfold chargedDist
  rw [ite_eq_right hxy, ite_eq_left ⟨hx, hy⟩]

lemma crossDist_eq_three {F : Finset (Sym2 V)} {x y : V} (h1 : ¬ G.Adj x y)
    (h2 : ¬ ∃ w ∈ uniq G i j ∪ common G i j, G.Adj x w ∧ G.Adj w y)
    (h3 : ¬ ∃ w, G.Adj x w ∧ s(w, y) ∈ F) : crossDist G i j F x y = 3 := by
  unfold crossDist
  rw [ite_eq_right h1, ite_eq_right (not_or.mpr ⟨h2, h3⟩)]

/-- **The triangle inequality through the overlap.** From a vertex of `N[i]` through a vertex of
`S`, the charged distance satisfies the triangle inequality, whatever `F`. -/
lemma chargedDist_tri_overlap (F : Finset (Sym2 V)) {x z w : V} (hx : x = i ∨ G.Adj i x)
    (hz : z ∈ overlap G i j) :
    chargedDist G i j F x w ≤ chargedDist G i j F x z + chargedDist G i j F z w := by
  have h0xz := chargedDist_nonneg (G := G) (i := i) (j := j) F x z
  have h0zw := chargedDist_nonneg (G := G) (i := i) (j := j) F z w
  by_cases hxz : x = z
  · rw [hxz, chargedDist_self]
    linarith
  by_cases hzw : z = w
  · rw [hzw, chargedDist_self]
    linarith
  have h1 := one_le_chargedDist (G := G) (i := i) (j := j) (F := F) hxz
  have h1' := one_le_chargedDist (G := G) (i := i) (j := j) (F := F) hzw
  have h3 := chargedDist_le_three (G := G) (i := i) (j := j) F x w
  by_cases hsum : 3 ≤ chargedDist G i j F x z + chargedDist G i j F z w
  · linarith
  -- both legs are edges
  have hsum' := not_le.mp hsum
  have hxz' : G.Adj x z := adj_of_chargedDist_lt_two hxz (by linarith)
  have hzw' : G.Adj z w := adj_of_chargedDist_lt_two hzw (by linarith)
  suffices h2 : chargedDist G i j F x w ≤ 2 by linarith
  by_cases hxw : x = w
  · rw [hxw, chargedDist_self]
    norm_num
  unfold chargedDist
  rw [ite_eq_right hxw]
  split_ifs with hA hB hC
  · -- `x ∈ U_i` and `w ∈ U_j`: `z` is a common neighbour, and it lies in `C`
    unfold crossDist
    split_ifs with hD hE
    · norm_num
    · norm_num
    · exfalso
      apply hE
      left
      refine ⟨z, ?_, hxz', hzw'⟩
      rcases Finset.mem_insert.mp hz with hzi | hz'
      · rw [hzi] at hzw'
        exact absurd hzw' (mem_uniq.mp hA.2).2.2
      · rcases Finset.mem_insert.mp hz' with hzj | hzC
        · rw [hzj] at hxz'
          exact absurd hxz'.symm (mem_uniq.mp hA.1).2.2
        · exact Finset.mem_union_right _ hzC
  · -- `x ∈ U_j` is impossible, since `x ∈ N[i]`
    exfalso
    obtain ⟨hxi, -, hix⟩ := mem_uniq.mp hB.2
    rcases hx with h | h
    · exact hxi h
    · exact hix h
  · norm_num
  · norm_num

end charged

/-! ### The ends in savings form -/

/-- `max_F σ*_F`: the largest maximum savings with the distance of Theorem 5.2, over the admissible
`F`. -/
noncomputable def sigmaMax (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (μ : V → V → ℝ) :
    ℝ :=
  (admissibleSets G i j).sup' ⟨∅, empty_mem_admissibleSets G i j⟩
    (fun F => sigmaStar (chargedDist G i j F) (resP μ i j) (resN μ i j))

section ends

variable {G : SimpleGraph V} [DecidableRel G.Adj] {i j : V} {μ : V → V → ℝ}

/-- **`W₁` with the charged distance depends only on the residuals.** -/
theorem W1_chargedDist_eq_resid (hi : OneStepAt G μ i) (hj : OneStepAt G μ j)
    (F : Finset (Sym2 V)) :
    W1 (chargedDist G i j F) (μ i) (μ j) = W1 (chargedDist G i j F) (resP μ i j) (resN μ i j) := by
  rw [W1_eq_W1_resid_on hi.nonneg hj.nonneg (by rw [hi.mass, hj.mass]) (chargedDist_nonneg F)
    (chargedDist_self F) fun x z w hx hz _ => chargedDist_tri_overlap F
      (mem_closed_of_mu_pos hi hx) (mem_overlap_of_min_pos hi hj hz)]
  rfl

/-- `kappaF F = 1 − 3τ + σ*_F`. -/
theorem kappaF_eq_sigmaStar (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) (F : Finset (Sym2 V)) :
    kappaF G i j μ F
      = 1 - 3 * resMass μ i j + sigmaStar (chargedDist G i j F) (resP μ i j) (resN μ i j) := by
  unfold kappaF cORm
  rw [W1_chargedDist_eq_resid hi hj F, W1_eq_three_mul_sub_sigmaStar (resP_nonneg μ i j)
    (resN_nonneg μ i j) (resP_sum_eq_resN_sum hi hj) (chargedDist_nonneg F)
    (fun x y _ _ => chargedDist_le_three F x y)]
  unfold resMass
  ring

/-- `kappaMax = 1 − 3τ + max_F σ*_F`. -/
theorem kappaMax_eq_sigmaMax (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) :
    kappaMax G i j μ = 1 - 3 * resMass μ i j + sigmaMax G i j μ := by
  apply le_antisymm
  · unfold kappaMax
    refine Finset.sup'_le _ _ fun F hF => ?_
    rw [kappaF_eq_sigmaStar hi hj F]
    have hle : sigmaStar (chargedDist G i j F) (resP μ i j) (resN μ i j) ≤ sigmaMax G i j μ :=
      Finset.le_sup' (fun F => sigmaStar (chargedDist G i j F) (resP μ i j) (resN μ i j)) hF
    linarith
  · obtain ⟨F, hF, hFmax⟩ := Finset.exists_mem_eq_sup' ⟨∅, empty_mem_admissibleSets G i j⟩
      (fun F => sigmaStar (chargedDist G i j F) (resP μ i j) (resN μ i j))
    have h1 : sigmaMax G i j μ = sigmaStar (chargedDist G i j F) (resP μ i j) (resN μ i j) := hFmax
    have h2 : kappaF G i j μ F ≤ kappaMax G i j μ := Finset.le_sup' (kappaF G i j μ) hF
    rw [h1, ← kappaF_eq_sigmaStar hi hj F]
    exact h2

/-- **Theorem 5.2 (attainable range)**, with the ends as the paper writes them: over the connected
graphs consistent with the local data of `(i, j)`, with their shortest-path distance and measures
that agree with `μ` (locality), the minimum and the maximum of the curvature are `1 − 3τ + σ*_∅` and
`1 − 3τ + max_F σ*_F`, and both are attained. -/
theorem attainable_range_savings_paper (hij : G.Adj i j) (hi : OneStepAt G μ i)
    (hj : OneStepAt G μ j) :
    (∀ {V' : Type u} [Fintype V'] [DecidableEq V'] (G' : SimpleGraph V') [DecidableRel G'.Adj]
        (e : V → V') (μ' : V' → V' → ℝ), G'.Connected → Consistent G i j G' e →
        Agrees G i j μ μ' e →
        1 - 3 * resMass μ i j + sigmaStar (chargedDist G i j ∅) (resP μ i j) (resN μ i j)
            ≤ cORm (fun x y => (G'.dist x y : ℝ)) μ' (e i) (e j) ∧
          cORm (fun x y => (G'.dist x y : ℝ)) μ' (e i) (e j)
            ≤ 1 - 3 * resMass μ i j + sigmaMax G i j μ) ∧
    ((realize G i j ∅).Connected ∧ Consistent G i j (realize G i j ∅) (embed G i j ∅) ∧
      ∀ μ' : RealV G i j ∅ → RealV G i j ∅ → ℝ, Agrees G i j μ μ' (embed G i j ∅) →
        cORm (fun x y => ((realize G i j ∅).dist x y : ℝ)) μ' (embed G i j ∅ i) (embed G i j ∅ j) =
          1 - 3 * resMass μ i j + sigmaStar (chargedDist G i j ∅) (resP μ i j) (resN μ i j)) ∧
    ∃ F, Admissible G i j F ∧
      sigmaStar (chargedDist G i j F) (resP μ i j) (resN μ i j) = sigmaMax G i j μ ∧
      (realize G i j F).Connected ∧ Consistent G i j (realize G i j F) (embed G i j F) ∧
      ∀ μ' : RealV G i j F → RealV G i j F → ℝ, Agrees G i j μ μ' (embed G i j F) →
        cORm (fun x y => ((realize G i j F).dist x y : ℝ)) μ' (embed G i j F i) (embed G i j F j) =
          1 - 3 * resMass μ i j + sigmaMax G i j μ := by
  have h0 := kappaF_eq_sigmaStar hi hj ∅
  have hM := kappaMax_eq_sigmaMax hi hj
  obtain ⟨hA, hB, F, hF, hFeq, hC⟩ := attainable_range_paper (G := G) hij hi hj
  refine ⟨?_, ?_, F, hF, ?_, hC.1, hC.2.1, ?_⟩
  · intro V' _ _ G' _ e μ' hconn hc hμ
    rw [← h0, ← hM]
    exact hA G' e μ' hconn hc hμ
  · rw [← h0]
    exact hB
  · have hF' := kappaF_eq_sigmaStar hi hj F
    rw [hFeq, hM] at hF'
    linarith
  · intro μ' hμ
    rw [← hM]
    exact hC.2.2 μ' hμ

end ends

end OllivierBF
