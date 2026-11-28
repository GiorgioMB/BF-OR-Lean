/- `W₁` depends only on the residuals; savings of partial plans. -/
module

public import OllivierBF.Transport

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]

def mass (π : V → V → ℝ) : ℝ := ∑ x, ∑ y, π x y

/-- The savings `Σ (3 − d) π`. -/
def savings (d : V → V → ℝ) (π : V → V → ℝ) : ℝ := ∑ x, ∑ y, (3 - d x y) * π x y

/-- A partial plan: nonnegative, with row sums at most `μ` and column sums at most `ν`. -/
def IsSubPlan (μ ν : V → ℝ) (π : V → V → ℝ) : Prop :=
  (∀ x y, 0 ≤ π x y) ∧ (∀ x, ∑ y, π x y ≤ μ x) ∧ (∀ y, ∑ x, π x y ≤ ν y)

variable {d : V → V → ℝ}

lemma IsCoupling.of_marg_eq {μ ν μ' ν' : V → ℝ} {π : V → V → ℝ} (h : IsCoupling μ ν π)
    (hμ : ∀ x, μ x = μ' x) (hν : ∀ y, ν y = ν' y) : IsCoupling μ' ν' π :=
  ⟨h.1, fun x => (h.2.1 x).trans (hμ x), fun y => (h.2.2 y).trans (hν y)⟩

lemma IsCoupling.mass_eq {μ ν : V → ℝ} {π : V → V → ℝ} (h : IsCoupling μ ν π) :
    mass π = ∑ x, μ x := by
  unfold mass
  exact Finset.sum_congr rfl fun x _ => h.2.1 x

lemma cost_eq_three_mass_sub_savings (π : V → V → ℝ) :
    cost d π = 3 * mass π - savings d π := by
  unfold cost mass savings
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

lemma cost_lin (π a b c : V → V → ℝ) (k : ℝ) :
    cost d (fun u v => π u v - a u v - b u v + k * c u v)
      = cost d π - cost d a - cost d b + k * cost d c := by
  have h : ∀ u v, d u v * (π u v - a u v - b u v + k * c u v)
      = d u v * π u v - d u v * a u v - d u v * b u v + k * (d u v * c u v) := by
    intro u v; ring
  unfold cost
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma IsCoupling.dropDiag {α β : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling α β π)
    (hself : ∀ x, d x x = 0) (z : V) {e : ℝ} (he : e ≤ π z z) :
    IsCoupling (fun x => α x - if x = z then e else 0) (fun y => β y - if y = z then e else 0)
        (fun u v => π u v - if u = z ∧ v = z then e else 0) ∧
      cost d (fun u v => π u v - if u = z ∧ v = z then e else 0) = cost d π := by
  refine ⟨⟨fun u v => ?_, fun u => ?_, fun v => ?_⟩, ?_⟩
  · show 0 ≤ π u v - (if u = z ∧ v = z then e else 0)
    by_cases h : u = z ∧ v = z
    · rw [ite_eq_left h]
      obtain ⟨rfl, rfl⟩ := h
      linarith
    · rw [ite_eq_right h, sub_zero]
      exact hπ.1 u v
  · show ∑ v, (π u v - if u = z ∧ v = z then e else 0) = α u - if u = z then e else 0
    rw [Finset.sum_sub_distrib, hπ.2.1 u]
    congr 1
    by_cases hu : u = z
    · subst hu; simp
    · simp [hu]
  · show ∑ u, (π u v - if u = z ∧ v = z then e else 0) = β v - if v = z then e else 0
    rw [Finset.sum_sub_distrib, hπ.2.2 v]
    congr 1
    by_cases hv : v = z
    · subst hv; simp
    · simp [hv]
  · unfold cost
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    by_cases h : u = z ∧ v = z
    · obtain ⟨rfl, rfl⟩ := h
      simp [hself]
    · simp [h]

lemma splice_core {α β : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling α β π)
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
  ·
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
  ·
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
  ·
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
  ·
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

theorem splice_vertex {α β : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling α β π)
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
    obtain ⟨π', hπ', hcost⟩ := splice_core (d := d) h1 z htri' hz1 hc' hα' hβ'
    refine ⟨π', hπ'.of_marg_eq (fun x => ?_) (fun y => ?_), hcost.trans h2.le⟩
    · show α x - (if x = z then π z z else 0) - (if x = z then c - π z z else 0)
          = α x - if x = z then c else 0
      split_ifs <;> ring
    · show β y - (if y = z then π z z else 0) - (if y = z then c - π z z else 0)
          = β y - if y = z then c else 0
      split_ifs <;> ring

theorem exists_resid_coupling_le {μ ν : V → ℝ} {π : V → V → ℝ} (hπ : IsCoupling μ ν π)
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
      obtain ⟨ρ', hρ', hcost'⟩ := splice_vertex (d := d) hρ hself a htri_a hα hβ
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

lemma exists_resid_coupling {μ ν : V → ℝ}
    (hmass : ∑ x, μ x = ∑ x, ν x) :
    ∃ ρ, IsCoupling (fun x => μ x - min (μ x) (ν x)) (fun y => ν y - min (μ y) (ν y)) ρ := by
  have hP : ∀ x, 0 ≤ μ x - min (μ x) (ν x) := fun x => sub_nonneg.2 (min_le_left _ _)
  have hN : ∀ y, 0 ≤ ν y - min (μ y) (ν y) := fun y => sub_nonneg.2 (min_le_right _ _)
  have hM : ∑ y, (ν y - min (μ y) (ν y)) = ∑ x, (μ x - min (μ x) (ν x)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hmass]
  obtain ⟨ρ, hρ, -⟩ := exists_piece_coupling (d := fun _ _ => (0 : ℝ)) hP hN rfl hM le_rfl
    (fun _ _ _ _ => le_rfl)
  exact ⟨ρ, hρ⟩

/-- `W₁` depends only on the residuals (Villani, Corollary 1.16). The triangle inequality is
needed only through the vertices where both measures are positive. -/
theorem W1_eq_W1_resid {μ ν : V → ℝ} (hμ : ∀ x, 0 ≤ μ x) (hν : ∀ x, 0 ≤ ν x)
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
    obtain ⟨ρ, hρ, hcost⟩ := exists_resid_coupling_le (d := d) hπ hμ hν hself hT
    exact (W1_le_cost hd0 hρ).trans hcost

theorem exists_extension {μ ν : V → ℝ} {π : V → V → ℝ} (hπ : IsSubPlan μ ν π)
    (hmass : ∑ x, μ x = ∑ y, ν y) (h3 : ∀ x y, 0 < μ x → 0 < ν y → d x y ≤ 3) :
    ∃ ρ, IsCoupling μ ν ρ ∧ savings d π ≤ savings d ρ := by
  have hμr : ∀ x, 0 ≤ μ x - ∑ y, π x y := fun x => sub_nonneg.2 (hπ.2.1 x)
  have hνr : ∀ y, 0 ≤ ν y - ∑ x, π x y := fun y => sub_nonneg.2 (hπ.2.2 y)
  have hM : ∑ y, (ν y - ∑ x, π x y) = ∑ x, (μ x - ∑ y, π x y) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hmass, Finset.sum_comm]
  have hdist : ∀ x y, 0 < μ x - ∑ y, π x y → 0 < ν y - ∑ x, π x y → d x y ≤ 3 := by
    intro x y hx hy
    have hx' : 0 ≤ ∑ y, π x y := Finset.sum_nonneg fun y _ => hπ.1 x y
    have hy' : 0 ≤ ∑ x, π x y := Finset.sum_nonneg fun x _ => hπ.1 x y
    exact h3 x y (by linarith) (by linarith)
  obtain ⟨σ, hσ, hσc⟩ := exists_piece_coupling (d := d) hμr hνr rfl hM (by norm_num) hdist
  refine ⟨fun x y => π x y + σ x y,
    ⟨fun x y => add_nonneg (hπ.1 x y) (hσ.1 x y), fun x => ?_, fun y => ?_⟩, ?_⟩
  · show ∑ y, (π x y + σ x y) = μ x
    calc ∑ y, (π x y + σ x y) = ∑ y, π x y + ∑ y, σ x y := Finset.sum_add_distrib
      _ = ∑ y, π x y + (μ x - ∑ y, π x y) := by rw [hσ.2.1 x]
      _ = μ x := by ring
  · show ∑ x, (π x y + σ x y) = ν y
    calc ∑ x, (π x y + σ x y) = ∑ x, π x y + ∑ x, σ x y := Finset.sum_add_distrib
      _ = ∑ x, π x y + (ν y - ∑ x, π x y) := by rw [hσ.2.2 y]
      _ = ν y := by ring
  · have hs : savings d (fun x y => π x y + σ x y) = savings d π + savings d σ := by
      unfold savings
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    have hσs : 0 ≤ savings d σ := by
      have hm' : mass σ = ∑ x, (μ x - ∑ y, π x y) := hσ.mass_eq
      have h := cost_eq_three_mass_sub_savings (d := d) σ
      rw [hm'] at h
      linarith
    rw [hs]
    linarith

theorem isLUB_savings {c : V → V → ℝ} {α β : V → ℝ} (hmass : ∑ x, α x = ∑ y, β y)
    (hc : ∀ x y, 0 ≤ c x y) (h3 : ∀ x y, 0 < α x → 0 < β y → c x y ≤ 3)
    (hne : ∃ ρ, IsCoupling α β ρ) :
    IsLUB (savings c '' {π | IsSubPlan α β π}) (3 * ∑ x, α x - W1 c α β) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨π, hπ, rfl⟩
    have hπ' : IsSubPlan α β π := hπ
    obtain ⟨ρ, hρ, hsav⟩ := exists_extension (d := c) hπ' hmass h3
    have hW := W1_le_cost hc hρ
    rw [cost_eq_three_mass_sub_savings, hρ.mass_eq] at hW
    linarith
  · intro s hs
    have hW : 3 * ∑ x, α x - s ≤ W1 c α β := le_W1 hne fun ρ hρ => by
      have hρs := hs ⟨ρ, ⟨hρ.1, fun x => (hρ.2.1 x).le, fun y => (hρ.2.2 y).le⟩, rfl⟩
      rw [cost_eq_three_mass_sub_savings, hρ.mass_eq]
      linarith
    linarith

lemma sum_le_savings_of_le {c c' : V → V → ℝ} {π : V → V → ℝ} (hπ : ∀ x y, 0 ≤ π x y)
    (h : ∀ x y, 0 < π x y → c x y ≤ c' x y) :
    ∑ x, ∑ y, (3 - c' x y) * π x y ≤ savings c π := by
  unfold savings
  refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
  rcases (hπ x y).eq_or_lt with h0 | h0
  · rw [← h0]
    simp
  · exact mul_le_mul_of_nonneg_right (by linarith [h x y h0]) h0.le

section

variable {α β : V → ℝ}

lemma isSubPlan_zero (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y) :
    IsSubPlan α β (fun _ _ => 0) :=
  ⟨fun _ _ => le_rfl, fun x => by simpa using hα x, fun y => by simpa using hβ y⟩

lemma IsSubPlan.le_row {π : V → V → ℝ} (hπ : IsSubPlan α β π) (x y : V) : π x y ≤ α x :=
  (Finset.single_le_sum (f := fun y' => π x y') (fun y' _ => hπ.1 x y') (Finset.mem_univ y)).trans
    (hπ.2.1 x)

lemma isClosed_subPlan : IsClosed {π : V → V → ℝ | IsSubPlan α β π} := by
  have hset : {π : V → V → ℝ | IsSubPlan α β π} =
      (⋂ x, ⋂ y, {π : V → V → ℝ | 0 ≤ π x y}) ∩
        ((⋂ x, {π : V → V → ℝ | ∑ y, π x y ≤ α x}) ∩ ⋂ y, {π : V → V → ℝ | ∑ x, π x y ≤ β y}) := by
    ext π
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact Iff.rfl
  rw [hset]
  exact (isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const (by fun_prop)).inter
    ((isClosed_iInter fun x => isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_iInter fun y => isClosed_le (by fun_prop) continuous_const))

theorem exists_max_subPlan (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y)
    (P : (V → V → ℝ) → Prop) (hP : IsClosed {π | P π}) (hP0 : P fun _ _ => 0)
    (f : (V → V → ℝ) → ℝ) (hf : Continuous f) :
    ∃ π, IsSubPlan α β π ∧ P π ∧ ∀ π', IsSubPlan α β π' → P π' → f π' ≤ f π := by
  have hsub : ({π : V → V → ℝ | IsSubPlan α β π} ∩ {π | P π}) ⊆
      Set.univ.pi fun x => Set.univ.pi fun _ : V => Set.Icc (0 : ℝ) (α x) := by
    intro π hπ
    have hπS : IsSubPlan α β π := hπ.1
    rw [Set.mem_univ_pi]
    intro x
    rw [Set.mem_univ_pi]
    intro y
    exact ⟨hπS.1 x y, hπS.le_row x y⟩
  have hcomp : IsCompact ({π : V → V → ℝ | IsSubPlan α β π} ∩ {π | P π}) :=
    (isCompact_univ_pi fun x => isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset
      ((isClosed_subPlan (α := α) (β := β)).inter hP) hsub
  have hne : ({π : V → V → ℝ | IsSubPlan α β π} ∩ {π | P π}).Nonempty :=
    ⟨fun _ _ => 0, isSubPlan_zero hα hβ, hP0⟩
  obtain ⟨π, hπ, hmax⟩ := hcomp.exists_isMaxOn hne hf.continuousOn
  exact ⟨π, hπ.1, hπ.2, fun π' h1 h2 => isMaxOn_iff.mp hmax π' ⟨h1, h2⟩⟩

lemma continuous_savings (c : V → V → ℝ) : Continuous (savings c) := by
  show Continuous fun π : V → V → ℝ => ∑ x, ∑ y, (3 - c x y) * π x y
  fun_prop

lemma isGreatest_of_isLUB (hα : ∀ x, 0 ≤ α x) (hβ : ∀ y, 0 ≤ β y)
    {f : (V → V → ℝ) → ℝ} (hf : Continuous f) {a : ℝ} (h : IsLUB (f '' {π | IsSubPlan α β π}) a) :
    IsGreatest (f '' {π | IsSubPlan α β π}) a := by
  have hP : IsClosed {π : V → V → ℝ | True} := by
    rw [Set.ofPred_true]
    exact isClosed_univ
  obtain ⟨π, hπ, -, hmax⟩ := exists_max_subPlan hα hβ (fun _ => True) hP trivial f hf
  have hG : IsGreatest (f '' {π | IsSubPlan α β π}) (f π) :=
    ⟨⟨π, hπ, rfl⟩, by
      rintro _ ⟨π', hπ', rfl⟩
      exact hmax π' hπ' trivial⟩
  rw [le_antisymm (h.2 hG.2) (h.1 hG.1)]
  exact hG

end

end OllivierBF
