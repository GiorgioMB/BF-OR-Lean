/-
  Measures and curvatures.
-/
import OllivierBF.Graph

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Uniform-idleness measure `m_u^p = p δ_u + (1 − p) ν_u`. -/
noncomputable def mp (p : ℝ) (u : V) : V → ℝ := fun k =>
  if k = u then p else if G.Adj u k then (1 - p) / ρ G u else 0

/-- Lazy weight `w_u = 1/(ρ_u + 1)`. -/
noncomputable def w (u : V) : ℝ := 1 / (ρ G u + 1)

/-- Lazy measure (Definition `def:lazy-rw`): uniform on the closed neighbourhood. -/
noncomputable def mLazy (u : V) : V → ℝ := mp G (w G u) u

/-- Dirac mass. -/
def dirac (u : V) : V → ℝ := fun k => if k = u then 1 else 0

variable (d : V → V → ℝ)

/-- `𝔠_{OR-p}`. -/
noncomputable def cORp (p : ℝ) (i j : V) : ℝ := 1 - W1 d (mp G p i) (mp G p j)

/-- Lazy OR curvature `𝔠_OR`. -/
noncomputable def cOR (i j : V) : ℝ := 1 - W1 d (mLazy G i) (mLazy G j)

/-- Non-lazy OR curvature `𝔠_{OR-0}`. -/
noncomputable def cOR0 (i j : V) : ℝ := cORp G d 0 i j

/-- LLY curvature, as the left limit at `p = 1` of `𝔠_{OR-p}/(1 − p)`. -/
noncomputable def cLLY (i j : V) : ℝ :=
  Filter.limUnder (nhdsWithin (1 : ℝ) (Set.Iio 1)) (fun p => cORp G d p i j / (1 - p))

/-! ### Balanced Forman curvature (Topping et al., Definition 1) -/

noncomputable def ρmax (i j : V) : ℝ := max (ρ G i) (ρ G j)
noncomputable def ρmin (i j : V) : ℝ := min (ρ G i) (ρ G j)

/-- `𝔖 = 2/ρ_i + 2/ρ_j − 2`. -/
noncomputable def bfS (i j : V) : ℝ := 2 / ρ G i + 2 / ρ G j - 2
/-- `𝔗 = 2/ρ_max + 1/ρ_min`. -/
noncomputable def bfT (i j : V) : ℝ := 2 / ρmax G i j + 1 / ρmin G i j
/-- 4-cycle term `𝔠_4 = Ξ/(ϖ_max ρ_max)` (zero if `ϖ_max = 0`). -/
noncomputable def C4 (i j : V) : ℝ :=
  if varpi G i j = 0 then 0 else (Xi G i j : ℝ) / ((varpi G i j : ℝ) * ρmax G i j)

/-- Balanced Forman curvature. -/
noncomputable def cBF (i j : V) : ℝ :=
  if ρmin G i j ≤ 1 then 0 else bfS G i j + bfT G i j * tri G i j + C4 G i j

/-- Matching statistic `𝒮 = 𝔪/ρ_max`. -/
noncomputable def matchStat (i j : V) : ℝ := (matchNum G i j : ℝ) / ρmax G i j

/-! ### Cited results (hypotheses, not axioms)

Every theorem that needs one of these takes `CitedFacts G d` as an argument. -/

structure CitedFacts : Prop where
  /-- Bourne et al. (2018), Thm 1.1 and Thm 5.5: `𝔠_{OR-p} = (1 − p) 𝔠_LLY` at
  `p₀ = 1/(ρ_max + 1)`. -/
  bourne : ∀ i j, G.Adj i j →
    cORp G d (1 / (ρmax G i j + 1)) i j = (1 - 1 / (ρmax G i j + 1)) * cLLY G d i j
  /-- Topping et al. (2022), Thm 2: `𝔠_BF ≤ 𝔠_LLY`. -/
  topping : ∀ i j, G.Adj i j → cBF G i j ≤ cLLY G d i j
  /-- Topping et al. (2022), Lemma 11, in the form `𝔠_4 ≤ 2 𝒮`. -/
  topping11 : ∀ i j, G.Adj i j → 2 ≤ ρmin G i j → C4 G i j ≤ 2 * matchStat G i j
  /-- Villani (2003), Cor. 1.16: saturating the diagonal never increases the cost. -/
  saturate : ∀ μ ν : V → ℝ, ∀ π, IsCoupling μ ν π →
    ∃ π', IsCoupling μ ν π' ∧ (∀ k, π' k k = min (μ k) (ν k)) ∧ cost d π' ≤ cost d π

variable {G d}

/-! ### Basic facts about the measures -/

lemma ρ_pos {u v : V} (huv : G.Adj u v) : 0 < ρ G u := by
  have : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).2 ⟨v, huv⟩
  simp only [ρ]; exact_mod_cast this

lemma w_pos (u : V) : 0 < w G u := by
  have : (0 : ℝ) ≤ ρ G u := by simp only [ρ]; positivity
  simp only [w]; positivity

/-- For an edge endpoint, `(1 − w_u)/ρ_u = w_u`. -/
lemma lazy_nbr_weight {u v : V} (huv : G.Adj u v) : (1 - w G u) / ρ G u = w G u := by
  have h := ρ_pos huv
  have h1 : ρ G u + 1 ≠ 0 := by linarith
  rw [div_eq_iff h.ne']
  simp only [w]
  field_simp
  ring

/-- `w_u < 1` at an edge endpoint. -/
lemma w_lt_one {u v : V} (huv : G.Adj u v) : w G u < 1 := by
  have h := ρ_pos huv
  simp only [w]; rw [div_lt_one (by linarith)]; linarith

/-- The lazy measure is `w_u` on the closed neighbourhood. -/
lemma mLazy_apply {u v : V} (huv : G.Adj u v) (k : V) :
    mLazy G u k = if k = u ∨ G.Adj u k then w G u else 0 := by
  simp only [mLazy, mp]
  by_cases h1 : k = u
  · simp [h1]
  · by_cases h2 : G.Adj u k
    · simp [h1, h2, lazy_nbr_weight huv]
    · simp [h1, h2]

lemma mp_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u k : V) : 0 ≤ mp G p u k := by
  have : 0 ≤ ρ G u := by simp only [ρ]; positivity
  simp only [mp]
  split_ifs
  · exact hp0
  · exact div_nonneg (by linarith) this
  · exact le_rfl

lemma mp_sum {p : ℝ} {u v : V} (huv : G.Adj u v) : ∑ k, mp G p u k = 1 := by
  have hρ := ρ_pos huv
  have hsplit : ∀ k, mp G p u k =
      (if k = u then p else 0) + (if G.Adj u k then (1 - p) / ρ G u else 0) := by
    intro k
    by_cases h1 : k = u
    · subst h1; simp [mp, SimpleGraph.irrefl]
    · simp [mp, h1]
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_filter, ← SimpleGraph.neighborFinset_eq_filter, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  have key : (G.degree u : ℝ) * ((1 - p) / ρ G u) = 1 - p := by
    simp only [ρ] at hρ ⊢
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hρ.ne', mul_one]
  linarith

lemma mLazy_nonneg (u k : V) : 0 ≤ mLazy G u k := by
  have h := w_pos (G := G) u
  have h1 : w G u ≤ 1 := by
    have : (0 : ℝ) ≤ ρ G u := by simp only [ρ]; positivity
    simp only [w]; rw [div_le_one (by linarith)]; linarith
  exact mp_nonneg h.le h1 u k

lemma mLazy_sum {u v : V} (huv : G.Adj u v) : ∑ k, mLazy G u k = 1 := mp_sum huv

lemma exists_coupling_lazy {i j : V} (hij : G.Adj i j) :
    ∃ π, IsCoupling (mLazy G i) (mLazy G j) π :=
  exists_coupling_prob (mLazy_nonneg i) (mLazy_nonneg j) (mLazy_sum hij) (mLazy_sum hij.symm)

/-! ### One-sided residuals (Lemma `lem:one-sided`)

For `ρ_i ≤ ρ_j` (so `w_j ≤ w_i`), all residual demand of `m_j` over `m_i` sits on `U_j`. -/

/-- The overlap set `{i, j} ∪ C`. -/
def overlap (i j : V) : Finset V := insert i (insert j (common G i j))

lemma w_anti {i j : V} (hle : ρ G i ≤ ρ G j) : w G j ≤ w G i := by
  have : (0 : ℝ) ≤ ρ G i := by simp only [ρ]; positivity
  simp only [w]; exact one_div_le_one_div_of_le (by linarith) (by linarith)

lemma lazy_min {i j : V} (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) (k : V) :
    min (mLazy G i k) (mLazy G j k) = if k ∈ overlap (G := G) i j then w G j else 0 := by
  have hw := w_anti (G := G) hle
  have hi0 := (w_pos (G := G) i).le
  have hj0 := (w_pos (G := G) j).le
  rw [mLazy_apply hij, mLazy_apply hij.symm]
  simp only [overlap, Finset.mem_insert, mem_common]
  by_cases hki : k = i
  · rw [hki]; simp [hij.symm, min_eq_right hw]
  by_cases hkj : k = j
  · rw [hkj]; simp [hij, hij.ne', min_eq_right hw]
  by_cases ha : G.Adj i k <;> by_cases hb : G.Adj j k <;>
    simp [hki, hkj, ha, hb, min_eq_right hw, min_eq_right hi0, min_eq_left hj0]

lemma lazy_resid_i {i j : V} (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) (k : V) :
    mLazy G i k - min (mLazy G i k) (mLazy G j k) =
      (if k ∈ overlap (G := G) i j then w G i - w G j else 0) +
      (if k ∈ uniq G i j then w G i else 0) := by
  rw [lazy_min hij hle, mLazy_apply hij]
  simp only [overlap, Finset.mem_insert, mem_common, mem_uniq]
  by_cases hki : k = i
  · rw [hki]; simp [hij.ne, SimpleGraph.irrefl]
  by_cases hkj : k = j
  · rw [hkj]; simp [hij, hij.ne', SimpleGraph.irrefl]
  by_cases ha : G.Adj i k <;> by_cases hb : G.Adj j k <;> simp [hki, hkj, ha, hb]

lemma lazy_resid_j {i j : V} (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) (k : V) :
    mLazy G j k - min (mLazy G i k) (mLazy G j k) =
      if k ∈ uniq G j i then w G j else 0 := by
  rw [lazy_min hij hle, mLazy_apply hij.symm]
  simp only [overlap, Finset.mem_insert, mem_common, mem_uniq]
  by_cases hki : k = i
  · rw [hki]; simp [hij.symm, hij.ne, SimpleGraph.irrefl]
  by_cases hkj : k = j
  · rw [hkj]; simp [hij, hij.ne', SimpleGraph.irrefl]
  by_cases ha : G.Adj i k <;> by_cases hb : G.Adj j k <;> simp [hki, hkj, ha, hb]

lemma card_overlap {i j : V} (hij : G.Adj i j) :
    ((overlap (G := G) i j).card : ℝ) = 2 + tri G i j := by
  have hi : i ∉ insert j (common G i j) := by
    simp [mem_common, hij.ne, SimpleGraph.irrefl]
  have hj : j ∉ common G i j := by simp [mem_common, SimpleGraph.irrefl]
  simp only [overlap, Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hj, tri]
  push_cast; ring

end OllivierBF
