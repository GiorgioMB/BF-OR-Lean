/-
  Theorem 5.2 of the paper: the full range of the curvature over the graphs consistent with the
  building blocks of an edge.

  The building blocks of `(i, j)` are the lists of the vertices of `listed` (`i`, `j`, `U_i`, `C`) and
  the degrees of the vertices of `known` (`listed` and everything in its lists). A graph `G'` on any
  vertex type is consistent with them through `e : V → V'`, injective on `known`, if the vertices of
  `listed` have the same lists and those of `known` the same degrees (`Consistent`); the measures of
  `G'` at `e i` and `e j` are those of `G`, carried by `e` (`Agrees`), which is what locality gives.
  A set `F` of candidate pairs `{u, y}` (`y ∈ U_j`, `u ∈ (U_j ∪ Z) \ {y}`) is admissible if every
  vertex lies in at most its free degree of pairs; `chargedDist F` is the distance of the theorem and
  `kappaF F = 1 − W₁` with it.

  * `range_bounds`: a consistent graph, with a metric that is a graph metric and separates vertices
    without short paths, has curvature `kappaF` of its own pairs, between `kappaF ∅` and `kappaMax`;
  * `realize F`: the listed edges, the pairs of `F`, and pendant vertices that complete the degrees,
    connected and consistent, with curvature `kappaF F` (`realize_kappa`);
  * `exact_range_paper`: Theorem 5.2.
-/
module

public import OllivierBF.TQ

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V)

/-! ### The building blocks -/

/-- The vertices whose lists are known: `i`, `j`, `U_i` and `C`. -/
def listed : Finset V := insert i (insert j (uniq G i j ∪ common G i j))

/-- The vertices whose degrees are known: `listed` and everything in its lists. -/
def known : Finset V := listed G i j ∪ (listed G i j).biUnion (fun v => G.neighborFinset v)

/-- `Z`: the vertices outside `N[i] ∪ N[j]` adjacent to `U_i`. -/
def outsideZ : Finset V :=
  ((uniq G i j).biUnion (fun v => G.neighborFinset v)).filter
    (fun z => z ≠ i ∧ z ≠ j ∧ ¬ G.Adj i z ∧ ¬ G.Adj j z)

/-- The candidate pairs `{u, y}`: `y ∈ U_j` and `u ∈ (U_j ∪ Z) \ {y}`. -/
def cand : Finset (Sym2 V) :=
  (((uniq G j i ∪ outsideZ G i j) ×ˢ uniq G j i).filter (fun p => p.1 ≠ p.2)).image (fun p => s(p.1, p.2))

/-- The number of listed edges at `v`, that is, of its edges to vertices of `listed`. -/
def listedDeg (v : V) : ℕ := ((listed G i j).filter (G.Adj v)).card

/-- The free degree `d̄_v`: the degree minus the listed edges. -/
def freeDeg (v : V) : ℕ := G.degree v - listedDeg G i j v

/-- The number of pairs of `F` at `v`. -/
def pairDeg (F : Finset (Sym2 V)) (v : V) : ℕ := (univ.filter (fun q => s(v, q) ∈ F)).card

/-- `F` is admissible: candidate pairs, at most `d̄_v` of them at every vertex `v`. -/
def Admissible (F : Finset (Sym2 V)) : Prop :=
  F ⊆ cand G i j ∧ ∀ v, pairDeg F v ≤ freeDeg G i j v

/-- The admissible sets. -/
def admissibleSets : Finset (Finset (Sym2 V)) :=
  (cand G i j).powerset.filter (fun F => ∀ v, pairDeg F v ≤ freeDeg G i j v)

/-! ### The distance and the curvature of Theorem 5.2 -/

/-- The distance of a pair `(x, y) ∈ U_i × U_j` for the pairs `F`. -/
def crossDist (F : Finset (Sym2 V)) (x y : V) : ℝ :=
  if G.Adj x y then 1
  else if (∃ w ∈ uniq G i j ∪ common G i j, G.Adj x w ∧ G.Adj w y) ∨ (∃ w, G.Adj x w ∧ s(w, y) ∈ F)
  then 2 else 3

/-- The distance of Theorem 5.2: `crossDist` on `U_i × U_j`, and `1` or `2` on the other pairs. -/
def chargedDist (F : Finset (Sym2 V)) (p q : V) : ℝ :=
  if p = q then 0
  else if p ∈ uniq G i j ∧ q ∈ uniq G j i then crossDist G i j F p q
  else if q ∈ uniq G i j ∧ p ∈ uniq G j i then crossDist G i j F q p
  else if G.Adj p q then 1 else 2

/-- The curvature for the pairs `F`. -/
noncomputable def kappaF (μ : V → V → ℝ) (F : Finset (Sym2 V)) : ℝ := cORm (chargedDist G i j F) μ i j

lemma empty_mem_admissibleSets : (∅ : Finset (Sym2 V)) ∈ admissibleSets G i j := by
  unfold admissibleSets
  rw [Finset.mem_filter]
  refine ⟨Finset.empty_mem_powerset _, fun v => ?_⟩
  unfold pairDeg
  simp

/-- The upper end `κ̄*`: the largest `kappaF F` over admissible `F`. -/
noncomputable def kappaMax (μ : V → V → ℝ) : ℝ :=
  (admissibleSets G i j).sup' ⟨∅, empty_mem_admissibleSets G i j⟩ (kappaF G i j μ)

/-! ### Consistent graphs -/

/-- `G'` is consistent with the building blocks of `(i, j)` in `G` through `e`. -/
structure Consistent {V' : Type u} [Fintype V'] [DecidableEq V'] (G' : SimpleGraph V')
    [DecidableRel G'.Adj] (e : V → V') : Prop where
  inj : Set.InjOn e (known G i j)
  lists : ∀ v ∈ listed G i j, ∀ w', G'.Adj (e v) w' ↔ ∃ w, G.Adj v w ∧ e w = w'
  degrees : ∀ w ∈ known G i j, G'.degree (e w) = G.degree w

/-- The measures `μ'` of `G'` at `e i` and `e j` are those of `G` at `i` and `j`, carried by `e`. -/
def Agrees (μ : V → V → ℝ) {V' : Type u} (μ' : V' → V' → ℝ) (e : V → V') : Prop :=
  ∀ v, (v = i ∨ v = j) →
    (∀ k ∈ known G i j, μ' (e v) (e k) = μ v k) ∧ (∀ x', (∀ k ∈ known G i j, e k ≠ x') → μ' (e v) x' = 0)

/-- The candidate pairs that are edges of `G'`. -/
def pairsOf {V' : Type u} (G' : SimpleGraph V') [DecidableRel G'.Adj] (e : V → V') : Finset (Sym2 V) :=
  (cand G i j).filter (fun z => Sym2.lift ⟨fun a b => decide (G'.Adj (e a) (e b)),
    fun a b => decide_eq_decide.mpr (G'.adj_comm (e a) (e b))⟩ z = true)

variable {G i j}

/-! ### Membership -/

lemma i_listed : i ∈ listed G i j := by simp [listed]

lemma j_listed : j ∈ listed G i j := by simp [listed]

lemma uniq_listed {x : V} (hx : x ∈ uniq G i j) : x ∈ listed G i j := by simp [listed, hx]

lemma common_listed {k : V} (hk : k ∈ common G i j) : k ∈ listed G i j := by simp [listed, hk]

lemma listed_known {v : V} (hv : v ∈ listed G i j) : v ∈ known G i j := Finset.mem_union_left _ hv

lemma nbr_known {v w : V} (hv : v ∈ listed G i j) (hw : G.Adj v w) : w ∈ known G i j :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, hv, (G.mem_neighborFinset v w).mpr hw⟩)

lemma closed_i_known {p : V} (hp : p = i ∨ G.Adj i p) : p ∈ known G i j := by
  rcases hp with rfl | h
  · exact listed_known i_listed
  · exact nbr_known i_listed h

lemma closed_j_known {q : V} (hq : q = j ∨ G.Adj j q) : q ∈ known G i j := by
  rcases hq with rfl | h
  · exact listed_known j_listed
  · exact nbr_known j_listed h

lemma mem_listed {v : V} :
    v ∈ listed G i j ↔ v = i ∨ v = j ∨ v ∈ uniq G i j ∨ v ∈ common G i j := by
  simp [listed]

lemma uniq_j_not_listed {y : V} (hy : y ∈ uniq G j i) : y ∉ listed G i j := by
  rw [mem_uniq] at hy
  obtain ⟨hyi, hjy, hiy⟩ := hy
  rw [mem_listed, mem_uniq, mem_common]
  rintro (h | h | ⟨-, h, -⟩ | ⟨h, -⟩)
  · exact hyi h
  · exact G.ne_of_adj hjy h.symm
  · exact hiy h
  · exact hiy h

lemma outsideZ_not_listed {z : V} (hz : z ∈ outsideZ G i j) : z ∉ listed G i j := by
  simp only [outsideZ, Finset.mem_filter] at hz
  obtain ⟨-, hzi, hzj, hiz, -⟩ := hz
  rw [mem_listed, mem_uniq, mem_common]
  rintro (h | h | ⟨-, h, -⟩ | ⟨h, -⟩)
  · exact hzi h
  · exact hzj h
  · exact hiz h
  · exact hiz h

lemma outsideZ_known {z : V} (hz : z ∈ outsideZ G i j) : z ∈ known G i j := by
  simp only [outsideZ, Finset.mem_filter, Finset.mem_biUnion] at hz
  obtain ⟨⟨x, hx, hxz⟩, -⟩ := hz
  exact nbr_known (uniq_listed hx) ((G.mem_neighborFinset x z).mp hxz)

/-- The vertices of a candidate pair are known, not listed, and distinct. -/
lemma cand_vertices {a b : V} (h : s(a, b) ∈ cand G i j) :
    a ∈ known G i j ∧ a ∉ listed G i j ∧ b ∈ known G i j ∧ b ∉ listed G i j ∧ a ≠ b := by
  simp only [cand, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at h
  obtain ⟨⟨u, y⟩, ⟨⟨hu, hy⟩, huy⟩, hs⟩ := h
  have hU : ∀ w, w ∈ uniq G j i ∪ outsideZ G i j → w ∈ known G i j ∧ w ∉ listed G i j := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact ⟨nbr_known j_listed ((mem_uniq.mp hw).2.1), uniq_j_not_listed hw⟩
    · exact ⟨outsideZ_known hw, outsideZ_not_listed hw⟩
  have hY : y ∈ known G i j ∧ y ∉ listed G i j := hU y (Finset.mem_union_left _ hy)
  rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨(hU _ hu).1, (hU _ hu).2, hY.1, hY.2, huy⟩
  · exact ⟨hY.1, hY.2, (hU _ hu).1, (hU _ hu).2, fun h => huy h.symm⟩

lemma mem_cand_of {w y : V} (hw : w ∈ uniq G j i ∪ outsideZ G i j) (hy : y ∈ uniq G j i)
    (hwy : w ≠ y) : s(w, y) ∈ cand G i j := by
  simp only [cand, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  exact ⟨(w, y), ⟨⟨hw, hy⟩, hwy⟩, rfl⟩

lemma mem_pairsOf {V' : Type u} [Fintype V'] [DecidableEq V'] {G' : SimpleGraph V'}
    [DecidableRel G'.Adj] {e : V → V'} {a b : V} :
    s(a, b) ∈ pairsOf G i j G' e ↔ s(a, b) ∈ cand G i j ∧ G'.Adj (e a) (e b) := by
  simp [pairsOf]

lemma pairsOf_subset {V' : Type u} [Fintype V'] [DecidableEq V'] {G' : SimpleGraph V'}
    [DecidableRel G'.Adj] {e : V → V'} : pairsOf G i j G' e ⊆ cand G i j :=
  Finset.filter_subset _ _

lemma mem_admissibleSets {F : Finset (Sym2 V)} : F ∈ admissibleSets G i j ↔ Admissible G i j F := by
  simp [admissibleSets, Admissible]

/-! ### The distance is nonnegative and decreases with `F` -/

lemma crossDist_nonneg (F : Finset (Sym2 V)) (x y : V) : 0 ≤ crossDist G i j F x y := by
  unfold crossDist
  split_ifs <;> norm_num

lemma chargedDist_nonneg (F : Finset (Sym2 V)) (p q : V) : 0 ≤ chargedDist G i j F p q := by
  unfold chargedDist
  split_ifs
  · exact le_rfl
  · exact crossDist_nonneg F p q
  · exact crossDist_nonneg F q p
  · norm_num
  · norm_num

lemma crossDist_anti {F F' : Finset (Sym2 V)} (h : F ⊆ F') (x y : V) :
    crossDist G i j F' x y ≤ crossDist G i j F x y := by
  unfold crossDist
  by_cases ha : G.Adj x y
  · rw [ite_eq_left ha, ite_eq_left ha]
  · rw [ite_eq_right ha, ite_eq_right ha]
    by_cases hF : (∃ w ∈ uniq G i j ∪ common G i j, G.Adj x w ∧ G.Adj w y) ∨
        (∃ w, G.Adj x w ∧ s(w, y) ∈ F)
    · have hF' : (∃ w ∈ uniq G i j ∪ common G i j, G.Adj x w ∧ G.Adj w y) ∨
          (∃ w, G.Adj x w ∧ s(w, y) ∈ F') := by
        rcases hF with hk | ⟨w, hw, hm⟩
        · exact Or.inl hk
        · exact Or.inr ⟨w, hw, h hm⟩
      rw [ite_eq_left hF, ite_eq_left hF']
    · rw [ite_eq_right hF]
      split_ifs <;> norm_num

lemma chargedDist_anti {F F' : Finset (Sym2 V)} (h : F ⊆ F') (p q : V) :
    chargedDist G i j F' p q ≤ chargedDist G i j F p q := by
  unfold chargedDist
  split_ifs
  · exact le_rfl
  · exact crossDist_anti h p q
  · exact crossDist_anti h q p
  · exact le_rfl
  · exact le_rfl

lemma W1_mono {c c' : V → V → ℝ} {α β : V → ℝ} (hc : ∀ x y, 0 ≤ c x y)
    (hcc : ∀ x y, c x y ≤ c' x y) (hne : ∃ π, IsCoupling α β π) : W1 c α β ≤ W1 c' α β := by
  refine le_W1 hne fun π hπ => (W1_le_cost hc hπ).trans ?_
  unfold cost
  exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_right (hcc x y) (hπ.1 x y)

lemma kappaF_mono {μ : V → V → ℝ} (hi : OneStepAt G μ i) (hj : OneStepAt G μ j)
    {F F' : Finset (Sym2 V)} (h : F ⊆ F') : kappaF G i j μ F ≤ kappaF G i j μ F' := by
  unfold kappaF cORm
  have := W1_mono (c := chargedDist G i j F') (c' := chargedDist G i j F) (α := μ i) (β := μ j)
    (chargedDist_nonneg F') (chargedDist_anti h)
    (exists_coupling_prob hi.nonneg hj.nonneg hi.mass hj.mass)
  linarith

/-! ### Distances in a consistent graph -/

section consistent

variable {V' : Type u} [Fintype V'] [DecidableEq V'] {G' : SimpleGraph V'} [DecidableRel G'.Adj]
variable {e : V → V'}

lemma Consistent.adj_iff (hc : Consistent G i j G' e) {v w : V} (hv : v ∈ listed G i j)
    (hw : w ∈ known G i j) : G'.Adj (e v) (e w) ↔ G.Adj v w := by
  rw [hc.lists v hv]
  constructor
  · rintro ⟨w₀, hvw₀, he⟩
    rwa [← hc.inj (nbr_known hv hvw₀) hw he]
  · exact fun h => ⟨w, h, rfl⟩

lemma Consistent.adj_iff' (hc : Consistent G i j G' e) {v w : V} (hv : v ∈ listed G i j)
    (hw : w ∈ known G i j) : G'.Adj (e w) (e v) ↔ G.Adj w v := by
  rw [G'.adj_comm, G.adj_comm]
  exact hc.adj_iff hv hw

lemma Consistent.ne (hc : Consistent G i j G' e) {p q : V} (hp : p ∈ known G i j)
    (hq : q ∈ known G i j) (hpq : p ≠ q) : e p ≠ e q :=
  fun h => hpq (hc.inj hp hq h)

/-- In a consistent graph, a pair of `U_i × U_j` has a common neighbour if and only if it has one in
`C ∪ U_i` or through a pair of the graph. -/
lemma Consistent.common_nbr (hc : Consistent G i j G' e) {x y : V} (hx : x ∈ uniq G i j)
    (hy : y ∈ uniq G j i) (hxy : ¬ G.Adj x y) :
    (∃ w', G'.Adj (e x) w' ∧ G'.Adj w' (e y)) ↔
      ((∃ w ∈ uniq G i j ∪ common G i j, G.Adj x w ∧ G.Adj w y) ∨
        (∃ w, G.Adj x w ∧ s(w, y) ∈ pairsOf G i j G' e)) := by
  have hxL := uniq_listed hx
  have hyK : y ∈ known G i j := nbr_known j_listed (mem_uniq.mp hy).2.1
  constructor
  · rintro ⟨w', h1, h2⟩
    obtain ⟨w, hxw, rfl⟩ := (hc.lists x hxL w').mp h1
    have hwK : w ∈ known G i j := nbr_known hxL hxw
    by_cases hwL : w ∈ uniq G i j ∪ common G i j
    · have hwl : w ∈ listed G i j := by
        rcases Finset.mem_union.mp hwL with h | h
        · exact uniq_listed h
        · exact common_listed h
      exact Or.inl ⟨w, hwL, hxw, (hc.adj_iff hwl hyK).mp h2⟩
    · refine Or.inr ⟨w, hxw, mem_pairsOf.mpr ⟨?_, h2⟩⟩
      obtain ⟨hyi, hjy, hiy⟩ := mem_uniq.mp hy
      obtain ⟨hxj, hix, hjx⟩ := mem_uniq.mp hx
      have hwi : w ≠ i := by
        rintro rfl
        exact hiy ((hc.adj_iff i_listed hyK).mp h2)
      have hwj : w ≠ j := by
        rintro rfl
        exact hjx hxw.symm
      have hwy : w ≠ y := by
        rintro rfl
        exact hxy hxw
      refine mem_cand_of ?_ hy hwy
      by_cases hjw : G.Adj j w
      · refine Finset.mem_union_left _ (mem_uniq.mpr ⟨hwi, hjw, fun hiw => hwL ?_⟩)
        exact Finset.mem_union_right _ (mem_common.mpr ⟨hiw, hjw⟩)
      · refine Finset.mem_union_right _ ?_
        simp only [outsideZ, Finset.mem_filter, Finset.mem_biUnion]
        refine ⟨⟨x, hx, (G.mem_neighborFinset x w).mpr hxw⟩, hwi, hwj, fun hiw => hwL ?_, hjw⟩
        exact Finset.mem_union_left _ (mem_uniq.mpr ⟨hwj, hiw, hjw⟩)
  · rintro (⟨w, hw, hxw, hwy⟩ | ⟨w, hxw, hm⟩)
    · have hwl : w ∈ listed G i j := by
        rcases Finset.mem_union.mp hw with h | h
        · exact uniq_listed h
        · exact common_listed h
      exact ⟨e w, (hc.adj_iff hxL (listed_known hwl)).mpr hxw, (hc.adj_iff hwl hyK).mpr hwy⟩
    · exact ⟨e w, (hc.adj_iff hxL (nbr_known hxL hxw)).mpr hxw, (mem_pairsOf.mp hm).2⟩

/-- **Distances in a consistent graph.** Between the supports of `μ_i` and `μ_j`, a metric of a
consistent graph is the distance of Theorem 5.2 for the pairs of that graph. -/
theorem Consistent.dist_eq (hij : G.Adj i j) (hc : Consistent G i j G' e) {d' : V' → V' → ℝ}
    (hd : GraphMetric G' d') (h3 : ThreeApart G' d') {p q : V} (hp : p = i ∨ G.Adj i p)
    (hq : q = j ∨ G.Adj j q) : d' (e p) (e q) = chargedDist G i j (pairsOf G i j G' e) p q := by
  have hpK : p ∈ known G i j := closed_i_known hp
  have hqK : q ∈ known G i j := closed_j_known hq
  have hiK : i ∈ known G i j := listed_known i_listed
  have hjK : j ∈ known G i j := listed_known j_listed
  have he_ij : G'.Adj (e i) (e j) := (hc.adj_iff i_listed hjK).mpr hij
  unfold chargedDist
  by_cases hpq : p = q
  · subst hpq; rw [ite_eq_left rfl, hd.self]
  rw [ite_eq_right hpq]
  have hne := hc.ne hpK hqK hpq
  by_cases hX : p ∈ uniq G i j ∧ q ∈ uniq G j i
  · rw [ite_eq_left hX]
    obtain ⟨hx, hy⟩ := hX
    have hxL := uniq_listed hx
    unfold crossDist
    by_cases ha : G.Adj p q
    · rw [ite_eq_left ha]; exact hd.adj ((hc.adj_iff hxL hqK).mpr ha)
    rw [ite_eq_right ha]
    have hna : ¬ G'.Adj (e p) (e q) := fun h => ha ((hc.adj_iff hxL hqK).mp h)
    by_cases hF : (∃ w ∈ uniq G i j ∪ common G i j, G.Adj p w ∧ G.Adj w q) ∨
        (∃ w, G.Adj p w ∧ s(w, q) ∈ pairsOf G i j G' e)
    · rw [ite_eq_left hF]
      obtain ⟨w', h1, h2⟩ := (hc.common_nbr hx hy ha).mpr hF
      exact le_antisymm (hd.le_two h1 h2) (hd.two_le hne hna)
    · rw [ite_eq_right hF]
      refine le_antisymm ?_ (h3 _ _ hne hna fun w' hw' => hF ((hc.common_nbr hx hy ha).mp ⟨w', hw'⟩))
      have hpi : G'.Adj (e p) (e i) := (hc.adj_iff' i_listed hpK).mpr (mem_uniq.mp hx).2.1.symm
      have hjq : G'.Adj (e j) (e q) := (hc.adj_iff j_listed hqK).mpr (mem_uniq.mp hy).2.1
      exact hd.le_three hpi he_ij hjq
  rw [ite_eq_right hX]
  have hY : ¬ (q ∈ uniq G i j ∧ p ∈ uniq G j i) := by
    rintro ⟨-, hp'⟩
    obtain ⟨hpi, -, hip⟩ := mem_uniq.mp hp'
    rcases hp with h | h
    · exact hpi h
    · exact hip h
  rw [ite_eq_right hY]
  -- one of `p`, `q` is in `{i, j} ∪ C`, adjacent to the other endpoint of `(i, j)` or equal to it
  have hjp : p ∉ uniq G i j → (p = j ∨ G.Adj p j) ∧ p ∈ listed G i j := by
    intro hpU
    rcases hp with rfl | hip
    · exact ⟨Or.inr hij, i_listed⟩
    · by_cases hpj : p = j
      · exact ⟨Or.inl hpj, by rw [hpj]; exact j_listed⟩
      · have hjp' : G.Adj j p := by
          by_contra hjp'
          exact hpU (mem_uniq.mpr ⟨hpj, hip, hjp'⟩)
        exact ⟨Or.inr hjp'.symm, common_listed (mem_common.mpr ⟨hip, hjp'⟩)⟩
  have hiq : q ∉ uniq G j i → (q = i ∨ G.Adj q i) ∧ q ∈ listed G i j := by
    intro hqU
    rcases hq with rfl | hjq
    · exact ⟨Or.inr hij.symm, j_listed⟩
    · by_cases hqi : q = i
      · exact ⟨Or.inl hqi, by rw [hqi]; exact i_listed⟩
      · have hiq' : G.Adj i q := by
          by_contra hiq'
          exact hqU (mem_uniq.mpr ⟨hqi, hjq, hiq'⟩)
        exact ⟨Or.inr hiq'.symm, common_listed (mem_common.mpr ⟨hiq', hjq⟩)⟩
  have hcase : p ∉ uniq G i j ∨ q ∉ uniq G j i := by
    by_contra h
    have h' := not_or.mp h
    exact hX ⟨not_not.mp h'.1, not_not.mp h'.2⟩
  -- adjacency is known, and a non-adjacent pair is at distance 2
  have hadj : G'.Adj (e p) (e q) ↔ G.Adj p q := by
    rcases hcase with h | h
    · exact hc.adj_iff (hjp h).2 hqK
    · exact hc.adj_iff' (hiq h).2 hpK
  by_cases ha : G.Adj p q
  · rw [ite_eq_left ha]; exact hd.adj (hadj.mpr ha)
  rw [ite_eq_right ha]
  have hna : ¬ G'.Adj (e p) (e q) := fun h => ha (hadj.mp h)
  refine le_antisymm ?_ (hd.two_le hne hna)
  rcases hcase with h | h
  · obtain ⟨hpj, hpL⟩ := hjp h
    rcases hpj with rfl | hpj
    · rcases hq with rfl | hjq
      · exact absurd rfl hpq
      · exact absurd hjq ha
    · rcases hq with rfl | hjq
      · exact absurd hpj ha
      · exact hd.le_two ((hc.adj_iff' j_listed hpK).mpr hpj) ((hc.adj_iff j_listed hqK).mpr hjq)
  · obtain ⟨hqi, hqL⟩ := hiq h
    rcases hqi with rfl | hqi
    · rcases hp with rfl | hip
      · exact absurd rfl hpq
      · exact absurd hip.symm ha
    · rcases hp with rfl | hip
      · exact absurd hqi.symm ha
      · exact hd.le_two ((hc.adj_iff' i_listed hpK).mpr hip.symm)
          ((hc.adj_iff i_listed hqK).mpr hqi.symm)

/-- The pairs of a consistent graph are admissible: at a vertex, they and the listed edges are
distinct edges of the consistent graph, whose degree is known. -/
theorem Consistent.admissible (hc : Consistent G i j G' e) : Admissible G i j (pairsOf G i j G' e) := by
  refine ⟨pairsOf_subset, fun v => ?_⟩
  unfold pairDeg freeDeg listedDeg
  set P := univ.filter (fun q => s(v, q) ∈ pairsOf G i j G' e)
  set Lv := (listed G i j).filter (G.Adj v)
  rcases P.eq_empty_or_nonempty with hP | ⟨q₀, hq₀⟩
  · rw [hP, Finset.card_empty]; exact Nat.zero_le _
  have hv := cand_vertices (pairsOf_subset (Finset.mem_filter.mp hq₀).2)
  have hPK : ∀ q ∈ P, q ∈ known G i j ∧ q ∉ listed G i j ∧ G'.Adj (e v) (e q) := by
    intro q hq
    have hm := (Finset.mem_filter.mp hq).2
    have h' := cand_vertices (pairsOf_subset hm)
    exact ⟨h'.2.2.1, h'.2.2.2.1, (mem_pairsOf.mp hm).2⟩
  have hLK : ∀ q ∈ Lv, q ∈ known G i j ∧ q ∈ listed G i j ∧ G'.Adj (e v) (e q) := by
    intro q hq
    obtain ⟨hqL, hvq⟩ := Finset.mem_filter.mp hq
    exact ⟨listed_known hqL, hqL, (hc.adj_iff' hqL hv.1).mpr hvq⟩
  have hdisj : Disjoint P Lv := by
    rw [Finset.disjoint_left]
    intro q hqP hqL
    exact (hPK q hqP).2.1 (hLK q hqL).2.1
  have hsub : (P ∪ Lv).image e ⊆ G'.neighborFinset (e v) := by
    intro x' hx'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx'
    rw [SimpleGraph.mem_neighborFinset]
    rcases Finset.mem_union.mp hq with hq | hq
    · exact (hPK q hq).2.2
    · exact (hLK q hq).2.2
  have hinj : Set.InjOn e (P ∪ Lv : Finset V) := by
    refine Set.InjOn.mono (fun q hq => ?_) hc.inj
    rcases Finset.mem_union.mp (Finset.mem_coe.mp hq) with hq | hq
    · exact Finset.mem_coe.mpr (hPK q hq).1
    · exact Finset.mem_coe.mpr (hLK q hq).1
  have hcard : P.card + Lv.card ≤ G.degree v := by
    rw [← Finset.card_union_eq_card_add_card.mpr hdisj, ← Finset.card_image_of_injOn hinj, ← hc.degrees v hv.1,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    exact Finset.card_le_card hsub
  omega

end consistent

/-! ### `W₁` is unchanged when measures and costs are carried by a map injective on the supports -/

section transfer

variable {V' : Type u} [Fintype V'] [DecidableEq V']

/-- **Transfer.** If `α'`, `β'` are `α`, `β` carried by `e` (injective on a set `K` that holds the
supports), and the costs agree on the supports, the two `W₁` are equal. -/
theorem W1_transfer (e : V → V') (K : Finset V) (he : Set.InjOn e K) {α β : V → ℝ}
    {α' β' : V' → ℝ} (hα : ∀ x, 0 ≤ α x) (hβ : ∀ x, 0 ≤ β x) (hα1 : ∑ x, α x = 1)
    (hβ1 : ∑ x, β x = 1) (hαK : ∀ x, x ∉ K → α x = 0) (hβK : ∀ x, x ∉ K → β x = 0)
    (hα' : ∀ x ∈ K, α' (e x) = α x) (hβ' : ∀ x ∈ K, β' (e x) = β x)
    (hα'0 : ∀ x', (∀ x ∈ K, e x ≠ x') → α' x' = 0) (hβ'0 : ∀ x', (∀ x ∈ K, e x ≠ x') → β' x' = 0)
    {c : V → V → ℝ} {c' : V' → V' → ℝ} (hc : ∀ x y, 0 ≤ c x y) (hc' : ∀ x y, 0 ≤ c' x y)
    (hcc : ∀ x y, 0 < α x → 0 < β y → c' (e x) (e y) = c x y) :
    W1 c' α' β' = W1 c α β := by
  have : Nonempty V := by
    rcases isEmpty_or_nonempty V with hV | hV
    · exfalso
      rw [Finset.univ_eq_empty, Finset.sum_empty] at hα1
      exact zero_ne_one hα1
    · exact hV
  set Ki : Finset V' := K.image e
  set g : V' → V := Function.invFunOn e (K : Set V)
  have hg : ∀ x ∈ K, g (e x) = x := fun x hx => he.leftInvOn_invFunOn (Finset.mem_coe.mpr hx)
  have hKi : ∀ x ∈ K, e x ∈ Ki := fun x hx => Finset.mem_image_of_mem e hx
  have hgK : ∀ x' ∈ Ki, g x' ∈ K ∧ e (g x') = x' := by
    intro x' hx'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hx'
    rw [hg x hx]
    exact ⟨hx, rfl⟩
  have hout : ∀ x', x' ∉ Ki → ∀ x ∈ K, e x ≠ x' := fun x' hx' x hx h =>
    hx' (by rw [← h]; exact hKi x hx)
  -- sums of functions that vanish off the supports
  have hsum : ∀ f : V' → ℝ, (∀ x', x' ∉ Ki → f x' = 0) → ∑ x', f x' = ∑ x ∈ K, f (e x) := by
    intro f hf
    rw [← Finset.sum_image he]
    exact (Finset.sum_subset (Finset.subset_univ _) fun x' _ hx' => hf x' hx').symm
  have hsumV : ∀ f : V → ℝ, (∀ x, x ∉ K → f x = 0) → ∑ x, f x = ∑ x ∈ K, f x := fun f hf =>
    (Finset.sum_subset (Finset.subset_univ K) fun x _ hx => hf x hx).symm
  have hπrow : ∀ π, IsCoupling α β π → ∀ x y, x ∉ K → π x y = 0 := by
    intro π hπ x y hx
    have hle : π x y ≤ ∑ y₁, π x y₁ :=
      Finset.single_le_sum (f := fun y₁ => π x y₁) (fun y₁ _ => hπ.1 x y₁) (Finset.mem_univ y)
    rw [hπ.2.1 x, hαK x hx] at hle
    exact le_antisymm hle (hπ.1 x y)
  have hπcol : ∀ π, IsCoupling α β π → ∀ x y, y ∉ K → π x y = 0 := by
    intro π hπ x y hy
    have hle : π x y ≤ ∑ x₁, π x₁ y :=
      Finset.single_le_sum (f := fun x₁ => π x₁ y) (fun x₁ _ => hπ.1 x₁ y) (Finset.mem_univ x)
    rw [hπ.2.2 y, hβK y hy] at hle
    exact le_antisymm hle (hπ.1 x y)
  have hπ'row : ∀ π', IsCoupling α' β' π' → ∀ x' y', x' ∉ Ki → π' x' y' = 0 := by
    intro π' hπ' x' y' hx'
    have hle : π' x' y' ≤ ∑ y₁, π' x' y₁ :=
      Finset.single_le_sum (f := fun y₁ => π' x' y₁) (fun y₁ _ => hπ'.1 x' y₁) (Finset.mem_univ y')
    rw [hπ'.2.1 x', hα'0 x' (hout x' hx')] at hle
    exact le_antisymm hle (hπ'.1 x' y')
  have hπ'col : ∀ π', IsCoupling α' β' π' → ∀ x' y', y' ∉ Ki → π' x' y' = 0 := by
    intro π' hπ' x' y' hy'
    have hle : π' x' y' ≤ ∑ x₁, π' x₁ y' :=
      Finset.single_le_sum (f := fun x₁ => π' x₁ y') (fun x₁ _ => hπ'.1 x₁ y') (Finset.mem_univ x')
    rw [hπ'.2.2 y', hβ'0 y' (hout y' hy')] at hle
    exact le_antisymm hle (hπ'.1 x' y')
  have hpos_row : ∀ {W : Type u} [Fintype W] [DecidableEq W] {a b : W → ℝ} {π : W → W → ℝ},
      IsCoupling a b π →
      ∀ x y, 0 < π x y → 0 < a x ∧ 0 < b y := by
    intro W _ _ a b π hπ x y hpos
    refine ⟨lt_of_lt_of_le hpos ?_, lt_of_lt_of_le hpos ?_⟩
    · rw [← hπ.2.1 x]
      exact Finset.single_le_sum (f := fun y₁ => π x y₁) (fun y₁ _ => hπ.1 x y₁) (Finset.mem_univ y)
    · rw [← hπ.2.2 y]
      exact Finset.single_le_sum (f := fun x₁ => π x₁ y) (fun x₁ _ => hπ.1 x₁ y) (Finset.mem_univ x)
  -- carrying a coupling forward
  let push : (V → V → ℝ) → V' → V' → ℝ := fun π x' y' =>
    if x' ∈ Ki ∧ y' ∈ Ki then π (g x') (g y') else 0
  have hpush_e : ∀ π, ∀ x ∈ K, ∀ y ∈ K, push π (e x) (e y) = π x y := by
    intro π x hx y hy
    show (if e x ∈ Ki ∧ e y ∈ Ki then π (g (e x)) (g (e y)) else 0) = π x y
    rw [ite_eq_left ⟨hKi x hx, hKi y hy⟩, hg x hx, hg y hy]
  have hpush_out : ∀ π x' y', (x' ∉ Ki ∨ y' ∉ Ki) → push π x' y' = 0 := by
    intro π x' y' h
    show (if x' ∈ Ki ∧ y' ∈ Ki then π (g x') (g y') else 0) = 0
    exact ite_eq_right fun hc => h.elim (fun h1 => h1 hc.1) (fun h2 => h2 hc.2)
  have hpush : ∀ π, IsCoupling α β π → IsCoupling α' β' (push π) := by
    intro π hπ
    refine ⟨fun x' y' => ?_, fun x' => ?_, fun y' => ?_⟩
    · show 0 ≤ (if x' ∈ Ki ∧ y' ∈ Ki then π (g x') (g y') else 0)
      split_ifs
      · exact hπ.1 _ _
      · exact le_rfl
    · by_cases hx' : x' ∈ Ki
      · obtain ⟨hgx, hex⟩ := hgK x' hx'
        rw [hsum (push π x') fun y' hy' => hpush_out π x' y' (Or.inr hy')]
        rw [← hex, Finset.sum_congr rfl fun y hy => hpush_e π _ hgx y hy, hα' _ hgx, ← hπ.2.1 (g x')]
        exact (hsumV (fun y => π (g x') y) fun y hy => hπcol π hπ _ y hy).symm
      · rw [hα'0 x' (hout x' hx')]
        exact Finset.sum_eq_zero fun y' _ => hpush_out π x' y' (Or.inl hx')
    · by_cases hy' : y' ∈ Ki
      · obtain ⟨hgy, hey⟩ := hgK y' hy'
        rw [hsum (fun x' => push π x' y') fun x' hx' => hpush_out π x' y' (Or.inl hx')]
        rw [← hey, Finset.sum_congr rfl fun x hx => hpush_e π x hx _ hgy, hβ' _ hgy, ← hπ.2.2 (g y')]
        exact (hsumV (fun x => π x (g y')) fun x hx => hπrow π hπ x _ hx).symm
      · rw [hβ'0 y' (hout y' hy')]
        exact Finset.sum_eq_zero fun x' _ => hpush_out π x' y' (Or.inr hy')
  have hcost_push : ∀ π, IsCoupling α β π → cost c' (push π) = cost c π := by
    intro π hπ
    unfold cost
    rw [hsum (fun x' => ∑ y', c' x' y' * push π x' y') fun x' hx' =>
      Finset.sum_eq_zero fun y' _ => by rw [hpush_out π x' y' (Or.inl hx'), mul_zero]]
    rw [hsumV (fun x => ∑ y, c x y * π x y) fun x hx =>
      Finset.sum_eq_zero fun y _ => by rw [hπrow π hπ x y hx, mul_zero]]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hsum (fun y' => c' (e x) y' * push π (e x) y') fun y' hy' => by
      rw [hpush_out π (e x) y' (Or.inr hy'), mul_zero]]
    rw [hsumV (fun y => c x y * π x y) fun y hy => by rw [hπcol π hπ x y hy, mul_zero]]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [hpush_e π x hx y hy]
    rcases (hπ.1 x y).lt_or_eq with hpos | hzero
    · obtain ⟨hαx, hβy⟩ := hpos_row hπ x y hpos
      rw [hcc x y hαx hβy]
    · rw [← hzero, mul_zero, mul_zero]
  -- bringing a coupling back
  let pull : (V' → V' → ℝ) → V → V → ℝ := fun π' x y =>
    if x ∈ K ∧ y ∈ K then π' (e x) (e y) else 0
  have hpull_in : ∀ π', ∀ x ∈ K, ∀ y ∈ K, pull π' x y = π' (e x) (e y) := by
    intro π' x hx y hy
    show (if x ∈ K ∧ y ∈ K then π' (e x) (e y) else 0) = π' (e x) (e y)
    exact ite_eq_left ⟨hx, hy⟩
  have hpull_out : ∀ π' x y, (x ∉ K ∨ y ∉ K) → pull π' x y = 0 := by
    intro π' x y h
    show (if x ∈ K ∧ y ∈ K then π' (e x) (e y) else 0) = 0
    exact ite_eq_right fun hc => h.elim (fun h1 => h1 hc.1) (fun h2 => h2 hc.2)
  have hpull : ∀ π', IsCoupling α' β' π' → IsCoupling α β (pull π') := by
    intro π' hπ'
    refine ⟨fun x y => ?_, fun x => ?_, fun y => ?_⟩
    · by_cases h : x ∈ K ∧ y ∈ K
      · rw [hpull_in π' x h.1 y h.2]; exact hπ'.1 _ _
      · rw [hpull_out π' x y (not_and_or.mp h)]
    · by_cases hx : x ∈ K
      · rw [hsumV (pull π' x) fun y hy => hpull_out π' x y (Or.inr hy),
          Finset.sum_congr rfl fun y hy => hpull_in π' x hx y hy, ← hα' x hx, ← hπ'.2.1 (e x)]
        exact (hsum (π' (e x)) fun y' hy' => hπ'col π' hπ' (e x) y' hy').symm
      · rw [hαK x hx]
        exact Finset.sum_eq_zero fun y _ => hpull_out π' x y (Or.inl hx)
    · by_cases hy : y ∈ K
      · rw [hsumV (fun x => pull π' x y) fun x hx => hpull_out π' x y (Or.inl hx),
          Finset.sum_congr rfl fun x hx => hpull_in π' x hx y hy, ← hβ' y hy, ← hπ'.2.2 (e y)]
        exact (hsum (fun x' => π' x' (e y)) fun x' hx' => hπ'row π' hπ' x' (e y) hx').symm
      · rw [hβK y hy]
        exact Finset.sum_eq_zero fun x _ => hpull_out π' x y (Or.inr hy)
  have hcost_pull : ∀ π', IsCoupling α' β' π' → cost c (pull π') = cost c' π' := by
    intro π' hπ'
    unfold cost
    rw [hsumV (fun x => ∑ y, c x y * pull π' x y) fun x hx =>
      Finset.sum_eq_zero fun y _ => by rw [hpull_out π' x y (Or.inl hx), mul_zero]]
    rw [hsum (fun x' => ∑ y', c' x' y' * π' x' y') fun x' hx' =>
      Finset.sum_eq_zero fun y' _ => by rw [hπ'row π' hπ' x' y' hx', mul_zero]]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hsumV (fun y => c x y * pull π' x y) fun y hy => by rw [hpull_out π' x y (Or.inr hy), mul_zero]]
    rw [hsum (fun y' => c' (e x) y' * π' (e x) y') fun y' hy' => by
      rw [hπ'col π' hπ' (e x) y' hy', mul_zero]]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [hpull_in π' x hx y hy]
    rcases (hπ'.1 (e x) (e y)).lt_or_eq with hpos | hzero
    · obtain ⟨hαx', hβy'⟩ := hpos_row hπ' (e x) (e y) hpos
      rw [hα' x hx] at hαx'
      rw [hβ' y hy] at hβy'
      rw [hcc x y hαx' hβy']
    · rw [← hzero, mul_zero, mul_zero]
  -- the two infima
  obtain ⟨π₀, hπ₀⟩ := exists_coupling_prob hα hβ hα1 hβ1
  refine le_antisymm ?_ ?_
  · refine le_W1 ⟨π₀, hπ₀⟩ fun π hπ => ?_
    rw [← hcost_push π hπ]
    exact W1_le_cost hc' (hpush π hπ)
  · refine le_W1 ⟨push π₀, hpush π₀ hπ₀⟩ fun π' hπ' => ?_
    rw [← hcost_pull π' hπ']
    exact W1_le_cost hc (hpull π' hπ')

end transfer

/-! ### The bounds -/

/-- **Theorem 5.2, the bounds.** The curvature of a consistent graph, with a metric that is a graph
metric and separates vertices without short paths, and measures that agree with `μ`, is `kappaF` of
the pairs of that graph, which lies between `kappaF ∅` and `kappaMax`. -/
theorem range_bounds {μ : V → V → ℝ} (hij : G.Adj i j) (hi : OneStepAt G μ i) (hj : OneStepAt G μ j)
    {V' : Type u} [Fintype V'] [DecidableEq V'] {G' : SimpleGraph V'} [DecidableRel G'.Adj]
    {e : V → V'} {d' : V' → V' → ℝ} {μ' : V' → V' → ℝ} (hc : Consistent G i j G' e)
    (hd : GraphMetric G' d') (h3 : ThreeApart G' d') (hμ : Agrees G i j μ μ' e) :
    cORm d' μ' (e i) (e j) = kappaF G i j μ (pairsOf G i j G' e) ∧
      kappaF G i j μ ∅ ≤ cORm d' μ' (e i) (e j) ∧ cORm d' μ' (e i) (e j) ≤ kappaMax G i j μ := by
  have hsuppK : ∀ v, (v = i ∨ v = j) → OneStepAt G μ v → ∀ x, x ∉ known G i j → μ v x = 0 := by
    intro v hv hv' x hx
    have hvL : v ∈ listed G i j := by
      rcases hv with h | h
      · rw [h]; exact i_listed
      · rw [h]; exact j_listed
    exact hv'.supp x (fun h => hx (by rw [h]; exact listed_known hvL)) fun h => hx (nbr_known hvL h)
  have hclosed : ∀ v, OneStepAt G μ v → ∀ x, 0 < μ v x → x = v ∨ G.Adj v x := by
    intro v hv x hx
    by_contra h
    have h' := not_or.mp h
    exact absurd (hv.supp x h'.1 h'.2) (ne_of_gt hx)
  have hval : cORm d' μ' (e i) (e j) = kappaF G i j μ (pairsOf G i j G' e) := by
    unfold cORm kappaF
    congr 1
    exact W1_transfer e (known G i j) hc.inj hi.nonneg hj.nonneg hi.mass hj.mass
      (hsuppK i (Or.inl rfl) hi) (hsuppK j (Or.inr rfl) hj) (hμ i (Or.inl rfl)).1 (hμ j (Or.inr rfl)).1
      (hμ i (Or.inl rfl)).2 (hμ j (Or.inr rfl)).2 (chargedDist_nonneg _) hd.nonneg
      fun x y hx hy => hc.dist_eq hij hd h3 (hclosed i hi x hx) (hclosed j hj y hy)
  refine ⟨hval, ?_, ?_⟩
  · rw [hval]
    exact kappaF_mono hi hj (Finset.empty_subset _)
  · rw [hval]
    exact Finset.le_sup' (kappaF G i j μ) (mem_admissibleSets.mpr hc.admissible)

/-! ### The graphs that attain the bounds -/

variable (G i j)

/-- Pendant vertices needed at a known vertex to complete its degree. -/
def pad (F : Finset (Sym2 V)) (v : {v // v ∈ known G i j}) : ℕ :=
  if v.1 ∈ listed G i j then 0 else freeDeg G i j v.1 - pairDeg F v.1

/-- The vertices of `realize F`: the known vertices and the pendant vertices. -/
abbrev RealV (F : Finset (Sym2 V)) : Type u :=
  {v // v ∈ known G i j} ⊕ (Σ v : {v // v ∈ known G i j}, Fin (pad G i j F v))

/-- Adjacency of `realize F` before symmetrization: listed edges, pairs of `F`, pendant edges. -/
def realRel (F : Finset (Sym2 V)) : RealV G i j F → RealV G i j F → Prop
  | Sum.inl a, Sum.inl b => (G.Adj a.1 b.1 ∧ (a.1 ∈ listed G i j ∨ b.1 ∈ listed G i j)) ∨ s(a.1, b.1) ∈ F
  | Sum.inl a, Sum.inr b => a = b.1
  | Sum.inr _, _ => False

/-- The graph that realizes the pairs `F`. -/
def realize (F : Finset (Sym2 V)) : SimpleGraph (RealV G i j F) := SimpleGraph.fromRel (realRel G i j F)

noncomputable instance (F : Finset (Sym2 V)) : DecidableRel (realize G i j F).Adj := Classical.decRel _

/-- The known vertices inside `realize F` (the others go to `i`, which does not matter). -/
def embed (F : Finset (Sym2 V)) (v : V) : RealV G i j F :=
  if h : v ∈ known G i j then Sum.inl ⟨v, h⟩ else Sum.inl ⟨i, listed_known i_listed⟩

variable {G i j}

lemma embed_of_known {F : Finset (Sym2 V)} {v : V} (hv : v ∈ known G i j) :
    embed G i j F v = Sum.inl ⟨v, hv⟩ := by
  simp [embed, hv]

lemma not_listed_of_mem_pair {F : Finset (Sym2 V)} (hF : F ⊆ cand G i j) {a b : V} (h : s(a, b) ∈ F) :
    a ∉ listed G i j ∧ b ∉ listed G i j := by
  have := cand_vertices (hF h)
  exact ⟨this.2.1, this.2.2.2.1⟩

lemma realize_adj_inl {F : Finset (Sym2 V)} {a b : {v // v ∈ known G i j}} :
    (realize G i j F).Adj (Sum.inl a) (Sum.inl b) ↔
      a.1 ≠ b.1 ∧ ((G.Adj a.1 b.1 ∧ (a.1 ∈ listed G i j ∨ b.1 ∈ listed G i j)) ∨ s(a.1, b.1) ∈ F) := by
  simp only [realize, SimpleGraph.fromRel_adj, ne_eq, Sum.inl.injEq, realRel]
  constructor
  · rintro ⟨hab, h | h⟩
    · exact ⟨fun h' => hab (Subtype.ext h'), h⟩
    · refine ⟨fun h' => hab (Subtype.ext h'), ?_⟩
      rcases h with ⟨hba, hl⟩ | hm
      · exact Or.inl ⟨hba.symm, hl.symm⟩
      · exact Or.inr (by rwa [Sym2.eq_swap])
  · rintro ⟨hab, h⟩
    exact ⟨fun h' => hab (congrArg Subtype.val h'), Or.inl h⟩

lemma realize_adj_inl_inr {F : Finset (Sym2 V)} {a : {v // v ∈ known G i j}}
    {b : Σ v : {v // v ∈ known G i j}, Fin (pad G i j F v)} :
    (realize G i j F).Adj (Sum.inl a) (Sum.inr b) ↔ a = b.1 := by
  simp [realize, SimpleGraph.fromRel_adj, realRel]

lemma realize_not_adj_inr_inr {F : Finset (Sym2 V)} {a b : Σ v : {v // v ∈ known G i j}, Fin (pad G i j F v)} :
    ¬ (realize G i j F).Adj (Sum.inr a) (Sum.inr b) := by
  simp [realize, SimpleGraph.fromRel_adj, realRel]

/-- `realize F` is consistent with the building blocks. -/
theorem realize_consistent {F : Finset (Sym2 V)} (hF : Admissible G i j F) :
    Consistent G i j (realize G i j F) (embed G i j F) where
  inj := by
    intro v hv w hw h
    rw [embed_of_known hv, embed_of_known hw] at h
    exact congrArg Subtype.val (Sum.inl.inj h)
  lists := by
    intro v hv w'
    rw [embed_of_known (listed_known hv)]
    rcases w' with b | b
    · rw [realize_adj_inl]
      constructor
      · rintro ⟨hne, (⟨hvb, -⟩ | hm)⟩
        · exact ⟨b.1, hvb, embed_of_known b.2⟩
        · exact absurd hv (not_listed_of_mem_pair hF.1 hm).1
      · rintro ⟨w, hvw, hw⟩
        rw [embed_of_known (nbr_known hv hvw)] at hw
        have hb : b.1 = w := by rw [← Sum.inl.inj hw]
        subst hb
        exact ⟨G.ne_of_adj hvw, Or.inl ⟨hvw, Or.inl hv⟩⟩
    · rw [realize_adj_inl_inr]
      constructor
      · intro hvb
        exfalso
        have hbl : b.1.1 ∈ listed G i j := by rw [← hvb]; exact hv
        have h0 : pad G i j F b.1 = 0 := by
          simp only [pad]
          rw [ite_eq_left hbl]
        have hlt := b.2.isLt
        omega
      · rintro ⟨w, hvw, hw⟩
        rw [embed_of_known (nbr_known hv hvw)] at hw
        exact (Sum.inl_ne_inr hw).elim
  degrees := by
    intro w hw
    rw [embed_of_known hw, ← SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.neighborFinset_eq_filter (G := realize G i j F), Finset.card_filter,
      Fintype.sum_sum_type]
    -- the pendant vertices at `w`
    have hpend : ∑ b : Σ v : {v // v ∈ known G i j}, Fin (pad G i j F v),
        (if (realize G i j F).Adj (Sum.inl ⟨w, hw⟩) (Sum.inr b) then 1 else 0) = pad G i j F ⟨w, hw⟩ := by
      simp_rw [realize_adj_inl_inr]
      rw [Fintype.sum_sigma]
      have hk : ∀ a : {v // v ∈ known G i j}, (∑ k : Fin (pad G i j F a),
          (if (⟨w, hw⟩ : {v // v ∈ known G i j}) =
            (⟨a, k⟩ : Σ v : {v // v ∈ known G i j}, Fin (pad G i j F v)).1 then 1 else 0)) =
          if (⟨w, hw⟩ : {v // v ∈ known G i j}) = a then pad G i j F a else 0 := by
        intro a
        by_cases h : (⟨w, hw⟩ : {v // v ∈ known G i j}) = a
        · simp [h]
        · simp [h]
      rw [Finset.sum_congr rfl fun a _ => hk a, Finset.sum_ite_eq]
      simp
    -- the known neighbours of `w`
    have hcond : ∀ a : {v // v ∈ known G i j},
        (realize G i j F).Adj (Sum.inl ⟨w, hw⟩) (Sum.inl a) ↔
          (w ≠ a.1 ∧ ((G.Adj w a.1 ∧ (w ∈ listed G i j ∨ a.1 ∈ listed G i j)) ∨ s(w, a.1) ∈ F)) :=
      fun a => realize_adj_inl
    have hknown : ∑ a : {v // v ∈ known G i j},
        (if (realize G i j F).Adj (Sum.inl ⟨w, hw⟩) (Sum.inl a) then 1 else 0) =
        ((known G i j).filter (fun v => w ≠ v ∧ ((G.Adj w v ∧ (w ∈ listed G i j ∨ v ∈ listed G i j)) ∨
          s(w, v) ∈ F))).card := by
      simp_rw [hcond]
      rw [Finset.card_filter]
      exact (Finset.sum_subtype (known G i j) (fun _ => Iff.rfl)
        (fun v => if w ≠ v ∧ ((G.Adj w v ∧ (w ∈ listed G i j ∨ v ∈ listed G i j)) ∨ s(w, v) ∈ F)
          then 1 else 0)).symm
    rw [hpend, hknown]
    by_cases hwl : w ∈ listed G i j
    · -- a listed vertex: its neighbours, and no pendant vertex
      have hpad : pad G i j F ⟨w, hw⟩ = 0 := by simp only [pad]; rw [ite_eq_left hwl]
      have hset : (known G i j).filter (fun v => w ≠ v ∧ ((G.Adj w v ∧ (w ∈ listed G i j ∨
          v ∈ listed G i j)) ∨ s(w, v) ∈ F)) = G.neighborFinset w := by
        ext v
        simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
        constructor
        · rintro ⟨-, -, ⟨hwv, -⟩ | hm⟩
          · exact hwv
          · exact absurd hwl (not_listed_of_mem_pair hF.1 hm).1
        · intro hwv
          exact ⟨nbr_known hwl hwv, G.ne_of_adj hwv, Or.inl ⟨hwv, Or.inl hwl⟩⟩
      rw [hset, hpad, SimpleGraph.card_neighborFinset_eq_degree, add_zero]
    · -- an unlisted known vertex: listed edges, pairs of `F`, pendant vertices
      have hset : (known G i j).filter (fun v => w ≠ v ∧ ((G.Adj w v ∧ (w ∈ listed G i j ∨
          v ∈ listed G i j)) ∨ s(w, v) ∈ F)) =
          (listed G i j).filter (G.Adj w) ∪ univ.filter (fun q => s(w, q) ∈ F) := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨-, -, ⟨hwv, hl⟩ | hm⟩
          · exact Or.inl ⟨hl.resolve_left hwl, hwv⟩
          · exact Or.inr hm
        · rintro (⟨hvl, hwv⟩ | hm)
          · exact ⟨listed_known hvl, G.ne_of_adj hwv, Or.inl ⟨hwv, Or.inr hvl⟩⟩
          · have := cand_vertices (hF.1 hm)
            exact ⟨this.2.2.1, this.2.2.2.2, Or.inr hm⟩
      have hdisj : Disjoint ((listed G i j).filter (G.Adj w)) (univ.filter (fun q => s(w, q) ∈ F)) := by
        rw [Finset.disjoint_left]
        intro v hv hv'
        exact (not_listed_of_mem_pair hF.1 (Finset.mem_filter.mp hv').2).2 (Finset.mem_filter.mp hv).1
      rw [hset, Finset.card_union_eq_card_add_card.mpr hdisj]
      have hpad : pad G i j F ⟨w, hw⟩ = freeDeg G i j w - pairDeg F w := by
        simp only [pad]; rw [ite_eq_right hwl]
      have hadm := hF.2 w
      have hlist : listedDeg G i j w ≤ G.degree w := by
        unfold listedDeg
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        refine Finset.card_le_card fun v hv => ?_
        rw [SimpleGraph.mem_neighborFinset]
        exact (Finset.mem_filter.mp hv).2
      rw [hpad]
      simp only [freeDeg, pairDeg, listedDeg] at hadm hlist ⊢
      omega

/-- `realize F` is connected: every known vertex is listed or in a list, every pendant vertex hangs
from a known vertex. -/
theorem realize_connected (hij : G.Adj i j) {F : Finset (Sym2 V)} (hF : Admissible G i j F) :
    (realize G i j F).Connected := by
  have hc := realize_consistent hF
  set r := embed G i j F i
  have hiK : i ∈ known G i j := listed_known i_listed
  -- every listed vertex reaches `e i`
  have hL : ∀ v ∈ listed G i j, (realize G i j F).Reachable (embed G i j F v) r := by
    intro v hv
    rcases mem_listed.mp hv with rfl | rfl | hvU | hvC
    · exact SimpleGraph.Reachable.refl _
    · exact ((hc.adj_iff i_listed (listed_known j_listed)).mpr hij).reachable.symm
    · exact ((hc.adj_iff i_listed (listed_known hv)).mpr (mem_uniq.mp hvU).2.1).reachable.symm
    · exact ((hc.adj_iff i_listed (listed_known hv)).mpr (mem_common.mp hvC).1).reachable.symm
  -- every known vertex reaches `e i`
  have hK : ∀ (v : V) (hv : v ∈ known G i j), (realize G i j F).Reachable (Sum.inl ⟨v, hv⟩) r := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvl | hvn
    · rw [← embed_of_known hv]; exact hL v hvl
    · simp only [Finset.mem_biUnion, SimpleGraph.mem_neighborFinset] at hvn
      obtain ⟨w, hwl, hwv⟩ := hvn
      have hadj := (hc.adj_iff hwl hv).mpr hwv
      rw [embed_of_known hv] at hadj
      exact hadj.reachable.symm.trans (hL w hwl)
  have hall : ∀ x, (realize G i j F).Reachable x r := by
    rintro (⟨v, hv⟩ | ⟨⟨v, hv⟩, k⟩)
    · exact hK v hv
    · have hadj : (realize G i j F).Adj (Sum.inl ⟨v, hv⟩) (Sum.inr ⟨⟨v, hv⟩, k⟩) :=
        realize_adj_inl_inr.mpr rfl
      exact hadj.reachable.symm.trans (hK v hv)
  have : Nonempty (RealV G i j F) := ⟨r⟩
  exact ⟨fun x y => (hall x).trans (hall y).symm⟩

/-- The pairs of `realize F` are `F`. -/
theorem pairsOf_realize {F : Finset (Sym2 V)} (hF : Admissible G i j F) :
    pairsOf G i j (realize G i j F) (embed G i j F) = F := by
  ext z
  refine Sym2.ind (fun a b => ?_) z
  rw [mem_pairsOf]
  constructor
  · rintro ⟨hz, hadj⟩
    have hv := cand_vertices hz
    rw [embed_of_known hv.1, embed_of_known hv.2.2.1, realize_adj_inl] at hadj
    rcases hadj.2 with ⟨-, hl⟩ | hm
    · exact absurd hl (by simp [hv.2.1, hv.2.2.2.1])
    · exact hm
  · intro hm
    have hv := cand_vertices (hF.1 hm)
    refine ⟨hF.1 hm, ?_⟩
    rw [embed_of_known hv.1, embed_of_known hv.2.2.1, realize_adj_inl]
    exact ⟨hv.2.2.2.2, Or.inr hm⟩

/-- The curvature of `realize F` is `kappaF F`. -/
theorem realize_kappa {μ : V → V → ℝ} (hij : G.Adj i j) (hi : OneStepAt G μ i) (hj : OneStepAt G μ j)
    {F : Finset (Sym2 V)} (hF : Admissible G i j F) {μ' : RealV G i j F → RealV G i j F → ℝ}
    (hμ : Agrees G i j μ μ' (embed G i j F)) :
    cORm (fun x y => ((realize G i j F).dist x y : ℝ)) μ' (embed G i j F i) (embed G i j F j) =
      kappaF G i j μ F := by
  have hconn := realize_connected hij hF
  have h := (range_bounds hij hi hj (realize_consistent hF) (graphMetric_dist hconn)
    (threeApart_dist hconn) hμ).1
  rwa [pairsOf_realize hF] at h

/-! ### Theorem 5.2 -/

/-- **Theorem 5.2 (exact range).** Over the connected graphs consistent with the building blocks of
`(i, j)`, with their shortest-path distance and measures that agree with `μ` (locality), the curvature
ranges over `[kappaF ∅, kappaMax]`: every such graph lies in it, the graph of listed edges with pendant
vertices attains the lower end, and some admissible `F` attains the upper end. -/
theorem exact_range_paper {μ : V → V → ℝ} (hij : G.Adj i j) (hi : OneStepAt G μ i)
    (hj : OneStepAt G μ j) :
    (∀ {V' : Type u} [Fintype V'] [DecidableEq V'] (G' : SimpleGraph V') [DecidableRel G'.Adj]
        (e : V → V') (μ' : V' → V' → ℝ), G'.Connected → Consistent G i j G' e →
        Agrees G i j μ μ' e →
        kappaF G i j μ ∅ ≤ cORm (fun x y => (G'.dist x y : ℝ)) μ' (e i) (e j) ∧
          cORm (fun x y => (G'.dist x y : ℝ)) μ' (e i) (e j) ≤ kappaMax G i j μ) ∧
    ((realize G i j ∅).Connected ∧ Consistent G i j (realize G i j ∅) (embed G i j ∅) ∧
      ∀ μ' : RealV G i j ∅ → RealV G i j ∅ → ℝ, Agrees G i j μ μ' (embed G i j ∅) →
        cORm (fun x y => ((realize G i j ∅).dist x y : ℝ)) μ' (embed G i j ∅ i) (embed G i j ∅ j) =
          kappaF G i j μ ∅) ∧
    ∃ F, Admissible G i j F ∧ kappaF G i j μ F = kappaMax G i j μ ∧
      (realize G i j F).Connected ∧ Consistent G i j (realize G i j F) (embed G i j F) ∧
      ∀ μ' : RealV G i j F → RealV G i j F → ℝ, Agrees G i j μ μ' (embed G i j F) →
        cORm (fun x y => ((realize G i j F).dist x y : ℝ)) μ' (embed G i j F i) (embed G i j F j) =
          kappaMax G i j μ := by
  have h0 : Admissible G i j ∅ := mem_admissibleSets.mp (empty_mem_admissibleSets G i j)
  refine ⟨?_, ⟨realize_connected hij h0, realize_consistent h0,
    fun μ' hμ => realize_kappa hij hi hj h0 hμ⟩, ?_⟩
  · intro V' _ _ G' _ e μ' hconn hc hμ
    exact (range_bounds hij hi hj hc (graphMetric_dist hconn) (threeApart_dist hconn) hμ).2
  obtain ⟨F, hFmem, hFmax⟩ := Finset.exists_mem_eq_sup' ⟨∅, empty_mem_admissibleSets G i j⟩
    (kappaF G i j μ)
  have hF := mem_admissibleSets.mp hFmem
  refine ⟨F, hF, by rw [kappaMax, hFmax], realize_connected hij hF, realize_consistent hF,
    fun μ' hμ => ?_⟩
  rw [realize_kappa hij hi hj hF hμ, kappaMax, hFmax]

end OllivierBF
