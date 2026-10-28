/-
  König's theorem for the cross-edge graph, the bound `𝔠₄ ≤ 2σ` (Lemma 3.6 of the paper),
  and the vertex-cover potentials behind the lazy transport envelope (Proposition 4.10).

  Nothing in this file takes a published result as a hypothesis. König's theorem is derived
  from Hall's marriage theorem in Mathlib by adding dummy vertices, and the envelope is a
  weak-duality bound: a 1-Lipschitz potential bounds every coupling from below.

  Convention: where it matters, the endpoints are labelled so that `ρ_i ≤ ρ_j`.
-/
module

public import OllivierBF.Interval

@[expose] public section

open Finset

set_option linter.unusedSectionVars false

namespace OllivierBF

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ} {i j : V}

/-! ### Vertex covers of the cross-edge graph -/

/-- `K` meets every cross edge of `(i, j)`, that is, `K` is a vertex cover of `B_{ij}`. -/
def CoversCross (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (K : Finset V) : Prop :=
  ∀ x ∈ uniq G i j, ∀ y ∈ uniq G j i, G.Adj x y → x ∈ K ∨ y ∈ K

/-- The neighbours in `U_j` of a set `S` of vertices. -/
def crossNbr (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (S : Finset V) : Finset V :=
  (uniq G j i).filter fun y => ∃ x ∈ S, G.Adj x y

/-- The deficiency `|S| − |N(S)|` of a set `S` in `B_{ij}`. -/
def deficiency (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (S : Finset V) : ℤ :=
  (S.card : ℤ) - ((crossNbr G i j S).card : ℤ)

/-- The Hall family: the neighbours in `U_j` of `x ∈ U_i` (tagged `inl`) and `δ` dummies
(tagged `inr`). -/
def hallFam (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (δ : ℕ)
    (x : {x // x ∈ uniq G i j}) : Finset (V ⊕ Fin δ) :=
  ((uniq G j i).filter (G.Adj x.1)).map Function.Embedding.inl ∪
    (Finset.univ : Finset (Fin δ)).map Function.Embedding.inr

/-- The pair `(x, y)` formed by a vertex `x ∈ U_i` and its Hall partner `y`. -/
def hallPair {δ : ℕ} (f : {x // x ∈ uniq G i j} → V ⊕ Fin δ) (x : {x // x ∈ uniq G i j}) :
    V × V :=
  (x.1, Sum.elim id (fun _ => x.1) (f x))

lemma uniq_not_mem_swap {x : V} (hx : x ∈ uniq G i j) : x ∉ uniq G j i :=
  fun h => (mem_uniq.1 hx).2.2 (mem_uniq.1 h).2.1

lemma mem_crossNbr {S : Finset V} {y : V} :
    y ∈ crossNbr G i j S ↔ y ∈ uniq G j i ∧ ∃ x ∈ S, G.Adj x y := by
  rw [crossNbr, Finset.mem_filter]

lemma crossNbr_empty : crossNbr G i j ∅ = ∅ := by
  simp [crossNbr]

lemma hallFam_inl {δ : ℕ} {x : {x // x ∈ uniq G i j}} {y : V}
    (h : Sum.inl y ∈ hallFam G i j δ x) : y ∈ uniq G j i ∧ G.Adj x.1 y := by
  unfold hallFam at h
  rcases Finset.mem_union.1 h with h | h
  · obtain ⟨y', hy', hyy'⟩ := Finset.mem_map.1 h
    simp only [Function.Embedding.inl_apply, Sum.inl.injEq] at hyy'
    subst hyy'
    exact Finset.mem_filter.1 hy'
  · obtain ⟨c, -, hc⟩ := Finset.mem_map.1 h
    simp at hc

/-- Hall's condition for the family with `δ = |S| − |N(S)|` dummies, where `S` has the largest
deficiency. -/
lemma hall_cond {S : Finset V}
    (hmax : ∀ T ∈ (uniq G i j).powerset, deficiency G i j T ≤ deficiency G i j S)
    (hNS : (crossNbr G i j S).card ≤ S.card) (s : Finset {x // x ∈ uniq G i j}) :
    s.card ≤ (s.biUnion (hallFam G i j (S.card - (crossNbr G i j S).card))).card := by
  rcases s.eq_empty_or_nonempty with hs | ⟨x₀, hx₀⟩
  · rw [hs]; simp
  obtain ⟨T, hT⟩ : ∃ T : Finset V, T = s.map (Function.Embedding.subtype _) := ⟨_, rfl⟩
  have hTX : T ⊆ uniq G i j := by
    intro x hx
    rw [hT] at hx
    obtain ⟨x', -, rfl⟩ := Finset.mem_map.1 hx
    exact x'.2
  have hTcard : T.card = s.card := by rw [hT]; exact Finset.card_map _
  have hdef := hmax T (Finset.mem_powerset.2 hTX)
  unfold deficiency at hdef
  have hsub : (crossNbr G i j T).map Function.Embedding.inl ∪
      (Finset.univ : Finset (Fin (S.card - (crossNbr G i j S).card))).map Function.Embedding.inr ⊆
      s.biUnion (hallFam G i j (S.card - (crossNbr G i j S).card)) := by
    intro z hz
    rw [Finset.mem_biUnion]
    rcases Finset.mem_union.1 hz with hz | hz
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hz
      obtain ⟨hyU, x, hxT, hxy⟩ := mem_crossNbr.1 hy
      rw [hT] at hxT
      obtain ⟨x', hx's, rfl⟩ := Finset.mem_map.1 hxT
      exact ⟨x', hx's, Finset.mem_union_left _
        (Finset.mem_map_of_mem _ (Finset.mem_filter.2 ⟨hyU, hxy⟩))⟩
    · exact ⟨x₀, hx₀, Finset.mem_union_right _ hz⟩
  have hdisj : Disjoint ((crossNbr G i j T).map Function.Embedding.inl)
      ((Finset.univ : Finset (Fin (S.card - (crossNbr G i j S).card))).map
        Function.Embedding.inr) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hz1
    obtain ⟨c, -, hc⟩ := Finset.mem_map.1 hz2
    simp at hc
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map, Finset.card_univ,
    Fintype.card_fin] at hcard
  omega

/-- An injective choice of Hall partners gives a cross matching of size `|U_i| − δ`. -/
lemma card_le_matchNum_add {δ : ℕ} (f : {x // x ∈ uniq G i j} → V ⊕ Fin δ)
    (hf : Function.Injective f)
    (hft : ∀ x y, f x = Sum.inl y → y ∈ uniq G j i ∧ G.Adj x.1 y) :
    (uniq G i j).card ≤ matchNum G i j + δ := by
  classical
  obtain ⟨A, hA⟩ : ∃ A : Finset {x // x ∈ uniq G i j},
      A = (uniq G i j).attach.filter (fun x => ∃ y, f x = Sum.inl y) := ⟨_, rfl⟩
  have hmemA : ∀ x, x ∈ A ↔ ∃ y, f x = Sum.inl y := by
    intro x
    rw [hA, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_attach _ _, h⟩⟩
  have hpair : ∀ x ∈ A, ∃ y, f x = Sum.inl y ∧ hallPair f x = (x.1, y) := by
    intro x hx
    obtain ⟨y, hy⟩ := (hmemA x).1 hx
    exact ⟨y, hy, by simp [hallPair, hy]⟩
  have hinj : Set.InjOn (hallPair f) (A : Set {x // x ∈ uniq G i j}) := by
    intro x _ x' _ h
    exact Subtype.ext (congrArg Prod.fst h)
  have hM : IsCrossMatching G i j (A.image (hallPair f)) := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 he
      obtain ⟨y, hy, hxy⟩ := hpair x hx
      rw [hxy]
      exact ⟨x.2, (hft x y hy).1, (hft x y hy).2⟩
    · intro e he e' he' h1
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 he
      obtain ⟨x', -, rfl⟩ := Finset.mem_image.1 he'
      have : x = x' := Subtype.ext h1
      exact congrArg _ this
    · intro e he e' he' h2
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 he
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 he'
      obtain ⟨y, hy, hxy⟩ := hpair x hx
      obtain ⟨y', hy', hxy'⟩ := hpair x' hx'
      have h2' : y = y' := by simpa [hxy, hxy'] using h2
      have : x = x' := hf (by rw [hy, hy', h2'])
      exact congrArg _ this
  have hMcard : (A.image (hallPair f)).card ≤ matchNum G i j := by
    unfold matchNum
    exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hM⟩)
  rw [Finset.card_image_of_injOn hinj] at hMcard
  -- the vertices of `U_i` sent to dummies are at most `δ`
  have hB : ((uniq G i j).attach.filter (fun x => ∃ c, f x = Sum.inr c)).card ≤ δ := by
    have hsub : ((uniq G i j).attach.filter (fun x => ∃ c, f x = Sum.inr c)).image f ⊆
        (Finset.univ : Finset (Fin δ)).map Function.Embedding.inr := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨c, hc⟩ := (Finset.mem_filter.1 hx).2
      rw [hc]
      exact Finset.mem_map.2 ⟨c, Finset.mem_univ _, rfl⟩
    have := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ hf, Finset.card_map, Finset.card_univ,
      Fintype.card_fin] at this
  have hcover : (uniq G i j).attach ⊆
      A ∪ (uniq G i j).attach.filter (fun x => ∃ c, f x = Sum.inr c) := by
    intro x _
    rcases hfx : f x with y | c
    · exact Finset.mem_union_left _ ((hmemA x).2 ⟨y, hfx⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_attach _ _, c, hfx⟩)
  have h1 := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  rw [Finset.card_attach] at h1
  omega

/-- **König's theorem** for the cross-edge graph: some vertex cover of `B_{ij}` has at most
`𝔪(i, j)` vertices. Derived from Hall's theorem by adding `δ` dummy vertices, where `δ` is the
largest deficiency `|S| − |N(S)|` of a set `S ⊆ U_i`. -/
theorem exists_cover_le_matchNum (i j : V) :
    ∃ K : Finset V, CoversCross G i j K ∧
      ((uniq G i j).filter (· ∈ K)).card + ((uniq G j i).filter (· ∈ K)).card
        ≤ matchNum G i j := by
  classical
  obtain ⟨S, hSmem, hSmax⟩ := Finset.exists_max_image (uniq G i j).powerset (deficiency G i j)
    ⟨∅, Finset.empty_mem_powerset _⟩
  have hSX : S ⊆ uniq G i j := Finset.mem_powerset.1 hSmem
  have hNS : (crossNbr G i j S).card ≤ S.card := by
    have h0 := hSmax ∅ (Finset.empty_mem_powerset _)
    unfold deficiency at h0
    rw [crossNbr_empty] at h0
    simp only [Finset.card_empty, Nat.cast_zero, sub_zero] at h0
    omega
  obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (hallFam G i j (S.card - (crossNbr G i j S).card))).1 (hall_cond hSmax hNS)
  have hft' : ∀ x y, f x = Sum.inl y → y ∈ uniq G j i ∧ G.Adj x.1 y := by
    intro x y hxy
    have h := hft x
    rw [hxy] at h
    exact hallFam_inl h
  have hX := card_le_matchNum_add f hf hft'
  refine ⟨(uniq G i j \ S) ∪ crossNbr G i j S, ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hxS : x ∈ S
    · exact Or.inr (Finset.mem_union_right _ (mem_crossNbr.2 ⟨hy, x, hxS, hxy⟩))
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hx, hxS⟩))
  · have h1 : ((uniq G i j).filter (· ∈ (uniq G i j \ S) ∪ crossNbr G i j S)).card
        ≤ (uniq G i j \ S).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxU, hxK⟩ := Finset.mem_filter.1 hx
      rcases Finset.mem_union.1 hxK with h | h
      · exact h
      · exact absurd (mem_crossNbr.1 h).1 (uniq_not_mem_swap hxU)
    have h2 : ((uniq G j i).filter (· ∈ (uniq G i j \ S) ∪ crossNbr G i j S)).card
        ≤ (crossNbr G i j S).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨hyU, hyK⟩ := Finset.mem_filter.1 hy
      rcases Finset.mem_union.1 hyK with h | h
      · exact absurd hyU (uniq_not_mem_swap (Finset.mem_sdiff.1 h).1)
      · exact h
    have h3 := Finset.card_sdiff_add_card_eq_card hSX
    omega

/-! ### Lemma 3.6: `𝔠₄ ≤ 2σ` -/

/-- The cross edges of `(i, j)`, as pairs `(x, y)` with `x ∈ U_i` and `y ∈ U_j`. -/
def crossPairs (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) : Finset (V × V) :=
  (uniq G i j ×ˢ uniq G j i).filter fun p => G.Adj p.1 p.2

lemma mem_crossPairs {p : V × V} :
    p ∈ crossPairs G i j ↔ (p.1 ∈ uniq G i j ∧ p.2 ∈ uniq G j i) ∧ G.Adj p.1 p.2 := by
  rw [crossPairs, Finset.mem_filter, Finset.mem_product]

lemma mem_xi {u v k : V} : k ∈ xi G u v ↔ k ∈ uniq G u v ∧ ∃ w ∈ uniq G v u, G.Adj k w := by
  rw [xi, Finset.mem_filter]

lemma card_xi_le_crossPairs : (xi G i j).card ≤ (crossPairs G i j).card := by
  calc (xi G i j).card ≤ ((crossPairs G i j).image Prod.fst).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨hxU, y, hyU, hxy⟩ := mem_xi.1 hx
        exact Finset.mem_image.2
          ⟨(x, y), mem_crossPairs.2 ⟨⟨hxU, hyU⟩, hxy⟩, rfl⟩
    _ ≤ (crossPairs G i j).card := Finset.card_image_le

lemma card_xi_swap_le_crossPairs : (xi G j i).card ≤ (crossPairs G i j).card := by
  calc (xi G j i).card ≤ ((crossPairs G i j).image Prod.snd).card := by
        apply Finset.card_le_card
        intro y hy
        obtain ⟨hyU, x, hxU, hyx⟩ := mem_xi.1 hy
        exact Finset.mem_image.2
          ⟨(x, y), mem_crossPairs.2 ⟨⟨hxU, hyU⟩, hyx.symm⟩, rfl⟩
    _ ≤ (crossPairs G i j).card := Finset.card_image_le

/-- Every vertex covers at most `ϖ_max` cross edges. -/
lemma crossPairs_card_le_cover {K : Finset V} (hK : CoversCross G i j K) :
    (crossPairs G i j).card
      ≤ (((uniq G i j).filter (· ∈ K)).card + ((uniq G j i).filter (· ∈ K)).card)
          * varpi G i j := by
  have hsub : crossPairs G i j ⊆
      ((uniq G i j).filter (· ∈ K)).biUnion
          (fun x => (G.neighborFinset x ∩ uniq G j i).image (fun y => (x, y))) ∪
        ((uniq G j i).filter (· ∈ K)).biUnion
          (fun y => (G.neighborFinset y ∩ uniq G i j).image (fun x => (x, y))) := by
    intro p hp
    obtain ⟨⟨hx, hy⟩, hadj⟩ := mem_crossPairs.1 hp
    rcases hK p.1 hx p.2 hy hadj with hK1 | hK2
    · refine Finset.mem_union_left _
        (Finset.mem_biUnion.2 ⟨p.1, Finset.mem_filter.2 ⟨hx, hK1⟩, ?_⟩)
      refine Finset.mem_image.2 ⟨p.2, Finset.mem_inter.2 ⟨?_, hy⟩, rfl⟩
      simpa [SimpleGraph.mem_neighborFinset] using hadj
    · refine Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨p.2, Finset.mem_filter.2 ⟨hy, hK2⟩, ?_⟩)
      refine Finset.mem_image.2 ⟨p.1, Finset.mem_inter.2 ⟨?_, hx⟩, rfl⟩
      simpa [SimpleGraph.mem_neighborFinset] using hadj.symm
  have hA : ∀ x ∈ (uniq G i j).filter (· ∈ K),
      ((G.neighborFinset x ∩ uniq G j i).image (fun y => (x, y))).card ≤ varpi G i j := by
    intro x hx
    refine Finset.card_image_le.trans ?_
    have h1 : boxClose G x i j ≤ (uniq G i j).sup (fun k => boxClose G k i j) :=
      Finset.le_sup (f := fun k => boxClose G k i j) (Finset.mem_filter.1 hx).1
    exact h1.trans (le_max_left _ _)
  have hB : ∀ y ∈ (uniq G j i).filter (· ∈ K),
      ((G.neighborFinset y ∩ uniq G i j).image (fun x => (x, y))).card ≤ varpi G i j := by
    intro y hy
    refine Finset.card_image_le.trans ?_
    have h1 : boxClose G y j i ≤ (uniq G j i).sup (fun w => boxClose G w j i) :=
      Finset.le_sup (f := fun w => boxClose G w j i) (Finset.mem_filter.1 hy).1
    exact h1.trans (le_max_right _ _)
  calc (crossPairs G i j).card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ (∑ x ∈ (uniq G i j).filter (· ∈ K),
            ((G.neighborFinset x ∩ uniq G j i).image (fun y => (x, y))).card)
          + ∑ y ∈ (uniq G j i).filter (· ∈ K),
            ((G.neighborFinset y ∩ uniq G i j).image (fun x => (x, y))).card :=
        add_le_add Finset.card_biUnion_le Finset.card_biUnion_le
    _ ≤ (∑ _x ∈ (uniq G i j).filter (· ∈ K), varpi G i j)
          + ∑ _y ∈ (uniq G j i).filter (· ∈ K), varpi G i j :=
        add_le_add (Finset.sum_le_sum hA) (Finset.sum_le_sum hB)
    _ = _ := by rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, add_mul]

/-- **Lemma 3.6**: `𝔠₄(i, j) ≤ 2σ_{ij}` on every edge. -/
theorem C4_le_two_matchStat (hij : G.Adj i j) : C4 G i j ≤ 2 * matchStat G i j := by
  classical
  have hb := ρmax_pos (G := G) hij
  have hb0 : ρmax G i j ≠ 0 := hb.ne'
  obtain ⟨K, hK, hKcard⟩ := exists_cover_le_matchNum (G := G) i j
  have hP := crossPairs_card_le_cover (G := G) (i := i) (j := j) hK
  have h1 := card_xi_le_crossPairs (G := G) (i := i) (j := j)
  have h2 := card_xi_swap_le_crossPairs (G := G) (i := i) (j := j)
  have hP' : (crossPairs G i j).card ≤ matchNum G i j * varpi G i j :=
    hP.trans (Nat.mul_le_mul_right _ hKcard)
  have hXi : Xi G i j ≤ 2 * (matchNum G i j * varpi G i j) := by
    unfold Xi
    omega
  unfold C4 matchStat
  split_ifs with hv
  · exact mul_nonneg zero_le_two (div_nonneg (Nat.cast_nonneg _) hb.le)
  · have hvpos : (0 : ℝ) < varpi G i j := by exact_mod_cast Nat.pos_of_ne_zero hv
    rw [div_le_iff₀ (mul_pos hvpos hb)]
    have hXi' : (Xi G i j : ℝ) ≤ 2 * ((matchNum G i j : ℝ) * varpi G i j) := by
      exact_mod_cast hXi
    have hcancel : (matchNum G i j : ℝ) / ρmax G i j * ρmax G i j = matchNum G i j :=
      div_mul_cancel₀ _ hb0
    have e : 2 * ((matchNum G i j : ℝ) / ρmax G i j) * ((varpi G i j : ℝ) * ρmax G i j)
        = 2 * ((matchNum G i j : ℝ) * varpi G i j) := by
      linear_combination (2 * (varpi G i j : ℝ)) * hcancel
    rw [e]
    exact hXi'

/-- The first coordinates of a cross matching lie in `ξ_i`, so `𝔪(i, j) ≤ |ξ_i|`. -/
lemma matchNum_le_xi : matchNum G i j ≤ (xi G i j).card := by
  obtain ⟨M, hM, hcard⟩ := exists_max_matching (G := G) i j
  rw [← hcard]
  have hinj : Set.InjOn Prod.fst (M : Set (V × V)) :=
    fun e he e' he' hfst => hM.2.1 e he e' he' hfst
  rw [← Finset.card_image_of_injOn hinj]
  refine Finset.card_le_card fun x hx => ?_
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨h1, h2, h3⟩ := hM.1 e he
  exact mem_xi.2 ⟨h1, e.2, h2, h3⟩

/-! ### Weak duality and the vertex-cover potentials (Proposition 4.10) -/

/-- **Weak duality**: a potential with `f x − f y ≤ d x y` bounds every coupling from below. -/
lemma cost_ge_potential {μ ν : V → ℝ} {π : V → V → ℝ} (f : V → ℝ)
    (hf : ∀ x y, f x - f y ≤ d x y) (hπ : IsCoupling μ ν π) :
    ∑ x, f x * μ x - ∑ y, f y * ν y ≤ cost d π := by
  have h1 : ∑ x, f x * μ x = ∑ x, ∑ y, f x * π x y := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum, hπ.2.1 x]
  have h2 : ∑ y, f y * ν y = ∑ x, ∑ y, f y * π x y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, hπ.2.2 y]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  unfold cost
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have e : f x * π x y - f y * π x y = (f x - f y) * π x y := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (hf x y) (hπ.1 x y)

/-- The potential `f_K` of Proposition 4.10: `2` on `{i} ∪ (U_i \ K)`, `0` on `U_j \ K`, and `1`
elsewhere. -/
noncomputable def coverPot (G : SimpleGraph V) [DecidableRel G.Adj] (i j : V) (K : Finset V)
    (x : V) : ℝ :=
  if x = i ∨ (x ∈ uniq G i j ∧ x ∉ K) then 2 else if x ∈ uniq G j i ∧ x ∉ K then 0 else 1

/-- `f_K` is 1-Lipschitz when `K` is a vertex cover of `B_{ij}`. -/
lemma coverPot_lip (hd : GraphMetric G d) {K : Finset V} (hK : CoversCross G i j K)
    (x y : V) : coverPot G i j K x - coverPot G i j K y ≤ d x y := by
  by_cases hxy : x = y
  · subst hxy; rw [hd.self]; simp
  have h1 := hd.one_le hxy
  have hx2 : coverPot G i j K x ≤ 2 := by unfold coverPot; split_ifs <;> norm_num
  have hy0 : 0 ≤ coverPot G i j K y := by unfold coverPot; split_ifs <;> norm_num
  by_cases hX : x = i ∨ (x ∈ uniq G i j ∧ x ∉ K)
  · by_cases hY : y ∈ uniq G j i ∧ y ∉ K
    · -- the only pairs at potential difference `2` are not adjacent
      have hnadj : ¬ G.Adj x y := by
        rcases hX with hxi | ⟨hxU, hxK⟩
        · rw [hxi]; exact (mem_uniq.1 hY.1).2.2
        · intro hadj
          rcases hK x hxU y hY.1 hadj with h | h
          · exact hxK h
          · exact hY.2 h
      have h2 := hd.two_le hxy hnadj
      linarith
    · have hy1 : 1 ≤ coverPot G i j K y := by
        unfold coverPot
        rw [ite_eq_right hY]
        split_ifs <;> norm_num
      linarith
  · have hx1 : coverPot G i j K x ≤ 1 := by
      unfold coverPot
      rw [ite_eq_right hX]
      split_ifs <;> norm_num
    linarith

lemma coverPot_overlap_sum (hij : G.Adj i j) (K : Finset V) :
    ∑ x ∈ overlap (G := G) i j, coverPot G i j K x = 3 + tri G i j := by
  have hi : i ∉ insert j (common G i j) := by
    simp [mem_common, hij.ne, SimpleGraph.irrefl]
  have hj : j ∉ common G i j := by simp [mem_common, SimpleGraph.irrefl]
  have hfi : coverPot G i j K i = 2 := by simp [coverPot]
  have hfj : coverPot G i j K j = 1 := by
    simp [coverPot, hij.ne', mem_uniq, SimpleGraph.irrefl]
  have hfC : ∀ k ∈ common G i j, coverPot G i j K k = 1 := by
    intro k hk
    obtain ⟨hik, hjk⟩ := mem_common.1 hk
    have hki : k ≠ i := by rintro rfl; exact G.irrefl hik
    simp [coverPot, hki, mem_uniq, hik, hjk]
  simp only [overlap]
  rw [Finset.sum_insert hi, Finset.sum_insert hj, hfi, hfj, Finset.sum_congr rfl hfC,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  simp only [tri]
  ring

lemma coverPot_Ui {K : Finset V} {x : V} (hx : x ∈ uniq G i j) :
    coverPot G i j K x = if x ∈ K then 1 else 2 := by
  obtain ⟨-, hix, -⟩ := mem_uniq.1 hx
  have hxi : x ≠ i := by rintro rfl; exact G.irrefl hix
  have hxUj : x ∉ uniq G j i := uniq_not_mem_swap hx
  by_cases hK : x ∈ K <;> simp [coverPot, hxi, hx, hxUj, hK]

lemma coverPot_Uj {K : Finset V} {x : V} (hx : x ∈ uniq G j i) :
    coverPot G i j K x = if x ∈ K then 1 else 0 := by
  obtain ⟨hxi, -, -⟩ := mem_uniq.1 hx
  have hxUi : x ∉ uniq G i j := uniq_not_mem_swap hx
  by_cases hK : x ∈ K <;> simp [coverPot, hxi, hxUi, hx, hK]

lemma coverPot_sum_Ui (K : Finset V) :
    ∑ x ∈ uniq G i j, coverPot G i j K x
      = 2 * ((uniq G i j).card : ℝ) - (((uniq G i j).filter (· ∈ K)).card : ℝ) := by
  rw [Finset.sum_congr rfl fun x hx => coverPot_Ui (K := K) hx]
  have h : ∀ x ∈ uniq G i j, (if x ∈ K then (1 : ℝ) else 2) = 2 - (if x ∈ K then 1 else 0) := by
    intro x _; split_ifs <;> norm_num
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_boole]
  ring

lemma coverPot_sum_Uj (K : Finset V) :
    ∑ x ∈ uniq G j i, coverPot G i j K x = (((uniq G j i).filter (· ∈ K)).card : ℝ) := by
  rw [Finset.sum_congr rfl fun x hx => coverPot_Uj (K := K) hx, Finset.sum_boole]

/-- The value of the potential `f_K` against `m_i − m_j`, bounding `W₁` from below. -/
theorem W1_ge_cover (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j)
    {K : Finset V} (hK : CoversCross G i j K) :
    (3 + tri G i j) * (w G i - w G j)
      + w G i * (2 * ((uniq G i j).card : ℝ) - ((uniq G i j).filter (· ∈ K)).card)
      - w G j * ((uniq G j i).filter (· ∈ K)).card
      ≤ W1 d (mLazy G i) (mLazy G j) := by
  apply le_W1 (exists_coupling_lazy hij)
  intro π hπ
  have hA : ∑ x, coverPot G i j K x * (if x ∈ overlap (G := G) i j then w G i - w G j else 0)
      = (3 + tri G i j) * (w G i - w G j) := by
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul, coverPot_overlap_sum hij]
  have hB : ∑ x, coverPot G i j K x * (if x ∈ uniq G i j then w G i else 0)
      = w G i * (2 * ((uniq G i j).card : ℝ) - ((uniq G i j).filter (· ∈ K)).card) := by
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul, coverPot_sum_Ui]
    ring
  have hC : ∑ x, coverPot G i j K x * (if x ∈ uniq G j i then w G j else 0)
      = w G j * ((uniq G j i).filter (· ∈ K)).card := by
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_mul, coverPot_sum_Uj]
    ring
  have htot : ∑ x, coverPot G i j K x * mLazy G i x - ∑ x, coverPot G i j K x * mLazy G j x
      = ∑ x, coverPot G i j K x * (if x ∈ overlap (G := G) i j then w G i - w G j else 0)
        + ∑ x, coverPot G i j K x * (if x ∈ uniq G i j then w G i else 0)
        - ∑ x, coverPot G i j K x * (if x ∈ uniq G j i then w G j else 0) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 := lazy_resid_i hij hle x
    have h2 := lazy_resid_j hij hle x
    have e : mLazy G i x - mLazy G j x =
        ((if x ∈ overlap (G := G) i j then w G i - w G j else 0)
          + (if x ∈ uniq G i j then w G i else 0)) - (if x ∈ uniq G j i then w G j else 0) := by
      linarith
    calc coverPot G i j K x * mLazy G i x - coverPot G i j K x * mLazy G j x
        = coverPot G i j K x * (mLazy G i x - mLazy G j x) := by ring
      _ = _ := by rw [e]; ring
  have hval := cost_ge_potential (coverPot G i j K) (coverPot_lip hd hK) hπ
  rw [htot, hA, hB, hC] at hval
  exact hval

/-- `ξ_j` is a vertex cover of the cross-edge graph. -/
lemma coversCross_xi : CoversCross G i j (xi G j i) := by
  intro x hx y hy hxy
  exact Or.inr (mem_xi.2 ⟨hy, x, hx, hxy.symm⟩)

lemma card_filter_xi_left : ((uniq G i j).filter (· ∈ xi G j i)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx hxi
  exact uniq_not_mem_swap hx (xi_subset j i hxi)

lemma card_filter_xi_right : ((uniq G j i).filter (· ∈ xi G j i)).card = (xi G j i).card := by
  congr 1
  ext x
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨xi_subset j i h, h⟩⟩

/-- `(2 + △) w_j + (2 + △) Δ_α + |U_i| w_i = 1`: the lazy measure `m_i` has mass one. -/
lemma lazy_identity (hij : G.Adj i j) :
    (2 + (tri G i j : ℝ)) * w G j + (2 + tri G i j) * (w G i - w G j)
      + (uniq G i j).card * w G i = 1 := by
  have hρw : ρ G i * w G i = 1 - w G i := by
    have h := lazy_nbr_weight hij
    rw [div_eq_iff (ρ_pos hij).ne'] at h
    linarith
  rw [card_uniq_real hij]
  linear_combination hρw

/-- **Proposition 4.10, the cover bound**: for every vertex cover `K` of `B_{ij}`,
`𝔠_OR ≤ −1 + 2 m⁰ + (1 + △) Δ_α + |K ∩ U_i| w_i + |K ∩ U_j| w_j`, with `m⁰ = (2 + △) w_j`. -/
theorem lazy_envelope_cover (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j)
    {K : Finset V} (hK : CoversCross G i j K) :
    cOR G d i j ≤ -1 + 2 * ((2 + tri G i j) * w G j) + (1 + tri G i j) * (w G i - w G j)
      + ((((uniq G i j).filter (· ∈ K)).card : ℝ) * w G i
        + (((uniq G j i).filter (· ∈ K)).card : ℝ) * w G j) := by
  have h := W1_ge_cover hd hij hle hK
  have key := lazy_identity (G := G) hij
  unfold cOR
  linarith

end OllivierBF
