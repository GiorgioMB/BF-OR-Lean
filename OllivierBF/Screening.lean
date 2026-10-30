/-
  The correctness of Algorithm 1 of the paper (certify-then-solve for the threshold set
  `{e : 𝔠_OR(e) < ϑ}`). The first stage computes an interval `[ℓ_e, u_e]` on every edge, the
  second intersects the upper end with a further certificate `U'_e` (the TLW bound in the paper)
  on the edges that the first leaves undecided, and the third solves the transport problem on the
  edges that are still undecided, which collapses their interval to the exact value.
  `certifyThenSolve_eq` holds for any valid intervals; `certifyThenSolve_paper` instantiates it
  with the 2-hop interval of Proposition 5.9. The second certificate enters as a hypothesis,
  because the TLW bound is not formalized here.
-/

module

public import OllivierBF.Paper

@[expose] public section

set_option linter.unusedSectionVars false

namespace OllivierBF

section abstract

variable {E : Type*}

/-- Upper end after the second stage: intersected with `U'` on the edges left undecided. -/
noncomputable def stage2Upper (ϑ : ℝ) (ℓ u U' : E → ℝ) (e : E) : ℝ :=
  if ℓ e < ϑ ∧ ϑ ≤ u e then min (u e) (U' e) else u e

/-- Upper end after the third stage: the edges still undecided are solved exactly. -/
noncomputable def stage3Upper (ϑ : ℝ) (c ℓ u U' : E → ℝ) (e : E) : ℝ :=
  if ℓ e < ϑ ∧ ϑ ≤ stage2Upper ϑ ℓ u U' e then c e else stage2Upper ϑ ℓ u U' e

/-- The output of Algorithm 1 on the edges `S`: the edges whose final upper end is below `ϑ`. -/
noncomputable def certifyThenSolve (S : Finset E) (ϑ : ℝ) (c ℓ u U' : E → ℝ) : Finset E :=
  S.filter fun e => stage3Upper ϑ c ℓ u U' e < ϑ

/-- **Algorithm 1 is exact**: if `ℓ ≤ c ≤ u` and `c ≤ U'` on every edge, certify-then-solve
returns exactly the edges with `c < ϑ`. -/
theorem certifyThenSolve_eq (S : Finset E) (ϑ : ℝ) {c ℓ u U' : E → ℝ}
    (hℓ : ∀ e ∈ S, ℓ e ≤ c e) (hu : ∀ e ∈ S, c e ≤ u e) (hU : ∀ e ∈ S, c e ≤ U' e) :
    certifyThenSolve S ϑ c ℓ u U' = S.filter fun e => c e < ϑ := by
  ext e
  simp only [certifyThenSolve, Finset.mem_filter]
  constructor
  · rintro ⟨he, h⟩
    refine ⟨he, ?_⟩
    have h2 : c e ≤ stage2Upper ϑ ℓ u U' e := by
      unfold stage2Upper
      split_ifs
      · exact le_min (hu e he) (hU e he)
      · exact hu e he
    unfold stage3Upper at h
    split_ifs at h with h3
    · exact h
    · exact lt_of_le_of_lt h2 h
  · rintro ⟨he, h⟩
    refine ⟨he, ?_⟩
    unfold stage3Upper
    split_ifs with h3
    · exact h
    · by_cases hl : ℓ e < ϑ
      · have hn : ¬ ϑ ≤ stage2Upper ϑ ℓ u U' e := fun hb => h3 ⟨hl, hb⟩
        exact not_le.1 hn
      · exact absurd h (not_lt.2 ((not_lt.1 hl).trans (hℓ e he)))

end abstract

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ}

/-- **Algorithm 1 with the 2-hop interval**: on any finite set of edges, oriented so that
`ρ_i ≤ ρ_j`, and for any further valid upper certificate `U'`, certify-then-solve started from
`[L^lazy, U^lazy]` returns exactly the edges with `𝔠_OR < ϑ`. -/
theorem certifyThenSolve_paper (hd : GraphMetric G d) (S : Finset (V × V))
    (hS : ∀ e ∈ S, G.Adj e.1 e.2 ∧ ρ G e.1 ≤ ρ G e.2) (ϑ : ℝ) {U' : V × V → ℝ}
    (hU : ∀ e ∈ S, cOR G d e.1 e.2 ≤ U' e) :
    certifyThenSolve S ϑ (fun e => cOR G d e.1 e.2)
        (fun e => Llazy (ρ G e.1) (ρ G e.2) (tri G e.1 e.2) (matchNum G e.1 e.2))
        (fun e => Ulazy G e.1 e.2) U'
      = S.filter fun e => cOR G d e.1 e.2 < ϑ :=
  certifyThenSolve_eq S ϑ (fun e he => lazy_quadrangle hd (hS e he).1 (hS e he).2)
    (fun e he => (lazy_envelope_paper hd (hS e he).1 (hS e he).2).1) hU

end OllivierBF
