/-
  Algorithm 1 of the paper (certify-then-solve) for the threshold set `{e ∈ E : κ(e) < ϑ}`.

  `certifyThenSolve` runs the three stages of the algorithm on an arbitrary finite set of edges:
  an interval `[lo e, up e]` on every edge, a second upper certificate `upPrior` on the edges it
  leaves undecided, and the exact value `κ` (the transport problem) on the edges that are still
  undecided. `certifyThenSolve_eq` proves that it returns exactly `{e ∈ E : κ(e) < ϑ}` whenever
  the certificates are valid, and `certifyThenSolve_paper` instantiates it with the 2-hop interval
  `[L^lazy_{ij}, U^lazy_{ij}]` and an arbitrary valid second-stage certificate. In the paper that
  certificate is the dual bound of TLW, whose validity is not formalized.
-/
module

public import OllivierBF.Paper

@[expose] public section

set_option linter.unusedSectionVars false

namespace OllivierBF

section algorithm

variable {ι : Type*}

/-- The upper end after the second stage: on the edges that the interval leaves undecided,
intersect with the second certificate `upPrior`. -/
noncomputable def stage2 (lo up upPrior : ι → ℝ) (ϑ : ℝ) (e : ι) : ℝ :=
  if lo e < ϑ ∧ ϑ ≤ up e then min (up e) (upPrior e) else up e

/-- The upper end after the third stage: on the edges that are still undecided, the exact
value. -/
noncomputable def stage3 (lo up upPrior κ : ι → ℝ) (ϑ : ℝ) (e : ι) : ℝ :=
  if lo e < ϑ ∧ ϑ ≤ stage2 lo up upPrior ϑ e then κ e else stage2 lo up upPrior ϑ e

/-- **Algorithm 1** (certify-then-solve): the edges whose final upper end is below `ϑ`. -/
noncomputable def certifyThenSolve (E : Finset ι) (lo up upPrior κ : ι → ℝ) (ϑ : ℝ) :
    Finset ι :=
  E.filter fun e => stage3 lo up upPrior κ ϑ e < ϑ

/-- **Algorithm 1 is correct**: if `lo ≤ κ ≤ up` and `κ ≤ upPrior` on every edge, it returns
exactly `{e ∈ E : κ(e) < ϑ}`. -/
theorem certifyThenSolve_eq (E : Finset ι) (lo up upPrior κ : ι → ℝ) (ϑ : ℝ)
    (hlo : ∀ e ∈ E, lo e ≤ κ e) (hup : ∀ e ∈ E, κ e ≤ up e)
    (hprior : ∀ e ∈ E, κ e ≤ upPrior e) :
    certifyThenSolve E lo up upPrior κ ϑ = E.filter fun e => κ e < ϑ := by
  unfold certifyThenSolve
  apply Finset.filter_congr
  intro e he
  have h1 := hlo e he
  have h2 := hup e he
  have h3 := hprior e he
  unfold stage3 stage2
  by_cases hA : lo e < ϑ ∧ ϑ ≤ up e
  · -- undecided after the first stage
    rw [if_pos hA]
    by_cases hB : lo e < ϑ ∧ ϑ ≤ min (up e) (upPrior e)
    · -- still undecided: the exact value decides
      rw [if_pos hB]
    · -- decided by the second certificate: `κ ≤ min (up, upPrior) < ϑ`
      rw [if_neg hB]
      have hmin : min (up e) (upPrior e) < ϑ := by
        by_contra hc
        exact hB ⟨hA.1, not_lt.mp hc⟩
      have hk : κ e ≤ min (up e) (upPrior e) := le_min h2 h3
      exact ⟨fun _ => lt_of_le_of_lt hk hmin, fun _ => hmin⟩
  · -- decided by the interval: `up < ϑ` puts the edge in, `ϑ ≤ lo` keeps it out
    rw [if_neg hA, if_neg hA]
    constructor
    · intro hu
      exact lt_of_le_of_lt h2 hu
    · intro hk
      by_contra hc
      exact hA ⟨lt_of_le_of_lt h1 hk, not_lt.mp hc⟩

end algorithm

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : V → V → ℝ}

/-- **Algorithm 1 with the certificates of the paper**: for oriented edges `(i, j)` with
`d_i ≤ d_j`, the 2-hop interval `[L^lazy_{ij}, U^lazy_{ij}]` (Theorem 4.7 and Proposition 4.10),
any valid second-stage certificate `upPrior`, and the exact lazy OR curvature, the algorithm
returns exactly the edges with `κ_OR(i, j) < ϑ`. -/
theorem certifyThenSolve_paper (hd : GraphMetric G d) (E : Finset (V × V))
    (hE : ∀ e ∈ E, G.Adj e.1 e.2 ∧ ρ G e.1 ≤ ρ G e.2) (upPrior : V × V → ℝ)
    (hprior : ∀ e ∈ E, cOR G d e.1 e.2 ≤ upPrior e) (ϑ : ℝ) :
    certifyThenSolve E
        (fun e => Llazy (ρ G e.1) (ρ G e.2) (tri G e.1 e.2) (matchNum G e.1 e.2))
        (fun e => Ulazy G e.1 e.2) upPrior (fun e => cOR G d e.1 e.2) ϑ
      = E.filter fun e => cOR G d e.1 e.2 < ϑ := by
  apply certifyThenSolve_eq
  · intro e he
    exact lazy_quadrangle hd (hE e he).1 (hE e he).2
  · intro e he
    exact (lazy_envelope_paper hd (hE e he).1 (hE e he).2).1
  · exact hprior

end OllivierBF
