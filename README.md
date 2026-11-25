# BF-OR-Lean

[![CI](https://github.com/GiorgioMB/BF-OR-Lean/actions/workflows/ci.yml/badge.svg)](https://github.com/GiorgioMB/BF-OR-Lean/actions/workflows/ci.yml)

A Lean 4 formalization of

> Giorgio Micaletto and Tebe Nigrelli. *From Proxy to Certificate: Ollivier–Ricci Bounds from the
> Building Blocks of Balanced Forman Curvature.* 2026.

For every edge of a finite simple graph and every one-step measure (lazy, non-lazy, or of uniform
idleness), the triangles and quadrangles at the endpoints certify an interval for the Ollivier–Ricci
(OR) curvature of the edge. This repository proves the savings form of the transport problem, the
certificate, its version for uniform idleness, and the correctness of certify-then-solve. The results
of the previous version of the paper (the BF interval and the 2-hop interval) remain proved here.
The experiments are in [Curvature-Transfer-Code](https://github.com/GiorgioMB/Curvature-Transfer-Code).

It builds with Lean `v4.36.0-rc1` and the Mathlib commit pinned in `lake-manifest.json`, has no `sorry`, and
declares no axioms; CI checks that the main theorems rest only on Lean's standard axioms
(`scripts/CheckAxioms.lean`). Published results enter only as hypotheses: Theorems 1.1 and 5.5 of
[Bourne et al.](https://arxiv.org/abs/1704.04398) as `BourneLinear` (Corollary 5.4) and, for the previous
version, their case `BourneFact` (Proposition 4.1 there).

```bash
lake exe cache get
lake build
```

## The main theorem

The triangle–quadrangle certificate (Theorem 5.3), for a one-step measure `μ`, a vertex cover `K` of the
edges between residual supply and demand, and the far sets `X₃`, `Y₃`:

```lean
theorem tq_upper_cover_paper (hd : GraphMetric G d) (h3 : ThreeApart G d)
    (hi : OneStepAt G μ i) (hj : OneStepAt G μ j) {K : Finset V} (hK : CoversResid G μ i j K)
    {X Y : Finset V} (hX : IsFarX G i j X) (hY : IsFarY G i j Y) :
    cORm d μ i j ≤ 1 - 2 * resMass μ i j + (∑ x ∈ K, resP μ i j x + ∑ y ∈ K, resN μ i j y)
      - max 0 (max (∑ x ∈ X, resP μ i j x - ∑ y ∈ overlap i j, resN μ i j y)
        (∑ y ∈ Y, resN μ i j y - ∑ x ∈ overlap i j, resP μ i j x))
```

with the lower end `tq_lower_paper`. `W1` is the infimum of the transport cost over couplings; lower ends
come from explicit couplings (`W1_le_cost`), and upper ends from bounds valid for every coupling of the
residuals, through `W1_eq_W1_resid`, the finite form of Corollary 1.16 of Villani, proved here by splicing
the mass that passes through each vertex. `ThreeApart` (distinct, non-adjacent vertices without a common
neighbour are at distance at least 3) holds for the shortest-path distance (`threeApart_dist`).

## What is proved

| Paper | Lean | File |
|---|---|---|
| Lemma 4.1 | `residuals_paper`; `resP_mLazy`, `resN_mLazy` for the lazy measure | `PaperTQ`, `OneStep` |
| Proposition 4.2 | `savings_paper`; `W1_eq_W1_resid` (Villani, Corollary 1.16), `cost_eq_three_mass_sub_savings` | `PaperTQ`, `Residual` |
| Theorem 5.3 (i) | `tq_lower_paper`; `exists_extension` for partial plans | `PaperTQ`, `Residual` |
| Theorem 5.3 (ii) | `tq_upper_paper` for any bound on the mass along edges; `tq_upper_cover_paper` for vertex covers | `PaperTQ`, `TQ` |
| Theorem 5.3 (iv), the bound `η'` | `tq_upper_blocks_paper` (componentwise bound) | `PaperTQ`, `TQ` |
| Theorem 5.3, lazy measure | `tq_lazy_paper` | `PaperTQ` |
| Corollary 5.4 | `idleness_paper`, `idleness_bounds`, `idleness_sign` (hypothesis `BourneLinear`) | `PaperTQ`, `Idleness` |
| Algorithm 1 | `certifyThenSolve_tq` | `TQ` |

Not formalized: Theorem 5.2 (the exact range over consistent graphs and its attainment, which need
constructions of graphs), parts (iii) and (iv) of Theorem 5.3 other than the bound `η'` (the containment of
the exact range, and the running time), the order of the greedy routing (any order gives a valid lower end),
and Remark 3.1.

### Results of the previous version

| Paper | Lean | File |
|---|---|---|
| Lemma 3.6 | `C4_le_two_matchStat`; `exists_cover_le_matchNum` (König's theorem, from Hall's) | `Cover` |
| Proposition 4.1 | `mixing_transfer_paper`, `cLLY_le_q_paper` (hypothesis `BourneFact`) | `Paper` |
| Theorem 4.3 | `jl_aug`; `jl_aug_exact_of_perfect` with the Jost–Liu upper bound `cOR0_le_tri_div` | `Bounds`, `Exactness` |
| Lemma 4.6 | `lazy_min`, `lazy_resid_i`, `lazy_resid_j` | `Curvature` |
| Theorem 4.7 | `lazy_quadrangle`; `lazy_quadrangle_exact_of_perfect` | `Bounds`, `Exactness` |
| Proposition 4.8 | `lazy_envelope_paper`; `lazy_envelope_cover` for every vertex cover; `mUU_le` | `Paper`, `Cover` |
| Proposition 5.1 | `bf_is_third_piece` (i); `LBF_eq`, `LBF_le_Lsq`, `bf_excess` (ii); `bfB_le_bfA` (iii) | `Bounds`, `Unclipped` |
| Theorem 5.4 | `bf_lower_paper` | `Paper` |
| Proposition 5.5 | `cBF_le_range` | `Paper` |
| Lemma 5.6 | `budget_region` | `Paper` |
| Theorem 5.7 | `bf_upper_paper` | `Paper` |
| Corollary 5.8 | `bf_interval_paper`; `phiInt_le_Llazy` | `Paper` |
| Proposition 5.9 | `two_hop_interval_paper` | `Paper` |
| Algorithm 1 | `certifyThenSolve_eq`; `certifyThenSolve_paper` for the 2-hop interval and any valid second stage | `Screening` |
| Proposition B.1 | `envelope_arbitrary_idleness` | `ArbitraryIdleness` |
| Corollary C.1 | `or_to_bf_lower_paper`; `coverage_bound` for (C.1) | `Paper` |
| Corollary C.2 | `or_to_bf_upper_paper` | `Paper` |

Not formalized: the statements that follow from the formulas by direct computation (the regularity and
monotonicity of the moduli, the deficit and closed forms, the identities of Remarks 4.5 and 5.3, Corollary 4.2
given Proposition 4.1, the last claim of Proposition 5.1 (iii) given (ii), and the comparisons between
explicit bounds in Proposition 5.5, Corollary 5.8, Proposition B.1, and Appendix A);
the exactness of Theorems 4.3 and 4.7 on edges that lie on no cycle of length at most 5; the exactness
statements of Theorem 5.4 and Corollary 5.8; the maximizers of `Ψ` and the `O(1)` evaluation; the comparison
after Corollary C.2; the examples; and the validity of the dual bound of TLW that Algorithm 1 uses.

## Layout

| File | Contents |
|---|---|
| `Transport` | couplings, `W1`, mixtures of couplings, the overlap lower bound |
| `Graph` | `GraphMetric`, neighbourhood statistics, cross matchings |
| `Curvature` | measures, the curvatures `cOR`, `cOR0`, `cORp`, `cLLY`, `cBF`, `BourneFact`, Lemma 4.6 |
| `Algebra` | the closed forms `L^lazy`, `L⁰`, `S`, `T`, `λ₁`, `λ₂` and their identities (no graphs) |
| `Bounds` | Theorems 4.3 and 4.7, Proposition 5.1 (i), the mixing transfer behind Proposition 4.1 |
| `Interval` | `S`, `T`, `□_{ij}` in the notation of `Algebra`, and the budget behind Lemma 5.6 |
| `Cover` | König's theorem for the cross-edge graph, Lemma 3.6, the vertex-cover potentials of Proposition 4.8 |
| `Paper` | the results of Sections 4–5 and Appendix C in the form of the paper |
| `Unclipped`, `Exactness`, `ArbitraryIdleness`, `Screening` | Proposition 5.1 (ii)–(iii), the exactness results, Proposition B.1, Algorithm 1 |
| `Residual` | `W₁` of the residuals (Villani, Corollary 1.16), savings, extension of partial plans |
| `OneStep` | one-step measures, residuals, Lemma 4.1, Proposition 4.2, lazy and uniform-idleness instances |
| `TQ` | Theorem 5.3: both ends, vertex-cover and componentwise bounds, `ThreeApart`, Algorithm 1 |
| `Idleness` | Corollary 5.4 under `BourneLinear` |
| `PaperTQ` | the results of this version in the form in which the paper states them |
