# BF-OR-Lean

[![CI](https://github.com/GiorgioMB/BF-OR-Lean/actions/workflows/ci.yml/badge.svg)](https://github.com/GiorgioMB/BF-OR-Lean/actions/workflows/ci.yml)

A Lean 4 formalization of the bounds of

> Giorgio Micaletto and Tebe Nigrelli. *From Proxy to Certificate: Two-Sided Ollivier--Ricci Bounds from Balanced Forman Curvature.* 2026. [arXiv:2603.13535](https://arxiv.org/abs/2603.13535)

For every edge of a finite simple graph, the Balanced Forman (BF) curvature of the edge and the degrees of its
endpoints certify an interval for its lazy Ollivier–Ricci (OR) curvature. This repository proves that
interval, the transport bounds it is built from, the 2-hop interval, the reverse direction, and the
correctness of certify-then-solve. The experiments are in
[Curvature-Transfer-Code](https://github.com/GiorgioMB/Curvature-Transfer-Code).

It builds with Lean `v4.36.0-rc1` and the Mathlib commit pinned in `lake-manifest.json`, has no `sorry`, and
declares no axioms; CI checks that the main theorems rest only on Lean's standard axioms
(`scripts/CheckAxioms.lean`). One published result, Lemma 3.3 of the paper
([Bourne et al.](https://arxiv.org/abs/1704.04398)), is not re-proved: it is the hypothesis `BourneFact` of
Proposition 4.1 only.

```bash
lake exe cache get
lake build
```

## The main theorem

The BF interval (Corollary 5.8), with the endpoints labelled so that `ρ G i ≤ ρ G j`:

```lean
theorem bf_interval_paper (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) :
    phiInt (ρ G i) (ρ G j) (cBF G i j) ≤ cOR G d i j ∧ cOR G d i j ≤ psiInt G i j (cBF G i j)
```

The theorems hold for every `d` with `GraphMetric G d` (zero on the diagonal, one on edges, at least one
between distinct vertices and two between non-adjacent ones, symmetric, triangle inequality);
`graphMetric_dist` shows that the shortest-path distance of a connected graph qualifies. `W1` is the infimum
of the transport cost over couplings: lower ends come from explicit couplings (`W1_le_cost`), upper ends
from 1-Lipschitz potentials (`cost_ge_potential`).

## What is proved

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
