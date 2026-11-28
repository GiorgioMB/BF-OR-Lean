# BF-OR-Lean

[![CI](https://github.com/GiorgioMB/BF-OR-Lean/actions/workflows/ci.yml/badge.svg)](https://github.com/GiorgioMB/BF-OR-Lean/actions/workflows/ci.yml)

A Lean 4 formalization of the main results of

> Giorgio Micaletto and Tebe Nigrelli. *From Proxy to Guarantee: Two-Sided Ollivier–Ricci Bounds
> from Balanced Forman Curvature.* 2026.

Appendix C of the paper describes the formalization. It builds with Lean `v4.36.0-rc1` and the
Mathlib commit pinned in `lake-manifest.json`, has no `sorry`, and declares no axioms. CI builds it
and checks that the theorems below depend only on `propext`, `Classical.choice`, and `Quot.sound`
(`scripts/CheckAxioms.lean`, `scripts/check_axioms.py`).

```bash
lake exe cache get
lake build
```

## Results

| Paper | Lean | File |
|---|---|---|
| Proposition 4.2 | `savings_paper` | `PaperTQ.lean` |
| Theorem 5.2 | `attainable_range_paper` | `AttainableRange.lean` |
| Theorem 5.3 (i) | `tq_lower_paper` | `PaperTQ.lean` |
| Theorem 5.3 (ii) | `tq_upper_paper` | `PaperTQ.lean` |
| Theorem 5.3 (iii) | `tq_range_paper` | `PaperTQ.lean` |
| Theorem 5.3 (iv), the bound `η'` | `tq_upper_blocks_paper` | `PaperTQ.lean` |

## How the statements relate to the paper

**Distance.** Any `GraphMetric`: `0` on the diagonal, `1` on edges, at least `1` between distinct
vertices and at least `2` between distinct non-adjacent ones, the triangle inequality, and symmetry.
Theorem 5.3 (ii) also needs `ThreeApart`: distinct non-adjacent vertices without a common neighbor
are at distance at least `3`. The shortest-path distance of a connected graph has both properties
(`graphMetric_dist`, `threeApart_dist`).

**Measures.** `OneStepAt G μ u`: `μ u` is a probability measure on `N[u]`. Proposition 4.2 and
Theorem 5.3 hold for every one-step measure; locality enters only in Theorem 5.2.

**`W₁`.** The infimum of the cost over couplings. That it depends only on the residuals, the finite
form of Villani's Corollary 1.16, is proved by splicing (`W1_eq_W1_resid`); no duality is used.

**Theorem 5.2.** A consistent graph is any connected graph `G'` with a map, injective on the
vertices of known degree, that preserves the lists of `i`, `j`, `U_i`, and `C` and those degrees
(`Consistent`). Locality is that the measures of `G'` at `i` and `j` are those of `G`, carried by
the map (`Agrees`). The ends are `kappaF ∅` and `kappaMax`, that is, `1 − W₁` with the distance of
the theorem, which equals `1 − 3τ + σ*_F`. A consistent graph has the curvature of its own pairs,
which are admissible (`range_bounds`). The listed edges, the pairs of an admissible `F`, and
pendant vertices that complete the degrees form a connected consistent graph with the curvature of
`F` (`realize_kappa`).

**Theorem 5.3.** `η` is the maximum value of a flow along single edges (`maxFlow`), and it is
attained (`isGreatest_maxFlow`). Every coupling of the residuals moves at most `η` along edges
(`adjMass_le_maxFlow`), and every bound on that mass is at least `η` (`maxFlow_le`); the `η'` of
(iv) is such a bound (`adjMass_le_blocks`). `X₃` and `Y₃` are `IsFarX` and `IsFarY`, as defined in
the theorem, and any subsets of them may be used. In (iv), `B` is any upper bound of the
expression that the paper maximizes, and the blocks are any partition that no supply–demand edge
outside `{i, j}` crosses; the paper's choices, the largest value and the connected components, are
instances. Part (i) holds for every feasible plan, so the order of the greedy routing does not
affect validity.

## Not formalized

Lemma 4.1 and Corollary 5.4 as stated, the running time in Theorem 5.3 (iv), the equality results
of Appendix B, and the experiments, which are in
[Curvature-Transfer-Code](https://github.com/GiorgioMB/Curvature-Transfer-Code).

## Layout

| File | Contents |
|---|---|
| `OllivierBF/Transport.lean` | couplings, cost, `W₁` |
| `OllivierBF/Graph.lean` | `GraphMetric`; `C`, `U_u`, `S` |
| `OllivierBF/Residual.lean` | `W₁` depends only on the residuals; savings of partial plans |
| `OllivierBF/OneStep.lean` | one-step measures, `κ_μ`, `r₊`, `r₋`, `τ` |
| `OllivierBF/TQ.lean` | edge mass, `ThreeApart`, distance-`3` pairs, blocks |
| `OllivierBF/AttainableRange.lean` | Theorem 5.2 |
| `OllivierBF/PaperTQ.lean` | Proposition 4.2 and Theorem 5.3 |
