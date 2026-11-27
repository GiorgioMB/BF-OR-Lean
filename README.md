# BF-OR-Lean

[![CI](https://github.com/GiorgioMB/BF-OR-Lean/actions/workflows/ci.yml/badge.svg)](https://github.com/GiorgioMB/BF-OR-Lean/actions/workflows/ci.yml)

A Lean 4 formalization of

> Giorgio Micaletto and Tebe Nigrelli. *From Proxy to Guarantee: Two-Sided Ollivier–Ricci Bounds
> from Balanced Forman Curvature.* 2026.

For an edge of a finite simple graph and a one-step measure, the paper determines the range of the
Ollivier–Ricci (OR) curvature over all graphs consistent with the local data of Balanced Forman
curvature (Theorem 5.2), and bounds the curvature by the triangle–quadrangle bound (Theorem 5.3),
through the savings form of the transport problem (Proposition 4.2). This repository proves these
results, and only these. The experiments are in
[Curvature-Transfer-Code](https://github.com/GiorgioMB/Curvature-Transfer-Code).

It builds with Lean `v4.36.0-rc1` and the Mathlib commit pinned in `lake-manifest.json`, has no `sorry`, and
declares no axioms; CI checks that the main theorems rest only on Lean's standard axioms
(`scripts/CheckAxioms.lean`).

```bash
lake exe cache get
lake build
```

## Results

| Paper | Lean | File |
|---|---|---|
| Lemma 4.1 | `residuals_full_paper` | `ResidualsFull` |
| Lemma 4.1, the lazy measure | `lazy_residuals_paper` | `ResidualsFull` |
| Proposition 4.2 | `savings_paper` | `PaperTQ` |
| Proposition 4.2, `σ*` a maximum and `κ_μ = 1 − 3τ + σ*` | `savings_max_paper` | `SavingsMax` |
| Theorem 5.2 | `attainable_range_paper` | `AttainableRange` |
| Theorem 5.2, ends `1 − 3τ + σ*_∅` and `1 − 3τ + max_F σ*_F` | `attainable_range_savings_paper` | `RangeSavings` |
| Theorem 5.3 (i) | `tq_lower_paper` | `PaperTQ` |
| Theorem 5.3 (ii) | `tq_upper_paper` | `PaperTQ` |
| Theorem 5.3 (ii), `η` the maximum flow | `tq_upper_maxFlow_paper` | `MaxFlow` |
| Theorem 5.3 (iv), the bound `η'` | `tq_upper_blocks_paper` | `PaperTQ` |
| Theorem 5.3 (iv), `η' ≥ η` | `maxFlow_le_blocks_paper` | `MaxFlow` |

The theorems hold for every distance that is a graph metric (`GraphMetric`) and, where a pair must
be at distance `3`, separates vertices without short paths (`ThreeApart`); the shortest-path
distance of a connected graph is both (`graphMetric_dist`, `threeApart_dist`). Theorem 5.2 ranges
over the connected graphs, on any vertex type, consistent with the local data through a map
injective on the known vertices (`Consistent`), with measures that agree with `μ` at the endpoints
(`Agrees`, which is what locality gives). Its ends are `kappaF ∅` and `kappaMax`, the curvature with
the distance of the theorem (`chargedDist`); `range_bounds` places every consistent graph between
them, and the graph `realize F` of the listed edges, the pairs of `F`, and pendant vertices that
complete the degrees attains `kappaF F` (`realize_kappa`). `attainable_range_savings_paper` states the ends as the paper
does, `1 − 3τ + σ*_∅` and `1 − 3τ + max_F σ*_F`: `chargedDist F` need not be a metric, but it
satisfies the triangle inequality through `S` (`chargedDist_tri_overlap`), which is all the residual
reduction needs (`W1_eq_W1_resid_on`), so `kappaF F = 1 − 3τ + σ*_F` (`kappaF_eq_sigmaStar`).

Not formalized: part (iii) of Theorem 5.3 and the running time in (iv), and the experiments.

## Layout

| File | Contents |
|---|---|
| `Transport` | couplings and `W₁` |
| `Graph` | graph metrics and the neighbourhoods of an edge |
| `Residual` | `W₁` of the residuals (Villani, Corollary 1.16), savings, extension of partial plans |
| `OneStep` | one-step measures, residuals, Lemma 4.1, Proposition 4.2 |
| `ResidualsFull` | Lemma 4.1 in full: supports, distances on `N[i] ∪ N[j]`, the lazy measure |
| `TQ` | Theorem 5.3 |
| `SavingsMax` | `σ*` as a maximum over partial plans (compactness), Proposition 4.2 as displayed |
| `PaperTQ` | Proposition 4.2 and Theorem 5.3 as the paper states them |
| `AttainableRange` | Theorem 5.2 |
| `RangeSavings` | the residual reduction for the charged distance, Theorem 5.2 in savings form |
| `MaxFlow` | `η` as a maximum flow, Theorem 5.3 (ii) and (iv) with it |
