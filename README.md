# BF-OR-Lean

[![CI](https://github.com/GiorgioMB/BF-OR-Lean/actions/workflows/ci.yml/badge.svg)](https://github.com/GiorgioMB/BF-OR-Lean/actions/workflows/ci.yml)

A Lean 4 formalization of

> Giorgio Micaletto and Tebe Nigrelli. *From Proxy to Certificate: Ollivier–Ricci Bounds from the
> Building Blocks of Balanced Forman Curvature.* 2026.

For an edge of a finite simple graph and a one-step measure, the paper determines the range of the
Ollivier–Ricci (OR) curvature over all graphs consistent with the building blocks of Balanced Forman
curvature (Theorem 5.2), and bounds the curvature by the triangle–quadrangle certificate (Theorem 5.3),
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
| Proposition 4.2 | `savings_paper` | `PaperTQ` |
| Theorem 5.2 | `exact_range_paper` | `ExactRange` |
| Theorem 5.3 (i) | `tq_lower_paper` | `PaperTQ` |
| Theorem 5.3 (ii) | `tq_upper_paper` | `PaperTQ` |
| Theorem 5.3 (iv), the bound `η'` | `tq_upper_blocks_paper` | `PaperTQ` |

The theorems hold for every distance that is a graph metric (`GraphMetric`) and, for the certificates of
distance `3`, separates vertices without short paths (`ThreeApart`); the shortest-path distance of a
connected graph is both (`graphMetric_dist`, `threeApart_dist`). Theorem 5.2 ranges over the connected
graphs, on any vertex type, consistent with the building blocks through a map injective on the known
vertices (`Consistent`), with measures that agree with `μ` at the endpoints (`Agrees`, which is what
locality gives). Its ends are `kappaF ∅` and `kappaMax`, the curvature with the distance of the theorem
(`chargedDist`); `range_bounds` places every consistent graph between them, and the graph `realize F` of
the listed edges, the pairs of `F`, and pendant vertices that complete the degrees attains `kappaF F`
(`realize_kappa`).

Not formalized: part (iii) of Theorem 5.3 and the running time in (iv), and the experiments.

## Layout

| File | Contents |
|---|---|
| `Transport` | couplings and `W₁` |
| `Graph` | graph metrics and the neighbourhoods of an edge |
| `Residual` | `W₁` of the residuals (Villani, Corollary 1.16), savings, extension of partial plans |
| `OneStep` | one-step measures, residuals, Lemma 4.1, Proposition 4.2 |
| `TQ` | Theorem 5.3 |
| `PaperTQ` | Proposition 4.2 and Theorem 5.3 as the paper states them |
| `ExactRange` | Theorem 5.2 |
