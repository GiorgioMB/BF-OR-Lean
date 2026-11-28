# BF-OR-Lean

[![CI](https://github.com/GiorgioMB/BF-OR-Lean/actions/workflows/ci.yml/badge.svg)](https://github.com/GiorgioMB/BF-OR-Lean/actions/workflows/ci.yml)

A Lean 4 formalization of the main results of

> Giorgio Micaletto and Tebe Nigrelli. *From Proxy to Guarantee: Two-Sided Ollivier–Ricci Bounds
> from Balanced Forman Curvature.* 2026.

It builds with Lean `v4.36.0-rc1` and the Mathlib commit pinned in `lake-manifest.json`, has no
`sorry`, and declares no axioms; CI checks that the main theorems rest only on Lean's standard
axioms (`scripts/CheckAxioms.lean`).

```bash
lake exe cache get
lake build
```

| Paper | Lean |
|---|---|
| Proposition 4.2 | `savings_paper` |
| Theorem 5.2 | `attainable_range_paper` |
| Theorem 5.3 (i) | `tq_lower_paper` |
| Theorem 5.3 (ii) | `tq_upper_paper` |
| Theorem 5.3 (iii) | `tq_range_paper` |
| Theorem 5.3 (iv) | `tq_upper_blocks_paper` |

The distance is any `GraphMetric`, with `ThreeApart` where a pair must be at distance `3`; the
shortest-path distance of a connected graph is both. Theorem 5.2 ranges over the connected graphs
consistent with the local data (`Consistent`) whose measures agree with `μ` (`Agrees`). Not
formalized: the running time in Theorem 5.3 (iv), and the experiments, which are in
[Curvature-Transfer-Code](https://github.com/GiorgioMB/Curvature-Transfer-Code).
