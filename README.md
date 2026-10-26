# BF-OR-Lean
A Lean 4 formalization of the main results of

> Giorgio Micaletto and Tebe Nigrelli. *What Balanced Forman Curvature Certifies About Ollivier–Ricci Curvature.* 2026.

For every edge of a finite simple graph, the paper shows that the Balanced Forman (BF) curvature of the edge and the degrees of its two endpoints certify a two-sided interval for its lazy Ollivier–Ricci (OR) curvature, without solving an optimal transport problem. This repository proves that interval in Lean, together with the transport bounds it is built from, its sharpened form, the comparison with the bound of Bhattacharya and Mukherjee, and the reverse direction (what an OR value certifies about BF).

- **Builds** with Lean `v4.36.0-rc1` and Mathlib commit [`cf5dd31`](https://github.com/leanprover-community/mathlib4/commit/cf5dd317652efe9d9d17252014a4cd442bf86469), both pinned in this repository.
- **Contains no `sorry`** and **declares no axioms**.
- **Four published results** cited by the paper are not re-proved. They enter as hypotheses of the theorems that use them, collected in the structure `CitedFacts` ([below](#cited-results)).

The experiments of the paper are in a separate repository, [Curvature-Transfer-Code](https://github.com/GiorgioMB/Curvature-Transfer-Code).

## Building

Install Lean through [elan](https://github.com/leanprover/elan), then run from the repository root:

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
```

`lean-toolchain` pins the Lean version and `lake-manifest.json` pins Mathlib, so `lake build` checks exactly the code described here. Running `lake update` moves to a newer Mathlib, which may need small fixes. The build prints deprecation and linter warnings but no errors.

To see what a theorem rests on, add to any file that imports `OllivierBF`:

```lean
#print axioms OllivierBF.bf_interval
```

The output should list only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The cited results do not appear there because they are hypotheses, not axioms.

## The main theorem

The BF interval of the paper (Corollary 5.6), for an edge whose endpoints both have degree at least 2:

```lean
theorem bf_interval (hd : GraphMetric G d) (cited : CitedFacts G d) (hij : G.Adj i j)
    (hle : ρ G i ≤ ρ G j) (h2 : 2 ≤ ρ G i) :
    phiElem (ρ G i) (ρ G j) (cBF G i j) ≤ cOR G d i j ∧ cOR G d i j ≤ psiUp G i j (cBF G i j)
```

Here `phiElem` is the lower modulus of Theorem 5.4 and `psiUp` the upper modulus of Theorem 5.5; both depend only on the BF value and the two degrees.

## What is proved

Numbering follows the current version of the manuscript. The last column lists the fields of `CitedFacts` that each proof actually uses.

| Paper | Lean | File | Cited results used |
|---|---|---|---|
| Lemma 3.6 (bound for Ξ) | `Xi_le` | `Graph` | none |
| Lemma 3.7 (box-count bound) | `varpi_le` | `Graph` | none |
| Proposition 4.1 (idleness transfer by mixing) | `mixing_transfer`, `mixing_dominates` | `Bounds` | `bourne` |
| Corollary 4.2 (triangle-free version) | `mixing_triangle_free` | `Bounds` | `bourne` |
| Theorem 4.4 (quadrangle-augmented Jost–Liu bound) | `jl_aug` | `Bounds` | none |
| Remark 4.5 and Appendix B (comparison with Bhattacharya–Mukherjee) | `LBM_le_Lsq`, `LBM_eq_Lsq_iff` | `Appendix` | none |
| Remark 4.6 (identity for the matching term) | `pos_part_sub_pos_part` | `Algebra` | none |
| Lemma 4.7 (one-sided residuals) | `lazy_min`, `lazy_resid_i`, `lazy_resid_j` | `Curvature` | none |
| Theorem 4.8 (lazy quadrangle bound) | `lazy_quadrangle` | `Bounds` | none |
| Proposition 4.11 (lazy transport envelope) | `lazy_envelope` | `Bounds` | `saturate` |
| Proposition 5.1 (i) (BF as an unclipped Jost–Liu bound) | `bf_is_third_piece` | `Bounds` | none |
| Remark 5.3 (the identities and inequalities it rests on) | `Llazy_sub_lamMix`, `lamMix_piece3_le`, `lamOld_piece3_le`, `lamTF_piece3_le` | `Algebra` | none |
| Theorem 5.4 (lower modulus) | `bf_lower`; `bf_lower_leaf` for an endpoint of degree 1; `phiElem_ge_lamTF` for the comparison with the lifts | `Interval` | `topping11` (`bf_lower` only) |
| Theorem 5.5 (upper modulus) | `bf_upper`, `psiUp_mono` | `Interval` | `saturate` |
| Corollary 5.6 (BF interval) | `bf_interval` | `Interval` | `saturate`, `topping11` |
| Proposition 5.7 (sharpened interval) | `sharpened_interval` | `Interval` | `saturate`, `topping11` |
| Proposition C.1 (coverage envelope) | `coverage_envelope` | `Appendix` | `saturate` |
| Corollary C.2 (lower bound on BF) | `or_to_bf_lower_env`, and the explicit special case `or_to_bf_lower` | `Appendix` | `saturate` |
| Corollary C.3 (upper bound on BF) | `or_to_bf_old` and `or_to_bf_mixing` (the terms of the first bound); `or_to_bf_elementary` (the second bound) | `Appendix` | `bourne`, `topping` (first two); none (third) |

The BF interval and the sharpened interval need only Villani's saturation result and Lemma 11 of Topping et al. The quadrangle-augmented Jost–Liu bound and the lazy quadrangle bound need none of the four.

## Cited results

| Field of `CitedFacts` | Statement in Lean | Source |
|---|---|---|
| `bourne` | `𝔠_{OR-p} = (1 − p) 𝔠_LLY` at `p = 1/(ρ_max + 1)` | [Bourne, Cushing, Liu, Münch, and Peyerimhoff (2018)](https://arxiv.org/abs/1704.04398), Theorems 1.1 and 5.5 |
| `topping` | `𝔠_BF ≤ 𝔠_LLY` | [Topping et al. (2022)](https://arxiv.org/abs/2111.14522), Theorem 2 |
| `topping11` | `𝔠_4 ≤ 2 𝒮` when `ρ_min ≥ 2` | Topping et al. (2022), Lemma 11 |
| `saturate` | every coupling can be replaced, at no larger cost, by one that keeps `min(μ(k), ν(k))` in place at every `k` | [Villani (2003)](https://bookstore.ams.org/gsm-58), Corollary 1.16 |

Every theorem that needs one of these takes `cited : CitedFacts G d` as an argument, so its statement is an implication from the cited results. Lean checks the implication; the agreement between each field and its published source is checked by hand.

## Modelling choices

- **Graphs.** `G : SimpleGraph V` on a finite type `V`. Connectedness is needed only to show that the shortest-path distance satisfies `GraphMetric`.
- **Distance.** The theorems hold for any `d : V → V → ℝ` with `GraphMetric G d`, which records the facts the proofs use: `d` vanishes on the diagonal, equals 1 on edges, is at least 1 between distinct vertices and at least 2 between distinct non-adjacent ones, is symmetric, and satisfies the triangle inequality. `graphMetric_dist` shows that the shortest-path distance of a connected graph qualifies.
- **Transport.** `W1 d μ ν` is the infimum of the cost over couplings. Upper bounds come from explicit couplings (`W1_le_cost`) and lower bounds from bounds valid for every coupling (`le_W1`); the existence of optimal couplings is never used.
- **Curvatures** (`Curvature.lean`). `mLazy u` is the uniform measure on the closed neighbourhood of `u` and `mp p u` the measure with idleness `p`. `cOR`, `cOR0`, and `cORp` are the lazy, non-lazy, and idleness-`p` OR curvatures, `cLLY` is the left limit at `p = 1` of `cORp p / (1 − p)`, and `cBF` is Balanced Forman curvature as in Definition 3.2 of the paper. `matchNum` is the matching number of the cross-edge graph.
- **Endpoint labels.** Most theorems label the endpoints so that `ρ G i ≤ ρ G j`. The mixing results (`mixing_transfer`, `mixing_dominates`, `mixing_triangle_free`, `or_to_bf_old`, `or_to_bf_mixing`) use `ρ G j ≤ ρ G i`, as Proposition 4.1 does.

## Not formalized

- The exactness statements on trees, complete graphs, and hypercubes (Theorems 4.4, 4.8, and 5.4, and Remark 4.3).
- Regularity and computation: the continuity, monotonicity, and convexity of the lower modulus; the concavity of `Ψ̂` and the finite set of candidate maximizers (`psiUp` is defined as a supremum, which is all the bounds need); the `O(1)` evaluation in Corollary 5.6; and the concavity of `Θ` and the computation of `t_min` in Appendix C.
- Proposition 4.9 (the envelope for arbitrary idleness) and the comparisons with its envelope `U^env` in Propositions 4.11 and 5.7.
- Parts (ii) and (iii) of Proposition 5.1.
- In Proposition 5.7, the upper end appears as `𝔠_OR ≤ Ψ̂(△) ≤ ψ(𝔠_BF)`, with `Ψ̂` evaluated at the true triangle count. The inequality `U^lazy ≤ Ψ̂(△)` is proved inside `sharpened_interval` but not stated separately.
- Edges with an endpoint of degree 1: `bf_upper`, `bf_interval`, and `sharpened_interval` assume both degrees are at least 2, and for such edges only the lower end is formalized (`bf_lower_leaf`).
- The closed form of the Bhattacharya–Mukherjee matching number in Remark 4.5. `LBM` is defined through it rather than from their definition.
- The inequality in Proposition 4.1 and the closed-form difference between the two lifts in Corollary 4.2.

## Layout

| File | Contents |
|---|---|
| `OllivierBF/Transport.lean` | Couplings, `W1`, mixtures of couplings, and the overlap lower bound |
| `OllivierBF/Graph.lean` | `GraphMetric`, neighbourhood statistics, cross matchings, Lemmas 3.6 and 3.7 |
| `OllivierBF/Curvature.lean` | Measures, curvatures, `CitedFacts`, and Lemma 4.7 |
| `OllivierBF/Algebra.lean` | Real-number identities behind Theorem 5.4 and Remark 5.3 (no graphs) |
| `OllivierBF/Bounds.lean` | Theorems 4.4 and 4.8, Propositions 4.1, 4.11, and 5.1 (i), and Corollary 4.2 |
| `OllivierBF/Interval.lean` | Theorems 5.4 and 5.5, Corollary 5.6, and Proposition 5.7 |
| `OllivierBF/Appendix.lean` | Appendix B, Proposition C.1, and Corollaries C.2 and C.3 |
| `OllivierBF.lean` | Imports all of the above |

## Citing

If you use this formalization, please cite the paper:

```bibtex
@misc{micaletto_nigrelli_2026,
  author = {Micaletto, Giorgio and Nigrelli, Tebe},
  title  = {What Balanced {Forman} Curvature Certifies About {Ollivier--Ricci} Curvature},
  year   = {2026}
}
```
