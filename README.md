# BF-OR-Lean
A Lean 4 formalization of the main results of

> Giorgio Micaletto and Tebe Nigrelli. *What Balanced Forman Curvature Certifies About Ollivier–Ricci Curvature.* 2026.

For every edge of a finite simple graph, the paper shows that the Balanced Forman (BF) curvature of the edge and the degrees of its two endpoints certify a two-sided interval for its lazy Ollivier–Ricci (OR) curvature, without solving an optimal transport problem. This repository proves that interval in Lean, together with the transport bounds it is built from, its sharpened form, the comparison with the bound of Bhattacharya and Mukherjee, and the reverse direction (what an OR value certifies about BF).

- **Builds** with Lean `v4.36.0-rc1` and Mathlib commit [`cf5dd31`](https://github.com/leanprover-community/mathlib4/commit/cf5dd317652efe9d9d17252014a4cd442bf86469), both pinned in this repository.
- **Contains no `sorry`** and **declares no axioms**. Every file uses the Lean module system (`module`, `public import`, `@[expose] public section`).
- **One published result**, Lemma 3.3 of the paper (Bourne et al.), is not re-proved. It enters as the explicit hypothesis `BourneFact` of Proposition 4.1 and Corollary 4.2 only ([below](#cited-results)). Every other statement of `OllivierBF/Paper.lean`, including the BF interval and the 2-hop interval, is proved from the definitions; König's theorem for the cross-edge graph is derived from Hall's theorem in Mathlib (`OllivierBF/Cover.lean`).

The experiments of the paper are in a separate repository, [Curvature-Transfer-Code](https://github.com/GiorgioMB/Curvature-Transfer-Code).

## Building

Install Lean through [elan](https://github.com/leanprover/elan), then run from the repository root:

```bash
lake exe cache get   # download prebuilt Mathlib
lake build
```

`lean-toolchain` pins the Lean version and `lake-manifest.json` pins Mathlib, so `lake build` checks exactly the code described here. Running `lake update` moves to a newer Mathlib, which may need small fixes.

To see what a theorem rests on, add to any file that imports `OllivierBF`:

```lean
#print axioms OllivierBF.bf_interval_paper
#print axioms OllivierBF.two_hop_interval_paper
```

The output should list only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The cited results do not appear there because they are hypotheses, not axioms.

## The main theorem

The BF interval of the paper (Corollary 5.8), for every edge, with the endpoints labelled so that `ρ G i ≤ ρ G j`:

```lean
theorem bf_interval_paper (hd : GraphMetric G d) (hij : G.Adj i j) (hle : ρ G i ≤ ρ G j) :
    phiInt (ρ G i) (ρ G j) (cBF G i j) ≤ cOR G d i j ∧ cOR G d i j ≤ psiInt G i j (cBF G i j)
```

Here `phiInt` is the lower end `φ^ℤ` of Corollary 5.8, which refines the lower modulus `phiAff a b ζ = L0 a b + kappa1 a b * max (ζ - bS a b) 0` of Theorem 5.4 (`phiInt_ge_phiAff`) through the integrality of the triangle count, and `psiInt` is the upper modulus of Theorem 5.7: the maximum of the two-piece envelope `psiTwo` over the integer triangle counts `0, 1, …, ⌊△_max⌋`. Both depend only on the BF value and the two degrees.

The statements in the form of the paper are collected in `OllivierBF/Paper.lean` and `OllivierBF/Cover.lean`, which derive them from the building blocks in the other files.

## What is proved

Numbering follows the current version of the manuscript (its Appendix E has the same table). The last column lists the published results that each proof takes as hypotheses.

| Paper | Lean | File | Cited results used |
|---|---|---|---|
| Lemma 3.6 (4-cycle term and matching number) | `C4_le_two_matchStat`; `exists_cover_le_matchNum` (König's theorem) | `Cover` | none |
| Proposition 4.1 (idleness transfer by mixing) | `mixing_transfer_paper`, `cLLY_le_q_paper` | `Paper` | `BourneFact` |
| Corollary 4.2 (triangle-free version) | `mixing_tf_paper`; `lamTF_closed` for the closed form | `Paper` | `BourneFact` (`mixing_tf_paper` only) |
| Theorem 4.3 (quadrangle-augmented Jost–Liu bound) | `jl_aug` | `Bounds` | none |
| Remark 4.4 and Appendix B (comparison with Bhattacharya–Mukherjee) | `LBM_le_Lsq`, `LBM_eq_Lsq_iff` | `Appendix` | none |
| Remark 4.5 (identity for the matching term) | `pos_part_sub_pos_part` | `Algebra` | none |
| Lemma 4.6 (one-sided residuals) | `lazy_min`, `lazy_resid_i`, `lazy_resid_j` | `Curvature` | none |
| Theorem 4.7 (lazy quadrangle bound) | `lazy_quadrangle`; `Llazy_deficit` for the deficit form | `Bounds`, `Paper` | none |
| Proposition 4.10 (lazy transport envelope) | `lazy_envelope_paper`; `lazy_envelope_cover` for every vertex cover; `mUU_le` for the bounds on `m^UU` | `Paper`, `Cover` | none |
| Proposition 5.1 (i) (BF as an unclipped Jost–Liu bound) | `bf_is_third_piece` | `Bounds` | none |
| Remark 5.3 (the identities and inequalities it rests on) | `Llazy_sub_lamMix`, `lamMix_piece3_le`, `lamOld_piece3_le`, `lamTF_piece3_le` | `Algebra` | none |
| Theorem 5.4 (lower modulus) | `bf_lower_paper`; `phiAff_mono`; `phiAff_virtual` for the virtual edge | `Paper` | none |
| Proposition 5.5 (range of BF and comparison with the lifts) | `cBF_le_range`; `phiAff_ge_lamTF` | `Paper` | none |
| Lemma 5.6 (budget region) | `budget_region` | `Paper` | none |
| Theorem 5.7 (upper modulus) | `bf_upper_paper`; `psiInt_mono`; `psiTwo_deficit` for the deficit form | `Paper` | none |
| Corollary 5.8 (BF interval) | `bf_interval_paper`; `phiInt_ge_phiAff`; `phiInt_le_Llazy` | `Paper` | none |
| Proposition 5.9 (2-hop interval) | `two_hop_interval_paper` | `Paper` | none |
| Corollary C.1 (lower bound on BF) | `or_to_bf_lower_paper`; `coverage_bound`, `coverage_bound_eq` for (C.1) | `Paper` | none |
| Corollary C.2 (upper bound on BF) | `or_to_bf_upper_paper` | `Paper` | none |

The lower ends come from explicit couplings (`W1_le_cost`) and the upper ends of Proposition 4.10 from explicit 1-Lipschitz potentials (`cost_ge_potential`, `coverPot`): for every vertex cover `K` of the cross-edge graph, `lazy_envelope_cover` bounds `𝔠_OR` by the potential that is `2` on `{i} ∪ (U_i \ K)`, `0` on `U_j \ K`, and `1` elsewhere. The covers `ξ_j` and a König cover with `𝔪(i, j)` vertices give `m^UU = min{𝔪 w_i, |ξ_j| w_j}`.

Several building blocks in the other files state longer or weaker forms from an earlier version of the paper, and `Paper.lean` derives the current statements from them. `phiElem` has a second slope on thresholds that no edge attains, `psiHat` and `Theta` keep terms that are never active, and `psiUp` maximizes over the whole interval of triangle counts rather than over integers. The theorems stated through them (`bf_lower`, `bf_upper`, `bf_interval`, `sharpened_interval`, `lazy_envelope`, `coverage_envelope`, `or_to_bf_lower_env`, `or_to_bf_lower`, `or_to_bf_old`, and `or_to_bf_mixing`) are superseded by those of `Paper.lean`, and only they use the structure `CitedFacts` below.

## Cited results

| Hypothesis | Statement in Lean | Source | Used by |
|---|---|---|---|
| `BourneFact` | `𝔠_{OR-p} = (1 − p) 𝔠_LLY` at `p = 1/(ρ_max + 1)` | [Bourne, Cushing, Liu, Münch, and Peyerimhoff (2018)](https://arxiv.org/abs/1704.04398), Theorems 1.1 and 5.5 | Proposition 4.1 and Corollary 4.2 |

A theorem that needs it takes `hB : BourneFact G d` as an argument, so its statement is an implication from the cited result. Lean checks the implication; the agreement with the published source is checked by hand.

The superseded theorems listed above take instead `cited : CitedFacts G d`, which bundles `BourneFact` (field `bourne`) with three results that the current proofs no longer need: Topping et al. (2022), Theorem 2 (`topping`, `𝔠_BF ≤ 𝔠_LLY`) and Lemma 11 (`topping11`, now the theorem `C4_le_two_matchStat`), and Villani (2003), Corollary 1.16 (`saturate`, replaced by the potentials of `Cover.lean`).

## Modelling choices

- **Graphs.** `G : SimpleGraph V` on a finite type `V`. Connectedness is needed only to show that the shortest-path distance satisfies `GraphMetric`.
- **Distance.** The theorems hold for any `d : V → V → ℝ` with `GraphMetric G d`, which records the facts the proofs use: `d` vanishes on the diagonal, equals 1 on edges, is at least 1 between distinct vertices and at least 2 between distinct non-adjacent ones, is symmetric, and satisfies the triangle inequality. `graphMetric_dist` shows that the shortest-path distance of a connected graph qualifies.
- **Transport.** `W1 d μ ν` is the infimum of the cost over couplings. Upper bounds come from explicit couplings (`W1_le_cost`) and lower bounds from bounds valid for every coupling (`le_W1`); the existence of optimal couplings is never used.
- **Curvatures** (`Curvature.lean`). `mLazy u` is the uniform measure on the closed neighbourhood of `u` and `mp p u` the measure with idleness `p`. `cOR`, `cOR0`, and `cORp` are the lazy, non-lazy, and idleness-`p` OR curvatures, `cLLY` is the left limit at `p = 1` of `cORp p / (1 − p)`, and `cBF` is Balanced Forman curvature as in Definition 3.2 of the paper. `matchNum` is the matching number of the cross-edge graph.
- **Endpoint labels.** All statements of `Paper.lean` label the endpoints so that `ρ G i ≤ ρ G j`, as the paper does. The building blocks of the mixing transfer in `Bounds.lean` (`cLLY_le_q`, `mixing_transfer`, `mixing_dominates`, `mixing_triangle_free`) use `ρ G j ≤ ρ G i`; `Paper.lean` restates them through the symmetry lemmas `cOR_comm` and `cLLY_comm`.

## Not formalized

- The exactness statements of Theorems 4.3, 4.7, and 5.4 and Corollary 5.8.
- Regularity and computation: the continuity, convexity, and piecewise linearity of the lower modulus, the location of the maximizers of `Ψ̂` in Theorem 5.7, and the `O(1)` evaluation in Corollary 5.8.
- Proposition 4.8 (the envelope for arbitrary idleness) and the comparison of `U^lazy` with `U^env` in Proposition 4.10.
- Parts (ii) and (iii) of Proposition 5.1.
- The closed form of the Bhattacharya–Mukherjee matching number in Remark 4.4. `LBM` is defined through it rather than from their definition.
- The comparison that follows Corollary C.2.
- The correctness of Algorithm 1 (certify-then-solve).

## Layout

| File | Contents |
|---|---|
| `OllivierBF/Transport.lean` | Couplings, `W1`, mixtures of couplings, and the overlap lower bound |
| `OllivierBF/Graph.lean` | `GraphMetric`, neighbourhood statistics, cross matchings, and the box-count bound (3.2) |
| `OllivierBF/Curvature.lean` | Measures, curvatures, `BourneFact`, `CitedFacts`, and Lemma 4.6 |
| `OllivierBF/Algebra.lean` | Real-number identities behind Theorem 5.4, Proposition 5.5, and Remark 5.3 (no graphs) |
| `OllivierBF/Bounds.lean` | Theorems 4.3 and 4.7, Proposition 5.1 (i), and building blocks for Propositions 4.1 and 4.10 and Corollary 4.2 |
| `OllivierBF/Interval.lean` | Building blocks for Theorems 5.4 and 5.7 (`phiElem`, `psiHat`, `psiUp`, and the cross-edge caps) |
| `OllivierBF/Appendix.lean` | Appendix B, and building blocks for Appendix C |
| `OllivierBF/Cover.lean` | König's theorem for the cross-edge graph (from Hall's theorem), Lemma 3.6, weak duality, and the vertex-cover potentials of Proposition 4.10 |
| `OllivierBF/Paper.lean` | Propositions 4.1, 4.10, 5.5, and 5.9, Corollaries 4.2 and 5.8, Theorems 5.4 and 5.7, Lemma 5.6, and Appendix C in the form of the paper |
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
