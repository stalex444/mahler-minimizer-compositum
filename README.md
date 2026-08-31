# The plastic number as a spectral threshold

Kernel-checked spectral results for the Bedford–Kim family
`χ_n(x) = x^(n+1)·(x³ − x − 1) + (x³ + x² − 1)` — the characteristic
polynomials of the linear-fractional-recurrence rational surface
automorphisms, built from the plastic polynomial and its monic
reciprocal. Seven compared theorems, in Lean 4 + Mathlib:

- for n ≥ 7 the family has a canonical root in `[117/100, ρ)` — the
  largest root below ρ — the sequence is strictly increasing, and it
  tends to ρ, the real root of `x³ = x + 1`: the plastic number,
  smallest Pisot number, and the threshold constant of the
  Blanc–Cantat classification of birational surface dynamical degrees
  (`plastic_salem_family`);
- every `χ_n` is strictly positive on `[ρ, ∞)`
  (`family_pos_of_rho_le`);
- the exact factorization `χ₇ = (x − 1) · L`, over any commutative
  ring, with `L` Lehmer's degree-10 polynomial — Lehmer's number,
  whose logarithm is the proven minimum positive entropy of a surface
  automorphism (McMullen), is the n = 7 member of the plastic family
  (`lehmer_first_rung`), and `L` has a root in `[117/100, ρ)`
  (`lehmer_root_below_plastic`);
- an exclusion witness: a nonreal root `z` of `x⁴ = x + 1` with
  `1 < ‖ρ·z‖ < ρ·Q` (`ruler_second_conjugate`), together with the
  identification of the twelve embedding products as exactly the
  conjugates of `ρ·Q` — both directions
  (`ruler_conjugates_eq_embedding_products`) and their count
  (`ruler_conjugates_card`) — so `ρ·Q` has a second conjugate strictly
  outside the unit circle and is neither a Pisot nor a Salem number,
  hence, by the cited classification, not the dynamical degree of any
  birational surface transformation.

Stated honestly: whether ρ itself is **attained** as a dynamical
degree is open in the literature — nothing here claims it — and the
interval `(1, 117/100)` is not swept here (Bedford–Kim's Salem
factorization places no roots there; cited, not formalized). Hypotheses are inline — ρ and Q enter only through their defining
equations, plus the root-selection inequality `1 < Q` on the exclusion
witness, which the quartic's negative real root genuinely fails — and
the compared statements use only core Mathlib vocabulary
(`Filter.Tendsto`, `nhds`, the complex norm) with no custom
definitions. Axioms on the compared theorems: at most `propext`,
`Classical.choice`, `Quot.sound` (the factorization needs only
`propext` and `Quot.sound`).

`Challenge.lean` states the seven results with placeholder proofs;
`Solution.lean` proves them all by transfer from the three proof
modules (`PdtIrreducible`, `PdtSalemFamily`, `PdtRulerMinpoly`); `comparator.json` is the machine
comparison surface; `formalization.yaml` carries sources,
classification, and disclosure.

Build:

```
lake exe cache get
lake build
```

(pinned toolchain and Mathlib; a green build is the kernel
verification).

This repository is the complete, self-contained proof development for
this entry — nothing is imported from any parent project. It belongs
to the larger kernel-verified project
[stalex444/pdt-lean](https://github.com/stalex444/pdt-lean)
(pinned reference revision
[`d66ffbe`](https://github.com/stalex444/pdt-lean/tree/d66ffbe813e48636aa636ffcd80070b81cbf10da);
Zenodo concept DOI
[10.5281/zenodo.21210683](https://doi.org/10.5281/zenodo.21210683)).
