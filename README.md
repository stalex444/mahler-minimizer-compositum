# The compositum of the two Mahler minimizers

Kernel-checked certificates, in Lean 4 + Mathlib, for the
multiplicative compositum of the two registered Mahler minimizers —
ρ, the real root of `x³ = x + 1` (the plastic number: Smyth's
nonreciprocal minimum, Siegel's smallest Pisot number) and `Q`, the
real root `> 1` of `x⁴ = x + 1` (the attainer of the degree-4 minimum in the minimal-measure tables) — together with the Bedford–Kim spectral
family whose limit ρ is. Seventeen compared theorems.

That `x^d − x − 1` attains the minimal Mahler measure above one among monic
irreducible integer polynomials at each degree `d ∈ {2, 3, 4}` is kernel-certified in the **registered
sibling entry** PALOMAR-2026-08-31-000004
([stalex444/mahler-measure-minima](https://github.com/stalex444/mahler-measure-minima/tree/ca3df22)):
the selection of the pair `(ρ, Q)` is the literature's and the
registry's, not this entry's. The registered-entry thread is a
mechanical identity, not prose:

```
M(rulerPoly) = (ρQ)² · M(X⁴ − X − 1),   M(X⁴ − X − 1) = ψ
```

with `ψ` the real root `> 1` of `ψ⁴ = ψ³ + 1` — the degree-4 quantity
pinned in the registered sibling, consumed here as the compared
identity `ruler_mahler_eq_quartic_measure`.

## The measure, the census, the house

For the degree-12 minimal polynomial of `ρQ` (written out in full in
every compared statement — "ruler" in statement names is the source
project's term for the product `ρQ`):

- the exact Mahler measure `M = ρ²·Q²·ψ` (`ruler_mahler_measure`; `ψ`
  is not a new constant — it is `−1/r₂` for the same quartic's
  negative real root, disclosed as forced);
- the registry bridge above (`ruler_mahler_eq_quartic_measure`);
- the complete unit-circle census: EXACTLY 5 conjugates strictly
  outside, EXACTLY 7 strictly inside, NONE on the circle
  (`ruler_conjugate_census`) — so `ρQ` is neither a Pisot nor a Salem
  number;
- the house: every conjugate other than `ρQ` has modulus `< ρQ`
  (`ruler_house`);
- the unit certificate: `ρQ` times an explicit degree-11 cofactor
  equals 1 over any commutative ring (`ruler_unit`);
- nonreciprocity: the coefficient list is neither its reversal nor
  the reversal's negation (`rulerPoly_nonreciprocal`), placing the
  polynomial in the regime of Smyth's theorem.

No novelty is claimed for the measure identity — the entry is not
aware of it in the literature, and the claimed contribution is the
kernel certificate.

## The degree problem

The product-degree program (Drungilas–Dubickas–Smyth 2012;
Drungilas–Dubickas–Luca 2013; Drungilas–Dubickas 2016;
Drungilas–Maciulevičius 2019; Virbalas 2023, 2025). The feasibility
of `(3, 4, 12)` is known — the `b ≤ 7` classification is complete
(Dubickas–Maciulevičius 2024) — and the contribution here is the
**certified witness at the canonical pair**: degree multiplicativity
`12 = 3·4` (`ruler_degree_multiplicative`; no general theorem forces
it for products, unlike the sum case — Isaacs 1970), the compositum
`ℚ(ρ) ⊔ ℚ(Q) = ℚ(ρQ)` of degree 12 with the two simple extensions
linearly disjoint (`ruler_linearDisjoint`; the disjointness half is
near-automatic from coprime degrees — disclosed), and the unit normal
form `α·β·γ = 1` at `(3, 4, 12)` (`ruler_unit`).

## The product recurrence

The same polynomial is the characteristic polynomial of the Hadamard
(termwise) product of the two fundamental recurrences
(`u(n+3) = u(n+1) + u(n)`, the Padovan/Perrin recurrence, and
`v(n+4) = v(n+1) + v(n)`): any product of solutions in a ℚ-algebra satisfies the order-12 recurrence (`product_recurrence_charpoly`), and over ℚ the
annihilator ideal of the product power sequence `n ↦ (ρQ)ⁿ` is
EXACTLY the principal ideal of the degree-12 polynomial
(`product_annihilator_iff`) — the classical order `≤ 3·4` bound
(Cerlienco–Mignotte–Piras 1987; Everest–van der Poorten–Shparlinski–
Ward 2003) is an equality, forced by the polynomial's kernel-held
irreducibility. A simple recurrence with a dominant real root is the
operative hypothesis class of the LRS decision-problems literature
(Ouaknine–Worrell 2014); the census and house certify both properties
for this instance.

## The spectral half, and the exclusion corollary

Bedford–Kim (J. Geom. Anal. 19 (2009)) construct rational surface
automorphisms whose characteristic polynomials
`χ_n(x) = x^(n+1)·(x³ − x − 1) + (x³ + x² − 1)` have spectral radii
increasing to ρ. Kernel-checked here: the canonical largest roots
below ρ, strictly increasing, tending to ρ
(`plastic_salem_family`), positivity on `[ρ, ∞)`
(`family_pos_of_rho_le`), the exact factorization `χ₇ = (x − 1)·L`
with `L` Lehmer's degree-10 polynomial (`lehmer_first_rung`) — so
Lehmer's number, whose logarithm is the proven minimum positive
entropy of a surface automorphism (McMullen 2007), is the n = 7
member of the plastic family — and a root of `L` in `[117/100, ρ)`
(`lehmer_root_below_plastic`).

Trailing corollary: the exclusion witness `ruler_second_conjugate`
plus the conjugate identification
(`ruler_conjugates_eq_embedding_products`, `ruler_conjugates_card`)
and the census give `ρQ` five conjugates strictly outside the unit
circle — neither Pisot nor Salem, hence by the **cited** Blanc–Cantat
classification (JAMS 29 (2016)) not the dynamical degree of any
birational surface transformation. The membership question is studied
by Blanc–Cantat and Kim (arXiv:2312.17729, preprint).

Stated honestly: whether ρ itself is **attained** as a dynamical
degree is open in the literature — nothing here claims it — and the
interval `(1, 117/100)` is not swept here (Bedford–Kim's Salem
factorization places no roots there; cited, not formalized).
Hypotheses are inline — ρ, `Q`, `ψ` enter only through their defining
equations plus root-selection inequalities — and the compared
statements use only core Mathlib vocabulary with no custom
definitions. Axioms on the compared theorems: at most `propext`,
`Classical.choice`, `Quot.sound` (the factorization and the unit
certificate need only `propext` and `Quot.sound`).

## Research audiences

The results address three research audiences. In the degree problem
for products and composita of algebraic numbers (Drungilas, Dubickas,
Smyth, and successors), the entry supplies a kernel-certified witness
of the product-feasible triple (3, 4, 12) at a canonically
distinguished pair, in the field's own αβγ = 1 normal form. In the
Mahler-measure tradition (Lehmer, Smyth, Mossinghoff), it evaluates
the measure of the composed product of the two degree-minimal
polynomials in closed form, in the second-smallest Pisot number. In
composed products of polynomials (Brawley–Carlitz and successors), it
is a certified rational instance where the finite-field coprimality
criterion is unavailable and irreducibility is instead proved by
elimination. And for researchers formalizing algebraic number theory,
it exercises Mathlib's Mahler-measure and linear-disjointness APIs on
a concrete irreducible degree-12 instance. Like the golden ratio, ρ·Q
is an algebraic unit of norm −1; the compared cofactor identity is
that norm computation, certified.

## Layout and build

`Challenge.lean` states the seventeen results with placeholder
proofs; `Solution.lean` proves them all by transfer from the six
proof modules (`PdtIrreducible`, `PdtSalemFamily`, `PdtRulerMinpoly`,
`PdtRulerCensus`, `PdtRulerMeasure`, `PdtRulerRecurrence`);
`comparator.json` is the machine comparison surface;
`formalization.yaml` carries sources, classification, and disclosure.

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
`PdtIrreducible`, `PdtSalemFamily`, and `PdtRulerMinpoly` descend
from material in the parent development at that revision;
`PdtRulerCensus`, `PdtRulerMeasure`, and `PdtRulerRecurrence` (with
the extensions of `PdtRulerMinpoly`: unit, nonreciprocity, degree
multiplicativity, compositum sup form, linear disjointness) are
native to this repository.
