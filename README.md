# The compositum of the two Mahler minimizers, with the Bedford–Kim plastic family and its `E_m` Coxeter bridge

**Version 2** of the registered entry PALOMAR-2026-09-01-000005 (version 1:
seventeen compared theorems, Lean 4.31.0). Version 2 re-establishes the
seventeen statements, unchanged, on Lean 4.35.0-rc2 / Mathlib
`065356127b1d` and adds five: the **Coxeter bridge**, which identifies the
spectral half of the entry with the Coxeter-element spectra of the `E_m`
star trees. Twenty-two compared theorems.

Kernel-checked certificates, in Lean 4 + Mathlib, for the
multiplicative compositum of the two registered Mahler minimizers —
ρ, the real root of `x³ = x + 1` (the plastic number: Smyth's
nonreciprocal minimum, Siegel's smallest Pisot number) and `Q`, the
real root `> 1` of `x⁴ = x + 1` (the attainer of the degree-4 minimum in
the minimal-measure tables) — together with the Bedford–Kim spectral
family whose limit ρ is.

That `x^d − x − 1` attains the minimal Mahler measure above one among monic
irreducible integer polynomials at each degree `d ∈ {2, 3, 4}` is
kernel-certified in the **registered sibling entry** PALOMAR-2026-08-31-000004
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

## New in version 2: the Coxeter bridge (statements 18–22)

Let `E_m = T(2,3,m−3)` be the star tree with arms of 1, 2 and `m−4` edges
(so `E_6, E_7, E_8` are the finite Dynkin diagrams, `E_9` affine, `E_10`
and beyond hyperbolic), `A` its generalized Cartan matrix, and
`c = s_0 s_1 ⋯ s_{m−1}` the Coxeter element, each simple reflection
written as the matrix `s_i = 1 − e_i e_iᵀ A` of the geometric
representation in the basis of simple roots. Kernel-checked:

- **(18) `coxeter_E_bridge`** — for every `m ≥ 4`,
  `(X − 1)·charpoly(c) = X^(m−2)·(X³ − X − 1) + (X³ + X² − 1)`,
  the classical `E_m` Coxeter-polynomial identity, recorded in
  Gross–Hironaka–McMullen (J. Number Theory 129 (2009), §1) and proved there
  as Cor. 4.3 for `n ≥ 4`, citing McKee–Rowlinson–Smyth 1999, Lemma 5. The
  right-hand side is `χ_{m−3}`, the
  Bedford–Kim member of statements (1)–(4): **the spectral half of this
  entry is the `E_m` Coxeter spectrum.** Proved by a determinant recurrence
  along the long arm together with Howlett's identity `U·c = U − A`
  (`U` the unipotent upper part of `A`; Bull. LMS 14 (1982)).
- **(19) `coxeter_E10_lehmer`** — with the `E_10` Cartan matrix written out
  as a `10 × 10` literal, the Coxeter polynomial of `E_10` is Lehmer's
  degree-10 polynomial (classical: McMullen, Publ. Math. IHES 95 (2002)).
- **(20) `coxeter_E_plastic`** — for every `m ≥ 10` the Coxeter polynomial
  of `E_m` has a root `λ_m ∈ [117/100, ρ)` with no real root above it; the
  `λ_m` increase strictly and tend to ρ. (`λ_m` is the canonical root
  `lam (m − 3)` of statement (1).)
- **(21) `coxeter_E_spectrum`** — for every `m ≥ 10` the complexified
  Coxeter element has an eigenvalue `λ ∈ (1, ρ)`, and every complex
  eigenvalue is unimodular, `λ`, or `λ⁻¹`.
- **(22) `coxeter_E_salem`** — that `λ` dominates the modulus of every
  eigenvalue and is a **Salem number** for every `m ≥ 10`, with the Salem
  predicate written out exactly as in the registered entry
  PALOMAR-2026-09-02-000003 (for hyperbolic crystallographic Coxeter
  systems, every element of spectral radius above 1 has a Salem spectral
  radius: McMullen 2002, Prop. 7.1; `E_m` is hyperbolic and crystallographic
  for `m ≥ 10`).

Two disclosures of version 1 are discharged for `n ≥ 7` (`m = n + 3`). The
Salem property of the Bedford–Kim roots, cited in version 1, is kernel-held:
the module theorem `PdtCoxeterSpectral.coxeter_E_salem` proves it at the
canonical root that witnesses (1), and on the compared surface it follows
from (18), (22), (1) and (2) — the eigenvalue of (22) is the largest real
root of `χ_{m−3}`, which is `lam n`. The interval `(1, 117/100)`, "not
swept" in version 1, is swept: by (18) every root of `χ_n` other than 1 is
an eigenvalue of `c`; by (21) the only eigenvalues off the unit circle are
`λ` and `λ⁻¹`; by (20) `λ = λ_m ≥ 117/100`. The mathematics of (18)–(22) is
classical; the contribution claimed is the kernel-checked bridge from the
Bedford–Kim family of (1)–(4) to the Coxeter elements of the `E_m` Weyl
groups, for every `m ≥ 4` (bridge) and every `m ≥ 10` (spectrum, Salem) at
once, with the Salem certificate carried by the registered Salem entry's own
modules.

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
`v(n+4) = v(n+1) + v(n)`): any product of solutions in a ℚ-algebra
satisfies the order-12 recurrence (`product_recurrence_charpoly`), and
over ℚ the annihilator ideal of the product power sequence
`n ↦ (ρQ)ⁿ` is EXACTLY the principal ideal of the degree-12 polynomial
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
(`lehmer_root_below_plastic`). Version 2 adds that this family IS the
`E_m` Coxeter spectrum (statements 18–22 above).

Trailing corollary: the exclusion witness `ruler_second_conjugate`
plus the conjugate identification
(`ruler_conjugates_eq_embedding_products`, `ruler_conjugates_card`)
and the census give `ρQ` five conjugates strictly outside the unit
circle — neither Pisot nor Salem, hence by the **cited** Blanc–Cantat
classification (JAMS 29 (2016)) not the dynamical degree of any
birational surface transformation. The membership question is studied
by Blanc–Cantat and Kim (arXiv:2312.17729, preprint).

Stated honestly: whether ρ itself is **attained** as a dynamical
degree is open in the literature — nothing here claims it. The
dynamical realization of the roots as automorphism entropies remains
cited, not formalized. Hypotheses are inline — ρ, `Q`, `ψ` enter only
through their defining equations plus root-selection inequalities, and
the `E_m` Cartan matrices only through their entries — and the compared
statements use only core Mathlib vocabulary with no custom definitions.
Axioms on every compared theorem: at most `propext`, `Classical.choice`,
`Quot.sound`.

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
elimination. Version 2 adds a fourth: the Coxeter-group and Salem-number
audience (McMullen; Gross–Hironaka–McMullen; Hironaka's Lehmer program),
for which the bridge gives the `E_m` Coxeter spectra, their Salem radii
and their limit ρ as one kernel-checked family. And for researchers
formalizing algebraic number theory, it exercises Mathlib's
Mahler-measure, linear-disjointness, `Matrix.charpoly` and `spectrum`
APIs on concrete instances. Like the golden ratio, ρ·Q is an algebraic
unit of norm −1; the compared cofactor identity is that norm
computation, certified.

## Layout and build

`Challenge.lean` states the twenty-two results with placeholder
proofs and imports Mathlib only; `Solution.lean` proves them all by
transfer from the proof modules; `comparator.json` is the machine
comparison surface; `formalization.yaml` carries sources,
classification, and disclosure; `BUILD.txt` is the build and axiom
record.

Proof modules. Version 1 (identical to the registered revision
`d78ce16` apart from the three-line module-system header that the
registry now requires at the top of every Lean file, and one two-line
proof repair in `PdtIrreducible` forced by the toolchain, statement
unchanged): `PdtIrreducible`,
`PdtSalemFamily`, `PdtRulerMinpoly`, `PdtRulerCensus`,
`PdtRulerMeasure`, `PdtRulerRecurrence`. The bridge: `PdtStarDet` (the
determinant recurrence), `PdtCoxElt` (Coxeter elements of a generalized
Cartan matrix; Howlett's identity), `PdtCoxeterBridge` (statements
18–20), `PdtCoxeterSpectral` (statements 21–22). The Salem certificate:
`PdtSalemCircle`, `PdtSalemArith`, `PdtSalemMinus`, `PdtPisotLadder`,
`PdtSalemEndgame`, carried unchanged, apart from the module-system header, from the registered Salem entry
PALOMAR-2026-09-02-000003 ([stalex444/salem-theorem](https://github.com/stalex444/salem-theorem));
`PdtPisotBoundary`, identical apart from the module-system header to the module of the same name in
the registered entries PALOMAR-2026-08-31-000004 (mahler-measure-minima)
and PALOMAR-2026-09-04-000004 (chiral-padovan-histories, registered
revision 14711e6); and `PdtSalemPlasticPattern`, a trimmed copy (the
plastic-pattern lines only, verbatim, plus `rho_real_root_unique` copied
verbatim from `PdtMahlerWindow` of stalex444/pdt-lean) of a module of the
author's unpublished development; the source module is not public, so the
trim is disclosed rather than externally checkable — every line of it is
kernel-checked in this build.

```
lake exe cache get
lake build
```

(pinned toolchain `leanprover/lean4:v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; a green build is the kernel
verification).

This repository is the complete, self-contained proof development for
this entry — nothing is imported from any parent project. It belongs
to the larger kernel-verified project
[stalex444/pdt-lean](https://github.com/stalex444/pdt-lean)
(pinned reference revision
[`d66ffbe`](https://github.com/stalex444/pdt-lean/tree/d66ffbe813e48636aa636ffcd80070b81cbf10da),
from which `PdtIrreducible`, `PdtSalemFamily` and `PdtRulerMinpoly`
descend; Zenodo concept DOI
[10.5281/zenodo.21210683](https://doi.org/10.5281/zenodo.21210683)),
the formal spine of Pisot Dimensional Theory, in which ρ and `Q` are the
two generators; that is why the author looked at this family. Nothing
in any compared statement depends on it.
