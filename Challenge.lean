import Mathlib

/-!
# The compositum of the two Mahler minimizers, with the Bedford–Kim plastic family

Two polynomials anchor the small-Mahler-measure literature. `x³ − x − 1` has
real root ρ, the plastic number: Smyth proved that its measure is the
minimum over all nonreciprocal algebraic integers (Bull. LMS 3 (1971)),
and Siegel proved ρ is the smallest Pisot number (Duke Math. J. 11
(1944)). `x⁴ − x − 1`, with real root `Q > 1`, is the attainer of the degree-4 minimum in the minimal-measure tables (Mossinghoff, Math. Comp. 67 (1998);
Mossinghoff–Rhin–Wu, Experiment. Math. 17 (2008)). That `x^d − x − 1`
attains the minimal Mahler measure above one among monic
irreducible integer polynomials at each degree
`d ∈ {2, 3, 4}` is kernel-certified in the registered entry
PALOMAR-2026-08-31-000004 (stalex444/mahler-measure-minima): the
selection of the pair `(ρ, Q)` is the literature's and the registry's,
not this entry's. The statements below certify the multiplicative
compositum of that pair — the degree-12 minimal polynomial of `ρQ`
("ruler", in statement names, is the source project's term for the
product `ρQ`; nothing in any statement depends on it), written out in
full wherever it appears:
`X¹² − 3X⁹ − 2X⁸ + 2X⁶ − X⁵ − 3X⁴ − X³ + X − 1`.

## The spectral half: the Bedford–Kim family and Lehmer's polynomial

Bedford–Kim (J. Geom. Anal. 19 (2009); arXiv:math/0611297) construct
rational surface automorphisms from linear fractional recurrences; the
characteristic polynomial of the induced action on cohomology is
`χ_n(x) = x^(n+1)·(x³ − x − 1) + (x³ + x² − 1)` (their eq. 0.3) — the
plastic polynomial paired with its (monic) reciprocal — and they prove
the spectral radii λ_n increase to ρ, the threshold constant of the classification of Blanc–Cantat Thm 1.2 (after Diller–Favre) of birational surface dynamical degrees
(JAMS 29 (2016)). Statements (1)–(4) are the SPECTRAL half of that
picture, kernel-checked: canonical largest roots below ρ (largest in
`[117/100, ρ)`, with `χ_n > 0` on `[ρ, ∞)`; the interval
`(1, 117/100)` is not swept here — Bedford–Kim's Salem factorization
places no roots there; cited), strict increase, convergence to ρ, and
the exact factorization `χ₇(x) = (x − 1)·L(x)` with `L` Lehmer's
degree-10 polynomial (Ann. of Math. 34 (1933)) — so Lehmer's number,
whose logarithm is the proven minimum positive entropy of a surface
automorphism (McMullen, Publ. Math. IHES 105 (2007), Thm 1.2), is the
first member (`n = 7`) of the plastic family. Whether ρ itself is
ATTAINED as a dynamical degree is open in the literature; nothing here
claims it.

## The measure, the census, the house, the unit, nonreciprocity

The compositum half's core: the exact Mahler measure
`M = ρ²·Q²·ψ` where `ψ` is the real root `> 1` of `ψ⁴ = ψ³ + 1`
(`ruler_mahler_measure` — `ψ` is not a new constant: it is `−1/r₂` for
the same quartic's negative real root `r₂`, the quartic recycled); the
registry bridge `M(rulerPoly) = (ρQ)² · M(X⁴ − X − 1)` with
`M(X⁴ − X − 1) = ψ` (`ruler_mahler_eq_quartic_measure` — re-proving that quantity in-repo; its value matches the one pinned in the registered entry above); the complete
unit-circle census — EXACTLY 5 conjugates strictly outside, EXACTLY 7
strictly inside, NONE on the circle (`ruler_conjugate_census`); the
house — every conjugate except `ρQ` itself has modulus `< ρQ`
(`ruler_house`); the unit certificate — an explicit degree-11 cofactor
with `ρQ · cofactor = 1` over any commutative ring (`ruler_unit`); and
nonreciprocity — the coefficient list is neither its reversal nor its
negation (`rulerPoly_nonreciprocal`), placing the polynomial in the
nonreciprocal regime governed by Smyth's theorem. No novelty is claimed
for the measure identity; the entry is not aware of it appearing in the
literature, and the contribution claimed is the kernel certificate.

## The degree problem

The product-degree problem — which triples `(a, b, c)` are realized by
`deg α = a`, `deg β = b`, `deg αβ = c` — is an active program
(Drungilas–Dubickas–Smyth, Publ. Mat. 56 (2012); Drungilas–Dubickas–
Luca, Math. Nachr. 286 (2013); Drungilas–Dubickas, Colloq. Math. 143
(2016); Drungilas–Maciulevičius, Lith. Math. J. 59 (2019); Virbalas,
Mathematics 11 (2023) and Lith. Math. J. 65 (2025); the `b ≤ 7`
classification completed by Dubickas–Maciulevičius, Open Math. (2024)).
The feasibility of `(3, 4, 12)` is known — no general theorem forces
`deg(αβ) = ab` for coprime degrees (`ζ₃·∛2` has degree 3), unlike the
sum case (Isaacs, Proc. AMS 25 (1970)) — and the contribution here is
the certified witness at the canonical pair: degree multiplicativity
`12 = 3·4` (`ruler_degree_multiplicative`), and the compositum
`ℚ(ρ) ⊔ ℚ(Q) = ℚ(ρQ)` of degree 12 with the two simple extensions
linearly disjoint (`ruler_linearDisjoint` — the disjointness half is
near-automatic from coprime degrees; disclosed). `ruler_unit` realizes
the triple in the normal form `α·β·γ = 1` of the 2016 paper.

## The product recurrence

The same polynomial is the characteristic polynomial of the Hadamard
(termwise) product of the two fundamental recurrences: for ANY
sequences with `u(n+3) = u(n+1) + u(n)` and `v(n+4) = v(n+1) + v(n)` in a ℚ-algebra, the product `u·v` satisfies the order-12 recurrence
with characteristic polynomial exactly the degree-12 polynomial above
(`product_recurrence_charpoly`; the integer-coefficient form over any
commutative ring is kernel-held as the module lemma `product_recurrence`; the order ≤ 3·4 bound is classical:
Cerlienco–Mignotte–Piras, Enseign. Math. 33 (1987); Everest–van der
Poorten–Shparlinski–Ward, AMS Surveys 104 (2003)). Over ℚ the bound is
an EQUALITY here: the annihilator ideal of the product power sequence
`n ↦ ρⁿQⁿ` is exactly the principal ideal generated by the degree-12
polynomial (`product_annihilator_iff`) — its irreducibility, held in
the proof modules, is what forces minimality. A simple recurrence with
a dominant real root is the operative hypothesis class of the LRS
decision-problems literature (Ouaknine–Worrell, SODA/ICALP 2014); the
census and house above certify both properties for this instance.

## The exclusion corollary

Statement (5) is an exclusion witness: a NONREAL root `z` of
`x⁴ = x + 1` with `1 < ‖ρ·z‖ < ρ·Q`. The products of embeddings are the
conjugates of `ρQ` in the degree-12 compositum — an identification
FORMALIZED as statements (6) and (7), unlike the Blanc–Cantat
classification, which remains cited — so `ρQ` has a second conjugate
strictly outside the unit circle (indeed five, by the census): `ρQ` is
neither a Pisot nor a Salem number, hence by the cited classification
not the dynamical degree of any birational surface transformation. The
membership question — which Salem/Pisot numbers are realized — is
studied by Blanc–Cantat (JAMS 29 (2016)) and Kim (arXiv:2312.17729,
preprint).

Hypotheses are inline — `ρ`, `Q`, `ψ` enter only through their defining
equations plus root-selection inequalities — and the statements use
only core Mathlib vocabulary: `Filter.Tendsto`, `nhds`, the complex
norm, `minpoly`, `Polynomial.rootSet`, `Set.ncard`,
`Polynomial.mahlerMeasure`, `IntermediateField` adjoin/sup,
`Module.finrank`, `Finset.range` sums. No custom definitions.

Sources (full bibliography with DOIs in `formalization.yaml`):
C. J. Smyth, "On the product of the conjugates outside the unit circle
of an algebraic integer", Bull. London Math. Soc. 3 (1971) 169–175.
C. L. Siegel, "Algebraic integers whose conjugates lie in the unit
circle", Duke Math. J. 11 (1944) 597–602. D. H. Lehmer, "Factorization
of certain cyclotomic functions", Ann. of Math. 34 (1933) 461–479.
E. Bedford and K. Kim, "Dynamics of rational surface automorphisms:
linear fractional recurrences", J. Geom. Anal. 19 (2009); arXiv:
math/0611297. J. Blanc and S. Cantat, "Dynamical degrees of birational
transformations of projective surfaces", J. Amer. Math. Soc. 29 (2016)
415–471. C. T. McMullen, "Dynamics on blowups of the projective plane",
Publ. Math. IHES 105 (2007) 49–89.
-/

namespace PlasticThreshold

/-- **Nothing at or above ρ**: every member of the Bedford–Kim family
`χ_n(x) = x^(n+1)·(x³ − x − 1) + (x³ + x² − 1)` is strictly positive on
`[ρ, ∞)`. -/
theorem family_pos_of_rho_le (rho : ℝ) (hrho : rho ^ 3 = rho + 1)
    (n : ℕ) {y : ℝ} (hy : rho ≤ y) :
    0 < y ^ (n + 1) * (y ^ 3 - y - 1) + (y ^ 3 + y ^ 2 - 1) := by
  sorry

/-- **The plastic number is the limit of the Bedford–Kim spectral
family** (the spectral half of Bedford–Kim 2009): for `n ≥ 7` the family
`χ_n(x) = x^(n+1)·(x³ − x − 1) + (x³ + x² − 1)` has a canonical root
`lam n` in `[117/100, ρ)`, the largest root below ρ; the sequence is
strictly increasing; and it tends to ρ, the real root of `x³ = x + 1`
(the plastic number). -/
theorem plastic_salem_family (rho : ℝ) (hrho : rho ^ 3 = rho + 1) :
    ∃ lam : ℕ → ℝ,
      (∀ n, 7 ≤ n →
        (117 / 100 : ℝ) ≤ lam n ∧ lam n < rho ∧
        (lam n) ^ (n + 1) * ((lam n) ^ 3 - lam n - 1) +
          ((lam n) ^ 3 + (lam n) ^ 2 - 1) = 0 ∧
        ∀ y : ℝ, lam n < y → y < rho →
          y ^ (n + 1) * (y ^ 3 - y - 1) + (y ^ 3 + y ^ 2 - 1) ≠ 0) ∧
      (∀ n, 7 ≤ n → lam n < lam (n + 1)) ∧
      Filter.Tendsto lam Filter.atTop (nhds rho) := by
  sorry

/-- **Lehmer is the first rung**: the exact factorization
`χ_7(x) = (x − 1)·L(x)` with `L` Lehmer's polynomial, over any
commutative ring. -/
theorem lehmer_first_rung {R : Type*} [CommRing R] (x : R) :
    x ^ 8 * (x ^ 3 - x - 1) + (x ^ 3 + x ^ 2 - 1) =
    (x - 1) * (x ^ 10 + x ^ 9 - x ^ 7 - x ^ 6 - x ^ 5 - x ^ 4 - x ^ 3 + x + 1) := by
  sorry

/-- **Lehmer's polynomial has a root below the plastic number**, in
`[117/100, ρ)` — the `n = 7` canonical root of the plastic family. -/
theorem lehmer_root_below_plastic (rho : ℝ) (hrho : rho ^ 3 = rho + 1) :
    ∃ x : ℝ, (117 / 100 : ℝ) ≤ x ∧ x < rho ∧
      x ^ 10 + x ^ 9 - x ^ 7 - x ^ 6 - x ^ 5 - x ^ 4 - x ^ 3 + x + 1 = 0 := by
  sorry

/-- **The ruler exclusion witness**: a nonreal root `z` of `x⁴ = x + 1`
with `1 < ‖ρ·z‖ < ρ·Q`. Together with statements (6) and (7) below,
which formalize the identification of the twelve embedding products as
the conjugates of `ρQ`, this is a second conjugate of `ρQ` strictly
outside the unit circle, so `ρQ` is neither a Pisot nor a Salem
number. -/
theorem ruler_second_conjugate (rho Q : ℝ) (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) (hQ1 : 1 < Q) :
    ∃ z : ℂ, z ^ 4 = z + 1 ∧ z.im ≠ 0 ∧
      1 < ‖(rho : ℂ) * z‖ ∧ ‖(rho : ℂ) * z‖ < rho * Q := by
  sorry

open Polynomial in
/-- **(6) The conjugates of `ρQ` ARE the products of embeddings.** A complex
number is a root of the minimal polynomial of `ρQ` precisely when it is a
product `w·z` of a root of the cubic with a root of the quartic. -/
theorem ruler_conjugates_eq_embedding_products {rho Q : ℝ} (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) (zeta : ℂ) :
    aeval zeta (minpoly ℚ (rho * Q)) = 0 ↔
      ∃ w z : ℂ, w ^ 3 = w + 1 ∧ z ^ 4 = z + 1 ∧ zeta = w * z := by
  sorry

open Polynomial in
/-- **(7) There are exactly twelve of them.** With (6) this is the full
identification: the root set of `minpoly ℚ (ρQ)` over `ℂ` has exactly twelve
elements, and they are exactly the twelve embedding products. -/
theorem ruler_conjugates_card {rho Q : ℝ} (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) :
    Fintype.card ((minpoly ℚ (rho * Q)).rootSet ℂ) = 12 := by
  sorry

/-- **(8) The ruler product is an algebraic unit.**  Over any commutative ring
with `r³ = r + 1` and `q⁴ = q + 1`, the product `r·q` times an explicit
degree-11 integer-coefficient cofactor equals `1`: the degree-12 polynomial has
constant term `−1`, so `ρQ` is a unit.  In particular `ρ·Q·(ρQ)⁻¹ = 1`
realizes the degree triple `(3, 4, 12)` in the normal form `α·β·γ = 1`. -/
theorem ruler_unit {R : Type*} [CommRing R] (r q : R)
    (hr : r ^ 3 = r + 1) (hq : q ^ 4 = q + 1) :
    (r * q) * ((r * q) ^ 11 - 3 * (r * q) ^ 8 - 2 * (r * q) ^ 7 + 2 * (r * q) ^ 5
      - (r * q) ^ 4 - 3 * (r * q) ^ 3 - (r * q) ^ 2 + 1) = 1 := by
  sorry

open Polynomial in
/-- **(9) The degree-12 polynomial is not reciprocal.**  Its coefficient list
`(1, 0, 0, −3, −2, 0, 2, −1, −3, −1, 0, 1, −1)` (leading coefficient first) is
neither its own reversal nor the negation of its reversal — both comparisons
fail at the coefficient of `X³` — so the minimal polynomial of `ρQ` lies in
the nonreciprocal regime of Smyth's theorem. -/
theorem rulerPoly_nonreciprocal :
    (X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1
        : ℚ[X]).reverse
      ≠ (X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1) ∧
    (X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1
        : ℚ[X]).reverse
      ≠ -(X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1) := by
  sorry

/-- **(10) Degree multiplicativity at the ruler product.**  The degree of the
minimal polynomial of `ρQ` is the PRODUCT of the degrees of the minimal
polynomials of `ρ` and `Q` — `12 = 3·4`.  No general theorem forces this for
products (`ζ₃·∛2` has degree 3, not 6), unlike the coprime-degree sum case;
the equality is content certified here. -/
theorem ruler_degree_multiplicative {rho Q : ℝ} (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) :
    (minpoly ℚ (rho * Q)).natDegree
      = (minpoly ℚ rho).natDegree * (minpoly ℚ Q).natDegree := by
  sorry

open IntermediateField in
/-- **(11) The compositum, its degree, and linear disjointness.**
`ℚ(ρ) ⊔ ℚ(Q) = ℚ(ρQ)`: the ruler product is a primitive element of the
compositum, which has degree 12 over `ℚ`, and the two simple extensions are
linearly disjoint.  DISCLOSURE: given the degrees 3 and 4, the disjointness
half is near-automatic from Mathlib's
`IntermediateField.LinearDisjoint.of_finrank_coprime`; the substantive content
is the sup-equality. -/
theorem ruler_linearDisjoint {rho Q : ℝ} (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) :
    ℚ⟮rho⟯ ⊔ ℚ⟮Q⟯ = ℚ⟮rho * Q⟯ ∧
      Module.finrank ℚ ↥(ℚ⟮rho⟯ ⊔ ℚ⟮Q⟯) = 12 ∧
      ℚ⟮rho⟯.LinearDisjoint ℚ⟮Q⟯ := by
  sorry

open Polynomial in
/-- **(12) The unit-circle census of the conjugates of the ruler product.**
The root set of `minpoly ℚ (ρQ)` in `ℂ` has EXACTLY 5 elements of modulus
`> 1`, EXACTLY 7 of modulus `< 1`, and none on the unit circle.  In
particular `ρQ` is neither a Pisot number (which would put all eleven other
conjugates inside) nor a Salem number (which would put conjugates on the
circle). -/
theorem ruler_conjugate_census {rho Q : ℝ} (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) :
    {ζ ∈ (minpoly ℚ (rho * Q)).rootSet ℂ | 1 < ‖ζ‖}.ncard = 5 ∧
      {ζ ∈ (minpoly ℚ (rho * Q)).rootSet ℂ | ‖ζ‖ < 1}.ncard = 7 ∧
      ∀ ζ ∈ (minpoly ℚ (rho * Q)).rootSet ℂ, ‖ζ‖ ≠ 1 := by
  sorry

open Polynomial in
/-- **(13) The house of the ruler product is `ρQ` itself.**  Every root of
`minpoly ℚ (ρQ)` other than `ρQ` has modulus strictly below `ρQ`: the ruler
product is the unique dominant root of its own minimal polynomial — the dominant-root property of the LRS decision-problems
literature's operative hypothesis class, certified for this instance. -/
theorem ruler_house {rho Q : ℝ} (hrho : rho ^ 3 = rho + 1) (hQ : Q ^ 4 = Q + 1)
    (hQ1 : 1 < Q) :
    ∀ ζ ∈ (minpoly ℚ (rho * Q)).rootSet ℂ, ζ ≠ ((rho * Q : ℝ) : ℂ) →
      ‖ζ‖ < rho * Q := by
  sorry

open Polynomial in
/-- **(14) The exact Mahler measure of the degree-12 polynomial.**
`M = ρ²·Q²·ψ`, where `ψ` is the real root `> 1` of `ψ⁴ = ψ³ + 1`.  (`ψ` is
forced by the same quartic: it is `−1/r₂` for the quartic's negative real
root `r₂`.)  The product of `max 1 ‖ζ‖` over the twelve conjugates of `ρQ`
collapses to this closed form. -/
theorem ruler_mahler_measure {rho Q psi : ℝ} (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) (hQ1 : 1 < Q)
    (hpsi : psi ^ 4 = psi ^ 3 + 1) (hpsi1 : 1 < psi) :
    ((X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1
        : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure = rho ^ 2 * Q ^ 2 * psi := by
  sorry

open Polynomial in
/-- **(15) The registry bridge, as a product identity.**  The Mahler measure of the quartic is `M(X⁴ − X − 1) = ψ` — the quantity pinned in the
registered entry PALOMAR-2026-08-31-000004 — and the measure of the degree-12
polynomial is exactly `(ρQ)²` times it:
`M(rulerPoly) = (ρQ)² · M(X⁴ − X − 1)`. -/
theorem ruler_mahler_eq_quartic_measure {rho Q psi : ℝ} (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) (hQ1 : 1 < Q)
    (hpsi : psi ^ 4 = psi ^ 3 + 1) (hpsi1 : 1 < psi) :
    ((X ^ 4 - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure = psi ∧
      ((X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1
          : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure
        = (rho * Q) ^ 2 * ((X ^ 4 - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure := by
  sorry

open Polynomial in
/-- **(16) The order-12 product recurrence, in characteristic-polynomial
form.**  For ANY sequences in a `ℚ`-algebra with `u(n+3) = u(n+1) + u(n)`
(the Padovan/Perrin recurrence, characteristic polynomial `x³ − x − 1`) and
`v(n+4) = v(n+1) + v(n)` (characteristic polynomial `x⁴ − x − 1`), the
termwise (Hadamard) product satisfies the order-12 recurrence whose
characteristic polynomial is exactly the degree-12 polynomial:
`∑ k ≤ 12, cₖ·(u(n+k)·v(n+k)) = 0` where `cₖ` are its coefficients. -/
theorem product_recurrence_charpoly {A : Type*} [CommRing A] [Algebra ℚ A]
    (u v : ℕ → A)
    (hu : ∀ n, u (n + 3) = u (n + 1) + u n)
    (hv : ∀ n, v (n + 4) = v (n + 1) + v n) (n : ℕ) :
    ∑ k ∈ Finset.range 13,
      (X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1
        : ℚ[X]).coeff k • (u (n + k) * v (n + k)) = 0 := by
  sorry

open Polynomial in
/-- **(17) The annihilator ideal is exactly the principal ideal of the
degree-12 polynomial.**  A rational polynomial `p` annihilates the product
power sequence `n ↦ ρⁿ·Qⁿ` (coefficient-wise:
`∀ n, ∑ k ≤ deg p, p.coeff k · (ρQ)^(n+k) = 0`) IF AND ONLY IF the degree-12
polynomial divides `p`.  In particular no nonzero recurrence of order `< 12`
annihilates the product: the classical order `≤ 3·4` bound for the Hadamard
product is an equality here, forced by the polynomial's irreducibility. -/
theorem product_annihilator_iff {rho Q : ℝ}
    (hrho : rho ^ 3 = rho + 1) (hQ : Q ^ 4 = Q + 1) (p : ℚ[X]) :
    (∀ n : ℕ, ∑ k ∈ Finset.range (p.natDegree + 1),
        p.coeff k • (rho ^ (n + k) * Q ^ (n + k)) = 0)
      ↔ (X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1
          : ℚ[X]) ∣ p := by
  sorry

end PlasticThreshold
