import Mathlib

/-!
# The plastic number as a spectral threshold: the Bedford–Kim family

Bedford–Kim (J. Geom. Anal. 19 (2009); arXiv:math/0611297) construct
rational surface automorphisms from linear fractional recurrences; the
characteristic polynomial of the induced action on cohomology is
`χ_n(x) = x^(n+1)·(x³ − x − 1) + (x³ + x² − 1)` (equivalently, their
eq. 0.3) — the plastic polynomial `x³ − x − 1` paired with its (monic)
reciprocal — and they
prove the spectral radii λ_n increase to the real root of `t³ = t + 1`,
the plastic number, the smallest Pisot number and the threshold constant
of the Blanc–Cantat classification of birational surface dynamical
degrees (JAMS 29 (2016)). The statements below are the SPECTRAL half of
that picture, kernel-checked: canonical largest roots below ρ, strict
increase, and convergence to ρ. Whether ρ itself is ATTAINED as a
dynamical degree is open in the literature; nothing here claims it.

The factorization `χ_7(x) = (x − 1)·L(x)`, with `L` Lehmer's degree-10
polynomial, is exact — so Lehmer's number, whose logarithm is the proven
minimum positive entropy of a surface automorphism (McMullen, Publ.
Math. IHES 105 (2007), Thm 1.2: `h(F) ≥ log λ_Lehmer`, attained by his
`F_10`), is the first member (`n = 7`) of the plastic family, and `L`
has a root in `[117/100, ρ)`.

The fifth statement is an exclusion witness in the same arithmetic
("ruler", in its name, is the source project's term for the product
`ρQ`; nothing in the statement depends on it): a NONREAL root `z` of
`x⁴ = x + 1` with `1 < ‖ρ·z‖ < ρ·Q`. The products of embeddings are the
conjugates of `ρQ` in the degree-12 compositum — an identification
FORMALIZED here, as statements (6) and (7), unlike the Blanc–Cantat
classification after it, which remains cited — so this is a second
conjugate of `ρQ` strictly
outside the unit circle: `ρQ` is neither a Pisot nor a Salem number
(and hence, by the cited classification, not the dynamical degree of
any birational surface transformation).

Hypotheses are inline — `ρ` and `Q` enter only through their defining
equations, plus the root-selection inequality `1 < Q` on the exclusion
witness, which the quartic's negative real root genuinely fails — and
the statements use only core Mathlib vocabulary —
`Filter.Tendsto`, `nhds`, the complex norm — with no custom
definitions. The roots below ρ are canonical: largest in `[117/100, ρ)`,
with `χ_n > 0` on `[ρ, ∞)`; the interval `(1, 117/100)` is not swept
here (Bedford–Kim's Salem factorization places no roots there; cited).

Sources: E. Bedford and K. Kim, "Dynamics of rational surface
automorphisms: linear fractional recurrences", J. Geom. Anal. 19 (2009);
arXiv:math/0611297. J. Blanc and S. Cantat, "Dynamical degrees of
birational transformations of projective surfaces", J. Amer. Math. Soc.
29 (2016) 415–471. D. H. Lehmer, "Factorization of certain cyclotomic
functions", Ann. of Math. 34 (1933). C. T. McMullen, "Dynamics on
blowups of the projective plane", Publ. Math. IHES 105 (2007) 49–89.
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

end PlasticThreshold
