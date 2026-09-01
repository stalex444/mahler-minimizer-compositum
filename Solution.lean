/-
Solution: proofs of the challenge statements, transferred from the
PdtIrreducible / PdtSalemFamily / PdtRulerMinpoly / PdtRulerCensus /
PdtRulerMeasure / PdtRulerRecurrence developments.
-/
import PdtSalemFamily
import PdtRulerMinpoly
import PdtRulerCensus
import PdtRulerMeasure
import PdtRulerRecurrence

open Polynomial IntermediateField

namespace PlasticThreshold

/-- **Nothing at or above ρ**: every member of the Bedford–Kim family
`χ_n(x) = x^(n+1)·(x³ − x − 1) + (x³ + x² − 1)` is strictly positive on
`[ρ, ∞)`. -/
theorem family_pos_of_rho_le (rho : ℝ) (hrho : rho ^ 3 = rho + 1)
    (n : ℕ) {y : ℝ} (hy : rho ≤ y) :
    0 < y ^ (n + 1) * (y ^ 3 - y - 1) + (y ^ 3 + y ^ 2 - 1) :=
  PDT.SalemFamily.family_pos_of_rho_le hrho n hy

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
      Filter.Tendsto lam Filter.atTop (nhds rho) :=
  PDT.SalemFamily.plastic_salem_family hrho

/-- **Lehmer is the first rung**: the exact factorization
`χ_7(x) = (x − 1)·L(x)` with `L` Lehmer's polynomial, over any
commutative ring. -/
theorem lehmer_first_rung {R : Type*} [CommRing R] (x : R) :
    x ^ 8 * (x ^ 3 - x - 1) + (x ^ 3 + x ^ 2 - 1) =
    (x - 1) * (x ^ 10 + x ^ 9 - x ^ 7 - x ^ 6 - x ^ 5 - x ^ 4 - x ^ 3 + x + 1) :=
  PDT.SalemFamily.lehmer_first_rung x

/-- **Lehmer's polynomial has a root below the plastic number**, in
`[117/100, ρ)` — the `n = 7` canonical root of the plastic family. -/
theorem lehmer_root_below_plastic (rho : ℝ) (hrho : rho ^ 3 = rho + 1) :
    ∃ x : ℝ, (117 / 100 : ℝ) ≤ x ∧ x < rho ∧
      x ^ 10 + x ^ 9 - x ^ 7 - x ^ 6 - x ^ 5 - x ^ 4 - x ^ 3 + x + 1 = 0 :=
  PDT.SalemFamily.lehmer_root_below_plastic hrho

/-- **The ruler exclusion witness**: a nonreal root `z` of `x⁴ = x + 1`
with `1 < ‖ρ·z‖ < ρ·Q`. Together with statements (6) and (7) below,
which formalize the identification of the twelve embedding products as
the conjugates of `ρQ`, this is a second conjugate of `ρQ` strictly
outside the unit circle, so `ρQ` is neither a Pisot nor a Salem
number. -/
theorem ruler_second_conjugate (rho Q : ℝ) (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) (hQ1 : 1 < Q) :
    ∃ z : ℂ, z ^ 4 = z + 1 ∧ z.im ≠ 0 ∧
      1 < ‖(rho : ℂ) * z‖ ∧ ‖(rho : ℂ) * z‖ < rho * Q :=
  PDT.SalemFamily.ruler_second_conjugate hQ hQ1 hrho

/-- **(6) The conjugates of `ρQ` ARE the products of embeddings.** A complex
number is a root of the minimal polynomial of `ρQ` precisely when it is a
product `w·z` of a root of the cubic with a root of the quartic. -/
theorem ruler_conjugates_eq_embedding_products {rho Q : ℝ} (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) (zeta : ℂ) :
    aeval zeta (minpoly ℚ (rho * Q)) = 0 ↔
      ∃ w z : ℂ, w ^ 3 = w + 1 ∧ z ^ 4 = z + 1 ∧ zeta = w * z :=
  PDT.RulerMinpoly.conjugates_eq_embedding_products hrho hQ zeta

/-- **(7) There are exactly twelve of them.** With (6) this is the full
identification: the root set of `minpoly ℚ (ρQ)` over `ℂ` has exactly twelve
elements, and they are exactly the twelve embedding products. -/
theorem ruler_conjugates_card {rho Q : ℝ} (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) :
    Fintype.card ((minpoly ℚ (rho * Q)).rootSet ℂ) = 12 := by
  rw [PDT.RulerMinpoly.ruler_minpoly hrho hQ]
  exact PDT.RulerMinpoly.ruler_conjugates_card

/-- **(8) The ruler product is an algebraic unit.** -/
theorem ruler_unit {R : Type*} [CommRing R] (r q : R)
    (hr : r ^ 3 = r + 1) (hq : q ^ 4 = q + 1) :
    (r * q) * ((r * q) ^ 11 - 3 * (r * q) ^ 8 - 2 * (r * q) ^ 7 + 2 * (r * q) ^ 5
      - (r * q) ^ 4 - 3 * (r * q) ^ 3 - (r * q) ^ 2 + 1) = 1 :=
  PDT.RulerMinpoly.ruler_unit r q hr hq

/-- **(9) The degree-12 polynomial is not reciprocal.** -/
theorem rulerPoly_nonreciprocal :
    (X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1
        : ℚ[X]).reverse
      ≠ (X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1) ∧
    (X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1
        : ℚ[X]).reverse
      ≠ -(X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1) :=
  PDT.RulerMinpoly.rulerPoly_nonreciprocal

/-- **(10) Degree multiplicativity at the ruler product.** -/
theorem ruler_degree_multiplicative {rho Q : ℝ} (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) :
    (minpoly ℚ (rho * Q)).natDegree
      = (minpoly ℚ rho).natDegree * (minpoly ℚ Q).natDegree :=
  PDT.RulerMinpoly.ruler_degree_multiplicative hrho hQ

/-- **(11) The compositum, its degree, and linear disjointness.** -/
theorem ruler_linearDisjoint {rho Q : ℝ} (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) :
    ℚ⟮rho⟯ ⊔ ℚ⟮Q⟯ = ℚ⟮rho * Q⟯ ∧
      Module.finrank ℚ ↥(ℚ⟮rho⟯ ⊔ ℚ⟮Q⟯) = 12 ∧
      ℚ⟮rho⟯.LinearDisjoint ℚ⟮Q⟯ :=
  ⟨PDT.RulerMinpoly.ruler_compositum_sup hrho hQ,
    PDT.RulerMinpoly.ruler_compositum_finrank hrho hQ,
    PDT.RulerMinpoly.ruler_linearDisjoint hrho hQ⟩

/-- **(12) The unit-circle census of the conjugates of the ruler product.** -/
theorem ruler_conjugate_census {rho Q : ℝ} (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) :
    {ζ ∈ (minpoly ℚ (rho * Q)).rootSet ℂ | 1 < ‖ζ‖}.ncard = 5 ∧
      {ζ ∈ (minpoly ℚ (rho * Q)).rootSet ℂ | ‖ζ‖ < 1}.ncard = 7 ∧
      ∀ ζ ∈ (minpoly ℚ (rho * Q)).rootSet ℂ, ‖ζ‖ ≠ 1 :=
  PDT.RulerCensus.ruler_conjugate_census hrho hQ

/-- **(13) The house of the ruler product is `ρQ` itself.** -/
theorem ruler_house {rho Q : ℝ} (hrho : rho ^ 3 = rho + 1) (hQ : Q ^ 4 = Q + 1)
    (hQ1 : 1 < Q) :
    ∀ ζ ∈ (minpoly ℚ (rho * Q)).rootSet ℂ, ζ ≠ ((rho * Q : ℝ) : ℂ) →
      ‖ζ‖ < rho * Q :=
  PDT.RulerCensus.ruler_house hrho hQ hQ1

/-- **(14) The exact Mahler measure of the degree-12 polynomial.** -/
theorem ruler_mahler_measure {rho Q psi : ℝ} (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) (hQ1 : 1 < Q)
    (hpsi : psi ^ 4 = psi ^ 3 + 1) (hpsi1 : 1 < psi) :
    ((X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1
        : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure = rho ^ 2 * Q ^ 2 * psi :=
  PDT.RulerMeasure.ruler_mahler_measure hrho hQ hQ1 hpsi hpsi1

/-- **(15) The registry bridge, as a product identity.** -/
theorem ruler_mahler_eq_quartic_measure {rho Q psi : ℝ} (hrho : rho ^ 3 = rho + 1)
    (hQ : Q ^ 4 = Q + 1) (hQ1 : 1 < Q)
    (hpsi : psi ^ 4 = psi ^ 3 + 1) (hpsi1 : 1 < psi) :
    ((X ^ 4 - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure = psi ∧
      ((X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1
          : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure
        = (rho * Q) ^ 2 * ((X ^ 4 - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure :=
  ⟨PDT.RulerMeasure.quartic_mahler_measure hpsi hpsi1,
    PDT.RulerMeasure.ruler_mahler_eq_quartic_measure hrho hQ hQ1⟩

/-- **(16) The order-12 product recurrence, in characteristic-polynomial
form.** -/
theorem product_recurrence_charpoly {A : Type*} [CommRing A] [Algebra ℚ A]
    (u v : ℕ → A)
    (hu : ∀ n, u (n + 3) = u (n + 1) + u n)
    (hv : ∀ n, v (n + 4) = v (n + 1) + v n) (n : ℕ) :
    ∑ k ∈ Finset.range 13,
      (X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1
        : ℚ[X]).coeff k • (u (n + k) * v (n + k)) = 0 :=
  PDT.RulerRecurrence.product_recurrence_charpoly u v hu hv n

/-- **(17) The annihilator ideal is exactly the principal ideal of the
degree-12 polynomial.** -/
theorem product_annihilator_iff {rho Q : ℝ}
    (hrho : rho ^ 3 = rho + 1) (hQ : Q ^ 4 = Q + 1) (p : ℚ[X]) :
    (∀ n : ℕ, ∑ k ∈ Finset.range (p.natDegree + 1),
        p.coeff k • (rho ^ (n + k) * Q ^ (n + k)) = 0)
      ↔ (X ^ 12 - 3 * X ^ 9 - 2 * X ^ 8 + 2 * X ^ 6 - X ^ 5 - 3 * X ^ 4 - X ^ 3 + X - 1
          : ℚ[X]) ∣ p :=
  PDT.RulerRecurrence.product_annihilator_iff hrho hQ p

end PlasticThreshold

/-! ### Axiom audit — every build prints the audit for the compared theorems -/

#print axioms PlasticThreshold.plastic_salem_family
#print axioms PlasticThreshold.family_pos_of_rho_le
#print axioms PlasticThreshold.lehmer_first_rung
#print axioms PlasticThreshold.lehmer_root_below_plastic
#print axioms PlasticThreshold.ruler_second_conjugate
#print axioms PlasticThreshold.ruler_conjugates_eq_embedding_products
#print axioms PlasticThreshold.ruler_conjugates_card
#print axioms PlasticThreshold.ruler_unit
#print axioms PlasticThreshold.rulerPoly_nonreciprocal
#print axioms PlasticThreshold.ruler_degree_multiplicative
#print axioms PlasticThreshold.ruler_linearDisjoint
#print axioms PlasticThreshold.ruler_conjugate_census
#print axioms PlasticThreshold.ruler_house
#print axioms PlasticThreshold.ruler_mahler_measure
#print axioms PlasticThreshold.ruler_mahler_eq_quartic_measure
#print axioms PlasticThreshold.product_recurrence_charpoly
#print axioms PlasticThreshold.product_annihilator_iff
