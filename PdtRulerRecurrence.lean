module
public import PdtRulerMinpoly

@[expose] public section
/-!
# PdtRulerRecurrence — the order-12 product recurrence of `rulerPoly`

Let `u` be ANY sequence satisfying the cubic shift recurrence
`u (n+3) = u (n+1) + u n` (the Padovan/Perrin recurrence, characteristic
polynomial `x³ − x − 1`) and `v` ANY sequence satisfying the quartic shift
recurrence `v (n+4) = v (n+1) + v n` (characteristic polynomial `x⁴ − x − 1`),
with values in an arbitrary commutative ring.  This module proves:

* `product_recurrence` — the termwise (Hadamard) product `w n = u n * v n`
  satisfies the order-12 linear recurrence
  `w (n+12) = 3w(n+9) + 2w(n+8) − 2w(n+6) + w(n+5) + 3w(n+4) + w(n+3) − w(n+1) + w n`,
  whose characteristic polynomial is exactly `rulerPoly`.
* `product_recurrence_charpoly` — the same statement in characteristic-
  polynomial form: `∑ k ∈ range 13, rulerPoly.coeff k • (u (n+k) * v (n+k)) = 0`
  in any `ℚ`-algebra.
* `product_recurrence_minimal` — minimality, over `ℚ`: for the canonical
  member of the family — the power sequences `u n = ρⁿ`, `v n = Qⁿ`, product
  `w n = (ρQ)ⁿ` — ANY `p ∈ ℚ[X]` whose coefficients annihilate `w`
  (`∀ n, ∑ k ∈ range (p.natDegree+1), p.coeff k • w (n+k) = 0`) is divisible
  by `rulerPoly`; in particular (`product_recurrence_minimal_degree`) a
  nonzero annihilator has degree ≥ 12, so no recurrence of order < 12
  annihilates every such product.  The classical order ≤ 3·4 bound for the
  Hadamard product is therefore an equality here, and the in-repo
  `rulerPoly_irreducible`/`ruler_minpoly` are what force it.

No physical claim appears in any statement.
-/

namespace PDT
namespace RulerRecurrence

open Polynomial RulerMinpoly

/-- **The order-12 product recurrence.**  Over ANY commutative ring, if `u`
satisfies the cubic recurrence `u (n+3) = u (n+1) + u n` and `v` the quartic
recurrence `v (n+4) = v (n+1) + v n`, the termwise product satisfies the
order-12 recurrence with characteristic polynomial
`rulerPoly = X¹² − 3X⁹ − 2X⁸ + 2X⁶ − X⁵ − 3X⁴ − X³ + X − 1`. -/
theorem product_recurrence {R : Type*} [CommRing R] (u v : ℕ → R)
    (hu : ∀ n, u (n + 3) = u (n + 1) + u n)
    (hv : ∀ n, v (n + 4) = v (n + 1) + v n) (n : ℕ) :
    u (n + 12) * v (n + 12)
      = 3 * (u (n + 9) * v (n + 9)) + 2 * (u (n + 8) * v (n + 8))
        - 2 * (u (n + 6) * v (n + 6)) + u (n + 5) * v (n + 5)
        + 3 * (u (n + 4) * v (n + 4)) + u (n + 3) * v (n + 3)
        - u (n + 1) * v (n + 1) + u n * v n := by
  have hu3 : u (n + 3) = u (n + 1) + u n := hu n
  have hu4 : u (n + 4) = u (n + 2) + u (n + 1) := hu (n + 1)
  have hu5 : u (n + 5) = u (n + 3) + u (n + 2) := hu (n + 2)
  have hu6 : u (n + 6) = u (n + 4) + u (n + 3) := hu (n + 3)
  have hu7 : u (n + 7) = u (n + 5) + u (n + 4) := hu (n + 4)
  have hu8 : u (n + 8) = u (n + 6) + u (n + 5) := hu (n + 5)
  have hu9 : u (n + 9) = u (n + 7) + u (n + 6) := hu (n + 6)
  have hu10 : u (n + 10) = u (n + 8) + u (n + 7) := hu (n + 7)
  have hu12 : u (n + 12) = u (n + 10) + u (n + 9) := hu (n + 9)
  have hv4 : v (n + 4) = v (n + 1) + v n := hv n
  have hv5 : v (n + 5) = v (n + 2) + v (n + 1) := hv (n + 1)
  have hv6 : v (n + 6) = v (n + 3) + v (n + 2) := hv (n + 2)
  have hv8 : v (n + 8) = v (n + 5) + v (n + 4) := hv (n + 4)
  have hv9 : v (n + 9) = v (n + 6) + v (n + 5) := hv (n + 5)
  have hv12 : v (n + 12) = v (n + 9) + v (n + 8) := hv (n + 8)
  simp only [hu12, hu10, hu9, hu8, hu7, hu6, hu5, hu4, hu3,
    hv12, hv9, hv8, hv6, hv5, hv4]
  ring1

/-- **The product recurrence in characteristic-polynomial form.**  In any
`ℚ`-algebra the previous identity reads
`∑ k ∈ range 13, rulerPoly.coeff k • (u (n+k) * v (n+k)) = 0`:
the characteristic polynomial of the order-12 product recurrence is exactly
`rulerPoly`, the minimal polynomial of `ρQ`. -/
theorem product_recurrence_charpoly {A : Type*} [CommRing A] [Algebra ℚ A]
    (u v : ℕ → A)
    (hu : ∀ n, u (n + 3) = u (n + 1) + u n)
    (hv : ∀ n, v (n + 4) = v (n + 1) + v n) (n : ℕ) :
    ∑ k ∈ Finset.range 13, rulerPoly.coeff k • (u (n + k) * v (n + k)) = 0 := by
  have h := product_recurrence u v hu hv n
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, rulerPoly]
  norm_num [coeff_X_pow, coeff_X, coeff_one, Algebra.smul_def, map_neg, map_one,
    map_ofNat]
  linear_combination h

/-! ### The canonical member of the family: the power sequences -/

/-- The power sequence of any root of the cubic satisfies the cubic shift
recurrence: the product family of `product_recurrence` contains `n ↦ ρⁿ`. -/
lemma pow_cubic_recurrence {R : Type*} [CommRing R] {r : R}
    (hr : r ^ 3 = r + 1) (n : ℕ) : r ^ (n + 3) = r ^ (n + 1) + r ^ n := by
  have h : r ^ (n + 3) = r ^ n * r ^ 3 := by ring
  rw [h, hr]; ring

/-- The power sequence of any root of the quartic satisfies the quartic shift
recurrence: the product family contains `n ↦ Qⁿ`. -/
lemma pow_quartic_recurrence {R : Type*} [CommRing R] {q : R}
    (hq : q ^ 4 = q + 1) (n : ℕ) : q ^ (n + 4) = q ^ (n + 1) + q ^ n := by
  have h : q ^ (n + 4) = q ^ n * q ^ 4 := by ring
  rw [h, hq]; ring

/-! ### Minimality over `ℚ` -/

/-- Bridge: applying a polynomial's coefficients to the shifted power sequence
`k ↦ x^(n+k)` is `x^n` times evaluating the polynomial at `x`. -/
lemma annihilator_sum_eq (x : ℝ) (p : ℚ[X]) (n : ℕ) :
    ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • x ^ (n + k)
      = x ^ n * aeval x p := by
  have hlt : (p.map (algebraMap ℚ ℝ)).natDegree < p.natDegree + 1 :=
    lt_of_le_of_lt (natDegree_map_le) (Nat.lt_succ_self _)
  rw [aeval_def, eval₂_eq_eval_map, eval_eq_sum_range' hlt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_map, Algebra.smul_def, pow_add]
  ring

/-- **Minimality of the order-12 product recurrence.**  Take the canonical
member of the product family, `u n = ρⁿ`, `v n = Qⁿ` (both in the family, by
`pow_cubic_recurrence`/`pow_quartic_recurrence`), so `w n = (ρQ)ⁿ`.  Any
`p ∈ ℚ[X]` whose coefficients annihilate `w` is divisible by `rulerPoly`:
annihilation at `n = 0` forces `p(ρQ) = 0`, and `ruler_minpoly` identifies
`rulerPoly` as the minimal polynomial of `ρQ`. -/
theorem product_recurrence_minimal {rho QQ : ℝ}
    (hr : rho ^ 3 = rho + 1) (hq : QQ ^ 4 = QQ + 1) (p : ℚ[X])
    (hp : ∀ n : ℕ, ∑ k ∈ Finset.range (p.natDegree + 1),
      p.coeff k • (rho ^ (n + k) * QQ ^ (n + k)) = 0) :
    rulerPoly ∣ p := by
  have h0 := hp 0
  simp only [← mul_pow] at h0
  rw [annihilator_sum_eq (rho * QQ) p 0, pow_zero, one_mul] at h0
  have hdvd := minpoly.dvd ℚ (rho * QQ) h0
  rwa [ruler_minpoly hr hq] at hdvd

/-- **No product recurrence of order < 12.**  A nonzero rational annihilator
of the product power sequence has degree at least 12: the classical
order ≤ 3·4 bound for the Hadamard product of the cubic and quartic
recurrences is an equality at `(ρ, Q)`. -/
theorem product_recurrence_minimal_degree {rho QQ : ℝ}
    (hr : rho ^ 3 = rho + 1) (hq : QQ ^ 4 = QQ + 1) (p : ℚ[X])
    (hp : ∀ n : ℕ, ∑ k ∈ Finset.range (p.natDegree + 1),
      p.coeff k • (rho ^ (n + k) * QQ ^ (n + k)) = 0)
    (hp0 : p ≠ 0) : 12 ≤ p.natDegree := by
  have h := natDegree_le_of_dvd (product_recurrence_minimal hr hq p hp) hp0
  rwa [rulerPoly_natDegree] at h

/-- **The annihilator ideal is exactly `(rulerPoly)`.**  A rational polynomial
annihilates the product power sequence `n ↦ ρⁿ·Qⁿ` IF AND ONLY IF it is a
multiple of `rulerPoly` — the annihilator ideal of the Hadamard product is the
principal ideal generated by the (irreducible, `rulerPoly_irreducible`)
minimal polynomial of `ρQ`. -/
theorem product_annihilator_iff {rho QQ : ℝ}
    (hr : rho ^ 3 = rho + 1) (hq : QQ ^ 4 = QQ + 1) (p : ℚ[X]) :
    (∀ n : ℕ, ∑ k ∈ Finset.range (p.natDegree + 1),
        p.coeff k • (rho ^ (n + k) * QQ ^ (n + k)) = 0)
      ↔ rulerPoly ∣ p := by
  constructor
  · exact product_recurrence_minimal hr hq p
  · rintro ⟨g, rfl⟩ n
    simp only [← mul_pow]
    rw [annihilator_sum_eq (rho * QQ) _ n, map_mul,
      aeval_rulerPoly rho QQ hr hq, zero_mul, mul_zero]

end RulerRecurrence
end PDT

/-! ### Axiom audit -/

#print axioms PDT.RulerRecurrence.product_recurrence
#print axioms PDT.RulerRecurrence.product_recurrence_charpoly
#print axioms PDT.RulerRecurrence.pow_cubic_recurrence
#print axioms PDT.RulerRecurrence.pow_quartic_recurrence
#print axioms PDT.RulerRecurrence.annihilator_sum_eq
#print axioms PDT.RulerRecurrence.product_recurrence_minimal
#print axioms PDT.RulerRecurrence.product_recurrence_minimal_degree
#print axioms PDT.RulerRecurrence.product_annihilator_iff
