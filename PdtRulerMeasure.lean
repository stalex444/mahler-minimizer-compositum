import PdtRulerCensus

/-!
# PdtRulerMeasure — the Mahler measure of the ruler minimal polynomial

Let `ρ` be the real root of `x³ = x + 1`, `Q` the real root `> 1` of
`x⁴ = x + 1`, and `ψ` the real root `> 1` of `ψ⁴ = ψ³ + 1` (the image of the
quartic's negative real root `r₂` under `x ↦ −1/x`).  This module computes, in
the kernel:

* `quartic_mahler_measure` — `M(X⁴ − X − 1) = ψ`: the Mahler measure of the
  PDT quartic itself, the degree-4 registry-bridge quantity.
* `ruler_mahler_measure` — `M(rulerPoly) = ρ²·Q²·ψ`: the Mahler measure of the
  degree-12 minimal polynomial of the ruler product `ρQ`.
* `ruler_mahler_eq_quartic_measure` — the bridge as a product identity:
  `M(rulerPoly) = (ρQ)² · M(X⁴ − X − 1)`.
* `ruler_mahler_gt_one` — `1 < M(rulerPoly)`.

Route: `rulerPoly` is monic, and `Polynomial.mahlerMeasure` of a monic complex
polynomial is the product of `max 1 ‖root‖` over its roots.  The mapped
polynomial factors into twelve explicit linear factors (the products `w·z` of
the three cubic roots with the four quartic roots, via the public
`ruler_factorization`), the certified rational brackets classify each root
against the unit circle, and the Vieta closed forms `|σ|² = ρ² − 1 = 1/ρ`,
`Q·r₂·|z|² = −1` collapse the outside product `ρQ·|ρz|²·|σQ|²` to `ρ²Q²·ψ`.
No numerics enter the kernel.
-/

namespace PDT
namespace RulerMeasure

open Polynomial Complex PDT.RulerMinpoly

/-! ### Brackets for the three real roots (the census versions are private) -/

private lemma cubic_gt_one {a : ℝ} (ha : a ^ 3 = a + 1) : 1 < a := by
  nlinarith [sq_nonneg (a + 9 / 10), sq_nonneg (a + 1 / 160), sq_nonneg a]

private lemma cubic_bounds {a : ℝ} (ha : a ^ 3 = a + 1) :
    132 / 100 < a ∧ a < 133 / 100 := by
  have h1 : 1 < a := cubic_gt_one ha
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg (a - 1), sq_nonneg (a + 1)]

private lemma quartic_pos_bounds {b : ℝ} (hb : b ^ 4 = b + 1) (h1 : 1 < b) :
    122 / 100 < b ∧ b < 123 / 100 := by
  constructor <;>
    nlinarith [sq_nonneg b, sq_nonneg (b - 1), sq_nonneg (b + 1), sq_nonneg (b ^ 2 - 1),
      sq_nonneg (b ^ 2 - b)]

private lemma quartic_neg_bounds {c : ℝ} (hc : c ^ 4 = c + 1) (h0 : c < 0) :
    -73 / 100 < c ∧ c < -72 / 100 := by
  have hm1 : -1 < c := by nlinarith [sq_nonneg (c + 1), sq_nonneg (c ^ 2 - 1)]
  constructor <;>
    nlinarith [sq_nonneg c, sq_nonneg (c + 1), sq_nonneg (c ^ 2 - 1), sq_nonneg (c ^ 2 + c)]

/-- The PDT quartic has a real root in `(−1, 0)`. -/
private lemma exists_quartic_neg_root : ∃ x : ℝ, x ^ 4 = x + 1 ∧ x < 0 := by
  have hc : ContinuousOn (fun y : ℝ => y ^ 4 - y - 1) (Set.Icc (-3 / 4) (-7 / 10)) := by
    fun_prop
  obtain ⟨x, hxm, hx⟩ := intermediate_value_Icc' (by norm_num : (-3 / 4 : ℝ) ≤ -7 / 10) hc
    (show (0:ℝ) ∈ Set.Icc ((-7 / 10 : ℝ) ^ 4 - (-7 / 10) - 1)
        ((-3 / 4 : ℝ) ^ 4 - (-3 / 4) - 1) by norm_num)
  exact ⟨x, by simp only at hx; linarith, lt_of_le_of_lt hxm.2 (by norm_num)⟩

/-! ### Uniqueness of the three real roots -/

private lemma cubic_unique {a b : ℝ} (ha : a ^ 3 = a + 1) (hb : b ^ 3 = b + 1) : a = b := by
  have h1 : 1 < a := cubic_gt_one ha
  have h2 : 1 < b := cubic_gt_one hb
  have key : (a - b) * (a ^ 2 + a * b + b ^ 2 - 1) = 0 := by linear_combination ha - hb
  have hpos : 0 < a ^ 2 + a * b + b ^ 2 - 1 := by nlinarith
  rcases mul_eq_zero.mp key with h | h
  · linarith [sub_eq_zero.mp h]
  · exact absurd h (ne_of_gt hpos)

private lemma quartic_pos_unique {a b : ℝ} (ha : a ^ 4 = a + 1) (h1 : 1 < a)
    (hb : b ^ 4 = b + 1) (h2 : 1 < b) : a = b := by
  have key : (a - b) * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 - 1) = 0 := by
    linear_combination ha - hb
  have hpos : 0 < a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 - 1 := by nlinarith
  rcases mul_eq_zero.mp key with h | h
  · linarith [sub_eq_zero.mp h]
  · exact absurd h (ne_of_gt hpos)

/-- The negative real root of the quartic is unique. -/
private lemma quartic_neg_unique {a b : ℝ} (ha : a ^ 4 = a + 1) (h0 : a < 0)
    (hb : b ^ 4 = b + 1) (h2 : b < 0) : a = b := by
  have ha2 : 0 < a ^ 2 := by nlinarith [mul_pos_of_neg_of_neg h0 h0]
  have hb2 : 0 < b ^ 2 := by nlinarith [mul_pos_of_neg_of_neg h2 h2]
  have key : (a - b) * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 - 1) = 0 := by
    linear_combination ha - hb
  have t1 : a ^ 3 < 0 := by nlinarith [mul_neg_of_neg_of_pos h0 ha2]
  have t2 : a ^ 2 * b < 0 := mul_neg_of_pos_of_neg ha2 h2
  have t3 : a * b ^ 2 < 0 := mul_neg_of_neg_of_pos h0 hb2
  have t4 : b ^ 3 < 0 := by nlinarith [mul_neg_of_neg_of_pos h2 hb2]
  have hneg : a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 - 1 < 0 := by linarith
  rcases mul_eq_zero.mp key with h | h
  · linarith [sub_eq_zero.mp h]
  · exact absurd h (ne_of_lt hneg)

/-! ### The chosen witnesses: `ρ`, `Q`, `r₂` -/

private noncomputable def rr : ℝ := exists_cubic_root_mem.choose

private lemma rr_cubic : rr ^ 3 = rr + 1 := exists_cubic_root_mem.choose_spec.1

private lemma rr_bounds : 132 / 100 < rr ∧ rr < 133 / 100 := cubic_bounds rr_cubic

private noncomputable def qq : ℝ := exists_quartic_root.choose

private lemma qq_quartic : qq ^ 4 = qq + 1 := exists_quartic_root.choose_spec.1

private lemma qq_gt_one : 1 < qq := exists_quartic_root.choose_spec.2

private lemma qq_bounds : 122 / 100 < qq ∧ qq < 123 / 100 :=
  quartic_pos_bounds qq_quartic qq_gt_one

private noncomputable def nn : ℝ := exists_quartic_neg_root.choose

private lemma nn_quartic : nn ^ 4 = nn + 1 := exists_quartic_neg_root.choose_spec.1

private lemma nn_neg : nn < 0 := exists_quartic_neg_root.choose_spec.2

private lemma nn_bounds : -73 / 100 < nn ∧ nn < -72 / 100 :=
  quartic_neg_bounds nn_quartic nn_neg

private lemma rr_pos : 0 < rr := by linarith [rr_bounds.1]
private lemma qq_pos : 0 < qq := by linarith [qq_bounds.1]

/-! ### The complex cubic root `σ` and quartic root `z` (upper half plane) -/

private noncomputable def sig : ℂ :=
  ((-rr / 2 : ℝ) : ℂ) + ((Real.sqrt (3 * rr ^ 2 - 4) / 2 : ℝ) : ℂ) * Complex.I

private lemma sig_disc_pos : 0 < 3 * rr ^ 2 - 4 := by
  have h := rr_bounds
  nlinarith [h.1, h.2]

/-- `σ` satisfies the quadratic cofactor of the cubic: `σ² + ρσ + ρ² = 1`. -/
private lemma sig_quadratic : sig ^ 2 + (rr : ℂ) * sig + (rr : ℂ) ^ 2 = 1 := by
  have hd2 : (Real.sqrt (3 * rr ^ 2 - 4)) ^ 2 = 3 * rr ^ 2 - 4 :=
    Real.sq_sqrt sig_disc_pos.le
  have hd2C : ((Real.sqrt (3 * rr ^ 2 - 4) : ℝ) : ℂ) ^ 2 = 3 * (rr : ℂ) ^ 2 - 4 := by
    exact_mod_cast hd2
  have hI : (Complex.I) ^ 2 = -1 := Complex.I_sq
  unfold sig
  push_cast
  linear_combination (((Real.sqrt (3 * rr ^ 2 - 4) : ℝ) : ℂ) ^ 2 / 4) * hI
    - (1 / 4 : ℂ) * hd2C

private lemma sig_re : sig.re = -rr / 2 := by
  simp [sig]

/-- The Vieta modulus of the cubic pair: `|σ|² = ρ² − 1`. -/
private lemma normSq_sig : Complex.normSq sig = rr ^ 2 - 1 := by
  have hd2 : (Real.sqrt (3 * rr ^ 2 - 4)) ^ 2 = 3 * rr ^ 2 - 4 :=
    Real.sq_sqrt sig_disc_pos.le
  unfold sig
  rw [Complex.normSq_add_mul_I]
  nlinarith [hd2]

/-- Newton–Vieta for the two real quartic roots: `(Q + r₂)(Q² + r₂²) = 1`. -/
private lemma quartic_key : (qq + nn) * (qq ^ 2 + nn ^ 2) = 1 := by
  have hne : qq - nn ≠ 0 := by
    have := qq_gt_one; have := nn_neg; intro h; linarith [sub_eq_zero.mp h]
  have h : (qq - nn) * ((qq + nn) * (qq ^ 2 + nn ^ 2) - 1) = 0 := by
    linear_combination qq_quartic - nn_quartic
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' hne
  · linarith [sub_eq_zero.mp h']

/-- Vieta product form: `Q·r₂·((Q + r₂)² − Q·r₂) = −1`. -/
private lemma quartic_prod : qq * nn * ((qq + nn) ^ 2 - qq * nn) = -1 := by
  linear_combination (-1 / 2 : ℝ) * qq_quartic + (-1 / 2 : ℝ) * nn_quartic
    + ((qq + nn) / 2) * quartic_key

private lemma zc_disc_pos : 0 < 3 * (qq + nn) ^ 2 / 4 - qq * nn := by
  have hm : qq * nn < 0 :=
    mul_neg_of_pos_of_neg (lt_trans one_pos qq_gt_one) nn_neg
  nlinarith [sq_nonneg (qq + nn)]

private noncomputable def zc : ℂ :=
  ((-(qq + nn) / 2 : ℝ) : ℂ)
    + ((Real.sqrt (3 * (qq + nn) ^ 2 / 4 - qq * nn) : ℝ) : ℂ) * Complex.I

private lemma zc_re : zc.re = -(qq + nn) / 2 := by
  simp [zc]

/-- The Vieta modulus of the quartic pair: `|z|² = (Q + r₂)² − Q·r₂`. -/
private lemma normSq_zc : Complex.normSq zc = (qq + nn) ^ 2 - qq * nn := by
  have hd2 : (Real.sqrt (3 * (qq + nn) ^ 2 / 4 - qq * nn)) ^ 2
      = 3 * (qq + nn) ^ 2 / 4 - qq * nn := Real.sq_sqrt zc_disc_pos.le
  unfold zc
  rw [Complex.normSq_add_mul_I]
  nlinarith [hd2]

/-! ### The conjugates -/

private noncomputable def sgb : ℂ := (starRingEnd ℂ) sig
private noncomputable def zcb : ℂ := (starRingEnd ℂ) zc

private lemma normSq_sgb : Complex.normSq sgb = rr ^ 2 - 1 := by
  rw [sgb, Complex.normSq_conj, normSq_sig]

private lemma normSq_zcb : Complex.normSq zcb = (qq + nn) ^ 2 - qq * nn := by
  rw [zcb, Complex.normSq_conj, normSq_zc]

/-- `σ̄` is the third root of the cubic: `σ̄ = −(ρ + σ)`. -/
private lemma sgb_eq_neg : sgb = -((rr : ℂ) + sig) := by
  apply Complex.ext
  · simp only [sgb, Complex.conj_re, sig_re, Complex.neg_re, Complex.add_re,
      Complex.ofReal_re]
    ring
  · simp only [sgb, Complex.conj_im, Complex.neg_im, Complex.add_im, Complex.ofReal_im]
    ring

/-- Sum of the quartic's complex pair: `z + z̄ = −(Q + r₂)`. -/
private lemma zc_add_zcb : zc + zcb = -(((qq : ℝ) : ℂ) + ((nn : ℝ) : ℂ)) := by
  rw [zcb, Complex.add_conj, zc_re]
  push_cast
  ring

/-- Product of the quartic's complex pair: `z·z̄ = (Q + r₂)² − Q·r₂`. -/
private lemma zc_mul_zcb : zc * zcb = ((qq : ℂ) + (nn : ℂ)) ^ 2 - (qq : ℂ) * (nn : ℂ) := by
  rw [zcb, Complex.mul_conj, normSq_zc]
  push_cast
  ring

/-- Product of the cubic's complex pair: `σ·σ̄ = ρ² − 1`. -/
private lemma sig_mul_sgb : sig * sgb = (rr : ℂ) ^ 2 - 1 := by
  rw [sgb, Complex.mul_conj, normSq_sig]
  push_cast
  ring

private lemma rr_cubicC : ((rr : ℝ) : ℂ) ^ 3 = (rr : ℂ) + 1 := by exact_mod_cast rr_cubic

/-! ### Exact interval arithmetic over the certified brackets -/

private lemma rr2_bounds : 17424 / 10000 < rr ^ 2 ∧ rr ^ 2 < 17689 / 10000 := by
  obtain ⟨h1, h2⟩ := rr_bounds
  constructor <;> nlinarith

private lemma qq2_bounds : 14884 / 10000 < qq ^ 2 ∧ qq ^ 2 < 15129 / 10000 := by
  obtain ⟨h1, h2⟩ := qq_bounds
  constructor <;> nlinarith

private lemma nn2_bounds : 5184 / 10000 < nn ^ 2 ∧ nn ^ 2 < 5329 / 10000 := by
  obtain ⟨h1, h2⟩ := nn_bounds
  constructor <;> nlinarith

private lemma c_bounds :
    11185 / 10000 < (qq + nn) ^ 2 - qq * nn ∧ (qq + nn) ^ 2 - qq * nn < 1158 / 1000 := by
  obtain ⟨hq1, hq2⟩ := qq_bounds
  obtain ⟨hn1, hn2⟩ := nn_bounds
  have hp1 : 49 / 100 < qq + nn := by linarith
  have hp2 : qq + nn < 51 / 100 := by linarith
  have hm1 : 8784 / 10000 < -(qq * nn) := by nlinarith
  have hm2 : -(qq * nn) < 8979 / 10000 := by nlinarith
  constructor <;> nlinarith

/-- `|ρQ|² > 1`. -/
private lemma val_rQ_gt : 1 < rr ^ 2 * qq ^ 2 := by
  nlinarith [rr2_bounds.1, qq2_bounds.1]

/-- `|ρz|² = |ρz̄|² > 1`. -/
private lemma val_rz_gt : 1 < rr ^ 2 * ((qq + nn) ^ 2 - qq * nn) := by
  nlinarith [rr2_bounds.1, c_bounds.1]

/-- `|σQ|² = |σ̄Q|² > 1`. -/
private lemma val_sQ_gt : 1 < (rr ^ 2 - 1) * qq ^ 2 := by
  nlinarith [rr2_bounds.1, qq2_bounds.1]

/-- `|ρr₂|² < 1` — the near-miss. -/
private lemma val_rn_lt : rr ^ 2 * nn ^ 2 < 1 := by
  nlinarith [rr2_bounds.2, nn2_bounds.2, rr2_bounds.1, nn2_bounds.1]

/-- `|σr₂|² = |σ̄r₂|² < 1`. -/
private lemma val_sn_lt : (rr ^ 2 - 1) * nn ^ 2 < 1 := by
  nlinarith [rr2_bounds.2, nn2_bounds.2, rr2_bounds.1, nn2_bounds.1]

/-- `|σz|² = |σz̄|² = |σ̄z|² = |σ̄z̄|² < 1`. -/
private lemma val_sz_lt : (rr ^ 2 - 1) * ((qq + nn) ^ 2 - qq * nn) < 1 := by
  nlinarith [rr2_bounds.2, c_bounds.2, rr2_bounds.1, c_bounds.1]

/-! ### Norm conversion helpers -/

private lemma one_le_norm {ζ : ℂ} (h : 1 < Complex.normSq ζ) : (1 : ℝ) ≤ ‖ζ‖ := by
  nlinarith [Complex.norm_mul_self_eq_normSq ζ, norm_nonneg ζ]

private lemma norm_le_one {ζ : ℂ} (h : Complex.normSq ζ < 1) : ‖ζ‖ ≤ 1 := by
  nlinarith [Complex.norm_mul_self_eq_normSq ζ, norm_nonneg ζ]

private lemma normSq_ofReal' (x : ℝ) : Complex.normSq (x : ℂ) = x ^ 2 := by
  rw [Complex.normSq_ofReal]; ring

/-! ### The linear factorization of the mapped polynomials -/

/-- The quartic's complex pair, split off: for every `w`,
`(x − wz)(x − wz̄) = x² + w(Q+r₂)x + w²((Q+r₂)² − Q·r₂)`. -/
private lemma quartic_pair_split (x w : ℂ) :
    (x - w * zc) * (x - w * zcb)
      = x ^ 2 + w * ((qq : ℂ) + (nn : ℂ)) * x
        + w ^ 2 * (((qq : ℂ) + (nn : ℂ)) ^ 2 - (qq : ℂ) * (nn : ℂ)) := by
  linear_combination (-(w * x)) * zc_add_zcb + w ^ 2 * zc_mul_zcb

/-- **The scaled quartic split.**  For EVERY `w : ℂ`, the four products of `w`
with the quartic roots are the roots of `x⁴ − w³x − w⁴`:
`(x − wQ)(x − wr₂)(x − wz)(x − wz̄) = x⁴ − w³x − w⁴`. -/
private lemma scaled_quartic_split (w x : ℂ) :
    (x - w * (qq : ℂ)) * (x - w * (nn : ℂ)) * (x - w * zc) * (x - w * zcb)
      = x ^ 4 - w ^ 3 * x - w ^ 4 := by
  have hkeyC : ((qq : ℂ) + (nn : ℂ)) * ((qq : ℂ) ^ 2 + (nn : ℂ) ^ 2) = 1 := by
    exact_mod_cast quartic_key
  have hprodC : (qq : ℂ) * (nn : ℂ) * (((qq : ℂ) + (nn : ℂ)) ^ 2 - (qq : ℂ) * (nn : ℂ))
      = -1 := by exact_mod_cast quartic_prod
  linear_combination ((x - w * (qq : ℂ)) * (x - w * (nn : ℂ))) * quartic_pair_split x w
    + (-(w ^ 3 * x)) * hkeyC + w ^ 4 * hprodC

/-- The twelve-fold evaluation identity: `rulerPoly` at `x` is the product of
the twelve linear factors `x − w·z`. -/
private lemma eval_identity (x : ℂ) :
    x ^ 12 - 3 * x ^ 9 - 2 * x ^ 8 + 2 * x ^ 6 - x ^ 5 - 3 * x ^ 4 - x ^ 3 + x - 1
      = ((x - (rr : ℂ) * (qq : ℂ)) * (x - (rr : ℂ) * (nn : ℂ)) * (x - (rr : ℂ) * zc)
            * (x - (rr : ℂ) * zcb))
          * ((x - sig * (qq : ℂ)) * (x - sig * (nn : ℂ)) * (x - sig * zc) * (x - sig * zcb))
          * ((x - sgb * (qq : ℂ)) * (x - sgb * (nn : ℂ)) * (x - sgb * zc) * (x - sgb * zcb)) := by
  have hfac := ruler_factorization x ((rr : ℝ) : ℂ) sig rr_cubicC sig_quadratic
  rw [scaled_quartic_split ((rr : ℝ) : ℂ) x, scaled_quartic_split sig x,
    scaled_quartic_split sgb x, sgb_eq_neg]
  linear_combination hfac

/-- **The linear factorization of `rulerPoly` over `ℂ`**, as a polynomial
identity: the mapped polynomial is the product of the twelve explicit linear
factors `X − w·z`. -/
private lemma map_rulerPoly_factor :
    rulerPoly.map (algebraMap ℚ ℂ)
      = (((X : ℂ[X]) - C ((rr : ℂ) * (qq : ℂ))) * (X - C ((rr : ℂ) * (nn : ℂ)))
            * (X - C ((rr : ℂ) * zc)) * (X - C ((rr : ℂ) * zcb)))
          * ((X - C (sig * (qq : ℂ))) * (X - C (sig * (nn : ℂ)))
            * (X - C (sig * zc)) * (X - C (sig * zcb)))
          * ((X - C (sgb * (qq : ℂ))) * (X - C (sgb * (nn : ℂ)))
            * (X - C (sgb * zc)) * (X - C (sgb * zcb))) := by
  apply Polynomial.funext
  intro x
  rw [eval_map_algebraMap, aeval_rulerPoly_eq]
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  exact eval_identity x

/-- The linear factorization of the quartic over `ℂ`. -/
private lemma map_quartic_factor :
    (X ^ 4 - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ)
      = ((X : ℂ[X]) - C ((qq : ℂ))) * (X - C ((nn : ℂ))) * (X - C zc) * (X - C zcb) := by
  apply Polynomial.funext
  intro x
  rw [eval_map_algebraMap]
  simp only [map_sub, map_pow, map_one, aeval_X, eval_mul, eval_sub, eval_X, eval_C]
  linear_combination (-1 : ℂ) * scaled_quartic_split 1 x

/-! ### The norms of the twelve roots against the unit circle -/

private lemma ge_rQ : (1 : ℝ) ≤ ‖(rr : ℂ) * (qq : ℂ)‖ :=
  one_le_norm (by simp only [Complex.normSq_mul, normSq_ofReal']; exact val_rQ_gt)

private lemma ge_rz : (1 : ℝ) ≤ ‖(rr : ℂ) * zc‖ :=
  one_le_norm (by simp only [Complex.normSq_mul, normSq_ofReal', normSq_zc]; exact val_rz_gt)

private lemma ge_rzb : (1 : ℝ) ≤ ‖(rr : ℂ) * zcb‖ :=
  one_le_norm (by simp only [Complex.normSq_mul, normSq_ofReal', normSq_zcb]; exact val_rz_gt)

private lemma ge_sQ : (1 : ℝ) ≤ ‖sig * (qq : ℂ)‖ :=
  one_le_norm (by simp only [Complex.normSq_mul, normSq_ofReal', normSq_sig]; exact val_sQ_gt)

private lemma ge_sbQ : (1 : ℝ) ≤ ‖sgb * (qq : ℂ)‖ :=
  one_le_norm (by simp only [Complex.normSq_mul, normSq_ofReal', normSq_sgb]; exact val_sQ_gt)

private lemma le_rn : ‖(rr : ℂ) * (nn : ℂ)‖ ≤ 1 :=
  norm_le_one (by simp only [Complex.normSq_mul, normSq_ofReal']; exact val_rn_lt)

private lemma le_sn : ‖sig * (nn : ℂ)‖ ≤ 1 :=
  norm_le_one (by simp only [Complex.normSq_mul, normSq_ofReal', normSq_sig]; exact val_sn_lt)

private lemma le_sbn : ‖sgb * (nn : ℂ)‖ ≤ 1 :=
  norm_le_one (by simp only [Complex.normSq_mul, normSq_ofReal', normSq_sgb]; exact val_sn_lt)

private lemma le_sz : ‖sig * zc‖ ≤ 1 :=
  norm_le_one (by simp only [Complex.normSq_mul, normSq_sig, normSq_zc]; exact val_sz_lt)

private lemma le_szb : ‖sig * zcb‖ ≤ 1 :=
  norm_le_one (by simp only [Complex.normSq_mul, normSq_sig, normSq_zcb]; exact val_sz_lt)

private lemma le_sbz : ‖sgb * zc‖ ≤ 1 :=
  norm_le_one (by simp only [Complex.normSq_mul, normSq_sgb, normSq_zc]; exact val_sz_lt)

private lemma le_sbzb : ‖sgb * zcb‖ ≤ 1 :=
  norm_le_one (by simp only [Complex.normSq_mul, normSq_sgb, normSq_zcb]; exact val_sz_lt)

private lemma ge_q : (1 : ℝ) ≤ ‖((qq : ℝ) : ℂ)‖ :=
  one_le_norm (by rw [normSq_ofReal']; nlinarith [qq2_bounds.1])

private lemma le_n : ‖((nn : ℝ) : ℂ)‖ ≤ 1 :=
  norm_le_one (by rw [normSq_ofReal']; nlinarith [nn2_bounds.2])

private lemma ge_z : (1 : ℝ) ≤ ‖zc‖ :=
  one_le_norm (by rw [normSq_zc]; nlinarith [c_bounds.1])

private lemma ge_zb : (1 : ℝ) ≤ ‖zcb‖ :=
  one_le_norm (by rw [normSq_zcb]; nlinarith [c_bounds.1])

/-! ### The norm values of the outside roots -/

private lemma norm_rQ : ‖(rr : ℂ) * (qq : ℂ)‖ = rr * qq := by
  rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos rr_pos qq_pos)]

private lemma norm_q : ‖((qq : ℝ) : ℂ)‖ = qq := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos qq_pos]

private lemma norm_pair_rz : ‖(rr : ℂ) * zc‖ * ‖(rr : ℂ) * zcb‖
    = rr ^ 2 * ((qq + nn) ^ 2 - qq * nn) := by
  have hpos : 0 < rr ^ 2 * ((qq + nn) ^ 2 - qq * nn) := by
    nlinarith [rr2_bounds.1, c_bounds.1]
  have h : ((rr : ℂ) * zc) * ((rr : ℂ) * zcb)
      = ((rr ^ 2 * ((qq + nn) ^ 2 - qq * nn) : ℝ) : ℂ) := by
    push_cast
    linear_combination ((rr : ℝ) : ℂ) ^ 2 * zc_mul_zcb
  rw [← norm_mul, h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

private lemma norm_pair_sQ : ‖sig * (qq : ℂ)‖ * ‖sgb * (qq : ℂ)‖
    = (rr ^ 2 - 1) * qq ^ 2 := by
  have hpos : 0 < (rr ^ 2 - 1) * qq ^ 2 := by
    nlinarith [rr2_bounds.1, qq2_bounds.1]
  have h : (sig * (qq : ℂ)) * (sgb * (qq : ℂ)) = (((rr ^ 2 - 1) * qq ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination ((qq : ℝ) : ℂ) ^ 2 * sig_mul_sgb
  rw [← norm_mul, h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

private lemma norm_pair_z : ‖zc‖ * ‖zcb‖ = (qq + nn) ^ 2 - qq * nn := by
  have hpos : 0 < (qq + nn) ^ 2 - qq * nn := by linarith [c_bounds.1]
  have h : zc * zcb = (((qq + nn) ^ 2 - qq * nn : ℝ) : ℂ) := by
    push_cast
    exact zc_mul_zcb
  rw [← norm_mul, h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

/-! ### The Mahler measures, in internal witness form -/

/-- `M(rulerPoly) = ρQ · |ρz|² · |σQ|²` — the outside product, with the two
conjugate pairs collapsed by their Vieta moduli. -/
private lemma mahler_internal :
    (rulerPoly.map (algebraMap ℚ ℂ)).mahlerMeasure
      = rr * qq * (rr ^ 2 * ((qq + nn) ^ 2 - qq * nn)) * ((rr ^ 2 - 1) * qq ^ 2) := by
  rw [map_rulerPoly_factor]
  simp only [mahlerMeasure_mul, mahlerMeasure_X_sub_C]
  rw [max_eq_right ge_rQ, max_eq_left le_rn, max_eq_right ge_rz, max_eq_right ge_rzb,
    max_eq_right ge_sQ, max_eq_left le_sn, max_eq_left le_sz, max_eq_left le_szb,
    max_eq_right ge_sbQ, max_eq_left le_sbn, max_eq_left le_sbz, max_eq_left le_sbzb]
  simp only [mul_one]
  linear_combination
    (‖(rr : ℂ) * zc‖ * ‖(rr : ℂ) * zcb‖ * (‖sig * (qq : ℂ)‖ * ‖sgb * (qq : ℂ)‖)) * norm_rQ
      + (rr * qq * (‖sig * (qq : ℂ)‖ * ‖sgb * (qq : ℂ)‖)) * norm_pair_rz
      + (rr * qq * (rr ^ 2 * ((qq + nn) ^ 2 - qq * nn))) * norm_pair_sQ

/-- `M(X⁴ − X − 1) = Q · |z|²` — the outside product of the quartic. -/
private lemma quartic_mahler_internal :
    ((X ^ 4 - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure
      = qq * ((qq + nn) ^ 2 - qq * nn) := by
  rw [map_quartic_factor]
  simp only [mahlerMeasure_mul, mahlerMeasure_X_sub_C]
  rw [max_eq_right ge_q, max_eq_left le_n, max_eq_right ge_z, max_eq_right ge_zb]
  simp only [mul_one]
  linear_combination (‖zc‖ * ‖zcb‖) * norm_q + qq * norm_pair_z

/-! ### The `ψ`-connection: `x ↦ −1/x` carries `x⁴ − x − 1` to `x⁴ − x³ − 1` -/

/-- Any real root `> 1` of `ψ⁴ = ψ³ + 1` is `−1/r₂`: `ψ·r₂ = −1`. -/
private lemma psi_nn_link {psi : ℝ} (hpsi : psi ^ 4 = psi ^ 3 + 1) (hpsi1 : 1 < psi) :
    psi * nn = -1 := by
  have hpos : 0 < psi := lt_trans one_pos hpsi1
  have hpsi0 : psi ≠ 0 := ne_of_gt hpos
  have hquart : (-psi⁻¹) ^ 4 = -psi⁻¹ + 1 := by
    field_simp
    linear_combination -hpsi
  have h0 : -psi⁻¹ < 0 := neg_lt_zero.mpr (inv_pos.mpr hpos)
  have hnn : nn = -psi⁻¹ := quartic_neg_unique nn_quartic nn_neg hquart h0
  rw [hnn, mul_neg, mul_inv_cancel₀ hpsi0]

/-- **Non-vacuity of the `ψ`-equation**: `ψ⁴ = ψ³ + 1` has a real root `> 1`
(namely `−1/r₂` for the quartic's negative root `r₂`). -/
theorem exists_psi_root : ∃ x : ℝ, x ^ 4 = x ^ 3 + 1 ∧ 1 < x := by
  have hnn0 : nn ≠ 0 := ne_of_lt nn_neg
  have h : 0 < -nn := neg_pos.mpr nn_neg
  have h2 : -nn < 1 := by linarith [nn_bounds.1]
  refine ⟨-nn⁻¹, ?_, ?_⟩
  · field_simp
    linear_combination -nn_quartic
  · have h3 : -nn * (-nn)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h)
    have h4 : (-nn)⁻¹ = -nn⁻¹ := by
      field_simp
    nlinarith [h3, h4, inv_pos.mpr h]

/-! ### The public theorems -/

/-- **The Mahler measure of the quartic.**  `M(X⁴ − X − 1) = ψ`, where `ψ`
is the real root `> 1` of `ψ⁴ = ψ³ + 1`: the transform `x ↦ −1/x` carries
`x⁴ − x − 1` to `x⁴ − x³ − 1`, and the quartic's Mahler measure
`Q·|z|² = −1/r₂` is exactly that root.  This is the degree-4 registry-bridge
quantity. -/
theorem quartic_mahler_measure {psi : ℝ} (hpsi : psi ^ 4 = psi ^ 3 + 1)
    (hpsi1 : 1 < psi) :
    ((X ^ 4 - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure = psi := by
  rw [quartic_mahler_internal]
  have hlink : psi * nn = -1 := psi_nn_link hpsi hpsi1
  have hnn0 : nn ≠ 0 := ne_of_lt nn_neg
  have key : nn * (qq * ((qq + nn) ^ 2 - qq * nn) - psi) = 0 := by
    linear_combination quartic_prod - hlink
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hnn0
  · exact sub_eq_zero.mp h

/-- **The Mahler measure of the ruler minimal polynomial.**
`M(rulerPoly) = ρ²·Q²·ψ`: the product of `max 1 ‖ζ‖` over the twelve
conjugates of `ρQ` collapses, via `|σ|² = ρ² − 1 = 1/ρ` and `Q·r₂·|z|² = −1`,
to `ρQ · |ρz|² · |σQ|² = ρ²Q²/(−r₂) = ρ²·Q²·ψ`. -/
theorem ruler_mahler_measure {rho QQ psi : ℝ} (hr : rho ^ 3 = rho + 1)
    (hq : QQ ^ 4 = QQ + 1) (hq1 : 1 < QQ)
    (hpsi : psi ^ 4 = psi ^ 3 + 1) (hpsi1 : 1 < psi) :
    (rulerPoly.map (algebraMap ℚ ℂ)).mahlerMeasure = rho ^ 2 * QQ ^ 2 * psi := by
  have hrho : rho = rr := cubic_unique hr rr_cubic
  have hQQ : QQ = qq := quartic_pos_unique hq hq1 qq_quartic qq_gt_one
  subst hrho hQQ
  rw [mahler_internal]
  have hlink : psi * nn = -1 := psi_nn_link hpsi hpsi1
  have hnn0 : nn ≠ 0 := ne_of_lt nn_neg
  have hq0 : qq ≠ 0 := ne_of_gt qq_pos
  have key : (qq * nn) * (rr * qq * (rr ^ 2 * ((qq + nn) ^ 2 - qq * nn))
      * ((rr ^ 2 - 1) * qq ^ 2) - rr ^ 2 * qq ^ 2 * psi) = 0 := by
    linear_combination (rr ^ 3 * (rr ^ 2 - 1) * qq ^ 3) * quartic_prod
      - (qq ^ 3 * rr ^ 2) * rr_cubic - (rr ^ 2 * qq ^ 3) * hlink
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (mul_ne_zero hq0 hnn0)
  · exact sub_eq_zero.mp h

/-- **The Mahler measure of the minimal polynomial of the ruler product**, in
minpoly form: `M(minpoly ℚ (ρQ)) = ρ²·Q²·ψ`. -/
theorem ruler_minpoly_mahler_measure {rho QQ psi : ℝ} (hr : rho ^ 3 = rho + 1)
    (hq : QQ ^ 4 = QQ + 1) (hq1 : 1 < QQ)
    (hpsi : psi ^ 4 = psi ^ 3 + 1) (hpsi1 : 1 < psi) :
    ((minpoly ℚ (rho * QQ)).map (algebraMap ℚ ℂ)).mahlerMeasure
      = rho ^ 2 * QQ ^ 2 * psi := by
  rw [ruler_minpoly hr hq]
  exact ruler_mahler_measure hr hq hq1 hpsi hpsi1

/-- **The registry bridge, as a product identity.**
`M(rulerPoly) = (ρQ)² · M(X⁴ − X − 1)`: the Mahler measure of the degree-12
ruler minimal polynomial is exactly `(ρQ)²` times the Mahler measure of the
PDT quartic — the degree-4 minimal measure candidate. -/
theorem ruler_mahler_eq_quartic_measure {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1)
    (hq : QQ ^ 4 = QQ + 1) (hq1 : 1 < QQ) :
    (rulerPoly.map (algebraMap ℚ ℂ)).mahlerMeasure
      = (rho * QQ) ^ 2 * ((X ^ 4 - X - 1 : ℚ[X]).map (algebraMap ℚ ℂ)).mahlerMeasure := by
  have hrho : rho = rr := cubic_unique hr rr_cubic
  have hQQ : QQ = qq := quartic_pos_unique hq hq1 qq_quartic qq_gt_one
  subst hrho hQQ
  rw [mahler_internal, quartic_mahler_internal]
  linear_combination (rr ^ 2 * qq ^ 3 * ((qq + nn) ^ 2 - qq * nn)) * rr_cubic

/-- **The Mahler measure of `rulerPoly` exceeds `1`.** -/
theorem ruler_mahler_gt_one : 1 < (rulerPoly.map (algebraMap ℚ ℂ)).mahlerMeasure := by
  rw [mahler_internal]
  have h1 : 1 < rr * qq := by nlinarith [rr_bounds.1, qq_bounds.1]
  have h2 := val_rz_gt
  have h3 := val_sQ_gt
  have h12 : 1 < rr * qq * (rr ^ 2 * ((qq + nn) ^ 2 - qq * nn)) := by nlinarith [h1, h2]
  nlinarith [h12, h3]

end RulerMeasure
end PDT

/-! ### Axiom audit — every public result rests on the kernel alone -/

#print axioms PDT.RulerMeasure.exists_psi_root
#print axioms PDT.RulerMeasure.quartic_mahler_measure
#print axioms PDT.RulerMeasure.ruler_mahler_measure
#print axioms PDT.RulerMeasure.ruler_minpoly_mahler_measure
#print axioms PDT.RulerMeasure.ruler_mahler_eq_quartic_measure
#print axioms PDT.RulerMeasure.ruler_mahler_gt_one
