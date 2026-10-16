module
public import PdtRulerMinpoly

@[expose] public section
/-!
# PdtRulerCensus — the unit-circle census of the conjugates of `ρQ`

Let `ρ` be the real root of `x³ = x + 1` and `Q` the real root `> 1` of
`x⁴ = x + 1`.  `PdtRulerMinpoly` identifies the twelve complex roots of
`minpoly ℚ (ρQ)` as exactly the products `w·z` of a root of the cubic with a
root of the quartic.  This module completes the geometry:

* `ruler_conjugate_census` — of those twelve roots, EXACTLY 5 have modulus
  `> 1`, EXACTLY 7 have modulus `< 1`, and NONE lies on the unit circle.
* `ruler_house` — every root `ζ ≠ ρQ` has `‖ζ‖ < ρQ`: the ruler product is
  the dominant root of its own minimal polynomial (the house of the algebraic
  unit `ρQ` is `ρQ` itself).

All classification inequalities are exact-rational interval arithmetic over
certified brackets for the three real roots (`ρ`, `Q`, and the quartic's
negative root `r₂`), driven by `nlinarith` from the defining equations; the
moduli come from the Vieta closed forms `|σ|² = ρ² − 1` (cubic pair) and
`|z|² = (Q + r₂)² − Q·r₂` (quartic pair).  No numerics enter the kernel.
-/

namespace PDT
namespace RulerCensus

open Polynomial Complex PDT.RulerMinpoly

/-! ### Brackets for the three real roots -/

/-- Any real root of the cubic exceeds `1`. -/
private lemma cubic_gt_one {a : ℝ} (ha : a ^ 3 = a + 1) : 1 < a := by
  nlinarith [sq_nonneg (a + 9 / 10), sq_nonneg (a + 1 / 160), sq_nonneg a]

/-- Bracket for the cubic root: `1.32 < ρ < 1.33`. -/
private lemma cubic_bounds {a : ℝ} (ha : a ^ 3 = a + 1) :
    132 / 100 < a ∧ a < 133 / 100 := by
  have h1 : 1 < a := cubic_gt_one ha
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg (a - 1), sq_nonneg (a + 1)]

/-- Bracket for the positive quartic root: `1.22 < Q < 1.23`. -/
private lemma quartic_pos_bounds {b : ℝ} (hb : b ^ 4 = b + 1) (h1 : 1 < b) :
    122 / 100 < b ∧ b < 123 / 100 := by
  constructor <;>
    nlinarith [sq_nonneg b, sq_nonneg (b - 1), sq_nonneg (b + 1), sq_nonneg (b ^ 2 - 1),
      sq_nonneg (b ^ 2 - b)]

/-- Bracket for the negative quartic root: `−0.73 < r₂ < −0.72`. -/
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

/-! ### Uniqueness of the real roots -/

/-- The real root of the cubic is unique. -/
private lemma cubic_unique {a b : ℝ} (ha : a ^ 3 = a + 1) (hb : b ^ 3 = b + 1) : a = b := by
  have h1 : 1 < a := cubic_gt_one ha
  have h2 : 1 < b := cubic_gt_one hb
  have key : (a - b) * (a ^ 2 + a * b + b ^ 2 - 1) = 0 := by linear_combination ha - hb
  have hpos : 0 < a ^ 2 + a * b + b ^ 2 - 1 := by nlinarith
  have := mul_eq_zero.mp key
  rcases this with h | h
  · linarith [sub_eq_zero.mp h]
  · exact absurd h (ne_of_gt hpos)

/-- The real root `> 1` of the quartic is unique. -/
private lemma quartic_pos_unique {a b : ℝ} (ha : a ^ 4 = a + 1) (h1 : 1 < a)
    (hb : b ^ 4 = b + 1) (h2 : 1 < b) : a = b := by
  have key : (a - b) * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 - 1) = 0 := by
    linear_combination ha - hb
  have hpos : 0 < a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 - 1 := by nlinarith
  rcases mul_eq_zero.mp key with h | h
  · linarith [sub_eq_zero.mp h]
  · exact absurd h (ne_of_gt hpos)

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

/-! ### The complex cubic root `σ` (positive imaginary part) -/

/-- `σ`, the root of the cubic in the upper half plane:
`σ = −ρ/2 + i·√(3ρ² − 4)/2`. -/
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

/-- `σ` is a root of the cubic. -/
private lemma sig_cubic : sig ^ 3 = sig + 1 := by
  have hrC : ((rr : ℝ) : ℂ) ^ 3 = (rr : ℂ) + 1 := by exact_mod_cast rr_cubic
  exact cubic_of_quadratic (rr : ℂ) sig hrC sig_quadratic

private lemma sig_im : sig.im = Real.sqrt (3 * rr ^ 2 - 4) / 2 := by
  simp [sig]

private lemma sig_im_pos : 0 < sig.im := by
  rw [sig_im]
  exact div_pos (Real.sqrt_pos.mpr sig_disc_pos) two_pos

private lemma sig_re : sig.re = -rr / 2 := by
  simp [sig]

/-- The Vieta modulus of the cubic pair: `|σ|² = ρ² − 1`. -/
private lemma normSq_sig : Complex.normSq sig = rr ^ 2 - 1 := by
  have hd2 : (Real.sqrt (3 * rr ^ 2 - 4)) ^ 2 = 3 * rr ^ 2 - 4 :=
    Real.sq_sqrt sig_disc_pos.le
  unfold sig
  rw [Complex.normSq_add_mul_I]
  nlinarith [hd2]

private lemma sig_ne_zero : sig ≠ 0 := by
  intro h
  have := sig_im_pos
  rw [h] at this
  simp at this

/-! ### The complex quartic root `z` (positive imaginary part) -/

/-- Newton–Vieta for the two real quartic roots: `(Q + r₂)(Q² + r₂²) = 1`. -/
private lemma quartic_key : (qq + nn) * (qq ^ 2 + nn ^ 2) = 1 := by
  have hne : qq - nn ≠ 0 := by
    have := qq_gt_one; have := nn_neg; intro h; linarith [sub_eq_zero.mp h]
  have h : (qq - nn) * ((qq + nn) * (qq ^ 2 + nn ^ 2) - 1) = 0 := by
    linear_combination qq_quartic - nn_quartic
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' hne
  · linarith [sub_eq_zero.mp h']

/-- Vieta product form: `Q·r₂·((Q + r₂)² − Q·r₂) = −1`, i.e. the quartic's
complex pair has `|z|² = (Q + r₂)² − Q·r₂` with `Q·r₂·|z|² = −1`. -/
private lemma quartic_prod : qq * nn * ((qq + nn) ^ 2 - qq * nn) = -1 := by
  linear_combination (-1 / 2 : ℝ) * qq_quartic + (-1 / 2 : ℝ) * nn_quartic
    + ((qq + nn) / 2) * quartic_key

/-- Any root of the quadratic cofactor `y² + (q+r)y + ((q+r)² − qr)` of the
quartic is itself a quartic root, given the two Vieta identities. -/
private lemma quartic_of_quadratic {q r y : ℂ} (hkey : (q + r) * (q ^ 2 + r ^ 2) = 1)
    (hprod : q * r * ((q + r) ^ 2 - q * r) = -1)
    (hy : y ^ 2 + (q + r) * y + ((q + r) ^ 2 - q * r) = 0) : y ^ 4 = y + 1 := by
  linear_combination (y ^ 2 - (q + r) * y + q * r) * hy + y * hkey - hprod

private lemma zc_disc_pos : 0 < 3 * (qq + nn) ^ 2 / 4 - qq * nn := by
  have hm : qq * nn < 0 :=
    mul_neg_of_pos_of_neg (lt_trans one_pos qq_gt_one) nn_neg
  nlinarith [sq_nonneg (qq + nn)]

/-- `z`, the root of the quartic in the upper half plane:
`z = −(Q + r₂)/2 + i·√(3(Q + r₂)²/4 − Q·r₂)`. -/
private noncomputable def zc : ℂ :=
  ((-(qq + nn) / 2 : ℝ) : ℂ)
    + ((Real.sqrt (3 * (qq + nn) ^ 2 / 4 - qq * nn) : ℝ) : ℂ) * Complex.I

/-- `z` satisfies the quadratic cofactor of the quartic. -/
private lemma zc_quadratic :
    zc ^ 2 + ((qq : ℂ) + (nn : ℂ)) * zc + (((qq : ℂ) + (nn : ℂ)) ^ 2 - (qq : ℂ) * (nn : ℂ))
      = 0 := by
  have hd2 : (Real.sqrt (3 * (qq + nn) ^ 2 / 4 - qq * nn)) ^ 2
      = 3 * (qq + nn) ^ 2 / 4 - qq * nn := Real.sq_sqrt zc_disc_pos.le
  have hd2C : ((Real.sqrt (3 * (qq + nn) ^ 2 / 4 - qq * nn) : ℝ) : ℂ) ^ 2
      = 3 * ((qq : ℂ) + (nn : ℂ)) ^ 2 / 4 - (qq : ℂ) * (nn : ℂ) := by exact_mod_cast hd2
  have hI : (Complex.I) ^ 2 = -1 := Complex.I_sq
  unfold zc
  push_cast
  linear_combination (((Real.sqrt (3 * (qq + nn) ^ 2 / 4 - qq * nn) : ℝ) : ℂ) ^ 2) * hI
    - hd2C

/-- `z` is a root of the quartic. -/
private lemma zc_quartic : zc ^ 4 = zc + 1 := by
  have hkeyC : ((qq : ℂ) + (nn : ℂ)) * ((qq : ℂ) ^ 2 + (nn : ℂ) ^ 2) = 1 := by
    exact_mod_cast quartic_key
  have hprodC : (qq : ℂ) * (nn : ℂ) * (((qq : ℂ) + (nn : ℂ)) ^ 2 - (qq : ℂ) * (nn : ℂ))
      = -1 := by exact_mod_cast quartic_prod
  exact quartic_of_quadratic hkeyC hprodC zc_quadratic

private lemma zc_im : zc.im = Real.sqrt (3 * (qq + nn) ^ 2 / 4 - qq * nn) := by
  simp [zc]

private lemma zc_im_pos : 0 < zc.im := by
  rw [zc_im]
  exact Real.sqrt_pos.mpr zc_disc_pos

private lemma zc_re : zc.re = -(qq + nn) / 2 := by
  simp [zc]

/-- The Vieta modulus of the quartic pair: `|z|² = (Q + r₂)² − Q·r₂`. -/
private lemma normSq_zc : Complex.normSq zc = (qq + nn) ^ 2 - qq * nn := by
  have hd2 : (Real.sqrt (3 * (qq + nn) ^ 2 / 4 - qq * nn)) ^ 2
      = 3 * (qq + nn) ^ 2 / 4 - qq * nn := Real.sq_sqrt zc_disc_pos.le
  unfold zc
  rw [Complex.normSq_add_mul_I]
  nlinarith [hd2]

private lemma zc_ne_zero : zc ≠ 0 := by
  intro h
  have := zc_im_pos
  rw [h] at this
  simp at this

/-! ### Conjugation and membership plumbing -/

private lemma conj_cubic {w : ℂ} (hw : w ^ 3 = w + 1) :
    (starRingEnd ℂ) w ^ 3 = (starRingEnd ℂ) w + 1 := by
  rw [← map_pow, hw, map_add, map_one]

private lemma conj_quartic {z : ℂ} (hz : z ^ 4 = z + 1) :
    (starRingEnd ℂ) z ^ 4 = (starRingEnd ℂ) z + 1 := by
  rw [← map_pow, hz, map_add, map_one]

/-- The root set of `rulerPoly` in `ℂ`, as a finset. -/
private noncomputable def RF : Finset ℂ := (rulerPoly.rootSet ℂ).toFinset

private lemma RF_card : RF.card = 12 := by
  rw [RF, Set.toFinset_card]
  exact ruler_conjugates_card

private lemma mem_RF {ζ : ℂ} : ζ ∈ RF ↔ ζ ∈ rulerPoly.rootSet ℂ := by
  rw [RF, Set.mem_toFinset]

/-- Every product of a cubic root with a quartic root is a conjugate of `ρQ`. -/
private lemma prod_mem {w z : ℂ} (hw : w ^ 3 = w + 1) (hz : z ^ 4 = z + 1) :
    w * z ∈ RF := by
  rw [mem_RF, Polynomial.mem_rootSet]
  exact ⟨rulerPoly_ne_zero, aeval_rulerPoly w z hw hz⟩

private lemma one_lt_norm {ζ : ℂ} (h : 1 < Complex.normSq ζ) : 1 < ‖ζ‖ := by
  nlinarith [Complex.norm_mul_self_eq_normSq ζ, norm_nonneg ζ]

private lemma norm_lt_one {ζ : ℂ} (h : Complex.normSq ζ < 1) : ‖ζ‖ < 1 := by
  nlinarith [Complex.norm_mul_self_eq_normSq ζ, norm_nonneg ζ]

/-! ### Exact interval arithmetic over the certified brackets

`|σ|² = ρ² − 1`, `|z|² = c := (Q + r₂)² − Q·r₂`; every squared modulus of a
conjugate is a product drawn from `ρ²`, `Q²`, `r₂²`, `ρ² − 1`, `c`. -/

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

/-- `|ρr₂|² < 1` — the near-miss, margin `≈ 0.079`. -/
private lemma val_rn_lt : rr ^ 2 * nn ^ 2 < 1 := by
  nlinarith [rr2_bounds.2, nn2_bounds.2, rr2_bounds.1, nn2_bounds.1]

/-- `|σr₂|² = |σ̄r₂|² < 1`. -/
private lemma val_sn_lt : (rr ^ 2 - 1) * nn ^ 2 < 1 := by
  nlinarith [rr2_bounds.2, nn2_bounds.2, rr2_bounds.1, nn2_bounds.1]

/-- `|σz|² = |σz̄|² = |σ̄z|² = |σ̄z̄|² < 1`. -/
private lemma val_sz_lt : (rr ^ 2 - 1) * ((qq + nn) ^ 2 - qq * nn) < 1 := by
  nlinarith [rr2_bounds.2, c_bounds.2, rr2_bounds.1, c_bounds.1]

/-- Separation inside the outside class: `|σQ|² < |ρz|²`. -/
private lemma sep_sQ_lt_rz :
    (rr ^ 2 - 1) * qq ^ 2 < rr ^ 2 * ((qq + nn) ^ 2 - qq * nn) := by
  nlinarith [rr2_bounds.1, rr2_bounds.2, qq2_bounds.1, qq2_bounds.2, c_bounds.1]

/-- Separation inside the inside class: `|σz|² < |ρr₂|²`. -/
private lemma sep_sz_lt_rn :
    (rr ^ 2 - 1) * ((qq + nn) ^ 2 - qq * nn) < rr ^ 2 * nn ^ 2 := by
  nlinarith [rr2_bounds.1, rr2_bounds.2, c_bounds.1, c_bounds.2, nn2_bounds.1]

/-- Separation inside the inside class: `|σr₂|² < |σz|²`. -/
private lemma sep_sn_lt_sz :
    (rr ^ 2 - 1) * nn ^ 2 < (rr ^ 2 - 1) * ((qq + nn) ^ 2 - qq * nn) := by
  nlinarith [rr2_bounds.1, nn2_bounds.2, c_bounds.1]

/-- For the house bound: `|ρz|² < |ρQ|²` (i.e. `c < Q²`). -/
private lemma sep_rz_lt_rQ :
    rr ^ 2 * ((qq + nn) ^ 2 - qq * nn) < rr ^ 2 * qq ^ 2 := by
  nlinarith [rr2_bounds.1, c_bounds.2, qq2_bounds.1]

/-! ### The twelve conjugates, named -/

private noncomputable def sgb : ℂ := (starRingEnd ℂ) sig
private noncomputable def zcb : ℂ := (starRingEnd ℂ) zc

private lemma sgb_cubic : sgb ^ 3 = sgb + 1 := conj_cubic sig_cubic
private lemma zcb_quartic : zcb ^ 4 = zcb + 1 := conj_quartic zc_quartic

private lemma sgb_im : sgb.im = -sig.im := Complex.conj_im sig
private lemma zcb_im : zcb.im = -zc.im := Complex.conj_im zc
private lemma zcb_re : zcb.re = zc.re := Complex.conj_re zc

private lemma normSq_sgb : Complex.normSq sgb = rr ^ 2 - 1 := by
  rw [sgb, Complex.normSq_conj, normSq_sig]

private lemma normSq_zcb : Complex.normSq zcb = (qq + nn) ^ 2 - qq * nn := by
  rw [zcb, Complex.normSq_conj, normSq_zc]

private lemma sgb_ne_zero : sgb ≠ 0 := by
  rw [sgb]
  simpa using sig_ne_zero

private lemma zcb_ne_zero : zcb ≠ 0 := by
  rw [zcb]
  simpa using zc_ne_zero

private lemma sig_ne_sgb : sig ≠ sgb := by
  intro h
  have h' := congrArg Complex.im h
  rw [sgb_im] at h'
  have := sig_im_pos
  linarith

private lemma zc_ne_zcb : zc ≠ zcb := by
  intro h
  have h' := congrArg Complex.im h
  rw [zcb_im] at h'
  have := zc_im_pos
  linarith

private lemma ne_of_im {a b : ℂ} (h : a.im ≠ b.im) : a ≠ b :=
  fun e => h (by rw [e])

private lemma ne_of_normSq {a b : ℂ} (h : Complex.normSq a ≠ Complex.normSq b) : a ≠ b :=
  fun e => h (by rw [e])

private lemma normSq_ofReal' (x : ℝ) : Complex.normSq (x : ℂ) = x ^ 2 := by
  rw [Complex.normSq_ofReal]; ring

/-! ### Imaginary parts of the products -/

private lemma im_mul_real_left (x : ℝ) (w : ℂ) : ((x : ℂ) * w).im = x * w.im := by
  simp [Complex.mul_im]

private lemma im_mul_real_right (w : ℂ) (x : ℝ) : (w * (x : ℂ)).im = w.im * x := by
  simp [Complex.mul_im]

private lemma rr_pos : 0 < rr := by linarith [rr_bounds.1]
private lemma qq_pos : 0 < qq := by linarith [qq_bounds.1]
private lemma p_pos : 0 < qq + nn := by linarith [qq_bounds.1, nn_bounds.1]

/-- `Im(σz) < 0`: both contributions are negative. -/
private lemma im_sz_neg : (sig * zc).im < 0 := by
  rw [Complex.mul_im, sig_re, sig_im, zc_re, zc_im]
  have h1 : 0 < Real.sqrt (3 * rr ^ 2 - 4) / 2 := div_pos (Real.sqrt_pos.mpr sig_disc_pos) two_pos
  have h2 : 0 < Real.sqrt (3 * (qq + nn) ^ 2 / 4 - qq * nn) := Real.sqrt_pos.mpr zc_disc_pos
  have h3 := rr_pos
  have h4 := p_pos
  nlinarith

/-- `Im(σz̄) > 0`: the square comparison `4ρ²·Im(z)² > (3ρ²−4)·(Q+r₂)²`. -/
private lemma im_szb_pos : 0 < (sig * zcb).im := by
  rw [Complex.mul_im, sig_re, sig_im, zcb_im, zc_im, zcb_re, zc_re]
  set X := 3 * (qq + nn) ^ 2 / 4 - qq * nn with hXdef
  set d := 3 * rr ^ 2 - 4 with hddef
  have hX : 0 < X := zc_disc_pos
  have hd : 0 < d := sig_disc_pos
  have hsX : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX.le
  have hsd : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd.le
  have hp1 : 49 / 100 < qq + nn := by linarith [qq_bounds.1, nn_bounds.1]
  have hp2 : qq + nn < 51 / 100 := by linarith [qq_bounds.2, nn_bounds.2]
  have hm1 : 8784 / 10000 < -(qq * nn) := by
    nlinarith [qq_bounds.1, qq_bounds.2, nn_bounds.1, nn_bounds.2]
  have hsq : (Real.sqrt d * (qq + nn)) ^ 2 < (2 * rr * Real.sqrt X) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, hsX, hsd]
    nlinarith [rr2_bounds.1, rr2_bounds.2, sq_nonneg (qq + nn)]
  have hlt : Real.sqrt d * (qq + nn) < 2 * rr * Real.sqrt X := by
    nlinarith [hsq, mul_nonneg (Real.sqrt_nonneg d) (le_of_lt p_pos),
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) rr_pos.le) (Real.sqrt_nonneg X)]
  nlinarith [hlt]

/-! ### Imaginary parts and squared moduli of the twelve products -/

private lemma im_rQ : ((rr : ℂ) * (qq : ℂ)).im = 0 := by
  rw [← Complex.ofReal_mul]; exact Complex.ofReal_im _

private lemma im_rn : ((rr : ℂ) * (nn : ℂ)).im = 0 := by
  rw [← Complex.ofReal_mul]; exact Complex.ofReal_im _

private lemma im_rz : ((rr : ℂ) * zc).im = rr * zc.im := im_mul_real_left rr zc

private lemma im_rzb : ((rr : ℂ) * zcb).im = -(rr * zc.im) := by
  rw [im_mul_real_left, zcb_im]; ring

private lemma im_sQ : (sig * (qq : ℂ)).im = sig.im * qq := im_mul_real_right sig qq

private lemma im_sbQ : (sgb * (qq : ℂ)).im = -(sig.im * qq) := by
  rw [im_mul_real_right, sgb_im]; ring

private lemma im_sn : (sig * (nn : ℂ)).im = sig.im * nn := im_mul_real_right sig nn

private lemma im_sbn : (sgb * (nn : ℂ)).im = -(sig.im * nn) := by
  rw [im_mul_real_right, sgb_im]; ring

private lemma im_sbzb : (sgb * zcb).im = -(sig * zc).im := by
  have : sgb * zcb = (starRingEnd ℂ) (sig * zc) := by rw [map_mul, sgb, zcb]
  rw [this, Complex.conj_im]

private lemma im_sbz : (sgb * zc).im = -(sig * zcb).im := by
  have : sgb * zc = (starRingEnd ℂ) (sig * zcb) := by
    rw [map_mul, sgb, zcb, Complex.conj_conj]
  rw [this, Complex.conj_im]

private lemma rzim_pos : 0 < rr * zc.im := mul_pos rr_pos zc_im_pos

private lemma sQim_pos : 0 < sig.im * qq := mul_pos sig_im_pos qq_pos

private lemma snim_neg : sig.im * nn < 0 := mul_neg_of_pos_of_neg sig_im_pos nn_neg

/-! ### The counting scheme

Five explicit distinct roots outside the unit circle and seven inside, in a
root set of twelve, force the exact census — cross-class distinctness is free
(the two norm classes are separated by `1`). -/

private lemma census_count {S A B : Finset ℂ} {p q : ℂ → Prop}
    [DecidablePred p] [DecidablePred q]
    (hS : S.card = 12) (hA5 : A.card = 5) (hB7 : B.card = 7)
    (hA : A ⊆ S.filter p) (hB : B ⊆ S.filter q)
    (hpq : ∀ x, ¬(p x ∧ q x)) :
    S.filter p = A ∧ S.filter q = B ∧ S.filter p ∪ S.filter q = S := by
  have hd : Disjoint (S.filter p) (S.filter q) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact hpq x ⟨(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2⟩
  have hsub : S.filter p ∪ S.filter q ⊆ S :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcard : (S.filter p).card + (S.filter q).card ≤ 12 := by
    rw [← Finset.card_union_of_disjoint hd]
    exact hS ▸ Finset.card_le_card hsub
  have h5 : 5 ≤ (S.filter p).card := hA5 ▸ Finset.card_le_card hA
  have h7 : 7 ≤ (S.filter q).card := hB7 ▸ Finset.card_le_card hB
  have hAeq : S.filter p = A :=
    (Finset.eq_of_subset_of_card_le hA (by omega)).symm
  have hBeq : S.filter q = B :=
    (Finset.eq_of_subset_of_card_le hB (by omega)).symm
  refine ⟨hAeq, hBeq, Finset.eq_of_subset_of_card_le hsub ?_⟩
  rw [Finset.card_union_of_disjoint hd, hS]
  omega

/-- The five conjugates outside the unit circle: `ρQ, ρz, ρz̄, σQ, σ̄Q`. -/
private noncomputable def outSet : Finset ℂ :=
  {(rr : ℂ) * (qq : ℂ), (rr : ℂ) * zc, (rr : ℂ) * zcb, sig * (qq : ℂ), sgb * (qq : ℂ)}

/-- The seven conjugates inside: `ρr₂, σr₂, σ̄r₂, σz, σz̄, σ̄z, σ̄z̄`. -/
private noncomputable def inSet : Finset ℂ :=
  {(rr : ℂ) * (nn : ℂ), sig * (nn : ℂ), sgb * (nn : ℂ), sig * zc, sig * zcb,
    sgb * zc, sgb * zcb}

private lemma outSet_card : outSet.card = 5 := by
  have ne12 : (rr : ℂ) * (qq : ℂ) ≠ (rr : ℂ) * zc :=
    ne_of_im (by rw [im_rQ, im_rz]; exact ne_of_lt rzim_pos)
  have ne13 : (rr : ℂ) * (qq : ℂ) ≠ (rr : ℂ) * zcb :=
    ne_of_im (by rw [im_rQ, im_rzb]; exact ne_of_gt (by linarith [rzim_pos]))
  have ne14 : (rr : ℂ) * (qq : ℂ) ≠ sig * (qq : ℂ) :=
    ne_of_im (by rw [im_rQ, im_sQ]; exact ne_of_lt sQim_pos)
  have ne15 : (rr : ℂ) * (qq : ℂ) ≠ sgb * (qq : ℂ) :=
    ne_of_im (by rw [im_rQ, im_sbQ]; exact ne_of_gt (by linarith [sQim_pos]))
  have ne23 : (rr : ℂ) * zc ≠ (rr : ℂ) * zcb :=
    ne_of_im (by rw [im_rz, im_rzb]; exact ne_of_gt (by linarith [rzim_pos]))
  have ne24 : (rr : ℂ) * zc ≠ sig * (qq : ℂ) :=
    ne_of_normSq (by
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_zc, normSq_sig]
      exact ne_of_gt sep_sQ_lt_rz)
  have ne25 : (rr : ℂ) * zc ≠ sgb * (qq : ℂ) :=
    ne_of_normSq (by
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_zc, normSq_sgb]
      exact ne_of_gt sep_sQ_lt_rz)
  have ne34 : (rr : ℂ) * zcb ≠ sig * (qq : ℂ) :=
    ne_of_normSq (by
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_zcb, normSq_sig]
      exact ne_of_gt sep_sQ_lt_rz)
  have ne35 : (rr : ℂ) * zcb ≠ sgb * (qq : ℂ) :=
    ne_of_normSq (by
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_zcb, normSq_sgb]
      exact ne_of_gt sep_sQ_lt_rz)
  have ne45 : sig * (qq : ℂ) ≠ sgb * (qq : ℂ) :=
    ne_of_im (by rw [im_sQ, im_sbQ]; exact ne_of_gt (by linarith [sQim_pos]))
  have m1 : (rr : ℂ) * (qq : ℂ) ∉
      ({(rr : ℂ) * zc, (rr : ℂ) * zcb, sig * (qq : ℂ), sgb * (qq : ℂ)} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨ne12, ne13, ne14, ne15⟩
  have m2 : (rr : ℂ) * zc ∉
      ({(rr : ℂ) * zcb, sig * (qq : ℂ), sgb * (qq : ℂ)} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨ne23, ne24, ne25⟩
  have m3 : (rr : ℂ) * zcb ∉ ({sig * (qq : ℂ), sgb * (qq : ℂ)} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨ne34, ne35⟩
  have m4 : sig * (qq : ℂ) ∉ ({sgb * (qq : ℂ)} : Finset ℂ) := by
    simp only [Finset.mem_singleton]
    exact ne45
  rw [outSet, Finset.card_insert_of_notMem m1, Finset.card_insert_of_notMem m2,
    Finset.card_insert_of_notMem m3, Finset.card_insert_of_notMem m4,
    Finset.card_singleton]

private lemma inSet_card : inSet.card = 7 := by
  have hrn : (rr ^ 2 - 1) * nn ^ 2 < rr ^ 2 * nn ^ 2 := by nlinarith [nn2_bounds.1]
  have ne12 : (rr : ℂ) * (nn : ℂ) ≠ sig * (nn : ℂ) :=
    ne_of_normSq (by
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_sig]
      exact ne_of_gt hrn)
  have ne13 : (rr : ℂ) * (nn : ℂ) ≠ sgb * (nn : ℂ) :=
    ne_of_normSq (by
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_sgb]
      exact ne_of_gt hrn)
  have nsfam : ∀ w z : ℂ, Complex.normSq w = rr ^ 2 - 1 →
      Complex.normSq z = (qq + nn) ^ 2 - qq * nn → (rr : ℂ) * (nn : ℂ) ≠ w * z := by
    intro w z hw hz
    refine ne_of_normSq ?_
    simp only [Complex.normSq_mul, normSq_ofReal', hw, hz]
    exact ne_of_gt sep_sz_lt_rn
  have nsfam2 : ∀ w z : ℂ, Complex.normSq w = rr ^ 2 - 1 →
      Complex.normSq z = (qq + nn) ^ 2 - qq * nn →
      ∀ w' : ℂ, Complex.normSq w' = rr ^ 2 - 1 → w' * (nn : ℂ) ≠ w * z := by
    intro w z hw hz w' hw'
    refine ne_of_normSq ?_
    simp only [Complex.normSq_mul, normSq_ofReal', hw, hz, hw']
    exact ne_of_lt sep_sn_lt_sz
  have ne23 : sig * (nn : ℂ) ≠ sgb * (nn : ℂ) :=
    ne_of_im (by rw [im_sn, im_sbn]; exact ne_of_lt (by linarith [snim_neg]))
  have ne45 : sig * zc ≠ sig * zcb := fun h => zc_ne_zcb (mul_left_cancel₀ sig_ne_zero h)
  have ne46 : sig * zc ≠ sgb * zc := fun h => sig_ne_sgb (mul_right_cancel₀ zc_ne_zero h)
  have ne47 : sig * zc ≠ sgb * zcb :=
    ne_of_im (by rw [im_sbzb]; exact ne_of_lt (by linarith [im_sz_neg]))
  have ne56 : sig * zcb ≠ sgb * zc :=
    ne_of_im (by rw [im_sbz]; exact ne_of_gt (by linarith [im_szb_pos]))
  have ne57 : sig * zcb ≠ sgb * zcb := fun h => sig_ne_sgb (mul_right_cancel₀ zcb_ne_zero h)
  have ne67 : sgb * zc ≠ sgb * zcb := fun h => zc_ne_zcb (mul_left_cancel₀ sgb_ne_zero h)
  have m1 : (rr : ℂ) * (nn : ℂ) ∉ ({sig * (nn : ℂ), sgb * (nn : ℂ), sig * zc, sig * zcb,
      sgb * zc, sgb * zcb} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨ne12, ne13, nsfam sig zc normSq_sig normSq_zc, nsfam sig zcb normSq_sig normSq_zcb,
      nsfam sgb zc normSq_sgb normSq_zc, nsfam sgb zcb normSq_sgb normSq_zcb⟩
  have m2 : sig * (nn : ℂ) ∉ ({sgb * (nn : ℂ), sig * zc, sig * zcb,
      sgb * zc, sgb * zcb} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨ne23, nsfam2 sig zc normSq_sig normSq_zc sig normSq_sig,
      nsfam2 sig zcb normSq_sig normSq_zcb sig normSq_sig,
      nsfam2 sgb zc normSq_sgb normSq_zc sig normSq_sig,
      nsfam2 sgb zcb normSq_sgb normSq_zcb sig normSq_sig⟩
  have m3 : sgb * (nn : ℂ) ∉ ({sig * zc, sig * zcb, sgb * zc, sgb * zcb} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨nsfam2 sig zc normSq_sig normSq_zc sgb normSq_sgb,
      nsfam2 sig zcb normSq_sig normSq_zcb sgb normSq_sgb,
      nsfam2 sgb zc normSq_sgb normSq_zc sgb normSq_sgb,
      nsfam2 sgb zcb normSq_sgb normSq_zcb sgb normSq_sgb⟩
  have m4 : sig * zc ∉ ({sig * zcb, sgb * zc, sgb * zcb} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨ne45, ne46, ne47⟩
  have m5 : sig * zcb ∉ ({sgb * zc, sgb * zcb} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push Not
    exact ⟨ne56, ne57⟩
  have m6 : sgb * zc ∉ ({sgb * zcb} : Finset ℂ) := by
    simp only [Finset.mem_singleton]
    exact ne67
  rw [inSet, Finset.card_insert_of_notMem m1, Finset.card_insert_of_notMem m2,
    Finset.card_insert_of_notMem m3, Finset.card_insert_of_notMem m4,
    Finset.card_insert_of_notMem m5, Finset.card_insert_of_notMem m6,
    Finset.card_singleton]

private lemma rr_cubicC : ((rr : ℝ) : ℂ) ^ 3 = (rr : ℂ) + 1 := by exact_mod_cast rr_cubic
private lemma qq_quarticC : ((qq : ℝ) : ℂ) ^ 4 = (qq : ℂ) + 1 := by exact_mod_cast qq_quartic
private lemma nn_quarticC : ((nn : ℝ) : ℂ) ^ 4 = (nn : ℂ) + 1 := by exact_mod_cast nn_quartic

private lemma outSet_subset : outSet ⊆ RF.filter (fun ζ => 1 < ‖ζ‖) := by
  intro ζ hζ
  rw [outSet] at hζ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hζ
  rcases hζ with rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_filter.mpr ⟨prod_mem rr_cubicC qq_quarticC, one_lt_norm (by
      simp only [Complex.normSq_mul, normSq_ofReal']; exact val_rQ_gt)⟩
  · exact Finset.mem_filter.mpr ⟨prod_mem rr_cubicC zc_quartic, one_lt_norm (by
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_zc]; exact val_rz_gt)⟩
  · exact Finset.mem_filter.mpr ⟨prod_mem rr_cubicC zcb_quartic, one_lt_norm (by
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_zcb]; exact val_rz_gt)⟩
  · exact Finset.mem_filter.mpr ⟨prod_mem sig_cubic qq_quarticC, one_lt_norm (by
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_sig]; exact val_sQ_gt)⟩
  · exact Finset.mem_filter.mpr ⟨prod_mem sgb_cubic qq_quarticC, one_lt_norm (by
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_sgb]; exact val_sQ_gt)⟩

private lemma inSet_subset : inSet ⊆ RF.filter (fun ζ => ‖ζ‖ < 1) := by
  intro ζ hζ
  rw [inSet] at hζ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hζ
  rcases hζ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_filter.mpr ⟨prod_mem rr_cubicC nn_quarticC, norm_lt_one (by
      simp only [Complex.normSq_mul, normSq_ofReal']; exact val_rn_lt)⟩
  · exact Finset.mem_filter.mpr ⟨prod_mem sig_cubic nn_quarticC, norm_lt_one (by
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_sig]; exact val_sn_lt)⟩
  · exact Finset.mem_filter.mpr ⟨prod_mem sgb_cubic nn_quarticC, norm_lt_one (by
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_sgb]; exact val_sn_lt)⟩
  · exact Finset.mem_filter.mpr ⟨prod_mem sig_cubic zc_quartic, norm_lt_one (by
      simp only [Complex.normSq_mul, normSq_sig, normSq_zc]; exact val_sz_lt)⟩
  · exact Finset.mem_filter.mpr ⟨prod_mem sig_cubic zcb_quartic, norm_lt_one (by
      simp only [Complex.normSq_mul, normSq_sig, normSq_zcb]; exact val_sz_lt)⟩
  · exact Finset.mem_filter.mpr ⟨prod_mem sgb_cubic zc_quartic, norm_lt_one (by
      simp only [Complex.normSq_mul, normSq_sgb, normSq_zc]; exact val_sz_lt)⟩
  · exact Finset.mem_filter.mpr ⟨prod_mem sgb_cubic zcb_quartic, norm_lt_one (by
      simp only [Complex.normSq_mul, normSq_sgb, normSq_zcb]; exact val_sz_lt)⟩

/-- The full identification: the outside filter IS the explicit five, the
inside filter IS the explicit seven, and together they exhaust the root set. -/
private lemma census_full :
    RF.filter (fun ζ => 1 < ‖ζ‖) = outSet ∧
      RF.filter (fun ζ => ‖ζ‖ < 1) = inSet ∧
      RF.filter (fun ζ => 1 < ‖ζ‖) ∪ RF.filter (fun ζ => ‖ζ‖ < 1) = RF :=
  census_count RF_card outSet_card inSet_card outSet_subset inSet_subset
    (fun _ h => lt_irrefl 1 (lt_trans h.1 h.2))

private lemma ncard_filter (p : ℂ → Prop) [DecidablePred p] :
    {ζ ∈ rulerPoly.rootSet ℂ | p ζ}.ncard = (RF.filter p).card := by
  have hset : {ζ ∈ rulerPoly.rootSet ℂ | p ζ} = ↑(RF.filter p) := by
    ext ζ
    simp [Finset.coe_filter, RF]
  rw [hset, Set.ncard_eq_toFinset_card', Finset.toFinset_coe]

/-- **The unit-circle census of `rulerPoly`.**  Of the twelve complex roots of
the minimal polynomial of `ρQ`, EXACTLY five lie strictly outside the unit
circle (`ρQ`, `ρz`, `ρz̄`, `σQ`, `σ̄Q`), EXACTLY seven lie strictly inside
(`ρr₂`, `σr₂`, `σ̄r₂`, `σz`, `σz̄`, `σ̄z`, `σ̄z̄`), and NONE lies on it.  In
particular `ρQ` is neither a Pisot number (which would put all eleven others
inside) nor a Salem number (which would put conjugates on the circle). -/
theorem rulerPoly_census :
    {ζ ∈ rulerPoly.rootSet ℂ | 1 < ‖ζ‖}.ncard = 5 ∧
      {ζ ∈ rulerPoly.rootSet ℂ | ‖ζ‖ < 1}.ncard = 7 ∧
      ∀ ζ ∈ rulerPoly.rootSet ℂ, ‖ζ‖ ≠ 1 := by
  obtain ⟨hOut, hIn, hUnion⟩ := census_full
  refine ⟨?_, ?_, ?_⟩
  · rw [ncard_filter, hOut, outSet_card]
  · rw [ncard_filter, hIn, inSet_card]
  · intro ζ hζ h1
    have hmem : ζ ∈ RF := mem_RF.mpr hζ
    rw [← hUnion] at hmem
    rcases Finset.mem_union.mp hmem with h | h
    · have := (Finset.mem_filter.mp h).2
      rw [h1] at this
      exact lt_irrefl 1 this
    · have := (Finset.mem_filter.mp h).2
      rw [h1] at this
      exact lt_irrefl 1 this

/-- **The unit-circle census of the conjugates of the ruler product.**  For the
real roots `ρ` of the cubic and `Q` of the quartic, the root set of
`minpoly ℚ (ρQ)` in `ℂ` has EXACTLY 5 elements of modulus `> 1`, EXACTLY 7 of
modulus `< 1`, and none on the unit circle. -/
theorem ruler_conjugate_census {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1)
    (hq : QQ ^ 4 = QQ + 1) :
    {ζ ∈ (minpoly ℚ (rho * QQ)).rootSet ℂ | 1 < ‖ζ‖}.ncard = 5 ∧
      {ζ ∈ (minpoly ℚ (rho * QQ)).rootSet ℂ | ‖ζ‖ < 1}.ncard = 7 ∧
      ∀ ζ ∈ (minpoly ℚ (rho * QQ)).rootSet ℂ, ‖ζ‖ ≠ 1 := by
  rw [ruler_minpoly hr hq]
  exact rulerPoly_census

private lemma norm_lt_of_normSq_lt {ζ : ℂ} {b : ℝ} (hb : 0 < b)
    (h : Complex.normSq ζ < b ^ 2) : ‖ζ‖ < b := by
  nlinarith [Complex.norm_mul_self_eq_normSq ζ, norm_nonneg ζ]

/-- **The house of the ruler product is `ρQ` itself.**  Every root of
`minpoly ℚ (ρQ)` other than `ρQ` has modulus strictly below `ρQ`: the ruler
product is the unique dominant root of its own minimal polynomial. -/
theorem ruler_house {rho QQ : ℝ} (hr : rho ^ 3 = rho + 1) (hq : QQ ^ 4 = QQ + 1)
    (hq1 : 1 < QQ) :
    ∀ ζ ∈ (minpoly ℚ (rho * QQ)).rootSet ℂ, ζ ≠ ((rho * QQ : ℝ) : ℂ) → ‖ζ‖ < rho * QQ := by
  rw [ruler_minpoly hr hq]
  have hrho : rho = rr := cubic_unique hr rr_cubic
  have hQQ : QQ = qq := quartic_pos_unique hq hq1 qq_quartic qq_gt_one
  subst hrho hQQ
  have hrq1 : 1 < rr * qq := by nlinarith [rr_bounds.1, qq_bounds.1]
  have hrq0 : 0 < rr * qq := lt_trans one_pos hrq1
  intro ζ hζ hne
  have hmem : ζ ∈ RF := mem_RF.mpr hζ
  obtain ⟨hOut, -, hUnion⟩ := census_full
  rw [← hUnion] at hmem
  rcases Finset.mem_union.mp hmem with h | h
  · rw [hOut] at h
    rw [outSet] at h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact absurd (by rw [Complex.ofReal_mul]) hne
    · refine norm_lt_of_normSq_lt hrq0 ?_
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_zc]
      nlinarith [sep_rz_lt_rQ]
    · refine norm_lt_of_normSq_lt hrq0 ?_
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_zcb]
      nlinarith [sep_rz_lt_rQ]
    · refine norm_lt_of_normSq_lt hrq0 ?_
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_sig]
      nlinarith [qq2_bounds.1]
    · refine norm_lt_of_normSq_lt hrq0 ?_
      simp only [Complex.normSq_mul, normSq_ofReal', normSq_sgb]
      nlinarith [qq2_bounds.1]
  · have := (Finset.mem_filter.mp h).2
    linarith

end RulerCensus
end PDT

/-! ### Axiom audit — every public result rests on the kernel alone -/

#print axioms PDT.RulerCensus.rulerPoly_census
#print axioms PDT.RulerCensus.ruler_conjugate_census
#print axioms PDT.RulerCensus.ruler_house

