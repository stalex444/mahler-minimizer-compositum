import Mathlib
import PdtSalemCircle
import PdtSalemArith
import PdtSalemFamily
import PdtPisotBoundary

/-!
# PdtSalemPlasticPattern — the plastic Pisot-pattern data (trimmed instance module)

The plastic section of the source project's `PdtSalemInstances` module, kept
verbatim: the general pattern constructor `pattern_of_simple_root`, the
companion bridge `Qmap_of_mirror`, the cubic cast lemmas, `plastic_pattern`
and `plastic_Qmap`.  The source module's other sections (the general minus
ladder, the both-sides corollaries via `PdtSalemQuadUnit`, and the `theta_4`
instance via `PdtThetaLadder` / `PdtMahlerTheta`) are not needed by the `E_m`
spectral statements and are omitted, together with those imports.  The one
lemma imported from `PdtMahlerWindow`, `rho_real_root_unique`, is copied
verbatim (namespace `PDT.Mahler` kept); `cubic_conj_norm_lt_one` comes from
`PdtPisotBoundary`.
-/

namespace PDT
namespace Mahler

lemma rho_real_root_unique {x y : ℝ} (hx : x ^ 3 = x + 1) (h1x : 1 < x)
    (hy : y ^ 3 = y + 1) (h1y : 1 < y) : x = y := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · nlinarith [hx, hy, mul_pos (sub_pos.2 h)
      (by nlinarith : (0:ℝ) < y^2 + y*x + x^2 - 1)]
  · nlinarith [hx, hy, mul_pos (sub_pos.2 h)
      (by nlinarith : (0:ℝ) < x^2 + x*y + y^2 - 1)]

end Mahler
end PDT

namespace PDT
namespace SalemInstances

noncomputable section
open Polynomial Complex Filter Set

/-! ### The general pattern constructor -/

/-- **The Pisot-pattern data from a simple dominant root.**  For a monic
integer polynomial whose complex image has `alpha` as a root, with the
derivative nonvanishing at `alpha` (simplicity) and every other complex
root strictly inside the unit circle, the multiset
`inside = roots.erase alpha` satisfies the three Pisot-pattern
hypotheses of the Salem program: strict interiority, conjugation
closure, and the factorization `Pz = SalemCircle.P alpha inside`. -/
theorem pattern_of_simple_root (Pz : Polynomial ℤ) (hmonic : Pz.Monic) (alpha : ℝ)
    (hroot : (Pz.map (Int.castRingHom ℂ)).eval ((alpha : ℂ)) = 0)
    (hsimple : (Polynomial.derivative (Pz.map (Int.castRingHom ℂ))).eval ((alpha : ℂ)) ≠ 0)
    (hsmall : ∀ z : ℂ, (Pz.map (Int.castRingHom ℂ)).eval z = 0 → z ≠ ((alpha : ℂ)) → ‖z‖ < 1) :
    ∃ inside : Multiset ℂ,
      (∀ z ∈ inside, ‖z‖ < 1) ∧ inside.map (starRingEnd ℂ) = inside ∧
      Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside := by
  classical
  set pC : Polynomial ℂ := Pz.map (Int.castRingHom ℂ) with hpC
  have hCmonic : pC.Monic := hmonic.map _
  have hCne : pC ≠ 0 := hCmonic.ne_zero
  have hsplits : pC.Splits := IsAlgClosed.splits pC
  have hmem : ((alpha : ℂ)) ∈ pC.roots := Polynomial.mem_roots'.mpr ⟨hCne, hroot⟩
  -- simplicity: the root multiplicity of `alpha` is exactly one
  have hmult : Polynomial.rootMultiplicity ((alpha : ℂ)) pC ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have h1 := Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hgt
    rw [Function.iterate_one] at h1
    exact hsimple h1
  have hcount : pC.roots.count ((alpha : ℂ)) = 1 := by
    have h1 : 0 < Polynomial.rootMultiplicity ((alpha : ℂ)) pC :=
      (Polynomial.rootMultiplicity_pos hCne).mpr hroot
    rw [Polynomial.count_roots]
    omega
  have hnotin : ((alpha : ℂ)) ∉ pC.roots.erase ((alpha : ℂ)) := by
    rw [← Multiset.count_eq_zero, Multiset.count_erase_self, hcount]
  refine ⟨pC.roots.erase ((alpha : ℂ)), ?_, ?_, ?_⟩
  · -- strict interiority
    intro z hz
    have hzmem : z ∈ pC.roots := Multiset.mem_of_mem_erase hz
    have hzroot : pC.eval z = 0 := (Polynomial.mem_roots'.mp hzmem).2
    have hzne : z ≠ ((alpha : ℂ)) := fun h => hnotin (h ▸ hz)
    exact hsmall z hzroot hzne
  · -- conjugation closure
    have hmapconj : pC.map (starRingEnd ℂ) = pC := by
      rw [hpC, Polynomial.map_map,
        show (starRingEnd ℂ).comp (Int.castRingHom ℂ) = Int.castRingHom ℂ from
          RingHom.ext_int _ _]
    have hroots_conj : pC.roots.map (starRingEnd ℂ) = pC.roots := by
      have h1 := hsplits.roots_map (starRingEnd ℂ)
      rw [hmapconj] at h1
      exact h1.symm
    rw [Multiset.map_erase _ (starRingEnd ℂ).injective, hroots_conj,
      Complex.conj_ofReal]
  · -- the factorization
    have hfac : pC = (pC.roots.map fun a => X - Polynomial.C a).prod :=
      hsplits.eq_prod_roots_of_monic hCmonic
    have hcons : ((alpha : ℂ)) ::ₘ pC.roots.erase ((alpha : ℂ)) = pC.roots :=
      Multiset.cons_erase hmem
    calc pC = (pC.roots.map fun a => X - Polynomial.C a).prod := hfac
      _ = ((((alpha : ℂ)) ::ₘ pC.roots.erase ((alpha : ℂ))).map
            fun a => X - Polynomial.C a).prod := by rw [hcons]
      _ = (X - Polynomial.C ((alpha : ℂ)))
          * ((pC.roots.erase ((alpha : ℂ))).map fun a => X - Polynomial.C a).prod := by
          rw [Multiset.map_cons, Multiset.prod_cons]
      _ = SalemCircle.P alpha (pC.roots.erase ((alpha : ℂ))) := rfl

/-! ### The general companion bridge -/

/-- **The companion bridge.**  An integer companion `Qz` whose complex
evaluations satisfy the mirror identity
`Qz(z) = z^(card+1)·Pz(1/z)` (for `z ≠ 0`) has complex image the
mirrored product `SalemCircle.Q alpha inside` — the cofinite-agreement
pattern of `PdtSalemArith.reflect_P_eq_Q`. -/
lemma Qmap_of_mirror (Pz Qz : Polynomial ℤ) (alpha : ℝ) (inside : Multiset ℂ)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside)
    (hmirror : ∀ z : ℂ, z ≠ 0 → (Qz.map (Int.castRingHom ℂ)).eval z
      = z ^ (inside.card + 1) * (Pz.map (Int.castRingHom ℂ)).eval z⁻¹) :
    Qz.map (Int.castRingHom ℂ) = SalemCircle.Q alpha inside := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hsub : ({(0 : ℂ)}ᶜ : Set ℂ) ⊆
      {x : ℂ | (Qz.map (Int.castRingHom ℂ)).eval x
        = (SalemCircle.Q alpha inside).eval x} := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    show (Qz.map (Int.castRingHom ℂ)).eval z = (SalemCircle.Q alpha inside).eval z
    rw [hmirror z hz0, hfacC]
    exact SalemCircle.mirror_P alpha inside hz0
  exact Set.Infinite.mono hsub ((Set.finite_singleton 0).infinite_compl)


/-! ### The plastic instance: scalar and cast lemmas -/

lemma cubic_monic : (X ^ 3 - X - 1 : Polynomial ℤ).Monic := by
  unfold Polynomial.Monic
  monicity!

lemma cubic_natDegree : (X ^ 3 - X - 1 : Polynomial ℤ).natDegree = 3 := by
  compute_degree!

lemma cubic_mapC :
    (X ^ 3 - X - 1 : Polynomial ℤ).map (Int.castRingHom ℂ) = X ^ 3 - X - 1 := by
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_one]

lemma cubic_evalC (z : ℂ) :
    ((X ^ 3 - X - 1 : Polynomial ℤ).map (Int.castRingHom ℂ)).eval z
      = z ^ 3 - z - 1 := by
  rw [cubic_mapC]
  simp only [eval_sub, eval_pow, eval_X, eval_one]

lemma cubic_deriv_eval (z : ℂ) :
    (Polynomial.derivative (X ^ 3 - X - 1 : Polynomial ℂ)).eval z
      = 3 * z ^ 2 - 1 := by
  simp only [derivative_sub, derivative_one, derivative_X, derivative_X_pow,
    eval_sub, eval_mul, eval_pow, eval_X, eval_C]
  norm_num

lemma cubic_comp_evalC (z : ℂ) :
    ((-(X ^ 3 + X ^ 2 - 1) : Polynomial ℤ).map (Int.castRingHom ℂ)).eval z
      = -(z ^ 3 + z ^ 2 - 1) := by
  simp only [Polynomial.map_neg, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, eval_neg,
    eval_sub, eval_add, eval_pow, eval_X, eval_one]

lemma cubic_comp_evalR (x : ℝ) :
    ((-(X ^ 3 + X ^ 2 - 1) : Polynomial ℤ).map (Int.castRingHom ℝ)).eval x
      = -(x ^ 3 + x ^ 2 - 1) := by
  simp only [Polynomial.map_neg, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, eval_neg,
    eval_sub, eval_add, eval_pow, eval_X, eval_one]

lemma cubic_family_evalR (n : ℕ) (x : ℝ) :
    ((X ^ (n + 1) * (X ^ 3 - X - 1) - -(X ^ 3 + X ^ 2 - 1) : Polynomial ℤ).map
      (Int.castRingHom ℝ)).eval x
      = x ^ (n + 1) * (x ^ 3 - x - 1) + (x ^ 3 + x ^ 2 - 1) := by
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_neg, Polynomial.map_add, Polynomial.map_X, Polynomial.map_one,
    eval_sub, eval_mul, eval_pow, eval_neg, eval_add, eval_X, eval_one]
  ring

/-! ### G1: the plastic pattern -/

/-- **The plastic Pisot pattern.**  The plastic polynomial `X³ − X − 1`
carries the Pisot-pattern data at its real root `rho`: the two other
complex roots are strictly inside the unit circle
(`cubic_conj_norm_lt_one` — the real-root branch is empty by the
banked exceeds-one certificate plus uniqueness), conjugation-closed,
and the complex image factors as `SalemCircle.P rho inside`. -/
theorem plastic_pattern (rho : ℝ) (hrho : rho ^ 3 = rho + 1) :
    ∃ inside : Multiset ℂ,
      (∀ z ∈ inside, ‖z‖ < 1) ∧ inside.map (starRingEnd ℂ) = inside ∧
      (X ^ 3 - X - 1 : Polynomial ℤ).map (Int.castRingHom ℂ)
        = SalemCircle.P rho inside := by
  have hrho1 : 1 < rho := SalemFamily.one_lt_of_cubic hrho
  apply pattern_of_simple_root (X ^ 3 - X - 1 : Polynomial ℤ) cubic_monic rho
  · -- the root
    rw [cubic_evalC]
    have h : ((rho : ℂ)) ^ 3 - (rho : ℂ) - 1 = (((rho ^ 3 - rho - 1 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [h, show rho ^ 3 - rho - 1 = 0 by linarith]
    exact Complex.ofReal_zero
  · -- simplicity: the derivative `3x² − 1` is positive at `rho > 1`
    rw [cubic_mapC, cubic_deriv_eval]
    have h : 3 * ((rho : ℂ)) ^ 2 - 1 = (((3 * rho ^ 2 - 1 : ℝ)) : ℂ) := by
      push_cast
      ring
    rw [h]
    rw [Complex.ofReal_ne_zero]
    nlinarith [hrho1]
  · -- interiority of every other root
    intro z hz hzne
    rw [cubic_evalC] at hz
    have hz3 : z ^ 3 = z + 1 := by linear_combination hz
    by_cases him : z.im = 0
    · exfalso
      have hre : z = ((z.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [him]
      have hzR : z.re ^ 3 = z.re + 1 := by
        have h := hz3
        rw [hre] at h
        exact_mod_cast h
      have h1 : 1 < z.re := SalemFamily.one_lt_of_cubic hzR
      have heq : z.re = rho := Mahler.rho_real_root_unique hzR h1 hrho hrho1
      exact hzne (by rw [hre, heq])
    · exact cubic_conj_norm_lt_one z hz3 him

/-- The plastic companion bridge: the complex image of
`−(X³ + X² − 1)` is the mirrored product `SalemCircle.Q rho inside`. -/
lemma plastic_Qmap (rho : ℝ) (inside : Multiset ℂ)
    (hfacC : (X ^ 3 - X - 1 : Polynomial ℤ).map (Int.castRingHom ℂ)
      = SalemCircle.P rho inside) :
    (-(X ^ 3 + X ^ 2 - 1) : Polynomial ℤ).map (Int.castRingHom ℂ)
      = SalemCircle.Q rho inside := by
  have hcard : inside.card = 2 := by
    have h := SalemArith.Pz_natDegree _ cubic_monic rho inside hfacC
    rw [cubic_natDegree] at h
    omega
  apply Qmap_of_mirror _ _ rho inside hfacC
  intro z hz
  rw [hcard, cubic_comp_evalC, cubic_evalC]
  field_simp
  ring

end
end SalemInstances
end PDT
