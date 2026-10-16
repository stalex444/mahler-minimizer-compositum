import Mathlib
import PdtCoxeterBridge
import PdtSalemPlasticPattern
import PdtSalemMinus
import PdtSalemEndgame

/-!
# The spectrum of the `E_m` Coxeter elements, and Salem-ness of their radii

The full spectral statement for the Coxeter elements of `W(E_m)`, composing
the bridge (`PdtCoxeterBridge`) with the minus-family trichotomy
(`PdtSalemMinus.salem_root_trichotomy_minus`) through the plastic Pisot
pattern (`PdtSalemPlasticPattern.plastic_pattern`), and the minus-family
Salem certificate (`PdtSalemMinus.salem_certificate_minus`).
-/

namespace PlasticThreshold.CoxeterSpectral

open Matrix Polynomial Filter

/-- Complex evaluation of the bridge. -/
lemma bridge_evalC (k : ℕ) (z : ℂ) :
    (z - 1) * ((CoxElt.cox (CoxeterBridge.Astar k)).charpoly.map (Int.castRingHom ℂ)).eval z
      = z ^ (k + 2) * (z ^ 3 - z - 1) + (z ^ 3 + z ^ 2 - 1) := by
  have h := congrArg (fun p : Polynomial ℤ => (p.map (Int.castRingHom ℂ)).eval z)
    (CoxeterBridge.coxeter_E_bridge k)
  simpa using h

/-- **The spectrum of the `E_m` Coxeter element** (`m ≥ 10`): every complex
eigenvalue has modulus `1` or is `λ` or `λ⁻¹`, where `λ = λ_{m-3}` is the
`PdtSalemFamily` canonical root. Hence the spectral radius is `λ`. -/
theorem coxeter_E_spectrum {rho : ℝ} (hrho : rho ^ 3 = rho + 1) (m : ℕ) (hm : 10 ≤ m) :
    ((PDT.SalemFamily.lam (m - 3) rho : ℝ) : ℂ) ∈
        spectrum ℂ ((CoxElt.cox (CoxeterBridge.Astar (m - 4))).map (Int.castRingHom ℂ)) ∧
      ∀ z ∈ spectrum ℂ ((CoxElt.cox (CoxeterBridge.Astar (m - 4))).map (Int.castRingHom ℂ)),
        ‖z‖ = 1 ∨ z = (PDT.SalemFamily.lam (m - 3) rho : ℂ) ∨
          z = ((PDT.SalemFamily.lam (m - 3) rho : ℂ))⁻¹ := by
  set lam := PDT.SalemFamily.lam (m - 3) rho with hlam
  have hn : 7 ≤ m - 3 := by omega
  have hk : m - 4 + 2 = m - 3 + 1 := by omega
  have hrho1 : 1 < rho := PDT.SalemFamily.one_lt_of_cubic hrho
  have hlam1 : 1 < lam := PDT.SalemFamily.lam_gt_one hrho hn
  obtain ⟨inside, hin, hconj, hfacC⟩ := PDT.SalemInstances.plastic_pattern rho hrho
  have hQ := PDT.SalemInstances.plastic_Qmap rho inside hfacC
  -- Rm evaluates to the Bedford–Kim member
  have hRm : ∀ z : ℂ, (PDT.SalemMinus.Rm rho inside (m - 3 + 1)).eval z
      = z ^ (m - 3 + 1) * (z ^ 3 - z - 1) + (z ^ 3 + z ^ 2 - 1) := by
    intro z
    rw [PDT.SalemMinus.eval_Rm, ← hfacC, ← hQ, PDT.SalemInstances.cubic_evalC,
      PDT.SalemInstances.cubic_comp_evalC]
    ring
  have hspec : ∀ z : ℂ, z ∈ spectrum ℂ
      ((CoxElt.cox (CoxeterBridge.Astar (m - 4))).map (Int.castRingHom ℂ)) ↔
      ((CoxElt.cox (CoxeterBridge.Astar (m - 4))).charpoly.map (Int.castRingHom ℂ)).eval z = 0 := by
    intro z
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map, IsRoot.def]
  -- the root λ
  have hrootR : ((lam : ℂ)) ^ (m - 3 + 1) * ((lam : ℂ) ^ 3 - (lam : ℂ) - 1)
      + ((lam : ℂ) ^ 3 + (lam : ℂ) ^ 2 - 1) = 0 := by
    have h := PDT.SalemFamily.lam_root hrho hn
    unfold PDT.SalemFamily.chi PDT.SalemFamily.P PDT.SalemFamily.Pstar at h
    have h' : ((lam ^ (m - 3 + 1) * (lam ^ 3 - lam - 1) + (lam ^ 3 + lam ^ 2 - 1) : ℝ) : ℂ)
        = 0 := by rw [h]; simp
    push_cast at h'
    exact h'
  refine ⟨?_, ?_⟩
  · rw [hspec]
    have hb := bridge_evalC (m - 4) (lam : ℂ)
    rw [hk, hrootR] at hb
    have hne : (lam : ℂ) - 1 ≠ 0 := by
      intro h
      have : (lam : ℂ) = ((1 : ℝ) : ℂ) := by rw [sub_eq_zero] at h; simpa using h
      have := Complex.ofReal_injective this
      linarith
    exact (mul_eq_zero.mp hb).resolve_left hne
  · intro z hz
    rw [hspec] at hz
    have hb := bridge_evalC (m - 4) z
    rw [hk, hz, mul_zero] at hb
    have hzR : (PDT.SalemMinus.Rm rho inside (m - 3 + 1)).eval z = 0 := by
      rw [hRm]; exact hb.symm
    have hrootRm : (PDT.SalemMinus.Rm rho inside (m - 3 + 1)).eval ((lam : ℂ)) = 0 := by
      rw [hRm]; exact hrootR
    exact PDT.SalemMinus.salem_root_trichotomy_minus rho inside hrho1 hin hconj
      (m - 3 + 1) (by omega) (by omega) lam hlam1 hrootRm z hzR

/-- **Every `E_m` spectral radius (`m ≥ 10`) is a Salem number** — for EVERY
`m ≥ 10`, not merely all but finitely many: the banked minus-family
certificate applies at every rung because `λ ∈ (1, 2)` and
`λ + λ⁻¹ ∈ (2, 3)`. -/
theorem coxeter_E_salem {rho : ℝ} (hrho : rho ^ 3 = rho + 1) (m : ℕ) (hm : 10 ≤ m) :
    PDT.SalemEndgame.IsSalem (PDT.SalemFamily.lam (m - 3) rho) := by
  set lam := PDT.SalemFamily.lam (m - 3) rho with hlam
  have hn : 7 ≤ m - 3 := by omega
  have hrho1 : 1 < rho := PDT.SalemFamily.one_lt_of_cubic hrho
  have hlam1 : 1 < lam := PDT.SalemFamily.lam_gt_one hrho hn
  have hlam2 : lam < 2 :=
    lt_trans (PDT.SalemFamily.lam_lt_rho hrho hn) (PDT.SalemFamily.rho_lt_two hrho)
  obtain ⟨inside, hin, hconj, hfacC⟩ := PDT.SalemInstances.plastic_pattern rho hrho
  have hQ := PDT.SalemInstances.plastic_Qmap rho inside hfacC
  have hroot : ((X ^ (m - 3 + 1) * (X ^ 3 - X - 1) - -(X ^ 3 + X ^ 2 - 1) : Polynomial ℤ).map
      (Int.castRingHom ℝ)).eval lam = 0 := by
    rw [PDT.SalemInstances.cubic_family_evalR]
    have h := PDT.SalemFamily.lam_root hrho hn
    unfold PDT.SalemFamily.chi PDT.SalemFamily.P PDT.SalemFamily.Pstar at h
    exact h
  have hZ : ∀ k : ℤ, lam ≠ (k : ℝ) := by
    intro k hk
    have h1 : (1 : ℝ) < k := hk ▸ hlam1
    have h2 : (k : ℝ) < 2 := hk ▸ hlam2
    have h1' : (1 : ℤ) < k := by exact_mod_cast h1
    have h2' : k < (2 : ℤ) := by exact_mod_cast h2
    omega
  have htr : ∀ k : ℤ, lam + lam⁻¹ ≠ (k : ℝ) := by
    intro k hk
    have hpos : 0 < lam := by linarith
    have hinv1 : lam⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam1
    have hgt : 2 < lam + lam⁻¹ := by
      have h0 : lam + lam⁻¹ - 2 = (lam - 1) ^ 2 / lam := by field_simp; ring
      have : 0 < (lam - 1) ^ 2 / lam := div_pos (by nlinarith) hpos
      linarith
    have h1 : (2 : ℝ) < k := hk ▸ hgt
    have h2 : (k : ℝ) < 3 := by rw [← hk]; linarith
    have h1' : (2 : ℤ) < k := by exact_mod_cast h1
    have h2' : k < (3 : ℤ) := by exact_mod_cast h2
    omega
  obtain ⟨hint, hdisk, hcirc, hinv⟩ := PDT.SalemMinus.salem_certificate_minus
    (X ^ 3 - X - 1) PDT.SalemInstances.cubic_monic rho hrho1 inside hin hconj hfacC
    (-(X ^ 3 + X ^ 2 - 1)) hQ (m - 3 + 1) (by omega) (by omega) lam hlam1 hroot hZ htr
  exact ⟨hlam1, hint, hdisk, hcirc, hinv⟩


/-! ### The compared forms, in core Mathlib vocabulary -/

/-- Complex evaluation of any identity of the bridge shape (stated for a
characteristic polynomial, keeping `Matrix.charpoly`'s instance path). -/
lemma evalC_of_bridge {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℤ} {n : ℕ}
    (h : (X - 1) * M.charpoly = X ^ n * (X ^ 3 - X - 1) + (X ^ 3 + X ^ 2 - 1)) (z : ℂ) :
    (z - 1) * (M.charpoly.map (Int.castRingHom ℂ)).eval z
      = z ^ n * (z ^ 3 - z - 1) + (z ^ 3 + z ^ 2 - 1) := by
  have h' := congrArg (fun q => (q.map (Int.castRingHom ℂ)).eval z) h
  simpa using h'

/-- Spectrum membership of an integer matrix viewed over `ℂ` is a root of its
characteristic polynomial. -/
lemma mem_spectrum_map_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ)
    (z : ℂ) :
    z ∈ spectrum ℂ (M.map (Int.castRingHom ℂ)) ↔
      (M.charpoly.map (Int.castRingHom ℂ)).eval z = 0 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map, IsRoot.def]

/-- The spectral data at the canonical root `λ = PDT.SalemFamily.lam (m - 3) ρ`,
for the explicit `E_m` Cartan matrix of the compared statements. -/
theorem spectrum_data_explicit {rho : ℝ} (hrho : rho ^ 3 = rho + 1)
    (m : ℕ) (hm : 10 ≤ m) (A : Matrix (Fin m) (Fin m) ℤ)
    (hA : ∀ a b : Fin m, A a b =
      if (a : ℕ) = b then 2
      else if (((b : ℕ) = a + 1 ∧ (b : ℕ) ≤ m - 4) ∨ ((a : ℕ) = m - 4 ∧ (b : ℕ) = m - 3) ∨
            ((a : ℕ) = m - 4 ∧ (b : ℕ) = m - 2) ∨ ((a : ℕ) = m - 2 ∧ (b : ℕ) = m - 1)) ∨
          (((a : ℕ) = b + 1 ∧ (a : ℕ) ≤ m - 4) ∨ ((b : ℕ) = m - 4 ∧ (a : ℕ) = m - 3) ∨
            ((b : ℕ) = m - 4 ∧ (a : ℕ) = m - 2) ∨ ((b : ℕ) = m - 2 ∧ (a : ℕ) = m - 1))
        then -1 else 0) :
    1 < PDT.SalemFamily.lam (m - 3) rho ∧ PDT.SalemFamily.lam (m - 3) rho < rho ∧
      ((PDT.SalemFamily.lam (m - 3) rho : ℝ) : ℂ) ∈ spectrum ℂ (((List.finRange m).map (fun i =>
          1 - Matrix.diagonal (fun b => if b = i then 1 else 0) * A)).prod.map (Int.castRingHom ℂ)) ∧
      ∀ z ∈ spectrum ℂ (((List.finRange m).map (fun i =>
          1 - Matrix.diagonal (fun b => if b = i then 1 else 0) * A)).prod.map (Int.castRingHom ℂ)),
        ‖z‖ = 1 ∨ z = (PDT.SalemFamily.lam (m - 3) rho : ℂ) ∨
          z = ((PDT.SalemFamily.lam (m - 3) rho : ℂ))⁻¹ := by
  set lam := PDT.SalemFamily.lam (m - 3) rho with hlam
  have hn : 7 ≤ m - 3 := by omega
  have hk : m - 2 = m - 3 + 1 := by omega
  have hrho1 : 1 < rho := PDT.SalemFamily.one_lt_of_cubic hrho
  have hlam1 : 1 < lam := PDT.SalemFamily.lam_gt_one hrho hn
  have hlamr : lam < rho := PDT.SalemFamily.lam_lt_rho hrho hn
  have hbr := CoxeterBridge.coxeter_E_bridge_explicit m (by omega) A hA
  obtain ⟨inside, hin, hconj, hfacC⟩ := PDT.SalemInstances.plastic_pattern rho hrho
  have hQ := PDT.SalemInstances.plastic_Qmap rho inside hfacC
  have hRm : ∀ z : ℂ, (PDT.SalemMinus.Rm rho inside (m - 3 + 1)).eval z
      = z ^ (m - 3 + 1) * (z ^ 3 - z - 1) + (z ^ 3 + z ^ 2 - 1) := by
    intro z
    rw [PDT.SalemMinus.eval_Rm, ← hfacC, ← hQ, PDT.SalemInstances.cubic_evalC,
      PDT.SalemInstances.cubic_comp_evalC]
    ring
  have hrootR : ((lam : ℂ)) ^ (m - 3 + 1) * ((lam : ℂ) ^ 3 - (lam : ℂ) - 1)
      + ((lam : ℂ) ^ 3 + (lam : ℂ) ^ 2 - 1) = 0 := by
    have h := PDT.SalemFamily.lam_root hrho hn
    unfold PDT.SalemFamily.chi PDT.SalemFamily.P PDT.SalemFamily.Pstar at h
    have h' : ((lam ^ (m - 3 + 1) * (lam ^ 3 - lam - 1) + (lam ^ 3 + lam ^ 2 - 1) : ℝ) : ℂ)
        = 0 := by rw [h]; simp
    push_cast at h'
    exact h'
  refine ⟨hlam1, hlamr, ?_, ?_⟩
  · rw [mem_spectrum_map_iff]
    have hb := evalC_of_bridge hbr (lam : ℂ)
    rw [hk, hrootR] at hb
    have hne : (lam : ℂ) - 1 ≠ 0 := by
      intro h
      have : (lam : ℂ) = ((1 : ℝ) : ℂ) := by rw [sub_eq_zero] at h; simpa using h
      have := Complex.ofReal_injective this
      linarith
    exact (mul_eq_zero.mp hb).resolve_left hne
  · intro z hz
    rw [mem_spectrum_map_iff] at hz
    have hb := evalC_of_bridge hbr z
    rw [hk, hz, mul_zero] at hb
    have hzR : (PDT.SalemMinus.Rm rho inside (m - 3 + 1)).eval z = 0 := by
      rw [hRm]; exact hb.symm
    have hrootRm : (PDT.SalemMinus.Rm rho inside (m - 3 + 1)).eval ((lam : ℂ)) = 0 := by
      rw [hRm]; exact hrootR
    exact PDT.SalemMinus.salem_root_trichotomy_minus rho inside hrho1 hin hconj
      (m - 3 + 1) (by omega) (by omega) lam hlam1 hrootRm z hzR

/-- **(21), compared form.** For every `m ≥ 10` the complexified Coxeter
element of `E_m` has an eigenvalue `λ ∈ (1, ρ)`, and every eigenvalue is
unimodular, `λ`, or `λ⁻¹`. -/
theorem coxeter_E_spectrum_explicit (rho : ℝ) (hrho : rho ^ 3 = rho + 1)
    (m : ℕ) (hm : 10 ≤ m) (A : Matrix (Fin m) (Fin m) ℤ)
    (hA : ∀ a b : Fin m, A a b =
      if (a : ℕ) = b then 2
      else if (((b : ℕ) = a + 1 ∧ (b : ℕ) ≤ m - 4) ∨ ((a : ℕ) = m - 4 ∧ (b : ℕ) = m - 3) ∨
            ((a : ℕ) = m - 4 ∧ (b : ℕ) = m - 2) ∨ ((a : ℕ) = m - 2 ∧ (b : ℕ) = m - 1)) ∨
          (((a : ℕ) = b + 1 ∧ (a : ℕ) ≤ m - 4) ∨ ((b : ℕ) = m - 4 ∧ (a : ℕ) = m - 3) ∨
            ((b : ℕ) = m - 4 ∧ (a : ℕ) = m - 2) ∨ ((b : ℕ) = m - 2 ∧ (a : ℕ) = m - 1))
        then -1 else 0) :
    ∃ lam : ℝ, 1 < lam ∧ lam < rho ∧
      (lam : ℂ) ∈ spectrum ℂ (((List.finRange m).map (fun i =>
          1 - Matrix.diagonal (fun b => if b = i then 1 else 0) * A)).prod.map (Int.castRingHom ℂ)) ∧
      ∀ z ∈ spectrum ℂ (((List.finRange m).map (fun i =>
          1 - Matrix.diagonal (fun b => if b = i then 1 else 0) * A)).prod.map (Int.castRingHom ℂ)),
        ‖z‖ = 1 ∨ z = (lam : ℂ) ∨ z = (lam : ℂ)⁻¹ :=
  ⟨_, spectrum_data_explicit hrho m hm A hA⟩

/-- **(22), compared form.** For every `m ≥ 10` the spectral radius of the
Coxeter element of `E_m` is a Salem number: an eigenvalue `λ ∈ (1, ρ)`
dominating the modulus of every eigenvalue, which is an algebraic integer
whose other conjugates lie in the closed unit disk, at least one ON the unit
circle, with `λ⁻¹` a conjugate. -/
theorem coxeter_E_salem_explicit (rho : ℝ) (hrho : rho ^ 3 = rho + 1)
    (m : ℕ) (hm : 10 ≤ m) (A : Matrix (Fin m) (Fin m) ℤ)
    (hA : ∀ a b : Fin m, A a b =
      if (a : ℕ) = b then 2
      else if (((b : ℕ) = a + 1 ∧ (b : ℕ) ≤ m - 4) ∨ ((a : ℕ) = m - 4 ∧ (b : ℕ) = m - 3) ∨
            ((a : ℕ) = m - 4 ∧ (b : ℕ) = m - 2) ∨ ((a : ℕ) = m - 2 ∧ (b : ℕ) = m - 1)) ∨
          (((a : ℕ) = b + 1 ∧ (a : ℕ) ≤ m - 4) ∨ ((b : ℕ) = m - 4 ∧ (a : ℕ) = m - 3) ∨
            ((b : ℕ) = m - 4 ∧ (a : ℕ) = m - 2) ∨ ((b : ℕ) = m - 2 ∧ (a : ℕ) = m - 1))
        then -1 else 0) :
    ∃ lam : ℝ, 1 < lam ∧ lam < rho ∧
      (lam : ℂ) ∈ spectrum ℂ (((List.finRange m).map (fun i =>
          1 - Matrix.diagonal (fun b => if b = i then 1 else 0) * A)).prod.map (Int.castRingHom ℂ)) ∧
      (∀ z ∈ spectrum ℂ (((List.finRange m).map (fun i =>
          1 - Matrix.diagonal (fun b => if b = i then 1 else 0) * A)).prod.map (Int.castRingHom ℂ)), ‖z‖ ≤ lam) ∧
      IsIntegral ℤ lam ∧
      (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ lam) = 0 → z ≠ (lam : ℂ) → ‖z‖ ≤ 1) ∧
      (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ lam) = 0 ∧ ‖z‖ = 1) ∧
      (Polynomial.aeval ((lam : ℂ))⁻¹) (minpoly ℚ lam) = 0 := by
  obtain ⟨h1, h2, hmem, htri⟩ := spectrum_data_explicit hrho m hm A hA
  obtain ⟨-, hint, hdisk, hcirc, hinv⟩ := coxeter_E_salem hrho m hm
  refine ⟨PDT.SalemFamily.lam (m - 3) rho, h1, h2, hmem, ?_, hint, hdisk, hcirc, hinv⟩
  intro z hz
  have hpos : 0 < PDT.SalemFamily.lam (m - 3) rho := by linarith
  rcases htri z hz with h | h | h
  · rw [h]; linarith
  · rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  · rw [h, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    have : (PDT.SalemFamily.lam (m - 3) rho)⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    linarith

end PlasticThreshold.CoxeterSpectral
