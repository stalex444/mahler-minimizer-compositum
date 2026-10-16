import Mathlib
import PdtStarDet
import PdtCoxElt
import PdtSalemFamily

/-!
# The `E_m` Coxeter bridge to the Bedford–Kim / plastic family

The bridge from the Weyl group of the star tree `E_m = T(2,3,m-3)` to the
Bedford–Kim / plastic family `χ_n` of `PdtSalemFamily`.

* `Astar k` — the generalized Cartan matrix of `E_{k+4}` (`2` on the diagonal,
  `-1` on edges), indices as in `PdtStarDet` (0 = tip of the long arm).
* `coxeter_E_bridge` — `(X - 1) · charpoly (s_0 s_1 ⋯ s_{m-1}) = χ_{m-3}`
  (the Gross–Hironaka–McMullen identity for the `E_m` star trees).
* `coxeter_E10_lehmer` — `E_10`'s Coxeter polynomial IS Lehmer's polynomial.
* `coxeter_E_plastic` — composed with `PdtSalemFamily`: for `m ≥ 10` the
  largest real eigenvalue of the Coxeter element of `W(E_m)` lies in
  `[117/100, ρ)`, is strictly increasing in `m`, and tends to the plastic
  number `ρ`.

The final section restates the three results in core Mathlib vocabulary
(`List.finRange`, `List.prod`, `Matrix.diagonal`, `Matrix.charpoly`, an
entrywise hypothesis for the Cartan matrix, a `!![…]` literal for `E_10`):
these `*_explicit` forms are the compared statements of `Challenge.lean`.
-/

namespace PlasticThreshold.CoxeterBridge

open Matrix Polynomial Filter

/-- The generalized Cartan matrix of the star tree `E_{k+4} = T(2,3,k+1)`. -/
def Astar (k : ℕ) : Matrix (Fin (k + 4)) (Fin (k + 4)) ℤ := fun a b =>
  if (a : ℕ) = b then 2
  else if StarDet.adjLt k a b ∨ StarDet.adjLt k b a then -1 else 0

lemma adjLt_lt {k i j : ℕ} (h : StarDet.adjLt k i j) : i < j := by
  unfold StarDet.adjLt at h; omega

lemma Astar_symm (k : ℕ) : (Astar k)ᵀ = Astar k := by
  ext a b
  simp only [transpose_apply, Astar]
  by_cases h : (a : ℕ) = b
  · simp [h]
  · have h' : ¬ (b : ℕ) = a := fun e => h e.symm
    simp only [h, h', ite_false, or_comm]

lemma Astar_diag (k : ℕ) (i : Fin (k + 4)) : Astar k i i = 2 := by simp [Astar]

/-- `X·U + Uᵀ` for `Astar k` is `StarDet.M X k`. -/
lemma M_eq (k : ℕ) :
    (X : Polynomial ℤ) • (CoxElt.Uup (Astar k)).map C + ((CoxElt.Uup (Astar k))ᵀ).map C
      = StarDet.M (X : Polynomial ℤ) k := by
  refine Matrix.ext fun a b => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, transpose_apply,
    smul_eq_mul, CoxElt.Uup, StarDet.M, Astar, Fin.lt_def, Fin.ext_iff]
  rcases lt_trichotomy (a : ℕ) b with h | h | h
  · have h1 : ¬ (b : ℕ) < a := by omega
    have h2 : ¬ (a : ℕ) = b := by omega
    have h3 : ¬ (b : ℕ) = a := by omega
    have h4 : ¬ StarDet.adjLt k b a := fun e => by have := adjLt_lt e; omega
    by_cases h5 : StarDet.adjLt k a b <;> simp [h, h1, h2, h3, h4, h5]
  · simp [h]
  · have h1 : ¬ (a : ℕ) < b := by omega
    have h2 : ¬ (a : ℕ) = b := by omega
    have h3 : ¬ (b : ℕ) = a := by omega
    have h4 : ¬ StarDet.adjLt k a b := fun e => by have := adjLt_lt e; omega
    by_cases h5 : StarDet.adjLt k b a <;> simp [h, h1, h2, h3, h4, h5]

/-- **The bridge.** `(X - 1)` times the characteristic polynomial of the
Coxeter element `s_0 s_1 ⋯ s_{k+3}` of `W(E_{k+4})` is
`X^(k+2)·(X³ - X - 1) + (X³ + X² - 1)` — the Bedford–Kim member `χ_{k+1}`. -/
theorem coxeter_E_bridge (k : ℕ) :
    (X - 1) * (CoxElt.cox (Astar k)).charpoly
      = X ^ (k + 2) * (X ^ 3 - X - 1) + (X ^ 3 + X ^ 2 - 1) := by
  rw [CoxElt.charpoly_cox _ (Astar_symm k) (Astar_diag k), M_eq, StarDet.det_M_closed]

/-- Cancellation of `X - 1` against `χ_7 = (X - 1)·L` (the identity of
`PDT.SalemFamily.lehmer_first_rung`), stated for the characteristic polynomial
of any integer matrix so that every polynomial in the proof lives in the
instance path of `Matrix.charpoly` (mixing it with a hand-written `ℤ[X]` sends
the Lean 4.35 kernel into deep recursion on the literal powers). -/
lemma lehmer_of_bridge {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℤ)
    (h : (X - 1) * M.charpoly = X ^ 8 * (X ^ 3 - X - 1) + (X ^ 3 + X ^ 2 - 1)) :
    M.charpoly = X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 := by
  refine mul_left_cancel₀ (a := X - 1) ?_ (h.trans ?_)
  · intro h0
    have h1 := congrArg (fun q => q.eval 2) h0
    simp at h1
  · ring

/-- **`E_10`'s Coxeter polynomial is Lehmer's polynomial.** -/
theorem coxeter_E10_lehmer :
    (CoxElt.cox (Astar 6)).charpoly
      = X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 := by
  have h := coxeter_E_bridge 6
  rw [show (6 : ℕ) + 2 = 8 from rfl] at h
  exact lehmer_of_bridge _ h

/-- Real evaluation of the bridge. -/
lemma bridge_eval (k : ℕ) (y : ℝ) :
    (y - 1) * ((CoxElt.cox (Astar k)).charpoly.map (Int.castRingHom ℝ)).eval y
      = y ^ (k + 2) * (y ^ 3 - y - 1) + (y ^ 3 + y ^ 2 - 1) := by
  have h := congrArg (fun p : Polynomial ℤ => (p.map (Int.castRingHom ℝ)).eval y)
    (coxeter_E_bridge k)
  simpa using h

/-- **McMullen's `E_n → ρ`, kernel-checked through `PdtSalemFamily`.** For `m ≥ 10`, the
largest real eigenvalue `lam m` of the Coxeter element of `W(E_m)` lies in
`[117/100, ρ)`; no real eigenvalue exceeds it; the sequence is strictly
increasing and tends to the plastic number. -/
theorem coxeter_E_plastic {rho : ℝ} (hrho : rho ^ 3 = rho + 1) :
    ∃ lam : ℕ → ℝ,
      (∀ m, 10 ≤ m →
        (117 / 100 ≤ lam m ∧ lam m < rho) ∧
        ((CoxElt.cox (Astar (m - 4))).charpoly.map (Int.castRingHom ℝ)).eval (lam m) = 0 ∧
        ∀ y : ℝ, lam m < y →
          ((CoxElt.cox (Astar (m - 4))).charpoly.map (Int.castRingHom ℝ)).eval y ≠ 0) ∧
      (∀ m, 10 ≤ m → lam m < lam (m + 1)) ∧
      Tendsto lam atTop (nhds rho) := by
  open PDT.SalemFamily in
  refine ⟨fun m => lam (m - 3) rho, ?_, ?_, ?_⟩
  · intro m hm
    have hn : 7 ≤ m - 3 := by omega
    have hk : m - 4 + 2 = m - 3 + 1 := by omega
    have hge := lam_ge_x0 hrho hn
    have hlt := lam_lt_rho hrho hn
    refine ⟨⟨hge, hlt⟩, ?_, ?_⟩
    · have hroot := lam_root hrho hn
      have hb := bridge_eval (m - 4) (lam (m - 3) rho)
      rw [hk] at hb
      unfold chi P Pstar at hroot
      have hne : lam (m - 3) rho - 1 ≠ 0 := by linarith
      have : (lam (m - 3) rho - 1) *
          ((CoxElt.cox (Astar (m - 4))).charpoly.map (Int.castRingHom ℝ)).eval
            (lam (m - 3) rho) = 0 := by rw [hb]; exact hroot
      exact (mul_eq_zero.mp this).resolve_left hne
    · intro y hy hzero
      have hb := bridge_eval (m - 4) y
      rw [hk, hzero, mul_zero] at hb
      have hchi : chi (m - 3) y = 0 := by unfold chi P Pstar; linarith
      rcases lt_or_ge y rho with hyr | hyr
      · exact lam_max hrho hn hy hyr hchi
      · have := chi_pos_of_rho_le hrho (m - 3) hyr
        linarith
  · intro m hm
    have hn : 7 ≤ m - 3 := by omega
    have h := lam_strictMono hrho hn
    have he : m + 1 - 3 = m - 3 + 1 := by omega
    simp only [he]
    exact h
  · obtain ⟨-, -, -⟩ := PDT.SalemFamily.plastic_salem_family hrho
    have ht : Tendsto (fun n => PDT.SalemFamily.lam n rho) atTop (nhds rho) :=
      (tendsto_add_atTop_iff_nat 7).mp (PDT.SalemFamily.mu_tendsto hrho)
    exact ht.comp (tendsto_sub_atTop_nat 3)


/-! ### The compared forms, in core Mathlib vocabulary -/

/-- A matrix given entrywise by the `E_{k+4}` formula of the compared
statements (written with `m = k + 4`) IS `Astar k`: after `k + 4 - 4 = k`,
`k + 4 - 3 = k + 1`, `k + 4 - 2 = k + 2`, `k + 4 - 1 = k + 3`, the edge
condition is literally `adjLt k a b ∨ adjLt k b a`. -/
lemma eq_Astar (k : ℕ) (A : Matrix (Fin (k + 4)) (Fin (k + 4)) ℤ)
    (hA : ∀ a b : Fin (k + 4), A a b =
      if (a : ℕ) = b then 2
      else if (((b : ℕ) = a + 1 ∧ (b : ℕ) ≤ k + 4 - 4) ∨ ((a : ℕ) = k + 4 - 4 ∧ (b : ℕ) = k + 4 - 3) ∨
            ((a : ℕ) = k + 4 - 4 ∧ (b : ℕ) = k + 4 - 2) ∨ ((a : ℕ) = k + 4 - 2 ∧ (b : ℕ) = k + 4 - 1)) ∨
          (((a : ℕ) = b + 1 ∧ (a : ℕ) ≤ k + 4 - 4) ∨ ((b : ℕ) = k + 4 - 4 ∧ (a : ℕ) = k + 4 - 3) ∨
            ((b : ℕ) = k + 4 - 4 ∧ (a : ℕ) = k + 4 - 2) ∨ ((b : ℕ) = k + 4 - 2 ∧ (a : ℕ) = k + 4 - 1))
        then -1 else 0) :
    A = Astar k := by
  have h4 : k + 4 - 4 = k := by omega
  have h3 : k + 4 - 3 = k + 1 := by omega
  have h2 : k + 4 - 2 = k + 2 := by omega
  have h1 : k + 4 - 1 = k + 3 := by omega
  ext a b
  rw [hA]
  simp only [Astar, StarDet.adjLt, h4, h3, h2, h1]
  -- the two sides now differ only in their `Decidable` instances
  exact if_congr Iff.rfl rfl (if_congr Iff.rfl rfl rfl)

/-- Real evaluation of any identity of the bridge shape (stated for a
characteristic polynomial, keeping `Matrix.charpoly`'s instance path). -/
lemma eval_of_bridge {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℤ} {n : ℕ}
    (h : (X - 1) * M.charpoly = X ^ n * (X ^ 3 - X - 1) + (X ^ 3 + X ^ 2 - 1)) (y : ℝ) :
    (y - 1) * (M.charpoly.map (Int.castRingHom ℝ)).eval y
      = y ^ n * (y ^ 3 - y - 1) + (y ^ 3 + y ^ 2 - 1) := by
  have h' := congrArg (fun q => (q.map (Int.castRingHom ℝ)).eval y) h
  simpa using h'

/-- **(18), compared form.** For every `m ≥ 4`, with `A` the generalized
Cartan matrix of the star tree `E_m = T(2,3,m-3)` (long arm `0, …, m-5`,
center `m-4`, short arm `m-3`, arm of length two `m-2, m-1`), the Coxeter
element `s_0 s_1 ⋯ s_{m-1}` (`s_i = 1 - e_i e_iᵀ A`) satisfies
`(X - 1) · charpoly = X^(m-2)·(X³ - X - 1) + (X³ + X² - 1)`. -/
theorem coxeter_E_bridge_explicit (m : ℕ) (hm : 4 ≤ m) (A : Matrix (Fin m) (Fin m) ℤ)
    (hA : ∀ a b : Fin m, A a b =
      if (a : ℕ) = b then 2
      else if (((b : ℕ) = a + 1 ∧ (b : ℕ) ≤ m - 4) ∨ ((a : ℕ) = m - 4 ∧ (b : ℕ) = m - 3) ∨
            ((a : ℕ) = m - 4 ∧ (b : ℕ) = m - 2) ∨ ((a : ℕ) = m - 2 ∧ (b : ℕ) = m - 1)) ∨
          (((a : ℕ) = b + 1 ∧ (a : ℕ) ≤ m - 4) ∨ ((b : ℕ) = m - 4 ∧ (a : ℕ) = m - 3) ∨
            ((b : ℕ) = m - 4 ∧ (a : ℕ) = m - 2) ∨ ((b : ℕ) = m - 2 ∧ (a : ℕ) = m - 1))
        then -1 else 0) :
    (X - 1) * Matrix.charpoly ((List.finRange m).map (fun i =>
        1 - Matrix.diagonal (fun b => if b = i then 1 else 0) * A)).prod
      = X ^ (m - 2) * (X ^ 3 - X - 1) + (X ^ 3 + X ^ 2 - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
  have hAk := eq_Astar k A hA
  subst hAk
  have he : k + 4 - 2 = k + 2 := by omega
  rw [he]
  exact coxeter_E_bridge k

/-- **(19), compared form.** The Coxeter element of `E_10 = T(2,3,7)`, with
its Cartan matrix written out, has Lehmer's polynomial as characteristic
polynomial. -/
theorem coxeter_E10_lehmer_explicit (A : Matrix (Fin 10) (Fin 10) ℤ)
    (hA : A = !![ 2, -1,  0,  0,  0,  0,  0,  0,  0,  0;
                 -1,  2, -1,  0,  0,  0,  0,  0,  0,  0;
                  0, -1,  2, -1,  0,  0,  0,  0,  0,  0;
                  0,  0, -1,  2, -1,  0,  0,  0,  0,  0;
                  0,  0,  0, -1,  2, -1,  0,  0,  0,  0;
                  0,  0,  0,  0, -1,  2, -1,  0,  0,  0;
                  0,  0,  0,  0,  0, -1,  2, -1, -1,  0;
                  0,  0,  0,  0,  0,  0, -1,  2,  0,  0;
                  0,  0,  0,  0,  0,  0, -1,  0,  2, -1;
                  0,  0,  0,  0,  0,  0,  0,  0, -1,  2]) :
    Matrix.charpoly ((List.finRange 10).map (fun i =>
        1 - Matrix.diagonal (fun b => if b = i then 1 else 0) * A)).prod
      = X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 := by
  have hA' : ∀ a b : Fin 10, A a b =
      if (a : ℕ) = b then 2
      else if (((b : ℕ) = a + 1 ∧ (b : ℕ) ≤ 10 - 4) ∨ ((a : ℕ) = 10 - 4 ∧ (b : ℕ) = 10 - 3) ∨
            ((a : ℕ) = 10 - 4 ∧ (b : ℕ) = 10 - 2) ∨ ((a : ℕ) = 10 - 2 ∧ (b : ℕ) = 10 - 1)) ∨
          (((a : ℕ) = b + 1 ∧ (a : ℕ) ≤ 10 - 4) ∨ ((b : ℕ) = 10 - 4 ∧ (a : ℕ) = 10 - 3) ∨
            ((b : ℕ) = 10 - 4 ∧ (a : ℕ) = 10 - 2) ∨ ((b : ℕ) = 10 - 2 ∧ (a : ℕ) = 10 - 1))
        then -1 else 0 := by
    subst hA
    intro a b
    fin_cases a <;> fin_cases b <;> rfl
  have h := coxeter_E_bridge_explicit 10 (by norm_num) A hA'
  rw [show (10 : ℕ) - 2 = 8 from rfl] at h
  exact lehmer_of_bridge _ h

/-- **(20), compared form.** For a family `A m` of `E_m` Cartan matrices
(given entrywise as in (18)), there is `λ : ℕ → ℝ` such that for every
`m ≥ 10`, `λ m ∈ [117/100, ρ)` is a root of the Coxeter polynomial of `E_m`
with no real root above it, `λ` is strictly increasing, and `λ → ρ`. -/
theorem coxeter_E_plastic_explicit (rho : ℝ) (hrho : rho ^ 3 = rho + 1)
    (A : (m : ℕ) → Matrix (Fin m) (Fin m) ℤ)
    (hA : ∀ (m : ℕ) (a b : Fin m), A m a b =
      if (a : ℕ) = b then 2
      else if (((b : ℕ) = a + 1 ∧ (b : ℕ) ≤ m - 4) ∨ ((a : ℕ) = m - 4 ∧ (b : ℕ) = m - 3) ∨
            ((a : ℕ) = m - 4 ∧ (b : ℕ) = m - 2) ∨ ((a : ℕ) = m - 2 ∧ (b : ℕ) = m - 1)) ∨
          (((a : ℕ) = b + 1 ∧ (a : ℕ) ≤ m - 4) ∨ ((b : ℕ) = m - 4 ∧ (a : ℕ) = m - 3) ∨
            ((b : ℕ) = m - 4 ∧ (a : ℕ) = m - 2) ∨ ((b : ℕ) = m - 2 ∧ (a : ℕ) = m - 1))
        then -1 else 0) :
    ∃ lam : ℕ → ℝ,
      (∀ m, 10 ≤ m →
        ((117 / 100 : ℝ) ≤ lam m ∧ lam m < rho) ∧
        ((Matrix.charpoly ((List.finRange m).map (fun i =>
            1 - Matrix.diagonal (fun b => if b = i then 1 else 0) * A m)).prod).map
              (Int.castRingHom ℝ)).eval (lam m) = 0 ∧
        ∀ y : ℝ, lam m < y →
          ((Matrix.charpoly ((List.finRange m).map (fun i =>
            1 - Matrix.diagonal (fun b => if b = i then 1 else 0) * A m)).prod).map
              (Int.castRingHom ℝ)).eval y ≠ 0) ∧
      (∀ m, 10 ≤ m → lam m < lam (m + 1)) ∧
      Filter.Tendsto lam Filter.atTop (nhds rho) := by
  open PDT.SalemFamily in
  refine ⟨fun m => lam (m - 3) rho, ?_, ?_, ?_⟩
  · intro m hm
    have hn : 7 ≤ m - 3 := by omega
    have hk : m - 2 = m - 3 + 1 := by omega
    have hbr := eval_of_bridge (coxeter_E_bridge_explicit m (by omega) (A m) (hA m))
    have hge := lam_ge_x0 hrho hn
    have hlt := lam_lt_rho hrho hn
    refine ⟨⟨hge, hlt⟩, ?_, ?_⟩
    · have hroot := lam_root hrho hn
      have hb := hbr (lam (m - 3) rho)
      rw [hk] at hb
      unfold chi P Pstar at hroot
      have hne : lam (m - 3) rho - 1 ≠ 0 := by linarith
      rw [hroot] at hb
      exact (mul_eq_zero.mp hb).resolve_left hne
    · intro y hy hzero
      have hb := hbr y
      rw [hk, hzero, mul_zero] at hb
      have hchi : chi (m - 3) y = 0 := by unfold chi P Pstar; linarith
      rcases lt_or_ge y rho with hyr | hyr
      · exact lam_max hrho hn hy hyr hchi
      · have := chi_pos_of_rho_le hrho (m - 3) hyr
        linarith
  · intro m hm
    have hn : 7 ≤ m - 3 := by omega
    have h := lam_strictMono hrho hn
    have he : m + 1 - 3 = m - 3 + 1 := by omega
    simp only [he]
    exact h
  · have ht : Tendsto (fun n => PDT.SalemFamily.lam n rho) atTop (nhds rho) :=
      (tendsto_add_atTop_iff_nat 7).mp (PDT.SalemFamily.mu_tendsto hrho)
    exact ht.comp (tendsto_sub_atTop_nat 3)

end PlasticThreshold.CoxeterBridge
