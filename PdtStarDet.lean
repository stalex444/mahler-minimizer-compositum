import Mathlib

/-!
# The star-tree determinant `det(x·U + Uᵀ)` for `E_m = T(2,3,m-3)`

The Coxeter-polynomial determinant of the `E_m` star tree `T(2,3,m-3)`,
`m = k + 4`, as `det(x·U + Uᵀ)`, `U` the unipotent upper part of the
generalized Cartan matrix.  Index `0` = tip of the long arm, `0..k-1` long arm,
`k` = center, `k+1` = the short arm, `k+2, k+3` = the arm of length two.
The closed form `det_M_closed` is proved by the leaf recurrence along the long
arm (`det_M_rec`) from the two base cases `k = 0, 1`, over any commutative ring.
-/

namespace PlasticThreshold.StarDet

open Matrix

/-- Adjacency of the star tree with long arm of `k` nodes, on ℕ indices
`i < j`. -/
def adjLt (k i j : ℕ) : Prop :=
  (j = i + 1 ∧ j ≤ k) ∨ (i = k ∧ j = k + 1) ∨ (i = k ∧ j = k + 2) ∨
    (i = k + 2 ∧ j = k + 3)

instance (k i j : ℕ) : Decidable (adjLt k i j) := by unfold adjLt; infer_instance

variable {R : Type*} [CommRing R]

/-- `x • U + Uᵀ` for the star tree: diagonal `x + 1`, upper edge `-x`,
lower edge `-1`. -/
def M (x : R) (k : ℕ) : Matrix (Fin (k + 4)) (Fin (k + 4)) R := fun i j =>
  if (i : ℕ) = j then x + 1
  else if adjLt k i j then -x
  else if adjLt k j i then -1
  else 0

lemma adjLt_succ (k i j : ℕ) : adjLt (k + 1) (i + 1) (j + 1) ↔ adjLt k i j := by
  unfold adjLt; omega

/-- Deleting the tip of the long arm gives the next-shorter star tree. -/
lemma M_shift (x : R) (k : ℕ) :
    (M x (k + 1)).submatrix Fin.succ Fin.succ = M x k := by
  ext i j
  simp only [submatrix_apply, M, Fin.val_succ, adjLt_succ]
  simp only [Nat.add_right_cancel_iff]

lemma M_row0 (x : R) (k : ℕ) (hk : 1 ≤ k) (j : Fin (k + 4)) (hj : 2 ≤ (j : ℕ)) :
    M x k 0 j = 0 := by
  simp only [M, Fin.val_zero]
  have h1 : ¬ (0 = (j : ℕ)) := by omega
  have h2 : ¬ adjLt k 0 j := by unfold adjLt; omega
  have h3 : ¬ adjLt k j 0 := by unfold adjLt; omega
  simp [h1, h2, h3]

lemma M_col0 (x : R) (k : ℕ) (hk : 1 ≤ k) (i : Fin (k + 4)) (hi : 2 ≤ (i : ℕ)) :
    M x k i 0 = 0 := by
  simp only [M, Fin.val_zero]
  have h1 : ¬ ((i : ℕ) = 0) := by omega
  have h2 : ¬ adjLt k i 0 := by unfold adjLt; omega
  have h3 : ¬ adjLt k 0 i := by unfold adjLt; omega
  simp [h1, h2, h3]

lemma M_00 (x : R) (k : ℕ) : M x k 0 0 = x + 1 := by simp [M]

lemma M_01 (x : R) (k : ℕ) (hk : 1 ≤ k) : M x k 0 1 = -x := by
  have h : adjLt k 0 1 := by unfold adjLt; omega
  simp [M, h]

lemma M_10 (x : R) (k : ℕ) (hk : 1 ≤ k) : M x k 1 0 = -1 := by
  have h1 : ¬ adjLt k 1 0 := by unfold adjLt; omega
  have h2 : adjLt k 0 1 := by unfold adjLt; omega
  simp [M, h1, h2]

/-- The minor deleting row 0 and column 1 has determinant `-det (M x k)`. -/
lemma det_minor01 (x : R) (k : ℕ) :
    ((M x (k + 2)).submatrix Fin.succ (Fin.succAbove 1)).det = -(M x k).det := by
  rw [det_succ_column_zero, Fin.sum_univ_succ,
    Finset.sum_eq_zero (fun i _ => by
      rw [submatrix_apply, Fin.one_succAbove_zero,
        M_col0 x (k + 2) (by omega) _ (by simp)]
      ring)]
  rw [add_zero, submatrix_apply, Fin.one_succAbove_zero, Fin.succAbove_zero,
    submatrix_submatrix, Fin.succ_zero_eq_one, M_10 x (k + 2) (by omega)]
  have hf : (Fin.succAbove (1 : Fin (k + 2 + 4)) ∘ Fin.succ : Fin (k + 4) → Fin (k + 2 + 4))
      = Fin.succ ∘ Fin.succ := by
    funext j; simp
  rw [hf, ← submatrix_submatrix, M_shift, M_shift]
  simp

/-- **The leaf recurrence** along the long arm. -/
theorem det_M_rec (x : R) (k : ℕ) :
    (M x (k + 2)).det = (x + 1) * (M x (k + 1)).det - x * (M x k).det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Finset.sum_eq_zero (fun j _ => by
      rw [M_row0 x (k + 2) (by omega) _ (by simp)]
      ring)]
  rw [add_zero, Fin.succAbove_zero, M_shift, M_00, Fin.succ_zero_eq_one,
    M_01 x (k + 2) (by omega), det_minor01]
  simp
  ring

/-! ### Base cases and the closed form -/

lemma M0_eq (x : R) : M x 0 = !![x + 1, -x, -x, 0;
                                  -1, x + 1, 0, 0;
                                  -1, 0, x + 1, -x;
                                  0, 0, -1, x + 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, adjLt]

lemma M1_eq (x : R) : M x 1 = !![x + 1, -x, 0, 0, 0;
                                  -1, x + 1, -x, -x, 0;
                                  0, -1, x + 1, 0, 0;
                                  0, -1, 0, x + 1, -x;
                                  0, 0, 0, -1, x + 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M, adjLt]

theorem det_M0 (x : R) : (M x 0).det = x ^ 4 + x ^ 3 + x ^ 2 + x + 1 := by
  rw [M0_eq, det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_succ_row_zero, Fin.succAbove]
  ring

theorem det_M1 (x : R) : (M x 1).det = x ^ 5 + x ^ 4 + x + 1 := by
  rw [M1_eq, det_succ_row_zero]
  simp [Fin.sum_univ_succ, det_succ_row_zero, Fin.succAbove]
  ring

/-- **The closed form**: `(x - 1) · det(x U + Uᵀ)` for `E_{k+4}` is
`x^(k+2)·(x³ - x - 1) + (x³ + x² - 1)`, i.e. `χ_{k+1}` of the Bedford–Kim
family (`PDT.SalemFamily.chi (k+1)`). -/
theorem det_M_closed (x : R) (k : ℕ) :
    (x - 1) * (M x k).det = x ^ (k + 2) * (x ^ 3 - x - 1) + (x ^ 3 + x ^ 2 - 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => rw [det_M0]; ring
    | 1, _ => rw [det_M1]; ring
    | k + 2, ih =>
      rw [det_M_rec]
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have e : (x - 1) * ((x + 1) * (M x (k + 1)).det - x * (M x k).det)
          = (x + 1) * ((x - 1) * (M x (k + 1)).det) - x * ((x - 1) * (M x k).det) := by
        ring
      rw [e, h1, h0]
      ring

end PlasticThreshold.StarDet
