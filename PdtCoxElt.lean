module
public import Mathlib

@[expose] public section
/-!
# The Coxeter element of a generalized Cartan matrix

The Coxeter element of a generalized Cartan matrix `A` as the ordered product
of the simple reflections `s_i = 1 - e_i e_iᵀ A` (the geometric representation
in the basis of simple roots: `s_i α_j = α_j - A_{ij} α_i`), and the identity
`U * (s_0 s_1 ⋯ s_{n-1}) = U - A` (Howlett's `c = -U⁻¹L`), proved by a
list induction in which every step is ring algebra.  For symmetric `A` with
diagonal `2` this gives `charpoly (s_0 ⋯ s_{n-1}) = det (X·U + Uᵀ)`.
-/

namespace PlasticThreshold.CoxElt

open Matrix

variable {n : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) R)

/-- The coordinate projector `e_i e_iᵀ`. -/
def E (i : Fin n) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal (fun b => if b = i then 1 else 0)

/-- The simple reflection `s_i v = v - (A v)_i e_i`. -/
def refl (i : Fin n) : Matrix (Fin n) (Fin n) R := 1 - E i * A

/-- The diagonal projector onto the coordinates listed in `l`. -/
def F (l : List (Fin n)) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal (fun b => if b ∈ l then 1 else 0)

/-- The "already-passed" strictly-upper part, built along the list. -/
def Nl : List (Fin n) → Matrix (Fin n) (Fin n) R
  | [] => 0
  | i :: l => Nl l + E i * A * F l

/-- The ordered product of reflections along `l`. -/
def P (l : List (Fin n)) : Matrix (Fin n) (Fin n) R := (l.map (refl A)).prod

/-- **The Coxeter element** `s_0 s_1 ⋯ s_{n-1}`. -/
def cox : Matrix (Fin n) (Fin n) R := P A (List.finRange n)

lemma F_nil : (F [] : Matrix (Fin n) (Fin n) R) = 0 := by
  simp [F]

lemma F_mul_E {l : List (Fin n)} {i : Fin n} :
    (F l : Matrix (Fin n) (Fin n) R) * E i = if i ∈ l then E i else 0 := by
  unfold F E
  rw [diagonal_mul_diagonal]
  split_ifs with h
  · congr 1; funext b; by_cases hb : b = i
    · subst hb; simp [h]
    · simp [hb]
  · rw [← diagonal_zero]; congr 1; funext b; by_cases hb : b = i
    · subst hb; simp [h]
    · simp [hb]

lemma E_mul_F {l : List (Fin n)} {i : Fin n} :
    (E i : Matrix (Fin n) (Fin n) R) * F l = if i ∈ l then E i else 0 := by
  unfold F E
  rw [diagonal_mul_diagonal]
  split_ifs with h
  · congr 1; funext b; by_cases hb : b = i
    · subst hb; simp [h]
    · simp [hb]
  · rw [← diagonal_zero]; congr 1; funext b; by_cases hb : b = i
    · subst hb; simp [h]
    · simp [hb]

lemma F_mul_F_self (l : List (Fin n)) :
    (F l : Matrix (Fin n) (Fin n) R) * F l = F l := by
  unfold F
  rw [diagonal_mul_diagonal]
  congr 1; funext b; split_ifs <;> simp

lemma F_cons (i : Fin n) (l : List (Fin n)) (hi : i ∉ l) :
    (F (i :: l) : Matrix (Fin n) (Fin n) R) = E i + F l := by
  unfold F E
  rw [diagonal_add]
  congr 1; funext b
  by_cases hb : b = i
  · subst hb; simp [hi]
  · simp [hb]

lemma Nl_mul_E (i : Fin n) : ∀ (l : List (Fin n)), i ∉ l → Nl A l * E i = 0
  | [] => by intro _; simp [Nl]
  | j :: l => by
    intro hi
    simp only [List.mem_cons, not_or] at hi
    simp only [Nl, add_mul, mul_assoc, F_mul_E, hi.2, ite_false, mul_zero, add_zero]
    exact Nl_mul_E i l hi.2

lemma aux_FF {S : Type*} [Ring S] (e f : S) (hef : e * f = 0) (hff : f * f = f) :
    (1 - (e + f)) * (1 - f) = 1 - (e + f) := by
  calc (1 - (e + f)) * (1 - f) = 1 - e - f - f + e * f + f * f := by noncomm_ring
    _ = 1 - (e + f) := by rw [hef, hff]; noncomm_ring

/-- Rows outside `l` are untouched: `(1 - F l) · P l = 1 - F l`. -/
lemma rows_fixed : ∀ (l : List (Fin n)), l.Nodup →
    (1 - F l) * P A l = (1 - F l : Matrix (Fin n) (Fin n) R)
  | [] => by intro _; simp [P, F_nil]
  | i :: l => by
    intro hnd
    have hi : i ∉ l := (List.nodup_cons.mp hnd).1
    have ih := rows_fixed l (List.nodup_cons.mp hnd).2
    have hFE : (F (i :: l) : Matrix (Fin n) (Fin n) R) * E i = E i := by
      rw [F_mul_E]; simp
    have hEF : (E i : Matrix (Fin n) (Fin n) R) * F l = 0 := by rw [E_mul_F]; simp [hi]
    have hFF : (1 - F (i :: l)) * (1 - F l) = (1 - F (i :: l) : Matrix (Fin n) (Fin n) R) := by
      rw [F_cons i l hi]
      exact aux_FF _ _ hEF (F_mul_F_self l)
    have step : (1 - F (i :: l)) * P A (i :: l)
        = (1 - F (i :: l)) * P A l - ((1 - F (i :: l)) * E i) * A * P A l := by
      simp only [P, List.map_cons, List.prod_cons, refl]
      noncomm_ring
    rw [step]
    have h0 : (1 - F (i :: l)) * E i = (0 : Matrix (Fin n) (Fin n) R) := by
      rw [sub_mul, one_mul, hFE, sub_self]
    rw [h0, zero_mul, zero_mul, sub_zero, ← hFF, mul_assoc, ih, hFF]

/-- **The ring-algebra step** of the main induction, in any ring. -/
lemma key_step {S : Type*} [Ring S] (u e a f p : S)
    (hue : u * e = e) (hfe : f * e = 0) (hu : u * p = u - f * a)
    (hrows : (1 - f) * p = 1 - f) :
    (u + e * a * f) * ((1 - e * a) * p) = (u + e * a * f) - (e + f) * a := by
  have hfp : f * p = p - (1 - f) := by rw [← hrows]; noncomm_ring
  calc (u + e * a * f) * ((1 - e * a) * p)
      = u * p - (u * e) * a * p + e * a * (f * p) - e * a * (f * e) * a * p := by
        noncomm_ring
    _ = (u - f * a) - e * a * p + e * a * (p - (1 - f)) - 0 := by
        rw [hu, hue, hfe, hfp]; noncomm_ring
    _ = (u + e * a * f) - (e + f) * a := by noncomm_ring

/-- **Main identity along a list**: `(1 + N_l) · P_l = (1 + N_l) - F_l · A`. -/
theorem main_list : ∀ (l : List (Fin n)), l.Nodup →
    (1 + Nl A l) * P A l = (1 + Nl A l) - F l * A
  | [] => by intro _; simp [Nl, P, F_nil]
  | i :: l => by
    intro hnd
    have hi : i ∉ l := (List.nodup_cons.mp hnd).1
    have hl := (List.nodup_cons.mp hnd).2
    have ih := main_list l hl
    have hue : (1 + Nl A l) * E i = E i := by rw [add_mul, one_mul, Nl_mul_E A i l hi, add_zero]
    have hfe : (F l : Matrix (Fin n) (Fin n) R) * E i = 0 := by rw [F_mul_E]; simp [hi]
    have hP : P A (i :: l) = (1 - E i * A) * P A l := by simp [P, refl]
    rw [hP, F_cons i l hi]
    simp only [Nl]
    rw [← add_assoc]
    exact key_step _ _ _ _ _ hue hfe ih (rows_fixed A l hl)

/-- `N` along an increasing list is the strictly upper part on its members. -/
lemma Nl_sorted : ∀ (l : List (Fin n)), l.Pairwise (· < ·) →
    ∀ a b, Nl A l a b = if a ∈ l ∧ b ∈ l ∧ a < b then A a b else 0
  | [] => by intro _ a b; simp [Nl]
  | i :: l => by
    intro hs a b
    have hs' := List.pairwise_cons.mp hs
    have ih := Nl_sorted l hs'.2 a b
    have hil : i ∉ l := fun h => lt_irrefl _ (hs'.1 i h)
    simp only [Nl, Matrix.add_apply, ih, E, F, mul_diagonal, diagonal_mul, List.mem_cons]
    by_cases ha : a = i
    · subst ha
      by_cases hb : b ∈ l
      · have hab : a < b := hs'.1 b hb
        simp [hil, hb, hab]
      · have hba : ¬ b = a ∨ ¬ a < b := by
          by_cases h : b = a
          · right; rw [h]; exact lt_irrefl _
          · left; exact h
        rcases hba with h | h <;> simp [hil, hb, h]
    · by_cases hal : a ∈ l
      · by_cases hb : b = i
        · subst hb
          have : b < a := hs'.1 a hal
          have hn : ¬ a < b := not_lt.mpr this.le
          simp [ha, hal, hn, hil]
        · simp [ha, hal, hb]
      · simp [ha, hal]

/-- The unipotent upper factor `U` of `A = U + L`. -/
def Uup : Matrix (Fin n) (Fin n) R := fun a b =>
  if a < b then A a b else if a = b then 1 else 0

lemma one_add_Nl_finRange : 1 + Nl A (List.finRange n) = Uup A := by
  ext a b
  rw [Matrix.add_apply, Nl_sorted A _ (List.pairwise_lt_finRange n)]
  simp only [List.mem_finRange, true_and, Uup, one_apply]
  by_cases h : a < b
  · simp [h, ne_of_lt h]
  · by_cases h' : a = b <;> simp [h, h']

lemma F_finRange : (F (List.finRange n) : Matrix (Fin n) (Fin n) R) = 1 := by
  simp [F]

/-- **Howlett's identity** `U · (s_0 s_1 ⋯ s_{n-1}) = U - A`, i.e. `c = -U⁻¹L`. -/
theorem U_mul_cox : Uup A * cox A = Uup A - A := by
  have h := main_list A (List.finRange n) (List.nodup_finRange n)
  rw [one_add_Nl_finRange, F_finRange, one_mul] at h
  exact h

lemma Uup_upperTriangular : (Uup A).BlockTriangular id := by
  intro i j hij
  simp only [Uup, id] at hij ⊢
  have h1 : ¬ i < j := not_lt.mpr hij.le
  have h2 : ¬ i = j := ne_of_gt hij
  simp [h1, h2]

lemma det_Uup_map :
    ((Uup A).map (Polynomial.C : R →+* Polynomial R)).det = 1 := by
  rw [det_of_isUpperTriangular]
  · simp [Uup]
  · intro i j hij
    simp only [map_apply, id] at hij ⊢
    rw [Uup_upperTriangular A hij, map_zero]

/-- **The Coxeter polynomial as a determinant**: for a symmetric `A` with
diagonal `2`, `charpoly (s_0 ⋯ s_{n-1}) = det (X·U + Uᵀ)`. -/
theorem charpoly_cox (hsymm : Aᵀ = A) (hdiag : ∀ i, A i i = 2) :
    (cox A).charpoly =
      ((Polynomial.X : Polynomial R) • (Uup A).map Polynomial.C
        + ((Uup A)ᵀ).map Polynomial.C).det := by
  have hL : Uup A - A = -(Uup A)ᵀ := by
    ext a b
    simp only [Matrix.sub_apply, Matrix.neg_apply, transpose_apply, Uup]
    by_cases h : a < b
    · have : ¬ b < a := not_lt.mpr h.le
      have hne : ¬ b = a := ne_of_gt h
      simp [h, this, hne]
    · by_cases h' : a = b
      · subst h'; simp [hdiag]; norm_num
      · have hba : b < a := lt_of_le_of_ne (not_lt.mp h) (Ne.symm h')
        have hs : A a b = A b a := by
          have := congrFun (congrFun hsymm b) a
          simpa [transpose_apply] using this
        simp [h, h', hba, hs]
  rw [charpoly, ← one_mul (charmatrix (cox A)).det, ← det_Uup_map A, ← det_mul]
  congr 1
  have hmap : (Uup A).map (Polynomial.C : R →+* Polynomial R) * (cox A).map Polynomial.C
      = (-(Uup A)ᵀ).map Polynomial.C := by
    rw [← Matrix.map_mul, U_mul_cox, hL]
  rw [charmatrix, mul_sub, RingHom.mapMatrix_apply, hmap, scalar_apply]
  refine Matrix.ext fun a b => ?_
  simp only [mul_diagonal, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.map_apply, Matrix.neg_apply, smul_eq_mul, map_neg, transpose_apply]
  ring

end PlasticThreshold.CoxElt
