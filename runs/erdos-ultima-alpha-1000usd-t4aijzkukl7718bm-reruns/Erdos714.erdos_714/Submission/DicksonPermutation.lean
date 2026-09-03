import FormalConjecturesUtil

/-!
A finite-field Dickson-polynomial recovery tool. These arithmetic results do
not assert a graph construction or a solution of Erdős Problem 714.
-/

open Matrix Polynomial

namespace Erdos714Dickson

section Trace
variable {R : Type*} [CommRing R]
abbrev Mat2 (R : Type*) := Matrix (Fin 2) (Fin 2) R

lemma cayley_two (M : Mat2 R) : M^2 = M.trace • M - M.det • (1 : Mat2 R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
      Matrix.det_fin_two, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] <;> ring

lemma power_rec (M : Mat2 R) (n : ℕ) :
    M^(n+2) = M.trace • M^(n+1) - M.det • M^n := by
  rw [pow_add, cayley_two, mul_sub, mul_smul_comm, mul_smul_comm, mul_one,
    ← pow_succ]

lemma trace_power_rec (M : Mat2 R) (n : ℕ) :
    (M^(n+2)).trace = M.trace * (M^(n+1)).trace - M.det * (M^n).trace := by
  rw [power_rec, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul]
  rfl

/-- Trace and determinant determine traces of every nonnegative power. -/
theorem trace_power_eq {A B : Mat2 R} (ht : A.trace = B.trace)
    (hd : A.det = B.det) (n : ℕ) : (A^n).trace = (B^n).trace := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simpa using ht
  | more n hn hn1 => rw [trace_power_rec, trace_power_rec, ht, hd, hn, hn1]

lemma trace_fifth (M : Mat2 R) :
    (M^5).trace = M.trace^5 - 5*M.det*M.trace^3 + 5*M.det^2*M.trace := by
  calc
    (M^5).trace = M.trace * (M^4).trace - M.det * (M^3).trace := trace_power_rec M 3
    _ = _ := by
      rw [trace_power_rec M 2, trace_power_rec M 1,
        trace_power_rec M 0]
      simp only [Nat.zero_add, pow_zero, pow_one, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat]
      ring

/-- The explicit fifth Dickson polynomial of the first kind. -/
lemma dickson_five (a : R) :
    Polynomial.dickson 1 a 5 = X^5 - C (5*a)*X^3 + C (5*a^2)*X := by
  norm_num [Polynomial.dickson]
  simp only [map_ofNat]
  ring

end Trace

section FiniteField
variable {F : Type*} [Field F] [Fintype F]

/-- Inverse powering recovers traces, even though the two original matrices
need not be equal or accompanied by a conjugating matrix. -/
theorem trace_recovery {d : ℕ}
    (hc : (Nat.card (GL (Fin 2) F)).Coprime d)
    (A B : GL (Fin 2) F)
    (ht : ((A : Mat2 F)^d).trace = ((B : Mat2 F)^d).trace)
    (hd : ((A : Mat2 F)^d).det = ((B : Mat2 F)^d).det) :
    (A : Mat2 F).trace = (B : Mat2 F).trace := by
  obtain ⟨m, _, hm⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hc.symm
    (Nat.ne_of_gt (Nat.card_pos (α := GL (Fin 2) F)))
  have recover (M : GL (Fin 2) F) : (M^d)^m = M := by
    rw [← pow_mul, ← pow_mod_natCard, hm, pow_mod_natCard, pow_one]
  have h := trace_power_eq ht hd m
  have hA : ((A : Mat2 F)^d)^m = (A : Mat2 F) := by
    exact congrArg Units.val (recover A)
  have hB : ((B : Mat2 F)^d)^m = (B : Mat2 F) := by
    exact congrArg Units.val (recover B)
  rwa [hA,hB] at h

/-- Companion matrices convert polynomial values into matrix traces. -/
def companion (a x : F) : Mat2 F := !![x,-a;1,0]

omit [Fintype F] in
@[simp] lemma companion_trace (a x : F) : (companion a x).trace = x := by
  simp [companion, Matrix.trace_fin_two]

omit [Fintype F] in
@[simp] lemma companion_det (a x : F) : (companion a x).det = a := by
  simp [companion, Matrix.det_fin_two]

/-- The nonzero-parameter Dickson quintic is injective under a precise
finite-group coprimality hypothesis. -/
theorem quintic_injective (a : F) (ha : a ≠ 0)
    (hc : (Nat.card (GL (Fin 2) F)).Coprime 5) :
    Function.Injective (fun x : F => x^5 - 5*a*x^3 + 5*a^2*x) := by
  intro x y he
  let A := Matrix.GeneralLinearGroup.mkOfDetNeZero (companion a x) (by simpa using ha)
  let B := Matrix.GeneralLinearGroup.mkOfDetNeZero (companion a y) (by simpa using ha)
  have ht : ((A : Mat2 F)^5).trace = ((B : Mat2 F)^5).trace := by
    simpa [A, B, trace_fifth] using he
  have hd : ((A : Mat2 F)^5).det = ((B : Mat2 F)^5).det := by
    simp [Matrix.det_pow, A, B]
  have h := trace_recovery hc A B ht hd
  simpa [A,B] using h

/-- The arithmetic exclusions required for fifth powers in the field and in GL₂. -/
lemma coprime_factors {q : ℕ} (hm : q % 5 = 2 ∨ q % 5 = 3) :
    (q-1).Coprime 5 ∧ (q^2-1).Coprime 5 ∧ (q^2-q).Coprime 5 := by
  have hq : 2 ≤ q := by omega
  have hs : q ≤ q^2 := by nlinarith
  have hs1 : 1 ≤ q^2 := by omega
  have hm2 : q^2 % 5 = 4 := by
    rcases hm with h | h <;> norm_num [pow_two, Nat.mul_mod, h]
  have h₁ : (q-1).Coprime 5 := by
    apply Nat.Coprime.symm
    apply Nat.prime_five.coprime_iff_not_dvd.mpr
    intro hd
    have he : (q-1+1)%5 = 1 := by simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
    rw [Nat.sub_add_cancel (by omega)] at he
    omega
  have h₂ : (q^2-1).Coprime 5 := by
    apply Nat.Coprime.symm
    apply Nat.prime_five.coprime_iff_not_dvd.mpr
    intro hd
    have he : (q^2-1+1)%5 = 1 := by simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
    rw [Nat.sub_add_cancel hs1, hm2] at he
    omega
  have h₃ : (q^2-q).Coprime 5 := by
    apply Nat.Coprime.symm
    apply Nat.prime_five.coprime_iff_not_dvd.mpr
    intro hd
    have he : (q^2-q+q)%5 = q%5 := by simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd]
    rw [Nat.sub_add_cancel hs, hm2] at he
    omega
  exact ⟨h₁,h₂,h₃⟩

lemma gl_coprime_five (hm : Fintype.card F % 5 = 2 ∨ Fintype.card F % 5 = 3) :
    (Nat.card (GL (Fin 2) F)).Coprime 5 := by
  rw [Matrix.card_GL_field]
  simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  exact (coprime_factors hm).2.1.mul_left (coprime_factors hm).2.2

lemma field_fifth_injective
    (hm : Fintype.card F % 5 = 2 ∨ Fintype.card F % 5 = 3) :
    Function.Injective (fun x : F => x^5) := by
  have hc : (Nat.card Fˣ).Coprime 5 := by
    simpa only [Nat.card_units, Nat.card_eq_fintype_card] using (coprime_factors hm).1
  intro x y he
  by_cases hx : x = 0
  · subst x
    have hy : y^5 = 0 := by simpa using he.symm
    exact (eq_zero_of_pow_eq_zero hy).symm
  by_cases hy : y = 0
  · subst y
    have hx' : x^5 = 0 := by simpa using he
    exact eq_zero_of_pow_eq_zero hx'
  have hu : (Units.mk0 x hx)^5 = (Units.mk0 y hy)^5 := by
    ext
    exact he
  exact congrArg Units.val (hc.pow_left_bijective.injective hu)

/-- The full Dickson quintic, including parameter zero, permutes the finite
field whenever its order is two or three modulo five. -/
theorem quintic_bijective (a : F)
    (hm : Fintype.card F % 5 = 2 ∨ Fintype.card F % 5 = 3) :
    Function.Bijective (fun x : F => x^5 - 5*a*x^3 + 5*a^2*x) := by
  apply (Finite.injective_iff_bijective).mp
  by_cases ha : a = 0
  · subst a
    simpa using field_fifth_injective hm
  · exact quintic_injective a ha (gl_coprime_five hm)

/-- This is the actual Mathlib Dickson polynomial, not just a similarly
shaped quintic. -/
theorem dickson_five_bijective (a : F)
    (hm : Fintype.card F % 5 = 2 ∨ Fintype.card F % 5 = 3) :
    Function.Bijective (fun x : F => (Polynomial.dickson 1 a 5).eval x) := by
  have he : (fun x : F => (Polynomial.dickson 1 a 5).eval x) =
      (fun x : F => x^5 - 5*a*x^3 + 5*a^2*x) := by
    funext x
    rw [dickson_five]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_C, eval_X]
  rw [he]
  exact quintic_bijective a hm

variable [CharP F 3]

/-- In characteristic three the same permutation has the stated sparse form. -/
theorem sparse_quintic_bijective (a : F)
    (hm : Fintype.card F % 5 = 2 ∨ Fintype.card F % 5 = 3) :
    Function.Bijective (fun x : F => x^5 + a*x^3 - a^2*x) := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have h5 : (5 : F) = -1 := by linear_combination 2*h3
  have he : (fun x : F => x^5 - 5*a*x^3 + 5*a^2*x) =
      (fun x : F => x^5 + a*x^3 - a^2*x) := by
    funext x
    rw [h5]
    ring
  rw [← he]
  exact quintic_bijective a hm

/-- Consequently a sparse Dickson equation has exactly one solution. -/
theorem sparse_quintic_unique (a b : F)
    (hm : Fintype.card F % 5 = 2 ∨ Fintype.card F % 5 = 3) :
    ∃! x : F, x^5 + a*x^3 - a^2*x = b := by
  obtain ⟨x,hx⟩ := (sparse_quintic_bijective a hm).surjective b
  exact ⟨x,hx,fun y hy => (sparse_quintic_bijective a hm).injective (hy.trans hx.symm)⟩

end FiniteField

lemma odd_power_three_mod_five (k : ℕ) :
    3^(2*k+1)%5 = 2 ∨ 3^(2*k+1)%5 = 3 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have he : 2*(k+1)+1 = (2*k+1)+2 := by omega
    rw [he, pow_add, Nat.mul_mod]
    rcases ih with h | h <;> norm_num [h]

/-- An unbounded, explicitly specified family of fields with unique recovery. -/
theorem odd_galois_unique (k : ℕ) (a b : GaloisField 3 (2*k+1)) :
    ∃! x : GaloisField 3 (2*k+1), x^5 + a*x^3 - a^2*x = b := by
  letI : Fintype (GaloisField 3 (2*k+1)) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField 3 (2*k+1)) = 3^(2*k+1) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 _ (by omega)]
  exact sparse_quintic_unique a b (hc ▸ odd_power_three_mod_five k)

end Erdos714Dickson

#print axioms Erdos714Dickson.trace_recovery
#print axioms Erdos714Dickson.quintic_injective

#print axioms Erdos714Dickson.dickson_five_bijective
#print axioms Erdos714Dickson.sparse_quintic_unique
#print axioms Erdos714Dickson.odd_galois_unique
