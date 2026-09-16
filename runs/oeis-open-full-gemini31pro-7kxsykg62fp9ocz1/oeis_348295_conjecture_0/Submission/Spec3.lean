import Mathlib
import Submission.Spec2

noncomputable def b (k : ℤ) : ℤ :=
  let exponent_real : ℝ := (k : ℝ) * (Real.sqrt 2 - 1)
  let exponent_int : ℤ := Int.floor exponent_real
  (-1 : ℤ) ^ exponent_int.toNat

noncomputable def S (N : ℤ) : ℤ :=
  Finset.sum (Finset.Ioc 0 N) b

lemma sum_split (f : ℤ → ℤ) (x y z : ℤ) (h1 : x ≤ y) (h2 : y ≤ z) :
  Finset.sum (Finset.Ioc x z) f = Finset.sum (Finset.Ioc x y) f + Finset.sum (Finset.Ioc y z) f := by
  sorry

lemma S_add (A B : ℤ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
  S (A + B) = S A + Finset.sum (Finset.Ioc 0 B) (fun k => b (A + k)) := by
  sorry


lemma b_eq (k : ℤ) (hk : 0 < k) :
  let x : ℤ := sorry
  b k = (-1 : ℤ) ^ (x - k).toNat := by
  sorry

lemma b_jump_P_odd (P Q : ℤ) (hP : 0 < P) (hQ_pos : 0 < Q) (hQ : Q^2 = 2*P^2 - 1) :
  ∀ k ∈ Finset.Ioc 0 P, b (k + P) = b k := by
  sorry

lemma b_jump_P_even (P Q : ℤ) (hP : 0 < P) (hQ_pos : 0 < Q) (hQ : Q^2 = 2*P^2 + 1) :
  ∀ k ∈ Finset.Ioc 0 P, b (k + P) = -b k := by
  sorry

lemma b_jump_2P_even (P Q P_prev : ℤ) (hP : 0 < P) (hQ_pos : 0 < Q) (hQ : Q^2 = 2*P^2 + 1) 
  (hP_prev : 2 * P_prev^2 ≤ P^2 - 1) (h_pos : 0 ≤ P_prev) :
  ∀ k ∈ Finset.Ioc 0 P_prev, b (k + 2*P) = b k := by
  sorry

