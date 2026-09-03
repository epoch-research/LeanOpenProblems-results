import Submission.No9Completion
import Submission.DivisorRepair

/-!
# A composite exceptional modulus cannot repair a no-3 odd family

This is a consequence of the verified no-9 obstruction. A composite extra
class has three distinct divisor resources, which repair it at the fresh
first ternary level. The repaired cover would have no modulus divisible by9.
The prime exceptional case is not excluded by this argument.
-/

namespace Erdos7NoThreeCompositeException
open Erdos7Reduction

variable {I : Type*} [Fintype I]

/-- Three distinct cofactor divisors suffice to turn an exceptional class into
three new, distinct moduli containing exactly one factor of3. Such a near-cover
would contradict the no-9 theorem. -/
theorem not_cover_with_composite_exception
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d r : ℕ) (hd : Odd d) (hd3 : ¬ 3 ∣ d)
    (hr : 1 < r) (hrd : r < d) (hrdiv : r ∣ d) (b : ℤ) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ (d : ℤ) ∣ x-b) := by
  classical
  intro hcover
  let e : Fin 3 → ℕ := ![1,r,d]
  have hei : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [e] at * <;> omega
  have hediv : ∀ t, e t ∣ d := by
    intro t
    fin_cases t
    · exact one_dvd d
    · exact hrdiv
    · exact dvd_rfl
  have heodd : ∀ t, Odd (e t) := fun t => hd.of_dvd_nat (hediv t)
  have hepos : ∀ t, 0 < e t := fun t => (heodd t).pos
  have heno3 : ∀ t, ¬ 3 ∣ e t := fun t ht => hd3 (ht.trans (hediv t))
  let n : I ⊕ Fin 3 → ℕ := Sum.elim m (fun t => 3*e t)
  let c : I ⊕ Fin 3 → ℤ := Sum.elim a (fun t => b+(d : ℤ)*t.val)
  have hninj : Function.Injective n := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (hinj hij)
      | inr t =>
        apply False.elim
        apply h3 i
        change m i=3*e t at hij
        rw [hij]
        exact dvd_mul_right _ _
    | inr t =>
      cases j with
      | inl j =>
        apply False.elim
        apply h3 j
        change 3*e t=m j at hij
        rw [← hij]
        exact dvd_mul_right _ _
      | inr u =>
        apply congrArg Sum.inr
        exact hei (Nat.mul_left_cancel (by decide : 0 < 3) hij)
  have hn : ∀ i, 1 < n i ∧ Odd (n i) := by
    intro i
    cases i with
    | inl i => exact hm i
    | inr t =>
      change 1 < 3*e t ∧ Odd (3*e t)
      refine ⟨?_,(by decide : Odd (3 : ℕ)).mul (heodd t)⟩
      have ht := hepos t
      omega
  have hncov : ∀ x : ℤ, ∃ i, (n i : ℤ) ∣ x-c i := by
    intro x
    rcases hcover x with ⟨i,hi⟩ | hx
    · exact ⟨Sum.inl i,hi⟩
    · obtain ⟨t,ht⟩ := Erdos7DivisorRepair.repair_one 3 1 0 d
        (by decide) (by decide) e hediv b x (by simpa using hx)
      exact ⟨Sum.inr t,by simpa [n,c] using ht⟩
  obtain ⟨i,hi⟩ := Erdos7No9Certificate.arithmetic_exists_nine n c ⟨hninj,hn,hncov⟩
  cases i with
  | inl i => exact h3 i ((by norm_num : (3 : ℕ) ∣ 9).trans hi)
  | inr t =>
    apply heno3 t
    change 3*3 ∣ 3*e t at hi
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp hi

/-- If a no-3 distinct odd family plus one nontrivial no-3 odd class covers,
that exceptional modulus has to be prime. This does not exclude that case. -/
theorem exceptional_modulus_prime
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : ℕ) (hd : 1 < d ∧ Odd d) (hd3 : ¬ 3 ∣ d) (b : ℤ)
    (hcover : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ (d : ℤ) ∣ x-b) :
    d.Prime := by
  by_contra hn
  obtain ⟨r,hrdiv,hr,hrd⟩ := (Nat.not_prime_iff_exists_dvd_lt (by omega : 2 ≤ d)).mp hn
  exact not_cover_with_composite_exception m a hinj hm h3 d r hd.2 hd3
    (by omega) hrd hrdiv b hcover

#print axioms not_cover_with_composite_exception
#print axioms exceptional_modulus_prime
end Erdos7NoThreeCompositeException
