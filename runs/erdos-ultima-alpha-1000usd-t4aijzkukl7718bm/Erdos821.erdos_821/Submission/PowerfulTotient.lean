import Submission.SquarefreeInput

/-!
# Injectivity of the totient function on powerful inputs

Prime powers have smooth totients relative to their input size, but this
does not create collisions: totient is injective on the positive powerful
integers. This structural fact does not settle Erdős 821.
-/

open Nat
open scoped Classical BigOperators

namespace Erdos821

/-- Every prime appearing in a powerful integer appears at least twice.
The convention at zero is harmless for the injectivity statement. -/
def PowerfulInput (a : ℕ) : Prop := ∀ p ∈ a.primeFactors, p^2 ∣ a

lemma predecessor_product_split (P Q : Finset ℕ) :
    (∏ q ∈ P, (q-1)) =
      (∏ q ∈ P \ Q, (q-1)) * ∏ q ∈ P ∩ Q, (q-1) := by
  have he : P \ (P ∩ Q) = P \ Q := by ext q; simp
  have h := Finset.prod_sdiff (f := fun q : ℕ => q-1)
    (show P ∩ Q ⊆ P from Finset.inter_subset_left)
  rw [he] at h
  exact h.symm

/-- After cancelling predecessor factors of common input primes, the
remaining cross-product identity involves only the differing supports. -/
lemma totient_collision_support_identity {a b : ℕ}
    (hφ : Nat.totient a = Nat.totient b) :
    a * (∏ q ∈ a.primeFactors \ b.primeFactors, (q-1)) *
      (∏ q ∈ b.primeFactors, q) =
    b * (∏ q ∈ b.primeFactors \ a.primeFactors, (q-1)) *
      (∏ q ∈ a.primeFactors, q) := by
  let C := ∏ q ∈ a.primeFactors ∩ b.primeFactors, (q-1)
  have hC : 0 < C := by
    apply Finset.prod_pos
    intro q hq
    have hprime := Nat.prime_of_mem_primeFactors (Finset.mem_inter.mp hq).1
    have := hprime.two_le
    omega
  have he : (a * ∏ q ∈ a.primeFactors, (q-1)) * (∏ q ∈ b.primeFactors, q) =
      (b * ∏ q ∈ b.primeFactors, (q-1)) * (∏ q ∈ a.primeFactors, q) := by
    rw [← Nat.totient_mul_prod_primeFactors, ← Nat.totient_mul_prod_primeFactors, hφ]
    ring
  rw [predecessor_product_split a.primeFactors b.primeFactors,
    predecessor_product_split b.primeFactors a.primeFactors,
    Finset.inter_comm b.primeFactors a.primeFactors] at he
  apply Nat.eq_of_mul_eq_mul_right hC
  simpa only [C, mul_assoc, mul_left_comm, mul_comm] using he

/-- The largest prime in only one support cannot occur with exponent at
least two on that side of a totient collision. -/
lemma not_sq_dvd_of_largest_support_difference {a b p : ℕ} (hb : b ≠ 0)
    (hφ : Nat.totient a = Nat.totient b)
    (hp : p ∈ a.primeFactors \ b.primeFactors)
    (hmax : ∀ q ∈ b.primeFactors \ a.primeFactors, q ≤ p) :
    ¬p^2 ∣ a := by
  have hpa := (Finset.mem_sdiff.mp hp).1
  have hpb := (Finset.mem_sdiff.mp hp).2
  have hpprime := Nat.prime_of_mem_primeFactors hpa
  have hcopB : Nat.Coprime p b := by
    apply hpprime.coprime_iff_not_dvd.mpr
    intro hd
    exact hpb (hpprime.mem_primeFactors hd hb)
  have hcopV : Nat.Coprime p (∏ q ∈ b.primeFactors \ a.primeFactors, (q-1)) := by
    apply Nat.Coprime.prod_right
    intro q hq
    have hqprime := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1
    have hq2 := hqprime.two_le
    have hqp := hmax q hq
    apply hpprime.coprime_iff_not_dvd.mpr
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  intro hp2
  have hd : p^2 ∣ a * (∏ q ∈ a.primeFactors \ b.primeFactors, (q-1)) *
      (∏ q ∈ b.primeFactors, q) :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hp2 _) _
  rw [totient_collision_support_identity hφ] at hd
  have hdRad : p^2 ∣ ∏ q ∈ a.primeFactors, q :=
    ((hcopB.mul_right hcopV).pow_left 2).dvd_of_dvd_mul_left hd
  have hSq := squarefree_prod_of_primes a.primeFactors
    (fun q hq => Nat.prime_of_mem_primeFactors hq)
  exact (Nat.squarefree_iff_prime_squarefree.mp hSq p hpprime) (by simpa [pow_two] using hdRad)

/-- Only primes occurring in one input support but not the other need the
powerful hypothesis. Shared prime powers need not satisfy any restriction. -/
lemma eq_of_totient_eq_of_powerful_differences {a b : ℕ}
    (hφ : Nat.totient a = Nat.totient b)
    (ha : ∀ p ∈ a.primeFactors \ b.primeFactors, p^2 ∣ a)
    (hb : ∀ p ∈ b.primeFactors \ a.primeFactors, p^2 ∣ b) : a = b := by
  by_cases hb0 : b = 0
  · subst b
    simpa only [Nat.totient_zero, Nat.totient_eq_zero] using hφ
  have ha0 : a ≠ 0 := by
    intro h
    have : Nat.totient b = 0 := by simpa [h] using hφ.symm
    exact hb0 (Nat.totient_eq_zero.mp this)
  apply eq_of_totient_eq_of_primeFactors_eq hφ
  by_contra hne
  let S := (a.primeFactors \ b.primeFactors) ∪ (b.primeFactors \ a.primeFactors)
  have hS : S.Nonempty := by
    by_contra h
    have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    apply hne
    ext p
    have hp : p ∉ S := by rw [he]; simp
    simp only [S, Finset.mem_union, Finset.mem_sdiff] at hp
    tauto
  let p := S.max' hS
  have hpS : p ∈ S := Finset.max'_mem _ _
  obtain hp | hp := Finset.mem_union.mp hpS
  · apply not_sq_dvd_of_largest_support_difference hb0 hφ hp
      (fun q hq => Finset.le_max' S q (Finset.mem_union_right _ hq))
    exact ha p hp
  · apply not_sq_dvd_of_largest_support_difference ha0 hφ.symm hp
      (fun q hq => Finset.le_max' S q (Finset.mem_union_left _ hq))
    exact hb p hp

/-- A totient fiber contains at most one powerful integer. -/
theorem totient_injective_on_powerful : Set.InjOn Nat.totient {a : ℕ | PowerfulInput a} := by
  intro a ha b hb hφ
  exact eq_of_totient_eq_of_powerful_differences hφ
    (fun p hp => ha p (Finset.mem_sdiff.mp hp).1)
    (fun p hp => hb p (Finset.mem_sdiff.mp hp).1)

lemma powerfulInput_pow (a k : ℕ) (hk : 2 ≤ k) : PowerfulInput (a^k) := by
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpa := hprime.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hp)
  exact (Nat.pow_dvd_pow p hk).trans (pow_dvd_pow_of_dvd hpa k)

/-- For each k>=2, totient restricted to kth powers is injective. -/
theorem totient_pow_injective (k : ℕ) (hk : 2 ≤ k) :
    Function.Injective (fun a : ℕ => Nat.totient (a^k)) := by
  intro a b h
  apply Nat.pow_left_injective (by omega : k ≠ 0)
  exact totient_injective_on_powerful (powerfulInput_pow a k hk)
    (powerfulInput_pow b k hk) h

lemma powerful_totient_fiber_card_le_one (n : ℕ) :
    {a : ℕ | PowerfulInput a ∧ Nat.totient a = n}.ncard ≤ 1 := by
  apply (Set.ncard_le_one ((finite_totient_fiber n).subset (fun _ ha => ha.2))).mpr
  intro a ha b hb
  exact totient_injective_on_powerful ha.1 hb.1 (ha.2.trans hb.2.symm)

/-- The input primes that appear to the first power, rather than its entire
prime support. -/
noncomputable def firstPowerSupport (a : ℕ) : Finset ℕ :=
  a.primeFactors.filter (fun p => ¬p^2 ∣ a)

/-- Within a fixed totient fiber, even the set of input primes occurring
exactly once determines the input. -/
theorem firstPowerSupport_injOn_totient_fiber (n : ℕ) :
    Set.InjOn firstPowerSupport {a : ℕ | Nat.totient a = n} := by
  intro a ha b hb he
  apply eq_of_totient_eq_of_powerful_differences (ha.trans hb.symm)
  · intro p hp
    by_contra hsq
    have hm : p ∈ firstPowerSupport a :=
      Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hp).1, hsq⟩
    rw [he] at hm
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mp hm).1
  · intro p hp
    by_contra hsq
    have hm : p ∈ firstPowerSupport b :=
      Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hp).1, hsq⟩
    rw [← he] at hm
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mp hm).1

end Erdos821
