import Submission.TwofoldNoThreeLift
import Submission.NoFiveCompletion

/-! A necessary condition on the input of the twofold lifting criterion.
This does not provide such an input or settle the original conjecture. -/
namespace Erdos7TwofoldNoThreeFive
open scoped BigOperators
open Erdos7TwofoldNoThreeLift
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem exists_five {I : Type} [Fintype I]
    (m : I → ℕ) (a₀ a₁ : I → ℤ)
    (hinj : Function.Injective m) (hm : ∀ i,1 < m i ∧ Odd (m i))
    (h3 : ∀ i,¬ 3 ∣ m i)
    (hcover : ∀ x : ℤ,∃ i,(m i : ℤ) ∣ x-a₀ i ∨ (m i : ℤ) ∣ x-a₁ i) :
    ∃ i,5 ∣ m i := by
  classical
  by_contra hn
  push_neg at hn
  obtain ⟨q,hqB,hq⟩ := Nat.exists_infinite_primes (6+∑ i,m i)
  have hq3 : 3 < q := by omega
  have hq5 : 5 < q := by omega
  have hqbig (i : I) : m i < q := by
    have hh : m i ≤ ∑ j,m j := Finset.single_le_sum
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  obtain ⟨a,ha₀,ha⟩ := exists_residues m q a₀ a₁ hm h3 hq hq3
  have hd := modulus_data m q hinj hm h3 hq hq3 hqbig
  have hc := lifted_covers m q a₀ a₁ hm h3 hq hq3 hcover a ha₀ ha
  obtain ⟨k,hk⟩ := Erdos7NoFive.arithmetic_exists_five (modulus m q) a
    ⟨hd.1,hd.2,hc⟩
  cases k with
  | inl i => exact hn i hk
  | inr z =>
    rcases z with ⟨t,k⟩
    change 5 ∣ 3^(t.val+1)*cofactor m q k at hk
    rcases (show Nat.Prime 5 by decide).dvd_mul.mp hk with hh | hh
    · have h53 : 5 ∣ 3 := (show Nat.Prime 5 by decide).dvd_of_dvd_pow hh
      norm_num at h53
    · cases k with
      | none =>
        change 5 ∣ q at hh
        rcases (Nat.dvd_prime hq).mp hh with h | h <;> omega
      | some t =>
        cases t with
        | none => norm_num [cofactor] at hh
        | some i => exact hn i hh

#print axioms exists_five
end Erdos7TwofoldNoThreeFive
