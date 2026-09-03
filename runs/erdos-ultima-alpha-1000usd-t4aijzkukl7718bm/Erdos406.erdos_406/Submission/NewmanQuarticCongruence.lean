import Submission.NewmanQuarticDescent
import Submission.Work

/-! Arithmetic consequences of the quartic descent. These do not prove
finiteness of the quartic-free candidates. -/
namespace Erdos406QuarticCongruence
open Polynomial Erdos406QuarticDescent Erdos406QuarticSquare
open Erdos406SparseTriple Erdos406Cyclotomic Erdos406Work

lemma sixSpaced_power_exponent (j : ℕ) (hsp : SixSpaced (2^j)) : 486 ∣ j := by
  have hg := (sixSpaced_implies_triple hsp).1
  obtain ⟨m, hm⟩ := even_exponent hg
  have he : 2^j = 4^m := by
    rw [hm, ← two_mul, pow_mul]
    norm_num
  have hu : 2^j % 3 = 1 := by rw [he]; simp [Nat.pow_mod]
  have hr := unit_triple_prefix (sixSpaced_implies_triple hsp) hu
  rw [he] at hr
  have hd : 243 ∣ m := (four_pow_mod_eq_one_iff 5 m).mp (by
    change 4^m % 729 = 1 % 729
    simpa using hr)
  obtain ⟨a, ha⟩ := hd
  refine ⟨a, ?_⟩
  omega

/-- The quartic can occur only in the exponent class eight modulo 486. -/
theorem candidate_quartic_exponent (k : ℕ) (hg : Nat.digits 3 (2^k) ⊆ [0,1])
    (hd : qQuartic ∣ digitPoly (Nat.digits 3 (2^k))) :
    ∃ a : ℕ, k = 486*a+8 := by
  obtain ⟨j,hk,_,hsp,_⟩ := candidate_quartic_descent k hg hd
  obtain ⟨a, ha⟩ := sixSpaced_power_exponent j hsp
  exact ⟨a, by omega⟩

/-- Every additional candidate containing the quartic descends to an
additional quartic-free candidate; it cannot descend to four or 256. -/
theorem additional_quartic_descent (k : ℕ) (hg : Nat.digits 3 (2^k) ⊆ [0,1])
    (h8 : k ≠ 8)
    (hd : qQuartic ∣ digitPoly (Nat.digits 3 (2^k))) :
    ∃ j : ℕ, j < k ∧ Nat.digits 3 (2^j) ⊆ [0,1] ∧
      j ≠ 0 ∧ j ≠ 2 ∧ j ≠ 8 ∧
      ¬ qQuartic ∣ digitPoly (Nat.digits 3 (2^j)) := by
  obtain ⟨j,hk,hgj,hsp,hfree⟩ := candidate_quartic_descent k hg hd
  have hj := sixSpaced_power_exponent j hsp
  obtain ⟨a, ha⟩ := hj
  exact ⟨j, by omega, hgj, by omega, by omega, by omega, hfree⟩

/-- A least exception to the stronger classification is quartic-free. -/
theorem least_additional_exponent_quartic_free (k : ℕ)
    (hg : Nat.digits 3 (2^k) ⊆ [0,1]) (h8 : k ≠ 8)
    (hmin : ∀ j < k, Nat.digits 3 (2^j) ⊆ [0,1] → j = 0 ∨ j = 2 ∨ j = 8) :
    ¬ qQuartic ∣ digitPoly (Nat.digits 3 (2^k)) := by
  intro hd
  obtain ⟨j,hjk,hgj,hj0,hj2,hj8,_⟩ := additional_quartic_descent k hg h8 hd
  rcases hmin j hjk hgj with h | h | h <;> contradiction

/-- The certified finite computation and the congruence combine to put any
additional quartic-containing exponent at least 2,000,384. This is still only
a lower bound, not a global cutoff. -/
theorem additional_quartic_lower_bound (k : ℕ)
    (hg : Nat.digits 3 (2^k) ⊆ [0,1]) (h8 : k ≠ 8)
    (hd : qQuartic ∣ digitPoly (Nat.digits 3 (2^k))) : 2000384 ≤ k := by
  obtain ⟨j,hk,hgj,hsp,_⟩ := candidate_quartic_descent k hg hd
  obtain ⟨a, ha⟩ := sixSpaced_power_exponent j hsp
  have hj : 2000000 ≤ j := by
    by_contra hh
    have hjc := (good_two_exponents_below_two_million (by omega : j < 2000000)).mp hgj
    omega
  omega

#print axioms sixSpaced_power_exponent
#print axioms candidate_quartic_exponent
#print axioms least_additional_exponent_quartic_free
#print axioms additional_quartic_lower_bound
end Erdos406QuarticCongruence
