import Submission.IncrementReduction

/-! A fixed-prime-set square-root combination rule is false. This does not
refute square-root subadditivity for the UNIFORM Jacobsthal function, and it
does not settle Erdős 970. -/
namespace Erdos970.SquareRootCombination
open Finset IncrementReduction Real

private def P : Finset ℕ := {17,19,23,29,31,37,41,43,47,53,59,61,67}

private lemma P_card : P.card = 13 := by decide +kernel

private lemma P_large : ∀ p ∈ P, 14 ≤ p := by decide +kernel

private lemma P_prime : ∀ p ∈ P, p.Prime := by decide +kernel

private theorem P_bound : PrimeSetBound P 14 := by
  classical
  intro r
  by_contra h
  push_neg at h
  have hc := cover_large_prime_budget P r 14 h
  have he : (range 14).filter (fun i => ∀ p ∈ P, p < 14 → ¬i ≡ r p [MOD p]) =
      range 14 := by
    apply filter_eq_self.mpr
    intro i hi p hp hsmall
    have := P_large p hp
    omega
  have he' : P.filter (fun p => 14 ≤ p) = P := filter_eq_self.mpr P_large
  rw [he,he',card_range,P_card] at hc
  omega

private def r : ℕ → ℕ
  | 17 => 1 | 19 => 3 | 23 => 5 | 29 => 7 | 31 => 9 | 37 => 11
  | 41 => 13 | 43 => 15 | 47 => 17 | 53 => 19 | 59 => 21
  | 61 => 23 | 67 => 25 | _ => 0

set_option maxRecDepth 10000 in
private lemma covered : ∀ i ∈ range 27, ∃ p ∈ insert 2 P, i ≡ r p [MOD p] := by
  decide +kernel

private theorem union_not_bound : ¬PrimeSetBound (P ∪ {2}) 27 := by
  intro hb
  obtain ⟨i,hi,ha⟩ := hb r
  obtain ⟨p,hp,hip⟩ := covered i (mem_range.mpr hi)
  exact ha p (by simpa only [union_singleton] using hp) hip

private lemma root_cost : (sqrt (14 : ℝ)+sqrt 2)^2 < 27 := by
  have h14 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 14)
  have h2 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp : (sqrt (14 : ℝ)*sqrt 2)^2 = 28 := by
    rw [mul_pow,h14,h2]
    norm_num
  have hp0 : 0 ≤ sqrt (14 : ℝ)*sqrt 2 := by positivity
  have hp1 : sqrt (14 : ℝ)*sqrt 2 < 11/2 := by nlinarith
  nlinarith

/-- Even with disjoint genuine prime sets and valid input interval bounds,
rounding up the squared sum of their square roots is not a valid combination
rule. Thirteen large odd primes have bound14; adding parity covers27 points. -/
theorem not_fixed_square_root_combination :
    ¬∀ (P Q : Finset ℕ), Disjoint P Q →
      (∀ p ∈ P, p.Prime) → (∀ p ∈ Q, p.Prime) →
      ∀ g h m : ℕ, PrimeSetBound P g → PrimeSetBound Q h →
        (sqrt (g : ℝ)+sqrt (h : ℝ))^2 < m → PrimeSetBound (P ∪ Q) m := by
  intro h
  have hd : Disjoint P {2} := by decide +kernel
  have hq : ∀ p ∈ ({2} : Finset ℕ), p.Prime := by decide +kernel
  exact union_not_bound (h P {2} hd P_prime hq 14 2 27 P_bound
    (primeSetBound_singleton 2 Nat.prime_two) root_cost)

#print axioms not_fixed_square_root_combination
end Erdos970.SquareRootCombination
