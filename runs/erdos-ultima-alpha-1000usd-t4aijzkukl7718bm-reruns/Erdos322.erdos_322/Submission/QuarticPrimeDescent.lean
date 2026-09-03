import Submission.Spec

/-! Exact quartic counts on numbers supported on the primes 2 and 5.
These special-target bounds do not bound the full count on arbitrary targets. -/
namespace Erdos322Research.QuarticPrimeDescent
open Erdos322

private theorem count_scale_sixteen_pow (a n : ℕ) :
    representationCount 4 (16^a*n) = representationCount 4 n := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ', mul_assoc, quartic_count_scale_two, ih]

private theorem count_scale_625_pow (a n : ℕ) :
    representationCount 4 (625^a*n) = representationCount 4 n := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ', mul_assoc, quartic_count_scale_five, ih]

theorem strip_two_exponent (a n : ℕ) :
    representationCount 4 (2^a*n) = representationCount 4 (2^(a%4)*n) := by
  have he : 2^a*n = 16^(a/4)*(2^(a%4)*n) := by
    calc
      2^a*n = 2^(4*(a/4)+a%4)*n := by rw [Nat.div_add_mod]
      _ = _ := by rw [pow_add, pow_mul, show (2 : ℕ)^4 = 16 by norm_num]; ring
  rw [he, count_scale_sixteen_pow]

theorem strip_five_exponent (a n : ℕ) :
    representationCount 4 (5^a*n) = representationCount 4 (5^(a%4)*n) := by
  have he : 5^a*n = 625^(a/4)*(5^(a%4)*n) := by
    calc
      5^a*n = 5^(4*(a/4)+a%4)*n := by rw [Nat.div_add_mod]
      _ = _ := by rw [pow_add, pow_mul, show (5 : ℕ)^4 = 625 by norm_num]; ring
  rw [he, count_scale_625_pow]

theorem count_zero_of_five_dvd {n : ℕ} (h5 : 5 ∣ n) (h625 : ¬625 ∣ n) :
    representationCount 4 n = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hs : ∑ i, (a i : ℕ)^4 = n := (Finset.mem_filter.mp ha).2
  have hd := five_dvd_all_of_fourth_sum hs h5
  apply h625
  rw [← hs]
  apply Finset.dvd_sum
  intro i _
  exact (show (5 : ℕ)^4 = 625 by norm_num) ▸ pow_dvd_pow_of_dvd (hd i) 4

private theorem count_eight : representationCount 4 8 = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hs : ∑ i, (a i : ℕ)^4 = 8 := (Finset.mem_filter.mp ha).2
  have hle (i : Fin 4) : (a i : ℕ)^4 % 16 ≤ 1 := by
    rw [Nat.pow_mod]
    have hi : (a i : ℕ)%16 < 16 := Nat.mod_lt _ (by decide)
    interval_cases (a i : ℕ)%16 <;> norm_num
  have hm := congrArg (fun x : ℕ ↦ x%16) hs
  simp only [Fin.sum_univ_four] at hm
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- The exact full count on every target of the form `2^a * 5^b`. -/
theorem count_two_five (a b : ℕ) :
    representationCount 4 (2^a*5^b) =
      if b%4 = 0 then
        (if a%4 = 0 then 4 else if a%4 = 1 then 6 else if a%4 = 2 then 1 else 0)
      else 0 := by
  rw [strip_two_exponent, mul_comm (2^(a%4)), strip_five_exponent,
    mul_comm (5^(b%4))]
  have ha : a%4 < 4 := Nat.mod_lt _ (by decide)
  have hb : b%4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases a%4 <;> interval_cases b%4 <;> norm_num only [pow_zero, pow_one,
    Nat.reducePow, mul_one, one_mul, Nat.reduceMul, Nat.reduceEqDiff, ite_true, ite_false]
  all_goals solve
    | (apply count_zero_of_five_dvd <;> norm_num)
    | (guard_target =ₛ representationCount 4 8 = 0; exact count_eight)
    | decide

/-- A uniform upper bound for this infinite class of targets only. -/
theorem count_two_five_le_six (a b : ℕ) : representationCount 4 (2^a*5^b) ≤ 6 := by
  rw [count_two_five]
  split_ifs <;> omega


/-- Infinitely many primes do not admit the simple coordinatewise divisibility
argument that works at 5. This does not exclude other descent arguments. -/
theorem infinitely_many_primes_without_coordinatewise_descent :
    {p : ℕ | p.Prime ∧ ∃ a : Fin 4 → ℕ,
      p ∣ ∑ i, a i^4 ∧ ¬ ∀ i, p ∣ a i}.Infinite := by
  let P : ℕ → ℕ := fun m ↦ (Nat.fermatNumber (m+2)).minFac
  have hp (m : ℕ) : (P m).Prime := Nat.minFac_prime (Nat.fermatNumber_ne_one (m+2))
  have hd (m : ℕ) : P m ∣ Nat.fermatNumber (m+2) := Nat.minFac_dvd _
  have hinj : Function.Injective P := by
    intro m n he
    by_contra hmn
    have hc := Nat.coprime_fermatNumber_fermatNumber (by omega : m+2 ≠ n+2)
    have hn : P m ∣ Nat.fermatNumber (n+2) := by rw [he]; exact hd n
    have h := Nat.dvd_gcd (hd m) hn
    change (Nat.fermatNumber (m+2)).gcd (Nat.fermatNumber (n+2)) = 1 at hc
    rw [hc] at h
    exact (hp m).not_dvd_one h
  apply (Set.infinite_range_of_injective hinj).mono
  rintro p ⟨m, rfl⟩
  refine ⟨hp m, ![1, 2^(2^m), 0, 0], ?_, ?_⟩
  · have hs : (∑ i : Fin 4, (![1, 2^(2^m), 0, 0] i : ℕ)^4) =
        Nat.fermatNumber (m+2) := by
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, one_pow, zero_pow (by decide : 4 ≠ 0), add_zero]
      unfold Nat.fermatNumber
      rw [pow_add (2 : ℕ) m 2, pow_mul]
      norm_num
      omega
    rw [hs]
    exact hd m
  · intro h
    exact (hp m).not_dvd_one (by simpa using h 0)

end Erdos322Research.QuarticPrimeDescent
