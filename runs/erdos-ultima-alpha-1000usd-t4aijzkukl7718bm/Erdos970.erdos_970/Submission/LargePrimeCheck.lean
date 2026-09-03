import FormalConjecturesUtil

/-! A diagnostic obstruction to an unconditional relative sieve-counting estimate. -/

namespace Erdos970.LargePrimeCheck

/-- The positions in the symmetric interval surviving the zero classes of primes below `p`. -/
def survivors (p : ℕ) : Finset ℤ :=
  (Finset.Icc (-(p : ℤ)) p).filter
    (fun n => ∀ q ∈ Finset.range p, q.Prime → ¬(q : ℤ) ∣ n)

theorem survivors_eq (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    survivors p = {-(p : ℤ), -1, 1, (p : ℤ)} := by
  classical
  ext n
  simp only [survivors, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hnlo, hnhi⟩, hn⟩
    have hna : n.natAbs ≤ p := by
      have ha : |n| ≤ (p : ℤ) := abs_le.mpr ⟨hnlo, hnhi⟩
      rw [Int.abs_eq_natAbs] at ha
      exact_mod_cast ha
    have hna0 : n.natAbs ≠ 0 := by
      intro hzero
      have hzero' : n = 0 := Int.natAbs_eq_zero.mp hzero
      subst n
      exact hn 2 (Finset.mem_range.mpr (by omega)) Nat.prime_two (dvd_zero _)
    have hcases : n.natAbs = 1 ∨ n.natAbs = p := by
      by_cases hn1 : n.natAbs = 1
      · exact Or.inl hn1
      · obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hn1
        have hqn : q ≤ n.natAbs := Nat.le_of_dvd (Nat.pos_of_ne_zero hna0) hqd
        have hqp : q = p := by
          by_contra hneq
          exact hn q (Finset.mem_range.mpr (by omega)) hq (Int.natCast_dvd.mpr hqd)
        subst q
        exact Or.inr (by omega)
    rcases hcases with hn1 | hnp
    · have ha : |n| = 1 := by rw [Int.abs_eq_natAbs, hn1]; norm_num
      rcases abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.mp ha with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
    · have ha : |n| = (p : ℤ) := by rw [Int.abs_eq_natAbs, hnp]
      rcases abs_eq (by positivity : (0 : ℤ) ≤ p) |>.mp ha with h | h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inl h
  · intro hn
    have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    have havoid_one (q : ℕ) (hq : q.Prime) : ¬(q : ℤ) ∣ (1 : ℤ) := by
      exact (Nat.prime_iff_prime_int.mp hq).not_dvd_one
    have havoid_p (q : ℕ) (hqp : q < p) (hq : q.Prime) : ¬(q : ℤ) ∣ (p : ℤ) := by
      intro hd
      have hdn : q ∣ p := by exact_mod_cast hd
      have hqe : q = p := (Nat.dvd_prime hp).mp hdn |>.resolve_left hq.ne_one
      omega
    rcases hn with rfl | rfl | rfl | rfl
    · refine ⟨⟨by omega, by omega⟩, ?_⟩
      intro q hq hprime hd
      exact havoid_p q (Finset.mem_range.mp hq) hprime (dvd_neg.mp hd)
    · refine ⟨⟨by omega, by omega⟩, ?_⟩
      intro q hq hprime hd
      exact havoid_one q hprime (dvd_neg.mp hd)
    · exact ⟨⟨by omega, by omega⟩, fun q hq hprime => havoid_one q hprime⟩
    · exact ⟨⟨by omega, by omega⟩, fun q hq hprime =>
        havoid_p q (Finset.mem_range.mp hq) hprime⟩

theorem survivors_card (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (survivors p).card = 4 := by
  have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  simp [survivors_eq p hp hp3,
    show (1 : ℤ) ≠ p by omega,
    show (-1 : ℤ) ≠ p by omega,
    show -(p : ℤ) ≠ (p : ℤ) by omega,
    show -(p : ℤ) ≠ -1 by omega,
    show -(p : ℤ) ≠ 1 by omega]

theorem removed_eq (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    (survivors p).filter (fun n => (p : ℤ) ∣ n) = {-(p : ℤ), (p : ℤ)} := by
  have hn : ¬(p : ℤ) ∣ (1 : ℤ) := (Nat.prime_iff_prime_int.mp hp).not_dvd_one
  simp [survivors_eq p hp hp3, Finset.filter_insert, Finset.filter_singleton, hn]

theorem removed_card (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) :
    ((survivors p).filter (fun n => (p : ℤ) ∣ n)).card = 2 := by
  have hpZ : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  simp [removed_eq p hp hp3, show -(p : ℤ) ≠ (p : ℤ) by omega]

/-- The relative concentration factor of a new, larger prime is unbounded. -/
theorem unbounded_relative_concentration (B : ℕ) :
    ∃ p : ℕ, p.Prime ∧ 3 ≤ p ∧ (survivors p).card = 4 ∧
      ((survivors p).filter (fun n => (p : ℤ) ∣ n)).card = 2 ∧
      B * (survivors p).card <
        p * ((survivors p).filter (fun n => (p : ℤ) ∣ n)).card := by
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (2 * B + 3)
  have hp3 : 3 ≤ p := by omega
  refine ⟨p, hp, hp3, survivors_card p hp hp3, removed_card p hp hp3, ?_⟩
  rw [survivors_card p hp hp3, removed_card p hp hp3]
  omega

#print axioms unbounded_relative_concentration
end Erdos970.LargePrimeCheck
