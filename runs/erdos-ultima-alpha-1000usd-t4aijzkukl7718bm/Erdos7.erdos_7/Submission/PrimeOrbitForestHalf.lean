import Submission.PrimeOrbitForestProbability
import Submission.OrderedWeightBarrier

/-! A limitation of a forest correction on irredundant odd arithmetic events.
No edge can remove more than half its child event's probability. This is not
a noncoverage theorem or a settlement of Erdős 7. -/
namespace Erdos7PrimeOrbitForestHalf
open scoped BigOperators
open Erdos7UnitOrbitPhaseProbability Erdos7PrimeOrbitForestProbability
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

lemma odd_divisor_totient_double {m n : ℕ} (hn : 0 < n) (ho : Odd n)
    (hd : m ∣ n) (hne : m ≠ n) : 2*m.totient ≤ n.totient := by
  have hm := Nat.pos_of_dvd_of_pos hd hn
  have hphi : m.totient ≠ n.totient := by
    intro h
    rcases Nat.eq_or_eq_of_totient_eq_totient hd h with h | h
    · exact hne h
    · have he : Even n := by rw [← h]; exact even_two_mul m
      exact (Nat.not_even_iff_odd.mpr ho) he
  obtain ⟨k,hk⟩ := Nat.totient_dvd_of_dvd hd
  have hkn : k ≠ 0 := by
    intro hz; rw [hz,mul_zero] at hk
    have := Nat.totient_pos.mpr hn
    omega
  have hko : k ≠ 1 := by intro hz; rw [hz,mul_one] at hk; exact hphi hk.symm
  have hk2 : 2 ≤ k := by omega
  rw [hk]
  nlinarith

lemma compatible_not_dvd {m n : ℕ} (a b : ℤ)
    (ha : IsUnit (a : ZMod m)) (hb : IsUnit (b : ZMod n))
    (hpriv : ∃ z : ℤ, (m:ℤ) ∣ z-a ∧ ¬(n:ℤ) ∣ z-b)
    (hc : CRTCompatible ha.unit hb.unit) : ¬ n ∣ m := by
  intro hd
  obtain ⟨z,hz,hnz⟩ := hpriv
  have hg := (compatible_int_iff a b ha hb).mp hc
  rw [Nat.gcd_eq_right hd] at hg
  have hd' : (n:ℤ) ∣ (m:ℤ) := by exact_mod_cast hd
  apply hnz
  convert dvd_sub (hd'.trans hz) hg using 1 <;> ring

/-- Exact CRT intersection mass is at most half the child's mass, because
odd proper divisors have totients differing by a factor of at least two. -/
theorem edge_half {N m n : ℕ} [NeZero N] (hN : Odd N)
    (hm : m ∣ N) (hn : n ∣ N) (a b : ℤ)
    (ha : IsUnit (a : ZMod m)) (hb : IsUnit (b : ZMod n))
    (hpriv : ∃ z : ℤ, (m:ℤ) ∣ z-a ∧ ¬(n:ℤ) ∣ z-b) :
    (if CRTCompatible ha.unit hb.unit then 1/((m.lcm n).totient:ℚ) else 0) ≤
      (1/(m.totient:ℚ))/2 := by
  have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hm (NeZero.pos N)
  have htpos : (0:ℚ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hmpos
  split_ifs with hc
  · have hnot := compatible_not_dvd a b ha hb hpriv hc
    have hlN := Nat.lcm_dvd hm hn
    have hlpos := Nat.pos_of_dvd_of_pos hlN (NeZero.pos N)
    have hne : m ≠ m.lcm n := by
      intro he
      apply hnot
      rw [he]
      exact Nat.dvd_lcm_right m n
    have hdouble := odd_divisor_totient_double hlpos (hN.of_dvd_nat hlN)
      (Nat.dvd_lcm_left m n) hne
    have hq : 2*(m.totient:ℚ) ≤ (m.lcm n).totient := by exact_mod_cast hdouble
    have hh := one_div_le_one_div_of_le (by positivity : (0:ℚ) < 2*m.totient) hq
    convert hh using 1 <;> ring
  · positivity

/-- A forest on unit arithmetic events retains at least half their total
first-moment weight. Private integers suffice; coverage is not assumed. -/
theorem forest_retains_half {I : Type} [Fintype I] (N : ℕ) [NeZero N]
    (hN : Odd N) (m : I → ℕ) (a : I → ℤ) (hd : ∀ i,m i ∣ N)
    (ha : ∀ i,IsUnit (a i : ZMod (m i)))
    (hpriv : ∀ i,∃ z : ℤ,(m i:ℤ) ∣ z-a i ∧ ∀ j,j ≠ i → ¬(m j:ℤ) ∣ z-a j)
    (parent : I → Option I) (rank : I → ℕ)
    (hrank : ∀ i j,parent i = some j → rank j < rank i) :
    (∑ i,1/((m i).totient:ℚ))/2 ≤
      (∑ i,1/((m i).totient:ℚ)) -
        ∑ i,(parent i).elim 0 (fun j =>
          if CRTCompatible (ha i).unit (ha j).unit then 1/(((m i).lcm (m j)).totient:ℚ) else 0) := by
  classical
  apply Erdos7OrderedWeightBarrier.forest_half_lower _ (fun i => by positivity) parent
  intro i j hij
  have hji : j ≠ i := by intro he; subst j; have := hrank i i hij; omega
  obtain ⟨z,hzi,hz⟩ := hpriv i
  exact edge_half hN (hd i) (hd j) (a i) (a j) (ha i) (ha j) ⟨z,hzi,hz j hji⟩

#print axioms odd_divisor_totient_double
#print axioms edge_half
#print axioms forest_retains_half
end
end Erdos7PrimeOrbitForestHalf
