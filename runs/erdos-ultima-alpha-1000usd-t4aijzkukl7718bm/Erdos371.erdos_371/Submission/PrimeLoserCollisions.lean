import Submission.PrimeLoserWeighted

/-! A second-moment reduction for prime-loser incidences. In the large-label
range, distinct incidences of one loser have distinct winning prime labels.
No sieve estimate for the off-diagonal set is assumed here. -/

namespace Erdos371
open Finset

lemma primeLoser_lt_primeWinner (n : ℕ) : primeLoser n < primeWinner n := by
  have h := consecutive_maxPrimeFac_ne n
  unfold primeLoser primeWinner
  rcases lt_or_gt_of_ne h with h | h
  · rw [min_eq_right h.le,max_eq_left h.le]
    exact h
  · rw [min_eq_left h.le,max_eq_right h.le]
    exact h

lemma primeLabel_pair_cases (n : ℕ) :
    (Nat.maxPrimeFac n = primeLoser n ∧ Nat.maxPrimeFac (n+1) = primeWinner n) ∨
      (Nat.maxPrimeFac n = primeWinner n ∧ Nat.maxPrimeFac (n+1) = primeLoser n) := by
  unfold primeLoser primeWinner
  rcases le_total (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) with h | h
  · simp [min_eq_left h,max_eq_right h]
  · simp [min_eq_right h,max_eq_left h]

/-- If the product period is at least twice the interval length, even the two
opposite orientations cannot both occur in the interval. -/
lemma unordered_divisor_pair_unique (p q N n m : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hc : p.Coprime q)
    (hn : n < N) (hm : m < N) (hprod : 2*N ≤ p*q)
    (hnpq : (p ∣ n ∧ q ∣ n+1) ∨ (q ∣ n ∧ p ∣ n+1))
    (hmpq : (p ∣ m ∧ q ∣ m+1) ∨ (q ∣ m ∧ p ∣ m+1)) : n = m := by
  have hsame (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
      (hnab : n < a*b) (hmab : m < a*b)
      (han : a ∣ n) (hbn : b ∣ n+1) (ham : a ∣ m) (hbm : b ∣ m+1) : n = m := by
    exact (adjacentRoot_unique a b hab ha hb n hnab han hbn).trans
      (adjacentRoot_unique a b hab ha hb m hmab ham hbm).symm
  have hopposite (a b : ℕ) (hab : a.Coprime b) (hsize : 2*N ≤ a*b)
      (han : a ∣ n) (hbn : b ∣ n+1) (hbm : b ∣ m) (ham : a ∣ m+1) : False := by
    have ha : a ∣ n+m+1 := by simpa only [Nat.add_assoc] using Nat.dvd_add han ham
    have hb : b ∣ n+m+1 := by
      convert Nat.dvd_add hbn hbm using 1; omega
    have hh := Nat.eq_zero_of_dvd_of_lt (hab.mul_dvd_of_dvd_of_dvd ha hb)
      (show n+m+1 < a*b by omega)
    omega
  rcases hnpq with ⟨hpn,hqn⟩ | ⟨hqn,hpn⟩ <;>
    rcases hmpq with ⟨hpm,hqm⟩ | ⟨hqm,hpm⟩
  · exact hsame p q hp hq hc (by omega) (by omega) hpn hqn hpm hqm
  · exact (hopposite p q hc hprod hpn hqn hqm hpm).elim
  · exact (hopposite q p hc.symm (by nlinarith) hqn hpn hpm hqm).elim
  · exact hsame q p hq hp hc.symm (by nlinarith) (by nlinarith) hqn hpn hqm hpm

/-- There are no repeated unordered prime edges in this high-label range. -/
theorem large_primeLabel_pair_injective (B N : ℕ) (hB : 1 ≤ B)
    (hsize : 2*N ≤ (B+1)^2) :
    Set.InjOn (fun n => (primeLoser n, primeWinner n)) (bothAboveSet B N) := by
  intro n hn m hm he
  change n ∈ (range N).filter (fun n => B < Nat.maxPrimeFac n ∧ B < Nat.maxPrimeFac (n+1)) at hn
  change m ∈ (range N).filter (fun n => B < Nat.maxPrimeFac n ∧ B < Nat.maxPrimeFac (n+1)) at hm
  obtain ⟨hnN,hnB,hnB'⟩ := mem_filter.mp hn
  obtain ⟨hmN,hmB,hmB'⟩ := mem_filter.mp hm
  have he₁ : primeLoser n = primeLoser m := congrArg Prod.fst he
  have he₂ : primeWinner n = primeWinner m := congrArg Prod.snd he
  let p := primeLoser n
  let q := primeWinner n
  have hpB : B < p := lt_min hnB hnB'
  have hqB : B < q := hpB.trans (primeLoser_lt_primeWinner n)
  have hnpq : (p ∣ n ∧ q ∣ n+1) ∨ (q ∣ n ∧ p ∣ n+1) := by
    rcases primeLabel_pair_cases n with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨by simpa only [ha] using (Nat.maxPrimeFac_dvd (n := n)),by simpa only [hb] using (Nat.maxPrimeFac_dvd (n := n+1))⟩
    · exact Or.inr ⟨by simpa only [ha] using (Nat.maxPrimeFac_dvd (n := n)),by simpa only [hb] using (Nat.maxPrimeFac_dvd (n := n+1))⟩
  have hmpq : (p ∣ m ∧ q ∣ m+1) ∨ (q ∣ m ∧ p ∣ m+1) := by
    rcases primeLabel_pair_cases m with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨by simpa only [ha, ← he₁] using (Nat.maxPrimeFac_dvd (n := m)),
        by simpa only [hb, ← he₂] using (Nat.maxPrimeFac_dvd (n := m+1))⟩
    · exact Or.inr ⟨by simpa only [ha, ← he₂] using (Nat.maxPrimeFac_dvd (n := m)),
        by simpa only [hb, ← he₁] using (Nat.maxPrimeFac_dvd (n := m+1))⟩
  have hc : p.Coprime q := by
    rcases hnpq with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact divisor_pair_coprime n p q ha hb
    · exact (divisor_pair_coprime n q p ha hb).symm
  exact unordered_divisor_pair_unique p q N n m (by omega) (by omega) hc
    (mem_range.mp hnN) (mem_range.mp hmN)
    (hsize.trans (by nlinarith)) hnpq hmpq

def primeLoserIncidences (p N : ℕ) : Finset ℕ :=
  (range N).filter fun n => primeLoser n = p

/-- Ordered pairs of distinct incidences of a common high prime loser. -/
def primeLoserCollisions (B N : ℕ) : Finset (ℕ × ℕ) :=
  (bothAboveSet B N).offDiag.filter fun nm => primeLoser nm.1 = primeLoser nm.2

/-- Thus each off-diagonal incidence in this range involves three distinct
prime labels, not a repeated two-prime configuration. -/
theorem primeLoserCollisions_distinct_winners (B N n m : ℕ)
    (hB : 1 ≤ B) (hsize : 2*N ≤ (B+1)^2)
    (hnm : (n,m) ∈ primeLoserCollisions B N) : primeWinner n ≠ primeWinner m := by
  obtain ⟨hnm,he⟩ := mem_filter.mp hnm
  obtain ⟨hn,hm,hne⟩ := mem_offDiag.mp hnm
  intro hw
  exact hne (large_primeLabel_pair_injective B N hB hsize hn hm (Prod.ext he hw))

#print axioms large_primeLabel_pair_injective
#print axioms primeLoserCollisions_distinct_winners
end Erdos371
