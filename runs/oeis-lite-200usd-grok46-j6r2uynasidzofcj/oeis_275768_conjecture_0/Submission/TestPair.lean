import FormalConjectures.Util.ProblemImports

open Nat Finset

example (n q : ℕ) (h : q ≤ n) : n + (n - q) = 2 * n - q := by
  rw [← Nat.add_sub_assoc h, ← Nat.two_mul]

def Sset (n : ℕ) : Finset ℕ :=
  Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n)

lemma mem_Sset_iff {n q : ℕ} :
    q ∈ Sset n ↔ q < n ∧ q.Prime ∧ (n - q).Prime ∧ (n + q).Prime := by
  simp [Sset, mem_filter, mem_range]

lemma not_prime_of_even_of_ne_two {m : ℕ} (he : Even m) (hne : m ≠ 2) : ¬ m.Prime :=
  fun hp => hne (hp.even_iff.mp he)

lemma mem_Sset_of_primes {n q : ℕ}
    (h1 : q < n) (h2 : q.Prime) (h3 : (n - q).Prime) (h4 : (n + q).Prime) :
    q ∈ Sset n := mem_Sset_iff.mpr ⟨h1, h2, h3, h4⟩

lemma two_not_mem_Sset_of_dvd_six {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) : 2 ∉ Sset n := by
  intro h
  have hsum : (n + 2).Prime := (mem_Sset_iff.mp h).2.2.2
  have heven : Even (n + 2) := (even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 6) h6)).add even_two
  have hne2 : n + 2 ≠ 2 := by omega
  exact not_prime_of_even_of_ne_two heven hne2 hsum

lemma three_not_mem_Sset_of_dvd_six {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) : 3 ∉ Sset n := by
  intro h
  have hsum : (n + 3).Prime := (mem_Sset_iff.mp h).2.2.2
  have hdvd : 3 ∣ n + 3 := (dvd_trans (by decide : 3 ∣ 6) h6).add (dvd_refl 3)
  have hgt : 3 < n + 3 := by omega
  exact not_prime_of_dvd_of_lt hdvd (by norm_num) hgt hsum

lemma five_le_of_mem_Sset_of_dvd_six {n q : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hq : q ∈ Sset n) : 5 ≤ q := by
  have hP : q.Prime := (mem_Sset_iff.mp hq).2.1
  have hq2 : q ≠ 2 := fun h => two_not_mem_Sset_of_dvd_six h6 hn (h ▸ hq)
  have hq3 : q ≠ 3 := fun h => three_not_mem_Sset_of_dvd_six h6 hn (h ▸ hq)
  exact hP.five_le_of_ne_two_of_ne_three hq2 hq3

lemma sub_mem_Sset_iff {n q : ℕ} (hq : q ∈ Sset n) :
    n - q ∈ Sset n ↔ (2 * n - q).Prime := by
  have h := mem_Sset_iff.mp hq
  have hqlt : q < n := h.1
  have hqP : q.Prime := h.2.1
  have hdiffP : (n - q).Prime := h.2.2.1
  have hqpos : 0 < q := hqP.pos
  have hsum : n + (n - q) = 2 * n - q := by
    rw [← Nat.add_sub_assoc (le_of_lt hqlt), ← Nat.two_mul]
  constructor
  · intro hnq
    have h2 := mem_Sset_iff.mp hnq
    simpa [hsum] using h2.2.2.2
  · intro h2n
    apply mem_Sset_of_primes
    · exact Nat.sub_lt (lt_trans hqpos hqlt) hqpos
    · exact hdiffP
    · simpa [Nat.sub_sub_self (le_of_lt hqlt)] using hqP
    · simpa [hsum] using h2n

def IsPaired (n q : ℕ) : Prop := q ∈ Sset n ∧ n - q ∈ Sset n

lemma isPaired_iff {n q : ℕ} (hq : q ∈ Sset n) :
    IsPaired n q ↔ (2 * n - q).Prime := by
  unfold IsPaired
  constructor
  · intro h
    exact (sub_mem_Sset_iff hq).mp h.2
  · intro hp
    exact ⟨hq, (sub_mem_Sset_iff hq).mpr hp⟩

lemma isPaired_sub {n q : ℕ} (h : IsPaired n q) : IsPaired n (n - q) := by
  have hq : q ∈ Sset n := h.1
  have hqlt : q < n := (mem_Sset_iff.mp hq).1
  have : n - (n - q) = q := Nat.sub_sub_self (le_of_lt hqlt)
  refine ⟨h.2, ?_⟩
  simpa [this] using hq

lemma not_eq_sub_self_of_mem_Sset {n q : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hq : q ∈ Sset n) : q ≠ n - q := by
  intro heq
  have hn2q : n = 2 * q := by omega
  have hqP : q.Prime := (mem_Sset_iff.mp hq).2.1
  have h3 : 3 ∣ n := dvd_trans (by decide : 3 ∣ 6) h6
  have h3q : 3 ∣ q := by
    have : 3 ∣ 2 * q := hn2q ▸ h3
    exact (Nat.Prime.dvd_mul Nat.prime_three).mp this |>.resolve_left (by decide)
  have hq3 : 3 < q := by
    have : 5 ≤ q := five_le_of_mem_Sset_of_dvd_six h6 hn hq
    omega
  exact (not_prime_of_dvd_of_lt h3q (by norm_num) hq3) hqP
