import Mathlib
open scoped Nat.Prime

def A289827 (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) n

lemma pc_succ (k : ℕ) : Nat.primeCounting (k+1) = Nat.primeCounting k + (if (k+1).Prime then 1 else 0) := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_succ]

lemma pc_add (n m : ℕ) :
    Nat.primeCounting (n + m) = Nat.primeCounting n + (Finset.range m).sum (fun i => if (n+i+1).Prime then 1 else 0) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have : n + (k+1) = (n+k) + 1 := by ring
    rw [this, pc_succ, ih, Finset.sum_range_succ]; ring_nf

lemma Piff (n m : ℕ) :
    (Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n)
      ↔ ((Finset.range m).sum (fun i => if (n+i+1).Prime then 1 else 0) = Nat.primeCounting m) := by
  rw [add_comm m n, pc_add n m]; omega

lemma par (n i j : ℕ) (hn : 11 ≤ n) (hi : (n+i).Prime) (hj : (n+j).Prime) : i % 2 = j % 2 := by
  have h2i : n + i ≠ 2 := by omega
  have h2j : n + j ≠ 2 := by omega
  have oi : Odd (n+i) := (hi.eq_two_or_odd').resolve_left h2i
  have oj : Odd (n+j) := (hj.eq_two_or_odd').resolve_left h2j
  rcases oi with ⟨a, ha⟩; rcases oj with ⟨b, hb⟩; omega

lemma noB (n i : ℕ) (hn : 11 ≤ n) :
    ¬ ((n+i).Prime ∧ (n+i+2).Prime ∧ (n+i+4).Prime) := by
  rintro ⟨p1, p2, p3⟩
  have : (n+i) % 3 = 0 ∨ (n+i+2) % 3 = 0 ∨ (n+i+4) % 3 = 0 := by omega
  rcases this with h | h | h
  · have := (p1.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)); omega
  · have := (p2.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)); omega
  · have := (p3.eq_one_or_self_of_dvd 3 (Nat.dvd_of_mod_eq_zero h)); omega

lemma pairLE (n i j : ℕ) (hn : 11 ≤ n) (hpar : i % 2 ≠ j % 2) :
    (if (n+i).Prime then 1 else 0) + (if (n+j).Prime then (1:ℕ) else 0) ≤ 1 := by
  split_ifs with ha hb
  · exact absurd (par n i j hn ha hb) hpar
  all_goals omega

lemma tripLE (n i : ℕ) (hn : 11 ≤ n) :
    (if (n+i).Prime then 1 else 0) + (if (n+i+2).Prime then 1 else 0)
      + (if (n+i+4).Prime then (1:ℕ) else 0) ≤ 2 := by
  split_ifs with ha hb hc
  · exact absurd ⟨ha, hb, hc⟩ (noB n i hn)
  all_goals omega

/-- **Open input.**  This is a strengthened form of the second Hardy–Littlewood
inequality restricted to comparable arguments:
`π(m+n) ≠ π(m) + π(n)` for all `11 ≤ m ≤ n`.
It has been verified computationally for all `n ≤ 10^8`.  It is provable for
`11 ≤ m ≤ 3158` from the minimal diameters of prime `k`-tuples, but for `m ≥ 3159`
Hensley–Richards constellations exist and its truth depends on the (unproven)
prime `k`-tuples / Dickson conjecture.  Hence this is the single genuinely open
number-theoretic ingredient of the whole conjecture. -/
lemma key (n m : ℕ) (h1 : 11 ≤ m) (h2 : m ≤ n) :
    Nat.primeCounting (m + n) ≠ Nat.primeCounting m + Nat.primeCounting n := sorry

lemma reduce (n : ℕ) : A289827 n ≤ 10 := by
  set P := (fun m => Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) with hP
  by_contra h
  push_neg at h
  have hle : Nat.findGreatest P n ≤ n := Nat.findGreatest_le n
  have hgt : 10 < Nat.findGreatest P n := h
  have hne : Nat.findGreatest P n ≠ 0 := by omega
  have hpos : P (Nat.findGreatest P n) := Nat.findGreatest_of_ne_zero rfl hne
  exact key n (Nat.findGreatest P n) (by omega) hle hpos

lemma small (n : ℕ) (hn : 11 ≤ n) :
    A289827 n = 1 ∨ A289827 n = 2 ∨ A289827 n = 4 ∨ A289827 n = 10 := by
  have hpos : A289827 n ≠ 0 →
      Nat.primeCounting (A289827 n + n) = Nat.primeCounting (A289827 n) + Nat.primeCounting n :=
    fun h0 => Nat.findGreatest_of_ne_zero
      (P := fun m => Nat.primeCounting (m+n)=Nat.primeCounting m+Nat.primeCounting n) rfl h0
  have hgr : ∀ m, A289827 n < m → m ≤ n →
      ¬ (Nat.primeCounting (m + n) = Nat.primeCounting m + Nat.primeCounting n) :=
    fun m hm hmn => Nat.findGreatest_is_greatest
      (P := fun m => Nat.primeCounting (m+n)=Nat.primeCounting m+Nat.primeCounting n) hm hmn
  have hle := reduce n
  interval_cases h : (A289827 n)
  · exfalso
    have h1 := hgr 1 (by omega) (by omega); have h2 := hgr 2 (by omega) (by omega)
    rw [Piff] at h1 h2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd] at h1 h2
    rw [show Nat.primeCounting 1 = 0 from by decide] at h1
    rw [show Nat.primeCounting 2 = 1 from by decide] at h2
    have p12 := pairLE n 1 2 hn (by decide)
    omega
  · left; rfl
  · right; left; rfl
  · exfalso
    have hp := hpos (by omega)
    have h4 := hgr 4 (by omega) (by omega); have h5 := hgr 5 (by omega) (by omega)
    rw [Piff] at hp h4 h5
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd] at hp h4 h5
    rw [show Nat.primeCounting 3 = 2 from by decide] at hp
    rw [show Nat.primeCounting 4 = 2 from by decide] at h4
    rw [show Nat.primeCounting 5 = 3 from by decide] at h5
    have p45 := pairLE n 4 5 hn (by decide)
    omega
  · right; right; left; rfl
  · exfalso
    have hp := hpos (by omega)
    have h6 := hgr 6 (by omega) (by omega); have h7 := hgr 7 (by omega) (by omega)
    rw [Piff] at hp h6 h7
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd] at hp h6 h7
    rw [show Nat.primeCounting 5 = 3 from by decide] at hp
    rw [show Nat.primeCounting 6 = 3 from by decide] at h6
    rw [show Nat.primeCounting 7 = 4 from by decide] at h7
    have p67 := pairLE n 6 7 hn (by decide)
    omega
  · exfalso
    have hp := hpos (by omega)
    rw [Piff] at hp
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd] at hp
    rw [show Nat.primeCounting 6 = 3 from by decide] at hp
    have t1 : (if (n+1).Prime then 1 else 0)+(if (n+3).Prime then 1 else 0)+(if (n+5).Prime then (1:ℕ) else 0) ≤ 2 := by
      simpa using tripLE n 1 hn
    have t2 : (if (n+2).Prime then 1 else 0)+(if (n+4).Prime then 1 else 0)+(if (n+6).Prime then (1:ℕ) else 0) ≤ 2 := by
      simpa using tripLE n 2 hn
    have p12 := pairLE n 1 2 hn (by decide); have p14 := pairLE n 1 4 hn (by decide)
    have p16 := pairLE n 1 6 hn (by decide); have p32 := pairLE n 3 2 hn (by decide)
    have p34 := pairLE n 3 4 hn (by decide); have p36 := pairLE n 3 6 hn (by decide)
    have p52 := pairLE n 5 2 hn (by decide); have p54 := pairLE n 5 4 hn (by decide)
    have p56 := pairLE n 5 6 hn (by decide)
    omega
  · exfalso
    have hp := hpos (by omega)
    rw [Piff] at hp
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd] at hp
    rw [show Nat.primeCounting 7 = 4 from by decide] at hp
    have t1 : (if (n+1).Prime then 1 else 0)+(if (n+3).Prime then 1 else 0)+(if (n+5).Prime then (1:ℕ) else 0) ≤ 2 := by
      simpa using tripLE n 1 hn
    have t3 : (if (n+3).Prime then 1 else 0)+(if (n+5).Prime then 1 else 0)+(if (n+7).Prime then (1:ℕ) else 0) ≤ 2 := by
      simpa using tripLE n 3 hn
    have t2 : (if (n+2).Prime then 1 else 0)+(if (n+4).Prime then 1 else 0)+(if (n+6).Prime then (1:ℕ) else 0) ≤ 2 := by
      simpa using tripLE n 2 hn
    have p12 := pairLE n 1 2 hn (by decide); have p14 := pairLE n 1 4 hn (by decide)
    have p16 := pairLE n 1 6 hn (by decide); have p32 := pairLE n 3 2 hn (by decide)
    have p34 := pairLE n 3 4 hn (by decide); have p36 := pairLE n 3 6 hn (by decide)
    have p52 := pairLE n 5 2 hn (by decide); have p54 := pairLE n 5 4 hn (by decide)
    have p56 := pairLE n 5 6 hn (by decide); have p72 := pairLE n 7 2 hn (by decide)
    have p74 := pairLE n 7 4 hn (by decide); have p76 := pairLE n 7 6 hn (by decide)
    omega
  · exfalso
    have hp := hpos (by omega)
    rw [Piff] at hp
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd] at hp
    rw [show Nat.primeCounting 8 = 4 from by decide] at hp
    have t1 : (if (n+1).Prime then 1 else 0)+(if (n+3).Prime then 1 else 0)+(if (n+5).Prime then (1:ℕ) else 0) ≤ 2 := by
      simpa using tripLE n 1 hn
    have t3 : (if (n+3).Prime then 1 else 0)+(if (n+5).Prime then 1 else 0)+(if (n+7).Prime then (1:ℕ) else 0) ≤ 2 := by
      simpa using tripLE n 3 hn
    have t2 : (if (n+2).Prime then 1 else 0)+(if (n+4).Prime then 1 else 0)+(if (n+6).Prime then (1:ℕ) else 0) ≤ 2 := by
      simpa using tripLE n 2 hn
    have t4 : (if (n+4).Prime then 1 else 0)+(if (n+6).Prime then 1 else 0)+(if (n+8).Prime then (1:ℕ) else 0) ≤ 2 := by
      simpa using tripLE n 4 hn
    have p12 := pairLE n 1 2 hn (by decide); have p14 := pairLE n 1 4 hn (by decide)
    have p16 := pairLE n 1 6 hn (by decide); have p18 := pairLE n 1 8 hn (by decide)
    have p32 := pairLE n 3 2 hn (by decide); have p34 := pairLE n 3 4 hn (by decide)
    have p36 := pairLE n 3 6 hn (by decide); have p38 := pairLE n 3 8 hn (by decide)
    have p52 := pairLE n 5 2 hn (by decide); have p54 := pairLE n 5 4 hn (by decide)
    have p56 := pairLE n 5 6 hn (by decide); have p58 := pairLE n 5 8 hn (by decide)
    have p72 := pairLE n 7 2 hn (by decide); have p74 := pairLE n 7 4 hn (by decide)
    have p76 := pairLE n 7 6 hn (by decide); have p78 := pairLE n 7 8 hn (by decide)
    omega
  · exfalso
    have hp := hpos (by omega)
    have h10 := hgr 10 (by omega) (by omega)
    rw [Piff] at hp h10
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd] at hp h10
    rw [show Nat.primeCounting 9 = 4 from by decide] at hp
    rw [show Nat.primeCounting 10 = 4 from by decide] at h10
    have t2 : (if (n+2).Prime then 1 else 0)+(if (n+4).Prime then 1 else 0)+(if (n+6).Prime then (1:ℕ) else 0) ≤ 2 := by
      simpa using tripLE n 2 hn
    have p110 := pairLE n 1 10 hn (by decide); have p310 := pairLE n 3 10 hn (by decide)
    have p510 := pairLE n 5 10 hn (by decide); have p710 := pairLE n 7 10 hn (by decide)
    have p910 := pairLE n 9 10 hn (by decide)
    have p18 := pairLE n 1 8 hn (by decide); have p38 := pairLE n 3 8 hn (by decide)
    have p58 := pairLE n 5 8 hn (by decide); have p78 := pairLE n 7 8 hn (by decide)
    have p98 := pairLE n 9 8 hn (by decide)
    omega
  · right; right; right; rfl

theorem oeis_289827_conjecture_0 (n : ℕ) (hn : 1 < n) :
    A289827 n = 1 ∨ A289827 n = 2 ∨ A289827 n = 4 ∨ A289827 n = 10 := by
  rcases Nat.lt_or_ge n 11 with h11 | h11
  · interval_cases n <;> decide
  · exact small n h11
