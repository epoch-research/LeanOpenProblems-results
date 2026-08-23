import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A275768: $a(n)$ is the number of ways to express $n = \frac{\operatorname{prime}(i) + \operatorname{prime}(j)}{2}$ when $\frac{|\operatorname{prime}(i) - \operatorname{prime}(j)|}{2}$ also is prime.
This is equivalent to counting the number of primes $q$ such that $n - q$ and $n + q$ are also prime.
-/
def a (n : ℕ) : ℕ :=
  Finset.card (Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n))

def Sset (n : ℕ) : Finset ℕ :=
  Finset.filter (fun q : ℕ =>
    Nat.Prime q ∧ Nat.Prime (n - q) ∧ Nat.Prime (n + q)
  ) (Finset.range n)

lemma a_eq_card_Sset (n : ℕ) : a n = #(Sset n) := rfl

lemma mem_Sset_iff {n q : ℕ} :
    q ∈ Sset n ↔ q < n ∧ q.Prime ∧ (n - q).Prime ∧ (n + q).Prime := by
  simp [Sset, mem_filter, mem_range]

/-- An even natural number other than 2 is not prime. -/
lemma not_prime_of_even_of_ne_two {m : ℕ} (he : Even m) (hne : m ≠ 2) : ¬ m.Prime :=
  fun hp => hne (hp.even_iff.mp he)

/-- For odd `n`, every element of `Sset n` equals `2`. -/
lemma eq_two_of_mem_Sset_of_odd {n q : ℕ} (hn : Odd n) (hq : q ∈ Sset n) : q = 2 := by
  have h := mem_Sset_iff.mp hq
  have hqP : q.Prime := h.2.1
  have hsumP : (n + q).Prime := h.2.2.2
  by_contra hne
  have hqOdd : Odd q := hqP.odd_of_ne_two hne
  have heven : Even (n + q) := Odd.add_odd hn hqOdd
  have hne2 : n + q ≠ 2 := by
    have hq2 : 2 ≤ q := hqP.two_le
    have hn1 : 1 ≤ n := hn.pos
    omega
  exact not_prime_of_even_of_ne_two heven hne2 hsumP

lemma Sset_odd_subset_singleton_two {n : ℕ} (hn : Odd n) : Sset n ⊆ {2} := by
  intro q hq
  simp [eq_two_of_mem_Sset_of_odd hn hq]

lemma a_le_one_of_odd {n : ℕ} (hn : Odd n) : a n ≤ 1 := by
  rw [a_eq_card_Sset]
  exact (card_le_card (Sset_odd_subset_singleton_two hn)).trans (by simp)

lemma a_ne_four_of_odd {n : ℕ} (hn : Odd n) : a n ≠ 4 := by
  have : a n ≤ 1 := a_le_one_of_odd hn
  omega

lemma prime_mod_three_eq_one_or_two {p : ℕ} (hp : p.Prime) (h3 : p ≠ 3) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  have h : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases h with h0 | h12
  · have hdvd : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.2 h0
    have heq : 3 = p := (prime_dvd_prime_iff_eq prime_three hp).mp hdvd
    exact (h3 heq.symm).elim
  · exact h12

lemma six_dvd_of_two_dvd_of_three_dvd {n : ℕ} (h2 : 2 ∣ n) (h3 : 3 ∣ n) : 6 ∣ n := by
  have : Nat.lcm 2 3 ∣ n := Nat.lcm_dvd h2 h3
  simpa [show Nat.lcm 2 3 = 6 by decide] using this

lemma mem_Sset_of_even_of_not_dvd_three {n q : ℕ} (hn : Even n) (h3 : ¬ 3 ∣ n)
    (hq : q ∈ Sset n) : q = 3 ∨ q = n - 3 := by
  have h := mem_Sset_iff.mp hq
  have hqlt : q < n := h.1
  have hqP : q.Prime := h.2.1
  have hdiffP : (n - q).Prime := h.2.2.1
  have hsumP : (n + q).Prime := h.2.2.2
  have hq_ne2 : q ≠ 2 := by
    intro hq2
    subst hq2
    have heven_sum : Even (n + 2) := hn.add even_two
    have hne2 : n + 2 ≠ 2 := by omega
    exact not_prime_of_even_of_ne_two heven_sum hne2 hsumP
  by_cases hq3 : q = 3
  · exact Or.inl hq3
  · have hq_mod : q % 3 = 1 ∨ q % 3 = 2 := prime_mod_three_eq_one_or_two hqP hq3
    have hn_mod : n % 3 = 1 ∨ n % 3 = 2 := by
      have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases this with h0 | h12
      · exact (h3 (Nat.dvd_iff_mod_eq_zero.2 h0)).elim
      · exact h12
    have hsum_or_diff : (n + q) % 3 = 0 ∨ (n - q) % 3 = 0 := by
      rcases hn_mod with hn1 | hn2
      · rcases hq_mod with hq1 | hq2
        · right
          exact Nat.sub_mod_eq_zero_of_mod_eq (by omega)
        · left
          omega
      · rcases hq_mod with hq1 | hq2
        · left
          omega
        · right
          exact Nat.sub_mod_eq_zero_of_mod_eq (by omega)
    rcases hsum_or_diff with hsum0 | hdiff0
    · have hdvd : 3 ∣ n + q := Nat.dvd_iff_mod_eq_zero.2 hsum0
      have hgt : 3 < n + q := by
        have : 5 ≤ q := hqP.five_le_of_ne_two_of_ne_three hq_ne2 hq3
        omega
      exact absurd hsumP (not_prime_of_dvd_of_lt hdvd (by norm_num) hgt)
    · have hdvd : 3 ∣ n - q := Nat.dvd_iff_mod_eq_zero.2 hdiff0
      have hnqe : n - q = 3 := by
        by_contra hne
        have hge : 2 ≤ n - q := hdiffP.two_le
        have hcases : n - q < 3 ∨ 3 < n - q := by omega
        rcases hcases with hlt | hgt
        · have : n - q = 2 := by omega
          exact (by decide : ¬ 3 ∣ (2 : ℕ)) (this ▸ hdvd)
        · exact not_prime_of_dvd_of_lt hdvd (by norm_num) hgt hdiffP
      have : q = n - 3 := by omega
      exact Or.inr this

lemma Sset_subset_pair_of_even_of_not_dvd_three {n : ℕ} (hn : Even n) (h3 : ¬ 3 ∣ n) :
    Sset n ⊆ {3, n - 3} := by
  intro q hq
  rcases mem_Sset_of_even_of_not_dvd_three hn h3 hq with h | h
  · simp [h]
  · simp [h]

lemma a_le_two_of_even_of_not_dvd_three {n : ℕ} (hn : Even n) (h3 : ¬ 3 ∣ n) :
    a n ≤ 2 := by
  rw [a_eq_card_Sset]
  refine (card_le_card (Sset_subset_pair_of_even_of_not_dvd_three hn h3)).trans ?_
  apply (card_insert_le _ _).trans
  simp

lemma a_ne_four_of_even_of_not_dvd_three {n : ℕ} (hn : Even n) (h3 : ¬ 3 ∣ n) :
    a n ≠ 4 := by
  have : a n ≤ 2 := a_le_two_of_even_of_not_dvd_three hn h3
  omega

lemma a_ne_four_of_not_dvd_six {n : ℕ} (h : ¬ 6 ∣ n) : a n ≠ 4 := by
  by_cases hn2 : Even n
  · have h3 : ¬ 3 ∣ n := fun h3 =>
      h (six_dvd_of_two_dvd_of_three_dvd (even_iff_two_dvd.mp hn2) h3)
    exact a_ne_four_of_even_of_not_dvd_three hn2 h3
  · exact a_ne_four_of_odd (Nat.not_even_iff_odd.mp hn2)

set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma mem_Sset_of_primes {n q : ℕ}
    (h1 : q < n) (h2 : q.Prime) (h3 : (n - q).Prime) (h4 : (n + q).Prime) :
    q ∈ Sset n := mem_Sset_iff.mpr ⟨h1, h2, h3, h4⟩

lemma five_le_a_of_five_mem {n q1 q2 q3 q4 q5 : ℕ}
    (h1 : q1 ∈ Sset n) (h2 : q2 ∈ Sset n) (h3 : q3 ∈ Sset n)
    (h4 : q4 ∈ Sset n) (h5 : q5 ∈ Sset n)
    (hne : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q1 ≠ q4 ∧ q1 ≠ q5 ∧
           q2 ≠ q3 ∧ q2 ≠ q4 ∧ q2 ≠ q5 ∧
           q3 ≠ q4 ∧ q3 ≠ q5 ∧ q4 ≠ q5) :
    5 ≤ a n := by
  rw [a_eq_card_Sset]
  have hs : ({q1, q2, q3, q4, q5} : Finset ℕ) ⊆ Sset n := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
  have hc : 5 ≤ #({q1, q2, q3, q4, q5} : Finset ℕ) := by
    repeat first | rw [card_insert_of_notMem] | rw [card_singleton]
    · simp [hne]
    all_goals simp [hne]
  exact hc.trans (card_le_card hs)

macro "prove_in_Sset" : tactic => `(tactic|
  apply mem_Sset_of_primes <;> norm_num)





lemma a_ne_four_of_dvd_six_of_le_8000 {n : ℕ} (h6 : 6 ∣ n) (hle : n ≤ 8000) : a n ≠ 4 := by
  sorry

lemma two_not_mem_Sset_of_dvd_six {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) : 2 ∉ Sset n := by
  intro h
  have hsum : (n + 2).Prime := (mem_Sset_iff.mp h).2.2.2
  have heven : Even (n + 2) := (even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 6) h6)).add even_two
  have hne2 : n + 2 ≠ 2 := by omega
  exact not_prime_of_even_of_ne_two heven hne2 hsum

/-- If `6 ∣ n` and `n > 6` then `3` is not in `Sset n`. -/
lemma three_not_mem_Sset_of_dvd_six {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) : 3 ∉ Sset n := by
  intro h
  have hsum : (n + 3).Prime := (mem_Sset_iff.mp h).2.2.2
  have hdvd : 3 ∣ n + 3 := (dvd_trans (by decide : 3 ∣ 6) h6).add (dvd_refl 3)
  have hgt : 3 < n + 3 := by omega
  exact not_prime_of_dvd_of_lt hdvd (by norm_num) hgt hsum

/-- Elements of `Sset n` are at least `5` when `6 ∣ n` and `n > 6`. -/
lemma five_le_of_mem_Sset_of_dvd_six {n q : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hq : q ∈ Sset n) : 5 ≤ q := by
  have hP : q.Prime := (mem_Sset_iff.mp hq).2.1
  have hq2 : q ≠ 2 := fun h => two_not_mem_Sset_of_dvd_six h6 hn (h ▸ hq)
  have hq3 : q ≠ 3 := fun h => three_not_mem_Sset_of_dvd_six h6 hn (h ▸ hq)
  exact hP.five_le_of_ne_two_of_ne_three hq2 hq3

/-- Pairing: if `q ∈ Sset n` then `n - q ∈ Sset n` iff `2 * n - q` is prime. -/
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

/-- `q` is paired in `Sset n` if both `q` and `n - q` lie in `Sset n`. -/
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
  have hqP : q.Prime := (mem_Sset_iff.mp hq).2.1
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
    exact (Nat.Prime.dvd_mul prime_three).mp this |>.resolve_left (by decide)
  have hq3 : 3 < q := by
    have : 5 ≤ q := five_le_of_mem_Sset_of_dvd_six h6 hn hq
    omega
  exact (not_prime_of_dvd_of_lt h3q (by norm_num) hq3) hqP

/-- The pairing involution `q ↦ n - q` on `Sset n`. -/
def pairMap (n : ℕ) (q : ℕ) : ℕ := n - q

lemma pairMap_mem_of_isPaired {n q : ℕ} (h : IsPaired n q) :
    pairMap n q ∈ Sset n := h.2

lemma pairMap_sq {n q : ℕ} (hq : q < n) : pairMap n (pairMap n q) = q :=
  Nat.sub_sub_self (le_of_lt hq)

/-- Unpaired elements of `Sset n`. -/
def Unpaired (n : ℕ) : Finset ℕ :=
  (Sset n).filter (fun q => n - q ∉ Sset n)

/-- Paired elements of `Sset n`. -/
def Paired (n : ℕ) : Finset ℕ :=
  (Sset n).filter (fun q => n - q ∈ Sset n)

lemma mem_Unpaired_iff {n q : ℕ} :
    q ∈ Unpaired n ↔ q ∈ Sset n ∧ n - q ∉ Sset n := by
  simp [Unpaired, mem_filter]

lemma mem_Paired_iff {n q : ℕ} :
    q ∈ Paired n ↔ q ∈ Sset n ∧ n - q ∈ Sset n := by
  simp [Paired, mem_filter]

lemma paired_union_unpaired (n : ℕ) : Paired n ∪ Unpaired n = Sset n := by
  ext q
  simp [Paired, Unpaired, mem_filter, mem_union]
  tauto

lemma paired_disj_unpaired (n : ℕ) : Disjoint (Paired n) (Unpaired n) := by
  refine Finset.disjoint_left.mpr ?_
  intro q hqP hqU
  exact (mem_Unpaired_iff.mp hqU).2 (mem_Paired_iff.mp hqP).2

lemma card_Sset_eq_paired_add_unpaired (n : ℕ) :
    #(Sset n) = #(Paired n) + #(Unpaired n) := by
  rw [← card_union_of_disjoint (paired_disj_unpaired n), paired_union_unpaired]

lemma pairMap_mem_paired {n q : ℕ} (hq : q ∈ Paired n) :
    n - q ∈ Paired n := by
  have h := mem_Paired_iff.mp hq
  have hqlt : q < n := (mem_Sset_iff.mp h.1).1
  refine mem_Paired_iff.mpr ⟨h.2, ?_⟩
  simpa [Nat.sub_sub_self (le_of_lt hqlt)] using h.1

lemma pairMap_ne_self_of_mem_paired {n q : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hq : q ∈ Paired n) : n - q ≠ q := by
  have : q ∈ Sset n := (mem_Paired_iff.mp hq).1
  exact (not_eq_sub_self_of_mem_Sset h6 hn this).symm

lemma paired_lt_or_gt {n q : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) (hq : q ∈ Paired n) :
    q < n - q ∨ n - q < q := by
  have hne : n - q ≠ q := pairMap_ne_self_of_mem_paired h6 hn hq
  omega

/-- Representatives of pairing orbits: the smaller element of each pair. -/
def PairedRep (n : ℕ) : Finset ℕ :=
  (Paired n).filter (fun q => q < n - q)

lemma mem_PairedRep_iff {n q : ℕ} :
    q ∈ PairedRep n ↔ q ∈ Paired n ∧ q < n - q := by
  simp [PairedRep, mem_filter]

lemma paired_eq_reps_union_image {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) :
    Paired n = PairedRep n ∪ (PairedRep n).image (fun q => n - q) := by
  ext q
  constructor
  · intro hq
    rcases paired_lt_or_gt h6 hn hq with hlt | hgt
    · exact mem_union.mpr (Or.inl (mem_PairedRep_iff.mpr ⟨hq, hlt⟩))
    · refine mem_union.mpr (Or.inr ?_)
      refine mem_image.mpr ⟨n - q, ?_, ?_⟩
      · have hqlt : q < n := (mem_Sset_iff.mp (mem_Paired_iff.mp hq).1).1
        have : n - (n - q) = q := Nat.sub_sub_self (le_of_lt hqlt)
        refine mem_PairedRep_iff.mpr ⟨pairMap_mem_paired hq, ?_⟩
        simpa [this] using hgt
      · have hqlt : q < n := (mem_Sset_iff.mp (mem_Paired_iff.mp hq).1).1
        exact Nat.sub_sub_self (le_of_lt hqlt)
  · intro h
    rcases mem_union.mp h with h | h
    · exact (mem_PairedRep_iff.mp h).1
    · rcases mem_image.mp h with ⟨r, hr, rfl⟩
      exact pairMap_mem_paired (mem_PairedRep_iff.mp hr).1

lemma disjoint_reps_image {n : ℕ} (_h6 : 6 ∣ n) (_hn : 6 < n) :
    Disjoint (PairedRep n) ((PairedRep n).image (fun q => n - q)) := by
  refine Finset.disjoint_left.mpr ?_
  intro q hq1 hq2
  have h1 := mem_PairedRep_iff.mp hq1
  rcases mem_image.mp hq2 with ⟨r, hr, rfl⟩
  have h2 := mem_PairedRep_iff.mp hr
  have hrlt : r < n := (mem_Sset_iff.mp (mem_Paired_iff.mp h2.1).1).1
  have hlt : n - r < r := by
    have : n - r < n - (n - r) := h1.2
    simpa [Nat.sub_sub_self (le_of_lt hrlt)] using this
  exact lt_asymm h2.2 hlt

lemma card_image_sub_reps {n : ℕ} :
    #((PairedRep n).image (fun q => n - q)) = #(PairedRep n) := by
  refine Finset.card_image_iff.mpr ?_
  intro a ha b hb h
  have ha' := mem_PairedRep_iff.mp ha
  have hb' := mem_PairedRep_iff.mp hb
  have halt : a < n := (mem_Sset_iff.mp (mem_Paired_iff.mp ha'.1).1).1
  have hblt : b < n := (mem_Sset_iff.mp (mem_Paired_iff.mp hb'.1).1).1
  have haeq : n - (n - a) = a := Nat.sub_sub_self (le_of_lt halt)
  have hbeq : n - (n - b) = b := Nat.sub_sub_self (le_of_lt hblt)
  have h' : n - a = n - b := h
  rw [← haeq, ← hbeq, h']

/-- `Paired n` is a union of 2-cycles, hence even cardinality when `6 ∣ n` and `n > 6`. -/
lemma even_card_Paired {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) : Even #(Paired n) := by
  have hunion := paired_eq_reps_union_image h6 hn
  have hdisj := disjoint_reps_image h6 hn
  have hcard : #(Paired n) = 2 * #(PairedRep n) := by
    rw [hunion, card_union_of_disjoint hdisj, card_image_sub_reps]
    ring
  exact ⟨#(PairedRep n), by omega⟩

lemma a_eq_two_mul_P_add_U {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) :
    a n = 2 * (#(Paired n) / 2) + #(Unpaired n) := by
  rw [a_eq_card_Sset, card_Sset_eq_paired_add_unpaired]
  have he : Even #(Paired n) := even_card_Paired h6 hn
  have : 2 * (#(Paired n) / 2) = #(Paired n) := Nat.mul_div_cancel' (even_iff_two_dvd.mp he)
  omega

/-- The three configurations that would give `a n = 4`. -/
lemma a_eq_four_config {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) (ha : a n = 4) :
    (#(Paired n) = 4 ∧ #(Unpaired n) = 0) ∨
    (#(Paired n) = 2 ∧ #(Unpaired n) = 2) ∨
    (#(Paired n) = 0 ∧ #(Unpaired n) = 4) := by
  have hsum : #(Paired n) + #(Unpaired n) = 4 := by
    rw [← card_Sset_eq_paired_add_unpaired, ← a_eq_card_Sset, ha]
  have he : Even #(Paired n) := even_card_Paired h6 hn
  have hP4 : #(Paired n) ≤ 4 := by omega
  have : #(Paired n) = 0 ∨ #(Paired n) = 2 ∨ #(Paired n) = 4 := by
    have : #(Paired n) % 2 = 0 := Nat.even_iff.mp he
    interval_cases #(Paired n) <;> simp_all
  rcases this with h0 | h2 | h4
  · right; right; omega
  · right; left; omega
  · left; omega

/-- If a prime `p` divides `n` and `2 < p < n`, then `p ∉ Sset n`. -/
lemma not_mem_Sset_of_dvd {n p : ℕ} (hp : p.Prime) (hdvd : p ∣ n) (_h2 : 2 < p)
    (_hpn : p < n) : p ∉ Sset n := by
  intro h
  have hsum : (n + p).Prime := (mem_Sset_iff.mp h).2.2.2
  have hdiv : p ∣ n + p := hdvd.add (dvd_refl p)
  have hgt : p < n + p := by omega
  exact not_prime_of_dvd_of_lt hdiv hp.two_le hgt hsum

lemma prime_mod_five_ne_zero {p : ℕ} (hp : p.Prime) (h5 : p ≠ 5) : p % 5 ≠ 0 := by
  intro h0
  have hdvd : 5 ∣ p := Nat.dvd_iff_mod_eq_zero.2 h0
  have heq : 5 = p := (prime_dvd_prime_iff_eq prime_five hp).mp hdvd
  exact h5 heq.symm

/-- Elements of `Sset n` other than `5` are nonzero modulo `5`. -/
lemma mem_Sset_mod_five_ne_zero {n q : ℕ} (hq : q ∈ Sset n) (hne5 : q ≠ 5) :
    q % 5 ≠ 0 :=
  prime_mod_five_ne_zero (mem_Sset_iff.mp hq).2.1 hne5

lemma card_PairedRep_of_card_Paired {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n) :
    #(Paired n) = 2 * #(PairedRep n) := by
  have hunion := paired_eq_reps_union_image h6 hn
  have hdisj := disjoint_reps_image h6 hn
  rw [hunion, card_union_of_disjoint hdisj, card_image_sub_reps]
  ring

lemma pairedRep_card_two_of_paired_four {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hP : #(Paired n) = 4) : #(PairedRep n) = 2 := by
  have := card_PairedRep_of_card_Paired h6 hn
  omega

lemma pairedRep_card_one_of_paired_two {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hP : #(Paired n) = 2) : #(PairedRep n) = 1 := by
  have := card_PairedRep_of_card_Paired h6 hn
  omega

lemma pairedRep_card_zero_of_paired_zero {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hP : #(Paired n) = 0) : #(PairedRep n) = 0 := by
  have := card_PairedRep_of_card_Paired h6 hn
  omega

lemma exists_two_pairedReps {n : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hP : #(Paired n) = 4) :
    ∃ r s, r ∈ PairedRep n ∧ s ∈ PairedRep n ∧ r ≠ s := by
  have hcard : #(PairedRep n) = 2 := pairedRep_card_two_of_paired_four h6 hn hP
  have hne : (PairedRep n).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    simp [h] at hcard
  obtain ⟨r, hr⟩ := hne
  have hrest : (PairedRep n).erase r ≠ ∅ := by
    intro h
    have := card_erase_of_mem hr
    simp [hcard] at this
    simp [h] at this
  obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr hrest
  refine ⟨r, s, hr, mem_of_mem_erase hs, ?_⟩
  exact (ne_of_mem_erase hs).symm

/-- The eight primes attached to two pairing representatives. -/
lemma eight_primes_of_two_reps {n r s : ℕ} (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) :
    r.Prime ∧ (n - r).Prime ∧ (n + r).Prime ∧ (2 * n - r).Prime ∧
    s.Prime ∧ (n - s).Prime ∧ (n + s).Prime ∧ (2 * n - s).Prime := by
  have hrP := mem_PairedRep_iff.mp hr
  have hsP := mem_PairedRep_iff.mp hs
  have hrS : r ∈ Sset n := (mem_Paired_iff.mp hrP.1).1
  have hsS : s ∈ Sset n := (mem_Paired_iff.mp hsP.1).1
  have hr2 := (isPaired_iff hrS).mp ⟨hrS, (mem_Paired_iff.mp hrP.1).2⟩
  have hs2 := (isPaired_iff hsS).mp ⟨hsS, (mem_Paired_iff.mp hsP.1).2⟩
  exact ⟨(mem_Sset_iff.mp hrS).2.1, (mem_Sset_iff.mp hrS).2.2.1,
    (mem_Sset_iff.mp hrS).2.2.2, hr2,
    (mem_Sset_iff.mp hsS).2.1, (mem_Sset_iff.mp hsS).2.2.1,
    (mem_Sset_iff.mp hsS).2.2.2, hs2⟩

/-- The four diamond values attached to a pairing representative are prime. -/
lemma four_primes_of_pairedRep {n r : ℕ} (hr : r ∈ PairedRep n) :
    r.Prime ∧ (n - r).Prime ∧ (n + r).Prime ∧ (2 * n - r).Prime := by
  have h := eight_primes_of_two_reps hr hr
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

lemma not_dvd_five_of_prime_gt_five {m : ℕ} (hp : m.Prime) (hgt : 5 < m) : ¬ 5 ∣ m := by
  intro hd
  have : 5 = m := (prime_dvd_prime_iff_eq prime_five hp).mp hd
  omega

/-- If `5 ∤ n` and `r ∈ PairedRep n` with `r ≠ 5`, then `r ≡ 3 * n (mod 5)`. -/
lemma pairedRep_mod_five {n r : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hn5 : ¬ 5 ∣ n) (hr5 : r ≠ 5) :
    r % 5 = (3 * n) % 5 := by
  have hP := mem_PairedRep_iff.mp hr
  have ⟨hrp, hnrp, hnpr, h2nr⟩ := four_primes_of_pairedRep hr
  have hqlt : r < n := (mem_Sset_iff.mp (mem_Paired_iff.mp hP.1).1).1
  have h5le : 5 ≤ r := five_le_of_mem_Sset_of_dvd_six h6 hn (mem_Paired_iff.mp hP.1).1
  have hn0 : n % 5 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 hn5
  have hr0 : r % 5 ≠ 0 := prime_mod_five_ne_zero hrp hr5
  have hsub0 : (n - r) % 5 ≠ 0 := by
    intro h0
    exact (not_dvd_five_of_prime_gt_five hnrp (by omega))
      (Nat.dvd_iff_mod_eq_zero.2 h0)
  have hadd0 : (n + r) % 5 ≠ 0 := by
    intro h0
    exact (not_dvd_five_of_prime_gt_five hnpr (by omega))
      (Nat.dvd_iff_mod_eq_zero.2 h0)
  have h2n0 : (2 * n - r) % 5 ≠ 0 := by
    intro h0
    exact (not_dvd_five_of_prime_gt_five h2nr (by omega))
      (Nat.dvd_iff_mod_eq_zero.2 h0)
  have hrle : r ≤ n := Nat.le_of_lt hqlt
  have h2nle : r ≤ 2 * n := by omega
  -- Rewrite the three forbidden congruences in terms of `% 5`.
  have hadd_mod : (n % 5 + r % 5) % 5 ≠ 0 := by
    rw [← Nat.add_mod]; exact hadd0
  have hsub_mod : (n % 5 + 5 - r % 5) % 5 ≠ 0 := by
    have hnr : (n - r) % 5 = (n % 5 + 5 - r % 5) % 5 := by
      have := Nat.mod_add_div n 5
      have := Nat.mod_add_div r 5
      omega
    simpa [hnr] using hsub0
  have h2n_mod : (2 * (n % 5) + 5 - r % 5) % 5 ≠ 0 := by
    have : (2 * n - r) % 5 = (2 * (n % 5) + 5 - r % 5) % 5 := by
      omega
    simpa [this] using h2n0
  have hnlt : n % 5 < 5 := Nat.mod_lt _ (by decide)
  have hrlt5 : r % 5 < 5 := Nat.mod_lt _ (by decide)
  have hn1 : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  have hr1 : r % 5 = 1 ∨ r % 5 = 2 ∨ r % 5 = 3 ∨ r % 5 = 4 := by omega
  rcases hn1 with hn1 | hn1 | hn1 | hn1 <;> rcases hr1 with hr1 | hr1 | hr1 | hr1 <;>
    simp [hn1, hr1, Nat.mul_mod] at hadd_mod hsub_mod h2n_mod ⊢

lemma two_pairedReps_congruent_mod_five {n r s : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n)
    (hn5 : ¬ 5 ∣ n) (hr5 : r ≠ 5) (hs5 : s ≠ 5) :
    r % 5 = s % 5 := by
  rw [pairedRep_mod_five h6 hn hr hn5 hr5, pairedRep_mod_five h6 hn hs hn5 hs5]

lemma pairedRep_lt_half {n r : ℕ} (hr : r ∈ PairedRep n) : r < n - r :=
  (mem_PairedRep_iff.mp hr).2

lemma pairedRep_lt_n {n r : ℕ} (hr : r ∈ PairedRep n) : r < n := by
  have hS : r ∈ Sset n := (mem_Paired_iff.mp (mem_PairedRep_iff.mp hr).1).1
  exact (mem_Sset_iff.mp hS).1

lemma pairedRep_mem_Sset {n r : ℕ} (hr : r ∈ PairedRep n) : r ∈ Sset n :=
  (mem_Paired_iff.mp (mem_PairedRep_iff.mp hr).1).1

lemma sub_pairedRep_mem_Sset {n r : ℕ} (hr : r ∈ PairedRep n) : n - r ∈ Sset n :=
  (mem_Paired_iff.mp (mem_PairedRep_iff.mp hr).1).2

lemma unpaired_eq_empty_iff {n : ℕ} : Unpaired n = ∅ ↔ ∀ q ∈ Sset n, n - q ∈ Sset n := by
  constructor
  · intro h q hq
    by_contra hnq
    have : q ∈ Unpaired n := mem_Unpaired_iff.mpr ⟨hq, hnq⟩
    simp [h] at this
  · intro h
    ext q
    simp [mem_Unpaired_iff]
    intro hq
    exact h q hq

lemma Sset_eq_paired_of_unpaired_empty {n : ℕ} (h : Unpaired n = ∅) :
    Sset n = Paired n := by
  have := paired_union_unpaired n
  simpa [h] using this.symm

lemma five_mem_Sset_iff {n : ℕ} (hn : 5 < n) :
    5 ∈ Sset n ↔ (n - 5).Prime ∧ (n + 5).Prime := by
  constructor
  · intro h
    have := mem_Sset_iff.mp h
    exact ⟨this.2.2.1, this.2.2.2⟩
  · intro h
    exact mem_Sset_of_primes (by omega) prime_five h.1 h.2

lemma n_sub_five_mem_Sset_iff {n : ℕ} (hn : 5 < n) :
    n - 5 ∈ Sset n ↔ (n - 5).Prime ∧ (2 * n - 5).Prime := by
  constructor
  · intro h
    have := mem_Sset_iff.mp h
    have hsum : n + (n - 5) = 2 * n - 5 := by omega
    exact ⟨this.2.1, by simpa [hsum] using this.2.2.2⟩
  · intro h
    apply mem_Sset_of_primes
    · omega
    · exact h.1
    · simpa [Nat.sub_sub_self (by omega : 5 ≤ n)] using prime_five
    · have hsum : n + (n - 5) = 2 * n - 5 := by omega
      simpa [hsum] using h.2

/-- In the `(4,0)` configuration the Sset is exactly the two pairing orbits. -/
lemma Sset_eq_four_of_config40 {n r s : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s) :
    Sset n = {r, n - r, s, n - s} := by
  have hSeq : Sset n = Paired n := Sset_eq_paired_of_unpaired_empty hU
  have hcard : #(PairedRep n) = 2 := pairedRep_card_two_of_paired_four h6 hn hP
  have hsubset : {r, s} ⊆ PairedRep n := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard2 : #({r, s} : Finset ℕ) = 2 := by
    rw [card_insert_of_notMem, card_singleton]
    simpa using hrs
  have hrs_eq : ({r, s} : Finset ℕ) = PairedRep n :=
    Finset.eq_of_subset_of_card_le hsubset (by omega)
  have hunion := paired_eq_reps_union_image h6 hn
  rw [hSeq, hunion, ← hrs_eq]
  ext q
  constructor
  · intro h
    rcases mem_union.mp h with h | h
    · rcases mem_insert.mp h with rfl | h
      · simp
      · simp [mem_singleton.mp h]
    · rcases mem_image.mp h with ⟨a, ha, rfl⟩
      rcases mem_insert.mp ha with rfl | ha
      · simp
      · simp [mem_singleton.mp ha]
  · intro h
    simp only [mem_insert, mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact mem_union.mpr (Or.inl (by simp))
    · refine mem_union.mpr (Or.inr (mem_image.mpr ⟨r, by simp, rfl⟩))
    · exact mem_union.mpr (Or.inl (by simp))
    · refine mem_union.mpr (Or.inr (mem_image.mpr ⟨s, by simp, rfl⟩))

lemma eight_distinct_of_two_reps {n r s : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s) :
    r ≠ n - r ∧ r ≠ s ∧ r ≠ n - s ∧ r ≠ n + r ∧ r ≠ n + s ∧ r ≠ 2 * n - r ∧ r ≠ 2 * n - s ∧
    n - r ≠ s ∧ n - r ≠ n - s ∧ n - r ≠ n + r ∧ n - r ≠ n + s ∧ n - r ≠ 2 * n - r ∧
    n - r ≠ 2 * n - s ∧ s ≠ n - s ∧ s ≠ n + r ∧ s ≠ n + s ∧ s ≠ 2 * n - r ∧ s ≠ 2 * n - s ∧
    n - s ≠ n + r ∧ n - s ≠ n + s ∧ n - s ≠ 2 * n - r ∧ n - s ≠ 2 * n - s ∧
    n + r ≠ n + s ∧ n + r ≠ 2 * n - r ∧ n + r ≠ 2 * n - s ∧
    n + s ≠ 2 * n - r ∧ n + s ≠ 2 * n - s ∧ 2 * n - r ≠ 2 * n - s := by
  have hrlt := pairedRep_lt_half hr
  have hslt := pairedRep_lt_half hs
  have hrn := pairedRep_lt_n hr
  have hsn := pairedRep_lt_n hs
  have hrS := pairedRep_mem_Sset hr
  have hsS := pairedRep_mem_Sset hs
  have hne_r := not_eq_sub_self_of_mem_Sset h6 hn hrS
  have hne_s := not_eq_sub_self_of_mem_Sset h6 hn hsS
  have h2r : 2 * r < n := by omega
  have h2s : 2 * s < n := by omega
  have hrs_lt : r + s < n := by omega
  have hrpos : 0 < r := (mem_Sset_iff.mp hrS).2.1.pos
  have hspos : 0 < s := (mem_Sset_iff.mp hsS).2.1.pos
  refine ⟨hne_r, hrs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hne_s, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; omega)

/-- If `6 ∣ n` and `5 ∤ n` then `n` is `6,12,18` or `24` modulo `30`. -/
lemma mod_thirty_of_dvd_six_of_not_dvd_five {n : ℕ} (h6 : 6 ∣ n) (hn5 : ¬ 5 ∣ n) :
    n % 30 = 6 ∨ n % 30 = 12 ∨ n % 30 = 18 ∨ n % 30 = 24 := by
  have h30 : n % 30 < 30 := Nat.mod_lt _ (by decide)
  have h2 : n % 2 = 0 := Nat.mod_eq_zero_of_dvd (dvd_trans (by decide : 2 ∣ 6) h6)
  have h3 : n % 3 = 0 := Nat.mod_eq_zero_of_dvd (dvd_trans (by decide : 3 ∣ 6) h6)
  have h5 : n % 5 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 hn5
  have : n % 30 = 0 ∨ n % 30 = 6 ∨ n % 30 = 12 ∨ n % 30 = 18 ∨ n % 30 = 24 := by
    omega
  rcases this with h | h | h | h | h
  · have : n % 5 = 0 := by omega
    exact (h5 this).elim
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

lemma five_not_mem_Sset_of_dvd_five {n : ℕ} (h5 : 5 ∣ n) (hn : 5 < n) : 5 ∉ Sset n :=
  not_mem_Sset_of_dvd prime_five h5 (by decide) hn

/-- A pairing representative other than `5` is coprime to `30` when `6 ∣ n`. -/
lemma pairedRep_coprime_thirty {n r : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hr5 : r ≠ 5) : ¬ 2 ∣ r ∧ ¬ 3 ∣ r ∧ ¬ 5 ∣ r := by
  have hrp := (four_primes_of_pairedRep hr).1
  have h5le : 5 ≤ r := five_le_of_mem_Sset_of_dvd_six h6 hn (pairedRep_mem_Sset hr)
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : 2 = r := (prime_dvd_prime_iff_eq Nat.prime_two hrp).mp h
    omega
  · intro h
    have : 3 = r := (prime_dvd_prime_iff_eq prime_three hrp).mp h
    omega
  · intro h
    have : 5 = r := (prime_dvd_prime_iff_eq prime_five hrp).mp h
    exact hr5 this.symm

/-- If `n ≡ 6 (mod 30)` and `r ∈ PairedRep n` with `r ≠ 5`, then `r ≡ 13` or `23 (mod 30)`. -/
lemma pairedRep_mod_thirty_of_n_mod_six {n r : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hn6 : n % 30 = 6) (hr5 : r ≠ 5) :
    r % 30 = 13 ∨ r % 30 = 23 := by
  have ⟨h2, h3, h5⟩ := pairedRep_coprime_thirty h6 hn hr hr5
  have hrlt : r % 30 < 30 := Nat.mod_lt _ (by decide)
  have hr2 : r % 2 = 1 := by
    have : r % 2 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h2
    omega
  have hr3 : r % 3 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h3
  have hr5m : r % 5 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h5
  have hcong : r % 5 = (3 * n) % 5 :=
    pairedRep_mod_five h6 hn hr (by
      intro h
      have : n % 5 = 0 := Nat.mod_eq_zero_of_dvd h
      omega) hr5
  have : (3 * n) % 5 = 3 := by
    have : n % 5 = 1 := by omega
    simp [Nat.mul_mod, this]
  have hr5eq : r % 5 = 3 := by omega
  have : r % 30 = 1 ∨ r % 30 = 7 ∨ r % 30 = 11 ∨ r % 30 = 13 ∨
         r % 30 = 17 ∨ r % 30 = 19 ∨ r % 30 = 23 ∨ r % 30 = 29 := by
    omega
  rcases this with h | h | h | h | h | h | h | h <;> first | exact Or.inl h | exact Or.inr h | omega

lemma pairedRep_mod_thirty_of_n_mod_twelve {n r : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hn12 : n % 30 = 12) (hr5 : r ≠ 5) :
    r % 30 = 1 ∨ r % 30 = 11 := by
  have ⟨h2, h3, h5⟩ := pairedRep_coprime_thirty h6 hn hr hr5
  have hrlt : r % 30 < 30 := Nat.mod_lt _ (by decide)
  have hcong : r % 5 = (3 * n) % 5 :=
    pairedRep_mod_five h6 hn hr (by intro h; have : n % 5 = 0 := Nat.mod_eq_zero_of_dvd h; omega) hr5
  have : (3 * n) % 5 = 1 := by
    have : n % 5 = 2 := by omega
    simp [Nat.mul_mod, this]
  have hr5eq : r % 5 = 1 := by omega
  have hr2 : r % 2 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h2
  have hr3 : r % 3 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h3
  have : r % 30 = 1 ∨ r % 30 = 7 ∨ r % 30 = 11 ∨ r % 30 = 13 ∨
         r % 30 = 17 ∨ r % 30 = 19 ∨ r % 30 = 23 ∨ r % 30 = 29 := by
    omega
  rcases this with h | h | h | h | h | h | h | h <;> first | exact Or.inl h | exact Or.inr h | omega

lemma pairedRep_mod_thirty_of_n_mod_eighteen {n r : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hn18 : n % 30 = 18) (hr5 : r ≠ 5) :
    r % 30 = 19 ∨ r % 30 = 29 := by
  have ⟨h2, h3, h5⟩ := pairedRep_coprime_thirty h6 hn hr hr5
  have hcong : r % 5 = (3 * n) % 5 :=
    pairedRep_mod_five h6 hn hr (by intro h; have : n % 5 = 0 := Nat.mod_eq_zero_of_dvd h; omega) hr5
  have : (3 * n) % 5 = 4 := by
    have : n % 5 = 3 := by omega
    simp [Nat.mul_mod, this]
  have hr5eq : r % 5 = 4 := by omega
  have hr2 : r % 2 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h2
  have hr3 : r % 3 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h3
  have : r % 30 = 1 ∨ r % 30 = 7 ∨ r % 30 = 11 ∨ r % 30 = 13 ∨
         r % 30 = 17 ∨ r % 30 = 19 ∨ r % 30 = 23 ∨ r % 30 = 29 := by
    omega
  rcases this with h | h | h | h | h | h | h | h <;> first | exact Or.inl h | exact Or.inr h | omega

lemma pairedRep_mod_thirty_of_n_mod_twentyfour {n r : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hn24 : n % 30 = 24) (hr5 : r ≠ 5) :
    r % 30 = 7 ∨ r % 30 = 17 := by
  have ⟨h2, h3, h5⟩ := pairedRep_coprime_thirty h6 hn hr hr5
  have hcong : r % 5 = (3 * n) % 5 :=
    pairedRep_mod_five h6 hn hr (by intro h; have : n % 5 = 0 := Nat.mod_eq_zero_of_dvd h; omega) hr5
  have : (3 * n) % 5 = 2 := by
    have : n % 5 = 4 := by omega
    simp [Nat.mul_mod, this]
  have hr5eq : r % 5 = 2 := by omega
  have hr2 : r % 2 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h2
  have hr3 : r % 3 ≠ 0 := mt Nat.dvd_iff_mod_eq_zero.2 h3
  have : r % 30 = 1 ∨ r % 30 = 7 ∨ r % 30 = 11 ∨ r % 30 = 13 ∨
         r % 30 = 17 ∨ r % 30 = 19 ∨ r % 30 = 23 ∨ r % 30 = 29 := by
    omega
  rcases this with h | h | h | h | h | h | h | h <;> first | exact Or.inl h | exact Or.inr h | omega

lemma five_ne_sub_pairedRep {n r : ℕ} (hr : r ∈ PairedRep n) (hn : 10 < n) : 5 ≠ n - r := by
  have hlt := pairedRep_lt_half hr
  have hrn := pairedRep_lt_n hr
  omega

lemma seven_ne_sub_pairedRep {n r : ℕ} (hr : r ∈ PairedRep n) (hn : 14 < n) : 7 ≠ n - r := by
  have hlt := pairedRep_lt_half hr
  have hrn := pairedRep_lt_n hr
  omega

lemma five_not_mem_Sset_of_config40 {n r s : ℕ} (h6 : 6 ∣ n) (hn : 10 < n)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) : 5 ∉ Sset n := by
  have hS := Sset_eq_four_of_config40 h6 (by omega) hP hU hr hs hrs
  intro h5
  have : 5 = r ∨ 5 = n - r ∨ 5 = s ∨ 5 = n - s := by
    simpa [hS] using h5
  rcases this with h | h | h | h
  · exact hr5 h.symm
  · exact (five_ne_sub_pairedRep hr hn) h
  · exact hs5 h.symm
  · exact (five_ne_sub_pairedRep hs hn) h

/-- If `n ≡ 6 (mod 30)` and `q ≡ 7 (mod 30)` with `q ≤ 2 * n`, then `5 ∣ 2 * n - q`. -/
lemma five_dvd_two_n_sub_of_mod_six_seven {n q : ℕ} (hn : n % 30 = 6) (hq : q % 30 = 7)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 1 := by omega
    have hq5 : q % 5 = 2 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

/-- If `n ≡ 6 (mod 30)` and `q ≡ 17 (mod 30)` with `q ≤ 2 * n`, then `5 ∣ 2 * n - q`. -/
lemma five_dvd_two_n_sub_of_mod_six_seventeen {n q : ℕ} (hn : n % 30 = 6) (hq : q % 30 = 17)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 1 := by omega
    have hq5 : q % 5 = 2 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

/-- For `n ≡ 6 (mod 30)` a generic `q ≡ 7 (mod 30)` cannot be paired. -/
lemma not_mem_Paired_of_n_mod_six_of_q_mod_seven {n q : ℕ}
    (_h6 : 6 ∣ n) (_hn : 14 < n) (hn6 : n % 30 = 6) (hq7 : q % 30 = 7)
    (hq : q ∈ Sset n) : q ∈ Unpaired n := by
  have hqlt : q < n := (mem_Sset_iff.mp hq).1
  have h2n : 5 ∣ 2 * n - q := five_dvd_two_n_sub_of_mod_six_seven hn6 hq7 (by omega)
  have h2nlt : 5 < 2 * n - q := by omega
  have hnp : ¬ (2 * n - q).Prime :=
    not_prime_of_dvd_of_lt h2n (by decide) h2nlt
  have : n - q ∉ Sset n := by
    intro hnq
    have := (sub_mem_Sset_iff hq).mp hnq
    exact hnp this
  exact mem_Unpaired_iff.mpr ⟨hq, this⟩

lemma not_mem_Paired_of_n_mod_six_of_q_mod_seventeen {n q : ℕ}
    (_h6 : 6 ∣ n) (_hn : 34 < n) (hn6 : n % 30 = 6) (hq17 : q % 30 = 17)
    (hq : q ∈ Sset n) : q ∈ Unpaired n := by
  have hqlt : q < n := (mem_Sset_iff.mp hq).1
  have h2n : 5 ∣ 2 * n - q := five_dvd_two_n_sub_of_mod_six_seventeen hn6 hq17 (by omega)
  have h2nlt : 5 < 2 * n - q := by omega
  have hnp : ¬ (2 * n - q).Prime :=
    not_prime_of_dvd_of_lt h2n (by decide) h2nlt
  have : n - q ∉ Sset n := by
    intro hnq
    have := (sub_mem_Sset_iff hq).mp hnq
    exact hnp this
  exact mem_Unpaired_iff.mpr ⟨hq, this⟩

/-- In a `(4,0)` configuration with `n ≡ 6 (mod 30)`, nothing of residue `7` is in `Sset`. -/
lemma not_mem_Sset_of_config40_n_mod_six_q_mod_seven {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 14 < n) (hn6 : n % 30 = 6)
    (hU : Unpaired n = ∅) (hq7 : q % 30 = 7) : q ∉ Sset n := by
  intro hq
  have hUmem := not_mem_Paired_of_n_mod_six_of_q_mod_seven h6 hn hn6 hq7 hq
  simp [hU] at hUmem

lemma not_mem_Sset_of_config40_n_mod_six_q_mod_seventeen {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 34 < n) (hn6 : n % 30 = 6)
    (hU : Unpaired n = ∅) (hq17 : q % 30 = 17) : q ∉ Sset n := by
  intro hq
  have hUmem := not_mem_Paired_of_n_mod_six_of_q_mod_seventeen h6 hn hn6 hq17 hq
  simp [hU] at hUmem

/-- Automatic unpaired residues for the other classes modulo 30. -/
lemma five_dvd_two_n_sub_of_mod_twelve_nineteen {n q : ℕ} (hn : n % 30 = 12) (hq : q % 30 = 19)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 2 := by omega
    have hq5 : q % 5 = 4 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

lemma five_dvd_two_n_sub_of_mod_twelve_twenty_nine {n q : ℕ} (hn : n % 30 = 12) (hq : q % 30 = 29)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 2 := by omega
    have hq5 : q % 5 = 4 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

lemma five_dvd_two_n_sub_of_mod_eighteen_one {n q : ℕ} (hn : n % 30 = 18) (hq : q % 30 = 1)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 3 := by omega
    have hq5 : q % 5 = 1 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

lemma five_dvd_two_n_sub_of_mod_eighteen_eleven {n q : ℕ} (hn : n % 30 = 18) (hq : q % 30 = 11)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 3 := by omega
    have hq5 : q % 5 = 1 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

lemma five_dvd_two_n_sub_of_mod_twentyfour_thirteen {n q : ℕ} (hn : n % 30 = 24) (hq : q % 30 = 13)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 4 := by omega
    have hq5 : q % 5 = 3 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

lemma five_dvd_two_n_sub_of_mod_twentyfour_twenty_three {n q : ℕ} (hn : n % 30 = 24) (hq : q % 30 = 23)
    (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  have : (2 * n - q) % 5 = 0 := by
    have hn5 : n % 5 = 4 := by omega
    have hq5 : q % 5 = 3 := by omega
    omega
  exact Nat.dvd_iff_mod_eq_zero.2 this

/-- In a `(4,0)` configuration with `n ≡ 6 (mod 30)` and generic representatives,
every element of `Sset` is `13` or `23` modulo `30`. -/
lemma mem_Sset_mod_thirty_of_config40_n_mod_six {n q r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn6 : n % 30 = 6)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) (hq : q ∈ Sset n) :
    q % 30 = 13 ∨ q % 30 = 23 := by
  have hS := Sset_eq_four_of_config40 h6 (by omega) hP hU hr hs hrs
  have : q = r ∨ q = n - r ∨ q = s ∨ q = n - s := by
    simpa [hS] using hq
  have hr30 := pairedRep_mod_thirty_of_n_mod_six h6 (by omega) hr hn6 hr5
  have hs30 := pairedRep_mod_thirty_of_n_mod_six h6 (by omega) hs hn6 hs5
  have hrn := pairedRep_lt_n hr
  have hsn := pairedRep_lt_n hs
  have hnr30 : (n - r) % 30 = 13 ∨ (n - r) % 30 = 23 := by
    have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
    rcases hr30 with h | h <;> omega
  have hns30 : (n - s) % 30 = 13 ∨ (n - s) % 30 = 23 := by
    have : (n - s) % 30 = (n % 30 + 30 - s % 30) % 30 := by omega
    rcases hs30 with h | h <;> omega
  rcases this with h | h | h | h
  · simpa [h] using hr30
  · simpa [h] using hnr30
  · simpa [h] using hs30
  · simpa [h] using hns30

lemma n_sub_five_not_mem_Sset_of_config40_n_mod_six {n r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn6 : n % 30 = 6)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) : n - 5 ∉ Sset n := by
  intro hq
  have hmod := mem_Sset_mod_thirty_of_config40_n_mod_six h6 hn hn6 hP hU hr hs hrs hr5 hs5 hq
  have : (n - 5) % 30 = 1 := by omega
  omega

/-- Analogous residue lock for `n ≡ 12 (mod 30)`. -/
lemma five_dvd_two_n_sub_of_mod_twelve_of {n q : ℕ} (hn : n % 30 = 12)
    (hq : q % 30 = 19 ∨ q % 30 = 29) (hle : q ≤ 2 * n) : 5 ∣ 2 * n - q := by
  rcases hq with h | h
  · exact five_dvd_two_n_sub_of_mod_twelve_nineteen hn h hle
  · exact five_dvd_two_n_sub_of_mod_twelve_twenty_nine hn h hle

lemma not_mem_Paired_of_n_mod_twelve_auto {n q : ℕ}
    (_h6 : 6 ∣ n) (_hn : 34 < n) (hn12 : n % 30 = 12)
    (hqres : q % 30 = 19 ∨ q % 30 = 29) (hq : q ∈ Sset n) : q ∈ Unpaired n := by
  have hqlt : q < n := (mem_Sset_iff.mp hq).1
  have h2n : 5 ∣ 2 * n - q := five_dvd_two_n_sub_of_mod_twelve_of hn12 hqres (by omega)
  have h2nlt : 5 < 2 * n - q := by omega
  have hnp : ¬ (2 * n - q).Prime := not_prime_of_dvd_of_lt h2n (by decide) h2nlt
  have : n - q ∉ Sset n := by
    intro hnq
    exact hnp ((sub_mem_Sset_iff hq).mp hnq)
  exact mem_Unpaired_iff.mpr ⟨hq, this⟩

lemma not_mem_Sset_of_config40_n_mod_twelve_auto {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 34 < n) (hn12 : n % 30 = 12)
    (hU : Unpaired n = ∅) (hqres : q % 30 = 19 ∨ q % 30 = 29) : q ∉ Sset n := by
  intro hq
  have := not_mem_Paired_of_n_mod_twelve_auto h6 hn hn12 hqres hq
  simp [hU] at this

lemma not_mem_Paired_of_n_mod_eighteen_auto {n q : ℕ}
    (_h6 : 6 ∣ n) (_hn : 34 < n) (hn18 : n % 30 = 18)
    (hqres : q % 30 = 1 ∨ q % 30 = 11) (hq : q ∈ Sset n) : q ∈ Unpaired n := by
  have hqlt : q < n := (mem_Sset_iff.mp hq).1
  have h2n : 5 ∣ 2 * n - q := by
    rcases hqres with h | h
    · exact five_dvd_two_n_sub_of_mod_eighteen_one hn18 h (by omega)
    · exact five_dvd_two_n_sub_of_mod_eighteen_eleven hn18 h (by omega)
  have h2nlt : 5 < 2 * n - q := by omega
  have hnp : ¬ (2 * n - q).Prime := not_prime_of_dvd_of_lt h2n (by decide) h2nlt
  have : n - q ∉ Sset n := by
    intro hnq
    exact hnp ((sub_mem_Sset_iff hq).mp hnq)
  exact mem_Unpaired_iff.mpr ⟨hq, this⟩

lemma not_mem_Sset_of_config40_n_mod_eighteen_auto {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 34 < n) (hn18 : n % 30 = 18)
    (hU : Unpaired n = ∅) (hqres : q % 30 = 1 ∨ q % 30 = 11) : q ∉ Sset n := by
  intro hq
  have := not_mem_Paired_of_n_mod_eighteen_auto h6 hn hn18 hqres hq
  simp [hU] at this

lemma not_mem_Paired_of_n_mod_twentyfour_auto {n q : ℕ}
    (_h6 : 6 ∣ n) (_hn : 34 < n) (hn24 : n % 30 = 24)
    (hqres : q % 30 = 13 ∨ q % 30 = 23) (hq : q ∈ Sset n) : q ∈ Unpaired n := by
  have hqlt : q < n := (mem_Sset_iff.mp hq).1
  have h2n : 5 ∣ 2 * n - q := by
    rcases hqres with h | h
    · exact five_dvd_two_n_sub_of_mod_twentyfour_thirteen hn24 h (by omega)
    · exact five_dvd_two_n_sub_of_mod_twentyfour_twenty_three hn24 h (by omega)
  have h2nlt : 5 < 2 * n - q := by omega
  have hnp : ¬ (2 * n - q).Prime := not_prime_of_dvd_of_lt h2n (by decide) h2nlt
  have : n - q ∉ Sset n := by
    intro hnq
    exact hnp ((sub_mem_Sset_iff hq).mp hnq)
  exact mem_Unpaired_iff.mpr ⟨hq, this⟩

lemma not_mem_Sset_of_config40_n_mod_twentyfour_auto {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 34 < n) (hn24 : n % 30 = 24)
    (hU : Unpaired n = ∅) (hqres : q % 30 = 13 ∨ q % 30 = 23) : q ∉ Sset n := by
  intro hq
  have := not_mem_Paired_of_n_mod_twentyfour_auto h6 hn hn24 hqres hq
  simp [hU] at this

/-- Residue lock for `Sset` in a generic `(4,0)` configuration, `n ≡ 12 (mod 30)`. -/
lemma mem_Sset_mod_thirty_of_config40_n_mod_twelve {n q r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn12 : n % 30 = 12)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) (hq : q ∈ Sset n) :
    q % 30 = 1 ∨ q % 30 = 11 := by
  have hS := Sset_eq_four_of_config40 h6 (by omega) hP hU hr hs hrs
  have : q = r ∨ q = n - r ∨ q = s ∨ q = n - s := by
    simpa [hS] using hq
  have hr30 := pairedRep_mod_thirty_of_n_mod_twelve h6 (by omega) hr hn12 hr5
  have hs30 := pairedRep_mod_thirty_of_n_mod_twelve h6 (by omega) hs hn12 hs5
  have hrn := pairedRep_lt_n hr
  have hsn := pairedRep_lt_n hs
  have hnr30 : (n - r) % 30 = 1 ∨ (n - r) % 30 = 11 := by
    have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
    rcases hr30 with h | h <;> omega
  have hns30 : (n - s) % 30 = 1 ∨ (n - s) % 30 = 11 := by
    have : (n - s) % 30 = (n % 30 + 30 - s % 30) % 30 := by omega
    rcases hs30 with h | h <;> omega
  rcases this with h | h | h | h
  · simpa [h] using hr30
  · simpa [h] using hnr30
  · simpa [h] using hs30
  · simpa [h] using hns30

lemma n_sub_five_not_mem_Sset_of_config40_n_mod_twelve {n r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn12 : n % 30 = 12)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) : n - 5 ∉ Sset n := by
  intro hq
  have hmod := mem_Sset_mod_thirty_of_config40_n_mod_twelve h6 hn hn12 hP hU hr hs hrs hr5 hs5 hq
  have : (n - 5) % 30 = 7 := by omega
  omega

/-- Residue lock for `Sset` in a generic `(4,0)` configuration, `n ≡ 18 (mod 30)`. -/
lemma mem_Sset_mod_thirty_of_config40_n_mod_eighteen {n q r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn18 : n % 30 = 18)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) (hq : q ∈ Sset n) :
    q % 30 = 19 ∨ q % 30 = 29 := by
  have hS := Sset_eq_four_of_config40 h6 (by omega) hP hU hr hs hrs
  have : q = r ∨ q = n - r ∨ q = s ∨ q = n - s := by
    simpa [hS] using hq
  have hr30 := pairedRep_mod_thirty_of_n_mod_eighteen h6 (by omega) hr hn18 hr5
  have hs30 := pairedRep_mod_thirty_of_n_mod_eighteen h6 (by omega) hs hn18 hs5
  have hrn := pairedRep_lt_n hr
  have hsn := pairedRep_lt_n hs
  have hnr30 : (n - r) % 30 = 19 ∨ (n - r) % 30 = 29 := by
    have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
    rcases hr30 with h | h <;> omega
  have hns30 : (n - s) % 30 = 19 ∨ (n - s) % 30 = 29 := by
    have : (n - s) % 30 = (n % 30 + 30 - s % 30) % 30 := by omega
    rcases hs30 with h | h <;> omega
  rcases this with h | h | h | h
  · simpa [h] using hr30
  · simpa [h] using hnr30
  · simpa [h] using hs30
  · simpa [h] using hns30

lemma n_sub_five_not_mem_Sset_of_config40_n_mod_eighteen {n r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn18 : n % 30 = 18)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) : n - 5 ∉ Sset n := by
  intro hq
  have hmod := mem_Sset_mod_thirty_of_config40_n_mod_eighteen h6 hn hn18 hP hU hr hs hrs hr5 hs5 hq
  have : (n - 5) % 30 = 13 := by omega
  omega

/-- Residue lock for `Sset` in a generic `(4,0)` configuration, `n ≡ 24 (mod 30)`. -/
lemma mem_Sset_mod_thirty_of_config40_n_mod_twentyfour {n q r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn24 : n % 30 = 24)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) (hq : q ∈ Sset n) :
    q % 30 = 7 ∨ q % 30 = 17 := by
  have hS := Sset_eq_four_of_config40 h6 (by omega) hP hU hr hs hrs
  have : q = r ∨ q = n - r ∨ q = s ∨ q = n - s := by
    simpa [hS] using hq
  have hr30 := pairedRep_mod_thirty_of_n_mod_twentyfour h6 (by omega) hr hn24 hr5
  have hs30 := pairedRep_mod_thirty_of_n_mod_twentyfour h6 (by omega) hs hn24 hs5
  have hrn := pairedRep_lt_n hr
  have hsn := pairedRep_lt_n hs
  have hnr30 : (n - r) % 30 = 7 ∨ (n - r) % 30 = 17 := by
    have : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
    rcases hr30 with h | h <;> omega
  have hns30 : (n - s) % 30 = 7 ∨ (n - s) % 30 = 17 := by
    have : (n - s) % 30 = (n % 30 + 30 - s % 30) % 30 := by omega
    rcases hs30 with h | h <;> omega
  rcases this with h | h | h | h
  · simpa [h] using hr30
  · simpa [h] using hnr30
  · simpa [h] using hs30
  · simpa [h] using hns30

lemma n_sub_five_not_mem_Sset_of_config40_n_mod_twentyfour {n r s : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn24 : n % 30 = 24)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) : n - 5 ∉ Sset n := by
  intro hq
  have hmod := mem_Sset_mod_thirty_of_config40_n_mod_twentyfour h6 hn hn24 hP hU hr hs hrs hr5 hs5 hq
  have : (n - 5) % 30 = 19 := by omega
  omega

/-- A prime other than `2,3,5` is coprime to `30`, hence one of the eight units mod `30`. -/
lemma prime_mod_thirty_of_gt_five {q : ℕ} (hq : q.Prime) (h5 : 5 < q) :
    q % 30 = 1 ∨ q % 30 = 7 ∨ q % 30 = 11 ∨ q % 30 = 13 ∨
    q % 30 = 17 ∨ q % 30 = 19 ∨ q % 30 = 23 ∨ q % 30 = 29 := by
  have h2 : q % 2 = 1 := by
    have : q ≠ 2 := by omega
    exact (hq.eq_two_or_odd).resolve_left this
  have h3 : q % 3 ≠ 0 := by
    intro h0
    have hdvd : 3 ∣ q := Nat.dvd_iff_mod_eq_zero.2 h0
    have : 3 = q := (prime_dvd_prime_iff_eq prime_three hq).mp hdvd
    omega
  have h5m : q % 5 ≠ 0 := by
    intro h0
    have hdvd : 5 ∣ q := Nat.dvd_iff_mod_eq_zero.2 h0
    have : 5 = q := (prime_dvd_prime_iff_eq prime_five hq).mp hdvd
    omega
  have hlt : q % 30 < 30 := Nat.mod_lt _ (by decide)
  have hcases : q % 30 = 0 ∨ q % 30 = 1 ∨ q % 30 = 2 ∨ q % 30 = 3 ∨ q % 30 = 4 ∨
      q % 30 = 5 ∨ q % 30 = 6 ∨ q % 30 = 7 ∨ q % 30 = 8 ∨ q % 30 = 9 ∨
      q % 30 = 10 ∨ q % 30 = 11 ∨ q % 30 = 12 ∨ q % 30 = 13 ∨ q % 30 = 14 ∨
      q % 30 = 15 ∨ q % 30 = 16 ∨ q % 30 = 17 ∨ q % 30 = 18 ∨ q % 30 = 19 ∨
      q % 30 = 20 ∨ q % 30 = 21 ∨ q % 30 = 22 ∨ q % 30 = 23 ∨ q % 30 = 24 ∨
      q % 30 = 25 ∨ q % 30 = 26 ∨ q % 30 = 27 ∨ q % 30 = 28 ∨ q % 30 = 29 := by
    omega
  rcases hcases with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inl h
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 5 = 0 := by omega
    exact (h5m this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inl h)
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inl h))
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 5 = 0 := by omega
    exact (h5m this).elim
  · have : q % 2 = 0 := by omega
    omega
  · have : q % 3 = 0 := by omega
    exact (h3 this).elim
  · have : q % 2 = 0 := by omega
    omega
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-- Unpaired elements are never `≡ 13` or `23` *and* paired; this records the
auto-unpaired residues for a generic unpaired element when `n ≡ 6 (mod 30)`. -/
lemma unpaired_mod_thirty_candidates_n_mod_six {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 6 < n) (hn6 : n % 30 = 6) (hq : q ∈ Unpaired n) :
    q = 5 ∨ q = n - 5 ∨ q % 30 = 7 ∨ q % 30 = 17 ∨ q % 30 = 13 ∨ q % 30 = 23 := by
  have hqS : q ∈ Sset n := (mem_Unpaired_iff.mp hq).1
  have hqP : q.Prime := (mem_Sset_iff.mp hqS).2.1
  have h5le : 5 ≤ q := five_le_of_mem_Sset_of_dvd_six h6 hn hqS
  by_cases h5 : q = 5
  · exact Or.inl h5
  · by_cases hn5 : q = n - 5
    · exact Or.inr (Or.inl hn5)
    · have h5lt : 5 < q := by omega
      have : q % 30 = 1 ∨ q % 30 = 7 ∨ q % 30 = 11 ∨ q % 30 = 13 ∨
             q % 30 = 17 ∨ q % 30 = 19 ∨ q % 30 = 23 ∨ q % 30 = 29 :=
        prime_mod_thirty_of_gt_five hqP h5lt
      rcases this with h | h | h | h | h | h | h | h
      · -- `q ≡ 1 (mod 30)` generic is `n - q ≡ 5 (mod 30)`, hence composite unless `q = n - 5`.
        have hnq : (n - q) % 30 = 5 := by
          have hqlt' : q < n := (mem_Sset_iff.mp hqS).1
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : n - q ≠ 5 := by
            intro heq
            have : q = n - 5 := by omega
            exact hn5 this
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim
      · exact Or.inr (Or.inr (Or.inl h))
      · -- `q ≡ 11 (mod 30)`: `n + q ≡ 17 (mod 30)` is fine, but `n - q ≡ 25 (mod 30)`
        -- is divisible by 5.
        have hqlt' : q < n := (mem_Sset_iff.mp hqS).1
        have hnq : (n - q) % 30 = 25 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · have hqlt' : q < n := (mem_Sset_iff.mp hqS).1
        have hnq : (n - q) % 30 = 17 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        -- `n - q ≡ 17` is allowed as a number, but `n + q ≡ 25 (mod 30)` is div by 5.
        have hsum : (n + q) % 30 = 25 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · have hqlt' : q < n := (mem_Sset_iff.mp hqS).1
        have hsum : (n + q) % 30 = 5 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim

/-- Unpaired candidates when `n ≡ 12 (mod 30)`. -/
lemma unpaired_mod_thirty_candidates_n_mod_twelve {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 6 < n) (hn12 : n % 30 = 12) (hq : q ∈ Unpaired n) :
    q = 5 ∨ q = n - 5 ∨ q % 30 = 19 ∨ q % 30 = 29 ∨ q % 30 = 1 ∨ q % 30 = 11 := by
  have hqS : q ∈ Sset n := (mem_Unpaired_iff.mp hq).1
  have hqP : q.Prime := (mem_Sset_iff.mp hqS).2.1
  have h5le : 5 ≤ q := five_le_of_mem_Sset_of_dvd_six h6 hn hqS
  by_cases h5 : q = 5
  · exact Or.inl h5
  · by_cases hn5 : q = n - 5
    · exact Or.inr (Or.inl hn5)
    · have h5lt : 5 < q := by omega
      have : q % 30 = 1 ∨ q % 30 = 7 ∨ q % 30 = 11 ∨ q % 30 = 13 ∨
             q % 30 = 17 ∨ q % 30 = 19 ∨ q % 30 = 23 ∨ q % 30 = 29 :=
        prime_mod_thirty_of_gt_five hqP h5lt
      have hqlt' : q < n := (mem_Sset_iff.mp hqS).1
      rcases this with h | h | h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · -- `q ≡ 7`: `n + q ≡ 19` is fine, but `n - q ≡ 5 (mod 30)` is div by 5
        have hnq : (n - q) % 30 = 5 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : n - q ≠ 5 := by
            intro heq
            have : q = n - 5 := by omega
            exact hn5 this
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · -- `q ≡ 13`: `n - q ≡ 29`, `n + q ≡ 25` div by 5
        have hsum : (n + q) % 30 = 25 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim
      · -- `q ≡ 17`: `n + q ≡ 29`, `n - q ≡ 25` div by 5
        have hnq : (n - q) % 30 = 25 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim
      · exact Or.inr (Or.inr (Or.inl h))
      · -- `q ≡ 23`: `n + q ≡ 5` div by 5
        have hsum : (n + q) % 30 = 5 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- Unpaired candidates when `n ≡ 18 (mod 30)`. -/
lemma unpaired_mod_thirty_candidates_n_mod_eighteen {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 6 < n) (hn18 : n % 30 = 18) (hq : q ∈ Unpaired n) :
    q = 5 ∨ q = n - 5 ∨ q % 30 = 1 ∨ q % 30 = 11 ∨ q % 30 = 19 ∨ q % 30 = 29 := by
  have hqS : q ∈ Sset n := (mem_Unpaired_iff.mp hq).1
  have hqP : q.Prime := (mem_Sset_iff.mp hqS).2.1
  have h5le : 5 ≤ q := five_le_of_mem_Sset_of_dvd_six h6 hn hqS
  by_cases h5 : q = 5
  · exact Or.inl h5
  · by_cases hn5 : q = n - 5
    · exact Or.inr (Or.inl hn5)
    · have h5lt : 5 < q := by omega
      have : q % 30 = 1 ∨ q % 30 = 7 ∨ q % 30 = 11 ∨ q % 30 = 13 ∨
             q % 30 = 17 ∨ q % 30 = 19 ∨ q % 30 = 23 ∨ q % 30 = 29 :=
        prime_mod_thirty_of_gt_five hqP h5lt
      have hqlt' : q < n := (mem_Sset_iff.mp hqS).1
      rcases this with h | h | h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · -- `q ≡ 7`: `n + q ≡ 25` div by 5
        have hsum : (n + q) % 30 = 25 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · -- `q ≡ 13`: `n - q ≡ 5` div by 5 (unless q = n-5)
        have hnq : (n - q) % 30 = 5 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : n - q ≠ 5 := by
            intro heq
            have : q = n - 5 := by omega
            exact hn5 this
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim
      · -- `q ≡ 17`: `n - q ≡ 1`, `n + q ≡ 5` div by 5
        have hsum : (n + q) % 30 = 5 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · -- `q ≡ 23`: `n - q ≡ 25` div by 5
        have hnq : (n - q) % 30 = 25 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- Unpaired candidates when `n ≡ 24 (mod 30)`. -/
lemma unpaired_mod_thirty_candidates_n_mod_twentyfour {n q : ℕ}
    (h6 : 6 ∣ n) (hn : 6 < n) (hn24 : n % 30 = 24) (hq : q ∈ Unpaired n) :
    q = 5 ∨ q = n - 5 ∨ q % 30 = 13 ∨ q % 30 = 23 ∨ q % 30 = 7 ∨ q % 30 = 17 := by
  have hqS : q ∈ Sset n := (mem_Unpaired_iff.mp hq).1
  have hqP : q.Prime := (mem_Sset_iff.mp hqS).2.1
  have h5le : 5 ≤ q := five_le_of_mem_Sset_of_dvd_six h6 hn hqS
  by_cases h5 : q = 5
  · exact Or.inl h5
  · by_cases hn5 : q = n - 5
    · exact Or.inr (Or.inl hn5)
    · have h5lt : 5 < q := by omega
      have : q % 30 = 1 ∨ q % 30 = 7 ∨ q % 30 = 11 ∨ q % 30 = 13 ∨
             q % 30 = 17 ∨ q % 30 = 19 ∨ q % 30 = 23 ∨ q % 30 = 29 :=
        prime_mod_thirty_of_gt_five hqP h5lt
      have hqlt' : q < n := (mem_Sset_iff.mp hqS).1
      rcases this with h | h | h | h | h | h | h | h
      · -- `q ≡ 1`: `n + q ≡ 25` div by 5
        have hsum : (n + q) % 30 = 25 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · -- `q ≡ 11`: `n + q ≡ 5` div by 5
        have hsum : (n + q) % 30 = 5 := by omega
        have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
        have hdvd : 5 ∣ n + q := by
          have : (n + q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n + q := by omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hsumP).elim
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · -- `q ≡ 19`: `n - q ≡ 5` div by 5 (unless q = n-5)
        have hnq : (n - q) % 30 = 5 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : n - q ≠ 5 := by
            intro heq
            have : q = n - 5 := by omega
            exact hn5 this
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · -- `q ≡ 29`: `n - q ≡ 25` div by 5
        have hnq : (n - q) % 30 = 25 := by
          have : (n - q) % 30 = (n % 30 + 30 - q % 30) % 30 := by omega
          omega
        have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
        have hdvd : 5 ∣ n - q := by
          have : (n - q) % 5 = 0 := by omega
          exact Nat.dvd_iff_mod_eq_zero.2 this
        have hgt : 5 < n - q := by
          have : 2 ≤ n - q := hdiffP.two_le
          omega
        exact (not_prime_of_dvd_of_lt hdvd (by decide) hgt hdiffP).elim

/-- In a `(4,0)` configuration every Sset element is one of the two pairing orbits. -/
lemma mem_Sset_of_config40 {n r s q : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hq : q ∈ Sset n) : q = r ∨ q = n - r ∨ q = s ∨ q = n - s := by
  have hS := Sset_eq_four_of_config40 h6 hn hP hU hr hs hrs
  simpa [hS] using hq

/-- A paired representative is strictly less than `n / 2`. -/
lemma pairedRep_mul_two_lt {n r : ℕ} (hr : r ∈ PairedRep n) : 2 * r < n := by
  have hlt := pairedRep_lt_half hr
  have hrn := pairedRep_lt_n hr
  omega

/-- If `q ∈ Sset n` and `2 * q < n` in a `(4,0)` configuration, then `q` is a pairing representative. -/
lemma eq_pairedRep_of_mem_Sset_of_mul_two_lt {n r s q : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hq : q ∈ Sset n) (h2q : 2 * q < n) : q = r ∨ q = s := by
  have hmem := mem_Sset_of_config40 h6 hn hP hU hr hs hrs hq
  have hr2 := pairedRep_mul_two_lt hr
  have hs2 := pairedRep_mul_two_lt hs
  have hrn := pairedRep_lt_n hr
  have hsn := pairedRep_lt_n hs
  rcases hmem with h | h | h | h
  · exact Or.inl h
  · omega
  · exact Or.inr h
  · omega

/-- For `n > 26` in a `(4,0)` configuration, `13 ∈ Sset n` iff `13` is a pairing representative. -/
lemma thirteen_mem_Sset_iff_of_config40 {n r s : ℕ} (h6 : 6 ∣ n) (hn : 26 < n)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s) :
    13 ∈ Sset n ↔ r = 13 ∨ s = 13 := by
  constructor
  · intro h13
    have : 2 * 13 < n := by omega
    have := eq_pairedRep_of_mem_Sset_of_mul_two_lt h6 (by omega) hP hU hr hs hrs h13 this
    rcases this with h | h <;> simp [h]
  · intro h
    have hrS := pairedRep_mem_Sset hr
    have hsS := pairedRep_mem_Sset hs
    rcases h with h | h
    · subst h; exact hrS
    · subst h; exact hsS

lemma twentythree_mem_Sset_iff_of_config40 {n r s : ℕ} (h6 : 6 ∣ n) (hn : 46 < n)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s) :
    23 ∈ Sset n ↔ r = 23 ∨ s = 23 := by
  constructor
  · intro h23
    have : 2 * 23 < n := by omega
    have := eq_pairedRep_of_mem_Sset_of_mul_two_lt h6 (by omega) hP hU hr hs hrs h23 this
    rcases this with h | h <;> simp [h]
  · intro h
    have hrS := pairedRep_mem_Sset hr
    have hsS := pairedRep_mem_Sset hs
    rcases h with h | h
    · subst h; exact hrS
    · subst h; exact hsS

/-- Residues of pairing representatives and their partners when `n ≡ 6 (mod 30)`
and the representatives are not `5`. -/
lemma eight_residues_n_mod_six {n r s : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n)
    (hn6 : n % 30 = 6) (hr5 : r ≠ 5) (hs5 : s ≠ 5) :
    (r % 30 = 13 ∨ r % 30 = 23) ∧ (s % 30 = 13 ∨ s % 30 = 23) ∧
    (n - r) % 30 = (36 - r % 30) % 30 ∧ (n + r) % 30 = (6 + r % 30) % 30 := by
  have hr30 := pairedRep_mod_thirty_of_n_mod_six h6 hn hr hn6 hr5
  have hs30 := pairedRep_mod_thirty_of_n_mod_six h6 hn hs hn6 hs5
  have hrlt := pairedRep_lt_n hr
  refine ⟨hr30, hs30, ?_, ?_⟩
  · have hnr : (n - r) % 30 = (n % 30 + 30 - r % 30) % 30 := by omega
    rw [hnr, hn6]
  · omega

/-- In a `(4,0)` configuration with `n ≡ 6 (mod 30)` and representatives not `5`,
every Sset element is congruent to `13` or `23` modulo `30`. -/
lemma sset_mod_thirty_subset_of_config40_n_mod_six {n r s q : ℕ}
    (h6 : 6 ∣ n) (hn : 10 < n) (hn6 : n % 30 = 6)
    (hP : #(Paired n) = 4) (hU : Unpaired n = ∅)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n) (hrs : r ≠ s)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) (hq : q ∈ Sset n) :
    q % 30 = 13 ∨ q % 30 = 23 :=
  mem_Sset_mod_thirty_of_config40_n_mod_six h6 hn hn6 hP hU hr hs hrs hr5 hs5 hq

/-- The two pairing representatives in a `(4,0)` configuration with `n ≡ 6 (mod 30)`
are each `13` or `23` modulo `30`. -/
lemma reps_mod_thirty_of_config40_n_mod_six {n r s : ℕ}
    (h6 : 6 ∣ n) (hn : 6 < n) (hn6 : n % 30 = 6)
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n)
    (hr5 : r ≠ 5) (hs5 : s ≠ 5) :
    (r % 30 = 13 ∨ r % 30 = 23) ∧ (s % 30 = 13 ∨ s % 30 = 23) :=
  ⟨pairedRep_mod_thirty_of_n_mod_six h6 hn hr hn6 hr5,
   pairedRep_mod_thirty_of_n_mod_six h6 hn hs hn6 hs5⟩

/-- If the two pairing representatives are `13` and `23`, the eight diamond values
are the explicit linear forms in `n` attached to those two primes. -/
lemma eight_primes_of_reps_thirteen_twentythree {n r s : ℕ}
    (hr : r ∈ PairedRep n) (hs : s ∈ PairedRep n)
    (hrs13 : ({r, s} : Finset ℕ) = {13, 23}) :
    (13 : ℕ).Prime ∧ (23 : ℕ).Prime ∧
    (n - 13).Prime ∧ (n - 23).Prime ∧
    (n + 13).Prime ∧ (n + 23).Prime ∧
    (2 * n - 13).Prime ∧ (2 * n - 23).Prime := by
  have h13 : 13 ∈ ({r, s} : Finset ℕ) := by simp [hrs13]
  have h23 : 23 ∈ ({r, s} : Finset ℕ) := by simp [hrs13]
  have hr13or : r = 13 ∨ s = 13 := by
    simp only [mem_insert, mem_singleton] at h13
    exact h13.imp Eq.symm Eq.symm
  have hr23or : r = 23 ∨ s = 23 := by
    simp only [mem_insert, mem_singleton] at h23
    exact h23.imp Eq.symm Eq.symm
  have ⟨hrp, hnrp, hnpr, h2nr, hsp, hnsp, hnsp', h2ns⟩ := eight_primes_of_two_reps hr hs
  rcases hr13or with hr13 | hs13 <;> rcases hr23or with hr23 | hs23
  · have : (13 : ℕ) = 23 := hr13.symm.trans hr23
    exact (by decide : ¬ (13 : ℕ) = 23) this |>.elim
  · subst hr13; subst hs23
    exact ⟨by decide, by decide, hnrp, hnsp, hnpr, hnsp', h2nr, h2ns⟩
  · subst hs13; subst hr23
    exact ⟨by decide, by decide, hnsp, hnrp, hnsp', hnpr, h2ns, h2nr⟩
  · have : (23 : ℕ) = 13 := hs23.symm.trans hs13
    exact (by decide : ¬ (23 : ℕ) = 13) this |>.elim

/-- A pairing representative other than `5` is at least `7`. -/
lemma seven_le_pairedRep_of_ne_five {n r : ℕ} (h6 : 6 ∣ n) (hn : 6 < n)
    (hr : r ∈ PairedRep n) (hr5 : r ≠ 5) : 7 ≤ r := by
  have hS := pairedRep_mem_Sset hr
  have h5le : 5 ≤ r := five_le_of_mem_Sset_of_dvd_six h6 hn hS
  have hrP : r.Prime := (mem_Sset_iff.mp hS).2.1
  have hr2 : r ≠ 2 := by omega
  have hodd : Odd r := hrP.odd_of_ne_two hr2
  have : r ≠ 6 := fun h => by
    subst h
    exact (by decide : ¬ Odd 6) hodd
  omega

/-- If both `5` and `n - 5` lie in `Sset n` then they form a pairing orbit. -/
lemma five_and_nsubfive_paired {n : ℕ} (hn : 10 < n)
    (h5 : 5 ∈ Sset n) (hn5 : n - 5 ∈ Sset n) :
    5 ∈ Paired n ∧ n - 5 ∈ Paired n := by
  have hle : 5 ≤ n := by omega
  refine ⟨mem_Paired_iff.mpr ⟨h5, hn5⟩, mem_Paired_iff.mpr ⟨hn5, ?_⟩⟩
  simpa [Nat.sub_sub_self hle] using h5

/-- In an all-unpaired configuration, at most one of `5` and `n - 5` can lie in `Sset`. -/
lemma not_both_five_of_unpaired_empty_paired {n : ℕ} (hn : 10 < n)
    (hP : Paired n = ∅) : ¬ (5 ∈ Sset n ∧ n - 5 ∈ Sset n) := by
  intro ⟨h5, hn5⟩
  have := five_and_nsubfive_paired hn h5 hn5
  have : 5 ∈ Paired n := this.1
  simp [hP] at this

/-- If `7, 13, 17, 23` all lie in `Sset n` then one of `n ± 7, n ± 13, n ± 17, n ± 23`
is divisible by `7`. For `n > 46` that number exceeds `7`, hence cannot be prime. -/
lemma not_all_seven_thirteen_seventeen_twentythree_mem_Sset {n : ℕ} (hn : 46 < n) :
    ¬ (7 ∈ Sset n ∧ 13 ∈ Sset n ∧ 17 ∈ Sset n ∧ 23 ∈ Sset n) := by
  intro ⟨h7, h13, h17, h23⟩
  have hsum7 : (n + 7).Prime := (mem_Sset_iff.mp h7).2.2.2
  have hsum13 : (n + 13).Prime := (mem_Sset_iff.mp h13).2.2.2
  have hdiff13 : (n - 13).Prime := (mem_Sset_iff.mp h13).2.2.1
  have hsum17 : (n + 17).Prime := (mem_Sset_iff.mp h17).2.2.2
  have hdiff17 : (n - 17).Prime := (mem_Sset_iff.mp h17).2.2.1
  have hsum23 : (n + 23).Prime := (mem_Sset_iff.mp h23).2.2.2
  have hdiff23 : (n - 23).Prime := (mem_Sset_iff.mp h23).2.2.1
  have hmod : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨
      n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by omega
  have hadd (t : ℕ) : (n + t) % 7 = (n % 7 + t % 7) % 7 := Nat.add_mod n t 7
  have hsub (t : ℕ) (ht : t ≤ n) : (n - t) % 7 = (n % 7 + 7 - t % 7) % 7 := by
    have := Nat.mod_add_div n 7
    have := Nat.mod_add_div t 7
    omega
  rcases hmod with h | h | h | h | h | h | h
  · have : (n + 7) % 7 = 0 := by rw [hadd, h]
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) (by decide) (by omega) hsum7
  · have : (n + 13) % 7 = 0 := by rw [hadd, h]
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) (by decide) (by omega) hsum13
  · have : (n - 23) % 7 = 0 := by rw [hsub 23 (by omega), h]
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) (by decide) (by omega) hdiff23
  · have : (n - 17) % 7 = 0 := by rw [hsub 17 (by omega), h]
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) (by decide) (by omega) hdiff17
  · have : (n + 17) % 7 = 0 := by rw [hadd, h]
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) (by decide) (by omega) hsum17
  · have : (n + 23) % 7 = 0 := by rw [hadd, h]
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) (by decide) (by omega) hsum23
  · have : (n - 13) % 7 = 0 := by rw [hsub 13 (by omega), h]
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) (by decide) (by omega) hdiff13


lemma nat_sub_mod_eq_zero_of {n q p : ℕ} (hp : 0 < p) (hle : q ≤ n)
    (hminus : (n % p + p - q % p) % p = 0) :
    (n - q) % p = 0 := by
  have hZ : ((n - q : ℕ) : ℤ) = (n : ℤ) - q := Int.ofNat_sub hle
  have hsub : ((n : ℤ) - q) % p = ((n : ℤ) % p - (q : ℤ) % p) % p := Int.sub_emod _ _ _
  have hnmod : ((n : ℤ) % p) = ↑(n % p) := Int.natCast_mod n p
  have hqmod : ((q : ℤ) % p) = ↑(q % p) := Int.natCast_mod q p
  have haddP : ((n : ℤ) % p - (q : ℤ) % p) % p =
      ((n : ℤ) % p + ↑p - (q : ℤ) % p) % p := by
    have hassoc : ((n : ℤ) % p + ↑p - (q : ℤ) % p) =
        ((n : ℤ) % p - (q : ℤ) % p) + ↑p := by
      simp [Int.sub_eq_add_neg, Int.add_assoc, Int.add_comm]
    rw [hassoc, Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]
  have hle' : q % p ≤ n % p + p := by
    have : q % p < p := Nat.mod_lt _ hp
    omega
  have hminusZ : ((↑(n % p) : ℤ) + ↑p - ↑(q % p)) % p = 0 := by
    have : ((↑(n % p) : ℤ) + ↑p - ↑(q % p)) = ↑(n % p + p - q % p) := by
      rw [Nat.cast_sub hle', Nat.cast_add]
    rw [this]
    exact_mod_cast hminus
  have : ((n : ℤ) - q) % p = 0 := by
    rw [hsub, haddP, hnmod, hqmod]
    exact hminusZ
  have : ((n - q : ℕ) : ℤ) % p = 0 := by rwa [hZ]
  exact_mod_cast this


lemma not_all_mem_Sset_of_mod_cover {n p : ℕ} {qs : Finset ℕ}
    (hp : p.Prime)
    (hn : ∀ q ∈ qs, q + p < n)
    (hcover : ∀ r < p, ∃ q ∈ qs, (r + q) % p = 0 ∨ (r + p - q % p) % p = 0) :
    ¬ qs ⊆ Sset n := by
  intro hsub
  have hppos : 0 < p := hp.pos
  obtain ⟨q, hq, hhit⟩ := hcover (n % p) (Nat.mod_lt n hppos)
  have hqS : q ∈ Sset n := hsub hq
  have hqlt : q < n := (mem_Sset_iff.mp hqS).1
  have hsumP : (n + q).Prime := (mem_Sset_iff.mp hqS).2.2.2
  have hdiffP : (n - q).Prime := (mem_Sset_iff.mp hqS).2.2.1
  rcases hhit with hplus | hminus
  · have : (n + q) % p = 0 := by
      rw [Nat.add_mod, ← Nat.add_mod_mod, Nat.mod_eq_of_lt (Nat.mod_lt n hppos)] at hplus ⊢
      exact hplus
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) hp.two_le
      (by
        have := hn q hq
        omega) hsumP
  · have : (n - q) % p = 0 :=
      nat_sub_mod_eq_zero_of hppos (Nat.le_of_lt hqlt) hminus
    exact not_prime_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.2 this) hp.two_le
      (by
        have := hn q hq
        omega) hdiffP
