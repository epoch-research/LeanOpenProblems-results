import FormalConjectures.Util.ProblemImports
open Finset Nat Set
noncomputable def tau (n : ℕ) : ℕ := (Nat.divisors n).card
noncomputable def A047983_count (m : ℕ) : ℕ :=
  let tau_m := tau m
  Finset.card ((Finset.Ico 1 m).filter (fun k : ℕ => tau k = tau_m))
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | A047983_count m = n}

lemma tau_prime {p : ℕ} (hp : Nat.Prime p) : tau p = 2 := by
  unfold tau
  rw [hp.divisors]
  rw [Finset.card_pair]
  exact hp.ne_one.symm

lemma prime_of_tau_eq_two {n : ℕ} (hnpos : 0 < n) (ht : tau n = 2) : Nat.Prime n := by
  by_cases hn2 : 2 ≤ n
  · by_contra hnp
    rcases Nat.exists_dvd_of_not_prime hn2 hnp with ⟨m, hmn, hm1, hmnne⟩
    have hsub : ({1, m, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Nat.mem_divisors]
      rcases hx with rfl | rfl | rfl
      · exact ⟨one_dvd n, Nat.pos_iff_ne_zero.mp hnpos⟩
      · exact ⟨hmn, Nat.pos_iff_ne_zero.mp hnpos⟩
      · exact ⟨dvd_rfl, Nat.pos_iff_ne_zero.mp hnpos⟩
    have hcardle := Finset.card_le_card hsub
    have hcard3 : ({1, m, n} : Finset ℕ).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simpa using hmnne
      · simp [hm1]
        omega
    unfold tau at ht
    omega
  · have : n = 1 := by omega
    subst n
    unfold tau at ht
    rw [Nat.divisors_one] at ht
    simp at ht

lemma tau_eq_two_iff_prime {n : ℕ} (hnpos : 0 < n) : tau n = 2 ↔ Nat.Prime n := by
  constructor
  · exact prime_of_tau_eq_two hnpos
  · exact tau_prime

lemma A_count_prime {p : ℕ} (hp : Nat.Prime p) : A047983_count p = Nat.primeCounting' p := by
  unfold A047983_count
  rw [tau_prime hp]
  unfold Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_bij (fun k _ => k)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hk ⊢
    exact ⟨hk.1.2, (tau_eq_two_iff_prime hk.1.1).mp hk.2⟩
  · intro a _ b _ h; exact h
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hk ⊢
    exact ⟨k, ⟨⟨hk.2.one_le, hk.1⟩, tau_prime hk.2⟩, rfl⟩

lemma tau_mul_prime_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    tau (p * q) = 4 := by
  unfold tau
  rw [Nat.card_divisors (mul_ne_zero hp.ne_zero hq.ne_zero)]
  have hpf : (p * q).primeFactors = ({p, q} : Finset ℕ) := by
    ext r
    simp only [Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hrp, hdvd, _⟩
      rcases hrp.dvd_or_dvd hdvd with h | h
      · left; exact ((hp.dvd_iff_eq hrp.ne_one).mp h).symm
      · right; exact ((hq.dvd_iff_eq hrp.ne_one).mp h).symm
    · intro h
      rcases h with hr | hr
      · subst r; exact ⟨hp, dvd_mul_right p q, mul_ne_zero hp.ne_zero hq.ne_zero⟩
      · subst r; exact ⟨hq, dvd_mul_left q p, mul_ne_zero hp.ne_zero hq.ne_zero⟩
  rw [hpf]
  rw [Nat.factorization_mul hp.ne_zero hq.ne_zero]
  have hqp0 : q.factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    exact hpq ((hq.dvd_iff_eq hp.ne_one).mp hd).symm
  have hpq0 : p.factorization q = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    exact hpq ((hp.dvd_iff_eq hq.ne_one).mp hd)
  simp [Finset.prod_insert, hpq, hpq.symm, hp.factorization_self, hq.factorization_self, hqp0, hpq0]


lemma count_Q_eq_card (p : ℕ) :
    Nat.count (fun k : ℕ => 1 ≤ k ∧ tau k = 4) p =
      ((Finset.Ico 1 p).filter (fun k => tau k = 4)).card := by
  change Nat.count (fun k : ℕ => 1 ≤ k ∧ tau k = 4) p =
      ((Finset.Ico 1 p).filter (fun k => tau k = 4)).card
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_bij (fun k _ => k)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hk ⊢
    exact ⟨⟨hk.2.1, hk.1⟩, hk.2.2⟩
  · intro a _ b _ h; exact h
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hk ⊢
    exact ⟨k, ⟨hk.1.2, hk.1.1, hk.2⟩, rfl⟩

/-- If more than `π'(p)` positive integers below `p` have τ=4, then the first occurrence for
`π'(p)` is below `p`. -/
lemma exists_count_eq_of_many_tau4 {p : ℕ}
    (hmany : Nat.primeCounting' p < ((Finset.Ico 1 p).filter (fun k => tau k = 4)).card) :
    ∃ m < p, A047983_count m = Nat.primeCounting' p := by
  classical
  let Q : ℕ → Prop := fun k => 1 ≤ k ∧ tau k = 4
  have hcountp : Nat.count Q p = ((Finset.Ico 1 p).filter (fun k => tau k = 4)).card := by
    simpa [Q] using count_Q_eq_card p
  have hltcount : Nat.primeCounting' p < Nat.count Q p := by simpa [hcountp] using hmany
  let m := Nat.nth Q (Nat.primeCounting' p)
  have hm_lt : m < p := Nat.nth_lt_of_lt_count (p := Q) hltcount
  have hcond : ∀ hf : {n | Q n}.Finite, Nat.primeCounting' p < #hf.toFinset := by
    intro hf
    exact hltcount.trans_le (Nat.count_le_card hf p)
  have hQm : Q m := Nat.nth_mem (p := Q) (Nat.primeCounting' p) hcond
  have hcountm : Nat.count Q m = Nat.primeCounting' p := Nat.count_nth hcond
  refine ⟨m, hm_lt, ?_⟩
  unfold A047983_count
  have htau_m : tau m = 4 := hQm.2
  rw [htau_m]
  rw [← hcountm]
  exact (count_Q_eq_card m).symm
