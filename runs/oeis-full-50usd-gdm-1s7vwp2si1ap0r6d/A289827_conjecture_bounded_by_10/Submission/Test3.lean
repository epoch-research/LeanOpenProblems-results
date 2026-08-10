import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime
open Finset

lemma coprime_of_prime_factor_le {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k < p) (a : ℕ)
    (ha : ∀ q, q.Prime → q ∣ a → q ≤ k) : Nat.Coprime a p := by
  rw [Nat.coprime_comm]
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  have := ha p hp hdvd
  omega

lemma prime_count_le_coprime_count {n m k a : ℕ} (h_hk : k < n + 1) (ha : ∀ q, q.Prime → q ∣ a → q ≤ k) :
    ((Ico (n + 1) (n + 1 + m)).filter Nat.Prime).card ≤ ((Ico (n + 1) (n + 1 + m)).filter (Nat.Coprime a)).card := by
  apply card_le_card
  intro p hp
  simp only [mem_filter, mem_Ico] at hp ⊢
  refine ⟨hp.1, ?_⟩
  exact coprime_of_prime_factor_le hp.2 (by omega) a ha

lemma card_filter_Ico_eq_range (a b : ℕ) (h : a ≤ b) (p : ℕ → Prop) [DecidablePred p] :
    ((Ico a b).filter p).card = ((range b).filter p).card - ((range a).filter p).card := by
  have h1 : range b = range a ∪ Ico a b := by
    rw [range_eq_Ico]
    exact (Ico_union_Ico_eq_Ico (zero_le a) h).symm
  have h2 : Disjoint (range a) (Ico a b) := by
    rw [range_eq_Ico]
    exact Ico_disjoint_Ico_consecutive 0 a b
  rw [h1, filter_union, card_union_of_disjoint]
  · omega
  · exact disjoint_filter_filter h2

lemma pi_diff_eq_prime_count {n m : ℕ} :
    π (m + n) - π n = ((Ico (n + 1) (n + 1 + m)).filter Nat.Prime).card := by
  have h_lhs : π (m + n) = π' (n + 1 + m) := congr_arg π' (by omega)
  have h_rhs : π n = π' (n + 1) := rfl
  rw [h_lhs, h_rhs]
  have h_le : n + 1 ≤ n + 1 + m := by omega
  have h_card := card_filter_Ico_eq_range (n + 1) (n + 1 + m) h_le Nat.Prime
  have h_def1 : π' (n + 1 + m) = ((range (n + 1 + m)).filter Nat.Prime).card := Nat.count_eq_card_filter_range Nat.Prime (n + 1 + m)
  have h_def2 : π' (n + 1) = ((range (n + 1)).filter Nat.Prime).card := Nat.count_eq_card_filter_range Nat.Prime (n + 1)
  omega

lemma prime_count_diff_le_coprime_count {n m k a : ℕ} (h_hk : k < n + 1) (ha : ∀ q, q.Prime → q ∣ a → q ≤ k) :
    π (m + n) - π n ≤ ((Ico (n + 1) (n + 1 + m)).filter (Nat.Coprime a)).card := by
  rw [pi_diff_eq_prime_count]
  exact prime_count_le_coprime_count h_hk ha

lemma card_coprime_Ico_multiple {a : ℕ} (k : ℕ) (q : ℕ) :
    ((Ico k (k + q * a)).filter (Nat.Coprime a)).card = q * Nat.totient a := by
  induction q with
  | zero =>
    simp
  | succ q ih =>
    have h1 : k + (q + 1) * a = k + q * a + a := by ring
    have h2 : k ≤ k + q * a := by omega
    have h3 : k + q * a ≤ k + q * a + a := by omega
    rw [h1, ← Ico_union_Ico_eq_Ico h2 h3]
    rw [filter_union, card_union_of_disjoint]
    · rw [ih, Nat.filter_coprime_Ico_eq_totient]
      ring
    · exact disjoint_filter_filter (Ico_disjoint_Ico_consecutive k (k + q * a) (k + q * a + a))

lemma card_coprime_Ico_decomposition {a : ℕ} (k : ℕ) (m : ℕ) :
    ((Ico k (k + m)).filter (Nat.Coprime a)).card =
      (m / a) * Nat.totient a + ((Ico (k + (m / a) * a) (k + m)).filter (Nat.Coprime a)).card := by
  have h2 : k + (m / a) * a ≤ k + m := by
    have : (m / a) * a ≤ m := Nat.div_mul_le_self m a
    omega
  have h3 : k ≤ k + (m / a) * a := by omega
  rw [← Ico_union_Ico_eq_Ico h3 h2]
  rw [filter_union, card_union_of_disjoint]
  · rw [card_coprime_Ico_multiple]
  · exact disjoint_filter_filter (Ico_disjoint_Ico_consecutive k (k + (m / a) * a) (k + m))


lemma card_filter_Ico_le {a b : ℕ} (p : ℕ → Prop) [DecidablePred p] :
    ((Ico a b).filter p).card ≤ b - a := by
  have h := card_le_card (filter_subset p (Ico a b))
  rw [Nat.card_Ico] at h
  exact h


lemma coprime_count_le_bound {a : ℕ} (k : ℕ) (m : ℕ) :
    ((Ico k (k + m)).filter (Nat.Coprime a)).card ≤ (m / a) * Nat.totient a + m % a := by
  rw [card_coprime_Ico_decomposition]
  have h_le := card_filter_Ico_le (Nat.Coprime a) (a := k + (m / a) * a) (b := k + m)
  have h_eq : k + m - (k + (m / a) * a) = m % a := by
    have h_div : (m / a) * a + m % a = m := by
      rw [mul_comm]
      exact Nat.div_add_mod m a
    omega
  rw [h_eq] at h_le
  omega


lemma prime_count_diff_le_bound {n m k a : ℕ} (h_hk : k < n + 1) (ha : ∀ q, q.Prime → q ∣ a → q ≤ k) :
    π (m + n) - π n ≤ (m / a) * Nat.totient a + m % a := by
  have h1 := prime_count_diff_le_coprime_count h_hk ha (m := m)
  have h2 := coprime_count_le_bound (a := a) (n + 1) m
  omega



lemma prime_dvd_prime {q p : ℕ} (hq : q.Prime) (hp : p.Prime) (h : q ∣ p) : q = p := by
  have := hp.eq_one_or_self_of_dvd q h
  rcases this with h1 | h2
  · subst h1
    exact False.elim (Nat.Prime.ne_one hq rfl)
  · exact h2

lemma prime_factors_le_of_primorial_6 : ∀ q, q.Prime → q ∣ 6 → q ≤ 3 := by
  intro q hp hdvd
  have : q ≤ 6 := Nat.le_of_dvd (by decide) hdvd
  interval_cases q <;> (try decide) <;> (first | revert hp; decide | revert hdvd; decide)

lemma prime_factors_le_of_primorial_30 : ∀ q, q.Prime → q ∣ 30 → q ≤ 5 := by
  intro q hq hdvd
  have h_dvd_mul : q ∣ 6 * 5 := hdvd
  rw [hq.dvd_mul] at h_dvd_mul
  rcases h_dvd_mul with h1 | h2
  · have : q ≤ 3 := prime_factors_le_of_primorial_6 q hq h1
    omega
  · have : q = 5 := prime_dvd_prime hq (by decide) h2
    omega


lemma prime_factors_le_of_primorial_210 : ∀ q, q.Prime → q ∣ 210 → q ≤ 7 := by
  intro q hq hdvd
  have h_dvd_mul : q ∣ 30 * 7 := hdvd
  rw [hq.dvd_mul] at h_dvd_mul
  rcases h_dvd_mul with h1 | h2
  · have : q ≤ 5 := prime_factors_le_of_primorial_30 q hq h1
    omega
  · have : q = 7 := prime_dvd_prime hq (by decide) h2
    omega

lemma prime_factors_le_of_primorial_2310 : ∀ q, q.Prime → q ∣ 2310 → q ≤ 11 := by
  intro q hq hdvd
  have h_dvd_mul : q ∣ 210 * 11 := hdvd
  rw [hq.dvd_mul] at h_dvd_mul
  rcases h_dvd_mul with h1 | h2
  · have : q ≤ 7 := prime_factors_le_of_primorial_210 q hq h1
    omega
  · have : q = 11 := prime_dvd_prime hq (by decide) h2
    omega

lemma prime_factors_le_of_primorial_30030 : ∀ q, q.Prime → q ∣ 30030 → q ≤ 13 := by
  intro q hq hdvd
  have h_dvd_mul : q ∣ 2310 * 13 := hdvd
  rw [hq.dvd_mul] at h_dvd_mul
  rcases h_dvd_mul with h1 | h2
  · have : q ≤ 11 := prime_factors_le_of_primorial_2310 q hq h1
    omega
  · have : q = 13 := prime_dvd_prime hq (by decide) h2
    omega

lemma prime_factors_le_of_primorial_510510 : ∀ q, q.Prime → q ∣ 510510 → q ≤ 17 := by
  intro q hq hdvd
  have h_dvd_mul : q ∣ 30030 * 17 := hdvd
  rw [hq.dvd_mul] at h_dvd_mul
  rcases h_dvd_mul with h1 | h2
  · have : q ≤ 13 := prime_factors_le_of_primorial_30030 q hq h1
    omega
  · have : q = 17 := prime_dvd_prime hq (by decide) h2
    omega

lemma prime_factors_le_of_primorial_9699690 : ∀ q, q.Prime → q ∣ 9699690 → q ≤ 19 := by
  intro q hq hdvd
  have h_dvd_mul : q ∣ 510510 * 19 := hdvd
  rw [hq.dvd_mul] at h_dvd_mul
  rcases h_dvd_mul with h1 | h2
  · have : q ≤ 17 := prime_factors_le_of_primorial_510510 q hq h1
    omega
  · have : q = 19 := prime_dvd_prime hq (by decide) h2
    omega

#check Nat.primeCounting'_add_le


def precompute_pi : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
    let l := precompute_pi n
    let next_val := l.head! + (if (n + 1).Prime then 1 else 0)
    next_val :: l

lemma check_all_pairs_true (N : ℕ) (h : check_all_pairs N = true) :
    ∀ n, n ≤ N → ∀ m, 10 < m → m ≤ n → π (m + n) ≠ π m + π n := by
  intro n hn m hm h_le
  have h_n_mem : n ∈ List.range (N + 1) := by
    rw [List.mem_range]
    omega
  have h_n_all := List.all_eq_true.1 h n h_n_mem
  have h_m_mem : m ∈ (List.range (n + 1)).filter (fun m => 10 < m) := by
    rw [List.mem_filter]
    refine ⟨?_, decide_eq_true hm⟩
    rw [List.mem_range]
    omega
  have h_all := List.all_eq_true.1 h_n_all m h_m_mem
  exact of_decide_eq_true h_all


def check_all_pairs_range (low high : ℕ) : Bool :=
  ((List.range (high + 1)).filter (fun n => low ≤ n)).all fun n =>
    ((List.range (n + 1)).filter (fun m => 10 < m)).all fun m =>
      decide (π (m + n) ≠ π m + π n)

lemma check_all_pairs_range_true (low high : ℕ) (h : check_all_pairs_range low high = true) :
    ∀ n, low ≤ n ∧ n ≤ high → ∀ m, 10 < m → m ≤ n → π (m + n) ≠ π m + π n := by
  intro n hn m hm h_le
  have h_n_mem : n ∈ (List.range (high + 1)).filter (fun n => low ≤ n) := by
    rw [List.mem_filter]
    refine ⟨?_, decide_eq_true hn.1⟩
    rw [List.mem_range]
    omega
  have h_n_all := List.all_eq_true.1 h n h_n_mem
  have h_m_mem : m ∈ (List.range (n + 1)).filter (fun m => 10 < m) := by
    rw [List.mem_filter]
    refine ⟨?_, decide_eq_true hm⟩
    rw [List.mem_range]
    omega
  have h_all := List.all_eq_true.1 h_n_all m h_m_mem
  exact of_decide_eq_true h_all



set_option maxRecDepth 500000

set_option maxHeartbeats 0


lemma forall_not_101_to_200 :
    ∀ n, 101 ≤ n ∧ n ≤ 200 → ∀ m, 10 < m → m ≤ n → π (m + n) ≠ π m + π n := by
  apply check_all_pairs_range_true 101 200 (by decide)


lemma forall_not_up_to_100 :
    ∀ n, n ≤ 100 → ∀ m, 10 < m → m ≤ n → π (m + n) ≠ π m + π n := by
  apply check_all_pairs_true 100 (by decide)





