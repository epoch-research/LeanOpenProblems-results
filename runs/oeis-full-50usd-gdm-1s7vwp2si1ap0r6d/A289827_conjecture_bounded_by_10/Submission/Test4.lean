import FormalConjectures.Util.ProblemImports

open Nat
open scoped Nat.Prime
open Finset

lemma coprime_of_prime_factor_le {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k < p) (a : ℕ)
    (ha : ∀ q, q.Prime → q ∣ a → q ≤ k) : Coprime a p := by
  rw [coprime_comm]
  rw [hp.coprime_iff_not_dvd]
  intro hdvd
  have := ha p hp hdvd
  omega

lemma prime_count_le_coprime_count {n m k a : ℕ} (h_hk : k < n + 1) (ha : ∀ q, q.Prime → q ∣ a → q ≤ k) :
    ((Ico (n + 1) (n + 1 + m)).filter Nat.Prime).card ≤ ((Ico (n + 1) (n + 1 + m)).filter (Coprime a)).card := by
  apply card_le_card
  intro p hp
  simp only [mem_filter, mem_Ico] at hp ⊢
  refine ⟨hp.1, ?_⟩
  exact coprime_of_prime_factor_le hp.2 (by omega) a ha

lemma card_filter_Ico_eq_range (a b : ℕ) (h : a ≤ b) (p : ℕ → Prop) [DecidablePred p] :
    ((Ico a b).filter p).card = ((range b).filter p).card - ((range a).filter p).card := by
  have h1 : range b = range a ∪ Ico a b := by
    rw [range_eq_Ico]
    exact (Ico_union_Ico_eq_Ico (Nat.zero_le a) h).symm
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
    π (m + n) - π n ≤ ((Ico (n + 1) (n + 1 + m)).filter (Coprime a)).card := by
  rw [pi_diff_eq_prime_count]
  exact prime_count_le_coprime_count h_hk ha

lemma card_coprime_Ico_multiple {a : ℕ} (k : ℕ) (q : ℕ) :
    ((Ico k (k + q * a)).filter (Coprime a)).card = q * totient a := by
  induction q with
  | zero =>
    simp
  | succ q ih =>
    have h1 : k + (q + 1) * a = k + q * a + a := by ring
    have h2 : k ≤ k + q * a := by omega
    have h3 : k + q * a ≤ k + q * a + a := by omega
    rw [h1, ← Ico_union_Ico_eq_Ico h2 h3]
    rw [filter_union, card_union_of_disjoint]
    · rw [ih, filter_coprime_Ico_eq_totient]
      ring
    · exact disjoint_filter_filter (Ico_disjoint_Ico_consecutive k (k + q * a) (k + q * a + a))

lemma card_coprime_Ico_decomposition {a : ℕ} (k : ℕ) (m : ℕ) :
    ((Ico k (k + m)).filter (Coprime a)).card =
      (m / a) * totient a + ((Ico (k + (m / a) * a) (k + m)).filter (Coprime a)).card := by
  have h2 : k + (m / a) * a ≤ k + m := by
    have : (m / a) * a ≤ m := div_mul_le_self m a
    omega
  have h3 : k ≤ k + (m / a) * a := by omega
  rw [← Ico_union_Ico_eq_Ico h3 h2]
  rw [filter_union, card_union_of_disjoint]
  · rw [card_coprime_Ico_multiple]
  · exact disjoint_filter_filter (Ico_disjoint_Ico_consecutive k (k + (m / a) * a) (k + m))

lemma coprime_count_le_nested_bound {a b : ℕ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : b ∣ a) (k : ℕ) (m : ℕ) :
    ((Ico k (k + m)).filter (Coprime a)).card ≤ (m / a) * totient a + ((m % a) / b + 1) * totient b := by
  rw [card_coprime_Ico_decomposition]
  have h_eq_len : k + m = k + (m / a) * a + m % a := by
    have : (m / a) * a + m % a = m := by
      rw [mul_comm]
      exact div_add_mod m a
    omega
  have h_goal_eq : ((Ico (k + (m / a) * a) (k + m)).filter (Coprime a)).card =
                    ((Ico (k + (m / a) * a) (k + (m / a) * a + m % a)).filter (Coprime a)).card := by
    rw [h_eq_len]
  rw [h_goal_eq]
  have h_sub : (Ico (k + (m / a) * a) (k + (m / a) * a + m % a)).filter (Coprime a) ⊆
               (Ico (k + (m / a) * a) (k + (m / a) * a + m % a)).filter (Coprime b) := by
    intro x hx
    simp only [mem_filter, mem_Ico] at hx ⊢
    refine ⟨hx.1, ?_⟩
    have h_cop : Coprime a x := hx.2
    have h_cop_b := Coprime.of_dvd_left hab h_cop
    rw [coprime_comm] at h_cop_b ⊢
    exact h_cop_b
  have h_sub_comm : (Ico (k + a * (m / a)) (k + a * (m / a) + m % a)).filter (Coprime a) ⊆
                    (Ico (k + a * (m / a)) (k + a * (m / a) + m % a)).filter (Coprime b) := by
    have h_comm' : (m / a) * a = a * (m / a) := mul_comm (m / a) a
    rw [← h_comm']
    exact h_sub
  have h_ico := Ico_filter_coprime_le (a := b) (k + (m / a) * a) (m % a) hb0
  have h_ico_comm : ((Ico (k + a * (m / a)) (k + a * (m / a) + m % a)).filter (Coprime b)).card ≤ (m % a / b + 1) * totient b := by
    have h_comm' : (m / a) * a = a * (m / a) := mul_comm (m / a) a
    rw [← h_comm']
    rw [mul_comm (m % a / b + 1) (totient b)]
    exact h_ico
  have h_le_card := card_le_card h_sub_comm
  have h_comm' : (m / a) * a = a * (m / a) := mul_comm (m / a) a
  rw [h_comm']
  clear h_eq_len h_goal_eq h_sub h_sub_comm h_ico h_comm'
  omega

lemma pi_add_lt_of_nested_coprime_bound {m a b : ℕ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : b ∣ a)
    (ha_prime : ∀ q, q.Prime → q ∣ a → q ≤ m)
    (h_bound : (m / a) * totient a + ((m % a) / b + 1) * totient b < π m)
    {n : ℕ} (hn : m ≤ n) : π (m + n) < π m + π n := by
  have h_le : π n ≤ π (m + n) := monotone_primeCounting (Nat.le_add_left n m)
  have h_hk : m < n + 1 := by omega
  have h_diff := prime_count_diff_le_coprime_count (m := m) h_hk ha_prime
  have h_nested := coprime_count_le_nested_bound ha0 hb0 hab (n + 1) m
  omega
