import FormalConjectures.Util.ProblemImports

open scoped Nat.Prime

open Finset

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

lemma pi_12_add_lt {n : ℕ} (hn : 12 ≤ n) : π (12 + n) < π 12 + π n := by
  have h_a : 6 < n + 1 := by omega
  have h_cop : #{p ∈ Ico (n + 1) (n + 1 + 12) | p.Prime} ≤ ((Ico (n + 1) (n + 1 + 12)).filter (Nat.Coprime 6)).card := by
    apply card_le_card
    intro p hp
    simp only [mem_filter, mem_Ico] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rw [Nat.coprime_comm]
    exact Nat.coprime_of_lt_prime (by decide) (by omega) hp.2
  have h_dec := card_coprime_Ico_decomposition (a := 6) (n + 1) 12
  have h_div : 12 / 6 = 2 := rfl
  have h_eq : n + 1 + (12 / 6) * 6 = n + 1 + 12 := by omega
  rw [h_div, h_eq] at h_dec
  simp only [Ico_self, filter_empty, card_empty, add_zero] at h_dec
  have h_tot : Nat.totient 6 = 2 := rfl
  rw [h_tot] at h_dec
  have h_count : ((Ico (n + 1) (n + 1 + 12)).filter (Nat.Coprime 6)).card = 4 := by omega
  rw [h_count] at h_cop
  have h_lhs : π (12 + n) = π' (n + 1 + 12) := congr_arg π' (by omega)
  have h_rhs : π n = π' (n + 1) := rfl
  have h_pi12 : π 12 = 5 := by decide
  have h_prime_count : #{p ∈ Ico (n + 1) (n + 1 + 12) | p.Prime} = π' (n + 1 + 12) - π' (n + 1) := by
    have h_le : n + 1 ≤ n + 1 + 12 := by omega
    have h_card := card_filter_Ico_eq_range (n + 1) (n + 1 + 12) h_le Nat.Prime
    -- since π' x = ((range x).filter Nat.Prime).card by definition
    -- we can just change the terms using rfl
    have h_def1 : π' (n + 1 + 12) = ((range (n + 1 + 12)).filter Nat.Prime).card := Nat.count_eq_card_filter_range Nat.Prime (n + 1 + 12)
    have h_def2 : π' (n + 1) = ((range (n + 1)).filter Nat.Prime).card := Nat.count_eq_card_filter_range Nat.Prime (n + 1)
    have h_def3 : #{p ∈ Ico (n + 1) (n + 1 + 12) | p.Prime} = ((Ico (n + 1) (n + 1 + 12)).filter Nat.Prime).card := rfl
    omega
  omega








lemma pi_11_add_lt {n : ℕ} (hn : 11 ≤ n) : π (11 + n) < π 11 + π n := by
  have h_a : 6 < n + 1 := by omega
  have h_cop : #{p ∈ Ico (n + 1) (n + 1 + 11) | p.Prime} ≤ ((Ico (n + 1) (n + 1 + 11)).filter (Nat.Coprime 6)).card := by
    apply card_le_card
    intro p hp
    simp only [mem_filter, mem_Ico] at hp ⊢
    refine ⟨hp.1, ?_⟩
    rw [Nat.coprime_comm]
    exact Nat.coprime_of_lt_prime (by decide) (by omega) hp.2
  have h_dec := card_coprime_Ico_decomposition (a := 6) (n + 1) 11
  have h_div : 11 / 6 = 1 := rfl
  have h_eq : n + 1 + (11 / 6) * 6 = n + 7 := by omega
  rw [h_div, h_eq] at h_dec
  have h_le_rem : ((Ico (n + 7) (n + 1 + 11)).filter (Nat.Coprime 6)).card ≤ 2 := by
    have h_len : n + 1 + 11 = n + 7 + 5 := by omega
    rw [h_len]
    have h0 : 6 ≠ 0 := by decide
    have h_le := Nat.Ico_filter_coprime_le (n + 7) 5 h0
    have h_tot : Nat.totient 6 = 2 := rfl
    have h_div2 : 5 / 6 = 0 := rfl
    rw [h_tot, h_div2] at h_le
    omega
  have h_tot : Nat.totient 6 = 2 := rfl
  rw [h_tot] at h_dec
  have h_count : ((Ico (n + 1) (n + 1 + 11)).filter (Nat.Coprime 6)).card ≤ 4 := by omega
  have h_lhs : π (11 + n) = π' (n + 1 + 11) := congr_arg π' (by omega)
  have h_rhs : π n = π' (n + 1) := rfl
  have h_pi11 : π 11 = 5 := by decide
  have h_prime_count : #{p ∈ Ico (n + 1) (n + 1 + 11) | p.Prime} = π' (n + 1 + 11) - π' (n + 1) := by
    have h_le : n + 1 ≤ n + 1 + 11 := by omega
    have h_card := card_filter_Ico_eq_range (n + 1) (n + 1 + 11) h_le Nat.Prime
    have h_def1 : π' (n + 1 + 11) = ((range (n + 1 + 11)).filter Nat.Prime).card := Nat.count_eq_card_filter_range Nat.Prime (n + 1 + 11)
    have h_def2 : π' (n + 1) = ((range (n + 1)).filter Nat.Prime).card := Nat.count_eq_card_filter_range Nat.Prime (n + 1)
    have h_def3 : #{p ∈ Ico (n + 1) (n + 1 + 11) | p.Prime} = ((Ico (n + 1) (n + 1 + 11)).filter Nat.Prime).card := rfl
    omega
  omega

