import Mathlib

open Nat

def fast_totient_aux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | k + 1, acc => fast_totient_aux n k (acc + (if n.Coprime (k + 1) then 1 else 0))

lemma fast_totient_aux_add (n k : ℕ) (acc : ℕ) :
  fast_totient_aux n k acc = acc + fast_totient_aux n k 0 := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
    rw [fast_totient_aux]
    rw [ih (acc + if n.Coprime (k + 1) then 1 else 0)]
    have h1 : fast_totient_aux n (k + 1) 0 = fast_totient_aux n k (if n.Coprime (k + 1) then 1 else 0) := by
      rw [fast_totient_aux, zero_add]
    rw [h1, ih (if n.Coprime (k + 1) then 1 else 0)]
    omega

lemma fast_totient_aux_eq_card (n k : ℕ) :
  fast_totient_aux n k 0 + (if n.Coprime 0 then 1 else 0) = (Finset.filter n.Coprime (Finset.range (k + 1))).card := by
  induction k with
  | zero =>
    simp only [fast_totient_aux]
    have h_range : Finset.range 1 = {0} := rfl
    rw [h_range, Finset.filter_singleton]
    split_ifs with h
    · simp only [Finset.card_singleton]
    · simp only [Finset.card_empty]
  | succ k ih =>
    rw [fast_totient_aux, fast_totient_aux_add]
    rw [Finset.range_succ, Finset.filter_insert]
    by_cases h_coprime : n.Coprime (k + 1)
    · have h_if : (if n.Coprime (k + 1) then insert (k + 1) (Finset.filter n.Coprime (Finset.range (k + 1))) else Finset.filter n.Coprime (Finset.range (k + 1))) = insert (k + 1) (Finset.filter n.Coprime (Finset.range (k + 1))) := if_pos h_coprime
      rw [h_if]
      rw [Finset.card_insert_of_notMem]
      · rw [← ih]
        split_ifs <;> omega
      · intro h_mem
        rw [Finset.mem_filter] at h_mem
        rw [Finset.mem_range] at h_mem
        omega
    · have h_if : (if n.Coprime (k + 1) then insert (k + 1) (Finset.filter n.Coprime (Finset.range (k + 1))) else Finset.filter n.Coprime (Finset.range (k + 1))) = Finset.filter n.Coprime (Finset.range (k + 1)) := if_neg h_coprime
      rw [h_if]
      rw [← ih]
      split_ifs <;> omega

def fast_totient (n : ℕ) : ℕ := fast_totient_aux n n 0

lemma fast_totient_eq_totient (n : ℕ) : fast_totient n = Nat.totient n := by
  rcases n with _ | _ | n
  · rfl
  · rfl
  · have h_not_coprime_zero : ¬ (n + 2).Coprime 0 := by
      intro h
      rw [Nat.coprime_zero_right] at h
      omega
    have h_not_coprime_self : ¬ (n + 2).Coprime (n + 2) := by
      intro h
      unfold Coprime at h
      rw [gcd_self] at h
      omega
    have h_eq := fast_totient_aux_eq_card (n + 2) (n + 2)
    rw [if_neg h_not_coprime_zero] at h_eq
    rw [add_zero] at h_eq
    unfold fast_totient
    rw [h_eq]
    have h_range : Finset.range (n + 3) = insert (n + 2) (Finset.range (n + 2)) := Finset.range_succ
    rw [h_range, Finset.filter_insert, if_neg h_not_coprime_self]
    rfl
