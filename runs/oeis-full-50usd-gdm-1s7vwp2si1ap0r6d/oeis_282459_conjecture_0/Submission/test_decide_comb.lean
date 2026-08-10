import FormalConjectures.Util.ProblemImports

open Nat

def certificate_0 : ℕ → ℕ
  | 53 => 1
  | 54 => 2
  | _ => 1

def certificate_1 : ℕ → ℕ
  | 153 => 1
  | 154 => 2
  | _ => 1

def certificate_2 : ℕ → ℕ
  | 253 => 1
  | 254 => 2
  | _ => 1

def certificate (n : ℕ) : ℕ :=
  if n < 153 then certificate_0 n
  else if n < 253 then certificate_1 n
  else certificate_2 n

lemma cert_valid_0 : ∀ n ∈ Finset.Ico 53 153, certificate_0 n > 0 := by
  decide

lemma cert_valid_1 : ∀ n ∈ Finset.Ico 153 253, certificate_1 n > 0 := by
  decide

lemma cert_valid_2 : ∀ n ∈ Finset.Ico 253 353, certificate_2 n > 0 := by
  decide

lemma cert_valid : ∀ n ∈ Finset.Ico 53 353, certificate n > 0 := by
  intro n hn
  rw [Finset.mem_Ico] at hn
  rcases lt_or_ge n 153 with h0 | h0
  · have h_in : n ∈ Finset.Ico 53 153 := by
      rw [Finset.mem_Ico]
      omega
    have h_cert := cert_valid_0 n h_in
    have h_eq : certificate n = certificate_0 n := by
      unfold certificate
      split_ifs <;> try omega
      rfl
    rw [h_eq]
    exact h_cert
  rcases lt_or_ge n 253 with h1 | h1
  · have h_in : n ∈ Finset.Ico 153 253 := by
      rw [Finset.mem_Ico]
      omega
    have h_cert := cert_valid_1 n h_in
    have h_eq : certificate n = certificate_1 n := by
      unfold certificate
      split_ifs <;> try omega
      rfl
    rw [h_eq]
    exact h_cert
  · have h_in : n ∈ Finset.Ico 253 353 := by
      rw [Finset.mem_Ico]
      omega
    have h_cert := cert_valid_2 n h_in
    have h_eq : certificate n = certificate_2 n := by
      unfold certificate
      split_ifs <;> try omega
      rfl
    rw [h_eq]
    exact h_cert
