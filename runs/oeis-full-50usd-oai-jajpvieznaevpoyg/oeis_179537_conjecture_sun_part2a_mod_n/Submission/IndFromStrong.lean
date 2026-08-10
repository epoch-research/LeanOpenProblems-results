import FormalConjectures.Util.ProblemImports
open Finset Nat Int

def A179537 (n : ℕ) : ℤ :=
  (Finset.range (n + 1)).sum fun k : ℕ =>
    ((choose n k : ℤ) ^ 2) * ((choose (n - k) k : ℤ) ^ 2) * ((-16 : ℤ) ^ k)
def A179537_sum_weighted (n : ℕ) : ℤ :=
  (Finset.range n).sum fun k : ℕ =>
    (((42 : ℤ) * Int.ofNat k + (37 : ℤ)) * ((-1 : ℤ) ^ k) * (A179537 k))

def bterm (n : ℕ) : ℤ := (((42 : ℤ) * Int.ofNat n + 37) * (-1 : ℤ)^n * A179537 n)

lemma sum_weighted_succ (n : ℕ) : A179537_sum_weighted (n+1) = A179537_sum_weighted n + bterm n := by
  simp [A179537_sum_weighted, bterm, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]

example
  (strong : ∀ n : ℕ, 1 ≤ n → ((n:ℤ) * bterm n - A179537_sum_weighted n) ≡ 0 [ZMOD ((n:ℤ)*(n+1))]) :
  ∀ n : ℕ, n ≥ 1 → A179537_sum_weighted n ≡ 0 [ZMOD n] := by
  intro n hn
  induction n using Nat.case_strong_induction_on with
  | hz => omega
  | hi n ih =>
    cases n with
    | zero => norm_num [A179537_sum_weighted, A179537, Int.ModEq]
    | succ m =>
      have hprev : A179537_sum_weighted (m+1) ≡ 0 [ZMOD (m+1:ℤ)] := ih (m+1) (by omega) (by omega)
      have hs := strong (m+1) (by omega)
      rw [Int.modEq_zero_iff_dvd] at hprev hs ⊢
      obtain ⟨u, hu⟩ := hprev
      obtain ⟨v, hv⟩ := hs
      use u + v
      rw [sum_weighted_succ]
      have hN : ((m + 1 : ℕ) : ℤ) ≠ 0 := by omega
      nlinarith [hu, hv]
