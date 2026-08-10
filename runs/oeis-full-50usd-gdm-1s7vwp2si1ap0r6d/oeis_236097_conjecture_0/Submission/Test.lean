import FormalConjectures.Util.ProblemImports

open Nat Finset
open scoped Nat.Prime

noncomputable def A236097 (n : ℕ) : ℕ :=
  (Icc 1 (n - 3)).sum fun k =>
    let p_val := k.totient + (n - k).totient / 2 + 1
    let p_prime := Nat.nth Nat.Prime (p_val - 1)
    if p_val.Prime ∧ (p_prime - p_val - 1).Prime ∧ (p_prime - p_val + 1).Prime then 1
    else 0

theorem A236097_32_pos : A236097 32 > 0 := by
  unfold A236097
  have h1 : 1 ∈ Icc 1 (32 - 3) := by
    simp
  have h2 : 0 < (fun k =>
    let p_val := k.totient + (32 - k).totient / 2 + 1
    let p_prime := Nat.nth Nat.Prime (p_val - 1)
    if p_val.Prime ∧ (p_prime - p_val - 1).Prime ∧ (p_prime - p_val + 1).Prime then 1
    else 0) 1 := by
    -- We need to evaluate the term at 1.
    -- Since k=1, p_val = 1.totient + 31.totient / 2 + 1 = 1 + 30 / 2 + 1 = 17.
    -- p_val - 1 = 16.
    -- p_prime = Nat.nth Nat.Prime 16.
    -- In Mathlib, the 17th prime (index 16) is 59.
    -- Let's see if we can prove this.
    sorry
  have h3 := Finset.single_le_sum (f := fun k =>
    let p_val := k.totient + (32 - k).totient / 2 + 1
    let p_prime := Nat.nth Nat.Prime (p_val - 1)
    if p_val.Prime ∧ (p_prime - p_val - 1).Prime ∧ (p_prime - p_val + 1).Prime then 1
    else 0) (fun i _ => Nat.zero_le _) h1
  exact h2.trans_le h3



