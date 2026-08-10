import FormalConjectures.Util.ProblemImports

open Nat Finset

example (a b : ℕ) : 2 ^ a * 3 ^ b ∈ Nat.smoothNumbers 4 := by
  have h1 : (1:ℕ) ∈ Nat.smoothNumbers 2 := Nat.mem_smoothNumbers_of_lt (by norm_num) (by norm_num)
  have h2 : 2 ^ a * 1 ∈ Nat.smoothNumbers 3 := by
    exact Nat.pow_mul_mem_smoothNumbers (by norm_num : (2:ℕ) ≠ 0) a h1
  have h3 : 3 ^ b * (2 ^ a * 1) ∈ Nat.smoothNumbers 4 := by
    exact Nat.pow_mul_mem_smoothNumbers (by norm_num : (3:ℕ) ≠ 0) b h2
  simpa [mul_assoc, mul_comm, mul_left_comm] using h3

example {m : ℕ} (hm : m ∈ Nat.smoothNumbers 4) : ∃ a b : ℕ, m = 2 ^ a * 3 ^ b := by
  let e3 := Nat.equivProdNatSmoothNumbers Nat.prime_three
  let x := e3.symm ⟨m, by simpa using hm⟩
  have hx' := congrArg Subtype.val (e3.apply_symm_apply ⟨m, by simpa using hm⟩)
  have hx : m = 3 ^ x.1 * x.2.1 := by
    change 3 ^ x.1 * x.2.1 = m at hx'
    exact hx'.symm
  let e2 := Nat.equivProdNatSmoothNumbers Nat.prime_two
  let y := e2.symm ⟨x.2.1, x.2.2⟩
  have hy' := congrArg Subtype.val (e2.apply_symm_apply ⟨x.2.1, x.2.2⟩)
  have hy : x.2.1 = 2 ^ y.1 * y.2.1 := by
    change 2 ^ y.1 * y.2.1 = x.2.1 at hy'
    exact hy'.symm
  have hy1 : y.2.1 = 1 := by
    have hy2 : y.2.1 ∈ Nat.smoothNumbers 2 := y.2.2
    have hnot : ¬ Nat.Prime 1 := by norm_num
    have : y.2.1 ∈ ({1} : Set ℕ) := by
      simpa [Nat.smoothNumbers_succ (N := 1) hnot, Nat.smoothNumbers_one] using hy2
    simpa using this
  refine ⟨y.1, x.1, ?_⟩
  rw [hx, hy, hy1]
  ring
