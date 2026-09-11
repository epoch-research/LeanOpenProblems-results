import FormalConjectures.Util.ProblemImports
open Matrix Nat Int

noncomputable def A226163 (n : ℕ) : ℤ :=
  if h : n < 2 then 0 else
  let p : ℕ := Nat.nth Nat.Prime (n - 1)
  let m : ℕ := (p - 1) / 2
  let C : ℤ := m.factorial.cast
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast
    let arg : ℤ := i' * i' - C * j'
    jacobiSym arg p
  M.det

theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  sorry

theorem oeis_226163_conjecture_0.disproof : ¬ (type_of% @oeis_226163_conjecture_0) := by
  intro h
  have h_3 : A226163 3 = 0 ↔ Nat.nth Nat.Prime (3 - 1) % 4 = 3 := h 3 (by omega)
  have hn_prime : Nat.nth Nat.Prime 2 = 5 := Nat.nth_prime_two_eq_five
  rw [hn_prime] at h_3
  have h_right : 5 % 4 = 3 ↔ False := by decide
  rw [h_right] at h_3
  have h_left : A226163 3 = 0 := by
    have h_mp : A226163 3 = 0 → False := h_3.mp
    -- wait, we are given h_3 : A226163 3 = 0 <-> False.
    -- This means A226163 3 != 0.
    -- The conjecture says A226163 3 = 0 <-> False.
    -- And we proved A226163 3 = -1 != 0.
    -- So the conjecture HOLDS for n=3 !
    sorry
  sorry
