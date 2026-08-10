import FormalConjectures.Util.ProblemImports

open Nat Set

noncomputable def A268597 (n : ℕ) : ℕ := 
  sInf { x : ℕ | x > 0 ∧ (x - 1) % Nat.totient x = n }

lemma solve_concrete (n : ℕ) (x : ℕ) (hx_pos : x > 0) (hx_eq : (x - 1) % x.totient = n) :
  A268597 n > 0 := by
  change sInf { x : ℕ | x > 0 ∧ (x - 1) % x.totient = n } > 0
  have h : ∃ y, y > 0 ∧ (y - 1) % y.totient = n := ⟨x, hx_pos, hx_eq⟩
  rcases h with ⟨y, hy_pos, hy_eq⟩
  have h_nonempty : { y : ℕ | y > 0 ∧ (y - 1) % y.totient = n }.Nonempty := ⟨y, hy_pos, hy_eq⟩
  have h_mem := Nat.sInf_mem h_nonempty
  exact h_mem.1

theorem test_hierarchical (n : ℕ) : A268597 n > 0 := by
  by_cases h0 : n < 2
  · rcases n with _ | _ | n
    · exact solve_concrete 0 1 (by decide) (by rfl)
    · exact solve_concrete 1 4 (by decide) (by rfl)
    · omega
  · have h_ge1 : n ≥ 2 := by omega
    let m1 := n - 2
    have h_eq1 : n = m1 + 2 := by omega
    rw [h_eq1]
    by_cases h_lt1 : m1 < 2
    · rcases m1 with _ | _ | m1
      · exact solve_concrete 2 9 (by decide) (by rfl)
      · exact solve_concrete 3 8 (by decide) (by rfl)
      · omega
    · sorry
