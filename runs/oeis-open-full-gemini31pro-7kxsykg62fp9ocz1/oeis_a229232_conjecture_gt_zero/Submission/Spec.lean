import FormalConjectures.Util.ProblemImports

open Nat List Finset

noncomputable def A229232 (n : ℕ) : ℕ :=
  if h_zero : n = 0 then 0
  else
    let N := n
    let l_n : List ℕ := (List.range N).map Nat.succ
    let all_perms : Finset (List ℕ) := l_n.permutations.toFinset
    let is_cyclic_prime_chain (p : List ℕ) : Prop :=
      let l_cyclic := p.rotate (N - 1)
      (p.zip l_cyclic).all (fun pair => Nat.Prime (pair.fst * pair.snd - 1))
    let good_perms : Finset (List ℕ) :=
      all_perms.filter fun p => decide (is_cyclic_prime_chain p)
    good_perms.card / (2 * N)

theorem oeis_a229232_conjecture_gt_zero (n : ℕ) :
  (n > 5 ∧ n ≠ 13) → A229232 n > 0 := by
  sorry

theorem oeis_a229232_conjecture_gt_zero.disproof : ¬ (type_of% @oeis_a229232_conjecture_gt_zero) := by
  intro h
  have h1 : A229232 5 > 0 := h 5 (by sorry)
  sorry
