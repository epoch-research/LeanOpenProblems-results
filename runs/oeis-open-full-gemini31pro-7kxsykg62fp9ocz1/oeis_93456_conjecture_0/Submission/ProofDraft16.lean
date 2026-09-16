import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  let L := n.choose 2 + 1
  let R := (n + 1).choose 2
  let is_composite (k : ℕ) : Prop := 1 < k ∧ ¬ k.Prime
  (Icc L R).filter is_composite |>.prod id

lemma disproof_aux (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
  let n := p * (p - 2)
  n > 1 ∧ ¬ (a (n - 1) ∣ a n) := by
  intro n
  have hp2 : 2 ≤ p := hp.two_le
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have heven : Even (p - 1) := by omega
  obtain ⟨k, hk⟩ := heven
  have h1 : n > 1 := by omega
  refine ⟨h1, ?_⟩
  sorry
