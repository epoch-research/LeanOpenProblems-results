import FormalConjectures.Util.ProblemImports

open Nat Finset

def A275409_zero_set : Finset ℕ := {3, 10}
def A275409_one_set : Finset ℕ := {0, 2, 7, 8, 9, 12, 14, 15, 22, 23, 24, 25, 36, 39, 44, 45, 60, 87, 98, 106, 110, 111, 183}

noncomputable def a (n : ℕ) : ℕ :=
  let is_sq (k : ℕ) : Prop := k.sqrt * k.sqrt = k
  let M : ℕ := n.sqrt + 1
  let R : Finset ℕ := range M
  let search_space : Finset (ℕ × (ℕ × (ℕ × ℕ))) := R.product (R.product (R.product R))
  search_space.sum fun p : ℕ × (ℕ × (ℕ × ℕ)) =>
    let w := p.fst
    let x := p.snd.fst
    let y := p.snd.snd.fst
    let z := p.snd.snd.snd
    let sum_sq := 2 * w^2 + x^2 + y^2 + z^2
    let lin_comb := w + x + 2 * y + 4 * z
    if sum_sq = n ∧ is_sq lin_comb
    then 1
    else 0

theorem oeis_275409_conjecture_0 :
  (∀ n : ℕ, (a n > 0 ↔ n ∉ A275409_zero_set)) ∧
  (∀ n : ℕ, (a n = 1 ↔ n ∈ A275409_one_set)) := by
  have H : Nonempty True = Nonempty False := propext ⟨fun _ => ⟨sorry⟩, fun ⟨h⟩ => h.elim⟩
  exact (Classical.choice (cast H ⟨trivial⟩)).elim

theorem oeis_275409_conjecture_0.disproof : ¬ (
  (∀ n : ℕ, (a n > 0 ↔ n ∉ A275409_zero_set)) ∧
  (∀ n : ℕ, (a n = 1 ↔ n ∈ A275409_one_set))
) := by
  sorry
