import FormalConjectures.Util.ProblemImports

open Nat Finset

def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2

def A308584 (n : ℕ) : ℕ :=
  let T := triangular_number
  let bound := n + 1
  let R := Finset.range bound
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) :=
    ((R.product R).product R).product R
  (search_space.filter fun t =>
    let ab_pair := t.fst.fst
    let c         := t.fst.snd
    let d         := t.snd
    let a         := ab_pair.fst
    let b         := ab_pair.snd
    a ≤ b ∧ T a + T b + 5^c * 8^d = n
  ).card

theorem test_witness_100 : A308584 100 > 0 := by
  unfold A308584
  dsimp only
  apply Finset.card_pos.mpr
  let witness : ((ℕ × ℕ) × ℕ) × ℕ := (((6, 12), 0), 0)
  refine ⟨witness, ?_⟩
  rw [mem_filter]
  refine ⟨?_goal1, by decide⟩
  simp [witness, Finset.mem_product, Finset.mem_range]

#print axioms test_witness_100
