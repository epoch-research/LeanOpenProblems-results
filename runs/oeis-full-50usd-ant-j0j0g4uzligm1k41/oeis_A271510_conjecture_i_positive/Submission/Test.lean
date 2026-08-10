import FormalConjectures.Util.ProblemImports

open Nat

def A271510 (n : ℕ) : ℕ :=
  let is_square (k : ℕ) : Prop := k.sqrt * k.sqrt = k
  let bound := n.sqrt
  let R : Finset ℕ := Finset.range (bound + 1)
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) := R.product R |>.product R |>.product R
  Finset.card $ search_space.filter fun p =>
    let x := p.fst.fst.fst
    let y := p.fst.fst.snd
    let z := p.fst.snd
    let w := p.snd
    x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
    x ≥ y ∧
    is_square (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2)

-- A positivity lemma: if (x,y,z,w) is a valid witness within the bound, then A271510 n > 0.
example (n x y z w : ℕ)
    (hx : x ≤ n.sqrt) (hy : y ≤ n.sqrt) (hz : z ≤ n.sqrt) (hw : w ≤ n.sqrt)
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n)
    (hxy : x ≥ y)
    (hsq : (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt * (x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2).sqrt
        = x ^ 2 + 8 * y ^ 2 + 16 * z ^ 2) :
    0 < A271510 n := by
  unfold A271510
  simp only
  rw [Finset.card_pos]
  refine ⟨(((x, y), z), w), ?_⟩
  rw [Finset.mem_filter]
  constructor
  · simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> omega
  · exact ⟨hsum, hxy, hsq⟩
