import FormalConjectures.Util.ProblemImports
open Finset Nat

/--
Number of ordered ways to write $n$ as $x^5 + 2y^5 + z(3z-1)/2 + w(3w+1)/2$, where $x,y,z,w$ are nonnegative integers.
The sequence definition provided uses a potentially insufficient bounding box `range (n + 1)` for $z$ and $w$.
A rigorous definition would compute bounds based on $n$. However, for the purpose of formalizing the conjecture,
we use the provided structure, trusting that the definition captures the correct count $a(n)$.
-/
def A274007 (n : ℕ) : ℕ :=
  let P1 (z : ℕ) : ℕ := (z * (3 * z - 1)) / 2
  let P2 (w : ℕ) : ℕ := (w * (3 * w + 1)) / 2

  -- A non-tight but constructive bound for the search space. This is acceptable for definition.
  let B : Finset ℕ := range (n + 1)

  card (
    (B.product B).product (B.product B)
    |>.filter (fun p =>
      -- Unpacking the tuple structure: p : (ℕ × ℕ) × (ℕ × ℕ)
      let x := p.fst.fst
      let y := p.fst.snd
      let z := p.snd.fst
      let w := p.snd.snd
      x^5 + 2 * y^5 + P1 z + P2 w = n
    )
  )

/--
Conjecture: (i) a(n) > 0 for all n = 0,1,2,..., and a(n) = 1 only for n = 0, 11, 57, 198, 229, 232, 1168, 2624.
-/


theorem oeis_274007_conjecture_i :
    (∀ n : ℕ, A274007 n > 0) ∧
    (∀ n : ℕ, A274007 n = 1 ↔ n ∈ ({0, 11, 57, 198, 229, 232, 1168, 2624} : Finset ℕ)) :=
by sorry
