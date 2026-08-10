import FormalConjectures.Util.ProblemImports

open Nat Int Finset

def B_A279056 (n : ℕ) : ℕ :=
  if n = 0 then 0 else
  let B : ℕ := n.sqrt + 1
  let R : Finset ℕ := range B
  let S := ((R.product R).product R).product R
  Finset.card $ S.filter fun p =>
    let w := p.fst.fst.fst
    let x := p.fst.fst.snd
    let y := p.fst.snd
    let z := p.snd
    let square_cond : Prop :=
      let val : ℤ := (x : ℤ)^3 + 8 * (y : ℤ) * (z : ℤ) * (2 * (y : ℤ) - (z : ℤ))
      IsSquare val
    w > 0 ∧
    w^2 + x^2 + y^2 + z^2 = n ∧
    square_cond

-- A component whose square is ≤ n is < n.sqrt + 1.
theorem bound_of_sq_le {a n : ℕ} (h : a^2 ≤ n) : a < n.sqrt + 1 := by
  have : a ≤ n.sqrt := by
    rw [Nat.le_sqrt]
    simpa [pow_two] using h
  omega

-- Reduce 0 < B to existence of a witness, deriving bounds from the sum.
theorem reduction (n : ℕ) (hn : n > 0)
    (w x y z : ℕ)
    (hw : w > 0)
    (hsum : w^2 + x^2 + y^2 + z^2 = n)
    (hsq : IsSquare ((x : ℤ)^3 + 8 * (y : ℤ) * (z : ℤ) * (2 * (y : ℤ) - (z : ℤ)))) :
    0 < B_A279056 n := by
  have hb : w < n.sqrt + 1 := bound_of_sq_le (by omega)
  have hx : x < n.sqrt + 1 := bound_of_sq_le (by omega)
  have hy : y < n.sqrt + 1 := bound_of_sq_le (by omega)
  have hz : z < n.sqrt + 1 := bound_of_sq_le (by omega)
  unfold B_A279056
  rw [if_neg hn.ne']
  simp only
  rw [Finset.card_pos]
  refine ⟨(((w, x), y), z), ?_⟩
  rw [Finset.mem_filter]
  constructor
  · refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact Finset.mem_range.mpr hb
    · exact Finset.mem_range.mpr hx
    · exact Finset.mem_range.mpr hy
    · exact Finset.mem_range.mpr hz
  · dsimp only
    refine ⟨by exact_mod_cast hw, ?_, hsq⟩
    exact_mod_cast hsum
