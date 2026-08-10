import FormalConjectures.Util.ProblemImports
open Nat Finset Int
noncomputable def a (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  let domain : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (R.product R).product (R.product R)
  Finset.card $ domain.filter (λ p : (ℕ × ℕ) × (ℕ × ℕ) =>
    let x := p.fst.fst; let y := p.fst.snd;
    let z := p.snd.fst; let w := p.snd.snd;
    x^2 + y^2 + z^2 + w^2 = n^2 ∧
    z ≤ w ∧
    (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))
  )

lemma a_pos_of_witness {n x y z w k : ℕ}
    (hx : x ≤ n) (hy : y ≤ n) (hz : z ≤ n) (hw : w ≤ n)
    (hsum : x^2 + y^2 + z^2 + w^2 = n^2)
    (hzw : z ≤ w)
    (hk : k ≤ n)
    (hpell : (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ)) : a n > 0 := by
  unfold a
  apply Finset.card_pos.mpr
  refine ⟨((x, y), (z, w)), ?_⟩
  simp [Nat.lt_succ_iff, hx, hy, hz, hw, hsum, hzw]
  exact ⟨k, by simpa [Nat.lt_succ_iff] using hk, hpell⟩

example : a 23 > 0 := by
  exact a_pos_of_witness (n:=23) (x:=10) (y:=2) (z:=5) (w:=20) (k:=3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
