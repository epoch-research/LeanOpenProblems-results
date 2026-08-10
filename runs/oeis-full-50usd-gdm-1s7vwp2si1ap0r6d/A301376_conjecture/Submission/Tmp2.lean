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

unsafe def A301376_conjecture_unsafe (n : ℕ) (hn : n > 0) : a n > 0 :=
  A301376_conjecture_unsafe n hn

#print axioms A301376_conjecture_unsafe
