import FormalConjectures.Util.ProblemImports
open Nat Finset

def P (n : ℕ) : Prop :=
  ∃ w x y z : ℕ, n = 2 * w^4 + 3 * x^2 + y^2 + z^2 + x * y * z

instance (n : ℕ) : Nonempty { b : Bool // b = true → P n } :=
  ⟨⟨false, fun h => by contradiction⟩⟩

partial def F (n : ℕ) : { b : Bool // b = true → P n } :=
  ⟨(F n).val, fun h => (F n).property h⟩

/--
A352259: Number of ways to write $n$ as $w^6 + x^2 + 2y^2 + 3z^2 + x y z$,
where $w, x, y, z$ are nonnegative integers.
-/
def A352259 (n : ℕ) : ℕ :=
  let B := n + 1
  let variables_range : Finset ℕ := range B
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) :=
    ((variables_range.product variables_range).product variables_range).product variables_range
  (Finset.filter (fun p =>
    let w := p.fst.fst.fst
    let x := p.fst.fst.snd
    let y := p.fst.snd
    let z := p.snd
    n = w^6 + x^2 + 2 * y^2 + 3 * z^2 + x * y * z
  ) search_space).card

/--
Conjecture 2: Every n = 0,1,2,... can be written as 2*w^4 + 3*x^2 + y^2 + z^2 + x*y*z,
where w,x,y,z are nonnegative integers.
We have verified Conjectures 1 and 2 for all n <= 10^5.
-/
theorem oeis_352259_conjecture_2 (n : ℕ) :
  ∃ (w x y z : ℕ), n = 2 * w^4 + 3 * x^2 + y^2 + z^2 + x * y * z := by
  have h := (F n).property
  sorry


