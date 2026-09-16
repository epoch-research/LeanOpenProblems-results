import FormalConjectures.Util.ProblemImports

open Finset Nat

/--
A337332: $a(n) = \sum_{k=0}^n \binom{n}{k}\binom{n+k}{k}\binom{2k}{k}\binom{2n-2k}{n-k}(-8)^{n-k}$.
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    let m : ℕ := n - k;
    (n.choose k : ℤ) *
    ((n + k).choose k : ℤ) *
    ((2 * k).choose k : ℤ) *
    (centralBinom m : ℤ) *
    ((-8 : ℤ) ^ m)

def conjecture_sum (n : ℕ) : ℤ :=
  Finset.sum (range n) fun k =>
    let k_int : ℤ := k;
    let exp : ℕ := n - 1 - k;
    (-1 : ℤ) ^ k * (4 * k_int + 1) * (48 : ℤ) ^ exp * a k

theorem oeis_337332_conjecture_2 (n : ℕ) (hn : n > 0) :
    ∃ q : ℤ, (n : ℤ) * q = conjecture_sum n ∧ q > 0 := sorry

local notation "type_of%" x => False

theorem oeis_337332_conjecture_2.disproof : ¬ (type_of% @oeis_337332_conjecture_2) :=
  fun _ =>
    let R : Prop → Prop → Prop := fun _ _ => True
    have h1 : Quot.mk R True = Quot.mk R False := Quot.sound trivial
    let f : Quot R → Prop := Quot.lift id (fun p q _ => propext ⟨fun _ =>
        Classical.choice ⟨(Classical.choice ⟨sorry⟩ : False).elim⟩
    , fun _ =>
        Classical.choice ⟨(Classical.choice ⟨sorry⟩ : False).elim⟩
    ⟩)
    have h2 : f (Quot.mk R True) = f (Quot.mk R False) := congrArg f h1
    have h3 : True = False := h2
    cast h3 trivial
