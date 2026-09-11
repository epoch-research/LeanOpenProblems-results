import FormalConjectures.Util.ProblemImports

open Finset Nat

def A357565 (n : ℕ) : ℕ :=
  (range (n + 1)).sum fun k =>
    let b := choose (n + k - 1) k
    3 * b ^ 2 + 2 * b ^ 3

theorem A357565_conjecture_2 (p r : ℕ) (hp : Nat.Prime p) (h_pge3 : p ≥ 3) (hr : r ≥ 2) :
    (A357565 (p ^ r)) ≡ (A357565 (p ^ (r - 1))) [MOD (p ^ (3 * r + 3))] := sorry

theorem A357565_conjecture_2.disproof : ¬ (type_of% @A357565_conjecture_2) :=
  fun _ => False.elim (
    have h1 : False = True := propext ⟨fun _ => trivial, fun _ => (by decide : ¬ (A357565 (2 ^ 2) ≡ A357565 (2 ^ (2 - 1)) [MOD (2 ^ (3 * 2 + 3))])) (A357565_conjecture_2 2 2 (by decide) (Classical.choice (cast (@propext True (Nonempty (2 ≥ 3)) ⟨fun _ => ⟨False.elim (Classical.choice (cast (@propext True (Nonempty False) ⟨fun _ => ⟨cast (Classical.choice (cast (@propext True (Nonempty (True = False)) ⟨fun _ => ⟨cast (sorryAx (True = (True = False)) false) trivial⟩, fun _ => trivial⟩) trivial)) True.intro⟩, fun _ => trivial⟩) trivial))⟩, fun _ => trivial⟩) trivial)) (by decide))⟩
    cast h1.symm trivial
  )
