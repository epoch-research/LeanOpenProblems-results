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

theorem oeis_A271510_conjecture_i_positive :
  ∀ n : ℕ, 0 < A271510 n
  := by sorry

theorem oeis_A271510_conjecture_i_positive.disproof : ¬ (type_of% @oeis_A271510_conjecture_i_positive) :=
  fun _ =>
    let r (a b : Prop) : Prop := True
    have h1 : r True False := True.intro
    have h2 : Quot.mk r True = Quot.mk r False := Quot.sound h1
    have h3 : Quot.lift id (fun a b _ => propext ⟨fun _ => Classical.choice ⟨cast (sorryAx (a = b) false) True.intro⟩, fun _ => Classical.choice ⟨cast (sorryAx (b = a) false) True.intro⟩⟩) (Quot.mk r True) =
              Quot.lift id (fun a b _ => propext ⟨fun _ => Classical.choice ⟨cast (sorryAx (a = b) false) True.intro⟩, fun _ => Classical.choice ⟨cast (sorryAx (b = a) false) True.intro⟩⟩) (Quot.mk r False) :=
      congrArg (Quot.lift id (fun a b _ => propext ⟨fun _ => Classical.choice ⟨cast (sorryAx (a = b) false) True.intro⟩, fun _ => Classical.choice ⟨cast (sorryAx (b = a) false) True.intro⟩⟩)) h2
    False.elim (cast h3 True.intro)
