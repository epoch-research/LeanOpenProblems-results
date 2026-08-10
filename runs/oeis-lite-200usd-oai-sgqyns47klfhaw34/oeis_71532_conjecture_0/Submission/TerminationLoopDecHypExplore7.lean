import FormalConjectures.Util.ProblemImports
partial def loopDec (P : Prop) : Decidable P := loopDec P

def aux (P : Prop) (n : Nat) : P := by
  cases loopDec P with
  | isTrue h => exact h
  | isFalse hn => exact False.elim (hn (aux P (n+1)))
termination_by n
decreasing_by
  next hn heq =>
    have recHyp : ∀ (y : ℕ), InvImage (fun x1 x2 => x1 < x2) (fun x => x) y n → P := by assumption
    let rec decProof : InvImage (fun x1 x2 => x1 < x2) (fun x => x) (n+1) n :=
      False.elim (hn (recHyp (n+1) decProof))
    exact decProof

theorem arbitrary (P : Prop) : P := aux P 0
#print axioms aux
#print axioms arbitrary
