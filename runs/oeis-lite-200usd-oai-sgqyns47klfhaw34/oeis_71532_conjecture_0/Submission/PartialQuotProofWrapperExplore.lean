import FormalConjectures.Util.ProblemImports

-- A custom quotient of proofs of P, if it can be partially inhabited, eliminates to P via Quot.ind.
def ProofQuot (P : Prop) := Quot (fun (_ _ : P) => True)
partial def pq (P : Prop) : ProofQuot P := pq P

theorem arbitrary (P : Prop) : P := by
  change P
  let q := pq P
  refine Quot.ind (motive := fun _ => P) (fun hp => hp) q

#print axioms arbitrary
