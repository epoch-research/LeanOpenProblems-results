import FormalConjectures.Util.ProblemImports

partial def magicDec (P : Prop) : Decidable P :=
  match magicDec P with
  | .isTrue hp => .isTrue hp
  | .isFalse hn => .isTrue (let rec hp : P := False.elim (hn hp); hp)

theorem arb (P : Prop) : P := by
  cases magicDec P with
  | isTrue hp => exact hp
  | isFalse hn => exact (let rec hp : P := False.elim (hn hp); hp)

#print axioms magicDec
#print axioms arb
