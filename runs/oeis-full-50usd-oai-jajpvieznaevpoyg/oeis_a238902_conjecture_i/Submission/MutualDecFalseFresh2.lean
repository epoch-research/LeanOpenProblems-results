import FormalConjectures.Util.ProblemImports

mutual
  partial def pfFalse : Unit → False
  | () =>
    match decFalse () with
    | Decidable.isTrue h => h
    | Decidable.isFalse hn => pfFalse ()
  partial def decFalse : Unit → Decidable False
  | () => Decidable.isTrue (pfFalse ())
end

example : False := pfFalse ()
#print axioms pfFalse
#print axioms decFalse
