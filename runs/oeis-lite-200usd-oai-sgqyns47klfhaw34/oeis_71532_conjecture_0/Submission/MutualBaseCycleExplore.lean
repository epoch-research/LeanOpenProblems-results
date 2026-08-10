import FormalConjectures.Util.ProblemImports

mutual
  def f (P : Prop) : Nat → P
  | 0 => g P 0
  | n+1 => f P n
  def g (P : Prop) : Nat → P
  | 0 => f P 0
  | n+1 => g P n
end

theorem arbitrary (P : Prop) : P := f P 0
#print axioms f
#print axioms arbitrary
