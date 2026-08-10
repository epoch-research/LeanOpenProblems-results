import FormalConjectures.Util.ProblemImports
-- try shadowing Odd
namespace Local
  def Odd (n : Nat) : Prop := True
  example : Odd 2 := trivial
end Local
-- root shadow impossible?
-- def Odd (n : Nat) : Prop := True
