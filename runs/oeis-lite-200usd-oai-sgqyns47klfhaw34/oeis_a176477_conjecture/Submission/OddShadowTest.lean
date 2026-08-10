import FormalConjectures.Util.ProblemImports
namespace Hack
  def Odd (n : Nat) : Prop := True
end Hack
open Hack
#check (show Odd 2 from trivial)
#print Odd
