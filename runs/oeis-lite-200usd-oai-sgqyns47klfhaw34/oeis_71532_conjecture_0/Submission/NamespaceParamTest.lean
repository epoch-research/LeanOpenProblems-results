import FormalConjectures.Util.ProblemImports
axiom P : Prop
namespace oeis_71532_conjecture_0
  theorem disproof (h : False) : ¬ P := by intro hp; exact h
end oeis_71532_conjecture_0
#check oeis_71532_conjecture_0.disproof
#print oeis_71532_conjecture_0.disproof
