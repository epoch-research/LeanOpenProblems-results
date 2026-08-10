import FormalConjectures.Util.ProblemImports
axiom P : Prop
namespace foo
 theorem disproof : ¬ P := by
   intro h
   exact disproof h
 #print axioms disproof
end foo
