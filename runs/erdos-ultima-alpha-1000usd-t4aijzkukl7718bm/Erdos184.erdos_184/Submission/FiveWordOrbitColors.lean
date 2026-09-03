import Submission.FiveWordOrbits0
import Submission.FiveWordOrbits1
import Submission.FiveWordOrbits2
import Submission.FiveWordOrbits3

/-! The color maps of the checked orbit witnesses are permutations. -/
namespace Erdos184Work.FiveWordOrbits0
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma color_bijective : ∀ i : Cases, Function.Bijective (colorMap i) := by decide +kernel
noncomputable def colorEquiv (i : Cases) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (colorMap i) (color_bijective i)
#print axioms color_bijective
end Erdos184Work.FiveWordOrbits0

namespace Erdos184Work.FiveWordOrbits1
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma color_bijective : ∀ i : Cases, Function.Bijective (colorMap i) := by decide +kernel
noncomputable def colorEquiv (i : Cases) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (colorMap i) (color_bijective i)
#print axioms color_bijective
end Erdos184Work.FiveWordOrbits1

namespace Erdos184Work.FiveWordOrbits2
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma color_bijective : ∀ i : Cases, Function.Bijective (colorMap i) := by decide +kernel
noncomputable def colorEquiv (i : Cases) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (colorMap i) (color_bijective i)
#print axioms color_bijective
end Erdos184Work.FiveWordOrbits2

namespace Erdos184Work.FiveWordOrbits3
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma color_bijective : ∀ i : Cases, Function.Bijective (colorMap i) := by decide +kernel
noncomputable def colorEquiv (i : Cases) : Equiv.Perm (Fin 5) :=
  Equiv.ofBijective (colorMap i) (color_bijective i)
#print axioms color_bijective
end Erdos184Work.FiveWordOrbits3

