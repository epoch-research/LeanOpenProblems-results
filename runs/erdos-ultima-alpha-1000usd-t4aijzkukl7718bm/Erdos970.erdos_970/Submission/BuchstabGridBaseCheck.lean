import Submission.BuchstabGridData

/-! Kernel-checked local inequalities for rounded integer profile tables.
This is a finite arithmetic certificate, not an assertion that the tables
already bound an arithmetic sieve. The latter needs prime-sector transfer. -/
namespace Erdos970.BuchstabGrid
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Rational initial envelope at the mesh nodes. The tail coefficient is
slightly enlarged from 9/217 to 3/50, leaving room for later error absorption. -/
def baseFormula (j : ℕ) : ℚ :=
  if j = 0 then 1 else if j ≤ 100 then (100*(90009/50000 : ℚ))/j
  else if j < 270 then
    (90009/50000 : ℚ)*((1-((j%10 : ℕ) : ℚ)/10)*profileValues[j/10-10]!+
      (((j%10 : ℕ) : ℚ)/10)*profileValues[j/10-10+1]!)
  else if j < 400 then (90009/50000 : ℚ)*(290999/500000)
  else 1+(3/50 : ℚ)*(400/j)^8

def integerBaseBound (j : ℕ) : Prop :=
  if j = 0 then scale ≤ (baseNodes (j))
  else if j ≤ 100 then scale*100*90009 ≤ (baseNodes (j))*50000*j
  else if j < 270 then
    scale*90009*((10-j%10)*profileNumerators[j/10-10]!+
      (j%10)*profileNumerators[j/10-10+1]!) ≤ (baseNodes (j))*50000*10*scale
  else if j < 400 then scale*90009*581998 ≤ (baseNodes (j))*50000*scale
  else scale*(50*j^8+3*400^8) ≤ (baseNodes (j))*50*j^8

instance (j : ℕ) : Decidable (integerBaseBound j) := by unfold integerBaseBound; infer_instance

lemma integer_base_bound : ∀ j : Fin 601, integerBaseBound j.val := by decide +kernel

lemma profile_value_eq : ∀ j : Fin 18,
    profileValues[j.val]! = (profileNumerators[j.val]! : ℚ)/1000000 := by decide +kernel

#print axioms integer_base_bound
end Erdos970.BuchstabGrid
