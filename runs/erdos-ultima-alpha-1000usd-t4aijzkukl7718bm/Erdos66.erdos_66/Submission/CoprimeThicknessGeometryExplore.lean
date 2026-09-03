import Submission.CoprimeThicknessExplore
import Submission.GraphBlockGeometryExplore

/-! Identification of the CRT-defined cyclic sets with the earlier coordinate
thickenings, after a vertical rescaling in the common plane. -/
namespace Erdos66CoprimeThicknessGeometry
open Erdos66CoprimeThickness Erdos66RectangularRadix Erdos66CyclicThickening
  Erdos66GraphBlockGeometry Erdos66MixedCyclicThickening Erdos66OriginRepair
open scoped Classical
set_option maxHeartbeats 1800000

variable (p K L : ℕ) [NeZero p] [NeZero K] [NeZero L]
variable (hp : p.Coprime (K*L)) (hKL : K.Coprime L)

noncomputable def verticalPreimage (k : ZMod p) (B : Finset (ZMod p × ZMod p)) :
    Finset (ZMod p × ZMod p) := Finset.univ.filter (fun z ↦ (z.1,k*z.2)∈B)

lemma high_digit_identity (n J : ℕ) :
    ((n/p:ℕ):ZMod p)-(((n/p:ℕ):ZMod J).val:ZMod p) =
      (J:ZMod p)*((n/(p*J):ℕ):ZMod p) := by
  by_cases hJ : J=0
  · subst J
    simp
  · letI : NeZero J := ⟨hJ⟩
    rw [ZMod.val_natCast, ←Nat.div_div_eq_div_mul]
    have hh : n/p % J + J*(n/p/J) = n/p := Nat.mod_add_div (n/p) J
    have he := congrArg (fun m : ℕ ↦ (m:ZMod p)) hh
    push_cast at he
    linear_combination -he

lemma leftSet_nat_mem (B : Finset (ZMod p × ZMod p)) (n : ℕ) :
    (n:ZMod (p*(p*(K*L))))∈leftSet p K L hp hKL B ↔
      ((n:ZMod p),(K:ZMod p)*((n/(p*K):ℕ):ZMod p))∈B := by
  rw [←encode_nat p (p*(K*L)) n, leftSet, mem_radixSet]
  simp only [leftRows, Finset.mem_filter, Finset.mem_univ, true_and,
    map_natCast, Prod.fst_natCast, Prod.snd_natCast, high_digit_identity]

lemma rightSet_nat_mem (C : Finset (ZMod p × ZMod p)) (n : ℕ) :
    (n:ZMod (p*(p*(K*L))))∈rightSet p K L hp hKL C ↔
      ((n:ZMod p),(L:ZMod p)*((n/(p*L):ℕ):ZMod p))∈C := by
  rw [←encode_nat p (p*(K*L)) n, rightSet, mem_radixSet]
  simp only [rightRows, Finset.mem_filter, Finset.mem_univ, true_and,
    map_natCast, Prod.fst_natCast, Prod.snd_natCast, high_digit_identity]

/-- This equivalence holds for every natural n, not just one period. -/
theorem leftSet_is_thickening (B : Finset (ZMod p × ZMod p)) (n : ℕ) :
    (n:ZMod (p*(p*(K*L))))∈leftSet p K L hp hKL B ↔
      (n:ZMod ((p*K)^2))∈thickenedSet p K (verticalPreimage p (K:ZMod p) B) := by
  rw [leftSet_nat_mem, thickenedSet_nat_mem]
  simp only [verticalPreimage, Finset.mem_filter, Finset.mem_univ, true_and]

theorem rightSet_is_thickening (C : Finset (ZMod p × ZMod p)) (n : ℕ) :
    (n:ZMod (p*(p*(K*L))))∈rightSet p K L hp hKL C ↔
      (n:ZMod ((p*L)^2))∈thickenedSet p L (verticalPreimage p (L:ZMod p) C) := by
  rw [rightSet_nat_mem, thickenedSet_nat_mem]
  simp only [verticalPreimage, Finset.mem_filter, Finset.mem_univ, true_and]

end Erdos66CoprimeThicknessGeometry
