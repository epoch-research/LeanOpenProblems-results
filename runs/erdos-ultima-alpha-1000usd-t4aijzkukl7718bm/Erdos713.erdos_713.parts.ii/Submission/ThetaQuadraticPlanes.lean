import FormalConjecturesUtil
import Submission.ThetaMinimalHallCore

/-! A finite quadratic-plane counterexample to an unrestricted Hall bound
for heavy pairs. This does not refute the density gap or Erdős 713. -/
open Finset
namespace Erdos713ThetaQuadraticPlanes
open Erdos713ThetaGram Erdos713GlobalLight Erdos713ThetaHeavyShadow
open Erdos713ThetaHeavyMatching Erdos713ThetaRigidHeavyMatching
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false

/-- Bit masks of the 120 affine singular planes for
Q(x)=x0*x1+x2*x3+x4 over F_2^5. -/
def masks : Array ℕ := #[
  51, 771, 805306371, 85, 1285, 1342177285, 8912913, 33825,
  1207959585, 33345, 671088705, 134742273, 1082130945, 545260545, 268992513, 170,
  2570, 2684354570, 18450, 2214592530, 4456482, 16770, 335544450, 2151678210,
  67371522, 272631810, 537149442, 204, 3084, 3221225484, 10260, 2181038100,
  2228292, 8580, 301990020, 2149581060, 33686532, 270534660, 1073881092, 5160,
  1090519080, 4680, 553648200, 1114248, 1074790920, 537920520, 16844808, 2147553288,
  12336, 50331696, 20560, 83886160, 25167888, 2155876368, 67641360, 34095120,
  41120, 167772320, 37749792, 134484000, 1077944352, 17072160, 49344, 201326784,
  69206592, 134352960, 538984512, 16941120, 135266688, 67182720, 33636480, 269516928,
  13056, 3146496, 21760, 5244160, 2281705728, 4727040, 2638080, 43520,
  10488320, 8655360, 1140859392, 1344000, 52224, 12585984, 8524800, 570442752,
  1213440, 4270080, 2181120, 285247488, 208896, 348160, 696320, 835584,
  3342336, 50528256, 5570560, 84213760, 2216755200, 2185297920, 11141120, 168427520,
  1209139200, 1099038720, 13369344, 202113024, 672399360, 562298880, 338165760, 306708480,
  808452096, 1347420160, 2694840320, 3233808384, 855638016, 1426063360, 2852126720, 3422552064]

def Inc (a : Fin 120) (x : Fin 32) : Prop := (masks[a.val]!).testBit x.val = true
instance : DecidableRel Inc := fun a x => inferInstanceAs (Decidable ((masks[a.val]!).testBit x.val = true))

def dataRow (a : Fin 120) : Finset (Fin 32) := univ.filter (Inc a)
def count (x y : Fin 32) : ℕ := (univ.filter (fun a : Fin 120 => Inc a x ∧ Inc a y)).card

lemma dataRow_card : ∀ a, (dataRow a).card = 4 := by decide
#print axioms dataRow_card
lemma rigid_data : ∀ a b : Fin 120, a ≠ b → (dataRow a ∩ dataRow b).card ≤ 2 := by decide
#print axioms rigid_data

/-- The singular-difference graph, including its diagonal. -/
def Positive (x y : Fin 32) : Prop := (2022213495 : ℕ).testBit (Nat.xor x.val y.val) = true
instance : DecidableRel Positive := fun x y =>
  inferInstanceAs (Decidable ((2022213495 : ℕ).testBit (Nat.xor x.val y.val) = true))

lemma count_data : ∀ x y, count x y = if x=y then 15 else if Positive x y then 3 else 0 := by
  intro x
  fin_cases x <;> decide
#print axioms count_data

lemma cross_data : ∀ a b : Fin 120, a ≠ b → 2 ≤ (dataRow a ∩ dataRow b).card →
    ∀ x ∈ dataRow a, x ∉ dataRow b → ∀ y ∈ dataRow b, y ∉ dataRow a → ¬ Positive x y := by
  intro a
  fin_cases a <;> decide
#print axioms cross_data

lemma orderedZero_data : ((univ : Finset (Fin 32 × Fin 32)).filter
    (fun p => p.1 ≠ p.2 ∧ ¬ Positive p.1 p.2)).card = 512 := by decide
#print axioms orderedZero_data
end Erdos713ThetaQuadraticPlanes
