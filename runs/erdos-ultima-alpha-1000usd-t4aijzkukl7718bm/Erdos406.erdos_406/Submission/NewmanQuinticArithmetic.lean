import Submission.NewmanQuinticTrace
/-! Kernel-checked finite arithmetic for the complete quintic classification.
This classifies a bounded coefficient problem, not arbitrary degrees. -/
namespace Erdos406QuinticTable

def tableCase (t : Fin 5) (a d : Fin 17) (b : Fin 45) : Prop :=
  let t := t.val + 1
  let a := (a.val : ℤ) - 8
  let d := (d.val : ℤ) - 8
  let b := (b.val : ℤ) - 6
  let c := ((4 : ℤ)^t - 244 - 81*a - 27*b - 3*d) / 9
  ((4 : ℤ)^t = 244 + 81*a + 27*b + 9*c + 3*d ∧
    |a^2 - 2*b| ≤ 13 ∧ |d^2 - 2*c| ≤ 13 ∧
    |-a^3 + 3*a*b - 3*c| ≤ 21 ∧ |-d^3 + 3*d*c - 3*b| ≤ 21 ∧
    2*(4 : ℤ)^t < 3*(244 + 81*d + 27*c + 9*b + 3*a) ∧
    2*(244 + 81*d + 27*c + 9*b + 3*a) < 3*(4 : ℤ)^t ∧
    0 ≤ a+b+c+d ∧ 0 < 2882 + 405*a - 675*b + 1125*c - 1875*d ∧
    |-a^5 + 5*a^3*b - 5*a*b^2 - 5*a^2*c + 5*b*c + 5*a*d - 5| ≤ 56 ∧
    |-d^5 + 5*d^3*c - 5*d*c^2 - 5*d^2*b + 5*c*b + 5*d*a - 5| ≤ 56) →
    (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 1) ∨
      (a = 5 ∧ b = 10 ∧ c = 10 ∧ d = 5)

instance (t : Fin 5) (a d : Fin 17) (b : Fin 45) : Decidable (tableCase t a d b) :=
  inferInstanceAs (Decidable (_ → _))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
lemma table_checked_0 : ∀ (a d : Fin 17) (b : Fin 45), tableCase ⟨0, by decide⟩ a d b := by
  decide +kernel
#print axioms table_checked_0

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
lemma table_checked_1 : ∀ (a d : Fin 17) (b : Fin 45), tableCase ⟨1, by decide⟩ a d b := by
  decide +kernel
#print axioms table_checked_1

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
lemma table_checked_2 : ∀ (a d : Fin 17) (b : Fin 45), tableCase ⟨2, by decide⟩ a d b := by
  decide +kernel
#print axioms table_checked_2

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
lemma table_checked_3 : ∀ (a d : Fin 17) (b : Fin 45), tableCase ⟨3, by decide⟩ a d b := by
  decide +kernel
#print axioms table_checked_3

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
lemma table_checked_4 : ∀ (a d : Fin 17) (b : Fin 45), tableCase ⟨4, by decide⟩ a d b := by
  decide +kernel
#print axioms table_checked_4

lemma table_checked : ∀ (t : Fin 5) (a d : Fin 17) (b : Fin 45), tableCase t a d b := by
  intro t
  fin_cases t
  · exact table_checked_0
  · exact table_checked_1
  · exact table_checked_2
  · exact table_checked_3
  · exact table_checked_4

#print axioms table_checked

lemma arithmetic_of_table
    (hchecked : ∀ (t : Fin 5) (a d : Fin 17) (b : Fin 45), tableCase t a d b)
    (a b c d : ℤ) (t : ℕ)
    (ht : 1 ≤ t) (ht5 : t ≤ 5) (ha : |a| ≤ 8) (hd : |d| ≤ 8)
    (h2a : |a^2 - 2*b| ≤ 13) (h2d : |d^2 - 2*c| ≤ 13)
    (h3a : |-a^3 + 3*a*b - 3*c| ≤ 21) (h3d : |-d^3 + 3*d*c - 3*b| ≤ 21)
    (h5a : |-a^5 + 5*a^3*b - 5*a*b^2 - 5*a^2*c + 5*b*c + 5*a*d - 5| ≤ 56)
    (h5d : |-d^5 + 5*d^3*c - 5*d*c^2 - 5*d^2*b + 5*c*b + 5*d*a - 5| ≤ 56)
    (hv : (4 : ℤ)^t = 244 + 81*a + 27*b + 9*c + 3*d)
    (hlo : 2*(4 : ℤ)^t < 3*(244 + 81*d + 27*c + 9*b + 3*a))
    (hhi : 2*(244 + 81*d + 27*c + 9*b + 3*a) < 3*(4 : ℤ)^t)
    (hone : 0 ≤ a+b+c+d)
    (hneg : 0 < 2882 + 405*a - 675*b + 1125*c - 1875*d) :
    (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 1) ∨
      (a = 5 ∧ b = 10 ∧ c = 10 ∧ d = 5) := by
  obtain ⟨ha0, ha1⟩ := abs_le.mp ha
  obtain ⟨hd0, hd1⟩ := abs_le.mp hd
  obtain ⟨h2a0, h2a1⟩ := abs_le.mp h2a
  have hs : a^2 ≤ 64 := by
    have hh := mul_nonneg (by omega : 0 ≤ 8-a) (by omega : 0 ≤ 8+a)
    nlinarith
  have hb0 : -6 ≤ b := by nlinarith [sq_nonneg a]
  have hb1 : b ≤ 38 := by nlinarith
  let ti : Fin 5 := ⟨t-1, by omega⟩
  let ai : Fin 17 := ⟨(a+8).toNat, by omega⟩
  let di : Fin 17 := ⟨(d+8).toNat, by omega⟩
  let bi : Fin 45 := ⟨(b+6).toNat, by omega⟩
  have hte : ti.val + 1 = t := by dsimp [ti]; omega
  have hae : (ai.val : ℤ) - 8 = a := by dsimp [ai]; omega
  have hde : (di.val : ℤ) - 8 = d := by dsimp [di]; omega
  have hbe : (bi.val : ℤ) - 6 = b := by dsimp [bi]; omega
  have hce : ((4 : ℤ)^t - 244 - 81*a - 27*b - 3*d)/9 = c := by omega
  have hh := hchecked ti ai di bi
  simp only [tableCase, hte, hae, hde, hbe, hce] at hh
  exact hh ⟨hv, h2a, h2d, h3a, h3d, hlo, hhi, hone, hneg, h5a, h5d⟩


end Erdos406QuinticTable

namespace Erdos406QuinticClassification

lemma quintic_arithmetic_classification (a b c d : ℤ) (t : ℕ)
    (ht : 1 ≤ t) (ht5 : t ≤ 5) (ha : |a| ≤ 8) (hd : |d| ≤ 8)
    (h2a : |a^2 - 2*b| ≤ 13) (h2d : |d^2 - 2*c| ≤ 13)
    (h3a : |-a^3 + 3*a*b - 3*c| ≤ 21) (h3d : |-d^3 + 3*d*c - 3*b| ≤ 21)
    (h5a : |-a^5 + 5*a^3*b - 5*a*b^2 - 5*a^2*c + 5*b*c + 5*a*d - 5| ≤ 56)
    (h5d : |-d^5 + 5*d^3*c - 5*d*c^2 - 5*d^2*b + 5*c*b + 5*d*a - 5| ≤ 56)
    (hv : (4 : ℤ)^t = 244 + 81*a + 27*b + 9*c + 3*d)
    (hlo : 2*(4 : ℤ)^t < 3*(244 + 81*d + 27*c + 9*b + 3*a))
    (hhi : 2*(244 + 81*d + 27*c + 9*b + 3*a) < 3*(4 : ℤ)^t)
    (hone : 0 ≤ a+b+c+d)
    (hneg : 0 < 2882 + 405*a - 675*b + 1125*c - 1875*d) :
    (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 1) ∨
      (a = 5 ∧ b = 10 ∧ c = 10 ∧ d = 5) := by
  exact Erdos406QuinticTable.arithmetic_of_table Erdos406QuinticTable.table_checked
    a b c d t ht ht5 ha hd h2a h2d h3a h3d h5a h5d hv hlo hhi hone hneg

#print axioms quintic_arithmetic_classification
end Erdos406QuinticClassification
