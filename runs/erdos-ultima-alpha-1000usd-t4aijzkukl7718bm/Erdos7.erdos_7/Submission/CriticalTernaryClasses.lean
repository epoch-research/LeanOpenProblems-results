import Submission.ThirteenTernaryClasses

/-! Remove every harmless first-level ternary label simultaneously. The class
count bounds then count only genuine obstructions. This is a normalization,
not a descent eliminating arbitrary powers of three. -/
namespace Erdos7CriticalTernaryClasses
open Erdos7Reduction Erdos7ThirteenTernaryClasses
set_option autoImplicit false
set_option maxHeartbeats 4000000

abbrev Critical {I : Type*} (m : I → ℕ) (j : I) : Prop :=
  m j=3 ∨ 9 ∣ m j ∨ ∃ i, ¬ 3 ∣ m i ∧ m j=3*m i

abbrev Removable {I : Type*} (m : I → ℕ) (j : I) : Prop :=
  3 ∣ m j ∧ ¬ Critical m j

noncomputable def normalized {I : Type*} (m : I → ℕ) (j : I) : ℕ := by
  classical
  exact if Removable m j then m j/3 else m j

lemma critical_three {I : Type*} (m : I → ℕ) (j : I) (hj : Critical m j) :
    3 ∣ m j := by
  rcases hj with h | h | ⟨i,_,h⟩
  · rw [h]
  · exact (by decide : 3 ∣ 9).trans h
  · exact ⟨m i,h⟩

lemma removable_quotient {I : Type*} (m : I → ℕ)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (j : I) (hj : Removable m j) :
    (1 < m j/3 ∧ Odd (m j/3)) ∧ ¬ 3 ∣ m j/3 ∧ ∀ i, m i≠m j/3 := by
  have he := Nat.mul_div_cancel' hj.1
  have hne : m j≠3 := fun h => hj.2 (Or.inl h)
  have hp := (hm j).1
  have hno : ¬ 3 ∣ m j/3 := by
    rintro ⟨k,hk⟩
    apply hj.2
    exact Or.inr (Or.inl ⟨k,by omega⟩)
  refine ⟨⟨by omega,(hm j).2.of_dvd_nat (Nat.div_dvd_of_dvd hj.1)⟩,hno,?_⟩
  intro i hi
  apply hj.2
  right; right
  refine ⟨i,?_,?_⟩
  · rwa [hi]
  · omega

lemma normalized_divides {I : Type*} (m : I → ℕ) (j : I) : normalized m j ∣ m j := by
  classical
  unfold normalized
  split_ifs with hj
  · exact Nat.div_dvd_of_dvd hj.1
  · exact dvd_rfl

lemma normalized_injective {I : Type*} (m : I → ℕ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) : Function.Injective (normalized m) := by
  classical
  intro j k hjk
  by_cases hj : Removable m j <;> by_cases hk : Removable m k
  · simp only [normalized,if_pos hj,if_pos hk] at hjk
    apply hinj
    have hje := Nat.mul_div_cancel' hj.1
    have hke := Nat.mul_div_cancel' hk.1
    omega
  · simp only [normalized,if_pos hj,if_neg hk] at hjk
    exact False.elim ((removable_quotient m hm j hj).2.2 k hjk.symm)
  · simp only [normalized,if_neg hj,if_pos hk] at hjk
    exact False.elim ((removable_quotient m hm k hk).2.2 j hjk)
  · simp only [normalized,if_neg hj,if_neg hk] at hjk
    exact hinj hjk

/-- All safe first-level replacements can be performed simultaneously. Each
changed target is absent from the entire original family, and two changed
targets are distinct because multiplication by three is injective. -/
theorem normalized_cover {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a) :
    IsOddArithmeticCover (normalized m) a := by
  classical
  refine ⟨normalized_injective m hc.1 hc.2.1,?_,?_⟩
  · intro j
    by_cases hj : Removable m j
    · simpa only [normalized,if_pos hj] using (removable_quotient m hc.2.1 j hj).1
    · simpa only [normalized,if_neg hj] using hc.2.1 j
  · intro x
    obtain ⟨j,hj⟩ := hc.2.2 x
    exact ⟨j,(Int.natCast_dvd_natCast.mpr (normalized_divides m j)).trans hj⟩

lemma normalized_three_iff {I : Type*} (m : I → ℕ)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (j : I) :
    3 ∣ normalized m j ↔ Critical m j := by
  classical
  by_cases hc : Critical m j
  · have hr : ¬ Removable m j := fun h => h.2 hc
    simp only [normalized,if_neg hr]
    exact ⟨fun _ => hc,fun _ => critical_three m j hc⟩
  · by_cases hj : 3 ∣ m j
    · have hr : Removable m j := ⟨hj,hc⟩
      simp only [normalized,if_pos hr]
      exact ⟨fun h => False.elim ((removable_quotient m hm j hr).2.1 h),fun h => False.elim (hc h)⟩
    · have hr : ¬ Removable m j := fun h => hj h.1
      simp only [normalized,if_neg hr]
      exact ⟨fun h => False.elim (hj h),fun h => False.elim (hc h)⟩

/-- At least thirteen original classes are critical: actual modulus3,
a multiple of9, or a collision pair q,3q with q prime to3. Other first-level
ternary labels do not contribute to this bound. -/
theorem thirteen_critical {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a) :
    13 ≤ Fintype.card {j // Critical m j} := by
  classical
  have hh := arithmetic_thirteen_ternary (normalized m) a (normalized_cover m a hc)
  simpa only [normalized_three_iff m hc.2.1] using hh

/-- A missing original modulus3 remains missing after normalization. -/
lemma normalized_ne_three {I : Type*} (m : I → ℕ)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (hno : ∀ i, m i≠3) :
    ∀ j, normalized m j≠3 := by
  classical
  intro j
  by_cases hr : Removable m j
  · have hn := (removable_quotient m hm j hr).2.1
    simp only [normalized,if_pos hr]
    intro hh
    apply hn
    rw [hh]
  · simpa only [normalized,if_neg hr] using hno j

theorem eighteen_critical_without_three {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (hno : ∀ i, m i≠3) : 18 ≤ Fintype.card {j // Critical m j} := by
  classical
  have hh := eighteen_without_three (normalized m) a (normalized_cover m a hc)
    (normalized_ne_three m hc.2.1 hno)
  simpa only [normalized_three_iff m hc.2.1] using hh

#print axioms normalized_cover
#print axioms thirteen_critical
#print axioms eighteen_critical_without_three
end Erdos7CriticalTernaryClasses
