import Submission.DoubleExceptionArithmetic
import Submission.NoThreeHoleSpan
import Submission.SmallTernaryBranches

/-! Two arbitrary nontrivial odd exceptional classes over a distinct no-3 base. -/
namespace Erdos7DoubleExceptionOdd
open Erdos7Reduction Erdos7MinimumTernaryClass Erdos7NoThreeHoleSpan
open Erdos7DoubleExceptionArithmetic
set_option maxHeartbeats 4000000

lemma free_ternary_residue (b₀ b₁ : ℤ) :
    ∃ r : ℤ, ¬ (3 : ℤ) ∣ r-b₀ ∧ ¬ (3 : ℤ) ∣ r-b₁ := by
  by_cases h : (3 : ℤ) ∣ b₀+1-b₁
  · exact ⟨b₀+2,by omega,by omega⟩
  · exact ⟨b₀+1,by omega,h⟩

/-- If either extra modulus has a factor3, a free ternary residue reduces to
the already established one-exception theorem. -/
lemma not_cover_when_three_divides {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d₀ d₁ : ℕ) (hd₀ : 3 ∣ d₀) (hd₁ : 1 < d₁ ∧ Odd d₁) (b₀ b₁ : ℤ) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨
      (d₀ : ℤ) ∣ x-b₀ ∨ (d₁ : ℤ) ∣ x-b₁) := by
  classical
  intro hcover
  by_cases h13 : 3 ∣ d₁
  · obtain ⟨r,hr₀,hr₁⟩ := free_ternary_residue b₀ b₁
    choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) r
    have hc : IsOddArithmeticCover m a' := by
      refine ⟨hinj,hm,fun x => ?_⟩
      rcases hcover (3*x+r) with ⟨i,hi⟩ | hi | hi
      · exact ⟨i,ha' i x hi⟩
      · have hh := (Int.natCast_dvd_natCast.mpr hd₀).trans hi
        exact False.elim (hr₀ (by omega))
      · have hh := (Int.natCast_dvd_natCast.mpr h13).trans hi
        exact False.elim (hr₁ (by omega))
    obtain ⟨i,hi⟩ := Erdos7No23Sieve.arithmetic_exists_three m a' hc
    exact h3 i hi
  · choose a' ha' using fun i => affine_residue (m i) (h3 i) (a i) (b₀+1)
    obtain ⟨b',hb'⟩ := affine_residue d₁ h13 b₁ (b₀+1)
    apply not_cover_with_odd_exception m a' hinj hm h3 d₁ hd₁ b'
    intro x
    rcases hcover (3*x+(b₀+1)) with ⟨i,hi⟩ | hi | hi
    · exact Or.inl ⟨i,ha' i x hi⟩
    · have hh := (Int.natCast_dvd_natCast.mpr hd₀).trans hi
      omega
    · exact Or.inr (hb' x hi)

/-- The two extra odd moduli need not be coprime to3, distinct from one
another, or distinct from the base labels. -/
theorem not_cover_with_two_odd_exceptions {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : Fin 2 → ℕ) (hd : ∀ j, 1 < d j ∧ Odd (d j)) (b : Fin 2 → ℤ) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ (∃ j, (d j : ℤ) ∣ x-b j)) := by
  classical
  intro hcover
  have hc : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨
      (d 0 : ℤ) ∣ x-b 0 ∨ (d 1 : ℤ) ∣ x-b 1 := by
    simpa only [Fin.exists_fin_two] using hcover
  by_cases h03 : 3 ∣ d 0
  · exact not_cover_when_three_divides m a hinj hm h3 (d 0) (d 1) h03 (hd 1) (b 0) (b 1) hc
  · by_cases h13 : 3 ∣ d 1
    · apply not_cover_when_three_divides m a hinj hm h3 (d 1) (d 0) h13 (hd 0) (b 1) (b 0)
      intro x
      rcases hc x with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · apply not_no_three_cover_with_two_exceptions m a hinj hm h3 d hd _ b hcover
      intro j
      fin_cases j <;> assumption

/-- Any index type of cardinality at most two is allowed, including empty. -/
theorem not_cover_with_at_most_two_odd_exceptions {I J : Type*} [Fintype I] [Fintype J]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : J → ℕ) (hd : ∀ j, 1 < d j ∧ Odd (d j)) (b : J → ℤ)
    (hJ : Fintype.card J ≤ 2) :
    ¬ (∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-a i) ∨ (∃ j, (d j : ℤ) ∣ x-b j)) := by
  classical
  intro hcover
  let f : J ↪ Fin 2 := Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hJ))
  let d' := Function.extend f d (fun _ => 5)
  let b' := Function.extend f b (fun _ => 0)
  have hd' (k : Fin 2) : 1 < d' k ∧ Odd (d' k) := by
    by_cases hk : ∃ j, f j=k
    · obtain ⟨j,rfl⟩ := hk
      simpa only [d',f.injective.extend_apply] using hd j
    · rw [show d' k=5 from Function.extend_apply' d (fun _ => 5) k hk]
      decide
  apply not_cover_with_two_odd_exceptions m a hinj hm h3 d' hd' b'
  intro x
  rcases hcover x with ⟨i,hi⟩ | ⟨j,hj⟩
  · exact Or.inl ⟨i,hi⟩
  · right
    refine ⟨f j,?_⟩
    simpa only [d',b',f.injective.extend_apply] using hj

/-- There is a base hole outside every pair of nontrivial odd congruences. -/
theorem hole_escape_two {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hinj : Function.Injective m)
    (hm : ∀ i, 1 < m i ∧ Odd (m i)) (h3 : ∀ i, ¬ 3 ∣ m i)
    (d : Fin 2 → ℕ) (hd : ∀ j, 1 < d j ∧ Odd (d j)) (b : Fin 2 → ℤ) :
    ∃ x : ℤ, Hole m a x ∧ ∀ j, ¬ (d j : ℤ) ∣ x-b j := by
  classical
  by_contra! hn
  apply not_cover_with_two_odd_exceptions m a hinj hm h3 d hd b
  intro x
  by_cases hx : ∃ i, (m i : ℤ) ∣ x-a i
  · exact Or.inl hx
  · exact Or.inr (hn x (fun i hi => hx ⟨i,hi⟩))

/-- Every ternary branch without modulus3 has at least three classes in ANY
odd cover. No irredundance or cardinality minimality is assumed. -/
theorem ternary_branch_card {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a)
    (r : ℤ) (hno : ∀ j, (3 : ℤ) ∣ a j-r → m j≠3) :
    3 ≤ Fintype.card {j // 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r} := by
  classical
  by_contra hsmall
  let K := {i : I // ¬ 3 ∣ m i}
  let J := {j : I // 3 ∣ m j ∧ (3 : ℤ) ∣ a j-r}
  obtain ⟨b,hb⟩ := Erdos7SmallTernaryBranches.restrict_ternary_branch m a hc r
  have hd (j : J) : 1 < m j/3 ∧ Odd (m j/3) := by
    have he : 3*(m j/3)=m j := Nat.mul_div_cancel' j.property.1
    have hm := hc.2.1 j
    have hne := hno j j.property.2
    refine ⟨by omega,hm.2.of_dvd_nat ?_⟩
    exact Nat.div_dvd_of_dvd j.property.1
  apply not_cover_with_at_most_two_odd_exceptions
    (fun i : K => m i) b (hc.1.comp Subtype.val_injective)
    (fun i => hc.2.1 i) (fun i => i.property)
    (fun j : J => m j/3) hd (fun j => (a j-r)/3) _ hb
  simp only [J,Fintype.card_subtype] at hsmall ⊢
  omega

#print axioms not_cover_with_two_odd_exceptions
#print axioms hole_escape_two
#print axioms not_cover_with_at_most_two_odd_exceptions
#print axioms ternary_branch_card
end Erdos7DoubleExceptionOdd
