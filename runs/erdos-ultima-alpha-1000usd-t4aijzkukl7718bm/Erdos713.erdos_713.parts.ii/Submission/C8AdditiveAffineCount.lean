import FormalConjecturesUtil
import Submission.C8AdditiveAffine

/-! C8-free restrictions of additive affine curves have Sidon parameter sums.
This is an auxiliary obstruction, not a settlement of Erdős 713. -/
open SimpleGraph Finset
namespace Erdos713C8AdditiveAffineCount
open scoped Classical
open Erdos713C8CommutingDifferences Erdos713C8AdditiveAffine
variable {K I : Type*} [Field K] [CharP K 2]
set_option maxHeartbeats 2000000

def SidonSums (t : I → Kˣ) : Prop :=
  ∀ a b c d : I, a ≠ b → (t a : K)+(t b : K)=(t c : K)+(t d : K) →
    (a=c ∧ b=d) ∨ (a=d ∧ b=c)

lemma sum_sidon (f : K →+ K) (t : I → Kˣ) (ht : Function.Injective t)
    (hf : (cycleGraph 8).Free (graph (fun i => curve f (t i))))
    (a b c d : I) (hab : a ≠ b)
    (hs : (t a : K)+(t b : K)=(t c : K)+(t d : K)) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  by_cases hac : a=c
  · subst c
    exact Or.inl ⟨rfl,ht (Units.ext (add_left_cancel hs))⟩
  by_cases had : a=d
  · subst d
    rw [add_comm (t c : K)] at hs
    exact Or.inr ⟨rfl,ht (Units.ext (add_left_cancel hs))⟩
  by_cases hbc : b=c
  · subst c
    rw [add_comm (t b : K)] at hs
    exact Or.inr ⟨ht (Units.ext (add_right_cancel hs)),rfl⟩
  by_cases hbd : b=d
  · subst d
    exact Or.inl ⟨ht (Units.ext (add_right_cancel hs)),rfl⟩
  have hcd : c ≠ d := by
    intro h
    rw [h,CharTwo.add_self_eq_zero] at hs
    exact hab (ht (Units.ext (CharTwo.add_eq_zero.mp hs)))
  exact (hf (contains_at f t ht a b c d hab hac had hbc hbd hcd hs)).elim

omit [CharP K 2] in
/-- Every nonzero sum has at most the two orientations of a single pair. -/
lemma sum_fiber_le_two_of_sidon [Fintype I] (t : I → Kˣ)
    (hsidon : SidonSums t) (u : K) :
    ((univ : Finset I).offDiag.filter
      (fun p : I × I => (t p.1 : K)+(t p.2 : K)=u)).card ≤ 2 := by
  classical
  let T := (univ : Finset I).offDiag.filter
    (fun p : I × I => (t p.1 : K)+(t p.2 : K)=u)
  by_cases hT : T.Nonempty
  · obtain ⟨p,hp⟩ := hT
    have hsub : T ⊆ {p,(p.2,p.1)} := by
      intro q hq
      have hp' := mem_filter.mp hp
      have hq' := mem_filter.mp hq
      rcases hsidon p.1 p.2 q.1 q.2 (mem_offDiag.mp hp'.1).2.2
        (hp'.2.trans hq'.2.symm) with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact mem_insert.mpr (Or.inl (Prod.ext h1 h2).symm)
      · exact mem_insert.mpr (Or.inr (mem_singleton.mpr (Prod.ext h2 h1).symm))
    exact (card_le_card hsub).trans card_le_two
  · have he : T = ∅ := not_nonempty_iff_eq_empty.mp hT
    change T.card ≤ 2
    simp [he]

omit [CharP K 2] in
/-- A finite pool for all distinct-pair sums bounds the parameter set. -/
theorem parameter_square_of_sidon [Fintype I] (t : I → Kˣ)
    (hsidon : SidonSums t)
    (S : Finset K) (hS : ∀ a b : I, a ≠ b → (t a : K)+(t b : K) ∈ S) :
    (Fintype.card I)^2 ≤ Fintype.card I+2*S.card := by
  classical
  let F : I × I → K := fun p => (t p.1 : K)+(t p.2 : K)
  have hbound := card_le_mul_card_image (f := F) (univ : Finset I).offDiag 2
    (fun u _ => sum_fiber_le_two_of_sidon t hsidon u)
  have hsub : ((univ : Finset I).offDiag.image F) ⊆ S := by
    intro u hu
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hu
    exact hS p.1 p.2 (mem_offDiag.mp hp).2.2
  have hcard := card_le_card hsub
  rw [offDiag_card,card_univ] at hbound
  have hle : Fintype.card I ≤ Fintype.card I*Fintype.card I := Nat.le_mul_self _
  have he := Nat.sub_add_cancel hle
  simp only [pow_two]
  omega

/-- On a translate of a finite additive subgroup U, the pool has size |U|.
Neither the ambient field nor the affine permutation group must be finite. -/
theorem translated_square_of_sidon [Fintype I] (t : I → Kˣ)
    (hsidon : SidonSums t)
    (U : AddSubgroup K) [Fintype U] (theta : K)
    (hU : ∀ i, (t i : K)-theta ∈ U) :
    (Fintype.card I)^2 ≤ Fintype.card I+2*Fintype.card U := by
  classical
  let S : Finset K := (univ : Finset U).image Subtype.val
  have hS : S.card ≤ Fintype.card U := by
    simpa only [card_univ] using (card_image_le (s := (univ : Finset U))
      (f := (Subtype.val : U → K)))
  have hp := parameter_square_of_sidon t hsidon S (fun a b _ => ?_)
  · omega
  · have hm : (t a : K)+(t b : K) ∈ U := by
      convert U.add_mem (hU a) (hU b) using 1
      ring_nf
      reduce_mod_char!
    exact mem_image.mpr ⟨⟨(t a : K)+(t b : K),hm⟩,mem_univ _,rfl⟩

/-- A fixed positive retained fraction is impossible as |U| grows. -/
theorem retained_fraction_of_sidon [Fintype I] (t : I → Kˣ)
    (hsidon : SidonSums t)
    (U : AddSubgroup K) [Fintype U] (theta : K)
    (hU : ∀ i, (t i : K)-theta ∈ U) (s : ℕ)
    (hs : Fintype.card U ≤ s*Fintype.card I) :
    Fintype.card U ≤ 2*s^2+s := by
  have hsq := translated_square_of_sidon t hsidon U theta hU
  have hk : Fintype.card I ≤ 2*s+1 := by
    nlinarith only [hs,hsq,sq_nonneg ((Fintype.card I : ℤ)-(2*s+1))]
  nlinarith only [hs,Nat.mul_le_mul_left s hk]


theorem parameter_square [Fintype I] (f : K →+ K) (t : I → Kˣ)
    (ht : Function.Injective t)
    (hf : (cycleGraph 8).Free (graph (fun i => curve f (t i))))
    (S : Finset K) (hS : ∀ a b : I, a ≠ b → (t a : K)+(t b : K) ∈ S) :
    (Fintype.card I)^2 ≤ Fintype.card I+2*S.card :=
  parameter_square_of_sidon t (sum_sidon f t ht hf) S hS

theorem translated_square [Fintype I] (f : K →+ K) (t : I → Kˣ)
    (ht : Function.Injective t)
    (hf : (cycleGraph 8).Free (graph (fun i => curve f (t i))))
    (U : AddSubgroup K) [Fintype U] (theta : K)
    (hU : ∀ i, (t i : K)-theta ∈ U) :
    (Fintype.card I)^2 ≤ Fintype.card I+2*Fintype.card U :=
  translated_square_of_sidon t (sum_sidon f t ht hf) U theta hU

theorem retained_fraction [Fintype I] (f : K →+ K) (t : I → Kˣ)
    (ht : Function.Injective t)
    (hf : (cycleGraph 8).Free (graph (fun i => curve f (t i))))
    (U : AddSubgroup K) [Fintype U] (theta : K)
    (hU : ∀ i, (t i : K)-theta ∈ U) (s : ℕ)
    (hs : Fintype.card U ≤ s*Fintype.card I) :
    Fintype.card U ≤ 2*s^2+s :=
  retained_fraction_of_sidon t (sum_sidon f t ht hf) U theta hU s hs

end Erdos713C8AdditiveAffineCount
