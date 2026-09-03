import Submission.SamplingVariance

/-! Sampling a finite natural-number prefix, with exact cardinality and moment
identities for its subsets. -/
namespace Erdos1206.PrefixSampling
open Finset FiniteProductSampling
open scoped BigOperators Classical

noncomputable def lift (M : ℕ) (e : Finset ℕ) : Finset (Fin M) :=
  univ.filter (fun v => v.val∈e)

@[simp] lemma mem_lift {M : ℕ} {e : Finset ℕ} {v : Fin M} : v∈lift M e ↔ v.val∈e := by
  simp [lift]

lemma lift_card_le (M : ℕ) (e : Finset ℕ) : (lift M e).card ≤ e.card := by
  apply card_le_card_of_injOn Fin.val (fun v hv => mem_lift.mp hv)
  exact fun _ _ _ _ h => Fin.ext h

lemma lift_card {M : ℕ} {e : Finset ℕ} (he : e ⊆ range M) : (lift M e).card=e.card := by
  apply card_nbij Fin.val (fun v hv => mem_lift.mp hv) (fun _ _ _ _ h => Fin.ext h)
  intro n hn
  refine ⟨⟨n,mem_range.mp (he hn)⟩,?_,rfl⟩
  exact mem_lift.mpr hn

noncomputable def label {M k : ℕ} [NeZero k] (ω : Fin M → Fin k) (n : ℕ) : Fin k :=
  if h : n < M then ω ⟨n,h⟩ else 0

@[simp] lemma label_fin {M k : ℕ} [NeZero k] (ω : Fin M → Fin k) (v : Fin M) :
    label ω v.val=ω v := by simp [label,v.isLt]

noncomputable def chosen {M k : ℕ} [NeZero k] (ω : Fin M → Fin k) (e : Finset ℕ) : Finset ℕ :=
  e.filter (fun n => label ω n=0)

lemma event_lift {M k : ℕ} [NeZero k] {e : Finset ℕ} (he : e ⊆ range M)
    (ω : Fin M → Fin k) :
    event (lift M e) ω=if ∀ n∈e, label ω n=0 then 1 else 0 := by
  have hh : (∀ v∈lift M e, ω v=0) ↔ (∀ n∈e, label ω n=0) := by
    constructor
    · intro h n hn
      have hnM := mem_range.mp (he hn)
      simpa only [label,dif_pos hnM] using h ⟨n,hnM⟩ (mem_lift.mpr hn)
    · intro h v hv
      simpa only [label_fin] using h v.val (mem_lift.mp hv)
  dsimp only [event]
  split_ifs <;> first | rfl | (exfalso; tauto)

lemma chosen_card_eq {M k : ℕ} [NeZero k] {e : Finset ℕ} (he : e ⊆ range M)
    (ω : Fin M → Fin k) :
    ((chosen ω e).card:ℝ)=∑ v∈lift M e, event {v} ω := by
  have hc : chosen ω e ⊆ range M := (filter_subset _ _).trans he
  rw [←lift_card hc]
  have hl : lift M (chosen ω e)=(lift M e).filter (fun v => ω v=0) := by
    ext v
    simp [chosen]
  rw [hl]
  simp only [event,mem_singleton,forall_eq,sum_boole]

lemma centered_sum_eq {M k : ℕ} [NeZero k] {e : Finset ℕ} (he : e ⊆ range M)
    (ω : Fin M → Fin k) :
    (∑ v∈lift M e, centered {v} ω)=((chosen ω e).card:ℝ)-(e.card:ℝ)/k := by
  simp only [centered,sum_sub_distrib,card_singleton,pow_one,sum_const,nsmul_eq_mul,
    lift_card he,chosen_card_eq he ω]
  ring

/-- Independent coordinate sampling has variance at most the source size. -/
theorem chosen_variance {M k : ℕ} [NeZero k] {e : Finset ℕ} (he : e ⊆ range M) :
    (𝔼 ω : Fin M → Fin k, (((chosen ω e).card:ℝ)-(e.card:ℝ)/k)^2) ≤ e.card := by
  have hsize (v : Fin M) (_hv : v∈lift M e) : ({v} : Finset (Fin M)).card ≤ 1 := by simp
  have hdeg (v : Fin M) : ((lift M e).filter (fun w => v∈({w} : Finset (Fin M)))).card ≤ 1 := by
    apply le_trans (card_le_card (t := {v}) ?_) (by simp)
    intro w hw
    have hvw := (mem_filter.mp hw).2
    simpa only [mem_singleton,eq_comm] using hvw
  have hh := SamplingVariance.variance_le (k := k) (r := 1) (D := 1) (lift M e) (fun v => ({v} : Finset (Fin M))) hsize hdeg
  simpa only [centered_sum_eq he,lift_card he,Nat.cast_one,mul_one] using hh

/-- Natural-number supports can be lifted without changing their sizes or
coordinate degrees when they lie inside the sampled prefix. -/
theorem family_variance {I : Type*} {M k : ℕ} [NeZero k]
    (E : Finset I) (F : I → Finset ℕ) {r D : ℕ}
    (hr : ∀ i∈E, (F i).card ≤ r)
    (hD : ∀ v, (E.filter (fun i => v∈F i)).card ≤ D) :
    (𝔼 ω : Fin M → Fin k, (∑ i∈E, centered (lift M (F i)) ω)^2) ≤ (E.card:ℝ)*r*D := by
  apply SamplingVariance.variance_le (k := k) (r := r) (D := D) E (fun i => lift M (F i))
  · intro i hi
    exact (lift_card_le _ _).trans (hr i hi)
  · intro v
    simpa only [mem_lift] using hD v.val

#print axioms chosen_variance
#print axioms family_variance
end Erdos1206.PrefixSampling
