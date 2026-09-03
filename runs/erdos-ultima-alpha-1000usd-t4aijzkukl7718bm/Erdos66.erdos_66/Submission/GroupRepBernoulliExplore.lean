import Submission.VariableBernoulliBoundsExplore

/-! Finite Bernoulli representation counts on an additive group, including
mixed counts with a fixed set. A linear order is used only to enumerate
unordered pairs, not as an ordered-group structure. -/
namespace Erdos66GroupRepBernoulli
open Erdos66FiniteBernoulli Erdos66BernoulliConcentration
open scoped Classical
variable {G : Type*} [Fintype G] [AddCommGroup G] [LinearOrder G]
set_option maxHeartbeats 1500000

noncomputable def count (C D : Finset G) (z : G) : ℕ :=
  (C.filter (fun a ↦ z-a∈D)).card
noncomputable def selected (ω : G → Bool) : Finset G := Finset.univ.filter (fun a ↦ ω a=true)
noncomputable def pairs (z : G) : Finset (G × G) := Finset.univ.filter (fun a ↦ a.1+a.2=z)
noncomputable def halfPairs (z : G) : Finset (G × G) := (pairs z).filter (fun a ↦ a.1≤a.2)
noncomputable def pairCoords (a : G × G) : Finset G := {a.1,a.2}
noncomputable def pairWeight (a : G × G) : ℝ := if a.1=a.2 then 1 else 2

lemma mem_selected (ω : G → Bool) (a : G) : a∈selected ω ↔ ω a=true := by simp [selected]
lemma mem_pairs {z : G} {a : G × G} : a∈pairs z ↔ a.1+a.2=z := by simp [pairs]
lemma mem_halfPairs {z : G} {a : G × G} : a∈halfPairs z ↔ a.1+a.2=z ∧ a.1≤a.2 := by
  simp [halfPairs,mem_pairs]

lemma pairCoords_disjoint (z : G) : (halfPairs z : Set (G × G)).Pairwise
    (fun a b ↦ Disjoint (pairCoords a) (pairCoords b)) := by
  intro a ha b hb hab
  obtain ⟨ha',hlea⟩ := mem_halfPairs.mp ha
  obtain ⟨hb',hleb⟩ := mem_halfPairs.mp hb
  apply Finset.disjoint_left.mpr
  intro i hia hib
  simp only [pairCoords,Finset.mem_insert,Finset.mem_singleton] at hia hib
  have heq : a.1+a.2=b.1+b.2 := ha'.trans hb'.symm
  have hstraight (he : a.1=b.1) : False := by
    have he₂ : a.2=b.2 := add_left_cancel (by simpa only [he] using heq)
    exact hab (Prod.ext he he₂)
  have hcross (he : a.1=b.2) : False := by
    have he₂ : a.2=b.1 := add_left_cancel (by simpa only [he,add_comm b.1 b.2] using heq)
    have hh : a.1=b.1 := le_antisymm (by simpa only [he₂] using hlea) (by simpa only [he] using hleb)
    exact hstraight hh
  rcases hia with hia | hia <;> rcases hib with hib | hib
  · exact hstraight (hia.symm.trans hib)
  · exact hcross (hia.symm.trans hib)
  · have he₂ : a.2=b.1 := hia.symm.trans hib
    apply hcross
    exact add_right_cancel (by simpa only [he₂,add_comm b.1 b.2] using heq)
  · have he₂ : a.2=b.2 := hia.symm.trans hib
    apply hstraight
    exact add_right_cancel (by simpa only [he₂] using heq)

lemma pairWeight_bounds (a : G × G) : 0 ≤ pairWeight a ∧ pairWeight a ≤ 2 := by
  unfold pairWeight
  split_ifs <;> norm_num

lemma symmetric_sum (z : G) (f : (G × G) → ℝ) (hf : ∀ a, f a.swap=f a) :
    (∑ a∈pairs z, f a) = ∑ a∈halfPairs z, pairWeight a*f a := by
  have hswap : (∑ a∈(pairs z).filter (fun a ↦ ¬a.1≤a.2), f a) =
      ∑ a∈(pairs z).filter (fun a ↦ a.1<a.2), f a := by
    apply Finset.sum_equiv (Equiv.prodComm _ _)
    · intro a
      simp only [Finset.mem_filter,mem_pairs,Equiv.prodComm_apply,Prod.fst_swap,Prod.snd_swap]
      constructor
      · rintro ⟨h,hl⟩; exact ⟨by simpa only [add_comm] using h,lt_of_not_ge hl⟩
      · rintro ⟨h,hl⟩; exact ⟨by simpa only [add_comm] using h,not_le_of_gt hl⟩
    · intro a ha; exact (hf a).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not (pairs z) (fun a ↦ a.1≤a.2) f
  rw [hswap] at hsplit
  rw [←hsplit]
  change (∑ a∈halfPairs z, f a)+_= _
  have hstrict : (pairs z).filter (fun a ↦ a.1<a.2) =
      (halfPairs z).filter (fun a ↦ a.1≠a.2) := by
    ext a
    simp only [Finset.mem_filter,halfPairs]
    constructor
    · rintro ⟨ha,hl⟩; exact ⟨⟨ha,hl.le⟩,ne_of_lt hl⟩
    · rintro ⟨⟨ha,hl⟩,he⟩; exact ⟨ha,lt_of_le_of_ne hl he⟩
  rw [hstrict,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases he : a.1=a.2 <;> simp [pairWeight,he] <;> ring

lemma sum_pairs (z : G) (f : G × G → ℝ) :
    (∑ a∈pairs z, f a) = ∑ x : G, f (x,z-x) := by
  symm
  apply Finset.sum_bij (fun x _ ↦ (x,z-x))
  · intro x hx; exact mem_pairs.mpr (by simp)
  · intro x hx y hy he; exact congrArg Prod.fst he
  · intro a ha
    have he : a.2=z-a.1 := eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using mem_pairs.mp ha)
    exact ⟨a.1,Finset.mem_univ _,Prod.ext rfl he.symm⟩
  · intro x hx; rfl

lemma pair_monomial (a : G × G) (ω : G → Bool) :
    monomial (pairCoords a) ω=bit (ω a.1)*bit (ω a.2) := by
  by_cases he : a.1=a.2
  · cases hw : ω a.2 <;> simp [monomial,pairCoords,he,bit,hw]
  · simp [monomial,pairCoords,he]

lemma selected_self (z : G) (ω : G → Bool) :
    (count (selected ω) (selected ω) z : ℝ) =
      ∑ a∈halfPairs z, pairWeight a*monomial (pairCoords a) ω := by
  have hh : (count (selected ω) (selected ω) z : ℝ)=∑ x : G, bit (ω x)*bit (ω (z-x)) := by
    simp only [count,selected,Finset.filter_filter,Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro a ha
    cases h₁ : ω a <;> cases h₂ : ω (z-a) <;> simp [bit,h₁,h₂]
  rw [hh,←sum_pairs z (fun a ↦ bit (ω a.1)*bit (ω a.2)),
    symmetric_sum z _ (fun a ↦ mul_comm _ _)]
  simp_rw [pair_monomial]

noncomputable def selfMean (z : G) (p : G → ℝ) : ℝ :=
  ∑ a∈halfPairs z, pairWeight a*∏ i∈pairCoords a, p i

lemma self_mgf (z : G) (p : G → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (t : ℝ) (ht : |t| ≤ 1/2) :
    expect p (fun ω ↦ Real.exp (t*((count (selected ω) (selected ω) z : ℝ)-selfMean z p))) ≤
      Real.exp (2*t^2*selfMean z p) := by
  simp_rw [selected_self]
  exact centered_mgf_bound p hp (halfPairs z) pairCoords (pairCoords_disjoint z)
    pairWeight (fun a _ ↦ pairWeight_bounds a) t ht

noncomputable def diagCorrection (z : G) (p : G → ℝ) : ℝ :=
  ∑ a∈(halfPairs z).filter (fun a ↦ a.1=a.2), (p a.1-p a.1^2)

lemma selfMean_decomposition (z : G) (p : G → ℝ) :
    selfMean z p=(∑ x : G, p x*p (z-x))+diagCorrection z p := by
  rw [selfMean,←sum_pairs z (fun a ↦ p a.1*p a.2),
    symmetric_sum z _ (fun a ↦ mul_comm _ _),diagCorrection,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases he : a.1=a.2
  · simp [pairWeight,pairCoords,he]; ring
  · simp [pairWeight,pairCoords,he]

lemma diagCorrection_bounds (hinj : Function.Injective (fun a : G ↦ a+a))
    (z : G) (p : G → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    0 ≤ diagCorrection z p ∧ diagCorrection z p ≤ 1 := by
  have hterm (i : G) : 0 ≤ p i-p i^2 ∧ p i-p i^2 ≤ 1 := by
    have hh := mul_nonneg (hp i).1 (sub_nonneg.mpr (hp i).2)
    constructor <;> nlinarith [(hp i).2,sq_nonneg (p i)]
  have hc : ((halfPairs z).filter (fun a ↦ a.1=a.2)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨ha,hae⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb,hbe⟩ := Finset.mem_filter.mp hb
    have he : a.1=b.1 := hinj (by simpa only [←hae,←hbe] using (mem_halfPairs.mp ha).1.trans (mem_halfPairs.mp hb).1.symm)
    exact Prod.ext he (hae.symm.trans (he.trans hbe))
  constructor
  · exact Finset.sum_nonneg (fun a ha ↦ (hterm a.1).1)
  · have hh := Finset.sum_le_sum (s := (halfPairs z).filter (fun a ↦ a.1=a.2)) (fun a ha ↦ (hterm a.1).2)
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hh
    exact hh.trans (by exact_mod_cast hc)

lemma mixed_selected (C : Finset G) (z : G) (ω : G → Bool) :
    (count C (selected ω) z : ℝ)=∑ a∈C, bit (ω (z-a)) := by
  simp only [count,Finset.card_filter,mem_selected]
  push_cast
  apply Finset.sum_congr rfl
  intro a ha
  cases hw : ω (z-a) <;> simp [bit,hw]

lemma mixed_mgf (C : Finset G) (z : G) (p : G → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (t : ℝ) (ht : |t| ≤ 1/2) :
    expect p (fun ω ↦ Real.exp (t*((count C (selected ω) z : ℝ)-∑ a∈C, p (z-a)))) ≤
      Real.exp (2*t^2*(∑ a∈C, p (z-a))) := by
  have hdis : (C : Set G).Pairwise (fun a b ↦ Disjoint ({z-a} : Finset G) {z-b}) := by
    intro a ha b hb hab
    simp only [Finset.disjoint_singleton]
    exact fun he ↦ hab (sub_right_injective he)
  have hh := centered_mgf_bound p hp C (fun a ↦ {z-a}) hdis (fun _ ↦ 1)
    (by intro a ha; norm_num) t ht
  simpa only [mixed_selected,monomial,Finset.prod_singleton,one_mul] using hh

lemma selected_card (ω : G → Bool) : ((selected ω).card : ℝ)=∑ a : G, bit (ω a) := by
  simp only [selected,Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro a ha
  cases hw : ω a <;> simp [bit,hw]

lemma card_mgf (p : G → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (t : ℝ) (ht : |t| ≤ 1/2) :
    expect p (fun ω ↦ Real.exp (t*(((selected ω).card : ℝ)-∑ a : G, p a))) ≤
      Real.exp (2*t^2*(∑ a : G, p a)) := by
  have hdis : ((Finset.univ : Finset G) : Set G).Pairwise (fun a b ↦ Disjoint ({a} : Finset G) {b}) := by
    intro a ha b hb hab
    simpa using hab
  have hh := centered_mgf_bound p hp Finset.univ (fun a : G ↦ {a}) hdis (fun _ ↦ 1)
    (by intro a ha; norm_num) t ht
  simpa only [selected_card,monomial,Finset.prod_singleton,one_mul] using hh

end Erdos66GroupRepBernoulli
