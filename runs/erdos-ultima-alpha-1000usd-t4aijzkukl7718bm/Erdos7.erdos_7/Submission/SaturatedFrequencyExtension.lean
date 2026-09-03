import Submission.Reachability945Certificate

/-!
# Saturated frequency prefixes and prime extensions

A fixed saturated prefix has a sharp quotient-size extension limit. This is a
limitation of that induction strategy, not a resolution of Erdős7.
-/

namespace Erdos7SaturatedExtension
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 100000

def ZeroFree {I G : Type*} [AddCommMonoid G] (v : I → G) : Prop :=
  ∀ s : Finset I, s.Nonempty → ∑ i ∈ s, v i ≠ 0

def Saturated {I G : Type*} [AddCommMonoid G] (v : I → G) : Prop :=
  ∀ x : G, ∃ s : Finset I, ∑ i ∈ s, v i = x

/-- Reverse transitions certify actual subset representations. Forward closure
alone, as in an overapproximation certificate, would not justify this conclusion. -/
theorem represented_of_backward {G : Type*} [AddCommGroup G] {L : ℕ}
    (v : Fin L → G) (R : ℕ → G → Prop)
    (hbase : ∀ x, R 0 x → x=0)
    (hback : ∀ i : Fin L, ∀ x, R (i.val+1) x → R i.val x ∨ R i.val (x-v i)) :
    ∀ j, j ≤ L → ∀ x, R j x →
      ∃ s : Finset (Fin L), (∀ i ∈ s, i.val < j) ∧ ∑ i ∈ s, v i = x := by
  classical
  intro j
  induction j with
  | zero =>
    intro hj x hx
    refine ⟨∅,by simp,?_⟩
    simp [hbase x hx]
  | succ j ih =>
    intro hj x hx
    let i : Fin L := ⟨j,by omega⟩
    have hjL : j ≤ L := by omega
    rcases hback i x hx with h | h
    · obtain ⟨s,hs,hx⟩ := ih hjL x h
      exact ⟨s,fun t ht => (hs t ht).trans_le (by omega),hx⟩
    · obtain ⟨s,hs,hx⟩ := ih hjL (x-v i) h
      have hin : i ∉ s := by intro hi; have := hs i hi; change j < j at this; omega
      refine ⟨insert i s, ?_, ?_⟩
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact Nat.lt_succ_self j
        · exact (hs t ht).trans_le (by omega)
      · rw [Finset.sum_insert hin,hx]
        simp [sub_eq_add_neg,add_left_comm]

/-- A zero-sum-free sequence in a finite group has fewer terms than the group
has elements. Prefix sums give the required injection. -/
theorem zero_free_card_lt {G : Type*} [AddCommGroup G] [Fintype G] {L : ℕ}
    (v : Fin L → G) (hv : ZeroFree v) : L < Fintype.card G := by
  classical
  let pref (j : Fin (L+1)) := ∑ i ∈ Finset.univ.filter (fun i : Fin L => i.val < j.val), v i
  have hneq (j l : Fin (L+1)) (hjl : j < l) : pref j ≠ pref l := by
    intro he
    let A := Finset.univ.filter (fun i : Fin L => i.val < j.val)
    let B := Finset.univ.filter (fun i : Fin L => i.val < l.val)
    have hsub : A ⊆ B := by
      intro i hi
      simp only [A,B,Finset.mem_filter,Finset.mem_univ,true_and] at *
      exact hi.trans hjl
    let i : Fin L := ⟨j.val,by have := l.isLt; change j.val < l.val at hjl; omega⟩
    have hne : (B \ A).Nonempty := by
      refine ⟨i,?_⟩
      simp only [Finset.mem_sdiff,B,A,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hjl,lt_irrefl _⟩
    have hh := Finset.sum_sdiff (f := v) hsub
    have he' : (∑ t ∈ A, v t) = ∑ t ∈ B, v t := he
    have hz : (∑ t ∈ B \ A, v t)=0 := by
      apply add_right_cancel (b := ∑ t ∈ A, v t)
      simpa only [zero_add] using hh.trans he'.symm
    exact hv (B \ A) hne hz
  have hinj : Function.Injective pref := by
    intro j l he
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hneq j l h he
    · exact hneq l j h he.symm
  have hcard := Fintype.card_le_of_injective pref hinj
  simp only [Fintype.card_fin] at hcard
  omega

/-- If old subset sums fill the kernel, every zero sum among projected new
terms lifts to a nonempty zero sum in the combined sequence. -/
theorem quotient_zero_free {I J G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (v : I → G) (w : J → G)
    (hsat : ∀ x, f x=0 → ∃ s : Finset I, ∑ i ∈ s, v i=x)
    (hfree : ZeroFree (Sum.elim v w)) : ZeroFree (fun j => f (w j)) := by
  classical
  intro t ht hz
  have hz' : f (-(∑ j ∈ t, w j))=0 := by
    rw [map_neg,map_sum,hz,neg_zero]
  obtain ⟨s,hs⟩ := hsat _ hz'
  have hne : (s.disjSum t).Nonempty := by
    obtain ⟨j,hj⟩ := ht
    exact ⟨Sum.inr j,by simpa using hj⟩
  apply hfree (s.disjSum t) hne
  rw [Finset.sum_disjSum]
  simpa only [Sum.elim_inl,Sum.elim_inr,hs,neg_add_cancel]

/-- Sharp upper bound for the number of new terms over a saturated kernel. -/
theorem extension_card_lt {I G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype H] {L : ℕ} (f : G →+ H) (v : I → G) (w : Fin L → G)
    (hsat : ∀ x, f x=0 → ∃ s : Finset I, ∑ i ∈ s, v i=x)
    (hfree : ZeroFree (Sum.elim v w)) : L < Fintype.card H :=
  zero_free_card_lt _ (quotient_zero_free f v w hsat hfree)

/-- For a saturated prefix in the first factor, the quotient bound is p-1. -/
theorem product_extension_bound {I G : Type*} [AddCommGroup G] {p L : ℕ} [NeZero p]
    (v : I → G) (hsat : Saturated v) (w : Fin L → G × ZMod p)
    (hfree : ZeroFree (Sum.elim (fun i => (v i,(0 : ZMod p))) w)) : L < p := by
  have hkernel : ∀ z : G × ZMod p, (AddMonoidHom.snd G (ZMod p)) z=0 →
      ∃ s : Finset I, ∑ i ∈ s, (v i,(0 : ZMod p))=z := by
    intro z hz
    obtain ⟨s,hs⟩ := hsat z.1
    refine ⟨s,Prod.ext ?_ ?_⟩
    · simpa only [Prod.fst_sum] using hs
    · simpa only [Prod.snd_sum,Finset.sum_const_zero] using hz.symm
  have h := extension_card_lt (AddMonoidHom.snd G (ZMod p))
    (fun i => (v i,(0 : ZMod p))) w hkernel hfree
  simpa only [ZMod.card] using h

/-- Zero-free sequences in independent factors can be combined. -/
theorem independent_product {I J G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (v : I → G) (w : J → H) (hv : ZeroFree v) (hw : ZeroFree w) :
    ZeroFree (Sum.elim (fun i => (v i,(0 : H))) (fun j => ((0 : G),w j))) := by
  classical
  intro s hs hz
  rw [Finset.sum_sum_eq_sum_toLeft_add_sum_toRight] at hz
  have hfst := congrArg Prod.fst hz
  have hsnd := congrArg Prod.snd hz
  simp only [Prod.fst_add,Prod.fst_sum,Prod.fst_zero,Sum.elim_inl,Sum.elim_inr,
    Finset.sum_const_zero,add_zero] at hfst
  simp only [Prod.snd_add,Prod.snd_sum,Prod.snd_zero,Sum.elim_inl,Sum.elim_inr,
    Finset.sum_const_zero,zero_add] at hsnd
  have hl : s.toLeft=∅ := by
    by_contra hn
    exact hv s.toLeft (Finset.nonempty_iff_ne_empty.mpr hn) hfst
  have hr : s.toRight=∅ := by
    by_contra hn
    exact hw s.toRight (Finset.nonempty_iff_ne_empty.mpr hn) hsnd
  have he := Finset.toLeft_disjSum_toRight (u := s)
  rw [hl,hr] at he
  exact hs.ne_empty (by simpa using he.symm)

lemma ones_zero_free {p L : ℕ} [NeZero p] (hL : L < p) :
    ZeroFree (fun _ : Fin L => (1 : ZMod p)) := by
  intro s hs hz
  have hcard : (s.card : ZMod p)=0 := by simpa using hz
  have hdiv : p ∣ s.card := (ZMod.natCast_eq_zero_iff _ _).mp hcard
  have hbound : s.card ≤ L := by simpa using Finset.card_le_univ s
  have he : s.card=0 := Nat.eq_zero_of_dvd_of_lt hdiv (lt_of_le_of_lt hbound hL)
  exact hs.ne_empty (Finset.card_eq_zero.mp he)

/-- The fixed saturated-prefix bound is SHARP. The sufficient direction does
not need saturation: append fewer than p copies of the new quotient generator. -/
theorem fixed_extension_iff {I G : Type*} [AddCommGroup G] {p L : ℕ} [NeZero p]
    (v : I → G) (hv : ZeroFree v) (hsat : Saturated v) :
    (∃ w : Fin L → G × ZMod p,
      ZeroFree (Sum.elim (fun i => (v i,(0 : ZMod p))) w)) ↔ L < p := by
  constructor
  · rintro ⟨w,hw⟩
    exact product_extension_bound v hsat w hw
  · intro hL
    exact ⟨fun _ => (0,1),independent_product v (fun _ : Fin L => (1 : ZMod p))
      hv (ones_zero_free hL)⟩

section Verified945
open Erdos7Reachability945

lemma base_exact : ∀ x : ZMod 945, Reach 0 x → x=0 := by
  unfold Reach
  decide +kernel

lemma backward : ∀ i : Fin 15, ∀ x : ZMod 945,
    Reach (i.val+1) x → Reach i.val x ∨ Reach i.val (x-frequency i) := by
  unfold Reach
  decide +kernel

lemma final_full : ∀ x : ZMod 945, Reach 15 x := by
  unfold Reach
  decide +kernel

/-- Actual saturation, not just a fully marked overapproximation. -/
theorem saturated945 : Saturated frequency := by
  intro x
  obtain ⟨s,hs,hx⟩ := represented_of_backward frequency Reach base_exact backward
    15 (by omega) x (final_full x)
  exact ⟨s,hx⟩

/-- Keeping the verified945 prefix fixed, no eleven new terms can be adjoined
in the product with a group of order11. New terms are otherwise unrestricted. -/
theorem no_eleven_extension : ¬ ∃ w : Fin 11 → ZMod 945 × ZMod 11,
    ZeroFree (Sum.elim (fun i => (frequency i,(0 : ZMod 11))) w) := by
  rintro ⟨w,hw⟩
  have h := product_extension_bound frequency saturated945 w hw
  omega

/-- A new prime11 introduces16 new divisor labels, exceeding the sharp bound.
This refutes ONLY fixed-prefix extension, not another global selection. -/
theorem no_sixteen_extension : ¬ ∃ w : Fin 16 → ZMod 945 × ZMod 11,
    ZeroFree (Sum.elim (fun i => (frequency i,(0 : ZMod 11))) w) := by
  rintro ⟨w,hw⟩
  have h := product_extension_bound frequency saturated945 w hw
  omega

/-- Sixteen new terms DO extend this same fixed prefix over a quotient of
order17. Thus the order11 failure must not be claimed for all larger primes. -/
theorem seventeen_extension :
    ZeroFree (Sum.elim (fun i => (frequency i,(0 : ZMod 17)))
      (fun _ : Fin 16 => ((0 : ZMod 945),(1 : ZMod 17)))) :=
  independent_product frequency (fun _ : Fin 16 => (1 : ZMod 17))
    Erdos7Reachability945.zero_free (ones_zero_free (by decide))

end Verified945

#print axioms represented_of_backward
#print axioms zero_free_card_lt
#print axioms quotient_zero_free
#print axioms extension_card_lt
#print axioms product_extension_bound
#print axioms independent_product
#print axioms ones_zero_free
#print axioms fixed_extension_iff
#print axioms saturated945
#print axioms no_eleven_extension
#print axioms no_sixteen_extension
#print axioms seventeen_extension
end Erdos7SaturatedExtension
