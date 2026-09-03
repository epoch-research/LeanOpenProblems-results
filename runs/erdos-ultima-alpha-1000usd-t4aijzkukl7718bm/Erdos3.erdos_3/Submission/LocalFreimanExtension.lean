import Submission.HigherFreimanExtraction

/-! Extending a sufficiently high-order Freiman map to a locally additive map
on mH-mH. The consistency and additivity requirements use orders 2m and 3m. -/
namespace Erdos3LocalFreimanExtension
open Finset Erdos3HigherFreimanRestriction
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 4000000

variable {G L : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup L]

lemma exists_multiset_of_mem_nsmul (H : Finset G) (m : ℕ) {x : G} (hx : x ∈ m • H) :
    ∃ s : Multiset G, (∀ a ∈ s, a ∈ H) ∧ s.card = m ∧ s.sum = x := by
  induction m generalizing x with
  | zero =>
    have hx0 : x = 0 := by simpa using hx
    exact ⟨0,by simp,by simp,by simp [hx0]⟩
  | succ m ih =>
    rw [add_nsmul,one_nsmul] at hx
    obtain ⟨a,ha,b,hb,hab⟩ := mem_add.mp hx
    obtain ⟨s,hs,hsc,hss⟩ := ih ha
    refine ⟨b ::ₘ s,?_,by simp [hsc],?_⟩
    · intro c hc
      rcases Multiset.mem_cons.mp hc with rfl | hc
      · exact hb
      · exact hs c hc
    · simpa only [Multiset.sum_cons,hss,add_comm] using hab

structure DifferenceRep (H : Finset G) (m : ℕ) (x : G) where
  pos : Multiset G
  neg : Multiset G
  pos_mem : ∀ a ∈ pos, a ∈ H
  neg_mem : ∀ a ∈ neg, a ∈ H
  pos_card : pos.card = m
  neg_card : neg.card = m
  eq_sub : pos.sum-neg.sum = x

namespace DifferenceRep

def value {H : Finset G} {m : ℕ} {x : G} (f : G → L) (r : DifferenceRep H m x) : L :=
  (r.pos.map f).sum-(r.neg.map f).sum

lemma nonempty_iff (H : Finset G) (m : ℕ) (x : G) : Nonempty (DifferenceRep H m x) ↔ x ∈ m • H-m • H := by
  constructor
  · rintro ⟨r⟩
    exact mem_sub.mpr ⟨r.pos.sum,by simpa only [r.pos_card] using multiset_sum_mem_nsmul H r.pos r.pos_mem,
      r.neg.sum,by simpa only [r.neg_card] using multiset_sum_mem_nsmul H r.neg r.neg_mem,r.eq_sub⟩
  · intro hx
    obtain ⟨a,ha,b,hb,hab⟩ := mem_sub.mp hx
    obtain ⟨s,hs,hsc,hss⟩ := exists_multiset_of_mem_nsmul H m ha
    obtain ⟨t,ht,htc,htt⟩ := exists_multiset_of_mem_nsmul H m hb
    exact ⟨⟨s,t,hs,ht,hsc,htc,by simpa only [hss,htt] using hab⟩⟩

lemma value_eq {H : Finset G} {m : ℕ} {f : G → L}
    (hf : IsAddFreimanHom (2*m) (H : Set G) Set.univ f) {x : G} (r s : DifferenceRep H m x) :
    r.value f = s.value f := by
  have hsum : (r.pos+s.neg).sum = (s.pos+r.neg).sum := by
    rw [Multiset.sum_add,Multiset.sum_add]
    exact sub_eq_sub_iff_add_eq_add.mp (r.eq_sub.trans s.eq_sub.symm)
  have hh := hf.map_sum_eq_map_sum (s := r.pos+s.neg) (t := s.pos+r.neg)
    (by intro a ha; rcases Multiset.mem_add.mp ha with ha | ha; exact r.pos_mem a ha; exact s.neg_mem a ha)
    (by intro a ha; rcases Multiset.mem_add.mp ha with ha | ha; exact s.pos_mem a ha; exact r.neg_mem a ha)
    (by rw [Multiset.card_add,r.pos_card,s.neg_card]; omega)
    (by rw [Multiset.card_add,s.pos_card,r.neg_card]; omega) hsum
  simp only [Multiset.map_add,Multiset.sum_add] at hh
  exact sub_eq_sub_iff_add_eq_add.mpr hh

lemma value_add {H : Finset G} {m : ℕ} {f : G → L}
    (hf : IsAddFreimanHom (3*m) (H : Set G) Set.univ f) {x y : G}
    (r : DifferenceRep H m x) (s : DifferenceRep H m y) (t : DifferenceRep H m (x+y)) :
    t.value f = r.value f+s.value f := by
  have he : r.pos.sum-r.neg.sum+(s.pos.sum-s.neg.sum) = t.pos.sum-t.neg.sum := by
    rw [r.eq_sub,s.eq_sub,t.eq_sub]
  rw [sub_add_sub_comm,sub_eq_sub_iff_add_eq_add] at he
  have hsum : ((r.pos+s.pos)+t.neg).sum = (t.pos+(r.neg+s.neg)).sum := by
    simpa only [Multiset.sum_add] using he
  have hh := hf.map_sum_eq_map_sum (s := (r.pos+s.pos)+t.neg) (t := t.pos+(r.neg+s.neg))
    (by
      intro a ha
      rcases Multiset.mem_add.mp ha with ha | ha
      · rcases Multiset.mem_add.mp ha with ha | ha
        · exact r.pos_mem a ha
        · exact s.pos_mem a ha
      · exact t.neg_mem a ha)
    (by
      intro a ha
      rcases Multiset.mem_add.mp ha with ha | ha
      · exact t.pos_mem a ha
      · rcases Multiset.mem_add.mp ha with ha | ha
        · exact r.neg_mem a ha
        · exact s.neg_mem a ha)
    (by simp only [Multiset.card_add,r.pos_card,s.pos_card,t.neg_card]; omega)
    (by simp only [Multiset.card_add,t.pos_card,r.neg_card,s.neg_card]; omega) hsum
  simp only [Multiset.map_add,Multiset.sum_add] at hh
  unfold value
  rw [sub_add_sub_comm,sub_eq_sub_iff_add_eq_add]
  exact hh.symm

end DifferenceRep

noncomputable def differenceExtension (H : Finset G) (m : ℕ) (f : G → L) (x : G) : L :=
  if hx : Nonempty (DifferenceRep H m x) then (Classical.choice hx).value f else 0

lemma differenceExtension_eq_value {H : Finset G} {m : ℕ} {f : G → L}
    (hf : IsAddFreimanHom (2*m) (H : Set G) Set.univ f) {x : G} (r : DifferenceRep H m x) :
    differenceExtension H m f x = r.value f := by
  rw [differenceExtension,dif_pos (show Nonempty (DifferenceRep H m x) from ⟨r⟩)]
  exact DifferenceRep.value_eq hf _ r

lemma differenceExtension_add {H : Finset G} {m : ℕ} {f : G → L}
    (hf : IsAddFreimanHom (3*m) (H : Set G) Set.univ f) {x y : G}
    (hx : x ∈ m • H-m • H) (hy : y ∈ m • H-m • H) (hxy : x+y ∈ m • H-m • H) :
    differenceExtension H m f (x+y) = differenceExtension H m f x+differenceExtension H m f y := by
  obtain ⟨r⟩ := (DifferenceRep.nonempty_iff H m x).mpr hx
  obtain ⟨s⟩ := (DifferenceRep.nonempty_iff H m y).mpr hy
  obtain ⟨t⟩ := (DifferenceRep.nonempty_iff H m (x+y)).mpr hxy
  have hf2 := hf.mono (by omega : 2*m ≤ 3*m)
  rw [differenceExtension_eq_value hf2 r,differenceExtension_eq_value hf2 s,differenceExtension_eq_value hf2 t]
  exact DifferenceRep.value_add hf r s t

lemma differenceExtension_zero {H : Finset G} {m : ℕ} {f : G → L}
    (hf : IsAddFreimanHom (2*m) (H : Set G) Set.univ f) : differenceExtension H m f 0 = 0 := by
  by_cases hr : Nonempty (DifferenceRep H m 0)
  · obtain ⟨r⟩ := hr
    let s : DifferenceRep H m 0 := ⟨r.pos,r.pos,r.pos_mem,r.pos_mem,r.pos_card,r.pos_card,sub_self _⟩
    rw [differenceExtension_eq_value hf s]
    exact sub_self _
  · simp only [differenceExtension,dif_neg hr]

lemma differenceExtension_sub {H : Finset G} {m : ℕ} (hm : 0 < m) {f : G → L}
    (hf : IsAddFreimanHom (2*m) (H : Set G) Set.univ f) {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    differenceExtension H m f (a-b) = f a-f b := by
  let u : Multiset G := Multiset.replicate (m-1) b
  have hu : ∀ x ∈ u, x ∈ H := by
    intro x hx
    exact (Multiset.eq_of_mem_replicate hx) ▸ hb
  let r : DifferenceRep H m (a-b) :=
    ⟨a ::ₘ u,b ::ₘ u,
      (by intro x hx; rcases Multiset.mem_cons.mp hx with rfl | hx; exact ha; exact hu x hx),
      (by intro x hx; rcases Multiset.mem_cons.mp hx with rfl | hx; exact hb; exact hu x hx),
      (by simp only [Multiset.card_cons,u,Multiset.card_replicate]; omega),
      (by simp only [Multiset.card_cons,u,Multiset.card_replicate]; omega),
      (by simp only [Multiset.sum_cons]; abel)⟩
  rw [differenceExtension_eq_value hf r]
  simp only [DifferenceRep.value,r,Multiset.map_cons,Multiset.sum_cons]
  abel

/-- A 3m-Freiman map gives a well-defined locally additive extension on mH-mH,
which agrees with the original frequency differences on H-H. -/
theorem exists_local_additive_extension (H : Finset G) (m : ℕ) (hm : 0 < m) (f : G → L)
    (hf : IsAddFreimanHom (3*m) (H : Set G) Set.univ f) :
    ∃ F : G → L, F 0 = 0 ∧
      (∀ a ∈ H, ∀ b ∈ H, F (a-b) = f a-f b) ∧
      (∀ x ∈ m • H-m • H, ∀ y ∈ m • H-m • H,
        x+y ∈ m • H-m • H → F (x+y) = F x+F y) := by
  have hf2 := hf.mono (by omega : 2*m ≤ 3*m)
  exact ⟨differenceExtension H m f,differenceExtension_zero hf2,
    fun _ ha _ hb ↦ differenceExtension_sub hm hf2 ha hb,
    fun _ hx _ hy hxy ↦ differenceExtension_add hf hx hy hxy⟩

#print axioms exists_local_additive_extension
end Erdos3LocalFreimanExtension
