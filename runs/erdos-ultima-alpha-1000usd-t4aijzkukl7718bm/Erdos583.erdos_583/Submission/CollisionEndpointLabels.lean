import Submission.NearCompletePairs

/-! A finite endpoint map with two exceptional labels can be repaired by
replacing one copy of its unique repeated exceptional label. -/
namespace Erdos583CollisionEndpointLabelsDevelopment
open SimpleGraph Erdos583Work
open Erdos583Work.QuotaTrails Erdos583Work.QuotaSurgery
open Erdos583NearCompletePairsDevelopment
open scoped Classical
set_option maxHeartbeats 1800000
set_option Elab.async false

lemma repair_two_exceptional_labels {I V : Type*} [Fintype I] [Fintype V]
    (f : I → V) (u v : V) (huv : u ≠ v)
    (hc : Fintype.card I=Fintype.card V)
    (hs : ∀ w, w ≠ u → w ≠ v → ∃ i, f i=w)
    (hi : ∀ w, w ≠ u → w ≠ v → ∀ i j, f i=w → f j=w → i=j)
    (hn : ¬ Function.Bijective f) :
    ∃ w d, ((w=u ∧ d=v) ∨ (w=v ∧ d=u)) ∧
      (∀ i, f i ≠ w) ∧ ∃ i j, i ≠ j ∧ f i=d ∧ f j=d ∧
      Function.Bijective (fun z ↦ if z=i then w else f z) := by
  classical
  have hns : ¬ Function.Surjective f := fun hh ↦ hn
    ((Fintype.bijective_iff_surjective_and_card f).mpr ⟨hh,hc⟩)
  have hni : ¬ Function.Injective f := fun hh ↦ hn
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hh,hc⟩)
  obtain ⟨w,hw⟩ := not_forall.mp hns
  have hw' : ∀ i, f i ≠ w := by simpa only [not_exists] using hw
  obtain ⟨i,j,hij,hne⟩ : ∃ i j, f i=f j ∧ i ≠ j := by
    simpa only [Function.Injective,not_forall,_root_.not_imp,exists_prop] using hni
  have hwuv : w=u ∨ w=v := by
    by_contra hh
    exact hw (hs w (fun h ↦ hh (Or.inl h)) (fun h ↦ hh (Or.inr h)))
  have hduv : f i=u ∨ f i=v := by
    by_contra hh
    exact hne (hi (f i) (fun h ↦ hh (Or.inl h)) (fun h ↦ hh (Or.inr h))
      i j rfl hij.symm)
  have hwd : ((w=u ∧ f i=v) ∨ (w=v ∧ f i=u)) := by
    rcases hwuv with hwu | hwv <;> rcases hduv with hdu | hdv
    · exact (hw' i (hdu.trans hwu.symm)).elim
    · exact Or.inl ⟨hwu,hdv⟩
    · exact Or.inr ⟨hwv,hdu⟩
    · exact (hw' i (hdv.trans hwv.symm)).elim
  refine ⟨w,f i,hwd,hw',i,j,hne,rfl,hij.symm,?_⟩
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_,hc⟩
  intro x
  by_cases hxw : x=w
  · exact ⟨i,by simp [hxw]⟩
  by_cases hxd : x=f i
  · exact ⟨j,by simp [Ne.symm hne,hij.symm,hxd]⟩
  have hxu : x ≠ u := by rcases hwd with ⟨rfl,hd⟩ | ⟨_,hd⟩ <;> aesop
  have hxv : x ≠ v := by rcases hwd with ⟨_,hd⟩ | ⟨rfl,hd⟩ <;> aesop
  obtain ⟨l,hl⟩ := hs x hxu hxv
  have hli : l ≠ i := by intro hh; subst l; exact hxd hl.symm
  exact ⟨l,by simp [hli,hl]⟩

lemma quota_one_unique_endpoint {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (w : V) (hw : T.quota w=1) :
    (∃ i, T.endpoint i=w) ∧
      ∀ i j, T.endpoint i=w → T.endpoint j=w → i=j := by
  obtain ⟨hs,hn⟩ := Nat.card_eq_one_iff_unique.mp hw
  obtain ⟨i,hi⟩ := hn
  refine ⟨⟨i,hi⟩,?_⟩
  intro i j hi hj
  exact congrArg Subtype.val (hs.elim (⟨i,hi⟩ : {z // T.endpoint z=w}) ⟨j,hj⟩)

lemma endpoint_not_bijective_of_even_quota {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (w : V) (hw : Even (T.quota w)) :
    ¬ Function.Bijective T.endpoint := by
  intro he
  have hq : T.quota w=1 := by
    apply Nat.card_eq_one_iff_unique.mpr
    constructor
    · refine ⟨fun i j ↦ Subtype.ext (he.injective (i.property.trans j.property.symm))⟩
    · obtain ⟨i,hi⟩ := he.surjective w
      exact ⟨i,hi⟩
  rw [hq] at hw
  exact (by decide : ¬ Even (1 : ℕ)) hw

lemma trail_endpoint_collision {V : Type*} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (T : TrailFamily G k) (u v : V) (huv : u ≠ v)
    (hc : 2*k=Fintype.card V)
    (hq : ∀ w, w ≠ u → w ≠ v → T.quota w=1)
    (hu : Even (T.quota u)) :
    ∃ w d, ((w=u ∧ d=v) ∨ (w=v ∧ d=u)) ∧
      (∀ z, T.endpoint z ≠ w) ∧ ∃ i j, i ≠ j ∧ T.endpoint i=d ∧ T.endpoint j=d ∧
      Function.Bijective (fun z ↦ if z=i then w else T.endpoint z) := by
  classical
  obtain ⟨w,d,hwd,hw,i,j,hij,hi,hj,he⟩ := repair_two_exceptional_labels T.endpoint u v huv
    (by simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm] using hc)
    (fun w hwu hwv ↦ (quota_one_unique_endpoint T w (hq w hwu hwv)).1)
    (fun w hwu hwv ↦ (quota_one_unique_endpoint T w (hq w hwu hwv)).2)
    (endpoint_not_bijective_of_even_quota T u hu)
  refine ⟨w,d,hwd,hw,i,j,hij,hi,hj,?_⟩
  convert he using 1
  funext z
  split_ifs <;> rfl

end Erdos583CollisionEndpointLabelsDevelopment
