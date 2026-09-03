import Submission.BernoulliCarrier

/-! Forbidden supports certifying positive-difference capacity at most two
for arbitrary integer sets. No assertion here specializes them to squares. -/
namespace Erdos773.IntegerDifferenceCapacity
open Finset
set_option maxHeartbeats 3000000

def apParams (m : ℕ) : Finset (ℕ × ℕ) := ((Icc 1 m) ×ˢ (Icc 1 m)).filter (fun ad => ad.1+2*ad.2 ≤ m)
def aps (m : ℕ) : Finset (Finset ℕ) := (apParams m).image (fun ad => {ad.1,ad.1+ad.2,ad.1+2*ad.2})
def reps (B : Finset ℕ) (D : ℕ) : Finset (ℕ × ℕ) := (B ×ˢ B).filter (fun ab => ab.1 < ab.2 ∧ ab.2=ab.1+D)
def support (E : Finset (ℕ × ℕ)) : Finset ℕ := E.image Prod.fst ∪ E.image Prod.snd
def sixes (m : ℕ) : Finset (Finset ℕ) :=
  ((Icc 1 m).biUnion (fun D => ((reps (Icc 1 m) D).powersetCard 3).image support)).filter (fun e => e.card=6)

lemma aps_card (m : ℕ) : (aps m).card ≤ m^2 := by
  exact card_image_le.trans ((card_filter_le _ _).trans_eq (by simp [card_product]; ring))
lemma aps_size {m : ℕ} {e : Finset ℕ} (he : e ∈ aps m) : e.card=3 := by
  obtain ⟨⟨a,D⟩,had,rfl⟩ := mem_image.mp he
  have hD := (mem_Icc.mp (mem_product.mp (mem_filter.mp had).1).2).1
  change ({a,a+D,a+2*D} : Finset ℕ).card=3
  have h₁ : a ≠ a+D := by omega
  have h₂ : a ≠ a+2*D := by omega
  have h₃ : a+D ≠ a+2*D := by omega
  rw [card_insert_of_notMem (by simpa only [mem_insert,mem_singleton,not_or] using And.intro h₁ h₂),
    card_insert_of_notMem (by simpa only [mem_singleton] using h₃),card_singleton]
lemma aps_subset {m : ℕ} {e : Finset ℕ} (he : e ∈ aps m) : e ⊆ Icc 1 m := by
  obtain ⟨⟨a,D⟩,had,rfl⟩ := mem_image.mp he
  obtain ⟨had,hadm⟩ := mem_filter.mp had
  have ha := mem_Icc.mp (mem_product.mp had).1
  have hD := mem_Icc.mp (mem_product.mp had).2
  intro x hx
  simp only [mem_insert,mem_singleton] at hx
  apply mem_Icc.mpr
  rcases hx with rfl | rfl | rfl <;> constructor <;> omega

lemma ap_mem {m a b c : ℕ} (ha : a ∈ Icc 1 m) (hc : c ∈ Icc 1 m)
    (hab : a<b) (he : a+c=b+b) : {a,b,c} ∈ aps m := by
  have ha' := mem_Icc.mp ha
  have hc' := mem_Icc.mp hc
  refine mem_image.mpr ⟨(a,b-a),mem_filter.mpr ⟨mem_product.mpr ⟨ha,mem_Icc.mpr ⟨by omega,by omega⟩⟩,
    by dsimp only; omega⟩,?_⟩
  have hb : a+(b-a)=b := by omega
  have hc : a+2*(b-a)=c := by omega
  simp only [hb,hc]

lemma apFree_of_avoids {m : ℕ} {B : Finset ℕ} (hB : B ⊆ Icc 1 m)
    (havoid : ∀ e ∈ aps m, ¬e ⊆ B) : ThreeAPFree (B:Set ℕ) := by
  intro a ha b hb c hc he
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact havoid {a,b,c} (ap_mem (hB ha) (hB hc) hlt he) (insert_subset ha (insert_subset hb (singleton_subset_iff.mpr hc)))
  · have hcb : c<b := by omega
    exact havoid {c,b,a} (ap_mem (hB hc) (hB ha) hcb (by omega)) (insert_subset hc (insert_subset hb (singleton_subset_iff.mpr ha)))

lemma fst_injective {B : Finset ℕ} {D : ℕ} : Set.InjOn Prod.fst (reps B D : Set (ℕ × ℕ)) := by
  intro ab hab cd hcd he
  have hp := (mem_filter.mp hab).2.2
  have hq := (mem_filter.mp hcd).2.2
  exact Prod.ext he (by omega)
lemma snd_injective {B : Finset ℕ} {D : ℕ} : Set.InjOn Prod.snd (reps B D : Set (ℕ × ℕ)) := by
  intro ab hab cd hcd he
  have hp := (mem_filter.mp hab).2.2
  have hq := (mem_filter.mp hcd).2.2
  exact Prod.ext (by omega) he
lemma reps_card (B : Finset ℕ) (D : ℕ) : (reps B D).card ≤ B.card := by
  exact card_le_card_of_injOn Prod.fst (fun ab hab => (mem_product.mp (mem_filter.mp hab).1).1) fst_injective
lemma support_subset {B : Finset ℕ} {D : ℕ} {E : Finset (ℕ × ℕ)} (hE : E ⊆ reps B D) : support E ⊆ B := by
  intro x hx
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨ab,hab,rfl⟩ := mem_image.mp hx
    exact (mem_product.mp (mem_filter.mp (hE hab)).1).1
  · obtain ⟨ab,hab,rfl⟩ := mem_image.mp hx
    exact (mem_product.mp (mem_filter.mp (hE hab)).1).2
lemma support_card {B : Finset ℕ} {D : ℕ} (hAP : ThreeAPFree (B:Set ℕ))
    {E : Finset (ℕ × ℕ)} (hE : E ⊆ reps B D) : (support E).card=2*E.card := by
  have hdis : Disjoint (E.image Prod.fst) (E.image Prod.snd) := by
    apply disjoint_left.mpr
    intro a ha hb
    obtain ⟨ab,hab,hea⟩ := mem_image.mp ha
    obtain ⟨cd,hcd,heb⟩ := mem_image.mp hb
    obtain ⟨hpB,hp⟩ := mem_filter.mp (hE hab)
    obtain ⟨hqB,hq⟩ := mem_filter.mp (hE hcd)
    have he : cd.1+ab.2=a+a := by omega
    have hh := hAP (mem_product.mp hqB).1 (hea ▸ (mem_product.mp hpB).1) (mem_product.mp hpB).2 he
    omega
  unfold support
  rw [card_union_of_disjoint hdis,
    card_image_of_injOn (fun p hp q hq he => fst_injective (hE hp) (hE hq) he),
    card_image_of_injOn (fun p hp q hq he => snd_injective (hE hp) (hE hq) he)]
  omega

lemma sixes_card (m : ℕ) : (sixes m).card ≤ m^4 := by
  calc
    _ ≤ ((Icc 1 m).biUnion (fun D => ((reps (Icc 1 m) D).powersetCard 3).image support)).card := card_filter_le _ _
    _ ≤ ∑ D ∈ Icc 1 m, (((reps (Icc 1 m) D).powersetCard 3).image support).card := card_biUnion_le
    _ ≤ ∑ _D ∈ Icc 1 m, m^3 := by
      apply sum_le_sum
      intro D hD
      apply card_image_le.trans
      rw [card_powersetCard]
      apply (Nat.choose_le_pow _ _).trans
      apply Nat.pow_le_pow_left
      simpa using reps_card (Icc 1 m) D
    _ = _ := by simp; ring
lemma sixes_size {m : ℕ} {e : Finset ℕ} (he : e ∈ sixes m) : e.card=6 := (mem_filter.mp he).2
lemma sixes_subset {m : ℕ} {e : Finset ℕ} (he : e ∈ sixes m) : e ⊆ Icc 1 m := by
  obtain ⟨D,hD,he⟩ := mem_biUnion.mp (mem_filter.mp he).1
  obtain ⟨E,hE,rfl⟩ := mem_image.mp he
  exact support_subset (mem_powersetCard.mp hE).1

lemma capacity_of_avoids {m : ℕ} {B : Finset ℕ} (hB : B ⊆ Icc 1 m)
    (hAP : ThreeAPFree (B:Set ℕ)) (havoid : ∀ e ∈ sixes m, ¬e ⊆ B) :
    ∀ D, 0<D → (reps B D).card ≤ 2 := by
  intro D hD
  by_contra! hlarge
  obtain ⟨E,hE,hcard⟩ := exists_subset_card_eq (show 3 ≤ (reps B D).card by omega)
  have hE' : E ⊆ reps (Icc 1 m) D := by
    intro ab hab
    obtain ⟨habB,habD⟩ := mem_filter.mp (hE hab)
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hB (mem_product.mp habB).1,hB (mem_product.mp habB).2⟩,habD⟩
  have hDm : D ≤ m := by
    obtain ⟨ab,hab⟩ := card_pos.mp (show 0<E.card by omega)
    obtain ⟨hp,hq⟩ := mem_filter.mp (hE' hab)
    have hb := mem_Icc.mp (mem_product.mp hp).2
    omega
  apply havoid (support E) _ (support_subset hE)
  apply mem_filter.mpr
  refine ⟨mem_biUnion.mpr ⟨D,mem_Icc.mpr ⟨hD,hDm⟩,
    mem_image.mpr ⟨E,mem_powersetCard.mpr ⟨hE',hcard⟩,rfl⟩⟩,?_⟩
  rw [support_card hAP hE,hcard]

#print axioms aps_card
#print axioms apFree_of_avoids
#print axioms sixes_card
#print axioms capacity_of_avoids
end Erdos773.IntegerDifferenceCapacity
