import Submission.GreedyBatchPromotions
import Submission.RegularizationSharedLinks

/-! Indexed creation witnesses for shared rank-three links in a mixed batch.
The one-mark and two-mark cases keep their true support sizes and original
edge multiplicities. No asymptotic restart theorem is asserted. -/
namespace Erdos773.GreedyBatchSharedWitnesses
open Finset HypergraphDegreeTrim UniformLayerRegularization
open FourUniformRegularization (pairDegree)
set_option maxHeartbeats 3000000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev Index (α : Type*) := Σ _ : Finset α, Σ _ : Finset α, Finset α

def firstEdges (H : Finset (Finset α)) (x y : α) (r : ℕ) :=
  (layer H r).filter (fun e => x∈e ∧ y∉e)

def mates (H : Finset (Finset α)) (x y : α) (s : ℕ) (A : Finset α) :=
  (layer H s).filter (fun f => insert y A⊆f ∧ x∉f)

def family (H : Finset (Finset α)) (x y : α) (r s : ℕ) : Finset (Index α) :=
  (firstEdges H x y r).sigma (fun e => (e.erase x).powersetCard 2 |>.sigma (mates H x y s))

structure Data (H : Finset (Finset α)) (x y : α) (r s : ℕ)
    (e A f : Finset α) : Prop where
  e_mem : e∈H
  f_mem : f∈H
  e_card : e.card=r
  f_card : f.card=s
  x_mem : x∈e
  y_mem : y∈f
  y_not : y∉e
  x_not : x∉f
  A_card : A.card=2
  A_e : A⊆e
  A_f : A⊆f
  x_A : x∉A
  y_A : y∉A

lemma data_of_mem {H : Finset (Finset α)} {x y : α} {r s : ℕ} {e A f : Finset α}
    (hi : (⟨e,A,f⟩:Index α)∈family H x y r s) : Data H x y r s e A f := by
  obtain ⟨he,hi⟩ := mem_sigma.mp hi
  obtain ⟨hA,hf⟩ := mem_sigma.mp hi
  obtain ⟨he,hx,hy⟩ := mem_filter.mp he
  obtain ⟨he,hr⟩ := mem_filter.mp he
  obtain ⟨hAs,hAc⟩ := mem_powersetCard.mp hA
  obtain ⟨hf,hsub,hxf⟩ := mem_filter.mp hf
  obtain ⟨hf,hs⟩ := mem_filter.mp hf
  exact ⟨he,hf,hr,hs,hx,hsub (mem_insert_self _ _),hy,hxf,hAc,
    hAs.trans (erase_subset _ _),(subset_insert _ _).trans hsub,
    fun h => notMem_erase x e (hAs h),fun h => hy ((hAs.trans (erase_subset _ _)) h)⟩

lemma mem_of_data {H : Finset (Finset α)} {x y : α} {r s : ℕ} {e A f : Finset α}
    (h : Data H x y r s e A f) : (⟨e,A,f⟩:Index α)∈family H x y r s := by
  refine mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨h.e_mem,h.e_card⟩,h.x_mem,h.y_not⟩,
    mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨?_,h.A_card⟩,
      mem_filter.mpr ⟨mem_filter.mpr ⟨h.f_mem,h.f_card⟩,insert_subset h.y_mem h.A_f,h.x_not⟩⟩⟩
  intro a ha
  exact mem_erase.mpr ⟨fun he => h.x_A (he ▸ ha),h.A_e ha⟩

lemma Data.swap {H : Finset (Finset α)} {x y : α} {r s : ℕ} {e A f : Finset α}
    (h : Data H x y r s e A f) : Data H y x s r f A e :=
  ⟨h.f_mem,h.e_mem,h.f_card,h.e_card,h.y_mem,h.x_mem,h.x_not,h.y_not,
    h.A_card,h.A_f,h.A_e,h.y_A,h.x_A⟩

lemma mates_card (H : Finset (Finset α)) (x y : α) (s P : ℕ)
    (hP : ∀ a, y≠a → pairDegree H y a≤P)
    (A : Finset α) (hA : A.Nonempty) (hy : y∉A) : (mates H x y s A).card≤P := by
  obtain ⟨a,ha⟩ := hA
  have hya : y≠a := fun he => hy (he.symm ▸ ha)
  apply (card_le_card (show mates H x y s A⊆H.filter (fun f => y∈f ∧ a∈f) from ?_)).trans (hP a hya)
  intro f hf
  obtain ⟨hf,hsub,hx⟩ := mem_filter.mp hf
  exact mem_filter.mpr ⟨(mem_filter.mp hf).1,hsub (mem_insert_self _ _),hsub (mem_insert_of_mem ha)⟩

lemma family_card (H : Finset (Finset α)) (x y : α) (r s P : ℕ)
    (hP : ∀ a, y≠a → pairDegree H y a≤P) :
    (family H x y r s).card≤degree (layer H r) x*(r-1).choose 2*P := by
  rw [family,card_sigma]
  have hrow (e : Finset α) (he : e∈firstEdges H x y r) :
      (((e.erase x).powersetCard 2).sigma (mates H x y s)).card≤(r-1).choose 2*P := by
    obtain ⟨he,hx,hy⟩ := mem_filter.mp he
    have hrc := (mem_filter.mp he).2
    rw [card_sigma]
    calc
      _ ≤ ∑ _A∈(e.erase x).powersetCard 2, P := by
        apply sum_le_sum
        intro A hA
        obtain ⟨hAe,hAc⟩ := mem_powersetCard.mp hA
        exact mates_card H x y s P hP A (card_pos.mp (by rw [hAc]; decide))
          (fun h => hy ((erase_subset x e) (hAe h)))
      _ = _ := by simp [card_erase_of_mem hx,hrc]
  calc
    _ ≤ ∑ _e∈firstEdges H x y r, (r-1).choose 2*P := sum_le_sum hrow
    _ = (firstEdges H x y r).card*((r-1).choose 2*P) := by simp
    _ ≤ degree (layer H r) x*((r-1).choose 2*P) := by
      apply Nat.mul_le_mul_right
      apply card_le_card
      intro e he
      obtain ⟨he,hx,hy⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨he,hx⟩
    _ = _ := by ring

def witness (x y : α) (i : Index α) : Finset α :=
  (i.1 \ insert x i.2.1)∪(i.2.2 \ insert y i.2.1)

def cost (H : Finset (Finset α)) (x y : α) (r s : ℕ) (R : Finset α) : ℕ :=
  ((family H x y r s).filter (fun i => witness x y i⊆R)).card

lemma witness_card {H : Finset (Finset α)} {x y : α} {r s : ℕ} {i : Index α}
    (hI : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤2) (hi : i∈family H x y r s) :
    (witness x y i).card=(r-3)+(s-3) := by
  rcases i with ⟨e,A,f⟩
  have h := data_of_mem hi
  have hef : e≠f := fun he => h.x_not (he ▸ h.x_mem)
  have hAe : insert x A⊆e := insert_subset h.x_mem h.A_e
  have hAf : insert y A⊆f := insert_subset h.y_mem h.A_f
  have hAc : (insert x A).card=3 := by rw [card_insert_of_notMem h.x_A,h.A_card]
  have hBc : (insert y A).card=3 := by rw [card_insert_of_notMem h.y_A,h.A_card]
  have hcommon : A=e∩f := eq_of_subset_of_card_le (subset_inter h.A_e h.A_f)
    (by rw [h.A_card]; exact hI e h.e_mem f h.f_mem hef)
  have hd : Disjoint (e \ insert x A) (f \ insert y A) := by
    apply disjoint_left.mpr
    intro a ha hb
    have hm : a∈A := hcommon.symm ▸ mem_inter.mpr ⟨(mem_sdiff.mp ha).1,(mem_sdiff.mp hb).1⟩
    exact (mem_sdiff.mp ha).2 (mem_insert_of_mem hm)
  change ((e \ insert x A)∪(f \ insert y A)).card=_
  rw [card_union_of_disjoint hd,card_sdiff_of_subset hAe,card_sdiff_of_subset hAf,h.e_card,h.f_card,hAc,hBc]

/-- Once a first-role mark a is fixed, the shared two-set is determined
by the original first edge, since its rank is at most four. -/
lemma first_role_link {H : Finset (Finset α)} {x y a : α} {r s : ℕ} {e A f : Finset α}
    (hr : r≤4) (hi : (⟨e,A,f⟩:Index α)∈family H x y r s)
    (ha : a∈e \ insert x A) : A=e \ {x,a} := by
  have h := data_of_mem hi
  have hxa : x≠a := fun he => (mem_sdiff.mp ha).2 (by simp [he])
  have hpair : ({x,a}:Finset α)⊆e := by simp [insert_subset_iff,h.x_mem,(mem_sdiff.mp ha).1]
  have hs : A⊆e \ {x,a} := by
    intro b hb
    refine mem_sdiff.mpr ⟨h.A_e hb,?_⟩
    simp only [mem_insert,mem_singleton]
    rintro (rfl | rfl)
    · exact h.x_A hb
    · exact (mem_sdiff.mp ha).2 (mem_insert_of_mem hb)
  apply eq_of_subset_of_card_le hs
  rw [card_sdiff_of_subset hpair,h.e_card,card_pair hxa,h.A_card]
  omega

lemma first_role_incidence (H : Finset (Finset α)) (x y a : α) (r s P : ℕ)
    (hr : 3≤r ∧ r≤4) (hP : ∀ u v, u≠v → pairDegree H u v≤P) :
    ((family H x y r s).filter (fun i => a∈i.1 \ insert x i.2.1)).card≤P^2 := by
  by_cases hax : a=x
  · subst a
    have he : (family H x y r s).filter (fun i => x∈i.1 \ insert x i.2.1)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact (mem_sdiff.mp (mem_filter.mp hi).2).2 (mem_insert_self _ _)
    rw [he,card_empty]
    exact Nat.zero_le _
  · let E := (firstEdges H x y r).filter (fun e => a∈e)
    have hE : E.card≤P := by
      apply (card_le_card (show E⊆H.filter (fun e => x∈e ∧ a∈e) from ?_)).trans (hP x a (Ne.symm hax))
      intro e he
      obtain ⟨he,ha⟩ := mem_filter.mp he
      obtain ⟨he,hx,hy⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨(mem_filter.mp he).1,hx,ha⟩
    have hc (e : Finset α) (he : e∈E) : (mates H x y s (e \ {x,a})).card≤P := by
      obtain ⟨he,ha⟩ := mem_filter.mp he
      obtain ⟨he,hx,hy⟩ := mem_filter.mp he
      have hecard := (mem_filter.mp he).2
      apply mates_card H x y s P (hP y) (e \ {x,a})
      · apply card_pos.mp
        rw [card_sdiff_of_subset (by simp [insert_subset_iff,hx,ha]),hecard,card_pair (Ne.symm hax)]
        omega
      · exact fun h => hy (mem_sdiff.mp h).1
    have hb : ((family H x y r s).filter (fun i => a∈i.1 \ insert x i.2.1)).card≤
        (E.sigma (fun e => mates H x y s (e \ {x,a}))).card := by
      apply card_le_card_of_injOn (fun i : Index α => (⟨i.1,i.2.2⟩ : Σ _ : Finset α, Finset α))
      · rintro ⟨e,A,f⟩ hi
        obtain ⟨hi,ha⟩ := mem_filter.mp hi
        have h := data_of_mem hi
        have hA := first_role_link hr.2 hi ha
        refine mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_filter.mpr
          ⟨mem_filter.mpr ⟨h.e_mem,h.e_card⟩,h.x_mem,h.y_not⟩,(mem_sdiff.mp ha).1⟩,?_⟩
        rw [← hA]
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨h.f_mem,h.f_card⟩,insert_subset h.y_mem h.A_f,h.x_not⟩
      · rintro ⟨e,A,f⟩ hi ⟨e',A',f'⟩ hi' he
        have he' : e=e' := congrArg Sigma.fst he
        have hf' : f=f' := congrArg (fun i : Σ _ : Finset α, Finset α => i.2) he
        subst e'; subst f'
        have hA := first_role_link hr.2 (mem_filter.mp hi).1 (mem_filter.mp hi).2
        have hA' := first_role_link hr.2 (mem_filter.mp hi').1 (mem_filter.mp hi').2
        rw [hA,hA']
    apply hb.trans
    rw [card_sigma]
    calc
      _ ≤ ∑ _e∈E, P := sum_le_sum hc
      _ = E.card*P := by simp
      _ ≤ P*P := Nat.mul_le_mul_right P hE
      _ = _ := by ring

lemma second_role_incidence (H : Finset (Finset α)) (x y a : α) (r s P : ℕ)
    (hs : 3≤s ∧ s≤4) (hP : ∀ u v, u≠v → pairDegree H u v≤P) :
    ((family H x y r s).filter (fun i => a∈i.2.2 \ insert y i.2.1)).card≤P^2 := by
  apply (show _≤((family H y x s r).filter (fun i => a∈i.1 \ insert y i.2.1)).card from ?_).trans
    (first_role_incidence H y x a s r P hs hP)
  apply card_le_card_of_injOn (fun i : Index α => (⟨i.2.2,i.2.1,i.1⟩ : Index α))
  · rintro ⟨e,A,f⟩ hi
    obtain ⟨hi,ha⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨mem_of_data (data_of_mem hi).swap,ha⟩
  · rintro ⟨e,A,f⟩ hi ⟨e',A',f'⟩ hi' he
    have hf : f=f' := congrArg Sigma.fst he
    have hA : A=A' := congrArg (fun i : Index α => i.2.1) he
    have hh : e=e' := congrArg (fun i : Index α => i.2.2) he
    subst e'; subst A'; subst f'
    rfl

lemma witness_incidence (H : Finset (Finset α)) (x y a : α) (r s P : ℕ)
    (hr : 3≤r ∧ r≤4) (hs : 3≤s ∧ s≤4)
    (hP : ∀ u v, u≠v → pairDegree H u v≤P) :
    ((family H x y r s).filter (fun i => a∈witness x y i)).card≤2*P^2 := by
  have he : (family H x y r s).filter (fun i => a∈witness x y i)=
      ((family H x y r s).filter (fun i => a∈i.1 \ insert x i.2.1))∪
      ((family H x y r s).filter (fun i => a∈i.2.2 \ insert y i.2.1)) := by
    ext i
    simp only [mem_filter,witness,mem_union]
    tauto
  rw [he]
  have hh := card_union_le
    ((family H x y r s).filter (fun i => a∈i.1 \ insert x i.2.1))
    ((family H x y r s).filter (fun i => a∈i.2.2 \ insert y i.2.1))
  have h1 := first_role_incidence H x y a r s P hr hP
  have h2 := second_role_incidence H x y a r s P hs hP
  omega

def swap (i : Index α) : Index α := ⟨i.2.2,i.2.1,i.1⟩

lemma swap_swap (i : Index α) : swap (swap i)=i := by cases i; rfl

lemma witness_swap (x y : α) (i : Index α) : witness y x (swap i)=witness x y i := union_comm _ _

lemma cost_le_swap (H : Finset (Finset α)) (x y : α) (r s : ℕ) (R : Finset α) :
    cost H x y r s R≤cost H y x s r R := by
  apply card_le_card_of_injOn swap
  · rintro ⟨e,A,f⟩ hi
    obtain ⟨hi,hR⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨mem_of_data (data_of_mem hi).swap,by rwa [witness_swap]⟩
  · intro i hi j hj he
    have hh := congrArg swap he
    simpa only [swap_swap] using hh

lemma cost_swap (H : Finset (Finset α)) (x y : α) (r s : ℕ) (R : Finset α) :
    cost H x y r s R=cost H y x s r R :=
  Nat.le_antisymm (cost_le_swap H x y r s R) (cost_le_swap H y x s r R)

def overlapCaps (m P : ℕ) (k : ℕ) : ℕ := if k=0 then m else 2*P^2

lemma incidence_bound (H : Finset (Finset α)) (x y : α) (r s P : ℕ)
    (hr : 3≤r ∧ r≤4) (hs : 3≤s ∧ s≤4)
    (hP : ∀ u v, u≠v → pairDegree H u v≤P) (A : Finset α) :
    IndexedBernoulliMoments.incidence (family H x y r s) (witness x y) A≤
      overlapCaps (degree (layer H r) x*(r-1).choose 2*P) P A.card := by
  by_cases hA : A.card=0
  · have he := card_eq_zero.mp hA
    subst A
    simpa [IndexedBernoulliMoments.incidence,overlapCaps] using family_card H x y r s P (hP y)
  · rw [overlapCaps,if_neg hA]
    obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0<A.card)
    apply (card_le_card (show (family H x y r s).filter (fun i => A⊆witness x y i)⊆
      (family H x y r s).filter (fun i => a∈witness x y i) from ?_)).trans
      (witness_incidence H x y a r s P hr hs hP)
    intro i hi
    obtain ⟨hi,hA⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨hi,hA ha⟩

/-- Mixed shared-link creation tails: (3,4) uses one mark, while (4,4)
uses two. The latter relies on the original intersection cap of two. -/
theorem cost_tail (H : Finset (Finset α)) (x y : α) (r s P q : ℕ)
    (hr : 3≤r ∧ r≤4) (hs : 3≤s ∧ s≤4)
    (hP : ∀ u v, u≠v → pairDegree H u v≤P)
    (hI : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤2)
    (p L : ℝ) (hp : 0≤p) (hp1 : p≤1) (hL : 0<L) :
    (∑ f : α → Bool, if L≤(cost H x y r s (selected f):ℝ) then trialWeight p f else 0) ≤
      (IndexedBernoulliMoments.budget ((r-3)+(s-3)) q
        (overlapCaps (degree (layer H r) x*(r-1).choose 2*P) P) p/L)^q := by
  exact IndexedBernoulliMoments.tail_bound (family H x y r s) (witness x y) ((r-3)+(s-3)) q
    (overlapCaps (degree (layer H r) x*(r-1).choose 2*P) P) p L hp hp1 hL
    (fun i hi => witness_card hI hi) (fun A _ => incidence_bound H x y r s P hr hs hP A)

#print axioms family_card
#print axioms witness_card
#print axioms first_role_incidence
#print axioms witness_incidence
#print axioms cost_swap
#print axioms cost_tail
end
end Erdos773.GreedyBatchSharedWitnesses
