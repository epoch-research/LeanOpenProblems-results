import Submission.ExceptionalPairDeletionExplore
import Submission.SignedRepBernoulliExplore
import Submission.BernoulliMatchingExplore

/-! Three-coordinate events controlling off-diagonal codegrees. Every
coordinate is incident to at most three events, so conflicts have size at
most nine. Diagonal degeneracies are kept separate. -/
namespace Erdos66TripleCodegreeGeometry
open Erdos66FiniteBernoulli Erdos66FiniteRepBernoulli Erdos66SignedRepBernoulli
  Erdos66ExceptionalPairDeletion
open scoped Classical
set_option maxHeartbeats 1800000

abbrev Triple (L : ℕ) := Fin (L+1) × Fin (L+1) × Fin (L+1)

noncomputable def tripleEvents (L b q : ℕ) : Finset (Triple L) :=
  Finset.univ.filter (fun x ↦ x.1.val+x.2.1.val=b ∧ x.1.val+x.2.2.val=q ∧
    x.1≠x.2.1 ∧ x.1≠x.2.2 ∧ x.2.1≠x.2.2)

noncomputable def tripleSupport {L : ℕ} (x : Triple L) : Finset (Fin (L+1)) :=
  {x.1,x.2.1,x.2.2}

lemma mem_tripleEvents {L b q : ℕ} {x : Triple L} : x∈tripleEvents L b q ↔
    x.1.val+x.2.1.val=b ∧ x.1.val+x.2.2.val=q ∧
      x.1≠x.2.1 ∧ x.1≠x.2.2 ∧ x.2.1≠x.2.2 := by simp [tripleEvents]

lemma tripleSupport_nonempty {L : ℕ} (x : Triple L) : (tripleSupport x).Nonempty :=
  ⟨x.1,by simp [tripleSupport]⟩

lemma coordinate_fibers_le_one (L b q : ℕ) (S : Finset (Triple L))
    (hS : ∀ x∈S, x.1.val+x.2.1.val=b ∧ x.1.val+x.2.2.val=q) (i : Fin (L+1)) :
    (S.filter (fun x ↦ x.1=i)).card ≤ 1 ∧
    (S.filter (fun x ↦ x.2.1=i)).card ≤ 1 ∧
    (S.filter (fun x ↦ x.2.2=i)).card ≤ 1 := by
  have hinj (x y : Triple L) (hx : x∈S) (hy : y∈S)
      (he : x.1=i ∧ y.1=i ∨ x.2.1=i ∧ y.2.1=i ∨ x.2.2=i ∧ y.2.2=i) : x=y := by
    have hx' := hS x hx
    have hy' := hS y hy
    have hv : x.1.val=i.val ∧ y.1.val=i.val ∨
        x.2.1.val=i.val ∧ y.2.1.val=i.val ∨ x.2.2.val=i.val ∧ y.2.2.val=i.val := by
      rcases he with he | he | he
      · exact Or.inl ⟨congrArg Fin.val he.1,congrArg Fin.val he.2⟩
      · exact Or.inr (Or.inl ⟨congrArg Fin.val he.1,congrArg Fin.val he.2⟩)
      · exact Or.inr (Or.inr ⟨congrArg Fin.val he.1,congrArg Fin.val he.2⟩)
    exact Prod.ext (Fin.ext (by omega)) (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  constructor
  · apply Finset.card_le_one.mpr
    intro x hx y hy
    exact hinj x y (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
      (Or.inl ⟨(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hy).2⟩)
  constructor
  · apply Finset.card_le_one.mpr
    intro x hx y hy
    exact hinj x y (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
      (Or.inr (Or.inl ⟨(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hy).2⟩))
  · apply Finset.card_le_one.mpr
    intro x hx y hy
    exact hinj x y (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1
      (Or.inr (Or.inr ⟨(Finset.mem_filter.mp hx).2,(Finset.mem_filter.mp hy).2⟩))

lemma incident_card_le_three (L b q : ℕ) (i : Fin (L+1)) :
    ((tripleEvents L b q).filter (fun x ↦ i∈tripleSupport x)).card ≤ 3 := by
  let S := tripleEvents L b q
  have he : S.filter (fun x ↦ i∈tripleSupport x) =
      (S.filter (fun x ↦ x.1=i) ∪ S.filter (fun x ↦ x.2.1=i)) ∪ S.filter (fun x ↦ x.2.2=i) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_union,tripleSupport,Finset.mem_insert,Finset.mem_singleton]
    tauto
  rw [he]
  have hs (x : Triple L) (hx : x∈S) : x.1.val+x.2.1.val=b ∧ x.1.val+x.2.2.val=q :=
    ⟨(mem_tripleEvents.mp hx).1,(mem_tripleEvents.mp hx).2.1⟩
  obtain ⟨h₁,h₂,h₃⟩ := coordinate_fibers_le_one L b q S hs i
  have h₄ := Finset.card_union_le (S.filter (fun x ↦ x.1=i)) (S.filter (fun x ↦ x.2.1=i))
  have h₅ := Finset.card_union_le
    (S.filter (fun x ↦ x.1=i) ∪ S.filter (fun x ↦ x.2.1=i)) (S.filter (fun x ↦ x.2.2=i))
  omega

lemma conflict_card_le_nine (L b q : ℕ) (x : Triple L) :
    ((tripleEvents L b q).filter (fun y ↦ ¬Disjoint (tripleSupport x) (tripleSupport y))).card ≤ 9 := by
  let S := tripleEvents L b q
  have he : S.filter (fun y ↦ ¬Disjoint (tripleSupport x) (tripleSupport y)) =
      (S.filter (fun y ↦ x.1∈tripleSupport y) ∪ S.filter (fun y ↦ x.2.1∈tripleSupport y)) ∪
        S.filter (fun y ↦ x.2.2∈tripleSupport y) := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_union,tripleSupport,Finset.disjoint_insert_left,
      Finset.disjoint_singleton_left,not_and_or,not_not]
    tauto
  rw [he]
  have h₁ := incident_card_le_three L b q x.1
  have h₂ := incident_card_le_three L b q x.2.1
  have h₃ := incident_card_le_three L b q x.2.2
  have h₄ := Finset.card_union_le (S.filter (fun y ↦ x.1∈tripleSupport y))
    (S.filter (fun y ↦ x.2.1∈tripleSupport y))
  have h₅ := Finset.card_union_le
    (S.filter (fun y ↦ x.1∈tripleSupport y) ∪ S.filter (fun y ↦ x.2.1∈tripleSupport y))
    (S.filter (fun y ↦ x.2.2∈tripleSupport y))
  dsimp [S] at h₄ h₅ ⊢
  omega


noncomputable def fullTriples (L b q : ℕ) (ω : Fin (L+1) → Bool) : Finset (Triple L) :=
  Finset.univ.filter (fun x ↦ x.1.val+x.2.1.val=b ∧ x.1.val+x.2.2.val=q ∧
    ω x.1=true ∧ ω x.2.1=true ∧ ω x.2.2=true)

lemma mem_fullTriples {L b q : ℕ} {ω : Fin (L+1) → Bool} {x : Triple L} :
    x∈fullTriples L b q ω ↔ x.1.val+x.2.1.val=b ∧ x.1.val+x.2.2.val=q ∧
      ω x.1=true ∧ ω x.2.1=true ∧ ω x.2.2=true := by simp [fullTriples]

lemma fullTriples_card (L b q : ℕ) (ω : Fin (L+1) → Bool) :
    (fullTriples L b q ω).card=codegree (selectedFinset L ω) b q := by
  unfold codegree tripleFiber
  apply Finset.card_bij (fun x _ ↦ x.1.val)
  · intro x hx
    obtain ⟨hb,hq,h₁,h₂,h₃⟩ := mem_fullTriples.mp hx
    have hx₁ : x.1.val∈selectedFinset L ω := by
      simpa only [selectedFinset,Set.Finite.mem_toFinset,mem_selected] using h₁
    have hx₂ : x.2.1.val∈selectedFinset L ω := by
      simpa only [selectedFinset,Set.Finite.mem_toFinset,mem_selected] using h₂
    have hx₃ : x.2.2.val∈selectedFinset L ω := by
      simpa only [selectedFinset,Set.Finite.mem_toFinset,mem_selected] using h₃
    exact Finset.mem_filter.mpr ⟨hx₁,by omega,by omega,by simpa only [show b-x.1.val=x.2.1.val by omega] using hx₂,
      by simpa only [show q-x.1.val=x.2.2.val by omega] using hx₃⟩
  · intro x hx y hy he
    have hx' := mem_fullTriples.mp hx
    have hy' := mem_fullTriples.mp hy
    exact Prod.ext (Fin.ext he) (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  · intro a ha
    obtain ⟨haD,hab,haq,hbD,hqD⟩ := Finset.mem_filter.mp ha
    have hD := selectedFinset_subset L ω
    let x : Fin (L+1) := ⟨a,Finset.mem_range.mp (hD haD)⟩
    let y : Fin (L+1) := ⟨b-a,Finset.mem_range.mp (hD hbD)⟩
    let z : Fin (L+1) := ⟨q-a,Finset.mem_range.mp (hD hqD)⟩
    have h₁ : ω x=true := by
      exact (mem_selected L ω x).mp (by simpa only [selectedFinset,Set.Finite.mem_toFinset] using haD)
    have h₂ : ω y=true := by
      exact (mem_selected L ω y).mp (by simpa only [selectedFinset,Set.Finite.mem_toFinset] using hbD)
    have h₃ : ω z=true := by
      exact (mem_selected L ω z).mp (by simpa only [selectedFinset,Set.Finite.mem_toFinset] using hqD)
    exact ⟨(x,y,z),mem_fullTriples.mpr ⟨by dsimp [x,y]; omega,by dsimp [x,z]; omega,h₁,h₂,h₃⟩,rfl⟩

lemma fullTriples_proper (L b q : ℕ) (ω : Fin (L+1) → Bool) :
    (fullTriples L b q ω).filter (fun x ↦ x.1≠x.2.1 ∧ x.1≠x.2.2 ∧ x.2.1≠x.2.2) =
      Erdos66BernoulliMatching.realized (tripleEvents L b q) tripleSupport ω := by
  ext x
  simp only [Finset.mem_filter,mem_fullTriples,Erdos66BernoulliMatching.realized,mem_tripleEvents]
  by_cases h₁ : x.1=x.2.1 <;> by_cases h₂ : x.1=x.2.2 <;> by_cases h₃ : x.2.1=x.2.2
  all_goals try simp [h₁,h₂,h₃]
  simp only [h₁,h₂,h₃,not_false_eq_true,and_true,monomial,tripleSupport,
    Finset.prod_insert,Finset.mem_insert,Finset.mem_singleton,or_self,if_false,Finset.prod_singleton]
  cases hx : ω x.1 <;> cases hy : ω x.2.1 <;> cases hz : ω x.2.2 <;> simp [bit,hx,hy,hz]

/-- Only x=y or x=z can cause a repeated coordinate when b and q differ.
Each contributes at most one event. -/
theorem codegree_le_realized_add_two (L b q : ℕ) (hbq : b≠q) (ω : Fin (L+1) → Bool) :
    codegree (selectedFinset L ω) b q ≤
      (Erdos66BernoulliMatching.realized (tripleEvents L b q) tripleSupport ω).card+2 := by
  let S := fullTriples L b q ω
  let P := fun x : Triple L ↦ x.1≠x.2.1 ∧ x.1≠x.2.2 ∧ x.2.1≠x.2.2
  have hs : S.filter (fun x ↦ ¬P x) ⊆
      S.filter (fun x ↦ x.1=x.2.1) ∪ S.filter (fun x ↦ x.1=x.2.2) := by
    intro x hx
    obtain ⟨hx,hnot⟩ := Finset.mem_filter.mp hx
    have hx' := mem_fullTriples.mp hx
    have hlast : x.2.1≠x.2.2 := by
      intro he
      have hv := congrArg Fin.val he
      omega
    have hsplit : x.1=x.2.1 ∨ x.1=x.2.2 := by dsimp [P] at hnot; tauto
    rcases hsplit with he | he
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,he⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx,he⟩)
  have h₁ : (S.filter (fun x ↦ x.1=x.2.1)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx' := mem_fullTriples.mp (Finset.mem_filter.mp hx).1
    have hy' := mem_fullTriples.mp (Finset.mem_filter.mp hy).1
    have he₁ := congrArg Fin.val (Finset.mem_filter.mp hx).2
    have he₂ := congrArg Fin.val (Finset.mem_filter.mp hy).2
    exact Prod.ext (Fin.ext (by omega)) (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  have h₂ : (S.filter (fun x ↦ x.1=x.2.2)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx' := mem_fullTriples.mp (Finset.mem_filter.mp hx).1
    have hy' := mem_fullTriples.mp (Finset.mem_filter.mp hy).1
    have he₁ := congrArg Fin.val (Finset.mem_filter.mp hx).2
    have he₂ := congrArg Fin.val (Finset.mem_filter.mp hy).2
    exact Prod.ext (Fin.ext (by omega)) (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  have hbad := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (p := P)
  have hgood : S.filter P=Erdos66BernoulliMatching.realized (tripleEvents L b q) tripleSupport ω :=
    fullTriples_proper L b q ω
  rw [hgood] at hsplit
  have hc : S.card=codegree (selectedFinset L ω) b q := fullTriples_card L b q ω
  omega

end Erdos66TripleCodegreeGeometry
