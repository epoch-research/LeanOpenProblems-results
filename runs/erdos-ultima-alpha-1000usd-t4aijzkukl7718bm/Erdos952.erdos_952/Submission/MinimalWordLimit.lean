import FormalConjecturesUtil

/-! Uniformly recurrent limits of finite-alphabet words. This is compact
symbolic dynamics, not an arithmetic obstruction by itself. -/
namespace Erdos952Investigation
namespace MinimalWordLimit
open Set Function
set_option maxHeartbeats 0

lemma exists_minimal_invariant {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X → X) (K : Set X) (hK : IsClosed K) (hne : K.Nonempty)
    (hfK : MapsTo f K K) :
    ∃ T : Set X, T ⊆ K ∧ T.Nonempty ∧ IsClosed T ∧ MapsTo f T T ∧
      ∀ U : Set X, U ⊆ T → U.Nonempty → IsClosed U → MapsTo f U U → U = T := by
  let S : Set (Set X) := {T | T.Nonempty ∧ IsClosed T ∧ MapsTo f T T}
  have hchain : ∀ c ⊆ S, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ lb ∈ S, ∀ T ∈ c, lb ⊆ T := by
    intro c hc hcc hcne
    letI : Nonempty c := hcne.to_subtype
    let V : c → Set X := fun T => T.val
    have hdir : Directed (· ⊇ ·) V := by
      intro A B
      rcases hcc.total A.property B.property with hAB | hBA
      · exact ⟨A,Subset.rfl,hAB⟩
      · exact ⟨B,hBA,Subset.rfl⟩
    have hn : (⋂ T : c, V T).Nonempty :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed V hdir
        (fun T => (hc T.property).1) (fun T => (hc T.property).2.1.isCompact)
        (fun T => (hc T.property).2.1)
    refine ⟨⋂ T : c, V T,⟨hn,isClosed_iInter (fun T => (hc T.property).2.1),?_⟩,?_⟩
    · intro z hz
      simp only [mem_iInter] at hz ⊢
      exact fun T => (hc T.property).2.2 (hz T)
    · intro T hT z hz
      exact mem_iInter.mp hz ⟨T,hT⟩
  obtain ⟨T,hTK,hT⟩ := zorn_superset_nonempty S hchain K ⟨hne,hK,hfK⟩
  refine ⟨T,hTK,hT.prop.1,hT.prop.2.1,hT.prop.2.2,?_⟩
  intro U hUT hUn hUc hUf
  exact hT.eq_of_le ⟨hUn,hUc,hUf⟩ hUT

/-- A compact invariant set contains a point whose returns to each
neighborhood have bounded gaps. -/
lemma exists_uniformly_recurrent_point {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X → X) (hf : Continuous f) (K : Set X) (hK : IsClosed K)
    (hne : K.Nonempty) (hfK : MapsTo f K K) :
    ∃ y ∈ K, ∀ U : Set X, IsOpen U → y ∈ U →
      ∃ R : ℕ, ∀ n : ℕ, ∃ k ≤ R, f^[n+k] y ∈ U := by
  classical
  obtain ⟨T,hTK,hTn,hTc,hTf,hmin⟩ := exists_minimal_invariant f K hK hne hfK
  obtain ⟨y,hy⟩ := hTn
  have horbit (z : X) (hz : z ∈ T) : closure (range (fun n : ℕ => f^[n] z)) = T := by
    apply hmin
    · apply closure_minimal _ hTc
      rintro _ ⟨n,rfl⟩
      exact hTf.iterate n hz
    · exact ⟨z,subset_closure ⟨0,rfl⟩⟩
    · exact isClosed_closure
    · apply MapsTo.closure _ hf
      rintro _ ⟨n,rfl⟩
      exact ⟨n+1,by simp [Function.iterate_succ_apply']⟩
  refine ⟨y,hTK hy,?_⟩
  intro U hU hyU
  have hcover : T ⊆ ⋃ n : ℕ, (f^[n]) ⁻¹' U := by
    intro z hz
    have hycl : y ∈ closure (range (fun n : ℕ => f^[n] z)) := by rw [horbit z hz]; exact hy
    obtain ⟨w,hwU,hw⟩ := (mem_closure_iff.mp hycl) U hU hyU
    obtain ⟨n,rfl⟩ := hw
    exact mem_iUnion.mpr ⟨n,hwU⟩
  obtain ⟨I,hI⟩ := hTc.isCompact.elim_finite_subcover
    (fun n : ℕ => (f^[n]) ⁻¹' U) (fun n => hU.preimage (hf.iterate n)) hcover
  refine ⟨I.sup id,?_⟩
  intro n
  obtain ⟨k,hk,hu⟩ := mem_iUnion₂.mp (hI (hTf.iterate n hy))
  refine ⟨k,Finset.le_sup (f := id) hk,?_⟩
  simpa only [mem_preimage,Function.iterate_add_apply,add_comm n k] using hu

abbrev shift {A : Type*} (w : ℕ → A) : ℕ → A := fun n => w (n+1)

lemma shift_iterate {A : Type*} (w : ℕ → A) (n i : ℕ) :
    shift^[n] w i = w (n+i) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',shift,ih]
    congr 1
    omega

lemma continuous_shift {A : Type*} [TopologicalSpace A] :
    Continuous (shift : (ℕ → A) → (ℕ → A)) :=
  continuous_pi (fun n => continuous_apply (n+1))

def UniformlyRecurrent {A : Type*} (w : ℕ → A) : Prop :=
  ∀ L : ℕ, ∃ R : ℕ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ n ≤ N+R ∧
    ∀ i < L, w (n+i) = w i

def PrefixLimit {A : Type*} (w v : ℕ → A) : Prop :=
  ∀ L : ℕ, ∃ n : ℕ, ∀ i < L, w (n+i) = v i

lemma prefix_neighborhood_open {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (v : ℕ → A) (L : ℕ) : IsOpen {w : ℕ → A | ∀ i < L, w i = v i} := by
  have he : {w : ℕ → A | ∀ i < L, w i = v i} =
      ⋂ i : Fin L, (fun w : ℕ → A => w i.val) ⁻¹' {v i.val} := by
    ext w
    simp only [mem_setOf_eq,mem_iInter,mem_preimage,mem_singleton_iff]
    exact ⟨fun h i => h i.val i.isLt,fun h i hi => h ⟨i,hi⟩⟩
  rw [he]
  exact isOpen_iInter_of_finite (fun i => (isOpen_discrete _).preimage (continuous_apply _))

/-- Every finite-alphabet word has a uniformly recurrent limit word, where
all finite prefixes of the limit occur in the original word. -/
theorem uniformly_recurrent_limit {A : Type*} [Finite A] (w : ℕ → A) :
    ∃ v : ℕ → A, PrefixLimit w v ∧ UniformlyRecurrent v := by
  classical
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  let K := closure (range (fun n : ℕ => shift^[n] w))
  have hK : MapsTo shift K K := by
    apply MapsTo.closure _ continuous_shift
    rintro _ ⟨n,rfl⟩
    exact ⟨n+1,by simp [Function.iterate_succ_apply']⟩
  obtain ⟨v,hv,hrec⟩ := exists_uniformly_recurrent_point shift continuous_shift K isClosed_closure
    ⟨w,subset_closure ⟨0,rfl⟩⟩ hK
  refine ⟨v,?_,?_⟩
  · intro L
    obtain ⟨u,hu,huK⟩ := (mem_closure_iff.mp hv) _ (prefix_neighborhood_open v L) (fun _ _ => rfl)
    obtain ⟨n,rfl⟩ := huK
    exact ⟨n,fun i hi => (shift_iterate w n i).symm.trans (hu i hi)⟩
  · intro L
    obtain ⟨R,hR⟩ := hrec _ (prefix_neighborhood_open v L) (fun _ _ => rfl)
    refine ⟨R,?_⟩
    intro N
    obtain ⟨k,hk,hreturn⟩ := hR N
    refine ⟨N+k,by omega,by omega,?_⟩
    intro i hi
    exact (shift_iterate v (N+k) i).symm.trans (hreturn i hi)

#print axioms uniformly_recurrent_limit
end MinimalWordLimit
end Erdos952Investigation
