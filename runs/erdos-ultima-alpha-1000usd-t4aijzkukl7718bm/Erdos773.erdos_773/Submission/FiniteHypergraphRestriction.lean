import Submission.RegularizationCommonNeighbors

/-! Restricting a hypergraph to its actual finite carrier. These identities
avoid counting deleted ambient vertices in a residual density argument. -/
namespace Erdos773.FiniteHypergraphRestriction
open Finset HypergraphDegreeTrim UniformLayerRegularization
open FourUniformRegularization (pairDegree)
open RegularizationCommonNeighbors (Adj common both)
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [DecidableEq α]

abbrev Carrier (Q : Finset α) := {a : α // a∈Q}

def down (Q : Finset α) (e : Finset α) : Finset (Carrier Q) := e.subtype (·∈Q)
def up (Q : Finset α) (e : Finset (Carrier Q)) : Finset α :=
  e.map (Function.Embedding.subtype _)
def restrict (Q : Finset α) (H : Finset (Finset α)) : Finset (Finset (Carrier Q)) :=
  H.image (down Q)

@[simp] lemma mem_down {Q e : Finset α} {x : Carrier Q} : x∈down Q e ↔ x.val∈e := by
  simp [down]
@[simp] lemma up_down {Q e : Finset α} (he : e⊆Q) : up Q (down Q e)=e :=
  subtype_map_of_mem he
@[simp] lemma down_up {Q : Finset α} (e : Finset (Carrier Q)) : down Q (up Q e)=e := by
  ext x
  simp [up,Function.Embedding.subtype]
lemma up_injective (Q : Finset α) : Function.Injective (up Q) :=
  fun _ _ h => by simpa using congrArg (down Q) h
@[simp] lemma up_card {Q : Finset α} (e : Finset (Carrier Q)) : (up Q e).card=e.card := card_map _
lemma up_subset {Q : Finset α} (e : Finset (Carrier Q)) : up Q e⊆Q :=
  fun _ ha => property_of_mem_map_subtype e ha
lemma down_card {Q e : Finset α} (he : e⊆Q) : (down Q e).card=e.card := by
  rw [← up_card,up_down he]

lemma mem_restrict {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) {f : Finset (Carrier Q)} :
    f∈restrict Q H ↔ up Q f∈H := by
  constructor
  · intro hf
    obtain ⟨e,he,rfl⟩ := mem_image.mp hf
    rwa [up_down (hH e he)]
  · intro hf
    exact mem_image.mpr ⟨up Q f,hf,down_up f⟩

lemma down_injOn {Q : Finset α} {H : Finset (Finset α)} (hH : ∀ e∈H, e⊆Q) :
    Set.InjOn (down Q) H := by
  intro e he f hf hh
  rw [← up_down (hH e he),← up_down (hH f hf),hh]

lemma restrict_card {Q : Finset α} {H : Finset (Finset α)} (hH : ∀ e∈H, e⊆Q) :
    (restrict Q H).card=H.card := card_image_of_injOn (down_injOn hH)

lemma degree_all_eq {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (x : Carrier Q) : degree (restrict Q H) x=degree H x.val := by
  have he : (restrict Q H).filter (fun e => x∈e)=(H.filter (fun e => x.val∈e)).image (down Q) := by
    ext e
    simp only [restrict,mem_filter,mem_image]
    constructor
    · rintro ⟨⟨f,hf,rfl⟩,hx⟩
      exact ⟨f,⟨hf,mem_down.mp hx⟩,rfl⟩
    · rintro ⟨f,⟨hf,hx⟩,rfl⟩
      exact ⟨⟨f,hf,rfl⟩,mem_down.mpr hx⟩
  unfold degree
  rw [he]
  exact card_image_of_injOn (down_injOn (fun e he => hH e (mem_filter.mp he).1))

lemma restrict_induced {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (I : Finset (Carrier Q)) :
    (restrict Q H).filter (·⊆I)=restrict Q (H.filter (·⊆up Q I)) := by
  ext f
  simp only [restrict,mem_filter,mem_image]
  constructor
  · rintro ⟨⟨e,he,rfl⟩,hsub⟩
    refine ⟨e,⟨he,?_⟩,rfl⟩
    have hh := (map_subset_map (f := Function.Embedding.subtype (·∈Q))).mpr hsub
    change up Q (down Q e)⊆up Q I at hh
    rwa [up_down (hH e he)] at hh
  · rintro ⟨e,⟨he,hsub⟩,rfl⟩
    refine ⟨⟨e,he,rfl⟩,?_⟩
    apply (map_subset_map (f := Function.Embedding.subtype (·∈Q))).mp
    change up Q (down Q e)⊆up Q I
    rwa [up_down (hH e he)]

lemma degree_eq {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (x : Carrier Q) (k : ℕ) :
    degree (layer (restrict Q H) k) x = degree (layer H k) x.val := by
  have he : ((layer (restrict Q H) k).filter (fun e => x∈e)).image (up Q)=
      (layer H k).filter (fun e => x.val∈e) := by
    ext e
    constructor
    · intro hm
      obtain ⟨f,hf,rfl⟩ := mem_image.mp hm
      obtain ⟨hf,hx⟩ := mem_filter.mp hf
      obtain ⟨hf,hk⟩ := mem_filter.mp hf
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_restrict hH).mp hf,by simpa using hk⟩,?_⟩
      exact mem_map.mpr ⟨x,hx,rfl⟩
    · intro hm
      obtain ⟨he,hx⟩ := mem_filter.mp hm
      obtain ⟨he,hk⟩ := mem_filter.mp he
      refine mem_image.mpr ⟨down Q e,mem_filter.mpr ⟨mem_filter.mpr ⟨?_,?_⟩,mem_down.mpr hx⟩,up_down (hH e he)⟩
      · exact mem_image.mpr ⟨e,he,rfl⟩
      · rwa [down_card (hH e he)]
  unfold degree
  rw [← he,card_image_of_injective _ (up_injective Q)]

lemma pair_eq {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (x y : Carrier Q) :
    pairDegree (restrict Q H) x y = pairDegree H x.val y.val := by
  have he : ((restrict Q H).filter (fun e => x∈e ∧ y∈e)).image (up Q)=
      H.filter (fun e => x.val∈e ∧ y.val∈e) := by
    ext e
    constructor
    · intro hm
      obtain ⟨f,hf,rfl⟩ := mem_image.mp hm
      obtain ⟨hf,hx,hy⟩ := mem_filter.mp hf
      exact mem_filter.mpr ⟨(mem_restrict hH).mp hf,mem_map.mpr ⟨x,hx,rfl⟩,mem_map.mpr ⟨y,hy,rfl⟩⟩
    · intro hm
      obtain ⟨he,hx,hy⟩ := mem_filter.mp hm
      exact mem_image.mpr ⟨down Q e,mem_filter.mpr ⟨mem_image.mpr ⟨e,he,rfl⟩,
        mem_down.mpr hx,mem_down.mpr hy⟩,up_down (hH e he)⟩
  unfold pairDegree
  rw [← he,card_image_of_injective _ (up_injective Q)]

lemma up_inter {Q : Finset α} (e f : Finset (Carrier Q)) : up Q (e∩f)=up Q e∩up Q f :=
  map_inter _ _

lemma adj_eq {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (x y : Carrier Q) :
    Adj (restrict Q H) x y ↔ x.val≠y.val ∧ ({x.val,y.val}:Finset α)∈H := by
  simp only [Adj,mem_restrict hH,up,map_insert,map_singleton,Function.Embedding.subtype_apply]
  exact and_congr (not_congr Subtype.ext_iff) Iff.rfl

lemma intersections {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (K : ℕ)
    (hK : ∀ e∈H, ∀ f∈H, e≠f → (e∩f).card≤K) :
    ∀ e∈restrict Q H, ∀ f∈restrict Q H, e≠f → (e∩f).card≤K := by
  intro e he f hf hef
  rw [← up_card,up_inter]
  exact hK _ ((mem_restrict hH).mp he) _ ((mem_restrict hH).mp hf)
    (fun h => hef (up_injective Q h))

lemma common_eq [Fintype α] {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (x y : Carrier Q) :
    common (restrict Q H) x y = common H x.val y.val := by
  have he : up Q (both (restrict Q H) (restrict Q H) x y)=both H H x.val y.val := by
    ext z
    constructor
    · intro hz
      obtain ⟨w,hw,rfl⟩ := mem_map.mp hz
      obtain ⟨hx,hy⟩ := RegularizationCommonNeighbors.mem_both.mp hw
      exact RegularizationCommonNeighbors.mem_both.mpr
        ⟨(adj_eq hH x w).mp hx,(adj_eq hH y w).mp hy⟩
    · intro hz
      obtain ⟨hx,hy⟩ := RegularizationCommonNeighbors.mem_both.mp hz
      have hzQ : z∈Q := hH _ hx.2 (by simp)
      let w : Carrier Q := ⟨z,hzQ⟩
      exact mem_map.mpr ⟨w,RegularizationCommonNeighbors.mem_both.mpr
        ⟨(adj_eq hH x w).mpr hx,(adj_eq hH y w).mpr hy⟩,rfl⟩
  unfold common
  rw [← he,up_card]

lemma independent_iff {Q : Finset α} {H : Finset (Finset α)}
    (hH : ∀ e∈H, e⊆Q) (A : Finset (Carrier Q)) :
    (∀ e∈restrict Q H, ¬e⊆A) ↔ (∀ e∈H, ¬e⊆up Q A) := by
  constructor
  · intro hi e he hsub
    apply hi (down Q e) (mem_image.mpr ⟨e,he,rfl⟩)
    intro x hx
    have hm := hsub (mem_down.mp hx)
    obtain ⟨y,hy,hyx⟩ := mem_map.mp hm
    have hh : y=x := Subtype.ext hyx
    simpa only [hh] using hy
  · intro hi e he hsub
    apply hi (up Q e) ((mem_restrict hH).mp he)
    exact map_subset_map.mpr hsub

#print axioms degree_eq
#print axioms pair_eq
#print axioms independent_iff
#print axioms common_eq
#print axioms intersections
end
end Erdos773.FiniteHypergraphRestriction
