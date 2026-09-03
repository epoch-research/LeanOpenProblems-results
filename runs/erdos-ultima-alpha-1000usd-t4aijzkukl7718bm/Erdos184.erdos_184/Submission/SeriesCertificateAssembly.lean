import Submission.SeriesCertificateData

/-! Independent local series certificates can be assembled along shared retained
vertices. Only the contracted private vertices must avoid all other pieces. -/
open scoped Classical
namespace Erdos184Work.LabelKernel
open Erdos184Serial
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

namespace SeriesAssembly
variable {I X : Type*} {E F U W : I → Type*}
  [Fintype I] [DecidableEq I] [DecidableEq X]
  [∀ i, Fintype (E i)] [∀ i, Fintype (F i)] [∀ i, Fintype (U i)] [∀ i, Fintype (W i)]
  [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (F i)]
  [∀ i, DecidableEq (U i)] [∀ i, DecidableEq (W i)]
  (d : ∀ i, SeriesData (E i) (F i) (U i) (W i))
  (src dst : ∀ i, E i → U i) (fineSrc fineDst : ∀ i, F i → W i)
  (place : ∀ i, W i ↪ X)

noncomputable local instance : DecidableEq (Σ i, E i) := Classical.decEq _
noncomputable local instance : DecidableEq (Σ i, F i) := Classical.decEq _

def coarseSource (e : Σ i, E i) : X := place e.1 ((d e.1).vertex (src e.1 e.2))
def coarseTarget (e : Σ i, E i) : X := place e.1 ((d e.1).vertex (dst e.1 e.2))
def fineSource (f : Σ i, F i) : X := place f.1 (fineSrc f.1 f.2)
def fineTarget (f : Σ i, F i) : X := place f.1 (fineDst f.1 f.2)

def data : SeriesData (Σ i, E i) (Σ i, F i) X X where
  fiber f := ⟨f.1, (d f.1).fiber f.2⟩
  representative e := ⟨e.1, (d e.1).representative e.2⟩
  vertex := id
  rank f := (d f.1).rank f.2
  parent f := ⟨f.1, (d f.1).parent f.2⟩
  link f := place f.1 ((d f.1).link f.2)

def pieceEdge (i : I) : F i ↪ (Σ j, F j) := Function.Embedding.sigmaMk i

lemma fiber_eq_map (i : I) (e : E i) :
    Finset.univ.filter (fun f => (data d place).fiber f = ⟨i,e⟩) =
      (Finset.univ.filter (fun f => (d i).fiber f = e)).map (pieceEdge i) := by
  ext ⟨j,f⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map,data,pieceEdge]
  constructor
  · intro h
    have hji : j = i := congrArg Sigma.fst h
    subst j
    exact ⟨f,eq_of_heq (Sigma.mk.inj h).2,rfl⟩
  · rintro ⟨g,hg,hgf⟩
    cases hgf
    exact congrArg (Sigma.mk i) hg

variable (hvalid : ∀ i, (d i).Valid (src i) (dst i) (fineSrc i) (fineDst i))

include hvalid in
lemma boundary (i : I) (e : E i) (x : X) :
    parity (fineSource fineSrc place) (fineTarget fineDst place)
      (Finset.univ.filter (fun f => (data d place).fiber f = ⟨i,e⟩)) x =
    if coarseSource d src place ⟨i,e⟩ = x ∨ coarseTarget d dst place ⟨i,e⟩ = x then 1 else 0 := by
  rw [fiber_eq_map]
  simp only [parity,Finset.sum_map]
  change (∑ f ∈ Finset.univ.filter (fun f => (d i).fiber f = e),
    if place i (fineSrc i f) = x ∨ place i (fineDst i f) = x then (1 : ZMod 2) else 0) =
    if place i ((d i).vertex (src i e)) = x ∨ place i ((d i).vertex (dst i e)) = x then 1 else 0
  by_cases hx : ∃ y, place i y = x
  · obtain ⟨y,rfl⟩ := hx
    simpa only [parity,(place i).injective.eq_iff] using (hvalid i).2.2.2 e y
  · have hn (y : W i) : ¬ place i y = x := fun h => hx ⟨y,h⟩
    simp only [hn,false_or,if_false,Finset.sum_const_zero]

variable (hprivate : ∀ i f, f ≠ (d i).representative ((d i).fiber f) →
  ∀ j, j ≠ i → ∀ g,
    place j (fineSrc j g) ≠ place i ((d i).link f) ∧
    place j (fineDst j g) ≠ place i ((d i).link f))

include hprivate in
lemma private_incidence (i : I) (f : F i)
    (hf : f ≠ (d i).representative ((d i).fiber f))
    (hlocal : Finset.univ.filter (fun g => fineSrc i g = (d i).link f ∨
        fineDst i g = (d i).link f) = {f,(d i).parent f}) :
    Finset.univ.filter (fun g => fineSource fineSrc place g = (data d place).link ⟨i,f⟩ ∨
      fineTarget fineDst place g = (data d place).link ⟨i,f⟩) =
        {⟨i,f⟩,(data d place).parent ⟨i,f⟩} := by
  ext ⟨j,g⟩
  by_cases hji : j = i
  · subst j
    have hg := Finset.ext_iff.mp hlocal g
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
      Finset.mem_singleton,data,fineSource,fineTarget,(place i).injective.eq_iff,
      Sigma.mk.inj_iff,heq_eq_eq,true_and] using hg
  · have hp := hprivate i f hf j hji g
    have hne (a : F i) : (⟨j,g⟩ : Σ k, F k) ≠ ⟨i,a⟩ := fun h => hji (congrArg Sigma.fst h)
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
      Finset.mem_singleton,data,fineSource,fineTarget,hp.1,hp.2,hne,false_or]

noncomputable def certificate : SeriesCertificate
    (coarseSource d src place) (coarseTarget d dst place)
    (fineSource fineSrc place) (fineTarget fineDst place) where
  fiber := (data d place).fiber
  representative := (data d place).representative
  fiber_representative e := by
    rcases e with ⟨i,e⟩
    exact congrArg (Sigma.mk i) ((hvalid i).1 e)
  vertex := Function.Embedding.refl X
  rank := (data d place).rank
  parent := (data d place).parent
  descent f := by
    rcases f with ⟨i,f⟩
    by_cases hf : f = (d i).representative ((d i).fiber f)
    · exact Or.inl (congrArg (Sigma.mk i) hf)
    · rcases (hvalid i).2.2.1 f with h | ⟨hr,hp,hl⟩
      · exact (hf h).elim
      · exact Or.inr ⟨hr,congrArg (Sigma.mk i) hp,place i ((d i).link f),
          private_incidence d fineSrc fineDst place hprivate i f hf hl⟩
  boundary e x := by
    rcases e with ⟨i,e⟩
    exact boundary d src dst fineSrc fineDst place hvalid i e x

#print axioms certificate
end SeriesAssembly
end Erdos184Work.LabelKernel
