import Submission.FiniteCliqueUltrafilterColoring

/-!
The full OR Fubini extension after a mutual first extension of a countable
K4-free graph is countably triangle-free edge-covered. In particular this
excludes every order-oriented second extension of that MUTUAL first stage.
It does not address two order-oriented stages or settle Erdős 595.
-/
set_option autoImplicit false
open SimpleGraph Set Filter
namespace Erdos595OrAfterMutual
open Erdos595Work Erdos595OneSided Erdos595FiniteCliqueUltrafilter

variable {V : Type*} (G : SimpleGraph V) (hG : G.CliqueFree 4)

abbrev first := ultrafilterGraph G hG
abbrev full := orGraph (first G hG)
  (finiteCliques_of_cliqueFree _ (ultrafilterGraph_cliqueFree G hG))

def Supported (P : Ultrafilter (Ultrafilter V)) : Prop :=
  ∃ S : Set V, (G.induce S).CliqueFree 3 ∧ {p | S ∈ p} ∈ P

/-- Only the TARGET of one Fubini direction is needed for this support. -/
lemma target_supported {P Q : Ultrafilter (Ultrafilter V)}
    (h : fubiniAdj (first G hG) P Q) : Supported G Q := by
  obtain ⟨p,hp⟩ := Ultrafilter.nonempty_of_mem h
  refine ⟨{v | G.neighborSet v ∈ p},ultrafilter_trace_cliqueFree G hG p,?_⟩
  exact Filter.mem_of_superset hp (fun q hq => hq.2)

noncomputable def support (P : Ultrafilter (Ultrafilter V)) : Set V :=
  by
    classical
    exact if h : Supported G P then h.choose else ∅

lemma support_spec {P : Ultrafilter (Ultrafilter V)} (h : Supported G P) :
    (G.induce (support G P)).CliqueFree 3 ∧ {p | support G P ∈ p} ∈ P := by
  classical
  have he : support G P = h.choose := dif_pos h
  rw [he]
  exact h.choose_spec

lemma support_ne_empty {P : Ultrafilter (Ultrafilter V)} (h : Supported G P) :
    support G P ≠ ∅ := by
  intro he
  have hm := (support_spec G h).2
  simp only [he,Ultrafilter.empty_notMem,setOf_false] at hm

lemma supported_of_same {P Q : Ultrafilter (Ultrafilter V)}
    (he : support G P = support G Q) (hQ : Supported G Q) : Supported G P := by
  classical
  by_contra hP
  have hp : support G P = ∅ := dif_neg hP
  exact support_ne_empty G hQ (he.symm.trans hp)

/-- The elementary three-point extraction, with a common support. -/
lemma no_three_on {A : Type*} (K : SimpleGraph A) (S : Set A)
    (hS : (K.induce S).CliqueFree 3) (P Q R : Ultrafilter A)
    (hP : S ∈ P) (hQ : S ∈ Q) (hR : S ∈ R)
    (hPQ : fubiniAdj K P Q) (hPR : fubiniAdj K P R)
    (hQR : fubiniAdj K Q R) : False := by
  classical
  obtain ⟨a,ha,haQ,haR⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hP (Filter.inter_mem hPQ hPR))
  obtain ⟨b,hb,hab,hbR⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hQ (Filter.inter_mem haQ hQR))
  obtain ⟨c,hc,hac,hbc⟩ := Ultrafilter.nonempty_of_mem
    (Filter.inter_mem hR (Filter.inter_mem haR hbR))
  exact hS _ (SimpleGraph.is3Clique_triple_iff.mpr
    (show (K.induce S).Adj ⟨a,ha⟩ ⟨b,hb⟩ ∧
      (K.induce S).Adj ⟨a,ha⟩ ⟨c,hc⟩ ∧
      (K.induce S).Adj ⟨b,hb⟩ ⟨c,hc⟩ from ⟨hab,hac,hbc⟩))

lemma no_three_same_support (P Q R : Ultrafilter (Ultrafilter V))
    (hPQ : fubiniAdj (first G hG) P Q)
    (hPR : fubiniAdj (first G hG) P R)
    (hQR : fubiniAdj (first G hG) Q R)
    (heQ : support G P = support G Q) (heR : support G P = support G R) : False := by
  have hQ := target_supported G hG hPQ
  have hR := target_supported G hG hPR
  have hP := supported_of_same G heQ hQ
  have hsP := support_spec G hP
  have hsQ := support_spec G hQ
  have hsR := support_spec G hR
  rw [← heQ] at hsQ
  rw [← heR] at hsR
  exact no_three_on (first G hG) {p | support G P ∈ p}
    (ultrafilterGraph_support_cliqueFree G hG _ hsP.1)
    P Q R hsP.2 hsQ.2 hsR.2 hPQ hPR hQR

/-- No countable-completeness assumption on any ultrafilter is used. -/
theorem countable_cover [Countable V] : IsCountableUnionOfTriangleFree (full G hG) := by
  classical
  letI : LinearOrder (Ultrafilter (Ultrafilter V)) :=
    IsWellOrder.linearOrder WellOrderingRel
  let e : V ↪ ℕ := ⟨(exists_injective_nat V).choose,(exists_injective_nat V).choose_spec⟩
  let enc : Set V → ℕ → Fin 2 := fun S n => if ∃ v ∈ S, e v = n then 1 else 0
  have henc : Function.Injective enc := by
    intro S T he
    ext v
    have hv := congrFun he (e v)
    have hS : (∃ w ∈ S, e w = e v) ↔ v ∈ S :=
      ⟨fun ⟨w,hw,he⟩ => e.injective he ▸ hw,fun hv => ⟨v,hv,rfl⟩⟩
    have hT : (∃ w ∈ T, e w = e v) ↔ v ∈ T :=
      ⟨fun ⟨w,hw,he⟩ => e.injective he ▸ hw,fun hv => ⟨v,hv,rfl⟩⟩
    simp only [enc,hS,hT] at hv
    by_cases hS : v ∈ S <;> by_cases hT : v ∈ T <;> simp_all
  let f := fun P => enc (support G P)
  apply countable_union_of_vertex_pieces _ f
  intro i
  let D := fun P Q => f P = i ∧ f Q = i ∧ fubiniAdj (first G hG) P Q
  have hD : ∀ P Q R, D P Q → D P R → D Q R → False := by
    intro P Q R hPQ hPR hQR
    exact no_three_same_support G hG P Q R hPQ.2.2 hPR.2.2 hQR.2.2
      (henc (hPQ.1.trans hPQ.2.1.symm)) (henc (hPR.1.trans hPR.2.1.symm))
  obtain ⟨H,hH,hcov⟩ := symGraph_two_cover D hD
  have he : vertexPiece (full G hG) f i = symGraph D hD := by
    ext P Q
    change ((fubiniAdj (first G hG) P Q ∨ fubiniAdj (first G hG) Q P) ∧
      f P = i ∧ f Q = i) ↔
      (f P = i ∧ f Q = i ∧ fubiniAdj (first G hG) P Q) ∨
      (f Q = i ∧ f P = i ∧ fubiniAdj (first G hG) Q P)
    tauto
  refine ⟨fun n => H (n != 0),fun n => hH _,?_⟩
  rw [he,hcov]
  ext P Q
  simp only [SimpleGraph.iSup_adj]
  constructor
  · rintro ⟨b,hb⟩
    cases b
    · exact ⟨0,hb⟩
    · exact ⟨1,hb⟩
  · rintro ⟨n,hn⟩
    exact ⟨_,hn⟩

theorem ordered_countable_cover [Countable V] [LinearOrder (Ultrafilter (Ultrafilter V))] :
    IsCountableUnionOfTriangleFree (Erdos595OrderedUltrafilter.graph (first G hG)) := by
  let f : Erdos595OrderedUltrafilter.graph (first G hG) →g full G hG :=
    ⟨id,fun h => h.imp And.right And.right⟩
  exact countable_union_of_hom f (countable_cover G hG)

#print axioms target_supported
#print axioms countable_cover
#print axioms ordered_countable_cover
end Erdos595OrAfterMutual
