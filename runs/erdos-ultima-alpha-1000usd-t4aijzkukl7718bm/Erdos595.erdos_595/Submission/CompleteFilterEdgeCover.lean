import Submission.CompleteFilterProduct
import Submission.BadEdgeUltrafilter

/-!
Countably complete filter products of finitely triangle-free-edge-coverable
coordinate graphs have a FINITE triangle-free edge cover. The finite bounds
need not be uniform. This rules out a product construction; it is not a
settlement of Erdős 595. The auxiliary ultrafilter is ordinary, not asserted
to be countably complete.
-/

set_option autoImplicit false
open Set Filter SimpleGraph
namespace Erdos595CompleteFilterEdgeCover
open Erdos595CompleteFilterProduct Erdos595BadEdge

variable {I : Type*} {A : I → Type*}

def CoversWith {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ H : Fin n → SimpleGraph V, (∀ j, (H j).CliqueFree 3) ∧
    ∀ a b, G.Adj a b → ∃ j, (H j).Adj a b

/-- A uniform finite edge-cover bound on a positive set of coordinates is
sufficient. Positivity is weaker than membership in the original filter. -/
theorem cover_of_positive (F : Filter I) [F.NeBot]
    (G : ∀ i, SimpleGraph (A i)) (S : Set I) (n : ℕ)
    (hS : (F ⊓ Filter.principal S).NeBot)
    (hcov : ∀ i ∈ S, CoversWith (G i) n) :
    CoversWith (graph F G) n := by
  classical
  letI : (F ⊓ Filter.principal S).NeBot := hS
  obtain ⟨U,hU⟩ := Ultrafilter.exists_le (F ⊓ Filter.principal S)
  have hUF : (U : Filter I) ≤ F := hU.trans inf_le_left
  have hUS : ∀ᶠ i in (U : Filter I), i ∈ S :=
    (hU.trans inf_le_right) (Filter.mem_principal_self S)
  let H (i : I) : Fin n → SimpleGraph (A i) :=
    if hi : i ∈ S then (hcov i hi).choose else fun _ => ⊥
  have hH (i : I) (hi : i ∈ S) :
      (∀ j, (H i j).CliqueFree 3) ∧
      ∀ a b, (G i).Adj a b → ∃ j, (H i j).Adj a b := by
    simpa only [H, dif_pos hi] using (hcov i hi).choose_spec
  let K (j : Fin n) := graph (U : Filter I) (fun i => H i j)
  refine ⟨K, ?_, ?_⟩
  · intro j t ht
    obtain ⟨x,y,z,hxy,hxz,hyz,_⟩ := SimpleGraph.is3Clique_iff.mp ht
    change ∀ᶠ i in (U : Filter I), (H i j).Adj (x i) (y i) at hxy
    change ∀ᶠ i in (U : Filter I), (H i j).Adj (x i) (z i) at hxz
    change ∀ᶠ i in (U : Filter I), (H i j).Adj (y i) (z i) at hyz
    obtain ⟨i,hi,hxy,hxz,hyz⟩ := (hUS.and (hxy.and (hxz.and hyz))).exists
    exact (hH i hi).1 j _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hxy,hxz,hyz⟩)
  · intro x y hxy
    have hxyU : ∀ᶠ i in (U : Filter I), (G i).Adj (x i) (y i) := hUF hxy
    have hex : ∀ᶠ i in (U : Filter I), ∃ j, (H i j).Adj (x i) (y i) :=
      (hUS.and hxyU).mono fun i hi => (hH i hi.1).2 _ _ hi.2
    exact Ultrafilter.eventually_exists_iff.mp hex

/-- Finite coordinate cover bounds cannot escape to infinity on every
positive set of a proper countably complete filter. -/
theorem finite_cover (F : Filter I) [F.NeBot] [CountableInterFilter F]
    (G : ∀ i, SimpleGraph (A i)) (hG : ∀ i, FiniteCover (G i)) :
    FiniteCover (graph F G) := by
  classical
  have hb : ∀ i, ∃ n, CoversWith (G i) n := hG
  choose bound hbound using hb
  obtain ⟨n,hn⟩ := positive_fibre F bound
  refine ⟨n, cover_of_positive F G {i | bound i = n} n hn ?_⟩
  intro i hi
  simpa only [show bound i = n from hi] using hbound i

theorem countable_cover (F : Filter I) [F.NeBot] [CountableInterFilter F]
    (G : ∀ i, SimpleGraph (A i)) (hG : ∀ i, FiniteCover (G i)) :
    Erdos595Work.IsCountableUnionOfTriangleFree (graph F G) :=
  (finite_cover F G hG).countable

#print axioms cover_of_positive
#print axioms finite_cover
#print axioms countable_cover
end Erdos595CompleteFilterEdgeCover
