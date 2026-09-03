import Submission.Work

/-!
The OR (rather than mutual) Fubini ultrafilter extension of a triangle-free
base can contain triangles, but it always has a two-piece triangle-free
edge cover. It therefore cannot supply a witness for Erdős Problem 595.
-/

set_option autoImplicit false
open SimpleGraph Set

namespace Erdos595OneSided

variable {V : Type*}

/-- No transitive directed triangle can occur in the Fubini relation of
a triangle-free graph. -/
theorem no_three_fubini (G : SimpleGraph V) (hG : G.CliqueFree 3)
    (p q r : Ultrafilter V)
    (hpq : Erdos595Work.fubiniAdj G p q)
    (hpr : Erdos595Work.fubiniAdj G p r)
    (hqr : Erdos595Work.fubiniAdj G q r) : False := by
  classical
  obtain ⟨a,haq,har⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem hpq hpr)
  obtain ⟨b,hab,hbr⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem haq hqr)
  obtain ⟨c,hac,hbc⟩ := Ultrafilter.nonempty_of_mem (Filter.inter_mem har hbr)
  exact hG _ (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)

section Relation

variable {X : Type*} (R : X → X → Prop)
  (hR : ∀ a b c, R a b → R a c → R b c → False)

def symGraph : SimpleGraph X where
  Adj a b := R a b ∨ R b a
  symm := fun _ _ h => h.symm
  loopless := fun a h => h.elim (fun h => hR a a a h h h) (fun h => hR a a a h h h)

private lemma out_out {a b c : X} (hab : R a b) (hac : R a c)
    (hbc : (symGraph R hR).Adj b c) : False := by
  rcases hbc with hbc | hcb
  · exact hR a b c hab hac hbc
  · exact hR a c b hac hab hcb

private lemma in_in {a b c : X} (hba : R b a) (hca : R c a)
    (hbc : (symGraph R hR).Adj b c) : False := by
  rcases hbc with hbc | hcb
  · exact hR b c a hbc hba hca
  · exact hR c b a hcb hca hba

/-- Any tournament on four vertices has a transitive triangle. -/
theorem symGraph_cliqueFree : (symGraph R hR).CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have adj : ∀ i j : Fin 4, i ≠ j → (symGraph R hR).Adj (e i) (e j) :=
    fun i j hij => e.map_rel_iff.mpr hij
  have h01 := adj 0 1 (by decide)
  have h02 := adj 0 2 (by decide)
  have h03 := adj 0 3 (by decide)
  rcases h01 with h01 | h10 <;> rcases h02 with h02 | h20 <;>
    rcases h03 with h03 | h30
  · exact out_out R hR h01 h02 (adj 1 2 (by decide))
  · exact out_out R hR h01 h02 (adj 1 2 (by decide))
  · exact out_out R hR h01 h03 (adj 1 3 (by decide))
  · exact in_in R hR h20 h30 (adj 2 3 (by decide))
  · exact out_out R hR h02 h03 (adj 2 3 (by decide))
  · exact in_in R hR h10 h30 (adj 1 3 (by decide))
  · exact in_in R hR h10 h20 (adj 1 2 (by decide))
  · exact in_in R hR h10 h20 (adj 1 2 (by decide))

variable [LinearOrder X]

def forwardGraph : SimpleGraph X where
  Adj a b := (a < b ∧ R a b) ∨ (b < a ∧ R b a)
  symm := fun _ _ h => h.symm
  loopless := fun a h => h.elim (fun h => lt_irrefl a h.1) (fun h => lt_irrefl a h.1)

include hR in
theorem forwardGraph_cliqueFree : (forwardGraph R).CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a,b,c,hab,hac,hbc,_⟩ := SimpleGraph.is3Clique_iff.mp ht
  rcases hab with ⟨hab,rab⟩ | ⟨hba,rba⟩ <;>
    rcases hac with ⟨hac,rac⟩ | ⟨hca,rca⟩ <;>
    rcases hbc with ⟨hbc,rbc⟩ | ⟨hcb,rcb⟩
  · exact hR a b c rab rac rbc
  · exact hR a c b rac rab rcb
  · order
  · exact hR c a b rca rcb rab
  · exact hR b a c rba rbc rac
  · order
  · exact hR b c a rbc rba rca
  · exact hR c b a rcb rca rba

/-- Split edges according to their Fubini direction in a fixed order. -/
theorem symGraph_two_cover :
    ∃ H : Bool → SimpleGraph X, (∀ i, (H i).CliqueFree 3) ∧
      symGraph R hR = ⨆ i, H i := by
  classical
  let H : Bool → SimpleGraph X
    | false => forwardGraph R
    | true => forwardGraph (fun a b => R b a)
  refine ⟨H, ?_, ?_⟩
  · intro i
    cases i
    · exact forwardGraph_cliqueFree R hR
    · exact forwardGraph_cliqueFree (fun a b => R b a)
        (fun a b c hba hca hcb => hR c b a hcb hca hba)
  · ext a b
    simp only [SimpleGraph.iSup_adj]
    constructor
    · intro hab
      have hne : a ≠ b := (symGraph R hR).ne_of_adj hab
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rcases hab with hab | hba
        · exact ⟨false, Or.inl ⟨hlt,hab⟩⟩
        · exact ⟨true, Or.inl ⟨hlt,hba⟩⟩
      · rcases hab with hab | hba
        · exact ⟨true, Or.inr ⟨hgt,hab⟩⟩
        · exact ⟨false, Or.inr ⟨hgt,hba⟩⟩
    · rintro ⟨i,h⟩
      cases i
      · exact h.imp And.right And.right
      · exact (h.imp And.right And.right).symm

end Relation

/-- Adjacency needs only one of the two Fubini directions. -/
def orUltrafilterGraph (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    SimpleGraph (Ultrafilter V) :=
  symGraph (Erdos595Work.fubiniAdj G) (no_three_fubini G hG)

theorem orUltrafilterGraph_cliqueFree (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    (orUltrafilterGraph G hG).CliqueFree 4 :=
  symGraph_cliqueFree (Erdos595Work.fubiniAdj G) (no_three_fubini G hG)

theorem orUltrafilterGraph_two_cover (G : SimpleGraph V) (hG : G.CliqueFree 3) :
    ∃ H : Bool → SimpleGraph (Ultrafilter V), (∀ i, (H i).CliqueFree 3) ∧
      orUltrafilterGraph G hG = ⨆ i, H i := by
  classical
  letI : LinearOrder (Ultrafilter V) := IsWellOrder.linearOrder WellOrderingRel
  exact symGraph_two_cover (Erdos595Work.fubiniAdj G) (no_three_fubini G hG)

#print axioms orUltrafilterGraph_cliqueFree
#print axioms orUltrafilterGraph_two_cover

end Erdos595OneSided
