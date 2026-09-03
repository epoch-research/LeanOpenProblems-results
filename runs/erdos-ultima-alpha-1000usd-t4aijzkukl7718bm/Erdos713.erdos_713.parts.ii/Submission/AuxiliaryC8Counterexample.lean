import FormalConjecturesUtil
import Submission.GlobalThetaLinks

/-! A finite obstruction to inferring higher girth in edge double-neighbourhoods.
This is not a counterexample to Erdős 713. -/
open SimpleGraph Finset
namespace Erdos713AuxC8
open Erdos713C6 Erdos713ThetaGram Erdos713GlobalTheta
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1000

def R (i j : Fin 5) : Prop := Nat.testBit ((![31,7,19,25,13] : Fin 5 → ℕ) i) j.val = true
instance : DecidableRel R := fun _ _ => inferInstanceAs (Decidable (_ = true))

lemma symmetric : ∀ i j, R i j ↔ R j i := by decide

/-- A guarded finite certificate, with only seven freely varying vertices
once the anchor is fixed. Early incidence tests keep the check small. -/
lemma certificate : ∀ d a b : Fin 5, a ≠ d → b ≠ d → a ≠ b →
    ∀ z w : Fin 5, z ≠ w → R d z → R d w → R a z → R b z → R a w → R b w →
    ∀ x y : Fin 5, x ≠ z → x ≠ w → y ≠ z → y ≠ w → x ≠ y →
      R d x → R d y → R a x → R b y →
      ∀ c : Fin 5, c ≠ d → c ≠ a → c ≠ b → ¬ (R c x ∧ R c y) := by decide

lemma no_link (d : Fin 5) : ¬ HasTheta (link R d) := by
  rintro ⟨a,b,ha,hb,h00,h10,h01,h11,h02,h22,h13,h23⟩
  have hA : Function.Injective (fun i => (a i).val) := Subtype.val_injective.comp ha
  have hB : Function.Injective (fun i => (b i).val) := Subtype.val_injective.comp hb
  exact certificate d (a 0).val (a 1).val (a 0).prop (a 1).prop
    (hA.ne (by decide : (0 : Fin 3) ≠ 1)) (b 0).val (b 1).val
    (hB.ne (by decide : (0 : Fin 4) ≠ 1)) (b 0).prop (b 1).prop h00 h10 h01 h11
    (b 2).val (b 3).val (hB.ne (by decide)) (hB.ne (by decide))
    (hB.ne (by decide)) (hB.ne (by decide)) (hB.ne (by decide))
    (b 2).prop (b 3).prop h02 h13 (a 2).val (a 2).prop
    (hA.ne (by decide)) (hA.ne (by decide)) ⟨h22,h23⟩

abbrev host := bipGraph R
instance : DecidableRel host.Adj := by
  rintro (a | a) (b | b) <;> dsimp [host,bipGraph] <;> infer_instance

lemma bipartite : host.IsBipartite := by
  refine ⟨Coloring.mk (fun z => Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1) z) ?_⟩
  rintro (a | a) (b | b) hab <;> simp_all [host,bipGraph]

lemma host_edges : host.edgeFinset.card = 17 := by decide

lemma free : pattern.Free host := by
  apply (free_iff_both_links R).mpr
  refine ⟨no_link,?_⟩
  have he : (fun b a => R a b) = R := by funext a b; exact propext (symmetric b a)
  have hQ : ∀ T : Fin 5 → Fin 5 → Prop, T = R → ∀ d, ¬ HasTheta (link T d) := by
    intro T hT
    subst T
    exact no_link
  exact hQ _ he

abbrev u : Fin 5 ⊕ Fin 5 := .inl 0
abbrev v : Fin 5 ⊕ Fin 5 := .inr 0

def localSet : Set (Fin 5 ⊕ Fin 5) := {z | z ≠ u ∧ z ≠ v ∧ (host.Adj u z ∨ host.Adj v z)}

def cycleMap : Fin 8 → Fin 5 ⊕ Fin 5 :=
  ![.inl 1, .inr 1, .inl 2, .inr 4, .inl 3, .inr 3, .inl 4, .inr 2]

lemma cycleMap_mem (i : Fin 8) : cycleMap i ∈ localSet := by
  fin_cases i <;> simp [cycleMap,localSet,u,v,host,bipGraph,R] <;> decide

lemma cycleMap_injective : Function.Injective cycleMap := by decide

lemma cycleMap_adj : ∀ i j, (cycleGraph 8).Adj i j → host.Adj (cycleMap i) (cycleMap j) := by
  decide

lemma cycle_in_auxiliary : cycleGraph 8 ⊑ host.induce localSet := by
  refine ⟨⟨⟨fun i => ⟨cycleMap i,cycleMap_mem i⟩,?_⟩,?_⟩⟩
  · exact cycleMap_adj _ _
  · intro i j hij
    exact cycleMap_injective (congrArg Subtype.val hij)

lemma auxiliary_counterexample :
    pattern.Free host ∧ host.Adj u v ∧ cycleGraph 8 ⊑ host.induce localSet :=
  ⟨free,by rfl,cycle_in_auxiliary⟩

/-- This negates an auxiliary inference, not the original conjecture. -/
theorem not_every_auxiliary_C8_free :
    ¬ (∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IsBipartite →
      pattern.Free G → ∀ u v, G.Adj u v →
        (cycleGraph 8).Free (G.induce {z | z ≠ u ∧ z ≠ v ∧ (G.Adj u z ∨ G.Adj v z)})) := by
  intro h
  exact h (Fin 5 ⊕ Fin 5) host bipartite free u v (by rfl) cycle_in_auxiliary

#print axioms not_every_auxiliary_C8_free
#print axioms host_edges
#print axioms auxiliary_counterexample
end Erdos713AuxC8
