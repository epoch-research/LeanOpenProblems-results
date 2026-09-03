import FormalConjecturesUtil
import Submission.CompactComponentsAudit

/-! Finite leaf pruning, preserving attained growth thresholds and the same
superlinear pure-power asymptotic, followed by the small-component criterion. -/
open SimpleGraph Filter Asymptotics
namespace Erdos713Pruning
open Erdos713Rate
universe u

/-- A finite sequence of deletions of vertices of degree at most one. -/
inductive PrunesTo {W : Type u} (G : SimpleGraph W) : Set W → Prop where
  | start : PrunesTo G Set.univ
  | delete {S : Set W} (h : PrunesTo G S) (x : S)
      (hx : Nat.card ((G.induce S).neighborSet x) ≤ 1) : PrunesTo G (S \ {x.val})

noncomputable def eraseIso {W : Type*} (G : SimpleGraph W) (S : Set W) (x : S) :
    ((G.induce S).induce {x}ᶜ) ≃g G.induce (S \ {x.val}) := by
  let e : ↥({x}ᶜ : Set S) ≃ ↥(S \ {x.val}) :=
    { toFun := fun v => ⟨v.val.val,v.val.prop,fun hv => v.prop (Subtype.ext hv)⟩
      invFun := fun v => ⟨⟨v.val,v.prop.1⟩,fun hv => v.prop.2 (congrArg Subtype.val hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨e,Iff.rfl⟩

theorem exists_core {W : Type u} [Fintype W] (G : SimpleGraph W) :
    ∃ S : Set W, PrunesTo G S ∧ ∀ v, 2 ≤ Nat.card ((G.induce S).neighborSet v) := by
  classical
  suffices hP : ∀ k : ℕ, ∀ S : Set W, Fintype.card S = k → PrunesTo G S →
      ∃ T : Set W, PrunesTo G T ∧ ∀ v, 2 ≤ Nat.card ((G.induce T).neighborSet v) from
    hP _ Set.univ rfl .start
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro S hcard hS
    by_cases hd : ∀ v, 2 ≤ Nat.card ((G.induce S).neighborSet v)
    · exact ⟨S,hS,hd⟩
    push_neg at hd
    obtain ⟨x,hx⟩ := hd
    have hsmall : Fintype.card ↥(S \ {x.val}) < k := by
      rw [← Fintype.card_congr (eraseIso G S x).toEquiv]
      exact (Fintype.card_subtype_lt (x := x) (by simp)).trans_eq hcard
    exact ih _ hsmall _ (by simp only [Fintype.card_eq_nat_card]) (.delete hS x (by omega))

/-- No induced subgraph of minimum degree two loses a vertex during pruning. -/
theorem PrunesTo.retains {W : Type u} [Fintype W] {G : SimpleGraph W} {S T : Set W}
    (hP : PrunesTo G S) (hT : ∀ v, 2 ≤ Nat.card ((G.induce T).neighborSet v)) : T ⊆ S := by
  classical
  induction hP with
  | start => exact Set.subset_univ T
  | @delete S hS x hx ih =>
    intro v hv
    refine ⟨ih hv,?_⟩
    intro he
    have hxT : x.val ∈ T := he ▸ hv
    let f : (G.induce T).neighborSet ⟨x.val,hxT⟩ ↪ (G.induce S).neighborSet x :=
      ⟨fun w => ⟨⟨w.val.val,ih w.val.prop⟩,w.prop⟩,by
        intro w z hwz
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun y : (G.induce S).neighborSet x => y.val.val) hwz⟩
    have hf := Fintype.card_le_of_embedding f
    simp only [Fintype.card_eq_nat_card] at hf
    have hd := hT ⟨x.val,hxT⟩
    omega

theorem core_unique {W : Type u} [Fintype W] {G : SimpleGraph W} {S T : Set W}
    (hS : PrunesTo G S) (hT : PrunesTo G T)
    (hdS : ∀ v, 2 ≤ Nat.card ((G.induce S).neighborSet v))
    (hdT : ∀ v, 2 ≤ Nat.card ((G.induce T).neighborSet v)) : S = T :=
  Set.Subset.antisymm (hT.retains hdS) (hS.retains hdT)

noncomputable def coreVertices {W : Type u} [Fintype W] (G : SimpleGraph W) : Set W :=
  Classical.choose (exists_core G)

theorem core_prunes {W : Type u} [Fintype W] (G : SimpleGraph W) :
    PrunesTo G (coreVertices G) := (Classical.choose_spec (exists_core G)).1

theorem core_min_degree {W : Type u} [Fintype W] (G : SimpleGraph W) :
    ∀ v, 2 ≤ Nat.card ((G.induce (coreVertices G)).neighborSet v) :=
  (Classical.choose_spec (exists_core G)).2

theorem PrunesTo.asymptotic {W : Type u} [Fintype W] {G : SimpleGraph W} {S : Set W}
    (hP : PrunesTo G S) {a c : ℝ} (ha : 1 < a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => c*(n : ℝ)^a)) :
    IsEquivalent atTop (fun n : ℕ => (extremalNumber n (G.induce S) : ℝ))
      (fun n : ℕ => c*(n : ℝ)^a) := by
  classical
  induction hP with
  | start => simpa only [extremalNumber_congr_right (induceUnivIso G)] using h
  | @delete S hS x hx ih =>
    have hx' : (G.induce S).degree x ≤ 1 := by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hx
    have hdel : IsEquivalent atTop
        (fun n : ℕ => (extremalNumber n ((G.induce S).induce {x}ᶜ) : ℝ))
        (fun n : ℕ => c*(n : ℝ)^a) := by
      by_cases hz : (G.induce S).degree x = 0
      · exact Erdos713Leaf.isolated_asymptotic _ hz ih
      · have h1 : (G.induce S).degree x = 1 := by omega
        obtain ⟨y,hxy,_⟩ := degree_eq_one_iff_existsUnique_adj.mp h1
        exact Erdos713Leaf.leaf_asymptotic _ h1 hxy ha hc ih
    simpa only [extremalNumber_congr_right (eraseIso G S x)] using hdel

theorem PrunesTo.rate {W : Type u} [Fintype W] {G : SimpleGraph W} {S : Set W}
    (hP : PrunesTo G S) {r : ℝ} (hR : HasRate (G.induce S) r) : HasRate G r := by
  classical
  induction hP with
  | start => exact iso_rate (induceUnivIso G).symm hR
  | @delete S hS x hx ih =>
    apply ih
    have hdel := iso_rate (eraseIso G S x) hR
    have hx' : (G.induce S).degree x ≤ 1 := by
      simpa only [Nat.card_eq_fintype_card,card_neighborSet_eq_degree] using hx
    by_cases hz : (G.induce S).degree x = 0
    · exact isolated_rate _ hz hdel
    · have h1 : (G.induce S).degree x = 1 := by omega
      obtain ⟨y,hxy,_⟩ := degree_eq_one_iff_existsUnique_adj.mp h1
      exact leaf_rate _ h1 hxy hdel

def SmallComponents {W : Type*} (G : SimpleGraph W) : Prop :=
  ∀ C : G.ConnectedComponent, ∃ S : Set C,
    C.toSimpleGraph.IsBipartiteWith S Sᶜ ∧ Nat.card S ≤ 3

theorem PrunesTo.rational_of_small_components {W : Type u} [Fintype W]
    {G : SimpleGraph W} {S : Set W} (hP : PrunesTo G S)
    (hS : SmallComponents (G.induce S)) {a c : ℝ} (ha : 1 ≤ a) (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n G : ℝ))
      (fun n : ℕ => c*(n : ℝ)^a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  obtain ⟨r,hr⟩ := Erdos713ComponentRates.rate_of_small_component_bipartitions (G.induce S) hS
  exact ⟨r,(exponent_eq (hP.rate hr) ha hc h).symm⟩

theorem component_min_degree {W : Type*} [Fintype W] (G : SimpleGraph W)
    (hd : ∀ v, 2 ≤ Nat.card (G.neighborSet v)) (C : G.ConnectedComponent) :
    ∀ v, 2 ≤ Nat.card (C.toSimpleGraph.neighborSet v) := by
  intro v
  let e : C.toSimpleGraph.neighborSet v ≃ G.neighborSet v.val :=
    { toFun := fun w => ⟨w.val.val,w.prop⟩
      invFun := fun w => ⟨⟨w.val,C.mem_supp_of_adj_mem_supp v.prop w.prop⟩,w.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact hd v.val

#print axioms exists_core
#print axioms core_unique
#print axioms core_min_degree
#print axioms PrunesTo.asymptotic
#print axioms PrunesTo.rational_of_small_components
end Erdos713Pruning
