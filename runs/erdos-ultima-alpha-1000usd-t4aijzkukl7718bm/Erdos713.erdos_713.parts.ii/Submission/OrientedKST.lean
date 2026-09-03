import FormalConjecturesUtil
import Submission.CompactPruningAudit

/-! One-sided Kővári–Sós–Turán bounds, keeping track of the root's
bipartition side. No unrestricted gluing theorem is assumed. -/
open SimpleGraph Filter Asymptotics Finset
namespace Erdos713OrientedKST
open Erdos713KST

noncomputable def copyOfEmbeddings {V : Type*} (G : SimpleGraph V) {s t : ℕ}
    (f : Fin s ↪ V) (g : Fin t ↪ V)
    (hadj : ∀ i j, G.Adj (f i) (g j)) : (Kst s t).Copy G := by
  refine ⟨⟨Sum.elim f g, ?_⟩, ?_⟩
  · rintro (i | j) (i' | j') h
    · simp at h
    · exact hadj i j'
    · exact (hadj i' j).symm
    · simp at h
  · rintro (i | j) (i' | j') h
    · exact congrArg Sum.inl (f.injective h)
    · exact ((hadj i j').ne h).elim
    · exact ((hadj i' j).ne h.symm).elim
    · exact congrArg Sum.inr (g.injective h)

open scoped Classical in
lemma sum_descFactorial_degree_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Set V) {s t : ℕ}
    (hno : ∀ (f : Fin s ↪ V) (g : Fin t ↪ V),
      (∀ i j, G.Adj (f i) (g j)) → (∀ j, g j ∈ T) → False) :
    ∑ v ∈ T.toFinset, (G.degree v).descFactorial s ≤ t * (Fintype.card V)^s := by
  classical
  let r : V → (Fin s ↪ V) → Prop := fun v f => ∀ i, G.Adj v (f i)
  have hAbove (v : V) : ((univ : Finset (Fin s ↪ V)).bipartiteAbove r v).card =
      (G.degree v).descFactorial s := by
    let e : ↥((univ : Finset (Fin s ↪ V)).bipartiteAbove r v) ≃
        (Fin s ↪ G.neighborSet v) :=
      { toFun := fun f =>
          ⟨fun i => ⟨f.val i, ((mem_bipartiteAbove r).mp f.prop).2 i⟩,
            fun i j hij => f.val.injective (congrArg Subtype.val hij)⟩
        invFun := fun f =>
          ⟨f.trans (Function.Embedding.subtype _),
            (mem_bipartiteAbove r).mpr ⟨mem_univ _, fun i => (f i).prop⟩⟩
        left_inv := by intro f; rfl
        right_inv := by intro f; rfl }
    rw [← Fintype.card_coe, Fintype.card_congr e, Fintype.card_embedding_eq,
      Fintype.card_fin, card_neighborSet_eq_degree]
  have hBelow (f : Fin s ↪ V) : (T.toFinset.bipartiteBelow r f).card ≤ t := by
    by_contra hn
    obtain ⟨g,hg⟩ := Function.Embedding.exists_of_card_le_finset
      (show Fintype.card (Fin t) ≤ (T.toFinset.bipartiteBelow r f).card by
        simpa using (show t ≤ (T.toFinset.bipartiteBelow r f).card by omega))
    have hm (j : Fin t) := (mem_bipartiteBelow r).mp (hg ⟨j,rfl⟩)
    exact hno f g (fun i j => ((hm j).2 i).symm)
      (fun j => Set.mem_toFinset.mp (hm j).1)
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := r) (s := T.toFinset) (t := (univ : Finset (Fin s ↪ V)))
  simp_rw [hAbove] at hsum
  rw [hsum]
  calc
    ∑ f : Fin s ↪ V, (T.toFinset.bipartiteBelow r f).card ≤
        ∑ _ : Fin s ↪ V, t := sum_le_sum fun f _ => hBelow f
    _ = t * (Fintype.card V).descFactorial s := by simp [Nat.mul_comm]
    _ ≤ t * (Fintype.card V)^s := Nat.mul_le_mul_left t (Nat.descFactorial_le_pow _ _)

open scoped Classical in
lemma sum_degree_pow_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Set V) {s t : ℕ}
    (hs : 1 ≤ s)
    (hno : ∀ (f : Fin s ↪ V) (g : Fin t ↪ V),
      (∀ i j, G.Adj (f i) (g j)) → (∀ j, g j ∈ T) → False) :
    ∑ v ∈ T.toFinset, G.degree v ^ s ≤
      (s+1)^s * (t+1) * (Fintype.card V)^s := by
  have hT : T.toFinset.card ≤ Fintype.card V := card_le_univ _
  calc
    ∑ v ∈ T.toFinset, G.degree v ^ s ≤
        ∑ v ∈ T.toFinset, (s+1)^s*((G.degree v).descFactorial s+1) :=
      sum_le_sum fun _ _ => pow_le_descFactorial _ _
    _ = (s+1)^s*((∑ v ∈ T.toFinset, (G.degree v).descFactorial s)+T.toFinset.card) := by
      simp [sum_add_distrib, ← mul_sum]
    _ ≤ (s+1)^s*(t*(Fintype.card V)^s+(Fintype.card V)^s) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add (sum_descFactorial_degree_le G T hno)
        (hT.trans (Nat.le_self_pow (by omega) _)))
    _ = _ := by ring

open scoped Classical in
lemma edge_pow_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (T : Set V) {s t : ℕ}
    (hB : G.IsBipartiteWith T Tᶜ) (hs : 1 ≤ s)
    (hno : ∀ (f : Fin s ↪ V) (g : Fin t ↪ V),
      (∀ i j, G.Adj (f i) (g j)) → (∀ j, g j ∈ T) → False) :
    G.edgeFinset.card^s ≤ (s+1)^s*(t+1)*(Fintype.card V)^(s-1+s) := by
  have hJ := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg T.toFinset
    (f := fun v => (G.degree v : ℝ)) (show (1 : ℝ) ≤ s by exact_mod_cast hs)
    (fun _ _ => Nat.cast_nonneg _)
  have he : (s : ℝ)-1 = ((s-1 : ℕ) : ℝ) := by rw [Nat.cast_sub hs,Nat.cast_one]
  rw [he] at hJ
  simp only [Real.rpow_natCast] at hJ
  have hJN : (∑ v ∈ T.toFinset, G.degree v)^s ≤
      T.toFinset.card^(s-1)*∑ v ∈ T.toFinset, G.degree v^s := by exact_mod_cast hJ
  have hE : ∑ v ∈ T.toFinset, G.degree v = G.edgeFinset.card :=
    isBipartiteWith_sum_degrees_eq_card_edges (s := T.toFinset) (t := Tᶜ.toFinset)
      (by simpa using hB)
  rw [hE] at hJN
  calc
    G.edgeFinset.card^s ≤ T.toFinset.card^(s-1)*∑ v ∈ T.toFinset, G.degree v^s := hJN
    _ ≤ (Fintype.card V)^(s-1)*((s+1)^s*(t+1)*(Fintype.card V)^s) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (card_le_univ _) _)
        (sum_degree_pow_le G T hs hno)
    _ = _ := by rw [pow_add]; ring

open scoped Classical in
/-- A complete bipartite copy can be forced with any specified root on a
specified side of a bipartite host, with the usual KST upper exponent. -/
lemma edge_pow_le_of_root_excluded {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Set V) {s t : ℕ}
    (hB : G.IsBipartiteWith S Sᶜ) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (x : Fin s ⊕ Fin t) (hroot : ∀ f : (Kst s t).Copy G, f x ∉ S) :
    G.edgeFinset.card^s ≤ (s+1)^s*(t+1)*(Fintype.card V)^(s-1+s) := by
  classical
  cases x with
  | inl i =>
    apply edge_pow_le G Sᶜ (by simpa using hB.symm) hs
    intro f g hadj hg
    apply hroot (copyOfEmbeddings G f g hadj)
    change f i ∈ S
    have hh := hB.mem_of_adj (hadj i ⟨0,by omega⟩)
    exact (hh.resolve_right (fun h => hg ⟨0,by omega⟩ h.2)).1
  | inr j =>
    apply edge_pow_le G S hB hs
    intro f g hadj hg
    exact hroot (copyOfEmbeddings G f g hadj) (hg j)

#print axioms edge_pow_le_of_root_excluded
end Erdos713OrientedKST
