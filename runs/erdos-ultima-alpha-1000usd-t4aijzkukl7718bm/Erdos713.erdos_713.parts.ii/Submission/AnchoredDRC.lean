import FormalConjecturesUtil
import Submission.Verified

open Filter SimpleGraph Asymptotics

namespace Erdos713Anchors
open Finset Erdos713C6 Erdos713DRC

def augmented {A B : Type*} (R : A → B → Prop) (a : A) : Fin 2 ⊕ B → Prop :=
  Sum.elim (fun _ => True) (R a)

theorem bipGraph_contained_of_maps {A B V : Type*} (R : A → B → Prop) (G : SimpleGraph V)
    (f : A → V) (g : B → V) (hf : Function.Injective f) (hg : Function.Injective g)
    (hdis : ∀ a b, f a ≠ g b) (hAdj : ∀ a b, R a b → G.Adj (f a) (g b)) :
    bipGraph R ⊑ G := by
  refine ⟨⟨⟨Sum.elim f g, ?_⟩, ?_⟩⟩
  · intro x y hxy
    cases x with
    | inl a =>
      cases y with
      | inl a' => exact hxy.elim
      | inr b => exact hAdj a b hxy
    | inr b =>
      cases y with
      | inl a => exact (hAdj a b hxy).symm
      | inr b' => exact hxy.elim
  · intro x y hxy
    change Sum.elim f g x = Sum.elim f g y at hxy
    cases x with
    | inl a =>
      cases y with
      | inl a' => exact congrArg Sum.inl (hf hxy)
      | inr b => exact (hdis a b hxy).elim
    | inr b =>
      cases y with
      | inl a => exact (hdis a b hxy.symm).elim
      | inr b' => exact congrArg Sum.inr (hg hxy)

open scoped Classical in
theorem contained_of_anchored_heavy_set {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    (R : A → B → Prop) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v)
    (z : Fin 2 ↪ V) (S : Finset V) (hS : Fintype.card A ≤ S.card)
    (hSz : ∀ a ∈ S, ∀ i, G.Adj a (z i))
    (hgood : ∀ x ∈ S, ∀ y ∈ S,
      Fintype.card A + Fintype.card B + 2 ≤ Fintype.card (G.commonNeighbors x y)) :
    bipGraph (augmented R) ⊑ G := by
  classical
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset hS
  choose u v huv using hR
  let L := (univ : Finset A).image f ∪ (univ : Finset (Fin 2)).image z
  let t : B → Finset V := fun b => (G.commonNeighbors (f (u b)) (f (v b))).toFinset \ L
  have hL : L.card ≤ Fintype.card A + 2 := by
    apply (card_union_le _ _).trans
    exact Nat.add_le_add ((card_image_le).trans (by simp)) ((card_image_le).trans (by simp))
  have ht (b : B) : Fintype.card B ≤ (t b).card := by
    have hg := hgood (f (u b)) (hf ⟨u b, rfl⟩) (f (v b)) (hf ⟨v b, rfl⟩)
    have hh := card_le_card_sdiff_add_card (s := (G.commonNeighbors (f (u b)) (f (v b))).toFinset)
      (t := L)
    rw [Set.toFinset_card] at hh
    dsimp only [t]
    omega
  have hHall (U : Finset B) : U.card ≤ (U.biUnion t).card := by
    rcases U.eq_empty_or_nonempty with rfl | hU
    · simp
    obtain ⟨b, hb⟩ := hU
    exact (card_le_univ U).trans ((ht b).trans (card_le_card (subset_biUnion_of_mem t hb)))
  obtain ⟨g, hginj, hg⟩ := (all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  have hdis (a : A) (b : B) : f a ≠ g b := by
    intro hab
    exact (mem_sdiff.mp (hg b)).2
      (hab ▸ mem_union_left _ (mem_image_of_mem f (mem_univ a)))
  have hdisz (i : Fin 2) (b : B) : z i ≠ g b := by
    intro hab
    exact (mem_sdiff.mp (hg b)).2
      (hab ▸ mem_union_right _ (mem_image_of_mem z (mem_univ i)))
  have hAdj (a : A) (b : B) (hab : R a b) : G.Adj (f a) (g b) := by
    have hh : g b ∈ G.commonNeighbors (f (u b)) (f (v b)) := by
      simpa only [Set.mem_toFinset] using (mem_sdiff.mp (hg b)).1
    rcases huv b a hab with rfl | rfl
    · exact hh.1
    · exact hh.2
  apply bipGraph_contained_of_maps (augmented R) G f (Sum.elim z g) f.injective
  · intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (z.injective hxy)
      | inr b => exact (hdisz i b hxy).elim
    | inr b =>
      cases y with
      | inl i => exact (hdisz i b hxy.symm).elim
      | inr b' => exact congrArg Sum.inr (hginj hxy)
  · intro a b
    cases b with
    | inl i => exact (hSz (f a) (hf ⟨a, rfl⟩) i).ne
    | inr b => exact hdis a b
  · intro a b hab
    cases b with
    | inl i => exact hSz (f a) (hf ⟨a, rfl⟩) i
    | inr b => exact hAdj a b hab

open scoped Classical in
theorem degree_sq_le_of_no_anchored_heavy_set {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s k : ℕ)
    (h : ∀ x y : V, x ≠ y → ∀ S : Finset V, S ⊆ (G.commonNeighbors x y).toFinset →
      (∀ u ∈ S, ∀ v ∈ S, k ≤ Fintype.card (G.commonNeighbors u v)) → S.card ≤ s) :
    ∑ v, G.degree v ^ 2 ≤ (s + k ^ 2 + 1) * Fintype.card V ^ 2 := by
  classical
  have hrow (p : V × V) : Fintype.card (G.commonNeighbors p.1 p.2) ≤
      s + (((G.commonNeighbors p.1 p.2).toFinset ×ˢ
      (G.commonNeighbors p.1 p.2).toFinset).filter
        (fun q => Fintype.card (G.commonNeighbors q.1 q.2) < k)).card +
        if p.1 = p.2 then Fintype.card V else 0 := by
    by_cases hp : p.1 = p.2
    · simp only [hp, ite_true]
      have hc : Fintype.card (G.commonNeighbors p.2 p.2) ≤ Fintype.card V :=
        Fintype.card_le_of_injective (f := fun x : G.commonNeighbors p.2 p.2 => x.val)
          Subtype.val_injective
      omega
    · simp only [hp, ite_false, add_zero]
      obtain ⟨S, hS, hcard, hgood⟩ := clean_set G (G.commonNeighbors p.1 p.2).toFinset k
      rw [Set.toFinset_card] at hcard
      exact hcard.trans (Nat.add_le_add_right (h p.1 p.2 hp S hS hgood) _)
  rw [← sum_common_eq_sum_degree_sq]
  calc
    _ ≤ ∑ p : V × V, (s + (((G.commonNeighbors p.1 p.2).toFinset ×ˢ
        (G.commonNeighbors p.1 p.2).toFinset).filter
          (fun q => Fintype.card (G.commonNeighbors q.1 q.2) < k)).card +
          if p.1 = p.2 then Fintype.card V else 0) := sum_le_sum fun p _ => hrow p
    _ ≤ s * Fintype.card V ^ 2 + k ^ 2 * Fintype.card V ^ 2 + Fintype.card V ^ 2 := by
      simp only [sum_add_distrib]
      have hc : (∑ _ : V × V, s) = s * Fintype.card V ^ 2 := by
        simp [Fintype.card_prod, pow_two, mul_comm]
      have hd : (∑ p : V × V, if p.1 = p.2 then Fintype.card V else 0) =
          Fintype.card V ^ 2 := by
        simp [Fintype.sum_prod_type, pow_two]
      rw [hc, hd]
      exact Nat.add_le_add_right (Nat.add_le_add_left (sum_bad_pairs_le G k) _) _
    _ = _ := by ring

open scoped Classical in
theorem augmented_edge_sq_le {A B V : Type*} [Fintype A] [Fintype B] [Fintype V]
    (R : A → B → Prop) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v)
    (hfree : (bipGraph (augmented R)).Free G) :
    G.edgeFinset.card ^ 2 ≤
      (Fintype.card A + (Fintype.card A + Fintype.card B + 2) ^ 2 + 1) * Fintype.card V ^ 3 := by
  classical
  have hb := degree_sq_le_of_no_anchored_heavy_set G (Fintype.card A)
    (Fintype.card A + Fintype.card B + 2) (by
      intro x y hxy S hS hg
      by_contra hcard
      let z : Fin 2 ↪ V := ⟨![x,y], by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all⟩
      apply hfree
      apply contained_of_anchored_heavy_set R G hR z S (by omega) ?_ hg
      intro a ha i
      have hh : a ∈ G.commonNeighbors x y := by simpa only [Set.mem_toFinset] using hS ha
      fin_cases i
      · exact hh.1.symm
      · exact hh.2.symm)
  have hc := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun v => G.degree v)
  rw [card_univ, sum_degrees_eq_twice_card_edges] at hc
  have hm := Nat.mul_le_mul_left (Fintype.card V) hb
  nlinarith

end Erdos713Anchors

#print axioms Erdos713Anchors.augmented_edge_sq_le

namespace Erdos713Anchors
open Finset Erdos713C6 Erdos713DRC

theorem extremal_sq_le {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v) (n : ℕ) :
    (extremalNumber n (bipGraph (augmented R))) ^ 2 ≤
      (Fintype.card A + (Fintype.card A + Fintype.card B + 2) ^ 2 + 1) * n ^ 3 := by
  classical
  let S : Finset (SimpleGraph (Fin n)) := {G | (bipGraph (augmented R)).Free G}
  change (S.sup (fun G => G.edgeFinset.card)) ^ 2 ≤ _
  by_cases hS : S.Nonempty
  · obtain ⟨G, hG, he⟩ := exists_mem_eq_sup S hS (fun G => G.edgeFinset.card)
    rw [he]
    have hfree : (bipGraph (augmented R)).Free G := by simpa [S] using hG
    simpa only [Fintype.card_fin] using augmented_edge_sq_le R G hR hfree
  · rw [not_nonempty_iff_eq_empty.mp hS]
    simp

theorem exponent_upper_of_containment {A B W : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v)
    {H : SimpleGraph W} (hH : H ⊑ bipGraph (augmented R)) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ≤ (3 : ℝ) / 2 := by
  have hO : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop]
      (fun n : ℕ => (extremalNumber n H : ℝ)) :=
    (isBigO_const_mul_left_iff hc).mp h.isBigO_symm
  have hP : (fun n : ℕ => (n : ℝ) ^ (a * (2 : ℝ))) =O[atTop]
      (fun n : ℕ => (extremalNumber n H : ℝ) ^ (2 : ℕ)) := by
    have he (n : ℕ) : ((n : ℝ) ^ a) ^ (2 : ℕ) = (n : ℝ) ^ (a * (2 : ℝ)) := by
      have hh := Real.rpow_mul_natCast (Nat.cast_nonneg (α := ℝ) n) a 2
      norm_num only [Nat.cast_ofNat] at hh
      exact hh.symm
    simpa only [he] using hO.pow 2
  have hB : (fun n : ℕ => (extremalNumber n H : ℝ) ^ (2 : ℕ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (3 : ℝ)) := by
    apply IsBigO.of_bound ((Fintype.card A + (Fintype.card A + Fintype.card B + 2) ^ 2 + 1 : ℕ) : ℝ)
    filter_upwards with n
    rw [Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
    have hn3 : (n : ℝ) ^ (3 : ℝ) = (n : ℝ) ^ (3 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (n : ℝ) 3
    rw [hn3, Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg _) _)]
    exact_mod_cast (Nat.pow_le_pow_left (hH.extremalNumber_le (n := n)) 2).trans
      (extremal_sq_le R hR n)
  have hExp := Erdos713C4.exponent_le_of_isBigO (hP.trans hB)
  linarith

theorem exponent_eq_of_containment {A B W : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v)
    {H : SimpleGraph W} (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ bipGraph (augmented R))
    {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a = (3 : ℝ) / 2 := by
  apply le_antisymm (exponent_upper_of_containment R hR hhi hc h)
  have hO : (fun n : ℕ => (extremalNumber n H : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ a) :=
    (isBigO_const_mul_right_iff hc).mp h.isBigO
  apply Erdos713C4.lower_exponent_of_prime_bound hO
  intro p hp
  exact (Erdos713C4.extremal_lower_prime p hp).trans hlo.extremalNumber_le

theorem rational_of_containment {A B W : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (hR : ∀ b, ∃ u v, ∀ a, R a b → a = u ∨ a = v)
    {H : SimpleGraph W} (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ bipGraph (augmented R))
    {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  refine ⟨3 / 2, ?_⟩
  simpa using (exponent_eq_of_containment R hR hlo hhi hc h).symm


end Erdos713Anchors

#print axioms Erdos713Anchors.rational_of_containment

namespace Erdos713Anchors
open Finset Erdos713C6 Erdos713DRC

open scoped Classical in
theorem contained_in_augmented {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) (E : Set B) (hE : Nat.card E ≤ 2) :
    bipGraph R ⊑ bipGraph (augmented (fun a (b : ↥(Eᶜ)) => R a b.val)) := by
  classical
  let e : E ↪ Fin 2 := Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hE))
  let g : B ↪ Fin 2 ⊕ ↥(Eᶜ) := (Equiv.Set.sumCompl E).symm.toEmbedding.trans
    (e.sumMap (Function.Embedding.refl _))
  apply bipGraph_contained_of_maps R _ Sum.inl (fun b => Sum.inr (g b)) Sum.inl_injective
    (Sum.inr_injective.comp g.injective) (by simp)
  intro a b hab
  by_cases hb : b ∈ E
  · simp [g, Equiv.Set.sumCompl_symm_apply_of_mem hb, bipGraph, augmented]
  · simpa [g, Equiv.Set.sumCompl_symm_apply_of_notMem hb, bipGraph, augmented] using hab

open scoped Classical in
theorem rational_of_exceptional_columns {A B W : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (R : A → B → Prop) (E : Set B) (hE : Nat.card E ≤ 2)
    (hR : ∀ b ∉ E, Nat.card {a // R a b} ≤ 2)
    {H : SimpleGraph W} (hlo : Erdos713C4.K22 ⊑ H) (hhi : H ⊑ bipGraph R)
    {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  let R' : A → ↥(Eᶜ) → Prop := fun a b => R a b.val
  have hR' (b : ↥(Eᶜ)) : Fintype.card {a // R' a b} ≤ 2 := by
    simpa only [R', Nat.card_eq_fintype_card] using hR b.val b.prop
  exact rational_of_containment R' (pair_cover_of_degree_two R' hR') hlo
    (hhi.trans (contained_in_augmented R E hE)) hc h

theorem rational_of_bipartition {W : Type*} [Fintype W] (H : SimpleGraph W)
    (S E : Set W) (hB : H.IsBipartiteWith S Sᶜ) (hE : Nat.card E ≤ 2)
    (hdeg : ∀ v ∈ Sᶜ, v ∉ E → Nat.card (H.neighborSet v) ≤ 2)
    (hlo : Erdos713C4.K22 ⊑ H) {a c : ℝ} (hc : c ≠ 0)
    (h : IsEquivalent atTop (fun n : ℕ => (extremalNumber n H : ℝ))
      (fun n : ℕ => c * (n : ℝ) ^ a)) : a ∈ Set.range ((↑) : ℚ → ℝ) := by
  classical
  haveI : Nonempty S := by
    obtain ⟨f⟩ := hlo
    have he : H.Adj (f (Sum.inl 0)) (f (Sum.inr 0)) :=
      f.toHom.map_adj (by simp [Erdos713C4.K22, completeBipartiteGraph])
    rcases hB.2 he with ⟨hu, _⟩ | ⟨_, hv⟩
    · exact ⟨⟨_, hu⟩⟩
    · exact ⟨⟨_, hv⟩⟩
  let R : S → ↥(Sᶜ) → Prop := fun u v => H.Adj u.val v.val
  let E' : Set ↥(Sᶜ) := {b | b.val ∈ E}
  have hE' : Nat.card E' ≤ 2 := by
    let f : E' ↪ E := ⟨fun b => ⟨b.val.val, b.prop⟩, by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : E => z.val) hxy⟩
    have hh := Fintype.card_le_of_embedding f
    simp only [Fintype.card_eq_nat_card] at hh
    exact hh.trans hE
  have hR (b : ↥(Sᶜ)) (hb : b ∉ E') : Nat.card {a : S // R a b} ≤ 2 := by
    let f : {a : S // R a b} ↪ H.neighborSet b.val :=
      ⟨fun a => ⟨a.val.val, a.prop.symm⟩, by
          intro x y hxy
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : H.neighborSet b.val => z.val) hxy⟩
    have hh := Fintype.card_le_of_embedding f
    simp only [Fintype.card_eq_nat_card] at hh
    exact hh.trans (hdeg b.val b.prop hb)
  have hhi : H ⊑ bipGraph R := by
    let e := (Equiv.Set.sumCompl S).symm
    refine ⟨⟨⟨e, ?_⟩, e.injective⟩⟩
    intro u v huv
    rcases hB.2 huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · have hv' : v ∉ S := hv
      simpa [e, Equiv.Set.sumCompl_symm_apply_of_mem hu,
        Equiv.Set.sumCompl_symm_apply_of_notMem hv', bipGraph, R] using huv
    · have hu' : u ∉ S := hu
      simpa [e, Equiv.Set.sumCompl_symm_apply_of_mem hv,
        Equiv.Set.sumCompl_symm_apply_of_notMem hu', bipGraph, R] using huv.symm
  exact rational_of_exceptional_columns R E' hE' hR hlo hhi hc h

end Erdos713Anchors

#print axioms Erdos713Anchors.rational_of_bipartition
