import FormalConjecturesUtil
import Submission.ForestCover

/-! Tripling one shore of a forest cannot create an eight-cycle. -/
open SimpleGraph
namespace Erdos713TripleShoreC8
open Erdos713OrientedCloneC8 Erdos713ForestCover
set_option maxHeartbeats 2000000
variable {A B : Type*}

lemma consecutive_roots_equal (R : A → B → Prop)
    (hR : (graph (⊥ : SimpleGraph B) R).IsAcyclic)
    (p : Fin 4 → A) (q : Fin 4 → B) (hq : Function.Injective q)
    (hA : ∀ i, R (p i) (q i)) (hB : ∀ i, R (p (i+1)) (q i)) : p 0 = p 1 := by
  let f : Fin 8 → B ⊕ A :=
    ![.inr (p 0),.inl (q 0),.inr (p 1),.inl (q 1),
      .inr (p 2),.inl (q 2),.inr (p 3),.inl (q 3)]
  have hf (i : Fin 8) : (graph (⊥ : SimpleGraph B) R).Adj (f i) (f (i+1)) := by
    fin_cases i
    · exact hA 0
    · exact hB 0
    · exact hA 1
    · exact hB 1
    · exact hA 2
    · exact hB 2
    · exact hA 3
    · exact hB 3
  have hh := forest_edge_repeats hR f hf
  simpa [f,Sym2.eq_iff,hq.eq_iff] using hh

theorem no_octagon (R : A → B → Prop)
    (hR : (graph (⊥ : SimpleGraph B) R).IsAcyclic)
    (p : Fin 4 → A × Fin 3) (q : Fin 4 → B)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hA : ∀ i, R (p i).1 (q i)) (hB : ∀ i, R (p (i+1)).1 (q i)) : False := by
  have hr (a : Fin 4) : (p a).1 = (p (a+1)).1 := by
    simpa only [add_zero,add_assoc] using
      consecutive_roots_equal R hR (fun i => (p (a+i)).1) (fun i => q (a+i))
        (hq.comp (add_right_injective a)) (fun i => hA (a+i))
        (fun i => by simpa only [add_assoc] using hB (a+i))
  have h0 (i : Fin 4) : (p i).1 = (p 0).1 := by
    fin_cases i
    · rfl
    · exact (hr 0).symm
    · exact (hr 1).symm.trans (hr 0).symm
    · exact hr 3
  have hi : Function.Injective (fun i => (p i).2) := by
    intro i j hij
    exact hp (Prod.ext ((h0 i).trans (h0 j).symm) hij)
  have hh := Fintype.card_le_of_injective _ hi
  norm_num at hh

/-- Extract the alternating shores from an injective cycle map. -/
lemma of_cycle_map (R : A → B → Prop)
    (hf : ∀ (p : Fin 4 → A) (q : Fin 4 → B), Function.Injective p → Function.Injective q →
      (∀ i, R (p i) (q i)) → (∀ i, R (p (i+1)) (q i)) → False)
    (f : Fin 8 → B ⊕ A) (hinj : Function.Injective f)
    (ha : ∀ i, (graph (⊥ : SimpleGraph B) R).Adj (f i) (f (i+1)))
    (a : A) (h0 : f 0 = .inr a) : False := by
  have stepL (i : Fin 8) (a : A) (h : f i = .inr a) : ∃ b, f (i+1) = .inl b := by
    have hh := ha i
    rcases he : f (i+1) with b|b
    · exact ⟨b,rfl⟩
    · simp [h,he,graph] at hh
  have stepR (i : Fin 8) (b : B) (h : f i = .inl b) : ∃ a, f (i+1) = .inr a := by
    have hh := ha i
    rcases he : f (i+1) with a|a
    · simp [h,he,graph] at hh
    · exact ⟨a,rfl⟩
  obtain ⟨b0,h1⟩ := stepL 0 a h0
  obtain ⟨a1,h2⟩ := stepR 1 b0 h1
  obtain ⟨b1,h3⟩ := stepL 2 a1 h2
  obtain ⟨a2,h4⟩ := stepR 3 b1 h3
  obtain ⟨b2,h5⟩ := stepL 4 a2 h4
  obtain ⟨a3,h6⟩ := stepR 5 b2 h5
  obtain ⟨b3,h7⟩ := stepL 6 a3 h6
  change f 1 = .inl b0 at h1
  change f 2 = .inr a1 at h2
  change f 3 = .inl b1 at h3
  change f 4 = .inr a2 at h4
  change f 5 = .inl b2 at h5
  change f 6 = .inr a3 at h6
  change f 7 = .inl b3 at h7
  let p : Fin 4 → A := ![a,a1,a2,a3]
  let q : Fin 4 → B := ![b0,b1,b2,b3]
  let e : Fin 4 → Fin 8 := ![0,2,4,6]
  let o : Fin 4 → Fin 8 := ![1,3,5,7]
  have hpv (i : Fin 4) : Sum.inr (p i) = f (e i) := by
    fin_cases i <;> simp [p,e,h0,h2,h4,h6]
  have hqv (i : Fin 4) : Sum.inl (q i) = f (o i) := by
    fin_cases i <;> simp [q,o,h1,h3,h5,h7]
  have he : Function.Injective e := by decide
  have ho : Function.Injective o := by decide
  apply hf p q
  · intro i j hij
    apply he
    apply hinj
    rw [← hpv,← hpv,hij]
  · intro i j hij
    apply ho
    apply hinj
    rw [← hqv,← hqv,hij]
  · intro i
    have hh := ha (e i)
    fin_cases i <;> simpa [e,p,q,h0,h1,h2,h3,h4,h5,h6,h7,graph] using hh
  · intro i
    have hh := ha (o i)
    fin_cases i <;> simpa [o,p,q,h0,h1,h2,h3,h4,h5,h6,h7,graph] using hh

lemma free_of_no_octagon (R : A → B → Prop)
    (hf : ∀ (p : Fin 4 → A) (q : Fin 4 → B), Function.Injective p → Function.Injective q →
      (∀ i, R (p i) (q i)) → (∀ i, R (p (i+1)) (q i)) → False) :
    (cycleGraph 8).Free (graph (⊥ : SimpleGraph B) R) := by
  rintro ⟨f⟩
  have ha (i : Fin 8) : (graph (⊥ : SimpleGraph B) R).Adj (f i) (f (i+1)) :=
    f.toHom.map_rel (cycleGraph_adj.mpr (Or.inr (by abel)))
  rcases h0 : f 0 with b|a
  · have hh := ha 0
    rcases h1 : f 1 with b'|a
    · simp [h0,h1,graph] at hh
    · apply of_cycle_map R hf (fun i => f (i+1)) (f.injective.comp (add_left_injective 1))
        (fun i => by simpa only [add_assoc] using ha (i+1)) a
      exact h1
  · exact of_cycle_map R hf f f.injective ha a h0

theorem triple_free (R : A → B → Prop)
    (hR : (graph (⊥ : SimpleGraph B) R).IsAcyclic) :
    (cycleGraph 8).Free (graph (⊥ : SimpleGraph B) (fun p : A × Fin 3 => R p.1)) :=
  free_of_no_octagon _ (no_octagon R hR)

#print axioms no_octagon
#print axioms triple_free
end Erdos713TripleShoreC8
