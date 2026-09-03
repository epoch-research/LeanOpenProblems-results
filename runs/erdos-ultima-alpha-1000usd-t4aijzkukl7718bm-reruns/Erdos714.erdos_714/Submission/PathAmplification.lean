import Submission.ColoredTensorThinning
import Submission.BlowupThinning

/-!
Three-layer relational compositions are covered by complete blocks indexed by
the middle edges. At the critical walk-amplification scale, every K44-free
edge thinning loses a power. No girth or unique-path assumption is needed.
This is a construction obstruction, not a resolution of Erdős 714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 2000000
namespace Erdos714PathAmplification
open Erdos714Packing

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

/-- The bipartite relation obtained by composing three arbitrary relations. -/
def host (R : A → Finset B) (S : B → Finset C) (T : C → Finset D) : SimpleGraph (A ⊕ D) :=
  Erdos714Tensor.incidence fun a d => ∃ b ∈ R a, ∃ c ∈ S b, d ∈ T c

/-- An actual middle edge; no count of distinct endpoint paths is substituted. -/
abbrev Index (S : B → Finset C) := Σ b : B, S b

/-- The two sides of the block have separate vertex types, so no loop issue arises. -/
def block (R : A → Finset B) (S : B → Finset C) (T : C → Finset D) (i : Index S) :
    Finset (A ⊕ D) :=
  (dual R i.1).map ⟨Sum.inl,Sum.inl_injective⟩ ∪
    (T i.2.val).map ⟨Sum.inr,Sum.inr_injective⟩

omit [Fintype B] [Fintype C] [Fintype D] in
lemma block_size (R : A → Finset B) (S : B → Finset C) (T : C → Finset D)
    (d : ℕ) (hR : ∀ b, (dual R b).card ≤ d) (hT : ∀ c, (T c).card ≤ d) (i : Index S) :
    (block R S T i).card ≤ 2*d := by
  have h := card_union_le ((dual R i.1).map ⟨Sum.inl,Sum.inl_injective⟩)
    ((T i.2.val).map ⟨Sum.inr,Sum.inr_injective⟩)
  rw [card_map,card_map] at h
  exact h.trans (by have := hR i.1; have := hT i.2.val; omega)

omit [Fintype B] [Fintype C] [Fintype D] in
lemma forward_cover (R : A → Finset B) (S : B → Finset C) (T : C → Finset D)
    (a : A) (d : D) (h : ∃ b ∈ R a, ∃ c ∈ S b, d ∈ T c) :
    ∃ i : Index S, Sum.inl a ∈ block R S T i ∧ Sum.inr d ∈ block R S T i := by
  obtain ⟨b,hb,c,hc,hd⟩ := h
  refine ⟨⟨b,c,hc⟩,?_,?_⟩ <;> simp [block,dual,hb,hd]

omit [Fintype B] [Fintype C] [Fintype D] in
lemma edge_cover (R : A → Finset B) (S : B → Finset C) (T : C → Finset D)
    (H : SimpleGraph (A ⊕ D)) (hH : H ≤ host R S T) :
    ∀ v w, H.Adj v w → ∃ i : Index S, v ∈ block R S T i ∧ w ∈ block R S T i := by
  intro v w hvw
  have h := hH hvw
  cases v with
  | inl a =>
    cases w with
    | inl a' => exact False.elim h
    | inr d => exact forward_cover R S T a d h
  | inr d =>
    cases w with
    | inr d' => exact False.elim h
    | inl a =>
      obtain ⟨i,hi,hj⟩ := forward_cover R S T a d h
      exact ⟨i,hj,hi⟩

omit [Fintype C] in
/-- Every selected edge is covered, including arbitrary nonuniform edge deletions. -/
theorem fourth_power (R : A → Finset B) (S : B → Finset C) (T : C → Finset D)
    (H : SimpleGraph (A ⊕ D)) (hH : H ≤ host R S T)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (d : ℕ) (hR : ∀ b, (dual R b).card ≤ d) (hT : ∀ c, (T c).card ≤ d) :
    H.edgeFinset.card^4 ≤ 10368*(∑ b, (S b).card)^4*d^7 := by
  have h := Erdos714BlockThinning.fourth_power_of_block_cover H hf
    (block R S T) d (block_size R S T d hR hT) (edge_cover R S T H hH)
  simpa only [Index,Fintype.card_sigma,Fintype.card_coe] using h

omit [Fintype C] in
/-- The tempting q^5-middle-edge, q-by-q-block scale is insufficient. -/
theorem critical_fourth (R : A → Finset B) (S : B → Finset C) (T : C → Finset D)
    (H : SimpleGraph (A ⊕ D)) (hH : H ≤ host R S T)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (q : ℕ) (hS : ∑ b, (S b).card ≤ q^5)
    (hR : ∀ b, (dual R b).card ≤ q) (hT : ∀ c, (T c).card ≤ q) :
    H.edgeFinset.card^4 ≤ 10368*q^27 := by
  calc
    _ ≤ 10368*(∑ b, (S b).card)^4*q^7 := fourth_power R S T H hH hf q hR hT
    _ ≤ 10368*(q^5)^4*q^7 := by gcongr
    _ = _ := by ring

omit [Fintype C] in
/-- A fixed fraction of q^7 edges forces the field/degree parameter to be bounded. -/
theorem size_budget (R : A → Finset B) (S : B → Finset C) (T : C → Finset D)
    (H : SimpleGraph (A ⊕ D)) (hH : H ≤ host R S T)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (q K : ℕ) (hq : 0 < q) (hS : ∑ b, (S b).card ≤ q^5)
    (hR : ∀ b, (dual R b).card ≤ q) (hT : ∀ c, (T c).card ≤ q)
    (he : q^7 ≤ K*H.edgeFinset.card) : q ≤ 10368*K^4 := by
  have hb := critical_fourth R S T H hH hf q hS hR hT
  have h : q^27*q ≤ q^27*(10368*K^4) := by
    calc
      _ = (q^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left he 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(10368*q^27) := Nat.mul_le_mul_left _ hb
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos hq 27)

section Walk
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- All alternating length-three walks in the base bipartite set system.
Simple-path-only variants are subgraphs and are therefore covered as well. -/
def walkThree (R : X → Finset Y) : SimpleGraph (X ⊕ Y) := host R (dual R) R

/-- At most q^4 base vertices on the row side and degree at most q on both
sides suffice. High girth and uniqueness of projected paths cannot improve this bound. -/
theorem walk_thinning (R : X → Finset Y) (H : SimpleGraph (X ⊕ Y))
    (hH : H ≤ walkThree R) (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (q : ℕ) (hX : Fintype.card X ≤ q^4)
    (hR : ∀ x, (R x).card ≤ q) (hD : ∀ y, (dual R y).card ≤ q) :
    H.edgeFinset.card^4 ≤ 10368*q^27 := by
  apply critical_fourth R (dual R) R H hH hf q ?_ hD hR
  rw [Erdos714Blowup.sum_dual_card]
  calc
    _ ≤ ∑ _x : X, q := sum_le_sum (fun x _ => hR x)
    _ = Fintype.card X*q := by simp
    _ ≤ q^4*q := Nat.mul_le_mul_right _ hX
    _ = q^5 := by ring

end Walk
end Erdos714PathAmplification
#print axioms Erdos714PathAmplification.block_size
#print axioms Erdos714PathAmplification.forward_cover
#print axioms Erdos714PathAmplification.edge_cover
#print axioms Erdos714PathAmplification.fourth_power
#print axioms Erdos714PathAmplification.critical_fourth
#print axioms Erdos714PathAmplification.size_budget
#print axioms Erdos714PathAmplification.walk_thinning
