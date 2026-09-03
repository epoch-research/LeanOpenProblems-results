import Submission.WittCircleBlocks

/-!
Arbitrary edge-thinning obstruction for odd-degree binary Witt norm-circle
hosts. The cover uses projective scales, and therefore only O(q^5) blocks.
This is not an obstruction to arbitrary graphs and does not settle Erdős714.
-/
noncomputable section
open Classical SimpleGraph Finset
open scoped CharTwo
set_option maxHeartbeats 3000000
namespace Erdos714WittCircleBlocks
open Erdos714WittNormCircle Erdos714BinaryInverseTrace
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]
local instance : Fintype (Projectivization F E) := Fintype.ofFinite _

lemma finrank_two (hE : Fintype.card E=Fintype.card F^2) : Module.finrank F E=2 := by
  have hc := Module.card_eq_pow_finrank (K := F) (V := E)
  rw [hE] at hc
  exact (Nat.pow_right_injective (Fintype.one_lt_card : 1 < Fintype.card F)) hc.symm

lemma projective_card (hE : Fintype.card E=Fintype.card F^2) :
    Fintype.card (Projectivization F E)=Fintype.card F+1 := by
  simpa only [Nat.card_eq_fintype_card] using
    Projectivization.card_of_finrank_two F E (finrank_two hE)

def block (η : E) (i : (E × E) × Projectivization F E) : Finset ((E × E) ⊕ (E × E)) :=
  (univ.image (fun x : F => Sum.inl (wittAdd i.1 (left η i.2.rep x)))) ∪
  (univ.image (fun t : F => Sum.inr (wittAdd (wittNeg i.1) (right η i.2.rep t))))

omit [Fintype E] in
lemma block_size (η : E) (i : (E × E) × Projectivization F E) :
    (block η i).card ≤ 2*Fintype.card F := by
  have h := card_union_le
    (univ.image (fun x : F => Sum.inl (wittAdd i.1 (left η i.2.rep x))))
    (univ.image (fun t : F => Sum.inr (wittAdd (wittNeg i.1) (right η i.2.rep t))))
  have h₁ := card_image_le (s := (univ : Finset F))
    (f := fun x : F => (Sum.inl (wittAdd i.1 (left η i.2.rep x)) : (E × E) ⊕ (E × E)))
  have h₂ := card_image_le (s := (univ : Finset F))
    (f := fun t : F => (Sum.inr (wittAdd (wittNeg i.1) (right η i.2.rep t)) : (E × E) ⊕ (E × E)))
  simp only [card_univ] at h₁ h₂
  exact h.trans (by omega)

lemma block_count_bound (hE : Fintype.card E=Fintype.card F^2) :
    Fintype.card ((E × E) × Projectivization F E) ≤ 2*Fintype.card F^5 := by
  rw [Fintype.card_prod,Fintype.card_prod,projective_card hE,hE]
  have hq : 0 < Fintype.card F := Fintype.card_pos
  calc
    _ = Fintype.card F^4*(Fintype.card F+1) := by ring
    _ ≤ Fintype.card F^4*(2*Fintype.card F) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

variable [CharP E 2]

omit [Fintype E] in
/-- The algebraic chart is a genuine cover of every selected edge; no edges
are assumed to survive merely because their endpoints lie in a block. -/
lemma block_cover (τ : E →+* E) (η : E)
    (hη : η^2+η=1) (hτη : τ η=η+1)
    (hfix : ∀ x : F, τ (algebraMap F E x)=algebraMap F E x)
    (hcoord : ∀ s : E, ∃ x t : F, s=algebraMap F E x+η*algebraMap F E t)
    (H : SimpleGraph ((E × E) ⊕ (E × E))) (hH : H ≤ graph τ) :
    ∀ v w, H.Adj v w → ∃ i : (E × E) × Projectivization F E,
      v ∈ block η i ∧ w ∈ block η i := by
  have hf (r c : E × E) (h : (graph τ).Adj (.inl r) (.inr c)) :
      ∃ i : (E × E) × Projectivization F E, Sum.inl r ∈ block η i ∧ Sum.inr c ∈ block η i := by
    obtain ⟨l,p,x,t,hx,ht⟩ := projective_chart τ η hη hτη hfix hcoord r c h
    refine ⟨(p,l),mem_union_left _ (mem_image.mpr ⟨x,mem_univ _,?_⟩),
      mem_union_right _ (mem_image.mpr ⟨t,mem_univ _,?_⟩)⟩
    · exact congrArg Sum.inl hx
    · exact congrArg Sum.inr ht
  intro v w hvw
  have h := hH hvw
  cases v with
  | inl r =>
    cases w with
    | inl c => exact False.elim h
    | inr c => exact hf r c h
  | inr c =>
    cases w with
    | inr r => exact False.elim h
    | inl r =>
      obtain ⟨i,hr,hc⟩ := hf r c h
      exact ⟨i,hc,hr⟩

/-- Projective-scale counting turns the complete-block chart into a
subcritical bound for EVERY K44-free edge subgraph. -/
theorem chart_thinning (τ : E →+* E) (η : E)
    (hη : η^2+η=1) (hτη : τ η=η+1)
    (hfix : ∀ x : F, τ (algebraMap F E x)=algebraMap F E x)
    (hcoord : ∀ s : E, ∃ x t : F, s=algebraMap F E x+η*algebraMap F E t)
    (hE : Fintype.card E=Fintype.card F^2)
    (H : SimpleGraph ((E × E) ⊕ (E × E))) (hH : H ≤ graph τ)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  have h := Erdos714BlockThinning.fourth_power_of_block_cover H hfree (block η)
    (Fintype.card F) (block_size η) (block_cover τ η hη hτη hfix hcoord H hH)
  calc
    _ ≤ 10368*Fintype.card ((E × E) × Projectivization F E)^4*Fintype.card F^7 := h
    _ ≤ 10368*(2*Fintype.card F^5)^4*Fintype.card F^7 := by
      gcongr
      exact block_count_bound hE
    _ = _ := by ring

lemma map_trace (k : ℕ) (hcard : Fintype.card F=2^k)
    (hE : Fintype.card E=Fintype.card F^2) (s : E) :
    algebraMap F E (Algebra.trace F E s)=s+conjugation k s := by
  rw [FiniteField.algebraMap_trace_eq_sum_pow,finrank_two hE,conjugation_apply]
  simp [sum_range_succ,Nat.card_eq_fintype_card,hcard]

/-- Trace extracts the two base-field coordinates explicitly. -/
lemma coordinates (k : ℕ) (hcard : Fintype.card F=2^k)
    (hE : Fintype.card E=Fintype.card F^2) (η : E) (hτη : conjugation k η=η+1) :
    ∀ s : E, ∃ x t : F, s=algebraMap F E x+η*algebraMap F E t := by
  intro s
  refine ⟨Algebra.trace F E (s*(η+1)),Algebra.trace F E s,?_⟩
  rw [map_trace k hcard hE,map_trace k hcard hE,map_mul,map_add,map_one,hτη]
  have h2 : (2:E)=0 := CharP.cast_eq_zero E 2
  ring_nf
  simp only [h2,mul_zero,add_zero]

variable [CharP F 2]

omit [Fintype F] in
lemma odd_trace_one (k : ℕ) (hk : Odd k) : traceSum k (1 : F)=1 := by
  obtain ⟨m,rfl⟩ := hk
  have h2 : (2:F)=0 := CharP.cast_eq_zero F 2
  simp [traceSum,h2,Nat.cast_add,Nat.cast_mul]

/-- Odd-degree binary Witt-circle hosts cannot be repaired by arbitrary
edge deletions while retaining the critical q^7 scale. -/
theorem odd_degree_thinning (k : ℕ) (hk : Odd k) (hcard : Fintype.card F=2^k)
    (hE : Fintype.card E=Fintype.card F^2)
    (H : SimpleGraph ((E × E) ⊕ (E × E))) (hH : H ≤ fieldGraph (F := F) (E := E))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 165888*Fintype.card F^27 := by
  obtain ⟨η,hη,hτη⟩ := extension_root (E := E) k hcard hE (1 : F) (odd_trace_one k hk)
  rw [map_one] at hη
  rw [fieldGraph_eq k hcard hE] at hH
  exact chart_thinning (conjugation k) η hη hτη (conjugation_coefficient k hcard)
    (coordinates k hcard hE η hτη) hE H hH hfree

/-- Denominator-free exclusion of unbounded critical-scale constructions
inside these hosts. The constant C may be arbitrary but fixed. -/
theorem critical_budget (k : ℕ) (hk : Odd k) (hcard : Fintype.card F=2^k)
    (hE : Fintype.card E=Fintype.card F^2)
    (H : SimpleGraph ((E × E) ⊕ (E × E))) (hH : H ≤ fieldGraph (F := F) (E := E))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (C : ℕ) (he : Fintype.card F^7 ≤ C*H.edgeFinset.card) :
    Fintype.card F ≤ 165888*C^4 := by
  have hm := odd_degree_thinning k hk hcard hE H hH hfree
  have h : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(165888*C^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (C*H.edgeFinset.card)^4 := Nat.pow_le_pow_left he 4
      _ = C^4*H.edgeFinset.card^4 := by ring
      _ ≤ C^4*(165888*Fintype.card F^27) := Nat.mul_le_mul_left _ hm
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (pow_pos Fintype.card_pos 27)

#print axioms block_count_bound
#print axioms block_cover
#print axioms chart_thinning
#print axioms coordinates
#print axioms odd_degree_thinning
#print axioms critical_budget
end Erdos714WittCircleBlocks
