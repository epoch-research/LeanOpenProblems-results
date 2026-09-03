import FormalConjecturesUtil
import Submission.UniformIncidence
import Submission.QuantitativeRobustCopies

/-! Linear vertex transversals and disjoint packings in dense H-free hosts
for patterns of strictly smaller extremal exponent. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713LinearRobustCopies
open Erdos713RobustCopies Erdos713UniformIncidence
variable {U V W : Type*}
set_option maxHeartbeats 2000000

lemma edge_bound_after_deletion_degree [Fintype V] (Q : SimpleGraph U) (G : SimpleGraph V)
    (S : Finset V) (hf : Q.Free (G.induce (S : Set V)ᶜ)) :
    Nat.card G.edgeSet ≤ envelope Q (Fintype.card V) + ∑ v ∈ S, Nat.card (G.neighborSet v) := by
  classical
  have hdel := edges_le_induce_compl_add_degree G S
  have hq : Nat.card (G.induce (S : Set V)ᶜ).edgeSet ≤
      extremalNumber (Fintype.card ↥((S : Set V)ᶜ)) Q := by
    simpa only [edgeFinset_card,Fintype.card_eq_nat_card] using card_edgeFinset_le_extremalNumber hf
  have hm := le_envelope Q (Fintype.card_subtype_le (fun v : V => v ∈ (S : Set V)ᶜ))
  exact hdel.trans (Nat.add_le_add_right (hq.trans hm) _)

/-- A strict exponent gap forces every vertex transversal to occupy a
positive fraction of the host. H-freeness is essential to this refinement. -/
theorem linear_transversal (H : SimpleGraph W) (Q : SimpleGraph U)
    {α c r : ℝ} (ha : 1 < α) (hr : 0 ≤ r) (hra : r < α) (hc : 0 < c)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (hQ : (fun n : ℕ => (extremalNumber n Q : ℝ)) =O[atTop] (fun n => (n : ℝ)^r)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), H.Free G →
      extremalNumber n H ≤ 2*Nat.card G.edgeSet → ∀ S : Finset (Fin n),
        Q.Free (G.induce (S : Set (Fin n))ᶜ) → δ*n < (S.card : ℝ) := by
  obtain ⟨δ,hd,hSmall⟩ := small_set_mass H ha hc hH (show 0 < c/8 by positivity)
  refine ⟨δ,hd,?_⟩
  filter_upwards [hSmall,scaled_edge_gap H Q hr hra hc hH hQ] with n hsmall hgap
  intro G hf hG S hS
  by_contra hbad
  have hs : (S.card : ℝ) ≤ δ*n := le_of_not_gt hbad
  have hMass := hsmall (Fin n) G (Fintype.card_fin n) hf S hs
  have hdel : (Nat.card G.edgeSet : ℝ) ≤ (envelope Q n : ℝ)+
      ∑ v ∈ S, (Nat.card (G.neighborSet v) : ℝ) := by
    exact_mod_cast (by simpa only [Fintype.card_fin] using edge_bound_after_deletion_degree Q G S hS)
  have hG' : (extremalNumber n H : ℝ) ≤ 2*(Nat.card G.edgeSet : ℝ) := by exact_mod_cast hG
  linarith [hgap.2.1,hgap.2.2]

/-- One constant and one eventual threshold give both a linear packing and
a linear transversal lower bound on the same dense H-free host. -/
theorem linear_copies_and_transversal [Fintype U] (H : SimpleGraph W) (Q : SimpleGraph U)
    {α c r : ℝ} (ha : 1 < α) (hr : 0 ≤ r) (hra : r < α) (hc : 0 < c)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (hQ : (fun n : ℕ => (extremalNumber n Q : ℝ)) =O[atTop] (fun n => (n : ℝ)^r)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), H.Free G →
      extremalNumber n H ≤ 2*Nat.card G.edgeSet →
        DisjointCopies ⌊δ*(n : ℝ)⌋₊ Q G ∧
        ∀ S : Finset (Fin n), Q.Free (G.induce (S : Set (Fin n))ᶜ) → δ*n < (S.card : ℝ) := by
  classical
  obtain ⟨τ,hτ,hTrans⟩ := linear_transversal H Q ha hr hra hc hH hQ
  let δ := τ/((Fintype.card U : ℝ)+1)
  have hd : 0 < δ := by dsimp [δ]; positivity
  have heq : δ*((Fintype.card U : ℝ)+1) = τ := by dsimp [δ]; field_simp
  have hdq : δ*(Fintype.card U : ℝ) ≤ τ := by nlinarith
  have hdτ : δ ≤ τ := by
    have hh := mul_nonneg hd.le (Nat.cast_nonneg (Fintype.card U) : (0 : ℝ) ≤ Fintype.card U)
    nlinarith
  refine ⟨δ,hd,?_⟩
  filter_upwards [hTrans] with n htrans
  intro G hf hG
  refine ⟨?_,?_⟩
  · apply disjoint_copies_of_avoidance Q G ⌊δ*(n : ℝ)⌋₊
    intro S hS
    have hfloor : (⌊δ*(n : ℝ)⌋₊ : ℝ) ≤ δ*n := Nat.floor_le (by positivity)
    have hsR : (S.card : ℝ) ≤ (⌊δ*(n : ℝ)⌋₊ : ℝ)*Fintype.card U := by exact_mod_cast hS
    have hSm : (S.card : ℝ) ≤ τ*n := by
      calc
        _ ≤ (⌊δ*(n : ℝ)⌋₊ : ℝ)*Fintype.card U := hsR
        _ ≤ (δ*n)*Fintype.card U := mul_le_mul_of_nonneg_right hfloor (Nat.cast_nonneg _)
        _ = (δ*Fintype.card U)*n := by ring
        _ ≤ τ*n := mul_le_mul_of_nonneg_right hdq (Nat.cast_nonneg _)
    have hcopy : Q ⊑ G.induce (S : Set (Fin n))ᶜ := by
      by_contra hfree
      exact (not_lt_of_ge hSm) (htrans G hf hG S hfree)
    obtain ⟨f⟩ := hcopy
    exact ⟨(Copy.induce G _).comp f,fun u => (f u).property⟩
  · intro S hS
    exact (mul_le_mul_of_nonneg_right hdτ (Nat.cast_nonneg n)).trans_lt (htrans G hf hG S hS)

/-- Rational-rate patterns actually contained in H have a strict exponent
gap if the exact exponent of H is irrational. No quotient-rate assumption
is made. -/
theorem known_subgraphs_linear [Fintype U] (H : SimpleGraph W) (Q : SimpleGraph U)
    {α c : ℝ} (ha : 1 < α) (hc : 0 < c)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (hirr : α ∉ Set.range ((↑) : ℚ → ℝ)) (hQH : Q ⊑ H)
    {r : ℚ} (hQ : Erdos713Rate.HasRate Q (r : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), H.Free G →
      extremalNumber n H ≤ 2*Nat.card G.edgeSet →
        DisjointCopies ⌊δ*(n : ℝ)⌋₊ Q G ∧
        ∀ S : Finset (Fin n), Q.Free (G.induce (S : Set (Fin n))ᶜ) → δ*n < (S.card : ℝ) := by
  have hrα : (r : ℝ) ≤ α := hQ.lower α ha.le
    ((Erdos713Rate.extremal_mono_bigO hQH).trans (Erdos713Rate.rate_of_asymptotic ha.le hc.ne' hH).upper)
  have hrα' : (r : ℝ) < α := lt_of_le_of_ne hrα (fun he => hirr ⟨r,he⟩)
  exact linear_copies_and_transversal H Q ha (by linarith [hQ.one_le]) hrα' hc hH hQ.upper

#print axioms edge_bound_after_deletion_degree
#print axioms linear_transversal
#print axioms linear_copies_and_transversal
#print axioms known_subgraphs_linear
end Erdos713LinearRobustCopies
