import FormalConjecturesUtil

/-! Consistent fixed-size edge marginals with quadratic objective. These
local models do not extend to globally positive moments and are not graph
extremizers. No rationality or counterexample to Erdős 713 is claimed. -/
open Finset SimpleGraph
open scoped Classical
namespace Erdos713LocalEdgeMarginals
variable {I V W : Type*}
set_option maxHeartbeats 1000000

/-- On a query S, put weight p on each singleton and weight 1-|S|p on
empty. The formula is defined for all S; positivity needs |S|p<=1. -/
noncomputable def expectation (p : ℝ) (S : Finset I) (f : Finset I → ℝ) : ℝ :=
  (1-(S.card : ℝ)*p)*f ∅ + p*∑ i ∈ S, f {i}

lemma normalized (p : ℝ) (S : Finset I) : expectation p S (fun _ => 1) = 1 := by
  simp only [expectation,sum_const,nsmul_eq_mul,mul_one]
  ring

lemma add (p : ℝ) (S : Finset I) (f g : Finset I → ℝ) :
    expectation p S (fun A => f A+g A) = expectation p S f+expectation p S g := by
  simp only [expectation,sum_add_distrib]
  ring

lemma smul (p c : ℝ) (S : Finset I) (f : Finset I → ℝ) :
    expectation p S (fun A => c*f A) = c*expectation p S f := by
  simp only [expectation,← mul_sum]
  ring

lemma nonnegative {p : ℝ} {S : Finset I} (hp : 0 ≤ p) (hS : S.card*p ≤ 1)
    (f : Finset I → ℝ) (h0 : 0 ≤ f ∅) (h1 : ∀ i ∈ S, 0 ≤ f {i}) :
    0 ≤ expectation p S f := by
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hS) h0)
    (mul_nonneg hp (sum_nonneg h1))

/-- Coherence holds for every test function under restriction to a smaller
query, not just for one-edge or forbidden-copy indicators. -/
lemma coherent (p : ℝ) {S T : Finset I} (hTS : T ⊆ S) (f : Finset I → ℝ) :
    expectation p S (fun A => f (A ∩ T)) = expectation p T f := by
  have hsplit := sum_sdiff (f := fun i => f ({i} ∩ T)) hTS
  have hleft : (∑ i ∈ S \ T, f ({i} ∩ T)) = ((S \ T).card : ℝ)*f ∅ := by
    calc
      _ = ∑ _i ∈ S \ T, f ∅ := sum_congr rfl (fun i hi => by
        rw [singleton_inter_of_notMem (mem_sdiff.mp hi).2])
      _ = _ := by simp only [sum_const,nsmul_eq_mul]
  have hright : (∑ i ∈ T, f ({i} ∩ T)) = ∑ i ∈ T, f {i} :=
    sum_congr rfl (fun i hi => by rw [singleton_inter_of_mem hi])
  rw [hleft,hright] at hsplit
  have hcard : ((S \ T).card : ℝ)+T.card = S.card := by
    exact_mod_cast card_sdiff_add_card_eq_card hTS
  simp only [expectation,empty_inter]
  rw [← hsplit]
  rw [← hcard]
  ring

lemma singleton_marginal (p : ℝ) {S : Finset I} {i : I} (hi : i ∈ S) :
    expectation p S (fun A => if i ∈ A then 1 else 0) = p := by
  simp [expectation, hi]

lemma vanish (p : ℝ) (S : Finset I) (f : Finset I → ℝ)
    (h0 : f ∅ = 0) (h1 : ∀ i ∈ S, f {i} = 0) : expectation p S f = 0 := by
  simp only [expectation,h0,mul_zero,zero_add,sum_eq_zero h1]

/-- Every conjunction requiring at least two distinct edges has zero
local expectation. No bound on the query size is needed for this identity. -/
lemma forbidden_monomial (p : ℝ) (S F : Finset I) (hF : 2 ≤ F.card) :
    expectation p S (fun A => if F ⊆ A then 1 else 0) = 0 := by
  apply vanish
  · have h : ¬ F ⊆ ∅ := fun hh => by
      have hc : F.card ≤ 0 := by simpa only [card_empty] using card_le_card hh
      omega
    simp [h]
  · intro i _
    have h : ¬ F ⊆ {i} := fun hh => by
      have hc : F.card ≤ 1 := by simpa only [card_singleton] using card_le_card hh
      omega
    simp [h]

noncomputable def density (r : ℕ) : ℝ := 1/((r : ℝ)+1)

lemma density_pos (r : ℕ) : 0 < density r := by unfold density; positivity

lemma query_budget (r : ℕ) {S : Finset I} (hS : S.card ≤ r) : S.card*density r ≤ 1 := by
  have h : (S.card : ℝ) ≤ r := by exact_mod_cast hS
  unfold density
  apply (mul_le_mul_of_nonneg_right h (by positivity)).trans
  rw [mul_one_div]
  exact (div_le_one (by positivity)).mpr (by linarith)

lemma positive_queries (r : ℕ) {S : Finset I} (hS : S.card ≤ r)
    (f : Finset I → ℝ) (hf : ∀ A ⊆ S, A.card ≤ 1 → 0 ≤ f A) :
    0 ≤ expectation (density r) S f := by
  apply nonnegative (density_pos r).le (query_budget r hS)
  · exact hf ∅ (empty_subset _) (by simp)
  · intro i hi
    exact hf {i} (singleton_subset_iff.mpr hi) (by simp)

noncomputable def objective (p : ℝ) (E : Finset I) : ℝ :=
  ∑ i ∈ E, expectation p {i} (fun A => if i ∈ A then 1 else 0)

lemma objective_eq (p : ℝ) (E : Finset I) : objective p E = p*E.card := by
  unfold objective
  simp only [singleton_marginal p (mem_singleton_self _),sum_const,nsmul_eq_mul]
  ring

/-- A global square detects the failure of positivity beyond the bounded
query range. Thus no claim about a semidefinite hierarchy is being made. -/
lemma variance (p : ℝ) (S : Finset I) :
    expectation p S (fun A => ((A.card : ℝ)-p*S.card)^2) =
      p*S.card*(1-p*S.card) := by
  simp only [expectation,card_empty,card_singleton,Nat.cast_zero,Nat.cast_one,
    sum_const,nsmul_eq_mul]
  ring

lemma negative_variance {p : ℝ} (S : Finset I) (h : 1 < p*S.card) :
    expectation p S (fun A => ((A.card : ℝ)-p*S.card)^2) < 0 := by
  rw [variance]
  exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

/-- An assignment containing at most one unordered edge is H-free whenever
H has at least two edges. Loops, if present in the assignment, are removed
by fromEdgeSet and cannot invalidate the bound. -/
lemma one_edge_free [Fintype V] [Fintype W] (H : SimpleGraph W)
    (hH : 2 ≤ H.edgeFinset.card) (A : Finset (Sym2 V)) (hA : A.card ≤ 1) :
    H.Free (fromEdgeSet (A : Set (Sym2 V))) := by
  have hsub : (fromEdgeSet (A : Set (Sym2 V))).edgeFinset ⊆ A := by
    intro e he
    have hh := mem_edgeFinset.mp he
    rw [edgeSet_fromEdgeSet] at hh
    exact hh.1
  have hsmall := (card_le_card hsub).trans hA
  rintro ⟨f⟩
  have hle := Fintype.card_le_of_injective f.mapEdgeSet f.mapEdgeSet.injective
  simp only [← edgeFinset_card] at hle
  omega

lemma free_queries_positive [Fintype V] [Fintype W] (H : SimpleGraph W)
    (hH : 2 ≤ H.edgeFinset.card) (r : ℕ) {S : Finset (Sym2 V)} (hS : S.card ≤ r)
    (f : Finset (Sym2 V) → ℝ)
    (hf : ∀ A ⊆ S, H.Free (fromEdgeSet (A : Set (Sym2 V))) → 0 ≤ f A) :
    0 ≤ expectation (density r) S f := by
  apply positive_queries r hS
  intro A hAS hA
  exact hf A hAS (one_edge_free H hH A hA)

lemma forbidden_graph_indicator [Fintype V] [Fintype W] (H : SimpleGraph W)
    (hH : 2 ≤ H.edgeFinset.card) (p : ℝ) (S : Finset (Sym2 V)) :
    expectation p S (fun A => if H.Free (fromEdgeSet (A : Set (Sym2 V))) then 1 else 0) = 1 := by
  unfold expectation
  have h0 := one_edge_free H hH (∅ : Finset (Sym2 V)) (by simp)
  have h1 (i : Sym2 V) := one_edge_free H hH ({i} : Finset (Sym2 V)) (by simp)
  simp only [if_pos h0,if_pos (h1 _),sum_const,nsmul_eq_mul,mul_one]
  ring

lemma graph_objective (p : ℝ) (n : ℕ) :
    objective p (⊤ : SimpleGraph (Fin n)).edgeFinset = p*n*(n-1)/2 := by
  rw [objective_eq,card_edgeFinset_top_eq_card_choose_two,Fintype.card_fin,Nat.cast_choose_two]
  ring

#print axioms normalized
#print axioms coherent
#print axioms singleton_marginal
#print axioms forbidden_monomial
#print axioms positive_queries
#print axioms negative_variance
#print axioms one_edge_free
#print axioms free_queries_positive
#print axioms forbidden_graph_indicator
#print axioms graph_objective
end Erdos713LocalEdgeMarginals
