import FormalConjecturesUtil
import Submission.CompactSymmRootsAudit

/-! Dense hosts cannot have bounded transversals for patterns of strictly
smaller extremal exponent. This uses the edge count, not root density. -/
open SimpleGraph Finset Filter Asymptotics
namespace Erdos713RobustCopies

variable {U V W : Type*}

def DisjointCopies (k : ℕ) (Q : SimpleGraph U) (G : SimpleGraph V) : Prop :=
  ∃ f : Fin k → Q.Copy G, ∀ i j, i ≠ j → ∀ u v, f i u ≠ f j v

/-- Taking the maximum avoids assuming monotonicity for patterns with
isolated vertices at small host orders. -/
noncomputable def envelope (Q : SimpleGraph U) (n : ℕ) : ℕ :=
  (range (n+1)).sup (fun m => extremalNumber m Q)

lemma le_envelope (Q : SimpleGraph U) {m n : ℕ} (hmn : m ≤ n) :
    extremalNumber m Q ≤ envelope Q n := by
  unfold envelope
  exact Finset.le_sup (f := fun m => extremalNumber m Q) (mem_range.mpr (by omega))

lemma envelope_upper (Q : SimpleGraph U) {r : ℝ} (hr : 0 ≤ r)
    (hQ : (fun n : ℕ => (extremalNumber n Q : ℝ)) =O[atTop] (fun n => (n : ℝ)^r)) :
    (fun n : ℕ => (envelope Q n : ℝ)) =O[atTop] (fun n => (n : ℝ)^r) := by
  obtain ⟨C,hC,hbound⟩ := Erdos713EdgeAttachments.global_extremal_bound_of_upper Q hr hQ
  apply IsBigO.of_bound C
  filter_upwards with n
  obtain ⟨m,hm,he⟩ := exists_mem_eq_sup (range (n+1)) (by simp) (fun m => extremalNumber m Q)
  rw [Real.norm_natCast,Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  change (((range (n+1)).sup (fun m => extremalNumber m Q) : ℕ) : ℝ) ≤ _
  rw [he]
  exact (hbound m).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show m ≤ n by simpa using hm)) hr) hC)

lemma edge_bound_after_deletion [Fintype V] (Q : SimpleGraph U) (G : SimpleGraph V)
    (S : Finset V) (hf : Q.Free (G.induce (S : Set V)ᶜ)) :
    Nat.card G.edgeSet ≤ envelope Q (Fintype.card V) + S.card*Fintype.card V := by
  classical
  have hdel := Erdos713Union.edges_le_induce_compl_add G S
  have hq := card_edgeFinset_le_extremalNumber hf
  have hn : Fintype.card ↥((S : Set V)ᶜ) ≤ Fintype.card V := Fintype.card_subtype_le _
  have hm := le_envelope Q hn
  simp only [edgeFinset_card, Fintype.card_eq_nat_card] at hq hdel
  simp only [Fintype.card_eq_nat_card] at hm ⊢
  exact hdel.trans (Nat.add_le_add_right (hq.trans hm) _)

lemma copy_avoiding_of_edge_bound [Fintype V] (Q : SimpleGraph U) (G : SimpleGraph V)
    (S : Finset V)
    (h : envelope Q (Fintype.card V) + S.card*Fintype.card V < Nat.card G.edgeSet) :
    ∃ f : Q.Copy G, ∀ u, f u ∉ S := by
  classical
  have hc : Q ⊑ G.induce (S : Set V)ᶜ := by
    by_contra hf
    exact (not_le_of_gt h) (edge_bound_after_deletion Q G S hf)
  obtain ⟨f⟩ := hc
  refine ⟨(Copy.induce G _).comp f,fun u => ?_⟩
  exact (f u).property

lemma disjoint_copies_of_avoidance [Fintype U] [Fintype V] (Q : SimpleGraph U)
    (G : SimpleGraph V) (k : ℕ)
    (h : ∀ S : Finset V, S.card ≤ k*Fintype.card U → ∃ f : Q.Copy G, ∀ u, f u ∉ S) :
    DisjointCopies k Q G := by
  classical
  induction k with
  | zero => exact ⟨Fin.elim0,fun i => Fin.elim0 i⟩
  | succ k ih =>
    obtain ⟨f,hf⟩ := ih (fun S hS => h S (hS.trans (Nat.mul_le_mul_right _ (Nat.le_succ k))))
    let S := univ.biUnion (fun i : Fin k => univ.image (f i))
    have hS : S.card ≤ k*Fintype.card U := by
      calc
        _ ≤ ∑ i : Fin k, (univ.image (f i)).card := card_biUnion_le
        _ ≤ ∑ _i : Fin k, Fintype.card U := sum_le_sum (fun i _ => card_image_le.trans (by simp))
        _ = _ := by simp
    obtain ⟨g,hg⟩ := h S (hS.trans (Nat.mul_le_mul_right _ (Nat.le_succ k)))
    have hgf (i : Fin k) (u v : U) : g u ≠ f i v := by
      intro he
      apply hg u
      rw [he]
      exact mem_biUnion.mpr ⟨i,mem_univ _,mem_image.mpr ⟨v,mem_univ _,rfl⟩⟩
    refine ⟨Fin.cases g f,?_⟩
    intro i j hij u v
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact (hij rfl).elim
    · exact hgf _ u v
    · exact (hgf _ v u).symm
    · exact hf _ _ (fun he => hij (congrArg Fin.succ he)) u v

lemma disjoint_copies_of_edge_bound [Fintype U] [Fintype V] (Q : SimpleGraph U)
    (G : SimpleGraph V) (k : ℕ)
    (h : envelope Q (Fintype.card V) + k*Fintype.card U*Fintype.card V < Nat.card G.edgeSet) :
    DisjointCopies k Q G := by
  apply disjoint_copies_of_avoidance Q G k
  intro S hS
  apply copy_avoiding_of_edge_bound Q G S
  exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ hS) _).trans_lt h

lemma eventual_edge_gap (H : SimpleGraph W) (Q : SimpleGraph U) {α c r : ℝ}
    (hr : 1 ≤ r) (hra : r < α) (hc : 0 < c)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (hQ : (fun n : ℕ => (extremalNumber n Q : ℝ)) =O[atTop] (fun n => (n : ℝ)^r)) (M : ℕ) :
    ∀ᶠ n : ℕ in atTop, 2*(envelope Q n + M*n) < extremalNumber n H := by
  have hO : (fun n : ℕ => (2 : ℝ)*((envelope Q n : ℝ)+(M*n : ℕ))) =O[atTop]
      (fun n : ℕ => (n : ℝ)^r) := ((envelope_upper Q (by linarith) hQ).add (Erdos713Rate.cast_linear_bigO hr M)).const_mul_left 2
  obtain ⟨C,hC⟩ := hO.bound
  have htop := Erdos713FutureRecords.lower_ratio_top hra hc hH
  filter_upwards [hC,htop.eventually_gt_atTop C,eventually_gt_atTop (0 : ℕ)] with n hbound hlower hn
  have hp : 0 < (n : ℝ)^r := Real.rpow_pos_of_pos (by exact_mod_cast hn) r
  have hlo : C*(n : ℝ)^r < (extremalNumber n H : ℝ) := (lt_div_iff₀ hp).mp hlower
  rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg hp.le] at hbound
  exact_mod_cast hbound.trans_lt hlo

/-- Every host with at least half the extremal edge count has arbitrarily
many disjoint Q copies, if Q has a strictly smaller upper exponent. -/
theorem eventual_disjoint_copies [Fintype U] (H : SimpleGraph W) (Q : SimpleGraph U)
    {α c r : ℝ} (hr : 1 ≤ r) (hra : r < α) (hc : 0 < c)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (hQ : (fun n : ℕ => (extremalNumber n Q : ℝ)) =O[atTop] (fun n => (n : ℝ)^r)) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      extremalNumber n H ≤ 2*Nat.card G.edgeSet → DisjointCopies k Q G := by
  filter_upwards [eventual_edge_gap H Q hr hra hc hH hQ (k*Fintype.card U)] with n hn
  intro G hG
  apply disjoint_copies_of_edge_bound Q G k
  simp only [Fintype.card_fin]
  omega

/-- Under an irrational exact exponent, every contained pattern with a
known rational attained rate has a strict exponent gap. -/
theorem known_subgraphs [Fintype U] (H : SimpleGraph W) (Q : SimpleGraph U)
    {α c : ℝ} (ha : 1 ≤ α) (hc : 0 < c)
    (hH : (fun n : ℕ => (extremalNumber n H : ℝ)) ~[atTop] (fun n => c*(n : ℝ)^α))
    (hirr : α ∉ Set.range ((↑) : ℚ → ℝ)) (hQH : Q ⊑ H)
    {r : ℚ} (hQ : Erdos713Rate.HasRate Q (r : ℝ)) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      extremalNumber n H ≤ 2*Nat.card G.edgeSet → DisjointCopies k Q G := by
  have hrα : (r : ℝ) ≤ α := hQ.lower α ha
    ((Erdos713Rate.extremal_mono_bigO hQH).trans (Erdos713Rate.rate_of_asymptotic ha hc.ne' hH).upper)
  have hrα' : (r : ℝ) < α := lt_of_le_of_ne hrα (fun he => hirr ⟨r,he⟩)
  exact eventual_disjoint_copies H Q hQ.one_le hrα' hc hH hQ.upper k

#print axioms disjoint_copies_of_edge_bound
#print axioms eventual_disjoint_copies
#print axioms known_subgraphs
end Erdos713RobustCopies
