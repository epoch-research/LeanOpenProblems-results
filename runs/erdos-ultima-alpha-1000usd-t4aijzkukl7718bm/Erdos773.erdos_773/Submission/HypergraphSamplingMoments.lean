import Submission.Hypergraph

/-! Finite high-moment bounds for induced edge counts under independent
vertex sampling. No asymptotic or concentration assumption is used. -/
namespace Erdos773.HypergraphSamplingMoments
open Finset
set_option maxHeartbeats 2000000
noncomputable section
variable {α : Type*} [DecidableEq α]

lemma touching_card (H : Finset (Finset α)) (U : Finset α) (K : ℕ)
    (hK : ∀ a, (H.filter (fun e => a ∈ e)).card ≤ K) :
    (H.filter (fun e => ¬Disjoint U e)).card ≤ U.card*K := by
  classical
  have hs : H.filter (fun e => ¬Disjoint U e) ⊆
      U.biUnion (fun a => H.filter (fun e => a ∈ e)) := by
    intro e he
    obtain ⟨he,hn⟩ := mem_filter.mp he
    rw [Finset.disjoint_left] at hn
    push_neg at hn
    obtain ⟨a,ha,hae⟩ := hn
    exact mem_biUnion.mpr ⟨a,ha,mem_filter.mpr ⟨he,hae⟩⟩
  calc
    _ ≤ (U.biUnion (fun a => H.filter (fun e => a ∈ e))).card := card_le_card hs
    _ ≤ ∑ a ∈ U, (H.filter (fun e => a ∈ e)).card := card_biUnion_le
    _ ≤ ∑ _a ∈ U, K := sum_le_sum (fun a _ => hK a)
    _ = _ := by simp

lemma union_step (H : Finset (Finset α)) (U : Finset α) (r K : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : ∀ e ∈ H, e.card=r)
    (hK : ∀ a, (H.filter (fun e => a ∈ e)).card ≤ K) :
    (∑ e ∈ H, p^(U∪e).card) ≤ p^U.card*(p^r*H.card+U.card*K) := by
  classical
  have ht (e : Finset α) (he : e ∈ H) : p^(U∪e).card ≤
      p^U.card*p^r+(if ¬Disjoint U e then p^U.card else 0) := by
    by_cases hd : Disjoint U e
    · rw [card_union_of_disjoint hd,hr e he,pow_add,if_neg (not_not.mpr hd),add_zero]
    · rw [if_pos hd]
      have hh : p^(U∪e).card ≤ p^U.card :=
        pow_le_pow_of_le_one hp hp1 (card_le_card subset_union_left)
      have hz : 0 ≤ p^U.card*p^r := by positivity
      linarith only [hh,hz]
  have hc : ((H.filter (fun e => ¬Disjoint U e)).card:ℝ) ≤ (U.card:ℝ)*K := by
    exact_mod_cast touching_card H U K hK
  calc
    _ ≤ ∑ e ∈ H, (p^U.card*p^r+(if ¬Disjoint U e then p^U.card else 0)) :=
      sum_le_sum ht
    _ = p^U.card*(p^r*H.card+(H.filter (fun e => ¬Disjoint U e)).card) := by
      rw [sum_add_distrib,← sum_filter]
      simp only [sum_const,nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hc) (pow_nonneg hp _)

/-- Ordered edge tuples, weighted by the size of their union with U. -/
def jointMoment (H : Finset (Finset α)) (p : ℝ) : ℕ → Finset α → ℝ
  | 0,U => p^U.card
  | k+1,U => ∑ e ∈ H, jointMoment H p k (U∪e)

lemma jointMoment_bound (H : Finset (Finset α)) (r K q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : ∀ e ∈ H, e.card=r)
    (hK : ∀ a, (H.filter (fun e => a ∈ e)).card ≤ K) :
    ∀ k U, U.card+r*k ≤ r*q → jointMoment H p k U ≤
      p^U.card*(p^r*H.card+(r*q:ℕ)*K)^k := by
  intro k
  induction k with
  | zero => intro U hU; simp [jointMoment]
  | succ k ih =>
    intro U hU
    simp only [Nat.mul_succ] at hU
    have hbase : (0:ℝ) ≤ p^r*H.card+(r*q:ℕ)*K := by positivity
    have hrec (e : Finset α) (he : e ∈ H) : (U∪e).card+r*k ≤ r*q := by
      have hh := card_union_le U e
      rw [hr e he] at hh
      omega
    have hstep := union_step H U r K p hp hp1 hr hK
    have hU' : (U.card:ℝ)*K ≤ ((r*q:ℕ):ℝ)*K := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show U.card ≤ r*q by omega))
        (Nat.cast_nonneg K)
    have hstep' := hstep.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hU') (pow_nonneg hp _))
    calc
      _ ≤ ∑ e ∈ H, p^(U∪e).card*(p^r*H.card+(r*q:ℕ)*K)^k :=
        sum_le_sum (fun e he => ih (U∪e) (hrec e he))
      _ = (∑ e ∈ H, p^(U∪e).card)*(p^r*H.card+(r*q:ℕ)*K)^k := (sum_mul _ _ _).symm
      _ ≤ (p^U.card*(p^r*H.card+(r*q:ℕ)*K))*(p^r*H.card+(r*q:ℕ)*K)^k :=
        mul_le_mul_of_nonneg_right hstep' (pow_nonneg hbase _)
      _ = _ := by rw [pow_succ]; ring

section Expectation
variable [Fintype α]

/-- The recursive union polynomial is the actual Bernoulli mixed moment. -/
lemma jointMoment_expectation (H : Finset (Finset α)) (p : ℝ) (k : ℕ) (U : Finset α) :
    jointMoment H p k U = ∑ f : α → Bool,
      if U ⊆ selected f then trialWeight p f*((H.filter (· ⊆ selected f)).card:ℝ)^k else 0 := by
  classical
  induction k generalizing U with
  | zero => simpa only [jointMoment,pow_zero,mul_one] using (sum_trialWeight_contains p U).symm
  | succ k ih =>
    simp only [jointMoment,ih]
    rw [sum_comm]
    apply sum_congr rfl
    intro f hf
    by_cases hU : U ⊆ selected f
    · simp only [union_subset_iff,hU,true_and,if_true]
      rw [← sum_filter]
      simp only [sum_const,nsmul_eq_mul,pow_succ]
      ring
    · simp only [union_subset_iff,hU,false_and,if_false,sum_const_zero]

/-- High moments of an induced r-uniform edge count. The error uses only
    the original maximum vertex degree K, not a sampled-degree hypothesis. -/
theorem moment_bound (H : Finset (Finset α)) (r K q : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hr : ∀ e ∈ H, e.card=r)
    (hK : ∀ a, (H.filter (fun e => a ∈ e)).card ≤ K) :
    (∑ f : α → Bool, trialWeight p f*((H.filter (· ⊆ selected f)).card:ℝ)^q) ≤
      (p^r*H.card+(r*q:ℕ)*K)^q := by
  have hb := jointMoment_bound H r K q p hp hp1 hr hK q ∅ (by simp)
  rw [jointMoment_expectation] at hb
  simpa only [empty_subset,if_true,card_empty,pow_zero,one_mul] using hb

/-- Markov's bound with arbitrary integral moment, entirely as finite sums. -/
theorem tail_bound (H : Finset (Finset α)) (r K q : ℕ) (p T : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hT : 0<T) (hr : ∀ e ∈ H, e.card=r)
    (hK : ∀ a, (H.filter (fun e => a ∈ e)).card ≤ K) :
    (∑ f : α → Bool, if T ≤ ((H.filter (· ⊆ selected f)).card:ℝ) then trialWeight p f else 0) ≤
      ((p^r*H.card+(r*q:ℕ)*K)/T)^q := by
  classical
  have hTq : 0<T^q := pow_pos hT q
  rw [div_pow]
  apply (le_div_iff₀ hTq).mpr
  calc
    _ = ∑ f : α → Bool,
        (if T ≤ ((H.filter (· ⊆ selected f)).card:ℝ) then trialWeight p f*T^q else 0) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro f hf
      split_ifs <;> simp
    _ ≤ ∑ f : α → Bool, trialWeight p f*((H.filter (· ⊆ selected f)).card:ℝ)^q := by
      apply sum_le_sum
      intro f hf
      split_ifs with h
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT.le h q) (trialWeight_nonneg hp hp1 f)
      · exact mul_nonneg (trialWeight_nonneg hp hp1 f) (pow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ _ := moment_bound H r K q p hp hp1 hr hK

end Expectation

#print axioms touching_card
#print axioms union_step
#print axioms jointMoment_bound
#print axioms jointMoment_expectation
#print axioms moment_bound
#print axioms tail_bound
end
end Erdos773.HypergraphSamplingMoments
