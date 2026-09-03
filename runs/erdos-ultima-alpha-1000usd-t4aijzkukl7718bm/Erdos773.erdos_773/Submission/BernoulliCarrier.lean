import Submission.Hypergraph

/-! Bernoulli sampling identities on arbitrary finite ambient carriers. -/
namespace Erdos773.BernoulliCarrier
open Finset
set_option maxHeartbeats 2000000
noncomputable section
variable {α : Type*} [DecidableEq α]

def sample (A : Finset α) (f : A → Bool) : Finset α := (selected f).map (Function.Embedding.subtype _)

omit [DecidableEq α] in
lemma sample_subset (A : Finset α) (f : A → Bool) : sample A f ⊆ A := by
  intro a ha
  obtain ⟨a,ha,rfl⟩ := mem_map.mp ha
  exact a.property

omit [DecidableEq α] in
lemma sample_card (A : Finset α) (f : A → Bool) : (sample A f).card=(selected f).card := card_map _

lemma contains_iff {A I : Finset α} (hI : I ⊆ A) (f : A → Bool) :
    I ⊆ sample A f ↔ I.subtype (· ∈ A) ⊆ selected f := by
  rw [← map_subset_map (f := Function.Embedding.subtype (· ∈ A)),subtype_map_of_mem hI]
  rfl

lemma contains (A I : Finset α) (hI : I ⊆ A) (p : ℝ) :
    (∑ f : A → Bool, if I ⊆ sample A f then trialWeight p f else 0)=p^I.card := by
  have hc : (I.subtype (· ∈ A)).card=I.card := by rw [← card_map (Function.Embedding.subtype _),subtype_map_of_mem hI]
  simp only [contains_iff hI,sum_trialWeight_contains,hc]

lemma weighted_card (A : Finset α) (p : ℝ) :
    (∑ f : A → Bool, trialWeight p f*((sample A f).card:ℝ))=p*A.card := by
  simpa only [sample_card,Fintype.card_coe] using sum_trialWeight_card (α := A) p

/-- Expected weighted count of all retained members of a finite family. -/
lemma weighted_family (A : Finset α) (H : Finset (Finset α)) (hH : ∀ I ∈ H, I ⊆ A) (p x : ℝ) :
    (∑ f : A → Bool, trialWeight p f*(∑ I ∈ H, if I ⊆ sample A f then x^I.card else 0)) =
      ∑ I ∈ H, (p*x)^I.card := by
  classical
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro I hI
  calc
    _ = (∑ f : A → Bool, if I ⊆ sample A f then trialWeight p f else 0)*x^I.card := by
      rw [sum_mul]
      apply sum_congr rfl
      intro f hf
      split_ifs <;> simp
    _ = _ := by rw [contains A I (hH I hI),mul_pow]

lemma weighted_count (A : Finset α) (H : Finset (Finset α)) (hH : ∀ I ∈ H, I ⊆ A) (p : ℝ) :
    (∑ f : A → Bool, trialWeight p f*((H.filter (· ⊆ sample A f)).card:ℝ)) = ∑ I ∈ H, p^I.card := by
  simpa only [one_pow,← sum_filter,sum_const,nsmul_eq_mul,mul_one] using weighted_family A H hH p 1

lemma weighted_uniform_count (A : Finset α) (H : Finset (Finset α))
    (hH : ∀ I ∈ H, I ⊆ A) (r : ℕ) (hr : ∀ I ∈ H, I.card=r) (p : ℝ) :
    (∑ f : A → Bool, trialWeight p f*((H.filter (· ⊆ sample A f)).card:ℝ)) = p^r*H.card := by
  rw [weighted_count A H hH p]
  calc
    _ = ∑ _I ∈ H, p^r := sum_congr rfl (fun I hI => congrArg (fun k => p^k) (hr I hI))
    _ = _ := by simp only [sum_const,nsmul_eq_mul]; ring

#print axioms weighted_uniform_count
#print axioms contains
#print axioms weighted_family
#print axioms weighted_count
end
end Erdos773.BernoulliCarrier
