import FormalConjecturesUtil
import Submission.SparseAffineAllowance
import Submission.PrimeSupportHall

/-! A precise sufficient matching criterion after discarding prime inputs and
inputs divisible by the slope. The matching and its Hall inequalities are
explicit hypotheses, not unconditional results about Erdős 371. -/

namespace Erdos371DiscardedMatchingCriterion

open Finset Filter Erdos371SparseAffineAllowance Erdos371PrimeSupportHall
abbrev P := Nat.maxPrimeFac

def retained (p A : ℕ) (F : ℕ → ℕ) : Finset ℕ :=
  (Icc 1 A).filter (fun a => P (F a) < P a ∧ ¬a.Prime ∧ ¬p ∣ a)

def favorable (A : ℕ) (F : ℕ → ℕ) : Finset ℕ :=
  (Icc 1 A).filter (fun b => P b ≤ P (F b))

lemma prime_inputs_card (A : ℕ) :
    ((Icc 1 A).filter Nat.Prime).card = Nat.primeCounting A := by
  have he : (Icc 1 A).filter Nat.Prime = (A+1).primesBelow := by
    ext a
    simp only [mem_filter, mem_Icc, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨_, ha⟩, hp⟩
      exact ⟨by omega, hp⟩
    · rintro ⟨ha, hp⟩
      exact ⟨⟨hp.pos, by omega⟩, hp⟩
  rw [he, Nat.primesBelow_card_eq_primeCounting']
  rfl

lemma multiples_inputs_card_le {p : ℕ} (hp : 0 < p) (A : ℕ) :
    ((Icc 1 A).filter (fun a => p ∣ a)).card ≤ A/p := by
  have hh : ((Icc 1 A).filter (fun a => p ∣ a)).card ≤ (Icc 1 (A/p)).card := by
    apply Finset.card_le_card_of_injOn (fun a : ℕ => a/p)
    · intro a ha
      change a ∈ (Icc 1 A).filter (fun a => p ∣ a) at ha
      obtain ⟨haA, hd⟩ := mem_filter.mp ha
      obtain ⟨ha1, haA⟩ := mem_Icc.mp haA
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd ha1 hd) hp, Nat.div_le_div_right haA⟩
    · intro a ha b hb he
      change a ∈ (Icc 1 A).filter (fun a => p ∣ a) at ha
      change b ∈ (Icc 1 A).filter (fun a => p ∣ a) at hb
      have haeq := Nat.div_mul_cancel (mem_filter.mp ha).2
      have hbeq := Nat.div_mul_cancel (mem_filter.mp hb).2
      change a/p = b/p at he
      rw [he] at haeq
      omega
  simpa using hh

lemma exception_inputs_card_le {p : ℕ} (hp : 0 < p) (A : ℕ) :
    ((Icc 1 A).filter (fun a => a.Prime ∨ p ∣ a)).card ≤ Nat.primeCounting A + A/p := by
  rw [Finset.filter_or]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add
    (prime_inputs_card A).le (multiples_inputs_card_le hp A))

lemma comparison_sum_eq (A : ℕ) (F : ℕ → ℕ) :
    (∑ a ∈ Icc 1 A, Erdos371PrimeDeletion.compare (P (F a)) (P a)) =
      (((Icc 1 A).filter (fun a => P (F a) < P a)).card : ℝ) - (favorable A F).card := by
  have he (a : ℕ) : Erdos371PrimeDeletion.compare (P (F a)) (P a) =
      (if P (F a) < P a then (1:ℝ) else 0) - (if P a ≤ P (F a) then 1 else 0) := by
    unfold Erdos371PrimeDeletion.compare
    split_ifs <;> norm_num <;> omega
  simp only [he, sum_sub_distrib, Finset.sum_boole, favorable]

lemma prefix_bound_of_retained_card {p A : ℕ} (hp : 0 < p) (F : ℕ → ℕ)
    (hcard : (retained p A F).card ≤ (favorable A F).card) :
    (∑ a ∈ Icc 1 A, Erdos371PrimeDeletion.compare (P (F a)) (P a)) ≤
      (A:ℝ)/p + Nat.primeCounting A := by
  have hsub : (Icc 1 A).filter (fun a => P (F a) < P a) ⊆
      retained p A F ∪ (Icc 1 A).filter (fun a => a.Prime ∨ p ∣ a) := by
    intro a ha
    obtain ⟨haA, haP⟩ := mem_filter.mp ha
    by_cases he : a.Prime ∨ p ∣ a
    · exact mem_union_right _ (mem_filter.mpr ⟨haA, he⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨haA, haP, not_or.mp he⟩)
  have hbad : ((Icc 1 A).filter (fun a => P (F a) < P a)).card ≤
      (favorable A F).card + (Nat.primeCounting A + A/p) := by
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add hcard (exception_inputs_card_le hp A)))
  have hbadR : (((Icc 1 A).filter (fun a => P (F a) < P a)).card : ℝ) ≤
      (favorable A F).card + ((Nat.primeCounting A:ℝ) + (A/p:ℕ)) := by exact_mod_cast hbad
  have hdiv : ((A/p:ℕ):ℝ) ≤ (A:ℝ)/p := Nat.cast_div_le
  rw [comparison_sum_eq]
  linarith

lemma prefix_bound_of_retained_matching {p A : ℕ} (hp : 0 < p) (F : ℕ → ℕ)
    (hm : ∃ f : retained p A F → ℕ, Function.Injective f ∧
      ∀ a, f a ∈ favorable A F) :
    (∑ a ∈ Icc 1 A, Erdos371PrimeDeletion.compare (P (F a)) (P a)) ≤
      (A:ℝ)/p + Nat.primeCounting A := by
  obtain ⟨f, hf, hmem⟩ := hm
  let g : retained p A F → favorable A F := fun a => ⟨f a, hmem a⟩
  have hg : Function.Injective g := by
    intro a b he
    exact hf (congrArg Subtype.val he)
  exact prefix_bound_of_retained_card hp F (Finset.card_le_card_of_injective hg)

/-- A universal matching of the retained sources would settle the conjecture.
No such universal matching is established here. -/
theorem density_half_of_retained_matching
    (hm : ∀ p : ℕ, p.Prime → ∀ A : ℕ,
      ∃ f : retained p A (fun a => a*p-1) → ℕ, Function.Injective f ∧
        ∀ a, f a ∈ favorable A (fun b => b*p-1))
    (hp : ∀ p : ℕ, p.Prime → ∀ A : ℕ,
      ∃ f : retained p A (fun a => a*p+1) → ℕ, Function.Injective f ∧
        ∀ a, f a ∈ favorable A (fun b => b*p+1)) :
    {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)}.HasDensity (1/2) := by
  apply density_half_of_sparse_prefix_allowance (C := 1) (D := 1) (E := 0)
    (by norm_num) (by norm_num) (by norm_num)
  · intro p hprime A
    simpa using prefix_bound_of_retained_matching hprime.pos (fun a => a*p-1) (hm p hprime A)
  · intro p hprime A
    simpa using prefix_bound_of_retained_matching hprime.pos (fun a => a*p+1) (hp p hprime A)

/-- The exact support inequalities required for the candidate shared-input-prime
graph, where the target support is that of the target's affine value. -/
def SupportCondition (p A : ℕ) (F : ℕ → ℕ) : Prop :=
  ∀ R : Finset ℕ, R ⊆ univ.biUnion (fun a : retained p A F => (a:ℕ).primeFactors) →
    (univ.filter (fun a : retained p A F => (a:ℕ).primeFactors ⊆ R)).card ≤
      ((favorable A F).filter (fun b => (R ∩ (F b).primeFactors).Nonempty)).card

lemma retained_matching_of_support_condition {p A : ℕ} (F : ℕ → ℕ)
    (h : SupportCondition p A F) :
    ∃ f : retained p A F → ℕ, Function.Injective f ∧
      ∀ a, f a ∈ favorable A F ∧
        ((a:ℕ).primeFactors ∩ (F (f a)).primeFactors).Nonempty :=
  (support_hall_iff (favorable A F) (fun a : retained p A F => (a:ℕ).primeFactors)
    (fun b => (F b).primeFactors)).mp h

theorem density_half_of_retained_support_conditions
    (hm : ∀ p : ℕ, p.Prime → ∀ A : ℕ, SupportCondition p A (fun a => a*p-1))
    (hp : ∀ p : ℕ, p.Prime → ∀ A : ℕ, SupportCondition p A (fun a => a*p+1)) :
    {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)}.HasDensity (1/2) := by
  apply density_half_of_retained_matching
  · intro p hprime A
    obtain ⟨f, hf, hmem⟩ := retained_matching_of_support_condition _ (hm p hprime A)
    exact ⟨f, hf, fun a => (hmem a).1⟩
  · intro p hprime A
    obtain ⟨f, hf, hmem⟩ := retained_matching_of_support_condition _ (hp p hprime A)
    exact ⟨f, hf, fun a => (hmem a).1⟩

end Erdos371DiscardedMatchingCriterion

#print axioms Erdos371DiscardedMatchingCriterion.prefix_bound_of_retained_matching
#print axioms Erdos371DiscardedMatchingCriterion.density_half_of_retained_support_conditions
