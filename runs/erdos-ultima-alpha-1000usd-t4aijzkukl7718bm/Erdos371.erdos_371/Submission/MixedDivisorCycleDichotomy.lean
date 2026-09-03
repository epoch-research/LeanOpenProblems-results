import Submission.DivisorCycleBound

/-!
A finite dichotomy for closed divisor walks with arbitrary traversal
orientations. Large label products force equality of the two endpoint
products; they do not exclude the mixed walk itself. No density assertion
or bound on the number of such walks is made here.
-/
namespace Erdos371
open Finset
set_option autoImplicit false

lemma endpoint_product_sub_le {ι : Type*} (s : Finset ι)
    (n a b : ι → ℕ)
    (ha : ∀ i ∈ s, a i ≤ n i+1) (hb : ∀ i ∈ s, n i ≤ b i) :
    (∏ i ∈ s, a i)-(∏ i ∈ s, b i) ≤
      (∏ i ∈ s, (n i+1))-(∏ i ∈ s, n i) := by
  have hA := prod_le_prod' ha
  have hB := prod_le_prod' hb
  omega

/-- The arbitrary orientation version of the divisor-cycle bound must
retain the exact-product-equality alternative. The empty indexing type
is allowed: its endpoint products are both one. -/
theorem endpoint_divisor_cycle_dichotomy {ι : Type*} [Fintype ι]
    (σ : ι ≃ ι) (n p a b : ι → ℕ) (N : ℕ)
    (hnN : ∀ i, n i ≤ N)
    (ha : ∀ i, n i ≤ a i ∧ a i ≤ n i+1)
    (hb : ∀ i, n i ≤ b i ∧ b i ≤ n i+1)
    (hp : ∀ i, p i ∣ a i) (hnext : ∀ i, p (σ i) ∣ b i) :
    (∏ i, a i) = (∏ i, b i) ∨
      (∏ i, p i) ≤ (N+1)^Fintype.card ι-N^Fintype.card ι := by
  have hdA : (∏ i, p i) ∣ ∏ i, a i :=
    prod_dvd_prod_of_dvd p a (fun i _ => hp i)
  have hdB : (∏ i, p i) ∣ ∏ i, b i := by
    have h := prod_dvd_prod_of_dvd (fun i => p (σ i)) b
      (s := univ) (fun i _ => hnext i)
    simpa only [Equiv.prod_comp] using h
  have hbound := prod_succ_sub_prod_le_pow_difference univ n N (fun i _ => hnN i)
  rcases lt_trichotomy (∏ i, a i) (∏ i, b i) with hlt | heq | hgt
  · right
    exact (Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) (Nat.dvd_sub hdB hdA)).trans
      ((endpoint_product_sub_le univ n b a (fun i _ => (hb i).2)
        (fun i _ => (ha i).1)).trans hbound)
  · exact Or.inl heq
  · right
    exact (Nat.le_of_dvd (Nat.sub_pos_of_lt hgt) (Nat.dvd_sub hdA hdB)).trans
      ((endpoint_product_sub_le univ n a b (fun i _ => (ha i).2)
        (fun i _ => (hb i).1)).trans hbound)

def mixedCycleSource (n : ℕ) (forward : Bool) : ℕ :=
  if forward then n else n+1

def mixedCycleTarget (n : ℕ) (forward : Bool) : ℕ :=
  if forward then n+1 else n

lemma mixedCycleSource_bounds (n : ℕ) (forward : Bool) :
    n ≤ mixedCycleSource n forward ∧ mixedCycleSource n forward ≤ n+1 := by
  cases forward <;> simp [mixedCycleSource]

lemma mixedCycleTarget_bounds (n : ℕ) (forward : Bool) :
    n ≤ mixedCycleTarget n forward ∧ mixedCycleTarget n forward ≤ n+1 := by
  cases forward <;> simp [mixedCycleTarget]

/-- This permits repeated labels and repeated edges. Divisibility is
applied once per incidence, so the label product retains multiplicity. -/
theorem mixed_divisor_cycle_dichotomy {ι : Type*} [Fintype ι]
    (σ : ι ≃ ι) (n p : ι → ℕ) (forward : ι → Bool) (N : ℕ)
    (hnN : ∀ i, n i ≤ N)
    (hp : ∀ i, p i ∣ mixedCycleSource (n i) (forward i))
    (hnext : ∀ i, p (σ i) ∣ mixedCycleTarget (n i) (forward i)) :
    (∏ i, mixedCycleSource (n i) (forward i)) =
      (∏ i, mixedCycleTarget (n i) (forward i)) ∨
    (∏ i, p i) ≤ Fintype.card ι*(N+1)^(Fintype.card ι-1) := by
  rcases endpoint_divisor_cycle_dichotomy σ n p
    (fun i => mixedCycleSource (n i) (forward i))
    (fun i => mixedCycleTarget (n i) (forward i)) N hnN
    (fun i => mixedCycleSource_bounds _ _) (fun i => mixedCycleTarget_bounds _ _)
    hp hnext with he | hle
  · exact Or.inl he
  · exact Or.inr (hle.trans (nat_succ_pow_sub_pow_le N (Fintype.card ι)))

/-- A large product of the actual largest-prime labels forces the
product-equality case. This is not an exclusion of mixed cycles. -/
theorem actual_mixed_cycle_product_equality_of_large {ι : Type*} [Fintype ι]
    (σ : ι ≃ ι) (n : ι → ℕ) (forward : ι → Bool) (N : ℕ)
    (hnN : ∀ i, n i ≤ N)
    (hclose : ∀ i,
      Nat.maxPrimeFac (mixedCycleTarget (n i) (forward i)) =
      Nat.maxPrimeFac (mixedCycleSource (n (σ i)) (forward (σ i))))
    (hlarge : Fintype.card ι*(N+1)^(Fintype.card ι-1) <
      ∏ i, Nat.maxPrimeFac (mixedCycleSource (n i) (forward i))) :
    (∏ i, mixedCycleSource (n i) (forward i)) =
      (∏ i, mixedCycleTarget (n i) (forward i)) := by
  have h := mixed_divisor_cycle_dichotomy σ n
    (fun i => Nat.maxPrimeFac (mixedCycleSource (n i) (forward i))) forward N hnN
    (fun _ => Nat.maxPrimeFac_dvd) (fun i => ?_)
  · exact h.resolve_right (not_le_of_gt hlarge)
  · dsimp only
    rw [← hclose i]
    exact Nat.maxPrimeFac_dvd

/-- A uniform lower bound for every label gives a directly usable finite
version of the large-product criterion. -/
theorem actual_mixed_cycle_product_equality_of_label_cutoff {ι : Type*} [Fintype ι]
    (σ : ι ≃ ι) (n : ι → ℕ) (forward : ι → Bool) (N B : ℕ)
    (hnN : ∀ i, n i ≤ N)
    (hclose : ∀ i,
      Nat.maxPrimeFac (mixedCycleTarget (n i) (forward i)) =
      Nat.maxPrimeFac (mixedCycleSource (n (σ i)) (forward (σ i))))
    (hB : ∀ i, B < Nat.maxPrimeFac (mixedCycleSource (n i) (forward i)))
    (hsize : Fintype.card ι*(N+1)^(Fintype.card ι-1) < (B+1)^Fintype.card ι) :
    (∏ i, mixedCycleSource (n i) (forward i)) =
      (∏ i, mixedCycleTarget (n i) (forward i)) := by
  apply actual_mixed_cycle_product_equality_of_large σ n forward N hnN hclose
  apply hsize.trans_le
  simpa using (prod_le_prod' (s := (univ : Finset ι))
    (f := fun _ => B+1)
    (g := fun i => Nat.maxPrimeFac (mixedCycleSource (n i) (forward i)))
    (fun i _ => Nat.succ_le_of_lt (hB i)))

#print axioms endpoint_divisor_cycle_dichotomy
#print axioms actual_mixed_cycle_product_equality_of_label_cutoff
end Erdos371
