import FormalConjecturesUtil
import Submission.Capacity126
import Submission.ArithmeticModel126
import Submission.Limit126

/-! The polynomial prime-support bound and the extremal limit. -/

namespace E126

/-- A polynomial upper bound for a positive set in terms of its sum-prime support. -/
theorem positive_card_bound (A : Finset ℕ) (hpos : ∀ a ∈ A, 0 < a) :
    A.card ≤ 1024 * ((∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card + 1) ^ 8 := by
  classical
  let S := Signature126.primeSupport A
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hsupp : ∀ i j : A, i ≠ j → (i.val + j.val).primeFactors ⊆ S := by
    intro i j hij p hp
    obtain ⟨hpr, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact (Independent126.prime_mem_iff A p).mpr
      ⟨hpr, i, i.property, j, j.property, (fun h => hij (Subtype.ext h)), hdvd⟩
  have ha : ∀ i : A, 0 < (i : ℕ) := fun i => hpos i i.property
  have hinj : Function.Injective (fun i : A => (i : ℕ)) := Subtype.val_injective
  have hc := opposition_capacity (arithmeticModel (fun i : A => (i : ℕ)) S hprime)
    (arithmeticModel_signed_neg _ ha hinj S hprime hsupp)
    (arithmeticModel_cnd _ ha S hprime hsupp)
  simpa [S, Signature126.primeSupport] using hc

/-- The original asymptotic assertion, for the independently copied extremal definition. -/
theorem extremal_tendsto {f : ℕ → ℕ} (hf : Independent126.IsMaximalAddFactorsCard f) :
    Filter.Tendsto (fun n => (f n : ℝ) / Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
  maximal_tendsto_of_positive_bound hf positive_card_bound

#print axioms opposition_capacity
#print axioms positive_card_bound
#print axioms extremal_tendsto

end E126
