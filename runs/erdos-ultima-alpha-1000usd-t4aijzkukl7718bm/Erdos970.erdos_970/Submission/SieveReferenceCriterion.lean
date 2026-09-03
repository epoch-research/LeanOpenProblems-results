import Submission.SieveCertificateTransfer
import Submission.SelbergPrimes

/-!
A sufficient reduction of the quadratic Jacobsthal conjecture to absolute-error sieve
certificates at the first `k` primes. Existence of the required certificates is not assumed
except as an explicit hypothesis of the final theorem.
-/
namespace Erdos970.FiniteSelberg

/-- An increasing list of primes dominates the corresponding initial list of primes. -/
theorem nth_prime_le_sorted {k : ℕ} (p : Fin k → ℕ)
    (hp : ∀ i, (p i).Prime) (hmono : StrictMono p) (i : Fin k) :
    Nat.nth Nat.Prime i.val ≤ p i := by
  classical
  have hsub : (Finset.Iio i).image p ⊆
      (Finset.range (p i)).filter Nat.Prime := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (hmono (Finset.mem_Iio.mp hj)), hp j⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hmono.injective.injOn, Fin.card_Iio,
    ← Nat.count_eq_card_filter_range] at hc
  exact (Nat.nth_monotone Nat.infinite_setOf_prime hc).trans_eq (Nat.nth_count (hp i))

/-- A pointwise lower polynomial whose main term exceeds its full absolute error budget. -/
def HasReferenceCertificate (k m : ℕ) : Prop :=
  ∃ c : Finset (Fin k) → ℝ,
    (∀ v : Fin k → Bool, v ≠ (fun _ => false) →
      (∑ T : Finset (Fin k), c T * hitMonomial T v) ≤ 0) ∧
    (∑ T : Finset (Fin k), |c T|) < (m : ℝ) *
      ∑ T : Finset (Fin k), c T * ∏ i ∈ T, (1 / (Nat.nth Nat.Prime i.val : ℝ))

/-- A valid reference certificate remains valid when the interval gets longer. -/
theorem HasReferenceCertificate.mono {k m m' : ℕ}
    (h : HasReferenceCertificate k m) (hmm' : m ≤ m') :
    HasReferenceCertificate k m' := by
  obtain ⟨c, hpoint, hmain⟩ := h
  refine ⟨c, hpoint, hmain.trans_le ?_⟩
  have hmean : 0 < ∑ T : Finset (Fin k), c T *
      ∏ i ∈ T, (1 / (Nat.nth Nat.Prime i.val : ℝ)) := by
    have hnorm : 0 ≤ ∑ T : Finset (Fin k), |c T| :=
      Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmm') hmean.le

/-- Reference certificates apply to any set of the same number of distinct primes. -/
theorem survivor_of_referenceCertificate {P : Finset ℕ} {m : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (r : ℕ → ℕ)
    (hcert : HasReferenceCertificate P.card m) :
    ∃ j < m, ∀ p ∈ P, ¬j ≡ r p [MOD p] := by
  classical
  obtain ⟨c, hpoint, hmain⟩ := hcert
  let p : Fin P.card → ℕ := P.orderEmbOfFin rfl
  have hp : ∀ i, (p i).Prime := fun i => hP _ (P.orderEmbOfFin_mem rfl i)
  have hmono : StrictMono p := (P.orderEmbOfFin rfl).strictMono
  have hq (i : Fin P.card) :
      1 / (p i : ℝ) < 1 ∧
      1 / (p i : ℝ) ≤ 1 / (Nat.nth Nat.Prime i.val : ℝ) ∧
      1 / (Nat.nth Nat.Prime i.val : ℝ) ≤ 1 := by
    have ha : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
    have hb : (1 : ℝ) < Nat.nth Nat.Prime i.val := by
      exact_mod_cast (Nat.prime_nth_prime i.val).one_lt
    have hab : (Nat.nth Nat.Prime i.val : ℝ) ≤ p i := by
      exact_mod_cast nth_prime_le_sorted p hp hmono i
    refine ⟨(div_lt_iff₀ (by linarith : (0 : ℝ) < p i)).mpr (by linarith),
      one_div_le_one_div_of_le (by linarith) hab, ?_⟩
    exact (div_le_one (by linarith : (0 : ℝ) < Nat.nth Nat.Prime i.val)).mpr hb.le
  obtain ⟨j, hj, hjall⟩ := survivor_from_dominating_moments Finset.univ c id
    (fun i => 1 / (p i : ℝ)) (fun i => 1 / (Nat.nth Nat.Prime i.val : ℝ)) hq m
    (fun j i => decide (j ≡ r (p i) [MOD p i]))
    (prime_hits_intersection_error p hp hmono.injective r m) hpoint hmain
  refine ⟨j, hj, ?_⟩
  intro q hqP
  have hqrange : q ∈ Set.range p := by
    simpa only [p, Finset.range_orderEmbOfFin, Finset.mem_coe] using hqP
  obtain ⟨i, rfl⟩ := hqrange
  exact of_decide_eq_false (hjall i)

/-- To handle at most `k` primes, certificates of each cardinality up to `k` suffice. -/
theorem isJacobsthalBound_of_referenceCertificates (k m : ℕ) (hm : 0 < m)
    (hcert : ∀ j, 0 < j → j ≤ k → HasReferenceCertificate j m) :
    IsJacobsthalBound k m := by
  classical
  by_contra hbad
  obtain ⟨P, hP, hPk, r, hcover⟩ := (not_isJacobsthalBound_iff_cover k m).mp hbad
  have hPpos : 0 < P.card := by
    obtain ⟨p, hp, _⟩ := hcover 0 hm
    exact Finset.card_pos.mpr ⟨p, hp⟩
  obtain ⟨j, hj, hjP⟩ := survivor_of_referenceCertificate hP r
    (hcert P.card hPpos hPk)
  obtain ⟨p, hp, hjp⟩ := hcover j hj
  exact hjP p hp hjp

/-- A uniformly quadratic family of reference certificates would prove the conjecture.
The quantitative certificate hypothesis remains an additional, unproved requirement. -/
theorem quadratic_bound_of_referenceCertificates (D : ℕ) (hD : 0 < D)
    (hcert : ∀ k, 0 < k → HasReferenceCertificate k (D * k ^ 2)) :
    ∃ C > (0 : ℝ), ∀ k : ℕ, 0 < k →
      (jacobsthalFunction k : ℝ) ≤ C * k ^ 2 := by
  apply quadratic_bound_iff_nat.mpr
  refine ⟨D, hD, fun k hk => ?_⟩
  apply isJacobsthalBound_of_referenceCertificates k (D * k ^ 2)
    (Nat.mul_pos hD (pow_pos hk 2))
  intro j hj hjk
  apply (hcert j hj).mono
  gcongr

#print axioms nth_prime_le_sorted
#print axioms survivor_of_referenceCertificate
#print axioms quadratic_bound_of_referenceCertificates

end Erdos970.FiniteSelberg
