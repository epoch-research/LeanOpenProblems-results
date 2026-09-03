import Submission.RecursivePositiveScaling

/-! Identify the real numerical seeded recurrence with the set-indexed sound
sieve. This bridges the two previously separate interfaces; it does not prove
positivity of either recurrence. -/
namespace Erdos970.RecursiveSieve
open Finset

/-- Only marginals below the current prefix budget are accessed. -/
theorem seededLinearEnvelope_congr (q r : ℕ → ℝ) (seed : ℕ → ℝ → ℝ)
    (k : ℕ) (x : ℝ) (hqr : ∀ i < k, q i = r i) :
    seededLinearEnvelope q seed k x = seededLinearEnvelope r seed k x := by
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
    have hc (i : Fin k) : seededLinearEnvelope q seed i.val (x*q i.val) =
        seededLinearEnvelope r seed i.val (x*r i.val) := by
      rw [hqr i.val i.isLt]
      exact ih i.val i.isLt _ (fun j hj => hqr j (hj.trans i.isLt))
    conv_lhs => rw [seededLinearEnvelope]
    conv_rhs => rw [seededLinearEnvelope]
    simp only [hc]

/-- The set-indexed first-hit recursion has exactly the scalar-mass form. -/
theorem seededLinearEnvelope_eq_seededEnvelope (q : ℕ → ℝ) (seed : ℕ → ℝ → ℝ)
    (m : ℝ) (k : ℕ) (T : Finset ℕ) (hT : ∀ i ∈ T, k ≤ i) :
    seededLinearEnvelope q seed k (m*∏ i ∈ T, q i) =
      seededEnvelope (fun U => m*∏ i ∈ U, q i-1) (fun U => m*∏ i ∈ U, q i+1)
        (fun n U => seed n (m*∏ i ∈ U, q i)) k T := by
  induction k using Nat.strong_induction_on generalizing T with
  | h k ih =>
    have hn (i : Fin k) : i.val ∉ T := by
      intro hi
      exact (not_lt_of_ge (hT i.val hi)) i.isLt
    have ht (i : Fin k) : ∀ j ∈ insert i.val T, i.val ≤ j := by
      intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · rfl
      · exact i.isLt.le.trans (hT j hj)
    have hm (i : Fin k) : m*∏ j ∈ insert i.val T, q j =
        (m*∏ j ∈ T, q j)*q i.val := by
      rw [prod_insert (hn i)]
      ring
    have he (i : Fin k) := ih i.val i.isLt (insert i.val T) (ht i)
    simp only [hm] at he
    conv_lhs => rw [seededLinearEnvelope]
    conv_rhs => rw [seededEnvelope]
    simp only [← he]

/-- The arbitrary-prime reference positivity criterion can be evaluated by
the scalar numerical recurrence, without any arithmetic change of meaning. -/
theorem seededReferencePositive_iff_linear (K m : ℕ) (j g : ℕ → ℕ) :
    SeededReferencePositive K m j g ↔
      0 < (seededLinearEnvelope
        (fun i => 1/(Nat.nth Nat.Prime i : ℝ)) (blockSource j g) K (m : ℝ)).1 := by
  let q (i : Fin K) : ℝ := 1/(Nat.nth Nat.Prime i.val : ℝ)
  have he := seededLinearEnvelope_eq_seededEnvelope (extendMarginal q) (blockSource j g)
    (m : ℝ) K ∅ (by simp)
  simp only [prod_empty,mul_one,prod_extendMarginal] at he
  have hc := seededLinearEnvelope_congr (extendMarginal q)
    (fun i => 1/(Nat.nth Nat.Prime i : ℝ)) (blockSource j g) K (m : ℝ)
    (fun i hi => by simp only [extendMarginal,hi,dif_pos,q])
  rw [hc] at he
  change 0 < (seededEnvelope _ _ _ K ∅).1 ↔ _
  rw [he]

/-- Plain-certified block sources do not change the set-indexed reference
criterion either. Validity of arithmetic source bounds alone is not enough
for this equivalence: their plain-envelope positivity is also required. -/
theorem seededReferencePositive_iff_plain_of_plain_certificates
    (K m : ℕ) (j g : ℕ → ℕ)
    (hg : ∀ n ≤ K, 0 < g n)
    (hpos : ∀ n ≤ K, 0 < (linearEnvelope
      (fun i => 1/(Nat.nth Nat.Prime i : ℝ)) (j n) (g n : ℝ)).1) :
    SeededReferencePositive K m j g ↔
      0 < (linearEnvelope (fun i => 1/(Nat.nth Nat.Prime i : ℝ)) K (m : ℝ)).1 := by
  rw [seededReferencePositive_iff_linear]
  have hq (i : ℕ) : 0 ≤ 1/(Nat.nth Nat.Prime i : ℝ) ∧
      1/(Nat.nth Nat.Prime i : ℝ) ≤ 1 := by
    have hp : (1 : ℝ) < Nat.nth Nat.Prime i := by exact_mod_cast (Nat.prime_nth_prime i).one_lt
    exact ⟨by positivity, (div_le_one (by linarith)).mpr hp.le⟩
  rw [block_seeded_eq_plain_of_plain_certificates _ hq j g K hg hpos _ (Nat.cast_nonneg m)]

#print axioms seededLinearEnvelope_eq_seededEnvelope
#print axioms seededReferencePositive_iff_linear
#print axioms seededReferencePositive_iff_plain_of_plain_certificates
end Erdos970.RecursiveSieve
