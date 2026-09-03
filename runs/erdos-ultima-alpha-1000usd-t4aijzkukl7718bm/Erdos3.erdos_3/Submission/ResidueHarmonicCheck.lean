import Submission.Reduction

/-! Residue subdivision gives a non-expansive harmonic-weight estimate, but
3-AP-freeness does not give any uniform strict contraction in that estimate.
This obstruction concerns a proposed proof method, not the original conjecture. -/
namespace Erdos3ResidueHarmonicCheck

open Finset Erdos3Reduction
set_option maxHeartbeats 1000000

def residueQuotient (S : Finset ℕ) (q r : ℕ) : Finset ℕ :=
  (S.filter (fun x ↦ x % q = r)).image (fun x ↦ x / q)

lemma quotient_weight_eq (S : Finset ℕ) (q r : ℕ) :
    recipWeight (residueQuotient S q r) =
      ∑ x ∈ S.filter (fun x ↦ x % q = r), 1 / ((x / q : ℕ) : ℝ) := by
  apply sum_image
  intro a ha b hb he
  have ha' := (mem_filter.mp ha).2
  have hb' := (mem_filter.mp hb).2
  change a / q = b / q at he
  change a % q = r at ha'
  change b % q = r at hb'
  calc
    a = q*(a/q) + a%q := (Nat.div_add_mod a q).symm
    _ = q*(b/q) + b%q := by rw [he, ha', hb']
    _ = b := Nat.div_add_mod b q

/-- With the low initial segment removed, subdivision cannot increase the
maximum normalized reciprocal weight. The coefficient here is exactly one. -/
theorem weight_le_max_residue {S : Finset ℕ} {q : ℕ} {M : ℝ}
    (hq : 0 < q) (hS : ∀ x ∈ S, q ≤ x)
    (hM : ∀ r < q, recipWeight (residueQuotient S q r) ≤ M) :
    recipWeight S ≤ M := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpoint (x : ℕ) (hx : x ∈ S) :
      1 / (x : ℝ) ≤ (1 / (q : ℝ)) * (1 / ((x / q : ℕ) : ℝ)) := by
    have hdiv : 0 < x / q := Nat.div_pos (hS x hx) hq
    rw [one_div_mul_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (show q * (x / q) ≤ x by simpa only [Nat.mul_comm] using Nat.div_mul_le_self x q)
  calc
    recipWeight S ≤ ∑ x ∈ S, (1 / (q : ℝ)) * (1 / ((x / q : ℕ) : ℝ)) :=
      sum_le_sum hpoint
    _ = (1 / (q : ℝ)) * ∑ r ∈ range q, recipWeight (residueQuotient S q r) := by
      simp_rw [quotient_weight_eq]
      rw [sum_fiberwise_of_maps_to (fun x _ ↦ mem_range.mpr (Nat.mod_lt x hq))]
      exact (mul_sum _ _ _).symm
    _ ≤ (1 / (q : ℝ)) * ∑ _r ∈ range q, M := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum (fun r hr ↦ hM r (mem_range.mp hr))
    _ = M := by simp [hqR.ne']

def witness (n : ℕ) : Finset ℕ := {3*n, 3*n+1, 3*n+5}

lemma witness_free (n : ℕ) : ThreeAPFree (witness n : Set ℕ) := by
  intro a ha b hb c hc he
  simp only [witness, mem_coe, mem_insert, mem_singleton] at ha hb hc
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> omega

lemma witness_quotients (n : ℕ) :
    residueQuotient (witness n) 3 0 = {n} ∧
    residueQuotient (witness n) 3 1 = {n} ∧
    residueQuotient (witness n) 3 2 = {n+1} := by
  have h0 : (3*n) % 3 = 0 := by omega
  have h1 : (3*n+1) % 3 = 1 := by omega
  have h2 : (3*n+5) % 3 = 2 := by omega
  have hd0 : (3*n) / 3 = n := by omega
  have hd1 : (3*n+1) / 3 = n := by omega
  have hd2 : (3*n+5) / 3 = n+1 := by omega
  simp [residueQuotient, witness, filter_insert, filter_singleton, h0, h1, h2, hd0, hd1, hd2]

lemma witness_weight_lower {n : ℕ} (hn : 0 < n) :
    3 / (3*(n : ℝ)+5) ≤ recipWeight (witness n) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have he : recipWeight (witness n) =
      1/(3*(n : ℝ)) + 1/(3*(n : ℝ)+1) + 1/(3*(n : ℝ)+5) := by
    simp [recipWeight, witness, add_assoc]
  rw [he]
  have h0 : 1/(3*(n : ℝ)+5) ≤ 1/(3*(n : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have h1 : 1/(3*(n : ℝ)+5) ≤ 1/(3*(n : ℝ)+1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  simp only [div_eq_mul_inv, one_mul] at *
  linarith

/-- Even above the initial segment, no coefficient c < 1 works uniformly in
the residue-max estimate, already for modulus 3 and three-point 3-AP-free sets. -/
theorem no_strict_residue_contraction (c : ℝ) (hc : c < 1) :
    ∃ S : Finset ℕ, ∃ M : ℝ, 0 < M ∧ ThreeAPFree (S : Set ℕ) ∧
      (∀ x ∈ S, 3 ≤ x) ∧
      (∀ r < 3, recipWeight (residueQuotient S 3 r) ≤ M) ∧
      c*M < recipWeight S := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 : ℝ) (5/(1-c)))
  have hn1 : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hn0 : 0 < n := by exact_mod_cast (zero_lt_one.trans hn1)
  have hnp : (0 : ℝ) < n := zero_lt_one.trans hn1
  have hcn : 5 < (n : ℝ)*(1-c) :=
    (div_lt_iff₀ (by linarith : 0 < 1-c)).mp ((le_max_right _ _).trans_lt hn)
  refine ⟨witness n, 1/(n : ℝ), by positivity, witness_free n, ?_, ?_, ?_⟩
  · intro x hx
    simp only [witness, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> omega
  · intro r hr
    obtain ⟨h0,h1,h2⟩ := witness_quotients n
    interval_cases r
    · simp [h0, recipWeight]
    · simp [h1, recipWeight]
    · simp only [h2, recipWeight, sum_singleton, Nat.cast_add, Nat.cast_one]
      exact one_div_le_one_div_of_le hnp (by linarith)
  · apply lt_of_lt_of_le _ (witness_weight_lower hn0)
    rw [mul_one_div, div_lt_div_iff₀ hnp (by positivity)]
    nlinarith

#print axioms weight_le_max_residue
#print axioms no_strict_residue_contraction
end Erdos3ResidueHarmonicCheck
