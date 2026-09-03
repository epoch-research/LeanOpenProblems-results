import Submission.ForestCapacity

/-! A root-overlap compensation inequality independent of exponent caps.
This is an auxiliary estimate, not an odd-covering obstruction on its own. -/
namespace Erdos7BinaryRootOverlap
set_option maxHeartbeats 1500000
set_option autoImplicit false

/-- Two boxes on the same ternary-survivor branch. Their leaf masses need only
be bounded above; missing leaf mass is charged to the vertex deficits. -/
lemma same_branch (u a b A B : ℚ) (hu0 : 0 ≤ u) (hu : u ≤ 2/3)
    (ha : 0 ≤ a ∧ a ≤ A) (hb : 0 ≤ b ∧ b ≤ B) :
    (2/3)*A*B ≤ u*a*b + 2*B*((2/3)*A-u*a) + 2*A*((2/3)*B-u*b) := by
  have hA : 0 ≤ A := ha.1.trans ha.2
  have hB : 0 ≤ B := hb.1.trans hb.2
  have h₁ := mul_nonneg (mul_nonneg hu0 (sub_nonneg.mpr ha.2))
    (show 0 ≤ 2*B-b by linarith)
  have h₂ := mul_nonneg (mul_nonneg hu0 hA) (sub_nonneg.mpr hb.2)
  have h₃ := mul_nonneg (mul_nonneg (show 0 ≤ 2-3*u by linarith) hA) hB
  nlinarith

/-- Opposite root branches have zero intersection. Since their masses sum to
one and neither exceeds2/3, their vertex deficits pay the same edge charge. -/
lemma opposite_branch (u v a b A B : ℚ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : u+v = 1) (ha : 0 ≤ a ∧ a ≤ A) (hb : 0 ≤ b ∧ b ≤ B) :
    (2/3)*A*B ≤ 2*B*((2/3)*A-u*a) + 2*A*((2/3)*B-v*b) := by
  have hA : 0 ≤ A := ha.1.trans ha.2
  have hB : 0 ≤ B := hb.1.trans hb.2
  have h₁ := mul_nonneg (mul_nonneg hB hu) (sub_nonneg.mpr ha.2)
  have h₂ := mul_nonneg (mul_nonneg hA hv) (sub_nonneg.mpr hb.2)
  have he : (u+v)*A*B = A*B := by rw [huv,one_mul]
  nlinarith

def branchMass (t : ℚ) (r : Bool) : ℚ := if r then t else 1-t

/-- A uniform two-branch edge charge with no finite profile or cardinality
assumption. For vertex weights W_i=(2/3)*A_i, the charge is(3/2)*W_i*W_j,
and its endpoint costs are3*W_j and3*W_i. -/
theorem compensated_pair (t a b A B : ℚ) (ht : 1/3 ≤ t ∧ t ≤ 2/3)
    (r s : Bool) (ha : 0 ≤ a ∧ a ≤ A) (hb : 0 ≤ b ∧ b ≤ B) :
    (2/3)*A*B ≤ (if r = s then branchMass t r*a*b else 0) +
      2*B*((2/3)*A-branchMass t r*a) + 2*A*((2/3)*B-branchMass t s*b) := by
  cases r <;> cases s <;> simp only [branchMass,Bool.false_eq_true,if_false,if_true,Bool.true_eq_false,zero_add]
  · exact same_branch (1-t) a b A B (by linarith [ht.2]) (by linarith [ht.1]) ha hb
  · exact opposite_branch (1-t) t a b A B (by linarith [ht.2]) (by linarith [ht.1]) (by ring) ha hb
  · exact opposite_branch t (1-t) a b A B (by linarith [ht.1]) (by linarith [ht.2]) (by ring) ha hb
  · exact same_branch t a b A B (by linarith [ht.1]) ht.2 ha hb

#print axioms compensated_pair
end Erdos7BinaryRootOverlap
