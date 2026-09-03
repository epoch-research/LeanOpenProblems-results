import Submission.TrianglePacking

/-! A small multiplier test for exact triangle compatibility. It avoids a search
over every pair of interval positions and supports kernel-checked large-interval
packing cuts. -/
namespace Erdos970.PatternPacking

/-- `u` and `v` are necessarily positive multiples of their common products. -/
def AdmitsMultiplierTriangle (m : ℕ) (A B C : Finset ℕ) : Prop :=
  ∃ a : Fin (m / commonProduct A B + 1), ∃ b : Fin (m / commonProduct B C + 1),
    0 < a.val ∧ 0 < b.val ∧
    commonProduct A B * a.val + commonProduct B C * b.val < m ∧
    commonProduct A C ∣ commonProduct A B * a.val + commonProduct B C * b.val

instance (m : ℕ) (A B C : Finset ℕ) : Decidable (AdmitsMultiplierTriangle m A B C) := by
  unfold AdmitsMultiplierTriangle
  infer_instance

/-- This is an exact test, not a sufficient heuristic. -/
theorem admitsTriangle_iff_multipliers (m : ℕ) (A B C : Finset ℕ)
    (hab : 0 < commonProduct A B) (hbc : 0 < commonProduct B C) :
    AdmitsTriangle m A B C ↔ AdmitsMultiplierTriangle m A B C := by
  constructor
  · rintro ⟨u, v, hu, hv, huv, hdu, hdv, hsum⟩
    obtain ⟨a, ha⟩ := hdu
    obtain ⟨b, hb⟩ := hdv
    have ha0 : 0 < a := by nlinarith
    have hb0 : 0 < b := by nlinarith
    have haM : a ≤ m / commonProduct A B := by
      apply (Nat.le_div_iff_mul_le hab).mpr
      nlinarith [u.isLt]
    have hbM : b ≤ m / commonProduct B C := by
      apply (Nat.le_div_iff_mul_le hbc).mpr
      nlinarith [v.isLt]
    refine ⟨⟨a, by omega⟩, ⟨b, by omega⟩, ha0, hb0, ?_, ?_⟩
    · simpa only [← ha, ← hb] using huv
    · simpa only [← ha, ← hb] using hsum
  · rintro ⟨a, b, ha, hb, hsum, hd⟩
    have hu : 0 < commonProduct A B * a.val := Nat.mul_pos hab ha
    have hv : 0 < commonProduct B C * b.val := Nat.mul_pos hbc hb
    refine ⟨⟨commonProduct A B * a.val, by omega⟩,
      ⟨commonProduct B C * b.val, by omega⟩, hu, hv, hsum, ?_, ?_, hd⟩
    · exact dvd_mul_right _ _
    · exact dvd_mul_right _ _

/-- Prime common products are positive, even for an empty intersection. -/
lemma commonProduct_pos (A B : Finset ℕ) (hprime : ∀ p ∈ A, p.Prime) :
    0 < commonProduct A B := by
  exact Finset.prod_pos (fun p hp => (hprime p (Finset.mem_inter.mp hp).1).pos)

/-- The finite multiplier checks imply the universal positional budget. -/
theorem patternCount_le_two_of_multiplier_checks (m : ℕ) (F : Finset (Finset ℕ))
    (hprime : ∀ A ∈ F, ∀ p ∈ A, p.Prime)
    (hcheck : ∀ A ∈ F, ∀ B ∈ F, ∀ C ∈ F, ¬AdmitsMultiplierTriangle m A B C)
    (r : ℕ → ℕ) : patternCount m F r ≤ 2 := by
  apply patternCount_le_two_of_noTriangle m F hprime
  intro A hA B hB C hC htri
  exact hcheck A hA B hB C hC
    ((admitsTriangle_iff_multipliers m A B C
      (commonProduct_pos A B (hprime A hA))
      (commonProduct_pos B C (hprime B hB))).mp htri)

#print axioms admitsTriangle_iff_multipliers
#print axioms patternCount_le_two_of_multiplier_checks
end Erdos970.PatternPacking
