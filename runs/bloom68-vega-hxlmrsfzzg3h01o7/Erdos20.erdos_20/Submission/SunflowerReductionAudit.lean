import Submission.SunflowerReduction

/-!
# Compilation and axiom audit for the auxiliary Erdős 20 reductions

This file imports only `Submission.SunflowerReduction`. The two audit theorems
restate the main outputs with their definitions expanded, to check the actual
quantifiers, cardinality bounds, positivity, and hereditary freeness.

Rebuild from `/workspace/leanproject` with:

```
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Submission/SunflowerFoundation.olean Submission/SunflowerFoundation.lean
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Submission/SunflowerReduction.olean Submission/SunflowerReduction.lean
lake env lean -DwarningAsError=true -o .lake/build/lib/lean/Submission/SunflowerReductionAudit.olean Submission/SunflowerReductionAudit.lean
```

The `#print axioms` commands below audit the reductions and their main supporting
lemmas. Neither this audit nor the reductions assert the exponential conjecture.
-/

set_option autoImplicit false

namespace SunflowerReductionAudit

open SunflowerFoundation SunflowerReduction

/-- The exact target and pure finite-family bound, with both reduction definitions
expanded. In particular there is no restriction on `k` or on the natural base. -/
theorem literal_target_equivalence :
    (∃ c : ℕ → ℕ, ∀ n k : ℕ, 0 < n → SunflowerFoundation.f n k < (c k) ^ n) ↔
      ∀ k : ℕ, ∃ C : ℕ, ∀ n : ℕ, 0 < n → ∀ {α : Type} (F : Finset (Set α)),
        (∀ A ∈ F, A.ncard = n) → (∀ A ∈ F, A.Finite) →
        ¬ HasSunflower F k → F.card ≤ C ^ n :=
  originalTarget_iff_uniformFreeBound

/-- The maximal-link output with the absolute profile expanded and the residual
rank explicitly positive. This uses the same arbitrary-kernel sunflower predicate
as the original problem, and makes no positivity assumption on `r`. -/
theorem literal_maximal_link_reduction {α : Type*} (F : Finset (Set α)) (n k r : ℕ)
    (hfinite : ∀ A ∈ F, A.Finite) (huniform : ∀ A ∈ F, A.ncard = n)
    (hfree : ¬ HasSunflower F k) (hlarge : r ^ n < F.card) :
    ∃ T : Finset α, 0 < n - T.card ∧
      (∀ A ∈ link F T, A.Finite) ∧
      (∀ A ∈ link F T, A.ncard = n - T.card) ∧
      ¬ HasSunflower (link F T) k ∧
      r ^ (n - T.card) < (link F T).card ∧
      ∀ U : Finset α, U.Nonempty → codegree (link F T) U ≤ r ^ ((n - T.card) - U.card) := by
  obtain ⟨T, hT, hfin, hunif, hfree', hprofile⟩ :=
    exists_free_absolute_profile_link F n k r hfinite huniform hfree hlarge
  exact ⟨T, by omega, hfin, hunif, hfree', hprofile.1, hprofile.2⟩

-- Boundary checks for the base-enlargement step.
example (C : ℕ) : C ^ 1 + 1 < (C + 2) ^ 1 :=
  pow_add_one_lt_add_two_pow C 1 (by decide)

example (n : ℕ) (hn : 0 < n) : (0 : ℕ) ^ n + 1 < (0 + 2) ^ n :=
  pow_add_one_lt_add_two_pow 0 n hn

end SunflowerReductionAudit

#print SunflowerReduction.OriginalTarget
#print SunflowerReduction.UniformFreeBound
#print SunflowerReduction.AbsoluteProfile
#print SunflowerReduction.AbsoluteProfileSunflower
#check SunflowerReduction.originalTarget_iff_uniformFreeBound
#check SunflowerReduction.exists_maximal_large_link
#check SunflowerReduction.exists_free_absolute_profile_link
#check SunflowerReduction.originalTarget_iff_absoluteProfileSunflower

#print axioms SunflowerFoundation.f_is_threshold
#print axioms SunflowerFoundation.threshold_iff_f_le
#print axioms SunflowerReduction.hasSunflower_iff_exists_set
#print axioms SunflowerReduction.threshold_succ_iff_card_le
#print axioms SunflowerReduction.uniformFreeBound_iff_f_le
#print axioms SunflowerReduction.pow_add_one_lt_add_two_pow
#print axioms SunflowerReduction.UniformFreeBound.f_lt
#print axioms SunflowerReduction.originalTarget_iff_uniformFreeBound
#print axioms SunflowerReduction.diff_injOn_of_subset
#print axioms SunflowerReduction.card_link
#print axioms SunflowerReduction.isSunflower_image_union
#print axioms SunflowerReduction.hasSunflower_of_link
#print axioms SunflowerReduction.not_hasSunflower_link
#print axioms SunflowerReduction.link_finite
#print axioms SunflowerReduction.link_uniform
#print axioms SunflowerReduction.disjoint_of_mem_link
#print axioms SunflowerReduction.codegree_pos
#print axioms SunflowerReduction.disjoint_of_codegree_link_pos
#print axioms SunflowerReduction.codegree_link_of_disjoint
#print axioms SunflowerReduction.exists_maximal_large_link
#print axioms SunflowerReduction.absoluteProfile_of_maximal_large_link
#print axioms SunflowerReduction.rank_pos_of_card_gt_pow
#print axioms SunflowerReduction.exists_absolute_profile_link
#print axioms SunflowerReduction.exists_free_absolute_profile_link
#print axioms SunflowerReduction.uniformFreeBound_iff_absoluteProfileSunflower
#print axioms SunflowerReduction.originalTarget_iff_absoluteProfileSunflower
#print axioms SunflowerReductionAudit.literal_target_equivalence
#print axioms SunflowerReductionAudit.literal_maximal_link_reduction
