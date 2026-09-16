import Submission.Spec

noncomputable def t0 : ℝ := t 0
noncomputable def t1 : ℝ := t 1

-- We can't eval Reals, but we can check if it reduces to something simple
-- Let's try to write a lemma to compute t 0

lemma t0_val : t 0 = 367 := by
  unfold t
  -- we can try to simplify
  sorry

