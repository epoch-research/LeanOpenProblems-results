import Submission.Spec

theorem disproof_test : ¬ (type_of% @oeis_a189286_conjecture_0) := by
  -- Can we prove this?
  -- F(x) = floor(6x) - floor(3x) - floor(2x) - floor(x).
  -- v_D(x) = floor(3x) - floor(2x) - floor(x).
  -- For x = 0 and y = 0.667, F(0) + F(0.667) = 0 + 1 = 1.
  -- D(0.667) = floor(2) - floor(0.667) - floor(1.334) = 2 - 0 - 1 = 1.
  -- So F(x)+F(y) = D(x+y) = 1.
  -- But we need F(x)+F(y) >= D(x+y) + v_p(2n-1).
  -- So we need v_p(2n-1) = 0.
  -- Can we have v_p(2n-1) >= 1 while F(x)+F(y) = D(x+y)?
  -- If x+y = 2/3 + epsilon, then 2(x+y) = 4/3 + 2epsilon.
  -- This does not make 2(x+y) an integer.
  -- So v_p(2n-1) has no contribution from this digit!
  sorry
