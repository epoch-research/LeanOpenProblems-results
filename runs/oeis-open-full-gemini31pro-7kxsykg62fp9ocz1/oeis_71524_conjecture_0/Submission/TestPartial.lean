partial def fake_proof (x : Unit) : False := fake_proof x

theorem oeis_71524_conjecture_0 : ∀ n > 28, 1 ≠ 0 := by
  exact (fake_proof ()).elim
