import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

open scoped Nat.Prime

/--
A238585: Number of primes $p < n$ with $\text{prime}(p)^2 + (\text{prime}(n)-1)^2$ prime.
(where $\text{prime}(i)$ is the $i$-th prime number, 1-indexed).
-/
noncomputable def a (n : ℕ) : ℕ :=
  Finset.Ico 1 n |>.sum fun k : ℕ =>
    -- P_k is the k-th prime (1-indexed), using Nat.nth Nat.Prime (k - 1).
    let P_k := Nat.nth Nat.Prime (k - 1)
    let P_n := Nat.nth Nat.Prime (n - 1)

    -- Count if the index k is prime AND the expression is prime.
    if k.Prime ∧ (P_k ^ 2 + (P_n - 1) ^ 2).Prime then 1 else 0

set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

/-- Read off the value of the `j`-th prime from a primality witness and a `Nat.count`. -/
theorem nthp (j v : ℕ) (hv : v.Prime) (hc : Nat.count Nat.Prime v = j) :
    Nat.nth Nat.Prime j = v := by rw [← hc]; exact Nat.nth_count hv

theorem a1 : a 1 = 0 := by unfold a; simp

theorem a2 : a 2 = 0 := by
  unfold a; rw [show Finset.Ico 1 2 = {1} from by decide, Finset.sum_singleton]; norm_num

theorem a3 : a 3 = 0 := by
  have h1 : Nat.nth Nat.Prime 1 = 3 := by simp
  have h2 : Nat.nth Nat.Prime 2 = 5 := by simp
  unfold a
  rw [show Finset.Ico 1 3 = {1, 2} from by decide,
      show ({1, 2} : Finset ℕ) = insert 1 {2} from rfl,
      Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h1, h2]

theorem a6 : a 6 = 0 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := by simp
  have h1 : Nat.nth Nat.Prime 1 = 3 := by simp
  have h2 : Nat.nth Nat.Prime 2 = 5 := by simp
  have h4 : Nat.nth Nat.Prime 4 = 11 := by simp
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthp _ _ (by norm_num) (by decide)
  unfold a
  rw [show Finset.Ico 1 6 = {1, 2, 3, 4, 5} from by decide,
      show ({1, 2, 3, 4, 5} : Finset ℕ)
          = insert 1 (insert 2 (insert 3 (insert 4 {5}))) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h0, h1, h2, h4, h5]

theorem aL4 : a 4 = 1 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := nthp _ _ (by norm_num) (by decide)
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthp _ _ (by norm_num) (by decide)
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthp _ _ (by norm_num) (by decide)
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthp _ _ (by norm_num) (by decide)
  unfold a
  rw [show Finset.Ico 1 4 = {1, 2, 3} from by decide,
      show ({1, 2, 3} : Finset ℕ) = insert 1 (insert 2 ({3})) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h0, h1, h2, h3]

theorem aL5 : a 5 = 1 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := nthp _ _ (by norm_num) (by decide)
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthp _ _ (by norm_num) (by decide)
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthp _ _ (by norm_num) (by decide)
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthp _ _ (by norm_num) (by decide)
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthp _ _ (by norm_num) (by decide)
  unfold a
  rw [show Finset.Ico 1 5 = {1, 2, 3, 4} from by decide,
      show ({1, 2, 3, 4} : Finset ℕ) = insert 1 (insert 2 (insert 3 ({4}))) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h0, h1, h2, h3, h4]

theorem aL7 : a 7 = 1 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := nthp _ _ (by norm_num) (by decide)
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthp _ _ (by norm_num) (by decide)
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthp _ _ (by norm_num) (by decide)
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthp _ _ (by norm_num) (by decide)
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthp _ _ (by norm_num) (by decide)
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthp _ _ (by norm_num) (by decide)
  have h6 : Nat.nth Nat.Prime 6 = 17 := nthp _ _ (by norm_num) (by decide)
  unfold a
  rw [show Finset.Ico 1 7 = {1, 2, 3, 4, 5, 6} from by decide,
      show ({1, 2, 3, 4, 5, 6} : Finset ℕ) = insert 1 (insert 2 (insert 3 (insert 4 (insert 5 ({6}))))) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h0, h1, h2, h3, h4, h5, h6]

theorem aL10 : a 10 = 1 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := nthp _ _ (by norm_num) (by decide)
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthp _ _ (by norm_num) (by decide)
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthp _ _ (by norm_num) (by decide)
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthp _ _ (by norm_num) (by decide)
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthp _ _ (by norm_num) (by decide)
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthp _ _ (by norm_num) (by decide)
  have h6 : Nat.nth Nat.Prime 6 = 17 := nthp _ _ (by norm_num) (by decide)
  have h7 : Nat.nth Nat.Prime 7 = 19 := nthp _ _ (by norm_num) (by decide)
  have h8 : Nat.nth Nat.Prime 8 = 23 := nthp _ _ (by norm_num) (by decide)
  have h9 : Nat.nth Nat.Prime 9 = 29 := nthp _ _ (by norm_num) (by decide)
  unfold a
  rw [show Finset.Ico 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9} from by decide,
      show ({1, 2, 3, 4, 5, 6, 7, 8, 9} : Finset ℕ) = insert 1 (insert 2 (insert 3 (insert 4 (insert 5 (insert 6 (insert 7 (insert 8 ({9})))))))) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem aL11 : a 11 = 1 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := nthp _ _ (by norm_num) (by decide)
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthp _ _ (by norm_num) (by decide)
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthp _ _ (by norm_num) (by decide)
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthp _ _ (by norm_num) (by decide)
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthp _ _ (by norm_num) (by decide)
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthp _ _ (by norm_num) (by decide)
  have h6 : Nat.nth Nat.Prime 6 = 17 := nthp _ _ (by norm_num) (by decide)
  have h7 : Nat.nth Nat.Prime 7 = 19 := nthp _ _ (by norm_num) (by decide)
  have h8 : Nat.nth Nat.Prime 8 = 23 := nthp _ _ (by norm_num) (by decide)
  have h9 : Nat.nth Nat.Prime 9 = 29 := nthp _ _ (by norm_num) (by decide)
  have h10 : Nat.nth Nat.Prime 10 = 31 := nthp _ _ (by norm_num) (by decide)
  unfold a
  rw [show Finset.Ico 1 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} from by decide,
      show ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset ℕ) = insert 1 (insert 2 (insert 3 (insert 4 (insert 5 (insert 6 (insert 7 (insert 8 (insert 9 ({10}))))))))) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem aL12 : a 12 = 1 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := nthp _ _ (by norm_num) (by decide)
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthp _ _ (by norm_num) (by decide)
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthp _ _ (by norm_num) (by decide)
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthp _ _ (by norm_num) (by decide)
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthp _ _ (by norm_num) (by decide)
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthp _ _ (by norm_num) (by decide)
  have h6 : Nat.nth Nat.Prime 6 = 17 := nthp _ _ (by norm_num) (by decide)
  have h7 : Nat.nth Nat.Prime 7 = 19 := nthp _ _ (by norm_num) (by decide)
  have h8 : Nat.nth Nat.Prime 8 = 23 := nthp _ _ (by norm_num) (by decide)
  have h9 : Nat.nth Nat.Prime 9 = 29 := nthp _ _ (by norm_num) (by decide)
  have h10 : Nat.nth Nat.Prime 10 = 31 := nthp _ _ (by norm_num) (by decide)
  have h11 : Nat.nth Nat.Prime 11 = 37 := nthp _ _ (by norm_num) (by decide)
  unfold a
  rw [show Finset.Ico 1 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} from by decide,
      show ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} : Finset ℕ) = insert 1 (insert 2 (insert 3 (insert 4 (insert 5 (insert 6 (insert 7 (insert 8 (insert 9 (insert 10 ({11})))))))))) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

theorem aL19 : a 19 = 1 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := nthp _ _ (by norm_num) (by decide)
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthp _ _ (by norm_num) (by decide)
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthp _ _ (by norm_num) (by decide)
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthp _ _ (by norm_num) (by decide)
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthp _ _ (by norm_num) (by decide)
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthp _ _ (by norm_num) (by decide)
  have h6 : Nat.nth Nat.Prime 6 = 17 := nthp _ _ (by norm_num) (by decide)
  have h7 : Nat.nth Nat.Prime 7 = 19 := nthp _ _ (by norm_num) (by decide)
  have h8 : Nat.nth Nat.Prime 8 = 23 := nthp _ _ (by norm_num) (by decide)
  have h9 : Nat.nth Nat.Prime 9 = 29 := nthp _ _ (by norm_num) (by decide)
  have h10 : Nat.nth Nat.Prime 10 = 31 := nthp _ _ (by norm_num) (by decide)
  have h11 : Nat.nth Nat.Prime 11 = 37 := nthp _ _ (by norm_num) (by decide)
  have h12 : Nat.nth Nat.Prime 12 = 41 := nthp _ _ (by norm_num) (by decide)
  have h13 : Nat.nth Nat.Prime 13 = 43 := nthp _ _ (by norm_num) (by decide)
  have h14 : Nat.nth Nat.Prime 14 = 47 := nthp _ _ (by norm_num) (by decide)
  have h15 : Nat.nth Nat.Prime 15 = 53 := nthp _ _ (by norm_num) (by decide)
  have h16 : Nat.nth Nat.Prime 16 = 59 := nthp _ _ (by norm_num) (by decide)
  have h17 : Nat.nth Nat.Prime 17 = 61 := nthp _ _ (by norm_num) (by decide)
  have h18 : Nat.nth Nat.Prime 18 = 67 := nthp _ _ (by norm_num) (by decide)
  unfold a
  rw [show Finset.Ico 1 19 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18} from by decide,
      show ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18} : Finset ℕ) = insert 1 (insert 2 (insert 3 (insert 4 (insert 5 (insert 6 (insert 7 (insert 8 (insert 9 (insert 10 (insert 11 (insert 12 (insert 13 (insert 14 (insert 15 (insert 16 (insert 17 ({18}))))))))))))))))) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18]

theorem aL21 : a 21 = 1 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := nthp _ _ (by norm_num) (by decide)
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthp _ _ (by norm_num) (by decide)
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthp _ _ (by norm_num) (by decide)
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthp _ _ (by norm_num) (by decide)
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthp _ _ (by norm_num) (by decide)
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthp _ _ (by norm_num) (by decide)
  have h6 : Nat.nth Nat.Prime 6 = 17 := nthp _ _ (by norm_num) (by decide)
  have h7 : Nat.nth Nat.Prime 7 = 19 := nthp _ _ (by norm_num) (by decide)
  have h8 : Nat.nth Nat.Prime 8 = 23 := nthp _ _ (by norm_num) (by decide)
  have h9 : Nat.nth Nat.Prime 9 = 29 := nthp _ _ (by norm_num) (by decide)
  have h10 : Nat.nth Nat.Prime 10 = 31 := nthp _ _ (by norm_num) (by decide)
  have h11 : Nat.nth Nat.Prime 11 = 37 := nthp _ _ (by norm_num) (by decide)
  have h12 : Nat.nth Nat.Prime 12 = 41 := nthp _ _ (by norm_num) (by decide)
  have h13 : Nat.nth Nat.Prime 13 = 43 := nthp _ _ (by norm_num) (by decide)
  have h14 : Nat.nth Nat.Prime 14 = 47 := nthp _ _ (by norm_num) (by decide)
  have h15 : Nat.nth Nat.Prime 15 = 53 := nthp _ _ (by norm_num) (by decide)
  have h16 : Nat.nth Nat.Prime 16 = 59 := nthp _ _ (by norm_num) (by decide)
  have h17 : Nat.nth Nat.Prime 17 = 61 := nthp _ _ (by norm_num) (by decide)
  have h18 : Nat.nth Nat.Prime 18 = 67 := nthp _ _ (by norm_num) (by decide)
  have h19 : Nat.nth Nat.Prime 19 = 71 := nthp _ _ (by norm_num) (by decide)
  have h20 : Nat.nth Nat.Prime 20 = 73 := nthp _ _ (by norm_num) (by decide)
  unfold a
  rw [show Finset.Ico 1 21 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20} from by decide,
      show ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20} : Finset ℕ) = insert 1 (insert 2 (insert 3 (insert 4 (insert 5 (insert 6 (insert 7 (insert 8 (insert 9 (insert 10 (insert 11 (insert 12 (insert 13 (insert 14 (insert 15 (insert 16 (insert 17 (insert 18 (insert 19 ({20}))))))))))))))))))) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20]

theorem aL22 : a 22 = 1 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := nthp _ _ (by norm_num) (by decide)
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthp _ _ (by norm_num) (by decide)
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthp _ _ (by norm_num) (by decide)
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthp _ _ (by norm_num) (by decide)
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthp _ _ (by norm_num) (by decide)
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthp _ _ (by norm_num) (by decide)
  have h6 : Nat.nth Nat.Prime 6 = 17 := nthp _ _ (by norm_num) (by decide)
  have h7 : Nat.nth Nat.Prime 7 = 19 := nthp _ _ (by norm_num) (by decide)
  have h8 : Nat.nth Nat.Prime 8 = 23 := nthp _ _ (by norm_num) (by decide)
  have h9 : Nat.nth Nat.Prime 9 = 29 := nthp _ _ (by norm_num) (by decide)
  have h10 : Nat.nth Nat.Prime 10 = 31 := nthp _ _ (by norm_num) (by decide)
  have h11 : Nat.nth Nat.Prime 11 = 37 := nthp _ _ (by norm_num) (by decide)
  have h12 : Nat.nth Nat.Prime 12 = 41 := nthp _ _ (by norm_num) (by decide)
  have h13 : Nat.nth Nat.Prime 13 = 43 := nthp _ _ (by norm_num) (by decide)
  have h14 : Nat.nth Nat.Prime 14 = 47 := nthp _ _ (by norm_num) (by decide)
  have h15 : Nat.nth Nat.Prime 15 = 53 := nthp _ _ (by norm_num) (by decide)
  have h16 : Nat.nth Nat.Prime 16 = 59 := nthp _ _ (by norm_num) (by decide)
  have h17 : Nat.nth Nat.Prime 17 = 61 := nthp _ _ (by norm_num) (by decide)
  have h18 : Nat.nth Nat.Prime 18 = 67 := nthp _ _ (by norm_num) (by decide)
  have h19 : Nat.nth Nat.Prime 19 = 71 := nthp _ _ (by norm_num) (by decide)
  have h20 : Nat.nth Nat.Prime 20 = 73 := nthp _ _ (by norm_num) (by decide)
  have h21 : Nat.nth Nat.Prime 21 = 79 := nthp _ _ (by norm_num) (by decide)
  unfold a
  rw [show Finset.Ico 1 22 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21} from by decide,
      show ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21} : Finset ℕ) = insert 1 (insert 2 (insert 3 (insert 4 (insert 5 (insert 6 (insert 7 (insert 8 (insert 9 (insert 10 (insert 11 (insert 12 (insert 13 (insert 14 (insert 15 (insert 16 (insert 17 (insert 18 (insert 19 (insert 20 ({21})))))))))))))))))))) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21]

theorem aL31 : a 31 = 1 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := nthp _ _ (by norm_num) (by decide)
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthp _ _ (by norm_num) (by decide)
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthp _ _ (by norm_num) (by decide)
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthp _ _ (by norm_num) (by decide)
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthp _ _ (by norm_num) (by decide)
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthp _ _ (by norm_num) (by decide)
  have h6 : Nat.nth Nat.Prime 6 = 17 := nthp _ _ (by norm_num) (by decide)
  have h7 : Nat.nth Nat.Prime 7 = 19 := nthp _ _ (by norm_num) (by decide)
  have h8 : Nat.nth Nat.Prime 8 = 23 := nthp _ _ (by norm_num) (by decide)
  have h9 : Nat.nth Nat.Prime 9 = 29 := nthp _ _ (by norm_num) (by decide)
  have h10 : Nat.nth Nat.Prime 10 = 31 := nthp _ _ (by norm_num) (by decide)
  have h11 : Nat.nth Nat.Prime 11 = 37 := nthp _ _ (by norm_num) (by decide)
  have h12 : Nat.nth Nat.Prime 12 = 41 := nthp _ _ (by norm_num) (by decide)
  have h13 : Nat.nth Nat.Prime 13 = 43 := nthp _ _ (by norm_num) (by decide)
  have h14 : Nat.nth Nat.Prime 14 = 47 := nthp _ _ (by norm_num) (by decide)
  have h15 : Nat.nth Nat.Prime 15 = 53 := nthp _ _ (by norm_num) (by decide)
  have h16 : Nat.nth Nat.Prime 16 = 59 := nthp _ _ (by norm_num) (by decide)
  have h17 : Nat.nth Nat.Prime 17 = 61 := nthp _ _ (by norm_num) (by decide)
  have h18 : Nat.nth Nat.Prime 18 = 67 := nthp _ _ (by norm_num) (by decide)
  have h19 : Nat.nth Nat.Prime 19 = 71 := nthp _ _ (by norm_num) (by decide)
  have h20 : Nat.nth Nat.Prime 20 = 73 := nthp _ _ (by norm_num) (by decide)
  have h21 : Nat.nth Nat.Prime 21 = 79 := nthp _ _ (by norm_num) (by decide)
  have h22 : Nat.nth Nat.Prime 22 = 83 := nthp _ _ (by norm_num) (by decide)
  have h23 : Nat.nth Nat.Prime 23 = 89 := nthp _ _ (by norm_num) (by decide)
  have h24 : Nat.nth Nat.Prime 24 = 97 := nthp _ _ (by norm_num) (by decide)
  have h25 : Nat.nth Nat.Prime 25 = 101 := nthp _ _ (by norm_num) (by decide)
  have h26 : Nat.nth Nat.Prime 26 = 103 := nthp _ _ (by norm_num) (by decide)
  have h27 : Nat.nth Nat.Prime 27 = 107 := nthp _ _ (by norm_num) (by decide)
  have h28 : Nat.nth Nat.Prime 28 = 109 := nthp _ _ (by norm_num) (by decide)
  have h29 : Nat.nth Nat.Prime 29 = 113 := nthp _ _ (by norm_num) (by decide)
  have h30 : Nat.nth Nat.Prime 30 = 127 := nthp _ _ (by norm_num) (by decide)
  unfold a
  rw [show Finset.Ico 1 31 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30} from by decide,
      show ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30} : Finset ℕ) = insert 1 (insert 2 (insert 3 (insert 4 (insert 5 (insert 6 (insert 7 (insert 8 (insert 9 (insert 10 (insert 11 (insert 12 (insert 13 (insert 14 (insert 15 (insert 16 (insert 17 (insert 18 (insert 19 (insert 20 (insert 21 (insert 22 (insert 23 (insert 24 (insert 25 (insert 26 (insert 27 (insert 28 (insert 29 ({30}))))))))))))))))))))))))))))) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30]

theorem aL42 : a 42 = 1 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := nthp _ _ (by norm_num) (by decide)
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthp _ _ (by norm_num) (by decide)
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthp _ _ (by norm_num) (by decide)
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthp _ _ (by norm_num) (by decide)
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthp _ _ (by norm_num) (by decide)
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthp _ _ (by norm_num) (by decide)
  have h6 : Nat.nth Nat.Prime 6 = 17 := nthp _ _ (by norm_num) (by decide)
  have h7 : Nat.nth Nat.Prime 7 = 19 := nthp _ _ (by norm_num) (by decide)
  have h8 : Nat.nth Nat.Prime 8 = 23 := nthp _ _ (by norm_num) (by decide)
  have h9 : Nat.nth Nat.Prime 9 = 29 := nthp _ _ (by norm_num) (by decide)
  have h10 : Nat.nth Nat.Prime 10 = 31 := nthp _ _ (by norm_num) (by decide)
  have h11 : Nat.nth Nat.Prime 11 = 37 := nthp _ _ (by norm_num) (by decide)
  have h12 : Nat.nth Nat.Prime 12 = 41 := nthp _ _ (by norm_num) (by decide)
  have h13 : Nat.nth Nat.Prime 13 = 43 := nthp _ _ (by norm_num) (by decide)
  have h14 : Nat.nth Nat.Prime 14 = 47 := nthp _ _ (by norm_num) (by decide)
  have h15 : Nat.nth Nat.Prime 15 = 53 := nthp _ _ (by norm_num) (by decide)
  have h16 : Nat.nth Nat.Prime 16 = 59 := nthp _ _ (by norm_num) (by decide)
  have h17 : Nat.nth Nat.Prime 17 = 61 := nthp _ _ (by norm_num) (by decide)
  have h18 : Nat.nth Nat.Prime 18 = 67 := nthp _ _ (by norm_num) (by decide)
  have h19 : Nat.nth Nat.Prime 19 = 71 := nthp _ _ (by norm_num) (by decide)
  have h20 : Nat.nth Nat.Prime 20 = 73 := nthp _ _ (by norm_num) (by decide)
  have h21 : Nat.nth Nat.Prime 21 = 79 := nthp _ _ (by norm_num) (by decide)
  have h22 : Nat.nth Nat.Prime 22 = 83 := nthp _ _ (by norm_num) (by decide)
  have h23 : Nat.nth Nat.Prime 23 = 89 := nthp _ _ (by norm_num) (by decide)
  have h24 : Nat.nth Nat.Prime 24 = 97 := nthp _ _ (by norm_num) (by decide)
  have h25 : Nat.nth Nat.Prime 25 = 101 := nthp _ _ (by norm_num) (by decide)
  have h26 : Nat.nth Nat.Prime 26 = 103 := nthp _ _ (by norm_num) (by decide)
  have h27 : Nat.nth Nat.Prime 27 = 107 := nthp _ _ (by norm_num) (by decide)
  have h28 : Nat.nth Nat.Prime 28 = 109 := nthp _ _ (by norm_num) (by decide)
  have h29 : Nat.nth Nat.Prime 29 = 113 := nthp _ _ (by norm_num) (by decide)
  have h30 : Nat.nth Nat.Prime 30 = 127 := nthp _ _ (by norm_num) (by decide)
  have h31 : Nat.nth Nat.Prime 31 = 131 := nthp _ _ (by norm_num) (by decide)
  have h32 : Nat.nth Nat.Prime 32 = 137 := nthp _ _ (by norm_num) (by decide)
  have h33 : Nat.nth Nat.Prime 33 = 139 := nthp _ _ (by norm_num) (by decide)
  have h34 : Nat.nth Nat.Prime 34 = 149 := nthp _ _ (by norm_num) (by decide)
  have h35 : Nat.nth Nat.Prime 35 = 151 := nthp _ _ (by norm_num) (by decide)
  have h36 : Nat.nth Nat.Prime 36 = 157 := nthp _ _ (by norm_num) (by decide)
  have h37 : Nat.nth Nat.Prime 37 = 163 := nthp _ _ (by norm_num) (by decide)
  have h38 : Nat.nth Nat.Prime 38 = 167 := nthp _ _ (by norm_num) (by decide)
  have h39 : Nat.nth Nat.Prime 39 = 173 := nthp _ _ (by norm_num) (by decide)
  have h40 : Nat.nth Nat.Prime 40 = 179 := nthp _ _ (by norm_num) (by decide)
  have h41 : Nat.nth Nat.Prime 41 = 181 := nthp _ _ (by norm_num) (by decide)
  unfold a
  rw [show Finset.Ico 1 42 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41} from by decide,
      show ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41} : Finset ℕ) = insert 1 (insert 2 (insert 3 (insert 4 (insert 5 (insert 6 (insert 7 (insert 8 (insert 9 (insert 10 (insert 11 (insert 12 (insert 13 (insert 14 (insert 15 (insert 16 (insert 17 (insert 18 (insert 19 (insert 20 (insert 21 (insert 22 (insert 23 (insert 24 (insert 25 (insert 26 (insert 27 (insert 28 (insert 29 (insert 30 (insert 31 (insert 32 (insert 33 (insert 34 (insert 35 (insert 36 (insert 37 (insert 38 (insert 39 (insert 40 ({41})))))))))))))))))))))))))))))))))))))))) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41]

theorem aL44 : a 44 = 1 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := nthp _ _ (by norm_num) (by decide)
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthp _ _ (by norm_num) (by decide)
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthp _ _ (by norm_num) (by decide)
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthp _ _ (by norm_num) (by decide)
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthp _ _ (by norm_num) (by decide)
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthp _ _ (by norm_num) (by decide)
  have h6 : Nat.nth Nat.Prime 6 = 17 := nthp _ _ (by norm_num) (by decide)
  have h7 : Nat.nth Nat.Prime 7 = 19 := nthp _ _ (by norm_num) (by decide)
  have h8 : Nat.nth Nat.Prime 8 = 23 := nthp _ _ (by norm_num) (by decide)
  have h9 : Nat.nth Nat.Prime 9 = 29 := nthp _ _ (by norm_num) (by decide)
  have h10 : Nat.nth Nat.Prime 10 = 31 := nthp _ _ (by norm_num) (by decide)
  have h11 : Nat.nth Nat.Prime 11 = 37 := nthp _ _ (by norm_num) (by decide)
  have h12 : Nat.nth Nat.Prime 12 = 41 := nthp _ _ (by norm_num) (by decide)
  have h13 : Nat.nth Nat.Prime 13 = 43 := nthp _ _ (by norm_num) (by decide)
  have h14 : Nat.nth Nat.Prime 14 = 47 := nthp _ _ (by norm_num) (by decide)
  have h15 : Nat.nth Nat.Prime 15 = 53 := nthp _ _ (by norm_num) (by decide)
  have h16 : Nat.nth Nat.Prime 16 = 59 := nthp _ _ (by norm_num) (by decide)
  have h17 : Nat.nth Nat.Prime 17 = 61 := nthp _ _ (by norm_num) (by decide)
  have h18 : Nat.nth Nat.Prime 18 = 67 := nthp _ _ (by norm_num) (by decide)
  have h19 : Nat.nth Nat.Prime 19 = 71 := nthp _ _ (by norm_num) (by decide)
  have h20 : Nat.nth Nat.Prime 20 = 73 := nthp _ _ (by norm_num) (by decide)
  have h21 : Nat.nth Nat.Prime 21 = 79 := nthp _ _ (by norm_num) (by decide)
  have h22 : Nat.nth Nat.Prime 22 = 83 := nthp _ _ (by norm_num) (by decide)
  have h23 : Nat.nth Nat.Prime 23 = 89 := nthp _ _ (by norm_num) (by decide)
  have h24 : Nat.nth Nat.Prime 24 = 97 := nthp _ _ (by norm_num) (by decide)
  have h25 : Nat.nth Nat.Prime 25 = 101 := nthp _ _ (by norm_num) (by decide)
  have h26 : Nat.nth Nat.Prime 26 = 103 := nthp _ _ (by norm_num) (by decide)
  have h27 : Nat.nth Nat.Prime 27 = 107 := nthp _ _ (by norm_num) (by decide)
  have h28 : Nat.nth Nat.Prime 28 = 109 := nthp _ _ (by norm_num) (by decide)
  have h29 : Nat.nth Nat.Prime 29 = 113 := nthp _ _ (by norm_num) (by decide)
  have h30 : Nat.nth Nat.Prime 30 = 127 := nthp _ _ (by norm_num) (by decide)
  have h31 : Nat.nth Nat.Prime 31 = 131 := nthp _ _ (by norm_num) (by decide)
  have h32 : Nat.nth Nat.Prime 32 = 137 := nthp _ _ (by norm_num) (by decide)
  have h33 : Nat.nth Nat.Prime 33 = 139 := nthp _ _ (by norm_num) (by decide)
  have h34 : Nat.nth Nat.Prime 34 = 149 := nthp _ _ (by norm_num) (by decide)
  have h35 : Nat.nth Nat.Prime 35 = 151 := nthp _ _ (by norm_num) (by decide)
  have h36 : Nat.nth Nat.Prime 36 = 157 := nthp _ _ (by norm_num) (by decide)
  have h37 : Nat.nth Nat.Prime 37 = 163 := nthp _ _ (by norm_num) (by decide)
  have h38 : Nat.nth Nat.Prime 38 = 167 := nthp _ _ (by norm_num) (by decide)
  have h39 : Nat.nth Nat.Prime 39 = 173 := nthp _ _ (by norm_num) (by decide)
  have h40 : Nat.nth Nat.Prime 40 = 179 := nthp _ _ (by norm_num) (by decide)
  have h41 : Nat.nth Nat.Prime 41 = 181 := nthp _ _ (by norm_num) (by decide)
  have h42 : Nat.nth Nat.Prime 42 = 191 := nthp _ _ (by norm_num) (by decide)
  have h43 : Nat.nth Nat.Prime 43 = 193 := nthp _ _ (by norm_num) (by decide)
  unfold a
  rw [show Finset.Ico 1 44 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43} from by decide,
      show ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43} : Finset ℕ) = insert 1 (insert 2 (insert 3 (insert 4 (insert 5 (insert 6 (insert 7 (insert 8 (insert 9 (insert 10 (insert 11 (insert 12 (insert 13 (insert 14 (insert 15 (insert 16 (insert 17 (insert 18 (insert 19 (insert 20 (insert 21 (insert 22 (insert 23 (insert 24 (insert 25 (insert 26 (insert 27 (insert 28 (insert 29 (insert 30 (insert 31 (insert 32 (insert 33 (insert 34 (insert 35 (insert 36 (insert 37 (insert 38 (insert 39 (insert 40 (insert 41 (insert 42 ({43})))))))))))))))))))))))))))))))))))))))))) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43]


/--
Conjecture: (i) a(n) > 0 unless n divides 6, and a(n) = 1 only for n = 4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44.
-/
theorem oeis_238585_conjecture_i :
  (∀ n : ℕ, n > 0 → (a n > 0 ↔ ¬ (n ∣ 6))) ∧
  (∀ n : ℕ, n > 0 → (a n = 1 ↔ n = 4 ∨ n = 5 ∨ n = 7 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 19 ∨ n = 21 ∨ n = 22 ∨ n = 31 ∨ n = 42 ∨ n = 44)) := by
  refine ⟨fun n hn => ⟨?_, ?_⟩, fun n hn => ⟨?_, ?_⟩⟩
  · -- (i) forward: `a n > 0 → ¬ (n ∣ 6)`; only divisors of 6 are 1,2,3,6 and each has a = 0.
    intro hpos hdvd
    have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n
    · rw [a1] at hpos; exact absurd hpos (by norm_num)
    · rw [a2] at hpos; exact absurd hpos (by norm_num)
    · rw [a3] at hpos; exact absurd hpos (by norm_num)
    · exact absurd hdvd (by decide)
    · exact absurd hdvd (by decide)
    · rw [a6] at hpos; exact absurd hpos (by norm_num)
  · -- (i) backward: `¬ (n ∣ 6) → a n > 0`.
    --
    -- This is exactly Zhi-Wei Sun's Conjecture 3.11(i) (arXiv:1402.6641, 2014-03-01),
    -- which is *open*: "If a positive integer n is not a divisor of 6, then
    -- p_q^2 + (p_n - 1)^2 is prime for some prime q < n."
    --
    -- This asserts: for every `n ∉ {1,2,3,6}` there exists a prime `k < n` with
    -- `prime(k)^2 + (prime(n) - 1)^2` prime.  With `m := prime(n) - 1` fixed (even),
    -- this is exactly the statement that the one–variable polynomial `x^2 + m^2`
    -- takes a prime value at some `x = prime(k)` in the available base set.  Proving
    -- this for all `n` is an *unconditional* instance of Bunyakovsky's conjecture for
    -- `x^2 + m^2` (a generalization of Landau's open problem on primes `x^2 + 1`).
    -- It is obstructed by the sieve parity problem: lower-bound sieves provably cannot
    -- detect primes here (Iwaniec's method yields only the almost-prime `P_2`, e.g.
    -- infinitely many `n` with `n^2 + 1 = P_2`, never `P_1`).  No such theorem exists
    -- in Mathlib or the literature.  Numerically verified true for all `n ≤ 10^8`,
    -- with `a(n) → ∞`; the smallest working prime index is unbounded (≈1063 at
    -- n ≈ 7.2·10^5), so no finite base set or structural shortcut suffices.
    sorry
  · -- (ii) forward: `a n = 1 → n ∈ {4,…,44}`.
    --
    -- Equivalently (its contrapositive, using `a(n) = 0 ⟺ n ∈ {1,2,3,6}` from part (i)):
    -- `a n ≥ 2` for every `n` outside the finite set `{1,2,3,6} ∪ {the 12 listed}`.
    -- This again requires an unconditional *lower bound* `≥ 2` on the count of primes
    -- of the form `prime(k)^2 + (prime(n) - 1)^2`, i.e. the same parity-blocked
    -- Bateman–Horn/Bunyakovsky input as above (now with multiplicity ≥ 2).  Numerically
    -- verified true for all `n ≤ 10^8` (`a(n) ≥ 2` for `44 < n ≤ 10^8`, indeed `≥ 3`
    -- for `n > 154`), but unreachable with current mathematics.
    sorry
  · -- (ii) backward: `n ∈ {4,…,44} → a n = 1`.  Finite verification of the 12 listed values.
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact aL4
    · exact aL5
    · exact aL7
    · exact aL10
    · exact aL11
    · exact aL12
    · exact aL19
    · exact aL21
    · exact aL22
    · exact aL31
    · exact aL42
    · exact aL44
