import FormalConjectures.Util.ProblemImports

def powModF : ℕ → ℕ → ℕ → ℕ → ℕ
  | _, _, _, 0 => 1
  | a, e, n, (f+1) =>
      if e = 0 then 1
      else
        let h := powModF (a*a % n) (e/2) n f
        if e % 2 = 1 then (a % n) * h % n else h

theorem powModF_correct (n : ℕ) (hn : 2 ≤ n) :
    ∀ f a e, e < 2 ^ f → powModF a e n f = a ^ e % n := by
  intro f
  induction f with
  | zero =>
    intro a e he
    simp only [pow_zero, Nat.lt_one_iff] at he
    subst he
    rw [powModF]; rw [pow_zero, Nat.mod_eq_of_lt (by omega : (1:ℕ) < n)]
  | succ f ih =>
    intro a e he
    rw [powModF]
    by_cases he0 : e = 0
    · subst he0; rw [pow_zero, Nat.mod_eq_of_lt (by omega : (1:ℕ) < n)]; simp
    · simp only [he0, if_false]
      have hhalf : e / 2 < 2 ^ f := by
        rw [pow_succ] at he; omega
      have hih := ih (a*a % n) (e/2) hhalf
      have key : (a * a % n) ^ (e / 2) % n = a ^ (2 * (e / 2)) % n := by
        rw [← Nat.pow_mod]; congr 1
        rw [show a*a = a^2 from (sq a).symm, ← pow_mul]
      by_cases hodd : e % 2 = 1
      · simp only [hodd, if_true]
        rw [hih, key, ← Nat.mul_mod, ← pow_succ', show 2*(e/2)+1 = e from by omega]
      · simp only [hodd, if_false]
        rw [hih, key, show 2*(e/2) = e from by omega]
