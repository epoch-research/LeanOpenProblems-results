import FormalConjectures.Util.ProblemImports

example (p n k : ℕ) [Fact p.Prime] (hk : k ≤ n) (hb : Nat.log p (3*n+2*k) < 4) :
    padicValNat p (Nat.choose (3*n+2*k) n) =
      ((Finset.Ico 1 4).filter fun i => p ^ i ≤ n % p ^ i + (3*n+2*k - n) % p ^ i).card := by
  simpa using (padicValNat_choose (p:=p) (n:=3*n+2*k) (k:=n) (b:=4) (by omega) hb)
