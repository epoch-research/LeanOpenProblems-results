import FormalConjectures.Util.ProblemImports

open Finset

variable {p : ℕ}

set_option maxHeartbeats 2000000

-- product of p consecutive integers with the unique multiple of p removed ≡ -1 mod p
theorem block_zmod (hp : Nat.Prime p) (a : ℕ) :
    (∏ i ∈ (Finset.Icc (a+1) (a+p)).erase ((a/p+1)*p), (i:ZMod p)) = -1 := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  -- the multiple
  set mult := (a/p+1)*p with hmdef
  have hmmem : mult ∈ Finset.Icc (a+1) (a+p) := by
    rw [Finset.mem_Icc, hmdef]
    have h1 := Nat.lt_div_add_one_mul_self a hp.pos
    have h2 := Nat.div_mul_le_self a p
    constructor <;> nlinarith [Nat.div_mul_le_self a p, Nat.lt_succ_mul_div a p]
  sorry
