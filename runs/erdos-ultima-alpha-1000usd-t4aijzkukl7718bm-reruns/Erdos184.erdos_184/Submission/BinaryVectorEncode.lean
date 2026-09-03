import Submission.SortedDisjointCertificate

/-! Positional encoding of bounded binary vectors, with a kernel-reducible definition. -/
namespace Erdos184
namespace BinaryVectorEncode

def encode : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n+1, f => f 0 + 2 * encode n (fun i => f i.succ)

lemma encode_lt (n : ℕ) (f : Fin n → ℕ) (hf : ∀ i, f i < 2) :
    encode n f < 2 ^ n := by
  induction n with
  | zero => simp [encode]
  | succ n ih =>
    have h := ih (fun i => f i.succ) (fun i => hf i.succ)
    have h0 := hf 0
    simp only [encode,pow_succ]
    omega

lemma digit_encode (n : ℕ) (f : Fin n → ℕ) (hf : ∀ i, f i < 2) (i : Fin n) :
    encode n f / 2 ^ i.val % 2 = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · have h0 := hf 0
      simp only [encode,Fin.val_zero,pow_zero,Nat.div_one]
      omega
    · have h0 := hf 0
      have hdiv : (f 0 + 2 * encode n (fun k => f k.succ)) / 2 =
          encode n (fun k => f k.succ) := by omega
      simp only [encode,Fin.val_succ,pow_succ]
      rw [Nat.mul_comm (2 ^ j.val) 2,← Nat.div_div_eq_div_mul,hdiv]
      exact ih (fun k => f k.succ) (fun k => hf k.succ) j

end BinaryVectorEncode
end Erdos184
