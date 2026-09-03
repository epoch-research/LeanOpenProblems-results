import FormalConjecturesUtil

/-! A binary quotient computation with a kernel-checked correctness proof.
The fixed-width branch is used only below its proved numerical bound; the
fallback is the ordinary natural quotient. No native decision axiom is used. -/
namespace Erdos970.KernelArithmetic

/-- Search the half-open integer range [q,q+2^bits). -/
def quotientSearch (n d : ℕ) : ℕ → ℕ → ℕ
  | 0, q => q
  | b+1, q => if (q+2^b)*d ≤ n then quotientSearch n d b (q+2^b)
      else quotientSearch n d b q

lemma quotientSearch_bounds (n d b q : ℕ) (hlo : q*d ≤ n)
    (hhi : n < (q+2^b)*d) :
    quotientSearch n d b q*d ≤ n ∧ n < (quotientSearch n d b q+1)*d := by
  induction b generalizing q with
  | zero => simpa [quotientSearch] using And.intro hlo hhi
  | succ b ih =>
    rw [quotientSearch]
    by_cases hmid : (q+2^b)*d ≤ n
    · rw [if_pos hmid]
      apply ih _ hmid
      convert hhi using 1 <;> simp only [pow_succ]; ring
    · rw [if_neg hmid]
      exact ih q hlo (lt_of_not_ge hmid)

lemma quotientSearch_eq_div (n d b : ℕ) (hd : 0 < d) (hn : n < 2^b) :
    quotientSearch n d b 0 = n/d := by
  have hb : n < (0+2^b)*d := by
    have hh : 2^b ≤ (0+2^b)*d := by
      simpa using Nat.le_mul_of_pos_right (2^b) hd
    exact hn.trans_le hh
  obtain ⟨hlo,hhi⟩ := quotientSearch_bounds n d b 0 (by simp) hb
  exact (Nat.div_eq_of_lt_le hlo hhi).symm

def quotient (n d : ℕ) : ℕ :=
  if n < 262144 ∧ 0 < d then quotientSearch n d 18 0 else n/d

lemma quotient_eq_div (n d : ℕ) : quotient n d = n/d := by
  unfold quotient
  split_ifs with h
  · apply quotientSearch_eq_div n d 18 h.2
    exact h.1
  · rfl

#print axioms quotient_eq_div
end Erdos970.KernelArithmetic
