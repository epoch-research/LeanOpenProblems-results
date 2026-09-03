import Submission.SmoothFactorPacking

/-! Exact two-sided factor certificates. The factor bounds on the winning
cofactor are retained; divisibility by p alone would not identify the winner. -/
namespace Erdos371

lemma maxPrimeFac_list_prod_lt (p : ℕ) (hp : 1 < p) (L : List ℕ)
    (hL : ∀ a ∈ L, 1 ≤ a ∧ a < p) : Nat.maxPrimeFac L.prod < p := by
  induction L with
  | nil => simpa using hp
  | cons a L ih =>
    have ha := hL a (by simp)
    have htail : ∀ b ∈ L, 1 ≤ b ∧ b < p := fun b hb => hL b (by simp [hb])
    have hpos : 0 < L.prod := List.prod_pos (fun b hb => (htail b hb).1)
    rw [List.prod_cons,Nat.maxPrimeFac_mul (by omega : a ≠ 0) hpos.ne']
    exact max_lt (Nat.maxPrimeFac_le.trans_lt ha.2) (ih htail)

/-- A certificate for a prescribed smaller-factor integer and a prescribed
prime winner. Lists are ordered, so their multiplicities are not discarded. -/
def PackedPrimePair (K p m w : ℕ) : Prop :=
  ∃ A B : List ℕ, A.length = K ∧ B.length = K ∧
    (∀ a ∈ A, 1 ≤ a ∧ a < p) ∧ (∀ b ∈ B, 1 ≤ b ∧ b ≤ p) ∧
    A.prod = m ∧ p*B.prod = w

lemma packedPrimePair_prime_factors (K p m w : ℕ) (hp : p.Prime)
    (h : PackedPrimePair K p m w) :
    Nat.maxPrimeFac m < p ∧ Nat.maxPrimeFac w = p := by
  obtain ⟨A,B,hA,hB,hAb,hBb,hm,hw⟩ := h
  have hAP := maxPrimeFac_list_prod_lt p hp.one_lt A hAb
  have hBP : Nat.maxPrimeFac B.prod ≤ p := by
    have h := maxPrimeFac_list_prod_lt (p+1) (by have := hp.two_le; omega) B
      (fun b hb => ⟨(hBb b hb).1,by have := (hBb b hb).2; omega⟩)
    omega
  have hBpos : 0 < B.prod := List.prod_pos (fun b hb => (hBb b hb).1)
  refine ⟨by simpa only [hm] using hAP,?_⟩
  rw [← hw,Nat.maxPrimeFac_mul hp.ne_zero hBpos.ne',hp.maxPrimeFac_eq_self,max_eq_left hBP]

/-- Coverage on both sides of the pair. The winning cofactor may contain p,
so its list entries are allowed to equal p, unlike the losing entries. -/
theorem exists_packedPrimePair (K p m w : ℕ) (hp : p.Prime)
    (hm : 0 < m) (hw : 0 < w) (hloss : Nat.maxPrimeFac m < p)
    (hwin : Nat.maxPrimeFac w = p) (hmsize : m^2 < p^K) (hwsize : w^2 < p^K) :
    PackedPrimePair K p m w := by
  obtain ⟨A,hAm,hAK,hAb⟩ := exists_exact_factor_list m p K hm hloss hmsize
  have hd : p ∣ w := by rw [← hwin]; exact Nat.maxPrimeFac_dvd
  have hb : 0 < w/p := Nat.div_pos (Nat.le_of_dvd hw hd) hp.pos
  have he : p*(w/p) = w := Nat.mul_div_cancel' hd
  have hsmall : Nat.maxPrimeFac (w/p) < p+1 := by
    have hle : Nat.maxPrimeFac (w/p) ≤ Nat.maxPrimeFac w := by
      calc
        _ ≤ max (Nat.maxPrimeFac p) (Nat.maxPrimeFac (w/p)) := le_max_right _ _
        _ = Nat.maxPrimeFac (p*(w/p)) := (Nat.maxPrimeFac_mul hp.ne_zero hb.ne').symm
        _ = _ := congrArg Nat.maxPrimeFac he
    omega
  have hbsize : (w/p)^2 < (p+1)^K :=
    ((Nat.pow_le_pow_left (Nat.div_le_self w p) 2).trans_lt hwsize).trans_le
      (Nat.pow_le_pow_left (Nat.le_succ p) K)
  obtain ⟨B,hBm,hBK,hBb⟩ := exists_exact_factor_list (w/p) (p+1) K hb hsmall hbsize
  refine ⟨A,B,hAK,hBK,hAb,?_,hAm,?_⟩
  · intro b hb
    exact ⟨(hBb b hb).1,by have := (hBb b hb).2; omega⟩
  · rw [hBm,he]

/-- An exact equivalence under the size hypothesis, not an estimate of the
number or orientation of these certificates. -/
theorem packedPrimePair_iff (K p m w : ℕ) (hp : p.Prime)
    (hm : 0 < m) (hw : 0 < w) (hmsize : m^2 < p^K) (hwsize : w^2 < p^K) :
    PackedPrimePair K p m w ↔ Nat.maxPrimeFac m < p ∧ Nat.maxPrimeFac w = p :=
  ⟨packedPrimePair_prime_factors K p m w hp,fun h =>
    exists_packedPrimePair K p m w hp hm hw h.1 h.2 hmsize hwsize⟩

def winningNumber (n : ℕ) : ℕ :=
  if Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) then n+1 else n

lemma comparison_numbers_bounds (n : ℕ) (hn : 1 < n) :
    1 < losingNumber n ∧ 1 < winningNumber n ∧
      losingNumber n ≤ n+1 ∧ winningNumber n ≤ n+1 := by
  unfold losingNumber winningNumber
  split_ifs <;> omega

lemma comparison_numbers_prime_factors (n : ℕ) (hn : 1 < n) :
    (primeWinner n).Prime ∧ Nat.maxPrimeFac (losingNumber n) < primeWinner n ∧
      Nat.maxPrimeFac (winningNumber n) = primeWinner n := by
  unfold losingNumber winningNumber primeWinner
  split_ifs with h
  · rw [max_eq_right h.le]
    exact ⟨Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega),h,rfl⟩
  · have hfall : Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac n :=
      lt_of_le_of_ne (not_lt.mp h) (consecutive_maxPrimeFac_ne n)
    rw [max_eq_left hfall.le]
    exact ⟨Nat.prime_maxPrimeFac_of_one_lt n hn,hfall,rfl⟩

/-- Actual comparisons have two-sided certificates throughout every range
where the displayed integer power condition holds. -/
theorem comparison_packedPrimePair (K N n : ℕ) (hn : 1 < n) (hnN : n < N)
    (hsize : N^2 < (primeWinner n)^K) :
    PackedPrimePair K (primeWinner n) (losingNumber n) (winningNumber n) := by
  obtain ⟨hl,hw,hlN,hwN⟩ := comparison_numbers_bounds n hn
  obtain ⟨hp,hlp,hwp⟩ := comparison_numbers_prime_factors n hn
  apply exists_packedPrimePair K (primeWinner n) (losingNumber n) (winningNumber n)
    hp (by omega) (by omega) hlp hwp
  · exact (Nat.pow_le_pow_left (by omega : losingNumber n ≤ N) 2).trans_lt hsize
  · exact (Nat.pow_le_pow_left (by omega : winningNumber n ≤ N) 2).trans_lt hsize

/-- Losing-side factors and divisibility alone do not determine the winning
prime once the product can exceed p^2: 4*4-1 is divisible by 3 but has winner 5. -/
lemma higher_factor_divisibility_not_winner :
    (3 : ℕ).Prime ∧ 3 ∣ 2*2*2*2-1 ∧ (2 : ℕ) < 3 ∧
      Nat.maxPrimeFac (2*2*2*2-1) = 5 := by
  decide +kernel

#print axioms maxPrimeFac_list_prod_lt
#print axioms exists_packedPrimePair
#print axioms packedPrimePair_iff
#print axioms comparison_packedPrimePair
#print axioms higher_factor_divisibility_not_winner
end Erdos371
