import Submission.LosingProductComparison

/-! Structured winner-preserving products. These finite examples disprove
blanket strict-increase assertions for the auxiliary product map, not any
asymptotic assertion about its distribution. -/
namespace Erdos371

lemma cyclotomic_cube_identities (k : ℕ) (hk : 1 ≤ k) :
    k^3 = (k-1)*(k^2+k+1)+1 ∧
    (k+1)^3+1 = (k+2)*(k^2+k+1) := by
  have he : k-1+1=k := Nat.sub_add_cancel hk
  constructor
  · nlinarith [sq_nonneg (k : ℤ)]
  · ring

lemma cyclotomic_sixth_identities (k : ℕ) (hk : 1 ≤ k) :
    k^6 = (k-1)*(k+1)*(k^2+k+1)*(k*(k-1)+1)+1 ∧
    (k+1)^6 = k*(k+2)*(k^2+k+1)*(k^2+3*k+3)+1 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  constructor <;> (try simp only [Nat.add_sub_cancel_left]) <;> ring

private lemma packed_fall (K p n : ℕ) (hp : p.Prime)
    (h : PackedPrimePair K p (n+1) n) :
    primeWinner n=p ∧ factorSign n = -1 ∧ losingNumber n=n+1 := by
  obtain ⟨hl,hw⟩ := packedPrimePair_prime_factors K p (n+1) n hp h
  simp [primeWinner,hw,max_eq_left hl.le,factorSign,predicateSign,
    losingNumber,hl.not_gt]

private lemma packed_rise (K p n : ℕ) (hp : p.Prime)
    (h : PackedPrimePair K p n (n+1)) :
    primeWinner n=p ∧ factorSign n = 1 ∧ losingNumber n=n := by
  obtain ⟨hl,hw⟩ := packedPrimePair_prime_factors K p n (n+1) hp h
  simp [primeWinner,hw,max_eq_right hl.le,factorSign,predicateSign,
    losingNumber,hl]

/-- The opposite-sign cubic example lies in the short-cofactor range. -/
theorem losingProduct_preserves_winner_cubic :
    primeWinner 4912=307 ∧ primeWinner 5832=307 ∧
    factorSign 4912 = -1 ∧ factorSign 5832 = 1 ∧
    losingProductIndex 4912 5832=28652616 ∧
    primeWinner 28652616=307 ∧ 4*5833 < (307 : ℕ)^2 := by
  have hp : Nat.Prime 307 := by norm_num
  have hn := packed_fall 3 307 4912 hp (by
    refine ⟨[17,17,17],[16,1,1],?_,?_,?_,?_,?_,?_⟩ <;> norm_num)
  have hm := packed_rise 3 307 5832 hp (by
    refine ⟨[18,18,18],[19,1,1],?_,?_,?_,?_,?_,?_⟩ <;> norm_num)
  have hr := packed_rise 3 307 28652616 hp (by
    refine ⟨[306,306,306],[7,67,199],?_,?_,?_,?_,?_,?_⟩ <;> norm_num)
  refine ⟨hn.1,hm.1,hn.2.1,hm.2.1,?_,hr.1,by norm_num⟩
  have hfalse : ¬(Nat.maxPrimeFac 4912 < Nat.maxPrimeFac (4912+1) ↔
      Nat.maxPrimeFac 5832 < Nat.maxPrimeFac (5832+1)) := by
    intro h
    have hsign : factorSign 4912 = factorSign 5832 := by
      change (if Nat.maxPrimeFac 4912 < Nat.maxPrimeFac (4912+1) then (1 : ℝ) else -1) =
        (if Nat.maxPrimeFac 5832 < Nat.maxPrimeFac (5832+1) then (1 : ℝ) else -1)
      simp only [h]
    rw [hn.2.1,hm.2.1] at hsign
    norm_num at hsign
  simp only [losingProductIndex,if_neg hfalse,hn.2.2,hm.2.2]

/-- The sixth-power construction has same-sign, comparable, nonadjacent
inputs whose loser labels are below the square root of their common winner.
This is a finite example, not an infinite prime-values claim. -/
theorem losingProduct_preserves_winner_same_sign :
    ∃ p n m r : ℕ, p.Prime ∧ 1 < n ∧ n < m ∧ 8*m < 9*n ∧
      n+1 < m ∧ primeWinner n=p ∧ primeWinner m=p ∧
      factorSign n = -1 ∧ factorSign m = -1 ∧
      (Nat.maxPrimeFac (losingNumber n))^2 < p ∧
      (Nat.maxPrimeFac (losingNumber m))^2 < p ∧
      losingProductIndex n m=r ∧ primeWinner r=p := by
  let p : ℕ := 5113
  let n : ℕ := 71^6-1
  let m : ℕ := 72^6-1
  let r : ℕ := 5112^6-1
  have hp : p.Prime := by norm_num [p]
  have hn := packed_fall 6 p n hp (by
    refine ⟨[71,71,71,71,71,71],[70,72,4971,1,1,1],?_,?_,?_,?_,?_,?_⟩ <;>
      norm_num [p,n])
  have hm := packed_fall 6 p m hp (by
    refine ⟨[72,72,72,72,72,72],[71,73,7,751,1,1],?_,?_,?_,?_,?_,?_⟩ <;>
      norm_num [p,m])
  have hr := packed_fall 8 p r hp (by
    refine ⟨[5112,5112,5112,5112,5112,5112,1,1],
      [5111,7,13,349,823,79,163,2029],?_,?_,?_,?_,?_,?_⟩ <;>
      norm_num [p,r])
  refine ⟨p,n,m,r,hp,by norm_num [n],by norm_num [n,m],by norm_num [n,m],
    by norm_num [n,m],hn.1,hm.1,hn.2.1,hm.2.1,?_,?_,?_,hr.1⟩
  · rw [hn.2.2]
    change (Nat.maxPrimeFac (71^6-1+1))^2 < p
    rw [Nat.sub_add_cancel (by norm_num : 1 ≤ (71 : ℕ)^6),
      Nat.maxPrimeFac_pow (by norm_num)]
    exact (Nat.pow_le_pow_left Nat.maxPrimeFac_le 2).trans_lt (by norm_num [p])
  · rw [hm.2.2]
    change (Nat.maxPrimeFac (72^6-1+1))^2 < p
    rw [Nat.sub_add_cancel (by norm_num : 1 ≤ (72 : ℕ)^6),
      Nat.maxPrimeFac_pow (by norm_num)]
    have h72 : Nat.maxPrimeFac 72 = 3 := by decide +kernel
    norm_num [h72,p]
  · have he : (Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) ↔
        Nat.maxPrimeFac m < Nat.maxPrimeFac (m+1)) := by
      have hnf : ¬Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1) := by
        intro h
        have hsign : factorSign n=1 := by simp [factorSign,predicateSign,h]
        rw [hn.2.1] at hsign
        norm_num at hsign
      have hmf : ¬Nat.maxPrimeFac m < Nat.maxPrimeFac (m+1) := by
        intro h
        have hsign : factorSign m=1 := by simp [factorSign,predicateSign,h]
        rw [hm.2.1] at hsign
        norm_num at hsign
      simp only [hnf,hmf]
    simp only [losingProductIndex,if_pos he,hn.2.2,hm.2.2]
    norm_num [n,m,r]

#print axioms losingProduct_preserves_winner_cubic
#print axioms losingProduct_preserves_winner_same_sign
end Erdos371
