import Submission.NewmanModTwoFrobenius

/-! Extending the restricted cubic classification to powers-of-three inputs.
This still has an explicit hypothesis on the entire reduction modulo two. -/
namespace Erdos406CubicHighBase
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoBinomial
  Erdos406ModTwoQuadratic Erdos406ModTwoCubic Erdos406ModTwoFrobenius
  Erdos406Cyclotomic Erdos406ReciprocalCandidate

def evenAt (x m : ℕ) : ℕ := (∑ i ∈ Finset.range m, x^(2*i))+x*(x^(2*m)+1)
def oneAt (x m : ℕ) : ℕ := 1+x^(4*m)+(x^2+x^3)*(∑ i ∈ Finset.range m, x^(4*i))

lemma evenCore_eval_at (x m : ℕ) : (evenCore m).eval (x : ℤ) = (evenAt x m : ℕ) := by
  simp only [evenCore,evenAt,eval_add,eval_mul,eval_X,eval_pow,eval_one,
    expand_eval,G,eval_finset_sum]
  push_cast
  simp only [← pow_mul]

lemma oneCore_eval_at (x m : ℕ) : (oneCore m).eval (x : ℤ) = (oneAt x m : ℕ) := by
  simp only [oneCore,oneAt,eval_add,eval_mul,eval_X,eval_pow,eval_one,
    expand_eval,G,eval_finset_sum]
  push_cast
  simp only [← pow_mul]

lemma three_power_mod_eight (L : ℕ) : (3^L : ℕ)%8 = 1 ∨ (3^L : ℕ)%8 = 3 := by
  rcases Nat.even_or_odd L with ⟨u,hu⟩ | ⟨u,hu⟩
  · left
    rw [hu,← two_mul,pow_mul,Nat.pow_mod]
    norm_num
  · right
    rw [hu,pow_add,pow_mul]
    norm_num [Nat.mul_mod,Nat.pow_mod]

lemma two_power_mod_eight (t : ℕ) :
    (2^t : ℕ)%8 = 1 ∨ (2^t : ℕ)%8 = 2 ∨ (2^t : ℕ)%8 = 4 ∨ (2^t : ℕ)%8 = 0 := by
  by_cases ht : t < 3
  · interval_cases t <;> norm_num
  · right; right; right
    exact Nat.mod_eq_zero_of_dvd (show 2^3 ∣ 2^t from Nat.pow_dvd_pow 2 (by omega))

lemma sum_power_mod (x d m M : ℕ) (hM : 1 < M) (hx : x^d%M = 1) :
    (∑ i ∈ Finset.range m, x^(d*i))%M = m%M := by
  have hp (i : ℕ) : x^(d*i)%M = 1 := by
    rw [pow_mul,Nat.pow_mod,hx,one_pow,Nat.mod_eq_of_lt hM]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ,Nat.add_mod,ih,hp]
    simp only [Nat.add_mod,Nat.mod_eq_of_lt hM,Nat.mod_mod]

lemma evenAt_mod_four (L m : ℕ) : evenAt (3^L) m%4 = (m+2)%4 := by
  have hx : (3^L : ℕ)%4 = 1 ∨ (3^L : ℕ)%4 = 3 := by
    have hh := three_power_mod_eight L
    omega
  have hsquare : ((3^L)^2 : ℕ)%4 = 1 := by
    rw [Nat.pow_mod]
    rcases hx with hx | hx <;> norm_num [hx]
  have hp : ((3^L)^(2*m) : ℕ)%4 = 1 := by
    rw [pow_mul,Nat.pow_mod,hsquare]
    norm_num
  have hs := sum_power_mod (3^L) 2 m 4 (by decide) hsquare
  unfold evenAt
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_mod,hs,hp]
  rcases hx with hx | hx <;> rw [hx]

lemma evenAt_gt_two (x m : ℕ) (hx : 3 ≤ x) : 2 < evenAt x m := by
  have hp : 0 < x^(2*m) := by positivity
  have hmul := Nat.mul_le_mul hx (show 1 ≤ x^(2*m)+1 by omega)
  unfold evenAt
  omega

lemma evenCore_power_divisor_at (L t k : ℕ) (hL : 0 < L)
    (hd : (evenCore (2^t)).eval ((3 : ℤ)^L) ∣ (2 : ℤ)^k) : t = 1 := by
  have hnat : evenAt (3^L) (2^t) ∣ 2^k := by
    have he := evenCore_eval_at (3^L) (2^t)
    norm_num only [Nat.cast_pow,Nat.cast_ofNat] at he
    rw [he] at hd
    exact_mod_cast hd
  have hx : 3 ≤ (3 : ℕ)^L := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 3) hL
  have hh := dvd_two_pow_gt_two_mod_four _ k (evenAt_gt_two _ _ hx) hnat
  rw [evenAt_mod_four] at hh
  by_cases ht0 : t = 0
  · subst t
    norm_num at hh
  by_contra ht1
  have hd4 : 4 ∣ 2^t := show 2^2 ∣ 2^t from Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd hd4] at hh
  norm_num at hh

lemma oneAt_mod_eight_ne_zero (L t : ℕ) : oneAt (3^L) (2^t)%8 ≠ 0 := by
  have hx := three_power_mod_eight L
  have hm := two_power_mod_eight t
  have hfour : ((3^L)^4 : ℕ)%8 = 1 := by
    rw [Nat.pow_mod]
    rcases hx with hx | hx <;> norm_num [hx]
  have hp : ((3^L)^(4*2^t) : ℕ)%8 = 1 := by
    rw [pow_mul,Nat.pow_mod,hfour]
    norm_num
  have hs := sum_power_mod (3^L) 4 (2^t) 8 (by decide) hfour
  unfold oneAt
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_mod,hs,hp]
  rcases hx with hx | hx <;> rcases hm with hm | hm | hm | hm <;>
    norm_num [hx,hm,Nat.pow_mod,Nat.mod_mod]

lemma oneAt_gt_eight (x m : ℕ) (hx : 3 ≤ x) (hm : 0 < m) : 8 < oneAt x m := by
  have hh : 3^4 ≤ x^(4*m) :=
    (Nat.pow_le_pow_left hx 4).trans (Nat.pow_le_pow_right (by omega) (by omega))
  unfold oneAt
  omega

lemma dvd_two_pow_gt_eight_mod_eight (n k : ℕ) (hn : 8 < n) (hd : n ∣ 2^k) : n%8 = 0 := by
  obtain ⟨j,_,hj⟩ := Nat.dvd_prime_pow Nat.prime_two |>.mp hd
  have hj3 : 3 ≤ j := by
    by_contra hh
    interval_cases j <;> norm_num at hj <;> omega
  rw [hj]
  exact Nat.mod_eq_zero_of_dvd (show 2^3 ∣ 2^j from Nat.pow_dvd_pow 2 hj3)

lemma oneCore_not_power_divisor_at (L t k : ℕ) (hL : 0 < L) :
    ¬ (oneCore (2^t)).eval ((3 : ℤ)^L) ∣ (2 : ℤ)^k := by
  intro hd
  have hnat : oneAt (3^L) (2^t) ∣ 2^k := by
    have he := oneCore_eval_at (3^L) (2^t)
    norm_num only [Nat.cast_pow,Nat.cast_ofNat] at he
    rw [he] at hd
    exact_mod_cast hd
  have hx : 3 ≤ (3 : ℕ)^L := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 3) hL
  exact oneAt_mod_eight_ne_zero L t
    (dvd_two_pow_gt_eight_mod_eight _ k (oneAt_gt_eight _ _ hx (by positivity)) hnat)

lemma binomial_dvd_at_power_three (P : ℤ[X]) (L d k : ℕ) (hL : 0 < L) (hd : 0 < d)
    (hdiv : (X^d+1 : ℤ[X]) ∣ P) (he : P.eval ((3 : ℤ)^L) = (2 : ℤ)^k) : L*d = 1 := by
  have hv := eval_dvd (x := (3 : ℤ)^L) hdiv
  rw [he,eval_add,eval_pow,eval_X,eval_one,← pow_mul] at hv
  apply Erdos406Structure.three_pow_add_one_dvd_two_pow (by positivity : 0 < L*d)
  exact_mod_cast hv

/-- The cubic family at any positive ternary power base is possible only
at the original base three and with the known polynomial of 256. -/
theorem cubic_mod_two_classification_at (P : ℤ[X]) (hP : Binary P) (a L k : ℕ)
    (hL : 0 < L)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*(X^3+X+1))
    (he : P.eval ((3 : ℤ)^L) = (2 : ℤ)^k) : L = 1 ∧ P = 1+X+X^2+X^5 := by
  have hL1 : L = 1 := by
    by_cases ha : a%2 = 0
    · let s := a/2
      have has : a = 2*s := by dsimp [s]; omega
      rw [has] at hm
      have hP' := cubic_even_lift P hP s hm
      obtain ⟨t,h,hA,hC⟩ := consecutive_B_normalized s
      have hp : P = expand ℤ 2 (B h)*evenCore (2^t) := by
        rw [hP',hA,hC,map_mul,map_mul,map_add,map_pow,expand_X,map_one,← pow_mul]
        unfold evenCore
        ring
      have hdC : (evenCore (2^t)).eval ((3 : ℤ)^L) ∣ (2 : ℤ)^k := by
        rw [← he,hp,eval_mul]
        exact dvd_mul_left _ _
      have ht := evenCore_power_divisor_at L t k hL hdC
      rw [ht,pow_one,evenCore_two] at hp
      have hdP : (X^1+1 : ℤ[X]) ∣ P := by
        refine ⟨expand ℤ 2 (B h)*(X^4-X^3+X^2+1),?_⟩
        rw [hp]
        ring
      simpa using binomial_dvd_at_power_three P L 1 k hL (by decide) hdP he
    have ha4 : a%4 = 1 ∨ a%4 = 3 := by omega
    rcases ha4 with ha4 | ha4
    · let u := a/4
      have hau : a = 4*u+1 := by dsimp [u]; omega
      rw [hau] at hm
      have hP' := cubic_one_mod_four_lift P hP u hm
      obtain ⟨t,h,hA,hC⟩ := consecutive_B_normalized u
      have hp : P = expand ℤ 4 (B h)*oneCore (2^t) := by
        rw [hP',hA,hC,map_mul,map_mul,map_add,map_pow,expand_X,map_one,← pow_mul]
        unfold oneCore
        ring
      apply False.elim
      apply oneCore_not_power_divisor_at L t k hL
      rw [← he,hp,eval_mul]
      exact dvd_mul_left _ _
    · let u := a/4
      have hau : a = 4*u+3 := by dsimp [u]; omega
      rw [hau] at hm
      have hp := cubic_three_mod_four_lift P hP u hm
      have hdP : (X^2+1 : ℤ[X]) ∣ P := by
        refine ⟨(X+1)*(X^3-X+1)*expand ℤ 4 (B u),?_⟩
        rw [hp,oddMask_factorization]
        ring
      have hh := binomial_dvd_at_power_three P L 2 k hL (by decide) hdP he
      omega
  refine ⟨hL1,cubic_mod_two_classification P hP a k hm ?_⟩
  simpa [hL1] using he


/-- Frobenius multiplicities of this cubic do not yield new cases: the
multiplicity and evaluation base must both be the original ones. -/
theorem cubic_two_power_mod_two_classification (t : ℕ) (P : ℤ[X]) (hP : Binary P)
    (a L k : ℕ) (hL : 0 < L)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*(X^3+X+1)^(2^t))
    (he : P.eval ((3 : ℤ)^L) = (2 : ℤ)^k) :
    t = 0 ∧ L = 1 ∧ P = 1+X+X^2+X^5 := by
  have hR : (X^3+X+1 : (ZMod 2)[X]).coeff 0 = 1 := by simp
  obtain ⟨Q,j,hQ,_,hmQ,heQ,_⟩ := frobenius_deflation t P hP _ hR a L k hL hm he
  have hh := (cubic_mod_two_classification_at Q hQ (a/2^t) (2^t*L) j
    (by positivity) hmQ heQ).1
  have ht : t = 0 := by
    by_contra ht
    have hgt : 1 < (2 : ℕ)^t := one_lt_pow₀ (by decide) ht
    nlinarith
  refine ⟨ht,cubic_mod_two_classification_at P hP a L k hL ?_ he⟩
  simpa [ht] using hm

/-- Direct classification of the original candidates in this enlarged,
but still restricted, Frobenius-cubic family. -/
theorem candidate_cubic_two_power_mod_two_classification (n : ℕ) (hn : n.isPowerOfTwo)
    (hg : Nat.digits 3 n ⊆ [0,1]) (a t : ℕ)
    (hm : (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) =
      (X+1)^a*(X^3+X+1)^(2^t)) : t = 0 ∧ n = 256 := by
  obtain ⟨k,rfl⟩ := hn
  have he : (digitPoly (Nat.digits 3 (2^k))).eval ((3 : ℤ)^1) = (2 : ℤ)^k := by
    rw [pow_one,digitPoly_eval_three]
    norm_cast
  obtain ⟨ht,_,hP⟩ := cubic_two_power_mod_two_classification t _
    (binary_digitPoly _ hg) a 1 k (by decide) hm he
  refine ⟨ht,?_⟩
  have hh := congrArg (eval (3 : ℤ)) hP
  rw [digitPoly_eval_three] at hh
  norm_num at hh
  exact_mod_cast hh

#print axioms cubic_mod_two_classification_at
#print axioms cubic_two_power_mod_two_classification
#print axioms candidate_cubic_two_power_mod_two_classification
end Erdos406CubicHighBase
