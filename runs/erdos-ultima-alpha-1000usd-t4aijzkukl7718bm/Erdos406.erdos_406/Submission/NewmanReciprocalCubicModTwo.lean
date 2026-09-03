import Submission.NewmanCubicHighBase

/-! Exclusion of the reciprocal cubic residual, including Frobenius
multiplicities. This is a restricted reduction hypothesis, not a global bound. -/
namespace Erdos406ReciprocalCubicModTwo
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoBinomial
  Erdos406ModTwoQuadratic Erdos406ModTwoCubic Erdos406ModTwoFrobenius
  Erdos406CubicHighBase Erdos406Cyclotomic Erdos406ReciprocalCandidate

lemma reciprocal_cubic_even_lift (P : ℤ[X]) (hP : Binary P) (s : ℕ)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^(2*s)*(X^3+X^2+1)) :
    P = expand ℤ 2 (B (s+1))+X*expand ℤ 2 (X*B s) := by
  apply binary_map_two_injective _ _ hP
    (binary_interleave _ _ (binary_B _) (binary_X_mul _ (binary_B _)))
  rw [hm,Polynomial.map_add,Polynomial.map_mul,map_X,map_expand,map_expand,
    Polynomial.map_mul,map_X,map_B,map_B,map_mul,expand_X,
    expand_binomial_power_two,expand_binomial_power_two]
  rw [show 2*(s+1) = 2*s+2 by omega,pow_add,mod_two_X_add_one_square]
  ring

lemma reciprocal_cubic_one_mod_four_lift (P : ℤ[X]) (hP : Binary P) (u : ℕ)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^(4*u+1)*(X^3+X^2+1)) :
    P = expand ℤ 4 (B (u+1))+(X+X^2)*expand ℤ 4 (B u) := by
  have hb : Binary (expand ℤ 4 (B (u+1))+(X+X^2)*expand ℤ 4 (B u)) := by
    have hh := binary_four_interleave (B (u+1)) (B u) (B u) 0 (binary_B _)
      (binary_B _) (binary_B _) (fun i => Or.inl (by simp))
    convert hh using 1
    simp only [map_zero,mul_zero,add_zero]
    ring
  apply binary_map_two_injective _ _ hP hb
  rw [hm,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_add,
    Polynomial.map_pow,map_X,map_expand,map_expand,map_B,map_B,
    expand_binomial_power_four,expand_binomial_power_four]
  rw [show 4*(u+1) = 4*u+4 by omega,pow_succ',pow_add,mod_two_X_add_one_fourth]
  have hc : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
  calc
    _ = (X+1)^(4*u)*(X^4+X^2+X+1+2*X^3) := by ring
    _ = _ := by rw [hc]; ring

noncomputable def reciprocalMask : ℤ[X] := 1+X+X^3+X^6

lemma reciprocalMask_factorization :
    reciprocalMask = (X+1)*(X^2+1)*(X^3-X^2+1) := by
  unfold reciprocalMask
  ring

lemma binary_reciprocalMask_expand_four (Q : ℤ[X]) (hQ : Binary Q) :
    Binary (reciprocalMask*expand ℤ 4 Q) := by
  have hh := binary_four_interleave Q Q (X*Q) Q hQ hQ (binary_X_mul Q hQ) hQ
  have he : reciprocalMask*expand ℤ 4 Q =
      expand ℤ 4 Q+X*expand ℤ 4 Q+X^2*expand ℤ 4 (X*Q)+X^3*expand ℤ 4 Q := by
    rw [map_mul,expand_X]
    unfold reciprocalMask
    ring
  rwa [he]

lemma reciprocal_cubic_three_mod_four_lift (P : ℤ[X]) (hP : Binary P) (u : ℕ)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^(4*u+3)*(X^3+X^2+1)) :
    P = reciprocalMask*expand ℤ 4 (B u) := by
  apply binary_map_two_injective _ _ hP
    (binary_reciprocalMask_expand_four _ (binary_B _))
  rw [hm,Polynomial.map_mul,map_expand,map_B,expand_binomial_power_four,pow_add]
  have hc : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
  have hf : (X+1 : (ZMod 2)[X])^3*(X^3+X^2+1) = 1+X+X^3+X^6 := by
    calc
      _ = 1+X+X^3+X^6+2*(X+2*X^2+2*X^3+3*X^4+2*X^5) := by ring
      _ = _ := by rw [hc]; ring
  rw [mul_assoc,hf]
  simp only [reciprocalMask,Polynomial.map_add,Polynomial.map_one,Polynomial.map_pow,map_X]
  ring

noncomputable def reciprocalEvenCore (m : ℕ) : ℤ[X] :=
  1+X^(2*m)+X^3*expand ℤ 2 (G m)
noncomputable def reciprocalOneCore (m : ℕ) : ℤ[X] :=
  1+X^(4*m)+(X+X^2)*expand ℤ 4 (G m)

def reciprocalEvenAt (x m : ℕ) : ℕ :=
  1+x^(2*m)+x^3*(∑ i ∈ Finset.range m, x^(2*i))
def reciprocalOneAt (x m : ℕ) : ℕ :=
  1+x^(4*m)+(x+x^2)*(∑ i ∈ Finset.range m, x^(4*i))

lemma reciprocalEvenCore_eval_at (x m : ℕ) :
    (reciprocalEvenCore m).eval (x : ℤ) = (reciprocalEvenAt x m : ℕ) := by
  simp only [reciprocalEvenCore,reciprocalEvenAt,eval_add,eval_mul,eval_X,eval_pow,eval_one,
    expand_eval,G,eval_finset_sum]
  push_cast
  simp only [← pow_mul]

lemma reciprocalOneCore_eval_at (x m : ℕ) :
    (reciprocalOneCore m).eval (x : ℤ) = (reciprocalOneAt x m : ℕ) := by
  simp only [reciprocalOneCore,reciprocalOneAt,eval_add,eval_mul,eval_X,eval_pow,eval_one,
    expand_eval,G,eval_finset_sum]
  push_cast
  simp only [← pow_mul]

lemma reciprocalEvenAt_mod_four (L m : ℕ) :
    reciprocalEvenAt (3^L) m%4 = (2+3^L*m)%4 := by
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
  unfold reciprocalEvenAt
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_mod,hs,hp]
  rcases hx with hx | hx <;> norm_num [Nat.pow_mod,hx,Nat.mod_mod]

lemma reciprocalEvenAt_gt_two (x m : ℕ) (hx : 3 ≤ x) (hm : 0 < m) :
    2 < reciprocalEvenAt x m := by
  have hh : 3^2 ≤ x^(2*m) :=
    (Nat.pow_le_pow_left hx 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  unfold reciprocalEvenAt
  omega

lemma reciprocalEvenCore_power_divisor_at (L t k : ℕ) (hL : 0 < L)
    (hd : (reciprocalEvenCore (2^t)).eval ((3 : ℤ)^L) ∣ (2 : ℤ)^k) : t = 1 := by
  have hnat : reciprocalEvenAt (3^L) (2^t) ∣ 2^k := by
    have he := reciprocalEvenCore_eval_at (3^L) (2^t)
    norm_num only [Nat.cast_pow,Nat.cast_ofNat] at he
    rw [he] at hd
    exact_mod_cast hd
  have hx : 3 ≤ (3 : ℕ)^L := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 3) hL
  have hh := dvd_two_pow_gt_two_mod_four _ k
    (reciprocalEvenAt_gt_two _ _ hx (by positivity)) hnat
  rw [reciprocalEvenAt_mod_four] at hh
  by_cases ht0 : t = 0
  · subst t
    have hm := three_power_mod_eight L
    norm_num at hh
    omega
  by_contra ht1
  have hd4 : 4 ∣ 2^t := show 2^2 ∣ 2^t from Nat.pow_dvd_pow 2 (by omega)
  simp [Nat.add_mod,Nat.mul_mod,Nat.mod_eq_zero_of_dvd hd4] at hh

lemma reciprocalOneAt_mod_eight_ne_zero (L t : ℕ) :
    reciprocalOneAt (3^L) (2^t)%8 ≠ 0 := by
  have hx := three_power_mod_eight L
  have hm := two_power_mod_eight t
  have hfour : ((3^L)^4 : ℕ)%8 = 1 := by
    rw [Nat.pow_mod]
    rcases hx with hx | hx <;> norm_num [hx]
  have hp : ((3^L)^(4*2^t) : ℕ)%8 = 1 := by
    rw [pow_mul,Nat.pow_mod,hfour]
    norm_num
  have hs := sum_power_mod (3^L) 4 (2^t) 8 (by decide) hfour
  unfold reciprocalOneAt
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_mod,hs,hp]
  rcases hx with hx | hx <;> rcases hm with hm | hm | hm | hm <;>
    norm_num [hx,hm,Nat.pow_mod,Nat.mod_mod]

lemma reciprocalOneAt_gt_eight (x m : ℕ) (hx : 3 ≤ x) (hm : 0 < m) :
    8 < reciprocalOneAt x m := by
  have hh : 3^4 ≤ x^(4*m) :=
    (Nat.pow_le_pow_left hx 4).trans (Nat.pow_le_pow_right (by omega) (by omega))
  unfold reciprocalOneAt
  omega

lemma reciprocalOneCore_not_power_divisor_at (L t k : ℕ) (hL : 0 < L) :
    ¬ (reciprocalOneCore (2^t)).eval ((3 : ℤ)^L) ∣ (2 : ℤ)^k := by
  intro hd
  have hnat : reciprocalOneAt (3^L) (2^t) ∣ 2^k := by
    have he := reciprocalOneCore_eval_at (3^L) (2^t)
    norm_num only [Nat.cast_pow,Nat.cast_ofNat] at he
    rw [he] at hd
    exact_mod_cast hd
  have hx : 3 ≤ (3 : ℕ)^L := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 3) hL
  exact reciprocalOneAt_mod_eight_ne_zero L t
    (dvd_two_pow_gt_eight_mod_eight _ k (reciprocalOneAt_gt_eight _ _ hx (by positivity)) hnat)

lemma reciprocalEvenCore_two : reciprocalEvenCore 2 =
    (X+1)*(X^4+X^2-X+1) := by
  simp [reciprocalEvenCore,G,Finset.sum_range_succ]
  ring

/-- The reciprocal cubic does not occur at any positive ternary power base,
regardless of the multiplicity of the linear factor. -/
theorem reciprocal_cubic_mod_two_exclusion (P : ℤ[X]) (hP : Binary P) (a L k : ℕ)
    (hL : 0 < L)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*(X^3+X^2+1)) :
    P.eval ((3 : ℤ)^L) ≠ (2 : ℤ)^k := by
  intro he
  by_cases ha : a%2 = 0
  · let s := a/2
    have has : a = 2*s := by dsimp [s]; omega
    rw [has] at hm
    have hP' := reciprocal_cubic_even_lift P hP s hm
    obtain ⟨t,h,hA,hC⟩ := consecutive_B_normalized s
    have hp : P = expand ℤ 2 (B h)*reciprocalEvenCore (2^t) := by
      rw [hP',hA,hC,map_mul,map_mul,map_add,map_pow,expand_X,map_one,← pow_mul]
      rw [map_mul]
      unfold reciprocalEvenCore
      ring
    have hdC : (reciprocalEvenCore (2^t)).eval ((3 : ℤ)^L) ∣ (2 : ℤ)^k := by
      rw [← he,hp,eval_mul]
      exact dvd_mul_left _ _
    have ht := reciprocalEvenCore_power_divisor_at L t k hL hdC
    rw [ht,pow_one,reciprocalEvenCore_two] at hp hdC
    have hdP : (X^1+1 : ℤ[X]) ∣ P := by
      refine ⟨expand ℤ 2 (B h)*(X^4+X^2-X+1),?_⟩
      rw [hp]
      ring
    have hL1 : L = 1 := by
      simpa using binomial_dvd_at_power_three P L 1 k hL (by decide) hdP he
    subst L
    norm_num at hdC
    have hd11 : (11 : ℤ) ∣ (2 : ℤ)^k :=
      (by norm_num : (11 : ℤ) ∣ 352).trans hdC
    have hn11 : 11 ∣ 2^k := by exact_mod_cast hd11
    have hh := (show Nat.Prime 11 by decide).dvd_of_dvd_pow hn11
    norm_num at hh
  have ha4 : a%4 = 1 ∨ a%4 = 3 := by omega
  rcases ha4 with ha4 | ha4
  · let u := a/4
    have hau : a = 4*u+1 := by dsimp [u]; omega
    rw [hau] at hm
    have hP' := reciprocal_cubic_one_mod_four_lift P hP u hm
    obtain ⟨t,h,hA,hC⟩ := consecutive_B_normalized u
    have hp : P = expand ℤ 4 (B h)*reciprocalOneCore (2^t) := by
      rw [hP',hA,hC,map_mul,map_mul,map_add,map_pow,expand_X,map_one,← pow_mul]
      unfold reciprocalOneCore
      ring
    apply reciprocalOneCore_not_power_divisor_at L t k hL
    rw [← he,hp,eval_mul]
    exact dvd_mul_left _ _
  · let u := a/4
    have hau : a = 4*u+3 := by dsimp [u]; omega
    rw [hau] at hm
    have hp := reciprocal_cubic_three_mod_four_lift P hP u hm
    have hdP : (X^2+1 : ℤ[X]) ∣ P := by
      refine ⟨(X+1)*(X^3-X^2+1)*expand ℤ 4 (B u),?_⟩
      rw [hp,reciprocalMask_factorization]
      ring
    have hh := binomial_dvd_at_power_three P L 2 k hL (by decide) hdP he
    omega

/-- The exclusion persists for all power-of-two multiplicities of the
reciprocal cubic, via exact Frobenius deflation. -/
theorem reciprocal_cubic_two_power_mod_two_exclusion (t : ℕ) (P : ℤ[X]) (hP : Binary P)
    (a L k : ℕ) (hL : 0 < L)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*(X^3+X^2+1)^(2^t)) :
    P.eval ((3 : ℤ)^L) ≠ (2 : ℤ)^k := by
  intro he
  have hR : (X^3+X^2+1 : (ZMod 2)[X]).coeff 0 = 1 := by simp
  obtain ⟨Q,j,hQ,_,hmQ,heQ,_⟩ := frobenius_deflation t P hP _ hR a L k hL hm he
  exact reciprocal_cubic_mod_two_exclusion Q hQ (a/2^t) (2^t*L) j (by positivity) hmQ heQ

#print axioms reciprocal_cubic_mod_two_exclusion
#print axioms reciprocal_cubic_two_power_mod_two_exclusion
end Erdos406ReciprocalCubicModTwo
