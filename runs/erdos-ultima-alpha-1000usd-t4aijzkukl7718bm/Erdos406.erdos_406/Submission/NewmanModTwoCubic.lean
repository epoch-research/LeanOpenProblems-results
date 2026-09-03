import Submission.NewmanModTwoQuadratic

/-! An all-degree classification for one restricted cubic reduction over F₂.
The hypothesis on the entire reduction is explicit. General reductions and
the finiteness conjecture remain uncontrolled by this result. -/
namespace Erdos406ModTwoCubic
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoBinomial
  Erdos406ModTwoQuadratic Erdos406Cyclotomic Erdos406ReciprocalCandidate

lemma consecutive_B_normalized (n : ℕ) : ∃ t h : ℕ,
    B n = B h*G (2^t) ∧ B (n+1) = B h*(X^(2^t)+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd n with ⟨u,hu⟩ | ⟨u,hu⟩
    · have hn : n = 2*u := by omega
      rw [hn]
      refine ⟨0,2*u,?_,?_⟩
      · rw [pow_zero,G_one,mul_one]
      · rw [B_odd,B_even,pow_zero,pow_one,mul_comm]
    · have hn : n = 2*u+1 := by omega
      obtain ⟨t,h,hA,hC⟩ := ih u (by omega)
      rw [hn]
      refine ⟨t+1,2*h,?_,?_⟩
      · rw [B_odd,hA,map_mul,B_even,pow_succ',G_double]
        ring
      · rw [show 2*u+1+1 = 2*(u+1) by omega,B_even,hC,map_mul,map_add,
          map_pow,expand_X,map_one,← pow_mul,pow_succ',B_even]

lemma B_constant_one (n : ℕ) : (B n).coeff 0 = 1 := by
  have hc := congrArg (fun p : (ZMod 2)[X] => p.coeff 0) (map_B n)
  simp only [coeff_map] at hc
  have hf : ((X+1 : (ZMod 2)[X])^n).coeff 0 = 1 := by
    simp [coeff_zero_eq_eval_zero]
  rw [hf] at hc
  rcases binary_B n 0 with h | h
  · simp [h] at hc
  · exact h

lemma pascal_even_expansion_power_divisor (h k : ℕ)
    (hd : (expand ℤ 2 (B h)).eval 3 ∣ (2 : ℤ)^k) : expand ℤ 2 (B h) = 1 := by
  have hb := binary_expand_two _ (binary_B h)
  have h0 : (expand ℤ 2 (B h)).coeff 0 = 1 := by
    rw [coeff_expand (by decide : 0 < 2)]
    simp [B_constant_one]
  obtain ⟨j,hj⟩ := positive_int_dvd_two_power _ (binary_eval_pos _ hb h0 3 (by norm_num)) k hd
  have hm : (expand ℤ 2 (B h)).map (Int.castRingHom (ZMod 2)) = (X+1)^(2*h) := by
    rw [map_expand,map_B,expand_binomial_power_two]
  rcases binary_binomial_mod_two_power_classification _ hb (2*h) j hm hj with hh | hh
  · exact hh
  · have hc := congrArg (fun p : ℤ[X] => p.coeff 1) hh
    change (expand ℤ 2 (B h)).coeff 1 = (X+1 : ℤ[X]).coeff 1 at hc
    norm_num [coeff_expand (by decide : 0 < 2),coeff_add,coeff_X,coeff_one] at hc

lemma binary_four_interleave (A B C D : ℤ[X])
    (hA : Binary A) (hB : Binary B) (hC : Binary C) (hD : Binary D) :
    Binary (expand ℤ 4 A+X*expand ℤ 4 B+X^2*expand ℤ 4 C+X^3*expand ℤ 4 D) := by
  have hh := binary_interleave _ _ (binary_interleave A C hA hC) (binary_interleave B D hB hD)
  have he : expand ℤ 2 (expand ℤ 2 A+X*expand ℤ 2 C)+
      X*expand ℤ 2 (expand ℤ 2 B+X*expand ℤ 2 D) =
      expand ℤ 4 A+X*expand ℤ 4 B+X^2*expand ℤ 4 C+X^3*expand ℤ 4 D := by
    simp only [map_add,map_mul,expand_X,expand_expand]
    norm_num
    ring
  rwa [he] at hh

lemma expand_binomial_power_four (n : ℕ) :
    expand (ZMod 2) 4 ((X+1)^n) = (X+1)^(4*n) := by
  rw [show 4 = 2*2 from rfl,expand_mul,expand_binomial_power_two,expand_binomial_power_two]
  congr 1
  omega

lemma mod_two_X_add_one_square : (X+1 : (ZMod 2)[X])^2 = X^2+1 := by
  have hh := expand_binomial_power_two 1
  simpa using hh.symm

lemma mod_two_X_add_one_fourth : (X+1 : (ZMod 2)[X])^4 = X^4+1 := by
  have hh := expand_binomial_power_four 1
  simpa using hh.symm

lemma cubic_even_lift (P : ℤ[X]) (hP : Binary P) (s : ℕ)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^(2*s)*(X^3+X+1)) :
    P = expand ℤ 2 (B s)+X*expand ℤ 2 (B (s+1)) := by
  apply binary_map_two_injective _ _ hP
    (binary_interleave _ _ (binary_B _) (binary_B _))
  rw [hm,Polynomial.map_add,Polynomial.map_mul,map_X,map_expand,map_expand,
    map_B,map_B,expand_binomial_power_two,expand_binomial_power_two]
  rw [show 2*(s+1) = 2*s+2 by omega,pow_add,mod_two_X_add_one_square]
  ring

lemma cubic_one_mod_four_lift (P : ℤ[X]) (hP : Binary P) (u : ℕ)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^(4*u+1)*(X^3+X+1)) :
    P = expand ℤ 4 (B (u+1))+(X^2+X^3)*expand ℤ 4 (B u) := by
  have hb : Binary (expand ℤ 4 (B (u+1))+(X^2+X^3)*expand ℤ 4 (B u)) := by
    have hh := binary_four_interleave (B (u+1)) 0 (B u) (B u) (binary_B _)
      (fun i => Or.inl (by simp)) (binary_B _) (binary_B _)
    convert hh using 1
    simp only [map_zero,mul_zero,add_zero]
    ring
  apply binary_map_two_injective _ _ hP hb
  rw [hm,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_add,
    Polynomial.map_pow,Polynomial.map_pow,map_X,map_expand,map_expand,map_B,map_B,
    expand_binomial_power_four,expand_binomial_power_four]
  rw [show 4*(u+1) = 4*u+4 by omega,pow_succ',pow_add,mod_two_X_add_one_fourth]
  have hc : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
  calc
    _ = (X+1)^(4*u)*(X^4+X^3+X^2+1+2*X) := by ring
    _ = _ := by rw [hc]; ring

noncomputable def oddMask : ℤ[X] := 1+X^3+X^5+X^6

lemma oddMask_factorization : oddMask = (X+1)*(X^2+1)*(X^3-X+1) := by
  unfold oddMask
  ring

lemma binary_oddMask_expand_four (Q : ℤ[X]) (hQ : Binary Q) :
    Binary (oddMask*expand ℤ 4 Q) := by
  have hh := binary_four_interleave Q (X*Q) (X*Q) Q hQ
    (binary_X_mul Q hQ) (binary_X_mul Q hQ) hQ
  have he : oddMask*expand ℤ 4 Q =
      expand ℤ 4 Q+X*expand ℤ 4 (X*Q)+X^2*expand ℤ 4 (X*Q)+X^3*expand ℤ 4 Q := by
    rw [map_mul,expand_X]
    unfold oddMask
    ring
  rwa [he]

lemma cubic_three_mod_four_lift (P : ℤ[X]) (hP : Binary P) (u : ℕ)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^(4*u+3)*(X^3+X+1)) :
    P = oddMask*expand ℤ 4 (B u) := by
  apply binary_map_two_injective _ _ hP (binary_oddMask_expand_four _ (binary_B _))
  rw [hm,Polynomial.map_mul,map_expand,map_B,expand_binomial_power_four,pow_add]
  have hc : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
  have hf : (X+1 : (ZMod 2)[X])^3*(X^3+X+1) =
      1+X^3+X^5+X^6 := by
    calc
      _ = 1+X^3+X^5+X^6+2*(X^5+2*X^4+2*X^3+3*X^2+2*X) := by ring
      _ = _ := by rw [hc]; ring
  rw [mul_assoc,hf]
  simp only [oddMask,Polynomial.map_add,Polynomial.map_one,Polynomial.map_pow,map_X]
  ring

noncomputable def evenCore (m : ℕ) : ℤ[X] := expand ℤ 2 (G m)+X*(X^(2*m)+1)
noncomputable def oneCore (m : ℕ) : ℤ[X] := 1+X^(4*m)+(X^2+X^3)*expand ℤ 4 (G m)

def evenValue (m : ℕ) : ℕ := (∑ i ∈ Finset.range m, 3^(2*i))+3*(3^(2*m)+1)
def oneValue (m : ℕ) : ℕ := 1+3^(4*m)+36*(∑ i ∈ Finset.range m, 3^(4*i))

lemma evenCore_eval (m : ℕ) : (evenCore m).eval 3 = (evenValue m : ℕ) := by
  simp only [evenCore,evenValue,eval_add,eval_mul,eval_X,eval_pow,eval_one,
    expand_eval,G,eval_finset_sum]
  push_cast
  norm_num [pow_mul]

lemma oneCore_eval (m : ℕ) : (oneCore m).eval 3 = (oneValue m : ℕ) := by
  simp only [oneCore,oneValue,eval_add,eval_mul,eval_X,eval_pow,eval_one,
    expand_eval,G,eval_finset_sum]
  push_cast
  norm_num
  norm_num [pow_mul]

lemma evenValue_gt_two (m : ℕ) : 2 < evenValue m := by
  have hh : 0 < (3 : ℕ)^(2*m) := by positivity
  unfold evenValue
  omega

lemma oneValue_gt_two (m : ℕ) (hm : 0 < m) : 2 < oneValue m := by
  have hh : 3 ≤ (3 : ℕ)^(4*m) := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 3) (by omega : 1 ≤ 4*m)
  unfold oneValue
  omega

lemma evenValue_mod_four (m : ℕ) : evenValue m % 4 = (m+6)%4 := by
  have hs : (∑ i ∈ Finset.range m, (3 : ℕ)^(2*i))%4 = m%4 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ,Nat.add_mod,ih,three_even_pow_mod_four]
      omega
  simp [evenValue,Nat.add_mod,Nat.mul_mod,hs,three_even_pow_mod_four]

lemma oneValue_mod_four (m : ℕ) : oneValue m % 4 = 2 := by
  have hp : (3^(4*m) : ℕ)%4 = 1 := by
    rw [pow_mul,Nat.pow_mod]
    norm_num
  simp [oneValue,Nat.add_mod,Nat.mul_mod,hp]

lemma dvd_two_pow_gt_two_mod_four (n k : ℕ) (hn : 2 < n) (hd : n ∣ 2^k) : n%4 = 0 := by
  obtain ⟨j,_,hj⟩ := Nat.dvd_prime_pow Nat.prime_two |>.mp hd
  have hj2 : 2 ≤ j := by
    by_contra hh
    interval_cases j <;> norm_num at hj <;> omega
  rw [hj]
  exact Nat.mod_eq_zero_of_dvd (show 2^2 ∣ 2^j from Nat.pow_dvd_pow 2 hj2)

lemma evenCore_power_divisor (t k : ℕ) (hd : (evenCore (2^t)).eval 3 ∣ (2 : ℤ)^k) : t = 1 := by
  rw [evenCore_eval] at hd
  have hn : evenValue (2^t) ∣ 2^k := by exact_mod_cast hd
  have hm := dvd_two_pow_gt_two_mod_four _ k (evenValue_gt_two _) hn
  rw [evenValue_mod_four] at hm
  by_cases ht0 : t = 0
  · subst t
    norm_num at hm
  by_contra ht1
  have hd4 : 4 ∣ 2^t := show 2^2 ∣ 2^t from Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd hd4] at hm
  norm_num at hm

lemma oneCore_not_power_divisor (t k : ℕ) : ¬ (oneCore (2^t)).eval 3 ∣ (2 : ℤ)^k := by
  intro hd
  rw [oneCore_eval] at hd
  have hn : oneValue (2^t) ∣ 2^k := by exact_mod_cast hd
  have hm := dvd_two_pow_gt_two_mod_four _ k (oneValue_gt_two _ (by positivity)) hn
  rw [oneValue_mod_four] at hm
  contradiction

lemma evenCore_two : evenCore 2 = 1+X+X^2+X^5 := by
  simp [evenCore,G,Finset.sum_range_succ]
  ring

/-- The restricted cubic family contains exactly the known digit polynomial
of 256, if its value at three is a power of two. No restriction on a is needed. -/
theorem cubic_mod_two_classification (P : ℤ[X]) (hP : Binary P) (a k : ℕ)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*(X^3+X+1))
    (he : P.eval 3 = (2 : ℤ)^k) : P = 1+X+X^2+X^5 := by
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
    have hdH : (expand ℤ 2 (B h)).eval 3 ∣ (2 : ℤ)^k := by
      rw [← he,hp,eval_mul]
      exact dvd_mul_right _ _
    have hH := pascal_even_expansion_power_divisor h k hdH
    rw [hH,one_mul] at hp
    have hdC : (evenCore (2^t)).eval 3 ∣ (2 : ℤ)^k := by rw [← hp,he]
    have ht := evenCore_power_divisor t k hdC
    rw [ht,pow_one,evenCore_two] at hp
    exact hp
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
    apply oneCore_not_power_divisor t k
    rw [← he,hp,eval_mul]
    exact dvd_mul_left _ _
  · let u := a/4
    have hau : a = 4*u+3 := by dsimp [u]; omega
    rw [hau] at hm
    have hp := cubic_three_mod_four_lift P hP u hm
    have hd : (X^2+1 : ℤ[X]) ∣ P := by
      refine ⟨(X+1)*(X^3-X+1)*expand ℤ 4 (B u),?_⟩
      rw [hp,oddMask_factorization]
      ring
    have hv := eval_dvd (x := (3 : ℤ)) hd
    rw [he] at hv
    have hn : 3^2+1 ∣ 2^k := by
      norm_num only [eval_add,eval_pow,eval_X,eval_one] at hv
      exact_mod_cast hv
    have hh := Erdos406Structure.three_pow_add_one_dvd_two_pow (by decide : 0 < 2) hn
    contradiction

/-- Direct classification of the original candidates in this one restricted
family. Arbitrary nonsplit reductions remain outside the theorem's scope. -/
theorem candidate_cubic_mod_two_classification (n : ℕ) (hn : n.isPowerOfTwo)
    (hg : Nat.digits 3 n ⊆ [0,1]) (a : ℕ)
    (hm : (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) =
      (X+1)^a*(X^3+X+1)) : n = 256 := by
  obtain ⟨k,rfl⟩ := hn
  have he : (digitPoly (Nat.digits 3 (2^k))).eval 3 = (2 : ℤ)^k := by
    rw [digitPoly_eval_three]
    norm_cast
  have hh := cubic_mod_two_classification _ (binary_digitPoly _ hg) a k hm he
  have hv := congrArg (eval (3 : ℤ)) hh
  rw [digitPoly_eval_three] at hv
  norm_num at hv
  exact_mod_cast hv

#print axioms consecutive_B_normalized
#print axioms cubic_mod_two_classification
#print axioms candidate_cubic_mod_two_classification
end Erdos406ModTwoCubic
