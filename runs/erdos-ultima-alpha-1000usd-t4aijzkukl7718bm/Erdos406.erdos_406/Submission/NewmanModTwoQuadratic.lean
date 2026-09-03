import Submission.NewmanModTwoBinomial

/-! An all-degree exclusion for a restricted nonsplit reduction modulo two.
The quadratic factor multiplicity is required to be a power of two. This does not classify
arbitrary candidate reductions and does not settle Erdős 406. -/
namespace Erdos406ModTwoQuadratic
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoBinomial Erdos406Cyclotomic
  Erdos406ReciprocalCandidate

noncomputable def B (n : ℕ) : ℤ[X] := (exists_binary_binomial_lift n).choose

lemma binary_B (n : ℕ) : Binary (B n) :=
  (exists_binary_binomial_lift n).choose_spec.choose_spec.1

lemma map_B (n : ℕ) : (B n).map (Int.castRingHom (ZMod 2)) = (X+1)^n :=
  (exists_binary_binomial_lift n).choose_spec.choose_spec.2.1

lemma B_zero : B 0 = 1 := by
  apply binary_map_two_injective _ _ (binary_B 0)
  · intro i
    by_cases hi : i = 0 <;> simp [coeff_one, hi]
  · rw [map_B]
    simp

lemma B_even (n : ℕ) : B (2*n) = expand ℤ 2 (B n) := by
  apply binary_map_two_injective _ _ (binary_B _) (binary_expand_two _ (binary_B n))
  rw [map_B, map_expand, map_B, expand_binomial_power_two]

lemma B_odd (n : ℕ) : B (2*n+1) = (X+1)*expand ℤ 2 (B n) := by
  apply binary_map_two_injective _ _ (binary_B _) (binary_interlace _ (binary_B n))
  rw [map_B, Polynomial.map_mul, Polynomial.map_add, map_X, Polynomial.map_one,
    map_expand, map_B, expand_binomial_power_two, pow_succ']

noncomputable def G (m : ℕ) : ℤ[X] := ∑ i ∈ Finset.range m, X^i

lemma G_one : G 1 = 1 := by simp [G]

lemma G_double (m : ℕ) : G (2*m) = (X+1)*expand ℤ 2 (G m) := by
  apply mul_right_cancel₀ (show (X-1 : ℤ[X]) ≠ 0 by exact X_sub_C_ne_zero 1)
  have hh := congrArg (expand ℤ 2) (geom_sum_mul (X : ℤ[X]) m)
  change expand ℤ 2 (G m * (X-1)) = expand ℤ 2 (X^m-1) at hh
  simp only [map_mul, map_sub, expand_X, map_one, map_pow, ← pow_mul] at hh
  calc
    _ = X^(2*m)-1 := geom_sum_mul X (2*m)
    _ = expand ℤ 2 (G m)*(X^2-1) := hh.symm
    _ = _ := by ring

/-- Consecutive binary Pascal patterns share all their high-bit factors.
Only the run of trailing binary ones changes. -/
lemma consecutive_B (n : ℕ) : ∃ t : ℕ, ∃ H : ℤ[X],
    B n = H*G (2^t) ∧ B (n+1) = H*(X^(2^t)+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd n with ⟨u,hu⟩ | ⟨u,hu⟩
    · have hn : n = 2*u := by omega
      rw [hn]
      refine ⟨0,expand ℤ 2 (B u),?_,?_⟩
      · rw [pow_zero, G_one, mul_one, B_even]
      · rw [B_odd, pow_zero, pow_one, mul_comm]
    · have hn : n = 2*u+1 := by omega
      obtain ⟨t,H,hA,hC⟩ := ih u (by omega)
      rw [hn]
      refine ⟨t+1,expand ℤ 2 H,?_,?_⟩
      · rw [B_odd, hA, map_mul, pow_succ', G_double]
        ring
      · rw [show 2*u+1+1 = 2*(u+1) by omega, B_even, hC,
          map_mul, map_add, map_pow, expand_X, map_one, ← pow_mul, pow_succ']

lemma binary_X_mul (P : ℤ[X]) (hP : Binary P) : Binary (X*P) := by
  intro i
  cases i with
  | zero => simp
  | succ i => simpa only [coeff_X_mul] using hP i

lemma binary_interleave (P Q : ℤ[X]) (hP : Binary P) (hQ : Binary Q) :
    Binary (expand ℤ 2 P + X*expand ℤ 2 Q) := by
  intro i
  rw [coeff_add]
  cases i with
  | zero => simpa only [coeff_X_mul_zero, add_zero, coeff_expand (by decide : 0 < 2),
      dvd_zero, if_true, Nat.zero_div] using hP 0
  | succ i =>
    rw [coeff_X_mul]
    simp only [coeff_expand (by decide : 0 < 2), Nat.dvd_iff_mod_eq_zero]
    split_ifs with h₁ h₂
    · omega
    · simpa using hP ((i+1)/2)
    · simpa using hQ (i/2)
    · simp

noncomputable def core (m : ℕ) : ℤ[X] := X^(2*m)+1+X*expand ℤ 2 (G m)

def coreValue (x m : ℕ) : ℕ := x^(2*m)+1+x*∑ i ∈ Finset.range m, x^(2*i)

lemma core_eval (x m : ℕ) : (core m).eval (x : ℤ) = (coreValue x m : ℕ) := by
  simp only [core, coreValue, eval_add, eval_pow, eval_X, eval_one, eval_mul,
    expand_eval, G, eval_finset_sum]
  push_cast
  simp only [← pow_mul]

lemma coreValue_gt_two (x m : ℕ) (hx : 3 ≤ x) (hm : 0 < m) : 2 < coreValue x m := by
  have hh : x ≤ x^(2*m) := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ x) (by omega : 1 ≤ 2*m)
  unfold coreValue
  omega

lemma coreValue_two (x : ℕ) : coreValue x 2 = (x+1)*(x^3+1) := by
  simp [coreValue, Finset.sum_range_succ]
  ring

lemma three_even_pow_mod_four (j : ℕ) : (3^(2*j) : ℕ) % 4 = 1 := by
  rw [pow_mul, Nat.pow_mod]
  norm_num

lemma coreValue_three_mod_four (L m : ℕ) :
    coreValue (3^L) m % 4 = (2+3^L*m) % 4 := by
  have hp (i : ℕ) : ((3^L)^(2*i) : ℕ) % 4 = 1 := by
    rw [← pow_mul, show L*(2*i) = 2*(L*i) by ring]
    exact three_even_pow_mod_four _
  have hs : (∑ i ∈ Finset.range m, (3^L)^(2*i)) % 4 = m % 4 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih, hp]
      omega
  simp [coreValue, Nat.add_mod, Nat.mul_mod, hp, hs]

/-- Every exceptional low-bit core has an odd divisor; in particular, it
cannot divide a power of two, at any positive power-of-three input. -/
lemma coreValue_not_dvd_two_power (L t k : ℕ) (hL : 0 < L) :
    ¬ coreValue (3^L) (2^t) ∣ 2^k := by
  intro hd
  have hx : 3 ≤ 3^L := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ 3) hL
  have hlarge := coreValue_gt_two (3^L) (2^t) hx (by positivity)
  obtain ⟨j,_,hj⟩ := Nat.dvd_prime_pow Nat.prime_two |>.mp hd
  have hj2 : 2 ≤ j := by
    by_contra hh
    interval_cases j <;> norm_num at hj <;> omega
  have hmod : coreValue (3^L) (2^t) % 4 = 0 := by
    rw [hj]
    exact Nat.mod_eq_zero_of_dvd (show 2^2 ∣ 2^j from Nat.pow_dvd_pow 2 hj2)
  by_cases ht0 : t = 0
  · subst t
    have hodd : coreValue (3^L) 1 % 2 = 1 := by
      have hxodd : (3^L : ℕ) % 2 = 1 := by rw [Nat.pow_mod]; norm_num
      simp [coreValue, Nat.add_mod, Nat.pow_mod, hxodd]
    have hdiv2 : 2 ∣ coreValue (3^L) 1 := by
      simpa using dvd_trans (by decide : 2 ∣ 4) (Nat.dvd_of_mod_eq_zero hmod)
    omega
  by_cases ht1 : t = 1
  · subst t
    have hd3 : 3^(3*L)+1 ∣ coreValue (3^L) (2^1) := by
      norm_num only [pow_one]
      rw [coreValue_two, ← pow_mul, Nat.mul_comm L 3]
      exact dvd_mul_left _ _
    have hh := Erdos406Structure.three_pow_add_one_dvd_two_pow (by omega : 0 < 3*L)
      (hd3.trans hd)
    omega
  have ht : 4 ∣ 2^t := show 2^2 ∣ 2^t from Nat.pow_dvd_pow 2 (by omega)
  rw [coreValue_three_mod_four, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd ht] at hmod
  norm_num at hmod

lemma core_not_dvd_two_power (L t k : ℕ) (hL : 0 < L) :
    ¬ (core (2^t)).eval ((3 : ℤ)^L) ∣ (2 : ℤ)^k := by
  intro hd
  have hd' : (coreValue (3^L) (2^t) : ℤ) ∣ (2 : ℤ)^k := by
    convert hd using 1
    norm_cast
    rw [core_eval]
  apply coreValue_not_dvd_two_power L t k hL
  exact_mod_cast hd'

lemma quadratic_even_lift (P : ℤ[X]) (hP : Binary P) (s : ℕ)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^(2*s)*(X^2+X+1)) :
    P = expand ℤ 2 (B (s+1)) + X*expand ℤ 2 (B s) := by
  apply binary_map_two_injective _ _ hP
    (binary_interleave _ _ (binary_B _) (binary_B _))
  rw [hm, Polynomial.map_add, Polynomial.map_mul, map_X, map_expand, map_expand,
    map_B, map_B, expand_binomial_power_two, expand_binomial_power_two]
  rw [show 2*(s+1) = 2*s+2 by omega, pow_add]
  have hc : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
  have hs : (X+1 : (ZMod 2)[X])^2 = X^2+1 := by
    calc
      _ = X^2+2*X+1 := by ring
      _ = _ := by rw [hc]; ring
  rw [hs]
  ring

lemma quadratic_odd_lift (P : ℤ[X]) (hP : Binary P) (s : ℕ)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^(2*s+1)*(X^2+X+1)) :
    P = (X^3+1)*expand ℤ 2 (B s) := by
  have he : (X^3+1)*expand ℤ 2 (B s) =
      expand ℤ 2 (B s)+X*expand ℤ 2 (X*B s) := by
    rw [map_mul, expand_X]
    ring
  apply binary_map_two_injective _ _ hP
  · rw [he]
    exact binary_interleave _ _ (binary_B _) (binary_X_mul _ (binary_B _))
  · rw [hm, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow, map_X,
      Polynomial.map_one, map_expand, map_B, expand_binomial_power_two, pow_succ']
    have hc : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
    calc
      _ = (X^3+1+2*(X^2+X))*(X+1)^(2*s) := by ring
      _ = _ := by rw [hc]; ring

/-- Nonsplit quadratic reduction with multiplicity one cannot occur in a
candidate, irrespective of the multiplicity of the linear factor. -/
theorem quadratic_mod_two_exclusion (P : ℤ[X]) (hP : Binary P) (a L k : ℕ)
    (hL : 0 < L)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*(X^2+X+1)) :
    P.eval ((3 : ℤ)^L) ≠ (2 : ℤ)^k := by
  intro he
  rcases Nat.even_or_odd a with ⟨s,hs⟩ | ⟨s,hs⟩
  · have ha : a = 2*s := by omega
    rw [ha] at hm
    rw [quadratic_even_lift P hP s hm] at he
    obtain ⟨t,H,hA,hC⟩ := consecutive_B s
    have hp : expand ℤ 2 (B (s+1)) + X*expand ℤ 2 (B s) =
        expand ℤ 2 H * core (2^t) := by
      rw [hA,hC,map_mul,map_mul,map_add,map_pow,expand_X,map_one,← pow_mul]
      unfold core
      ring
    rw [hp,eval_mul] at he
    exact core_not_dvd_two_power L t k hL ⟨(expand ℤ 2 H).eval ((3 : ℤ)^L), by
      rw [← he]
      ring⟩
  · have ha : a = 2*s+1 := by omega
    rw [ha] at hm
    have hd : (X^3+1 : ℤ[X]) ∣ P := ⟨expand ℤ 2 (B s),quadratic_odd_lift P hP s hm⟩
    have hv := eval_dvd (x := (3 : ℤ)^L) hd
    rw [he] at hv
    have hn : 3^(3*L)+1 ∣ 2^k := by
      norm_num only [eval_add, eval_pow, eval_X, eval_one] at hv
      rw [← pow_mul, Nat.mul_comm L 3] at hv
      exact_mod_cast hv
    have hh := Erdos406Structure.three_pow_add_one_dvd_two_pow (by omega : 0 < 3*L) hn
    omega

/-- A direct necessary condition on the original candidate set. It does not
exclude higher quadratic multiplicities or other irreducible factors modulo two. -/
theorem candidate_quadratic_mod_two_exclusion (n : ℕ) (hn : n.isPowerOfTwo)
    (hg : Nat.digits 3 n ⊆ [0,1]) (a : ℕ) :
    (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) ≠
      (X+1)^a*(X^2+X+1) := by
  intro hm
  obtain ⟨k,rfl⟩ := hn
  apply quadratic_mod_two_exclusion _ (binary_digitPoly _ hg) a 1 k (by decide) hm
  simp only [pow_one, digitPoly_eval_three, Nat.cast_pow, Nat.cast_ofNat]

/-- The coefficientwise canonical lift, not a ring homomorphism. -/
noncomputable def liftTwo (P : (ZMod 2)[X]) : ℤ[X] :=
  Polynomial.ofFinsupp (P.toFinsupp.mapRange (fun a : ZMod 2 => (a.val : ℤ)) (by simp))

lemma coeff_liftTwo (P : (ZMod 2)[X]) (i : ℕ) :
    (liftTwo P).coeff i = ((P.coeff i).val : ℤ) := by
  simp only [liftTwo, coeff_ofFinsupp, Finsupp.mapRange_apply, toFinsupp_apply]

lemma binary_liftTwo (P : (ZMod 2)[X]) : Binary (liftTwo P) := by
  intro i
  rw [coeff_liftTwo]
  have h := ZMod.val_lt (P.coeff i)
  omega

lemma map_liftTwo (P : (ZMod 2)[X]) :
    (liftTwo P).map (Int.castRingHom (ZMod 2)) = P := by
  ext i
  rw [coeff_map, coeff_liftTwo]
  simp

lemma expand_two_eq_square (P : (ZMod 2)[X]) : expand (ZMod 2) 2 P = P^2 := by
  have hh := map_frobenius_expand 2 P
  have hf : frobenius (ZMod 2) 2 = RingHom.id (ZMod 2) := by
    ext a
    fin_cases a <;> decide
  simpa [hf] using hh

lemma binary_eval_pos (P : ℤ[X]) (hP : Binary P) (h0 : P.coeff 0 = 1)
    (x : ℤ) (hx : 0 ≤ x) : 0 < P.eval x := by
  have hnn (i : ℕ) : 0 ≤ P.coeff i * x^i := by
    have hc : 0 ≤ P.coeff i := by rcases hP i with h | h <;> simp [h]
    exact mul_nonneg hc (pow_nonneg hx _)
  have hh := Finset.single_le_sum (s := Finset.range (P.natDegree+1))
    (f := fun i => P.coeff i*x^i) (fun i _ => hnn i)
    (show 0 ∈ Finset.range (P.natDegree+1) by simp)
  change P.coeff 0*x^0 ≤ ∑ i ∈ Finset.range (P.natDegree+1), P.coeff i*x^i at hh
  rw [h0, pow_zero, mul_one, ← eval_eq_sum_range] at hh
  omega

lemma positive_int_dvd_two_power (z : ℤ) (hz : 0 < z) (k : ℕ)
    (hd : z ∣ (2 : ℤ)^k) : ∃ j : ℕ, z = (2 : ℤ)^j := by
  have hn : z.natAbs ∣ 2^k := by simpa using Int.natAbs_dvd_natAbs.mpr hd
  obtain ⟨j,_,hj⟩ := Nat.dvd_prime_pow Nat.prime_two |>.mp hn
  refine ⟨j,?_⟩
  have hh := Int.natAbs_of_nonneg hz.le
  rw [hj] at hh
  exact_mod_cast hh.symm

/-- Frobenius descent extends the exclusion to every power-of-two
multiplicity of the quadratic factor. It does not cover arbitrary positive
quadratic multiplicities. -/
theorem quadratic_two_power_mod_two_exclusion (t : ℕ) (P : ℤ[X]) (hP : Binary P)
    (a L k : ℕ) (hL : 0 < L)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*(X^2+X+1)^(2^t)) :
    P.eval ((3 : ℤ)^L) ≠ (2 : ℤ)^k := by
  induction t generalizing P a L k with
  | zero =>
    simp only [pow_zero,pow_one] at hm
    exact quadratic_mod_two_exclusion P hP a L k hL hm
  | succ t ih =>
    intro he
    let Q : ℤ[X] := liftTwo ((X+1)^(a/2)*(X^2+X+1)^(2^t))
    have hQ : Binary Q := binary_liftTwo _
    have hmQ : Q.map (Int.castRingHom (ZMod 2)) =
        (X+1)^(a/2)*(X^2+X+1)^(2^t) := map_liftTwo _
    have hQ0 : Q.coeff 0 = 1 := by
      change (liftTwo _).coeff 0 = 1
      rw [coeff_liftTwo]
      norm_num [coeff_zero_eq_eval_zero]
      decide
    have hmE : (expand ℤ 2 Q).map (Int.castRingHom (ZMod 2)) =
        (X+1)^(2*(a/2))*(X^2+X+1)^(2^(t+1)) := by
      rw [map_expand,hmQ,expand_two_eq_square,mul_pow,← pow_mul,← pow_mul]
      rw [Nat.mul_comm (a/2) 2,← pow_succ]
    have hE : Binary (expand ℤ 2 Q) := binary_expand_two Q hQ
    have hsmall : ∃ j : ℕ, Q.eval ((3 : ℤ)^(2*L)) = (2 : ℤ)^j := by
      have hdiv : Q.eval ((3 : ℤ)^(2*L)) ∣ (2 : ℤ)^k := by
        by_cases ha : a % 2 = 0
        · have hp : P = expand ℤ 2 Q := by
            apply binary_map_two_injective P _ hP hE
            rw [hm,hmE,show 2*(a/2) = a by omega]
          rw [hp,expand_eval,← pow_mul, Nat.mul_comm L 2] at he
          rw [he]
        · have hp : P = (X+1)*expand ℤ 2 Q := by
            apply binary_map_two_injective P _ hP (binary_interlace Q hQ)
            rw [hm,Polynomial.map_mul,Polynomial.map_add,map_X,Polynomial.map_one,hmE]
            conv_lhs => rw [show a = 2*(a/2)+1 by omega,pow_succ']
            ring
          rw [hp,eval_mul,expand_eval,← pow_mul,Nat.mul_comm L 2] at he
          exact ⟨(X+1 : ℤ[X]).eval ((3 : ℤ)^L), by rw [← he]; ring⟩
      exact positive_int_dvd_two_power _ (binary_eval_pos Q hQ hQ0 _ (by positivity)) k hdiv
    obtain ⟨j,hj⟩ := hsmall
    exact ih Q hQ (a/2) (2*L) j (by omega) hmQ hj

/-- This excludes a nontrivial, infinite family of nonsplit reductions, not
all nonsplit reductions. -/
theorem candidate_quadratic_two_power_mod_two_exclusion (n : ℕ) (hn : n.isPowerOfTwo)
    (hg : Nat.digits 3 n ⊆ [0,1]) (a t : ℕ) :
    (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) ≠
      (X+1)^a*(X^2+X+1)^(2^t) := by
  intro hm
  obtain ⟨k,rfl⟩ := hn
  apply quadratic_two_power_mod_two_exclusion t _ (binary_digitPoly _ hg) a 1 k
    (by decide) hm
  simp only [pow_one,digitPoly_eval_three,Nat.cast_pow,Nat.cast_ofNat]

#print axioms quadratic_two_power_mod_two_exclusion
#print axioms candidate_quadratic_two_power_mod_two_exclusion
#print axioms consecutive_B
#print axioms coreValue_not_dvd_two_power
#print axioms quadratic_mod_two_exclusion
#print axioms candidate_quadratic_mod_two_exclusion
end Erdos406ModTwoQuadratic
