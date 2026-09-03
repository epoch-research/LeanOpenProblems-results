import Submission.NewmanFixedResidualTools
import Submission.AffineDyadicTowerFiniteness

/-! Finiteness in a single fixed residual family over F₂. The residual
polynomial is fixed throughout; allowing it to vary remains uncontrolled. -/
namespace Erdos406FixedResidual
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoBinomial
  Erdos406ModTwoQuadratic Erdos406ModTwoFrobenius Erdos406FixedResidualTools
  Erdos406AffineTower Erdos406Cyclotomic Erdos406ReciprocalCandidate

lemma binomial_frobenius (r : ℕ) :
    (X+1 : (ZMod 2)[X])^(2^r) = X^(2^r)+1 := by
  simpa using add_pow_expChar_pow (X : (ZMod 2)[X]) 1 2 r

lemma binomial_residual_degree (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) (a : ℕ) :
    ((X+1)^a*R).natDegree = a+R.natDegree := by
  have hx : (X+1 : (ZMod 2)[X]) ≠ 0 := by simpa using X_add_C_ne_zero (1 : ZMod 2)
  have hxd : (X+1 : (ZMod 2)[X]).natDegree = 1 := by
    simpa using natDegree_X_add_C (1 : ZMod 2)
  rw [natDegree_mul (pow_ne_zero _ hx) (residual_ne_zero R hR),natDegree_pow,hxd,mul_one]

/-- Except for a=0,1, a candidate's linear multiplicity lies within the
residual degree below the next dyadic boundary. -/
lemma near_dyadic_boundary (P : ℤ[X]) (hP : Binary P) (R : (ZMod 2)[X])
    (hR : R.coeff 0 = 1) (a k : ℕ) (ha : 2 ≤ a)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R)
    (he : P.eval 3 = (2 : ℤ)^k) :
    ∃ r : ℕ, a < 2^r ∧ 2^r ≤ a+R.natDegree := by
  let s := a.log2
  let u := a-2^s
  have hpow : 2^s ≤ a := Nat.log2_self_le (by omega)
  have htop : a < 2^(s+1) := (Nat.log2_lt (by omega : a ≠ 0)).mp (by dsimp [s]; omega)
  have hau : a = 2^s+u := by dsimp [u]; omega
  refine ⟨s+1,htop,?_⟩
  by_contra hb
  have hgap : u+R.natDegree < 2^s := by
    rw [pow_succ] at hb
    omega
  have hmap : P.map (Int.castRingHom (ZMod 2)) =
      (X^(2^s)+1)*((X+1)^u*R) := by
    rw [hm,hau,pow_add,binomial_frobenius,mul_assoc]
  have hshape := separated_binomial_lift P hP ((X+1)^u*R) (2^s)
    (by rwa [binomial_residual_degree R hR u]) hmap
  have hd : 3^(2^s)+1 ∣ 2^k := by
    have hdz : ((3 : ℤ)^(2^s)+1) ∣ (2 : ℤ)^k := by
      rw [← he,hshape,eval_mul,eval_add,eval_pow,eval_X,eval_one]
      exact dvd_mul_right _ _
    exact_mod_cast hdz
  have hh := Erdos406Structure.three_pow_add_one_dvd_two_pow
    (by positivity : 0 < 2^s) hd
  rw [pow_succ,hh] at htop
  omega

lemma shifted_residual_map (P : ℤ[X]) (R : (ZMod 2)[X]) (a s r : ℕ)
    (hlo : 2^r ≤ a+2^s)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R) :
    ((X^(2^s)-1)*P).map (Int.castRingHom (ZMod 2)) =
      (X^(2^r)+1)*((X+1)^(a+2^s-2^r)*R) := by
  have hminus : (X^(2^s)-1 : (ZMod 2)[X]) = (X+1)^(2^s) := by
    rw [binomial_frobenius]
    have hc : (2 : (ZMod 2)[X]) = 0 := CharP.cast_eq_zero _ 2
    linear_combination -hc
  rw [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_pow,map_X,
    Polynomial.map_one,hminus,hm,← mul_assoc,← pow_add,
    show 2^s+a = 2^r+(a+2^s-2^r) by omega,pow_add,binomial_frobenius,mul_assoc]

/-- A large candidate in a fixed residual family yields a bounded pair of
integer end values and a fixed-coefficient affine dyadic-tower equation. -/
lemma bounded_affine_representation (P : ℤ[X]) (hP : Binary P) (R : (ZMod 2)[X])
    (hR : R.coeff 0 = 1) (a k s r : ℕ) (hD : R.natDegree ≤ 2^s)
    (hlo : a < 2^r) (hhi : 2^r ≤ a+R.natDegree) (hlarge : 2*2^s ≤ 2^r)
    (hm : P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R)
    (he : P.eval 3 = (2 : ℤ)^k) :
    ∃ A B : ℤ, A ≠ 0 ∧ |A| ≤ endBound (2*2^s) ∧ |B| ≤ endBound (2*2^s) ∧
      (3^(2^s)-1)*2^k = A*3^(2^r)+B := by
  let T := 2^s
  let N := 2^r
  let K := 2*T
  let F : ℤ[X] := (X^T-1)*P
  let S : (ZMod 2)[X] := (X+1)^(a+T-N)*R
  have hKN : K ≤ N := hlarge
  have hDS : S.natDegree < K := by
    dsimp [S]
    rw [binomial_residual_degree R hR]
    dsimp [K,T,N] at *
    omega
  have hmF : F.map (Int.castRingHom (ZMod 2)) = (X^N+1)*S :=
    shifted_residual_map P R a s r (by omega) hm
  have hdegP : P.natDegree = a+R.natDegree := residual_degree P hP R hR a hm
  have hdegF : F.natDegree < N+K := by
    have hb := natDegree_mul_le (p := (X^T-1 : ℤ[X])) (q := P)
    have hdt : (X^T-1 : ℤ[X]).natDegree = T := by
      simpa using (natDegree_X_pow_sub_C (R := ℤ) (n := T) (r := 1))
    rw [hdt,hdegP] at hb
    dsimp [F]
    dsimp [K,T,N] at *
    omega
  have hzero : ∀ i, K ≤ i → i < N → F.coeff i = 0 := by
    intro i hi hiN
    exact middle_coeff_zero P hP S T N K i hDS hi hiN hmF
  have hdecomp := eval_eq_endValues F N K hKN hdegF hzero
  have hbF : ∀ i, |F.coeff i| ≤ 1 := shifted_binary_difference_bound P hP T
  have hA := endValue_bound F N K hbF
  have hB := endValue_bound F 0 K hbF
  have hfe : F.eval 3 = (3^T-1)*P.eval 3 := by simp [F]
  have hnz : P ≠ 0 := by
    intro hh
    rw [hh,eval_zero] at he
    have : (0 : ℤ) < 2^k := by positivity
    omega
  have hPe : (3 : ℤ)^N ≤ P.eval 3 := binary_eval_lower_bound P hP hnz N (by omega)
  have hC : (1 : ℤ) ≤ 3^T-1 := by
    have ht : 1 ≤ T := Nat.one_le_pow _ _ (by decide)
    have hh : (3 : ℤ)^1 ≤ 3^T := pow_le_pow_right₀ (by decide) ht
    norm_num at hh
    omega
  have hAnz : endValue F N K ≠ 0 := by
    intro hh
    rw [hh,mul_zero,add_zero,hfe] at hdecomp
    have hsmall : endValue F 0 K < P.eval 3 := calc
      _ ≤ |endValue F 0 K| := le_abs_self _
      _ ≤ endBound K := hB
      _ < (3 : ℤ)^K := endBound_lt K
      _ ≤ 3^N := pow_le_pow_right₀ (by decide) hKN
      _ ≤ P.eval 3 := hPe
    have hpos : (0 : ℤ) < P.eval 3 := by rw [he]; positivity
    nlinarith
  refine ⟨endValue F N K,endValue F 0 K,hAnz,hA,hB,?_⟩
  rw [hfe,he] at hdecomp
  dsimp [K,T,N] at hdecomp ⊢
  linarith


def boundedTowerIndices (C W : ℤ) : Set ℕ :=
  {r | ∃ A B : ℤ, A ≠ 0 ∧ |A| ≤ W ∧ |B| ≤ W ∧
    ∃ k : ℕ, C*2^k = A*3^(2^r)+B}

lemma finite_bounded_tower_indices (C W : ℤ) (hC : C ≠ 0) :
    (boundedTowerIndices C W).Finite := by
  let As : Set ℤ := {A | |A| ≤ W ∧ A ≠ 0}
  have hAs : As.Finite := (Set.finite_Icc (-W) W).subset (by
    intro A hA
    exact abs_le.mp hA.1)
  have hf := hAs.biUnion (fun A hA => (Set.finite_Icc (-W) W).biUnion
    (fun B _ => finite_affine_dyadic_tower A B C hA.2 hC))
  apply hf.subset
  rintro r ⟨A,B,hAnz,hA,hB,k,he⟩
  exact Set.mem_iUnion.mpr ⟨A,Set.mem_iUnion.mpr ⟨⟨hA,hAnz⟩,
    Set.mem_iUnion.mpr ⟨B,Set.mem_iUnion.mpr ⟨abs_le.mp hB,⟨k,he⟩⟩⟩⟩⟩

def ResidualExponents (R : (ZMod 2)[X]) : Set ℕ :=
  {a | ∃ P : ℤ[X], Binary P ∧ P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R ∧
    ∃ k : ℕ, P.eval 3 = (2 : ℤ)^k}

/-- The linear multiplicity has only finitely many possible values when
all other factors of the reduction modulo two are fixed. -/
theorem finite_residual_exponents (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) :
    (ResidualExponents R).Finite := by
  let s := R.natDegree
  let C : ℤ := 3^(2^s)-1
  let W := endBound (2*2^s)
  have hD : R.natDegree ≤ 2^s := Nat.le_of_lt Nat.lt_two_pow_self
  have hT : 1 ≤ 2^s := Nat.one_le_pow _ _ (by decide)
  have hC : C ≠ 0 := by
    have hh : (3 : ℤ)^1 ≤ 3^(2^s) := pow_le_pow_right₀ (by decide) hT
    dsimp [C]
    norm_num at hh
    omega
  have hf := (Set.finite_lt_nat (2*2^s)).union
    ((finite_bounded_tower_indices C W hC).biUnion
      (fun r _ => Set.finite_lt_nat (2^r)))
  apply hf.subset
  rintro a ⟨P,hP,hm,k,he⟩
  by_cases ha : a < 2*2^s
  · exact Or.inl ha
  right
  obtain ⟨r,hlo,hhi⟩ := near_dyadic_boundary P hP R hR a k (by omega) hm he
  obtain ⟨A,B,hAnz,hA,hB,hE⟩ := bounded_affine_representation P hP R hR a k s r
    hD hlo hhi (by omega) hm he
  have hr : r ∈ boundedTowerIndices C W := ⟨A,B,hAnz,hA,hB,k,hE⟩
  exact Set.mem_iUnion.mpr ⟨r,Set.mem_iUnion.mpr ⟨hr,hlo⟩⟩

/-- Finiteness of binary polynomials of pure-power value in one fixed
residual family. This is not finiteness of the union over all residuals. -/
theorem finite_binary_fixed_residual (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) :
    {P : ℤ[X] | Binary P ∧ ∃ a : ℕ,
      P.map (Int.castRingHom (ZMod 2)) = (X+1)^a*R ∧
      ∃ k : ℕ, P.eval 3 = (2 : ℤ)^k}.Finite := by
  apply ((finite_residual_exponents R hR).image
    (fun a => liftTwo ((X+1)^a*R))).subset
  rintro P ⟨hP,a,hm,k,he⟩
  refine ⟨a,⟨P,hP,hm,k,he⟩,?_⟩
  exact (binary_map_two_injective _ _ hP (binary_liftTwo _)
    (hm.trans (map_liftTwo _).symm)).symm

/-- Direct fixed-residual finiteness for the natural-number candidates. -/
theorem finite_candidates_fixed_residual (R : (ZMod 2)[X]) (hR : R.coeff 0 = 1) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1] ∧ ∃ a : ℕ,
      (digitPoly (Nat.digits 3 n)).map (Int.castRingHom (ZMod 2)) =
        (X+1)^a*R}.Finite := by
  apply ((finite_binary_fixed_residual R hR).image (fun P => (P.eval 3).natAbs)).subset
  rintro n ⟨⟨k,rfl⟩,hg,a,hm⟩
  have he : (digitPoly (Nat.digits 3 (2^k))).eval 3 = (2 : ℤ)^k := by
    rw [digitPoly_eval_three]
    norm_cast
  refine ⟨digitPoly (Nat.digits 3 (2^k)),⟨binary_digitPoly _ hg,a,hm,k,he⟩,?_⟩
  change ((digitPoly (Nat.digits 3 (2^k))).eval 3).natAbs = 2^k
  rw [he]
  simp

#print axioms near_dyadic_boundary
#print axioms bounded_affine_representation
#print axioms finite_residual_exponents
#print axioms finite_binary_fixed_residual
#print axioms finite_candidates_fixed_residual
end Erdos406FixedResidual
