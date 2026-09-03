import Submission.NewmanFixedResidual

/-! Binary block concatenation and nonnegative overlap corrections.
These are structural tools; no global candidate bound is asserted. -/
namespace Erdos406BinaryBlocks
open Polynomial Erdos406ReciprocalFlip Erdos406ModTwoBinomial
  Erdos406ModTwoQuadratic Erdos406FixedResidualTools

noncomputable def cut {A : Type*} [Semiring A] (P : A[X]) (start T : ℕ) : A[X] :=
  ∑ i ∈ Finset.range T, monomial i (P.coeff (start+i))

lemma coeff_cut {A : Type*} [Semiring A] (P : A[X]) (start T i : ℕ) :
    (cut P start T).coeff i = if i < T then P.coeff (start+i) else 0 := by
  classical
  simp [cut,finset_sum_coeff,coeff_monomial]

lemma cut_degree {A : Type*} [Semiring A] (P : A[X]) (start T : ℕ) (hT : 0 < T) :
    (cut P start T).natDegree < T := by
  have hh : (cut P start T).natDegree ≤ T-1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff_cut,if_neg (by omega)]
  omega

lemma binary_cut (P : ℤ[X]) (hP : Binary P) (start T : ℕ) : Binary (cut P start T) := by
  intro i
  rw [coeff_cut]
  split_ifs
  · exact hP _
  · exact Or.inl rfl

lemma cut_decomposition {A : Type*} [Semiring A] (P : A[X]) (T : ℕ)
    (hP : P.natDegree < 2*T) : P = cut P 0 T+X^T*cut P T T := by
  ext i
  rw [coeff_add,coeff_X_pow_mul',coeff_cut]
  by_cases hi : i < T
  · rw [if_pos hi,if_neg (by omega),add_zero,Nat.zero_add]
  · rw [if_neg hi,if_pos (by omega),zero_add,coeff_cut]
    by_cases hi2 : i < 2*T
    · rw [if_pos (by omega),show T+(i-T) = i by omega]
    · rw [if_neg (by omega),coeff_eq_zero_of_natDegree_lt (by omega)]

lemma binary_separated_add (U V : ℤ[X]) (hU : Binary U) (hV : Binary V)
    (T : ℕ) (hD : U.natDegree < T) : Binary (U+X^T*V) := by
  intro i
  rw [coeff_add,coeff_X_pow_mul']
  by_cases hi : i < T
  · rw [if_neg (by omega),add_zero]
    exact hU _
  · rw [if_pos (by omega),coeff_eq_zero_of_natDegree_lt (by omega),zero_add]
    exact hV _

noncomputable def geo {A : Type*} [Semiring A] (T M : ℕ) : A[X] :=
  ∑ j ∈ Finset.range M, X^(j*T)

lemma geo_zero {A : Type*} [Semiring A] (T : ℕ) : (geo T 0 : A[X]) = 0 := by simp [geo]

lemma geo_succ_last {A : Type*} [Semiring A] (T M : ℕ) :
    (geo T (M+1) : A[X]) = geo T M+X^(M*T) := by
  simp [geo,Finset.sum_range_succ]

lemma geo_succ_first {A : Type*} [Semiring A] (T M : ℕ) :
    (geo T (M+1) : A[X]) = 1+X^T*geo T M := by
  unfold geo
  rw [Finset.sum_range_succ',Finset.mul_sum]
  simp only [Nat.zero_mul,pow_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.succ_mul,← pow_add,Nat.add_comm]

lemma geo_mul {A : Type*} [Ring A] (T M : ℕ) :
    (geo T M : A[X])*(X^T-1) = X^(M*T)-1 := by
  have hh := geom_sum_mul (X^T : A[X]) M
  simp only [← pow_mul] at hh
  simpa only [geo,Nat.mul_comm T] using hh

lemma geo_eval_one (T M : ℕ) : (geo T M : ℤ[X]).eval 1 = (M : ℤ) := by
  simp [geo,eval_finset_sum]

lemma map_geo {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) (T M : ℕ) :
    (geo T M : A[X]).map f = geo T M := by
  simp only [geo,Polynomial.map_sum,Polynomial.map_pow,map_X]

noncomputable def run (W V : ℤ[X]) (T : ℕ) : ℕ → ℤ[X]
  | 0 => V
  | M+1 => W+X^T*run W V T M

lemma run_eq (W V : ℤ[X]) (T M : ℕ) :
    run W V T M = W*geo T M+X^(M*T)*V := by
  induction M with
  | zero => simp [run,geo_zero]
  | succ M ih =>
    rw [run,ih,geo_succ_first,Nat.succ_mul,pow_add]
    ring

lemma binary_run (W V : ℤ[X]) (hW : Binary W) (hV : Binary V)
    (T : ℕ) (hD : W.natDegree < T) (M : ℕ) : Binary (run W V T M) := by
  induction M with
  | zero => exact hV
  | succ M ih => exact binary_separated_add W _ hW ih T hD

noncomputable def pattern {A : Type*} [Semiring A] (U V W : A[X]) (T M : ℕ) : A[X] :=
  U+X^T*(W*geo T (M-1)+X^((M-1)*T)*V)

lemma binary_pattern (U V W : ℤ[X]) (hU : Binary U) (hV : Binary V) (hW : Binary W)
    (T M : ℕ) (hDU : U.natDegree < T) (hDW : W.natDegree < T) :
    Binary (pattern U V W T M) := by
  unfold pattern
  rw [← run_eq]
  exact binary_separated_add U _ hU (binary_run W V hW hV T hDW _) T hDU

lemma pattern_eq_geometric {A : Type*} [CommSemiring A] (U V : A[X])
    (T M : ℕ) (hM : 0 < M) :
    pattern U V (U+V) T M = (U+X^T*V)*geo T M := by
  have hm : M = M-1+1 := by omega
  calc
    _ = U*(1+X^T*geo T (M-1))+X^T*V*(geo T (M-1)+X^((M-1)*T)) := by
      unfold pattern
      ring
    _ = (U+X^T*V)*geo T M := by
      rw [← geo_succ_first,← geo_succ_last,← hm]
      ring

lemma map_pattern {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B)
    (U V W : A[X]) (T M : ℕ) :
    (pattern U V W T M).map f = pattern (U.map f) (V.map f) (W.map f) T M := by
  simp [pattern,map_geo]

lemma pattern_eval_one (U V W : ℤ[X]) (T M : ℕ) (hM : 0 < M) :
    (pattern U V W T M).eval 1 = (M : ℤ)*W.eval 1+(U+V-W).eval 1 := by
  simp only [pattern,eval_add,eval_mul,eval_pow,eval_X,one_pow,one_mul,geo_eval_one,eval_sub]
  rw [Int.natCast_sub (by omega : 1 ≤ M)]
  push_cast
  ring

lemma xor_coeff_correction (U V W : ℤ[X]) (hU : Binary U) (hV : Binary V) (hW : Binary W)
    (hm : W.map (Int.castRingHom (ZMod 2)) =
      U.map (Int.castRingHom (ZMod 2))+V.map (Int.castRingHom (ZMod 2))) (i : ℕ) :
    (U+V-W).coeff i = 0 ∨ (U+V-W).coeff i = 2 := by
  have hc := congrArg (fun P : (ZMod 2)[X] => P.coeff i) hm
  simp only [coeff_map,coeff_add] at hc
  rw [coeff_sub,coeff_add]
  rcases hU i with hu | hu <;> rcases hV i with hv | hv <;> rcases hW i with hw | hw <;>
    simp [hu,hv,hw] at hc ⊢

lemma nonneg_poly_eq_zero_of_eval_one_eq_zero (J : ℤ[X])
    (hnn : ∀ i, 0 ≤ J.coeff i) (hz : J.eval 1 = 0) : J = 0 := by
  have hs : (∑ i ∈ Finset.range (J.natDegree+1), J.coeff i) = 0 := by
    simpa only [eval_eq_sum_range,one_pow,mul_one] using hz
  have hc := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).mp hs
  ext i
  by_cases hi : i ≤ J.natDegree
  · simpa using hc i (Finset.mem_range.mpr (by omega))
  · simp [coeff_eq_zero_of_natDegree_lt (by omega : J.natDegree < i)]

lemma xor_correction_bound (U V W : ℤ[X]) (hU : Binary U) (hV : Binary V) (hW : Binary W)
    (hm : W.map (Int.castRingHom (ZMod 2)) =
      U.map (Int.castRingHom (ZMod 2))+V.map (Int.castRingHom (ZMod 2)))
    (T : ℕ) (hDU : U.natDegree < T) (hDV : V.natDegree < T) (hDW : W.natDegree < T) :
    (U+V-W = 0 ∨ 0 < (U+V-W).eval 1) ∧ (U+V-W).eval 1 ≤ 2*T := by
  let J := U+V-W
  have hj (i : ℕ) : J.coeff i = 0 ∨ J.coeff i = 2 :=
    xor_coeff_correction U V W hU hV hW hm i
  have hnn (i : ℕ) : 0 ≤ J.coeff i := by rcases hj i with h | h <;> omega
  have hdeg : J.natDegree < T :=
    (natDegree_sub_le (U+V) W).trans_lt (max_lt ((natDegree_add_le U V).trans_lt (max_lt hDU hDV)) hDW)
  have he : J.eval 1 = ∑ i ∈ Finset.range T, J.coeff i := by
    simpa only [one_pow,mul_one] using eval_eq_sum_range' hdeg (1 : ℤ)
  have hnonneg : 0 ≤ J.eval 1 := by rw [he]; exact Finset.sum_nonneg (fun i _ => hnn i)
  constructor
  · by_cases hz : J.eval 1 = 0
    · exact Or.inl (nonneg_poly_eq_zero_of_eval_one_eq_zero J hnn hz)
    · right
      change 0 < J.eval 1
      omega
  · change J.eval 1 ≤ 2*T
    rw [he]
    calc
      _ ≤ ∑ _i ∈ Finset.range T, (2 : ℤ) := by
        apply Finset.sum_le_sum
        intro i _
        rcases hj i with h | h <;> omega
      _ = 2*T := by simp; ring

#print axioms pattern_eq_geometric
#print axioms xor_correction_bound
end Erdos406BinaryBlocks
