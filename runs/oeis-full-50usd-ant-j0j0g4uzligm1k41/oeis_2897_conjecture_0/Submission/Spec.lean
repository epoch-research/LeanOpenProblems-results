import FormalConjectures.Util.ProblemImports

open Nat MvPolynomial Finsupp

/--
The sequence $a(n)$ is defined by $a(n) = \binom{2n}{n}^3$.
We use `Nat.choose (2 * n) n` for the central binomial coefficient.
-/
def a (n : ℕ) : ℕ := (Nat.choose (2 * n) n) ^ 3

-- Define the set of variables {x, y, z}
abbrev Vars := Fin 3

/--
The finsupp corresponding to the monomial $x^n y^n z^n$.
This is the map $\lambda i. n$. Since `Fin 3` is finite, this function is finitely supported.
We mark it noncomputable as it builds a mathematical object defined in terms of finite support.
-/
noncomputable def xyz_pow_n (n : ℕ) : Finsupp Vars ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars => n) (Set.toFinite _)

-- The polynomial ring over ℤ with 3 variables
local notation "P" => MvPolynomial Vars ℤ

/--
The polynomial $P_n(X, Y, Z) = (1 + X + Y + Z)^{2n} (1 + X + Y - Z)^n (1 + X - Y + Z)^n$.
We identify $X_0, X_1, X_2$ with $X, Y, Z$.
We mark it noncomputable due to dependencies in the polynomial ring structure.
-/
noncomputable def P_n (n : ℕ) : P :=
  let X := MvPolynomial.X 0
  let Y := MvPolynomial.X 1
  let Z := MvPolynomial.X 2
  let p1 : P := 1 + X + Y + Z
  let p2 : P := 1 + X + Y - Z
  let p3 : P := 1 + X - Y + Z
  p1 ^ (2 * n) * p2 ^ n * p3 ^ n

noncomputable section

variable {R : Type*} [CommRing R]

variable {σ : Type*} [DecidableEq σ]

-- One-step: coefficient of a partial derivative.
theorem coeff_pderiv (i : σ) (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m (pderiv i p) = (m i + 1) * coeff (m + single i 1) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : s = m + single i 1
    · have h1 : s - single i 1 = m := by rw [h, add_tsub_cancel_right]
      have h2 : s i = m i + 1 := by rw [h]; simp
      rw [if_pos h1, if_pos h, h2]; push_cast; ring
    · rw [if_neg h, mul_zero]
      by_cases h2 : s - single i 1 = m
      · have hi : s i = 0 := by
          by_contra hne
          apply h
          rw [← h2, tsub_add_cancel_of_le]
          rw [single_le_iff]
          exact Nat.one_le_iff_ne_zero.mpr hne
        rw [if_pos h2, hi]; simp
      · rw [if_neg h2]
  | add p q hp hq => simp [hp, hq, mul_add]

theorem coeff_iterate_pderiv (i : σ) (k : ℕ) (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    coeff m ((pderiv i)^[k] p) = ((m i + k).descFactorial k) * coeff (m + single i k) p := by
  induction k generalizing m p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Function.comp_apply, coeff_pderiv, ih]
    have e1 : m + single i 1 + single i k = m + single i (k + 1) := by
      rw [add_assoc, ← single_add, Nat.add_comm 1 k]
    rw [e1]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    rw [show m i + 1 + k = m i + (k + 1) by omega, Nat.descFactorial_succ,
      show m i + (k + 1) - k = m i + 1 by omega]
    push_cast
    ring

-- Commutation of partial derivatives.
theorem pderiv_comm (i j : σ) (p : MvPolynomial σ R) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  ext m
  rw [coeff_pderiv, coeff_pderiv, coeff_pderiv, coeff_pderiv]
  have e : m + single i 1 + single j 1 = m + single j 1 + single i 1 := by
    rw [add_assoc, add_assoc, add_comm (single i 1)]
  rw [e]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; ring
  · rw [if_neg h, if_neg (Ne.symm h)]
    push_cast
    ring

theorem iterate_pderiv_comm (i j : σ) (a : ℕ) (p : MvPolynomial σ R) :
    pderiv j ((pderiv i)^[a] p) = (pderiv i)^[a] (pderiv j p) := by
  induction a generalizing p with
  | zero => simp
  | succ a ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [pderiv_comm, ih]

section Specific

open Finset

-- Pure finite-sum Pascal identity (over a ℚ-module M).
lemma sum_step {M : Type*} [AddCommGroup M] [Module ℚ M] (N : ℕ) (W : ℕ → M) :
    (∑ m ∈ range (N+1), ((-1:ℚ)^m * (N.choose m)) • W m)
      - (∑ m ∈ range (N+1), ((-1:ℚ)^m * (N.choose m)) • W (m+1))
      = ∑ m ∈ range (N+2), ((-1:ℚ)^m * ((N+1).choose m)) • W m := by
  rw [Finset.sum_range_succ' (fun m => ((-1:ℚ)^m * ((N+1).choose m)) • W m) (N+1)]
  rw [Finset.sum_range_succ' (fun m => ((-1:ℚ)^m * (N.choose m)) • W m) N]
  rw [Finset.sum_range_succ (fun m => ((-1:ℚ)^m * (N.choose m)) • W (m+1)) N]
  rw [Finset.sum_range_succ (fun m => ((-1:ℚ)^(m+1) * ((N+1).choose (m+1))) • W (m+1)) N]
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_smul]
  -- Now reduce to a sum over range N plus boundary terms.
  have key : ∀ m, ((-1:ℚ)^(m+1) * ((N+1).choose (m+1))) • W (m+1)
      = ((-1:ℚ)^(m+1) * (N.choose (m+1))) • W (m+1) - ((-1:ℚ)^m * (N.choose m)) • W (m+1) := by
    intro m
    rw [← sub_smul]
    congr 1
    rw [Nat.choose_succ_succ, Nat.cast_add]
    ring
  rw [Finset.sum_congr rfl (fun m _ => key m)]
  rw [Finset.sum_sub_distrib]
  have hlast : ((-1:ℚ)^(N+1) * ((N+1).choose (N+1))) • W (N+1)
      = - (((-1:ℚ)^N * (N.choose N)) • W (N+1)) := by
    rw [← neg_smul]
    congr 1
    simp only [Nat.choose_self, Nat.cast_one, mul_one]
    ring
  rw [hlast]
  abel

namespace OpProof

abbrev K := MvPolynomial (Fin 3) ℚ

def Op (p : K) : K := pderiv 1 (pderiv 2 p)

variable (G H : ℕ → K)
  (hG1 : ∀ m, pderiv 1 (G m) = G (m+1))
  (hG2 : ∀ m, pderiv 2 (G m) = G (m+1))
  (hH1 : ∀ m, pderiv 1 (H m) = H (m+1))
  (hH2 : ∀ m, pderiv 2 (H m) = - H (m+1))

include hG1 hG2 hH1 hH2

lemma Op_step (p q : ℕ) : Op (G p * H q) = G (p+2) * H q - G p * H (q+2) := by
  simp only [Op, pderiv_mul, hG1, hG2, hH1, hH2, map_add, map_neg]
  ring

lemma op_iterate (a b N : ℕ) :
    Op^[N] (G a * H b)
      = ∑ m ∈ range (N+1), ((-1:ℚ)^m * (N.choose m)) • (G (a + 2*(N-m)) * H (b + 2*m)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hOp : Op^[N+1] (G a * H b)
        = (∑ m ∈ range (N+1), ((-1:ℚ)^m * (N.choose m)) • (G (a+2*(N+1-m)) * H (b+2*m)))
          - (∑ m ∈ range (N+1), ((-1:ℚ)^m * (N.choose m)) • (G (a+2*(N+1-(m+1))) * H (b+2*(m+1)))) := by
      rw [Function.iterate_succ_apply', ih, Op, map_sum, map_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hsmul : ∀ (c : ℚ) (Z : K), pderiv 1 (pderiv 2 (c • Z)) = c • pderiv 1 (pderiv 2 Z) := by
        intro c Z
        rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, pderiv_C_mul, pderiv_C_mul]
      have step : pderiv 1 (pderiv 2 (((-1:ℚ)^m * (N.choose m)) • (G (a+2*(N-m)) * H (b+2*m))))
          = ((-1:ℚ)^m * (N.choose m)) • (G (a+2*(N-m)+2) * H (b+2*m))
            - ((-1:ℚ)^m * (N.choose m)) • (G (a+2*(N-m)) * H (b+2*m+2)) := by
        rw [hsmul]
        rw [show pderiv 1 (pderiv 2 (G (a+2*(N-m)) * H (b+2*m)))
              = G (a+2*(N-m)+2) * H (b+2*m) - G (a+2*(N-m)) * H (b+2*m+2)
            from Op_step G H hG1 hG2 hH1 hH2 _ _]
        rw [smul_sub]
      rw [step]
      have e1 : a + 2*(N-m) + 2 = a + 2*(N+1-m) := by omega
      have e2 : a + 2*(N-m) = a + 2*(N+1-(m+1)) := by omega
      have e3 : b + 2*m + 2 = b + 2*(m+1) := by ring
      rw [e1, e2, e3]
    rw [hOp]
    exact sum_step N (fun m => G (a+2*(N+1-m)) * H (b+2*m))

end OpProof

namespace Final

open OpProof

-- the three linear forms
def p1 : K := 1 + X 0 + X 1 + X 2
def p2 : K := 1 + X 0 + X 1 - X 2
def p3 : K := 1 + X 0 - X 1 + X 2

lemma pderiv1_p1 : pderiv (1 : Fin 3) p1 = 1 := by
  simp only [p1, map_add, pderiv_one, pderiv_X_self, pderiv_X_of_ne (by decide : (0:Fin 3) ≠ 1),
    pderiv_X_of_ne (by decide : (2:Fin 3) ≠ 1)]; ring
lemma pderiv2_p1 : pderiv (2 : Fin 3) p1 = 1 := by
  simp only [p1, map_add, pderiv_one, pderiv_X_self, pderiv_X_of_ne (by decide : (0:Fin 3) ≠ 2),
    pderiv_X_of_ne (by decide : (1:Fin 3) ≠ 2)]; ring
lemma pderiv1_p2 : pderiv (1 : Fin 3) p2 = 1 := by
  simp only [p2, map_add, map_sub, pderiv_one, pderiv_X_self,
    pderiv_X_of_ne (by decide : (0:Fin 3) ≠ 1),
    pderiv_X_of_ne (by decide : (2:Fin 3) ≠ 1)]; ring
lemma pderiv2_p2 : pderiv (2 : Fin 3) p2 = -1 := by
  simp only [p2, map_add, map_sub, pderiv_one, pderiv_X_self,
    pderiv_X_of_ne (by decide : (0:Fin 3) ≠ 2),
    pderiv_X_of_ne (by decide : (1:Fin 3) ≠ 2)]; ring
lemma pderiv1_p3 : pderiv (1 : Fin 3) p3 = -1 := by
  simp only [p3, map_add, map_sub, pderiv_one, pderiv_X_self,
    pderiv_X_of_ne (by decide : (0:Fin 3) ≠ 1),
    pderiv_X_of_ne (by decide : (2:Fin 3) ≠ 1)]; ring
lemma pderiv2_p3 : pderiv (2 : Fin 3) p3 = 1 := by
  simp only [p3, map_add, map_sub, pderiv_one, pderiv_X_self,
    pderiv_X_of_ne (by decide : (0:Fin 3) ≠ 2),
    pderiv_X_of_ne (by decide : (1:Fin 3) ≠ 2)]; ring

-- iterate preserves negation
lemma iterate_pderiv_neg (m : ℕ) (x : K) :
    (pderiv (1:Fin 3))^[m] (-x) = -((pderiv (1:Fin 3))^[m] x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_neg, ih]

variable (n : ℕ)

def Gf : ℕ → K := fun m => (pderiv 1)^[m] (p1 ^ (2*n))
def Hf : ℕ → K := fun m => (pderiv 1)^[m] (p2 ^ n * p3 ^ n)

lemma hG1 (m : ℕ) : pderiv 1 (Gf n m) = Gf n (m+1) := by
  rw [Gf, Gf, Function.iterate_succ_apply']
lemma hH1 (m : ℕ) : pderiv 1 (Hf n m) = Hf n (m+1) := by
  rw [Hf, Hf, Function.iterate_succ_apply']

lemma pderiv2_G0 : pderiv 2 (p1 ^ (2*n)) = pderiv 1 (p1 ^ (2*n)) := by
  rw [pderiv_pow, pderiv_pow, pderiv1_p1, pderiv2_p1]

lemma pderiv2_H0 : pderiv 2 (p2 ^ n * p3 ^ n) = -(pderiv 1 (p2 ^ n * p3 ^ n)) := by
  rw [pderiv_mul, pderiv_mul, pderiv_pow, pderiv_pow, pderiv_pow, pderiv_pow,
    pderiv1_p2, pderiv2_p2, pderiv1_p3, pderiv2_p3]
  ring

lemma hG2 (m : ℕ) : pderiv 2 (Gf n m) = Gf n (m+1) := by
  rw [Gf, Gf, iterate_pderiv_comm, pderiv2_G0, ← Function.iterate_succ_apply]
lemma hH2 (m : ℕ) : pderiv 2 (Hf n m) = -(Hf n (m+1)) := by
  rw [Hf, Hf, iterate_pderiv_comm, pderiv2_H0, iterate_pderiv_neg, ← Function.iterate_succ_apply]

-- Bridge: coeff at single 0 i equals univariate coefficient after setting X1=X2=0, X0=Y.
def Ψ : K →ₐ[ℚ] Polynomial ℚ :=
  aeval (fun j : Fin 3 => if j = 0 then Polynomial.X else 0)

lemma coeff_single_zero_Ψ (Q : K) (i : ℕ) :
    coeff (Finsupp.single 0 i) Q = (Ψ Q).coeff i := by
  induction Q using MvPolynomial.induction_on' with
  | monomial s c =>
    rw [coeff_monomial, Ψ, aeval_monomial]
    have hprod : (s.prod fun j e => (if j = 0 then (Polynomial.X : Polynomial ℚ) else 0) ^ e)
        = (if s 1 = 0 ∧ s 2 = 0 then (Polynomial.X : Polynomial ℚ) ^ (s 0) else 0) := by
      rw [Finsupp.prod_fintype]
      · rw [Fin.prod_univ_three]
        simp only [zero_pow_eq]
        norm_num
        by_cases h1 : s 1 = 0 <;> by_cases h2 : s 2 = 0 <;>
          simp [h1, h2]
      · intro j; simp
    rw [hprod, Polynomial.algebraMap_eq]
    have hsingle : (s = Finsupp.single 0 i) ↔ (s 0 = i ∧ s 1 = 0 ∧ s 2 = 0) := by
      constructor
      · intro h; subst h; exact ⟨by simp, by simp, by simp⟩
      · rintro ⟨h0, h1, h2⟩
        ext j; fin_cases j <;> simp [Finsupp.single_apply, h0, h1, h2]
    by_cases hs : s 1 = 0 ∧ s 2 = 0
    · rw [if_pos hs, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases hi : s 0 = i
      · rw [if_pos (hsingle.mpr ⟨hi, hs.1, hs.2⟩), if_pos hi.symm, mul_one]
      · rw [if_neg (fun h => hi (hsingle.mp h).1), if_neg (fun h => hi h.symm), mul_zero]
    · rw [if_neg hs, mul_zero, Polynomial.coeff_zero, if_neg]
      intro h
      exact hs ⟨(hsingle.mp h).2.1, (hsingle.mp h).2.2⟩
  | add p q hp hq => simp [hp, hq, map_add, Polynomial.coeff_add]

-- iterate of pderiv 1 on a power of f with pderiv 1 f = 1
lemma iterate_pderiv_pow_eq (f : K) (hf : pderiv 1 f = 1) (N : ℕ) :
    ∀ m, (pderiv 1)^[m] (f ^ N) = (N.descFactorial m) • f ^ (N - m) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_nsmul, pderiv_pow, hf, mul_one,
      ← nsmul_eq_mul, smul_smul, Nat.sub_sub]
    congr 1
    rw [Nat.descFactorial_succ]; ring

-- pull a pderiv-1-constant out of iterated pderiv 1
lemma iterate_pderiv_const_mul (a : K) (ha : pderiv 1 a = 0) (m : ℕ) (g : K) :
    (pderiv 1)^[m] (a * g) = a * (pderiv 1)^[m] g := by
  induction m generalizing g with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, pderiv_mul, ha, zero_mul,
      zero_add, ih]

-- u and d
def u : K := 1 + X 0
def d : K := X 1 - X 2

lemma pderiv1_u : pderiv 1 (u : K) = 0 := by
  simp only [u, map_add, pderiv_one, pderiv_X_of_ne (by decide : (0:Fin 3) ≠ 1)]; ring
lemma pderiv1_d : pderiv 1 (d : K) = 1 := by
  simp only [d, map_sub, pderiv_X_self, pderiv_X_of_ne (by decide : (2:Fin 3) ≠ 1)]; ring

lemma Psi_X0 : Ψ (X 0 : K) = Polynomial.X := by simp [Ψ]
lemma Psi_X1 : Ψ (X 1 : K) = 0 := by simp [Ψ]
lemma Psi_X2 : Ψ (X 2 : K) = 0 := by simp [Ψ]
lemma Psi_p1 : Ψ (p1 : K) = 1 + Polynomial.X := by
  simp only [p1, map_add, map_one, Psi_X0, Psi_X1, Psi_X2]; ring
lemma Psi_u : Ψ (u : K) = 1 + Polynomial.X := by
  simp only [u, map_add, map_one, Psi_X0]
lemma Psi_d : Ψ (d : K) = 0 := by
  simp only [d, map_sub, Psi_X1, Psi_X2, sub_zero]

lemma p2p3_eq : (p2 : K) * p3 = u^2 - d^2 := by
  simp only [p2, p3, u, d]; ring

lemma H0_eq : (p2 : K)^n * p3^n = (u^2 - d^2)^n := by
  rw [← mul_pow, p2p3_eq]

-- iterate of pderiv 1 distributes over finite sums
lemma iterate_pderiv_sum {ι} (s : Finset ι) (f : ι → K) (m : ℕ) :
    (pderiv 1)^[m] (∑ i ∈ s, f i) = ∑ i ∈ s, (pderiv 1)^[m] (f i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    apply Finset.sum_congr rfl
    intro i _; rw [Function.iterate_succ_apply']

lemma pderiv1_natCast (c : ℕ) : pderiv (1:Fin 3) ((c : K)) = 0 := by
  rw [← map_natCast (C : ℚ →+* K) c, pderiv_C]

-- key per-term computation: Ψ of iterated pderiv 1 of (constant) * d^j
lemma Psi_iter_d (a : K) (ha : pderiv 1 a = 0) (j k : ℕ) :
    Ψ ((pderiv 1)^[2*k] (a * d^j)) = if j = 2*k then ((2*k).factorial : Polynomial ℚ) * Ψ a else 0 := by
  rw [iterate_pderiv_const_mul a ha, iterate_pderiv_pow_eq d pderiv1_d j (2*k),
    map_mul, map_nsmul, map_pow, Psi_d]
  by_cases hjk : j = 2*k
  · subst hjk
    rw [if_pos rfl, Nat.sub_self, pow_zero, Nat.descFactorial_self, mul_smul_comm, mul_one,
      nsmul_eq_mul]
  · rw [if_neg hjk]
    rcases lt_or_gt_of_ne hjk with hlt | hgt
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt, zero_smul, mul_zero]
    · rw [zero_pow (by omega : j - 2*k ≠ 0), smul_zero, mul_zero]

lemma Psi_Gf (m : ℕ) :
    Ψ (Gf n m) = (((2*n).descFactorial m : Polynomial ℚ)) * (1 + Polynomial.X)^(2*n - m) := by
  rw [Gf, iterate_pderiv_pow_eq p1 pderiv1_p1 (2*n) m, map_nsmul, map_pow, Psi_p1, nsmul_eq_mul]

lemma Psi_Hf (k : ℕ) (hk : k ≤ n) :
    Ψ (Hf n (2*k))
      = ((2*k).factorial : Polynomial ℚ) * (-1)^((n-k)+n) * (Nat.choose n k : Polynomial ℚ)
          * (1 + Polynomial.X)^(2*(n-k)) := by
  have hsum : Ψ (Hf n (2*k)) = ∑ m ∈ Finset.range (n+1),
      (if 2*(n-m) = 2*k then ((2*k).factorial : Polynomial ℚ) *
          Ψ (((-1:K))^(m+n) * (u^2)^m * (Nat.choose n m : K)) else 0) := by
    rw [Hf, H0_eq, sub_pow, iterate_pderiv_sum, map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have ha : pderiv 1 (((-1:K))^(m+n) * (u^2)^m * (Nat.choose n m : K)) = 0 := by
      rw [pderiv_mul, pderiv_mul]
      simp [pderiv_pow, pderiv1_u, pderiv1_natCast]
    rw [show ((-1:K))^(m+n) * (u^2)^m * (d^2)^(n-m) * (Nat.choose n m : K)
          = (((-1:K))^(m+n) * (u^2)^m * (Nat.choose n m : K)) * d^(2*(n-m)) by
        rw [← pow_mul]; ring]
    rw [Psi_iter_d _ ha (2*(n-m)) k]
  rw [hsum, Finset.sum_eq_single (n-k)]
  · rw [if_pos (show 2*(n-(n-k)) = 2*k by omega)]
    simp only [map_mul, map_pow, Psi_u, map_neg, map_one, map_natCast]
    rw [Nat.choose_symm hk, ← pow_mul]
    push_cast
    ring
  · intro m hm hne
    have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    rw [if_neg (fun hcontra => hne (by omega))]
  · intro h
    exact absurd (Finset.mem_range.mpr (show n - k < n + 1 by omega)) h

lemma term_coeff (k : ℕ) (hk : k ≤ n) :
    coeff (Finsupp.single 0 n) (Gf n (2*(n-k)) * Hf n (2*k))
      = ((2*n).factorial : ℚ) * (-1)^((n-k)+n) * (n.choose k) * ((2*n).choose n) := by
  rw [coeff_single_zero_Ψ, map_mul, Psi_Gf, Psi_Hf n k hk, show 2*n - 2*(n-k) = 2*k from by omega]
  have hS : (((2*n).descFactorial (2*(n-k)) : Polynomial ℚ) * (1 + Polynomial.X)^(2*k))
        * (((2*k).factorial : Polynomial ℚ) * (-1)^((n-k)+n) * (Nat.choose n k : Polynomial ℚ)
            * (1 + Polynomial.X)^(2*(n-k)))
      = (((2*n).descFactorial (2*(n-k)) : ℚ) * (2*k).factorial * (-1)^((n-k)+n) * (Nat.choose n k))
          • (1 + Polynomial.X)^(2*n) := by
    rw [Polynomial.smul_eq_C_mul]
    have hc : (1 + Polynomial.X : Polynomial ℚ)^(2*n)
        = (1+Polynomial.X)^(2*k) * (1+Polynomial.X)^(2*(n-k)) := by
      rw [← pow_add]; congr 1; omega
    rw [hc]
    push_cast [Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_1,
      Polynomial.C_eq_natCast]
    ring
  rw [hS, Polynomial.coeff_smul, Polynomial.coeff_one_add_X_pow, smul_eq_mul]
  rw [show ((2*n).descFactorial (2*(n-k)) : ℚ) * (2*k).factorial = ((2*n).factorial : ℚ) from by
        have h := Nat.factorial_mul_descFactorial (show 2*(n-k) ≤ 2*n from by omega)
        rw [show 2*n - 2*(n-k) = 2*k from by omega] at h
        rw [← Nat.cast_mul, Nat.mul_comm ((2*n).descFactorial (2*(n-k))) ((2*k).factorial), h]]

lemma sum_choose_sq : ∑ k ∈ Finset.range (n+1), (n.choose k)^2 = (2*n).choose n := by
  have := Nat.add_choose_eq n n n
  rw [show n + n = 2*n from by ring] at this
  rw [this, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => n.choose i * n.choose j)]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [Nat.choose_symm hin, sq]

lemma coeff_F_eq :
    coeff (Finsupp.single 0 n + Finsupp.single 1 n + Finsupp.single 2 n) (Gf n 0 * Hf n 0)
      = ((2*n).choose n : ℚ)^3 := by
  have hcomm : Function.Commute (⇑(pderiv (1:Fin 3)) : K → K) (⇑(pderiv 2)) :=
    fun x => pderiv_comm 1 2 x
  have hOp : Op^[n] (Gf n 0 * Hf n 0)
      = (pderiv 1)^[n] ((pderiv 2)^[n] (Gf n 0 * Hf n 0)) :=
    congrFun (Function.Commute.comp_iterate hcomm n) (Gf n 0 * Hf n 0)
  have e2 : coeff (Finsupp.single 0 n) (Op^[n] (Gf n 0 * Hf n 0))
      = (n.factorial : ℚ)^2 *
        coeff (Finsupp.single 0 n + Finsupp.single 1 n + Finsupp.single 2 n) (Gf n 0 * Hf n 0) := by
    rw [hOp, coeff_iterate_pderiv, coeff_iterate_pderiv, Finsupp.add_apply,
        Finsupp.single_eq_of_ne' (show (0:Fin 3) ≠ 1 by decide),
        Finsupp.single_eq_of_ne' (show (0:Fin 3) ≠ 2 by decide),
        Finsupp.single_eq_of_ne' (show (1:Fin 3) ≠ 2 by decide)]
    simp only [add_zero, zero_add, Nat.descFactorial_self]
    push_cast; ring
  have e1 : coeff (Finsupp.single 0 n) (Op^[n] (Gf n 0 * Hf n 0))
      = ∑ k ∈ Finset.range (n+1),
          ((-1:ℚ)^k * (n.choose k)) * coeff (Finsupp.single 0 n) (Gf n (2*(n-k)) * Hf n (2*k)) := by
    rw [op_iterate (Gf n) (Hf n) (hG1 n) (hG2 n) (hH1 n) (hH2 n) 0 0 n, coeff_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [coeff_smul, smul_eq_mul, zero_add, zero_add]
  have hsum : (∑ k ∈ Finset.range (n+1),
        ((-1:ℚ)^k * (n.choose k)) * coeff (Finsupp.single 0 n) (Gf n (2*(n-k)) * Hf n (2*k)))
      = ((2*n).factorial : ℚ) * ((2*n).choose n)^2 := by
    have hterm : ∀ k ∈ Finset.range (n+1),
        ((-1:ℚ)^k * (n.choose k)) * coeff (Finsupp.single 0 n) (Gf n (2*(n-k)) * Hf n (2*k))
          = ((2*n).factorial : ℚ) * ((2*n).choose n) * (n.choose k : ℚ)^2 := by
      intro k hk'
      have hk : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk')
      rw [term_coeff n k hk]
      have hsign : ((-1:ℚ))^k * (-1)^((n-k)+n) = 1 := by
        rw [← pow_add, show k + ((n-k)+n) = 2*n from by omega, pow_mul, neg_one_sq, one_pow]
      rw [show ((-1:ℚ)^k * (n.choose k)) * (((2*n).factorial:ℚ) * (-1)^((n-k)+n)
              * (n.choose k) * ((2*n).choose n))
            = ((2*n).factorial:ℚ) * ((2*n).choose n) * ((n.choose k:ℚ)^2)
              * ((-1:ℚ)^k * (-1)^((n-k)+n)) from by ring]
      rw [hsign, mul_one]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    rw [show (∑ k ∈ Finset.range (n+1), (n.choose k:ℚ)^2) = ((2*n).choose n : ℚ) from by
        exact_mod_cast sum_choose_sq n]
    ring
  have key : (n.factorial : ℚ)^2 *
      coeff (Finsupp.single 0 n + Finsupp.single 1 n + Finsupp.single 2 n) (Gf n 0 * Hf n 0)
      = ((2*n).factorial : ℚ) * ((2*n).choose n)^2 := by
    rw [← e2, e1, hsum]
  have hfact : ((2*n).factorial : ℚ) = ((2*n).choose n : ℚ) * (n.factorial:ℚ)^2 := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2*n from by omega)
    rw [show 2*n - n = n from by omega] at h
    rw [show ((2*n).choose n : ℚ) * (n.factorial:ℚ)^2
          = (((2*n).choose n * n.factorial * n.factorial : ℕ) : ℚ) from by push_cast; ring, h]
  rw [hfact, show ((2*n).choose n : ℚ) * (n.factorial:ℚ)^2 * ((2*n).choose n)^2
        = (n.factorial:ℚ)^2 * ((2*n).choose n)^3 from by ring] at key
  have hn0 : (n.factorial:ℚ)^2 ≠ 0 := by positivity
  exact mul_left_cancel₀ hn0 key

lemma coeff_FF :
    coeff (Finsupp.single 0 n + Finsupp.single 1 n + Finsupp.single 2 n)
      (p1 ^ (2*n) * p2 ^ n * p3 ^ n) = ((2*n).choose n : ℚ)^3 := by
  have h := coeff_F_eq n
  rw [show Gf n 0 = p1 ^ (2*n) from rfl, show Hf n 0 = p2 ^ n * p3 ^ n from rfl] at h
  rw [mul_assoc]
  exact h

end Final

/--
**oeis_2897_conjecture_0**:
Conjecture: The g.f. is also the diagonal of the rational function 1/(1 - (x + y)*(1 - 4*z*t) - z - t) = 1/det(I - M*diag(x, y, z, t)), I the 4 x 4 unit matrix and M the 4 x 4 matrix [1, 1, 1, 1; 1, 1, 1, 1; 1, 1, 1, -1; 1 , 1, -1, 1]. If true, then a(n) = [(x*y*z)^n] (1 + x + y + z)^(2*n)*(1 + x + y - z)^n*(1 + x - y + z)^n. - _Peter Bala_, Apr 10 2022
-/
theorem oeis_2897_conjecture_0 (n : ℕ) :
  (a n : ℤ) = MvPolynomial.coeff (xyz_pow_n n) (P_n n) :=
by
  have hxyz : xyz_pow_n n
      = Finsupp.single 0 n + Finsupp.single 1 n + Finsupp.single 2 n := by
    ext j
    fin_cases j <;>
      simp [xyz_pow_n, Finsupp.ofSupportFinite, Finsupp.single_apply]
  have hmap : MvPolynomial.map (Int.castRingHom ℚ) (P_n n)
      = Final.p1 ^ (2*n) * Final.p2 ^ n * Final.p3 ^ n := by
    simp only [P_n, map_mul, map_pow, map_add, map_sub, MvPolynomial.map_X, map_one]
    rfl
  rw [← @Int.cast_inj ℚ _ _, hxyz]
  have hrhs : ((coeff (Finsupp.single 0 n + Finsupp.single 1 n + Finsupp.single 2 n)
        (P_n n) : ℤ) : ℚ)
      = ((2*n).choose n : ℚ)^3 := by
    rw [show ((coeff (Finsupp.single 0 n + Finsupp.single 1 n + Finsupp.single 2 n) (P_n n) : ℤ) : ℚ)
          = (Int.castRingHom ℚ) (coeff (Finsupp.single 0 n + Finsupp.single 1 n + Finsupp.single 2 n) (P_n n)) from rfl,
        ← coeff_map, hmap, Final.coeff_FF]
  rw [hrhs]
  push_cast [a]
  ring
