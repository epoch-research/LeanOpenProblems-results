import FormalConjectures.Util.ProblemImports

open Nat Finset Polynomial
open scoped BigOperators ComplexConjugate

/--
A103885: $a(n) = [x^{2n}] \left(\frac{1 + x}{1 - x}\right)^n$.
The sequence is given by the combinatorial identity:
$$a(n) = \sum_{k = 0}^n \binom{n}{k} \binom{2n+k-1}{n-1}$$
with $a(0) = 1$.
-/
def A103885 (n : ℕ) : ℕ :=
  if n = 0 then 1
  else
    let r : ℕ := n - 1
    (range (n + 1)).sum (fun k => (n.choose k) * ((2 * n + k - 1).choose r))

-- The sequence b(n) = a(m*n) lifted to ℝ
noncomputable def A103885_subsequence_real (m n : ℕ) : ℝ :=
  (A103885 (m * n) : ℝ)

open BigOperators

-- The indices k = 1 to 2m, used in the product
def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

-- The factor Product_{k=1}^{2m} (2mn + k)
noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) + (k : ℝ))

-- The factor Product_{k=1}^{2m} (2mn - k)
noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k =>
    ((2 * m * n : ℝ) - (k : ℝ))

/-
Proof strategy.  The binomial sum is the first component of a two-dimensional
recurrence with transition matrix T(x) and denominator (2*x+1)*(2*x+2).
The upper-right entry R_m(x) of a product of m transition matrices has degree
at most 2*m.  Reflection of the matrices gives R_m(-x-m) = R_m(x).
At x = -j/2, all the factors are strictly positive entrywise, except that for
odd j there is exactly one strictly negative factor, T(-1/2).  Consequently
R_m has alternating signs at the 2*m+1 half-integers from -m to 0.  The
intermediate value theorem and the degree bound locate all its complex roots.
Finally, elimination of the second component gives the desired recurrence;
its central coefficient is a translate of R_{2*m}, hence is even.
-/

namespace A103885Proof

def T {R : Type*} [CommRing R] (x : R) : Matrix (Fin 2) (Fin 2) R :=
  !![22*x^2 + 24*x + 6, 5*x^2 + 5*x + 1;
     100*x^2 + 100*x + 24, 22*x^2 + 20*x + 4]

def flip {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  !![M 1 1, M 0 1; M 1 0, M 0 0]

lemma flip_mul {R : Type*} [CommRing R] (M N : Matrix (Fin 2) (Fin 2) R) :
    flip (M * N) = flip N * flip M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flip, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma T_reflect {R : Type*} [CommRing R] (x : R) : T (-x-1) = flip (T x) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [T, flip] <;> ring

lemma T_det {R : Type*} [CommRing R] (x : R) :
    (T x).det = -((2*x+1)^2 * (2*x) * (2*x+2)) := by
  simp [T, Matrix.det_fin_two]
  ring

def block {R : Type*} [CommRing R] : ℕ → R → Matrix (Fin 2) (Fin 2) R
  | 0, _ => 1
  | n+1, x => T (x+n) * block n x

lemma block_add {R : Type*} [CommRing R] (a b : ℕ) (x : R) :
    block (a+b) x = block b (x+a) * block a x := by
  induction b with
  | zero => simp [block]
  | succ b ih =>
    change T (x + ↑(a+b)) * block (a+b) x =
      (T (x + ↑a + ↑b) * block b (x+a)) * block a x
    rw [ih, Nat.cast_add, add_assoc, Matrix.mul_assoc]

lemma block_succ_right {R : Type*} [CommRing R] (m : ℕ) (x : R) :
    block (m+1) x = block m (x+1) * T x := by
  simpa [block, Nat.add_comm] using block_add 1 m x

lemma block_reflect {R : Type*} [CommRing R] (m : ℕ) (x : R) :
    block m (-x-m) = flip (block m x) := by
  induction m generalizing x with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp [block, flip]
  | succ m ih =>
    rw [block_succ_right m x, flip_mul]
    rw [block]
    have h1 : -x - (↑(m+1) : R) + m = -x-1 := by push_cast; ring
    have h2 : -x - (↑(m+1) : R) = -(x+1)-m := by push_cast; ring
    rw [h1, h2, T_reflect, ih]

noncomputable def Rpoly (m : ℕ) : ℝ[X] := block m X 0 1

lemma block_eval (m : ℕ) (x : ℝ) (i j : Fin 2) :
    (block m (X : ℝ[X]) i j).eval x = block m x i j := by
  induction m generalizing i j with
  | zero => fin_cases i <;> fin_cases j <;> simp [block]
  | succ m ih =>
    simp only [block, Matrix.mul_apply, Fin.sum_univ_two, eval_add, eval_mul, ih]
    congr 1 <;> congr 1 <;>
      fin_cases i <;> simp [T] <;> ring

lemma Rpoly_eval (m : ℕ) (x : ℝ) : (Rpoly m).eval x = block m x 0 1 := block_eval m x 0 1

lemma Rpoly_reflect (m : ℕ) (x : ℝ) :
    (Rpoly m).eval (-x-m) = (Rpoly m).eval x := by
  simp [Rpoly_eval, block_reflect, flip]

lemma T_natDegree (m : ℕ) (i j : Fin 2) :
    (T (X + (m : ℝ[X])) i j).natDegree ≤ 2 := by
  fin_cases i <;> fin_cases j <;> simp [T] <;> compute_degree!

lemma block_natDegree (m : ℕ) (i j : Fin 2) :
    (block m (X : ℝ[X]) i j).natDegree ≤ 2*m := by
  induction m generalizing i j with
  | zero => fin_cases i <;> fin_cases j <;> simp [block]
  | succ m ih =>
    simp only [block, Matrix.mul_apply, Fin.sum_univ_two]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_mul_le).trans (by
        have := T_natDegree m i 0
        have := ih 0 j
        omega)
    · exact (Polynomial.natDegree_mul_le).trans (by
        have := T_natDegree m i 1
        have := ih 1 j
        omega)

lemma Rpoly_natDegree (m : ℕ) : (Rpoly m).natDegree ≤ 2*m := block_natDegree m 0 1

def Good (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (∀ i j, 0 ≤ M i j) ∧ (∀ i, 0 < M i i)

def Strict (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop := ∀ i j, 0 < M i j

lemma good_one : Good (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  constructor
  · intro i j; fin_cases i <;> fin_cases j <;> norm_num
  · intro i; simp

lemma strict_good {M : Matrix (Fin 2) (Fin 2) ℝ} (h : Strict M) : Good M :=
  ⟨fun i j => (h i j).le, fun i => h i i⟩

lemma good_mul {M N : Matrix (Fin 2) (Fin 2) ℝ} (hM : Good M) (hN : Good N) :
    Good (M*N) := by
  constructor
  · intro i j
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hM.1 i k) (hN.1 k j))
  · intro i
    apply lt_of_lt_of_le (mul_pos (hM.2 i) (hN.2 i))
    exact Finset.single_le_sum (fun k _ => mul_nonneg (hM.1 i k) (hN.1 k i)) (Finset.mem_univ i)

lemma strict_mul_good {M N : Matrix (Fin 2) (Fin 2) ℝ} (hM : Strict M) (hN : Good N) :
    Strict (M*N) := by
  intro i j
  apply lt_of_lt_of_le (mul_pos (hM i j) (hN.2 j))
  exact Finset.single_le_sum (fun k _ => mul_nonneg (hM i k).le (hN.1 k j)) (Finset.mem_univ j)

lemma good_mul_strict {M N : Matrix (Fin 2) (Fin 2) ℝ} (hM : Good M) (hN : Strict N) :
    Strict (M*N) := by
  intro i j
  apply lt_of_lt_of_le (mul_pos (hM.2 i) (hN i j))
  exact Finset.single_le_sum (fun k _ => mul_nonneg (hM.1 i k) (hN k j).le) (Finset.mem_univ i)

lemma good_flip {M : Matrix (Fin 2) (Fin 2) ℝ} (h : Good M) : Good (flip M) := by
  constructor
  · intro i j; fin_cases i <;> fin_cases j <;> simp [flip] <;> apply h.1
  · intro i; fin_cases i <;> simp [flip] <;> apply h.2

lemma strict_flip {M : Matrix (Fin 2) (Fin 2) ℝ} (h : Strict M) : Strict (flip M) := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [flip] <;> apply h

lemma T_strict {x : ℝ} (hx : 0 ≤ x) : Strict (T x) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [T] <;> positivity

lemma block_good (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : Good (block m x) := by
  induction m with
  | zero => exact good_one
  | succ m ih => exact good_mul (strict_good (T_strict (by positivity))) ih

lemma block_strict (m : ℕ) (hm : 1 ≤ m) {x : ℝ} (hx : 0 ≤ x) : Strict (block m x) := by
  cases m with
  | zero => omega
  | succ m => exact strict_mul_good (T_strict (by positivity)) (block_good m hx)

lemma neg_T_half : Strict (-T (- (1/2 : ℝ))) := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [T]

lemma Rpoly_integer_pos (m q : ℕ) (hm : 1 ≤ m) (hq : q ≤ m) :
    0 < (Rpoly m).eval (-(q : ℝ)) := by
  rw [Rpoly_eval]
  have hblock : block m (-(q : ℝ)) = block (m-q) (0 : ℝ) * flip (block q 0) := by
    have h := block_add q (m-q) (-(q : ℝ))
    rw [Nat.add_sub_of_le hq] at h
    simpa using h.trans (by rw [show -(q : ℝ) + q = 0 by ring,
      show -(q : ℝ) = -(0 : ℝ)-q by ring, block_reflect])
  rw [hblock]
  by_cases hq0 : q = 0
  · subst q
    have hf : flip (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [flip]
    simpa only [Nat.sub_zero, block, hf, Matrix.mul_one] using
      block_strict m hm (x := 0) (by norm_num) 0 1
  · exact good_mul_strict (block_good _ (by norm_num))
      (strict_flip (block_strict q (by omega) (by norm_num))) 0 1

lemma Rpoly_half_neg (m q : ℕ) (hq : q < m) :
    (Rpoly m).eval (-(q : ℝ) - 1/2) < 0 := by
  rw [Rpoly_eval]
  have hblock : block m (-(q : ℝ)-1/2) =
      block (m-(q+1)) (1/2 : ℝ) * T (- (1/2 : ℝ)) * flip (block q (1/2 : ℝ)) := by
    have h := block_add (q+1) (m-(q+1)) (-(q : ℝ)-1/2)
    rw [Nat.add_sub_of_le (by omega : q+1 ≤ m)] at h
    rw [h, block]
    have h1 : -(q : ℝ)-1/2+↑(q+1) = 1/2 := by push_cast; ring
    have h2 : -(q : ℝ)-1/2+q = -(1/2) := by ring
    have h3 : -(q : ℝ)-1/2 = -(1/2)-q := by ring
    rw [h1, h2, h3, block_reflect, ← Matrix.mul_assoc]
  rw [hblock]
  have hpos := strict_mul_good
    (good_mul_strict (block_good (m-(q+1)) (by norm_num : (0 : ℝ) ≤ 1/2)) neg_T_half)
    (good_flip (block_good q (by norm_num : (0 : ℝ) ≤ 1/2))) 0 1
  simpa using hpos

lemma Rpoly_grid_sign (m j : ℕ) (hm : 1 ≤ m) (hj : j ≤ 2*m) :
    0 < (-1 : ℝ)^j * (Rpoly m).eval (-(j : ℝ)/2) := by
  rcases Nat.even_or_odd j with he | ho
  · obtain ⟨q, rfl⟩ := he
    have h := Rpoly_integer_pos m q hm (by omega)
    rw [← two_mul, pow_mul]
    norm_num
    convert h using 1 <;> congr 1 <;> push_cast <;> ring
  · obtain ⟨q, rfl⟩ := ho
    have h := Rpoly_half_neg m q (by omega)
    rw [pow_add, pow_mul]
    norm_num
    convert h using 1 <;> congr 1 <;> push_cast <;> ring

lemma eval_map_real (p : ℝ[X]) (x : ℝ) :
    (p.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((p.eval x : ℝ) : ℂ) := by
  exact (Polynomial.eval_map _ _).trans (Polynomial.eval₂_at_apply _ _)

lemma Rpoly_interval_root (m j : ℕ) (hm : 1 ≤ m) (hj : j < 2*m) :
    ∃ x : ℝ, -(↑(j+1) : ℝ)/2 < x ∧ x < -(j : ℝ)/2 ∧ (Rpoly m).eval x = 0 := by
  have h0 := Rpoly_grid_sign m j hm (by omega)
  have h1 := Rpoly_grid_sign m (j+1) hm (by omega)
  rw [pow_succ] at h1
  have hn : (-1 : ℝ)^j * (Rpoly m).eval (-(↑(j+1) : ℝ)/2) < 0 := by nlinarith
  have hab : -(↑(j+1) : ℝ)/2 ≤ -(j : ℝ)/2 := by push_cast; linarith
  obtain ⟨x, hx, he⟩ := intermediate_value_Ioo hab
    ((continuous_const.mul (Rpoly m).continuous).continuousOn) ⟨hn, h0⟩
  exact ⟨x, hx.1, hx.2, (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (by norm_num))⟩

lemma Rpoly_roots (m : ℕ) (hm : 1 ≤ m) :
    (Rpoly m).degree = (2*m : ℕ) ∧
    (∀ z : ℂ, ((Rpoly m).map (algebraMap ℝ ℂ)).eval z = 0 →
      z.im = 0 ∧ z.re ∈ Set.Icc (-(m : ℝ)) 0) := by
  classical
  have hr : ∀ i : Fin (2*m), ∃ x : ℝ,
      -(↑(i.val+1) : ℝ)/2 < x ∧ x < -(i.val : ℝ)/2 ∧ (Rpoly m).eval x = 0 :=
    fun i => Rpoly_interval_root m i hm i.isLt
  choose r hr using hr
  have hinj : Function.Injective r := by
    intro i j hij
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have hij' : (i.val+1 : ℝ) ≤ j.val := by exact_mod_cast hlt
      have hri := (hr i).1
      have hrj := (hr j).2.1
      push_cast at hri hrj
      rw [hij] at hri
      linarith
    · have hij' : (j.val+1 : ℝ) ≤ i.val := by exact_mod_cast hgt
      have hri := (hr i).2.1
      have hrj := (hr j).1
      push_cast at hri hrj
      rw [hij] at hri
      linarith
  let S : Finset ℂ := Finset.univ.image (fun i => (r i : ℂ))
  have hcard : S.card = 2*m := by
    change (Finset.univ.image (Complex.ofReal ∘ r)).card = 2*m
    rw [Finset.card_image_of_injective _ (Complex.ofReal_injective.comp hinj)]
    simp
  have hS : ∀ z ∈ S, ((Rpoly m).map (algebraMap ℝ ℂ)).eval z = 0 := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    rw [eval_map_real, (hr i).2.2, Complex.ofReal_zero]
  have hp : Rpoly m ≠ 0 := by
    intro h
    have := Rpoly_grid_sign m 0 hm (by omega)
    simp [h] at this
  have hpc : (Rpoly m).map (algebraMap ℝ ℂ) ≠ 0 := Polynomial.map_ne_zero hp
  have hdeg : ((Rpoly m).map (algebraMap ℝ ℂ)).natDegree ≤ S.card := by
    rw [Polynomial.natDegree_map, hcard]
    exact Rpoly_natDegree m
  have hroots := Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero hS hdeg hpc
  have hdeg_eq : (Rpoly m).natDegree = 2*m := by
    apply le_antisymm (Rpoly_natDegree m)
    have h := Polynomial.card_roots' ((Rpoly m).map (algebraMap ℝ ℂ))
    rw [hroots, Polynomial.natDegree_map] at h
    change S.card ≤ (Rpoly m).natDegree at h
    rwa [hcard] at h
  refine ⟨(Polynomial.degree_eq_natDegree hp).trans (congrArg Nat.cast hdeg_eq), ?_⟩
  intro z hz
  have hzS : z ∈ S := by
    rw [← Finset.mem_val, ← hroots, Polynomial.mem_roots hpc]
    exact hz
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzS
  simp only [Complex.ofReal_im, Complex.ofReal_re, Set.mem_Icc, true_and]
  have hlo := (hr i).1
  have hhi := (hr i).2.1
  have hib : (i.val+1 : ℝ) ≤ 2*m := by exact_mod_cast i.isLt
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  push_cast at hlo hhi
  constructor <;> linarith

lemma coeff_comp_neg (p : ℝ[X]) (n : ℕ) :
    (p.comp (-X)).coeff n = (-1 : ℝ)^n * p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [Polynomial.add_comp, hp, hq, mul_add]
  | monomial k a =>
    rw [Polynomial.monomial_comp]
    have hh : (-(X : ℝ[X]))^k = C ((-1 : ℝ)^k) * X^k := by
      rw [neg_pow]
      simp only [map_pow, map_neg, map_one]
    rw [hh, ← mul_assoc, ← C_mul, Polynomial.coeff_C_mul_X_pow]
    by_cases h : n = k
    · subst n; simp [mul_comm]
    · simp [Polynomial.coeff_monomial, h, Ne.symm h]

lemma even_expand_contract (p : ℝ[X]) (h : ∀ x : ℝ, p.eval (-x) = p.eval x) :
    Polynomial.expand ℝ 2 (Polynomial.contract 2 p) = p := by
  have he : p.comp (-X) = p := Polynomial.funext (by simpa using h)
  ext n
  rw [Polynomial.coeff_expand (by norm_num : 0 < 2)]
  by_cases hn : 2 ∣ n
  · rw [if_pos hn, Polynomial.coeff_contract (by norm_num), Nat.div_mul_cancel hn]
  · rw [if_neg hn]
    have hc := congrArg (fun q : ℝ[X] => q.coeff n) he
    dsimp only at hc
    rw [coeff_comp_neg] at hc
    have ho : Odd n := Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hn)
    rw [ho.neg_one_pow] at hc
    linarith

noncomputable def affine (m : ℕ) : ℝ[X] := C (m : ℝ) * X - C (m : ℝ)
noncomputable def Ppoly (m : ℕ) : ℝ[X] := (Rpoly m).comp (affine m)
noncomputable def Hpoly (m : ℕ) : ℝ[X] := (Rpoly (2*m)).comp (affine m)
noncomputable def Qpoly (m : ℕ) : ℝ[X] := Polynomial.contract 2 (Hpoly m)

lemma affine_eval (m : ℕ) (x : ℝ) : (affine m).eval x = m*x-m := by simp [affine]
lemma Ppoly_eval (m : ℕ) (x : ℝ) : (Ppoly m).eval x = (Rpoly m).eval (m*x-m) := by
  simp [Ppoly, affine_eval]
lemma Hpoly_eval (m : ℕ) (x : ℝ) : (Hpoly m).eval x = (Rpoly (2*m)).eval (m*x-m) := by
  simp [Hpoly, affine_eval]

lemma Hpoly_even (m : ℕ) (x : ℝ) : (Hpoly m).eval (-x) = (Hpoly m).eval x := by
  simp only [Hpoly_eval]
  convert Rpoly_reflect (2*m) ((m : ℝ)*x-m) using 1 <;> congr 1 <;> push_cast <;> ring

lemma Qpoly_expand (m : ℕ) : Polynomial.expand ℝ 2 (Qpoly m) = Hpoly m :=
  even_expand_contract _ (Hpoly_even m)

lemma Qpoly_eval_sq (m : ℕ) (x : ℝ) : (Qpoly m).eval (x^2) = (Hpoly m).eval x := by
  rw [← Qpoly_expand, Polynomial.expand_eval]

lemma affine_natDegree (m : ℕ) (hm : 1 ≤ m) : (affine m).natDegree = 1 := by
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold affine
  compute_degree!
  omega

lemma Ppoly_degree (m : ℕ) (hm : 1 ≤ m) : (Ppoly m).degree = (2*m : ℕ) := by
  have hr := (Rpoly_roots m hm).1
  have hn : (Rpoly m).natDegree = 2*m := Polynomial.natDegree_eq_of_degree_eq_some hr
  have hpnd : (Ppoly m).natDegree = 2*m := by
    rw [Ppoly, Polynomial.natDegree_comp, hn, affine_natDegree m hm, mul_one]
  have hp : Ppoly m ≠ 0 := by intro h; simp [h] at hpnd; omega
  rw [Polynomial.degree_eq_natDegree hp, hpnd]

lemma Hpoly_degree (m : ℕ) (hm : 1 ≤ m) : (Hpoly m).degree = (4*m : ℕ) := by
  have hr := (Rpoly_roots (2*m) (by omega)).1
  have hn : (Rpoly (2*m)).natDegree = 2*(2*m) := Polynomial.natDegree_eq_of_degree_eq_some hr
  have hpnd : (Hpoly m).natDegree = 4*m := by
    rw [Hpoly, Polynomial.natDegree_comp, hn, affine_natDegree m hm, mul_one]
    omega
  have hp : Hpoly m ≠ 0 := by intro h; simp [h] at hpnd; omega
  rw [Polynomial.degree_eq_natDegree hp, hpnd]

lemma Qpoly_degree (m : ℕ) (hm : 1 ≤ m) : (Qpoly m).degree = (2*m : ℕ) := by
  have hn := Polynomial.natDegree_eq_of_degree_eq_some (Hpoly_degree m hm)
  rw [← Qpoly_expand, Polynomial.natDegree_expand] at hn
  have hqnd : (Qpoly m).natDegree = 2*m := by omega
  have hq : Qpoly m ≠ 0 := by intro h; simp [h] at hqnd; omega
  rw [Polynomial.degree_eq_natDegree hq, hqnd]

lemma Ppoly_symmetry (m : ℕ) (x : ℝ) : (Ppoly m).eval x = (Ppoly m).eval (1-x) := by
  simp only [Ppoly_eval]
  convert (Rpoly_reflect m ((m : ℝ)*x-m)).symm using 1 <;> congr 1 <;> ring

lemma affine_complex (m : ℕ) (z : ℂ) :
    ((affine m).map (algebraMap ℝ ℂ)).eval z = (m : ℂ)*z-m := by
  simp [affine]

lemma Ppoly_roots (m : ℕ) (hm : 1 ≤ m) (z : ℂ)
    (hz : ((Ppoly m).map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc 0 1 := by
  rw [Ppoly, Polynomial.map_comp, Polynomial.eval_comp, affine_complex] at hz
  have h := (Rpoly_roots m hm).2 _ hz
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [Complex.sub_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    mul_zero, zero_add, sub_zero, Complex.sub_re, Complex.mul_re, zero_mul,
    Set.mem_Icc, add_zero] at h
  refine ⟨(_root_.mul_eq_zero.mp h.1).resolve_left (ne_of_gt hmpos), ?_, ?_⟩ <;> nlinarith [h.2.1, h.2.2]

lemma Qpoly_roots (m : ℕ) (hm : 1 ≤ m) (z : ℂ)
    (hz : ((Qpoly m).map (algebraMap ℝ ℂ)).eval (z^2) = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (-1) 1 := by
  have he : ((Hpoly m).map (algebraMap ℝ ℂ)).eval z = 0 := by
    rw [← Qpoly_expand, Polynomial.map_expand, Polynomial.expand_eval]
    exact hz
  rw [Hpoly, Polynomial.map_comp, Polynomial.eval_comp, affine_complex] at he
  have h := (Rpoly_roots (2*m) (by omega)).2 _ he
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  simp only [Complex.sub_im, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    mul_zero, zero_add, sub_zero, Complex.sub_re, Complex.mul_re, zero_mul,
    Set.mem_Icc, Nat.cast_mul, Nat.cast_ofNat, add_zero] at h
  refine ⟨(_root_.mul_eq_zero.mp h.1).resolve_left (ne_of_gt hmpos), ?_, ?_⟩ <;> nlinarith [h.2.1, h.2.2]

end A103885Proof

namespace A103885Proof

noncomputable def F (n k : ℕ) : ℝ := (n.choose k : ℝ) * ((2*n+k-1).choose (n-1) : ℝ)
noncomputable def G (n k : ℕ) : ℝ := ((n-1).choose k : ℝ) * ((2*n+k).choose (n-1) : ℝ)

lemma F_zero (n k : ℕ) (hk : n < k) : F n k = 0 := by simp [F, Nat.choose_eq_zero_of_lt hk]
lemma G_zero (n k : ℕ) (hk : n-1 < k) : G n k = 0 := by simp [G, Nat.choose_eq_zero_of_lt hk]

lemma F_factorial (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    F n k = (n : ℝ) * ((2*n+k-1).factorial : ℝ) /
      ((k.factorial : ℝ) * ((n-k).factorial : ℝ) * ((n+k).factorial : ℝ)) := by
  unfold F
  rw [Nat.cast_choose ℝ hk, Nat.cast_choose ℝ (by omega : n-1 ≤ 2*n+k-1)]
  have hsub : 2*n+k-1-(n-1) = n+k := by omega
  rw [hsub]
  have hfac : (n.factorial : ℝ) = n * ((n-1).factorial : ℝ) := by
    have hf := Nat.factorial_succ (n-1)
    rw [Nat.sub_add_cancel hn] at hf
    exact_mod_cast hf
  rw [hfac]
  have h0 : ((n-1).factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma G_factorial (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n-1) :
    G n k = ((2*n+k).factorial : ℝ) /
      ((k.factorial : ℝ) * ((n-1-k).factorial : ℝ) * ((n+k+1).factorial : ℝ)) := by
  unfold G
  rw [Nat.cast_choose ℝ hk, Nat.cast_choose ℝ (by omega : n-1 ≤ 2*n+k)]
  have hsub : 2*n+k-(n-1) = n+k+1 := by omega
  rw [hsub]
  have h0 : ((n-1).factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma factorial_pred (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) = n * ((n-1).factorial : ℝ) := by
  have h := Nat.factorial_succ (n-1)
  rw [Nat.sub_add_cancel hn] at h
  exact_mod_cast h

lemma F_step_k (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    ((k : ℝ)+1) * (n+k+1) * F n (k+1) =
      ((n : ℝ)-k) * (2*n+k) * F n k := by
  by_cases hkn : k = n
  · subst k
    rw [F_zero n (n+1) (by omega)]
    ring
  have hkn : k < n := by omega
  rw [F_factorial n (k+1) hn (by omega), F_factorial n k hn hk]
  have h1 : 2*n+(k+1)-1 = (2*n+k-1)+1 := by omega
  have h2 : n-k = (n-(k+1))+1 := by omega
  have h3 : n+(k+1) = (n+k)+1 := by omega
  rw [h1, h2, h3, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ 2*n+k), Nat.cast_sub (by omega : k+1 ≤ n)]
  push_cast
  have hnk : (k : ℝ) < n := by exact_mod_cast hkn
  field_simp (disch := (first | positivity | linarith))
  <;> ring

lemma F_step_n (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n+1) :
    F n k = ((n : ℝ) * (n+1-k) * (n+k+1) /
      ((n+1) * (2*n+k) * (2*n+k+1))) * F (n+1) k := by
  by_cases hkn : k = n+1
  · subst k
    rw [F_zero n (n+1) (by omega)]
    push_cast
    ring
  have hkn : k ≤ n := by omega
  rw [F_factorial n k hn hkn, F_factorial (n+1) k (by omega) hk]
  have h1 : 2*(n+1)+k-1 = ((2*n+k-1)+1)+1 := by omega
  have h2 : n+1-k = (n-k)+1 := by omega
  have h3 : n+1+k = (n+k)+1 := by omega
  rw [h1, h2, h3, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ 2*n+k), Nat.cast_sub hkn]
  push_cast
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hnk : (k : ℝ) ≤ n := by exact_mod_cast hkn
  field_simp (disch := (first | positivity | linarith))
  <;> ring

lemma G_shift (n k : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * G n k = ((k : ℝ)+1) * F n (k+1) := by
  have h := Nat.add_one_mul_choose_eq (n-1) k
  rw [Nat.sub_add_cancel hn] at h
  have hc : (n : ℝ) * ((n-1).choose k : ℝ) = (n.choose (k+1) : ℝ) * (k+1) := by
    exact_mod_cast h
  unfold F G
  have he : 2*n+(k+1)-1 = 2*n+k := by omega
  rw [he]
  linear_combination ((2*n+k).choose (n-1) : ℝ) * hc

lemma G_ratio (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    G n k = (((n : ℝ)-k)*(2*n+k)/(n*(n+k+1))) * F n k := by
  have h := F_step_k n k hn hk
  have hg := G_shift n k hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  field_simp
  linear_combination (n+k+1) * hg + h

lemma G_step_n (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n+1) :
    G n k = (((n : ℝ)+1-k)*(n-k)/((n+1)*(2*n+k+1))) * F (n+1) k := by
  by_cases hkn : k = n+1
  · subst k
    rw [G_zero n (n+1) (by omega)]
    push_cast
    ring
  have hkn : k ≤ n := by omega
  rw [G_ratio n k hn hkn, F_step_n n k hn hk]
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  field_simp
  <;> ring

lemma F_step_k_div (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    F n (k+1) = (((n : ℝ)-k)*(2*n+k)/((k+1)*(n+k+1))) * F n k := by
  have h := F_step_k n k hn hk
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  field_simp
  linear_combination h

noncomputable def certA (n k : ℝ) : ℝ :=
  k*(k+n+1)*(10*k*n^2+10*k*n+2*k-28*n^3-47*n^2-25*n-4) /
    ((k+2*n)*(n+1)*(k+2*n+1))
noncomputable def certG (n k : ℝ) : ℝ :=
  k*(2*n+1)*(k-n-1)*(4*k*n+2*k+3*n^2+7*n+2) /
    ((k+2*n)*(n+1)*(k+2*n+1))

lemma telescope_A (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n+1) :
    (2*(n : ℝ)+1)*(2*n+2)*F (n+1) k -
      (32*(n : ℝ)^2+34*n+8)*F n k - (20*(n : ℝ)^2+20*n+4)*G n k =
    certA n (k+1) * F (n+1) (k+1) - certA n k * F (n+1) k := by
  rw [F_step_n n k hn hk, G_step_n n k hn hk,
    F_step_k_div (n+1) k (by omega) hk]
  unfold certA
  push_cast
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  field_simp
  <;> ring

lemma telescope_G (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n+1) :
    (2*(n : ℝ)+1)*(2*n+2)*G (n+1) k -
      (20*(n : ℝ)^2+18*n+4)*F n k - (12*(n : ℝ)^2+10*n+2)*G n k =
    certG n (k+1) * F (n+1) (k+1) - certG n k * F (n+1) k := by
  rw [G_ratio (n+1) k (by omega) hk, F_step_n n k hn hk, G_step_n n k hn hk,
    F_step_k_div (n+1) k (by omega) hk]
  unfold certG
  push_cast
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  field_simp
  <;> ring

noncomputable def aval (n : ℕ) : ℝ := if n = 0 then 1 else ∑ k ∈ range (n+1), F n k
noncomputable def cval (n : ℕ) : ℝ := if n = 0 then -1 else ∑ k ∈ range n, G n k

lemma sum_F (n : ℕ) (hn : 1 ≤ n) : ∑ k ∈ range (n+2), F n k = aval n := by
  simp [Finset.sum_range_succ, F_zero n (n+1) (by omega), aval, show n ≠ 0 by omega]

lemma sum_G (n : ℕ) (hn : 1 ≤ n) : ∑ k ∈ range (n+2), G n k = cval n := by
  simp [Finset.sum_range_succ, G_zero n (n+1) (by omega), G_zero n n (by omega),
    cval, show n ≠ 0 by omega]

lemma aval_step (n : ℕ) :
    (2*(n : ℝ)+1)*(2*n+2)*aval (n+1) =
      (32*(n : ℝ)^2+34*n+8)*aval n + (20*(n : ℝ)^2+20*n+4)*cval n := by
  by_cases hn : n = 0
  · subst n; norm_num [aval, cval, F, Finset.sum_range_succ, Nat.choose]
  have hn : 1 ≤ n := by omega
  have h := Finset.sum_congr rfl (fun k (hk : k ∈ range (n+2)) =>
    telescope_A n k hn (by have := Finset.mem_range.mp hk; omega))
  have ht := Finset.sum_range_sub (fun k : ℕ => certA n k * F (n+1) k) (n+2)
  push_cast at ht
  rw [ht] at h
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  rw [sum_F n hn, sum_G n hn] at h
  have hf : ∑ k ∈ range (n+2), F (n+1) k = aval (n+1) := by simp [aval]
  rw [hf, F_zero (n+1) (n+2) (by omega)] at h
  norm_num [certA] at h
  linarith

lemma cval_step (n : ℕ) :
    (2*(n : ℝ)+1)*(2*n+2)*cval (n+1) =
      (20*(n : ℝ)^2+18*n+4)*aval n + (12*(n : ℝ)^2+10*n+2)*cval n := by
  by_cases hn : n = 0
  · subst n; norm_num [aval, cval, F, G, Finset.sum_range_succ, Nat.choose]
  have hn : 1 ≤ n := by omega
  have h := Finset.sum_congr rfl (fun k (hk : k ∈ range (n+2)) =>
    telescope_G n k hn (by have := Finset.mem_range.mp hk; omega))
  have ht := Finset.sum_range_sub (fun k : ℕ => certG n k * F (n+1) k) (n+2)
  push_cast at ht
  rw [ht] at h
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  rw [sum_F n hn, sum_G n hn] at h
  have hg : ∑ k ∈ range (n+2), G (n+1) k = cval (n+1) := by
    rw [show n+2 = (n+1)+1 by omega, Finset.sum_range_succ]
    simp [cval, G_zero (n+1) (n+1) (by omega)]
  rw [hg, F_zero (n+1) (n+2) (by omega)] at h
  norm_num [certG] at h
  linarith

end A103885Proof

open scoped Matrix

namespace A103885Proof

noncomputable def scale (m : ℕ) (x : ℝ) : ℝ := ∏ k ∈ range (2*m), (2*x+k+1)

lemma scale_zero (x : ℝ) : scale 0 x = 1 := by simp [scale]

lemma scale_succ (m : ℕ) (x : ℝ) :
    scale (m+1) x = ((2*(x+m)+1)*(2*(x+m)+2))*scale m x := by
  unfold scale
  rw [show 2*(m+1) = (2*m+1)+1 by omega, Finset.prod_range_succ, Finset.prod_range_succ]
  push_cast
  ring

lemma scale_pos (m : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 < scale m x := by
  apply Finset.prod_pos
  intro k _
  positivity

lemma block_det (m : ℕ) (x : ℝ) :
    (block m x).det = (-1 : ℝ)^m * scale m x * scale m (x-1/2) := by
  induction m with
  | zero => simp [block, scale_zero]
  | succ m ih =>
    rw [block, Matrix.det_mul, T_det, ih, scale_succ, scale_succ, pow_succ]
    ring

noncomputable def vseq (n : ℕ) : Fin 2 → ℝ := ![aval n, 2*aval n+4*cval n]

lemma vseq_step (n : ℕ) :
    (T (n : ℝ)) *ᵥ vseq n = ((2*(n : ℝ)+1)*(2*n+2)) • vseq (n+1) := by
  ext i
  fin_cases i <;> simp [T, vseq, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · linear_combination -(aval_step n)
  · linear_combination -2*(aval_step n) - 4*(cval_step n)

lemma block_vseq (m n : ℕ) :
    block m (n : ℝ) *ᵥ vseq n = scale m n • vseq (n+m) := by
  induction m with
  | zero => simp [block, scale_zero]
  | succ m ih =>
    rw [block, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul]
    rw [show (n : ℝ)+m = ↑(n+m) by push_cast; rfl, vseq_step]
    rw [smul_smul, scale_succ]
    congr 1
    push_cast
    ring

lemma eliminate (M N : Matrix (Fin 2) (Fin 2) ℝ) (u v w : Fin 2 → ℝ) (s t d : ℝ)
    (hs : s ≠ 0) (hM : M *ᵥ u = s • v) (hN : N *ᵥ v = t • w) (hd : M.det = s*d) :
    t*M 0 1*w 0 + d*N 0 1*u 0 = (N*M) 0 1*v 0 := by
  have h0 := congrFun hM 0
  have h1 := congrFun hM 1
  have h2 := congrFun hN 0
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at h0 h1 h2
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  apply mul_left_cancel₀ hs
  linear_combination -s*M 0 1*h2 - N 0 1*(M 0 1*h1-M 1 1*h0) - N 0 1*u 0*hd

lemma aval_recurrence (m l : ℕ) :
    scale m (l+m) * (Rpoly m).eval (l : ℝ) * aval (l+2*m) +
      ((-1 : ℝ)^m * scale m ((l : ℝ)-1/2)) * (Rpoly m).eval ((l : ℝ)+m) * aval l =
    (Rpoly (2*m)).eval (l : ℝ) * aval (l+m) := by
  have h := eliminate (block m (l : ℝ)) (block m ((l : ℝ)+m))
    (vseq l) (vseq (l+m)) (vseq ((l+m)+m)) (scale m l) (scale m (l+m))
    ((-1 : ℝ)^m*scale m ((l : ℝ)-1/2))
    (ne_of_gt (scale_pos m (Nat.cast_nonneg l))) (block_vseq m l)
    (by simpa only [Nat.cast_add] using block_vseq m (l+m))
    (by rw [block_det]; ring)
  rw [← block_add m m (l : ℝ)] at h
  simp only [vseq, Matrix.cons_val_zero, Rpoly_eval] at *
  simpa only [two_mul, Nat.add_assoc] using h

end A103885Proof

namespace A103885Proof

lemma prod_Ioc_range (f : ℕ → ℝ) (N : ℕ) :
    (∏ k ∈ Finset.Ioc 0 N, f k) = ∏ k ∈ range N, f (k+1) := by
  have hI : Finset.Ioc 0 N = Finset.Ico 1 (N+1) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hI, Finset.prod_Ico_eq_prod_range]
  simp [Nat.add_comm]

lemma scale_plus (m n : ℕ) : scale m ((m : ℝ)*n) = prod_factor_plus m n := by
  unfold prod_factor_plus product_indices
  rw [prod_Ioc_range]
  unfold scale
  apply Finset.prod_congr rfl
  intro k _
  push_cast
  ring

lemma scale_minus (m n : ℕ) :
    scale m ((m : ℝ)*n-m-1/2) = prod_factor_minus m n := by
  unfold prod_factor_minus product_indices
  rw [prod_Ioc_range]
  unfold scale
  rw [← Finset.prod_range_reflect (fun k : ℕ => 2*(m : ℝ)*n-↑(k+1)) (2*m)]
  apply Finset.prod_congr rfl
  intro k hk
  have hk : k < 2*m := Finset.mem_range.mp hk
  rw [Nat.cast_add, Nat.cast_sub (by omega : k ≤ 2*m-1),
    Nat.cast_sub (by omega : 1 ≤ 2*m)]
  push_cast
  ring

lemma aval_eq (n : ℕ) : aval n = (A103885 n : ℝ) := by
  unfold aval A103885
  split_ifs <;> simp [F]

lemma subseq_eq (m n : ℕ) : A103885_subsequence_real m n = aval (m*n) := by
  exact (aval_eq (m*n)).symm

lemma recurrence_final (m n : ℕ) (hn : 1 ≤ n) :
    (prod_factor_plus m n * (Ppoly m).eval (n : ℝ)) * (A103885_subsequence_real m (n+1)) +
    ((-1 : ℝ)^m * prod_factor_minus m n * (Ppoly m).eval (-(n : ℝ))) *
      (A103885_subsequence_real m (n-1)) =
    (Qpoly m).eval ((n : ℝ)^2) * (A103885_subsequence_real m n) := by
  have h := aval_recurrence m (m*(n-1))
  have hmid : m*(n-1)+m = m*n := by
    calc
      m*(n-1)+m = m*((n-1)+1) := by ring
      _ = m*n := by rw [Nat.sub_add_cancel hn]
  have htop : m*(n-1)+2*m = m*(n+1) := by nlinarith [hmid]
  have hc : ((m*(n-1) : ℕ) : ℝ) = (m : ℝ)*n-m := by
    rw [Nat.cast_mul, Nat.cast_sub hn]
    push_cast
    ring
  rw [hmid, htop, hc, show (m : ℝ)*n-m+m = m*n by ring, scale_plus, scale_minus] at h
  rw [Qpoly_eval_sq, Hpoly_eval, Ppoly_eval, Ppoly_eval]
  have href : (Rpoly m).eval ((m : ℝ) * -(n : ℝ) - m) =
      (Rpoly m).eval ((m : ℝ)*n) := by
    convert Rpoly_reflect m ((m : ℝ)*n) using 1 <;> congr 1 <;> ring
  rw [href]
  simp only [subseq_eq]
  exact h

end A103885Proof

/--
The recurrence given below can be rewritten in the form
(2*n+1)*(2*n+2)*P(2,n)*a(n+1) - (2*n-1)*(2*n-2)*P(2,-n)*a(n-1) = Q(2,n^2)*a(n), where the polynomial Q(2,n) = 4*(55*n^2 - 34*n + 3) and the polynomial P(2,n) = 5*n^2 - 5*n + 1 satisfies the symmetry condition P(2,n) = P(2,1-n) and has real zeros.
More generally, for fixed m = 1,2,3,..., we conjecture that the sequence b(n) := a(m*n) satisfies a recurrence of the form ( Product_{k = 1..2*m} (2*m*n + k) ) * P(2*m,n)*b(n+1) + (-1)^m*( Product_{k = 1..2*m} (2*m*n - k) ) * P(2*m,-n)*b(n-1) = Q(2*m,n^2)*b(n), where the polynomials P(2*m,n) and Q(2*m,n) have degree 2*m. Conjecturally, the polynomial P(2*m,n) = P(2*m,1-n) and has real zeros in the interval [0, 1]. The 4*m zeros of the polynomial Q(2*m,n^2) seem to belong to the interval [-1, 1] and 4*m - 2 of these zeros appear to be approximated by the rational numbers +- k/(3*m), where 1 <= k <= 3*m - 2, k not a multiple of 3.
-/
theorem oeis_a103885_conjecture_0 (m : ℕ) (hm : 1 ≤ m) :
    ∃ (P Q : Polynomial ℝ),
      -- P and Q have degree 2m
      P.degree = (2 * m : ℕ) ∧ Q.degree = (2 * m : ℕ) ∧
      -- The recurrence relation holds for all n >= 1
      (∀ (n : ℕ) (hn : 1 ≤ n),
        (prod_factor_plus m n * P.eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +

        ((-1 : ℝ) ^ m * prod_factor_minus m n * P.eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =

        (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real m n)) ∧

      -- P symmetry: P(x) = P(1-x)
      (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧

      -- P has real zeros in [0, 1]: all complex zeros are real and in [0, 1]
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧

      -- Q zero properties: The zeros of Q(x^2) are real and in [-1, 1].
      (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1)) :=
  by
    refine ⟨A103885Proof.Ppoly m, A103885Proof.Qpoly m,
      A103885Proof.Ppoly_degree m hm, A103885Proof.Qpoly_degree m hm,
      A103885Proof.recurrence_final m, A103885Proof.Ppoly_symmetry m,
      A103885Proof.Ppoly_roots m hm, A103885Proof.Qpoly_roots m hm⟩

theorem oeis_a103885_conjecture_0.disproof : ¬ (type_of% @oeis_a103885_conjecture_0) := sorry
