import FormalConjectures.Util.ProblemImports

set_option linter.all false

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

lemma A103885_zero : A103885 0 = 1 := rfl

lemma A103885_one : A103885 1 = 2 := by
  unfold A103885
  have hne : ¬ (1 = 0) := Nat.succ_ne_zero 0
  simp [hne]
  rw [Finset.range_add_one, Finset.sum_insert (by simp), Finset.range_one,
      Finset.sum_singleton]
  simp [Nat.choose_self]

lemma A103885_two : A103885 2 = 16 := by
  unfold A103885
  have hne : ¬ (2 = 0) := Nat.succ_ne_zero 1
  simp [hne]
  rw [show Finset.range (2 + 1) = Finset.range 3 from rfl]
  rw [Finset.range_add_one, Finset.sum_insert (by simp),
      Finset.range_add_one, Finset.sum_insert (by simp),
      Finset.range_one, Finset.sum_singleton]
  simp [Nat.choose_succ_succ, Nat.choose_zero_right, Nat.choose_self]

def A103885_term (n k : ℕ) : ℕ :=
  n.choose k * (2 * n + k - 1).choose (n - 1)

lemma A103885_eq_sum {n : ℕ} (hn : 0 < n) :
    A103885 n = (range (n + 1)).sum (fun k => A103885_term n k) := by
  simp [A103885, A103885_term, hn.ne']

noncomputable def P1 : Polynomial ℝ :=
  C (5 : ℝ) * X ^ 2 - C (5 : ℝ) * X + C (1 : ℝ)

noncomputable def Q1 : Polynomial ℝ :=
  C (4 : ℝ) * (C (55 : ℝ) * X ^ 2 - C (34 : ℝ) * X + C (3 : ℝ))

lemma P1_eval (x : ℝ) : P1.eval x = 5 * x ^ 2 - 5 * x + 1 := by
  unfold P1; simp

lemma Q1_eval (x : ℝ) : Q1.eval x = 4 * (55 * x ^ 2 - 34 * x + 3) := by
  unfold Q1; simp

lemma P1_degree : P1.degree = (2 : ℕ) := by
  unfold P1; compute_degree!

lemma Q1_degree : Q1.degree = (2 : ℕ) := by
  unfold Q1; compute_degree!

lemma P1_symmetry (x : ℝ) : P1.eval x = P1.eval (1 - x) := by
  simp [P1_eval]; ring

private def product_indices (m : ℕ) : Finset ℕ :=
  Finset.Ioc 0 (2 * m)

noncomputable def prod_factor_plus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k => ((2 * m * n : ℝ) + (k : ℝ))

noncomputable def prod_factor_minus (m n : ℕ) : ℝ :=
  (product_indices m).prod fun k => ((2 * m * n : ℝ) - (k : ℝ))


lemma P1_eval_neg (n : ℕ) : P1.eval (-(n : ℝ)) = 5 * (n : ℝ) ^ 2 + 5 * n + 1 := by
  rw [P1_eval, neg_sq, mul_neg, sub_neg_eq_add]

lemma P1_map_eval (z : ℂ) :
    (P1.map (algebraMap ℝ ℂ)).eval z = 5 * z ^ 2 - 5 * z + 1 := by
  unfold P1; simp

lemma Q1_map_eval (w : ℂ) :
    (Q1.map (algebraMap ℝ ℂ)).eval w = 4 * (55 * w ^ 2 - 34 * w + 3) := by
  unfold Q1; simp

lemma P1_roots_mem
    (z : ℂ) (hz : (P1.map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (0 : ℝ) 1 := by
  have hz' : (5 : ℂ) * z ^ 2 - 5 * z + 1 = 0 := (P1_map_eval z).symm.trans hz
  have hre : (5 : ℝ) * (z.re * z.re - z.im * z.im) - 5 * z.re + 1 = 0 := by
    have := congrArg Complex.re hz'
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.add_re] at this
    linarith
  have him : (5 : ℝ) * z.im * (2 * z.re - 1) = 0 := by
    have := congrArg Complex.im hz'
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_im, Complex.add_im] at this
    linarith
  have hz0 : z.im = 0 := by
    have h5 : (5 : ℝ) ≠ 0 := by norm_num
    have him' : z.im * (2 * z.re - 1) = 0 := by
      have : (5 : ℝ) * z.im * (2 * z.re - 1) = 5 * (z.im * (2 * z.re - 1)) := by
        ac_rfl
      exact (mul_eq_zero.mp (this.symm.trans him)).resolve_left h5
    rcases (mul_eq_zero.mp him') with him0 | hhalf
    · exact him0
    · have hre0 : z.re = 1 / 2 := by linarith
      rw [hre0] at hre
      nlinarith [sq_nonneg z.im]
  have hquad : (5 : ℝ) * z.re ^ 2 - 5 * z.re + 1 = 0 := by
    simp [hz0, pow_two] at hre
    linarith
  have hsq : (2 * z.re - 1) ^ 2 = (1 / 5 : ℝ) := by
    have hex : (5 : ℝ) * (2 * z.re - 1) ^ 2 - 1 =
        4 * (5 * z.re ^ 2 - 5 * z.re + 1) := by
      simp [pow_two]; linarith
    have : (5 : ℝ) * (2 * z.re - 1) ^ 2 - 1 = 0 := by
      simpa [hquad] using hex
    linarith
  have hmem : z.re ∈ Set.Icc (0 : ℝ) 1 := by
    have hlt : (2 * z.re - 1) ^ 2 < (1 : ℝ) ^ 2 := by
      rw [hsq]; norm_num
    have habs : |2 * z.re - 1| < 1 := by
      simpa using (sq_lt_sq.mp hlt)
    have hii := abs_lt.mp habs
    exact ⟨by linarith, by linarith⟩
  exact ⟨hz0, hmem⟩

lemma Q1_sq_roots_mem
    (z : ℂ) (hz : (Q1.map (algebraMap ℝ ℂ)).eval (z ^ 2) = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (-1 : ℝ) 1 := by
  have hz' : (4 : ℂ) * (55 * (z ^ 2) ^ 2 - 34 * z ^ 2 + 3) = 0 :=
    (Q1_map_eval (z ^ 2)).symm.trans hz
  have hp : (55 : ℂ) * (z ^ 2) ^ 2 - 34 * z ^ 2 + 3 = 0 :=
    (mul_eq_zero.mp hz').resolve_left (by norm_num)
  set w : ℂ := z ^ 2
  have hw0 : (55 : ℂ) * w ^ 2 - 34 * w + 3 = 0 := hp
  have hre : (55 : ℝ) * (w.re * w.re - w.im * w.im) - 34 * w.re + 3 = 0 := by
    have := congrArg Complex.re hw0
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.add_re] at this
    linarith
  have him : (2 : ℝ) * w.im * (55 * w.re - 17) = 0 := by
    have := congrArg Complex.im hw0
    simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_im, Complex.add_im] at this
    linarith
  have himw : w.im = 0 := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    have him' : w.im * (55 * w.re - 17) = 0 := by
      have : (2 : ℝ) * w.im * (55 * w.re - 17) = 2 * (w.im * (55 * w.re - 17)) := by
        ac_rfl
      exact (mul_eq_zero.mp (this.symm.trans him)).resolve_left h2
    rcases (mul_eq_zero.mp him') with him0 | hmid
    · exact him0
    · have hwre0 : w.re = 17 / 55 := by linarith
      rw [hwre0] at hre
      nlinarith [sq_nonneg w.im]
  have hwre : (55 : ℝ) * w.re ^ 2 - 34 * w.re + 3 = 0 := by
    simp [himw, pow_two] at hre
    linarith
  have hsq : (55 * w.re - 17) ^ 2 = (124 : ℝ) := by
    have hex : (55 * w.re - 17) ^ 2 - 124 =
        55 * (55 * w.re ^ 2 - 34 * w.re + 3) := by
      simp [pow_two]; linarith
    have : (55 * w.re - 17) ^ 2 - 124 = 0 := by simpa [hwre] using hex
    linarith
  have w_nonneg : (0 : ℝ) ≤ w.re := by
    have hlt : (55 * w.re - 17) ^ 2 < (17 : ℝ) ^ 2 := by
      rw [hsq]; norm_num
    have habs : |55 * w.re - 17| < 17 := by simpa using (sq_lt_sq.mp hlt)
    have hii := abs_lt.mp habs
    linarith
  have w_le1 : w.re ≤ 1 := by
    have hlt : (55 * w.re - 17) ^ 2 < (38 : ℝ) ^ 2 := by
      rw [hsq]; norm_num
    have habs : |55 * w.re - 17| < 38 := by simpa using (sq_lt_sq.mp hlt)
    have hii := abs_lt.mp habs
    linarith
  have himz : z.im = 0 := by
    have hre' : z.re * z.re - z.im * z.im = w.re := by
      have : (z ^ 2).re = z.re * z.re - z.im * z.im := by
        simp [pow_two, Complex.mul_re]
      exact this.symm.trans (rfl : (z ^ 2).re = w.re)
    have hprod : z.re * z.im = 0 := by
      have : (z ^ 2).im = 0 := himw
      simp [pow_two, Complex.mul_im] at this
      linarith
    rcases mul_eq_zero.mp hprod with h | h
    · have : -(z.im * z.im) = w.re := by simpa [h] using hre'
      nlinarith [sq_nonneg z.im, w_nonneg]
    · exact h
  have hbound : z.re ∈ Set.Icc (-1 : ℝ) 1 := by
    have heq : z.re * z.re = w.re := by
      have : (z ^ 2).re = w.re := rfl
      simp [himz, pow_two, Complex.mul_re, Complex.mul_im] at this
      exact this
    have hle : z.re ^ 2 ≤ (1 : ℝ) := by
      simpa [pow_two] using (le_trans (le_of_eq heq) w_le1)
    exact abs_le.mp ((sq_le_one_iff_abs_le_one z.re).mp hle)
  exact ⟨himz, hbound⟩

lemma Ioc_zero_two : Finset.Ioc 0 2 = ({1, 2} : Finset ℕ) := by
  ext k
  simp only [mem_Ioc, mem_insert, mem_singleton]
  constructor
  · intro ⟨hk0, hk2⟩
    interval_cases k <;> simp
  · intro h
    rcases h with h | h <;> subst k <;> simp

lemma prod_factor_plus_one (n : ℕ) :
    prod_factor_plus 1 n = (2 * n + 1 : ℝ) * (2 * n + 2) := by
  unfold prod_factor_plus product_indices
  rw [Ioc_zero_two]
  simp

lemma prod_factor_minus_one (n : ℕ) :
    prod_factor_minus 1 n = (2 * n - 1 : ℝ) * (2 * n - 2) := by
  unfold prod_factor_minus product_indices
  rw [Ioc_zero_two]
  simp





noncomputable def wzS (n k : ℝ) : ℝ :=
  k * (110 * k ^ 2 * n ^ 5 + 30 * k ^ 2 * n ^ 4 - 68 * k ^ 2 * n ^ 3
    - 20 * k ^ 2 * n ^ 2 + 6 * k ^ 2 * n + 2 * k ^ 2
    + 410 * k * n ^ 6 - 260 * k * n ^ 5 - 258 * k * n ^ 4
    + 150 * k * n ^ 3 + 30 * k * n ^ 2 - 10 * k * n - 2 * k
    + 290 * n ^ 7 - 265 * n ^ 6 - 187 * n ^ 5 + 138 * n ^ 4
    + 33 * n ^ 3 - 5 * n ^ 2 - 4 * n)

noncomputable def wzD (n k : ℝ) : ℝ :=
  n * (k - n - 1) * (k + 2 * n - 2) * (k + 2 * n - 1)

noncomputable def alpha1 (n : ℝ) : ℝ :=
  (2 * n + 1) * (2 * n + 2) * (5 * n ^ 2 - 5 * n + 1)

noncomputable def gamma1 (n : ℝ) : ℝ :=
  (2 * n - 1) * (2 * n - 2) * (5 * n ^ 2 + 5 * n + 1)

noncomputable def beta1 (n : ℝ) : ℝ :=
  4 * (55 * n ^ 4 - 34 * n ^ 2 + 3)

/-! Expression trees for the WZ identity, certified by interpolation. -/

inductive BivE
  | c : ℤ → BivE
  | varN : BivE
  | varK : BivE
  | add : BivE → BivE → BivE
  | mul : BivE → BivE → BivE
  | neg : BivE → BivE

namespace BivE

def evalZ : BivE → ℤ → ℤ → ℤ
  | c a, _, _ => a
  | varN, n, _ => n
  | varK, _, k => k
  | add a b, n, k => a.evalZ n k + b.evalZ n k
  | mul a b, n, k => a.evalZ n k * b.evalZ n k
  | neg a, n, k => -a.evalZ n k

def evalR : BivE → ℝ → ℝ → ℝ
  | c a, _, _ => (a : ℝ)
  | varN, n, _ => n
  | varK, _, k => k
  | add a b, n, k => a.evalR n k + b.evalR n k
  | mul a b, n, k => a.evalR n k * b.evalR n k
  | neg a, n, k => -a.evalR n k

def degN : BivE → ℕ
  | c _ => 0
  | varN => 1
  | varK => 0
  | add a b => max a.degN b.degN
  | mul a b => a.degN + b.degN
  | neg a => a.degN

def degK : BivE → ℕ
  | c _ => 0
  | varN => 0
  | varK => 1
  | add a b => max a.degK b.degK
  | mul a b => a.degK + b.degK
  | neg a => a.degK

def pow : BivE → ℕ → BivE
  | _, 0 => c 1
  | e, m + 1 => e.mul (e.pow m)

def substKsucc : BivE → BivE
  | c a => c a
  | varN => varN
  | varK => add varK (c 1)
  | add a b => add a.substKsucc b.substKsucc
  | mul a b => mul a.substKsucc b.substKsucc
  | neg a => neg a.substKsucc

def substKN : BivE → BivE
  | c a => c a
  | varN => varN
  | varK => varN
  | add a b => add a.substKN b.substKN
  | mul a b => mul a.substKN b.substKN
  | neg a => neg a.substKN

lemma evalR_int (e : BivE) (n k : ℤ) :
    e.evalR (n : ℝ) (k : ℝ) = (e.evalZ n k : ℝ) := by
  induction e with
  | c a => simp [evalR, evalZ]
  | varN => simp [evalR, evalZ]
  | varK => simp [evalR, evalZ]
  | add a b iha ihb => simp [evalR, evalZ, iha, ihb]
  | mul a b iha ihb => simp [evalR, evalZ, iha, ihb]
  | neg a ih => simp [evalR, evalZ, ih]

lemma evalR_nat (e : BivE) (n k : ℕ) :
    e.evalR (n : ℝ) (k : ℝ) = (e.evalZ (n : ℤ) (k : ℤ) : ℝ) :=
  e.evalR_int n k

lemma evalR_substKsucc (e : BivE) (n k : ℝ) :
    e.substKsucc.evalR n k = e.evalR n (k + 1) := by
  induction e <;> simp [substKsucc, evalR, *]

lemma evalR_substKN (e : BivE) (n k : ℝ) :
    e.substKN.evalR n k = e.evalR n n := by
  induction e <;> simp [substKN, evalR, *]

lemma exists_poly_n (e : BivE) (k : ℝ) :
    ∃ p : ℝ[X], p.natDegree ≤ e.degN ∧ ∀ n : ℝ, p.eval n = e.evalR n k := by
  induction e with
  | c a =>
      refine ⟨C (a : ℝ), ?_, fun n => ?_⟩
      · simp [degN]
      · simp [evalR]
  | varN =>
      refine ⟨X, ?_, fun n => ?_⟩
      · simp [degN]
      · simp [evalR]
  | varK =>
      refine ⟨C k, ?_, fun n => ?_⟩
      · simp [degN]
      · simp [evalR]
  | add a b iha ihb =>
      obtain ⟨pa, hda, hea⟩ := iha
      obtain ⟨pb, hdb, heb⟩ := ihb
      refine ⟨pa + pb, ?_, fun n => ?_⟩
      · calc
          (pa + pb).natDegree ≤ max pa.natDegree pb.natDegree := natDegree_add_le _ _
          _ ≤ max a.degN b.degN := max_le_max hda hdb
      · simp [evalR, hea, heb]
  | mul a b iha ihb =>
      obtain ⟨pa, hda, hea⟩ := iha
      obtain ⟨pb, hdb, heb⟩ := ihb
      refine ⟨pa * pb, ?_, fun n => ?_⟩
      · calc
          (pa * pb).natDegree ≤ pa.natDegree + pb.natDegree := natDegree_mul_le
          _ ≤ a.degN + b.degN := _root_.add_le_add hda hdb
      · simp [evalR, hea, heb]
  | neg a ih =>
      obtain ⟨pa, hda, hea⟩ := ih
      refine ⟨-pa, ?_, fun n => ?_⟩
      · simpa [degN, natDegree_neg] using hda
      · simp [evalR, hea]

lemma exists_poly_k (e : BivE) (n : ℝ) :
    ∃ p : ℝ[X], p.natDegree ≤ e.degK ∧ ∀ k : ℝ, p.eval k = e.evalR n k := by
  induction e with
  | c a =>
      refine ⟨C (a : ℝ), ?_, fun k => ?_⟩
      · simp [degK]
      · simp [evalR]
  | varN =>
      refine ⟨C n, ?_, fun k => ?_⟩
      · simp [degK]
      · simp [evalR]
  | varK =>
      refine ⟨X, ?_, fun k => ?_⟩
      · simp [degK]
      · simp [evalR]
  | add a b iha ihb =>
      obtain ⟨pa, hda, hea⟩ := iha
      obtain ⟨pb, hdb, heb⟩ := ihb
      refine ⟨pa + pb, ?_, fun k => ?_⟩
      · calc
          (pa + pb).natDegree ≤ max pa.natDegree pb.natDegree := natDegree_add_le _ _
          _ ≤ max a.degK b.degK := max_le_max hda hdb
      · simp [evalR, hea, heb]
  | mul a b iha ihb =>
      obtain ⟨pa, hda, hea⟩ := iha
      obtain ⟨pb, hdb, heb⟩ := ihb
      refine ⟨pa * pb, ?_, fun k => ?_⟩
      · calc
          (pa * pb).natDegree ≤ pa.natDegree + pb.natDegree := natDegree_mul_le
          _ ≤ a.degK + b.degK := _root_.add_le_add hda hdb
      · simp [evalR, hea, heb]
  | neg a ih =>
      obtain ⟨pa, hda, hea⟩ := ih
      refine ⟨-pa, ?_, fun k => ?_⟩
      · simpa [degK, natDegree_neg] using hda
      · simp [evalR, hea]

lemma cast_fin_injective (d : ℕ) :
    Function.Injective (fun i : Fin d => (i.val : ℝ)) := by
  intro a b h
  exact Fin.ext (Nat.cast_injective h)

lemma evalR_eq_zero_of_grid (e : BivE)
    (hgrid : ∀ i j : ℕ, i < e.degN + 1 → j < e.degK + 1 → e.evalZ i j = 0)
    (n k : ℝ) : e.evalR n k = 0 := by
  have hrows : ∀ j : ℕ, j < e.degK + 1 → ∀ nv : ℝ, e.evalR nv (j : ℝ) = 0 := by
    intro j hj nv
    obtain ⟨p, hpdeg, hpe⟩ := exists_poly_n e (j : ℝ)
    have hz : p = 0 := by
      refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero
        p (f := fun i : Fin (e.degN + 1) => (i.val : ℝ))
        (cast_fin_injective _) ?_ ?_
      · intro i
        have hi : (i.val : ℕ) < e.degN + 1 := i.isLt
        rw [hpe, evalR_nat]
        exact_mod_cast hgrid i.val j hi hj
      · have : p.natDegree ≤ e.degN := hpdeg
        have : Fintype.card (Fin (e.degN + 1)) = e.degN + 1 := Fintype.card_fin _
        omega
    rw [← hpe nv, hz, eval_zero]
  obtain ⟨q, hqdeg, hqe⟩ := exists_poly_k e n
  have hz : q = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      q (f := fun j : Fin (e.degK + 1) => (j.val : ℝ))
      (cast_fin_injective _) ?_ ?_
    · intro j
      have hj : (j.val : ℕ) < e.degK + 1 := j.isLt
      rw [hqe, hrows j.val hj]
    · have : q.natDegree ≤ e.degK := hqdeg
      have : Fintype.card (Fin (e.degK + 1)) = e.degK + 1 := Fintype.card_fin _
      omega
  rw [← hqe k, hz, eval_zero]

end BivE

open BivE

def eN : BivE := BivE.varN
def eK : BivE := BivE.varK
def eC (a : ℤ) : BivE := BivE.c a
def e1 : BivE := eC 1
def e2 : BivE := eC 2
def e3 : BivE := eC 3

def eSum : List BivE → BivE
  | [] => eC 0
  | t :: ts => t.add (eSum ts)

def mon (coeff : ℤ) (dk dn : ℕ) : BivE :=
  (eC coeff).mul ((eK.pow dk).mul (eN.pow dn))

def eWzS : BivE :=
  eK.mul (eSum [
    mon 110 2 5, mon 30 2 4, mon (-68) 2 3, mon (-20) 2 2,
    mon 6 2 1, mon 2 2 0, mon 410 1 6, mon (-260) 1 5,
    mon (-258) 1 4, mon 150 1 3, mon 30 1 2, mon (-10) 1 1,
    mon (-2) 1 0, mon 290 0 7, mon (-265) 0 6, mon (-187) 0 5,
    mon 138 0 4, mon 33 0 3, mon (-5) 0 2, mon (-4) 0 1
  ])

def eWzD : BivE :=
  eN.mul (((eK.add (eN.neg)).add (eC (-1))).mul (
    ((eK.add ((eC 2).mul eN)).add (eC (-2))).mul (
      (eK.add ((eC 2).mul eN)).add (eC (-1)))))

def eAlpha1 : BivE :=
  (((eC 2).mul eN).add e1).mul (
    (((eC 2).mul eN).add e2).mul (
      ((eC 5).mul (eN.pow 2)).add (((eC (-5)).mul eN).add e1)))

def eGamma1 : BivE :=
  (((eC 2).mul eN).add (eC (-1))).mul (
    (((eC 2).mul eN).add (eC (-2))).mul (
      ((eC 5).mul (eN.pow 2)).add (((eC 5).mul eN).add e1)))

def eBeta1 : BivE :=
  (eC 4).mul (((eC 55).mul (eN.pow 4)).add (((eC (-34)).mul (eN.pow 2)).add e3))

def eRkN : BivE := (eK.add (eN.neg)).neg.mul (eK.add ((eC 2).mul eN))
def eRkD : BivE := (eK.add e1).mul ((eK.add eN).add e1)
def eRnpN : BivE :=
  (eK.add ((eC 2).mul eN)).mul ((eN.add e1).mul ((eK.add ((eC 2).mul eN)).add e1))
def eRnpD : BivE := eN.mul (((eN.add (eK.neg)).add e1).mul ((eK.add eN).add e1))
def eRnmN : BivE := (eK.add (eN.neg)).neg.mul ((eK.add eN).mul (eN.add (eC (-1))))
def eRnmD : BivE :=
  eN.mul (((eK.add ((eC 2).mul eN)).add (eC (-2))).mul
    ((eK.add ((eC 2).mul eN)).add (eC (-1))))

def eTerm1 : BivE :=
  eWzS.substKsucc.mul (eWzD.mul (eRkN.mul (eRnpD.mul eRnmD)))
def eTerm2 : BivE :=
  eWzS.mul (eWzD.substKsucc.mul (eRkD.mul (eRnpD.mul eRnmD)))
def eTerm3 : BivE :=
  eAlpha1.mul (eRnpN.mul (eWzD.substKsucc.mul (eWzD.mul (eRkD.mul eRnmD))))
def eTerm4 : BivE :=
  eGamma1.mul (eRnmN.mul (eWzD.substKsucc.mul (eWzD.mul (eRkD.mul eRnpD))))
def eTerm5 : BivE :=
  eBeta1.mul (eWzD.substKsucc.mul (eWzD.mul (eRkD.mul (eRnpD.mul eRnmD))))

def eExpr : BivE :=
  eTerm1.add (eTerm2.neg.add (eTerm3.neg.add (eTerm4.add eTerm5)))

def e2n1 : BivE := ((eC 2).mul eN).add e1
def e2n2 : BivE := ((eC 2).mul eN).add e2
def e3n1 : BivE := ((eC 3).mul eN).add e1
def e3n2 : BivE := ((eC 3).mul eN).add e2
def eNp1 : BivE := eN.add e1

def eBdry : BivE :=
  (eWzS.substKN.mul (e2n1.mul e2n2)).add (
    (eAlpha1.mul (eNp1.mul ((eC 3).mul (e3n1.mul (eWzD.substKN.mul e2n2))))).add (
      (eAlpha1.mul ((eC 3).mul (e3n1.mul (e3n2.mul eWzD.substKN)))).add (
        (eBeta1.mul (eWzD.substKN.mul (e2n1.mul e2n2))).neg)))

@[simp] lemma evalR_c (a : ℤ) (n k : ℝ) : (BivE.c a).evalR n k = (a : ℝ) := rfl
@[simp] lemma evalR_varN (n k : ℝ) : BivE.varN.evalR n k = n := rfl
@[simp] lemma evalR_varK (n k : ℝ) : BivE.varK.evalR n k = k := rfl
@[simp] lemma evalR_add' (a b : BivE) (n k : ℝ) :
    (a.add b).evalR n k = a.evalR n k + b.evalR n k := rfl
@[simp] lemma evalR_mul' (a b : BivE) (n k : ℝ) :
    (a.mul b).evalR n k = a.evalR n k * b.evalR n k := rfl
@[simp] lemma evalR_neg' (a : BivE) (n k : ℝ) : a.neg.evalR n k = -a.evalR n k := rfl
@[simp] lemma evalR_eC (a : ℤ) (n k : ℝ) : (eC a).evalR n k = (a : ℝ) := rfl
@[simp] lemma evalR_eN (n k : ℝ) : eN.evalR n k = n := rfl
@[simp] lemma evalR_eK (n k : ℝ) : eK.evalR n k = k := rfl
@[simp] lemma evalR_e1 (n k : ℝ) : e1.evalR n k = 1 := by simp [e1]
@[simp] lemma evalR_e2 (n k : ℝ) : e2.evalR n k = 2 := by simp [e2]
@[simp] lemma evalR_e3 (n k : ℝ) : e3.evalR n k = 3 := by simp [e3]

lemma evalR_pow (e : BivE) (m : ℕ) (n k : ℝ) :
    (e.pow m).evalR n k = (e.evalR n k) ^ m := by
  induction m with
  | zero => simp [BivE.pow]
  | succ m ih =>
      simp [BivE.pow, ih]
      rw [← _root_.pow_succ']

lemma evalR_sum (ts : List BivE) (n k : ℝ) :
    (eSum ts).evalR n k = (ts.map (fun t => t.evalR n k)).sum := by
  induction ts with
  | nil => simp [eSum]
  | cons t ts ih => simp [eSum, ih]

lemma evalR_mon (coeff : ℤ) (dk dn : ℕ) (n k : ℝ) :
    (mon coeff dk dn).evalR n k = (coeff : ℝ) * k ^ dk * n ^ dn := by
  simp [mon, evalR_pow, mul_assoc]

lemma eWzS_evalR (n k : ℝ) : eWzS.evalR n k = wzS n k := by
  unfold eWzS wzS
  simp only [evalR_mul', evalR_eK, evalR_sum, evalR_mon, pow_zero, pow_one,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

lemma eWzD_evalR (n k : ℝ) : eWzD.evalR n k = wzD n k := by
  simp only [eWzD, wzD, evalR_mul', evalR_add', evalR_neg', evalR_eN, evalR_eK,
    evalR_eC]
  ring

lemma eAlpha1_evalR (n k : ℝ) : eAlpha1.evalR n k = alpha1 n := by
  simp only [eAlpha1, alpha1, evalR_mul', evalR_add', evalR_eC, evalR_eN,
    evalR_e1, evalR_e2, evalR_pow]
  ring

lemma eGamma1_evalR (n k : ℝ) : eGamma1.evalR n k = gamma1 n := by
  simp only [eGamma1, gamma1, evalR_mul', evalR_add', evalR_eC, evalR_eN,
    evalR_e1, evalR_pow]
  ring

lemma eBeta1_evalR (n k : ℝ) : eBeta1.evalR n k = beta1 n := by
  simp only [eBeta1, beta1, evalR_mul', evalR_add', evalR_eC, evalR_eN,
    evalR_e3, evalR_pow]
  ring

lemma eRkN_evalR (n k : ℝ) : eRkN.evalR n k = - (k - n) * (k + 2 * n) := by
  simp only [eRkN, evalR_mul', evalR_add', evalR_neg', evalR_eK, evalR_eN,
    evalR_eC]
  ring

lemma eRkD_evalR (n k : ℝ) : eRkD.evalR n k = (k + 1) * (k + n + 1) := by
  simp only [eRkD, evalR_mul', evalR_add', evalR_eK, evalR_eN, evalR_e1]

lemma eRnpN_evalR (n k : ℝ) :
    eRnpN.evalR n k = (k + 2 * n) * (n + 1) * (k + 2 * n + 1) := by
  simp only [eRnpN, evalR_mul', evalR_add', evalR_eK, evalR_eN, evalR_e1,
    evalR_eC]
  ring

lemma eRnpD_evalR (n k : ℝ) :
    eRnpD.evalR n k = n * (n - k + 1) * (k + n + 1) := by
  simp only [eRnpD, evalR_mul', evalR_add', evalR_neg', evalR_eK, evalR_eN,
    evalR_e1]
  ring

lemma eRnmN_evalR (n k : ℝ) :
    eRnmN.evalR n k = - (k - n) * (k + n) * (n - 1) := by
  simp only [eRnmN, evalR_mul', evalR_add', evalR_neg', evalR_eK, evalR_eN,
    evalR_eC]
  ring

lemma eRnmD_evalR (n k : ℝ) :
    eRnmD.evalR n k = n * (k + 2 * n - 2) * (k + 2 * n - 1) := by
  simp only [eRnmD, evalR_mul', evalR_add', evalR_eK, evalR_eN, evalR_eC]
  ring

lemma eExpr_evalR (n k : ℝ) :
    eExpr.evalR n k =
      wzS n (k + 1) * wzD n k * (- (k - n) * (k + 2 * n)) *
        (n * (n - k + 1) * (k + n + 1)) * (n * (k + 2 * n - 2) * (k + 2 * n - 1))
      - wzS n k * wzD n (k + 1) * ((k + 1) * (k + n + 1)) *
        (n * (n - k + 1) * (k + n + 1)) * (n * (k + 2 * n - 2) * (k + 2 * n - 1))
      - alpha1 n * ((k + 2 * n) * (n + 1) * (k + 2 * n + 1)) * wzD n (k + 1) * wzD n k *
        ((k + 1) * (k + n + 1)) * (n * (k + 2 * n - 2) * (k + 2 * n - 1))
      + gamma1 n * (- (k - n) * (k + n) * (n - 1)) * wzD n (k + 1) * wzD n k *
        ((k + 1) * (k + n + 1)) * (n * (n - k + 1) * (k + n + 1))
      + beta1 n * wzD n (k + 1) * wzD n k * ((k + 1) * (k + n + 1)) *
        (n * (n - k + 1) * (k + n + 1)) * (n * (k + 2 * n - 2) * (k + 2 * n - 1)) := by
  unfold eExpr eTerm1 eTerm2 eTerm3 eTerm4 eTerm5
  simp only [BivE.evalR, BivE.evalR_substKsucc,
    eWzS_evalR, eWzD_evalR, eAlpha1_evalR, eGamma1_evalR, eBeta1_evalR,
    eRkN_evalR, eRkD_evalR, eRnpN_evalR, eRnpD_evalR, eRnmN_evalR, eRnmD_evalR]
  simp only [sub_eq_add_neg]
  ac_rfl

lemma eExpr_degN_le : eExpr.degN ≤ 19 := by decide
lemma eExpr_degK_le : eExpr.degK ≤ 12 := by decide

set_option maxHeartbeats 4000000
lemma eExpr_grid_bool :
    (List.range 20).all (fun i =>
      (List.range 13).all (fun j => eExpr.evalZ i j == 0)) = true := by decide

lemma eExpr_grid : ∀ i j : ℕ, i < 20 → j < 13 → eExpr.evalZ i j = 0 := by
  intro i j hi hj
  have h := eExpr_grid_bool
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i hi j hj

lemma eExpr_evalR_zero (n k : ℝ) : eExpr.evalR n k = 0 := by
  refine BivE.evalR_eq_zero_of_grid eExpr ?_ n k
  intro i j hi hj
  have hi' : i < 20 := lt_of_lt_of_le hi (Nat.succ_le_succ eExpr_degN_le)
  have hj' : j < 13 := lt_of_lt_of_le hj (Nat.succ_le_succ eExpr_degK_le)
  exact eExpr_grid i j hi' hj'

lemma e2n1_evalR (n k : ℝ) : e2n1.evalR n k = 2 * n + 1 := by
  simp only [e2n1, evalR_add', evalR_mul', evalR_eC, evalR_eN, evalR_e1, Int.cast_ofNat]
lemma e2n2_evalR (n k : ℝ) : e2n2.evalR n k = 2 * n + 2 := by
  simp only [e2n2, evalR_add', evalR_mul', evalR_eC, evalR_eN, evalR_e2, Int.cast_ofNat]
lemma e3n1_evalR (n k : ℝ) : e3n1.evalR n k = 3 * n + 1 := by
  simp only [e3n1, evalR_add', evalR_mul', evalR_eC, evalR_eN, evalR_e1, Int.cast_ofNat]
lemma e3n2_evalR (n k : ℝ) : e3n2.evalR n k = 3 * n + 2 := by
  simp only [e3n2, evalR_add', evalR_mul', evalR_eC, evalR_eN, evalR_e2, Int.cast_ofNat]
lemma eNp1_evalR (n k : ℝ) : eNp1.evalR n k = n + 1 := by
  simp only [eNp1, evalR_add', evalR_eN, evalR_e1]

lemma eBdry_evalR (n k : ℝ) :
    eBdry.evalR n k =
      wzS n n * (2 * n + 1) * (2 * n + 2)
        + alpha1 n * (n + 1) * 3 * (3 * n + 1) * wzD n n * (2 * n + 2)
        + alpha1 n * 3 * (3 * n + 1) * (3 * n + 2) * wzD n n
        - beta1 n * wzD n n * (2 * n + 1) * (2 * n + 2) := by
  unfold eBdry
  simp only [evalR_add', evalR_mul', evalR_neg', evalR_eC,
    BivE.evalR_substKN, eWzS_evalR, eWzD_evalR, eAlpha1_evalR, eBeta1_evalR,
    e2n1_evalR, e2n2_evalR, e3n1_evalR, e3n2_evalR, eNp1_evalR]
  simp only [sub_eq_add_neg]
  ac_rfl

lemma eBdry_degN_le : eBdry.degN ≤ 20 := by decide
lemma eBdry_degK_le : eBdry.degK ≤ 0 := by decide

lemma eBdry_grid_bool :
    (List.range 21).all (fun i => eBdry.evalZ i 0 == 0) = true := by decide

lemma eBdry_grid : ∀ i : ℕ, i < 21 → eBdry.evalZ i 0 = 0 := by
  intro i hi
  have h := eBdry_grid_bool
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i hi

lemma eBdry_evalR_zero (n k : ℝ) : eBdry.evalR n k = 0 := by
  refine BivE.evalR_eq_zero_of_grid eBdry ?_ n k
  intro i j hi hj
  have hi' : i < 21 := lt_of_lt_of_le hi (Nat.succ_le_succ eBdry_degN_le)
  have hj' : j < 1 := lt_of_lt_of_le hj (Nat.succ_le_succ eBdry_degK_le)
  have hj0 : j = 0 := by omega
  subst hj0
  exact eBdry_grid i hi'

lemma wz_cleared (n k : ℝ) :
    wzS n (k + 1) * wzD n k * (- (k - n) * (k + 2 * n)) *
        (n * (n - k + 1) * (k + n + 1)) * (n * (k + 2 * n - 2) * (k + 2 * n - 1))
      - wzS n k * wzD n (k + 1) * ((k + 1) * (k + n + 1)) *
        (n * (n - k + 1) * (k + n + 1)) * (n * (k + 2 * n - 2) * (k + 2 * n - 1))
      - alpha1 n * ((k + 2 * n) * (n + 1) * (k + 2 * n + 1)) * wzD n (k + 1) * wzD n k *
        ((k + 1) * (k + n + 1)) * (n * (k + 2 * n - 2) * (k + 2 * n - 1))
      + gamma1 n * (- (k - n) * (k + n) * (n - 1)) * wzD n (k + 1) * wzD n k *
        ((k + 1) * (k + n + 1)) * (n * (n - k + 1) * (k + n + 1))
      + beta1 n * wzD n (k + 1) * wzD n k * ((k + 1) * (k + n + 1)) *
        (n * (n - k + 1) * (k + n + 1)) * (n * (k + 2 * n - 2) * (k + 2 * n - 1)) = 0 := by
  rw [← eExpr_evalR]
  exact eExpr_evalR_zero n k

noncomputable def Fℝ (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * ((2 * n + k - 1).choose (n - 1) : ℝ)

lemma A103885_eq_Fℝ {n : ℕ} (hn : 0 < n) :
    (A103885 n : ℝ) = ∑ k ∈ range (n + 1), Fℝ n k := by
  rw [A103885_eq_sum hn]
  simp [Fℝ, A103885_term]

lemma Fℝ_eq_zero_of_lt {n k : ℕ} (h : n < k) : Fℝ n k = 0 := by
  simp [Fℝ, choose_eq_zero_of_lt h]

lemma cast_choose_succ_right (n k : ℕ) :
    (n.choose (k + 1) : ℝ) * (k + 1 : ℝ) = (n.choose k : ℝ) * ((n - k : ℕ) : ℝ) := by
  have := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq n k)
  simpa [Nat.cast_mul] using this

lemma cast_choose_mul_succ (n k : ℕ) :
    (n.choose k : ℝ) * (n + 1 : ℝ) = ((n + 1).choose k : ℝ) * ((n + 1 - k : ℕ) : ℝ) := by
  have := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_mul_succ_eq n k)
  simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using this

lemma cast_succ_mul_choose (n k : ℕ) :
    ((n + 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
      (n.choose k : ℝ) * ((n : ℝ) + 1) := by
  have h := congrArg (fun x : ℕ => (x : ℝ)) (Nat.add_one_mul_choose_eq n k)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
  linarith

lemma cast_nat_sub_one {n : ℕ} (hn : 1 ≤ n) :
    ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 :=
  Nat.cast_pred (by omega)

lemma cast_two_mul_add_sub {n k t : ℕ} (ht : t ≤ 2 * n + k) :
    ((2 * n + k - t : ℕ) : ℝ) = 2 * (n : ℝ) + (k : ℝ) - (t : ℝ) := by
  have h : ((2 * n + k - t : ℕ) : ℝ) = ((2 * n + k : ℕ) : ℝ) - (t : ℝ) :=
    Nat.cast_sub ht
  simpa [Nat.cast_add, Nat.cast_mul] using h

/-- Cleared identity: `C(n,k+1)/C(n,k)=(n-k)/(k+1)` and
`C(2n+k,n-1)/C(2n+k-1,n-1)=(2n+k)/(n+k+1)`. -/
lemma Fℝ_ratio_k_succ_cleared {n k : ℕ} (hk : k < n) :
    Fℝ n (k + 1) * ((k : ℝ) + 1) * ((n : ℝ) + k + 1) =
      Fℝ n k * ((n : ℝ) - k) * (2 * (n : ℝ) + k) := by
  unfold Fℝ
  have h1 : (n.choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
      (n.choose k : ℝ) * ((n : ℝ) - k) := by
    simpa [Nat.cast_sub hk.le] using cast_choose_succ_right n k
  have hidx : 2 * n + (k + 1) - 1 = 2 * n + k := by omega
  rw [hidx]
  have h2 : ((2 * n + k).choose (n - 1) : ℝ) * ((n : ℝ) + k + 1) =
      ((2 * n + k - 1).choose (n - 1) : ℝ) * (2 * (n : ℝ) + k) := by
    have src := cast_choose_mul_succ (2 * n + k - 1) (n - 1)
    have hm : 2 * n + k - 1 + 1 = 2 * n + k := by omega
    have hL : ((2 * n + k - 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + k := by exact_mod_cast hm
    have hR : ((2 * n + k - (n - 1) : ℕ) : ℝ) = (n : ℝ) + k + 1 := by
      have : 2 * n + k - (n - 1) = n + k + 1 := by omega
      exact_mod_cast this
    rw [hm, hL, hR] at src
    linarith
  calc
    (n.choose (k + 1) : ℝ) * ((2 * n + k).choose (n - 1) : ℝ) *
        ((k : ℝ) + 1) * ((n : ℝ) + k + 1)
      = ((n.choose (k + 1) : ℝ) * ((k : ℝ) + 1)) *
          (((2 * n + k).choose (n - 1) : ℝ) * ((n : ℝ) + k + 1)) := by
        ac_rfl
    _ = ((n.choose k : ℝ) * ((n : ℝ) - k)) *
          (((2 * n + k - 1).choose (n - 1) : ℝ) * (2 * (n : ℝ) + k)) := by
        rw [h1, h2]
    _ = (n.choose k : ℝ) * ((2 * n + k - 1).choose (n - 1) : ℝ) *
          ((n : ℝ) - k) * (2 * (n : ℝ) + k) := by
        ac_rfl

/-- `C(n+1,k)/C(n,k)=(n+1)/(n+1-k)` and
`C(2n+k+1,n)/C(2n+k-1,n-1)=(2n+k)(2n+k+1)/(n(n+k+1))`. -/
lemma Fℝ_ratio_n_succ_cleared {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n + 1) :
    Fℝ (n + 1) k * (n : ℝ) * ((n : ℝ) + 1 - k) * ((k : ℝ) + n + 1) =
      Fℝ n k * (2 * (n : ℝ) + k) * ((n : ℝ) + 1) * (2 * (n : ℝ) + k + 1) := by
  unfold Fℝ
  have hidx : 2 * (n + 1) + k - 1 = 2 * n + k + 1 := by omega
  have hidx2 : (n + 1) - 1 = n := by omega
  rw [hidx, hidx2]
  have h1 : ((n + 1).choose k : ℝ) * ((n : ℝ) + 1 - k) =
      (n.choose k : ℝ) * ((n : ℝ) + 1) := by
    have src := cast_choose_mul_succ n k
    have hsub : ((n + 1 - k : ℕ) : ℝ) = (n : ℝ) + 1 - k := by
      have h : ((n + 1 - k : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) - (k : ℝ) :=
        Nat.cast_sub hk
      simpa [Nat.cast_add, Nat.cast_one] using h
    rw [hsub] at src
    linarith
  have hstep1 : ((2 * n + k).choose n : ℝ) * (n : ℝ) =
      ((2 * n + k - 1).choose (n - 1) : ℝ) * (2 * (n : ℝ) + k) := by
    have src := cast_succ_mul_choose (2 * n + k - 1) (n - 1)
    have ht : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      have : n - 1 + 1 = n := by omega
      exact_mod_cast this
    have htN : n - 1 + 1 = n := by omega
    have hs : (2 * n + k - 1 + 1 : ℕ) = 2 * n + k := by omega
    have hsR : ((2 * n + k - 1 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + k := by
      have := congrArg (fun x : ℕ => (x : ℝ)) hs
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul] at this
      exact this
    rw [ht, htN, hs, hsR] at src
    exact src
  have hstep2 : ((2 * n + k + 1).choose n : ℝ) * ((n : ℝ) + k + 1) =
      ((2 * n + k).choose n : ℝ) * (2 * (n : ℝ) + k + 1) := by
    have src := cast_choose_mul_succ (2 * n + k) n
    have hL : ((2 * n + k : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + k + 1 := by
      simp [Nat.cast_mul, Nat.cast_add]
    have hR : ((2 * n + k + 1 - n : ℕ) : ℝ) = (n : ℝ) + k + 1 := by
      have : 2 * n + k + 1 - n = n + k + 1 := by omega
      exact_mod_cast this
    rw [hL, hR] at src
    -- src : C(2n+k,n)*((2n+k)+1) = C(2n+k+1,n)*((2n+k+1-n))
    -- after rw: C(2n+k,n)*(2n+k+1) = C(2n+k+1,n)*(n+k+1)
    linarith
  calc
    ((n + 1).choose k : ℝ) * ((2 * n + k + 1).choose n : ℝ) *
        (n : ℝ) * ((n : ℝ) + 1 - k) * ((k : ℝ) + n + 1)
      = (((n + 1).choose k : ℝ) * ((n : ℝ) + 1 - k)) *
          ((2 * n + k + 1).choose n : ℝ) * (n : ℝ) * ((k : ℝ) + n + 1) := by ac_rfl
    _ = ((n.choose k : ℝ) * ((n : ℝ) + 1)) *
          ((2 * n + k + 1).choose n : ℝ) * (n : ℝ) * ((k : ℝ) + n + 1) := by
        rw [h1]
    _ = (n.choose k : ℝ) * ((n : ℝ) + 1) * (n : ℝ) *
          (((2 * n + k + 1).choose n : ℝ) * ((n : ℝ) + k + 1)) := by ac_rfl
    _ = (n.choose k : ℝ) * ((n : ℝ) + 1) * (n : ℝ) *
          (((2 * n + k).choose n : ℝ) * (2 * (n : ℝ) + k + 1)) := by
        rw [hstep2]
    _ = (n.choose k : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + k + 1) *
          (((2 * n + k).choose n : ℝ) * (n : ℝ)) := by ac_rfl
    _ = (n.choose k : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + k + 1) *
          (((2 * n + k - 1).choose (n - 1) : ℝ) * (2 * (n : ℝ) + k)) := by
        rw [hstep1]
    _ = (n.choose k : ℝ) * ((2 * n + k - 1).choose (n - 1) : ℝ) *
          (2 * (n : ℝ) + k) * ((n : ℝ) + 1) * (2 * (n : ℝ) + k + 1) := by ac_rfl

/-- `F(n-1,k)/F(n,k) = (n-k)(n+k)(n-1)/(n(2n+k-2)(2n+k-1))`. -/
lemma Fℝ_ratio_n_pred_cleared {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n - 1) :
    Fℝ (n - 1) k * (n : ℝ) * (2 * (n : ℝ) + k - 2) * (2 * (n : ℝ) + k - 1) =
      Fℝ n k * ((n : ℝ) - k) * ((n : ℝ) + k) * ((n : ℝ) - 1) := by
  unfold Fℝ
  have hidx : 2 * (n - 1) + k - 1 = 2 * n + k - 3 := by omega
  have hidx2 : n - 1 - 1 = n - 2 := by omega
  rw [hidx, hidx2]
  have h1 : ((n - 1).choose k : ℝ) * (n : ℝ) =
      (n.choose k : ℝ) * ((n : ℝ) - k) := by
    have src := cast_choose_mul_succ (n - 1) k
    have hs : n - 1 + 1 = n := by omega
    rw [hs] at src
    have hL : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      rw [cast_nat_sub_one (by omega)]; ring
    have hR : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := Nat.cast_sub (by omega)
    rw [hL, hR] at src
    exact src
  have hA : ((2 * n + k - 2).choose (n - 2) : ℝ) * ((n : ℝ) + k) =
      ((2 * n + k - 3).choose (n - 2) : ℝ) * (2 * (n : ℝ) + k - 2) := by
    have src := cast_choose_mul_succ (2 * n + k - 3) (n - 2)
    have hm : 2 * n + k - 3 + 1 = 2 * n + k - 2 := by omega
    rw [hm] at src
    have hL : ((2 * n + k - 3 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + k - 2 := by
      rw [cast_two_mul_add_sub (by omega : 3 ≤ 2 * n + k)]; ring
    have hR : ((2 * n + k - 2 - (n - 2) : ℕ) : ℝ) = (n : ℝ) + k := by
      have : 2 * n + k - 2 - (n - 2) = n + k := by omega
      exact_mod_cast this
    rw [hL, hR] at src
    linarith
  have hB : ((2 * n + k - 1).choose (n - 1) : ℝ) * ((n : ℝ) - 1) =
      ((2 * n + k - 2).choose (n - 2) : ℝ) * (2 * (n : ℝ) + k - 1) := by
    have src := cast_succ_mul_choose (2 * n + k - 2) (n - 2)
    have ht : ((n - 2 : ℕ) : ℝ) + 1 = (n : ℝ) - 1 := by
      have : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
        have h : ((n - 2 : ℕ) : ℝ) = ((n : ℕ) : ℝ) - (2 : ℝ) := Nat.cast_sub (by omega)
        simpa using h
      rw [this]; ring
    have htN : n - 2 + 1 = n - 1 := by omega
    have hs : 2 * n + k - 2 + 1 = 2 * n + k - 1 := by omega
    have hsR : ((2 * n + k - 2 : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + k - 1 := by
      rw [cast_two_mul_add_sub (by omega : 2 ≤ 2 * n + k)]; ring
    rw [ht, htN, hs, hsR] at src
    exact src
  calc
    ((n - 1).choose k : ℝ) * ((2 * n + k - 3).choose (n - 2) : ℝ) *
        (n : ℝ) * (2 * (n : ℝ) + k - 2) * (2 * (n : ℝ) + k - 1)
      = (((n - 1).choose k : ℝ) * (n : ℝ)) *
          ((2 * n + k - 3).choose (n - 2) : ℝ) *
          (2 * (n : ℝ) + k - 2) * (2 * (n : ℝ) + k - 1) := by ac_rfl
    _ = ((n.choose k : ℝ) * ((n : ℝ) - k)) *
          ((2 * n + k - 3).choose (n - 2) : ℝ) *
          (2 * (n : ℝ) + k - 2) * (2 * (n : ℝ) + k - 1) := by rw [h1]
    _ = (n.choose k : ℝ) * ((n : ℝ) - k) * (2 * (n : ℝ) + k - 1) *
          (((2 * n + k - 3).choose (n - 2) : ℝ) * (2 * (n : ℝ) + k - 2)) := by ac_rfl
    _ = (n.choose k : ℝ) * ((n : ℝ) - k) * (2 * (n : ℝ) + k - 1) *
          (((2 * n + k - 2).choose (n - 2) : ℝ) * ((n : ℝ) + k)) := by
        rw [← hA]
    _ = (n.choose k : ℝ) * ((n : ℝ) - k) * ((n : ℝ) + k) *
          (((2 * n + k - 2).choose (n - 2) : ℝ) * (2 * (n : ℝ) + k - 1)) := by ac_rfl
    _ = (n.choose k : ℝ) * ((n : ℝ) - k) * ((n : ℝ) + k) *
          (((2 * n + k - 1).choose (n - 1) : ℝ) * ((n : ℝ) - 1)) := by
        rw [← hB]
    _ = (n.choose k : ℝ) * ((2 * n + k - 1).choose (n - 1) : ℝ) *
          ((n : ℝ) - k) * ((n : ℝ) + k) * ((n : ℝ) - 1) := by ac_rfl

noncomputable def Gℝ (n k : ℕ) : ℝ :=
  wzS (n : ℝ) (k : ℝ) / wzD (n : ℝ) (k : ℝ) * Fℝ n k

lemma wzD_ne_zero_of_le {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n) :
    wzD (n : ℝ) (k : ℝ) ≠ 0 := by
  unfold wzD
  have h1 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hk' : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2 : (k : ℝ) - (n : ℝ) - 1 ≠ 0 := by linarith
  have h3 : (k : ℝ) + 2 * (n : ℝ) - 2 ≠ 0 := by linarith
  have h4 : (k : ℝ) + 2 * (n : ℝ) - 1 ≠ 0 := by linarith
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4

lemma wzS_zero_of_zero (n : ℝ) : wzS n 0 = 0 := by
  unfold wzS; ring

attribute [irreducible] wzS

lemma Gℝ_zero (n : ℕ) : Gℝ n 0 = 0 := by
  simp [Gℝ, wzS_zero_of_zero]

lemma cast_three_mul_sub_one {n : ℕ} (hn : 1 ≤ n) :
    ((3 * n - 1 : ℕ) : ℝ) = 3 * (n : ℝ) - 1 := by
  have h : ((3 * n - 1 : ℕ) : ℝ) = ((3 * n : ℕ) : ℝ) - ((1 : ℕ) : ℝ) :=
    Nat.cast_sub (by omega : 1 ≤ 3 * n)
  simp only [Nat.cast_mul, Nat.cast_one] at h
  exact h

lemma Fℝ_nn_ne_zero {n : ℕ} (hn : 1 ≤ n) : Fℝ n n ≠ 0 := by
  unfold Fℝ
  have hch : (n.choose n : ℝ) = 1 := by simp
  rw [hch, one_mul]
  have hidx : 2 * n + n - 1 = 3 * n - 1 := by omega
  rw [hidx]
  have hpos : 0 < (3 * n - 1).choose (n - 1) :=
    Nat.choose_pos (by omega)
  exact_mod_cast hpos.ne'

lemma Fℝ_ratio_boundary_n {n : ℕ} (hn : 2 ≤ n) :
    Fℝ (n + 1) n * (2 * (n : ℝ) + 1) =
      Fℝ n n * ((n : ℝ) + 1) * 3 * (3 * (n : ℝ) + 1) := by
  have h := Fℝ_ratio_n_succ_cleared (n := n) (k := n) (by omega) (by omega)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have h1 : ((n : ℝ) + 1 - n) = 1 := by linarith
  have h2 : ((n : ℝ) + n + 1) = 2 * (n : ℝ) + 1 := by linarith
  have h3 : (2 * (n : ℝ) + n) = 3 * (n : ℝ) := by linarith
  have h4 : (2 * (n : ℝ) + n + 1) = 3 * (n : ℝ) + 1 := by linarith
  simp only [h1, h2, h3, h4, mul_one] at h
  have hmul : Fℝ (n + 1) n * (2 * (n : ℝ) + 1) * (n : ℝ) =
      Fℝ n n * ((n : ℝ) + 1) * 3 * (3 * (n : ℝ) + 1) * (n : ℝ) := by
    convert h using 1 <;> ac_rfl
  exact mul_right_cancel₀ hn0 hmul

lemma Fℝ_ratio_boundary_succ {n : ℕ} (hn : 2 ≤ n) :
    Fℝ (n + 1) (n + 1) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2) =
      Fℝ n n * 3 * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2) := by
  unfold Fℝ
  have hidx : 2 * (n + 1) + (n + 1) - 1 = 3 * n + 2 := by omega
  have hidx2 : n + 1 - 1 = n := by omega
  have hidx3 : 2 * n + n - 1 = 3 * n - 1 := by omega
  rw [hidx, hidx2, hidx3]
  have e1 : ((3 * n).choose n : ℝ) * (n : ℝ) =
      ((3 * n - 1).choose (n - 1) : ℝ) * (3 * (n : ℝ)) := by
    have src := cast_succ_mul_choose (3 * n - 1) (n - 1)
    have ht : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      rw [cast_nat_sub_one (by omega)]; abel
    have htN : n - 1 + 1 = n := by omega
    have hs' : 3 * n - 1 + 1 = 3 * n := by omega
    have hsR : ((3 * n - 1 : ℕ) : ℝ) + 1 = 3 * (n : ℝ) := by
      rw [cast_three_mul_sub_one (by omega)]; abel
    rw [ht, htN, hs', hsR] at src
    exact src
  have e2 : ((3 * n + 1).choose n : ℝ) * (2 * (n : ℝ) + 1) =
      ((3 * n).choose n : ℝ) * (3 * (n : ℝ) + 1) := by
    have src := cast_choose_mul_succ (3 * n) n
    have hL : ((3 * n : ℕ) : ℝ) + 1 = 3 * (n : ℝ) + 1 := by
      simp [Nat.cast_mul]
    have hR : ((3 * n + 1 - n : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by
      have : 3 * n + 1 - n = 2 * n + 1 := by omega
      exact_mod_cast this
    rw [hL, hR] at src
    linarith
  have e3 : ((3 * n + 2).choose n : ℝ) * (2 * (n : ℝ) + 2) =
      ((3 * n + 1).choose n : ℝ) * (3 * (n : ℝ) + 2) := by
    have src := cast_choose_mul_succ (3 * n + 1) n
    have hidx' : (3 * n + 1 + 1 : ℕ) = 3 * n + 2 := by omega
    have hL : ((3 * n + 1 : ℕ) : ℝ) + 1 = 3 * (n : ℝ) + 2 := by
      have : ((3 * n + 1 : ℕ) : ℝ) = 3 * (n : ℝ) + 1 := by
        simp [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [this]; ring
    rw [hidx'] at src
    rw [hL] at src
    have hR' : ((3 * n + 2 - n : ℕ) : ℝ) = 2 * (n : ℝ) + 2 := by
      have : 3 * n + 2 - n = 2 * n + 2 := by omega
      exact_mod_cast this
    rw [hR'] at src
    linarith
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have e1' : ((3 * n).choose n : ℝ) =
      ((3 * n - 1).choose (n - 1) : ℝ) * 3 := by
    have : ((3 * n).choose n : ℝ) * (n : ℝ) =
        ((3 * n - 1).choose (n - 1) : ℝ) * 3 * (n : ℝ) := by
      convert e1 using 1; ac_rfl
    exact mul_right_cancel₀ hn0 this
  have hmain : ((3 * n + 2).choose n : ℝ) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2) =
      ((3 * n - 1).choose (n - 1) : ℝ) * 3 * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2) := by
    have hstep1 : ((3 * n + 2).choose n : ℝ) * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2) =
        ((3 * n + 1).choose n : ℝ) * (2 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2) := by
      have := congrArg (fun x : ℝ => (2 * (n : ℝ) + 1) * x) e3
      linarith
    have hstep2 : ((3 * n + 1).choose n : ℝ) * (2 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2) =
        ((3 * n).choose n : ℝ) * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2) := by
      have := congrArg (fun x : ℝ => x * (3 * (n : ℝ) + 2)) e2
      linarith
    rw [hstep1, hstep2, e1']
    try ac_rfl
  simpa [Nat.choose_self, Nat.cast_one, one_mul] using hmain

lemma boundary_cancel_cleared (n : ℝ) :
    wzS n n * (2 * n + 1) * (2 * n + 2)
      + alpha1 n * (n + 1) * 3 * (3 * n + 1) * wzD n n * (2 * n + 2)
      + alpha1 n * 3 * (3 * n + 1) * (3 * n + 2) * wzD n n
      - beta1 n * wzD n n * (2 * n + 1) * (2 * n + 2) = 0 := by
  rw [← eBdry_evalR n 0]
  exact eBdry_evalR_zero n 0

lemma boundary_denoms_ne_zero {n : ℕ} (hn : 2 ≤ n) :
    wzD (n : ℝ) (n : ℝ) ≠ 0 ∧
      (2 * (n : ℝ) + 1) ≠ 0 ∧ (2 * (n : ℝ) + 2) ≠ 0 := by
  refine ⟨wzD_ne_zero_of_le hn (le_rfl), ?_, ?_⟩
  · have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith

lemma boundary_cancel {n : ℕ} (hn : 2 ≤ n) :
    wzS (n : ℝ) n / wzD (n : ℝ) n
      + alpha1 (n : ℝ) * (((n : ℝ) + 1) * 3 * (3 * (n : ℝ) + 1) / (2 * (n : ℝ) + 1))
      + alpha1 (n : ℝ) *
          (3 * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2) /
            ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2)))
      - beta1 (n : ℝ) = 0 := by
  have ⟨hD, h1, h2⟩ := boundary_denoms_ne_zero hn
  have hcleared := boundary_cancel_cleared (n : ℝ)
  have hden : wzD (n : ℝ) n * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hD h1) h2
  apply (mul_right_inj' hden).mp
  convert hcleared using 1 <;> field_simp [hD, h1, h2] <;> ring

lemma ratio_k_succ_form {n k : ℕ} (hk : k < n) :
    Fℝ n (k + 1) * (((k : ℝ) + 1) * ((k : ℝ) + n + 1)) =
      Fℝ n k * (-((k : ℝ) - n) * ((k : ℝ) + 2 * n)) := by
  have h := Fℝ_ratio_k_succ_cleared hk
  convert h using 1 <;> ring

lemma ratio_n_succ_form {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n + 1) :
    Fℝ (n + 1) k * ((n : ℝ) * ((n : ℝ) - k + 1) * ((k : ℝ) + n + 1)) =
      Fℝ n k * (((k : ℝ) + 2 * n) * ((n : ℝ) + 1) * ((k : ℝ) + 2 * n + 1)) := by
  have h := Fℝ_ratio_n_succ_cleared hn hk
  convert h using 1
  · have : (n : ℝ) - k + 1 = (n : ℝ) + 1 - k := by linarith
    simp only [this]; ac_rfl
  · ac_rfl

lemma ratio_n_pred_form {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n - 1) :
    Fℝ (n - 1) k * ((n : ℝ) * ((k : ℝ) + 2 * n - 2) * ((k : ℝ) + 2 * n - 1)) =
      Fℝ n k * (-((k : ℝ) - n) * ((k : ℝ) + n) * ((n : ℝ) - 1)) := by
  have h := Fℝ_ratio_n_pred_cleared hn hk
  convert h using 1 <;> ring

lemma wz_ratio_denoms_ne {n k : ℕ} (hn : 2 ≤ n) (hk : k < n) :
    ((k : ℝ) + 1) * ((k : ℝ) + n + 1) ≠ 0 ∧
      (n : ℝ) * ((n : ℝ) - k + 1) * ((k : ℝ) + n + 1) ≠ 0 ∧
      (n : ℝ) * ((k : ℝ) + 2 * n - 2) * ((k : ℝ) + 2 * n - 1) ≠ 0 := by
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hkn : (k : ℝ) + 1 ≤ (n : ℝ) := by
    have : k + 1 ≤ n := by omega
    exact_mod_cast this
  have h1a : (k : ℝ) + 1 ≠ 0 := by linarith
  have h1b : (k : ℝ) + (n : ℝ) + 1 ≠ 0 := by linarith
  have h2b : (n : ℝ) - (k : ℝ) + 1 ≠ 0 := by
    have : (k : ℝ) + 1 ≤ (n : ℝ) := hkn
    linarith
  have h3b : (k : ℝ) + 2 * (n : ℝ) - 2 ≠ 0 := by linarith
  have h3c : (k : ℝ) + 2 * (n : ℝ) - 1 ≠ 0 := by linarith
  exact ⟨mul_ne_zero h1a h1b,
    mul_ne_zero (mul_ne_zero hn0 h2b) h1b,
    mul_ne_zero (mul_ne_zero hn0 h3b) h3c⟩

lemma rearrange_h1 (s1 d0 f1 s0 d1 f0 r d e : ℝ) :
    (s1 * d0 * f1 - s0 * d1 * f0) * r * d * e =
      (s1 * d0 * (f1 * r) - s0 * d1 * f0 * r) * d * e := by
  have hL : (s1 * d0 * f1 - s0 * d1 * f0) * r =
      s1 * d0 * f1 * r - s0 * d1 * f0 * r := sub_mul _ _ _
  rw [hL]
  congr 1 <;> ac_rfl

lemma rearrange_h3 (s1 d0 f rkN s0 d1 rkD d e : ℝ) :
    (s1 * d0 * (f * rkN) - s0 * d1 * f * rkD) * d * e =
      f * (s1 * d0 * rkN * d * e - s0 * d1 * rkD * d * e) := by
  have hL : (s1 * d0 * (f * rkN) - s0 * d1 * f * rkD) * d * e =
      s1 * d0 * (f * rkN) * d * e - s0 * d1 * f * rkD * d * e := by
    rw [sub_mul, sub_mul]
  have hR : f * (s1 * d0 * rkN * d * e - s0 * d1 * rkD * d * e) =
      f * (s1 * d0 * rkN * d * e) - f * (s0 * d1 * rkD * d * e) := mul_sub _ _ _
  rw [hL, hR]
  congr 1 <;> ac_rfl

lemma rearrange_h5 (f a rnpN d1 d0 rkD rnmD g rnmN rnpD b : ℝ) :
    f * (a * rnpN * d1 * d0 * rkD * rnmD
      - g * rnmN * d1 * d0 * rkD * rnpD
      - b * d1 * d0 * rkD * rnpD * rnmD) =
    a * (f * rnpN) * d1 * d0 * rkD * rnmD
      - g * (f * rnmN) * d1 * d0 * rkD * rnpD
      - b * f * d1 * d0 * rkD * rnpD * rnmD := by
  have hL :
      f * (a * rnpN * d1 * d0 * rkD * rnmD
        - g * rnmN * d1 * d0 * rkD * rnpD
        - b * d1 * d0 * rkD * rnpD * rnmD) =
      f * (a * rnpN * d1 * d0 * rkD * rnmD)
        - f * (g * rnmN * d1 * d0 * rkD * rnpD)
        - f * (b * d1 * d0 * rkD * rnpD * rnmD) := by
    rw [sub_eq_add_neg, sub_eq_add_neg, mul_add, mul_add, mul_neg, mul_neg]
    simp only [sub_eq_add_neg]
  rw [hL]
  congr 1
  · congr 1 <;> ac_rfl
  · ac_rfl

lemma rearrange_h7 (a fnp rnpD d1 d0 rkD rnmD g fnm b f : ℝ) :
    a * (fnp * rnpD) * d1 * d0 * rkD * rnmD
      - g * (fnm * rnmD) * d1 * d0 * rkD * rnpD
      - b * f * d1 * d0 * rkD * rnpD * rnmD =
    (a * fnp - g * fnm - b * f) * d1 * d0 * rkD * rnpD * rnmD := by
  ring

lemma rearrange_h4 (f s1 d0 rkN rnpD rnmD s0 d1 rkD a rnpN g rnmN b : ℝ)
    (hid' : s1 * d0 * rkN * rnpD * rnmD - s0 * d1 * rkD * rnpD * rnmD
        - a * rnpN * d1 * d0 * rkD * rnmD
        + g * rnmN * d1 * d0 * rkD * rnpD
        + b * d1 * d0 * rkD * rnpD * rnmD = 0) :
    f * (s1 * d0 * rkN * rnpD * rnmD - s0 * d1 * rkD * rnpD * rnmD) =
      f * (a * rnpN * d1 * d0 * rkD * rnmD
        - g * rnmN * d1 * d0 * rkD * rnpD
        - b * d1 * d0 * rkD * rnpD * rnmD) := by
  linear_combination f * hid'

lemma Gℝ_diff {n k : ℕ} (hn : 2 ≤ n) (hk : k < n) :
    Gℝ n (k + 1) - Gℝ n k =
      alpha1 (n : ℝ) * Fℝ (n + 1) k
        - gamma1 (n : ℝ) * Fℝ (n - 1) k
        - beta1 (n : ℝ) * Fℝ n k := by
  have hD : wzD (n : ℝ) (k : ℝ) ≠ 0 := wzD_ne_zero_of_le hn (le_of_lt hk)
  have hD1 : wzD (n : ℝ) ((k + 1 : ℕ) : ℝ) ≠ 0 :=
    wzD_ne_zero_of_le hn (Nat.succ_le_of_lt hk)
  have hkcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := Nat.cast_succ k
  have hD1' : wzD (n : ℝ) ((k : ℝ) + 1) ≠ 0 := by rwa [← hkcast]
  have ⟨hkD, hnpD, hnmD⟩ := wz_ratio_denoms_ne hn hk
  have hrk := ratio_k_succ_form (n := n) (k := k) hk
  have hrnp := ratio_n_succ_form (n := n) (k := k) (by omega) (by omega)
  have hrnm := ratio_n_pred_form (n := n) (k := k) hn (Nat.le_sub_one_of_lt hk)
  have hid := wz_cleared (n : ℝ) (k : ℝ)
  set S0 := wzS (n : ℝ) (k : ℝ)
  set S1 := wzS (n : ℝ) ((k : ℝ) + 1)
  set D0 := wzD (n : ℝ) (k : ℝ)
  set D1 := wzD (n : ℝ) ((k : ℝ) + 1)
  set rkN := -((k : ℝ) - n) * ((k : ℝ) + 2 * n)
  set rkD := ((k : ℝ) + 1) * ((k : ℝ) + n + 1)
  set rnpN := ((k : ℝ) + 2 * n) * ((n : ℝ) + 1) * ((k : ℝ) + 2 * n + 1)
  set rnpD := (n : ℝ) * ((n : ℝ) - k + 1) * ((k : ℝ) + n + 1)
  set rnmN := -((k : ℝ) - n) * ((k : ℝ) + n) * ((n : ℝ) - 1)
  set rnmD := (n : ℝ) * ((k : ℝ) + 2 * n - 2) * ((k : ℝ) + 2 * n - 1)
  have hcleared :
      (S1 * D0 * Fℝ n (k + 1) - S0 * D1 * Fℝ n k) * rkD * rnpD * rnmD =
        (alpha1 (n : ℝ) * Fℝ (n + 1) k
          - gamma1 (n : ℝ) * Fℝ (n - 1) k
          - beta1 (n : ℝ) * Fℝ n k) * D1 * D0 * rkD * rnpD * rnmD := by
    have h1 :
        (S1 * D0 * Fℝ n (k + 1) - S0 * D1 * Fℝ n k) * rkD * rnpD * rnmD =
          (S1 * D0 * (Fℝ n (k + 1) * rkD) - S0 * D1 * Fℝ n k * rkD) * rnpD * rnmD :=
      rearrange_h1 _ _ _ _ _ _ _ _ _
    have h2 :
        (S1 * D0 * (Fℝ n (k + 1) * rkD) - S0 * D1 * Fℝ n k * rkD) * rnpD * rnmD =
          (S1 * D0 * (Fℝ n k * rkN) - S0 * D1 * Fℝ n k * rkD) * rnpD * rnmD := by
      rw [hrk]
    have h3 :
        (S1 * D0 * (Fℝ n k * rkN) - S0 * D1 * Fℝ n k * rkD) * rnpD * rnmD =
          Fℝ n k * (S1 * D0 * rkN * rnpD * rnmD - S0 * D1 * rkD * rnpD * rnmD) :=
      rearrange_h3 _ _ _ _ _ _ _ _ _
    have h4 :
        Fℝ n k * (S1 * D0 * rkN * rnpD * rnmD - S0 * D1 * rkD * rnpD * rnmD) =
          Fℝ n k * (alpha1 (n : ℝ) * rnpN * D1 * D0 * rkD * rnmD
            - gamma1 (n : ℝ) * rnmN * D1 * D0 * rkD * rnpD
            - beta1 (n : ℝ) * D1 * D0 * rkD * rnpD * rnmD) := by
      have hid' :
          S1 * D0 * rkN * rnpD * rnmD - S0 * D1 * rkD * rnpD * rnmD
            - alpha1 (n : ℝ) * rnpN * D1 * D0 * rkD * rnmD
            + gamma1 (n : ℝ) * rnmN * D1 * D0 * rkD * rnpD
            + beta1 (n : ℝ) * D1 * D0 * rkD * rnpD * rnmD = 0 := by
        convert hid
      exact rearrange_h4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hid'
    have h5 :
        Fℝ n k * (alpha1 (n : ℝ) * rnpN * D1 * D0 * rkD * rnmD
          - gamma1 (n : ℝ) * rnmN * D1 * D0 * rkD * rnpD
          - beta1 (n : ℝ) * D1 * D0 * rkD * rnpD * rnmD) =
          (alpha1 (n : ℝ) * (Fℝ n k * rnpN) * D1 * D0 * rkD * rnmD
            - gamma1 (n : ℝ) * (Fℝ n k * rnmN) * D1 * D0 * rkD * rnpD
            - beta1 (n : ℝ) * Fℝ n k * D1 * D0 * rkD * rnpD * rnmD) :=
      rearrange_h5 _ _ _ _ _ _ _ _ _ _ _
    have h6 :
        (alpha1 (n : ℝ) * (Fℝ n k * rnpN) * D1 * D0 * rkD * rnmD
          - gamma1 (n : ℝ) * (Fℝ n k * rnmN) * D1 * D0 * rkD * rnpD
          - beta1 (n : ℝ) * Fℝ n k * D1 * D0 * rkD * rnpD * rnmD) =
          (alpha1 (n : ℝ) * (Fℝ (n + 1) k * rnpD) * D1 * D0 * rkD * rnmD
            - gamma1 (n : ℝ) * (Fℝ (n - 1) k * rnmD) * D1 * D0 * rkD * rnpD
            - beta1 (n : ℝ) * Fℝ n k * D1 * D0 * rkD * rnpD * rnmD) := by
      rw [← hrnp, ← hrnm]
    have h7 :
        (alpha1 (n : ℝ) * (Fℝ (n + 1) k * rnpD) * D1 * D0 * rkD * rnmD
          - gamma1 (n : ℝ) * (Fℝ (n - 1) k * rnmD) * D1 * D0 * rkD * rnpD
          - beta1 (n : ℝ) * Fℝ n k * D1 * D0 * rkD * rnpD * rnmD) =
          (alpha1 (n : ℝ) * Fℝ (n + 1) k
            - gamma1 (n : ℝ) * Fℝ (n - 1) k
            - beta1 (n : ℝ) * Fℝ n k) * D1 * D0 * rkD * rnpD * rnmD :=
      rearrange_h7 _ _ _ _ _ _ _ _ _ _ _
    exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans h7)))))
  -- divide by the nonzero prefactors
  have hden3 : rkD * rnpD * rnmD ≠ 0 := by
    unfold rkD rnpD rnmD
    exact mul_ne_zero (mul_ne_zero hkD hnpD) hnmD
  have hcleared' :
      S1 * D0 * Fℝ n (k + 1) - S0 * D1 * Fℝ n k =
        D0 * D1 * (alpha1 (n : ℝ) * Fℝ (n + 1) k
          - gamma1 (n : ℝ) * Fℝ (n - 1) k
          - Fℝ n k * beta1 (n : ℝ)) := by
    apply mul_right_cancel₀ hden3
    convert hcleared using 1
    · ac_rfl
    · rw [mul_comm (Fℝ n k) (beta1 (n : ℝ))]; ac_rfl
  unfold Gℝ
  rw [hkcast]
  have hden : D1 * D0 ≠ 0 := mul_ne_zero hD1' hD
  have hrepr :
      S1 / D1 * Fℝ n (k + 1) - S0 / D0 * Fℝ n k =
        (S1 * D0 * Fℝ n (k + 1) - S0 * D1 * Fℝ n k) / (D1 * D0) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_sub_div _ _ hD1' hD]
    congr 1 <;> ac_rfl
  rw [hrepr, hcleared', mul_comm (Fℝ n k) (beta1 (n : ℝ))]
  rw [show D1 * D0 = D0 * D1 from mul_comm _ _]
  exact mul_div_cancel_left₀ _ (mul_ne_zero hD hD1')

lemma m1_wz_sum (n : ℕ) (hn : 2 ≤ n) :
    alpha1 (n : ℝ) * (A103885 (n + 1) : ℝ)
      - gamma1 (n : ℝ) * (A103885 (n - 1) : ℝ)
      = beta1 (n : ℝ) * (A103885 n : ℝ) := by
  have hdiff : ∀ k ∈ range n,
      Gℝ n (k + 1) - Gℝ n k =
        alpha1 (n : ℝ) * Fℝ (n + 1) k
          - gamma1 (n : ℝ) * Fℝ (n - 1) k
          - beta1 (n : ℝ) * Fℝ n k := by
    intro k hk
    exact Gℝ_diff hn (mem_range.mp hk)
  have htel : ∑ k ∈ range n, (Gℝ n (k + 1) - Gℝ n k) = Gℝ n n := by
    rw [sum_range_sub, Gℝ_zero]
    ring
  have hsum :
      ∑ k ∈ range n,
          (alpha1 (n : ℝ) * Fℝ (n + 1) k
            - gamma1 (n : ℝ) * Fℝ (n - 1) k
            - beta1 (n : ℝ) * Fℝ n k) = Gℝ n n := by
    rw [← htel]
    exact sum_congr rfl (fun k hk => (hdiff k hk).symm)
  have hdistrib :
      alpha1 (n : ℝ) * ∑ k ∈ range n, Fℝ (n + 1) k
        - gamma1 (n : ℝ) * ∑ k ∈ range n, Fℝ (n - 1) k
        - beta1 (n : ℝ) * ∑ k ∈ range n, Fℝ n k = Gℝ n n := by
    rw [← hsum]
    simp [sum_sub_distrib, mul_sum]
  have hnp : (A103885 (n + 1) : ℝ) = ∑ k ∈ range (n + 2), Fℝ (n + 1) k :=
    A103885_eq_Fℝ (by omega)
  have hn0 : (A103885 n : ℝ) = ∑ k ∈ range (n + 1), Fℝ n k :=
    A103885_eq_Fℝ (by omega)
  have hnm : (A103885 (n - 1) : ℝ) = ∑ k ∈ range n, Fℝ (n - 1) k := by
    have : (n - 1) + 1 = n := by omega
    simpa [this] using A103885_eq_Fℝ (n := n - 1) (by omega)
  have hsum_np : ∑ k ∈ range n, Fℝ (n + 1) k =
      (A103885 (n + 1) : ℝ) - Fℝ (n + 1) n - Fℝ (n + 1) (n + 1) := by
    have hsplit : range (n + 2) = insert (n + 1) (insert n (range n)) := by
      ext x
      simp only [mem_insert, mem_range]
      omega
    rw [hnp, hsplit, sum_insert, sum_insert]
    · ring
    · simp [mem_range]
    · simp [mem_insert, mem_range]
  have hsum_n : ∑ k ∈ range n, Fℝ n k = (A103885 n : ℝ) - Fℝ n n := by
    have hsplit : range (n + 1) = insert n (range n) := by
      ext x
      simp only [mem_insert, mem_range]
      omega
    rw [hn0, hsplit, sum_insert]
    · ring
    · simp [mem_range]
  rw [hsum_np, ← hnm, hsum_n] at hdistrib
  -- α(a(n+1)-F(n+1,n)-F(n+1,n+1)) - γ a(n-1) - β(a(n)-F(n,n)) = G(n,n)
  have hrearr :
      alpha1 (n : ℝ) * (A103885 (n + 1) : ℝ)
        - gamma1 (n : ℝ) * (A103885 (n - 1) : ℝ)
        - beta1 (n : ℝ) * (A103885 n : ℝ)
      = Gℝ n n + alpha1 (n : ℝ) * Fℝ (n + 1) n
          + alpha1 (n : ℝ) * Fℝ (n + 1) (n + 1)
          - beta1 (n : ℝ) * Fℝ n n := by
    linarith [hdistrib]
  -- Show the leftover vanishes
  have hleft :
      Gℝ n n + alpha1 (n : ℝ) * Fℝ (n + 1) n
        + alpha1 (n : ℝ) * Fℝ (n + 1) (n + 1)
        - beta1 (n : ℝ) * Fℝ n n = 0 := by
    have hFn : Fℝ n n ≠ 0 := Fℝ_nn_ne_zero (by omega)
    have ⟨hD, h1, h2⟩ := boundary_denoms_ne_zero hn
    have hb := boundary_cancel hn
    have hr1 := Fℝ_ratio_boundary_n hn
    have hr2 := Fℝ_ratio_boundary_succ hn
    -- F(n+1,n) = F(n,n) * (n+1)*3*(3n+1)/(2n+1)
    have r1 : Fℝ (n + 1) n =
        Fℝ n n * (((n : ℝ) + 1) * 3 * (3 * (n : ℝ) + 1) / (2 * (n : ℝ) + 1)) := by
      calc
        Fℝ (n + 1) n
            = Fℝ (n + 1) n * (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 1) :=
              (mul_div_cancel_right₀ _ h1).symm
        _ = (Fℝ n n * ((n : ℝ) + 1) * 3 * (3 * (n : ℝ) + 1)) / (2 * (n : ℝ) + 1) := by
              rw [hr1]
        _ = Fℝ n n * (((n : ℝ) + 1) * 3 * (3 * (n : ℝ) + 1) / (2 * (n : ℝ) + 1)) := by
              simp only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have r2 : Fℝ (n + 1) (n + 1) =
        Fℝ n n * (3 * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2) /
          ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2))) := by
      have h12 : (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2) ≠ 0 := mul_ne_zero h1 h2
      calc
        Fℝ (n + 1) (n + 1)
            = Fℝ (n + 1) (n + 1) * ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2)) /
                ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2)) :=
              (mul_div_cancel_right₀ _ h12).symm
        _ = (Fℝ n n * 3 * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2)) /
              ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2)) := by
              rw [← hr2]; ac_rfl
        _ = Fℝ n n * (3 * (3 * (n : ℝ) + 1) * (3 * (n : ℝ) + 2) /
              ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2))) := by
              simp only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    unfold Gℝ at *
    rw [r1, r2]
    have := congrArg (fun x : ℝ => Fℝ n n * x) hb
    convert this using 1 <;> ring
  linarith [hrearr, hleft]

lemma alpha1_eq (n : ℕ) :
    alpha1 (n : ℝ) = prod_factor_plus 1 n * P1.eval (n : ℝ) := by
  rw [prod_factor_plus_one, P1_eval, alpha1]

lemma gamma1_eq (n : ℕ) :
    gamma1 (n : ℝ) = prod_factor_minus 1 n * P1.eval (-(n : ℝ)) := by
  rw [prod_factor_minus_one, P1_eval_neg, gamma1]

lemma beta1_eq (n : ℕ) :
    beta1 (n : ℝ) = Q1.eval ((n : ℝ) ^ 2) := by
  rw [Q1_eval, beta1]; ring

lemma m1_recurrence_of_two (n : ℕ) (hn : 2 ≤ n) :
    prod_factor_plus 1 n * P1.eval (n : ℝ) * A103885_subsequence_real 1 (n + 1) +
      ((-1 : ℝ) ^ 1 * prod_factor_minus 1 n * P1.eval (-(n : ℝ))) *
        A103885_subsequence_real 1 (n - 1) =
      Q1.eval ((n : ℝ) ^ 2) * A103885_subsequence_real 1 n := by
  unfold A103885_subsequence_real
  simp only [one_mul, pow_one]
  have hsum := m1_wz_sum n hn
  rw [alpha1_eq, gamma1_eq, beta1_eq] at hsum
  linarith

lemma m1_recurrence (n : ℕ) (hn : 1 ≤ n) :
    prod_factor_plus 1 n * P1.eval (n : ℝ) * A103885_subsequence_real 1 (n + 1) +
      ((-1 : ℝ) ^ 1 * prod_factor_minus 1 n * P1.eval (-(n : ℝ))) *
        A103885_subsequence_real 1 (n - 1) =
      Q1.eval ((n : ℝ) ^ 2) * A103885_subsequence_real 1 n := by
  by_cases h1 : n = 1
  · subst h1
    have ha0 : A103885_subsequence_real 1 0 = 1 := by
      unfold A103885_subsequence_real; rw [A103885_zero]; norm_num
    have ha1 : A103885_subsequence_real 1 1 = 2 := by
      unfold A103885_subsequence_real; change (A103885 1 : ℝ) = 2; rw [A103885_one]; norm_num
    have ha2 : A103885_subsequence_real 1 2 = 16 := by
      unfold A103885_subsequence_real; change (A103885 2 : ℝ) = 16; rw [A103885_two]; norm_num
    rw [prod_factor_plus_one, prod_factor_minus_one, P1_eval, P1_eval_neg, Q1_eval,
      ha0, ha1, ha2]
    norm_num
  · exact m1_recurrence_of_two n (by omega)

lemma alpha1_neg (n : ℝ) : alpha1 (-n) = gamma1 n := by
  unfold alpha1 gamma1
  ring

lemma m1_recurrence_S (n : ℕ) (hn : 1 ≤ n) :
    alpha1 (n : ℝ) * (A103885 (n + 1) : ℝ)
      - alpha1 (-(n : ℝ)) * (A103885 (n - 1) : ℝ)
      = beta1 (n : ℝ) * (A103885 n : ℝ) := by
  rw [alpha1_neg]
  by_cases h2 : 2 ≤ n
  · exact m1_wz_sum n h2
  · have hn1 : n = 1 := by omega
    subst hn1
    unfold alpha1 gamma1 beta1
    rw [A103885_zero, A103885_one, A103885_two]
    norm_num

/-- Unnormalized transfer matrix S(x) = [[β(x), α(-x)], [α(x), 0]]. -/
noncomputable def Smat (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![beta1 x, alpha1 (-x); alpha1 x, 0]

/-- Polynomial versions of the m=1 coefficients. -/
noncomputable def alphaP : Polynomial ℝ :=
  (C (2 : ℝ) * X + C 1) * (C (2 : ℝ) * X + C 2) * P1

noncomputable def betaP : Polynomial ℝ :=
  C (4 : ℝ) * (C (55 : ℝ) * X ^ 4 - C (34 : ℝ) * X ^ 2 + C 3)

lemma alphaP_eval (x : ℝ) : alphaP.eval x = alpha1 x := by
  unfold alphaP alpha1 P1
  simp [eval_mul, eval_add, eval_pow]
  try ring

lemma betaP_eval (x : ℝ) : betaP.eval x = beta1 x := by
  unfold betaP beta1
  simp [eval_mul, eval_add, eval_pow, eval_sub]
  try ring

/-- Shift a polynomial: `p(X + a)`. -/
noncomputable def shiftP (p : Polynomial ℝ) (a : ℝ) : Polynomial ℝ :=
  p.comp (X + C a)

/-- Polynomial transfer matrix `S(X + a)`. -/
noncomputable def SmatP (a : ℝ) : Matrix (Fin 2) (Fin 2) (Polynomial ℝ) :=
  !![shiftP betaP a, shiftP (alphaP.comp (-X)) a; shiftP alphaP a, 0]

/-- The polynomial matrix product `S(X+m-1) ⋯ S(X)`. -/
noncomputable def SprodP : ℕ → Matrix (Fin 2) (Fin 2) (Polynomial ℝ)
  | 0 => 1
  | m + 1 => SmatP (m : ℝ) * SprodP m

/-- The polynomial `(S(X+m-1) ⋯ S(X))_{0 1}` in the starting position. -/
noncomputable def fSP (m : ℕ) : Polynomial ℝ :=
  SprodP m 0 1

lemma SprodP_zero : SprodP 0 = 1 := rfl

lemma SprodP_succ (m : ℕ) : SprodP (m + 1) = SmatP (m : ℝ) * SprodP m := rfl

lemma fSP_zero : fSP 0 = 0 := by
  simp [fSP, SprodP_zero]

lemma fSP_one : fSP 1 = alphaP.comp (-X) := by
  simp [fSP, SprodP, SmatP, shiftP]

lemma SprodP_21 (m : ℕ) (hm : 1 ≤ m) :
    SprodP m 1 1 = shiftP alphaP ((m : ℝ) - 1) * fSP (m - 1) := by
  revert hm
  cases m with
  | zero => intro h; omega
  | succ m =>
    intro _
    rw [SprodP_succ]
    simp [Matrix.mul_apply, SmatP, fSP, Fin.sum_univ_two]

lemma fSP_succ_succ (m : ℕ) :
    fSP (m + 2) =
      shiftP betaP (m + 1 : ℝ) * fSP (m + 1) +
        shiftP (alphaP.comp (-X)) (m + 1 : ℝ) * shiftP alphaP (m : ℝ) * fSP m := by
  rw [fSP, SprodP_succ]
  simp [Matrix.mul_apply, Fin.sum_univ_two, SmatP]
  -- fSP (m+2) = shiftP betaP (m+1) * SprodP (m+1) 0 1
  --            + shiftP (alphaP.comp (-X)) (m+1) * SprodP (m+1) 1 1
  have h21 : SprodP (m + 1) 1 1 = shiftP alphaP (m : ℝ) * fSP m := by
    simpa using SprodP_21 (m + 1) (Nat.succ_pos m)
  rw [h21]
  simp [fSP]
  ring

/-- Vector `(a(n), a(n-1))`. -/
noncomputable def avec (n : ℕ) : Fin 2 → ℝ :=
  ![ (A103885 n : ℝ), (A103885 (n - 1) : ℝ) ]

lemma mulVec_fin2 (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (i : Fin 2) :
    (M.mulVec v) i = M i 0 * v 0 + M i 1 * v 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma Smat_mulVec (n : ℕ) (hn : 1 ≤ n) :
    Matrix.mulVec (Smat (n : ℝ)) (avec n) = alpha1 (n : ℝ) • avec (n + 1) := by
  have hrec := m1_recurrence_S n hn
  ext i
  fin_cases i <;>
    simp [Smat, avec, mulVec_fin2, Pi.smul_apply] <;>
    try linarith [hrec]

/-- Product `S(n+m-1) ⋯ S(n)` as a numeric matrix. -/
noncomputable def Sprod (m n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (List.range m).foldl (fun acc i => Smat ((n + i : ℕ) : ℝ) * acc) 1

lemma Sprod_zero (n : ℕ) : Sprod 0 n = 1 := rfl

lemma Sprod_succ (m n : ℕ) :
    Sprod (m + 1) n = Smat ((n + m : ℕ) : ℝ) * Sprod m n := by
  simp [Sprod, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma Sprod_mulVec (m n : ℕ) (hn : 1 ≤ n) :
    Matrix.mulVec (Sprod m n) (avec n) =
      ((Finset.range m).prod (fun i => alpha1 ((n + i : ℕ) : ℝ))) • avec (n + m) := by
  induction m with
  | zero =>
    simp [Sprod_zero, avec]
  | succ m ih =>
    rw [Sprod_succ, ← Matrix.mulVec_mulVec, ih]
    have hn' : 1 ≤ n + m := by omega
    have hS := Smat_mulVec (n + m) hn'
    rw [Matrix.mulVec_smul, hS]
    simp [Finset.prod_range_succ, smul_smul, mul_comm, add_assoc]

/-- Forward product starting at `m * n`. -/
noncomputable def Uprod (m n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Sprod m (m * n)

/-- Backward product starting at `m * n - m`. -/
noncomputable def Fprod (m n : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Sprod m (m * (n - 1))

lemma Uprod_mulVec (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Matrix.mulVec (Uprod m n) (avec (m * n)) =
      ((Finset.range m).prod (fun i => alpha1 ((m * n + i : ℕ) : ℝ))) •
        avec (m * (n + 1)) := by
  have h : 1 ≤ m * n := Nat.mul_pos hm hn
  simpa [Uprod, mul_add, mul_one, add_comm, add_left_comm, add_assoc] using
    Sprod_mulVec m (m * n) h

lemma Fprod_mulVec (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) :
    Matrix.mulVec (Fprod m n) (avec (m * (n - 1))) =
      ((Finset.range m).prod (fun i => alpha1 ((m * (n - 1) + i : ℕ) : ℝ))) •
        avec (m * n) := by
  have h : 1 ≤ m * (n - 1) := by
    have : 1 ≤ n - 1 := by omega
    exact Nat.mul_pos hm this
  have hmn : m * (n - 1) + m = m * n := by
    have : n - 1 + 1 = n := by omega
    calc m * (n - 1) + m = m * (n - 1) + m * 1 := by rw [mul_one]
      _ = m * (n - 1 + 1) := by rw [← mul_add]
      _ = m * n := by rw [this]
  simpa [Fprod, hmn] using Sprod_mulVec m (m * (n - 1)) h

/-- Unnormalized forward coefficient of `a(m(n+1))`. -/
noncomputable def cPlus (m n : ℕ) : ℝ :=
  ((Finset.range m).prod (fun i => alpha1 ((m * (n - 1) + i : ℕ) : ℝ))) *
    Fprod m n 0 1

/-- The three-term identity obtained by eliminating `a(mn-1)`. -/
lemma transfer_three_term (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) :
    let paf := (Finset.range m).prod (fun i => alpha1 ((m * n + i : ℕ) : ℝ))
    let pab := (Finset.range m).prod (fun i => alpha1 ((m * (n - 1) + i : ℕ) : ℝ))
    let U := Uprod m n
    let F := Fprod m n
    pab * F 0 1 * paf * (A103885 (m * (n + 1)) : ℝ)
      + U 0 1 * F.det * (A103885 (m * (n - 1)) : ℝ)
      = pab * (F 0 1 * U 0 0 + U 0 1 * F 1 1) * (A103885 (m * n) : ℝ) := by
  intro paf pab U F
  have hU := Uprod_mulVec m n hm (by omega : 1 ≤ n)
  have hF := Fprod_mulVec m n hm hn
  have hU0 : U 0 0 * (A103885 (m * n) : ℝ) + U 0 1 * (A103885 (m * n - 1) : ℝ) =
      paf * (A103885 (m * (n + 1)) : ℝ) := by
    have := congrArg (fun v : Fin 2 → ℝ => v 0) hU
    simp [avec, mulVec_fin2, Pi.smul_apply] at this
    simpa [Uprod, paf] using this
  have hF0 : F 0 0 * (A103885 (m * (n - 1)) : ℝ)
      + F 0 1 * (A103885 (m * (n - 1) - 1) : ℝ) =
      pab * (A103885 (m * n) : ℝ) := by
    have := congrArg (fun v : Fin 2 → ℝ => v 0) hF
    simp [avec, mulVec_fin2, Pi.smul_apply] at this
    simpa [Fprod, pab] using this
  have hF1 : F 1 0 * (A103885 (m * (n - 1)) : ℝ)
      + F 1 1 * (A103885 (m * (n - 1) - 1) : ℝ) =
      pab * (A103885 (m * n - 1) : ℝ) := by
    have := congrArg (fun v : Fin 2 → ℝ => v 1) hF
    simp [avec, mulVec_fin2, Pi.smul_apply] at this
    simpa [Fprod, pab] using this
  have hdetF : F.det = F 0 0 * F 1 1 - F 0 1 * F 1 0 := by
    simp [Matrix.det_fin_two]
  have hdet :
      F.det * (A103885 (m * (n - 1)) : ℝ) =
        pab * (F 1 1 * (A103885 (m * n) : ℝ) - F 0 1 * (A103885 (m * n - 1) : ℝ)) := by
    rw [hdetF]
    linear_combination (F 1 1) * hF0 - (F 0 1) * hF1
  set aN := (A103885 (m * n) : ℝ)
  set aNp := (A103885 (m * (n + 1)) : ℝ)
  set aNm := (A103885 (m * (n - 1)) : ℝ)
  set aN1 := (A103885 (m * n - 1) : ℝ)
  have hU0' : U 0 0 * aN + U 0 1 * aN1 = paf * aNp := by
    simpa [aN, aN1, aNp] using hU0
  have hdet' : F.det * aNm = pab * (F 1 1 * aN - F 0 1 * aN1) := by
    simpa [aN, aNm, aN1] using hdet
  have hrepl1 : pab * F 0 1 * paf * aNp = pab * F 0 1 * (U 0 0 * aN + U 0 1 * aN1) := by
    have := congrArg (fun t : ℝ => pab * F 0 1 * t) hU0'.symm
    convert this using 1 <;> ring
  have hrepl2 : U 0 1 * F.det * aNm = U 0 1 * (pab * (F 1 1 * aN - F 0 1 * aN1)) := by
    have := congrArg (fun t : ℝ => U 0 1 * t) hdet'
    convert this using 1 <;> ring
  calc
    pab * F 0 1 * paf * (A103885 (m * (n + 1)) : ℝ)
        + U 0 1 * F.det * (A103885 (m * (n - 1)) : ℝ)
        = pab * F 0 1 * paf * aNp + U 0 1 * F.det * aNm := by
          simp [aNp, aNm]
    _ = pab * F 0 1 * (U 0 0 * aN + U 0 1 * aN1)
          + U 0 1 * (pab * (F 1 1 * aN - F 0 1 * aN1)) := by
          rw [hrepl1, hrepl2]
    _ = pab * (F 0 1 * U 0 0 + U 0 1 * F 1 1) * aN := by
          ring
    _ = pab * (F 0 1 * U 0 0 + U 0 1 * F 1 1) * (A103885 (m * n) : ℝ) := by
          simp [aN]

/-- Recursive real transfer product `S(x+m-1) ⋯ S(x)`. -/
noncomputable def SprodR : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℝ
  | 0, _ => 1
  | m + 1, x => Smat (x + m) * SprodR m x

lemma SprodR_zero (x : ℝ) : SprodR 0 x = 1 := rfl

lemma SprodR_succ (m : ℕ) (x : ℝ) :
    SprodR (m + 1) x = Smat (x + m) * SprodR m x := rfl

lemma SprodR_nat (m n : ℕ) : SprodR m (n : ℝ) = Sprod m n := by
  induction m with
  | zero => simp [SprodR_zero, Sprod_zero]
  | succ m ih =>
    rw [SprodR_succ, Sprod_succ, ih]
    simp

lemma shiftP_eval (p : Polynomial ℝ) (a x : ℝ) :
    (shiftP p a).eval x = p.eval (x + a) := by
  simp [shiftP, eval_comp, eval_add]

lemma alphaP_comp_neg_eval (x : ℝ) :
    (alphaP.comp (-X)).eval x = alpha1 (-x) := by
  rw [eval_comp, eval_neg, eval_X, alphaP_eval]

lemma SmatP_eval (a x : ℝ) (i j : Fin 2) :
    (SmatP a i j).eval x = Smat (x + a) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [SmatP, Smat, shiftP_eval, alphaP_eval, betaP_eval, alphaP_comp_neg_eval,
      eval_zero]

lemma SprodP_eval (m : ℕ) (x : ℝ) (i j : Fin 2) :
    (SprodP m i j).eval x = SprodR m x i j := by
  induction m generalizing i j with
  | zero =>
    simp [SprodP_zero, SprodR_zero]
    by_cases h : i = j
    · subst h
      simp [Matrix.one_apply]
    · simp [Matrix.one_apply, h]
  | succ m ih =>
    rw [SprodP_succ, SprodR_succ]
    simp [Matrix.mul_apply, Fin.sum_univ_two, eval_add, eval_mul]
    rw [SmatP_eval, SmatP_eval, ih, ih]

lemma fSP_eval (m : ℕ) (x : ℝ) : (fSP m).eval x = SprodR m x 0 1 := by
  simp [fSP, SprodP_eval]

lemma fSP_eval_nat (m n : ℕ) : (fSP m).eval (n : ℝ) = Sprod m n 0 1 := by
  rw [fSP_eval, SprodR_nat]

lemma Fprod_01 (m n : ℕ) :
    Fprod m n 0 1 = (fSP m).eval ((m * (n - 1) : ℕ) : ℝ) := by
  rw [Fprod, fSP_eval_nat]

lemma Uprod_01 (m n : ℕ) :
    Uprod m n 0 1 = (fSP m).eval ((m * n : ℕ) : ℝ) := by
  rw [Uprod, fSP_eval_nat]

/-- `det S(x) = -α(x) α(-x)`. -/
lemma Smat_det (x : ℝ) : (Smat x).det = - alpha1 x * alpha1 (-x) := by
  simp [Smat, Matrix.det_fin_two]
  ring

lemma Sprod_det (m n : ℕ) :
    (Sprod m n).det =
      (Finset.range m).prod
        (fun i => - alpha1 ((n + i : ℕ) : ℝ) * alpha1 (-((n + i : ℕ) : ℝ))) := by
  induction m with
  | zero => simp [Sprod_zero]
  | succ m ih =>
    rw [Sprod_succ, Matrix.det_mul, ih, Smat_det, Finset.prod_range_succ]
    ring

/-- Polynomial identity for the two-step bracket. -/
lemma beta_alpha_bracket (x : ℝ) :
    beta1 x * beta1 (x + 1) + alpha1 (-x - 1) * alpha1 x =
      (5 * x ^ 2 + 5 * x + 1) *
        (4 * (2440 * x ^ 6 + 7320 * x ^ 5 + 3813 * x ^ 4
          - 4574 * x ^ 3 - 3112 * x ^ 2 + 395 * x + 288)) := by
  unfold beta1 alpha1
  ring

lemma beta_alpha_bracket_of_P1_neg {x : ℝ} (h : P1.eval (-x) = 0) :
    beta1 x * beta1 (x + 1) + alpha1 (-x - 1) * alpha1 x = 0 := by
  have : 5 * x ^ 2 + 5 * x + 1 = 0 := by
    simpa [P1_eval] using h
  rw [beta_alpha_bracket, this, zero_mul]

/-- The two real roots of `P1(-X) = 5X^2 + 5X + 1`. -/
noncomputable def sigma1 : ℝ := (-5 + Real.sqrt 5) / 10
noncomputable def sigma2 : ℝ := (-5 - Real.sqrt 5) / 10

lemma sq_sqrt5 : (Real.sqrt 5) ^ 2 = 5 :=
  Real.sq_sqrt (by norm_num)

lemma P1_eval_neg_sigma1 : P1.eval (-sigma1) = 0 := by
  unfold P1 sigma1
  simp
  have hs : (Real.sqrt 5) ^ 2 = 5 := sq_sqrt5
  field_simp
  ring_nf
  rw [hs]
  ring

lemma P1_eval_neg_sigma2 : P1.eval (-sigma2) = 0 := by
  unfold P1 sigma2
  simp
  have hs : (Real.sqrt 5) ^ 2 = 5 := sq_sqrt5
  field_simp
  ring_nf
  rw [hs]
  ring

lemma P1_eval_succ_of_neg {s : ℝ} (h : P1.eval (-s) = 0) :
    P1.eval (s + 1) = 0 := by
  simp [P1_eval] at h ⊢
  nlinarith [h]

lemma alpha1_of_P1 {x : ℝ} (h : P1.eval x = 0) : alpha1 x = 0 := by
  unfold alpha1
  simp [P1_eval] at h
  nlinarith [h]

/-- Factors of `P1` peeled from `fSP`. Empty product when `m < 2`. -/
noncomputable def peelP1 (m : ℕ) : Polynomial ℝ :=
  (Finset.Icc 1 m.pred.pred).prod fun j => P1.comp (-X - C (j : ℝ))

noncomputable def knownFactor (m : ℕ) : Polynomial ℝ :=
  alphaP.comp (-X) * peelP1 m

lemma peelP1_one : peelP1 1 = 1 := by
  simp [peelP1]

lemma peelP1_two : peelP1 2 = 1 := by
  simp [peelP1]

lemma knownFactor_one : knownFactor 1 = alphaP.comp (-X) := by
  simp [knownFactor, peelP1_one]

lemma knownFactor_two : knownFactor 2 = alphaP.comp (-X) := by
  simp [knownFactor, peelP1_two]

lemma fSP_dvd_alpha_neg : ∀ m : ℕ, alphaP.comp (-X) ∣ fSP m
  | 0 => dvd_zero _
  | 1 => ⟨1, by simp [fSP_one]⟩
  | m + 2 => by
      have h1 := fSP_dvd_alpha_neg (m + 1)
      have h0 := fSP_dvd_alpha_neg m
      rw [fSP_succ_succ]
      refine dvd_add ?_ ?_
      · exact dvd_mul_of_dvd_right h1 _
      · exact dvd_mul_of_dvd_right h0 _

lemma fSP_eval_succ_succ (m : ℕ) (x : ℝ) :
    (fSP (m + 2)).eval x =
      beta1 (x + m + 1) * (fSP (m + 1)).eval x +
        alpha1 (-(x + m + 1)) * alpha1 (x + m) * (fSP m).eval x := by
  rw [fSP_succ_succ]
  simp only [eval_add, eval_mul, shiftP_eval, betaP_eval, alphaP_eval,
    alphaP_comp_neg_eval]
  ring

lemma Smat_mul_col1_of_alpha_neg (x : ℝ) (hx : alpha1 (-x) = 0)
    (M : Matrix (Fin 2) (Fin 2) ℝ) :
    (Smat x * M) 0 1 = beta1 x * M 0 1 ∧
    (Smat x * M) 1 1 = alpha1 x * M 0 1 := by
  constructor
  · simp [Smat, Matrix.mul_apply, Fin.sum_univ_two, hx]
  · simp [Smat, Matrix.mul_apply, Fin.sum_univ_two]

lemma SprodR_succ_succ (k : ℕ) (x : ℝ) :
    SprodR (k + 2) x = Smat (x + (k + 1 : ℕ)) * (Smat (x + k) * SprodR k x) := by
  rw [SprodR_succ, SprodR_succ, Nat.cast_succ]

lemma mulVec_Smat_apply (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    (A * B) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma fSP_eval_sigma_sub_base (j : ℕ) (s : ℝ) (hs : P1.eval (-s) = 0) :
    (fSP (j + 2)).eval (s - (j : ℝ)) = 0 := by
  rw [fSP_eval, SprodR_succ_succ]
  have h1 : s - (j : ℝ) + (j + 1 : ℕ) = s + 1 := by
    simp [Nat.cast_add, Nat.cast_one]; ring
  have h0 : s - (j : ℝ) + j = s := by ring
  rw [h1, h0]
  set M := SprodR j (s - (j : ℝ))
  have ha : alpha1 (-s) = 0 := alpha1_of_P1 hs
  have hc := Smat_mul_col1_of_alpha_neg s ha M
  rw [mulVec_Smat_apply]
  have hA00 : Smat (s + 1) 0 0 = beta1 (s + 1) := by simp [Smat]
  have hA01 : Smat (s + 1) 0 1 = alpha1 (-(s + 1)) := by simp [Smat]
  rw [hA00, hA01, hc.1, hc.2]
  have hbr := beta_alpha_bracket_of_P1_neg hs
  have hbr' : beta1 (s + 1) * beta1 s + alpha1 (-(s + 1)) * alpha1 s = 0 := by
    convert hbr using 1 <;> ring
  linear_combination M 0 1 * hbr'

lemma fSP_eval_sigma_sub_step (j : ℕ) (s : ℝ) (hs : P1.eval (-s) = 0)
    (hprev : (fSP (j + 2)).eval (s - (j : ℝ)) = 0) :
    (fSP (j + 3)).eval (s - (j : ℝ)) = 0 := by
  rw [show j + 3 = (j + 1) + 2 by ring, fSP_eval_succ_succ, hprev, mul_zero, zero_add]
  have hP : P1.eval (s + 1) = 0 := P1_eval_succ_of_neg hs
  have ha : alpha1 (s + 1) = 0 := alpha1_of_P1 hP
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by simp
  have hshift : s - (j : ℝ) + (j + 1 : ℕ) = s + 1 := by
    rw [hcast]; ring
  rw [hshift, ha, mul_zero, zero_mul]

/-- `fSP m` vanishes at `s - j` whenever `P1(-s) = 0` and `m ≥ j + 2`. -/
lemma fSP_eval_sigma_sub (m j : ℕ) (s : ℝ) (hs : P1.eval (-s) = 0)
    (hj : 1 ≤ j) (hjm : j + 2 ≤ m) :
    (fSP m).eval (s - (j : ℝ)) = 0 := by
  revert hjm
  induction m using Nat.strong_induction_on with
  | h m ihm =>
    intro hjm
    have hcases : m = j + 2 ∨ m = j + 3 ∨ j + 4 ≤ m := by omega
    rcases hcases with hm | hm | hm
    · subst hm
      exact fSP_eval_sigma_sub_base j s hs
    · subst hm
      refine fSP_eval_sigma_sub_step j s hs ?_
      exact ihm (j + 2) (by omega) (by omega)
    · rw [show m = (m - 2) + 2 by omega, fSP_eval_succ_succ]
      have hm1 : m - 2 + 1 = m - 1 := by omega
      have h1 : (fSP (m - 1)).eval (s - (j : ℝ)) = 0 :=
        ihm (m - 1) (by omega) (by omega)
      have h0 : (fSP (m - 2)).eval (s - (j : ℝ)) = 0 :=
        ihm (m - 2) (by omega) (by omega)
      rw [hm1, h1, h0]
      ring

lemma P1_comp_neg_shift (j : ℕ) (x : ℝ) :
    (P1.comp (-X - C (j : ℝ))).eval x = P1.eval (-x - j) := by
  simp [eval_comp, eval_add, eval_neg, eval_C]

lemma sigma_sum : sigma1 + sigma2 = -1 := by
  unfold sigma1 sigma2
  ring

lemma sigma_prod : sigma1 * sigma2 = (1 / 5 : ℝ) := by
  unfold sigma1 sigma2
  have hs : (Real.sqrt 5) ^ 2 = 5 := sq_sqrt5
  field_simp
  ring_nf
  rw [hs]
  ring

lemma two_ne_of_sigma : sigma1 ≠ sigma2 := by
  unfold sigma1 sigma2
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  field_simp
  linarith

lemma isRoot_P1_comp (j : ℕ) (s : ℝ) (hs : P1.eval (-s) = 0) :
    (P1.comp (-X - C (j : ℝ))).IsRoot (s - j) := by
  simp [IsRoot, P1_comp_neg_shift]
  convert hs using 1 <;> ring

lemma P1_shift_ne_zero (j : ℕ) : P1.comp (-X - C (j : ℝ)) ≠ 0 := by
  intro h
  have := congrArg (fun p => p.eval 0) h
  simp [P1_comp_neg_shift, P1_eval] at this
  nlinarith [sq_nonneg (j : ℝ)]

lemma P1_shift_eq_linears (j : ℕ) :
    P1.comp (-X - C (j : ℝ)) =
      C (5 : ℝ) * (X - C (sigma1 - (j : ℝ))) * (X - C (sigma2 - (j : ℝ))) := by
  apply Polynomial.funext
  intro x
  rw [P1_comp_neg_shift, P1_eval]
  simp [eval_mul, eval_sub]
  have h1 : 5 * (-x - (j : ℝ)) ^ 2 - 5 * (-x - (j : ℝ)) + 1 =
      5 * (x + j) ^ 2 + 5 * (x + j) + 1 := by ring
  have h2 : 5 * (x - (sigma1 - (j : ℝ))) * (x - (sigma2 - (j : ℝ))) =
      5 * ((x + j) ^ 2 - (sigma1 + sigma2) * (x + j) + sigma1 * sigma2) := by
    ring
  rw [h1, h2, sigma_sum, sigma_prod]
  ring

lemma P1_shift_dvd_fSP (m j : ℕ) (hj : 1 ≤ j) (hjm : j + 2 ≤ m) :
    P1.comp (-X - C (j : ℝ)) ∣ fSP m := by
  have h1 : (fSP m).IsRoot (sigma1 - j) := by
    simpa [IsRoot] using
      fSP_eval_sigma_sub m j sigma1 P1_eval_neg_sigma1 hj hjm
  have h2 : (fSP m).IsRoot (sigma2 - j) := by
    simpa [IsRoot] using
      fSP_eval_sigma_sub m j sigma2 P1_eval_neg_sigma2 hj hjm
  have e1 : X - C (sigma1 - (j : ℝ)) ∣ fSP m := dvd_iff_isRoot.mpr h1
  have e2 : X - C (sigma2 - (j : ℝ)) ∣ fSP m := dvd_iff_isRoot.mpr h2
  have hne : sigma1 - (j : ℝ) ≠ sigma2 - (j : ℝ) := by
    intro h; exact two_ne_of_sigma (by linarith)
  have hcop :
      IsCoprime (X - C (sigma1 - (j : ℝ))) (X - C (sigma2 - (j : ℝ))) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne hne).isUnit
  have hmul : (X - C (sigma1 - (j : ℝ))) * (X - C (sigma2 - (j : ℝ))) ∣ fSP m :=
    hcop.mul_dvd e1 e2
  rw [P1_shift_eq_linears, mul_assoc]
  have hu : IsUnit (C (5 : ℝ)) := isUnit_C.mpr (by norm_num)
  simpa [mul_comm] using hu.mul_right_dvd.mpr hmul

lemma sqrt5_gt_two : (2 : ℝ) < Real.sqrt 5 := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma sqrt5_lt_three : Real.sqrt 5 < (3 : ℝ) := by
  rw [Real.sqrt_lt (by norm_num) (by norm_num)]
  norm_num

lemma sigma1_mem : sigma1 ∈ Set.Ioo (-(1 : ℝ)) 0 := by
  unfold sigma1
  have hs1 := sqrt5_gt_two
  have hs2 := sqrt5_lt_three
  constructor <;> { field_simp; linarith }

lemma sigma2_mem : sigma2 ∈ Set.Ioo (-(1 : ℝ)) 0 := by
  unfold sigma2
  have hs1 := sqrt5_gt_two
  have hs2 := sqrt5_lt_three
  constructor <;> { field_simp; linarith }

lemma sigma_diff : sigma1 - sigma2 = Real.sqrt 5 / 5 := by
  unfold sigma1 sigma2; ring

lemma sigma_diff_not_int {k : ℤ} : sigma1 - sigma2 ≠ (k : ℝ) := by
  intro h
  have hsq : (1 : ℝ) / 5 = (k : ℝ) ^ 2 := by
    have : (Real.sqrt 5 / 5) ^ 2 = (k : ℝ) ^ 2 := by rw [← sigma_diff, h]
    have h5 : (Real.sqrt 5) ^ 2 = 5 := sq_sqrt5
    field_simp [h5] at this
    linarith
  have : (5 : ℝ) * (k : ℝ) ^ 2 = 1 := by linarith
  have hint : (5 : ℤ) * k ^ 2 = 1 := by exact_mod_cast this
  have : (5 : ℤ) ∣ 1 := ⟨k ^ 2, by linarith [hint]⟩
  norm_num at this

lemma sigma_shift_ne {i j : ℕ} (hij : i ≠ j) (a b : ℝ)
    (ha : a = sigma1 ∨ a = sigma2) (hb : b = sigma1 ∨ b = sigma2) :
    a - (i : ℝ) ≠ b - (j : ℝ) := by
  intro heq
  have hdiff : a - b = (i : ℝ) - j := by linarith
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hij (Nat.cast_injective (by linarith : (i : ℝ) = j))
  · apply sigma_diff_not_int (k := (i : ℤ) - j)
    simp [Int.cast_sub]; linarith
  · apply sigma_diff_not_int (k := (j : ℤ) - i)
    simp [Int.cast_sub]; linarith
  · exact hij (Nat.cast_injective (by linarith : (i : ℝ) = j))

lemma isCoprime_of_splits_no_common_root {p q : ℝ[X]}
    (hp : p.Splits) (hp0 : p ≠ 0)
    (h : ∀ x, p.IsRoot x → ¬ q.IsRoot x) : IsCoprime p q := by
  rw [← gcd_isUnit_iff]
  have hd_dvd : gcd p q ∣ p := gcd_dvd_left _ _
  have hd0 : gcd p q ≠ 0 := by
    intro hd
    have : p = 0 := eq_zero_of_zero_dvd (hd ▸ gcd_dvd_left p q)
    exact hp0 this
  have hds : (gcd p q).Splits := Splits.of_dvd hp hp0 hd_dvd
  by_cases hdeg : (gcd p q).degree = 0
  · exact isUnit_iff_degree_eq_zero.mpr hdeg
  · obtain ⟨x, hx⟩ := hds.exists_eval_eq_zero hdeg
    have hp_root : p.IsRoot x := eval_eq_zero_of_dvd_of_eval_eq_zero hd_dvd hx
    have hq_dvd : gcd p q ∣ q := gcd_dvd_right _ _
    have hq_root : q.IsRoot x := eval_eq_zero_of_dvd_of_eval_eq_zero hq_dvd hx
    exact (h x hp_root hq_root).elim

lemma P1_shift_splits (j : ℕ) : (P1.comp (-X - C (j : ℝ))).Splits := by
  rw [P1_shift_eq_linears]
  exact ((Splits.C (5 : ℝ)).mul (Splits.X_sub_C _)).mul (Splits.X_sub_C _)

lemma P1_shift_roots {j : ℕ} {x : ℝ} (hx : (P1.comp (-X - C (j : ℝ))).IsRoot x) :
    x = sigma1 - j ∨ x = sigma2 - j := by
  rw [IsRoot, P1_shift_eq_linears] at hx
  have hx5 : (5 : ℝ) * (x - (sigma1 - j)) * (x - (sigma2 - j)) = 0 := by
    simpa [eval_mul, eval_sub] using hx
  have h5 : (5 : ℝ) ≠ 0 := by norm_num
  have hxmul : (5 : ℝ) * ((x - (sigma1 - j)) * (x - (sigma2 - j))) = 0 := by
    convert hx5 using 1; ring
  have hprod : (x - (sigma1 - j)) * (x - (sigma2 - j)) = 0 :=
    (mul_eq_zero.mp hxmul).resolve_left h5
  exact (mul_eq_zero.mp hprod).imp (fun h => by linarith) (fun h => by linarith)

lemma P1_shift_coprime {i j : ℕ} (hij : i ≠ j) :
    IsCoprime (P1.comp (-X - C (i : ℝ))) (P1.comp (-X - C (j : ℝ))) := by
  refine isCoprime_of_splits_no_common_root (P1_shift_splits i) (P1_shift_ne_zero i) ?_
  intro x hx hxj
  have hx' := P1_shift_roots hx
  have hxj' := P1_shift_roots hxj
  rcases hx' with hx' | hx' <;> rcases hxj' with hxj' | hxj'
  · exact sigma_shift_ne hij sigma1 sigma1 (Or.inl rfl) (Or.inl rfl) (by linarith)
  · exact sigma_shift_ne hij sigma1 sigma2 (Or.inl rfl) (Or.inr rfl) (by linarith)
  · exact sigma_shift_ne hij sigma2 sigma1 (Or.inr rfl) (Or.inl rfl) (by linarith)
  · exact sigma_shift_ne hij sigma2 sigma2 (Or.inr rfl) (Or.inr rfl) (by linarith)

lemma peelP1_dvd_fSP : ∀ m : ℕ, peelP1 m ∣ fSP m
  | 0 => dvd_zero _
  | 1 => by simp [peelP1_one]
  | 2 => by simp [peelP1_two]
  | m + 3 => by
      have hrange : Finset.Icc 1 (m + 3).pred.pred = Finset.Icc 1 (m + 1) := by
        simp [Nat.pred]
      have : peelP1 (m + 3) =
          (Finset.Icc 1 (m + 1)).prod fun j => P1.comp (-X - C (j : ℝ)) := by
        simp [peelP1, hrange]
      rw [this]
      refine Finset.prod_dvd_of_coprime ?_ ?_
      · intro a ha b hb hab
        exact P1_shift_coprime hab
      · intro j hj
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
        have hj2 : j ≤ m + 1 := (Finset.mem_Icc.mp hj).2
        exact P1_shift_dvd_fSP (m + 3) j hj1 (by omega)

lemma alphaP_comp_neg_ne_zero : alphaP.comp (-X) ≠ 0 := by
  intro h0
  have := congrArg (fun p : Polynomial ℝ => p.eval 0) h0
  simp [eval_comp, eval_neg, eval_X] at this
  have hα := alphaP_eval 0
  simp [alpha1] at hα
  linarith

lemma peelP1_ne_zero (m : ℕ) : peelP1 m ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  exact P1_shift_ne_zero j

lemma knownFactor_ne_zero (m : ℕ) : knownFactor m ≠ 0 := by
  exact mul_ne_zero alphaP_comp_neg_ne_zero (peelP1_ne_zero m)

lemma alphaP_comp_neg_eq :
    alphaP.comp (-X) =
      C (20 : ℝ) * (X - C ((1 : ℝ) / 2)) * (X - C (1 : ℝ)) *
        (X - C sigma1) * (X - C sigma2) := by
  apply Polynomial.funext
  intro x
  rw [alphaP_comp_neg_eval]
  unfold alpha1
  simp only [eval_mul, eval_sub, eval_C, eval_X]
  have hP : 5 * x ^ 2 + 5 * x + 1 = 5 * (x - sigma1) * (x - sigma2) := by
    have h1 : 5 * (x - sigma1) * (x - sigma2) =
        5 * (x ^ 2 - (sigma1 + sigma2) * x + sigma1 * sigma2) := by ring
    rw [h1, sigma_sum, sigma_prod]
    ring
  rw [show (2 * (-x) + 1) * (2 * (-x) + 2) * (5 * (-x) ^ 2 - 5 * (-x) + 1) =
        (-(2 * x) + 1) * (-(2 * x) + 2) * (5 * x ^ 2 + 5 * x + 1) by ring, hP]
  ring

lemma alphaP_comp_neg_splits : (alphaP.comp (-X)).Splits := by
  rw [alphaP_comp_neg_eq]
  exact ((((Splits.C (20 : ℝ)).mul (Splits.X_sub_C _)).mul (Splits.X_sub_C _)).mul
    (Splits.X_sub_C _)).mul (Splits.X_sub_C _)

lemma alphaP_comp_neg_roots {x : ℝ} (hx : (alphaP.comp (-X)).IsRoot x) :
    x = (1 / 2 : ℝ) ∨ x = 1 ∨ x = sigma1 ∨ x = sigma2 := by
  rw [IsRoot, alphaP_comp_neg_eq] at hx
  have hx20 :
      (20 : ℝ) * (x - 1 / 2) * (x - 1) * (x - sigma1) * (x - sigma2) = 0 := by
    simpa [eval_mul, eval_sub] using hx
  have h20 : (20 : ℝ) ≠ 0 := by norm_num
  have hrest : (x - 1 / 2) * (x - 1) * (x - sigma1) * (x - sigma2) = 0 := by
    have : (20 : ℝ) * ((x - 1 / 2) * (x - 1) * (x - sigma1) * (x - sigma2)) = 0 := by
      convert hx20 using 1; ring
    exact (mul_eq_zero.mp this).resolve_left h20
  rcases mul_eq_zero.mp hrest with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
  · exact Or.inr (Or.inr (Or.inr (by linarith)))

lemma sigma_sub_lt_neg_one {j : ℕ} (hj : 1 ≤ j) {s : ℝ}
    (hs : s < 0) : s - (j : ℝ) < -1 := by
  have : (1 : ℝ) ≤ j := by exact_mod_cast hj
  linarith

lemma alpha_neg_coprime_P1_shift (j : ℕ) (hj : 1 ≤ j) :
    IsCoprime (alphaP.comp (-X)) (P1.comp (-X - C (j : ℝ))) := by
  refine isCoprime_of_splits_no_common_root alphaP_comp_neg_splits
    alphaP_comp_neg_ne_zero ?_
  intro x hx hxj
  have hx' := alphaP_comp_neg_roots hx
  have hxj' := P1_shift_roots hxj
  have hlt : x < -1 := by
    rcases hxj' with h | h <;> rw [h]
    · exact sigma_sub_lt_neg_one hj sigma1_mem.2
    · exact sigma_sub_lt_neg_one hj sigma2_mem.2
  rcases hx' with h | h | h | h <;> { rw [h] at hlt; linarith [sigma1_mem.1, sigma2_mem.1] }

lemma alpha_neg_coprime_peel (m : ℕ) :
    IsCoprime (alphaP.comp (-X)) (peelP1 m) := by
  refine IsCoprime.prod_right ?_
  intro j hj
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  exact alpha_neg_coprime_P1_shift j hj1

lemma knownFactor_dvd_fSP (m : ℕ) : knownFactor m ∣ fSP m := by
  simpa [knownFactor] using
    (alpha_neg_coprime_peel m).mul_dvd (fSP_dvd_alpha_neg m) (peelP1_dvd_fSP m)

/-- Quotient `fSP m / knownFactor m`. -/
noncomputable def Gpoly (m : ℕ) : Polynomial ℝ :=
  fSP m / knownFactor m

lemma Gpoly_mul (m : ℕ) : knownFactor m * Gpoly m = fSP m := by
  rw [Gpoly]
  exact EuclideanDomain.mul_div_cancel' (knownFactor_ne_zero m) (knownFactor_dvd_fSP m)

/-- The polynomial `P` of the conjecture, for `m ≥ 2`. -/
noncomputable def Ppoly (m : ℕ) : Polynomial ℝ :=
  (Gpoly m).comp (C (m : ℝ) * (X - 1))

/-- Even extraction: if `p.comp (-X) = p` then `p = (evenExtract p).comp (X^2)`. -/
noncomputable def evenExtract (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (p.natDegree / 2 + 1), C (p.coeff (2 * i)) * X ^ i

/-- The polynomial `Q` of the conjecture, for `m ≥ 2`. -/
noncomputable def Qpoly (m : ℕ) : Polynomial ℝ :=
  evenExtract ((Gpoly (2 * m)).comp (C (m : ℝ) * (X - 1)))

lemma P1_natDegree : P1.natDegree = 2 := by
  have h := P1_degree
  rwa [degree_eq_iff_natDegree_eq_of_pos (by norm_num : (0 : ℕ) < 2)] at h

lemma P1_leading : P1.leadingCoeff = 5 := by
  have hcoeff : P1.coeff 2 = 5 := by
    unfold P1
    rw [coeff_add, coeff_sub, coeff_C_mul, coeff_C_mul, coeff_C, coeff_X_pow, coeff_X]
    simp
  rw [leadingCoeff, P1_natDegree, hcoeff]

lemma lin_leading (a b : ℝ) (ha : a ≠ 0) :
    (C a * X + C b).leadingCoeff = a := by
  have hdeg : (C a * X + C b).natDegree = 1 := by
    have hX : (C a * X).natDegree = 1 := by
      rw [show C a * X = C a * X ^ 1 by simp, natDegree_C_mul ha, natDegree_X_pow]
    have hC : (C b).natDegree < 1 := by simp [natDegree_C]
    exact (natDegree_add_eq_left_of_natDegree_lt (hC.trans_eq hX.symm)).trans hX
  rw [leadingCoeff, hdeg, coeff_add, coeff_C_mul, coeff_X, coeff_C]
  simp

lemma alphaP_degree : alphaP.degree = (4 : ℕ) := by
  unfold alphaP P1; compute_degree!

lemma alphaP_natDegree : alphaP.natDegree = 4 := by
  have h := alphaP_degree
  rwa [degree_eq_iff_natDegree_eq_of_pos (by norm_num : (0 : ℕ) < 4)] at h

lemma alphaP_ne_zero : alphaP ≠ 0 := by
  intro h
  have := alphaP_natDegree
  simp [h] at this

lemma alphaP_leading : alphaP.leadingCoeff = 20 := by
  unfold alphaP
  rw [leadingCoeff_mul, leadingCoeff_mul, P1_leading,
    lin_leading 2 1 (by norm_num), lin_leading 2 2 (by norm_num)]
  norm_num

lemma betaP_degree : betaP.degree = (4 : ℕ) := by
  unfold betaP; compute_degree!

lemma betaP_natDegree : betaP.natDegree = 4 := by
  have h := betaP_degree
  rwa [degree_eq_iff_natDegree_eq_of_pos (by norm_num : (0 : ℕ) < 4)] at h

lemma betaP_ne_zero : betaP ≠ 0 := by
  intro h
  have := betaP_natDegree
  simp [h] at this

lemma betaP_leading : betaP.leadingCoeff = 220 := by
  rw [leadingCoeff, betaP_natDegree]
  unfold betaP
  simp [coeff_C_mul, coeff_sub, coeff_add, coeff_X_pow, coeff_C]
  norm_num

lemma shiftP_natDegree (p : Polynomial ℝ) (a : ℝ) :
    (shiftP p a).natDegree = p.natDegree := by
  rw [shiftP, natDegree_comp, natDegree_X_add_C, mul_one]

lemma shiftP_leading (p : Polynomial ℝ) (a : ℝ) :
    (shiftP p a).leadingCoeff = p.leadingCoeff := by
  by_cases hp : p = 0
  · simp [hp, shiftP]
  · have hq : (X + C a : Polynomial ℝ).natDegree ≠ 0 := by simp
    rw [shiftP, leadingCoeff_comp hq, leadingCoeff_X_add_C, one_pow, mul_one]

lemma shiftP_ne_zero {p : Polynomial ℝ} {a : ℝ} (hp : p ≠ 0) : shiftP p a ≠ 0 := by
  intro h
  apply hp
  apply Polynomial.funext
  intro x
  have := congrArg (fun q : Polynomial ℝ => q.eval (x - a)) h
  simpa [shiftP_eval, eval_zero] using this

lemma P1_shift_natDegree (j : ℕ) : (P1.comp (-X - C (j : ℝ))).natDegree = 2 := by
  have hlin : (-X - C (j : ℝ)).natDegree = 1 := by
    rw [show -X - C (j : ℝ) = -(X + C (j : ℝ)) by ring, natDegree_neg, natDegree_X_add_C]
  rw [natDegree_comp, P1_natDegree, hlin]

lemma peelP1_natDegree (m : ℕ) :
    (peelP1 m).natDegree = 2 * (m.pred.pred) := by
  unfold peelP1
  have hne : ∀ j ∈ Finset.Icc 1 m.pred.pred, P1.comp (-X - C (j : ℝ)) ≠ 0 :=
    fun j _ => P1_shift_ne_zero j
  rw [natDegree_prod _ _ hne]
  have : ∀ j ∈ Finset.Icc 1 m.pred.pred,
      (P1.comp (-X - C (j : ℝ))).natDegree = 2 :=
    fun j _ => P1_shift_natDegree j
  rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul, mul_comm]
  simp [Nat.card_Icc]

lemma alphaP_comp_neg_natDegree : (alphaP.comp (-X)).natDegree = 4 := by
  rw [natDegree_comp, alphaP_natDegree]
  simp

lemma alphaP_comp_neg_leading : (alphaP.comp (-X)).leadingCoeff = 20 := by
  have hq : (-X : Polynomial ℝ).natDegree ≠ 0 := by simp
  rw [leadingCoeff_comp hq, alphaP_leading, alphaP_natDegree]
  norm_num

lemma knownFactor_natDegree_of_two {m : ℕ} (hm : 2 ≤ m) :
    (knownFactor m).natDegree = 2 * m := by
  unfold knownFactor
  rw [natDegree_mul alphaP_comp_neg_ne_zero (peelP1_ne_zero m),
    alphaP_comp_neg_natDegree, peelP1_natDegree]
  have : m.pred.pred = m - 2 := by simp [Nat.pred_eq_sub_one, Nat.sub_sub]
  rw [this]
  omega

lemma fSP_natDegree_one : (fSP 1).natDegree = 4 := by
  rw [fSP_one, alphaP_comp_neg_natDegree]

lemma fSP_leading_one : (fSP 1).leadingCoeff = 20 := by
  rw [fSP_one, alphaP_comp_neg_leading]

lemma shiftP_betaP_ne_zero (a : ℝ) : shiftP betaP a ≠ 0 :=
  shiftP_ne_zero betaP_ne_zero

lemma fSP_ne_zero_one : fSP 1 ≠ 0 := by
  intro h
  have := congrArg natDegree h
  simp [fSP_natDegree_one] at this

lemma fSP_natDegree_two : (fSP 2).natDegree = 8 := by
  have h := fSP_succ_succ 0
  simp only [Nat.cast_zero, zero_add] at h
  have heq : fSP 2 = shiftP betaP 1 * fSP 1 := by
    simpa [fSP_zero, mul_zero, add_zero] using h
  rw [heq, natDegree_mul (shiftP_betaP_ne_zero 1) fSP_ne_zero_one,
    shiftP_natDegree, betaP_natDegree, fSP_natDegree_one]

lemma fSP_leading_two : (fSP 2).leadingCoeff = 4400 := by
  have h := fSP_succ_succ 0
  simp only [Nat.cast_zero, zero_add] at h
  have heq : fSP 2 = shiftP betaP 1 * fSP 1 := by
    simpa [fSP_zero, mul_zero, add_zero] using h
  rw [heq, leadingCoeff_mul, shiftP_leading, betaP_leading, fSP_leading_one]
  norm_num

lemma fSP_ne_zero_of_natDegree {m : ℕ} (h : (fSP m).natDegree ≠ 0) : fSP m ≠ 0 := by
  intro hf
  simp [hf] at h

/-- Degree and leading coefficient of `fSP m` for `m ≥ 1`. -/
lemma fSP_natDegree_and_leading :
    ∀ m : ℕ, 1 ≤ m →
      (fSP m).natDegree = 4 * m ∧ 0 < (fSP m).leadingCoeff := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm
    match m with
    | 0 => omega
    | 1 => exact ⟨fSP_natDegree_one, by simp [fSP_leading_one]⟩
    | 2 => exact ⟨fSP_natDegree_two, by simp [fSP_leading_two]⟩
    | n + 3 =>
      have hn1 : 1 ≤ n + 2 := by omega
      have hn0 : 1 ≤ n + 1 := by omega
      have ih1 := ih (n + 2) (by omega) hn1
      have ih0 := ih (n + 1) (by omega) hn0
      have hrec := fSP_succ_succ (n + 1)
      have hβ : shiftP betaP ((n + 1 : ℕ) + 1 : ℝ) ≠ 0 := shiftP_betaP_ne_zero _
      have hf1 : fSP (n + 2) ≠ 0 := fSP_ne_zero_of_natDegree (by
        rw [ih1.1]; omega)
      have hf0 : fSP (n + 1) ≠ 0 := fSP_ne_zero_of_natDegree (by
        rw [ih0.1]; omega)
      have hαn : shiftP (alphaP.comp (-X)) ((n + 1 : ℕ) + 1 : ℝ) ≠ 0 :=
        shiftP_ne_zero alphaP_comp_neg_ne_zero
      have hα : shiftP alphaP ((n + 1 : ℕ) : ℝ) ≠ 0 :=
        shiftP_ne_zero alphaP_ne_zero
      set t1 := shiftP betaP ((n + 1 : ℕ) + 1 : ℝ) * fSP (n + 2)
      set t2 := shiftP (alphaP.comp (-X)) ((n + 1 : ℕ) + 1 : ℝ) *
          shiftP alphaP ((n + 1 : ℕ) : ℝ) * fSP (n + 1)
      have ht1d : t1.natDegree = 4 * (n + 3) := by
        unfold t1
        rw [natDegree_mul hβ hf1, shiftP_natDegree, betaP_natDegree, ih1.1]
        omega
      have ht2d : t2.natDegree = 4 * (n + 3) := by
        unfold t2
        have hmul1 : shiftP (alphaP.comp (-X)) ((n + 1 : ℕ) + 1 : ℝ) *
            shiftP alphaP ((n + 1 : ℕ) : ℝ) ≠ 0 := mul_ne_zero hαn hα
        rw [natDegree_mul hmul1 hf0, natDegree_mul hαn hα, shiftP_natDegree,
          shiftP_natDegree, alphaP_comp_neg_natDegree, alphaP_natDegree, ih0.1]
        omega
      have ht1lc : t1.leadingCoeff = 220 * (fSP (n + 2)).leadingCoeff := by
        unfold t1
        rw [leadingCoeff_mul, shiftP_leading, betaP_leading]
      have ht2lc : t2.leadingCoeff = 400 * (fSP (n + 1)).leadingCoeff := by
        unfold t2
        rw [leadingCoeff_mul, leadingCoeff_mul, shiftP_leading, shiftP_leading,
          alphaP_comp_neg_leading, alphaP_leading]
        ring
      have hsum : t1.leadingCoeff + t2.leadingCoeff ≠ 0 := by
        rw [ht1lc, ht2lc]
        nlinarith [ih1.2, ih0.2]
      have hdeq : t1.degree = t2.degree := by
        have h1 : t1 ≠ 0 := mul_ne_zero hβ hf1
        have h2 : t2 ≠ 0 := mul_ne_zero (mul_ne_zero hαn hα) hf0
        rw [degree_eq_natDegree h1, degree_eq_natDegree h2, ht1d, ht2d]
      have hfsp : fSP (n + 3) = t1 + t2 := by
        simpa [t1, t2] using hrec
      have hdeg : (fSP (n + 3)).natDegree = 4 * (n + 3) := by
        have h1 : t1 ≠ 0 := mul_ne_zero hβ hf1
        have hdeg_eq : (t1 + t2).degree = t1.degree := by
          rw [degree_add_eq_of_leadingCoeff_add_ne_zero hsum, hdeq, max_self]
        rw [hfsp, natDegree_eq_of_degree_eq_some
          (hdeg_eq.trans (degree_eq_natDegree h1)), ht1d]
      have hlcpos : 0 < (fSP (n + 3)).leadingCoeff := by
        rw [hfsp, leadingCoeff_add_of_degree_eq hdeq hsum, ht1lc, ht2lc]
        nlinarith [ih1.2, ih0.2]
      exact ⟨hdeg, hlcpos⟩

lemma fSP_natDegree_of_one {m : ℕ} (hm : 1 ≤ m) : (fSP m).natDegree = 4 * m :=
  (fSP_natDegree_and_leading m hm).1

lemma fSP_leading_pos {m : ℕ} (hm : 1 ≤ m) : 0 < (fSP m).leadingCoeff :=
  (fSP_natDegree_and_leading m hm).2

lemma fSP_ne_zero_of_one {m : ℕ} (hm : 1 ≤ m) : fSP m ≠ 0 :=
  fSP_ne_zero_of_natDegree (by rw [fSP_natDegree_of_one hm]; omega)

lemma Gpoly_natDegree_of_two {m : ℕ} (hm : 2 ≤ m) :
    (Gpoly m).natDegree = 2 * m := by
  have hmul := congrArg natDegree (Gpoly_mul m)
  have hKF := knownFactor_ne_zero m
  have hG : Gpoly m ≠ 0 := by
    intro h
    have := Gpoly_mul m
    simp [h] at this
    exact fSP_ne_zero_of_one (by omega : 1 ≤ m) this.symm
  rw [natDegree_mul hKF hG, knownFactor_natDegree_of_two hm,
    fSP_natDegree_of_one (by omega : 1 ≤ m)] at hmul
  omega

lemma Gpoly_ne_zero_of_two {m : ℕ} (hm : 2 ≤ m) : Gpoly m ≠ 0 := by
  intro h
  have := Gpoly_natDegree_of_two hm
  simp [h] at this
  omega

lemma Gpoly_degree_of_two {m : ℕ} (hm : 2 ≤ m) :
    (Gpoly m).degree = (2 * m : ℕ) := by
  rw [degree_eq_natDegree (Gpoly_ne_zero_of_two hm), Gpoly_natDegree_of_two hm]

lemma P1_shift_leading (j : ℕ) : (P1.comp (-X - C (j : ℝ))).leadingCoeff = 5 := by
  have hq : (-X - C (j : ℝ)).natDegree ≠ 0 := by
    have : (-X - C (j : ℝ)).natDegree = 1 := by
      rw [show -X - C (j : ℝ) = -(X + C (j : ℝ)) by ring,
        natDegree_neg, natDegree_X_add_C]
    omega
  rw [leadingCoeff_comp hq, P1_leading]
  have : (-X - C (j : ℝ)).leadingCoeff = -1 := by
    rw [show -X - C (j : ℝ) = -(X + C (j : ℝ)) by ring, leadingCoeff_neg,
      leadingCoeff_X_add_C]
  rw [this, P1_natDegree]
  norm_num

lemma leadingCoeff_prod_pos {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ)
    (h : ∀ i ∈ s, 0 < (f i).leadingCoeff) :
    0 < (s.prod f).leadingCoeff := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, leadingCoeff_mul]
    exact mul_pos (h a (mem_insert_self _ _))
      (ih fun i hi => h i (mem_insert_of_mem hi))

lemma peelP1_leading_pos (m : ℕ) : 0 < (peelP1 m).leadingCoeff := by
  unfold peelP1
  refine leadingCoeff_prod_pos _ _ ?_
  intro j hj
  rw [P1_shift_leading]
  norm_num

lemma knownFactor_leading_pos (m : ℕ) : 0 < (knownFactor m).leadingCoeff := by
  unfold knownFactor
  rw [leadingCoeff_mul, alphaP_comp_neg_leading]
  nlinarith [peelP1_leading_pos m]

lemma Gpoly_leading_pos {m : ℕ} (hm : 2 ≤ m) : 0 < (Gpoly m).leadingCoeff := by
  have hmul := congrArg leadingCoeff (Gpoly_mul m)
  rw [leadingCoeff_mul] at hmul
  have hf : 0 < (fSP m).leadingCoeff := fSP_leading_pos (by omega)
  have hKF : 0 < (knownFactor m).leadingCoeff := knownFactor_leading_pos m
  nlinarith

/-! ### Sign lemmas at half-integers -/

lemma P1_eval_half (k : ℤ) :
    P1.eval ((k : ℝ) / 2) = (5 * (k : ℝ) ^ 2 - 10 * k + 4) / 4 := by
  rw [P1_eval]
  ring

lemma P1_eval_half_form (k : ℤ) :
    5 * (k : ℝ) ^ 2 - 10 * k + 4 = 5 * ((k : ℝ) - 1) ^ 2 - 1 := by
  ring

lemma P1_eval_half_neg : P1.eval ((1 : ℝ) / 2) < 0 := by
  rw [P1_eval]; norm_num

noncomputable def halfZ (k : ℤ) : ℝ := (k : ℝ) / 2

lemma halfZ_nat (j : ℕ) : halfZ j = (j : ℝ) / 2 := by simp [halfZ]

lemma halfZ_neg_nat (j : ℕ) : -((j : ℝ) / 2) = halfZ (-(j : ℤ)) := by
  simp [halfZ]; ring

lemma P1_eval_half_pos {k : ℤ} (hk : k ≠ 1) : 0 < P1.eval (halfZ k) := by
  rw [halfZ, P1_eval_half, div_pos_iff]
  refine Or.inl ⟨?_, by norm_num⟩
  rw [P1_eval_half_form]
  have hne : (k : ℝ) ≠ 1 := by exact_mod_cast hk
  have habs : (1 : ℝ) ≤ |(k : ℝ) - 1| := by
    have : (1 : ℤ) ≤ |k - 1| := Int.one_le_abs (sub_ne_zero.mpr hk)
    exact_mod_cast this
  nlinarith [sq_abs ((k : ℝ) - 1), sq_nonneg ((k : ℝ) - 1)]

lemma alpha1_eq_lin_P1 (x : ℝ) :
    alpha1 x = (2 * x + 1) * (2 * x + 2) * P1.eval x := by
  unfold alpha1; rw [P1_eval]

lemma alpha1_half (k : ℤ) :
    alpha1 (halfZ k) = ((k : ℝ) + 1) * ((k : ℝ) + 2) * P1.eval (halfZ k) := by
  rw [alpha1_eq_lin_P1, halfZ]; ring

lemma alpha1_half_zero_neg1 : alpha1 (halfZ (-1)) = 0 := by
  rw [alpha1_half, halfZ]; norm_num

lemma alpha1_half_zero_neg2 : alpha1 (halfZ (-2)) = 0 := by
  rw [alpha1_half, halfZ]; norm_num

lemma alpha1_half_neg : alpha1 (halfZ 1) < 0 := by
  rw [alpha1_half, halfZ]; norm_num [P1_eval]

lemma alpha1_half_pos {k : ℤ} (h1 : k ≠ 1) (h2 : k ≠ -1) (h3 : k ≠ -2) :
    0 < alpha1 (halfZ k) := by
  rw [alpha1_half]
  have hp : 0 < P1.eval (halfZ k) := P1_eval_half_pos h1
  have hlin : 0 < ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
    rcases le_or_gt (0 : ℤ) k with hk | hk
    · have hk0 : (0 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    · have hk' : k ≤ -3 := by omega
      have hkR : (k : ℝ) ≤ -3 := by exact_mod_cast hk'
      nlinarith
  nlinarith

lemma alpha1_half_neg_iff (k : ℤ) : alpha1 (halfZ k) < 0 ↔ k = 1 := by
  constructor
  · intro h
    by_contra hk
    by_cases h2 : k = -1
    · subst h2; have := alpha1_half_zero_neg1; linarith
    · by_cases h3 : k = -2
      · subst h3; have := alpha1_half_zero_neg2; linarith
      · have := alpha1_half_pos hk h2 h3; linarith
  · intro h; subst h; exact alpha1_half_neg

lemma alpha1_half_eq_zero_iff (k : ℤ) :
    alpha1 (halfZ k) = 0 ↔ k = -1 ∨ k = -2 := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    by_cases h1 : k = 1
    · subst h1; have := alpha1_half_neg; linarith
    · have := alpha1_half_pos h1 hne.1 hne.2; linarith
  · intro h
    rcases h with h | h
    · subst h; exact alpha1_half_zero_neg1
    · subst h; exact alpha1_half_zero_neg2

lemma alpha1_half_pos_of_nat {j : ℕ} (hj : j ≠ 1) : 0 < alpha1 (halfZ j) := by
  have h1 : (j : ℤ) ≠ 1 := by exact_mod_cast hj
  have h2 : (j : ℤ) ≠ -1 := by
    intro h; have : (0 : ℤ) ≤ j := Int.natCast_nonneg _; omega
  have h3 : (j : ℤ) ≠ -2 := by
    intro h; have : (0 : ℤ) ≤ j := Int.natCast_nonneg _; omega
  exact alpha1_half_pos h1 h2 h3

lemma beta1_half_neg_one : beta1 (halfZ 1) < 0 := by
  unfold beta1 halfZ; norm_num

lemma beta1_half_neg_negone : beta1 (halfZ (-1)) < 0 := by
  unfold beta1 halfZ; norm_num

lemma beta1_half_pos {k : ℤ} (h1 : k ≠ 1) (h2 : k ≠ -1) :
    0 < beta1 (halfZ k) := by
  unfold beta1 halfZ
  have hform : 55 * ((k : ℝ) / 2) ^ 4 - 34 * ((k : ℝ) / 2) ^ 2 + 3 =
      (55 * (k : ℝ) ^ 4 - 136 * (k : ℝ) ^ 2 + 48) / 16 := by
    ring
  have hpos : 0 < 55 * ((k : ℝ) / 2) ^ 4 - 34 * ((k : ℝ) / 2) ^ 2 + 3 := by
    rw [hform, div_pos_iff]
    refine Or.inl ⟨?_, by norm_num⟩
    by_cases hk0 : k = 0
    · subst hk0; norm_num
    · have : k ≤ -2 ∨ 2 ≤ k := by omega
      have hk2 : (2 : ℤ) ≤ |k| := by
        rcases this with h | h
        · rw [abs_of_nonpos (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; exact h
      have hu : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by
        have : (4 : ℤ) ≤ k ^ 2 := by
          have hsq : (2 : ℤ) ^ 2 ≤ |k| ^ 2 :=
            pow_le_pow_left₀ (by norm_num) hk2 2
          simpa [sq_abs] using hsq
        exact_mod_cast this
      set u := (k : ℝ) ^ 2
      have hu4 : (4 : ℝ) ≤ u := hu
      nlinarith
  nlinarith

lemma beta1_half_neg_iff (k : ℤ) : beta1 (halfZ k) < 0 ↔ k = 1 ∨ k = -1 := by
  constructor
  · intro h
    by_contra hk
    push_neg at hk
    have := beta1_half_pos hk.1 hk.2
    linarith
  · intro h
    rcases h with h | h
    · subst h; exact beta1_half_neg_one
    · subst h; exact beta1_half_neg_negone

lemma beta1_half_ne_zero (k : ℤ) : beta1 (halfZ k) ≠ 0 := by
  by_cases h1 : k = 1
  · subst h1; exact (ne_of_lt beta1_half_neg_one)
  · by_cases h2 : k = -1
    · subst h2; exact (ne_of_lt beta1_half_neg_negone)
    · exact (beta1_half_pos h1 h2).ne'

lemma fSP_one_eval_half (j : ℕ) :
    (fSP 1).eval (-(j : ℝ) / 2) = alpha1 (halfZ (j : ℤ)) := by
  rw [fSP_one, alphaP_comp_neg_eval, halfZ]
  congr 1
  push_cast
  ring

lemma fSP_two_eq : fSP 2 = shiftP betaP 1 * fSP 1 := by
  have h := fSP_succ_succ 0
  simp only [Nat.cast_zero, zero_add] at h
  simpa [fSP_zero, mul_zero, add_zero] using h

lemma fSP_two_eval_half (j : ℕ) :
    (fSP 2).eval (-(j : ℝ) / 2) =
      beta1 (halfZ ((2 : ℤ) - (j : ℤ))) * alpha1 (halfZ (j : ℤ)) := by
  rw [fSP_two_eq, eval_mul, shiftP_eval, betaP_eval, fSP_one_eval_half]
  congr 1
  simp [halfZ]; ring

/-- Combined sign statement: `fSP m` is nonzero at `-j/2`, and is negative
iff `j + 1 = 2m`. -/
lemma pos_of_not_neg_ne {a : ℝ} (hne : a ≠ 0) (h : ¬ a < 0) : 0 < a :=
  lt_of_le_of_ne (not_lt.mp h) hne.symm

lemma add_ne_zero_of_same_sign {a b : ℝ}
    (h : (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0)) : a + b ≠ 0 := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> linarith

lemma fSP_eval_half_sign :
    ∀ m : ℕ, 1 ≤ m → ∀ j : ℕ,
      (fSP m).eval (-(j : ℝ) / 2) ≠ 0 ∧
        ((fSP m).eval (-(j : ℝ) / 2) < 0 ↔ j + 1 = 2 * m) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm j
    match m with
    | 0 => omega
    | 1 =>
      rw [fSP_one_eval_half]
      constructor
      · intro h
        have := (alpha1_half_eq_zero_iff (j : ℤ)).mp h
        rcases this with h | h
        · have : (j : ℤ) ≥ 0 := Int.natCast_nonneg _
          omega
        · have : (j : ℤ) ≥ 0 := Int.natCast_nonneg _
          omega
      · rw [alpha1_half_neg_iff]
        constructor <;> intro h
        · have : j = 1 := by exact_mod_cast h
          omega
        · have : j = 1 := by omega
          exact_mod_cast this
    | 2 =>
      rw [fSP_two_eval_half]
      constructor
      · intro h
        rcases mul_eq_zero.mp h with hβ | hα
        · exact beta1_half_ne_zero _ hβ
        · have := (alpha1_half_eq_zero_iff (j : ℤ)).mp hα
          rcases this with hj | hj
          · have : (j : ℤ) ≥ 0 := Int.natCast_nonneg _; omega
          · have : (j : ℤ) ≥ 0 := Int.natCast_nonneg _; omega
      · constructor
        · intro h
          have hαz : alpha1 (halfZ (j : ℤ)) ≠ 0 := by
            intro hz
            have := (alpha1_half_eq_zero_iff (j : ℤ)).mp hz
            rcases this with hj | hj
            · have : (j : ℤ) ≥ 0 := Int.natCast_nonneg _; omega
            · have : (j : ℤ) ≥ 0 := Int.natCast_nonneg _; omega
          by_cases hj1 : j = 1
          · subst hj1
            have heq : ((2 : ℤ) - (1 : ℤ)) = (1 : ℤ) := by norm_num
            simp [heq] at h
            exact (not_lt_of_gt (mul_pos_of_neg_of_neg beta1_half_neg_one
              alpha1_half_neg) h).elim
          · have hα : 0 < alpha1 (halfZ (j : ℤ)) := alpha1_half_pos_of_nat hj1
            have hβ : beta1 (halfZ ((2 : ℤ) - (j : ℤ))) < 0 := by nlinarith
            have hk := (beta1_half_neg_iff ((2 : ℤ) - (j : ℤ))).mp hβ
            rcases hk with hk | hk
            · have hjZ : (j : ℤ) = 1 := by linarith
              have : j = 1 := by exact_mod_cast hjZ
              exact (hj1 this).elim
            · have hjZ : (j : ℤ) = 3 := by linarith
              have : j = 3 := by exact_mod_cast hjZ
              omega
        · intro h
          have hj : j = 3 := by omega
          subst hj
          have heq : ((2 : ℤ) - (3 : ℤ)) = (-1 : ℤ) := by norm_num
          simp [heq]
          exact mul_neg_of_neg_of_pos beta1_half_neg_negone
            (alpha1_half_pos_of_nat (by decide : (3 : ℕ) ≠ 1))
    | n + 3 =>
      have hn1 : 1 ≤ n + 2 := by omega
      have hn0 : 1 ≤ n + 1 := by omega
      have ih1 := ih (n + 2) (by omega) hn1 j
      have ih0 := ih (n + 1) (by omega) hn0 j
      have heval := fSP_eval_succ_succ (n + 1) (-(j : ℝ) / 2)
      have hAeq : beta1 (-(j : ℝ) / 2 + (n + 1 : ℕ) + 1) =
          beta1 (halfZ ((2 : ℤ) * ((n : ℤ) + 2) - (j : ℤ))) := by
        unfold halfZ; push_cast; ring
      have hBeq : alpha1 (-(-(j : ℝ) / 2 + (n + 1 : ℕ) + 1)) =
          alpha1 (halfZ ((j : ℤ) - (2 : ℤ) * ((n : ℤ) + 2))) := by
        unfold halfZ; push_cast; ring
      have hCeq : alpha1 (-(j : ℝ) / 2 + (n + 1 : ℕ)) =
          alpha1 (halfZ ((2 : ℤ) * ((n : ℤ) + 1) - (j : ℤ))) := by
        unfold halfZ; push_cast; ring
      set A := beta1 (halfZ ((2 : ℤ) * ((n : ℤ) + 2) - (j : ℤ)))
      set B := alpha1 (halfZ ((j : ℤ) - (2 : ℤ) * ((n : ℤ) + 2)))
      set C := alpha1 (halfZ ((2 : ℤ) * ((n : ℤ) + 1) - (j : ℤ)))
      set F1 := (fSP (n + 2)).eval (-(j : ℝ) / 2)
      set F0 := (fSP (n + 1)).eval (-(j : ℝ) / 2)
      have hsum : (fSP (n + 3)).eval (-(j : ℝ) / 2) = A * F1 + B * C * F0 := by
        rw [heval, hAeq, hBeq, hCeq]
      have hAne : A ≠ 0 := beta1_half_ne_zero _
      have hF1ne : F1 ≠ 0 := ih1.1
      have hF0ne : F0 ≠ 0 := ih0.1
      have ht1ne : A * F1 ≠ 0 := mul_ne_zero hAne hF1ne
      -- Integer forms of the induction hypotheses
      have hF1lt : F1 < 0 ↔ (j : ℤ) + 1 = 2 * ((n : ℤ) + 2) := by
        rw [ih1.2]; constructor <;> intro h <;> exact_mod_cast h
      have hF0lt : F0 < 0 ↔ (j : ℤ) + 1 = 2 * ((n : ℤ) + 1) := by
        rw [ih0.2]; constructor <;> intro h <;> exact_mod_cast h
      have hAlt : A < 0 ↔
          (2 : ℤ) * ((n : ℤ) + 2) - (j : ℤ) = 1 ∨
          (2 : ℤ) * ((n : ℤ) + 2) - (j : ℤ) = -1 := by
        simpa [A] using beta1_half_neg_iff ((2 : ℤ) * ((n : ℤ) + 2) - (j : ℤ))
      have hBlt : B < 0 ↔ (j : ℤ) - (2 : ℤ) * ((n : ℤ) + 2) = 1 := by
        simpa [B] using alpha1_half_neg_iff ((j : ℤ) - (2 : ℤ) * ((n : ℤ) + 2))
      have hClt : C < 0 ↔ (2 : ℤ) * ((n : ℤ) + 1) - (j : ℤ) = 1 := by
        simpa [C] using alpha1_half_neg_iff ((2 : ℤ) * ((n : ℤ) + 1) - (j : ℤ))
      have hB0iff : B = 0 ↔
          (j : ℤ) - (2 : ℤ) * ((n : ℤ) + 2) = -1 ∨
          (j : ℤ) - (2 : ℤ) * ((n : ℤ) + 2) = -2 := by
        simpa [B] using alpha1_half_eq_zero_iff ((j : ℤ) - (2 : ℤ) * ((n : ℤ) + 2))
      have hC0iff : C = 0 ↔
          (2 : ℤ) * ((n : ℤ) + 1) - (j : ℤ) = -1 ∨
          (2 : ℤ) * ((n : ℤ) + 1) - (j : ℤ) = -2 := by
        simpa [C] using alpha1_half_eq_zero_iff ((2 : ℤ) * ((n : ℤ) + 1) - (j : ℤ))
      -- term1 is negative iff we are at the target index
      have ht1lt : A * F1 < 0 ↔ (j : ℤ) + 1 = 2 * ((n : ℤ) + 3) := by
        constructor
        · intro hmul
          have hcases : 0 < A ∧ F1 < 0 ∨ A < 0 ∧ 0 < F1 := mul_neg_iff.mp hmul
          rcases hcases with ⟨hA, hF⟩ | ⟨hA, hF⟩
          · have : (j : ℤ) + 1 = 2 * ((n : ℤ) + 2) := hF1lt.mp hF
            have : (2 : ℤ) * ((n : ℤ) + 2) - (j : ℤ) = 1 := by omega
            have : A < 0 := hAlt.mpr (Or.inl this)
            linarith
          · have hA' := hAlt.mp hA
            rcases hA' with h1 | hm1
            · have : (j : ℤ) + 1 = 2 * ((n : ℤ) + 2) := by omega
              have : F1 < 0 := hF1lt.mpr this
              linarith
            · omega
        · intro hj
          -- j+1 = 2(n+3) ⇒ 2(n+2)-j = -1 ⇒ A<0, and F1>0
          have : (2 : ℤ) * ((n : ℤ) + 2) - (j : ℤ) = -1 := by omega
          have hA : A < 0 := hAlt.mpr (Or.inr this)
          have hne : (j : ℤ) + 1 ≠ 2 * ((n : ℤ) + 2) := by omega
          have hF : 0 < F1 := by
            have : ¬ F1 < 0 := fun h => hne (hF1lt.mp h)
            exact pos_of_not_neg_ne hF1ne this
          exact mul_neg_of_neg_of_pos hA hF
      -- Main claims
      constructor
      · -- nonzero
        intro hz
        rw [hsum] at hz
        by_cases hBz : B = 0
        · simp only [hBz, zero_mul, add_zero] at hz; exact ht1ne hz
        · by_cases hCz : C = 0
          · simp only [hCz, mul_zero, zero_mul, add_zero] at hz; exact ht1ne hz
          · -- both terms nonzero and same sign
            have ht2ne : B * C * F0 ≠ 0 :=
              mul_ne_zero (mul_ne_zero hBz hCz) hF0ne
            have hsame : (0 < A * F1 ∧ 0 < B * C * F0) ∨
                (A * F1 < 0 ∧ B * C * F0 < 0) := by
              by_cases hj : (j : ℤ) + 1 = 2 * ((n : ℤ) + 3)
              · -- both negative
                have ht1 : A * F1 < 0 := ht1lt.mpr hj
                have hB : B < 0 := by
                  have : (j : ℤ) - (2 : ℤ) * ((n : ℤ) + 2) = 1 := by omega
                  exact hBlt.mpr this
                have hCpos : 0 < C := by
                  have hne1 : (2 : ℤ) * ((n : ℤ) + 1) - (j : ℤ) ≠ 1 := by omega
                  have hne0 : C ≠ 0 := hCz
                  have : ¬ C < 0 := fun h => hne1 (hClt.mp h)
                  exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hne0)
                have hF0pos : 0 < F0 := by
                  have hne : (j : ℤ) + 1 ≠ 2 * ((n : ℤ) + 1) := by omega
                  have : ¬ F0 < 0 := fun h => hne (hF0lt.mp h)
                  exact lt_of_le_of_ne (not_lt.mp this) hF0ne.symm
                have ht2 : B * C * F0 < 0 :=
                  mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hB hCpos) hF0pos
                right
                exact ⟨ht1, ht2⟩
              · -- both positive
                have ht1 : 0 < A * F1 := by
                  have : ¬ A * F1 < 0 := fun h => hj (ht1lt.mp h)
                  exact lt_of_le_of_ne (not_lt.mp this) ht1ne.symm
                have hBpos : 0 < B := by
                  have hne : (j : ℤ) - (2 : ℤ) * ((n : ℤ) + 2) ≠ 1 := by omega
                  have : ¬ B < 0 := fun h => hne (hBlt.mp h)
                  exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hBz)
                have hCF : 0 < C * F0 := by
                  by_cases hCneg : C < 0
                  · have : (2 : ℤ) * ((n : ℤ) + 1) - (j : ℤ) = 1 := hClt.mp hCneg
                    have : (j : ℤ) + 1 = 2 * ((n : ℤ) + 1) := by omega
                    have hF0neg : F0 < 0 := hF0lt.mpr this
                    exact mul_pos_of_neg_of_neg hCneg hF0neg
                  · have hCpos : 0 < C :=
                      pos_of_not_neg_ne hCz hCneg
                    have hF0pos : 0 < F0 := by
                      have : ¬ F0 < 0 := fun h => by
                        have : (j : ℤ) + 1 = 2 * ((n : ℤ) + 1) := hF0lt.mp h
                        have : (2 : ℤ) * ((n : ℤ) + 1) - (j : ℤ) = 1 := by omega
                        exact hCneg (hClt.mpr this)
                      exact pos_of_not_neg_ne hF0ne this
                    exact mul_pos hCpos hF0pos
                left
                exact ⟨ht1, by simpa [mul_assoc] using (mul_pos hBpos hCF)⟩
            exact add_ne_zero_of_same_sign hsame hz
      · constructor
        · intro hneg
          rw [hsum] at hneg
          by_contra hjN
          have hj : (j : ℤ) + 1 ≠ 2 * ((n : ℤ) + 3) := by exact_mod_cast hjN
          have ht1 : 0 < A * F1 := by
            have : ¬ A * F1 < 0 := fun h => hj (ht1lt.mp h)
            exact lt_of_le_of_ne (not_lt.mp this) ht1ne.symm
          have ht2 : 0 ≤ B * C * F0 := by
            by_cases hBz : B = 0
            · simp [hBz]
            · by_cases hCz : C = 0
              · simp [hCz]
              · have hBpos : 0 < B := by
                  have hne : (j : ℤ) - (2 : ℤ) * ((n : ℤ) + 2) ≠ 1 := by omega
                  have : ¬ B < 0 := fun h => hne (hBlt.mp h)
                  exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hBz)
                have hCF : 0 < C * F0 := by
                  by_cases hCneg : C < 0
                  · have : (2 : ℤ) * ((n : ℤ) + 1) - (j : ℤ) = 1 := hClt.mp hCneg
                    have : (j : ℤ) + 1 = 2 * ((n : ℤ) + 1) := by omega
                    have hF0neg : F0 < 0 := hF0lt.mpr this
                    exact mul_pos_of_neg_of_neg hCneg hF0neg
                  · have hCpos : 0 < C :=
                      pos_of_not_neg_ne hCz hCneg
                    have hF0pos : 0 < F0 := by
                      have : ¬ F0 < 0 := fun h => by
                        have : (j : ℤ) + 1 = 2 * ((n : ℤ) + 1) := hF0lt.mp h
                        have : (2 : ℤ) * ((n : ℤ) + 1) - (j : ℤ) = 1 := by omega
                        exact hCneg (hClt.mpr this)
                      exact pos_of_not_neg_ne hF0ne this
                    exact mul_pos hCpos hF0pos
                exact le_of_lt (by simpa [mul_assoc] using (mul_pos hBpos hCF))
          linarith
        · intro hjN
          have hj : (j : ℤ) + 1 = 2 * ((n : ℤ) + 3) := by exact_mod_cast hjN
          rw [hsum]
          have ht1 : A * F1 < 0 := ht1lt.mpr hj
          have ht2 : B * C * F0 ≤ 0 := by
            have hB : B < 0 := by
              have : (j : ℤ) - (2 : ℤ) * ((n : ℤ) + 2) = 1 := by omega
              exact hBlt.mpr this
            by_cases hCz : C = 0
            · simp [hCz]
            · have hCpos : 0 < C := by
                have hne : (2 : ℤ) * ((n : ℤ) + 1) - (j : ℤ) ≠ 1 := by omega
                have : ¬ C < 0 := fun h => hne (hClt.mp h)
                exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hCz)
              have hF0pos : 0 < F0 := by
                have hne : (j : ℤ) + 1 ≠ 2 * ((n : ℤ) + 1) := by omega
                have : ¬ F0 < 0 := fun h => hne (hF0lt.mp h)
                exact lt_of_le_of_ne (not_lt.mp this) hF0ne.symm
              exact le_of_lt
                (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hB hCpos) hF0pos)
          linarith

lemma fSP_eval_half_neg_iff {m j : ℕ} (hm : 1 ≤ m) :
    (fSP m).eval (-(j : ℝ) / 2) < 0 ↔ j + 1 = 2 * m :=
  (fSP_eval_half_sign m hm j).2

lemma fSP_eval_half_ne_zero {m j : ℕ} (hm : 1 ≤ m) :
    (fSP m).eval (-(j : ℝ) / 2) ≠ 0 :=
  (fSP_eval_half_sign m hm j).1

lemma fSP_eval_half_pos {m j : ℕ} (hm : 1 ≤ m) (hj : j + 1 ≠ 2 * m) :
    0 < (fSP m).eval (-(j : ℝ) / 2) := by
  have hne := fSP_eval_half_ne_zero (m := m) (j := j) hm
  have hiff := fSP_eval_half_neg_iff (m := m) (j := j) hm
  have : ¬ (fSP m).eval (-(j : ℝ) / 2) < 0 := fun h => hj (hiff.mp h)
  exact lt_of_le_of_ne (le_of_not_gt this) hne.symm

lemma P1_eval_halfZ_neg_iff (k : ℤ) : P1.eval (halfZ k) < 0 ↔ k = 1 := by
  constructor
  · intro h
    by_contra hk
    have := P1_eval_half_pos hk
    linarith
  · intro h; subst h
    simpa [halfZ] using P1_eval_half_neg

lemma P1_eval_halfZ_ne_zero (k : ℤ) : P1.eval (halfZ k) ≠ 0 := by
  by_cases h : k = 1
  · subst h; exact (ne_of_lt (by simpa [halfZ] using P1_eval_half_neg))
  · exact (P1_eval_half_pos h).ne'

lemma knownFactor_eval (m : ℕ) (x : ℝ) :
    (knownFactor m).eval x =
      alpha1 (-x) * ((Finset.Icc 1 m.pred.pred).prod fun j => P1.eval (-x - (j : ℝ))) := by
  unfold knownFactor peelP1
  rw [eval_mul, alphaP_comp_neg_eval, eval_prod]
  simp [eval_comp, eval_add, eval_sub, eval_neg, eval_X, eval_C]

lemma knownFactor_eval_half (m j : ℕ) :
    (knownFactor m).eval (-(j : ℝ) / 2) =
      alpha1 (halfZ (j : ℤ)) *
        ((Finset.Icc 1 m.pred.pred).prod fun k => P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ)))) := by
  rw [knownFactor_eval]
  congr 1
  · unfold halfZ; push_cast; ring
  · refine Finset.prod_congr rfl ?_
    intro k hk
    unfold halfZ; push_cast; ring

lemma knownFactor_eval_half_ne_zero {m j : ℕ} :
    (knownFactor m).eval (-(j : ℝ) / 2) ≠ 0 := by
  rw [knownFactor_eval_half]
  refine mul_ne_zero ?_ ?_
  · intro h
    have h' := (alpha1_half_eq_zero_iff (j : ℤ)).mp h
    have hn : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg _
    rcases h' with h' | h' <;> omega
  · refine Finset.prod_ne_zero_iff.mpr ?_
    intro k hk
    exact P1_eval_halfZ_ne_zero _

lemma pred_pred_eq (m : ℕ) : m.pred.pred = m - 2 := by
  simp [Nat.pred_eq_sub_one, Nat.sub_sub]

lemma peel_factor_neg_iff (j k : ℕ) :
    P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ))) < 0 ↔ (j : ℤ) = 2 * (k : ℤ) + 1 := by
  rw [P1_eval_halfZ_neg_iff]
  constructor <;> intro h <;> omega

lemma exists_peel_neg {m j : ℕ} (hm : 2 ≤ m) :
    (∃ k ∈ Finset.Icc 1 (m - 2), P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ))) < 0) ↔
      Odd j ∧ 3 ≤ j ∧ j + 3 ≤ 2 * m := by
  constructor
  · intro ⟨k, hk, hneg⟩
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk2 : k ≤ m - 2 := (Finset.mem_Icc.mp hk).2
    have hjk : (j : ℤ) = 2 * (k : ℤ) + 1 := (peel_factor_neg_iff j k).mp hneg
    have hjN : j = 2 * k + 1 := by exact_mod_cast hjk
    refine ⟨?_, ?_, ?_⟩
    · rw [hjN]; exact odd_two_mul_add_one k
    · omega
    · omega
  · intro ⟨hodd, h3, hup⟩
    obtain ⟨t, rfl⟩ := hodd
    have ht1 : 1 ≤ t := by omega
    have ht2 : t ≤ m - 2 := by omega
    refine ⟨t, Finset.mem_Icc.mpr ⟨ht1, ht2⟩, ?_⟩
    exact (peel_factor_neg_iff (2 * t + 1) t).mpr (by push_cast; ring)

lemma peel_prod_neg_of_exists {m j : ℕ} (hm : 2 ≤ m)
    (hex : ∃ k ∈ Finset.Icc 1 (m - 2),
      P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ))) < 0) :
    ((Finset.Icc 1 (m - 2)).prod fun k =>
      P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ)))) < 0 := by
  obtain ⟨t, ht, hneg⟩ := hex
  have huniq : ∀ k ∈ Finset.Icc 1 (m - 2), k ≠ t →
      0 < P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ))) := by
    intro k hk hne
    have : (j : ℤ) ≠ 2 * (k : ℤ) + 1 := by
      intro heq
      have htj : (j : ℤ) = 2 * (t : ℤ) + 1 := (peel_factor_neg_iff j t).mp hneg
      have : (k : ℤ) = t := by omega
      have : k = t := by exact_mod_cast this
      exact hne this
    have hnn : ¬ P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ))) < 0 := fun h =>
      this ((peel_factor_neg_iff j k).mp h)
    exact lt_of_le_of_ne (le_of_not_gt hnn) (P1_eval_halfZ_ne_zero _).symm
  have hsplit := Finset.prod_eq_mul_prod_diff_singleton ht
    (fun k => P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ))))
  rw [hsplit]
  have hpos : 0 < ((Finset.Icc 1 (m - 2) \ {t}).prod
      fun k => P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ)))) :=
    Finset.prod_pos fun k hk => by
      have hk' : k ∈ Finset.Icc 1 (m - 2) := (Finset.mem_sdiff.mp hk).1
      have hne : k ≠ t := by
        intro hkt
        exact (Finset.mem_sdiff.mp hk).2 (hkt ▸ Finset.mem_singleton_self t)
      exact huniq k hk' hne
  exact mul_neg_of_neg_of_pos hneg hpos

lemma peel_prod_pos_of_not_exists {m j : ℕ} (hm : 2 ≤ m)
    (hnex : ¬ ∃ k ∈ Finset.Icc 1 (m - 2),
      P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ))) < 0) :
    0 < ((Finset.Icc 1 (m - 2)).prod fun k =>
      P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ)))) := by
  have hnn : ∀ k ∈ Finset.Icc 1 (m - 2),
      ¬ P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ))) < 0 := by
    intro k hk h; exact hnex ⟨k, hk, h⟩
  refine Finset.prod_pos ?_
  intro k hk
  exact lt_of_le_of_ne (le_of_not_gt (hnn k hk)) (P1_eval_halfZ_ne_zero _).symm

lemma knownFactor_eval_half_neg_iff {m j : ℕ} (hm : 2 ≤ m) :
    (knownFactor m).eval (-(j : ℝ) / 2) < 0 ↔ Odd j ∧ j + 3 ≤ 2 * m := by
  have hpred : m.pred.pred = m - 2 := pred_pred_eq m
  rw [knownFactor_eval_half, hpred]
  have hαneg : alpha1 (halfZ (j : ℤ)) < 0 ↔ j = 1 := by
    rw [alpha1_half_neg_iff]; constructor <;> intro h <;> exact_mod_cast h
  constructor
  · intro hmul
    have hcases : 0 < alpha1 (halfZ (j : ℤ)) ∧
        (Finset.Icc 1 (m - 2)).prod (fun k => P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ)))) < 0 ∨
        alpha1 (halfZ (j : ℤ)) < 0 ∧
        0 < (Finset.Icc 1 (m - 2)).prod (fun k => P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ)))) :=
      mul_neg_iff.mp hmul
    rcases hcases with ⟨hα, hpr⟩ | ⟨hα, hpr⟩
    · have hex : ∃ k ∈ Finset.Icc 1 (m - 2),
          P1.eval (halfZ ((j : ℤ) - 2 * (k : ℤ))) < 0 := by
        by_contra hnex
        have := peel_prod_pos_of_not_exists hm hnex
        linarith
      have := (exists_peel_neg hm).mp hex
      exact ⟨this.1, this.2.2⟩
    · have hj1 : j = 1 := hαneg.mp hα
      subst hj1
      exact ⟨odd_one, by omega⟩
  · intro ⟨hodd, hup⟩
    by_cases hj1 : j = 1
    · subst hj1
      have hα : alpha1 (halfZ (1 : ℤ)) < 0 := alpha1_half_neg
      have hnex : ¬ ∃ k ∈ Finset.Icc 1 (m - 2),
          P1.eval (halfZ ((1 : ℤ) - 2 * (k : ℤ))) < 0 := by
        intro hex
        have h3 : 3 ≤ (1 : ℕ) := ((exists_peel_neg hm).mp hex).2.1
        omega
      have hpr : 0 < (Finset.Icc 1 (m - 2)).prod
          fun k => P1.eval (halfZ ((1 : ℤ) - 2 * (k : ℤ))) :=
        peel_prod_pos_of_not_exists hm hnex
      exact mul_neg_of_neg_of_pos hα hpr
    · have hα : 0 < alpha1 (halfZ (j : ℤ)) := alpha1_half_pos_of_nat hj1
      have h3 : 3 ≤ j := by
        obtain ⟨t, ht⟩ := hodd
        have : t ≠ 0 := fun h => by subst h; subst ht; exact hj1 rfl
        omega
      have hex := (exists_peel_neg hm).mpr ⟨hodd, h3, hup⟩
      have hpr := peel_prod_neg_of_exists hm hex
      exact mul_neg_of_pos_of_neg hα hpr

lemma Gpoly_eval (m : ℕ) (x : ℝ) :
    (knownFactor m).eval x * (Gpoly m).eval x = (fSP m).eval x := by
  simpa using congrArg (fun p => p.eval x) (Gpoly_mul m)

lemma Gpoly_eval_half_neg_iff {m j : ℕ} (hm : 2 ≤ m) (hj : j ≤ 2 * m) :
    (Gpoly m).eval (-(j : ℝ) / 2) < 0 ↔ Odd j := by
  have hmul := Gpoly_eval m (-(j : ℝ) / 2)
  have hK0 := knownFactor_eval_half_ne_zero (m := m) (j := j)
  have hf0 := fSP_eval_half_ne_zero (m := m) (j := j) (by omega : 1 ≤ m)
  have hfneg := fSP_eval_half_neg_iff (m := m) (j := j) (by omega : 1 ≤ m)
  have hKneg := knownFactor_eval_half_neg_iff (m := m) (j := j) hm
  have hG0 : (Gpoly m).eval (-(j : ℝ) / 2) ≠ 0 := by
    intro h
    have : (fSP m).eval (-(j : ℝ) / 2) = 0 := by
      simpa [h] using hmul.symm
    exact hf0 this
  constructor
  · intro hG
    -- G<0, KF * G = fSP so KF and fSP have opposite signs
    by_cases hodd : Odd j
    · exact hodd
    · -- even j: fSP > 0 (j+1=2m ⇒ j=2m-1 odd), KF > 0 (not odd)
      have hfpos : 0 < (fSP m).eval (-(j : ℝ) / 2) :=
        fSP_eval_half_pos (by omega : 1 ≤ m) (fun hjm => by
          have hj1 : j + 1 = 2 * m := hjm
          have hjm1 : j = 2 * m - 1 := by omega
          have : Odd (2 * (m - 1) + 1) := odd_two_mul_add_one (m - 1)
          have heq : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
          rw [hjm1, heq] at hodd
          exact hodd this)
      have hKpos : 0 < (knownFactor m).eval (-(j : ℝ) / 2) := by
        have : ¬ (knownFactor m).eval (-(j : ℝ) / 2) < 0 := fun h =>
          hodd (hKneg.mp h).1
        exact lt_of_le_of_ne (le_of_not_gt this) hK0.symm
      have : 0 < (Gpoly m).eval (-(j : ℝ) / 2) := by
        have : 0 < (knownFactor m).eval (-(j : ℝ) / 2) *
            (Gpoly m).eval (-(j : ℝ) / 2) := by
          rw [hmul]; exact hfpos
        exact pos_of_mul_pos_right this (le_of_lt hKpos)
      linarith
  · intro hodd
    by_cases htarget : j + 1 = 2 * m
    · -- j = 2m-1 odd: fSP < 0, KF > 0 (j+3 = 2m+2 > 2m)
      have hf : (fSP m).eval (-(j : ℝ) / 2) < 0 := hfneg.mpr htarget
      have hKpos : 0 < (knownFactor m).eval (-(j : ℝ) / 2) := by
        have : ¬ (knownFactor m).eval (-(j : ℝ) / 2) < 0 := fun h => by
          have := (hKneg.mp h).2
          omega
        exact lt_of_le_of_ne (le_of_not_gt this) hK0.symm
      have : (knownFactor m).eval (-(j : ℝ) / 2) *
          (Gpoly m).eval (-(j : ℝ) / 2) < 0 := by
        rw [hmul]; exact hf
      nlinarith
    · -- odd, not 2m-1: fSP > 0, and j+3 ≤ 2m so KF < 0
      have hfpos : 0 < (fSP m).eval (-(j : ℝ) / 2) :=
        fSP_eval_half_pos (by omega) htarget
      have hup : j + 3 ≤ 2 * m := by
        obtain ⟨t, ht⟩ := hodd
        have : 2 * t + 1 + 3 ≤ 2 * m := by
          have : 2 * t + 1 ≠ 2 * m - 1 := by
            intro h
            have : j + 1 = 2 * m := by
              rw [ht]; omega
            exact htarget this
          have : 2 * t + 1 ≤ 2 * m := by
            rw [← ht]; exact hj
          omega
        rw [ht]; exact this
      have hK : (knownFactor m).eval (-(j : ℝ) / 2) < 0 :=
        hKneg.mpr ⟨hodd, hup⟩
      have : (knownFactor m).eval (-(j : ℝ) / 2) *
          (Gpoly m).eval (-(j : ℝ) / 2) > 0 := by
        rw [hmul]; exact hfpos
      nlinarith

lemma Gpoly_eval_half_ne_zero {m j : ℕ} (hm : 2 ≤ m) :
    (Gpoly m).eval (-(j : ℝ) / 2) ≠ 0 := by
  intro h
  have := Gpoly_eval m (-(j : ℝ) / 2)
  simp [h] at this
  exact fSP_eval_half_ne_zero (m := m) (j := j) (by omega) this.symm

lemma Gpoly_eval_half_pos {m j : ℕ} (hm : 2 ≤ m) (hj : j ≤ 2 * m) (he : Even j) :
    0 < (Gpoly m).eval (-(j : ℝ) / 2) := by
  have hne := Gpoly_eval_half_ne_zero (m := m) (j := j) hm
  have : ¬ (Gpoly m).eval (-(j : ℝ) / 2) < 0 := fun h =>
    (Nat.not_odd_iff_even.mpr he) ((Gpoly_eval_half_neg_iff hm hj).mp h)
  exact lt_of_le_of_ne (le_of_not_gt this) hne.symm

lemma exists_root_of_sign_change {p : Polynomial ℝ} {a b : ℝ} (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ x, a < x ∧ x < b ∧ p.eval x = 0 := by
  have hc : ContinuousOn (fun x => p.eval x) (Set.Icc a b) :=
    (Polynomial.continuous p).continuousOn
  rcases (mul_neg_iff.mp h) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · -- 0 < eval a and eval b < 0
    have hmem : (0 : ℝ) ∈ Set.Ioo (p.eval b) (p.eval a) := ⟨hb, ha⟩
    obtain ⟨x, hxI, hx0⟩ := (intermediate_value_Ioo' hab.le hc hmem)
    exact ⟨x, hxI.1, hxI.2, hx0⟩
  · -- eval a < 0 and 0 < eval b
    have hmem : (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b) := ⟨ha, hb⟩
    obtain ⟨x, hxI, hx0⟩ := (intermediate_value_Ioo hab.le hc hmem)
    exact ⟨x, hxI.1, hxI.2, hx0⟩

lemma Gpoly_sign_change {m j : ℕ} (hm : 2 ≤ m) (hj : j < 2 * m) :
    (Gpoly m).eval (-(j : ℝ) / 2) * (Gpoly m).eval (-((j + 1 : ℕ) : ℝ) / 2) < 0 := by
  have hj0 : j ≤ 2 * m := by omega
  have hj1 : j + 1 ≤ 2 * m := by omega
  by_cases he : Even j
  · have hpos := Gpoly_eval_half_pos hm hj0 he
    have hodd : Odd (j + 1) := Even.add_one he
    have hneg : (Gpoly m).eval (-((j + 1 : ℕ) : ℝ) / 2) < 0 :=
      (Gpoly_eval_half_neg_iff hm hj1).mpr hodd
    nlinarith
  · have hodd : Odd j := Nat.not_even_iff_odd.mp he
    have hneg : (Gpoly m).eval (-(j : ℝ) / 2) < 0 :=
      (Gpoly_eval_half_neg_iff hm hj0).mpr hodd
    have he' : Even (j + 1) := Nat.even_add_one.mpr he
    have hpos := Gpoly_eval_half_pos hm hj1 he'
    nlinarith

lemma Gpoly_root_in_interval {m j : ℕ} (hm : 2 ≤ m) (hj : j < 2 * m) :
    ∃ x : ℝ, -((j + 1 : ℕ) : ℝ) / 2 < x ∧ x < -(j : ℝ) / 2 ∧ (Gpoly m).eval x = 0 := by
  have hab : -((j + 1 : ℕ) : ℝ) / 2 < -(j : ℝ) / 2 := by
    have : (j : ℝ) < ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self j
    linarith
  have hmul : (Gpoly m).eval (-((j + 1 : ℕ) : ℝ) / 2) *
      (Gpoly m).eval (-(j : ℝ) / 2) < 0 := by
    convert (Gpoly_sign_change hm hj) using 1
    push_cast
    ring
  exact exists_root_of_sign_change hab hmul

lemma beta1_even (x : ℝ) : beta1 (-x) = beta1 x := by
  unfold beta1; ring

/-- `S(-x-1).transpose = S(x+1)`. -/
lemma Smat_transpose_reflect (x : ℝ) : (Smat (-x - 1)).transpose = Smat (x + 1) := by
  have hb : beta1 (-x - 1) = beta1 (x + 1) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using beta1_even (x + 1)
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Smat, Matrix.transpose_apply, hb]
  · simp [Smat, Matrix.transpose_apply]; ring
  · simp [Smat, Matrix.transpose_apply]; ring
  · simp [Smat, Matrix.transpose_apply]

/-- The product also grows on the right: `S(x+m)⋯S(x) = (S(x+m)⋯S(x+1)) S(x)`. -/
lemma SprodR_mul_Smat (m : ℕ) (x : ℝ) :
    SprodR (m + 1) x = SprodR m (x + 1) * Smat x := by
  induction m with
  | zero =>
    simp [SprodR_succ, SprodR_zero]
  | succ m ih =>
    rw [SprodR_succ, ih, SprodR_succ, mul_assoc]
    congr 1
    congr 1
    push_cast
    ring

/-- Matrix reflection: `(SprodR m (-x-m)).transpose = SprodR m (x+1)`. -/
lemma SprodR_reflect_transpose (m : ℕ) (x : ℝ) :
    (SprodR m (-x - (m : ℝ))).transpose = SprodR m (x + 1) := by
  induction m generalizing x with
  | zero =>
    simp [SprodR_zero]
  | succ m ih =>
    rw [SprodR_succ, Matrix.transpose_mul]
    have hidx : -x - ((m + 1 : ℕ) : ℝ) + (m : ℝ) = -x - 1 := by
      push_cast; ring
    rw [hidx, Smat_transpose_reflect]
    have harg : -x - ((m + 1 : ℕ) : ℝ) = -(x + 1) - (m : ℝ) := by
      push_cast; ring
    rw [harg, ih (x + 1)]
    have hcons := (SprodR_mul_Smat m (x + 1)).symm
    convert hcons using 2

/-- The `(1,1)` entry of an `(m+1)`-step product. -/
lemma SprodR_11 (m : ℕ) (x : ℝ) :
    SprodR (m + 1) x 1 1 = alpha1 (x + (m : ℝ)) * (fSP m).eval x := by
  have h := SprodP_21 (m + 1) (Nat.succ_pos m)
  have hcast : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  simp only [hcast, Nat.add_one_sub_one] at h
  have he := congrArg (fun p : Polynomial ℝ => p.eval x) h
  simpa [SprodP_eval, shiftP_eval, alphaP_eval, eval_mul] using he

/-- The reflection identity for `fSP`. -/
lemma fSP_eval_reflect (m : ℕ) (x : ℝ) :
    alpha1 (-x) * (fSP m).eval (-x - (m : ℝ)) =
      alpha1 (x + (m : ℝ)) * (fSP m).eval x := by
  have hmul : SprodR (m + 1) x = SprodR m (x + 1) * Smat x := SprodR_mul_Smat m x
  have h11 : SprodR (m + 1) x 1 1 =
      SprodR m (x + 1) 1 0 * Smat x 0 1 + SprodR m (x + 1) 1 1 * Smat x 1 1 := by
    rw [hmul]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hleft : SprodR (m + 1) x 1 1 = alpha1 (-x) * SprodR m (x + 1) 1 0 := by
    simp [h11, Smat]
    ring
  have hright : SprodR (m + 1) x 1 1 = alpha1 (x + (m : ℝ)) * (fSP m).eval x :=
    SprodR_11 m x
  have htrans : SprodR m (x + 1) 1 0 = SprodR m (-x - (m : ℝ)) 0 1 := by
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0)
      (SprodR_reflect_transpose m x)
    simpa [Matrix.transpose_apply] using this.symm
  rw [hright] at hleft
  rw [htrans, ← fSP_eval] at hleft
  exact hleft.symm

lemma pred_pred_succ_sub_cast {m j : ℕ} (hm : 2 ≤ m) (hj : j ≤ m.pred.pred) :
    ((m.pred.pred + 1 - j : ℕ) : ℝ) = (m : ℝ) - 1 - (j : ℝ) := by
  have hpred : m.pred.pred = m - 2 := pred_pred_eq m
  have h1 : m.pred.pred + 1 - j = m - 1 - j := by omega
  rw [h1]
  have hle : j ≤ m - 1 := by omega
  have hle' : 1 ≤ m := by omega
  rw [Nat.cast_sub hle, Nat.cast_sub hle']
  push_cast
  ring

/-- Reflection identity for the known factor of `fSP`. -/
lemma knownFactor_eval_reflect {m : ℕ} (hm : 2 ≤ m) (x : ℝ) :
    (knownFactor m).eval (-x - m) * alpha1 (-x) =
      (knownFactor m).eval x * alpha1 (x + m) := by
  rw [knownFactor_eval, knownFactor_eval]
  have hprod : ((Finset.Icc 1 m.pred.pred).prod fun j => P1.eval (-(-x - m) - (j : ℝ))) =
      ((Finset.Icc 1 m.pred.pred).prod fun j => P1.eval (-x - (j : ℝ))) := by
    refine Finset.prod_nbij'
        (fun j => m.pred.pred + 1 - j) (fun j => m.pred.pred + 1 - j) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      have hj' : 1 ≤ j ∧ j ≤ m.pred.pred := Finset.mem_Icc.mp hj
      have hφ : 1 ≤ m.pred.pred + 1 - j ∧ m.pred.pred + 1 - j ≤ m.pred.pred := by omega
      exact Finset.mem_Icc.mpr hφ
    · intro j hj
      have hj' : 1 ≤ j ∧ j ≤ m.pred.pred := Finset.mem_Icc.mp hj
      have hφ : 1 ≤ m.pred.pred + 1 - j ∧ m.pred.pred + 1 - j ≤ m.pred.pred := by omega
      exact Finset.mem_Icc.mpr hφ
    · intro j hj
      have hj' : 1 ≤ j ∧ j ≤ m.pred.pred := Finset.mem_Icc.mp hj
      have hle : j ≤ m.pred.pred + 1 := by omega
      exact Nat.sub_sub_self hle
    · intro j hj
      have hj' : 1 ≤ j ∧ j ≤ m.pred.pred := Finset.mem_Icc.mp hj
      have hle : j ≤ m.pred.pred + 1 := by omega
      exact Nat.sub_sub_self hle
    · intro j hj
      have hjle : j ≤ m.pred.pred := (Finset.mem_Icc.mp hj).2
      have hz : -(-x - (m : ℝ)) - (j : ℝ) = x + (m : ℝ) - (j : ℝ) := by ring
      rw [hz, P1_symmetry]
      apply congrArg (fun t => P1.eval t)
      rw [pred_pred_succ_sub_cast hm hjle]
      ring
  rw [hprod]
  ring

/-- Polynomial form of the reflection identity for `Gpoly`. -/
lemma Gpoly_eq_reflect {m : ℕ} (hm : 2 ≤ m) :
    (Gpoly m).comp (-X - C (m : ℝ)) = Gpoly m := by
  have hpt : ∀ x : ℝ,
      (knownFactor m).eval (-x - m) * alpha1 (-x) *
        ((Gpoly m).eval (-x - m) - (Gpoly m).eval x) = 0 := by
    intro x
    have hf := fSP_eval_reflect m x
    have hx := Gpoly_eval m x
    have hy := Gpoly_eval m (-x - m)
    have hKF := knownFactor_eval_reflect hm x
    calc
      (knownFactor m).eval (-x - m) * alpha1 (-x) *
          ((Gpoly m).eval (-x - m) - (Gpoly m).eval x)
        = alpha1 (-x) * ((knownFactor m).eval (-x - m) * (Gpoly m).eval (-x - m)) -
            ((knownFactor m).eval (-x - m) * alpha1 (-x)) * (Gpoly m).eval x := by
          ring
      _ = alpha1 (-x) * (fSP m).eval (-x - m) -
            ((knownFactor m).eval x * alpha1 (x + m)) * (Gpoly m).eval x := by
          rw [hy, hKF]
      _ = alpha1 (x + m) * (fSP m).eval x -
            (knownFactor m).eval x * alpha1 (x + m) * (Gpoly m).eval x := by
          rw [hf]
      _ = alpha1 (x + m) * ((knownFactor m).eval x * (Gpoly m).eval x) -
            (knownFactor m).eval x * alpha1 (x + m) * (Gpoly m).eval x := by
          rw [hx]
      _ = 0 := by ring
  have hpoly :
      (knownFactor m).comp (-X - C (m : ℝ)) * (alphaP.comp (-X)) *
        ((Gpoly m).comp (-X - C (m : ℝ)) - Gpoly m) = 0 := by
    apply Polynomial.funext
    intro x
    simp only [eval_mul, eval_sub, eval_comp, eval_neg, eval_X, eval_C, eval_zero, alphaP_eval]
    exact hpt x
  have hA : (knownFactor m).comp (-X - C (m : ℝ)) ≠ 0 := by
    intro h
    rcases (comp_eq_zero_iff.mp h) with h0 | ⟨_, hq⟩
    · exact knownFactor_ne_zero m h0
    · have h1 : (-X - C (m : ℝ)).coeff 1 = -1 := by simp
      have h1' : (C ((-X - C (m : ℝ)).coeff 0)).coeff 1 = 0 := by simp
      have : (-1 : ℝ) = 0 := by
        simpa [h1, h1'] using congrArg (fun p : Polynomial ℝ => p.coeff 1) hq
      exact absurd this (by norm_num)
  have hB : alphaP.comp (-X) ≠ 0 := alphaP_comp_neg_ne_zero
  have hC :
      (Gpoly m).comp (-X - C (m : ℝ)) - Gpoly m = 0 := by
    have hmul := mul_eq_zero.mp hpoly
    rcases hmul with h | hC
    · have hmul' := mul_eq_zero.mp h
      rcases hmul' with hA' | hB'
      · exact (hA hA').elim
      · exact (hB hB').elim
    · exact hC
  exact sub_eq_zero.mp hC

lemma Gpoly_eval_reflect {m : ℕ} (hm : 2 ≤ m) (x : ℝ) :
    (Gpoly m).eval (-x - m) = (Gpoly m).eval x := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval x) (Gpoly_eq_reflect hm)
  simpa [eval_comp, eval_sub, eval_neg, eval_X, eval_C] using h

lemma Ppoly_eval {m : ℕ} (x : ℝ) :
    (Ppoly m).eval x = (Gpoly m).eval ((m : ℝ) * (x - 1)) := by
  unfold Ppoly
  simp [eval_comp, eval_mul, eval_sub, eval_C, eval_X]

lemma Ppoly_degree {m : ℕ} (hm : 2 ≤ m) : (Ppoly m).degree = (2 * m : ℕ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hlin : (C (m : ℝ) * (X - 1)).natDegree = 1 := by
    have hX : (X - 1 : Polynomial ℝ) = X - C 1 := by simp
    rw [hX, natDegree_C_mul hm0, natDegree_X_sub_C]
  have hnat : (Ppoly m).natDegree = 2 * m := by
    unfold Ppoly
    rw [natDegree_comp, Gpoly_natDegree_of_two hm, hlin, mul_one]
  have hne : Ppoly m ≠ 0 := by
    intro h0
    have hdeg0 : (Ppoly m).natDegree = 0 := by simp [h0]
    rw [hnat] at hdeg0
    omega
  rw [degree_eq_natDegree hne, hnat]

lemma Ppoly_symmetry {m : ℕ} (hm : 2 ≤ m) (x : ℝ) :
    (Ppoly m).eval x = (Ppoly m).eval (1 - x) := by
  rw [Ppoly_eval, Ppoly_eval]
  have := Gpoly_eval_reflect hm ((m : ℝ) * (x - 1))
  -- G(m(x-1)) = G(-m(x-1)-m) = G(-mx)
  -- P(1-x) = G(m((1-x)-1)) = G(-mx)
  convert this.symm using 2
  ring

noncomputable def Gpoly_chosenRoot (m j : ℕ) (hm : 2 ≤ m) (hj : j < 2 * m) : ℝ :=
  Classical.choose (Gpoly_root_in_interval hm hj)

lemma Gpoly_chosenRoot_spec (m j : ℕ) (hm : 2 ≤ m) (hj : j < 2 * m) :
    -((j + 1 : ℕ) : ℝ) / 2 < Gpoly_chosenRoot m j hm hj ∧
      Gpoly_chosenRoot m j hm hj < -(j : ℝ) / 2 ∧
        (Gpoly m).eval (Gpoly_chosenRoot m j hm hj) = 0 :=
  Classical.choose_spec (Gpoly_root_in_interval hm hj)

lemma Gpoly_chosenRoot_strict {m j k : ℕ} (hm : 2 ≤ m)
    (hj : j < 2 * m) (hk : k < 2 * m) (hjk : j < k) :
    Gpoly_chosenRoot m k hm hk < Gpoly_chosenRoot m j hm hj := by
  have hj' := Gpoly_chosenRoot_spec m j hm hj
  have hk' := Gpoly_chosenRoot_spec m k hm hk
  have hle : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ k)
  linarith

lemma Gpoly_chosenRoot_injective {m : ℕ} (hm : 2 ≤ m) {j k : ℕ}
    (hj : j < 2 * m) (hk : k < 2 * m)
    (h : Gpoly_chosenRoot m j hm hj = Gpoly_chosenRoot m k hm hk) : j = k := by
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · have := Gpoly_chosenRoot_strict hm hj hk hjk; linarith
  · exact hjk
  · have := Gpoly_chosenRoot_strict hm hk hj hjk; linarith

lemma Gpoly_card_roots {m : ℕ} (hm : 2 ≤ m) : (Gpoly m).roots.card = 2 * m := by
  classical
  let r : Fin (2 * m) → ℝ := fun i => Gpoly_chosenRoot m i.1 hm i.2
  have hr : ∀ i, (Gpoly m).IsRoot (r i) := fun i =>
    (Gpoly_chosenRoot_spec m i.1 hm i.2).2.2
  have hinj : Function.Injective r := by
    intro i j h
    exact Fin.ext (Gpoly_chosenRoot_injective hm i.2 j.2 h)
  have himg : Finset.univ.image r ⊆ (Gpoly m).roots.toFinset := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact Multiset.mem_toFinset.mpr
      ((mem_roots (Gpoly_ne_zero_of_two hm)).mpr (hr i))
  have hcard_img : (Finset.univ.image r).card = 2 * m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hle1 : (Finset.univ.image r).card ≤ (Gpoly m).roots.toFinset.card :=
    Finset.card_le_card himg
  have hle2 : (Gpoly m).roots.toFinset.card ≤ (Gpoly m).roots.card :=
    Multiset.toFinset_card_le _
  have hle3 : (Gpoly m).roots.card ≤ (Gpoly m).natDegree := card_roots' _
  have hdeg : (Gpoly m).natDegree = 2 * m := Gpoly_natDegree_of_two hm
  omega

lemma Gpoly_splits_of_two {m : ℕ} (hm : 2 ≤ m) : (Gpoly m).Splits := by
  rw [splits_iff_card_roots, Gpoly_card_roots hm, Gpoly_natDegree_of_two hm]

lemma Gpoly_chosen_image_subset {m : ℕ} (hm : 2 ≤ m) :
    Finset.univ.image (fun i : Fin (2 * m) => Gpoly_chosenRoot m i.1 hm i.2)
      ⊆ (Gpoly m).roots.toFinset := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
  exact Multiset.mem_toFinset.mpr
    ((mem_roots (Gpoly_ne_zero_of_two hm)).mpr
      (Gpoly_chosenRoot_spec m i.1 hm i.2).2.2)

lemma Gpoly_chosen_image_card {m : ℕ} (hm : 2 ≤ m) :
    (Finset.univ.image (fun i : Fin (2 * m) => Gpoly_chosenRoot m i.1 hm i.2)).card =
      2 * m := by
  refine (Finset.card_image_of_injective _ ?_).trans (by simp)
  intro i j h
  exact Fin.ext (Gpoly_chosenRoot_injective hm i.2 j.2 h)

lemma Gpoly_roots_eq_chosen {m : ℕ} (hm : 2 ≤ m) :
    (Gpoly m).roots.toFinset =
      Finset.univ.image (fun i : Fin (2 * m) => Gpoly_chosenRoot m i.1 hm i.2) := by
  classical
  have himg := Gpoly_chosen_image_subset hm
  have hle : (Gpoly m).roots.toFinset.card ≤
      (Finset.univ.image (fun i : Fin (2 * m) => Gpoly_chosenRoot m i.1 hm i.2)).card := by
    have h1 := Multiset.toFinset_card_le (Gpoly m).roots
    have h2 := Gpoly_card_roots hm
    have h3 := Gpoly_chosen_image_card hm
    omega
  exact (Finset.eq_of_subset_of_card_le himg hle).symm

lemma Gpoly_root_mem {m : ℕ} (hm : 2 ≤ m) {x : ℝ} (hx : (Gpoly m).IsRoot x) :
    -(m : ℝ) < x ∧ x < 0 := by
  have hxmem : x ∈ (Gpoly m).roots.toFinset :=
    Multiset.mem_toFinset.mpr ((mem_roots (Gpoly_ne_zero_of_two hm)).mpr hx)
  rw [Gpoly_roots_eq_chosen hm] at hxmem
  rcases Finset.mem_image.mp hxmem with ⟨i, _, rfl⟩
  have spec := Gpoly_chosenRoot_spec m i.1 hm i.2
  have hlo : -((i.1 + 1 : ℕ) : ℝ) / 2 ≥ -(m : ℝ) := by
    have : ((i.1 + 1 : ℕ) : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast (by omega : i.1 + 1 ≤ 2 * m)
    have h2 : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    linarith
  have hhi : -(i.1 : ℝ) / 2 ≤ 0 := by
    have : (0 : ℝ) ≤ (i.1 : ℝ) := Nat.cast_nonneg _
    linarith
  constructor
  · linarith [spec.1]
  · linarith [spec.2.1]

lemma Ppoly_map_eval (m : ℕ) (z : ℂ) :
    ((Ppoly m).map (algebraMap ℝ ℂ)).eval z =
      ((Gpoly m).map (algebraMap ℝ ℂ)).eval ((m : ℂ) * (z - 1)) := by
  unfold Ppoly
  rw [Polynomial.map_comp, eval_comp]
  congr 1
  simp

lemma IsRoot_map_real {p : Polynomial ℝ} {r : ℝ}
    (h : (p.map (algebraMap ℝ ℂ)).IsRoot (r : ℂ)) : p.IsRoot r := by
  rw [IsRoot, eval_map] at h
  have : p.eval₂ (algebraMap ℝ ℂ) (algebraMap ℝ ℂ r) = 0 := by
    simpa using h
  rw [eval₂_at_apply] at this
  exact (algebraMap ℝ ℂ).injective (by simpa using this)

lemma complex_of_real_mul_root {m : ℕ} {z : ℂ} {r : ℝ}
    (h : (r : ℂ) = (m : ℂ) * (z - 1)) (hm : m ≠ 0) :
    z.im = 0 ∧ z.re = 1 + r / m := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have him : z.im = 0 := by
    have himg := congrArg Complex.im h.symm
    simp [Complex.mul_im, Complex.sub_im] at himg
    have : (m : ℝ) * z.im = 0 := by simpa using himg
    exact (_root_.mul_eq_zero.mp this).resolve_left hm0
  have hre : (m : ℝ) * (z.re - 1) = r := by
    have hreg := congrArg Complex.re h.symm
    simp [Complex.mul_re, Complex.sub_re, him] at hreg
    exact hreg
  refine ⟨him, ?_⟩
  have : z.re - 1 = r / (m : ℝ) := by
    field_simp [hm0]
    linarith [hre]
  linarith

lemma Ppoly_roots_mem {m : ℕ} (hm : 2 ≤ m)
    (z : ℂ) (hz : (Ppoly m |>.map (algebraMap ℝ ℂ)).eval z = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (0 : ℝ) 1 := by
  have hz' : ((Gpoly m).map (algebraMap ℝ ℂ)).eval ((m : ℂ) * (z - 1)) = 0 := by
    rwa [Ppoly_map_eval] at hz
  have hG0 : Gpoly m ≠ 0 := Gpoly_ne_zero_of_two hm
  have hroot : ((Gpoly m).map (algebraMap ℝ ℂ)).IsRoot ((m : ℂ) * (z - 1)) := hz'
  have hrange := (Gpoly_splits_of_two hm).mem_range_of_isRoot hG0 hroot
  rcases hrange with ⟨r, hr⟩
  have hr0 : (Gpoly m).IsRoot r := IsRoot_map_real (by
    rwa [← hr] at hroot)
  have hrI := Gpoly_root_mem hm hr0
  have hmne : m ≠ 0 := by omega
  have hzr := complex_of_real_mul_root hr hmne
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hmne)
  have hre : z.re = 1 + r / (m : ℝ) := hzr.2
  refine ⟨hzr.1, ⟨?_, ?_⟩⟩
  · rw [hre]
    have : -(m : ℝ) / (m : ℝ) < r / (m : ℝ) :=
      div_lt_div_of_pos_right hrI.1 hmpos
    have hdiv : -(m : ℝ) / (m : ℝ) = -1 := by field_simp
    linarith
  · rw [hre]
    have : r / (m : ℝ) < 0 := div_neg_of_neg_of_pos hrI.2 hmpos
    linarith

lemma coeff_comp_neg_X (p : Polynomial ℝ) (n : ℕ) :
    (p.comp (-X)).coeff n = (-1 : ℝ) ^ n * p.coeff n := by
  have : (-X : Polynomial ℝ) = C (-1) * X := by simp
  rw [this, comp_C_mul_X_coeff]
  ring

lemma odd_coeff_of_eq_comp_neg {p : Polynomial ℝ} (hp : p.comp (-X) = p) {n : ℕ}
    (hn : Odd n) : p.coeff n = 0 := by
  have h : (p.comp (-X)).coeff n = p.coeff n := by
    simpa using congrArg (fun q : Polynomial ℝ => q.coeff n) hp
  rw [coeff_comp_neg_X] at h
  have h1 : (-1 : ℝ) ^ n = -1 := Odd.neg_one_pow hn
  rw [h1] at h
  linarith

lemma evenExtract_coeff (p : Polynomial ℝ) (i : ℕ) :
    (evenExtract p).coeff i =
      if i ∈ Finset.range (p.natDegree / 2 + 1) then p.coeff (2 * i) else 0 := by
  unfold evenExtract
  rw [finset_sum_coeff]
  simp only [coeff_C_mul, coeff_X_pow]
  by_cases hi : i ∈ Finset.range (p.natDegree / 2 + 1)
  · rw [if_pos hi, Finset.sum_eq_single i]
    · simp
    · intro j hj hne
      rw [if_neg (id (Ne.symm hne) : ¬ i = j), mul_zero]
    · intro h; exact (h hi).elim
  · rw [if_neg hi]
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hne : i ≠ j := fun h => hi (h ▸ hj)
    rw [if_neg hne, mul_zero]

lemma expand_evenExtract_coeff (p : Polynomial ℝ) (n : ℕ) :
    ((evenExtract p).comp (X ^ 2)).coeff n =
      if Even n ∧ n / 2 ≤ p.natDegree / 2 then p.coeff n else 0 := by
  have hexp : (evenExtract p).comp (X ^ 2) = expand ℝ 2 (evenExtract p) :=
    (expand_eq_comp_X_pow (R := ℝ) (p := 2)).symm
  rw [hexp, coeff_expand (by norm_num : (0 : ℕ) < 2)]
  by_cases hdvd : 2 ∣ n
  · have hE : Even n := even_iff_two_dvd.mpr hdvd
    have hdiv : 2 * (n / 2) = n := Nat.mul_div_cancel' hdvd
    rw [if_pos hdvd, evenExtract_coeff]
    by_cases hle : n / 2 ∈ Finset.range (p.natDegree / 2 + 1)
    · have hle' : n / 2 ≤ p.natDegree / 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hle)
      rw [if_pos hle, if_pos (And.intro hE hle'), hdiv]
    · have hle' : ¬ n / 2 ≤ p.natDegree / 2 := by
        intro h
        exact hle (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr h))
      rw [if_neg hle, if_neg]
      exact fun h => hle' h.2
  · have hE : ¬ Even n := mt even_iff_two_dvd.mp hdvd
    rw [if_neg hdvd, if_neg]
    exact fun h => hE h.1

lemma eq_evenExtract_comp {p : Polynomial ℝ} (hp : p.comp (-X) = p) :
    p = (evenExtract p).comp (X ^ 2) := by
  ext n
  rw [expand_evenExtract_coeff]
  by_cases hE : Even n
  · by_cases hle : n / 2 ≤ p.natDegree / 2
    · rw [if_pos ⟨hE, hle⟩]
    · rw [if_neg]
      · apply coeff_eq_zero_of_natDegree_lt
        have : p.natDegree / 2 < n / 2 := Nat.lt_of_not_ge hle
        have h2 : 2 * (n / 2) = n := Nat.mul_div_cancel' (even_iff_two_dvd.mp hE)
        omega
      · exact fun h => hle h.2
  · rw [if_neg (fun h => hE h.1)]
    exact odd_coeff_of_eq_comp_neg hp (Nat.not_even_iff_odd.mp hE)

lemma Qraw_comp_neg {m : ℕ} (hm : 1 ≤ m) :
    ((Gpoly (2 * m)).comp (C (m : ℝ) * (X - 1))).comp (-X) =
      (Gpoly (2 * m)).comp (C (m : ℝ) * (X - 1)) := by
  have hm2 : 2 ≤ 2 * m := by omega
  apply Polynomial.funext
  intro x
  simp [eval_comp]
  have h := Gpoly_eval_reflect hm2 ((m : ℝ) * (x - 1))
  have heq : (m : ℝ) * (-x - 1) = -((m : ℝ) * (x - 1)) - ((2 * m : ℕ) : ℝ) := by
    push_cast; ring
  rw [heq]
  exact h

lemma Gpoly_zero : Gpoly 0 = 0 := by
  have h := Gpoly_mul 0
  rw [fSP_zero] at h
  exact (_root_.mul_eq_zero.mp h).resolve_left (knownFactor_ne_zero 0)

lemma Qraw_eq (m : ℕ) :
    (Gpoly (2 * m)).comp (C (m : ℝ) * (X - 1)) =
      (Qpoly m).comp (X ^ 2) := by
  unfold Qpoly
  cases m with
  | zero =>
    rw [Gpoly_zero, zero_comp]
    have : evenExtract (0 : Polynomial ℝ) = 0 := by
      unfold evenExtract
      simp
    rw [this, zero_comp]
  | succ m =>
    exact eq_evenExtract_comp (Qraw_comp_neg (Nat.succ_pos m))

lemma Qraw_natDegree {m : ℕ} (hm : 1 ≤ m) :
    ((Gpoly (2 * m)).comp (C (m : ℝ) * (X - 1))).natDegree = 4 * m := by
  have hm2 : 2 ≤ 2 * m := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hlin : (C (m : ℝ) * (X - 1)).natDegree = 1 := by
    have hX : (X - 1 : Polynomial ℝ) = X - C 1 := by simp
    rw [hX, natDegree_C_mul hm0, natDegree_X_sub_C]
  rw [natDegree_comp, Gpoly_natDegree_of_two hm2, hlin]
  ring

lemma Qpoly_natDegree {m : ℕ} (hm : 1 ≤ m) : (Qpoly m).natDegree = 2 * m := by
  have h := congrArg natDegree (Qraw_eq m)
  have hdeg := Qraw_natDegree hm
  rw [hdeg] at h
  have hX2 : ((Qpoly m).comp (X ^ 2)).natDegree = (Qpoly m).natDegree * 2 := by
    rw [natDegree_comp, natDegree_X_pow]
  rw [hX2] at h
  -- 4 * m = natDegree Q * 2
  have : (Qpoly m).natDegree * 2 = 4 * m := h.symm
  omega

lemma Qpoly_ne_zero {m : ℕ} (hm : 1 ≤ m) : Qpoly m ≠ 0 := by
  intro h0
  have := Qpoly_natDegree hm
  simp [h0] at this
  omega

lemma Qpoly_degree {m : ℕ} (hm : 2 ≤ m) : (Qpoly m).degree = (2 * m : ℕ) := by
  have hm1 : 1 ≤ m := by omega
  rw [degree_eq_natDegree (Qpoly_ne_zero hm1), Qpoly_natDegree hm1]

lemma Qpoly_sq_roots_mem {m : ℕ} (hm : 2 ≤ m)
    (z : ℂ) (hz : ((Qpoly m).map (algebraMap ℝ ℂ)).eval (z ^ 2) = 0) :
    z.im = 0 ∧ z.re ∈ Set.Icc (-1 : ℝ) 1 := by
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 ≤ 2 * m := by omega
  have hz' : (((Qpoly m).comp (X ^ 2)).map (algebraMap ℝ ℂ)).eval z = 0 := by
    rw [Polynomial.map_comp, eval_comp]
    simpa using hz
  rw [← Qraw_eq] at hz'
  have hzG : ((Gpoly (2 * m)).map (algebraMap ℝ ℂ)).eval ((m : ℂ) * (z - 1)) = 0 := by
    rw [Polynomial.map_comp, eval_comp] at hz'
    convert hz' using 2
    simp
  have hG0 : Gpoly (2 * m) ≠ 0 := Gpoly_ne_zero_of_two hm2
  have hroot : ((Gpoly (2 * m)).map (algebraMap ℝ ℂ)).IsRoot ((m : ℂ) * (z - 1)) := hzG
  have hrange := (Gpoly_splits_of_two hm2).mem_range_of_isRoot hG0 hroot
  rcases hrange with ⟨r, hr⟩
  have hr0 : (Gpoly (2 * m)).IsRoot r := IsRoot_map_real (by
    rwa [← hr] at hroot)
  have hrI := Gpoly_root_mem hm2 hr0
  have hmne : m ≠ 0 := by omega
  have hzr := complex_of_real_mul_root hr hmne
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero hmne)
  have hre : z.re = 1 + r / (m : ℝ) := hzr.2
  refine ⟨hzr.1, ⟨?_, ?_⟩⟩
  · rw [hre]
    have hlo : -(2 * (m : ℝ)) < r := by
      convert hrI.1 using 1
      push_cast; ring
    have : -(2 * (m : ℝ)) / (m : ℝ) < r / (m : ℝ) :=
      div_lt_div_of_pos_right hlo hmpos
    have hdiv : -(2 * (m : ℝ)) / (m : ℝ) = -2 := by field_simp
    linarith
  · rw [hre]
    have : r / (m : ℝ) < 0 := div_neg_of_neg_of_pos hrI.2 hmpos
    linarith

lemma int_sq_ne_five (t : ℤ) : t ^ 2 ≠ 5 := by
  intro h
  have habs : t.natAbs ^ 2 = 5 := by
    have : (t.natAbs : ℤ) ^ 2 = 5 := by
      rw [Int.natAbs_sq]
      exact h
    exact_mod_cast this
  have ht : t.natAbs = 0 ∨ t.natAbs = 1 ∨ t.natAbs = 2 ∨ 3 ≤ t.natAbs := by omega
  rcases ht with h0 | h1 | h2 | h3
  · simp [h0] at habs
  · simp [h1] at habs
  · simp [h2] at habs
  · have : 3 ^ 2 ≤ t.natAbs ^ 2 := Nat.pow_le_pow_left h3 2
    omega

lemma P1_eval_int_ne_zero (k : ℤ) : P1.eval (k : ℝ) ≠ 0 := by
  intro h
  have h' : (5 : ℝ) * (k : ℝ) ^ 2 - 5 * k + 1 = 0 := by
    simpa [P1_eval] using h
  have hdisc : (10 * (k : ℝ) - 5) ^ 2 = 5 := by nlinarith
  have hinter : ((10 * k - 5 : ℤ) : ℝ) = 10 * (k : ℝ) - 5 := by push_cast; ring
  have ht2 : (10 * k - 5 : ℤ) ^ 2 = 5 := by
    have : ((10 * k - 5 : ℤ) : ℝ) ^ 2 = 5 := by rw [hinter]; exact hdisc
    exact_mod_cast this
  exact int_sq_ne_five _ ht2

lemma alpha1_nat_ne_zero (i : ℕ) : alpha1 (i : ℝ) ≠ 0 := by
  rw [alpha1_eq_lin_P1]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (P1_eval_int_ne_zero i)
  · have : (0 : ℝ) < 2 * (i : ℝ) + 1 := by
      exact_mod_cast (Nat.succ_pos (2 * i))
    linarith
  · have : (0 : ℝ) < 2 * (i : ℝ) + 2 := by
      exact_mod_cast (Nat.succ_pos (2 * i + 1))
    linarith

lemma P1_eval_neg_int_ne_zero (k : ℕ) : P1.eval (-(k : ℝ)) ≠ 0 := by
  simpa using P1_eval_int_ne_zero (-(k : ℤ))

lemma alpha1_neg_of_ge_two {s : ℕ} (hs : 2 ≤ s) : alpha1 (-(s : ℝ)) ≠ 0 := by
  rw [alpha1_eq_lin_P1]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (P1_eval_neg_int_ne_zero s)
  · have hge : (2 : ℝ) * (s : ℝ) ≥ 4 := by exact_mod_cast (by omega : 4 ≤ 2 * s)
    linarith
  · have hge : (2 : ℝ) * (s : ℝ) ≥ 4 := by exact_mod_cast (by omega : 4 ≤ 2 * s)
    linarith

lemma Icc_union_succ (a b c : ℕ) (h1 : a ≤ b + 1) (h2 : b ≤ c) :
    Finset.Icc a b ∪ Finset.Icc (b + 1) c = Finset.Icc a c := by
  ext x
  simp only [Finset.mem_union, Finset.mem_Icc]
  omega

lemma Icc_disjoint_succ (a b c : ℕ) :
    Disjoint (Finset.Icc a b) (Finset.Icc (b + 1) c) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx hx'
  have hxab := Finset.mem_Icc.mp hx
  have hxbc := Finset.mem_Icc.mp hx'
  omega

lemma pred_pred_Icc {m : ℕ} (hm : 2 ≤ m) :
    Finset.Icc (m.pred.pred + 1) (2 * m).pred.pred =
      Finset.Icc (m - 1) (2 * m - 2) := by
  have h1 : m.pred.pred + 1 = m - 1 := by rw [pred_pred_eq m]; omega
  have h2 : (2 * m).pred.pred = 2 * m - 2 := pred_pred_eq (2 * m)
  rw [h1, h2]

lemma Ioc_even_odd (m : ℕ) :
    Finset.Ioc 0 (2 * m) =
      (Finset.range m).image (fun i => 2 * i + 1) ∪
        (Finset.range m).image (fun i => 2 * i + 2) := by
  ext k
  simp only [Finset.mem_Ioc, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · intro ⟨hk0, hkm⟩
    rcases Nat.even_or_odd k with he | ho
    · obtain ⟨i, rfl⟩ := even_iff_exists_two_mul.mp he
      refine Or.inr ⟨i - 1, ?_, ?_⟩
      · omega
      · omega
    · obtain ⟨i, rfl⟩ := ho
      exact Or.inl ⟨i, by omega, rfl⟩
  · intro h
    rcases h with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;> omega

lemma image_odd_even_disjoint (m : ℕ) :
    Disjoint ((Finset.range m).image (fun i => 2 * i + 1))
      ((Finset.range m).image (fun i => 2 * i + 2)) := by
  refine Finset.disjoint_left.mpr ?_
  intro a ha hb
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, h⟩ := Finset.mem_image.mp hb
  omega

lemma injOn_two_mul_add_one (s : Finset ℕ) :
    Set.InjOn (fun i : ℕ => 2 * i + 1) s := by
  intro a _ b _ h
  have h' : 2 * a + 1 = 2 * b + 1 := h
  omega

lemma injOn_two_mul_add_two (s : Finset ℕ) :
    Set.InjOn (fun i : ℕ => 2 * i + 2) s := by
  intro a _ b _ h
  have h' : 2 * a + 2 = 2 * b + 2 := h
  omega

lemma prod_pair_Ioc (m : ℕ) (x : ℝ) :
    (Finset.range m).prod (fun i =>
      (x + ((2 * i + 1 : ℕ) : ℝ)) * (x + ((2 * i + 2 : ℕ) : ℝ))) =
      (Finset.Ioc 0 (2 * m)).prod (fun k => x + (k : ℝ)) := by
  have hdisj := image_odd_even_disjoint m
  rw [Ioc_even_odd, Finset.prod_union hdisj]
  rw [Finset.prod_image (injOn_two_mul_add_one _),
      Finset.prod_image (injOn_two_mul_add_two _),
      ← Finset.prod_mul_distrib]

lemma two_mul_add_one_cast (m n i : ℕ) :
    (2 : ℝ) * ((m * n + i : ℕ) : ℝ) + 1 =
      (2 * m * n : ℝ) + ((2 * i + 1 : ℕ) : ℝ) := by
  push_cast; ring

lemma two_mul_add_two_cast (m n i : ℕ) :
    (2 : ℝ) * ((m * n + i : ℕ) : ℝ) + 2 =
      (2 * m * n : ℝ) + ((2 * i + 2 : ℕ) : ℝ) := by
  push_cast; ring

lemma prod_plus_linear (m n : ℕ) :
    (Finset.range m).prod (fun i =>
      ((2 : ℝ) * ((m * n + i : ℕ) : ℝ) + 1) *
        ((2 : ℝ) * ((m * n + i : ℕ) : ℝ) + 2)) =
      prod_factor_plus m n := by
  unfold prod_factor_plus product_indices
  simp_rw [two_mul_add_one_cast, two_mul_add_two_cast]
  simpa using prod_pair_Ioc m (2 * m * n : ℝ)

lemma paf_decomp (m n : ℕ) :
    (Finset.range m).prod (fun i => alpha1 ((m * n + i : ℕ) : ℝ)) =
      prod_factor_plus m n *
        (Finset.range m).prod (fun i => P1.eval ((m * n + i : ℕ) : ℝ)) := by
  simp_rw [alpha1_eq_lin_P1]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [← Finset.prod_mul_distrib, prod_plus_linear]

lemma knownFactor_double_eval {m : ℕ} (hm : 2 ≤ m) (x : ℝ) :
    (knownFactor (2 * m)).eval x =
      (knownFactor m).eval x *
        ((Finset.Icc (m.pred.pred + 1) (2 * m).pred.pred).prod
          fun j => P1.eval (-x - (j : ℝ))) := by
  rw [knownFactor_eval, knownFactor_eval]
  have hI : Finset.Icc 1 (2 * m).pred.pred =
      Finset.Icc 1 m.pred.pred ∪
        Finset.Icc (m.pred.pred + 1) (2 * m).pred.pred := by
    refine (Icc_union_succ 1 m.pred.pred (2 * m).pred.pred ?_ ?_).symm
    · have : m.pred.pred = m - 2 := pred_pred_eq m
      omega
    · have : m.pred.pred = m - 2 := pred_pred_eq m
      have : (2 * m).pred.pred = 2 * m - 2 := pred_pred_eq (2 * m)
      omega
  have hdisj := Icc_disjoint_succ 1 m.pred.pred (2 * m).pred.pred
  rw [hI, Finset.prod_union hdisj]
  ring

lemma cast_mul_sub_one {m n : ℕ} (hn : 1 ≤ n) :
    ((m * (n - 1) : ℕ) : ℝ) = (m : ℝ) * ((n : ℝ) - 1) := by
  rw [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one]

lemma cast_add_pred {m i : ℕ} (hm : 1 ≤ m) :
    ((i + (m - 1) : ℕ) : ℝ) = (i : ℝ) + (m : ℝ) - 1 := by
  rw [Nat.cast_add, Nat.cast_sub hm]
  push_cast
  ring

lemma P1_prod_identity {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n) :
    (Finset.range m).prod (fun i => P1.eval ((m * n + i : ℕ) : ℝ)) =
      (Finset.Icc (m.pred.pred + 1) (2 * m).pred.pred).prod
        (fun j => P1.eval (-((m * (n - 1) : ℕ) : ℝ) - (j : ℝ))) := by
  rw [pred_pred_Icc hm]
  refine Finset.prod_nbij' (fun i => i + (m - 1)) (fun j => j - (m - 1)) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have hlo : m - 1 ≤ i + (m - 1) := Nat.le_add_left _ _
    have hhi : i + (m - 1) ≤ 2 * m - 2 := by
      have : i + (m - 1) ≤ (m - 1) + (m - 1) :=
        Nat.add_le_add_right (Nat.le_pred_of_lt hi') _
      have heq : (m - 1) + (m - 1) = 2 * m - 2 := by omega
      omega
    exact Finset.mem_Icc.mpr ⟨hlo, hhi⟩
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have : j - (m - 1) < m := by omega
    exact Finset.mem_range.mpr this
  · intro i _hi
    exact Nat.add_sub_cancel i (m - 1)
  · intro j hj
    exact Nat.sub_add_cancel (Finset.mem_Icc.mp hj).1
  · intro i _hi
    have hsym := P1_symmetry ((m * n + i : ℕ) : ℝ)
    rw [hsym]
    refine congrArg (fun t => P1.eval t) ?_
    have hs := cast_mul_sub_one (m := m) hn
    have hi' := cast_add_pred (m := m) (i := i) (by omega)
    rw [hs, hi']
    push_cast
    ring

lemma Gpoly_eval_Ppoly_pos {m n : ℕ} (hn : 1 ≤ n) :
    (Gpoly m).eval ((m * (n - 1) : ℕ) : ℝ) = (Ppoly m).eval (n : ℝ) := by
  rw [Ppoly_eval, cast_mul_sub_one hn]

lemma Gpoly_eval_Ppoly_neg {m n : ℕ} (hm : 2 ≤ m) :
    (Gpoly m).eval ((m * n : ℕ) : ℝ) = (Ppoly m).eval (-(n : ℝ)) := by
  rw [Ppoly_eval]
  have h := Gpoly_eval_reflect hm ((m : ℝ) * n)
  have : -((m : ℝ) * n) - (m : ℝ) = (m : ℝ) * ((-(n : ℝ)) - 1) := by ring
  rw [← this]
  convert h.symm using 2
  push_cast
  ring

lemma Qpoly_eval_sq_of_pos {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n) :
    (Qpoly m).eval ((n : ℝ) ^ 2) =
      (Gpoly (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ) := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval (n : ℝ)) (Qraw_eq m)
  simp [eval_comp] at h
  rw [cast_mul_sub_one hn]
  simpa [pow_two] using h.symm

lemma Sprod_concat (a b start : ℕ) :
    Sprod (a + b) start = Sprod a (start + b) * Sprod b start := by
  induction a with
  | zero =>
    simp [Sprod_zero]
  | succ a ih =>
    have hsum : a + 1 + b = a + b + 1 := by omega
    rw [hsum, Sprod_succ, ih, Sprod_succ, mul_assoc]
    have hidx : start + (a + b) = start + b + a := by omega
    congr 2
    exact congrArg (fun k : ℕ => (k : ℝ)) hidx

lemma UF_eq_double (m n : ℕ) (hn : 1 ≤ n) :
    Uprod m n * Fprod m n = Sprod (2 * m) (m * (n - 1)) := by
  have h := Sprod_concat m m (m * (n - 1))
  have hsucc : (n - 1).succ = n := Nat.succ_pred_eq_of_pos hn
  have hmn : m * (n - 1) + m = m * n := by
    calc
      m * (n - 1) + m = m * (n - 1).succ := (Nat.mul_succ _ _).symm
      _ = m * n := by rw [hsucc]
  simpa [Uprod, Fprod, two_mul, hmn, add_comm] using h.symm

lemma UF_01 (m n : ℕ) (hn : 1 ≤ n) :
    (Uprod m n * Fprod m n) 0 1 = (fSP (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ) := by
  rw [UF_eq_double m n hn, ← fSP_eval_nat]

lemma Sprod_det_factor (m s : ℕ) :
    (Sprod m s).det =
      (-1 : ℝ) ^ m *
        ((Finset.range m).prod (fun i => alpha1 ((s + i : ℕ) : ℝ))) *
        ((Finset.range m).prod (fun i => alpha1 (-((s + i : ℕ) : ℝ)))) := by
  rw [Sprod_det]
  calc
    (Finset.range m).prod (fun i =>
        -alpha1 ((s + i : ℕ) : ℝ) * alpha1 (-((s + i : ℕ) : ℝ)))
      = (Finset.range m).prod (fun i =>
          (-1 : ℝ) * (alpha1 ((s + i : ℕ) : ℝ) *
            alpha1 (-((s + i : ℕ) : ℝ)))) := by
        refine Finset.prod_congr rfl ?_
        intro i _; ring
    _ = (Finset.range m).prod (fun _ => (-1 : ℝ)) *
          (Finset.range m).prod (fun i =>
            alpha1 ((s + i : ℕ) : ℝ) * alpha1 (-((s + i : ℕ) : ℝ))) := by
        rw [Finset.prod_mul_distrib]
    _ = (-1 : ℝ) ^ m *
          ((Finset.range m).prod (fun i => alpha1 ((s + i : ℕ) : ℝ)) *
            (Finset.range m).prod (fun i =>
              alpha1 (-((s + i : ℕ) : ℝ)))) := by
        rw [Finset.prod_const, Finset.card_range, Finset.prod_mul_distrib]
    _ = (-1 : ℝ) ^ m *
          (Finset.range m).prod (fun i => alpha1 ((s + i : ℕ) : ℝ)) *
          (Finset.range m).prod (fun i => alpha1 (-((s + i : ℕ) : ℝ))) := by
        ring

noncomputable def avec0 : Fin 2 → ℝ := ![1, -4]

lemma alpha1_zero : alpha1 0 = 2 := by unfold alpha1; norm_num
lemma beta1_zero : beta1 0 = 12 := by unfold beta1; norm_num

lemma Smat_zero_mulVec :
    Matrix.mulVec (Smat 0) avec0 = alpha1 0 • avec 1 := by
  ext i
  fin_cases i <;>
    simp [Smat, avec0, avec, mulVec_fin2, Pi.smul_apply, alpha1_zero, beta1_zero,
      A103885_zero, A103885_one] <;> norm_num

lemma Sprod_mulVec_from_zero {k : ℕ} (hk : 1 ≤ k) :
    Matrix.mulVec (Sprod k 0) avec0 =
      ((Finset.range k).prod (fun i => alpha1 (i : ℝ))) • avec k := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      rw [Sprod_succ, Sprod_zero]
      simpa [Finset.prod_range_one, add_zero] using Smat_zero_mulVec
    | succ k =>
      have ih' := ih (by omega)
      rw [Sprod_succ, ← Matrix.mulVec_mulVec, ih', Matrix.mulVec_smul]
      have hidx : ((0 + (k + 1) : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) := by simp
      rw [hidx]
      have hS := Smat_mulVec (k + 1) (by omega)
      rw [hS]
      simp [Finset.prod_range_succ, smul_smul, mul_comm]

lemma Sprod_det_zero_start {m : ℕ} (hm : 2 ≤ m) : (Sprod m 0).det = 0 := by
  rw [Sprod_det]
  refine Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : 1 < m)) ?_
  have hα : alpha1 (-(1 : ℝ)) = 0 := by
    unfold alpha1; norm_num
  simp [hα]

lemma pab_ne_zero_of_two {m n : ℕ} :
    (Finset.range m).prod (fun i => alpha1 ((m * (n - 1) + i : ℕ) : ℝ)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _hi
  exact alpha1_nat_ne_zero _

lemma KF_eval_pos_start {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (knownFactor (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ) ≠ 0 := by
  rw [knownFactor_eval]
  refine mul_ne_zero ?_ ?_
  · have hs : 2 ≤ m * (n - 1) := by
      have : 1 ≤ n - 1 := by omega
      exact Nat.mul_le_mul hm this
    exact alpha1_neg_of_ge_two hs
  · refine Finset.prod_ne_zero_iff.mpr ?_
    intro j _hj
    convert P1_eval_int_ne_zero
      (-((m * (n - 1) : ℕ) : ℤ) - (j : ℤ)) using 2
    rw [Int.cast_sub, Int.cast_neg]
    simp

lemma KF_eval_zero_ne {m : ℕ} :
    (knownFactor m).eval (0 : ℝ) ≠ 0 := by
  rw [knownFactor_eval]
  refine mul_ne_zero ?_ ?_
  · simpa using alpha1_nat_ne_zero 0
  · refine Finset.prod_ne_zero_iff.mpr ?_
    intro j _hj
    simpa using P1_eval_neg_int_ne_zero j

lemma prod_minus_zero_one (m : ℕ) (hm : 1 ≤ m) :
    prod_factor_minus m 1 = 0 := by
  unfold prod_factor_minus product_indices
  refine Finset.prod_eq_zero (Finset.mem_Ioc.mpr ⟨by omega, le_rfl⟩) ?_
  simp

lemma cast_mn_split {m n : ℕ} (hn : 1 ≤ n) :
    ((m * n : ℕ) : ℝ) = ((m * (n - 1) : ℕ) : ℝ) + (m : ℝ) := by
  have hsucc : (n - 1).succ = n := Nat.succ_pred_eq_of_pos hn
  have h : m * n = m * (n - 1) + m := by
    calc
      m * n = m * (n - 1).succ := by rw [hsucc]
      _ = m * (n - 1) + m := Nat.mul_succ _ _
  rw [h, Nat.cast_add]

lemma Ioc_zero_card (t : ℕ) : (Finset.Ioc 0 t).card = t := by
  simp [Nat.card_Ioc]

lemma Ioc_extend_two (t : ℕ) :
    Finset.Ioc 0 (t + 2) = Finset.Ioc 0 t ∪ {t + 1, t + 2} := by
  ext k
  simp only [Finset.mem_Ioc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  omega

lemma Ioc_insert_two_disjoint (t : ℕ) :
    Disjoint (Finset.Ioc 0 t) ({t + 1, t + 2} : Finset ℕ) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx hx'
  have hx0 := Finset.mem_Ioc.mp hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
  omega

lemma pair_prod (a b : ℕ) (h : a ≠ b) (f : ℕ → ℝ) :
    ({a, b} : Finset ℕ).prod f = f a * f b := by
  rw [Finset.prod_insert (by simp [h]), Finset.prod_singleton]

lemma prod_Ioc_extend (t : ℕ) (x : ℝ) :
    (x + ((t + 1 : ℕ) : ℝ)) * (x + ((t + 2 : ℕ) : ℝ)) *
      (Finset.Ioc 0 t).prod (fun k => x + (k : ℝ)) =
    (Finset.Ioc 0 (t + 2)).prod (fun k => x + (k : ℝ)) := by
  have hU := Ioc_extend_two t
  have hD := Ioc_insert_two_disjoint t
  rw [hU, Finset.prod_union hD, pair_prod (t + 1) (t + 2) (by omega)]
  ring

lemma range_split_add (a b : ℕ) :
    Finset.range (a + b) =
      Finset.range a ∪ (Finset.range b).image (fun j => a + j) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image]
  constructor
  · intro hx
    by_cases h : x < a
    · exact Or.inl h
    · refine Or.inr ⟨x - a, by omega, by omega⟩
  · intro h
    rcases h with h | ⟨i, hi, rfl⟩ <;> omega

lemma range_image_disjoint (a b : ℕ) :
    Disjoint (Finset.range a) ((Finset.range b).image (fun j => a + j)) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hx hx'
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx'
  have : a + i < a := Finset.mem_range.mp hx
  omega

lemma injOn_add_left (a : ℕ) (s : Finset ℕ) :
    Set.InjOn (fun j : ℕ => a + j) s := by
  intro x _ y _ h
  have h' : a + x = a + y := h
  omega

lemma prod_minus_neg_form (m n : ℕ) :
    prod_factor_minus m n =
      (Finset.Ioc 0 (2 * m)).prod (fun k => -((2 : ℝ) * ((m * n : ℕ) : ℝ)) + (k : ℝ)) := by
  unfold prod_factor_minus product_indices
  have h :
      (Finset.Ioc 0 (2 * m)).prod (fun k => (2 * m * n : ℝ) - k) =
        (Finset.Ioc 0 (2 * m)).prod
          (fun k => -(-((2 : ℝ) * ((m * n : ℕ) : ℝ)) + (k : ℝ))) := by
    refine Finset.prod_congr rfl ?_
    intro k _hk
    push_cast
    ring
  rw [h, Finset.prod_neg, Ioc_zero_card]
  have : (-1 : ℝ) ^ (2 * m) = 1 := by
    rw [pow_mul, neg_one_sq, one_pow]
  rw [this, one_mul]

lemma P1_prod_identity_neg {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n) :
    (Finset.range (m - 1)).prod
        (fun j => P1.eval (-((m * n : ℕ) : ℝ) - (j : ℝ))) *
      (Finset.range m).prod
        (fun i => P1.eval (-((m * (n - 1) + i : ℕ) : ℝ))) =
      (Finset.range (2 * m - 1)).prod
        (fun j => P1.eval (-((m * (n - 1) : ℕ) : ℝ) - (j : ℝ))) := by
  have hsum : 2 * m - 1 = m + (m - 1) := by omega
  have hsplit := range_split_add m (m - 1)
  have hdisj := range_image_disjoint m (m - 1)
  have hR :
      (Finset.range (2 * m - 1)).prod
        (fun j => P1.eval (-((m * (n - 1) : ℕ) : ℝ) - (j : ℝ))) =
      (Finset.range m).prod
          (fun i => P1.eval (-((m * (n - 1) : ℕ) : ℝ) - (i : ℝ))) *
        (Finset.range (m - 1)).prod
          (fun j => P1.eval (-((m * (n - 1) : ℕ) : ℝ) - ((m + j : ℕ) : ℝ))) := by
    rw [hsum, hsplit, Finset.prod_union hdisj,
      Finset.prod_image (injOn_add_left m _)]
  have hcast := cast_mn_split (m := m) hn
  have hL1 :
      (Finset.range (m - 1)).prod
        (fun j => P1.eval (-((m * n : ℕ) : ℝ) - (j : ℝ))) =
      (Finset.range (m - 1)).prod
        (fun j => P1.eval (-((m * (n - 1) : ℕ) : ℝ) - ((m + j : ℕ) : ℝ))) := by
    refine Finset.prod_congr rfl ?_
    intro j _hj
    refine congrArg (fun t => P1.eval t) ?_
    have : ((m + j : ℕ) : ℝ) = (m : ℝ) + (j : ℝ) := by push_cast; ring
    rw [hcast, this]
    ring
  have hL2 :
      (Finset.range m).prod
        (fun i => P1.eval (-((m * (n - 1) + i : ℕ) : ℝ))) =
      (Finset.range m).prod
        (fun i => P1.eval (-((m * (n - 1) : ℕ) : ℝ) - (i : ℝ))) := by
    refine Finset.prod_congr rfl ?_
    intro i _hi
    refine congrArg (fun t => P1.eval t) ?_
    push_cast
    ring
  rw [hL1, hL2, hR]
  ring

/-- Both sides equal `∏_{k=1}^{2m+2} (-2mn + k)`. -/
lemma lin_prod_identity_neg {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n) :
    ((2 : ℝ) * (-((m * n : ℕ) : ℝ)) + 1) *
        ((2 : ℝ) * (-((m * n : ℕ) : ℝ)) + 2) *
      (Finset.range m).prod (fun i =>
        ((2 : ℝ) * (-((m * (n - 1) + i : ℕ) : ℝ)) + 1) *
          ((2 : ℝ) * (-((m * (n - 1) + i : ℕ) : ℝ)) + 2)) =
      ((2 : ℝ) * (-((m * (n - 1) : ℕ) : ℝ)) + 1) *
        ((2 : ℝ) * (-((m * (n - 1) : ℕ) : ℝ)) + 2) *
        prod_factor_minus m n := by
  set x : ℝ := -((2 : ℝ) * ((m * n : ℕ) : ℝ))
  have hLHS0 :
      ((2 : ℝ) * (-((m * n : ℕ) : ℝ)) + 1) *
          ((2 : ℝ) * (-((m * n : ℕ) : ℝ)) + 2) =
        (x + (1 : ℕ)) * (x + (2 : ℕ)) := by
    unfold x
    push_cast
    ring
  -- Reindex: -2(s+i)+1 = x + 2(m-i)+1
  have hrange :
      (Finset.range m).prod (fun i =>
        ((2 : ℝ) * (-((m * (n - 1) + i : ℕ) : ℝ)) + 1) *
          ((2 : ℝ) * (-((m * (n - 1) + i : ℕ) : ℝ)) + 2)) =
      (Finset.range m).prod (fun i =>
        (x + ((2 * (m - i) + 1 : ℕ) : ℝ)) *
          (x + ((2 * (m - i) + 2 : ℕ) : ℝ))) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have hsi : ((m * (n - 1) + i : ℕ) : ℝ) =
        ((m * n : ℕ) : ℝ) - (m : ℝ) + (i : ℝ) := by
      have h := cast_mn_split (m := m) hn
      rw [Nat.cast_add]
      linarith
    have hm_i : ((m - i : ℕ) : ℝ) = (m : ℝ) - (i : ℝ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hi')]
    have e1 : (2 : ℝ) * (-((m * (n - 1) + i : ℕ) : ℝ)) + 1 =
        x + ((2 * (m - i) + 1 : ℕ) : ℝ) := by
      rw [hsi]
      unfold x
      push_cast
      rw [hm_i]
      ring
    have e2 : (2 : ℝ) * (-((m * (n - 1) + i : ℕ) : ℝ)) + 2 =
        x + ((2 * (m - i) + 2 : ℕ) : ℝ) := by
      rw [hsi]
      unfold x
      push_cast
      rw [hm_i]
      ring
    rw [e1, e2]
  -- j = m - i runs through 1..m
  have hreindex :
      (Finset.range m).prod (fun i =>
        (x + ((2 * (m - i) + 1 : ℕ) : ℝ)) *
          (x + ((2 * (m - i) + 2 : ℕ) : ℝ))) =
      (Finset.Icc 1 m).prod (fun j =>
        (x + ((2 * j + 1 : ℕ) : ℝ)) * (x + ((2 * j + 2 : ℕ) : ℝ))) := by
    refine Finset.prod_nbij' (fun i => m - i) (fun j => m - j) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      have hi' : i < m := Finset.mem_range.mp hi
      have : 1 ≤ m - i ∧ m - i ≤ m := by omega
      exact Finset.mem_Icc.mpr this
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      have : m - j < m := by omega
      exact Finset.mem_range.mpr this
    · intro i hi
      have hi' : i < m := Finset.mem_range.mp hi
      exact Nat.sub_sub_self (Nat.le_of_lt hi')
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      exact Nat.sub_sub_self hj'.2
    · intro i _hi
      rfl
  have hdisj0 : Disjoint ({0} : Finset ℕ) (Finset.Icc 1 m) := by
    refine Finset.disjoint_left.mpr ?_
    intro j hj hj'
    simp only [Finset.mem_singleton] at hj
    have := (Finset.mem_Icc.mp hj').1
    omega
  have hfull :
      (x + (1 : ℕ)) * (x + (2 : ℕ)) *
        (Finset.Icc 1 m).prod (fun j =>
          (x + ((2 * j + 1 : ℕ) : ℝ)) * (x + ((2 * j + 2 : ℕ) : ℝ))) =
      (Finset.Icc 0 m).prod (fun j =>
        (x + ((2 * j + 1 : ℕ) : ℝ)) * (x + ((2 * j + 2 : ℕ) : ℝ))) := by
    have : Finset.Icc 0 m = ({0} : Finset ℕ) ∪ Finset.Icc 1 m := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
      omega
    rw [this, Finset.prod_union hdisj0]
    simp
  have hIcc_range : Finset.Icc 0 m = Finset.range (m + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  have hpair :
      (Finset.Icc 0 m).prod (fun j =>
        (x + ((2 * j + 1 : ℕ) : ℝ)) * (x + ((2 * j + 2 : ℕ) : ℝ))) =
      (Finset.Ioc 0 (2 * m + 2)).prod (fun k => x + (k : ℝ)) := by
    rw [hIcc_range]
    have : 2 * (m + 1) = 2 * m + 2 := by omega
    simpa [this] using prod_pair_Ioc (m + 1) x
  -- RHS
  have hs : ((m * (n - 1) : ℕ) : ℝ) = ((m * n : ℕ) : ℝ) - (m : ℝ) := by
    linarith [cast_mn_split (m := m) hn]
  have hRlin :
      ((2 : ℝ) * (-((m * (n - 1) : ℕ) : ℝ)) + 1) *
          ((2 : ℝ) * (-((m * (n - 1) : ℕ) : ℝ)) + 2) =
        (x + ((2 * m + 1 : ℕ) : ℝ)) * (x + ((2 * m + 2 : ℕ) : ℝ)) := by
    rw [hs]
    unfold x
    push_cast
    ring
  have hRm :
      prod_factor_minus m n =
        (Finset.Ioc 0 (2 * m)).prod (fun k => x + (k : ℝ)) := by
    simpa [x] using (prod_minus_neg_form m n)
  have hRfull :
      (x + ((2 * m + 1 : ℕ) : ℝ)) * (x + ((2 * m + 2 : ℕ) : ℝ)) *
        (Finset.Ioc 0 (2 * m)).prod (fun k => x + (k : ℝ)) =
      (Finset.Ioc 0 (2 * m + 2)).prod (fun k => x + (k : ℝ)) :=
    prod_Ioc_extend (2 * m) x
  calc
    ((2 : ℝ) * (-((m * n : ℕ) : ℝ)) + 1) *
        ((2 : ℝ) * (-((m * n : ℕ) : ℝ)) + 2) *
      (Finset.range m).prod (fun i =>
        ((2 : ℝ) * (-((m * (n - 1) + i : ℕ) : ℝ)) + 1) *
          ((2 : ℝ) * (-((m * (n - 1) + i : ℕ) : ℝ)) + 2))
      = (x + (1 : ℕ)) * (x + (2 : ℕ)) *
          (Finset.Icc 1 m).prod (fun j =>
            (x + ((2 * j + 1 : ℕ) : ℝ)) * (x + ((2 * j + 2 : ℕ) : ℝ))) := by
        rw [hLHS0, hrange, hreindex]
    _ = (Finset.Ioc 0 (2 * m + 2)).prod (fun k => x + (k : ℝ)) := by
        rw [hfull, hpair]
    _ = ((2 : ℝ) * (-((m * (n - 1) : ℕ) : ℝ)) + 1) *
          ((2 : ℝ) * (-((m * (n - 1) : ℕ) : ℝ)) + 2) *
          prod_factor_minus m n := by
        rw [hRlin, hRm, hRfull]

lemma knownFactor_mul_P1 {m : ℕ} (x : ℝ) (hm : 2 ≤ m) :
    (knownFactor m).eval x * P1.eval (-x) =
      alpha1 (-x) *
        (Finset.range (m - 1)).prod (fun j => P1.eval (-x - (j : ℝ))) := by
  rw [knownFactor_eval, pred_pred_eq]
  have hrange : Finset.range (m - 1) = insert 0 (Finset.Icc 1 (m - 2)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hdisj : (0 : ℕ) ∉ Finset.Icc 1 (m - 2) := by
    simp [Finset.mem_Icc]
  have hprod :
      (Finset.range (m - 1)).prod (fun j => P1.eval (-x - (j : ℝ))) =
        P1.eval (-x) *
          (Finset.Icc 1 (m - 2)).prod (fun j => P1.eval (-x - (j : ℝ))) := by
    rw [hrange, Finset.prod_insert hdisj]
    simp
  rw [hprod]
  ring

lemma knownFactor_double_mul_P1 {m : ℕ} (x : ℝ) (hm : 2 ≤ m) :
    (knownFactor (2 * m)).eval x * P1.eval (-x) =
      alpha1 (-x) *
        (Finset.range (2 * m - 1)).prod (fun j => P1.eval (-x - (j : ℝ))) := by
  have hm2 : 2 ≤ 2 * m := by omega
  have := knownFactor_mul_P1 (m := 2 * m) x hm2
  simpa using this

lemma Id2_core {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n) :
    (knownFactor m).eval ((m * n : ℕ) : ℝ) *
      (Finset.range m).prod
        (fun i => alpha1 (-((m * (n - 1) + i : ℕ) : ℝ))) =
      (knownFactor (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ) *
        prod_factor_minus m n := by
  set s : ℕ := m * (n - 1)
  set mn : ℕ := m * n
  have hPmn : P1.eval (-(mn : ℝ)) ≠ 0 := P1_eval_neg_int_ne_zero _
  have hPs : P1.eval (-(s : ℝ)) ≠ 0 := P1_eval_neg_int_ne_zero _
  have hα :
      (Finset.range m).prod (fun i => alpha1 (-((s + i : ℕ) : ℝ))) =
        (Finset.range m).prod (fun i =>
          ((2 : ℝ) * (-((s + i : ℕ) : ℝ)) + 1) *
            ((2 : ℝ) * (-((s + i : ℕ) : ℝ)) + 2)) *
        (Finset.range m).prod (fun i => P1.eval (-((s + i : ℕ) : ℝ))) := by
    simp_rw [alpha1_eq_lin_P1]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hKFmn := knownFactor_mul_P1 (x := (mn : ℝ)) hm
  have hKFs := knownFactor_double_mul_P1 (x := (s : ℝ)) hm
  have hαmn : alpha1 (-(mn : ℝ)) =
      ((2 : ℝ) * (-(mn : ℝ)) + 1) * ((2 : ℝ) * (-(mn : ℝ)) + 2) *
        P1.eval (-(mn : ℝ)) := by
    rw [alpha1_eq_lin_P1]
  have hαs : alpha1 (-(s : ℝ)) =
      ((2 : ℝ) * (-(s : ℝ)) + 1) * ((2 : ℝ) * (-(s : ℝ)) + 2) *
        P1.eval (-(s : ℝ)) := by
    rw [alpha1_eq_lin_P1]
  have hlin' : ((2 : ℝ) * (-(mn : ℝ)) + 1) * ((2 : ℝ) * (-(mn : ℝ)) + 2) *
      (Finset.range m).prod (fun i =>
        ((2 : ℝ) * (-((s + i : ℕ) : ℝ)) + 1) *
          ((2 : ℝ) * (-((s + i : ℕ) : ℝ)) + 2)) =
    ((2 : ℝ) * (-(s : ℝ)) + 1) * ((2 : ℝ) * (-(s : ℝ)) + 2) *
      prod_factor_minus m n := by
    simpa [s, mn] using lin_prod_identity_neg hm hn
  have hP' :
      (Finset.range (m - 1)).prod (fun j => P1.eval (-(mn : ℝ) - (j : ℝ))) *
        (Finset.range m).prod (fun i => P1.eval (-((s + i : ℕ) : ℝ))) =
      (Finset.range (2 * m - 1)).prod
        (fun j => P1.eval (-(s : ℝ) - (j : ℝ))) := by
    simpa [s, mn] using P1_prod_identity_neg hm hn
  have hKFs' :
      ((2 : ℝ) * (-(s : ℝ)) + 1) * ((2 : ℝ) * (-(s : ℝ)) + 2) *
        (Finset.range (2 * m - 1)).prod
          (fun j => P1.eval (-(s : ℝ) - (j : ℝ))) =
      (knownFactor (2 * m)).eval (s : ℝ) := by
    apply mul_left_cancel₀ hPs
    have := hKFs
    rw [hαs] at this
    linarith
  have hKF' : (knownFactor m).eval (mn : ℝ) =
      ((2 : ℝ) * (-(mn : ℝ)) + 1) * ((2 : ℝ) * (-(mn : ℝ)) + 2) *
        (Finset.range (m - 1)).prod (fun j => P1.eval (-(mn : ℝ) - (j : ℝ))) := by
    apply mul_left_cancel₀ hPmn
    convert hKFmn using 1
    · ring
    · rw [hαmn]; ring
  have hL :
      (knownFactor m).eval (mn : ℝ) *
        (Finset.range m).prod (fun i => alpha1 (-((s + i : ℕ) : ℝ))) =
      (((2 : ℝ) * (-(mn : ℝ)) + 1) * ((2 : ℝ) * (-(mn : ℝ)) + 2) *
        (Finset.range m).prod (fun i =>
          ((2 : ℝ) * (-((s + i : ℕ) : ℝ)) + 1) *
            ((2 : ℝ) * (-((s + i : ℕ) : ℝ)) + 2))) *
      ((Finset.range (m - 1)).prod (fun j => P1.eval (-(mn : ℝ) - (j : ℝ))) *
        (Finset.range m).prod (fun i => P1.eval (-((s + i : ℕ) : ℝ)))) := by
    rw [hKF', hα]
    ring
  have hR :
      (knownFactor (2 * m)).eval (s : ℝ) * prod_factor_minus m n =
      (((2 : ℝ) * (-(s : ℝ)) + 1) * ((2 : ℝ) * (-(s : ℝ)) + 2) *
        prod_factor_minus m n) *
      (Finset.range (2 * m - 1)).prod
        (fun j => P1.eval (-(s : ℝ) - (j : ℝ))) := by
    rw [← hKFs']
    ring
  rw [hL, hR, hlin', hP']

lemma sub_four_of_mul (x y z : ℝ) (h : x + -(y * 4) = z) : x - 4 * y = z := by
  linear_combination h

lemma det_rel_four (A B C D a b p : ℝ)
    (h0 : A - 4 * C = p * a)
    (h1 : B - 4 * D = p * b)
    (hdet : A * D - C * B = 0) (hp : p ≠ 0) :
    C * b = D * a := by
  apply mul_left_cancel₀ hp
  have ha : p * a = A - 4 * C := h0.symm
  have hb : p * b = B - 4 * D := h1.symm
  calc
    p * (C * b) = C * (p * b) := by ring
    _ = C * (B - 4 * D) := by rw [hb]
    _ = C * B - 4 * C * D := by ring
    _ = A * D - 4 * C * D := by linear_combination -hdet
    _ = D * (A - 4 * C) := by ring
    _ = D * (p * a) := by rw [ha]
    _ = p * (D * a) := by ring

lemma elim_mid (U00 U01 F01 F11 a b c paf : ℝ)
    (hU : U00 * a + U01 * b = paf * c)
    (hrel : F01 * b = F11 * a) :
    F01 * paf * c = (U00 * F01 + U01 * F11) * a := by
  calc
    F01 * paf * c = F01 * (paf * c) := by rw [mul_assoc]
    _ = F01 * (U00 * a + U01 * b) := by rw [hU]
    _ = F01 * U00 * a + F01 * U01 * b := by ring
    _ = U00 * F01 * a + U01 * (F01 * b) := by ring
    _ = U00 * F01 * a + U01 * (F11 * a) := by rw [hrel]
    _ = (U00 * F01 + U01 * F11) * a := by ring

lemma rec_combine (s pp pm q ap am a : ℝ)
    (h : s * pp * ap + s * pm * am = s * q * a) :
    s * (pp * ap + pm * am - q * a) = 0 := by
  linear_combination h

lemma prod_alpha_add_cast (m : ℕ) :
    (Finset.range m).prod (fun i => alpha1 ((m + i : ℕ) : ℝ)) =
      (Finset.range m).prod (fun i => alpha1 ((m : ℝ) + (i : ℝ))) := by
  refine Finset.prod_congr rfl ?_
  intro i _hi
  congr 1
  push_cast
  ring

lemma recurrence_n_one {m : ℕ} (hm : 2 ≤ m) :
    prod_factor_plus m 1 * (Ppoly m).eval (1 : ℝ) *
        A103885_subsequence_real m 2 +
      ((-1 : ℝ) ^ m * prod_factor_minus m 1 * (Ppoly m).eval (-(1 : ℝ))) *
        A103885_subsequence_real m 0 =
      (Qpoly m).eval ((1 : ℝ) ^ 2) * A103885_subsequence_real m 1 := by
  unfold A103885_subsequence_real
  have hminus0 : prod_factor_minus m 1 = 0 := prod_minus_zero_one m (by omega)
  simp only [hminus0, mul_zero, zero_mul, add_zero]
  have hP1 : (Ppoly m).eval (1 : ℝ) = (Gpoly m).eval (0 : ℝ) := by
    rw [Ppoly_eval]; ring
  have hQ1 : (Qpoly m).eval ((1 : ℝ) ^ 2) = (Gpoly (2 * m)).eval (0 : ℝ) := by
    simpa using Qpoly_eval_sq_of_pos hm (by omega : 1 ≤ 1)
  rw [hP1, hQ1]
  -- reduce to prod_plus * G(0) * a(2m) = G_{2m}(0) * a(m)
  have hidx1 : (m * 2 : ℕ) = 2 * m := by ring
  have hidx2 : (m * 1 : ℕ) = m := by ring
  simp [hidx1, hidx2]
  have hf0 : (fSP m).eval (0 : ℝ) = (knownFactor m).eval 0 * (Gpoly m).eval 0 :=
    (Gpoly_eval m 0).symm
  have hf20 : (fSP (2 * m)).eval (0 : ℝ) =
      (knownFactor (2 * m)).eval 0 * (Gpoly (2 * m)).eval 0 :=
    (Gpoly_eval (2 * m) 0).symm
  have hKF := knownFactor_double_eval hm (0 : ℝ)
  have hP1prod := P1_prod_identity (m := m) (n := 1) hm (by omega)
  have hpab0 : (Finset.range m).prod (fun i => alpha1 (i : ℝ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro i _hi; exact alpha1_nat_ne_zero i
  have hF := Sprod_mulVec_from_zero (k := m) (by omega)
  have hU := Uprod_mulVec m 1 (by omega) (by omega)
  have hFdet : (Fprod m 1).det = 0 := by
    simpa [Fprod] using Sprod_det_zero_start hm
  have hpaf_cast := prod_alpha_add_cast m
  have hU0 :
      Uprod m 1 0 0 * (A103885 m : ℝ) + Uprod m 1 0 1 * (A103885 (m - 1) : ℝ) =
        (Finset.range m).prod (fun i => alpha1 ((m + i : ℕ) : ℝ)) *
          (A103885 (2 * m) : ℝ) := by
    have := congrArg (fun v : Fin 2 → ℝ => v 0) hU
    simp [avec, mulVec_fin2, Pi.smul_apply] at this
    -- this : U00 * a(m) + U01 * a(m-1) = (∏ α(↑m+↑i)) * a(m*2)
    have hcast : (Finset.range m).prod (fun i => alpha1 ((m : ℝ) + (i : ℝ))) =
        (Finset.range m).prod (fun i => alpha1 ((m + i : ℕ) : ℝ)) := hpaf_cast.symm
    have h2 : (m * 2 : ℕ) = 2 * m := by ring
    rw [hcast, h2] at this
    exact this
  have hF0' :
      Fprod m 1 0 0 - 4 * Fprod m 1 0 1 =
        (Finset.range m).prod (fun i => alpha1 (i : ℝ)) * (A103885 m : ℝ) := by
    have h0 := congrArg (fun v : Fin 2 → ℝ => v 0) hF
    have h0' : Sprod m 0 0 0 * avec0 0 + Sprod m 0 0 1 * avec0 1 =
        ((Finset.range m).prod (fun i => alpha1 (i : ℝ))) * avec m 0 := by
      simpa [mulVec_fin2, Pi.smul_apply] using h0
    simp [avec0, avec] at h0'
    have hEq : Sprod m 0 = Fprod m 1 := rfl
    rw [hEq] at h0'
    exact sub_four_of_mul _ _ _ h0'
  have hF1' :
      Fprod m 1 1 0 - 4 * Fprod m 1 1 1 =
        (Finset.range m).prod (fun i => alpha1 (i : ℝ)) * (A103885 (m - 1) : ℝ) := by
    have h1 := congrArg (fun v : Fin 2 → ℝ => v 1) hF
    have h1' : Sprod m 0 1 0 * avec0 0 + Sprod m 0 1 1 * avec0 1 =
        ((Finset.range m).prod (fun i => alpha1 (i : ℝ))) * avec m 1 := by
      simpa [mulVec_fin2, Pi.smul_apply] using h1
    simp [avec0, avec] at h1'
    have hEq : Sprod m 0 = Fprod m 1 := rfl
    rw [hEq] at h1'
    exact sub_four_of_mul _ _ _ h1'
  have hUF :
      (Uprod m 1 * Fprod m 1) 0 1 =
        Uprod m 1 0 0 * Fprod m 1 0 1 + Uprod m 1 0 1 * Fprod m 1 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hrel :
      Fprod m 1 0 1 * (A103885 (m - 1) : ℝ) =
        Fprod m 1 1 1 * (A103885 m : ℝ) :=
    det_rel_four (Fprod m 1 0 0) (Fprod m 1 1 0) (Fprod m 1 0 1)
      (Fprod m 1 1 1) (A103885 m : ℝ) (A103885 (m - 1) : ℝ)
      ((Finset.range m).prod (fun i => alpha1 (i : ℝ))) hF0' hF1'
      (by simpa [Matrix.det_fin_two] using hFdet) hpab0
  have hmul :
      Fprod m 1 0 1 *
          (Finset.range m).prod (fun i => alpha1 ((m + i : ℕ) : ℝ)) *
          (A103885 (2 * m) : ℝ) =
        (Uprod m 1 * Fprod m 1) 0 1 * (A103885 m : ℝ) := by
    have := elim_mid (Uprod m 1 0 0) (Uprod m 1 0 1) (Fprod m 1 0 1)
      (Fprod m 1 1 1) (A103885 m : ℝ) (A103885 (m - 1) : ℝ)
      (A103885 (2 * m) : ℝ)
      ((Finset.range m).prod (fun i => alpha1 ((m + i : ℕ) : ℝ)))
      hU0 hrel
    rw [hUF]
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hF01 : Fprod m 1 0 1 = (fSP m).eval (0 : ℝ) := by
    simpa [Fprod] using Fprod_01 m 1
  have hUF01 : (Uprod m 1 * Fprod m 1) 0 1 = (fSP (2 * m)).eval (0 : ℝ) := by
    simpa using UF_01 m 1 (by omega)
  have hsimp : (fSP m).eval 0 *
      (Finset.range m).prod (fun i => alpha1 ((m + i : ℕ) : ℝ)) *
      (A103885 (2 * m) : ℝ) =
    (fSP (2 * m)).eval 0 * (A103885 m : ℝ) := by
    simpa [hF01, hUF01] using hmul
  have hpaf1 := paf_decomp m 1
  have hKFne : (knownFactor m).eval 0 ≠ 0 := KF_eval_zero_ne
  have hPne : ((Finset.Icc (m.pred.pred + 1) (2 * m).pred.pred).prod
      fun j => P1.eval (-(j : ℝ))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j _hj
    simpa using P1_eval_neg_int_ne_zero j
  have := hsimp
  rw [hf0, hf20] at this
  have hpaf_eq :
      (Finset.range m).prod (fun i => alpha1 ((m + i : ℕ) : ℝ)) =
        (Finset.range m).prod (fun i => alpha1 ((m * 1 + i : ℕ) : ℝ)) := by
    refine Finset.prod_congr rfl ?_
    intro i _hi
    congr 1
    simp
  rw [hpaf_eq, hpaf1] at this
  have hprodP :
      (Finset.range m).prod (fun i => P1.eval ((m * 1 + i : ℕ) : ℝ)) =
        (Finset.Icc (m.pred.pred + 1) (2 * m).pred.pred).prod
          fun j => P1.eval (-(j : ℝ)) := by
    simpa using hP1prod
  rw [hKF, hprodP] at this
  apply mul_left_cancel₀ hKFne
  apply mul_left_cancel₀ hPne
  convert this using 1
  · ring
  · ring

lemma recurrence_of_two {m n : ℕ} (hm : 2 ≤ m) (hn : 1 ≤ n) :
    prod_factor_plus m n * (Ppoly m).eval (n : ℝ) *
        A103885_subsequence_real m (n + 1) +
      ((-1 : ℝ) ^ m * prod_factor_minus m n * (Ppoly m).eval (-(n : ℝ))) *
        A103885_subsequence_real m (n - 1) =
      (Qpoly m).eval ((n : ℝ) ^ 2) * A103885_subsequence_real m n := by
  rcases eq_or_lt_of_le hn with hn1 | hn2
  · subst hn1
    simpa using recurrence_n_one hm
  · unfold A103885_subsequence_real
    have hn2' : 2 ≤ n := by omega
    have htr := transfer_three_term m n (by omega) hn2'
    set paf := (Finset.range m).prod (fun i => alpha1 ((m * n + i : ℕ) : ℝ))
    set pab := (Finset.range m).prod (fun i => alpha1 ((m * (n - 1) + i : ℕ) : ℝ))
    set U := Uprod m n
    set F := Fprod m n
    have hpaf := paf_decomp m n
    have hF01 : F 0 1 = (knownFactor m).eval ((m * (n - 1) : ℕ) : ℝ) *
        (Ppoly m).eval (n : ℝ) := by
      unfold F
      rw [Fprod_01, ← Gpoly_eval, Gpoly_eval_Ppoly_pos hn]
    have hU01 : U 0 1 = (knownFactor m).eval ((m * n : ℕ) : ℝ) *
        (Ppoly m).eval (-(n : ℝ)) := by
      unfold U
      rw [Uprod_01, ← Gpoly_eval, Gpoly_eval_Ppoly_neg hm]
    have hUF01 : (U * F) 0 1 = (knownFactor (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ) *
        (Qpoly m).eval ((n : ℝ) ^ 2) := by
      have : (U * F) 0 1 = (fSP (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ) := by
        unfold U F
        exact UF_01 m n hn
      rw [this, ← Gpoly_eval, Qpoly_eval_sq_of_pos hm hn]
    have hFdet : F.det = (-1 : ℝ) ^ m * pab *
        (Finset.range m).prod (fun i => alpha1 (-((m * (n - 1) + i : ℕ) : ℝ))) := by
      unfold F pab
      simpa [Fprod] using Sprod_det_factor m (m * (n - 1))
    have hId1 : (knownFactor m).eval ((m * (n - 1) : ℕ) : ℝ) * paf =
        (knownFactor (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ) * prod_factor_plus m n := by
      have hKF := knownFactor_double_eval hm ((m * (n - 1) : ℕ) : ℝ)
      have hP := P1_prod_identity (m := m) (n := n) hm hn
      unfold paf at hpaf ⊢
      rw [hKF, hpaf, hP]
      ring
    have hscale := KF_eval_pos_start (m := m) (n := n) hm hn2'
    have hpab0 : pab ≠ 0 := by
      unfold pab
      exact pab_ne_zero_of_two
    have hleft1 : pab * F 0 1 * paf = pab *
        (knownFactor (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ) *
        prod_factor_plus m n * (Ppoly m).eval (n : ℝ) := by
      rw [hF01]
      have := congrArg (fun t => pab * t * (Ppoly m).eval (n : ℝ)) hId1
      convert this using 1 <;> ring
    have hright : pab * (U * F) 0 1 = pab *
        (knownFactor (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ) *
        (Qpoly m).eval ((n : ℝ) ^ 2) := by
      rw [hUF01]; ring
    have hId2 : (knownFactor m).eval ((m * n : ℕ) : ℝ) * F.det =
        pab * (knownFactor (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ) *
          ((-1 : ℝ) ^ m) * prod_factor_minus m n := by
      have hcore := Id2_core (m := m) (n := n) hm hn
      rw [hFdet]
      have := congrArg (fun t => (-1 : ℝ) ^ m * pab * t) hcore
      convert this using 1 <;> ring
    have hleft2 : U 0 1 * F.det = pab *
        (knownFactor (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ) *
        ((-1 : ℝ) ^ m) * prod_factor_minus m n * (Ppoly m).eval (-(n : ℝ)) := by
      rw [hU01]
      have := congrArg (fun t => t * (Ppoly m).eval (-(n : ℝ))) hId2
      convert this using 1 <;> ring
    have htr' : pab * F 0 1 * paf * (A103885 (m * (n + 1)) : ℝ) +
        U 0 1 * F.det * (A103885 (m * (n - 1)) : ℝ) =
      pab * (F 0 1 * U 0 0 + U 0 1 * F 1 1) * (A103885 (m * n) : ℝ) := by
      simpa [paf, pab, U, F] using htr
    have hUFcomm : F 0 1 * U 0 0 + U 0 1 * F 1 1 = (U * F) 0 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
    rw [hUFcomm] at htr'
    have htr'' :
        (pab * (knownFactor (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ)) *
            (prod_factor_plus m n * (Ppoly m).eval (n : ℝ)) *
            (A103885 (m * (n + 1)) : ℝ) +
          (pab * (knownFactor (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ)) *
            ((-1 : ℝ) ^ m * prod_factor_minus m n * (Ppoly m).eval (-(n : ℝ))) *
            (A103885 (m * (n - 1)) : ℝ) =
        (pab * (knownFactor (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ)) *
          (Qpoly m).eval ((n : ℝ) ^ 2) * (A103885 (m * n) : ℝ) := by
      have := htr'
      rw [hleft1, hleft2, hright] at this
      convert this using 1 <;> ring
    have hzero := rec_combine
      (pab * (knownFactor (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ))
      (prod_factor_plus m n * (Ppoly m).eval (n : ℝ))
      ((-1 : ℝ) ^ m * prod_factor_minus m n * (Ppoly m).eval (-(n : ℝ)))
      ((Qpoly m).eval ((n : ℝ) ^ 2))
      (A103885 (m * (n + 1)) : ℝ)
      (A103885 (m * (n - 1)) : ℝ)
      (A103885 (m * n) : ℝ) htr''
    have hfac : pab * (knownFactor (2 * m)).eval ((m * (n - 1) : ℕ) : ℝ) ≠ 0 :=
      mul_ne_zero hpab0 hscale
    have hdes := (mul_eq_zero.mp hzero).resolve_left hfac
    linear_combination hdes

/--
The recurrence given below can be rewritten in the form
(2*n+1)*(2*n+2)*P(2,n)*a(n+1) - (2*n-1)*(2*n-2)*P(2,-n)*a(n-1) = Q(2,n^2)*a(n), where the polynomial Q(2,n) = 4*(55*n^2 - 34*n + 3) and the polynomial P(2,n) = 5*n^2 - 5*n + 1 satisfies the symmetry condition P(2,n) = P(2,1-n) and has real zeros.
More generally, for fixed m = 1,2,3,..., we conjecture that the sequence b(n) := a(m*n) satisfies a recurrence of the form ( Product_{k = 1..2*m} (2*m*n + k) ) * P(2*m,n)*b(n+1) + (-1)^m*( Product_{k = 1..2*m} (2*m*n - k) ) * P(2*m,-n)*b(n-1) = Q(2*m,n^2)*b(n), where the polynomials P(2*m,n) and Q(2*m,n) have degree 2*m. Conjecturally, the polynomial P(2*m,n) = P(2*m,1-n) and has real zeros in the interval [0, 1]. The 4*m zeros of the polynomial Q(2*m,n^2) seem to belong to the interval [-1, 1] and 4*m - 2 of these zeros appear to be approximated by the rational numbers +- k/(3*m), where 1 <= k <= 3*m - 2, k not a multiple of 3.
-/
theorem oeis_a103885_conjecture_0 (m : ℕ) (hm : 1 ≤ m) :
    ∃ (P Q : Polynomial ℝ),
      P.degree = (2 * m : ℕ) ∧ Q.degree = (2 * m : ℕ) ∧
      (∀ (n : ℕ) (hn : 1 ≤ n),
        (prod_factor_plus m n * P.eval (n : ℝ)) * (A103885_subsequence_real m (n + 1)) +
        ((-1 : ℝ) ^ m * prod_factor_minus m n * P.eval (-(n : ℝ))) * (A103885_subsequence_real m (n - 1)) =
        (Q.eval ((n : ℝ)^2)) * (A103885_subsequence_real m n)) ∧
      (∀ x : ℝ, P.eval x = P.eval (1 - x)) ∧
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).eval z = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc 0 1)) ∧
      (∀ z : ℂ, (Q.map (algebraMap ℝ ℂ)).eval (z^2) = 0 → z.im = 0 ∧ z.re ∈ (Set.Icc (-1) 1)) := by
  rcases eq_or_lt_of_le hm with hm1 | _hmgt
  · subst hm1
    exact ⟨P1, Q1, P1_degree, Q1_degree, m1_recurrence, P1_symmetry, P1_roots_mem,
      Q1_sq_roots_mem⟩
  · have hm2 : 2 ≤ m := by omega
    refine ⟨Ppoly m, Qpoly m, Ppoly_degree hm2, Qpoly_degree hm2, ?_, ?_, ?_, ?_⟩
    · intro n hn
      exact recurrence_of_two hm2 hn
    · exact Ppoly_symmetry hm2
    · exact Ppoly_roots_mem hm2
    · exact Qpoly_sq_roots_mem hm2
