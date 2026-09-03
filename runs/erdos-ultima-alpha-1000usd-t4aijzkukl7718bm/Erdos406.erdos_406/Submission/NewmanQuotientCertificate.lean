import FormalConjecturesUtil

/-! Exact quotient-coefficient certificates for exclusions of particular
Newman divisors. These results do not bound arbitrary factors' degrees and
 do not settle Erdős 406. -/
namespace Erdos406Quotient
open Polynomial

noncomputable def listPoly : List ℤ → ℤ[X]
  | [] => 0
  | a :: w => C a + X * listPoly w

def addCoeffs : List ℤ → List ℤ → List ℤ
  | [], v => v
  | u, [] => u
  | a :: u, b :: v => (a + b) :: addCoeffs u v

def mulCoeffs : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: u, v => addCoeffs (v.map (a * ·)) (0 :: mulCoeffs u v)

lemma listPoly_addCoeffs (u v : List ℤ) :
    listPoly (addCoeffs u v) = listPoly u + listPoly v := by
  induction u generalizing v with
  | nil => simp [addCoeffs, listPoly]
  | cons a u ih =>
    cases v with
    | nil => simp [addCoeffs, listPoly]
    | cons b v => simp [addCoeffs, listPoly, ih]; ring

lemma listPoly_scale (a : ℤ) (v : List ℤ) :
    listPoly (v.map (a * ·)) = C a * listPoly v := by
  induction v with
  | nil => simp [listPoly]
  | cons b v ih => simp [listPoly, ih]; ring

lemma listPoly_mulCoeffs (u v : List ℤ) :
    listPoly (mulCoeffs u v) = listPoly u * listPoly v := by
  induction u with
  | nil => simp [mulCoeffs, listPoly]
  | cons a u ih =>
    rw [mulCoeffs, listPoly_addCoeffs, listPoly_scale]
    simp [listPoly, ih]; ring

lemma listPoly_monomial (m : ℕ) (a : ℤ) :
    listPoly (List.replicate m 0 ++ [a]) = monomial m a := by
  induction m with
  | zero => simp [listPoly]
  | succ m ih =>
    simp [List.replicate_succ, listPoly, ih, ← C_mul_X_pow_eq_monomial, pow_succ]
    ring

lemma listPoly_certificate (S Q E : List ℤ) (m : ℕ) (a : ℤ)
    (hc : mulCoeffs S Q = addCoeffs (List.replicate m 0 ++ [a]) E) :
    listPoly S * listPoly Q = monomial m a + listPoly E := by
  rw [← listPoly_mulCoeffs, hc, listPoly_addCoeffs, listPoly_monomial]

def weight (w : List ℤ) : ℤ := (w.map abs).sum

lemma weight_nonneg (w : List ℤ) : 0 ≤ weight w := by
  induction w with
  | nil => simp [weight]
  | cons a w ih => simp only [weight, List.map_cons, List.sum_cons]; positivity

lemma listPoly_mul_bound (w : List ℤ) (R : ℤ[X]) (M : ℤ)
    (hM : 0 ≤ M) (hR : ∀ i, |R.coeff i| ≤ M) (n : ℕ) :
    |(listPoly w * R).coeff n| ≤ weight w * M := by
  induction w generalizing n with
  | nil => simp [listPoly, weight]
  | cons a w ih =>
    have ha : |a * R.coeff n| ≤ |a| * M := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hR n) (abs_nonneg a)
    cases n with
    | zero =>
      simpa [listPoly, weight, add_mul, mul_assoc] using
        (ha.trans (by have hw : 0 ≤ (w.map abs).sum := weight_nonneg w; nlinarith))
    | succ n =>
      simpa only [listPoly, add_mul, mul_assoc, coeff_add, coeff_C_mul,
        coeff_X_mul, weight, List.map_cons, List.sum_cons] using
        (abs_add_le (a * R.coeff (n + 1)) ((listPoly w * R).coeff n)).trans
          (by have hh := ih n; simp only [weight] at hh; nlinarith)

lemma exists_max_abs_coeff (R : ℤ[X]) :
    ∃ j, ∀ i, |R.coeff i| ≤ |R.coeff j| := by
  obtain ⟨j, hj, hmax⟩ := (Finset.range (R.natDegree + 1)).exists_max_image
    (fun i => |R.coeff i|) (by simp)
  refine ⟨j, fun i => ?_⟩
  by_cases hi : i ≤ R.natDegree
  · exact hmax i (by simpa using Nat.lt_succ_of_le hi)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega : R.natDegree < i), abs_zero]
    exact abs_nonneg _

lemma quotient_bound (Q P R : ℤ[X]) (S E : List ℤ) (a : ℤ) (m : ℕ)
    (hPR : P = Q * R)
    (hcert : listPoly S * Q = monomial m a + listPoly E)
    (hP : ∀ i, |P.coeff i| ≤ 1) :
    ∀ i, (|a| - weight E) * |R.coeff i| ≤ weight S := by
  obtain ⟨j, hj⟩ := exists_max_abs_coeff R
  let M := |R.coeff j|
  have hM : 0 ≤ M := abs_nonneg _
  have hR : ∀ i, |R.coeff i| ≤ M := hj
  have hcoef : a * R.coeff j =
      (listPoly S * P).coeff (j + m) - (listPoly E * R).coeff (j + m) := by
    have he : monomial m a * R = listPoly S * P - listPoly E * R := by
      rw [hPR, ← mul_assoc, hcert]; ring
    have hh := congrArg (fun p : ℤ[X] => p.coeff (j + m)) he
    simpa only [coeff_monomial_mul, coeff_sub] using hh
  have hb : |a| * M ≤ weight S + weight E * M := by
    calc
      _ = |a * R.coeff j| := (abs_mul _ _).symm
      _ ≤ |(listPoly S * P).coeff (j + m)| + |(listPoly E * R).coeff (j + m)| := by
        rw [hcoef]; exact abs_sub _ _
      _ ≤ _ := by
        have h1 := listPoly_mul_bound S P 1 (by norm_num) hP (j + m)
        have h2 := listPoly_mul_bound E R M hM hR (j + m)
        nlinarith
  intro i
  by_cases he : 0 ≤ |a| - weight E
  · have hh := mul_le_mul_of_nonneg_left (hR i) he
    nlinarith
  · have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge he) (abs_nonneg (R.coeff i))
    exact hh.trans (weight_nonneg S)

noncomputable def qFive : ℤ[X] := 1 - 2 * X + 2 * X ^ 2 + X ^ 5

def sFive : List ℤ := [-9, -14, -12, 3, 33, 69, 85, 44, -85, -35, 31, 47, -12, -33, -6, 23, 11, -11, -12]

def eFive : List ℤ := [-9, 4, -2, -1, 3, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, -1, -4, -1, 11, -11, -12]

lemma qFive_certificate :
    listPoly sFive * qFive = monomial 9 256 + listPoly eFive := by
  simp only [sFive, eFive, qFive, listPoly, ← C_mul_X_pow_eq_monomial]
  norm_num
  ring

lemma qFive_quotient_bound (P R : ℤ[X]) (hPR : P = qFive * R)
    (hP : ∀ i, |P.coeff i| ≤ 1) : ∀ i, |R.coeff i| ≤ 2 := by
  intro i
  have hh := quotient_bound qFive P R sFive eFive 256 9 hPR qFive_certificate hP i
  norm_num [weight, sFive, eFive] at hh
  omega

/-- This degree-five polynomial has no normalized Newman multiple, of any
 degree. The proof uses an exact dominant-coefficient certificate, not a
 floating root filter or a bounded-degree search. -/
theorem qFive_not_dvd_newman (P : ℤ[X]) (h0 : P.coeff 0 = 1)
    (hP : ∀ i, P.coeff i = 0 ∨ P.coeff i = 1) : ¬ qFive ∣ P := by
  rintro ⟨R, hPR⟩
  have hb := qFive_quotient_bound P R hPR (fun i => by
    rcases hP i with h | h <;> rw [h] <;> norm_num)
  have hh (i : ℕ) : -2 ≤ R.coeff i ∧ R.coeff i ≤ 2 := abs_le.mp (hb i)
  have hcoef (i : ℕ) := congrArg (fun p : ℤ[X] => p.coeff i) hPR
  have hc0 := hcoef 0
  have hc1 := hcoef 1
  have hc2 := hcoef 2
  have hc3 := hcoef 3
  have hc4 := hcoef 4
  have hc5 := hcoef 5
  norm_num [qFive, add_mul, sub_mul, mul_assoc, coeff_X_pow_mul', coeff_X_mul] at hc0 hc1 hc2 hc3 hc4 hc5
  have h1 := hP 1
  have h2 := hP 2
  have h3 := hP 3
  have h4 := hP 4
  have h5 := hP 5
  have hb1 := hh 1
  have hb2 := hh 2
  have hb3 := hh 3
  have hb4 := hh 4
  have hb5 := hh 5
  omega

lemma ofDigits_coeff_zero_one (w : List ℕ) (hw : w ⊆ [0, 1]) (i : ℕ) :
    (Nat.ofDigits (X : ℤ[X]) w).coeff i = 0 ∨
      (Nat.ofDigits (X : ℤ[X]) w).coeff i = 1 := by
  induction w generalizing i with
  | nil => simp [Nat.ofDigits]
  | cons d w ih =>
    have hd := hw (List.mem_cons_self ..)
    have ht : w ⊆ [0, 1] := fun a ha => hw (List.mem_cons_of_mem _ ha)
    cases i with
    | zero =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl <;> simp [Nat.ofDigits]
    | succ i => simpa [Nat.ofDigits, coeff_X_mul] using ih ht i

theorem qFive_not_dvd_digits (w : List ℕ) (hw : w ⊆ [0, 1]) :
    ¬ qFive ∣ Nat.ofDigits (X : ℤ[X]) (1 :: w) := by
  apply qFive_not_dvd_newman
  · simp [Nat.ofDigits]
  · exact ofDigits_coeff_zero_one _ (by simpa using hw)

#print axioms qFive_quotient_bound
#print axioms qFive_not_dvd_newman
end Erdos406Quotient
