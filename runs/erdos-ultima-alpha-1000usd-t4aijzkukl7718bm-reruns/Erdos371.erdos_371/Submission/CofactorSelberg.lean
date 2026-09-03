import FormalConjecturesUtil
import Submission.TwoLinearSelberg
import Submission.CofactorSieve

/-! Polynomial-threshold cofactor rectangle estimates from the quadratic
Selberg sieve. All counts here are unsigned. -/

namespace Erdos371CofactorSelberg

open Finset Erdos371TwoLinearSelberg Erdos371CofactorSieve
  Erdos371SieveEulerProduct Erdos371TwoLinearSieve

attribute [local instance] Classical.propDecidable

noncomputable def inputs (w a b N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun n => a ∣ n ∧ b ∣ n+1 ∧
    (n/a).Prime ∧ ((n+1)/b).Prime ∧ w ≤ n/a ∧ w ≤ (n+1)/b

lemma inputs_card_le_primeInputs {a b v : ℕ} (ha : 0<a) (hb : 0<b)
    (hab : a.Coprime b) (hv : v<a*b) (hav : a∣v) (hbv : b∣v+1)
    (w N T : ℕ) (hT : N/(a*b)+1 ≤ T) :
    (inputs w a b N).card ≤
      (primeInputs (oddPrimes w) b (v/a) a ((v+1)/b) T).card := by
  apply Finset.card_le_card_of_injOn (fun n => n/(a*b))
  · intro n hn
    change n ∈ inputs w a b N at hn
    obtain ⟨hnN, han, hbn, hp, hq, hpl, hql⟩ := Finset.mem_filter.mp hn
    have hnlt := Finset.mem_range.mp hnN
    have hforms := progression_forms ha hb hab hv hav hbv han hbn
    change n/(a*b) ∈ primeInputs (oddPrimes w) b (v/a) a ((v+1)/b) T
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hforms.1 ▸ hp, hforms.2 ▸ hq, ?_⟩
    · have hh := Nat.div_le_div_right (by omega : n≤N) (c := a*b)
      omega
    · intro p hpm
      have hh := (mem_oddPrimes.mp hpm).1
      constructor <;> omega
  · intro n hn m hm hnm
    change n ∈ inputs w a b N at hn
    change m ∈ inputs w a b N at hm
    obtain ⟨_, han, hbn, _⟩ := Finset.mem_filter.mp hn
    obtain ⟨_, ham, hbm, _⟩ := Finset.mem_filter.mp hm
    have hn := Nat.mod_add_div n (a*b)
    have hm := Nat.mod_add_div m (a*b)
    rw [progression_remainder hab hv hav hbv han hbn] at hn
    rw [progression_remainder hab hv hav hbv ham hbm] at hm
    change n/(a*b)=m/(a*b) at hnm
    rw [hnm] at hn
    omega

/-- Fixed-cofactor prime pairs are bounded by the two-linear-form sieve.
  The upper bound `T` for the progression length can be common to a box. -/
theorem inputs_card_le {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (w N T : ℕ) (hT : N/(a*b)+1 ≤ T) (hw : 2 < w) (hlarge : (4*w)^20 ≤ T) :
    (inputs w a b N).card ≤
      9*(T:ℝ)*weight (oddPrimes w) a * weight (oddPrimes w) b / (Real.log w)^2 := by
  by_cases hab : a.Coprime b
  · obtain ⟨v,hv,hav,hbv⟩ := exists_progression_origin ha hb hab
    have hc := inputs_card_le_primeInputs ha hb hab hv hav hbv w N T hT
    have hs := two_linear_selberg_upper hw (progression_determinant hav hbv) hlarge
    calc
      _ ≤ ((primeInputs (oddPrimes w) b (v/a) a ((v+1)/b) T).card:ℝ) := by exact_mod_cast hc
      _ ≤ _ := by convert hs using 1 <;> ring
  · have he : inputs w a b N = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hh := Finset.mem_filter.mp hn
      exact hab (coprime_of_consecutive_divisors hh.2.1 hh.2.2.1)
    rw [he, Finset.card_empty, Nat.cast_zero]
    apply div_nonneg
    · apply mul_nonneg
      · apply mul_nonneg (by positivity)
        exact weight_nonneg (fun p hp => oddPrimes_prime hp) a
      · exact weight_nonneg (fun p hp => oddPrimes_prime hp) b
    · positivity

noncomputable def rectangle (w A U B V N : ℕ) : Finset ℕ :=
  (Icc A U).biUnion fun a => (Icc B V).biUnion fun b => inputs w a b N

lemma rectangle_card_bound {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (w U V N T : ℕ) (hw : 2 < w) (hT : N/(A*B)+1 ≤ T) (hlarge : (4*w)^20 ≤ T) :
    (rectangle w A U B V N).card ≤
      9*(Real.exp 1)^2*(T:ℝ)*U*V/(Real.log w)^2 := by
  let s := oddPrimes w
  have hs : ∀ p ∈ s, p.Prime := fun p hp => oddPrimes_prime hp
  have hc : (rectangle w A U B V N).card ≤
      ∑ a ∈ Icc A U, ∑ b ∈ Icc B V, (inputs w a b N).card :=
    card_biUnion_le.trans (sum_le_sum (fun _ _ => card_biUnion_le))
  have hcard : (rectangle w A U B V N).card ≤
      (9*(T:ℝ)/(Real.log w)^2) *
        (∑ a ∈ Icc A U, ∑ b ∈ Icc B V, weight s a * weight s b) := by
    calc
      _ ≤ ∑ a ∈ Icc A U, ∑ b ∈ Icc B V, ((inputs w a b N).card:ℝ) := by
        exact_mod_cast hc
      _ ≤ ∑ a ∈ Icc A U, ∑ b ∈ Icc B V,
          9*(T:ℝ)*weight s a*weight s b/(Real.log w)^2 := by
        apply sum_le_sum
        intro a ha
        apply sum_le_sum
        intro b hb
        have haA := (mem_Icc.mp ha).1
        have hbB := (mem_Icc.mp hb).1
        apply inputs_card_le (hA.trans_le haA) (hB.trans_le hbB) w N T _ hw hlarge
        have hden : A*B ≤ a*b := Nat.mul_le_mul haA hbB
        have hh := Nat.div_le_div_left hden (Nat.mul_pos hA hB) (a := N)
        omega
      _ = _ := by simp only [mul_sum]; congr 1; ext a; congr 1; ext b; ring
  have hsubA : Icc A U ⊆ Icc 1 U := by
    intro a ha
    obtain ⟨ha,hb⟩ := mem_Icc.mp ha
    exact mem_Icc.mpr ⟨by omega,hb⟩
  have hsubB : Icc B V ⊆ Icc 1 V := by
    intro b hb
    obtain ⟨ha,hb⟩ := mem_Icc.mp hb
    exact mem_Icc.mpr ⟨by omega,hb⟩
  have hsum : (∑ a ∈ Icc A U, ∑ b ∈ Icc B V, weight s a*weight s b) ≤
      (Real.exp 1)^2*(U:ℝ)*V := by
    calc
      _ ≤ ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V, weight s a*weight s b := by
        apply (sum_le_sum (fun a _ =>
          sum_le_sum_of_subset_of_nonneg hsubB
            (fun b _ _ => mul_nonneg (weight_nonneg hs a) (weight_nonneg hs b)))).trans
        apply sum_le_sum_of_subset_of_nonneg hsubA
        intro a _ _
        exact sum_nonneg (fun b _ => mul_nonneg (weight_nonneg hs a) (weight_nonneg hs b))
      _ ≤ _ := weight_box_sum_le hs U V
  calc
    _ ≤ (9*(T:ℝ)/(Real.log w)^2) *
        (∑ a ∈ Icc A U, ∑ b ∈ Icc B V, weight s a*weight s b) := hcard
    _ ≤ (9*(T:ℝ)/(Real.log w)^2) * ((Real.exp 1)^2*(U:ℝ)*V) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- A dyadic rectangle has a bound independent of its aspect ratio. -/
theorem dyadic_rectangle_bound {A B N : ℕ} (hA : 0 < A) (hB : 0 < B)
    (hAB : A*B ≤ N) (w : ℕ) (hw : 2 < w) (hlarge : (4*w)^20 ≤ N/(A*B)+1) :
    (rectangle w A (2*A) B (2*B) N).card ≤
      72*(Real.exp 1)^2*(N:ℝ)/(Real.log w)^2 := by
  have hh := rectangle_card_bound hA hB w (2*A) (2*B) N (N/(A*B)+1) hw le_rfl hlarge
  have hA' : (0:ℝ) < A := Nat.cast_pos.mpr hA
  have hB' : (0:ℝ) < B := Nat.cast_pos.mpr hB
  have hdiv : ((N/(A*B)+1:ℕ):ℝ) ≤ 2*(N:ℝ)/((A:ℝ)*B) := by
    have hcast : ((N/(A*B):ℕ):ℝ) ≤ (N:ℝ)/((A:ℝ)*B) := by
      simpa using (Nat.cast_div_le (α := ℝ) (m := N) (n := A*B))
    have hunit : (1:ℝ) ≤ (N:ℝ)/((A:ℝ)*B) := by
      apply (le_div_iff₀ (by positivity)).mpr
      simpa using (Nat.cast_le.mpr hAB : ((A*B:ℕ):ℝ) ≤ N)
    push_cast
    simp only [div_eq_mul_inv] at *
    linarith
  calc
    _ ≤ 9*(Real.exp 1)^2*((N/(A*B)+1:ℕ):ℝ)*((2*A:ℕ):ℝ)*((2*B:ℕ):ℝ)/(Real.log w)^2 := hh
    _ ≤ 9*(Real.exp 1)^2*(2*(N:ℝ)/((A:ℝ)*B))*((2*A:ℕ):ℝ)*((2*B:ℕ):ℝ)/(Real.log w)^2 := by
      gcongr
    _ = _ := by push_cast; field_simp; ring

/-- Include both orientations of the dyadic cofactor rectangle, and discard
boxes whose progression length is below the chosen sieve threshold. -/
noncomputable def admissibleBox (w i j N : ℕ) : Finset ℕ :=
  if 2^i*2^j ≤ N ∧ (4*w)^20 ≤ N/(2^i*2^j)+1 then
    rectangle w (2^i) (2*2^i) (2^j) (2*2^j) N ∪
      rectangle w (2^j) (2*2^j) (2^i) (2*2^i) N
  else ∅

lemma admissibleBox_card_bound (w i j N : ℕ) (hw : 2 < w) :
    (admissibleBox w i j N).card ≤ 144*(Real.exp 1)^2*(N:ℝ)/(Real.log w)^2 := by
  unfold admissibleBox
  split_ifs with h
  · have h1 := dyadic_rectangle_bound (Nat.two_pow_pos i) (Nat.two_pow_pos j) h.1 w hw h.2
    have h2 := dyadic_rectangle_bound (Nat.two_pow_pos j) (Nat.two_pow_pos i)
      (by simpa [mul_comm] using h.1) w hw (by simpa [mul_comm] using h.2)
    have hc := Nat.cast_le (α := ℝ) |>.mpr (card_union_le
      (rectangle w (2^i) (2*2^i) (2^j) (2*2^j) N)
      (rectangle w (2^j) (2*2^j) (2^i) (2*2^i) N))
    push_cast at hc
    exact hc.trans ((add_le_add h1 h2).trans_eq (by ring))
  · simp only [card_empty, Nat.cast_zero]
    positivity

noncomputable def diagonalCover (w L t N : ℕ) : Finset ℕ :=
  (range (t+1)).biUnion fun i => (Icc i (i+L)).biUnion fun j => admissibleBox w i j N

/-- Only the number of permitted dyadic aspect ratios is lost in the sum. -/
theorem diagonalCover_card_bound (w L t N : ℕ) (hw : 2 < w) :
    (diagonalCover w L t N).card ≤
      144*(Real.exp 1)^2*(N:ℝ)*(t+1:ℕ)*(L+1:ℕ)/(Real.log w)^2 := by
  have hc : (diagonalCover w L t N).card ≤
      ∑ i ∈ range (t+1), ∑ j ∈ Icc i (i+L), (admissibleBox w i j N).card :=
    card_biUnion_le.trans (sum_le_sum (fun _ _ => card_biUnion_le))
  calc
    _ ≤ ∑ i ∈ range (t+1), ∑ j ∈ Icc i (i+L), ((admissibleBox w i j N).card:ℝ) := by
      exact_mod_cast hc
    _ ≤ ∑ i ∈ range (t+1), ∑ _j ∈ Icc i (i+L),
        144*(Real.exp 1)^2*(N:ℝ)/(Real.log w)^2 :=
      sum_le_sum (fun _ _ => sum_le_sum (fun _ _ => admissibleBox_card_bound _ _ _ _ hw))
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, Nat.card_Icc]
      have he (i : ℕ) : i+L+1-i=L+1 := by omega
      simp only [he, sum_const, card_range, nsmul_eq_mul]
      ring

end Erdos371CofactorSelberg

#print axioms Erdos371CofactorSelberg.diagonalCover_card_bound
