import Submission.LambertBoundaryClearing

/-!
An auxiliary obstruction to shortening full-period detection windows.
This is not a settlement of the conjecture in Spec.lean.
-/
namespace IncompletePhaseKernel

open Finset

lemma exists_mul_pow_lt_pow (a b c : ℕ) (hb : 0 < b) (hba : b < a) (hc : 0 < c) :
    ∃ L : ℕ, 0 < L ∧ c * b ^ L < a ^ L := by
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hr : (1 : ℚ) < (a : ℚ) / b := (one_lt_div hbQ).mpr (by exact_mod_cast hba)
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (c : ℚ) hr
  have hpos : 0 < L := by
    by_contra hn
    have hz : L = 0 := by omega
    rw [hz, pow_zero] at hL
    have : (1 : ℚ) ≤ c := by exact_mod_cast hc
    linarith
  refine ⟨L, hpos, ?_⟩
  rw [div_pow] at hL
  have h := (lt_div_iff₀ (pow_pos hbQ L)).mp hL
  exact_mod_cast h

lemma geometric_sum_le (B L : ℕ) (hB : 2 ≤ B) :
    (∑ k ∈ range L, B ^ k) ≤ B ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, pow_succ]
    have h := Nat.mul_le_mul_left (B ^ L) hB
    omega

lemma bounded_vector_modular_relation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C Q : ℕ) (hC : 0 < C)
    (hcard : C ^ Fintype.card ι < (Q + 1) ^ Fintype.card κ)
    (b : ι → κ → ℤ) :
    ∃ w : κ → ℤ, w ≠ 0 ∧ (∀ j, |w j| ≤ Q) ∧
      ∀ i, (C : ℤ) ∣ ∑ j, w j * b i j := by
  classical
  letI : NeZero C := ⟨hC.ne'⟩
  let f : (κ → Fin (Q+1)) → (ι → ZMod C) :=
    fun u i => ∑ j, (u j : ZMod C) * (b i j : ZMod C)
  have hc : Fintype.card (ι → ZMod C) < Fintype.card (κ → Fin (Q+1)) := by
    simpa using hcard
  obtain ⟨u, v, huv, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f hc
  let w : κ → ℤ := fun j => (u j : ℤ) - (v j : ℤ)
  refine ⟨w, ?_, ?_, ?_⟩
  · intro hw
    apply huv
    funext j
    apply Fin.ext
    have hj := congrFun hw j
    simp only [w, Pi.zero_apply, sub_eq_zero] at hj
    exact_mod_cast hj
  · intro j
    have hu := (u j).isLt
    have hv := (v j).isLt
    apply abs_le.mpr
    dsimp [w]
    constructor <;> omega
  · intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    simp only [w, Int.cast_sub, Int.cast_natCast, sub_mul, sum_sub_distrib]
    exact sub_eq_zero.mpr (congrFun he i)

/-- If the digit box grows faster than the geometric output grid, some
bounded nonzero digit vector annihilates all output coordinates exactly. -/
theorem bounded_geometric_kernel (d m B Q : ℕ) (hB : 2 ≤ B)
    (hgap : B ^ m < (Q+1) ^ d) (a : Fin m → Fin d → ℤ) :
    ∃ L : ℕ, 0 < L ∧ ∃ w : Fin d × Fin L → ℤ,
      w ≠ 0 ∧ (∀ j, |w j| ≤ Q) ∧
      ∀ i, ∑ j, w j * (a i j.1 * (B : ℤ) ^ j.2.val) = 0 := by
  classical
  let A : ℕ := (∑ i, ∑ j, (a i j).natAbs) + 1
  have hA : 0 < A := by dsimp [A]; omega
  have ha (i : Fin m) (j : Fin d) : |a i j| ≤ (A : ℤ) := by
    have h1 := single_le_sum (f := fun j : Fin d => (a i j).natAbs)
      (fun _ _ => Nat.zero_le _) (mem_univ j)
    have h2 := single_le_sum (f := fun i : Fin m => ∑ j, (a i j).natAbs)
      (fun _ _ => Nat.zero_le _) (mem_univ i)
    have hh : (a i j).natAbs ≤ A := by
      exact (h1.trans h2).trans (Nat.le_succ _)
    rw [← Int.natCast_natAbs]
    exact_mod_cast hh
  let C₀ : ℕ := 2 * (d*Q*A) + 1
  have hC₀ : 0 < C₀ := by dsimp [C₀]; omega
  obtain ⟨L, hL, hsize⟩ := exists_mul_pow_lt_pow ((Q+1)^d) (B^m) (C₀^m)
    (pow_pos (by omega) _) hgap (pow_pos hC₀ _)
  let C := C₀ * B^L
  have hC : 0 < C := Nat.mul_pos hC₀ (pow_pos (by omega) _)
  have hcard : C ^ Fintype.card (Fin m) <
      (Q+1) ^ Fintype.card (Fin d × Fin L) := by
    simpa only [C, mul_pow, Fintype.card_fin, Fintype.card_prod,
      ← pow_mul, Nat.mul_comm L m] using hsize
  obtain ⟨w, hw, hbound, hdiv⟩ := bounded_vector_modular_relation C Q hC hcard
    (fun i (j : Fin d × Fin L) => a i j.1 * (B : ℤ)^j.2.val)
  refine ⟨L, hL, w, hw, hbound, ?_⟩
  intro i
  have hg : (∑ k : Fin L, (B : ℤ) ^ k.val) ≤ (B : ℤ)^L := by
    exact_mod_cast (show (∑ k : Fin L, B ^ k.val) ≤ B^L from by
      simpa only [Fin.sum_univ_eq_sum_range] using geometric_sum_le B L hB)
  have hnorm : |∑ j, w j * (a i j.1 * (B : ℤ)^j.2.val)| ≤
      (d : ℤ)*Q*A*B^L := by
    calc
      _ ≤ ∑ j, |w j * (a i j.1 * (B : ℤ)^j.2.val)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin d × Fin L, (Q : ℤ)*A*B^j.2.val := by
        apply sum_le_sum
        intro j _
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (B : ℤ)^j.2.val)]
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (hbound j) (ha i j.1) (abs_nonneg _) (by positivity)) (by positivity)
      _ = (d : ℤ)*Q*A*(∑ k : Fin L, (B : ℤ)^k.val) := by
        rw [Fintype.sum_prod_type]
        simp only [← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hg (by positivity)
  have hlt : |∑ j, w j * (a i j.1 * (B : ℤ)^j.2.val)| < (C : ℤ) := by
    have hbL : (0 : ℤ) < (B : ℤ)^L := by positivity
    have ht : (0 : ℤ) ≤ (d : ℤ)*Q*A*B^L := by positivity
    dsimp [C, C₀]
    nlinarith
  exact Int.eq_zero_of_abs_lt_dvd (hdiv i) hlt

lemma periodic_block (d B : ℕ) (f : ℕ → ℚ)
    (hf : ∀ n, (B : ℚ)*f (n+d)=f n) (n k : ℕ) :
    (B : ℚ)^k*f (n+d*k)=f n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, pow_succ, mul_assoc, hf, ih]

def sample (d L : ℕ) (j : Fin d × Fin L) : ℕ :=
  j.1.val + d*(L-1-j.2.val)

lemma sample_injective (d L : ℕ) (hd : 0 < d) : Function.Injective (sample d L) := by
  intro u v huv
  have hu : (sample d L u) % d = u.1.val := by
    simp [sample, Nat.mod_eq_of_lt u.1.isLt]
  have hv : (sample d L v) % d = v.1.val := by
    simp [sample, Nat.mod_eq_of_lt v.1.isLt]
  have he : u.1.val = v.1.val := by rw [← hu, ← hv, huv]
  have hk : L-1-u.2.val = L-1-v.2.val := by
    have hmul : d*(L-1-u.2.val)=d*(L-1-v.2.val) := by
      simp only [sample, he] at huv
      omega
    exact Nat.eq_of_mul_eq_mul_left hd hmul
  apply Prod.ext
  · exact Fin.ext he
  · apply Fin.ext
    have huL := u.2.isLt
    have hvL := v.2.isLt
    omega

/-- This concerns a SINGLE rational geometrically periodic sequence, not the
full target tail, which is a sum of infinitely many different periods. -/
theorem rational_periodic_kernel (d m B Q H : ℕ) (hB : 2 ≤ B)
    (hgap : B^m < (Q+1)^d) (f : ℕ → ℚ)
    (hf : ∀ n, (B : ℚ)*f (n+d)=f n) :
    ∃ L : ℕ, 0 < L ∧ ∃ w : Fin d × Fin L → ℤ,
      w ≠ 0 ∧ (∀ j, |w j| ≤ Q) ∧
      ∀ i : Fin m, ∑ j, (w j : ℚ)*f (H+i.val+sample d L j)=0 := by
  classical
  let r (u : Fin m × Fin d) := f (H+u.1.val+u.2.val)
  let C : ℕ := ∏ u : Fin m × Fin d, (r u).den
  have hC : 0 < C := prod_pos (fun u _ => (r u).pos)
  let a (i : Fin m) (j : Fin d) : ℤ :=
    (r (i,j)).num*(C/(r (i,j)).den : ℕ)
  have ha (i : Fin m) (j : Fin d) : (C : ℚ)*f (H+i.val+j.val) = a i j := by
    have hd : (r (i,j)).den ∣ C := dvd_prod_of_mem (fun u => (r u).den) (mem_univ (i,j))
    change (C : ℚ)*r (i,j) = _
    simp only [a, Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div_charZero hd]
    conv_lhs => rw [← Rat.num_div_den (r (i,j))]
    ring
  obtain ⟨L, hL, w, hw, hbound, hzero⟩ := bounded_geometric_kernel d m B Q hB hgap a
  refine ⟨L, hL, w, hw, hbound, ?_⟩
  intro i
  have hfactor (j : Fin d × Fin L) :
      (B : ℚ)^(L-1)*f (H+i.val+sample d L j) =
        (B : ℚ)^j.2.val*f (H+i.val+j.1.val) := by
    have hj : j.2.val ≤ L-1 := by have := j.2.isLt; omega
    have hp : (B : ℚ)^(L-1) = (B : ℚ)^j.2.val*(B : ℚ)^(L-1-j.2.val) := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    rw [hp, sample, ← Nat.add_assoc, mul_assoc,
      periodic_block d B f hf (H+i.val+j.1.val) (L-1-j.2.val)]
  have hmul : (C : ℚ)*(B : ℚ)^(L-1)*
      (∑ j, (w j : ℚ)*f (H+i.val+sample d L j)) = 0 := by
    calc
      _ = ∑ j, (w j : ℚ)*((a i j.1 : ℚ)*(B : ℚ)^j.2.val) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        calc
          _ = (w j : ℚ)*(C*(B^(L-1)*f (H+i.val+sample d L j))) := by ring
          _ = _ := by rw [hfactor, ← ha i j.1]; ring
      _ = _ := by exact_mod_cast hzero i
  have hne : (C : ℚ)*(B : ℚ)^(L-1) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hmul).resolve_left hne

lemma four_pow_lt_factorial (d : ℕ) (hd : 12 ≤ d) : 4^d < d.factorial := by
  induction d, hd using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ d hd ih =>
    rw [pow_succ, Nat.factorial_succ]
    have h := Nat.mul_lt_mul_of_pos_right ih (show 0 < 4 by omega)
    have h' := Nat.mul_le_mul_left d.factorial (show 4 ≤ d+1 by omega)
    nlinarith

lemma factorial_digit_gap (d : ℕ) (hd : 12 ≤ d) :
    d.factorial^(d-1) < (d.factorial/4+1)^d := by
  have hp := Nat.factorial_pos d
  have he := four_pow_lt_factorial d hd
  have hl : d.factorial ≤ 4*(d.factorial/4+1) := by omega
  have hpow := Nat.pow_le_pow_left hl d
  rw [mul_pow] at hpow
  have hmul := Nat.mul_lt_mul_of_pos_right he (pow_pos hp (d-1))
  have hnum : d.factorial*d.factorial^(d-1)=d.factorial^d := by
    rw [← pow_succ']; congr 1; omega
  rw [hnum] at hmul
  exact Nat.lt_of_mul_lt_mul_left (hmul.trans_le hpow)

open LambertBoundaryClearing LambertRawBounds LambertDifferenceOperators

def rationalRow (d n : ℕ) : ℚ :=
  1/((d.factorial : ℚ)^(n/d)*((d.factorial : ℚ)-1))

lemma rationalRow_period (d : ℕ) (hd : 0 < d) (n : ℕ) :
    (d.factorial : ℚ)*rationalRow d (n+d)=rationalRow d n := by
  have hb : (d.factorial : ℚ) ≠ 0 := by positivity
  simp only [rationalRow, Nat.add_div_right _ hd, pow_succ]
  field_simp

lemma rawApplyQ_period (ds : List ℕ) (d B : ℕ) (f : ℕ → ℚ)
    (hf : ∀ n, (B : ℚ)*f (n+d)=f n) :
    ∀ n, (B : ℚ)*rawApplyQ ds f (n+d)=rawApplyQ ds f n := by
  induction ds generalizing f with
  | nil => exact hf
  | cons k ks ih =>
    apply ih
    intro n
    have h1 := hf (n+k)
    have h2 := hf n
    rw [show n+d+k=n+k+d by omega]
    linear_combination (k.factorial : ℚ)*h1-h2

lemma rationalRow_cast (d n : ℕ) : (rationalRow d n : ℝ)=geometricRowTail d n := by
  simp [rationalRow, geometricRowTail]

/-- Every proper phase window can be annihilated with a nonzero bounded
integer vector of unrestricted support, even after any fixed raw filter.
No assertion about annihilating the FULL target sum is made. -/
theorem incomplete_phase_kernel (d H : ℕ) (hd : 12 ≤ d) (ds : List ℕ) :
    ∃ L : ℕ, 0 < L ∧ ∃ w : Fin d × Fin L → ℤ,
      w ≠ 0 ∧ (∀ j, |w j| ≤ (d.factorial/4 : ℕ)) ∧
      ∀ i : Fin (d-1), ∑ j, (w j : ℝ)*
        rawApply ds (geometricRowTail d) (H+i.val+sample d L j)=0 := by
  obtain ⟨L, hL, w, hw, hbound, hzero⟩ :=
    rational_periodic_kernel d (d-1) d.factorial (d.factorial/4) H
      (by exact Nat.factorial_le (by omega : 2 ≤ d)) (factorial_digit_gap d hd)
      (rawApplyQ ds (rationalRow d))
      (rawApplyQ_period ds d d.factorial _ (rationalRow_period d (by omega)))
  refine ⟨L, hL, w, hw, hbound, ?_⟩
  intro i
  have hc : ∀ n, (rawApplyQ ds (rationalRow d) n : ℝ)=
      rawApply ds (geometricRowTail d) n := by
    intro n
    rw [cast_rawApplyQ]
    simp only [rationalRow_cast]
  have hz := hzero i
  have hzR : (∑ j, (w j : ℝ)*(rawApplyQ ds (rationalRow d)
      (H+i.val+sample d L j) : ℝ))=0 := by exact_mod_cast hz
  simpa only [hc] using hzR

end IncompletePhaseKernel

#print axioms IncompletePhaseKernel.bounded_geometric_kernel
#print axioms IncompletePhaseKernel.rational_periodic_kernel
#print axioms IncompletePhaseKernel.incomplete_phase_kernel
