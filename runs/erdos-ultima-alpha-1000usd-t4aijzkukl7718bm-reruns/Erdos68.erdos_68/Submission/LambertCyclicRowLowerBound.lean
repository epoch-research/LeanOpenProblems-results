import Submission.FactorialGeometricProductBound

/-!
Supremum-norm lower bounds for uncancelled Lambert rows. These estimates
concern individual rows, not integrally cleared forms in the full target.
-/

namespace LambertCyclicRowLowerBound

open Finset LambertDifferenceOperators LambertRawBounds
  LambertSharperOperatorBounds FactorialGeometricProductBound

noncomputable section

lemma normalized_factorial_le_three_quarters (d k : ℕ) (hd : 12 ≤ d)
    (hk : 2 ≤ k) (hkd : k < d) :
    (k.factorial : ℝ)/rate d^k ≤ 3/4 := by
  by_cases hh : d ≤ 2*k
  · have hb := normalized_factorial_upper_half d k (by omega) hh hkd.le
    have he : 1 ≤ d-k := by omega
    have hp : (3/4 : ℝ)^(d-k) ≤ (3/4 : ℝ)^1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) he
    exact hb.trans (by simpa using hp)
  · by_cases hk4 : 4 ≤ k
    · have hb := normalized_factorial_lower_half d k (by omega) (by omega)
      have hp : (3/4 : ℝ)^k ≤ (3/4 : ℝ)^4 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hk4
      norm_num at hp
      linarith
    · have hp : (4 : ℝ) ≤ rate d := by
        have hl := rate_lower_third d (by omega)
        have hdR : (12 : ℝ) ≤ d := by exact_mod_cast hd
        linarith
      have hk' : k=2 ∨ k=3 := by omega
      rcases hk' with rfl | rfl
      · apply (div_le_iff₀ (pow_pos (rate_pos d) 2)).mpr
        norm_num
        nlinarith [sq_nonneg (rate d-4)]
      · have hb : (4 : ℝ)^3 ≤ rate d^3 := pow_le_pow_left₀ (by norm_num) hp 3
        apply (div_le_iff₀ (pow_pos (rate_pos d) 3)).mpr
        norm_num at hb ⊢
        linarith

lemma exp_neg_four_mul_le (t : ℝ) (ht : 0 ≤ t) (hu : t ≤ 3/4) :
    Real.exp (-(4*t)) ≤ 1-t := by
  rw [Real.exp_neg, inv_eq_one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have he := Real.add_one_le_exp (4*t)
  have hm := mul_le_mul_of_nonneg_right he (show 0 ≤ 1-t by linarith)
  nlinarith [mul_nonneg ht (show 0 ≤ 3-4*t by linarith)]

/-- A lower product bound complementary to the existing upper bound. -/
theorem lower_product_uniform (K d : ℕ) (hd : 12 ≤ d) (hKd : K+1 < d) :
    Real.exp (-48) ≤
      ((List.range' 2 K).map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod := by
  have hrate := rate_pos d
  let s := (List.range' 2 K).toFinset
  have hmem (k : ℕ) (hk : k ∈ s) : 2 ≤ k ∧ k < d := by
    obtain ⟨i, hi, he⟩ := List.mem_range'.mp (List.mem_toFinset.mp hk)
    omega
  have hs : (∑ k ∈ s, (k.factorial : ℝ)/rate d^k) ≤ 12 := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.range (d+1))
      (fun k hk => Finset.mem_range.mpr (by have := hmem k hk; omega))
      (by intros; positivity))
    exact normalized_factorial_sum_le_twelve d (by omega)
  have heq : (∏ k ∈ s, (1-(k.factorial : ℝ)/rate d^k)) =
      ((List.range' 2 K).map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod :=
    List.prod_toFinset _ List.nodup_range'
  rw [← heq]
  calc
    Real.exp (-48) ≤ Real.exp (∑ k ∈ s, -(4*((k.factorial : ℝ)/rate d^k))) := by
      apply Real.exp_le_exp.mpr
      simp only [Finset.sum_neg_distrib, ← Finset.mul_sum]
      linarith
    _ = ∏ k ∈ s, Real.exp (-(4*((k.factorial : ℝ)/rate d^k))) := Real.exp_sum _ _
    _ ≤ _ := by
      apply Finset.prod_le_prod (by intros; positivity)
      intro k hk
      exact exp_neg_four_mul_le _ (by positivity)
        (normalized_factorial_le_three_quarters d k hd (hmem k hk).1 (hmem k hk).2)

section FiniteNorm

variable {ι : Type*} [Fintype ι]

lemma compose_norm_le (f : ι → ℝ) (σ : ι → ι) : ‖f ∘ σ‖ ≤ ‖f‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr
  intro i
  exact norm_le_pi_norm f (σ i)

lemma shift_norm_lower (f : ι → ℝ) (σ : ι → ι) (t : ℝ) (ht : 0 ≤ t) :
    (1-t)*‖f‖ ≤ ‖fun i => t*f (σ i)-f i‖ := by
  have hb : ‖t • (f ∘ σ)‖ ≤ t*‖f‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left (compose_norm_le f σ) ht
  have he := norm_sub_norm_le f (t • (f ∘ σ))
  rw [norm_sub_rev] at he
  change ‖f‖-‖t • (f ∘ σ)‖ ≤ ‖fun i => t*f (σ i)-f i‖ at he
  nlinarith

lemma exists_norm_ge [Nonempty ι] (f : ι → ℝ) (a : ℝ)
    (ha : 0 < a) (hf : a ≤ ‖f‖) : ∃ i, a ≤ |f i| := by
  by_contra hn
  push_neg at hn
  have hl : ‖f‖ < a := (pi_norm_lt_iff ha).mpr (by simpa only [Real.norm_eq_abs] using hn)
  linarith

end FiniteNorm

/-- The raw shift on the normalized finite periodic model. -/
def cyclicShift (d k : ℕ) (f : ZMod d → ℝ) : ZMod d → ℝ :=
  fun h => ((k.factorial : ℝ)/rate d^k)*f (h+k)-f h

def cyclicApply (d : ℕ) : List ℕ → (ZMod d → ℝ) → (ZMod d → ℝ)
  | [], f => f
  | k::ks, f => cyclicApply d ks (cyclicShift d k f)

lemma cyclicApply_norm_lower (d : ℕ) [NeZero d] (ks : List ℕ)
    (hks : ∀ k ∈ ks, (k.factorial : ℝ)/rate d^k ≤ 1) (f : ZMod d → ℝ) :
    (ks.map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod * ‖f‖ ≤
      ‖cyclicApply d ks f‖ := by
  have hrate := rate_pos d
  induction ks generalizing f with
  | nil => simp [cyclicApply]
  | cons k ks ih =>
    have hp : 0 ≤ (ks.map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod := by
      apply List.prod_nonneg
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      linarith [hks j (by simp [hj])]
    have hb := shift_norm_lower f (fun h => h+(k : ZMod d))
      ((k.factorial : ℝ)/rate d^k) (by positivity)
    have hi := ih (fun j hj => hks j (by simp [hj])) (cyclicShift d k f)
    change _ ≤ ‖cyclicApply d ks (cyclicShift d k f)‖
    simp only [List.map_cons, List.prod_cons]
    calc
      _ = (ks.map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod *
          ((1-(k.factorial : ℝ)/rate d^k)*‖f‖) := by ring
      _ ≤ (ks.map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod *
          ‖cyclicShift d k f‖ := mul_le_mul_of_nonneg_left hb hp
      _ ≤ _ := hi

/-- The initial normalized geometric row. -/
def rowModel (d : ℕ) (h : ZMod d) : ℝ := rate d^h.val/(d.factorial-1)

lemma geometricRowTail_model (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    rate d^n * geometricRowTail d n = rowModel d (n : ZMod d) := by
  have hp := rate_pos d
  have hf : (d.factorial : ℝ)-1 ≠ 0 := by
    have ht : (2 : ℝ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hd
    linarith
  simp only [rowModel, ZMod.val_natCast, geometricRowTail]
  have he : rate d^n = rate d^(n%d)*(d.factorial : ℝ)^(n/d) := by
    rw [← rate_pow d (by omega), ← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [he]
  field_simp

lemma rawShift_model (d k : ℕ) (r : ℕ → ℝ) (f : ZMod d → ℝ)
    (hr : ∀ n, rate d^n*r n = f (n : ZMod d)) (n : ℕ) :
    rate d^n*rawShift k r n = cyclicShift d k f (n : ZMod d) := by
  have hp := rate_pos d
  have hpow : rate d^k ≠ 0 := (pow_pos hp k).ne'
  unfold rawShift cyclicShift
  rw [← Nat.cast_add, ← hr (n+k), ← hr n, pow_add]
  field_simp

lemma rawApply_model (d : ℕ) (ks : List ℕ) (r : ℕ → ℝ) (f : ZMod d → ℝ)
    (hr : ∀ n, rate d^n*r n = f (n : ZMod d)) (n : ℕ) :
    rate d^n*rawApply ks r n = cyclicApply d ks f (n : ZMod d) := by
  induction ks generalizing r f with
  | nil => exact hr n
  | cons k ks ih =>
    exact ih (rawShift k r) (cyclicShift d k f) (rawShift_model d k r f hr)

lemma rowModel_norm_lower (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    1/rate d ≤ ‖rowModel d‖ := by
  have hp := rate_pos d
  have hdf : (2 : ℝ) ≤ d.factorial := by exact_mod_cast Nat.factorial_le hd
  have hh : (d-1 : ℕ) < d := by omega
  have hb := norm_le_pi_norm (rowModel d) ((d-1 : ℕ) : ZMod d)
  rw [rowModel, ZMod.val_natCast_of_lt hh, Real.norm_eq_abs, abs_of_pos
    (div_pos (pow_pos hp _) (by linarith))] at hb
  apply le_trans _ hb
  apply (div_le_div_iff₀ hp (by linarith : (0 : ℝ) < d.factorial-1)).mpr
  rw [one_mul, ← pow_succ, show d-1+1=d by omega, rate_pow d (by omega)]
  linarith

/-- In every complete phase window, an uncancelled row has a quantitatively
nonzero raw-operator value. This is not yet a statement about the full tail. -/
theorem row_lower_in_every_window (K d H : ℕ) (hd : 12 ≤ d) (hKd : K+1 < d) :
    ∃ n, H ≤ n ∧ n < H+d ∧
      Real.exp (-48)/rate d ≤
        rate d^n * |rawApply (List.range' 2 K) (geometricRowTail d) n| := by
  have hrate := rate_pos d
  letI : NeZero d := ⟨by omega⟩
  let f := cyclicApply d (List.range' 2 K) (rowModel d)
  have hl : Real.exp (-48)/rate d ≤ ‖f‖ := by
    have hc := cyclicApply_norm_lower d (List.range' 2 K) (by
      intro k hk
      obtain ⟨i, hi, he⟩ := List.mem_range'.mp hk
      exact (normalized_factorial_le_three_quarters d k hd (by omega) (by omega)).trans
        (by norm_num)) (rowModel d)
    calc
      _ = Real.exp (-48)*(1/rate d) := by ring
      _ ≤ ((List.range' 2 K).map (fun k => 1-(k.factorial : ℝ)/rate d^k)).prod *
          ‖rowModel d‖ := mul_le_mul (lower_product_uniform K d hd hKd)
            (rowModel_norm_lower d (by omega)) (by positivity)
            ((Real.exp_pos _).le.trans (lower_product_uniform K d hd hKd))
      _ ≤ _ := hc
  obtain ⟨h, hh⟩ := exists_norm_ge f (Real.exp (-48)/rate d) (by positivity) hl
  let j := (h-(H : ZMod d)).val
  have hj : j < d := ZMod.val_lt _
  have he : ((H+j : ℕ) : ZMod d) = h := by
    simp only [Nat.cast_add, j, ZMod.natCast_zmod_val]
    ring
  refine ⟨H+j, by omega, by omega, ?_⟩
  have hm := rawApply_model d (List.range' 2 K) (geometricRowTail d) (rowModel d)
    (geometricRowTail_model d (by omega)) (H+j)
  rw [he] at hm
  dsimp [f] at hh
  rw [← hm, abs_mul, abs_of_pos (pow_pos (rate_pos d) _)] at hh
  exact hh

end
end LambertCyclicRowLowerBound

#print axioms LambertCyclicRowLowerBound.lower_product_uniform
#print axioms LambertCyclicRowLowerBound.row_lower_in_every_window
