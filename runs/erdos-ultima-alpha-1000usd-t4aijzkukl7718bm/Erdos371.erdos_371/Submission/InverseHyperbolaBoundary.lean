import Submission.MarkedHyperbolaCancellation
import Submission.ThinMonotoneBands

/-! The one-unit losing-product cutoff shift, and exact marked index prefixes. -/
namespace Erdos371.Kloosterman
open Finset Filter
open scoped Topology

lemma hyperbolaCutoff_mono (p : ℕ) {N M : ℕ} (hNM : N ≤ M) (y : ℕ) :
    hyperbolaCutoff p N y ≤ hyperbolaCutoff p M y := by
  unfold hyperbolaCutoff
  split_ifs
  · rfl
  · exact min_le_min_left _ (Nat.add_le_add_right
      (Nat.div_le_div_right (Nat.sub_le_sub_right hNM 1)) 1)

lemma hyperbolaCutoff_succ_le (p N y : ℕ) :
    hyperbolaCutoff p (N+1) y ≤ hyperbolaCutoff p N y + 1 := by
  by_cases hy : y = 0
  · simp only [hyperbolaCutoff, if_pos hy]
    omega
  simp only [hyperbolaCutoff, if_neg hy, Nat.add_sub_cancel]
  have hdiv : N/y ≤ (N-1)/y + 1 := by
    cases N with
    | zero => simp
    | succ N =>
      simp only [Nat.succ_sub_one, Nat.succ_div]
      split_ifs <;> omega
  omega

/-- Explicit boundary bound for either inverse orientation. -/
theorem inverse_hyperbola_boundary_bound (p : ℕ) [Fact p.Prime]
    (s : Bool) (N H K T : ℕ) (hH : 0 < H) (hcover : p ≤ K*H) (hT : 2 ≤ T) :
    |(inverseHyperbolaCount p s (N+1) : ℝ)/p - (inverseHyperbolaCount p s N : ℝ)/p| ≤
      (H : ℝ)/p + 1/(p : ℝ) +
        4*K*(4/(T : ℝ)+5/(p : ℝ)+Real.sqrt (Real.sqrt (3/(p : ℝ)))*(T : ℝ)) := by
  rw [inverseHyperbolaCount_eq_region, inverseHyperbolaCount_eq_region]
  have he := MonotoneRectangles.thin_monotone_band
    (fun x : (ZMod p)ˣ => (x : ZMod p).val)
    (fun x => (orientedInverse p s x).val)
    (hyperbolaCutoff p N) (hyperbolaCutoff p (N+1))
    (hyperbolaCutoff_antitone _ _) (hyperbolaCutoff_antitone _ _)
    p H K 1 (Fact.out : p.Prime).pos hH hcover
    (fun x => ZMod.val_lt _) (by simp [hyperbolaCutoff]) (by simp [hyperbolaCutoff])
    (hyperbolaCutoff_mono p (Nat.le_succ N)) (hyperbolaCutoff_succ_le p N)
    (4/(T : ℝ)+5/(p : ℝ)+Real.sqrt (Real.sqrt (3/(p : ℝ)))*(T : ℝ)) (by
      intro U V hU hV
      rw [oriented_rectCount_eq]
      exact signed_rectangle_ratio_uniform p s U V T hU hV hT)
  simpa only [Nat.cast_one] using he

/-- Uniform o(p) mass on the product-equality boundary of either curve. -/
theorem inverse_hyperbola_boundary_tendsto (p : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hp : Tendsto p atTop atTop) (s : ℕ → Bool) (N : ℕ → ℕ) :
    Tendsto (fun n => |(inverseHyperbolaCount (p n) (s n) (N n+1) : ℝ)/(p n) -
      (inverseHyperbolaCount (p n) (s n) (N n) : ℝ)/(p n)|) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro ε hε
    exact Eventually.of_forall fun n => hε.trans_le (abs_nonneg _)
  · intro ε hε
    obtain ⟨K,hK⟩ := exists_nat_gt (max (2 : ℝ) (4/ε))
    have hK2 : 2 ≤ K := by exact_mod_cast (le_max_left _ _).trans hK.le
    have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have hKe : 1/(K : ℝ) < ε/4 := by
      have hk := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hK)
      apply (div_lt_iff₀ hK0).mpr
      nlinarith
    obtain ⟨T,hT⟩ := exists_nat_gt (max (2 : ℝ) (64*(K : ℝ)/ε))
    have hT2 : 2 ≤ T := by exact_mod_cast (le_max_left _ _).trans hT.le
    have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
    have hTe : 16*(K : ℝ)/T < ε/4 := by
      have ht := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hT)
      apply (div_lt_iff₀ hT0).mpr
      nlinarith
    let A : ℝ := 1/(K : ℝ)+16*(K : ℝ)/T
    have hA : A < ε := by dsimp [A]; linarith
    have hroot := ((((tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)).comp hp).sqrt).sqrt).mul_const (T : ℝ)
    have ht := ((tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp hp).add
      ((((tendsto_const_div_atTop_nhds_zero_nat (5 : ℝ)).comp hp).add hroot).const_mul (4*(K : ℝ)))
    simp only [Real.sqrt_zero,zero_mul,add_zero,mul_zero] at ht
    filter_upwards [ht.eventually_lt_const (show 0 < ε-A by linarith)] with n hn
    dsimp only [Function.comp_apply] at hn
    let H : ℕ := p n/K+1
    have hH : 0 < H := Nat.succ_pos _
    have hcover : p n ≤ K*H := by
      have hm := Nat.mod_lt (p n) (show 0 < K by omega)
      have he := Nat.div_add_mod (p n) K
      dsimp [H]
      nlinarith
    have hb := inverse_hyperbola_boundary_bound (p n) (s n) (N n) H K T hH hcover hT2
    have hw := integer_grid_width_ratio (p n) K (Fact.out : (p n).Prime).pos (by omega)
    change (H : ℝ)/(p n) ≤ _ at hw
    calc
      _ ≤ A+(2/(p n : ℝ)+4*(K : ℝ)*(5/(p n : ℝ)+Real.sqrt (Real.sqrt (3/(p n : ℝ)))*(T : ℝ))) := by
        apply (hb.trans (add_le_add (add_le_add hw le_rfl) le_rfl)).trans_eq
        dsimp [A]
        ring
      _ < ε := by linarith

/-- The rise uses ab<N, whereas the fall at ab-1 uses ab≤N. -/
theorem inverse_hyperbola_prefix_difference_tendsto (p : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hp : Tendsto p atTop atTop) (N : ℕ → ℕ) :
    Tendsto (fun n => |(inverseHyperbolaCount (p n) true (N n) : ℝ)/(p n) -
      (inverseHyperbolaCount (p n) false (N n+1) : ℝ)/(p n)|) atTop (nhds 0) := by
  have ht := (inverse_hyperbola_difference_tendsto p hp N).add
    (inverse_hyperbola_boundary_tendsto p hp (fun _ => false) N)
  simp only [add_zero] at ht
  apply squeeze_zero (fun n => abs_nonneg _) _ ht
  intro n
  simpa only [abs_sub_comm] using abs_sub_le
    ((inverseHyperbolaCount (p n) true (N n) : ℝ)/(p n))
    ((inverseHyperbolaCount (p n) false (N n) : ℝ)/(p n))
    ((inverseHyperbolaCount (p n) false (N n+1) : ℝ)/(p n))

section Marked
variable (p : ℕ) [Fact p.Prime]

lemma markedProductCount_two_cutoff_difference_bound (N M : ℕ) :
    |(markedProductCount p true N : ℝ)/p - (markedProductCount p false M : ℝ)/p| ≤
      |(inverseHyperbolaCount p true N : ℝ)/p - (inverseHyperbolaCount p false M : ℝ)/p| +
        2/(p : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have ht : |(markedProductCount p true N : ℝ)/p - (inverseHyperbolaCount p true N : ℝ)/p| ≤ 1/(p : ℝ) := by
    rw [← sub_div,abs_div,abs_of_pos hp0]
    exact div_le_div_of_nonneg_right (markedProductCount_error p true N) hp0.le
  have hf : |(inverseHyperbolaCount p false M : ℝ)/p - (markedProductCount p false M : ℝ)/p| ≤ 1/(p : ℝ) := by
    rw [abs_sub_comm,← sub_div,abs_div,abs_of_pos hp0]
    exact div_le_div_of_nonneg_right (markedProductCount_error p false M) hp0.le
  have h1 := abs_sub_le ((markedProductCount p true N : ℝ)/p)
    ((inverseHyperbolaCount p true N : ℝ)/p) ((markedProductCount p false M : ℝ)/p)
  have h2 := abs_sub_le ((inverseHyperbolaCount p true N : ℝ)/p)
    ((inverseHyperbolaCount p false M : ℝ)/p) ((markedProductCount p false M : ℝ)/p)
  have he : (2 : ℝ)/p = 1/p+1/p := by ring
  rw [he]
  linarith

/-- Actual index-prefix count, retaining the eligible factorization marks. -/
noncomputable def markedIndexCount (s : Bool) (N : ℕ) : ℕ :=
  ((chosenDivisorMarks p s).filter fun ab =>
    (if s then ab.1*ab.2 else ab.1*ab.2-1) < N).card

omit [Fact p.Prime] in
lemma markedIndexCount_true (N : ℕ) :
    markedIndexCount p true N = markedProductCount p true N := rfl

omit [Fact p.Prime] in
lemma markedIndexCount_false (N : ℕ) :
    markedIndexCount p false N = markedProductCount p false (N+1) := by
  unfold markedIndexCount markedProductCount
  congr 1
  ext ab
  simp only [mem_filter, Bool.false_eq_true, if_false]
  constructor
  · rintro ⟨hab,hN⟩
    exact ⟨hab,by omega⟩
  · rintro ⟨hab,hN⟩
    have hbounds : ab ∈ (Ico 2 p).product (Ico 1 p) := (mem_filter.mp hab).1
    have ha := (mem_Ico.mp (mem_product.mp hbounds).1).1
    have hb := (mem_Ico.mp (mem_product.mp hbounds).2).1
    have hprod : 0 < ab.1*ab.2 := Nat.mul_pos (by omega) (by omega)
    exact ⟨hab,by omega⟩
end Marked

/-- Exact marked natural-index prefixes balance to o(p), uniformly in N.
The normalization remains the winning prime, and multiplicities remain. -/
theorem marked_index_prefix_difference_tendsto (p : ℕ → ℕ) [∀ n, Fact (p n).Prime]
    (hp : Tendsto p atTop atTop) (N : ℕ → ℕ) :
    Tendsto (fun n => |(markedIndexCount (p n) true (N n) : ℝ)/(p n) -
      (markedIndexCount (p n) false (N n) : ℝ)/(p n)|) atTop (nhds 0) := by
  simp_rw [markedIndexCount_true,markedIndexCount_false]
  have ht := (inverse_hyperbola_prefix_difference_tendsto p hp N).add
    ((tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp hp)
  simp only [add_zero] at ht
  exact squeeze_zero (fun n => abs_nonneg _)
    (fun n => markedProductCount_two_cutoff_difference_bound (p n) (N n) (N n+1)) ht

#print axioms markedIndexCount_false
#print axioms marked_index_prefix_difference_tendsto
#print axioms hyperbolaCutoff_succ_le
#print axioms inverse_hyperbola_boundary_tendsto
#print axioms inverse_hyperbola_prefix_difference_tendsto
end Erdos371.Kloosterman
