import Submission.GrowingVaughanShortTerms

/-! A power-separated prime/modulus range permits polynomially growing
Vaughan cutoffs, with an explicit power saving for the two short terms.
The long-divisor kernel is still present and still needs signed cancellation. -/
namespace Erdos371
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma vaughan_cardinality_budget_power_bound (N U V C : ℕ) (P : Finset ℕ)
    (a b u v : ℝ) (hN : 1 ≤ N)
    (hP : (P.card : ℝ) ≤ (N : ℝ)^a) (hC : (N : ℝ)^b ≤ C)
    (hU : (U : ℝ) ≤ (N : ℝ)^u) (hV : (V : ℝ) ≤ (N : ℝ)^v) :
    (P.card : ℝ)*(U*V : ℕ)/(C+1 : ℕ) ≤ (N : ℝ)^(-(b-a-u-v)) := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hpow : 0 < (N : ℝ)^b := Real.rpow_pos_of_pos hNr b
  have hnum : (P.card : ℝ)*(U*V : ℕ) ≤ (N : ℝ)^(a+u+v) := by
    simp only [Nat.cast_mul,Real.rpow_add hNr]
    exact (mul_le_mul hP (mul_le_mul hU hV (Nat.cast_nonneg V)
      (Real.rpow_nonneg hNr.le u)) (by positivity) (Real.rpow_nonneg hNr.le a)).trans_eq (by ring)
  calc
    _ ≤ (N : ℝ)^(a+u+v)/(C+1 : ℕ) := div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (N : ℝ)^(a+u+v)/(N : ℝ)^b := div_le_div_of_nonneg_left
      (Real.rpow_nonneg hNr.le _) hpow (by push_cast; linarith)
    _ = _ := by rw [← Real.rpow_sub hNr]; congr 1; ring

lemma vaughan_cardinality_budget_power_zero (U V C : ℕ → ℕ) (P : ℕ → Finset ℕ)
    (a b u v : ℝ) (hgap : a+u+v < b)
    (hsize : ∀ᶠ N : ℕ in atTop, (P N).card ≤ (N : ℝ)^a ∧ (N : ℝ)^b ≤ C N ∧
      (U N : ℝ) ≤ (N : ℝ)^u ∧ (V N : ℝ) ≤ (N : ℝ)^v) :
    Tendsto (fun N => ((P N).card : ℝ)*(U N*V N : ℕ)/(C N+1 : ℕ)) atTop (𝓝 0) := by
  have hz := (tendsto_rpow_neg_atTop (by linarith : 0 < b-a-u-v)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply squeeze_zero' (Eventually.of_forall (fun N => by positivity)) _ hz
  filter_upwards [hsize,eventually_ge_atTop (1 : ℕ)] with N hs hN
  exact vaughan_cardinality_budget_power_bound N (U N) (V N) (C N) (P N) a b u v
    hN hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

/-- A finite power-saving form: the short-term error is bounded by
12*N^(-(b-a-u-v)), uniformly in every cofactor endpoint. -/
theorem mangoldtKernel_power_vaughan_error (N U V C : ℕ) (P : Finset ℕ)
    (F : ℕ → ℕ) (a b u v : ℝ) (hN : 1 ≤ N)
    (hU1 : 1 ≤ U) (hV1 : 1 ≤ V) (hUV : U*V ≤ C)
    (hPpos : ∀ p ∈ P, 0 < p)
    (hP : (P.card : ℝ) ≤ (N : ℝ)^a) (hC : (N : ℝ)^b ≤ C)
    (hU : (U : ℝ) ≤ (N : ℝ)^u) (hV : (V : ℝ) ≤ (N : ℝ)^v) :
    |(mangoldtCutoffSkew P (Icc 1 (N/(C+1))) C F-
        vaughanLongKernel U V P (Icc 1 (N/(C+1))) C F)/N| ≤
      12*(N : ℝ)^(-(b-a-u-v)) := by
  have h := mangoldtKernel_growing_vaughan_ratio_bound U V N P C F hN hU1 hV1 hUV hPpos
  have hb := mul_le_mul_of_nonneg_left
    (vaughan_cardinality_budget_power_bound N U V C P a b u v hN hP hC hU hV)
    (by norm_num : (0 : ℝ)≤12)
  exact h.trans (by simpa only [mul_div_assoc,mul_assoc] using hb)

noncomputable def vaughanPowerCutoff (γ : ℝ) (N : ℕ) : ℕ := ⌊(N : ℝ)^γ⌋₊

lemma vaughanPowerCutoff_tendsto (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (vaughanPowerCutoff γ) atTop atTop :=
  tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop)

lemma vaughanPowerCutoff_le (γ : ℝ) (N : ℕ) :
    (vaughanPowerCutoff γ N : ℝ) ≤ (N : ℝ)^γ := Nat.floor_le (Real.rpow_nonneg (by positivity) γ)

lemma vaughanPowerCutoff_pos (γ : ℝ) (hγ : 0 ≤ γ) (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ vaughanPowerCutoff γ N :=
  Nat.floor_pos.mpr (Real.one_le_rpow (by exact_mod_cast hN) hγ)

lemma vaughanPowerCutoff_sq_le (γ b : ℝ) (hγb : 2*γ ≤ b)
    (N C : ℕ) (hN : 1 ≤ N) (hC : (N : ℝ)^b ≤ C) :
    vaughanPowerCutoff γ N*vaughanPowerCutoff γ N ≤ C := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  have hT := vaughanPowerCutoff_le γ N
  have hh := mul_le_mul hT hT (by positivity : (0 : ℝ)≤vaughanPowerCutoff γ N)
    (Real.rpow_nonneg hNr.le γ)
  have hp : (N : ℝ)^γ*(N : ℝ)^γ ≤ (N : ℝ)^b := by
    rw [← Real.rpow_add hNr]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)
  exact_mod_cast hh.trans (hp.trans hC)

/-- Both Vaughan cutoffs can be the explicit power floor(N^γ), provided
that a+2γ<b. This is stronger than a nonquantitative growing diagonal. -/
theorem mangoldtKernel_polynomial_vaughan_remainder_tendsto (a b γ : ℝ)
    (ha : 0 ≤ a) (hγ : 0 < γ) (hgap : a+2*γ < b)
    (C : ℕ → ℕ) (P : ℕ → Finset ℕ) (F : ℕ → ℕ → ℕ)
    (hP : ∀ᶠ N : ℕ in atTop, ∀ p ∈ P N, 0 < p)
    (hsize : ∀ᶠ N : ℕ in atTop, (P N).card ≤ (N : ℝ)^a ∧ (N : ℝ)^b ≤ C N) :
    Tendsto (fun N => (mangoldtCutoffSkew (P N) (Icc 1 (N/(C N+1))) (C N) (F N)-
      vaughanLongKernel (vaughanPowerCutoff γ N) (vaughanPowerCutoff γ N)
        (P N) (Icc 1 (N/(C N+1))) (C N) (F N))/N) atTop (𝓝 0) := by
  refine mangoldtKernel_growing_vaughan_remainder_tendsto _ _ C P F ?_ hP ?_
  · filter_upwards [hsize,eventually_ge_atTop (1 : ℕ)] with N hs hN
    have hT := vaughanPowerCutoff_pos γ hγ.le N hN
    exact ⟨hT,hT,vaughanPowerCutoff_sq_le γ b (by linarith) N (C N) hN hs.2⟩
  · apply vaughan_cardinality_budget_power_zero _ _ C P a b γ γ (by linarith)
    filter_upwards [hsize] with N hs
    exact ⟨hs.1,hs.2,vaughanPowerCutoff_le γ N,vaughanPowerCutoff_le γ N⟩

/-- A bound on the moduli themselves implies the cardinality condition.
It applies in particular to the actual prime-modulus bands. -/
lemma positive_moduli_card_le_rpow (N : ℕ) (a : ℝ) (P : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p ∧ (p : ℝ) ≤ (N : ℝ)^a) :
    (P.card : ℝ) ≤ (N : ℝ)^a := by
  have hs : P ⊆ Icc 1 ⌊(N : ℝ)^a⌋₊ := by
    intro p hp
    exact mem_Icc.mpr ⟨(hP p hp).1,Nat.le_floor (hP p hp).2⟩
  have hh := card_le_card hs
  simp only [Nat.card_Icc,Nat.add_sub_cancel] at hh
  exact (Nat.cast_le.mpr hh).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) a))

#print axioms mangoldtKernel_power_vaughan_error
#print axioms mangoldtKernel_polynomial_vaughan_remainder_tendsto
#print axioms vaughanPowerCutoff_tendsto
end Erdos371
