import Submission.SidonInSumset
import Submission.TranslatedSquareFibers

/-!
The first N squares cannot be covered by B+B with |B| below N^(2/3-o(1)).
This excludes a particular small-additive-basis route to a disproof of Erdos 773;
it is not an upper bound on Sidon subsets of the squares.
-/
namespace Erdos773.SquareAdditiveBasis
open Finset Filter SidonInSumset TranslatedSquareFibers
open scoped Pointwise
set_option maxHeartbeats 1000000

/-- Uniform finite incidence consequence of the square-difference divisor bound. -/
theorem finite_cover_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ K > (0:ℝ), ∀ N : ℕ, ∀ X Y : Finset ℕ,
      (Icc 1 N).image (fun n : ℕ => n^2) ⊆ X+Y →
      (N:ℝ) ≤ Y.card*Real.sqrt (X.card*(K*(N:ℝ)^δ)) + X.card := by
  obtain ⟨K,hK,htranslate⟩ := commonValues_subpower δ hδ
  refine ⟨K,hK,?_⟩
  intro N X Y hcover
  have hcard : ((Icc 1 N).image (fun n : ℕ => n^2)).card=N := by
    rw [card_image_of_injective _ (Nat.pow_left_injective (by decide : (2:ℕ) ≠ 0))]
    simp
  have hb := card_le_of_translate_bound ((Icc 1 N).image (fun n : ℕ => n^2)) X Y hcover
    (K*(N:ℝ)^δ) (mul_nonneg hK.le (Real.rpow_nonneg (Nat.cast_nonneg N) δ))
    (htranslate N)
  simpa only [hcard] using hb

private lemma scalar_lower {X b K ε : ℝ} (hX : 0 < X) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hsmall : 2*X^(2/3-ε) ≤ X) (hfactor : 4*K*X^(-2*ε) < 1)
    (hcover : X ≤ b*Real.sqrt (b*(K*X^ε)) + b) :
    X^(2/3-ε) ≤ b := by
  by_contra! hn
  have hhalf : b ≤ X/2 := by linarith
  have hlead : X/2 ≤ b*Real.sqrt (b*(K*X^ε)) := by linarith
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ X/2) hlead 2
  rw [mul_pow,Real.sq_sqrt (by positivity)] at hs
  have hsq : X^2 ≤ 4*b^3*K*X^ε := by nlinarith only [hs]
  have hp := pow_le_pow_left₀ hb hn.le 3
  have hm := mul_le_mul_of_nonneg_right hp (show 0 ≤ 4*K*X^ε by positivity)
  have hid : (X^(2/3-ε))^3*X^ε = X^2*X^(-2*ε) := by
    rw [← Real.rpow_mul_natCast hX.le,← Real.rpow_natCast X 2,
      ← Real.rpow_add hX,← Real.rpow_add hX]
    congr 1
    norm_num
    ring
  have hmajor : X^2 ≤ X^2*(4*K*X^(-2*ε)) := by
    calc
      _ ≤ 4*b^3*K*X^ε := hsq
      _ ≤ 4*(X^(2/3-ε))^3*K*X^ε := by nlinarith only [hm]
      _ = 4*K*((X^(2/3-ε))^3*X^ε) := by ring
      _ = X^2*(4*K*X^(-2*ε)) := by rw [hid]; ring
  have hlt := mul_lt_mul_of_pos_left hfactor (sq_pos_of_pos hX)
  nlinarith only [hmajor,hlt]

/-- Every additive basis of order two for the first N squares has at least
    N^(2/3-epsilon) elements, uniformly over all bases at sufficiently large N. -/
theorem eventual_basis_lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B : Finset ℕ,
      (Icc 1 N).image (fun n : ℕ => n^2) ⊆ B+B →
      (N:ℝ)^(2/3-ε) ≤ B.card := by
  obtain ⟨K,hK,hcoverBound⟩ := finite_cover_bound ε hε
  have hlarge : Tendsto (fun N : ℕ => (N:ℝ)^(1/3+ε)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : (0:ℝ) < 1/3+ε)).comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun N : ℕ => (N:ℝ)^(-(2*ε))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by positivity : (0:ℝ) < 2*ε)).comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ N : ℕ in atTop, 4*K*(N:ℝ)^(-2*ε) < 1 := by
    have ht : Tendsto (fun N : ℕ => 4*K*(N:ℝ)^(-(2*ε))) atTop (nhds 0) := by
      simpa using hzero.const_mul (4*K)
    have he := ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))
    simpa only [mul_zero,neg_mul] using he
  filter_upwards [hlarge.eventually_ge_atTop 2,hsmall,eventually_ge_atTop 1]
    with N hlarge hsmall hN
  intro B hcover
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hslack : 2*(N:ℝ)^(2/3-ε) ≤ N := by
    calc
      _ ≤ (N:ℝ)^(1/3+ε)*(N:ℝ)^(2/3-ε) :=
        mul_le_mul_of_nonneg_right hlarge (Real.rpow_nonneg hNpos.le _)
      _ = N := by
        rw [← Real.rpow_add hNpos]
        norm_num [show (1/3+ε)+(2/3-ε)=(1:ℝ) by ring]
  exact scalar_lower hNpos (Nat.cast_nonneg B.card) hK.le hslack hsmall
    (hcoverBound N B B hcover)

/-- In particular, no fixed power below 2/3, even with an arbitrary fixed
    multiplicative constant, can bound such bases along an unbounded sequence. -/
theorem eventual_exceeds_fixed_power (α C : ℝ) (hα : α < 2/3) :
    ∀ᶠ N : ℕ in atTop, ∀ B : Finset ℕ,
      (Icc 1 N).image (fun n : ℕ => n^2) ⊆ B+B →
      C*(N:ℝ)^α < B.card := by
  let δ : ℝ := (2/3-α)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hlarge : Tendsto (fun N : ℕ => (N:ℝ)^δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventual_basis_lower δ hδ,hlarge.eventually_gt_atTop C,eventually_ge_atTop 1]
    with N hb hC hN
  intro B hcover
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  calc
    C*(N:ℝ)^α < (N:ℝ)^δ*(N:ℝ)^α :=
      mul_lt_mul_of_pos_right hC (Real.rpow_pos_of_pos hNpos α)
    _ = (N:ℝ)^(2/3-δ) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      dsimp [δ]
      ring
    _ ≤ B.card := hb B hcover

/-- The C4/Sidon sumset upper-bound expression itself is necessarily
    N^(1-o(1)) for every rectangular sumset cover of the squares. Thus choosing
    unequal summand sets cannot repair the proposed fixed-power disproof. -/
theorem eventual_incidence_certificate_lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ X Y : Finset ℕ,
      (Icc 1 N).image (fun n : ℕ => n^2) ⊆ X+Y →
      (N:ℝ)^(1-ε) ≤ Y.card*Real.sqrt X.card + X.card := by
  obtain ⟨K,hK,hcoverBound⟩ := finite_cover_bound ε hε
  have hlarge : Tendsto (fun N : ℕ => (N:ℝ)^ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [hlarge.eventually_ge_atTop K,hlarge.eventually_ge_atTop 1,eventually_ge_atTop 1]
    with N hlarge hlarge1 hN
  intro X Y hcover
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hpowpos : 0 < (N:ℝ)^ε := Real.rpow_pos_of_pos hNpos ε
  have hroot : Real.sqrt (K*(N:ℝ)^ε) ≤ (N:ℝ)^ε := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hpowpos.le,by nlinarith [mul_le_mul_of_nonneg_right hlarge hpowpos.le]⟩
  have hbound := hcoverBound N X Y hcover
  rw [Real.sqrt_mul (Nat.cast_nonneg X.card)] at hbound
  have hfirst := mul_le_mul_of_nonneg_left hroot
    (show (0:ℝ) ≤ Y.card*Real.sqrt X.card by positivity)
  have hlast := mul_le_mul_of_nonneg_right hlarge1 (Nat.cast_nonneg (α := ℝ) X.card)
  have htotal : (N:ℝ) ≤ (N:ℝ)^ε*(Y.card*Real.sqrt X.card+X.card) := by
    nlinarith only [hbound,hfirst,hlast]
  apply (mul_le_mul_iff_left₀ hpowpos).mp
  have hid : (N:ℝ)^ε*(N:ℝ)^(1-ε) = N := by
    rw [← Real.rpow_add hNpos]
    norm_num
  nlinarith only [hid,htotal]

#print axioms finite_cover_bound
#print axioms eventual_basis_lower
#print axioms eventual_exceeds_fixed_power
#print axioms eventual_incidence_certificate_lower
end Erdos773.SquareAdditiveBasis
