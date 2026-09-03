import Submission.Explore
import Submission.NatPairAlgebraExplore
import Submission.CountingExplore
import Submission.SaturatingCyclicFamilyExplore

/-! The integer cost of placing a dense finite palette member in one block.
This restricts a proposed placement method; it does not disprove Erdos 66. -/
namespace Erdos66PalettePlacementCost
open Filter AdditiveCombinatorics Erdos66NatPairAlgebra
open scoped Topology Classical
set_option maxHeartbeats 1500000

lemma window_pair_mass (F : Finset ℕ) (a M : ℕ)
    (hF : ∀ x∈F, a ≤ x ∧ x < a+M) :
    F.card^2=∑ n∈Finset.Ico (2*a) (2*a+2*M), sumRep (F : Set ℕ) n := by
  simp_rw [←pairs_self]
  rw [pairs_sum]
  have he : ((F.product F).filter (fun p ↦ p.1+p.2 ∈ Finset.Ico (2*a) (2*a+2*M)))=F.product F := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hp
    have h₁ := hF p.1 hp₁
    have h₂ := hF p.2 hp₂
    exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  rw [he, Finset.product_eq_sprod, Finset.card_product, pow_two]

/-- A block's self-pair mass must fit under the old logarithmic envelope. -/
theorem finite_window_cost (A : Set ℕ) (F : Finset ℕ) (a M : ℕ) (K C : ℝ)
    (hC : 0 ≤ C) (hA : ∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2))
    (hsub : (F : Set ℕ) ⊆ A) (hF : ∀ x∈F, a ≤ x ∧ x < a+M) :
    (F.card : ℝ)^2 ≤ 2*(M : ℝ)*(K+C*Real.log (2*(a : ℝ)+2*M+2)) := by
  have hmass : (F.card : ℝ)^2=∑ n∈Finset.Ico (2*a) (2*a+2*M), (sumRep (F : Set ℕ) n : ℝ) := by
    exact_mod_cast window_pair_mass F a M hF
  rw [hmass]
  calc
    _ ≤ ∑ _n∈Finset.Ico (2*a) (2*a+2*M), (K+C*Real.log (2*(a : ℝ)+2*M+2)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hmono : (sumRep (F : Set ℕ) n : ℝ) ≤ sumRep A n := by exact_mod_cast Erdos66Explore.sumRep_mono hsub n
      have hnb : (n : ℝ)+2 ≤ 2*(a : ℝ)+2*M+2 := by exact_mod_cast Nat.add_le_add_right (Finset.mem_Ico.mp hn).2.le 2
      have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ)+2) hnb
      exact hmono.trans ((hA n).trans (by gcongr))
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_Ico,Nat.add_sub_cancel_left,Nat.cast_mul,Nat.cast_ofNat]

noncomputable def placed (M : ℕ) (a : ℕ) (B : Finset (ZMod M)) : Finset ℕ :=
  B.image (fun b ↦ a+b.val)

lemma placed_card (M : ℕ) [NeZero M] (a : ℕ) (B : Finset (ZMod M)) :
    (placed M a B).card=B.card := by
  apply Finset.card_image_of_injective
  intro x y hxy
  exact ZMod.val_injective M (Nat.add_left_cancel hxy)

lemma placed_bounds (M : ℕ) [NeZero M] (a : ℕ) (B : Finset (ZMod M)) :
    ∀ x∈placed M a B, a ≤ x ∧ x < a+M := by
  intro x hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
  have hh := ZMod.val_lt b
  omega

/-- Applies to every palette member, without assuming cyclic flatness. -/
theorem palette_member_cost (A : Set ℕ) (M : ℕ) [NeZero M] (a : ℕ)
    (B : Finset (ZMod M)) (K C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2))
    (hB : (placed M a B : Set ℕ) ⊆ A) :
    (B.card : ℝ)^2 ≤ 2*(M : ℝ)*(K+C*Real.log (2*(a : ℝ)+2*M+2)) := by
  have hh := finite_window_cost A (placed M a B) a M K C hC hA hB (placed_bounds M a B)
  simpa only [placed_card] using hh

/-- A positive-density member needs a logarithm comparable to its block width. -/
theorem positive_density_cost (A : Set ℕ) (M : ℕ) [NeZero M] (a : ℕ)
    (B : Finset (ZMod M)) (K C ρ : ℝ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ)
    (hA : ∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2))
    (hB : (placed M a B : Set ℕ) ⊆ A) (hdense : ρ*M ≤ B.card) :
    ρ^2*M ≤ 2*K+2*C*Real.log (2*(a : ℝ)+2*M+2) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hh := palette_member_cost A M a B K C hC hA hB
  have hs := pow_le_pow_left₀ (mul_nonneg hρ hM.le) hdense 2
  have hmul : (ρ^2*M)*M ≤ (2*K+2*C*Real.log (2*(a : ℝ)+2*M+2))*M := by nlinarith
  exact (mul_le_mul_iff_left₀ hM).mp hmul

/-- In particular, fixed positive density forces exponential placement scale.
This is a bound on the integer realization, not on the finite cyclic palette. -/
theorem positive_density_exponential_cost (A : Set ℕ) (M : ℕ) [NeZero M] (a : ℕ)
    (B : Finset (ZMod M)) (K C ρ : ℝ) (hC : 0 < C) (hρ : 0 ≤ ρ)
    (hA : ∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2))
    (hB : (placed M a B : Set ℕ) ⊆ A) (hdense : ρ*M ≤ B.card) :
    Real.exp ((ρ^2*M-2*K)/(2*C)) ≤ 2*(a : ℝ)+2*M+2 := by
  have hh := positive_density_cost A M a B K C ρ hC.le hρ hA hB hdense
  have hl : (ρ^2*M-2*K)/(2*C) ≤ Real.log (2*(a : ℝ)+2*M+2) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*C)).mpr
    nlinarith
  have he := Real.exp_le_exp.mpr hl
  rwa [Real.exp_log (by positivity)] at he


/-- Uniformly in the ambient set, blocks of fixed positive density cannot be
placed at polynomial locations under a fixed logarithmic envelope. -/
theorem eventually_no_polynomial_dense_window (K C ρ : ℝ)
    (hC : 0 ≤ C) (hρ : 0 < ρ) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ M : ℕ in atTop, ∀ (A : Set ℕ) (F : Finset ℕ) (a : ℕ),
      (∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2)) →
      (F : Set ℕ) ⊆ A → (∀ x∈F, a ≤ x ∧ x < a+M) →
      a ≤ M^d → ¬ (ρ*M ≤ F.card) := by
  have hlog : Tendsto (fun M : ℕ ↦ Real.log (M : ℝ)/(M : ℝ))
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun M : ℕ ↦
      (2*K+2*C*Real.log 6)/(M : ℝ)+(2*C*d)*(Real.log (M : ℝ)/(M : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using
      (tendsto_const_div_atTop_nhds_zero_nat (2*K+2*C*Real.log 6)).add
        (hlog.const_mul (2*C*d))
  filter_upwards [eventually_ge_atTop 1,
    hsmall.eventually_lt_const (sq_pos_of_pos hρ)] with M hM hsmall
  intro A F a hA hsub hF ha hdense
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0<M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hp : (M : ℝ) ≤ (M : ℝ)^d := by exact_mod_cast Nat.le_pow hd
  have hap : (a : ℝ) ≤ (M : ℝ)^d := by exact_mod_cast ha
  have hl : Real.log (2*(a : ℝ)+2*M+2) ≤ Real.log 6+d*Real.log (M : ℝ) := by
    calc
      _ ≤ Real.log (6*(M : ℝ)^d) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (pow_ne_zero _ hMp.ne'),Real.log_pow]
  have hcost := finite_window_cost A F a M K C hC hA hsub hF
  have hs := pow_le_pow_left₀ (mul_nonneg hρ.le hMp.le) hdense 2
  have hm : (ρ^2*M)*M ≤ (2*K+2*C*Real.log (2*(a : ℝ)+2*M+2))*M := by nlinarith
  have hc := (mul_le_mul_iff_left₀ hMp).mp hm
  have hupper : ρ^2*M ≤ 2*K+2*C*Real.log 6+(2*C*d)*Real.log (M : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ 2*C)
    nlinarith
  have he : (2*K+2*C*Real.log 6)/(M : ℝ)+
      (2*C*d)*(Real.log (M : ℝ)/(M : ℝ)) =
      (2*K+2*C*Real.log 6+(2*C*d)*Real.log (M : ℝ))/M := by ring
  rw [he] at hsmall
  have hh := (div_lt_iff₀ hMp).mp hsmall
  linarith


/-- A sharper version at the sparse logarithmic scale: a block whose squared
cardinality exceeds lambda M log M needs exponent at least lambda/(2C).
This is uniform in the finite block and in the ambient set. -/
theorem eventually_no_oversized_logarithmic_window (K C lmb : ℝ)
    (hC : 0 ≤ C) (d : ℕ) (hd : 0 < d) (hlmb : 2*C*d < lmb) :
    ∀ᶠ M : ℕ in atTop, ∀ (A : Set ℕ) (F : Finset ℕ) (a : ℕ),
      (∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2)) →
      (F : Set ℕ) ⊆ A → (∀ x∈F, a ≤ x ∧ x < a+M) →
      a ≤ M^d → ¬ (lmb*M*Real.log (M : ℝ) ≤ (F.card : ℝ)^2) := by
  have hlog : Tendsto (fun M : ℕ ↦ Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := (hlog.const_div_atTop (2*K+2*C*Real.log 6)).eventually_lt_const
    (sub_pos.mpr hlmb)
  filter_upwards [eventually_ge_atTop 2,hsmall] with M hM hsmall
  intro A F a hA hsub hF ha hlarge
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0<M by omega)
  have hM1 : (1 : ℝ) < M := by exact_mod_cast (show 1<M by omega)
  have hlogp : 0 < Real.log (M : ℝ) := Real.log_pos hM1
  have hp : (M : ℝ) ≤ (M : ℝ)^d := by exact_mod_cast Nat.le_pow hd
  have hap : (a : ℝ) ≤ (M : ℝ)^d := by exact_mod_cast ha
  have hl : Real.log (2*(a : ℝ)+2*M+2) ≤ Real.log 6+d*Real.log (M : ℝ) := by
    calc
      _ ≤ Real.log (6*(M : ℝ)^d) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_mul (by norm_num) (pow_ne_zero _ hMp.ne'),Real.log_pow]
  have hcost := finite_window_cost A F a M K C hC hA hsub hF
  have hm : (lmb*Real.log (M : ℝ))*M ≤
      (2*K+2*C*Real.log (2*(a : ℝ)+2*M+2))*M := by nlinarith
  have hc := (mul_le_mul_iff_left₀ hMp).mp hm
  have hh := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ 2*C)
  have hs := (div_lt_iff₀ hlogp).mp hsmall
  nlinarith

/-- Consequence for a sequence of block placements with a limiting logarithmic
cardinality coefficient. No cyclic flatness assumption is needed. -/
theorem logarithmic_window_coefficient_le (A : Set ℕ) (K C β : ℝ)
    (hC : 0 ≤ C) (d : ℕ) (hd : 0 < d)
    (hA : ∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2))
    (M a : ℕ → ℕ) (F : ℕ → Finset ℕ) (hM : Tendsto M atTop atTop)
    (hdata : ∀ᶠ k : ℕ in atTop,
      (F k : Set ℕ) ⊆ A ∧ (∀ x∈F k, a k ≤ x ∧ x < a k+M k) ∧ a k ≤ (M k)^d)
    (hβ : Tendsto (fun k ↦ (F k |>.card : ℝ)^2 /
      ((M k : ℝ)*Real.log (M k : ℝ))) atTop (𝓝 β)) :
    β ≤ 2*C*d := by
  by_contra hnot
  have hlt : 2*C*d < β := lt_of_not_ge hnot
  let lmb := (2*C*d+β)/2
  have hlmb : 2*C*d < lmb := by dsimp [lmb]; linarith
  have hlmbβ : lmb < β := by dsimp [lmb]; linarith
  have hno := hM.eventually (eventually_no_oversized_logarithmic_window K C lmb hC d hd hlmb)
  obtain ⟨k,hk,hkdata,hkM,hkβ⟩ := (hno.and (hdata.and
    ((hM.eventually (eventually_ge_atTop 2)).and (hβ.eventually_const_lt hlmbβ)))).exists
  obtain ⟨hsub,hF,ha⟩ := hkdata
  have hMp : (0 : ℝ) < M k := by exact_mod_cast (show 0<M k by omega)
  have hlogp : 0 < Real.log (M k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1<M k by omega))
  have hlarge := (lt_div_iff₀ (mul_pos hMp hlogp)).mp hkβ
  apply hk A (F k) (a k) hA hsub hF ha
  nlinarith


/-- A sufficiently high logarithmic sparse palette level already exceeds the
integer block budget. In particular the issue is not limited to dense members
near the full group. -/
theorem eventually_no_high_palette_level (K C c₀ η : ℝ) (H d : ℕ)
    (hC : 0 ≤ C) (hη : η ≤ 1) (hd : 0 < d)
    (hlarge : 2*C*d < (1-η)*c₀*(H : ℝ)^2) :
    ∀ᶠ M : ℕ in atTop, ∀ (A : Set ℕ) (B : Finset (ZMod M)) (a : ℕ) (μ : ℝ),
      (∀ n, (sumRep A n : ℝ) ≤ K+C*Real.log ((n : ℝ)+2)) →
      (placed M a B : Set ℕ) ⊆ A → a ≤ M^d → c₀*Real.log (M : ℝ) ≤ μ →
      (∀ z, |(Erdos66OuterCarryProfile.cyclicCount M B B z : ℝ)-μ*(H : ℝ)^2| ≤
        η*(μ*(H : ℝ)^2)) → False := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_no_oversized_logarithmic_window K C ((1-η)*c₀*(H : ℝ)^2)
      hC d hd hlarge] with M hM hno
  intro A B a μ hA hsub ha hμ hflat
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0<M by omega)
  letI : NeZero M := ⟨by omega⟩
  have hm := (abs_le.mp (Erdos66SaturatingCyclicFamily.actualMean_error
    M B B (μ*(H : ℝ)^2) (η*(μ*(H : ℝ)^2)) hflat)).1
  have hmean : (1-η)*μ*(H : ℝ)^2 ≤ (B.card : ℝ)^2/M := by
    dsimp [Erdos66SaturatingCyclicFamily.actualMean] at hm
    ring_nf at hm ⊢
    linarith
  have hmul := mul_le_mul_of_nonneg_left hμ
    (mul_nonneg (sub_nonneg.mpr hη) (sq_nonneg (H : ℝ)))
  have hlow : ((1-η)*c₀*(H : ℝ)^2)*Real.log (M : ℝ) ≤ (B.card : ℝ)^2/M := by
    nlinarith
  have hcard := (le_div_iff₀ hMp).mp hlow
  apply hno A (placed M a B) a hA hsub (placed_bounds M a B) ha
  rw [placed_card]
  nlinarith

end Erdos66PalettePlacementCost
