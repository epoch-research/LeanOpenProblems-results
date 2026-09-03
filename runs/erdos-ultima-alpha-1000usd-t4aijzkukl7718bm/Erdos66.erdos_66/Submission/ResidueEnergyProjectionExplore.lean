import Submission.AutocorrelationStabilityExplore

/-! A finite residue-projection energy identity and its stability. These
mean-square estimates are not pointwise residue splitting. -/
namespace Erdos66ResidueEnergyProjection
open Erdos66MixedEnergy Erdos66AutocorrelationStability
open scoped Classical
set_option maxHeartbeats 2400000
variable {G H : Type*} [AddCommGroup G] [Fintype G] [AddCommGroup H] [Fintype H]

noncomputable def piece (φ : G →+ H) (f : G → ℝ) (i : H) (x : G) : ℝ :=
  if φ x=i then f x else 0

lemma sum_piece (φ : G →+ H) (f : G → ℝ) (x : G) : (∑ i : H, piece φ f i x)=f x := by
  simp [piece]

lemma sum_piece_product (φ : G →+ H) (f : G → ℝ) (x y : G) :
    (∑ i : H, piece φ f i x*piece φ f i y)=if φ y=φ x then f x*f y else 0 := by
  simp only [piece,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  split_ifs <;> simp

lemma sum_corr_piece (φ : G →+ H) (f : G → ℝ) (h : G) :
    (∑ i : H, corr (piece φ f i) h)=if φ h=0 then corr f h else 0 := by
  simp only [corr]
  rw [Finset.sum_comm]
  simp_rw [sum_piece_product]
  have he (x : G) : φ (x+h)=φ x ↔ φ h=0 := by rw [map_add,add_eq_left]
  simp_rw [he]
  split_ifs <;> simp

lemma sum_conv_piece (φ : G →+ H) (f : G → ℝ) (z : G) :
    (∑ i : H, conv f (piece φ f i) z)=conv f f z := by
  simp only [conv]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,sum_piece]

/-- The sum of full-versus-residue energies is the autocorrelation energy
restricted to differences in the kernel of the residue map. -/
lemma sum_energy_piece (φ : G →+ H) (f : G → ℝ) :
    (∑ i : H, energy f (piece φ f i))=
      ∑ h : G, if φ h=0 then corr f h^2 else 0 := by
  simp only [energy_eq_corr_inner]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,sum_corr_piece]
  apply Finset.sum_congr rfl
  intro h hh
  split_ifs <;> ring

noncomputable def variance (φ : G →+ H) (f : G → ℝ) : ℝ :=
  ∑ i : H, ∑ z : G, (conv f (piece φ f i) z-conv f f z/Fintype.card H)^2

lemma variance_nonneg (φ : G →+ H) (f : G → ℝ) : 0 ≤ variance φ f :=
  Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

lemma variance_eq (φ : G →+ H) (f : G → ℝ) :
    variance φ f=(∑ i : H, energy f (piece φ f i))-energy f f/Fintype.card H := by
  have hm : (Fintype.card H : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  rw [variance,Finset.sum_comm]
  have hp (z : G) :
      (∑ i : H, (conv f (piece φ f i) z-conv f f z/Fintype.card H)^2)=
        (∑ i : H, conv f (piece φ f i) z^2)-conv f f z^2/Fintype.card H := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    simp only [← Finset.sum_mul,← Finset.mul_sum,sum_conv_piece,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
    ring
  simp_rw [hp]
  rw [Finset.sum_sub_distrib,← Finset.sum_div,Finset.sum_comm]
  rfl

lemma variance_corr_eq (φ : G →+ H) (f : G → ℝ) :
    variance φ f=∑ h : G, ((if φ h=0 then (1 : ℝ) else 0)-1/Fintype.card H)*corr f h^2 := by
  rw [variance_eq,sum_energy_piece,energy_eq_corr_inner]
  simp only [← pow_two,Finset.sum_div,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  split_ifs <;> ring

lemma weighted_corr_energy_difference (w f g : G → ℝ) (hw : ∀ h, |w h| ≤ 1) :
    (∑ h : G, w h*(corr f h^2-corr g h^2))^2 ≤
      (∑ z : G, (conv f f z-conv g g z)^2)*(2*energy f f+2*energy g g) := by
  have he : (∑ h : G, w h*(corr f h^2-corr g h^2))=
      ∑ h : G, (w h*(corr f h-corr g h))*(corr f h+corr g h) := by
    apply Finset.sum_congr rfl
    intro h hh
    ring
  rw [he]
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun h ↦ w h*(corr f h-corr g h)) (fun h ↦ corr f h+corr g h)
  have ha : (∑ h : G, (w h*(corr f h-corr g h))^2) ≤
      ∑ z : G, (conv f f z-conv g g z)^2 := by
    apply le_trans _ (corr_error_le_conv_error f g)
    apply Finset.sum_le_sum
    intro h hh
    have hw2 := pow_le_pow_left₀ (abs_nonneg _) (hw h) 2
    rw [sq_abs,one_pow] at hw2
    simpa only [mul_pow,one_mul] using mul_le_mul_of_nonneg_right hw2 (sq_nonneg (corr f h-corr g h))
  have hb : (∑ h : G, (corr f h+corr g h)^2) ≤ 2*energy f f+2*energy g g := by
    rw [energy_eq_corr_inner f f,energy_eq_corr_inner g g,Finset.mul_sum,
      Finset.mul_sum,← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun h _ ↦ by nlinarith [sq_nonneg (corr f h-corr g h)])
  exact hs.trans (mul_le_mul ha hb (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)))

/-- A small self-convolution error controls the difference of residue
projection variances, for an arbitrary finite quotient group. -/
theorem variance_difference_sq (φ : G →+ H) (f g : G → ℝ) :
    (variance φ f-variance φ g)^2 ≤
      (∑ z : G, (conv f f z-conv g g z)^2)*(2*energy f f+2*energy g g) := by
  have hm : (1 : ℝ) ≤ Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hp : 0 ≤ 1/(Fintype.card H : ℝ) := by positivity
  have hu : 1/(Fintype.card H : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hm
  have hw (h : G) : |((if φ h=0 then (1 : ℝ) else 0)-1/Fintype.card H)| ≤ 1 := by
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hh := weighted_corr_energy_difference
    (fun h ↦ (if φ h=0 then (1 : ℝ) else 0)-1/Fintype.card H) f g hw
  rw [variance_corr_eq,variance_corr_eq,← Finset.sum_sub_distrib]
  convert hh using 2
  apply Finset.sum_congr rfl
  intro h hh
  ring

end Erdos66ResidueEnergyProjection
