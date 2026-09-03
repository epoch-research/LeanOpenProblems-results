import Submission.FiniteImageEnergy

/-! Positive quadratic parameter counts and logarithmic equal-value energy
force divergent reciprocal mass on DISTINCT values. Auxiliary only. -/
namespace Erdos1206.QuadraticImageMass
open Finset Filter FiniteImageEnergy
open scoped Classical Topology

def grid (k : ℕ) : Finset (ℕ × ℕ) := range (2^k) ×ˢ range (2^k)
noncomputable def annulus (P : ℕ × ℕ → Prop) (k : ℕ) : Finset (ℕ × ℕ) :=
  (grid (k+1)).filter P \ grid k

lemma annulus_subset (P : ℕ × ℕ → Prop) (k : ℕ) : annulus P k⊆grid (k+1) :=
  sdiff_subset.trans (filter_subset _ _)

lemma annulus_lower {P : ℕ × ℕ → Prop} {k : ℕ} {x : ℕ × ℕ}
    (hx : x∈annulus P k) : 2^k ≤ max x.1 x.2 := by
  have hn := (mem_sdiff.mp hx).2
  simp only [grid,mem_product,mem_range,not_and_or,not_lt] at hn
  rcases hn with h | h
  · exact h.trans (le_max_left _ _)
  · exact h.trans (le_max_right _ _)

lemma annulus_card {P : ℕ × ℕ → Prop} {k : ℕ}
    (hmany : ((2:ℝ)^(k+1))^2/2 ≤ ((grid (k+1)).filter P).card) :
    ((2:ℝ)^k)^2 ≤ (annulus P k).card := by
  have hc := card_le_card_sdiff_add_card (s := (grid (k+1)).filter P) (t := grid k)
  have hc' : (((grid (k+1)).filter P).card:ℝ) ≤ (annulus P k).card+(grid k).card := by exact_mod_cast hc
  have hgrid : ((grid k).card:ℝ)=((2:ℝ)^k)^2 := by simp [grid,card_product,pow_two]
  rw [hgrid] at hc'
  rw [pow_succ (2:ℝ) k] at hmany
  nlinarith

lemma annulus_mass_lower (P : ℕ × ℕ → Prop) (f : ℕ × ℕ → ℕ)
    (K C L k : ℕ) (hK : 0<K) (hC : 0<C)
    (hpos : ∀ x, P x → 0<f x)
    (hupp : ∀ x∈grid (k+1), f x≤K*(2^(k+1))^2)
    (hen : (equalPairs (grid (k+1)) f).card ≤ C*(k+1+L)*(2^(k+1))^2)
    (hmany : ((2:ℝ)^(k+1))^2/2 ≤ ((grid (k+1)).filter P).card) :
    1/(16*(K:ℝ)*C*(k+1+L)) ≤ ∑n∈(annulus P k).image f, (1:ℝ)/n := by
  let S := annulus P k
  let M : ℝ := ∑n∈S.image f, (1:ℝ)/n
  let T : ℝ := ((2:ℝ)^k)^2
  have hT : 0<T := by dsimp [T]; positivity
  have hM : 0≤M := sum_nonneg (fun _ _ => by positivity)
  have hcard : T ≤ S.card := annulus_card hmany
  have hE : ((equalPairs S f).card:ℝ) ≤ 4*(C:ℝ)*(k+1+L)*T := by
    have hh := (card_le_card (equalPairs_mono (annulus_subset P k) f)).trans hen
    have hh' : ((equalPairs S f).card:ℝ) ≤ (C:ℝ)*(k+1+L)*((2:ℝ)^(k+1))^2 := by exact_mod_cast hh
    dsimp [T]
    rw [pow_succ (2:ℝ) k] at hh'
    nlinarith only [hh']
  have hI : ((S.image f).card:ℝ) ≤ (4*(K:ℝ)*T)*M := by
    apply image_card_le_height_mul_mass S f (by positivity)
    intro x hx
    have hxg := annulus_subset P k hx
    have hxP := (mem_filter.mp (mem_sdiff.mp hx).1).2
    refine ⟨hpos x hxP,?_⟩
    have hh := hupp x hxg
    have hh' : (f x:ℝ) ≤ (K:ℝ)*((2:ℝ)^(k+1))^2 := by exact_mod_cast hh
    dsimp [T]
    rw [pow_succ (2:ℝ) k] at hh'
    nlinarith only [hh']
  have hs : T^2 ≤ (S.card:ℝ)^2 := pow_le_pow_left₀ hT.le hcard 2
  have hCE := image_card_energy S f
  have hprod := mul_le_mul hI hE (by positivity : (0:ℝ)≤(equalPairs S f).card)
    (mul_nonneg (by positivity) hM)
  have hh : T^2*1 ≤ T^2*(16*(K:ℝ)*C*(k+1+L)*M) := by
    nlinarith only [hs,hCE,hprod]
  have hh' : 1 ≤ 16*(K:ℝ)*C*(k+1+L)*M :=
    (mul_le_mul_iff_right₀ (sq_pos_of_pos hT)).mp hh
  have hden : 0 < 16*(K:ℝ)*C*(k+1+L) := by
    have hKR : (0:ℝ)<K := by exact_mod_cast hK
    have hCR : (0:ℝ)<C := by exact_mod_cast hC
    positivity
  exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hh')

lemma annulus_image_disjoint (P : ℕ × ℕ → Prop) (f : ℕ × ℕ → ℕ) (K R : ℕ)
    (hR : 0<R) (hgap : 4*K<(2^R)^2)
    (hlow : ∀ x, (max x.1 x.2)^2≤f x)
    (hupp : ∀ k, ∀ x∈grid k, f x≤K*(2^k)^2) :
    Pairwise (fun i j => Disjoint ((annulus P (R*i)).image f) ((annulus P (R*j)).image f)) := by
  suffices h : ∀ i j, i<j → Disjoint ((annulus P (R*i)).image f) ((annulus P (R*j)).image f) by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hh | hh
    · exact h i j hh
    · exact (h j i hh).symm
  intro i j hij
  apply disjoint_left.mpr
  intro n hni hnj
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hni
  obtain ⟨y,hy,he⟩ := mem_image.mp hnj
  have hxu := hupp (R*i+1) x (annulus_subset P (R*i) hx)
  have hyl : (2^(R*j))^2≤f y :=
    (Nat.pow_le_pow_left (annulus_lower hy) 2).trans (hlow y)
  have hexp : R*i+R ≤ R*j := by nlinarith
  have hpow := Nat.pow_le_pow_right (n := 2) (by decide) hexp
  have hsquare := Nat.pow_le_pow_left hpow 2
  have hlt := Nat.mul_lt_mul_of_pos_right hgap (show 0<((2:ℕ)^(R*i))^2 by positivity)
  have hbound : K*(2^(R*i+1))^2 < (2^(R*j))^2 := by
    rw [pow_succ (2:ℕ) (R*i)]
    rw [pow_add,mul_pow] at hsquare
    nlinarith only [hlt,hsquare]
  omega

/-- A positive parameter proportion, quadratic upper/lower heights, and an
O(N² log N) equal-value energy bound give nonsummability on the image set. -/
theorem distinct_values_not_summable (P : ℕ × ℕ → Prop) (f : ℕ × ℕ → ℕ)
    (K C L : ℕ) (hK : 0<K) (hC : 0<C)
    (hpos : ∀ x, P x → 0<f x)
    (hlow : ∀ x, (max x.1 x.2)^2≤f x)
    (hupp : ∀ k, ∀ x∈grid k, f x≤K*(2^k)^2)
    (hen : ∀ k, (equalPairs (grid k) f).card ≤ C*(k+L)*(2^k)^2)
    (hmany : ∀ᶠ k : ℕ in atTop, ((2:ℝ)^k)^2/2 ≤ ((grid k).filter P).card) :
    ¬ Summable (fun n : ℕ => if n∈f '' {x | P x} then (1:ℝ)/n else 0) := by
  intro hs
  let R := 4*K+1
  have hR : 0<R := by dsimp [R]; omega
  have hgap : 4*K<(2^R)^2 := by
    have hh : R<(2:ℕ)^R := Nat.lt_two_pow_self
    have hp : 1≤(2:ℕ)^R := Nat.one_le_two_pow
    dsimp only [R] at hh
    dsimp only [R]
    nlinarith
  let S (j : ℕ) := (annulus P (R*j)).image f
  have hsub : ∀ j, (S j:Set ℕ)⊆f '' {x | P x} := by
    intro j n hn
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
    exact ⟨x,(mem_filter.mp (mem_sdiff.mp hx).1).2,rfl⟩
  have hmass : Summable (fun j => ∑n∈S j, (1:ℝ)/n) :=
    disjoint_masses_summable hs S hsub (annulus_image_disjoint P f K R hR hgap hlow hupp)
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hmany
  have hev : ∀ᶠ j : ℕ in atTop,
      1/(16*(K:ℝ)*C*(R+L+1)*(j+1)) ≤ ∑n∈S j, (1:ℝ)/n := by
    filter_upwards [eventually_ge_atTop J] with j hj
    have hj' : J≤R*j+1 := by have hh : 1≤R := hR; nlinarith
    have hh := annulus_mass_lower P f K C L (R*j) hK hC hpos
      (hupp _) (hen _) (hJ _ hj')
    have hKR : (0:ℝ)<K := by exact_mod_cast hK
    have hCR : (0:ℝ)<C := by exact_mod_cast hC
    have hRR : (0:ℝ)<R := by exact_mod_cast hR
    have hden : 16*(K:ℝ)*C*((R*j:ℕ)+1+L) ≤ 16*(K:ℝ)*C*(R+L+1)*(j+1) := by
      push_cast
      have h := mul_nonneg (show (0:ℝ)≤L+1 by positivity) (show (0:ℝ)≤j by positivity)
      have hc : 0≤16*(K:ℝ)*C := by positivity
      nlinarith
    exact (one_div_le_one_div_of_le (by positivity) hden).trans hh
  have hsmall : Summable (fun j : ℕ => 1/(16*(K:ℝ)*C*(R+L+1)*(j+1))) := by
    apply hmass.of_norm_bounded_eventually_nat
    filter_upwards [hev] with j hj
    simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : (0:ℝ)≤1/(16*(K:ℝ)*C*(R+L+1)*(j+1)))] using hj
  have hKR : (K:ℝ)≠0 := by exact_mod_cast hK.ne'
  have hCR : (C:ℝ)≠0 := by exact_mod_cast hC.ne'
  have hRLR : (R:ℝ)+L+1 ≠ 0 := by positivity
  have hshift : Summable (fun j : ℕ => (1:ℝ)/(j+1)) := by
    convert hsmall.mul_left (16*(K:ℝ)*C*(R+L+1)) using 1
    funext j
    have hj : (j:ℝ)+1 ≠ 0 := by positivity
    field_simp
  apply Real.not_summable_natCast_inv
  have hh : Summable (fun j : ℕ => (((j+1:ℕ):ℝ))⁻¹) := by simpa only [Nat.cast_add,Nat.cast_one,one_div] using hshift
  exact (summable_nat_add_iff 1).mp hh

#print axioms distinct_values_not_summable
end Erdos1206.QuadraticImageMass
