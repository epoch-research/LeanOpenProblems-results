import Submission.QuadraticBandPacking

/-!
Uniform bounds for levels of the carry correction in affine parabola lifts.
Construction-specific auxiliary work, not a settlement of Erdos 773.
-/
namespace Erdos773.AffineParabolaLevelBound
open Finset QuadraticBandPacking
set_option maxHeartbeats 2000000

/-- A short integral multiple of any slope has a small residue. -/
lemma short_slope (p Q : ℕ) (hp : 0 < p) (hQ : 0 < Q) (hpQ : p ≤ Q^2) (L : ℤ) :
    ∃ h j d : ℤ, 0 < h ∧ h ≤ Q ∧ |d| ≤ Q ∧ h*L=(p:ℤ)*j+d := by
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQ
  obtain ⟨j,h,hh₀,hhQ,habs⟩ := Real.exists_int_int_abs_mul_sub_le ((L:ℝ)/p) hQ
  let d : ℤ := h*L-(p:ℤ)*j
  have hd : |(d:ℝ)| ≤ (Q:ℝ) := by
    have he : (d:ℝ)=(p:ℝ)*((h:ℝ)*((L:ℝ)/p)-j) := by
      dsimp [d]
      push_cast
      field_simp
    rw [he,abs_mul,abs_of_pos hpR]
    calc
      _ ≤ (p:ℝ)*(1/((Q:ℝ)+1)) := mul_le_mul_of_nonneg_left habs hpR.le
      _ ≤ (Q:ℝ) := by
        have hpQR : (p:ℝ) ≤ (Q:ℝ)^2 := by exact_mod_cast hpQ
        rw [mul_one_div]
        apply (div_le_iff₀ (show (0:ℝ)<(Q:ℝ)+1 by positivity)).mpr
        nlinarith only [hpQR,hQR]
  refine ⟨h,j,d,hh₀,hhQ,?_,?_⟩
  · exact_mod_cast hd
  · dsimp [d]; ring

/-- Keys of all occupied bands lie in a short integer interval. -/
lemma key_bounds {p Q : ℕ} (hp : 0 < p) (hQ : 0 < Q)
    {A D C x : ℝ} {k : ℤ} (hA₀ : 0 ≤ A) (hAQ : A ≤ Q)
    (hD : |D| ≤ Q) (hC₀ : 0 ≤ C) (hCQ : C ≤ (Q:ℝ)*(p:ℝ)^2)
    (hx₀ : 0 ≤ x) (hxp : x ≤ p)
    (hlow : (k:ℝ)*(p:ℝ)^2+C ≤ quad A (D*p) x)
    (hhigh : quad A (D*p) x ≤ (k:ℝ)*(p:ℝ)^2+C+A*p) :
    -(3*(Q:ℤ)) ≤ k ∧ k ≤ 2*(Q:ℤ) := by
  have hp₀ : (0:ℝ) < p := by exact_mod_cast hp
  have hp₁ : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hQ₀ : (0:ℝ) ≤ Q := by positivity
  have hquad₀ : 0 ≤ A*x^2 := mul_nonneg hA₀ (sq_nonneg x)
  have hquad : A*x^2 ≤ (Q:ℝ)*(p:ℝ)^2 := by gcongr
  have hlin : |D*p*x| ≤ (Q:ℝ)*(p:ℝ)^2 := by
    rw [abs_mul,abs_mul,abs_of_pos hp₀,abs_of_nonneg hx₀]
    calc
      _ ≤ (Q:ℝ)*(p:ℝ)*(p:ℝ) := by gcongr
      _ = _ := by ring
  have hlin' := abs_le.mp hlin
  have herror : A*p ≤ (Q:ℝ)*(p:ℝ)^2 := by
    calc
      _ ≤ (Q:ℝ)*(p:ℝ) := mul_le_mul_of_nonneg_right hAQ hp₀.le
      _ ≤ (Q:ℝ)*(p:ℝ)^2 := by gcongr; nlinarith only [hp₁]
  have hlow' : -(3*(Q:ℝ))*(p:ℝ)^2 ≤ (k:ℝ)*(p:ℝ)^2 := by
    dsimp [quad] at hhigh
    nlinarith only [hhigh,hquad₀,hlin'.1,hCQ,herror]
  have hhigh' : (k:ℝ)*(p:ℝ)^2 ≤ (2*(Q:ℝ))*(p:ℝ)^2 := by
    dsimp [quad] at hlow
    nlinarith only [hlow,hquad,hlin'.2,hC₀]
  constructor
  · exact_mod_cast (mul_le_mul_iff_left₀ (sq_pos_of_pos hp₀)).mp hlow'
  · exact_mod_cast (mul_le_mul_iff_left₀ (sq_pos_of_pos hp₀)).mp hhigh'



def bandKey (p : ℕ) (L C h j b : ℤ) : ℤ :=
  h*((b^2/(p:ℤ)+L*b-C)/(p:ℤ))-j*b

lemma band_identity {p : ℕ} {L C h j d b : ℤ}
    (hslope : h*L=(p:ℤ)*j+d)
    (hc : b^2/(p:ℤ)+L*b ≡ C [ZMOD (p:ℤ)]) :
    h*b^2+d*(p:ℤ)*b=bandKey p L C h j b*(p:ℤ)^2+h*p*C+h*(b^2%(p:ℤ)) := by
  have hd : (p:ℤ) ∣ b^2/(p:ℤ)+L*b-C := by
    simpa only [neg_sub] using dvd_neg.mpr hc.dvd
  have hediv := Int.mul_ediv_cancel' hd
  have hr := Int.emod_add_mul_ediv (b^2) (p:ℤ)
  dsimp [bandKey]
  linear_combination -h*hr-h*(p:ℤ)*hediv-(p:ℤ)*b*hslope

lemma residue_bands {p : ℕ} (hp : 0 < p) {L C h j d b : ℤ}
    (hh : 0 < h) (hslope : h*L=(p:ℤ)*j+d)
    (hc : b^2/(p:ℤ)+L*b ≡ C [ZMOD (p:ℤ)]) :
    (bandKey p L C h j b:ℝ)*(p:ℝ)^2+(h:ℝ)*p*C ≤ quad h ((d:ℝ)*p) b ∧
    quad h ((d:ℝ)*p) b ≤ (bandKey p L C h j b:ℝ)*(p:ℝ)^2+(h:ℝ)*p*C+(h:ℝ)*p := by
  have hpZ : (0:ℤ) < p := by exact_mod_cast hp
  have he := band_identity hslope hc
  have hr₀ := Int.emod_nonneg (b^2) hpZ.ne'
  have hrp := Int.emod_lt_of_pos (b^2) hpZ
  have hlo : bandKey p L C h j b*(p:ℤ)^2+h*p*C ≤ h*b^2+d*p*b := by
    have hx := mul_nonneg hh.le hr₀
    nlinarith only [he,hx]
  have hhi : h*b^2+d*p*b ≤ bandKey p L C h j b*(p:ℤ)^2+h*p*C+h*p := by
    have hx := mul_le_mul_of_nonneg_left hrp.le hh.le
    nlinarith only [he,hx]
  constructor
  · dsimp [quad]; exact_mod_cast hlo
  · dsimp [quad]; exact_mod_cast hhi

/-- Uniformly in the affine slope and intercept, a carry level contains
at most 20Q integer labels when p<=Q² and 2Q<=p. -/
theorem uniform_level_card (p Q : ℕ) (hp : 0 < p) (hQ : 0 < Q)
    (hpQ : p ≤ Q^2) (hQp : 2*Q ≤ p) (L C : ℤ)
    (hC₀ : 0 ≤ C) (hCp : C ≤ p) (S : Finset ℤ)
    (hS : ∀ b ∈ S, 0 ≤ b ∧ b ≤ p)
    (hc : ∀ b ∈ S, b^2/(p:ℤ)+L*b ≡ C [ZMOD (p:ℤ)]) :
    S.card ≤ 20*Q := by
  classical
  obtain ⟨h,j,d,hh₀,hhQ,hdQ,hslope⟩ := short_slope p Q hp hQ hpQ L
  have hpR : (0:ℝ) < p := by exact_mod_cast hp
  have hhR : (0:ℝ) < h := by exact_mod_cast hh₀
  have hhQR : (h:ℝ) ≤ Q := by exact_mod_cast hhQ
  have hdQR : |(d:ℝ)| ≤ Q := by exact_mod_cast hdQ
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQ
  have hsmall : 2*(h:ℝ) ≤ p := by
    have hQpR : 2*(Q:ℝ) ≤ p := by exact_mod_cast hQp
    linarith only [hhQR,hQpR]
  have hpQR : (p:ℝ) ≤ (Q:ℝ)^2 := by exact_mod_cast hpQ
  let key : ℤ → ℤ := bandKey p L C h j
  let offset : ℝ := (h:ℝ)*p*C
  have hoff₀ : 0 ≤ offset := by dsimp [offset]; positivity
  have hoffQ : offset ≤ (Q:ℝ)*(p:ℝ)^2 := by
    have hCpR : (C:ℝ) ≤ p := by exact_mod_cast hCp
    dsimp [offset]
    calc
      _ ≤ (Q:ℝ)*(p:ℝ)*(p:ℝ) := by gcongr
      _ = _ := by ring
  have hbands (b : ℤ) (hb : b ∈ S) :
      (key b:ℝ)*(p:ℝ)^2+offset ≤ quad h ((d:ℝ)*p) b ∧
      quad h ((d:ℝ)*p) b ≤ (key b:ℝ)*(p:ℝ)^2+offset+(h:ℝ)*p :=
    residue_bands hp hh₀ hslope (hc b hb)
  have hkeys : S.image key ⊆ Icc (-(3*(Q:ℤ))) (2*(Q:ℤ)) := by
    intro k hk
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hk
    have hx₀ : (0:ℝ) ≤ b := by exact_mod_cast (hS b hb).1
    have hxp : (b:ℝ) ≤ p := by exact_mod_cast (hS b hb).2
    exact mem_Icc.mpr (key_bounds hp hQ hhR.le hhQR hdQR hoff₀ hoffQ hx₀ hxp
      (hbands b hb).1 (hbands b hb).2)
  have hKcard : ((S.image key).card:ℝ) ≤ 5*(Q:ℝ)+1 := by
    have hn : (Icc (-(3*(Q:ℤ))) (2*(Q:ℤ))).card=5*Q+1 := by
      rw [Int.card_Icc]
      omega
    have hh := card_le_card hkeys
    rw [hn] at hh
    exact_mod_cast hh
  let U := S.filter (fun b : ℤ => (0:ℝ) ≤ 2*(h:ℝ)*b+(d:ℝ)*p)
  let V := S.filter (fun b : ℤ => ¬ (0:ℝ) ≤ 2*(h:ℝ)*b+(d:ℝ)*p)
  have hpartition : U.card+V.card=S.card := by
    simpa only [U,V] using card_filter_add_card_filter_not (s:=S)
      (fun b : ℤ => (0:ℝ) ≤ 2*(h:ℝ)*b+(d:ℝ)*p)
  have hU : (U.card:ℝ) ≤ 8*(Q:ℝ)+1 := by
    have hcoords : ∀ b ∈ U, (0:ℝ) ≤ b ∧ (b:ℝ) ≤ 0+p := by
      intro b hb
      have hh := hS b (mem_filter.mp hb).1
      constructor <;> norm_cast <;> omega
    have hh := branch_card U key h ((d:ℝ)*p) p Q 0 offset hhR hpR hQR.le hsmall hpQR
      hcoords (fun b hb => (mem_filter.mp hb).2)
      (fun b hb => hbands b (mem_filter.mp hb).1)
    have hsub : U.image key ⊆ S.image key := image_subset_image (filter_subset _ _)
    have hcardR : ((U.image key).card:ℝ) ≤ (S.image key).card := by exact_mod_cast card_le_card hsub
    linarith only [hh,hcardR,hKcard,hhQR]
  have hV : (V.card:ℝ) ≤ 8*(Q:ℝ)+1 := by
    let T := V.image (fun b : ℤ => -b)
    let key' : ℤ → ℤ := fun b => key (-b)
    have hTcard : T.card=V.card := card_image_of_injective _ neg_injective
    have hTkeys : T.image key'=V.image key := by
      simp only [T,key',image_image,Function.comp_def,neg_neg]
    have hcoords : ∀ b ∈ T, -(p:ℝ) ≤ b ∧ (b:ℝ) ≤ -(p:ℝ)+p := by
      intro b hb
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
      have hh := hS c (mem_filter.mp hc).1
      constructor <;> norm_cast <;> omega
    have hder : ∀ b ∈ T, (0:ℝ) ≤ 2*(h:ℝ)*b-((d:ℝ)*p) := by
      intro b hb
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
      have hh := (mem_filter.mp hc).2
      push_cast
      linarith only [hh]
    have hbandT : ∀ b ∈ T,
        (key' b:ℝ)*(p:ℝ)^2+offset ≤ quad h (-((d:ℝ)*p)) b ∧
        quad h (-((d:ℝ)*p)) b ≤ (key' b:ℝ)*(p:ℝ)^2+offset+(h:ℝ)*p := by
      intro b hb
      obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
      have hh := hbands c (mem_filter.mp hc).1
      simpa only [key',neg_neg,Int.cast_neg,quad,neg_sq,neg_mul_neg] using hh
    have hh := branch_card T key' h (-((d:ℝ)*p)) p Q (-(p:ℝ)) offset
      hhR hpR hQR.le hsmall hpQR hcoords (by simpa only [sub_eq_add_neg] using hder) hbandT
    rw [hTcard,hTkeys] at hh
    have hsub : V.image key ⊆ S.image key := image_subset_image (filter_subset _ _)
    have hcardR : ((V.image key).card:ℝ) ≤ (S.image key).card := by exact_mod_cast card_le_card hsub
    linarith only [hh,hcardR,hKcard,hhQR]
  have hpartR : (U.card:ℝ)+V.card=S.card := by exact_mod_cast hpartition
  have hQone : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hresult : (S.card:ℝ) ≤ 20*(Q:ℝ) := by linarith only [hU,hV,hpartR,hQone]
  exact_mod_cast hresult

/-- A square-root bound for an arbitrary affine carry level, including
small moduli and arbitrary integer intercepts. No primality is needed. -/
theorem level_card_sq (p : ℕ) (hp : 0 < p) (L C : ℤ) (S : Finset ℤ)
    (hS : ∀ b ∈ S, 0 ≤ b ∧ b ≤ p)
    (hc : ∀ b ∈ S, b^2/(p:ℤ)+L*b ≡ C [ZMOD (p:ℤ)]) :
    S.card^2 ≤ 1600*p := by
  let Q := p.sqrt+1
  have hQ : 0 < Q := by dsimp [Q]; omega
  have hpQ : p ≤ Q^2 := by
    have hh := Nat.lt_succ_sqrt p
    dsimp [Q]
    nlinarith only [hh]
  have hs : 1 ≤ p.sqrt := Nat.sqrt_pos.mpr hp
  have hQQ : Q ≤ 2*p.sqrt := by dsimp [Q]; omega
  have hQQsq : Q^2 ≤ 4*p := by
    have h₁ := Nat.pow_le_pow_left hQQ 2
    have h₂ := Nat.sqrt_le p
    nlinarith only [h₁,h₂]
  by_cases hQp : 2*Q ≤ p
  · have hpZ : (0:ℤ) < p := by exact_mod_cast hp
    have hC₀ := Int.emod_nonneg C hpZ.ne'
    have hCp := (Int.emod_lt_of_pos C hpZ).le
    have hc' : ∀ b ∈ S, b^2/(p:ℤ)+L*b ≡ C%(p:ℤ) [ZMOD (p:ℤ)] := by
      intro b hb
      exact (hc b hb).trans (by simp only [Int.ModEq,Int.emod_emod])
    have hh := uniform_level_card p Q hp hQ hpQ hQp L (C%(p:ℤ)) hC₀ hCp S hS hc'
    have hh2 := Nat.pow_le_pow_left hh 2
    nlinarith only [hh2,hQQsq]
  · have hs2 : p.sqrt ≤ 2 := by
      by_contra hn
      have h3 : 3 ≤ p.sqrt := by omega
      have hm := Nat.mul_le_mul_left p.sqrt h3
      have hsquare := Nat.sqrt_le p
      dsimp [Q] at hQp
      nlinarith only [hm,hsquare,hQp,h3]
    have hp5 : p ≤ 5 := by dsimp [Q] at hQp; omega
    have hsub : S ⊆ Icc 0 (p:ℤ) := fun b hb => mem_Icc.mpr (hS b hb)
    have hcount : S.card ≤ p+1 := by
      have hh := card_le_card hsub
      rw [Int.card_Icc] at hh
      simpa using hh
    have hcount6 : S.card ≤ 6 := by omega
    have hh := Nat.pow_le_pow_left hcount6 2
    omega

#print axioms short_slope
#print axioms uniform_level_card
#print axioms level_card_sq

end Erdos773.AffineParabolaLevelBound
