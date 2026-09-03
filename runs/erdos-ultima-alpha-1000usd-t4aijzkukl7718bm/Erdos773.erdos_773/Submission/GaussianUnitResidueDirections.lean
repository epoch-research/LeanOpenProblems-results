import Submission.GaussianIncidentEncoding
import Submission.AllowedAlphabetRotationDivisibility

/-! Necessary restrictions on the ACTUAL normalized small Gaussian factor.
Signs and coordinate permutations of the output are included. These are
collision restrictions, not a Sidon construction. -/
namespace Erdos773.GaussianUnitResidueDirections
open Finset GaussianCollisionFactorization GaussianQuadrantFactor GaussianIncidentEncoding
set_option maxHeartbeats 2000000
noncomputable section

private lemma row_defect {Q a b c p s q t : ℤ}
    (hcop : IsCoprime Q a) (hab : a ≡ b [ZMOD Q])
    (hc : c ≡ t*a [ZMOD Q]) (he : q*c=p*a+s*b) : Q ∣ p+s-q*t := by
  have hh : q*(t*a) ≡ (p+s)*a [ZMOD Q] := by
    apply ((Int.ModEq.refl q).mul hc.symm).trans
    rw [he]
    convert (Int.ModEq.refl (p*a)).add ((Int.ModEq.refl s).mul hab.symm) using 1
    ring
  apply hcop.dvd_of_dvd_mul_left
  convert hh.dvd using 1; ring

private lemma combine_coprime {Q m n t : ℤ} (hc : IsCoprime m n)
    (hm : Q ∣ m*t) (hn : Q ∣ n*t) : Q ∣ t := by
  obtain ⟨u,v,huv⟩ := hc
  have hh := dvd_add (dvd_mul_of_dvd_right hm u) (dvd_mul_of_dvd_right hn v)
  convert hh using 1
  linear_combination -t*huv

/-- The four sign cases restrict one of the two coordinates or their sum
or difference. The mixed-sign cases need only a factor two. -/
theorem signed_rotation_divisibility {Q a b u v m n : ℤ}
    (hcop : IsCoprime Q a) (hmn : IsCoprime m n)
    (hab : a ≡ b [ZMOD Q])
    (hu : u ≡ a [ZMOD Q] ∨ u ≡ -a [ZMOD Q])
    (hv : v ≡ a [ZMOD Q] ∨ v ≡ -a [ZMOD Q])
    (hr : (m^2+n^2)*u=(m^2-n^2)*a+2*m*n*b)
    (hi : (m^2+n^2)*v= -(2*m*n)*a+(m^2-n^2)*b) :
    Q ∣ 4*n ∨ Q ∣ 4*m ∨ Q ∣ 2*(m-n) ∨ Q ∣ 2*(m+n) := by
  have hrow (t : ℤ) (hh : u ≡ t*a [ZMOD Q]) :
      Q ∣ m^2-n^2+2*m*n-(m^2+n^2)*t := row_defect hcop hab hh hr
  have hrow' (t : ℤ) (hh : v ≡ t*a [ZMOD Q]) :
      Q ∣ m^2-n^2-2*m*n-(m^2+n^2)*t := by
    convert row_defect hcop hab hh hi using 1; ring
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · have h1 := hrow 1 (by simpa using hu)
    have h2 := hrow' 1 (by simpa using hv)
    apply Or.inl
    apply combine_coprime hmn
    · convert dvd_sub h1 h2 using 1; ring
    · convert dvd_neg.mpr (dvd_add h1 h2) using 1; ring
  · have h1 := hrow 1 (by simpa using hu)
    have h2 := hrow' (-1) (by simpa using hv)
    apply Or.inr ∘ Or.inr ∘ Or.inl
    apply combine_coprime hmn
    · convert h2 using 1; ring
    · convert h1 using 1; ring
  · have h1 := hrow (-1) (by simpa using hu)
    have h2 := hrow' 1 (by simpa using hv)
    apply Or.inr ∘ Or.inr ∘ Or.inr
    apply combine_coprime hmn
    · convert h1 using 1; ring
    · convert dvd_neg.mpr h2 using 1; ring
  · have h1 := hrow (-1) (by simpa using hu)
    have h2 := hrow' (-1) (by simpa using hv)
    apply Or.inr ∘ Or.inl
    apply combine_coprime hmn
    · convert dvd_add h1 h2 using 1; ring
    · convert dvd_sub h1 h2 using 1; ring

private lemma signed_residue {Q a c d t : ℤ}
    (hc : a ≡ c [ZMOD Q]) (hd : a ≡ d [ZMOD Q])
    (ht : t^2 ∈ ({c^2,d^2} : Finset ℤ)) :
    t ≡ a [ZMOD Q] ∨ t ≡ -a [ZMOD Q] := by
  simp only [mem_insert, mem_singleton] at ht
  rcases ht with ht | ht
  · rcases (sq_eq_sq_iff_eq_or_eq_neg).mp ht with he | he
    · exact Or.inl (he ▸ hc.symm)
    · exact Or.inr (he ▸ hc.symm.neg)
  · rcases (sq_eq_sq_iff_eq_or_eq_neg).mp ht with he | he
    · exact Or.inl (he ▸ hd.symm)
    · exact Or.inr (he ▸ hd.symm.neg)

lemma factor_rotation {a b : ℤ} {g h : G} (he : (⟨a,b⟩ : G)=g*h) :
    (h.re^2+h.im^2)*(g*star h).re=
      (h.re^2-h.im^2)*a+2*h.re*h.im*b ∧
    (h.re^2+h.im^2)*(g*star h).im=
      -(2*h.re*h.im)*a+(h.re^2-h.im^2)*b := by
  have hr := congrArg Zsqrtd.re he
  have hi := congrArg Zsqrtd.im he
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] at hr hi
  rw [hr,hi]
  simp only [Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.re_star,Zsqrtd.im_star]
  constructor <;> ring

/-- This applies to the original normalized factor, not to a possibly much
larger half-angle parameter obtained by choosing an output orientation. -/
theorem factor_divisibility {Q : ℤ} {a b c d : ℕ} {g h : G}
    (hcop : IsCoprime Q (a:ℤ)) (hmn : IsCoprime h.re h.im)
    (hb : (a:ℤ) ≡ b [ZMOD Q]) (hc : (a:ℤ) ≡ c [ZMOD Q])
    (hd : (a:ℤ) ≡ d [ZMOD Q])
    (he : gauss a b=g*h)
    (hw : squareCoords (gauss c d)=squareCoords (g*star h)) :
    Q ∣ 4*h.im ∨ Q ∣ 4*h.re ∨ Q ∣ 2*(h.re-h.im) ∨ Q ∣ 2*(h.re+h.im) := by
  have hu : (g*star h).re^2 ∈ ({(c:ℤ)^2,(d:ℤ)^2} : Finset ℤ) := by
    change _ ∈ squareCoords (gauss c d)
    rw [hw]
    simp [squareCoords]
  have hv : (g*star h).im^2 ∈ ({(c:ℤ)^2,(d:ℤ)^2} : Finset ℤ) := by
    change _ ∈ squareCoords (gauss c d)
    rw [hw]
    simp [squareCoords]
  obtain ⟨hr,hi⟩ := factor_rotation he
  exact signed_rotation_divisibility hcop hmn hb
    (signed_residue hc hd hu) (signed_residue hc hd hv) hr hi

private lemma dvd_square_bound {Q t : ℤ} (hd : Q ∣ t) (ht : t≠0) : Q^2≤t^2 := by
  obtain ⟨k,hk⟩ := hd
  have hk0 : k≠0 := by intro hh; rw [hh,mul_zero] at hk; exact ht hk
  have hk1 : (1:ℤ)≤k^2 := by have := sq_pos_of_ne_zero hk0; omega
  have hm := mul_le_mul_of_nonneg_left hk1 (sq_nonneg Q)
  rw [hk]
  nlinarith only [hm]

/-- A uniform norm cutoff, including all four possible output sign patterns. -/
theorem factor_norm_cutoff {Q : ℤ} {a b c d : ℕ} {g h : G}
    (hcop : IsCoprime Q (a:ℤ)) (hmn : IsCoprime h.re h.im)
    (hr : 0<h.re) (hi : 0<h.im) (hne : h.re≠h.im)
    (hb : (a:ℤ) ≡ b [ZMOD Q]) (hc : (a:ℤ) ≡ c [ZMOD Q])
    (hd : (a:ℤ) ≡ d [ZMOD Q])
    (he : gauss a b=g*h)
    (hw : squareCoords (gauss c d)=squareCoords (g*star h)) :
    Q^2≤16*h.norm := by
  have hnorm : h.norm=h.re^2+h.im^2 := by rw [Zsqrtd.norm_def]; ring
  rw [hnorm]
  rcases factor_divisibility hcop hmn hb hc hd he hw with hn | hm | hs | hs
  · have hh := dvd_square_bound hn (by positivity : 4*h.im≠0)
    nlinarith only [hh,sq_nonneg h.re]
  · have hh := dvd_square_bound hm (by positivity : 4*h.re≠0)
    nlinarith only [hh,sq_nonneg h.im]
  · have hh := dvd_square_bound hs (by intro hh; apply hne; omega)
    nlinarith only [hh,sq_nonneg (h.re+h.im),sq_nonneg h.re,sq_nonneg h.im]
  · have hh := dvd_square_bound hs (by positivity : 2*(h.re+h.im)≠0)
    nlinarith only [hh,sq_nonneg (h.re-h.im),sq_nonneg h.re,sq_nonneg h.im]

/-- Every nontrivial collision in a common unit residue class has an actual
small Gaussian direction obeying the cutoff. -/
theorem exists_restricted_direction {Q : ℤ} {a b c d N : ℕ}
    (ha : 0<a) (haN : a≤N) (hbN : b≤N)
    (hcop : IsCoprime Q (a:ℤ))
    (hb : (a:ℤ) ≡ b [ZMOD Q]) (hc : (a:ℤ) ≡ c [ZMOD Q])
    (hd : (a:ℤ) ≡ d [ZMOD Q]) (he : a^2+b^2=c^2+d^2)
    (hne : squareCoords (gauss a b)≠squareCoords (gauss c d)) :
    ∃ p∈directions N, ∃ g : G,
      gauss a b=g*gauss p.1 p.2 ∧
      squareCoords (gauss c d)=squareCoords (g*star (gauss p.1 p.2)) ∧
      0<p.2 ∧ Q^2≤16*(normSq p : ℤ) := by
  obtain ⟨p,hp,g,hg,hw⟩ := exists_direction ha haN hbN he
  obtain ⟨hu,hcop',hpar,hN⟩ := mem_directions hp
  have hv : 0<p.2 := by
    by_contra hv
    have hv0 : p.2=0 := by omega
    have hs : star (gauss p.1 p.2)=gauss p.1 p.2 := by
      ext <;> simp [gauss,hv0]
    apply hne
    rw [hw,hs,← hg]
  have hdiff : (gauss p.1 p.2).re≠(gauss p.1 p.2).im := by
    intro hh
    have hh' : p.1=p.2 := by
      change (p.1:ℤ)=(p.2:ℤ) at hh
      exact_mod_cast hh
    exact hpar (hh' ▸ rfl)
  have hcut := factor_norm_cutoff hcop (direction_coprime hp)
    (by change (0:ℤ)<(p.1:ℤ); exact_mod_cast hu)
    (by change (0:ℤ)<(p.2:ℤ); exact_mod_cast hv) hdiff hb hc hd hg hw
  rw [norm_gauss] at hcut
  exact ⟨p,hp,g,hg,hw,hv,hcut⟩


/-- Specialization to the exact factorial-size carrier. No rational-rotation
hypothesis is assumed: the direction comes from the given integer collision. -/
theorem candidate_restricted_direction (h : ℕ)
    (σ τ υ ω : Equiv.Perm (Fin h))
    (he : (AllowedAlphabetCandidate.root h σ)^2+(AllowedAlphabetCandidate.root h τ)^2=
      (AllowedAlphabetCandidate.root h υ)^2+(AllowedAlphabetCandidate.root h ω)^2)
    (hne : σ≠υ ∧ σ≠ω) :
    ∃ p∈directions (2*(AllowedAlphabetCandidate.base h)^(h+1)), ∃ g : G,
      gauss (AllowedAlphabetCandidate.root h σ) (AllowedAlphabetCandidate.root h τ)=
        g*gauss p.1 p.2 ∧
      squareCoords (gauss (AllowedAlphabetCandidate.root h υ) (AllowedAlphabetCandidate.root h ω))=
        squareCoords (g*star (gauss p.1 p.2)) ∧
      0<p.2 ∧ (AllowedAlphabetRotationDivisibility.strongModulus h)^2≤16*(normSq p : ℤ) := by
  apply exists_restricted_direction (AllowedAlphabetCandidate.root_pos h σ)
    (AllowedAlphabetSwapRigidity.leading_range h σ).2.le
    (AllowedAlphabetSwapRigidity.leading_range h τ).2.le
    (AllowedAlphabetRotationDivisibility.root_strong_unit h σ)
    (AllowedAlphabetRotationDivisibility.strong_common_residue h σ τ)
    (AllowedAlphabetRotationDivisibility.strong_common_residue h σ υ)
    (AllowedAlphabetRotationDivisibility.strong_common_residue h σ ω) he
  intro hh
  have hm : (AllowedAlphabetCandidate.root h σ : ℤ)^2 ∈
      squareCoords (gauss (AllowedAlphabetCandidate.root h υ) (AllowedAlphabetCandidate.root h ω)) := by
    rw [← hh]
    simp [squareCoords,gauss]
  simp only [squareCoords,gauss,mem_insert,mem_singleton] at hm
  have hi {α β : Equiv.Perm (Fin h)}
      (ha : (AllowedAlphabetCandidate.root h α : ℤ)^2=
        (AllowedAlphabetCandidate.root h β : ℤ)^2) : α=β := by
    apply AllowedAlphabetCandidate.root_injective h
    apply Nat.pow_left_injective (by decide : (2:ℕ)≠0)
    exact_mod_cast ha
  rcases hm with hm | hm
  · exact hne.1 (hi hm)
  · exact hne.2 (hi hm)

end
end Erdos773.GaussianUnitResidueDirections

#print axioms Erdos773.GaussianUnitResidueDirections.signed_rotation_divisibility
#print axioms Erdos773.GaussianUnitResidueDirections.factor_divisibility
#print axioms Erdos773.GaussianUnitResidueDirections.factor_norm_cutoff
#print axioms Erdos773.GaussianUnitResidueDirections.exists_restricted_direction

#print axioms Erdos773.GaussianUnitResidueDirections.candidate_restricted_direction
