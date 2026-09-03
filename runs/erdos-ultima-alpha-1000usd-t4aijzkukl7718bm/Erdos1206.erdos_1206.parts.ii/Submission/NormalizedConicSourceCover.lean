import Submission.SummableConicSource

/-! A reciprocal-summable divisor cover for surviving rationally scaled
instances of the explicit conic, relative to a positive-density source.
This is not a cover of all cubic collisions. -/
namespace Erdos1206.NormalizedConicSourceCover
open SquarefreeConicFamily SummableConicSource
open scoped Classical

def commonGcd (t u : ℕ) : ℕ :=
  Nat.gcd (Nat.gcd (F 0 t u) (F 1 t u)) (Nat.gcd (F 2 t u) (F 3 t u))
def normalizedMax (v : ℕ × ℕ) : ℕ := F 3 v.1 v.2/commonGcd v.1 v.2

lemma commonGcd_dvd (t u : ℕ) (i : Fin 4) : commonGcd t u ∣ F i t u := by
  fin_cases i
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)

lemma commonGcd_pos {t u : ℕ} (hu : 0 < u) : 0 < commonGcd t u :=
  Nat.pos_of_dvd_of_pos (commonGcd_dvd t u 0) (ordered t u hu).1

lemma certificate_u (t u : ℕ) :
    (-401149908:ℤ)*(F 0 t u:ℤ)+(-749322324)*(F 1 t u:ℤ)+366771600*(F 2 t u:ℤ)=
      721465056*(u:ℤ)^2 := by
  simp only [F,QuadraticSquarefreeSieve.quad,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  norm_num [a,b,c,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  ring

lemma certificate_t (t u : ℕ) :
    (-335988:ℤ)*(F 0 t u:ℤ)+(-552276)*(F 1 t u:ℤ)+271440*(F 2 t u:ℤ)=
      721465056*(t:ℤ)^2 := by
  simp only [F,QuadraticSquarefreeSieve.quad,Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  norm_num [a,b,c,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  ring

lemma commonGcd_dvd_constant {t u : ℕ} (hcop : Nat.Coprime t u) :
    commonGcd t u ∣ 721465056 := by
  have hd (i : Fin 4) : (commonGcd t u:ℤ) ∣ (F i t u:ℤ) := by exact_mod_cast commonGcd_dvd t u i
  have huZ : (commonGcd t u:ℤ) ∣ 721465056*(u:ℤ)^2 := by
    rw [←certificate_u]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right (hd 0) _) (dvd_mul_of_dvd_right (hd 1) _))
      (dvd_mul_of_dvd_right (hd 2) _)
  have htZ : (commonGcd t u:ℤ) ∣ 721465056*(t:ℤ)^2 := by
    rw [←certificate_t]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right (hd 0) _) (dvd_mul_of_dvd_right (hd 1) _))
      (dvd_mul_of_dvd_right (hd 2) _)
  have hu' : commonGcd t u ∣ 721465056*u^2 := by exact_mod_cast huZ
  have ht' : commonGcd t u ∣ 721465056*t^2 := by exact_mod_cast htZ
  have hh := Nat.dvd_gcd ht' hu'
  simpa only [Nat.gcd_mul_left,(hcop.pow 2 2).gcd_eq_one,mul_one] using hh

lemma normalizedMax_mul (v : ℕ × ℕ) : commonGcd v.1 v.2*normalizedMax v=F 3 v.1 v.2 :=
  Nat.mul_div_cancel' (commonGcd_dvd v.1 v.2 3)

lemma normalizedMax_gt_one {v : ℕ × ℕ} (hu : 0 < v.2) : 1 < normalizedMax v := by
  obtain ⟨ha,hab,hbc,hcd⟩ := ordered v.1 v.2 hu
  have hg : commonGcd v.1 v.2 ≤ F 0 v.1 v.2 := Nat.le_of_dvd ha (commonGcd_dvd _ _ 0)
  have hmul := normalizedMax_mul v
  by_contra hh
  have hle : normalizedMax v ≤ 1 := le_of_not_gt hh
  have hb := Nat.mul_le_mul_left (commonGcd v.1 v.2) hle
  nlinarith only [hg,hab,hbc,hcd,hmul,hb]

lemma height_sq_le (v : ℕ × ℕ) : (DyadicBoxReciprocal.height v)^2 ≤ F 3 v.1 v.2 := by
  change (max v.1 v.2)^2 ≤ 589*v.2^2+43324*v.1*v.2+797983*v.1^2
  rcases le_total v.1 v.2 with h | h
  · rw [max_eq_right h]
    ring_nf
    omega
  · rw [max_eq_left h]
    ring_nf
    omega

lemma normalizedMax_reciprocal_le {v : ℕ × ℕ} (hcop : Nat.Coprime v.1 v.2) (hu : 0 < v.2) :
    (1:ℝ)/normalizedMax v ≤ 721465056*(1/(DyadicBoxReciprocal.height v:ℝ)^2) := by
  have hg := Nat.le_of_dvd (by decide : 0 < 721465056) (commonGcd_dvd_constant hcop)
  have hh : (DyadicBoxReciprocal.height v)^2 ≤ 721465056*normalizedMax v := calc
    _ ≤ F 3 v.1 v.2 := height_sq_le v
    _ = commonGcd v.1 v.2*normalizedMax v := (normalizedMax_mul v).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hg
  have hhR : (DyadicBoxReciprocal.height v:ℝ)^2 ≤ 721465056*(normalizedMax v:ℝ) := by exact_mod_cast hh
  have hd : (0:ℝ) < normalizedMax v := by exact_mod_cast (Nat.zero_lt_one.trans (normalizedMax_gt_one hu))
  have hH : 0 < DyadicBoxReciprocal.height v := hu.trans_le (Nat.le_max_right _ _)
  have hHR : (0:ℝ) < (DyadicBoxReciprocal.height v:ℝ)^2 := by positivity
  rw [mul_one_div]
  exact (div_le_div_iff₀ hd hHR).mpr (by simpa only [one_mul] using hhR)

lemma normalizedMax_dvd_proportional (x : Fin 4 → ℕ) {t u : ℕ} (hu : 0 < u)
    (hprop : ∀ i, x i*F 0 t u=x 0*F i t u) : normalizedMax (t,u) ∣ x 3 := by
  have hF0 := (ordered t u hu).1
  have hcross (i : Fin 4) : F 3 t u*x i=x 3*F i t u := by
    have h₁ := congrArg (fun n : ℕ => n*F 3 t u) (hprop i)
    have h₂ := congrArg (fun n : ℕ => n*F i t u) (hprop 3)
    apply Nat.eq_of_mul_eq_mul_left hF0
    nlinarith only [h₁,h₂]
  have hd (i : Fin 4) : F 3 t u ∣ x 3*F i t u := ⟨x i,(hcross i).symm⟩
  have hh := Nat.dvd_gcd (Nat.dvd_gcd (hd 0) (hd 1)) (Nat.dvd_gcd (hd 2) (hd 3))
  simp only [Nat.gcd_mul_left] at hh
  apply (Nat.div_dvd_iff_dvd_mul (commonGcd_dvd t u 3) (commonGcd_pos hu)).mpr
  simpa only [commonGcd,mul_comm] using hh

lemma normalized_survivors_summable {A : Set ℕ}
    (hs : Summable (DyadicBoxReciprocal.weight (survivors A))) :
    Summable (fun v : survivors A => (1:ℝ)/normalizedMax v) := by
  have hh := (hs.subtype (survivors A)).mul_left 721465056
  apply hh.of_nonneg_of_le (fun v => by positivity)
  intro v
  have hv := v.property
  have hcop := hv.1
  have hu := hv.2.1
  simpa only [Function.comp_apply,DyadicBoxReciprocal.weight,if_pos v.property] using
    normalizedMax_reciprocal_le hcop hu

noncomputable def cover (A : Set ℕ) : Set ℕ :=
  Set.range (fun v : survivors A => normalizedMax v)

lemma cover_summable {A : Set ℕ} (hs : Summable (DyadicBoxReciprocal.weight (survivors A))) :
    Summable (fun n : ℕ => if n ∈ cover A then (1:ℝ)/n else 0) := by
  choose w hw using (fun n : cover A => n.property)
  have hi : Function.Injective w := by
    intro a b he
    apply Subtype.ext
    rw [←hw a,←hw b,he]
  have hh := (normalized_survivors_summable hs).comp_injective hi
  have hh' : Summable (fun n : cover A => (1:ℝ)/(n:ℕ)) := by
    apply hh.congr
    intro n
    simp only [Function.comp_apply,hw n]
  simpa only [Set.indicator_apply] using
    (summable_subtype_iff_indicator (f := fun n : ℕ => (1:ℝ)/n) (s := cover A)).mp hh'

lemma one_not_mem_cover (A : Set ℕ) : 1 ∉ cover A := by
  rintro ⟨v,hv⟩
  have hh := normalizedMax_gt_one v.property.2.1
  change normalizedMax v=1 at hv
  omega

/-- A source-relative summable divisor cover, including all positive rational
scalings and common-gcd normalizations of primitive conic points. -/
theorem exists_source_cover :
    ∃ A B : Set ℕ, (∀ n ∈ A, Squarefree n) ∧ 0 < A.lowerDensity ∧ 1 ∉ B ∧
      Summable (fun n : ℕ => if n ∈ B then (1:ℝ)/n else 0) ∧
      ∀ (t u : ℕ) (x : Fin 4 → ℕ), Nat.Coprime t u → 0 < u → 0 < x 0 →
        (∀ i, x i*F 0 t u=x 0*F i t u) → (∀ i, x i ∈ A) →
        ∃ d ∈ B, d ∣ x 3 := by
  obtain ⟨A,hAS,hAd,hs⟩ := exists_source_summable_parameters
  refine ⟨A,cover A,hAS,hAd,one_not_mem_cover A,cover_summable hs,?_⟩
  intro t u x hcop hu hx hprop hmem
  have hv : (t,u) ∈ survivors A := ⟨hcop,hu,x,hx,hprop,hmem⟩
  exact ⟨normalizedMax (t,u),⟨⟨(t,u),hv⟩,rfl⟩,normalizedMax_dvd_proportional x hu hprop⟩

#print axioms commonGcd_dvd_constant
#print axioms normalizedMax_dvd_proportional
#print axioms cover_summable
#print axioms exists_source_cover
end Erdos1206.NormalizedConicSourceCover
