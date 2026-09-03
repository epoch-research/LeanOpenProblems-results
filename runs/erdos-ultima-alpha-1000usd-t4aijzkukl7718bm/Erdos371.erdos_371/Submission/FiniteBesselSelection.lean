import FormalConjecturesUtil

/-! An elementary finite Bessel selection estimate for approximately
orthogonal bounded vectors, with no lower norm bound on the vectors. -/
namespace Erdos371.FiniteSieve
open Finset
variable {ι Ω : Type*}

lemma bounded_sq_le_one {x : ℝ} (hx : |x|≤1) : x^2≤1 := by
  obtain ⟨hl,hu⟩ := abs_le.mp hx
  nlinarith

/-- A signed-sum proof of a coarse Bessel inequality. The off-diagonal loss
is K^2*eta; no positive lower bound on any witness norm is required. -/
theorem finite_bessel_absolute_sum (I : Finset ι) (X : Finset Ω)
    (G : Ω → ℝ) (W : ι → Ω → ℝ) (η : ℝ) (hη : 0≤η)
    (hG : ∀ x ∈ X, |G x|≤1) (hW : ∀ i ∈ I, ∀ x ∈ X, |W i x|≤1)
    (hGram : ∀ i ∈ I, ∀ j ∈ I, i≠j → |∑ x ∈ X, W i x*W j x|≤η*X.card) :
    (∑ i ∈ I, |∑ x ∈ X, G x*W i x|)^2 ≤
      (X.card : ℝ)^2*(I.card+(I.card : ℝ)^2*η) := by
  classical
  let a : ι → ℝ := fun i => ∑ x ∈ X, G x*W i x
  let s : ι → ℝ := fun i => if 0≤a i then 1 else -1
  let V : Ω → ℝ := fun x => ∑ i ∈ I, s i*W i x
  have hs (i : ι) : |s i|=1 := by dsimp [s]; split_ifs <;> norm_num
  have hsa (i : ι) : s i*a i=|a i| := by
    dsimp [s]
    split_ifs with h
    · rw [one_mul,abs_of_nonneg h]
    · rw [neg_one_mul,abs_of_neg (lt_of_not_ge h)]
  have he : (∑ i ∈ I, |a i|) = ∑ x ∈ X, G x*V x := by
    calc
      _ = ∑ i ∈ I, ∑ x ∈ X, G x*(s i*W i x) := by
        apply sum_congr rfl
        intro i _
        rw [← hsa i]
        dsimp only [a]
        rw [mul_sum]
        apply sum_congr rfl
        intro x _
        ring
      _ = _ := by rw [sum_comm]; simp only [V,mul_sum]
  have hGsq : (∑ x ∈ X, (G x)^2)≤X.card := by
    calc
      _ ≤ ∑ _x ∈ X, (1 : ℝ) := sum_le_sum fun x hx => bounded_sq_le_one (hG x hx)
      _ = _ := by simp
  have hk (i : ι) (hi : i ∈ I) (j : ι) (hj : j ∈ I) :
      (∑ x ∈ X, (s i*W i x)*(s j*W j x)) ≤
        (if i=j then (X.card : ℝ) else 0)+η*X.card := by
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl]
      have hv (x : Ω) (hx : x ∈ X) : (s i*W i x)*(s i*W i x)≤1 := by
        rw [← pow_two]
        apply bounded_sq_le_one
        simpa only [abs_mul,hs i,one_mul] using hW i hi x hx
      calc
        _ ≤ ∑ _x ∈ X, (1 : ℝ) := sum_le_sum hv
        _ = X.card := by simp
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · rw [if_neg hij,zero_add]
      have he' : (∑ x ∈ X, (s i*W i x)*(s j*W j x)) =
          (s i*s j)*(∑ x ∈ X, W i x*W j x) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro x _
        ring
      rw [he']
      apply (le_abs_self _).trans
      simpa only [abs_mul,hs i,hs j,one_mul] using hGram i hi j hj hij
  have hVsq : (∑ x ∈ X, (V x)^2)≤X.card*(I.card+(I.card : ℝ)^2*η) := by
    calc
      _ = ∑ i ∈ I, ∑ j ∈ I, ∑ x ∈ X, (s i*W i x)*(s j*W j x) := by
        simp only [V,pow_two,sum_mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        rw [sum_comm]
      _ ≤ ∑ i ∈ I, ∑ j ∈ I, ((if i=j then (X.card : ℝ) else 0)+η*X.card) :=
        sum_le_sum fun i hi => sum_le_sum fun j hj => hk i hi j hj
      _ = _ := by
        simp only [sum_add_distrib,sum_ite_eq,sum_const,nsmul_eq_mul]
        have hh (i : ι) (hi : i∈I) : (if i∈I then (X.card : ℝ) else 0)=X.card := if_pos hi
        rw [sum_congr rfl hh]
        simp only [sum_const,nsmul_eq_mul]
        ring
  change (∑ i ∈ I, |a i|)^2≤_
  rw [he]
  calc
    _ ≤ (∑ x ∈ X, (G x)^2)*(∑ x ∈ X, (V x)^2) := sum_mul_sq_le_sq_mul_sq X G V
    _ ≤ X.card*(∑ x ∈ X, (V x)^2) :=
      mul_le_mul_of_nonneg_right hGsq (sum_nonneg fun _ _ => sq_nonneg _)
    _ ≤ X.card*(X.card*(I.card+(I.card : ℝ)^2*η)) :=
      mul_le_mul_of_nonneg_left hVsq (Nat.cast_nonneg _)
    _ = _ := by ring

/-- At least one witness has small correlation with any bounded target. -/
theorem finite_bessel_selection (I : Finset ι) (hI : I.Nonempty)
    (X : Finset Ω) (hX : X.Nonempty) (G : Ω → ℝ) (W : ι → Ω → ℝ)
    (η ε : ℝ) (hη : 0≤η) (hε : 0<ε)
    (hsize : (1 : ℝ)/I.card+η<ε^2)
    (hG : ∀ x ∈ X, |G x|≤1) (hW : ∀ i ∈ I, ∀ x ∈ X, |W i x|≤1)
    (hGram : ∀ i ∈ I, ∀ j ∈ I, i≠j → |∑ x ∈ X, W i x*W j x|≤η*X.card) :
    ∃ i ∈ I, |(∑ x ∈ X, G x*W i x)/(X.card : ℝ)|<ε := by
  have hIr : (0 : ℝ)<I.card := by exact_mod_cast card_pos.mpr hI
  have hXr : (0 : ℝ)<X.card := by exact_mod_cast card_pos.mpr hX
  by_contra hn
  push_neg at hn
  have hlo : (I.card : ℝ)*ε*X.card≤∑ i ∈ I, |∑ x ∈ X, G x*W i x| := by
    calc
      _ = ∑ _i ∈ I, ε*X.card := by simp; ring
      _ ≤ _ := sum_le_sum fun i hi => by
        have h := hn i hi
        rw [abs_div,abs_of_pos hXr] at h
        exact (le_div_iff₀ hXr).mp h
  have hs := finite_bessel_absolute_sum I X G W η hη hG hW hGram
  have hloSq := pow_le_pow_left₀ (show 0≤(I.card : ℝ)*ε*X.card by positivity) hlo 2
  have hmul := mul_lt_mul_of_pos_left hsize (show 0<(I.card : ℝ)^2 by positivity)
  have he : (I.card : ℝ)^2*((1 : ℝ)/I.card+η)=I.card+(I.card : ℝ)^2*η := by
    field_simp
  rw [he] at hmul
  have hmul' := mul_lt_mul_of_pos_left hmul (show 0<(X.card : ℝ)^2 by positivity)
  nlinarith

#print axioms finite_bessel_selection
end Erdos371.FiniteSieve
