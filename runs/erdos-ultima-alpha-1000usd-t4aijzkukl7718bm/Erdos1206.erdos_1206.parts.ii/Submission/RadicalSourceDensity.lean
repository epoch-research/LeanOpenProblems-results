import Submission.SquareDivisorTail
import Submission.PositiveDensityTransfer

/-! Positive lower density survives passage to radicals. A bounded-cofactor
subsource is obtained first, using the uniform large-square-divisor tail. -/
namespace Erdos1206.RadicalSourceDensity
open Finset UniqueFactorizationMonoid PositiveDensityTransfer
open scoped Classical

lemma radical_pos (n : ℕ) : 0 < radical n := Nat.pos_of_ne_zero radical_ne_zero
lemma radical_le {n : ℕ} (hn : 0 < n) : radical n ≤ n := Nat.le_of_dvd hn radical_dvd_self

lemma nat_primeFactors_radical (n : ℕ) : (radical n).primeFactors=n.primeFactors := by
  simpa only [primeFactors_eq_natPrimeFactors] using (primeFactors_radical (a := n))

lemma cofactor_bound {K n : ℕ} (hn : 0 < n)
    (hK : ∀ b : ℕ,K < b → ¬ b^2 ∣ n) : n ≤ K^2*radical n := by
  obtain ⟨a,b,_,hb,he,ha⟩ := Nat.sq_mul_squarefree_of_pos hn
  have hbK : b ≤ K := by
    by_contra! h
    apply hK b h
    rw [←he]
    exact dvd_mul_right _ _
  have har : a ∣ radical n := (dvd_radical_iff ha.isRadical hn.ne').mpr (by rw [←he]; exact dvd_mul_left _ _)
  have hale : a ≤ radical n := Nat.le_of_dvd (radical_pos n) har
  calc
    n = b^2*a := he.symm
    _ ≤ K^2*a := Nat.mul_le_mul_right a (Nat.pow_le_pow_left hbK 2)
    _ ≤ K^2*radical n := Nat.mul_le_mul_left _ hale

/-- The retained source has positive density, with a fixed bound on n/rad(n). -/
theorem exists_bounded_source {A : Set ℕ} (hA : 0 < A.lowerDensity) :
    ∃ K : ℕ,0 < K ∧ ∃ S : Set ℕ,S ⊆ A ∧ 0 < S.lowerDensity ∧
      ∀ n ∈ S,0 < n ∧ n ≤ K^2*radical n := by
  obtain ⟨δ,hδ,C,hpre⟩ := prefix_bound_of_positive_lowerDensity hA
  obtain ⟨K,hK,hbad⟩ := SquareDivisorTail.uniform_tail (half_pos hδ)
  let S : Set ℕ := {n | n ∈ A ∧ 0 < n ∧ ∀ b : ℕ,K < b → ¬ b^2 ∣ n}
  refine ⟨K,hK,S,fun _ hn => hn.1,?_,fun n hn => ⟨hn.2.1,cofactor_bound hn.2.1 hn.2.2⟩⟩
  apply positive_lowerDensity_of_prefix_bound (δ := δ/2) (C := C+1) (half_pos hδ)
  intro N
  let U := (range N).filter (fun n => n ∈ A)
  let V := (range N).filter (fun n => n ∈ S)
  have hsub : U ⊆ V ∪ SquareDivisorTail.bad K N ∪ {0} := by
    intro n hn
    obtain ⟨hnN,hnA⟩ := mem_filter.mp hn
    by_cases hn0 : n=0
    · exact mem_union_right _ (mem_singleton.mpr hn0)
    · have hnp : 0 < n := Nat.pos_of_ne_zero hn0
      by_cases hg : ∀ b : ℕ,K < b → ¬ b^2 ∣ n
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hnN,hnA,hnp,hg⟩))
      · push_neg at hg
        exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨hnp,(mem_range.mp hnN).le⟩,hg⟩))
  have hc := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  have hu : U.card=(A ∩ Set.Iio N).ncard := prefix_card A N
  have hv : V.card=(S ∩ Set.Iio N).ncard := by
    rw [←prefix_card S N]
    congr 1
    ext n
    simp only [V,mem_filter,mem_range]
  rw [hu,hv,card_singleton] at hc
  have hcR : ((A ∩ Set.Iio N).ncard:ℝ) ≤ (S ∩ Set.Iio N).ncard+(SquareDivisorTail.bad K N).card+1 := by exact_mod_cast hc
  linarith [hpre N,hbad N]

/-- A fixed cofactor bound bounds the fibers of the radical map uniformly. -/
theorem bounded_image_density {A : Set ℕ} (hA : 0 < A.lowerDensity) {K : ℕ} (hK : 0 < K)
    (hbound : ∀ n ∈ A,0 < n ∧ n ≤ K*radical n) :
    0 < (radical '' A).lowerDensity := by
  obtain ⟨δ,hδ,C,hpre⟩ := prefix_bound_of_positive_lowerDensity hA
  have hKR : (0:ℝ) < K := by exact_mod_cast hK
  apply positive_lowerDensity_of_prefix_bound (δ := δ/K) (C := C/K) (div_pos hδ hKR)
  intro N
  let U := (range N).filter (fun n => n ∈ A)
  let V := (range N).filter (fun n => n ∈ radical '' A)
  let f (n : ℕ) := (n/radical n,radical n)
  have he (n : ℕ) : (f n).1*(f n).2=n := Nat.div_mul_cancel radical_dvd_self
  have hmap : Set.MapsTo f (U : Set ℕ) (((Icc 1 K).product V) : Set (ℕ × ℕ)) := by
    intro n hn
    change n ∈ U at hn
    obtain ⟨hnN,hnA⟩ := mem_filter.mp hn
    obtain ⟨hn0,hnK⟩ := hbound n hnA
    have hf0 : 0 < (f n).1 := by have hh := he n; nlinarith
    have hfK : (f n).1 ≤ K := by
      have hre : (f n).1*radical n=n := he n
      have hh : (f n).1*radical n ≤ K*radical n := by rwa [hre]
      exact Nat.le_of_mul_le_mul_right hh (radical_pos n)
    refine mem_product.mpr ⟨mem_Icc.mpr ⟨hf0,hfK⟩,mem_filter.mpr ⟨?_,n,hnA,rfl⟩⟩
    exact mem_range.mpr ((radical_le hn0).trans_lt (mem_range.mp hnN))
  have hinj : Set.InjOn f (U : Set ℕ) := by
    intro n _ m _ h
    have hh := congrArg (fun z : ℕ × ℕ => z.1*z.2) h
    simpa only [he] using hh
  have hc := card_le_card_of_injOn (t := (Icc 1 K).product V) f hmap hinj
  have hprod : ((Icc 1 K).product V).card=K*V.card := by
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using Finset.card_product (Icc 1 K) V
  rw [hprod] at hc
  have hu : U.card=(A ∩ Set.Iio N).ncard := prefix_card A N
  have hv : V.card=((radical '' A) ∩ Set.Iio N).ncard := prefix_card (radical '' A) N
  rw [hu,hv] at hc
  have hcR : ((A ∩ Set.Iio N).ncard:ℝ) ≤ (K:ℝ)*((radical '' A) ∩ Set.Iio N).ncard := by exact_mod_cast hc
  have hh : δ*N ≤ (K:ℝ)*((radical '' A) ∩ Set.Iio N).ncard+C := by linarith [hpre N]
  calc
    δ/(K:ℝ)*N = (δ*N)/K := by ring
    _ ≤ ((K:ℝ)*((radical '' A) ∩ Set.Iio N).ncard+C)/K := div_le_div_of_nonneg_right hh hKR.le
    _ = _ := by field_simp

/-- The radical image of any positive-lower-density set again has positive
lower density. This does not preserve cube-Sidonness. -/
theorem radical_image_density {A : Set ℕ} (hA : 0 < A.lowerDensity) :
    0 < (radical '' A).lowerDensity := by
  obtain ⟨K,hK,S,hSA,hS,hbound⟩ := exists_bounded_source hA
  exact superset (bounded_image_density hS (pow_pos hK 2) hbound) (Set.image_mono hSA)

#print axioms exists_bounded_source
#print axioms bounded_image_density
#print axioms radical_image_density
end Erdos1206.RadicalSourceDensity
