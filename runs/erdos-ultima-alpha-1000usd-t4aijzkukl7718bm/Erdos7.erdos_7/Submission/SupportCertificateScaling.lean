import FormalConjecturesUtil

/-! Rational interpretation of the integer-scaled prefix row inequalities.
These are generic arithmetic lemmas, not a covering theorem. -/
namespace Erdos7SupportCertificateScaling
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma normalized_row {I : Type*} [Fintype I] (L den old next base : ℕ)
    (w x : I → ℕ) (hL : 0 < L) (hd : 0 < den)
    (h : next*den ≤ old*base+∑ i,w i*x i) :
    (next:ℚ)/L ≤ (base:ℚ)/den*((old:ℚ)/L)+∑ i,(w i:ℚ)/den*((x i:ℚ)/L) := by
  have hLQ : (0:ℚ) < L := by exact_mod_cast hL
  have hdQ : (0:ℚ) < den := by exact_mod_cast hd
  have hh : (next:ℚ)*den ≤ old*base+∑ i,(w i:ℚ)*x i := by exact_mod_cast h
  have he : (base:ℚ)/den*((old:ℚ)/L)+∑ i,(w i:ℚ)/den*((x i:ℚ)/L) =
      ((old:ℚ)*base+∑ i,(w i:ℚ)*x i)/(den*L) := by
    simp only [div_eq_mul_inv,mul_inv_rev,add_mul,Finset.sum_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  rw [he]
  apply (le_div_iff₀ (mul_pos hdQ hLQ)).mpr
  convert hh using 1
  field_simp

lemma base_coefficient (p cd cn T : ℕ) (hp : 0 < p) (hcd : 0 < cd) (hc : cn ≤ cd*p) :
    (((cd*p-cn)*p^T:ℕ):ℚ)/((cd*p^(T+1):ℕ):ℚ)=1-((cn:ℚ)/cd)/(p:ℚ) := by
  have hpQ : (p:ℚ)≠0 := by exact_mod_cast hp.ne'
  have hcdQ : (cd:ℚ)≠0 := by exact_mod_cast hcd.ne'
  simp only [Nat.cast_mul,Nat.cast_sub hc,Nat.cast_pow,pow_succ]
  field_simp
  <;> ring

lemma increment_coefficient (p cd cn T a : ℕ) (hp : 1 < p) (hcd : 0 < cd) (ha : a < T) :
    ((cn*(p-1)*p^(T-1-a):ℕ):ℚ)/((cd*p^(T+1):ℕ):ℚ)=
      ((cn:ℚ)/cd)*((p:ℚ)-1)/(p:ℚ)^(a+2) := by
  have hpQ : (p:ℚ)≠0 := by exact_mod_cast (show p≠0 by omega)
  have hcdQ : (cd:ℚ)≠0 := by exact_mod_cast hcd.ne'
  have he : T+1=(T-1-a)+(a+2) := by omega
  simp only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ p by omega),Nat.cast_one,Nat.cast_pow]
  rw [he,pow_add]
  field_simp
  <;> ring

/-- Positive matrix rows may be checked with a single natural denominator. -/
lemma normalized_moment_row {I K : Type*} [Fintype I] [Fintype K]
    (L den old next : ℕ) (r : K → ℕ) (C : K → I → ℕ) (M : I → ℕ)
    (hL : 0 < L) (hd : 0 < den)
    (h : den*old+(∑ k,r k*∑ i,C k i*M i) ≤ den*next) :
    (old:ℚ)/L+(∑ k,(r k:ℚ)/den*∑ i,(C k i:ℚ)*((M i:ℚ)/L)) ≤ (next:ℚ)/L := by
  have hLQ : (0:ℚ) < L := by exact_mod_cast hL
  have hdQ : (0:ℚ) < den := by exact_mod_cast hd
  have hh : (den:ℚ)*old+(∑ k,(r k:ℚ)*∑ i,(C k i:ℚ)*M i) ≤ den*next := by exact_mod_cast h
  have he : (old:ℚ)/L+(∑ k,(r k:ℚ)/den*∑ i,(C k i:ℚ)*((M i:ℚ)/L)) =
      ((den:ℚ)*old+∑ k,(r k:ℚ)*∑ i,(C k i:ℚ)*M i)/(den*L) := by
    simp only [div_eq_mul_inv,mul_inv_rev,add_mul,Finset.sum_mul,Finset.mul_sum]
    congr 1
    · field_simp
    · apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      ring
  rw [he]
  apply (div_le_iff₀ (mul_pos hdQ hLQ)).mpr
  convert hh using 1
  field_simp

lemma moment_coefficients (p cd cn : ℕ) (hp : 1 < p) (hcd : 0 < cd) :
    ((cn*(p-1)^2:ℕ):ℚ)/((cd*(p-1)^3:ℕ):ℚ)=((cn:ℚ)/cd)/((p:ℚ)-1) ∧
    ((cn*(p+1)*(p-1):ℕ):ℚ)/((cd*(p-1)^3:ℕ):ℚ)=((cn:ℚ)/cd)*((p:ℚ)+1)/((p:ℚ)-1)^2 ∧
    ((cn*(p^2+4*p+1):ℕ):ℚ)/((cd*(p-1)^3:ℕ):ℚ)=((cn:ℚ)/cd)*((p:ℚ)^2+4*p+1)/((p:ℚ)-1)^3 := by
  have hpQ : (1:ℚ) < p := by exact_mod_cast hp
  have hm : (p:ℚ)-1≠0 := by linarith
  have hcdQ : (cd:ℚ)≠0 := by exact_mod_cast hcd.ne'
  simp only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ p by omega),Nat.cast_one,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
  constructor
  · field_simp
  constructor <;> field_simp <;> ring

lemma min_coefficient (cd cn q K : ℕ) (hcd : 0 < cd) (hq : 0 < q) (hc : cd ≤ cn) :
    min ((cn:ℚ)/cd-1) (((cn:ℚ)/cd)/(q:ℚ)*K)=
      ((min ((cn-cd)*q) (cn*K):ℕ):ℚ)/((cd*q:ℕ):ℚ) := by
  have hcdQ : (cd:ℚ)≠0 := by exact_mod_cast hcd.ne'
  have hqQ : (q:ℚ)≠0 := by exact_mod_cast hq.ne'
  have he₁ : (cn:ℚ)/cd-1=(((cn-cd)*q:ℕ):ℚ)/((cd*q:ℕ):ℚ) := by
    simp only [Nat.cast_mul,Nat.cast_sub hc]
    field_simp
    <;> ring
  have he₂ : ((cn:ℚ)/cd)/(q:ℚ)*K=((cn*K:ℕ):ℚ)/((cd*q:ℕ):ℚ) := by
    simp only [Nat.cast_mul]
    field_simp
    <;> ring
  rw [he₁,he₂,min_div_div_right (Nat.cast_nonneg (cd*q)),Nat.cast_min]

lemma normalized_loss_row (L Mscale Cscale cd cn q M S C : ℕ)
    (hL : 0 < L) (hM : 0 < Mscale) (hC : 0 < Cscale) (hcd : 0 < cd) (hq : 0 < q)
    (h : cn*M*L*Cscale ≤ C*(cd*q*Mscale*L)+Mscale*Cscale*S) :
    ((cn:ℚ)/cd)/(q:ℚ)*((M:ℚ)/Mscale)-(S:ℚ)/((cd:ℚ)*q*L) ≤ (C:ℚ)/Cscale := by
  have hLQ : (0:ℚ) < L := by exact_mod_cast hL
  have hMQ : (0:ℚ) < Mscale := by exact_mod_cast hM
  have hCQ : (0:ℚ) < Cscale := by exact_mod_cast hC
  have hcdQ : (0:ℚ) < cd := by exact_mod_cast hcd
  have hqQ : (0:ℚ) < q := by exact_mod_cast hq
  have hh : (cn:ℚ)*M*L*Cscale ≤ C*((cd:ℚ)*q*Mscale*L)+Mscale*Cscale*S := by exact_mod_cast h
  apply sub_le_iff_le_add.mpr
  apply le_of_mul_le_mul_right (a := (cd:ℚ)*q*Mscale*L*Cscale) ?_ (by positivity)
  convert hh using 1 <;> field_simp <;> ring

#print axioms normalized_loss_row

#print axioms normalized_row
#print axioms normalized_moment_row
end Erdos7SupportCertificateScaling
