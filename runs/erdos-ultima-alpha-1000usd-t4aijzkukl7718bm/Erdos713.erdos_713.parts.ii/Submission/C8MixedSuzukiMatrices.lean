import FormalConjecturesUtil

/-! Polynomial identities for a mixed central/noncentral Suzuki-type
matrix pair. These do not prove the rational-exponent conjecture. -/
namespace Erdos713C8MixedSuzukiMatrices
variable {K : Type*} [Field K] [CharP K 2]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

abbrev Mat (K : Type*) := Matrix (Fin 4) (Fin 4) K

def X (u v : K) : Mat K := !![1,0,0,0; 0,1,0,0; u,0,1,0; v,u,0,1]
def Y (t k : K) : Mat K := !![1,1,t,k; 0,1,1,1+t; 0,0,1,1; 0,0,0,1]

lemma X_sq (u v : K) : X u v * X u v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X,Matrix.mul_apply,Fin.sum_univ_succ,CharTwo.add_self_eq_zero]

lemma Y_inv (t k : K) : Y t k * Y (t+1) k = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Y,Matrix.mul_apply,Fin.sum_univ_succ] <;>
    ring_nf <;> reduce_mod_char!

/-- A degree-four identity replacing a full characteristic-polynomial
calculation. The two scalar coefficients are the nonconstant reciprocal
characteristic coefficients of X*Y. -/
lemma reciprocal_identity (t k u v : K) :
    (X u v*Y t k)^2 + (Y (t+1) k*X u v)^2 =
      (k*v+u) • (X u v*Y t k+Y (t+1) k*X u v) +
      ((t^2+t+k)*u^2+v) • (1 : Mat K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X,Y,pow_two] <;>
    ring_nf <;> reduce_mod_char!

omit [CharP K 2] in
lemma product_corner (t k u v : K) : (X u v*Y t k) 0 3 = k := by
  simp [X,Y,Matrix.mul_apply,Fin.sum_univ_succ]

omit [CharP K 2] in
lemma reverse_corner (t k u v : K) : (Y t k*X u v) 3 0 = v := by
  simp [X,Y,Matrix.mul_apply,Fin.sum_univ_succ]

lemma square_corner (t k u v : K) (h : k*v+u=0) :
    ((X u v*Y t k)^2) 0 3 = 1 := by
  simp [X,Y,pow_two,Matrix.mul_apply,Fin.sum_univ_succ]
  linear_combination (norm := (ring_nf; reduce_mod_char!)) k*h

lemma reverse_square_corner (t k u v : K) (h : k*v+u=0) :
    ((Y t k*X u v)^2) 3 0 = u^2 := by
  simp [X,Y,pow_two,Matrix.mul_apply,Fin.sum_univ_succ]
  linear_combination (norm := (ring_nf; reduce_mod_char!)) v*h

lemma order_four (t k u v : K) (h1 : k*v+u=0)
    (h2 : (t^2+t+k)*u^2+v=0) : (X u v*Y t k)^4 = 1 := by
  let M := X u v*Y t k
  let N := Y (t+1) k*X u v
  have hMN : M*N=1 := by
    calc
      M*N = X u v*(Y t k*Y (t+1) k)*X u v := by
        simp only [M,N,mul_assoc]
      _ = 1 := by rw [Y_inv,mul_one,X_sq]
  have hsq : M^2=N^2 := by
    apply CharTwo.add_eq_zero.mp
    simpa only [h1,h2,zero_smul,add_zero] using reciprocal_identity t k u v
  change M^4=1
  calc
    M^4 = M^2*M^2 := by rw [← pow_add]
    _ = M^2*N^2 := by rw [hsq]
    _ = M*(M*N)*N := by simp only [pow_two,mul_assoc]
    _ = 1 := by rw [hMN,mul_one,hMN]

lemma twisted_norm_ne_zero (σ : K →+* K) (hσ : ∀ a, σ (σ a)=a^2) (t : K) :
    1+t+σ t ≠ 0 := by
  intro h
  have hh := congrArg σ h
  simp only [map_add,map_one,map_zero,hσ] at hh
  have ht : t*(t+1)=0 := by
    linear_combination (norm := (ring_nf; reduce_mod_char!)) hh-h
  rcases mul_eq_zero.mp ht with ht | ht
  · subst t
    simp at h
  · have ht1 : t=1 := CharTwo.add_eq_zero.mp ht
    subst t
    simp [CharTwo.add_self_eq_zero] at h

lemma twisted_scalars (σ : K →+* K) (hσ : ∀ a, σ (σ a)=a^2) (t : K) :
    let k := 1+t+σ t
    let ℓ := t^2+t+k
    k ≠ 0 ∧ ℓ ≠ 0 ∧ σ (1/(k*ℓ))=(1/(k*ℓ))/k := by
  let k := 1+t+σ t
  let ℓ := t^2+t+k
  have hk : k ≠ 0 := twisted_norm_ne_zero σ hσ t
  have hkσ : σ k=ℓ := by
    dsimp [k,ℓ]
    simp only [map_add,map_one,hσ]
    ring_nf
    reduce_mod_char!
  have hℓ : ℓ ≠ 0 := by rw [← hkσ]; exact (map_ne_zero σ).mpr hk
  have hℓσ : σ ℓ=k^2 := by rw [← hkσ,hσ]
  refine ⟨hk,hℓ,?_⟩
  change σ (1/(k*ℓ))=(1/(k*ℓ))/k
  rw [map_div₀,map_one,map_mul,hkσ,hℓσ]
  field_simp


lemma scalar_relations (t k : K) (hk : k ≠ 0) :
    let u := 1/(k*(t^2+t+k))
    let v := u/k
    k*v+u=0 ∧ (t^2+t+k)*u^2+v=0 := by
  dsimp
  constructor <;> field_simp [hk] <;> ring_nf <;> reduce_mod_char!

end Erdos713C8MixedSuzukiMatrices
