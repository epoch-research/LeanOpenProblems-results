import FormalConjecturesUtil

/-! A three-ray exclusion for a multiplicative Gold-trace candidate.
This is not a K44-freeness theorem or a solution of Erdős 714. -/

set_option maxHeartbeats 1000000
noncomputable section
namespace Erdos714GoldTrace
variable {E : Type*} [Field E] [CharP E 2]

/-- The four-term relative trace expression. -/
def tr4 (τ : E →+* E) (z : E) : E := z+τ z+τ (τ z)+τ (τ (τ z))

omit [CharP E 2] in
lemma tr4_add (τ : E →+* E) (x y : E) : tr4 τ (x+y)=tr4 τ x+tr4 τ y := by
  simp only [tr4,map_add]; ring

omit [CharP E 2] in
lemma tr4_zero (τ : E →+* E) : tr4 τ 0=0 := by simp [tr4]

/-- The incidence kernel tested in this continuation. -/
def kernel (τ σ : E →+* E) (x y : E) : E := tr4 τ ((x*y)*σ (x*y)+x*y)

/-- The natural order-three ray triple has no common neighbor. Although this
is a genuine obstruction to a particular configuration, the candidate still
has other K44 copies, including after restricting to a power-injective subgroup. -/
theorem three_ray_no_common (τ σ : E →+* E)
    (hc : ∀ z, τ (σ z)=σ (τ z)) (ω : E)
    (hω : ω^2+ω+1=0) (hτ : τ ω=ω^2) (hσ : σ ω=ω^2) (y : E) :
    ¬ (kernel τ σ 1 y=1 ∧ kernel τ σ ω y=1 ∧ kernel τ σ (ω^2) y=1) := by
  have hω3 : ω^3=1 := by linear_combination (ω-1)*hω
  have hω4 : ω^4=ω := by rw [show (4:ℕ)=3+1 from rfl,pow_add,hω3]; simp
  have hτω2 : τ (τ ω)=ω := by rw [hτ,map_pow,hτ,←pow_mul]; exact hω4
  have hτωsq : τ (ω^2)=ω := by rw [←hτ]; exact hτω2
  have hω2σ : σ (ω^2)=ω := by rw [map_pow,hσ,←pow_mul]; exact hω4
  have hg₁ : (ω*y)*σ (ω*y)=y*σ y := by
    rw [map_mul,hσ]
    linear_combination y*σ y*(hω3)
  have hg₂ : (ω^2*y)*σ (ω^2*y)=y*σ y := by
    rw [map_mul,hω2σ]
    linear_combination y*σ y*(hω3)
  rintro ⟨h₀,h₁,h₂⟩
  change tr4 τ ((1*y)*σ (1*y)+1*y)=1 at h₀
  change tr4 τ ((ω*y)*σ (ω*y)+ω*y)=1 at h₁
  change tr4 τ ((ω^2*y)*σ (ω^2*y)+ω^2*y)=1 at h₂
  simp only [one_mul] at h₀
  rw [hg₁] at h₁
  rw [hg₂] at h₂
  rw [tr4_add] at h₀ h₁ h₂
  have hsum : tr4 τ y+tr4 τ (ω*y)+tr4 τ (ω^2*y)=0 := by
    rw [←tr4_add,←tr4_add]
    have he : y+ω*y+ω^2*y=0 := by linear_combination y*hω
    rw [he,tr4_zero]
  have hgold : tr4 τ (y*σ y)=1 := by
    linear_combination (norm := (ring_nf; reduce_mod_char!)) h₀+h₁+h₂-hsum
  have ht₀ : tr4 τ y=0 := by linear_combination h₀-hgold
  have ht₁ : tr4 τ (ω*y)=0 := by linear_combination h₁-hgold
  have hb : y+τ (τ y)=0 := by
    dsimp [tr4] at ht₀ ht₁
    simp only [map_mul,hτ,hτωsq] at ht₁
    linear_combination (norm := (ring_nf; reduce_mod_char!))
      ht₁-ω^2*ht₀-(y+τ (τ y))*hω
  have hy : τ (τ y)=y := by
    linear_combination (norm := (ring_nf; reduce_mod_char!)) hb
  have hys : τ (τ (σ y))=σ y := by rw [hc,hc,hy]
  have hg : tr4 τ (y*σ y)=0 := by
    dsimp [tr4]
    simp only [map_mul,hy,hys]
    ring_nf
    reduce_mod_char!
  exact one_ne_zero (hgold.symm.trans hg)

end Erdos714GoldTrace
#print axioms Erdos714GoldTrace.three_ray_no_common
