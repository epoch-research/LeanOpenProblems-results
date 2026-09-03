import Submission.CubicTraceNormPlane
import Submission.NormLineBound

/-! Aligning a cubic norm plane with an anisotropic quadratic central cocycle.
This excludes another candidate construction, not the Erdős conjecture. -/
noncomputable section
open Classical
open scoped CharTwo
set_option maxHeartbeats 4000000
namespace Erdos714QuaternionNormPlane
open Erdos714BinaryLift
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Four distinct points of a constant cubic norm cannot lie on an F-line. -/
lemma not_scalar [FiniteDimensional F E] [CharP E 2]
    (hdim : Module.finrank F E=3) (p u v : E)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hn : ∀ i, Algebra.norm F (p+plane u v i)=Algebra.norm F p) :
    ∀ t : F, v ≠ t • u := by
  intro t ht
  let s : Fin 4 → F := ![0,1,t,1+t]
  have he (i : Fin 4) : s i • u=plane u v i := by
    fin_cases i <;> simp [s,plane,ht,add_smul]
  have hs : Function.Injective s := by
    intro i j h
    apply plane_injective hu hv huv
    rw [← he,← he,h]
  exact hu (Erdos714NormLine.cubic_direction_zero hdim p u (Algebra.norm F p) ⟨s,hs⟩
    (fun i => by change Algebra.norm F (p+s i • u)=_; rw [he]; exact hn i))

def quad (eta x y : F) : F := x^2+x*y+eta*y^2

lemma quad_scale (eta s x y : F) : quad eta (s*x) (s*y)=s^2*quad eta x y := by
  unfold quad
  ring

def central (b : (F × F × F) ≃ₗ[F] E) : E := b (0,0,1)

lemma central_ne_zero (b : (F × F × F) ≃ₗ[F] E) : central b ≠ 0 := by
  intro h
  have hb : b (0,0,(1:F))=b 0 := by rw [map_zero]; exact h
  have he := b.injective hb
  exact one_ne_zero (congrArg (fun z : F × F × F => z.2.2) he)

/-- After aligning one norm-plane direction with the center, its other
projection is nonzero. An anisotropic quadratic form then supplies the
unique nonzero scaling which makes the plane a cyclic-four orbit. -/
theorem exists_cyclic_plane [Fintype F] [Fintype E] [CharP E 2]
    (hdim : Module.finrank F E=3) (b : (F × F × F) ≃ₗ[F] E)
    (eta : F) (hQ : ∀ x y, quad eta x y=0 → x=0 ∧ y=0) :
    ∃ p v : E,
      let s := quad eta (b.symm v).1 (b.symm v).2.1
      s ≠ 0 ∧ Algebra.norm F p ≠ 0 ∧ ∀ i : Fin 4,
        Algebra.norm F (p+plane (s • central b) v i)=Algebra.norm F p := by
  obtain ⟨p,u,v,hu,hv,huv,_,_,hp,hn⟩ :=
    Erdos714CubicTraceNormPlane.exists_plane_in_kernel hdim (0 : E →ₗ[F] F)
  have hns := not_scalar hdim p u v hu hv huv hn
  let c := central b/u
  have hc : c ≠ 0 := div_ne_zero (central_ne_zero b) hu
  have hcu : c*u=central b := div_mul_cancel₀ _ hu
  let v' := c*v
  let k := quad eta (b.symm v').1 (b.symm v').2.1
  have hk : k ≠ 0 := by
    intro hk0
    obtain ⟨hx,hy⟩ := hQ _ _ hk0
    let t : F := (b.symm v').2.2
    have he : v'=t • central b := by
      apply b.symm.injective
      simp only [map_smul,central,LinearEquiv.symm_apply_apply]
      apply Prod.ext
      · simpa using hx
      · apply Prod.ext
        · simpa using hy
        · simp [t]
    apply hns t
    apply mul_left_cancel₀ hc
    calc
      c*v = t • central b := he
      _ = t • (c*u) := by rw [hcu]
      _ = c*(t • u) := by rw [Algebra.smul_def,Algebra.smul_def]; ring
  let s := k⁻¹
  have hs : s ≠ 0 := inv_ne_zero hk
  let d : E := algebraMap F E s*c
  have hd : d ≠ 0 := mul_ne_zero (by simpa using (algebraMap F E).injective.ne hs) hc
  have hdu : d*u=s • central b := by
    simp [d,Algebra.smul_def,mul_assoc,hcu]
  have hdv : d*v=s • v' := by simp [d,v',Algebra.smul_def,mul_assoc]
  have hq : quad eta (b.symm (d*v)).1 (b.symm (d*v)).2.1=s := by
    rw [hdv,map_smul]
    change quad eta (s*(b.symm v').1) (s*(b.symm v').2.1)=s
    rw [quad_scale]
    change s^2*k=s
    dsimp [s]
    field_simp
  refine ⟨d*p,d*v,?_⟩
  dsimp only
  rw [hq]
  refine ⟨hs,?_,?_⟩
  · rw [map_mul]
    exact mul_ne_zero (Algebra.norm_ne_zero_iff.mpr hd) hp
  · intro i
    have he : d*p+plane (s • central b) (d*v) i=d*(p+plane u v i) := by
      rw [← hdu]
      fin_cases i <;> simp [plane] <;> ring
    rw [he,map_mul,hn]
    exact (map_mul (Algebra.norm F) d p).symm

#print axioms not_scalar
#print axioms exists_cyclic_plane
end Erdos714QuaternionNormPlane
