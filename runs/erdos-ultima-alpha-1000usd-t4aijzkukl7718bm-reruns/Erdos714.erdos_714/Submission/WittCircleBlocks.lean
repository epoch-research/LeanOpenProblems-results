import Submission.WittNormCircleFinite

/-!
Growing quadratic blocks in the odd-degree binary Witt norm-circle host.
The block cover will concern arbitrary edge thinnings, not just induced
subgraphs. This is a construction obstruction, not Erdős714.
-/
noncomputable section
open Classical SimpleGraph Finset
open scoped CharTwo
set_option maxHeartbeats 3000000
namespace Erdos714WittCircleBlocks
open Erdos714WittNormCircle
variable {E : Type*} [Field E] [CharP E 2]

def wittNeg (p : E × E) : E × E := (p.1,p.2+p.1^2)

lemma witt_cancel (p u v : E × E) :
    wittAdd (wittAdd p u) (wittAdd (wittNeg p) v)=wittAdd u v := by
  have h2 : (2:E)=0 := CharP.cast_eq_zero E 2
  apply Prod.ext <;> dsimp [wittAdd,wittNeg] <;> ring_nf <;> simp only [h2,mul_zero,add_zero,zero_add]

lemma witt_cancel_right (p u : E × E) : wittAdd (wittAdd p (wittNeg u)) u=p := by
  have h2 : (2:E)=0 := CharP.cast_eq_zero E 2
  apply Prod.ext <;> dsimp [wittAdd,wittNeg] <;> ring_nf <;> simp only [h2,mul_zero,add_zero]

omit [CharP E 2] in
lemma witt_left_injective (p : E × E) : Function.Injective (wittAdd p) := by
  intro u v h
  have h₁ : u.1=v.1 := add_left_cancel (congrArg Prod.fst h)
  have h₂ := congrArg Prod.snd h
  change p.2+u.2+p.1*u.1=p.2+v.2+p.1*v.1 at h₂
  rw [h₁] at h₂
  exact Prod.ext h₁ (add_left_cancel (add_right_cancel h₂))

lemma translate_cover (r c u v : E × E) (h : wittAdd r c=wittAdd u v) :
    ∃ p : E × E, wittAdd p u=r ∧ wittAdd (wittNeg p) v=c := by
  let p := wittAdd r (wittNeg u)
  have hp : wittAdd p u=r := witt_cancel_right r u
  refine ⟨p,hp,?_⟩
  apply witt_left_injective r
  rw [←hp,witt_cancel,hp]
  exact h.symm

omit [CharP E 2] in
lemma norm_mul (τ : E →+* E) (x y : E) :
    conjugateNorm τ (x*y)=conjugateNorm τ x*conjugateNorm τ y := by
  simp only [conjugateNorm,map_mul]
  ring

omit [CharP E 2] in
lemma norm_div (τ : E →+* E) (x y : E) :
    conjugateNorm τ (x/y)=conjugateNorm τ x/conjugateNorm τ y := by
  simp only [conjugateNorm,map_div₀]
  ring

omit [CharP E 2] in
lemma norm_pow (τ : E →+* E) (x : E) (n : ℕ) :
    conjugateNorm τ (x^n)=(conjugateNorm τ x)^n := by
  simp only [conjugateNorm,map_pow,mul_pow]

omit [CharP E 2] in
lemma norm_nonzero (τ : E →+* E) (x : E) (hx : x ≠ 0) : conjugateNorm τ x ≠ 0 :=
  mul_ne_zero hx (by simpa only [map_zero] using τ.injective.ne hx)

/-- The elementary degree-two Hilbert-90 calculation. -/
lemma hilbert90 (τ : E →+* E) (d : E) (hd : conjugateNorm τ d=1) :
    ∃ s : E, s ≠ 0 ∧ τ s=d*s := by
  by_cases he : d=1
  · exact ⟨1,one_ne_zero,by simp [he]⟩
  have hd0 : d ≠ 0 := by intro hz; simp [hz,conjugateNorm] at hd
  have hτ : τ d=d⁻¹ := by
    apply (mul_left_cancel₀ hd0)
    simpa only [mul_inv_cancel₀ hd0,conjugateNorm] using hd
  refine ⟨1+d⁻¹,?_,?_⟩
  · intro hz
    have hi : d⁻¹=1 := by simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_right hz
    exact he (inv_eq_one.mp hi)
  · rw [map_add,map_one,map_inv₀,hτ,inv_inv,mul_add,mul_one,mul_inv_cancel₀ hd0]
    exact add_comm _ _

variable {F : Type*} [Field F] [Algebra F E]

/-- Two parabolic row and column curves. A nonzero common sum gives an edge. -/
def left (η α : E) (x : F) : E × E :=
  (α*algebraMap F E x,η*(α*algebraMap F E x)^2)
def right (η α : E) (t : F) : E × E :=
  (η*(α*algebraMap F E t),η*(α*algebraMap F E t)^2)

lemma norm_coordinates (τ : E →+* E) (η : E)
    (hη : η^2+η=1) (hτη : τ η=η+1)
    (hfix : ∀ x : F, τ (algebraMap F E x)=algebraMap F E x) (x t : F) :
    conjugateNorm τ (algebraMap F E x+η*algebraMap F E t)=
      (algebraMap F E x)^2+algebraMap F E x*algebraMap F E t+(algebraMap F E t)^2 := by
  have h2 : (2:E)=0 := CharP.cast_eq_zero E 2
  rw [conjugateNorm,map_add,map_mul,hfix,hfix,hτη]
  calc
    _ = (algebraMap F E x)^2+algebraMap F E x*algebraMap F E t+
        (η^2+η)*(algebraMap F E t)^2 := by
      ring_nf
      simp only [h2,mul_zero,zero_add]
    _ = _ := by rw [hη,one_mul]

lemma block_sum (τ : E →+* E) (η : E)
    (hη : η^2+η=1) (hτη : τ η=η+1)
    (hfix : ∀ x : F, τ (algebraMap F E x)=algebraMap F E x)
    (α : E) (x t : F) :
    wittAdd (left η α x) (right η α t) =
      (α*(algebraMap F E x+η*algebraMap F E t),
        α^2*η*conjugateNorm τ (algebraMap F E x+η*algebraMap F E t)) := by
  rw [norm_coordinates τ η hη hτη hfix]
  apply Prod.ext <;> dsimp [left,right,wittAdd] <;> ring

/-- Every norm-circle connection is a scaled sum from the two curves. -/
lemma connection_chart (τ : E →+* E) (η : E)
    (hη : η^2+η=1) (hτη : τ η=η+1)
    (hfix : ∀ x : F, τ (algebraMap F E x)=algebraMap F E x)
    (hcoord : ∀ s : E, ∃ x t : F, s=algebraMap F E x+η*algebraMap F E t)
    (s z : E) (hs : s ≠ 0) (hz : conjugateNorm τ z=(conjugateNorm τ s)^2) :
    ∃ α : E, α ≠ 0 ∧ ∃ x t : F, wittAdd (left η α x) (right η α t)=(s,z) := by
  have hnη : conjugateNorm τ η=1 := by
    rw [conjugateNorm,hτη]
    linear_combination hη
  have hη0 : η ≠ 0 := by intro he; simp [he] at hη
  let d := z/(η*s^2)
  have hd : conjugateNorm τ d=1 := by
    dsimp [d]
    rw [norm_div,norm_mul,norm_pow,hnη,one_mul,hz]
    exact div_self (pow_ne_zero 2 (norm_nonzero τ s hs))
  obtain ⟨w,hw,hτw⟩ := hilbert90 τ d hd
  obtain ⟨x,t,hcoordw⟩ := hcoord w
  refine ⟨s/w,div_ne_zero hs hw,x,t,?_⟩
  rw [block_sum τ η hη hτη hfix,←hcoordw,div_mul_cancel₀ _ hw]
  apply Prod.ext
  · rfl
  · dsimp
    rw [conjugateNorm,hτw]
    dsimp [d]
    field_simp

omit [CharP E 2] in
/-- Rescaling a block by a base-field unit does not change its vertex curves. -/
lemma adjust_scalar (α β : E) (u : Fˣ) (hu : (u : F) • α=β) (x : F) :
    β*algebraMap F E ((u : F)⁻¹*x)=α*algebraMap F E x := by
  rw [←hu,Algebra.smul_def,map_mul,map_inv₀]
  have hu0 : algebraMap F E (u : F) ≠ 0 := by simp
  field_simp

/-- Projective block scales suffice: there are only q+1, not q^2-1. -/
lemma projective_chart (τ : E →+* E) (η : E)
    (hη : η^2+η=1) (hτη : τ η=η+1)
    (hfix : ∀ x : F, τ (algebraMap F E x)=algebraMap F E x)
    (hcoord : ∀ s : E, ∃ x t : F, s=algebraMap F E x+η*algebraMap F E t)
    (r c : E × E) (hedge : (graph τ).Adj (.inl r) (.inr c)) :
    ∃ l : Projectivization F E, ∃ p : E × E, ∃ x t : F,
      wittAdd p (left η l.rep x)=r ∧ wittAdd (wittNeg p) (right η l.rep t)=c := by
  obtain ⟨α,hα,x,t,hxt⟩ := connection_chart τ η hη hτη hfix hcoord
    (wittAdd r c).1 (wittAdd r c).2 hedge.1 hedge.2
  let l := Projectivization.mk F α hα
  obtain ⟨u,hu⟩ := Projectivization.exists_smul_eq_mk_rep F α hα
  have hu' : (u : F) • α=l.rep := by simpa only [Units.smul_def] using hu
  have hx : left η l.rep ((u : F)⁻¹*x)=left η α x := by
    simp only [left,adjust_scalar α l.rep u hu']
  have ht : right η l.rep ((u : F)⁻¹*t)=right η α t := by
    simp only [right,adjust_scalar α l.rep u hu']
  have he : wittAdd r c=wittAdd (left η l.rep ((u : F)⁻¹*x)) (right η l.rep ((u : F)⁻¹*t)) := by
    rw [hx,ht,hxt]
  obtain ⟨p,hp,hc⟩ := translate_cover r c _ _ he
  exact ⟨l,p,_,_,hp,hc⟩

#print axioms witt_cancel
#print axioms hilbert90
#print axioms connection_chart
#print axioms projective_chart
end Erdos714WittCircleBlocks
