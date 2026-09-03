import Submission.QuaternionCubicNorm

/-! The complementary isotropic case, completing the exclusion of this
entire bilinear central-extension family in binary characteristic. This
still does not settle Erdős Problem 714. -/
noncomputable section
open SimpleGraph Classical
open scoped CharTwo
set_option maxHeartbeats 5000000
namespace Erdos714QuaternionCubicAll
open Erdos714QuaternionCubicNorm
open Erdos714QuaternionNormPlane (quad)
open Erdos714BinaryLift (plane)
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable (eta : F) (b : (F × F × F) ≃ₗ[F] E)

def linearCoordinate (t : F) : E →ₗ[F] F where
  toFun a := (b.symm a).1-t*(b.symm a).2.1
  map_add' a c := by simp [mul_add]; ring
  map_smul' s a := by simp; ring

lemma coord_eq (t : F) {a : E} (ha : linearCoordinate b t a=0) :
    (b.symm a).1=t*(b.symm a).2.1 := sub_eq_zero.mp ha

lemma cocycle_zero (t : F) (ht : t^2+t+eta=0) (a z : E)
    (ha : linearCoordinate b t a=0) (hz : linearCoordinate b t z=0) :
    cocycle eta (b.symm a).1 (b.symm a).2.1 (b.symm z).1 (b.symm z).2.1=0 := by
  rw [coord_eq b t ha,coord_eq b t hz]
  unfold cocycle
  linear_combination ((b.symm a).2.1*(b.symm z).2.1)*ht

lemma quad_zero (t : F) (ht : t^2+t+eta=0) (a : E)
    (ha : linearCoordinate b t a=0) : quad eta (b.symm a).1 (b.symm a).2.1=0 := by
  simpa [quad,cocycle,pow_two,mul_assoc] using cocycle_zero eta b t ht a a ha ha

lemma generator_injective (p : E) : Function.Injective (generator eta b p) := by
  intro a z h
  have he := congrArg (fun g => value eta b (g*fromE eta b p)) h
  have he' : a+p=z+p := by simpa only [generator_step] using he
  exact add_right_cancel he'

/-- On the isotropic direction plane, the cross term vanishes between
directions. The generator's central correction cancels its interaction
with the affine base point. -/
lemma generator_step_add (p a z : E)
    (hC : cocycle eta (b.symm a).1 (b.symm a).2.1 (b.symm z).1 (b.symm z).2.1=0) :
    value eta b (generator eta b p a*fromE eta b (p+z))=a+p+z := by
  have he : coords eta (generator eta b p a*fromE eta b (p+z))=
      b.symm a+b.symm p+b.symm z := by
    apply Prod.ext
    · change (b.symm a).1+(b.symm (p+z)).1=(b.symm a).1+(b.symm p).1+(b.symm z).1
      simp [add_assoc]
    · apply Prod.ext
      · change (b.symm a).2.1+(b.symm (p+z)).2.1=(b.symm a).2.1+(b.symm p).2.1+(b.symm z).2.1
        simp [add_assoc]
      · change (b.symm a).2.2-cocycle eta (b.symm a).1 (b.symm a).2.1 (b.symm p).1 (b.symm p).2.1+
          (b.symm (p+z)).2.2+cocycle eta (b.symm a).1 (b.symm a).2.1 (b.symm (p+z)).1 (b.symm (p+z)).2.1=
          (b.symm a).2.2+(b.symm p).2.2+(b.symm z).2.2
        rw [map_add]
        dsimp only [Prod.fst_add,Prod.snd_add]
        unfold cocycle at hC ⊢
        linear_combination hC
  simp [value,he]

lemma generator_inv [CharP F 2] (t : F) (ht : t^2+t+eta=0) (p a : E)
    (ha : linearCoordinate b t a=0) : (generator eta b p a)⁻¹=generator eta b p a := by
  have hs : (generator eta b p a)^2=1 := by
    rw [square]
    change center eta (quad eta (b.symm a).1 (b.symm a).2.1)=1
    rw [quad_zero eta b t ht a ha]
    rfl
  exact inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs)

def planeCopy [CharP F 2] [CharP E 2] (t : F) (ht : t^2+t+eta=0)
    (p u v : E) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hlu : linearCoordinate b t u=0) (hlv : linearCoordinate b t v=0)
    (hp : Algebra.norm F p ≠ 0)
    (hn : ∀ i, Algebra.norm F (p+plane u v i)=Algebra.norm F p) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Copy (graph eta b) := by
  let P := plane u v
  have hP : Function.Injective P := Erdos714BinaryLift.plane_injective hu hv huv
  have hzero (i : Fin 4) : linearCoordinate b t (P i)=0 := by
    fin_cases i <;> simp [P,plane,hlu,hlv]
  have from_inj : Function.Injective (fromE eta b) := (coords eta).symm.injective.comp b.symm.injective
  let L : Fin 4 → Root F eta × Fˣ := fun i => (generator eta b p (P i),1)
  let R : Fin 4 → Root F eta × Fˣ := fun i => (fromE eta b (p+P i),Units.mk0 (Algebra.norm F p) hp)
  have hL : Function.Injective L := fun i j h => hP (generator_injective eta b p (congrArg Prod.fst h))
  have hR : Function.Injective R := fun i j h => hP (add_left_cancel (from_inj (congrArg Prod.fst h)))
  have hedge (i j : Fin 4) : (graph eta b).Adj (.inl (L i)) (.inr (R j)) := by
    change Algebra.norm F (value eta b ((generator eta b p (P i))⁻¹*fromE eta b (p+P j)))=1*Algebra.norm F p
    rw [generator_inv eta b t ht p _ (hzero i),generator_step_add eta b p (P i) (P j)
      (cocycle_zero eta b t ht _ _ (hzero i) (hzero j)),one_mul]
    obtain ⟨k,hk⟩ := Erdos714BinaryLift.plane_closed u v i j
    simpa only [P,add_comm,add_left_comm,add_assoc] using
      (congrArg (fun x => Algebra.norm F (p+x)) hk).trans (hn k)
  refine ⟨⟨Sum.map L R,?_⟩,Sum.map_injective.mpr ⟨hL,hR⟩⟩
  intro a z haz
  cases a with
  | inl i => cases z with
    | inl j => simp at haz
    | inr j => exact hedge i j
  | inr i => cases z with
    | inl j => exact hedge j i
    | inr j => simp at haz

theorem isotropic_not_free [Fintype F] [Fintype E] [CharP F 2]
    (hdim : Module.finrank F E=3) (t : F) (ht : t^2+t+eta=0) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph eta b) := by
  letI : CharP E 2 := charP_of_injective_algebraMap (algebraMap F E).injective 2
  obtain ⟨p,u,v,hu,hv,huv,hlu,hlv,hp,hn⟩ :=
    Erdos714CubicTraceNormPlane.exists_plane_in_kernel hdim (linearCoordinate b t)
  exact fun hf => hf ⟨planeCopy eta b t ht p u v hu hv huv hlu hlv hp hn⟩

/-- All cocycle parameters are covered, not just a selected anisotropic
parameter or a selected cubic-field basis. -/
theorem not_free [Fintype F] [Fintype E] [CharP F 2]
    (hdim : Module.finrank F E=3) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph eta b) := by
  by_cases ht : ∃ t : F, t^2+t+eta=0
  · obtain ⟨t,ht⟩ := ht
    exact isotropic_not_free eta b hdim t ht
  · apply Erdos714QuaternionCubicNorm.not_free eta b hdim
    intro x y hxy
    by_cases hy : y=0
    · subst y
      simp [quad] at hxy
      exact ⟨hxy,rfl⟩
    · exfalso
      apply ht
      refine ⟨x/y,?_⟩
      apply (mul_right_inj' (pow_ne_zero 2 hy)).mp
      field_simp
      unfold quad at hxy
      linear_combination hxy

#print axioms generator_step_add
#print axioms planeCopy
#print axioms isotropic_not_free
#print axioms not_free
end Erdos714QuaternionCubicAll
