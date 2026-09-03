import Submission.CrossGraphExplore

/-! A non-Cartesian finite lift whose first natural row is the parameter set.
Neither field addition nor the lift's scale is identified with integer addition. -/
namespace Erdos66ShearedParabolaPrefix
open Erdos66OriginRepair Erdos66FiniteField Erdos66CrossGraph
open scoped Classical
set_option maxHeartbeats 1400000

lemma pairCount_addEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [DecidableEq G] [DecidableEq H] (f : G ≃+ H) (A B : Finset G) (z : G) :
    pairCount (A.image f) (B.image f) (f z)=pairCount A B z := by
  unfold pairCount
  rw [Finset.filter_image,Finset.card_image_of_injective _ f.injective]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  have he : f z-f x∈B.image f ↔ z-x∈B := by
    rw [←map_sub]
    exact Finset.mem_image.trans (by
      constructor
      · rintro ⟨y,hy,he⟩
        exact f.injective he ▸ hy
      · intro hx
        exact ⟨z-x,hx,rfl⟩)
  rw [he]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def shear : (F × F) ≃+ (F × F) where
  toFun z := (z.1,z.2-z.1)
  invFun z := (z.1,z.2+z.1)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_add' z w := by ext <;> dsimp <;> ring

noncomputable def sheared (U : Finset F) : Finset (F × F) := (parabolaSet U).image shear

lemma mem_sheared (U : Finset F) (x y : F) :
    (x,y)∈sheared U ↔ ∃ u∈U, y+x=x^2/u := by
  have he : (x,y)=shear (x,y+x) := by ext <;> simp [shear]
  rw [he]
  simp only [sheared,Finset.mem_image,EmbeddingLike.apply_eq_iff_eq]
  constructor
  · rintro ⟨z,hz,hze⟩
    have hz' : z=(x,y+x) := hze
    subst z
    simpa only [parabolaSet,Finset.mem_filter,Finset.mem_univ,true_and] using hz
  · intro h
    refine ⟨(x,y+x),?_,rfl⟩
    simpa only [parabolaSet,Finset.mem_filter,Finset.mem_univ,true_and] using h

lemma first_row (U : Finset F) (hU : ∀ u∈U, u≠0) (hne : U.Nonempty) (x : F) :
    (x,0)∈sheared U ↔ x=0 ∨ x∈U := by
  rw [mem_sheared,zero_add]
  constructor
  · rintro ⟨u,hu,he⟩
    have he' := (eq_div_iff (hU u hu)).mp he
    have hz : x*(x-u)=0 := by linear_combination -he'
    rcases mul_eq_zero.mp hz with hx | hx
    · exact Or.inl hx
    · exact Or.inr (sub_eq_zero.mp hx ▸ hu)
  · rintro (rfl | hx)
    · obtain ⟨u,hu⟩ := hne
      exact ⟨u,hu,by simp⟩
    · refine ⟨x,hx,?_⟩
      apply (eq_div_iff (hU x hx)).mpr
      ring

lemma sheared_pairCount (U V : Finset F) (z : F × F) :
    pairCount (sheared U) (sheared V) (shear z)=pairCount (parabolaSet U) (parabolaSet V) z :=
  pairCount_addEquiv (shear (F := F)) (parabolaSet U) (parabolaSet V) z

noncomputable def encoded (p : ℕ) [Fact p.Prime] (U : Finset (ZMod p)) : Finset ℕ :=
  (sheared U).image (fun z ↦ z.1.val+p*z.2.val)

lemma encoded_prefix (p : ℕ) [Fact p.Prime] (U : Finset (ZMod p))
    (hU : ∀ u∈U, u≠0) (hne : U.Nonempty) (n : ℕ) (hn : n<p) :
    n∈encoded p U ↔ n=0 ∨ (n:ZMod p)∈U := by
  have hp : 0<p := NeZero.pos p
  constructor
  · rintro h
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp h
    have hx := z.1.val_lt
    have hy := z.2.val_lt
    have hy0 : z.2.val=0 := by nlinarith
    have hz2 : z.2=0 := ZMod.val_injective p (by simpa only [ZMod.val_zero] using hy0)
    have hzn : z.1.val=n := by simpa only [hy0,mul_zero,add_zero] using he
    have hz1 : z.1=(n:ZMod p) := by rw [←hzn,ZMod.natCast_zmod_val]
    have hze : z=((n:ZMod p),0) := Prod.ext hz1 hz2
    have hrow := (first_row U hU hne (n:ZMod p)).mp (by simpa only [hze] using hz)
    rcases hrow with h0 | hu
    · left
      have hv := congrArg ZMod.val h0
      simpa only [ZMod.val_natCast_of_lt hn,ZMod.val_zero] using hv
    · exact Or.inr hu
  · intro h
    have hrow : ((n:ZMod p),0)∈sheared U := by
      apply (first_row U hU hne _).mpr
      rcases h with rfl | h
      · exact Or.inl (by simp)
      · exact Or.inr h
    exact Finset.mem_image.mpr ⟨((n:ZMod p),0),hrow,by simp [ZMod.val_natCast_of_lt hn]⟩

lemma encoded_lt (p : ℕ) [Fact p.Prime] (U : Finset (ZMod p)) {n : ℕ}
    (hn : n∈encoded p U) : n<p^2 := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hn
  have hx := z.1.val_lt
  have hy := z.2.val_lt
  nlinarith

end Erdos66ShearedParabolaPrefix
