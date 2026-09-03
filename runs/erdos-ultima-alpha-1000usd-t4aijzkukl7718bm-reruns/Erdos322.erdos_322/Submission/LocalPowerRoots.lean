import FormalConjecturesUtil

/-! Elementary nonsingular power roots modulo prime powers. -/
namespace Erdos322Research.LocalPowerRoots
noncomputable section
open Finset

variable (p : ℕ) [Fact p.Prime]

/-- Reduction from a prime-power ring to its prime field. -/
def reduction (e : ℕ) : ZMod (p^(e+1)) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by omega : e+1 ≠ 0)) (ZMod p)

@[simp] lemma reduction_natCast (e a : ℕ) : reduction p e (a : ZMod (p^(e+1)))=(a : ZMod p) :=
  map_natCast _ _

lemma isUnit_of_reduction_ne_zero (e : ℕ) (a : ZMod (p^(e+1)))
    (ha : reduction p e a ≠ 0) : IsUnit a := by
  have hp : p.Prime := Fact.out
  have hn : ¬p ∣ a.val := by
    intro hd
    apply ha
    rw [← ZMod.natCast_zmod_val a, reduction_natCast]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hc : a.val.Coprime (p^(e+1)) := hp.coprime_pow_of_not_dvd hn
  rw [← ZMod.natCast_zmod_val a]
  exact (ZMod.isUnit_iff_coprime _ _).mpr hc

/-- The power map is injective on each nonsingular residue class. -/
theorem pow_injective_on_residue (e k : ℕ) (hk : ¬p ∣ k) (a : ZMod p) (ha : a ≠ 0)
    (x y : ZMod (p^(e+1))) (hx : reduction p e x=a) (hy : reduction p e y=a)
    (h : x^k=y^k) : x=y := by
  let S : ZMod (p^(e+1)) := ∑ i ∈ range k, x^i*y^(k-1-i)
  have hs : reduction p e S=(k : ZMod p)*a^(k-1) := by
    simp only [S,map_sum,map_mul,map_pow,hx,hy,geom_sum₂_self]
  have hu : IsUnit S := by
    apply isUnit_of_reduction_ne_zero p e
    rw [hs]
    exact mul_ne_zero ((ZMod.natCast_eq_zero_iff _ _).not.mpr hk) (pow_ne_zero _ ha)
  have he : S*(x-y)=S*0 := by
    dsimp only [S]
    rw [geom_sum₂_mul,h,sub_self,mul_zero]
  exact sub_eq_zero.mp (hu.mul_left_cancel he)

/-- Every value in the appropriate residue class has a unique power root
in a chosen nonsingular residue class, at every prime-power modulus. -/
theorem exists_pow_root (e k : ℕ) (hk : ¬p ∣ k) (a : ZMod p) (ha : a ≠ 0)
    (v : ZMod (p^(e+1))) (hv : reduction p e v=a^k) :
    ∃ x : ZMod (p^(e+1)), reduction p e x=a ∧ x^k=v := by
  classical
  let A : ZMod (p^(e+1)) := a.val
  have hA : reduction p e A=a := by simp [A]
  let T := {x : ZMod (p^(e+1)) // reduction p e x=a}
  let f : T → T := fun x ↦ ⟨x.val^k-A^k+A, by
    simp only [map_add,map_sub,map_pow,x.property,hA]
    ring⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply pow_injective_on_residue p e k hk a ha x.val y.val x.property y.property
    have he := congrArg (fun z : T ↦ z.val) hxy
    change x.val^k-A^k+A=y.val^k-A^k+A at he
    linear_combination he
  have ht : reduction p e (v-A^k+A)=a := by
    simp only [map_add,map_sub,map_pow,hv,hA]
    ring
  obtain ⟨x,hx⟩ := Finite.surjective_of_injective hf (⟨v-A^k+A,ht⟩ : T)
  refine ⟨x.val,x.property,?_⟩
  have he := congrArg (fun z : T ↦ z.val) hx
  change x.val^k-A^k+A=v-A^k+A at he
  linear_combination he

end
end Erdos322Research.LocalPowerRoots
