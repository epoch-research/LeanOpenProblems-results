import FormalConjecturesUtil

/-!
A coset obstruction for a characteristic-two quartic-trace graph candidate.
This file does not settle Erdős Problem 714.
-/

open SimpleGraph
open scoped CharTwo

namespace Erdos714QuarticTrace

variable {E : Type*} [CommRing E] [Nontrivial E] [CharP E 2]

def quarticForm (x y : E) : E := x^3*y + x*y^3

lemma quarticForm_factor (x y : E) : quarticForm x y = x*y*(x+y)^2 := by
  have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
  rw [add_sq, h2]
  simp only [zero_mul, add_zero]
  unfold quarticForm
  ring

lemma quarticForm_symm (x y : E) : quarticForm x y = quarticForm y x := by
  unfold quarticForm
  ring

@[simp] lemma quarticForm_self (x : E) : quarticForm x x = 0 := by
  rw [quarticForm_factor, CharTwo.add_self_eq_zero]
  simp

/-- A relative trace followed by any additive outer trace. -/
def graph (ρ : E →+* E) (T : E →+ E) : SimpleGraph E where
  Adj x y := T (quarticForm x y + ρ (quarticForm x y)) = 1
  symm := by
    intro x y h
    simpa only [quarticForm_symm y x] using h
  loopless := by
    intro x
    simp

/-- On a coset of the fixed ring, the relative quartic trace is a polynomial in the sum. -/
theorem coset_identity (ρ : E →+* E) (θ a b : E)
    (hθ : ρ θ = θ + 1) (ha : ρ a = a) (hb : ρ b = b) :
    quarticForm (θ+a) (θ+b) + ρ (quarticForm (θ+a) (θ+b)) =
      (a+b)^3 + (a+b)^2 := by
  have hsum : (θ+a)+(θ+b) = a+b := by
    calc
      (θ+a)+(θ+b) = (θ+θ)+(a+b) := by ring
      _ = a+b := by rw [CharTwo.add_self_eq_zero, zero_add]
  rw [quarticForm_factor, hsum]
  simp only [map_mul, map_pow, map_add, hθ, ha, hb]
  have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
  calc
    (θ+a)*(θ+b)*(a+b)^2 + (θ+1+a)*(θ+1+b)*(a+b)^2 =
        (2*(θ+a)*(θ+b) + (θ+θ) + a+b+1)*(a+b)^2 := by ring
    _ = (a+b)^3+(a+b)^2 := by
      rw [h2, CharTwo.add_self_eq_zero]
      ring

lemma graph_coset_adj (ρ : E →+* E) (T : E →+ E) (θ a b : E)
    (hθ : ρ θ = θ+1) (ha : ρ a = a) (hb : ρ b = b) :
    (graph ρ T).Adj (θ+a) (θ+b) ↔ T ((a+b)^3+(a+b)^2) = 1 := by
  change T (_ + _) = 1 ↔ _
  rw [coset_identity ρ θ a b hθ ha hb]

/-- The four elements of a binary plane. -/
def plane (u v : E) : Fin 4 → E := ![0,u,v,u+v]

lemma plane_injective {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Function.Injective (plane u v) := by
  have huv0 : u+v ≠ 0 := fun h => huv (CharTwo.add_eq_zero.mp h)
  have huuv : u ≠ u+v := by
    intro h
    apply hv
    exact (add_left_cancel (show u+0 = u+v by simpa using h)).symm
  have hvuv : v ≠ u+v := by
    intro h
    apply hu
    exact (add_right_cancel (show 0+v = u+v by simpa using h)).symm
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [plane, hu, hv, huv, huv0, huuv, hvuv, Ne.symm hu, Ne.symm hv,
      Ne.symm huv, Ne.symm huv0, Ne.symm huuv, Ne.symm hvuv] at h ⊢

lemma plane_closed (u v : E) (i j : Fin 4) :
    ∃ k, plane u v i + plane u v j = plane u v k := by
  fin_cases i <;> fin_cases j <;>
    simp [Fin.exists_fin_succ, plane, add_assoc, add_left_comm, add_comm]

/-- An affine plane in the reduced connection set gives eight distinct graph vertices. -/
theorem not_free_of_coset_plane (ρ : E →+* E) (T : E →+ E)
    (θ p u v : E) (hθ : ρ θ = θ+1)
    (hp : ρ p = p) (hu' : ρ u = u) (hv' : ρ v = v)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hS : ∀ i : Fin 4,
      T ((p+plane u v i)^3 + (p+plane u v i)^2) = 1) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph ρ T) := by
  let L (i : Fin 4) := θ+plane u v i
  let R (i : Fin 4) := θ+(p+plane u v i)
  have hfixed (i : Fin 4) : ρ (plane u v i) = plane u v i := by
    fin_cases i <;> simp [plane, hu', hv']
  have hL : Function.Injective L := by
    intro i j h
    exact plane_injective hu hv huv (add_left_cancel h)
  have hR : Function.Injective R := by
    intro i j h
    exact plane_injective hu hv huv (add_left_cancel (add_left_cancel h))
  have hE : ∀ i j, (graph ρ T).Adj (L i) (R j) := by
    intro i j
    apply (graph_coset_adj ρ T θ (plane u v i) (p+plane u v j) hθ
      (hfixed i) (by simp [hp, hfixed])).mpr
    obtain ⟨k, hk⟩ := plane_closed u v i j
    rw [add_left_comm, hk]
    exact hS k
  have hdisjoint : ∀ i j, L i ≠ R j := by
    intro i j he
    have h := hE i j
    rw [he] at h
    exact (graph ρ T).loopless _ h
  intro hfree
  apply hfree
  refine ⟨⟨⟨Sum.elim L R, ?_⟩, ?_⟩⟩
  · intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => simp at hab
      | inr j => exact hE i j
    | inr i =>
      cases b with
      | inl j => exact (hE j i).symm
      | inr j => simp at hab
  · intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (hL hab)
      | inr j => exact False.elim (hdisjoint i j hab)
    | inr i =>
      cases b with
      | inl j => exact False.elim (hdisjoint j i hab.symm)
      | inr j => exact congrArg Sum.inr (hR hab)

end Erdos714QuarticTrace

#print axioms Erdos714QuarticTrace.coset_identity
#print axioms Erdos714QuarticTrace.not_free_of_coset_plane
