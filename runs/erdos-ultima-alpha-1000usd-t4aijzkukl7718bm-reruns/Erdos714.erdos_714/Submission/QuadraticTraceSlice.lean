import FormalConjecturesUtil

/-!
A quadratic-fixed-ring slice criterion for polarized trace graphs. This is
an obstruction criterion for candidate constructions, not a proof or
disproof of Erdős 714. No bound on the number of profile solutions is assumed
without being stated explicitly.
-/

open SimpleGraph

namespace Erdos714QuadraticTraceSlice

variable {E : Type*} [CommRing E]

def trace2 (τ : E →+* E) (z : E) : E := z + τ z

def halfTrace (τ : E →+* E) (z : E) : E := z + τ (τ z)

def trace4 (τ : E →+* E) (z : E) : E := trace2 τ (halfTrace τ z)

lemma trace4_expand (τ : E →+* E) (z : E) :
    trace4 τ z = z + τ z + τ (τ z) + τ (τ (τ z)) := by
  simp only [trace4, trace2, halfTrace, map_add]
  ring

lemma trace2_add (τ : E →+* E) (x y : E) :
    trace2 τ (x+y) = trace2 τ x + trace2 τ y := by
  simp only [trace2, map_add]
  ring

lemma halfTrace_fixed (τ : E →+* E) (y : E) (hy : τ (τ (τ (τ y))) = y) :
    τ (τ (halfTrace τ y)) = halfTrace τ y := by
  simp only [halfTrace, map_add, hy]
  ring

/-- The polarized expression reduces from four trace terms to two when its
row coordinates are fixed by the square of the endomorphism. -/
theorem row_reduction (τ : E →+* E) (f : E → E) (x y : E)
    (hx : τ (τ x) = x) (hfx : τ (τ (f x)) = f x) :
    trace4 τ (f x*y+x*f y) =
      trace2 τ (f x*halfTrace τ y+x*halfTrace τ (f y)) := by
  unfold trace4
  congr 1
  simp only [halfTrace, map_add, map_mul, hx, hfx]
  ring

/-- Cancellation is valid without characteristic-two or field hypotheses. -/
lemma trace2_cross_cancel (τ : E →+* E) (x u : E)
    (hx : τ (τ x) = x) (hu : τ (τ u) = u) :
    trace2 τ (x*τ u-τ x*u) = 0 := by
  simp only [trace2, map_sub, map_mul, hx, hu]
  ring

/-- Row and column profiles force the original trace incidence. -/
theorem profile_identity (τ : E →+* E) (f : E → E) (A B C x y : E)
    (hx : τ (τ x) = x) (hfx : τ (τ (f x)) = f x)
    (hB : τ (τ B) = B) (hy : τ (τ (τ (τ y))) = y)
    (hrow : f x+A*x+B*τ x=C)
    (hcol : halfTrace τ (f y) = A*halfTrace τ y+τ (B*halfTrace τ y)) :
    trace4 τ (f x*y+x*f y) = trace2 τ (C*halfTrace τ y) := by
  rw [row_reduction τ f x y hx hfx]
  have ht := halfTrace_fixed τ y hy
  have hu : τ (τ (B*halfTrace τ y)) = B*halfTrace τ y := by
    simp only [map_mul, hB, ht]
  have he : f x*halfTrace τ y+x*halfTrace τ (f y) =
      C*halfTrace τ y+(x*τ (B*halfTrace τ y)-τ x*(B*halfTrace τ y)) := by
    rw [hcol]
    linear_combination halfTrace τ y * hrow
  rw [he, trace2_add, trace2_cross_cancel τ x _ hx hu, add_zero]

/-- Two distinct parts are used, so no looplessness assumption on the kernel
is needed and cross-part vertex collisions cannot be hidden. -/
def graph (τ : E →+* E) (f : E → E) : SimpleGraph (E ⊕ E) where
  Adj
    | .inl x, .inr y => trace4 τ (f x*y+x*f y) = 1
    | .inr y, .inl x => trace4 τ (f x*y+x*f y) = 1
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp
  loopless := by intro u; cases u <;> simp

/-- Actual copies from injective profiles; all degeneracy and counting
requirements remain visible as hypotheses. -/
def profileCopy (τ : E →+* E) (f : E → E) (A B C : E)
    {r s : ℕ} (rows : Fin r ↪ E) (cols : Fin s ↪ E)
    (hx : ∀ i, τ (τ (rows i)) = rows i)
    (hfx : ∀ i, τ (τ (f (rows i))) = f (rows i))
    (hB : τ (τ B) = B)
    (hy : ∀ j, τ (τ (τ (τ (cols j)))) = cols j)
    (hrow : ∀ i, f (rows i)+A*rows i+B*τ (rows i)=C)
    (hcol : ∀ j, halfTrace τ (f (cols j)) =
      A*halfTrace τ (cols j)+τ (B*halfTrace τ (cols j)))
    (htarget : ∀ j, trace2 τ (C*halfTrace τ (cols j)) = 1) :
    (completeBipartiteGraph (Fin r) (Fin s)).Copy (graph τ f) where
  toHom :=
    { toFun := Sum.map rows cols
      map_rel' := by
        intro u v huv
        have h (i : Fin r) (j : Fin s) :
            trace4 τ (f (rows i)*cols j+rows i*f (cols j)) = 1 := by
          rw [profile_identity τ f A B C (rows i) (cols j)
            (hx i) (hfx i) hB (hy j) (hrow i) (hcol j)]
          exact htarget j
        cases u with
        | inl i =>
          cases v with
          | inl j => simp at huv
          | inr j => exact h i j
        | inr j =>
          cases v with
          | inl i => exact h i j
          | inr i => simp at huv }
  injective' := Sum.map_injective.mpr ⟨rows.injective, cols.injective⟩

theorem not_free_of_profiles (τ : E →+* E) (f : E → E) (A B C : E)
    {r : ℕ} (rows cols : Fin r ↪ E)
    (hx : ∀ i, τ (τ (rows i)) = rows i)
    (hfx : ∀ i, τ (τ (f (rows i))) = f (rows i))
    (hB : τ (τ B) = B)
    (hy : ∀ j, τ (τ (τ (τ (cols j)))) = cols j)
    (hrow : ∀ i, f (rows i)+A*rows i+B*τ (rows i)=C)
    (hcol : ∀ j, halfTrace τ (f (cols j)) =
      A*halfTrace τ (cols j)+τ (B*halfTrace τ (cols j)))
    (htarget : ∀ j, trace2 τ (C*halfTrace τ (cols j)) = 1) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (graph τ f) := by
  intro h
  exact h ⟨profileCopy τ f A B C rows cols hx hfx hB hy hrow hcol htarget⟩

/-- For a monomial the fixed-row hypothesis on f follows automatically. -/
theorem monomial_not_free (τ : E →+* E) (d : ℕ) (A B C : E)
    {r : ℕ} (rows cols : Fin r ↪ E)
    (hx : ∀ i, τ (τ (rows i)) = rows i)
    (hB : τ (τ B) = B)
    (hy : ∀ j, τ (τ (τ (τ (cols j)))) = cols j)
    (hrow : ∀ i, (rows i)^d+A*rows i+B*τ (rows i)=C)
    (hcol : ∀ j, halfTrace τ ((cols j)^d) =
      A*halfTrace τ (cols j)+τ (B*halfTrace τ (cols j)))
    (htarget : ∀ j, trace2 τ (C*halfTrace τ (cols j)) = 1) :
    ¬ (completeBipartiteGraph (Fin r) (Fin r)).Free (graph τ (·^d)) := by
  apply not_free_of_profiles τ (·^d) A B C rows cols hx _ hB hy hrow hcol htarget
  intro i
  simp only [map_pow, hx i]

end Erdos714QuadraticTraceSlice

#print axioms Erdos714QuadraticTraceSlice.row_reduction
#print axioms Erdos714QuadraticTraceSlice.profile_identity
#print axioms Erdos714QuadraticTraceSlice.profileCopy
#print axioms Erdos714QuadraticTraceSlice.not_free_of_profiles
#print axioms Erdos714QuadraticTraceSlice.monomial_not_free

namespace Erdos714MonomialScaling

open Erdos714QuadraticTraceSlice

variable {F : Type*} [Field F]

/-- A nonzero coefficient can be removed whenever it is a (d*d-1)-st power. -/
theorem kernel_scale (d : ℕ) (hd : 0 < d) (u c x y : F) (hu : u ≠ 0)
    (hc : c = u^(d*d-1)) :
    (u*x)^d*((u^d)⁻¹*y)+c*(u*x)*(((u^d)⁻¹*y)^d) = x^d*y+x*y^d := by
  have hpow : c*u = (u^d)^d := by
    rw [hc, ← pow_succ, Nat.sub_add_cancel (Nat.mul_pos hd hd), pow_mul]
  calc
    (u*x)^d*((u^d)⁻¹*y)+c*(u*x)*(((u^d)⁻¹*y)^d) =
        (u^d*(u^d)⁻¹)*x^d*y+((c*u)*((u^d)⁻¹)^d)*x*y^d := by
      simp only [mul_pow]
      ring
    _ = x^d*y+x*y^d := by
      have hi : u^d*(u^d)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hu)
      have hi' : (u^d)^d*((u^d)⁻¹)^d = 1 := by rw [← mul_pow, hi, one_pow]
      rw [hpow, hi, hi']
      simp

def graph (τ : F →+* F) (d : ℕ) (c : F) : SimpleGraph (F ⊕ F) where
  Adj
    | .inl x, .inr y => trace4 τ (x^d*y+c*x*y^d) = 1
    | .inr y, .inl x => trace4 τ (x^d*y+c*x*y^d) = 1
    | _, _ => False
  symm := by intro u v; cases u <;> cases v <;> simp
  loopless := by intro u; cases u <;> simp

/-- Actual graph isomorphism, not just equality of degree counts. -/
def scalingIso (τ : F →+* F) (d : ℕ) (hd : 0 < d) (u c : F)
    (hu : u ≠ 0) (hc : c = u^(d*d-1)) : graph τ d 1 ≃g graph τ d c where
  toEquiv := Equiv.sumCongr (Equiv.mulLeft₀ u hu)
    (Equiv.mulLeft₀ ((u^d)⁻¹) (inv_ne_zero (pow_ne_zero _ hu)))
  map_rel_iff' := by
    intro a b
    cases a with
    | inl x =>
      cases b with
      | inl y => rfl
      | inr y =>
        change trace4 τ ((u*x)^d*((u^d)⁻¹*y)+c*(u*x)*(((u^d)⁻¹*y)^d)) = 1 ↔
          trace4 τ (x^d*y+1*x*y^d) = 1
        rw [kernel_scale d hd u c x y hu hc, one_mul]
    | inr y =>
      cases b with
      | inl x =>
        change trace4 τ ((u*x)^d*((u^d)⁻¹*y)+c*(u*x)*(((u^d)⁻¹*y)^d)) = 1 ↔
          trace4 τ (x^d*y+1*x*y^d) = 1
        rw [kernel_scale d hd u c x y hu hc, one_mul]
      | inr x => rfl

/-- The coprime power-map condition makes every nonzero coefficient equivalent. -/
theorem exists_scalingIso [Fintype F] (τ : F →+* F) (d : ℕ) (hd : 0 < d)
    (hcop : (Fintype.card F-1).Coprime (d*d-1)) (c : F) (hc : c ≠ 0) :
    Nonempty (graph τ d 1 ≃g graph τ d c) := by
  classical
  have hcop' : (Nat.card Fˣ).Coprime (d*d-1) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using hcop
  obtain ⟨u, hu⟩ := (powCoprime hcop').surjective (Units.mk0 c hc)
  have hp : (u : F)^(d*d-1) = c := by
    have h := congrArg Units.val hu
    exact h
  exact ⟨scalingIso τ d hd u c (Units.ne_zero u) hp.symm⟩

/-- In both checked degree-57 fields there is only one nonzero coefficient class. -/
theorem degree57_scaling [Fintype F] (τ : F →+* F)
    (hcard : Fintype.card F = 2^16 ∨ Fintype.card F = 2^20)
    (c : F) (hc : c ≠ 0) : Nonempty (graph τ 57 1 ≃g graph τ 57 c) := by
  apply exists_scalingIso τ 57 (by decide) _ c hc
  rcases hcard with hcard | hcard <;> rw [hcard] <;> decide

end Erdos714MonomialScaling

#print axioms Erdos714MonomialScaling.kernel_scale
#print axioms Erdos714MonomialScaling.exists_scalingIso
#print axioms Erdos714MonomialScaling.degree57_scaling
