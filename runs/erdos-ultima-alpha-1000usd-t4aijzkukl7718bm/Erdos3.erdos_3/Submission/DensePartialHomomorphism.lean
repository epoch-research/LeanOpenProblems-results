import FormalConjecturesUtil

/-! Exact extension of a partially multiplicative map from a sufficiently dense
subset of a finite group. Both the source and target may be noncommutative. -/
namespace Erdos3DensePartialHomomorphism
open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 2000000

lemma exists_common_good {X : Type*} [Fintype X] (S : Finset X) (m : ℕ)
    (hm : m*(Fintype.card X-S.card) < Fintype.card X) (e : Fin m → X ≃ X) :
    ∃ x : X, ∀ i : Fin m, e i x ∈ S := by
  let B : Finset X := univ.biUnion (fun i : Fin m ↦ (univ \ S).image (e i).symm)
  have hB : B.card ≤ m*(Fintype.card X-S.card) := by
    calc
      _ ≤ ∑ i : Fin m, ((univ \ S).image (e i).symm).card := card_biUnion_le
      _ = _ := by simp only [card_image_of_injective _ (Equiv.injective _),
        card_sdiff_of_subset (subset_univ _),card_univ,sum_const,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  by_contra! hno
  have hsub : univ ⊆ B := by
    intro x _
    obtain ⟨i,hi⟩ := hno x
    apply mem_biUnion.mpr
    refine ⟨i,mem_univ _,mem_image.mpr ?_⟩
    exact ⟨e i x,mem_sdiff.mpr ⟨mem_univ _,hi⟩,(e i).symm_apply_apply x⟩
  have hc := card_le_card hsub
  rw [card_univ] at hc
  omega

lemma exists_four_good {X : Type*} [Fintype X] (S : Finset X)
    (hS : 4*(Fintype.card X-S.card) < Fintype.card X)
    (a b c d : X ≃ X) : ∃ x : X, a x ∈ S ∧ b x ∈ S ∧ c x ∈ S ∧ d x ∈ S := by
  obtain ⟨x,hx⟩ := exists_common_good S 4 hS ![a,b,c,d]
  exact ⟨x,by simpa using hx 0,by simpa using hx 1,by simpa using hx 2,by simpa using hx 3⟩

variable {G H : Type*} [Group G] [Fintype G] [Group H]

lemma dense_pair (S : Finset G) (hS : 4*(Fintype.card G-S.card) < Fintype.card G)
    (x : G) : ∃ t : G, t ∈ S ∧ x*t ∈ S := by
  obtain ⟨t,ht,hxt,_,_⟩ := exists_four_good S hS (Equiv.refl G) (Equiv.mulLeft x)
    (Equiv.refl G) (Equiv.refl G)
  exact ⟨t,ht,hxt⟩

/-- Ratios f(xb)/f(b) do not depend on which admissible pair is chosen. -/
lemma partial_ratio_independent (S : Finset G)
    (hS : 4*(Fintype.card G-S.card) < Fintype.card G) (f : G → H)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a*b ∈ S → f (a*b) = f a*f b)
    (x b d : G) (hb : b ∈ S) (hxb : x*b ∈ S) (hd : d ∈ S) (hxd : x*d ∈ S) :
    f (x*b)*(f b)⁻¹ = f (x*d)*(f d)⁻¹ := by
  obtain ⟨t,ht,hbt,hdt,hxt⟩ := exists_four_good S hS (Equiv.refl G)
    (Equiv.mulLeft b⁻¹) (Equiv.mulLeft d⁻¹) (Equiv.mulLeft x)
  change b⁻¹*t ∈ S at hbt
  change d⁻¹*t ∈ S at hdt
  change x*t ∈ S at hxt
  have h1 : f (x*t) = f (x*b)*f (b⁻¹*t) := by
    simpa only [mul_assoc, mul_inv_cancel_left] using
      hmul (x*b) hxb (b⁻¹*t) hbt (by simpa only [mul_assoc,mul_inv_cancel_left] using hxt)
  have h2 : f t = f b*f (b⁻¹*t) := by
    simpa only [mul_inv_cancel_left] using
      hmul b hb (b⁻¹*t) hbt (by simpa only [mul_inv_cancel_left] using ht)
  have h3 : f (x*t) = f (x*d)*f (d⁻¹*t) := by
    simpa only [mul_assoc, mul_inv_cancel_left] using
      hmul (x*d) hxd (d⁻¹*t) hdt (by simpa only [mul_assoc,mul_inv_cancel_left] using hxt)
  have h4 : f t = f d*f (d⁻¹*t) := by
    simpa only [mul_inv_cancel_left] using
      hmul d hd (d⁻¹*t) hdt (by simpa only [mul_inv_cancel_left] using ht)
  calc
    _ = f (x*t)*(f t)⁻¹ := by rw [h1,h2]; group
    _ = _ := by rw [h3,h4]; group

/-- Exact partial multiplicativity above density 3/4 extends uniquely to the
whole group. No topology or finiteness assumption on the target is used. -/
theorem dense_partial_homomorphism (S : Finset G)
    (hS : 4*(Fintype.card G-S.card) < Fintype.card G) (f : G → H)
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a*b ∈ S → f (a*b) = f a*f b) :
    ∃! φ : G →* H, ∀ a ∈ S, φ a = f a := by
  choose t ht hxt using dense_pair S hS
  let F : G → H := fun x ↦ f (x*t x)*(f (t x))⁻¹
  have hrep (x b : G) (hb : b ∈ S) (hxb : x*b ∈ S) :
      F x = f (x*b)*(f b)⁻¹ := partial_ratio_independent S hS f hmul x (t x) b
        (ht x) (hxt x) hb hxb
  have hFmul (x y : G) : F (x*y) = F x*F y := by
    obtain ⟨b,hb,hyb,hxyb,_⟩ := exists_four_good S hS (Equiv.refl G)
      (Equiv.mulLeft y) (Equiv.mulLeft (x*y)) (Equiv.refl G)
    change y*b ∈ S at hyb
    change (x*y)*b ∈ S at hxyb
    rw [hrep (x*y) b hb hxyb,hrep x (y*b) hyb (by simpa only [mul_assoc] using hxyb),
      hrep y b hb hyb]
    simp only [mul_assoc]
    group
  let φ : G →* H :=
    { toFun := F
      map_one' := by
        have hh : F 1*1 = F 1*F 1 := by simpa only [one_mul,mul_one] using hFmul 1 1
        exact (mul_left_cancel hh).symm
      map_mul' := hFmul }
  have hφ (a : G) (ha : a ∈ S) : φ a = f a := by
    change F a = f a
    rw [hrep a (t a) (ht a) (hxt a),hmul a ha (t a) (ht a) (hxt a)]
    group
  refine ⟨φ,hφ,?_⟩
  intro ψ hψ
  ext x
  obtain ⟨b,hb,hxb⟩ := dense_pair S hS x
  calc
    ψ x = ψ (x*b)*(ψ b)⁻¹ := by rw [map_mul]; group
    _ = f (x*b)*(f b)⁻¹ := by rw [hψ _ hxb,hψ _ hb]
    _ = φ x := (hrep x b hb hxb).symm

#print axioms dense_partial_homomorphism
end Erdos3DensePartialHomomorphism
