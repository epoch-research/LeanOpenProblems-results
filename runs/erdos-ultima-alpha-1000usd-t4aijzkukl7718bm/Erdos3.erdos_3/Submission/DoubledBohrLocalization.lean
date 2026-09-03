import Submission.LocalizedQuadraticCorrelation

/-! Localizing derivative directions into doubled Bohr sets preserves their
halves in the domain where the quadratic integration estimate is valid. -/
namespace Erdos3DoubledBohrLocalization
open Finset Erdos3FiniteBohr Erdos3BohrCovering Erdos3FreimanFrequencyGraph
  Erdos3LocalQuadraticIntegration
open scoped BigOperators Classical Pointwise
set_option maxHeartbeats 5000000

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

noncomputable def doubledBohr (C : Finset (AddChar G ℂ)) (r : ℝ) : Finset G :=
  (bohr C r).image (doubleHom (G := G))

lemma double_halfHom (h2 : Function.Bijective (fun x : G ↦ x+x)) (x : G) :
    halfHom h2 x+halfHom h2 x = x :=
  (AddEquiv.ofBijective (doubleHom (G := G)) h2).apply_symm_apply x

lemma mem_doubledBohr (h2 : Function.Bijective (fun x : G ↦ x+x))
    (C : Finset (AddChar G ℂ)) (r : ℝ) (x : G) :
    x ∈ doubledBohr C r ↔ halfHom h2 x ∈ bohr C r := by
  constructor
  · intro hx
    obtain ⟨y,hy,he⟩ := mem_image.mp hx
    have hh : halfHom h2 x = y := by rw [← he]; exact halfHom_double h2 y
    rwa [hh]
  · intro hx
    exact mem_image.mpr ⟨halfHom h2 x,hx,double_halfHom h2 x⟩

lemma doubledBohr_card (h2 : Function.Bijective (fun x : G ↦ x+x))
    (C : Finset (AddChar G ℂ)) (r : ℝ) : (doubledBohr C r).card = (bohr C r).card :=
  card_image_of_injective _ h2.injective

lemma doubledBohr_nonempty (C : Finset (AddChar G ℂ)) {r : ℝ} (hr : 0 ≤ r) :
    (doubledBohr C r).Nonempty := image_nonempty.mpr ⟨0,bohr_zero C hr⟩

lemma doubledBohr_add (C : Finset (AddChar G ℂ)) {r s : ℝ} {x y : G}
    (hx : x ∈ doubledBohr C r) (hy : y ∈ doubledBohr C s) :
    x+y ∈ doubledBohr C (r+s) := by
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
  exact mem_image.mpr ⟨a+b,bohr_add ha hb,(doubleHom (G := G)).map_add a b⟩

lemma doubledBohr_sub (C : Finset (AddChar G ℂ)) {r s : ℝ} {x y : G}
    (hx : x ∈ doubledBohr C r) (hy : y ∈ doubledBohr C s) :
    x-y ∈ doubledBohr C (r+s) := by
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hy
  exact mem_image.mpr ⟨a-b,by simpa only [sub_eq_add_neg] using bohr_add ha (bohr_neg hb),
    (doubleHom (G := G)).map_sub a b⟩

lemma doubledBohr_subset (C : Finset (AddChar G ℂ)) (r : ℝ) :
    doubledBohr C r ⊆ bohr C (2*r) := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
  change y+y ∈ _
  simpa only [two_mul] using bohr_add hy hy

/-- Recenter a large subset of T so that its directions have small halves.
The new fixed center is retained explicitly. -/
theorem exists_doubled_bohr_restriction (h2 : Function.Bijective (fun x : G ↦ x+x))
    (C : Finset (AddChar G ℂ)) (T : Finset G) (hT : T.Nonempty) :
    ∃ H : Finset G, ∃ t₀ : G,
      0 ∈ H ∧ H ⊆ doubledBohr C (1/16) ∧
      T.card ≤ 129^(2*C.card)*H.card ∧ t₀ ∈ T ∧ ∀ h ∈ H, h+t₀ ∈ T := by
  let U := doubledBohr C (1/32)
  have hU : U.Nonempty := doubledBohr_nonempty C (by norm_num)
  have hcount : Fintype.card G ≤ 129^(2*C.card)*U.card := by
    rw [doubledBohr_card h2]
    simpa only [show 2*64+1 = 129 by decide,show (2 : ℝ)/(64 : ℕ) = 1/32 by norm_num] using
      card_bohr_lower C (q := 64) (by decide)
  obtain ⟨a,ha⟩ := exists_large_translate_fiber T id U hU hcount
  let T' := T.filter (fun t ↦ t-a ∈ U)
  have hT' : T'.Nonempty := by
    apply card_pos.mp
    change T.card ≤ 129^(2*C.card)*T'.card at ha
    have hp := hT.card_pos
    by_contra h
    have hz : T'.card = 0 := by omega
    rw [hz,mul_zero] at ha
    omega
  obtain ⟨t₀,ht₀⟩ := hT'
  let H := T'.image (fun t ↦ t-t₀)
  have hHcard : H.card = T'.card := card_image_of_injective _ (fun _ _ hh ↦ sub_left_injective hh)
  refine ⟨H,t₀,mem_image.mpr ⟨t₀,ht₀,sub_self _⟩,?_,?_,(mem_filter.mp ht₀).1,?_⟩
  · intro h hh
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hh
    have hp := doubledBohr_sub C (mem_filter.mp ht).2 (mem_filter.mp ht₀).2
    simpa only [show (1/32 : ℝ)+1/32 = 1/16 by norm_num,
      show (t-a)-(t₀-a) = t-t₀ by abel] using hp
  · rw [hHcard]
    exact ha
  · intro h hh
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hh
    simpa only [sub_add_cancel] using (mem_filter.mp ht).1

lemma doubled_small_card (h2 : Function.Bijective (fun x : G ↦ x+x))
    (C : Finset (AddChar G ℂ)) :
    Fintype.card G ≤ 65^(2*C.card)*(doubledBohr C (1/16)).card := by
  rw [doubledBohr_card h2]
  simpa only [show 2*32+1 = 65 by decide,show (2 : ℝ)/(32 : ℕ) = 1/16 by norm_num] using
    card_bohr_lower C (q := 32) (by decide)

#print axioms exists_doubled_bohr_restriction
end Erdos3DoubledBohrLocalization
