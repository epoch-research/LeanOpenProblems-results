import FormalConjecturesUtil

/-!
A two-error (Hamming) bound for short linearly independent point families.
This constrains a proposed low-rank construction, not arbitrary K44-free graphs.
It does not settle Erdős Problem 714.
-/
noncomputable section
open Finset Classical
set_option maxHeartbeats 2000000
namespace Erdos714ShortIndependence
variable {F V I A B : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Independence of every subfamily with at most k indices. -/
def ShortIndependent (f : I → V) (k : ℕ) : Prop :=
  ∀ S : Finset I, S.card ≤ k → LinearIndependent F (fun i : S => f i)

lemma ShortIndependent.comp {f : I → V} {k : ℕ} (h : ShortIndependent (F := F) f k)
    (e : A ↪ I) : ShortIndependent (F := F) (f ∘ e) k := by
  intro S hS
  let T := S.image e
  have hT : T.card ≤ k := (card_image_le).trans hS
  let j : S → T := fun x => ⟨e x, mem_image.mpr ⟨x,x.property,rfl⟩⟩
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val he)
  exact (h T hT).comp j hj

/-- A supported coefficient vector is detected by the corresponding independent subfamily. -/
lemma coefficient_zero {f : I → V} {k : ℕ} (h : ShortIndependent (F := F) f k)
    (c : I →₀ F) (hc : c.support.card ≤ k) (hz : Finsupp.linearCombination F f c = 0) : c = 0 := by
  have hs : ∑ i : c.support, c i • f i = 0 := by
    rw [Finset.sum_coe_sort c.support (fun i => c i • f i)]
    exact hz
  have hh := Fintype.linearIndependent_iff.mp (h c.support hc) (fun i : c.support => c i) hs
  ext i
  by_cases hi : i ∈ c.support
  · exact hh ⟨i,hi⟩
  · exact Finsupp.notMem_support_iff.mp hi

/-- Four-point independence makes linear combinations of at most two points unique. -/
lemma sparse_injective {f : I → V} (h : ShortIndependent (F := F) f 4)
    (c d : I →₀ F) (hc : c.support.card ≤ 2) (hd : d.support.card ≤ 2)
    (he : Finsupp.linearCombination F f c = Finsupp.linearCombination F f d) : c = d := by
  apply sub_eq_zero.mp
  apply coefficient_zero h (c-d)
  · have hs := card_le_card (Finsupp.support_sub (f := c) (g := d))
    have hu := card_union_le c.support d.support
    omega
  · rw [map_sub,he,sub_self]

/-- Coefficients supported at one index in each of two disjoint classes. -/
def pairCoefficients (x : (A × B) × Fˣ × Fˣ) : (A ⊕ B) →₀ F :=
  Finsupp.single (.inl x.1.1) (x.2.1 : F) + Finsupp.single (.inr x.1.2) (x.2.2 : F)

lemma pair_support (x : (A × B) × Fˣ × Fˣ) : (pairCoefficients x).support.card ≤ 2 := by
  have hs := card_le_card (Finsupp.support_add (g₁ := Finsupp.single (Sum.inl x.1.1 : A ⊕ B) (x.2.1 : F))
    (g₂ := Finsupp.single (Sum.inr x.1.2 : A ⊕ B) (x.2.2 : F)))
  rw [Finsupp.support_single_ne_zero _ x.2.1.ne_zero,
    Finsupp.support_single_ne_zero _ x.2.2.ne_zero] at hs
  simpa [pairCoefficients] using hs

lemma pair_injective : Function.Injective (pairCoefficients (A := A) (B := B) (F := F)) := by
  rintro ⟨⟨a,b⟩,u,v⟩ ⟨⟨c,d⟩,w,z⟩ h
  have ha : a = c := by
    by_contra hac
    have hh := congrArg (fun t : (A ⊕ B) →₀ F => t (.inl a)) h
    simp [pairCoefficients,Ne.symm hac] at hh
  have hb : b = d := by
    by_contra hbd
    have hh := congrArg (fun t : (A ⊕ B) →₀ F => t (.inr b)) h
    simp [pairCoefficients,Ne.symm hbd] at hh
  subst c
  subst d
  have hu : u = w := by
    apply Units.ext
    have hh := congrArg (fun t : (A ⊕ B) →₀ F => t (.inl a)) h
    simpa [pairCoefficients,Finsupp.single_apply] using hh
  have hv : v = z := by
    apply Units.ext
    have hh := congrArg (fun t : (A ⊕ B) →₀ F => t (.inr b)) h
    simpa [pairCoefficients,Finsupp.single_apply] using hh
  subst w
  subst z
  rfl

/-- The two-term coefficient space must fit injectively in the ambient vector space. -/
theorem split_card_bound [Fintype F] [Fintype V] [Fintype A] [Fintype B]
    (f : A ⊕ B → V) (h : ShortIndependent (F := F) f 4) :
    Fintype.card A * Fintype.card B * (Fintype.card F-1)^2 ≤ Fintype.card V := by
  let g : (A × B) × Fˣ × Fˣ → V := fun x => Finsupp.linearCombination F f (pairCoefficients x)
  have hg : Function.Injective g := by
    intro x y he
    exact pair_injective (sparse_injective h _ _ (pair_support x) (pair_support y) he)
  have hc := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_prod,Fintype.card_units, pow_two] using hc

/-- In particular, six coordinates cannot support q^3 such point vectors for q>=4. -/
theorem not_shortIndependent_six [Fintype F] (hq : 4 ≤ Fintype.card F)
    (f : Fin (Fintype.card F^3) → Fin 6 → F) :
    ¬ ShortIndependent (F := F) f 4 := by
  let q := Fintype.card F
  let m := q^2+q+2
  have hq4 : 4 ≤ q := hq
  have hq2 : 4*q ≤ q^2 := by nlinarith
  have hq3 : 4*q^2 ≤ q^3 := by nlinarith [Nat.mul_le_mul_right (q^2) hq4]
  have hm : 2*m ≤ q^3 := by dsimp [m]; nlinarith
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin m ⊕ Fin m) (β := Fin (q^3)) (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)
  intro h
  have hb := split_card_bound (f ∘ e) (h.comp e)
  simp only [Fintype.card_fin,Fintype.card_fun] at hb
  change m*m*(q-1)^2 ≤ q^6 at hb
  have hqsub : q-1+1 = q := Nat.sub_add_cancel (by omega)
  have hp : m*(q-1)+2 = q^3+q := by
    have he := congrArg (fun x : ℕ => (q^2+q+2)*x) hqsub
    dsimp [m]
    nlinarith [he]
  have hlt : q^3 < m*(q-1) := by omega
  have hs : (q^3)^2 < (m*(q-1))^2 := by nlinarith
  nlinarith


/-- Even seven linear coordinates are insufficient once q>=16. -/
theorem not_shortIndependent_card [Fintype F] [Fintype V]
    (hq : 16 ≤ Fintype.card F) (hV : Fintype.card V ≤ Fintype.card F^7)
    (f : Fin (Fintype.card F^3) → V) : ¬ ShortIndependent (F := F) f 4 := by
  let q := Fintype.card F
  let m := q^3/2
  have hq16 : 16 ≤ q := hq
  have hqpos : 0 < q := by omega
  have hq3 : 2 ≤ q^3 := by nlinarith [Nat.mul_le_mul_right (q^2) hq16]
  have hmpos : 0 < m := Nat.div_pos hq3 (by decide)
  have hml : 2*m ≤ q^3 := Nat.mul_div_le _ _
  have hmh : q^3 < 2*(m+1) := Nat.lt_mul_div_succ _ (by decide)
  have hmass : q^3 ≤ 3*m := by omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin m ⊕ Fin m) (β := Fin (q^3)) (by simp only [Fintype.card_sum,Fintype.card_fin]; omega)
  intro h
  have hb := (split_card_bound (f ∘ e) (h.comp e)).trans hV
  simp only [Fintype.card_fin] at hb
  change m*m*(q-1)^2 ≤ q^7 at hb
  have hqsub : q-1+1 = q := Nat.sub_add_cancel (by omega)
  have hqminus : 15 ≤ q-1 := by omega
  have hfac : 9*q < (q-1)^2 := by
    have hmul := Nat.mul_le_mul_right (q-1) hqminus
    nlinarith
  have hsq : (q^3)^2 ≤ (3*m)^2 := by nlinarith
  have hlt : q^7 < m*m*(q-1)^2 := by
    calc
      q^7 = q*(q^3)^2 := by ring
      _ ≤ q*(3*m)^2 := Nat.mul_le_mul_left _ hsq
      _ = m^2*(9*q) := by ring
      _ < m^2*(q-1)^2 := Nat.mul_lt_mul_of_pos_left hfac (pow_pos hmpos _)
      _ = _ := by ring
  omega

/-- Homogeneous coordinates turn affine independence into linear independence. -/
lemma homogeneous_independent [Fintype I] (f : I → V) (h : AffineIndependent F f) :
    LinearIndependent F (fun i => ((1 : F), f i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hs : ∑ i, c i = 0 := by
    simpa only [map_sum,map_zero,map_smul,LinearMap.fst_apply,smul_eq_mul,mul_one] using congrArg (LinearMap.fst F F V) hc
  have hv : ∑ i, c i • f i = 0 := by
    simpa only [map_sum,map_zero,map_smul,LinearMap.snd_apply] using congrArg (LinearMap.snd F F V) hc
  apply (affineIndependent_iff_of_fintype F f).mp h c hs
  rw [Finset.univ.weightedVSub_eq_linear_combination hs]
  exact hv

/-- Four-point affine independence on q^3 points cannot be maintained in six affine coordinates. -/
theorem not_shortAffine_six [Fintype F] (hq : 16 ≤ Fintype.card F)
    (f : Fin (Fintype.card F^3) → Fin 6 → F) :
    ¬ (∀ S : Finset (Fin (Fintype.card F^3)), S.card ≤ 4 →
      AffineIndependent F (fun i : S => f i)) := by
  intro h
  apply not_shortIndependent_card (V := F × (Fin 6 → F)) hq
    (by simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]; exact le_of_eq (by ring)) (fun i => ((1 : F), f i))
  intro S hS
  exact homogeneous_independent _ (h S hS)


/-- With enough indices, independence of exactly k distinct vectors includes all shorter cases. -/
lemma shortIndependent_of_exact [Fintype I] {f : I → V} {k : ℕ}
    (hk : k ≤ Fintype.card I)
    (h : ∀ e : Fin k ↪ I, LinearIndependent F (fun i => f (e i))) :
    ShortIndependent (F := F) f k := by
  intro S hS
  obtain ⟨T,hST,_,hT⟩ := exists_subsuperset_card_eq (subset_univ S) hS
    (by simpa only [card_univ] using hk)
  let e : Fin k ≃ T := Fintype.equivOfCardEq (by simp [hT])
  let j : Fin k ↪ I := ⟨fun i => e i,fun i j he => e.injective (Subtype.ext he)⟩
  let g : S → Fin k := fun i => e.symm ⟨i,hST i.property⟩
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    have he := congrArg (fun z : Fin k => (e z).val) hxy
    simpa [g] using he
  convert (h j).comp g hg using 1
  funext i
  simp [j,g]

/-- An explicit four-index dependence exists; the result is not confined to shorter subfamilies. -/
theorem exists_dependent_four_six [Fintype F] (hq : 4 ≤ Fintype.card F)
    (f : Fin (Fintype.card F^3) → Fin 6 → F) :
    ∃ e : Fin 4 ↪ Fin (Fintype.card F^3), ¬ LinearIndependent F (fun i => f (e i)) := by
  by_contra! h
  apply not_shortIndependent_six hq f
  apply shortIndependent_of_exact ?_ h
  simp only [Fintype.card_fin]
  have hq3 : Fintype.card F ≤ Fintype.card F^3 := by
    simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ Fintype.card F) (by decide : 1 ≤ 3)
  omega

/-- Six affine coordinates likewise force an affinely dependent four-tuple. -/
theorem exists_affine_dependent_four_six [Fintype F] (hq : 16 ≤ Fintype.card F)
    (f : Fin (Fintype.card F^3) → Fin 6 → F) :
    ∃ e : Fin 4 ↪ Fin (Fintype.card F^3), ¬ AffineIndependent F (fun i => f (e i)) := by
  by_contra! h
  apply not_shortIndependent_card (V := F × (Fin 6 → F)) hq
    (by simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]; exact le_of_eq (by ring))
    (fun i => ((1 : F),f i))
  apply shortIndependent_of_exact ?_ (fun e => homogeneous_independent _ (h e))
  simp only [Fintype.card_fin]
  have hq3 : Fintype.card F ≤ Fintype.card F^3 := by
    simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ Fintype.card F) (by decide : 1 ≤ 3)
  omega

#print axioms shortIndependent_of_exact
#print axioms exists_dependent_four_six
#print axioms exists_affine_dependent_four_six

#print axioms not_shortIndependent_card
#print axioms homogeneous_independent
#print axioms not_shortAffine_six

#print axioms coefficient_zero
#print axioms sparse_injective
#print axioms split_card_bound
#print axioms not_shortIndependent_six
end Erdos714ShortIndependence
