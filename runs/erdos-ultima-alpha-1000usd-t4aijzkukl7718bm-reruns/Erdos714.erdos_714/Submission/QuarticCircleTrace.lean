import FormalConjecturesUtil

/-! A quartic-circle point outside any ternary additive kernel. -/
noncomputable section
open Classical Finset
set_option maxHeartbeats 3000000
namespace Erdos714QuarticCircleTrace

lemma exponent_coprime (k : ℕ) : (4*k+2).Coprime (2*k+3) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  generalize hd : Nat.gcd (4*k+2) (2*k+3)=d
  have h₁ : d∣4*k+2 := hd ▸ Nat.gcd_dvd_left _ _
  have h₂ : d∣2*k+3 := hd ▸ Nat.gcd_dvd_right _ _
  have h₄ : d∣4 := by
    have h := Nat.dvd_sub (dvd_mul_of_dvd_right h₂ 2) h₁
    have he : 2*(2*k+3)-(4*k+2)=4 := by omega
    rwa [he] at h
  have hd4 : d≤4 := Nat.le_of_dvd (by decide) h₄
  interval_cases d <;> omega

variable {F : Type*} [Field F] [Fintype F]

/-- In a field of order 3 mod 4, a permutation turns fourth powers into squares. -/
lemma exists_square_permutation (hmod : Fintype.card F%4=3) :
    ∃ e : F ≃ F, ∀ x, (e x)^2=x^4 := by
  let k := Fintype.card F/4
  have hcard : Fintype.card F=4*k+3 := by dsimp [k]; omega
  let n := 2*k+3
  have hcop : (Nat.card Fˣ).Coprime n := by
    simpa [Nat.card_eq_fintype_card,Fintype.card_units,hcard,n] using exponent_coprime k
  have hs : Function.Surjective (fun x : F => x^n) := by
    intro x
    by_cases hx : x=0
    · exact ⟨0,by simp [hx,n]⟩
    · obtain ⟨y,hy⟩ := hcop.pow_left_bijective.surjective (Units.mk0 x hx)
      exact ⟨y,by simpa using congrArg Units.val hy⟩
  let e : F ≃ F := Equiv.ofBijective (fun x => x^n)
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨hs,rfl⟩)
  refine ⟨e,?_⟩
  intro x
  change (x^n)^2=x^4
  by_cases hx : x=0
  · simp [hx,n]
  · have hp := FiniteField.pow_card_sub_one_eq_one x hx
    rw [hcard] at hp
    have he : n*2=(4*k+3-1)+4 := by dsimp [n]; omega
    rw [← pow_mul,he,pow_add,hp,one_mul]

variable (hns : ¬ IsSquare (-1 : F))

omit [Fintype F] in
include hns in
lemma denominator (t : F) : 1+t^2≠0 := by
  intro h
  apply hns
  refine ⟨t,?_⟩
  linear_combination -h

def circle (t : F) : F × F := ((1-t^2)/(1+t^2),2*t/(1+t^2))

omit [Fintype F] in
include hns in
lemma circle_eq (t : F) : (circle t).1^2+(circle t).2^2=1 := by
  dsimp [circle]
  field_simp [denominator hns t]
  ring

omit [Fintype F] in
include hns in
lemma circle_injective (h2 : (2:F)≠0) : Function.Injective (circle : F → F × F) := by
  have h₁ (t : F) : 1+(circle t).1≠0 := by
    dsimp [circle]
    field_simp [denominator hns t]
    ring_nf
    exact h2
  have h₂ (t : F) : (1+(circle t).1)*t=(circle t).2 := by
    dsimp [circle]
    field_simp [denominator hns t]
    ring
  intro x y h
  have ha := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  have hx := h₂ x
  rw [ha,hb,← h₂ y] at hx
  exact mul_left_cancel₀ (h₁ y) hx

lemma square_fiber_le_two (z : F) : (univ.filter (fun x : F => x^2=z)).card≤2 := by
  by_cases h : ∃ a : F, a^2=z
  · obtain ⟨a,ha⟩ := h
    have hs : univ.filter (fun x : F => x^2=z) ⊆ {a,-a} := by
      intro x hx
      have hh := (mem_filter.mp hx).2
      rw [← ha,sq_eq_sq_iff_eq_or_eq_neg] at hh
      simpa using hh
    exact (card_le_card hs).trans (by simpa using card_insert_le a ({-a} : Finset F))
  · have he : univ.filter (fun x : F => x^2=z)=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ⟨x,(mem_filter.mp hx).2⟩
    simp [he]

/-- At least #F points on the quartic circle; one omitted conic point is harmless. -/
lemma quartic_circle_large (hmod : Fintype.card F%4=3) (h2 : (2:F)≠0) :
    Fintype.card F≤(univ.filter (fun p : F × F => p.1^4+p.2^4=1)).card := by
  obtain ⟨e,he⟩ := exists_square_permutation hmod
  have hns : ¬IsSquare (-1:F) := by rw [FiniteField.isSquare_neg_one_iff,hmod]; simp
  let f : F → F × F := fun t => (e.symm (circle t).1,e.symm (circle t).2)
  have hf (t : F) : (f t).1^4+(f t).2^4=1 := by
    dsimp [f]
    rw [← he,← he,e.apply_symm_apply,e.apply_symm_apply]
    exact circle_eq hns t
  have hi : Function.Injective f := by
    intro x y h
    apply circle_injective hns h2
    apply Prod.ext
    · exact e.symm.injective (congrArg Prod.fst h)
    · exact e.symm.injective (congrArg Prod.snd h)
  let g : F → ↥(univ.filter (fun p : F × F => p.1^4+p.2^4=1)) :=
    fun t => ⟨f t,by simp only [mem_filter,mem_univ,true_and]; exact hf t⟩
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g
    (fun x y h => hi (congrArg Subtype.val h))

lemma quartic_fiber_le_two (hmod : Fintype.card F%4=3) (z : F) :
    (univ.filter (fun x : F => x^4=z)).card≤2 := by
  obtain ⟨e,he⟩ := exists_square_permutation hmod
  have h := card_le_card_of_injOn e
    (s := univ.filter (fun x : F => x^4=z)) (t := univ.filter (fun x : F => x^2=z))
    (by intro x hx; simpa [he] using hx)
    (by intro x hx y hy hxy; exact e.injective hxy)
  exact h.trans (square_fiber_le_two z)

lemma ternary_kernel_card (T : F →+ ZMod 3) (hsur : Function.Surjective T) :
    3*(univ.filter (fun x : F => T x=0)).card=Fintype.card F := by
  have hc (t : ZMod 3) : Fintype.card {x : F // T x=t}=Fintype.card {x : F // T x=0} :=
    Fintype.card_congr (AddMonoidHom.fiberEquivOfSurjective hsur t 0)
  have h := Fintype.sum_fiberwise T (fun _ => (1 : ℕ))
  simp only [sum_const,card_univ,nsmul_eq_mul,mul_one] at h
  simp_rw [hc] at h
  simpa only [sum_const,card_univ,ZMod.card,nsmul_eq_mul,Fintype.card_subtype] using h

/-- No surjective ternary additive map vanishes on all first coordinates
of this quartic circle. The proof is finite counting, not a character-sum estimate. -/
theorem exists_quartic_trace_one (hmod : Fintype.card F%4=3) (h2 : (2:F)≠0)
    (T : F →+ ZMod 3) (hsur : Function.Surjective T) :
    ∃ a b : F, a^4+b^4=1 ∧ T a=1 := by
  have hex : ∃ a b : F, a^4+b^4=1 ∧ T a≠0 := by
    by_contra! hbad
    let P := univ.filter (fun p : F × F => p.1^4+p.2^4=1)
    let K := univ.filter (fun a : F => T a=0)
    have hbound : P.card≤2*K.card := by
      refine card_le_mul_card_image_of_maps_to (f := Prod.fst) (s := P) (t := K) ?_ 2 ?_
      · intro p hp
        simp only [K,mem_filter,mem_univ,true_and]
        exact hbad p.1 p.2 ((mem_filter.mp hp).2)
      · intro a ha
        have hc := card_le_card_of_injOn Prod.snd
          (s := P.filter (fun p => p.1=a))
          (t := univ.filter (fun b : F => b^4=1-a^4)) (by
            intro p hp
            have h := mem_filter.mp hp
            have he := (mem_filter.mp h.1).2
            rw [h.2] at he
            simp only [mem_coe,mem_filter,mem_univ,true_and]
            exact eq_sub_of_add_eq' he) (by
              intro p hp r hr hpr
              apply Prod.ext
              · exact (mem_filter.mp hp).2.trans (mem_filter.mp hr).2.symm
              · exact hpr)
        exact hc.trans (quartic_fiber_le_two hmod _)
    have hlarge := quartic_circle_large hmod h2
    have hk := ternary_kernel_card T hsur
    have hpos : 0<Fintype.card F := Fintype.card_pos
    change 3*K.card=Fintype.card F at hk
    change Fintype.card F≤P.card at hlarge
    omega
  obtain ⟨a,b,hab,ha⟩ := hex
  have hcases : ∀ t : ZMod 3, t≠0 → t=1 ∨ t= -1 := by decide
  rcases hcases (T a) ha with h | h
  · exact ⟨a,b,hab,h⟩
  · refine ⟨-a,b,by convert hab using 1; ring,?_⟩
    rw [map_neg,h,neg_neg]

/-- Specialize the counting theorem to the actual absolute field trace. -/
theorem exists_actual_trace_one [CharP F 3] (hmod : Fintype.card F%4=3) :
    letI := ZMod.algebra F 3
    ∃ a b : F, a^4+b^4=1 ∧ Algebra.trace (ZMod 3) F a=1 := by
  letI := ZMod.algebra F 3
  have h2 : (2:F)≠0 := by
    intro h
    have h3 : (3:F)=0 := CharP.cast_eq_zero F 3
    have h1 : (1:F)=0 := by linear_combination h3-h
    exact one_ne_zero h1
  exact exists_quartic_trace_one hmod h2
    (Algebra.trace (ZMod 3) F).toAddMonoidHom (Algebra.trace_surjective (ZMod 3) F)

#print axioms quartic_circle_large
#print axioms quartic_fiber_le_two
#print axioms exists_quartic_trace_one
#print axioms exists_actual_trace_one
end Erdos714QuarticCircleTrace
