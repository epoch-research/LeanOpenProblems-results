import Submission.EllipticTorsionReflection

/-! A geometric cap for points selected from a finite list of reflection pairs.
This is not a bound on arbitrary rational-distance sets. -/
namespace Erdos213.ReflectionPairBound
open EuclideanGeometry

lemma pair_count {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset (I × Bool))
    (hp : ∀ i j, (i,false) ∈ S → (i,true) ∈ S →
      (j,false) ∈ S → (j,true) ∈ S → i = j) :
    S.card ≤ Fintype.card I + 1 := by
  classical
  let A := Finset.univ.filter (fun i => (i,false) ∈ S)
  let B := Finset.univ.filter (fun i => (i,true) ∈ S)
  have hI : (A ∩ B).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    simp only [Finset.mem_inter, A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact hp i j hi.1 hi.2 hj.1 hj.2
  have hU : (A ∪ B).card ≤ Fintype.card I := Finset.card_le_univ _
  have hS : S = A.product {false} ∪ B.product {true} := by
    ext ⟨i,b⟩
    cases b <;> simp [A, B]
  have hdis : Disjoint (A.product {false}) (B.product {true}) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨i,b⟩ ha hb
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_singleton] at ha hb
    exact Bool.false_ne_true (ha.2.symm.trans hb.2)
  rw [hS, Finset.card_union_of_disjoint hdis]
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_singleton, mul_one]
  have he := Finset.card_union_add_card_inter A B
  omega

noncomputable def point {I : Type*} (z : I → ℂ) (p : I × Bool) : ℂ :=
  if p.2 then starRingEnd ℂ (z p.1) else z p.1

/-- At most one complete pair may be selected when distinct pair centers have
distinct real coordinates and no selected four indices are cospherical. -/
theorem card_le_of_no_four {I : Type*} [Fintype I] [DecidableEq I]
    (z : I → ℂ) (hx : Function.Injective (fun i => (z i).re))
    (S : Finset (I × Bool))
    (hgp : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬Cospherical ({point z a,point z b,point z c,point z d} : Set ℂ)) :
    S.card ≤ Fintype.card I + 1 := by
  apply pair_count S
  intro i j hi0 hi1 hj0 hj1
  by_contra hij
  have h := EllipticTorsionCap.conjugate_pairs_cospherical (z i) (z j)
    (fun he => hij (hx he))
  apply hgp (i,false) hi0 (i,true) hi1 (j,false) hj0 (j,true) hj1
    (by simp) (by simpa) (by simp) (by simp) (by simpa) (by simp)
  simpa [point] using h

lemma point_injective {I : Type*} (z : I → ℂ)
    (hx : Function.Injective (fun i => (z i).re))
    (hy : ∀ i, (z i).im ≠ 0) : Function.Injective (point z) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ h
  have hr : (z i).re = (z j).re := by
    have hh := congrArg Complex.re h
    cases b <;> cases c <;> simpa [point] using hh
  have hij := hx hr
  subst j
  have hm := congrArg Complex.im h
  cases b <;> cases c
  · rfl
  · exfalso
    apply hy i
    simp [point] at hm
    linarith only [hm]
  · exfalso
    apply hy i
    simp [point] at hm
    linarith only [hm]
  · rfl

/-- Actual finite point-set version. Nonreal representatives prevent a
reflection pair from collapsing, and the covering hypothesis is explicit. -/
theorem finset_card_le_of_no_four {I : Type*} [Fintype I] [DecidableEq I]
    (z : I → ℂ) (hx : Function.Injective (fun i => (z i).re))
    (hy : ∀ i, (z i).im ≠ 0) (S : Finset ℂ)
    (hcover : ∀ p ∈ S, ∃ i, p = z i ∨ p = starRingEnd ℂ (z i))
    (hgp : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬Cospherical ({a,b,c,d} : Set ℂ)) :
    S.card ≤ Fintype.card I + 1 := by
  classical
  let T := Finset.univ.filter (fun p => point z p ∈ S)
  have hi := point_injective z hx hy
  have himage : T.image (point z) = S := by
    ext p
    constructor
    · intro hp
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hp
      exact (Finset.mem_filter.mp ha).2
    · intro hp
      obtain ⟨i,he | he⟩ := hcover p hp
      · apply Finset.mem_image.mpr
        refine ⟨(i,false),?_,?_⟩
        · simp [T,point,← he,hp]
        · simpa [point] using he.symm
      · apply Finset.mem_image.mpr
        refine ⟨(i,true),?_,?_⟩
        · simp [T,point,← he,hp]
        · simpa [point] using he.symm
  have hb := card_le_of_no_four z hx T (by
    intro a ha b hb c hc d hd hab hac had hbc hbd hcd
    simp only [T,Finset.mem_filter,Finset.mem_univ,true_and] at ha hb hc hd
    exact hgp _ ha _ hb _ hc _ hd
      (hi.ne hab) (hi.ne hac) (hi.ne had) (hi.ne hbc) (hi.ne hbd) (hi.ne hcd))
  have he : S.card = T.card := by
    rw [← himage,Finset.card_image_of_injective T hi]
  omega

/-- Three nondegenerate axis-aligned rectangles centered at the origin,
with distinct squared abscissae, cannot contain eight points avoiding every
four-point circle. This statement has no distance-arithmetic hypotheses. -/
theorem three_rectangles_card_le_seven
    (a b : Fin 3 → ℝ) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hx : Function.Injective (fun i => (a i)^2)) (S : Finset ℂ)
    (hcover : ∀ p ∈ S, ∃ i, p.re^2=(a i)^2 ∧ p.im^2=(b i)^2)
    (hgp : ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, ∀ s ∈ S,
      p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
      ¬Cospherical ({p,q,r,s} : Set ℂ)) : S.card ≤ 7 := by
  let z : Fin 3 × Bool → ℂ := fun j => ⟨if j.2 then -a j.1 else a j.1,b j.1⟩
  have hzx : Function.Injective (fun i => (z i).re) := by
    rintro ⟨i,u⟩ ⟨j,v⟩ h
    have he : (a i)^2 = (a j)^2 := by
      have hh := congrArg (fun x : ℝ => x^2) h
      cases u <;> cases v <;> simpa [z] using hh
    have hij := hx he
    subst j
    cases u <;> cases v
    · rfl
    · exfalso
      apply ha i
      simp [z] at h
      linarith only [h]
    · exfalso
      apply ha i
      simp [z] at h
      linarith only [h]
    · rfl
  have hzy : ∀ i, (z i).im ≠ 0 := fun i => hb i.1
  have hzcover : ∀ p ∈ S, ∃ i, p = z i ∨ p = starRingEnd ℂ (z i) := by
    intro p hp
    obtain ⟨i,hre,him⟩ := hcover p hp
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hre with hr | hr <;>
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp him with hi | hi
    · refine ⟨(i,false),Or.inl ?_⟩
      apply Complex.ext <;> simp [z,hr,hi]
    · refine ⟨(i,false),Or.inr ?_⟩
      apply Complex.ext <;> simp [z,hr,hi]
    · refine ⟨(i,true),Or.inl ?_⟩
      apply Complex.ext <;> simp [z,hr,hi]
    · refine ⟨(i,true),Or.inr ?_⟩
      apply Complex.ext <;> simp [z,hr,hi]
  have hh := finset_card_le_of_no_four z hzx hzy S hzcover hgp
  simpa using hh

#print axioms three_rectangles_card_le_seven
#print axioms pair_count
#print axioms finset_card_le_of_no_four
#print axioms card_le_of_no_four

end Erdos213.ReflectionPairBound
