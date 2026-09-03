import Submission.QuadraticRecoveryThinning
import Submission.NormPolynomialLevels

/-!
The complementary-block obstruction for quadratic cubic-recovery graphs
extends to every characteristic. Three colors suffice for the possible
projective row multiplicity. No homogeneity assumption on N is imposed.
-/
noncomputable section
open Classical Finset SimpleGraph Polynomial
set_option maxHeartbeats 4000000
namespace Erdos714QuadraticAll
open Erdos714LinearBlocks Erdos714QuadraticThinning

/-- Bounded fibers can be split into finitely many injective color classes. -/
lemma color_fibers {A T : Type*} [Fintype A] (f : A → T) (d : ℕ)
    (hf : ∀ t, (univ.filter (fun a => f a=t)).card ≤ d) :
    ∃ c : A → Fin d, ∀ a b, f a=f b → c a=c b → a=b := by
  by_cases hA : Nonempty A
  · letI : Inhabited A := ⟨Classical.choice hA⟩
    obtain ⟨g,hg⟩ := Erdos714NormLevels.enumerate_sets
      (fun t => univ.filter (fun a => f a=t)) d hf
    have ha (a : A) : ∃ i, g i (f a)=a := hg _ _ (mem_filter.mpr ⟨mem_univ _,rfl⟩)
    choose c hc using ha
    refine ⟨c,?_⟩
    intro a b hab hcb
    rw [← hc a,← hc b,hab,hcb]
  · letI : IsEmpty A := not_nonempty_iff.mp hA
    exact ⟨isEmptyElim,fun a => isEmptyElim a⟩

variable {F : Type*} [Field F]

/-- The first four normalized row coordinates suffice to bound projective fibers. -/
def profile (Q : QuadraticForm F (V (F := F)))
    (B : V (F := F) ≃ₗ[F] V (F := F)) (x : Allowed Q) : V (F := F) :=
  ((Q x.val)^2)⁻¹ • B x.val

lemma recover_profile (Q : QuadraticForm F (V (F := F)))
    (B : V (F := F) ≃ₗ[F] V (F := F)) (x : Allowed Q) :
    x.val=(Q x.val)^2 • B.symm (profile Q B x) := by
  simp only [profile,map_smul,LinearEquiv.symm_apply_apply,smul_smul]
  rw [mul_inv_cancel₀ (pow_ne_zero 2 x.property),one_smul]

/-- Every projective row coincidence also coincides in the normalized profile. -/
lemma ray_profile (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (B : V (F := F) ≃ₗ[F] V (F := F)) (x y : Allowed Q) (a : F)
    (h : rowLift Q N B x=a • rowLift Q N B y) : profile Q B x=profile Q B y := by
  have hx : B x.val=a • B y.val := by
    ext i
    fin_cases i
    · simpa [rowLift] using congrArg (fun p : U (F := F) × U (F := F) => p.1 0) h
    · simpa [rowLift] using congrArg (fun p : U (F := F) × U (F := F) => p.1 1) h
    · simpa [rowLift] using congrArg (fun p : U (F := F) × U (F := F) => p.2 0) h
    · simpa [rowLift] using congrArg (fun p : U (F := F) × U (F := F) => p.2 1) h
  have hs : (Q x.val)^2=a*(Q y.val)^2 := by
    simpa [rowLift] using congrArg (fun p : U (F := F) × U (F := F) => p.1 2) h
  have ha : a ≠ 0 := by
    intro ha
    have hz : (Q x.val)^2=0 := by simpa [ha] using hs
    exact pow_ne_zero 2 x.property hz
  ext i
  simp only [profile,Pi.smul_apply,smul_eq_mul,hx,hs]
  field_simp

variable [Fintype F]

/-- In all characteristics each normalized profile has at most three actual rows. -/
lemma profile_fiber_bound (Q : QuadraticForm F (V (F := F)))
    (B : V (F := F) ≃ₗ[F] V (F := F)) (v : V (F := F)) :
    (univ.filter (fun x : Allowed Q => profile Q B x=v)).card ≤ 3 := by
  let S := univ.filter (fun x : Allowed Q => profile Q B x=v)
  let P : F[X] := C (Q (B.symm v))*X^3-1
  have hp : P ≠ 0 := by
    intro h
    have hh := congrArg (Polynomial.eval (0 : F)) h
    simp [P] at hh
  have hdeg : P.natDegree ≤ 3 := by dsimp [P]; compute_degree!
  have hrec (x : Allowed Q) (hx : x ∈ S) : x.val=(Q x.val)^2 • B.symm v := by
    rw [← (mem_filter.mp hx).2]
    exact recover_profile Q B x
  have hi : Set.InjOn (fun x : Allowed Q => Q x.val) (S : Set (Allowed Q)) := by
    intro x hx y hy hxy
    apply Subtype.ext
    change Q x.val=Q y.val at hxy
    rw [hrec x hx,hrec y hy,hxy]
  have hroot (x : Allowed Q) (hx : x ∈ S) : P.eval (Q x.val)=0 := by
    have hq : Q x.val=(Q x.val)^4*Q (B.symm v) := by
      calc
        _ = Q ((Q x.val)^2 • B.symm v) := congrArg Q (hrec x hx)
        _ = _ := by rw [Q.map_smul,smul_eq_mul]; ring
    apply (mul_eq_zero.mp (show Q x.val*P.eval (Q x.val)=0 from ?_)).resolve_left x.property
    simp only [P,eval_sub,eval_mul,eval_C,eval_pow,eval_X,eval_one]
    linear_combination -hq
  have hs : (S.image (fun x : Allowed Q => Q x.val)).val ⊆ P.roots := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := mem_image.mp ha
    exact (Polynomial.mem_roots hp).mpr (hroot x hx)
  calc
    _ = (S.image (fun x : Allowed Q => Q x.val)).card := (card_image_of_injOn hi).symm
    _ ≤ P.natDegree := Polynomial.card_le_degree_of_subset_roots hs
    _ ≤ 3 := hdeg

/-- Three colors give projectively injective row families, with no assumption
that the field has characteristic three or that cubing is injective. -/
lemma row_colors (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (B : V (F := F) ≃ₗ[F] V (F := F)) :
    ∃ c : Allowed Q → Fin 3, ∀ i : Fin 3,
      RayInjective (F := F) (fun x : {x : Allowed Q // c x=i} => rowLift Q N B x.val) := by
  obtain ⟨c,hc⟩ := color_fibers (profile Q B) 3 (fun v => by
    convert profile_fiber_bound Q B v using 1
    apply congrArg Finset.card
    ext x
    simp only [mem_filter,mem_univ,true_and])
  refine ⟨c,?_⟩
  intro i x y a h
  apply Subtype.ext
  exact hc x.val y.val (ray_profile Q N B x.val y.val a h)
    (x.property.trans y.property.symm)

/-- An actual selected incidence system, with only the original quadratic law
assumed on its edges. No generic-rank or scalar-only argument is used. -/
theorem selected_fourth_power (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (B : V (F := F) ≃ₗ[F] V (F := F)) (E : Finset (Allowed Q × Allowed Q))
    (hfree : NoRectangle E)
    (hE : ∀ z ∈ E, B z.1.val ⬝ᵥ z.2.val=
      (Q z.1.val)^2*(Q z.2.val)^2+Q z.1.val*N z.1.val*Q z.2.val) :
    E.card^4 ≤ 37015056*Fintype.card F^27 := by
  obtain ⟨c,hc⟩ := row_colors Q N B
  let S (i : Fin 3) := {x : Allowed Q // c x=i}
  let E' (i : Fin 3) : Finset (S i × Allowed Q) :=
    univ.filter (fun z => (z.1.val,z.2) ∈ E)
  let T (i : Fin 3) := E.filter (fun z => c z.1=i)
  have hcard (i : Fin 3) : (E' i).card=(T i).card := by
    let e : S i × Allowed Q ↪ Allowed Q × Allowed Q :=
      (Function.Embedding.subtype _).prodMap (Function.Embedding.refl _)
    have he : (E' i).map e=T i := by
      ext z
      constructor
      · intro hz
        obtain ⟨w,hw,rfl⟩ := mem_map.mp hz
        exact mem_filter.mpr ⟨(mem_filter.mp hw).2,w.1.property⟩
      · intro hz
        obtain ⟨hz,hi⟩ := mem_filter.mp hz
        exact mem_map.mpr ⟨(⟨z.1,hi⟩,z.2),mem_filter.mpr ⟨mem_univ _,hz⟩,rfl⟩
    rw [← he,card_map]
  have hn : Fintype.card (Allowed Q) ≤ Fintype.card F^4 := by
    simpa only [Fintype.card_fun,Fintype.card_fin] using
      Fintype.card_subtype_le (fun x : V (F := F) => Q x ≠ 0)
  have hb (i : Fin 3) : (T i).card^4 ≤ 456976*Fintype.card F^27 := by
    rw [← hcard]
    apply chart_fourth_power (by simp [Module.finrank_fintype_fun_eq_card])
      (fun x : S i => rowLift Q N B x.val) (columnLift Q) (hc i)
      (column_ray_injective Q) (fun x => row_nonzero Q N B x.val) (column_nonzero Q) (E' i)
    · intro f g hfg
      apply hfree (f.trans (Function.Embedding.subtype _)) g
      intro k l
      exact (mem_filter.mp (hfg k l)).2
    · intro z hz
      exact (lift_compatibility Q N B _ _).mpr (hE _ (mem_filter.mp hz).2)
    · exact (Fintype.card_subtype_le _).trans hn
    · exact hn
  have hcover : E ⊆ univ.biUnion T := by
    intro z hz
    exact mem_biUnion.mpr ⟨c z.1,mem_univ _,mem_filter.mpr ⟨hz,rfl⟩⟩
  have he : E.card ≤ ∑ i : Fin 3, (T i).card := (card_le_card hcover).trans card_biUnion_le
  have hp := pow_sum_le_card_mul_sum_pow (s := (univ : Finset (Fin 3)))
    (f := fun i => (T i).card) (by intros; omega) 3
  calc
    _ ≤ (∑ i : Fin 3, (T i).card)^4 := Nat.pow_le_pow_left he 4
    _ ≤ 3^3*∑ i : Fin 3, (T i).card^4 := by simpa using hp
    _ ≤ 3^3*∑ _i : Fin 3, (456976*Fintype.card F^27) := by
      gcongr with i _
      exact hb i
    _ = _ := by simp; ring

/-- Uniform obstruction in EVERY characteristic, for arbitrary Q and N and
arbitrary edge thinning. The original nonzero-Q vertex guard is retained. -/
theorem arbitrary_thinning (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (B : V (F := F) ≃ₗ[F] V (F := F)) (H : SimpleGraph (Allowed Q ⊕ Allowed Q))
    (hH : H ≤ graph Q N B) (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 37015056*Fintype.card F^27 := by
  let E : Finset (Allowed Q × Allowed Q) := univ.filter (fun z => H.Adj (.inl z.1) (.inr z.2))
  have hbi : H ≤ completeBipartiteGraph (Allowed Q) (Allowed Q) := by
    intro x y hxy
    have h := hH hxy
    cases x <;> cases y <;> simp_all [graph]
  have he : E.card=H.edgeFinset.card := by
    have hh := Erdos714Packing.incidence_edges (Erdos714Unbalanced.neighborhoods H)
    rw [Erdos714Unbalanced.incidence_neighborhoods H hbi] at hh
    rw [hh]
    have hc : (∑ z : Allowed Q × Allowed Q,
        if H.Adj (.inl z.1) (.inr z.2) then 1 else 0 : ℕ)=E.card := by
      simp only [sum_boole,Nat.cast_id]
      rfl
    rw [← hc,Fintype.sum_prod_type]
    simp only [sum_boole,Nat.cast_id,Erdos714Unbalanced.neighborhoods]
  have hrect : NoRectangle E := by
    intro f g hfg
    have hfree := (Erdos714Packing.free_iff_no_rectangle (Erdos714Unbalanced.neighborhoods H)
      (by decide : 0 < 4)).mp (by rwa [Erdos714Unbalanced.incidence_neighborhoods H hbi])
    apply hfree f g
    intro i j
    simpa only [E,Erdos714Unbalanced.neighborhoods,mem_filter,mem_univ,true_and] using hfg i j
  rw [← he]
  apply selected_fourth_power Q N B E hrect
  intro z hz
  exact hH (mem_filter.mp hz).2

/-- Bundled nondegenerate pairings are included, not just a fixed dot product. -/
theorem bilinear_thinning (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (P : V (F := F) →ₗ[F] Module.Dual F (V (F := F))) (hP : Function.Bijective P)
    (H : SimpleGraph (Allowed Q ⊕ Allowed Q)) (hH : H ≤ bilinearGraph Q N P)
    (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H) :
    H.edgeFinset.card^4 ≤ 37015056*Fintype.card F^27 := by
  let B := (LinearEquiv.ofBijective P hP).trans (dotProductEquiv F (Fin 4)).symm
  have hpair (x y : V (F := F)) : B x ⬝ᵥ y=P x y := by
    have h := (dotProductEquiv F (Fin 4)).apply_symm_apply (P x)
    exact congrArg (fun f : Module.Dual F (V (F := F)) => f y) h
  apply arbitrary_thinning Q N B H _ hf
  intro v w hvw
  have h := hH hvw
  cases v <;> cases w
  all_goals first | exact h | simpa only [graph,bilinearGraph,hpair] using h

/-- A critical edge constant is possible only at bounded field orders. -/
theorem size_budget (Q : QuadraticForm F (V (F := F))) (N : V (F := F) → F)
    (B : V (F := F) ≃ₗ[F] V (F := F)) (H : SimpleGraph (Allowed Q ⊕ Allowed Q))
    (hH : H ≤ graph Q N B) (hf : (completeBipartiteGraph (Fin 4) (Fin 4)).Free H)
    (K : ℕ) (hdense : Fintype.card F^7 ≤ K*H.edgeFinset.card) : Fintype.card F ≤ 37015056*K^4 := by
  have he := arbitrary_thinning Q N B H hH hf
  have hh : Fintype.card F^27*Fintype.card F ≤ Fintype.card F^27*(37015056*K^4) := by
    calc
      _ = (Fintype.card F^7)^4 := by ring
      _ ≤ (K*H.edgeFinset.card)^4 := Nat.pow_le_pow_left hdense 4
      _ = K^4*H.edgeFinset.card^4 := mul_pow _ _ _
      _ ≤ K^4*(37015056*Fintype.card F^27) := Nat.mul_le_mul_left _ he
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (pow_pos Fintype.card_pos 27)

end Erdos714QuadraticAll
#print axioms Erdos714QuadraticAll.color_fibers
#print axioms Erdos714QuadraticAll.recover_profile
#print axioms Erdos714QuadraticAll.ray_profile
#print axioms Erdos714QuadraticAll.profile_fiber_bound
#print axioms Erdos714QuadraticAll.row_colors
#print axioms Erdos714QuadraticAll.selected_fourth_power
#print axioms Erdos714QuadraticAll.arbitrary_thinning
#print axioms Erdos714QuadraticAll.size_budget

#print axioms Erdos714QuadraticAll.bilinear_thinning
