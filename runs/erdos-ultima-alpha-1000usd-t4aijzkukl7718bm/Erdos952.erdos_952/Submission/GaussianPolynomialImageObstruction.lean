import Submission.Investigation

/-! Nonlinear Gaussian polynomial images have finitely many pairs at each
fixed nonzero difference. Consequently their finite additive neighborhoods
contain no infinite bounded-step path. This is a geometric obstruction for a
specified class of sets, not a classification of Gaussian-prime paths. -/
namespace Erdos952Investigation.GaussianPolynomialImageObstruction
open Polynomial
open scoped Classical
set_option maxHeartbeats 0
noncomputable section

/-- A polynomial over the Gaussian integers cannot have a nonzero additive
period unless it is constant. -/
lemma polynomial_eq_C_of_period (P : Polynomial GaussianInt) (h : GaussianInt)
    (hh : h ≠ 0) (hp : ∀ z, P.eval (z+h) = P.eval z) : P = C (P.eval 0) := by
  have he (n : ℕ) : P.eval ((n : GaussianInt)*h) = P.eval 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,hp,ih]
  have hi : Function.Injective (fun n : ℕ => (n : GaussianInt)*h) := by
    intro m n he
    exact Nat.cast_injective (mul_right_cancel₀ hh he)
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective hi).mono
  rintro z ⟨n,rfl⟩
  simpa only [eval_C] using he n

/-- Every nonzero translate difference of a nonlinear polynomial is
nonconstant; in particular it cannot equal any prescribed constant. -/
lemma difference_polynomial_ne_zero (P : Polynomial GaussianInt)
    (hP : 2 ≤ P.natDegree) (h d : GaussianInt) (hh : h ≠ 0) :
    P.comp (X+C h)-P-C d ≠ 0 := by
  intro he
  have hd := congrArg Polynomial.derivative he
  have hperiod : ∀ z, P.derivative.eval (z+h) = P.derivative.eval z := by
    have he' : P.derivative.comp (X+C h) = P.derivative := by
      simpa only [derivative_sub,derivative_comp,derivative_add,derivative_X,
        derivative_C,add_zero,one_mul,sub_zero,derivative_zero,sub_eq_zero] using hd
    intro z
    have hz := congrArg (Polynomial.eval z) he'
    simpa only [eval_comp,eval_add,eval_X,eval_C] using hz
  have hconst := polynomial_eq_C_of_period P.derivative h hh hperiod
  have hdeg : P.derivative.natDegree = P.natDegree-1 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (Polynomial.degree_derivative_eq P (by omega))
  rw [hconst,natDegree_C] at hdeg
  omega

lemma finite_fixed_shift_solutions (P : Polynomial GaussianInt)
    (hP : 2 ≤ P.natDegree) (h d : GaussianInt) (hh : h ≠ 0) :
    {z : GaussianInt | P.eval (z+h)-P.eval z = d}.Finite := by
  have hf := Polynomial.finite_setOf_isRoot (difference_polynomial_ne_zero P hP h d hh)
  simpa only [Polynomial.IsRoot,eval_sub,eval_comp,eval_add,eval_X,eval_C,
    sub_eq_zero] using hf

/-- Fixing a nonzero output difference leaves only finitely many pairs of
Gaussian inputs. Divisibility bounds the input difference; each resulting
finite-difference equation is a nonzero polynomial equation. -/
theorem fixed_difference_pairs_finite (P : Polynomial GaussianInt)
    (hP : 2 ≤ P.natDegree) (d : GaussianInt) (hd : d ≠ 0) :
    {uv : GaussianInt × GaussianInt | P.eval uv.2-P.eval uv.1 = d}.Finite := by
  let H : Set GaussianInt := {h | h.norm ≤ d.norm ∧ h ≠ 0}
  have hH : H.Finite := (norm_sublevel_finite d.norm).subset (fun _ hh => hh.1)
  have hU := hH.biUnion (fun h hh =>
    (finite_fixed_shift_solutions P hP h d hh.2).image (fun z => (z,z+h)))
  apply hU.subset
  intro uv huv
  change P.eval uv.2-P.eval uv.1 = d at huv
  have hne : uv.2-uv.1 ≠ 0 := by
    intro he
    rw [sub_eq_zero.mp he,sub_self] at huv
    exact hd huv.symm
  have hdiv : uv.2-uv.1 ∣ d := by
    rw [← huv]
    exact Polynomial.sub_dvd_eval_sub uv.2 uv.1 P
  have hb : (uv.2-uv.1).norm ≤ d.norm :=
    Int.le_of_dvd (GaussianInt.norm_pos.mpr hd)
      (Zsqrtd.normMonoidHom.map_dvd hdiv)
  simp only [Set.mem_iUnion,Set.mem_image]
  refine ⟨uv.2-uv.1,⟨hb,hne⟩,uv.1,?_,?_⟩
  · have he : uv.1+(uv.2-uv.1) = uv.2 := by abel
    simpa only [Set.mem_setOf_eq,he] using huv
  · simp

/-- Output edges restricted to any finite set of nonzero differences are
finite as well. -/
theorem finite_difference_edges (P : Polynomial GaussianInt)
    (hP : 2 ≤ P.natDegree) (D : Set GaussianInt) (hD : D.Finite) :
    {uv : GaussianInt × GaussianInt | uv.1 ∈ Set.range P.eval ∧
      uv.2 ∈ Set.range P.eval ∧ uv.1 ≠ uv.2 ∧ uv.2-uv.1 ∈ D}.Finite := by
  let E : Set GaussianInt := D \ {0}
  have hE : E.Finite := hD.diff
  have hU := hE.biUnion (fun d hd =>
    (fixed_difference_pairs_finite P hP d hd.2).image
      (fun uv => (P.eval uv.1,P.eval uv.2)))
  apply hU.subset
  rintro uv ⟨⟨u,hu⟩,⟨v,hv⟩,hne,hd⟩
  have hn : uv.2-uv.1 ≠ 0 := sub_ne_zero.mpr hne.symm
  simp only [Set.mem_iUnion,Set.mem_image]
  refine ⟨uv.2-uv.1,⟨hd,hn⟩,(u,v),?_,?_⟩
  · simp only [Set.mem_setOf_eq,hu,hv]
  · exact Prod.ext hu hv

/-- A sequence whose changes use only finitely many ordered edges has
finite range, even if it repeats vertices or pauses. -/
lemma finite_range_of_finite_changes {α : Type*} (x : ℕ → α)
    (E : Set (α × α)) (hE : E.Finite)
    (hx : ∀ n, x n ≠ x (n+1) → (x n,x (n+1)) ∈ E) :
    (Set.range x).Finite := by
  have hf : (insert (x 0) (Prod.snd '' E)).Finite := (hE.image Prod.snd).insert _
  apply hf.subset
  rintro z ⟨n,rfl⟩
  induction n with
  | zero => exact Set.mem_insert _ _
  | succ n ih =>
    by_cases he : x n = x (n+1)
    · exact he ▸ ih
    · exact Set.mem_insert_of_mem _ ⟨(x n,x (n+1)),hx n he,rfl⟩

/-- A path inside a nonlinear polynomial image with a finite increment
alphabet necessarily has finite range. No primality hypothesis is used. -/
theorem polynomial_image_path_finite_range (P : Polynomial GaussianInt)
    (hP : 2 ≤ P.natDegree) (x : ℕ → GaussianInt)
    (hx : ∀ n, x n ∈ Set.range P.eval)
    (hD : (Set.range (fun n => x (n+1)-x n)).Finite) :
    (Set.range x).Finite := by
  apply finite_range_of_finite_changes x _
    (finite_difference_edges P hP _ hD)
  intro n hn
  exact ⟨hx n,hx (n+1),hn,⟨n,rfl⟩⟩

/-- Adding any fixed finite set of offsets does not permit an infinite
finite-increment path through a nonlinear polynomial image. -/
theorem polynomial_image_offsets_path_finite_range (P : Polynomial GaussianInt)
    (hP : 2 ≤ P.natDegree) (T : Set GaussianInt) (hT : T.Finite)
    (x : ℕ → GaussianInt)
    (hx : ∀ n, ∃ u t : GaussianInt, t ∈ T ∧ x n = P.eval u+t)
    (hD : (Set.range (fun n => x (n+1)-x n)).Finite) :
    (Set.range x).Finite := by
  choose u t ht he using hx
  let y : ℕ → GaussianInt := fun n => P.eval (u n)
  have hy (n : ℕ) : x n = y n+t n := he n
  let D := Set.range (fun n => x (n+1)-x n)
  let F := (fun v : GaussianInt × (GaussianInt × GaussianInt) => v.1-v.2.2+v.2.1) ''
    (D ×ˢ (T ×ˢ T))
  have hF : F.Finite := (hD.prod (hT.prod hT)).image _
  have hyD : (Set.range (fun n => y (n+1)-y n)).Finite := by
    apply hF.subset
    rintro d ⟨n,rfl⟩
    refine ⟨(x (n+1)-x n,t n,t (n+1)),⟨⟨n,rfl⟩,ht n,ht (n+1)⟩,?_⟩
    dsimp only
    rw [hy (n+1),hy n]
    abel
  have hyf := polynomial_image_path_finite_range P hP y (fun n => ⟨u n,rfl⟩) hyD
  have hf := (hyf.prod hT).image (fun v : GaussianInt × GaussianInt => v.1+v.2)
  apply hf.subset
  rintro z ⟨n,rfl⟩
  exact ⟨(y n,t n),⟨⟨n,rfl⟩,ht n⟩,(hy n).symm⟩

/-- A fixed norm-neighborhood is a finite-offset neighborhood, since the
Gaussian norm has finite sublevel sets. -/
theorem polynomial_neighborhood_path_finite_range (P : Polynomial GaussianInt)
    (hP : 2 ≤ P.natDegree) (B C : ℤ) (x : ℕ → GaussianInt)
    (hx : ∀ n, ∃ u : GaussianInt, (x n-P.eval u).norm ≤ B)
    (hs : ∀ n, (x (n+1)-x n).norm ≤ C) : (Set.range x).Finite := by
  apply polynomial_image_offsets_path_finite_range P hP
    {t | t.norm ≤ B} (norm_sublevel_finite B) x
  · intro n
    obtain ⟨u,hu⟩ := hx n
    exact ⟨u,x n-P.eval u,hu,by abel⟩
  · apply (norm_sublevel_finite C).subset
    rintro d ⟨n,rfl⟩
    exact hs n

/-- In particular, an injective bounded-step path cannot remain near a
nonlinear polynomial image. This theorem does not assume primality. -/
theorem no_injective_polynomial_neighborhood_path (P : Polynomial GaussianInt)
    (hP : 2 ≤ P.natDegree) (B C : ℤ) (x : ℕ → GaussianInt)
    (hx : Function.Injective x) (hs : ∀ n, (x (n+1)-x n).norm ≤ C) :
    ¬ ∀ n, ∃ u : GaussianInt, (x n-P.eval u).norm ≤ B := by
  intro hp
  exact (Set.infinite_range_of_injective hx)
    (polynomial_neighborhood_path_finite_range P hP B C x hp hs)

/-- The obstruction is uniform in the starting point: each finite offset
neighborhood has a common bound on the length of every injective segment
with increments in a specified finite set. -/
theorem uniform_polynomial_offsets_segment_bound (P : Polynomial GaussianInt)
    (hP : 2 ≤ P.natDegree) (T D : Set GaussianInt) (hT : T.Finite) (hD : D.Finite) :
    ∃ M : ℕ, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, ∃ u t : GaussianInt, t ∈ T ∧ x n = P.eval u+t) →
      (∀ n < L, x (n+1)-x n ∈ D) → L < M := by
  let F := (fun v : GaussianInt × (GaussianInt × GaussianInt) => v.1-v.2.2+v.2.1) ''
    (D ×ˢ (T ×ˢ T))
  have hF : F.Finite := (hD.prod (hT.prod hT)).image _
  let E : Set (GaussianInt × GaussianInt) :=
    {uv | uv.1 ∈ Set.range P.eval ∧ uv.2 ∈ Set.range P.eval ∧
      uv.1 ≠ uv.2 ∧ uv.2-uv.1 ∈ F}
  have hE : E.Finite := finite_difference_edges P hP F hF
  refine ⟨(E.ncard+1)*T.ncard,?_⟩
  intro x L hxi hxp hxs
  choose u t ht he using (fun n : ℕ => hxp (min n L) (min_le_right _ _))
  let y : ℕ → GaussianInt := fun n => P.eval (u n)
  have hy (n : ℕ) (hn : n ≤ L) : x n = y n+t n := by
    simpa only [min_eq_left hn] using he n
  have hedge (n : ℕ) (hn : n < L) (hne : y n ≠ y (n+1)) :
      (y n,y (n+1)) ∈ E := by
    refine ⟨⟨u n,rfl⟩,⟨u (n+1),rfl⟩,hne,?_⟩
    refine ⟨(x (n+1)-x n,t n,t (n+1)),⟨hxs n hn,ht n,ht (n+1)⟩,?_⟩
    dsimp only
    rw [hy (n+1) (by omega),hy n hn.le]
    abel
  let V := insert (y 0) (Prod.snd '' E)
  have hV : V.Finite := (hE.image Prod.snd).insert _
  have hyv (n : ℕ) : n ≤ L → y n ∈ V := by
    induction n with
    | zero => intro _; exact Set.mem_insert _ _
    | succ n ih =>
      intro hn
      by_cases hh : y n = y (n+1)
      · exact hh ▸ ih (by omega)
      · exact Set.mem_insert_of_mem _ ⟨(y n,y (n+1)),hedge n (by omega) hh,rfl⟩
  let W := (fun v : GaussianInt × GaussianInt => v.1+v.2) '' (V ×ˢ T)
  have hW : W.Finite := (hV.prod hT).image _
  have hxw (n : ℕ) (hn : n ∈ Set.Iic L) : x n ∈ W := by
    exact ⟨(y n,t n),⟨hyv n hn,ht n⟩,(hy n hn).symm⟩
  have hl := Set.ncard_le_ncard_of_injOn x hxw hxi hW
  have hI : (Set.Iic L).ncard = L+1 := by rw [← Finset.coe_Iic,Set.ncard_coe_finset,Nat.card_Iic]
  rw [hI] at hl
  have hvcard : V.ncard ≤ E.ncard+1 :=
    (Set.ncard_insert_le _ _).trans (Nat.add_le_add_right (Set.ncard_image_le hE) 1)
  have hwcard : W.ncard ≤ (E.ncard+1)*T.ncard := by
    calc
      _ ≤ (V ×ˢ T).ncard := Set.ncard_image_le (hV.prod hT)
      _ = V.ncard*T.ncard := Set.ncard_prod
      _ ≤ _ := Nat.mul_le_mul_right T.ncard hvcard
  omega

/-- In norm language, every fixed-width nonlinear polynomial neighborhood
has a uniform finite-segment bound for each squared jump bound. -/
theorem uniform_polynomial_neighborhood_segment_bound (P : Polynomial GaussianInt)
    (hP : 2 ≤ P.natDegree) (B C : ℤ) :
    ∃ M : ℕ, ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, ∃ u : GaussianInt, (x n-P.eval u).norm ≤ B) →
      (∀ n < L, (x (n+1)-x n).norm ≤ C) → L < M := by
  obtain ⟨M,hM⟩ := uniform_polynomial_offsets_segment_bound P hP
    {t | t.norm ≤ B} {d | d.norm ≤ C} (norm_sublevel_finite B) (norm_sublevel_finite C)
  refine ⟨M,?_⟩
  intro x L hx hp hs
  apply hM x L hx _ hs
  intro n hn
  obtain ⟨u,hu⟩ := hp n hn
  exact ⟨u,x n-P.eval u,hu,by abel⟩

#print axioms uniform_polynomial_offsets_segment_bound
#print axioms uniform_polynomial_neighborhood_segment_bound
#print axioms polynomial_image_offsets_path_finite_range
#print axioms no_injective_polynomial_neighborhood_path
#print axioms difference_polynomial_ne_zero
#print axioms fixed_difference_pairs_finite
#print axioms polynomial_image_path_finite_range
end
end Erdos952Investigation.GaussianPolynomialImageObstruction
