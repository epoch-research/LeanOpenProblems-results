import FormalConjecturesUtil

/-!
A uniform K_{4,4} in characteristic-three cubic norm graphs.
This file does not prove or disprove Erdős Problem 714.
-/

open SimpleGraph Polynomial

set_option maxHeartbeats 3000000

namespace Erdos714CharThreeNorm

variable {F : Type*} [Field F] [CharP F 3]

/-- Coordinate norm in the algebra with basis `1, θ, θ²`, where `θ³=θ+d`. -/
def normForm (d : F) (v : F × F × F) : F :=
  v.1 ^ 3 + 2 * v.1 ^ 2 * v.2.2 + v.1 * v.2.2 ^ 2 - v.1 * v.2.1 ^ 2 +
    d * v.2.1 ^ 3 - d * v.2.1 * v.2.2 ^ 2 -
    3 * d * v.1 * v.2.1 * v.2.2 + d ^ 2 * v.2.2 ^ 3

/-- The displayed cubic really is the determinant of the multiplication matrix. -/
theorem normForm_eq_det (d : F) (v : F × F × F) :
    normForm d v = Matrix.det
      !![v.1, d*v.2.2, d*v.2.1;
         v.2.1, v.1+v.2.2, v.2.1+d*v.2.2;
         v.2.2, v.2.1, v.1+v.2.2] := by
  rw [Matrix.det_fin_three]
  change normForm d v =
    v.1 * (v.1 + v.2.2) * (v.1 + v.2.2) - v.1 * (v.2.1 + d*v.2.2) * v.2.1 -
    (d*v.2.2) * v.2.1 * (v.1+v.2.2) + (d*v.2.2) * (v.2.1+d*v.2.2) * v.2.2 +
    (d*v.2.1) * v.2.1 * v.2.1 - (d*v.2.1) * (v.1+v.2.2) * v.2.2
  unfold normForm
  ring

@[simp] theorem normForm_plane (d x y : F) :
    normForm d (x, y, 0) = x ^ 3 - x * y ^ 2 + d * y ^ 3 := by
  simp [normForm]

/-- On the plane used below the norm is the product over the three conjugates. -/
theorem normForm_plane_conjugates (d x y theta : F)
    (htheta : theta ^ 3 - theta = d) :
    normForm d (x, y, 0) =
      (x + y * theta) * (x + y * (theta + 1)) * (x + y * (theta - 1)) := by
  have hc := add_pow_char (x) (y * theta) 3
  simp only [mul_pow] at hc
  rw [normForm_plane]
  calc
    x ^ 3 - x * y ^ 2 + d * y ^ 3 =
        (x + y * theta) ^ 3 - y ^ 2 * (x + y * theta) := by
      rw [hc, ← htheta]
      ring
    _ = _ := by ring

/-- The weighted bipartite graph in these norm coordinates. -/
def graph (d : F) : SimpleGraph (Bool × ((F × F × F) × Fˣ)) where
  Adj u v := u.1 ≠ v.1 ∧ normForm d (u.2.1 + v.2.1) = (u.2.2 : F) * (v.2.2 : F)
  symm := by
    intro u v h
    exact ⟨h.1.symm, by simpa only [add_comm, mul_comm] using h.2⟩
  loopless := by intro u h; exact h.1 rfl

private lemma neg_one_ne_one : (-1 : F) ≠ 1 := by
  intro h
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have : (1 : F) = 0 := by linear_combination h3 + h
  exact one_ne_zero this

/-- All fields admit the following explicit configuration, provided the weights are nonzero. -/
theorem graph_not_free (c : F) (hc : c ≠ 0) (hd : -c ^ 3 - c ≠ 0) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph (-c ^ 3 - c)) := by
  let d := -c ^ 3 - c
  let D : Fˣ := Units.mk0 d hd
  let B : Fˣ := Units.mk0 (-c ^ 3) (neg_ne_zero.mpr (pow_ne_zero 3 hc))
  let L : Fin 4 → Bool × ((F × F × F) × Fˣ) :=
    ![(false, (0, 0, 0), 1), (false, (1, 0, 0), 1),
      (false, (-1, 0, 0), 1), (false, (0, 1, 0), -1)]
  let R : Fin 4 → Bool × ((F × F × F) × Fˣ) :=
    ![(true, (0, 1, 0), D), (true, (1, 1, 0), D),
      (true, (-1, 1, 0), D), (true, (c, -1, 0), B)]
  have hL : Function.Injective L := by
    intro i j hij
    have hp := congrArg (fun v : Bool × ((F × F × F) × Fˣ) => v.2.1) hij
    fin_cases i <;> fin_cases j <;>
      simp [L, neg_one_ne_one, Ne.symm neg_one_ne_one] at hp ⊢
  have hR : Function.Injective R := by
    intro i j hij
    have hp := congrArg (fun v : Bool × ((F × F × F) × Fˣ) => v.2.1) hij
    fin_cases i <;> fin_cases j <;>
      simp [R, neg_one_ne_one, Ne.symm neg_one_ne_one] at hp ⊢
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have h2 : (2 : F) = -1 := by linear_combination h3
  have h6 : (6 : F) = 0 := by linear_combination 2 * h3
  have h8 : (8 : F) = -1 := by linear_combination 3 * h3
  have hleft : ∀ i, (L i).1 = false := by intro i; fin_cases i <;> rfl
  have hright : ∀ i, (R i).1 = true := by intro i; fin_cases i <;> rfl
  have hp : (c + 1) ^ 3 = c ^ 3 + 1 := by simpa using add_pow_char c (1 : F) 3
  have hm : (c - 1) ^ 3 = c ^ 3 - 1 := by simpa using sub_pow_char c (1 : F)
  have hE : ∀ i j, (graph d).Adj (L i) (R j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [L, R, graph, normForm, D, B, d, hp, hm,
        show (-1 : F) + c = c - 1 by ring, show (1 : F) + c = c + 1 by ring] <;>
      ring_nf <;> simp [h2, h3, h6, h8] <;> ring
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
      | inr j =>
        have h : (L i).1 = (R j).1 := congrArg Prod.fst hab
        rw [hleft, hright] at h
        exact False.elim (Bool.false_ne_true h)
    | inr i =>
      cases b with
      | inl j =>
        have h : (L j).1 = (R i).1 := (congrArg Prod.fst hab).symm
        rw [hleft, hright] at h
        exact False.elim (Bool.false_ne_true h)
      | inr j => exact congrArg Sum.inr (hR hab)

/-- The Artin–Schreier map is not onto a finite characteristic-three field. -/
theorem exists_outside_artinSchreier [Finite F] : ∃ c : F, ∀ x : F, x ^ 3 - x ≠ c := by
  classical
  have hn : ¬ Function.Surjective (fun x : F => x ^ 3 - x) := by
    intro hs
    have hi := Finite.injective_iff_surjective.mpr hs
    have he : (0 : F) = 1 := hi (by simp)
    exact zero_ne_one he
  simpa only [Function.Surjective, not_forall, not_exists] using hn

/-- The chosen parameter gives an irreducible cubic, not a split or degenerate norm form. -/
theorem parameter_irreducible (c : F) (hc : ∀ x : F, x ^ 3 - x ≠ c) :
    c ≠ 0 ∧ -c ^ 3 - c ≠ 0 ∧
      Irreducible ((X ^ 3 - X - C (-c ^ 3 - c)) : F[X]) := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have hroot : ∀ x : F, x ^ 3 - x ≠ -c ^ 3 - c := by
    intro x hx
    apply hc (x + c)
    rw [add_pow_char x c 3]
    linear_combination hx - c * h3
  have hc0 : c ≠ 0 := by
    intro h
    exact hc 0 (by simp [h])
  have hd0 : -c ^ 3 - c ≠ 0 := by
    intro h
    exact hroot 0 (by simp [h])
  refine ⟨hc0, hd0, ?_⟩
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hdeg : ((X ^ 3 - X - C (-c ^ 3 - c)) : F[X]).natDegree = 3 := by
      compute_degree!
    rw [hdeg]
    decide
  · intro x hx
    apply hroot x
    simpa only [Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hx

/-- Every finite characteristic-three field has this cubic-norm K_{4,4} obstruction. -/
theorem finite_char_three_obstruction [Finite F] :
    ∃ d : F, Irreducible ((X ^ 3 - X - C d) : F[X]) ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (graph d) := by
  obtain ⟨c, hc⟩ := exists_outside_artinSchreier (F := F)
  obtain ⟨hc0, hd0, hirr⟩ := parameter_irreducible c hc
  exact ⟨-c ^ 3 - c, hirr, graph_not_free c hc0 hd0⟩

#print axioms normForm_eq_det
#print axioms normForm_plane_conjugates
#print axioms graph_not_free
#print axioms finite_char_three_obstruction

end Erdos714CharThreeNorm
