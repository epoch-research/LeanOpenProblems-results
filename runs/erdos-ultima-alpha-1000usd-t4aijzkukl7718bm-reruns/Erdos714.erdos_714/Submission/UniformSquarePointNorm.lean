import FormalConjecturesUtil

/-!
A uniform obstruction to the ordinary cubic norm construction restricted to
nonzero square point norms and nonzero square weights. This does not prove
or disprove Erdős 714. The fixed cubic remains irreducible on the explicitly
specified unbounded sequence of finite fields.
-/

open Polynomial SimpleGraph

namespace Erdos714UniformSquarePoints

variable {F : Type*} [Field F] [CharP F 3]

/-- Cubic norm for θ³=θ+1 in the basis 1,θ,θ². -/
def normForm (v : Fin 3 → F) : F :=
  v 0^3 + 2*v 0^2*v 2 + v 0*v 2^2 - v 0*v 1^2 +
    v 1^3 - v 1*v 2^2 - 3*v 0*v 1*v 2 + v 2^3

theorem normForm_eq_det (v : Fin 3 → F) :
    normForm v = Matrix.det
      !![v 0, v 2, v 1;
         v 1, v 0+v 2, v 1+v 2;
         v 2, v 1, v 0+v 2] := by
  simp [Matrix.det_fin_three, normForm]
  ring

/-- Translate the standard characteristic-three copy by θ². -/
def rows : Fin 4 → Fin 3 → F :=
  ![![0,0,1], ![1,0,1], ![-1,0,1], ![0,1,1]]

def columns : Fin 4 → Fin 3 → F :=
  ![![0,1,-1], ![1,1,-1], ![-1,1,-1], ![1,-1,-1]]

def weights : Fin 4 → F := ![1,1,1,-1]

def pointNorms : Bool → Fin 4 → F
  | false => ![1,-1,1,1]
  | true => ![-1,1,-1,1]

def points : Bool → Fin 4 → Fin 3 → F
  | false => rows
  | true => columns

theorem norm_edges (i j : Fin 4) :
    normForm (rows i + columns j) = weights (F := F) i * weights j := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  fin_cases i <;> fin_cases j <;>
    simp only [rows, columns, weights, pointNorms, points, normForm, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons]
  · linear_combination 0 * h3
  · linear_combination 0 * h3
  · linear_combination 0 * h3
  · linear_combination 0 * h3
  · linear_combination 0 * h3
  · linear_combination 2 * h3
  · linear_combination 0 * h3
  · linear_combination 2 * h3
  · linear_combination 0 * h3
  · linear_combination 0 * h3
  · linear_combination -2 * h3
  · linear_combination 0 * h3
  · linear_combination 3 * h3
  · linear_combination 2 * h3
  · linear_combination 4 * h3
  · linear_combination 0 * h3

theorem point_norms (s : Bool) (i : Fin 4) :
    normForm (points s i) = pointNorms (F := F) s i := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  cases s <;> fin_cases i <;>
    simp only [rows, columns, weights, pointNorms, points, normForm, Pi.add_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons]
  · linear_combination 0 * h3
  · linear_combination 2 * h3
  · linear_combination 0 * h3
  · linear_combination 0 * h3
  · linear_combination 0 * h3
  · linear_combination 0 * h3
  · linear_combination -2 * h3
  · linear_combination -2 * h3

private lemma neg_one_ne_one : (-1 : F) ≠ 1 := by
  intro h
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  apply (one_ne_zero : (1 : F) ≠ 0)
  linear_combination h + h3

theorem rows_injective : Function.Injective (rows (F := F)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [rows, funext_iff, Fin.forall_fin_succ,
      neg_one_ne_one, Ne.symm neg_one_ne_one] at h ⊢

theorem columns_injective : Function.Injective (columns (F := F)) := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp [columns, funext_iff, Fin.forall_fin_succ,
      neg_one_ne_one, Ne.symm neg_one_ne_one] at h ⊢

/-- The bipartite coordinate norm graph, before restricting vertices. -/
def graph : SimpleGraph (Bool × ((Fin 3 → F) × F)) where
  Adj u v := u.1 ≠ v.1 ∧ normForm (u.2.1 + v.2.1) = u.2.2 * v.2.2
  symm := by
    intro u v h
    exact ⟨h.1.symm, by simpa only [add_comm, mul_comm] using h.2⟩
  loopless := by intro v h; exact h.1 rfl

/-- Zero is excluded from BOTH square conditions. -/
def allowed (v : Bool × ((Fin 3 → F) × F)) : Prop :=
  v.2.2 ≠ 0 ∧ IsSquare v.2.2 ∧
    normForm v.2.1 ≠ 0 ∧ IsSquare (normForm v.2.1)

def restrictedGraph : SimpleGraph {v // allowed (F := F) v} := graph.induce _

lemma certificate_allowed (hs : IsSquare (-1 : F)) (s : Bool) (i : Fin 4) :
    allowed (s, points s i, weights (F := F) i) := by
  have hs1 : IsSquare (1 : F) := ⟨1, by simp⟩
  change weights i ≠ 0 ∧ IsSquare (weights i) ∧
    normForm (points s i) ≠ 0 ∧ IsSquare (normForm (points s i))
  rw [point_norms]
  cases s <;> fin_cases i <;>
    simp [weights, pointNorms, hs, hs1]

/-- The same explicit copy works whenever minus one is a square. -/
theorem restrictedGraph_not_free (hs : IsSquare (-1 : F)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (restrictedGraph (F := F)) := by
  let L (i : Fin 4) : {v // allowed (F := F) v} :=
    ⟨(false, rows i, weights i), certificate_allowed hs false i⟩
  let R (i : Fin 4) : {v // allowed (F := F) v} :=
    ⟨(true, columns i, weights i), certificate_allowed hs true i⟩
  have hL : Function.Injective L := by
    intro i j h
    apply rows_injective (F := F)
    exact congrArg (fun v : {v // allowed (F := F) v} => v.val.2.1) h
  have hR : Function.Injective R := by
    intro i j h
    apply columns_injective (F := F)
    exact congrArg (fun v : {v // allowed (F := F) v} => v.val.2.1) h
  have hE : ∀ i j, restrictedGraph.Adj (L i) (R j) := by
    intro i j
    exact ⟨Bool.false_ne_true, norm_edges i j⟩
  intro hfree
  apply hfree
  refine ⟨⟨⟨Sum.elim L R, ?_⟩, ?_⟩⟩
  · intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => simp at hxy
      | inr j => exact hE i j
    | inr i =>
      cases y with
      | inl j => exact (hE j i).symm
      | inr j => simp at hxy
  · intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (hL hxy)
      | inr j => exact False.elim (Bool.false_ne_true
          (congrArg (fun v : {v // allowed (F := F) v} => v.val.1) hxy))
    | inr i =>
      cases y with
      | inl j => exact False.elim (Bool.false_ne_true
          (congrArg (fun v : {v // allowed (F := F) v} => v.val.1) hxy).symm)
      | inr j => exact congrArg Sum.inr (hR hxy)

/-- Explicit Frobenius iteration for an Artin--Schreier root of one. -/
lemma artinSchreier_iteration (x : F) (hx : x^3-x = 1) (m : ℕ) :
    x^(3^m) = x + (m : F) := by
  have hx3 : x^3 = x+1 := by linear_combination hx
  induction m with
  | zero => simp
  | succ m ih =>
    have hn : (m : F)^3 = m := by
      simpa only [frobenius_def] using map_natCast (frobenius F 3) m
    rw [pow_succ, pow_mul, ih, add_pow_char, hx3, hn]
    push_cast
    ring

/-- The fixed cubic remains irreducible unless the extension degree is divisible by three. -/
theorem parameter_irreducible [Fintype F] (m : ℕ)
    (hc : Fintype.card F = 3^m) (hm : ¬ 3 ∣ m) :
    Irreducible (X^3-X-1 : F[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · have hd : (X^3-X-1 : F[X]).natDegree = 3 := by compute_degree!
    rw [hd]
    decide
  · intro x hx
    have hx' : x^3-x = 1 := by simpa [Polynomial.IsRoot, sub_eq_zero] using hx
    have hi := artinSchreier_iteration x hx' m
    have hq : x^(3^m) = x := by simpa [hc] using FiniteField.pow_card x
    have hm0 : (m : F) = 0 := by linear_combination hq - hi
    exact hm ((CharP.cast_eq_zero_iff F 3 m).mp hm0)

/-- Every even extension degree not divisible by three admits the fixed obstruction. -/
theorem finite_even_obstruction [Fintype F] (m : ℕ)
    (hc : Fintype.card F = 3^m) (he : Even m) (hm : ¬ 3 ∣ m) :
    Irreducible (X^3-X-1 : F[X]) ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (restrictedGraph (F := F)) := by
  refine ⟨parameter_irreducible m hc hm, restrictedGraph_not_free ?_⟩
  rw [FiniteField.isSquare_neg_one_iff, hc]
  obtain ⟨k, rfl⟩ := he
  rw [← two_mul k, pow_mul]
  norm_num [Nat.pow_mod]

/-- A uniform nonfree family with a GENUINE irreducible cubic norm. -/
theorem finite_obstruction [Fintype F] (k : ℕ)
    (hc : Fintype.card F = 3^(6*k+2)) :
    Irreducible (X^3-X-1 : F[X]) ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (restrictedGraph (F := F)) := by
  refine ⟨parameter_irreducible (6*k+2) hc (by omega), restrictedGraph_not_free ?_⟩
  rw [FiniteField.isSquare_neg_one_iff, hc]
  have h : 3^(6*k+2) % 4 = 1 := by
    rw [pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  omega

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The obstruction is instantiated over an unbounded sequence, not only one field. -/
theorem galois_field_obstruction (k : ℕ) :
    Irreducible (X^3-X-1 : (GaloisField 3 (6*k+2))[X]) ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
        (restrictedGraph (F := GaloisField 3 (6*k+2))) := by
  letI : Fintype (GaloisField 3 (6*k+2)) := Fintype.ofFinite _
  apply finite_obstruction k
  rw [Fintype.card_eq_nat_card, GaloisField.card 3 (6*k+2) (by omega)]

/-- Explicitly unbounded base-field sizes for the genuine norm obstruction. -/
theorem arbitrarily_large_obstruction (N : ℕ) :
    ∃ k : ℕ, N < Nat.card (GaloisField 3 (6*k+2)) ∧
      Irreducible (X^3-X-1 : (GaloisField 3 (6*k+2))[X]) ∧
      ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free
        (restrictedGraph (F := GaloisField 3 (6*k+2))) := by
  refine ⟨N, ?_, galois_field_obstruction N⟩
  rw [GaloisField.card 3 (6*N+2) (by omega)]
  exact (Nat.lt_pow_self (n := N) (a := 3) (by decide)).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))

#print axioms normForm_eq_det
#print axioms restrictedGraph_not_free
#print axioms artinSchreier_iteration
#print axioms parameter_irreducible
#print axioms finite_even_obstruction
#print axioms finite_obstruction
#print axioms galois_field_obstruction
#print axioms arbitrarily_large_obstruction

end Erdos714UniformSquarePoints
