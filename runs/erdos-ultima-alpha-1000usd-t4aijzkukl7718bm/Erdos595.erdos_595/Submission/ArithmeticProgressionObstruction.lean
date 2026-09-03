import FormalConjecturesUtil

/-!
A finite obstruction to homogeneous midpoint rules on K_{3,3,3}, and a
conditional ordered-triangle Ramsey transfer. No finite Ramsey existence
result, and no settlement of Erdős 595, is claimed in this file.
-/

set_option autoImplicit false
open SimpleGraph Set
namespace Erdos595ArithmeticProgression

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

def defect (m : Fin 3) (x y z : E) : E :=
  if m = 0 then y + z - (2 : ℚ) • x
  else if m = 1 then x + z - (2 : ℚ) • y
  else x + y - (2 : ℚ) • z

def F : SimpleGraph (Fin 9) where
  Adj a b := a.val % 3 ≠ b.val % 3
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

instance : DecidableRel F.Adj := fun _ _ => inferInstanceAs (Decidable (_ ≠ _))

def Tri (a b c : Fin 9) : Prop :=
  a < b ∧ b < c ∧ F.Adj a b ∧ F.Adj a c ∧ F.Adj b c

instance (a b c : Fin 9) : Decidable (Tri a b c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem F_cliqueFree : F.CliqueFree 4 := by
  classical
  by_contra hn
  let e := SimpleGraph.topEmbeddingOfNotCliqueFree hn
  have he : ∀ i j : Fin 4, i ≠ j → (e i).val % 3 ≠ (e j).val % 3 :=
    fun i j hij => e.map_rel_iff.mpr hij
  have h01 := he 0 1 (by decide)
  have h02 := he 0 2 (by decide)
  have h03 := he 0 3 (by decide)
  have h12 := he 1 2 (by decide)
  have h13 := he 1 3 (by decide)
  have h23 := he 2 3 (by decide)
  have h0 := Nat.mod_lt (e 0).val (by decide : 0 < 3)
  have h1 := Nat.mod_lt (e 1).val (by decide : 0 < 3)
  have h2 := Nat.mod_lt (e 2).val (by decide : 0 < 3)
  have h3 := Nat.mod_lt (e 3).val (by decide : 0 < 3)
  omega

theorem collapse_0 (f : Fin 9 → Fin 9 → E)
    (h : ∀ a b c, Tri a b c → defect 0 (f a b) (f a c) (f b c) = 0) :
    f 0 1 = f 0 2 := by
  have hsum : (6 : ℚ) • (f 0 1 - f 0 2) = 0 := by
    calc
      _ = (-4 : ℚ) • defect 0 (f 0 1) (f 0 2) (f 1 2) +
          (1 : ℚ) • defect 0 (f 0 1) (f 0 5) (f 1 5) +
          (2 : ℚ) • defect 0 (f 0 2) (f 0 4) (f 2 4) +
          (-1 : ℚ) • defect 0 (f 0 2) (f 0 7) (f 2 7) +
          (1 : ℚ) • defect 0 (f 0 4) (f 0 5) (f 4 5) +
          (1 : ℚ) • defect 0 (f 0 5) (f 0 7) (f 5 7) +
          (-2 : ℚ) • defect 0 (f 1 2) (f 1 3) (f 2 3) +
          (-1 : ℚ) • defect 0 (f 1 3) (f 1 5) (f 3 5) +
          (-2 : ℚ) • defect 0 (f 2 3) (f 2 4) (f 3 4) +
          (1 : ℚ) • defect 0 (f 2 3) (f 2 7) (f 3 7) +
          (-1 : ℚ) • defect 0 (f 3 4) (f 3 5) (f 4 5) +
          (-1 : ℚ) • defect 0 (f 3 5) (f 3 7) (f 5 7) := by
            norm_num [defect, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
            module
      _ = 0 := by
        rw [h 0 1 2 (by decide),
          h 0 1 5 (by decide),
          h 0 2 4 (by decide),
          h 0 2 7 (by decide),
          h 0 4 5 (by decide),
          h 0 5 7 (by decide),
          h 1 2 3 (by decide),
          h 1 3 5 (by decide),
          h 2 3 4 (by decide),
          h 2 3 7 (by decide),
          h 3 4 5 (by decide),
          h 3 5 7 (by decide)]
        simp
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsum).resolve_left (by norm_num))

theorem collapse_1 (f : Fin 9 → Fin 9 → E)
    (h : ∀ a b c, Tri a b c → defect 1 (f a b) (f a c) (f b c) = 0) :
    f 0 1 = f 0 5 := by
  have hsum : (6 : ℚ) • (f 0 1 - f 0 5) = 0 := by
    calc
      _ = (-1 : ℚ) • defect 1 (f 0 1) (f 0 2) (f 1 2) +
          (3 : ℚ) • defect 1 (f 0 1) (f 0 5) (f 1 5) +
          (4 : ℚ) • defect 1 (f 0 1) (f 0 8) (f 1 8) +
          (-2 : ℚ) • defect 1 (f 0 2) (f 0 4) (f 2 4) +
          (-4 : ℚ) • defect 1 (f 0 4) (f 0 8) (f 4 8) +
          (1 : ℚ) • defect 1 (f 1 2) (f 1 3) (f 2 3) +
          (2 : ℚ) • defect 1 (f 1 3) (f 1 5) (f 3 5) +
          (1 : ℚ) • defect 1 (f 1 5) (f 1 6) (f 5 6) +
          (2 : ℚ) • defect 1 (f 1 6) (f 1 8) (f 6 8) +
          (-1 : ℚ) • defect 1 (f 2 3) (f 2 4) (f 3 4) +
          (1 : ℚ) • defect 1 (f 3 4) (f 3 5) (f 4 5) +
          (-1 : ℚ) • defect 1 (f 4 5) (f 4 6) (f 5 6) +
          (-2 : ℚ) • defect 1 (f 4 6) (f 4 8) (f 6 8) := by
            norm_num [defect, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
            module
      _ = 0 := by
        rw [h 0 1 2 (by decide),
          h 0 1 5 (by decide),
          h 0 1 8 (by decide),
          h 0 2 4 (by decide),
          h 0 4 8 (by decide),
          h 1 2 3 (by decide),
          h 1 3 5 (by decide),
          h 1 5 6 (by decide),
          h 1 6 8 (by decide),
          h 2 3 4 (by decide),
          h 3 4 5 (by decide),
          h 4 5 6 (by decide),
          h 4 6 8 (by decide)]
        simp
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsum).resolve_left (by norm_num))

theorem collapse_2 (f : Fin 9 → Fin 9 → E)
    (h : ∀ a b c, Tri a b c → defect 2 (f a b) (f a c) (f b c) = 0) :
    f 2 3 = f 2 4 := by
  have hsum : (3 : ℚ) • (f 2 3 - f 2 4) = 0 := by
    calc
      _ = (-1 : ℚ) • defect 2 (f 0 1) (f 0 2) (f 1 2) +
          (1 : ℚ) • defect 2 (f 0 1) (f 0 5) (f 1 5) +
          (2 : ℚ) • defect 2 (f 0 2) (f 0 4) (f 2 4) +
          (-1 : ℚ) • defect 2 (f 0 2) (f 0 7) (f 2 7) +
          (-2 : ℚ) • defect 2 (f 0 4) (f 0 5) (f 4 5) +
          (1 : ℚ) • defect 2 (f 0 5) (f 0 7) (f 5 7) +
          (-1 : ℚ) • defect 2 (f 1 2) (f 1 3) (f 2 3) +
          (-1 : ℚ) • defect 2 (f 1 2) (f 1 6) (f 2 6) +
          (1 : ℚ) • defect 2 (f 1 3) (f 1 5) (f 3 5) +
          (1 : ℚ) • defect 2 (f 1 5) (f 1 6) (f 5 6) +
          (1 : ℚ) • defect 2 (f 2 3) (f 2 4) (f 3 4) +
          (-2 : ℚ) • defect 2 (f 2 6) (f 2 7) (f 6 7) +
          (2 : ℚ) • defect 2 (f 3 4) (f 3 5) (f 4 5) +
          (2 : ℚ) • defect 2 (f 5 6) (f 5 7) (f 6 7) := by
            norm_num [defect, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
            module
      _ = 0 := by
        rw [h 0 1 2 (by decide),
          h 0 1 5 (by decide),
          h 0 2 4 (by decide),
          h 0 2 7 (by decide),
          h 0 4 5 (by decide),
          h 0 5 7 (by decide),
          h 1 2 3 (by decide),
          h 1 2 6 (by decide),
          h 1 3 5 (by decide),
          h 1 5 6 (by decide),
          h 2 3 4 (by decide),
          h 2 6 7 (by decide),
          h 3 4 5 (by decide),
          h 5 6 7 (by decide)]
        simp
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsum).resolve_left (by norm_num))

theorem no_fixed_midpoint (m : Fin 3) (f : Fin 9 → Fin 9 → E)
    (h : ∀ a b c, Tri a b c → defect m (f a b) (f a c) (f b c) = 0)
    (hne : ∀ a b c, Tri a b c → f a b ≠ f a c) : False := by
  fin_cases m
  · exact hne 0 1 2 (by decide) (collapse_0 f h)
  · exact hne 0 1 5 (by decide) (collapse_1 f h)
  · exact hne 2 3 4 (by decide) (collapse_2 f h)

section Transfer
variable {V : Type*} [LinearOrder V]

def OrderedTriangle (G : SimpleGraph V) (a b c : V) : Prop :=
  a < b ∧ b < c ∧ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c

/-- The usual ordered triangle Ramsey property for the finite graph F. -/
def TriangleRamsey (G : SimpleGraph V) : Prop :=
  ∀ col : V → V → V → Fin 3, ∃ i : Fin 9 → V, StrictMono i ∧
    (∀ a b, F.Adj a b → G.Adj (i a) (i b)) ∧
    ∃ m, ∀ a b c, Tri a b c → col (i a) (i b) (i c) = m

/-- A nonconstant arithmetic-progression assignment would color triangles
by their midpoint position, contradicting a homogeneous copy of F. -/
theorem no_AP_assignment_of_ramsey (G : SimpleGraph V) (hG : TriangleRamsey G)
    (f : V → V → E)
    (hf : ∀ a b c, OrderedTriangle G a b c →
      f a b ≠ f a c ∧ ∃ m : Fin 3, defect m (f a b) (f a c) (f b c) = 0) : False := by
  classical
  let col : V → V → V → Fin 3 := fun a b c =>
    if h : OrderedTriangle G a b c then (hf a b c h).2.choose else 0
  obtain ⟨i,hi,hadj,m,hm⟩ := hG col
  have ht : ∀ a b c, Tri a b c → OrderedTriangle G (i a) (i b) (i c) := by
    rintro a b c ⟨hab,hbc,hab',hac',hbc'⟩
    exact ⟨hi hab,hi hbc,hadj a b hab',hadj a c hac',hadj b c hbc'⟩
  apply no_fixed_midpoint m (fun a b => f (i a) (i b))
  · intro a b c h
    have hmid := (hf (i a) (i b) (i c) (ht a b c h)).2.choose_spec
    have hc : col (i a) (i b) (i c) =
        (hf (i a) (i b) (i c) (ht a b c h)).2.choose := by
      simp only [col, dif_pos (ht a b c h)]
    rw [← hc, hm a b c h] at hmid
    exact hmid
  · intro a b c h
    exact (hf (i a) (i b) (i c) (ht a b c h)).1

end Transfer

#print axioms F_cliqueFree
#print axioms no_fixed_midpoint
#print axioms no_AP_assignment_of_ramsey
end Erdos595ArithmeticProgression
