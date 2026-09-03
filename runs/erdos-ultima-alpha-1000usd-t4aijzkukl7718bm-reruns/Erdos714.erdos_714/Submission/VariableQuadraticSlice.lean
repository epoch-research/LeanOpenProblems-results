import FormalConjecturesUtil

/-!
A structured obstruction for a varying quadratic-form candidate. A quartic
in a base-field line controls an entire sign/conjugation rectangle. This file
does not assert a solution of Erdős 714 or a uniform finite-field specialization.
-/
noncomputable section
open SimpleGraph
namespace Erdos714VariableQuadratic
variable {E : Type*} [Field E] [CharP E 3]

def norm (τ : E →+* E) (x : E) : E := x*τ x

def relation (τ : E →+* E) (x z : E) : Prop :=
  norm τ z ≠ 1 ∧ norm τ (x+z*τ x) = 1+(norm τ z)^2

def graph (τ : E →+* E) : SimpleGraph ((E × E) ⊕ (E × E)) where
  Adj a b := match a,b with
    | .inl x, .inr y => relation τ (x.1+y.1) (x.2+y.2)
    | .inr y, .inl x => relation τ (x.1+y.1) (x.2+y.2)
    | _,_ => False
  symm := by intro a b; cases a <;> cases b <;> exact id
  loopless := by intro a; cases a <;> exact not_false

omit [CharP E 3] in
lemma norm_pair (τ : E →+* E) (i a b : E) (hi : i^2 = -1)
    (hτi : τ i = -i) (ha : τ a = a) (hb : τ b = b) :
    norm τ (a+b*i) = a^2+b^2 := by
  simp only [norm, map_add, map_mul, ha, hb, hτi]
  linear_combination -b^2*hi

omit [CharP E 3] in
lemma norm_neg (τ : E →+* E) (x : E) : norm τ (-x) = norm τ x := by
  simp [norm]

omit [CharP E 3] in
lemma relation_neg (τ : E →+* E) (x z : E) : relation τ (-x) z ↔ relation τ x z := by
  unfold relation
  rw [map_neg, show -x+z*(-τ x) = -(x+z*τ x) by ring, norm_neg]

omit [CharP E 3] in
lemma norm_conjugate (τ : E →+* E) (hτ : Function.Involutive τ) (x : E) :
    norm τ (τ x) = norm τ x := by
  simp only [norm, hτ x]
  ring

omit [CharP E 3] in
lemma relation_conjugate (τ : E →+* E) (hτ : Function.Involutive τ) (x z : E) :
    relation τ (τ x) (τ z) ↔ relation τ x z := by
  unfold relation
  rw [norm_conjugate τ hτ]
  have hh : τ x+τ z*τ (τ x) = τ (x+z*τ x) := by simp
  rw [hh, norm_conjugate τ hτ]

omit [CharP E 3] in
/-- The varying form is genuinely nonsingular on the stated open set. -/
lemma transform_injective (τ : E →+* E) (hτ : Function.Involutive τ)
    (z : E) (hz : norm τ z ≠ 1) : Function.Injective (fun x => x+z*τ x) := by
  intro x y h
  have hh := congrArg τ h
  simp only [map_add, map_mul, hτ x, hτ y] at hh
  have hprod : (1-norm τ z)*(x-y) = 0 := by
    unfold norm
    linear_combination h-z*hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hz.symm))

omit [CharP E 3] in
lemma transform_bijective [Finite E] (τ : E →+* E) (hτ : Function.Involutive τ)
    (z : E) (hz : norm τ z ≠ 1) : Function.Bijective (fun x => x+z*τ x) :=
  ⟨transform_injective τ hτ z hz, Finite.surjective_of_injective (transform_injective τ hτ z hz)⟩

/-- This is the actual one-variable eliminant for the displayed rows, not a
generic degree argument for arbitrary common neighborhoods. -/
def quartic (b c t : E) : E := t^4+(c^2-b^2)*t^2+b^4+1+c^2*(b+1)^2

lemma slice_equation (τ : E →+* E) (i b c t : E) (hi : i^2 = -1)
    (hτi : τ i = -i) (hb : τ b = b) (hc : τ c = c) (ht : τ t = t) :
    relation τ (c*(1+i)) (t+b*i) ↔ t^2+b^2 ≠ 1 ∧ quartic b c t = 0 := by
  have hz := norm_pair τ i t b hi hτi ht hb
  have hx : c*(1+i)+(t+b*i)*τ (c*(1+i)) =
      c*(1+t+b)+c*(1-t+b)*i := by
    simp only [map_mul, map_add, map_one, hc, hτi]
    linear_combination -b*c*hi
  have hnorm : norm τ (c*(1+i)+(t+b*i)*τ (c*(1+i))) =
      (c*(1+t+b))^2+(c*(1-t+b))^2 := by
    rw [hx]
    exact norm_pair τ i _ _ hi hτi (by simp [hb,hc,ht]) (by simp [hb,hc,ht])
  have h3 : (3 : E) = 0 := CharP.cast_eq_zero E 3
  have hid : (c*(1+t+b))^2+(c*(1-t+b))^2 - (1+(t^2+b^2)^2) =
      -quartic b c t := by
    unfold quartic
    linear_combination (c^2*(t^2+b^2+2*b+1)-t^2*b^2)*h3
  unfold relation
  rw [hz, hnorm, ← sub_eq_zero, hid, neg_eq_zero]

/-- The four neighbors come from independent sign and conjugation symmetries. -/
def columns (i b c : E) : Fin 4 → E × E :=
  ![(c*(1+i),b*i), (-c*(1+i),b*i), (c*(1-i),-b*i), (-c*(1-i),-b*i)]

lemma columns_injective (i b c : E) (hi : i^2 = -1) (hb : b ≠ 0) (hc : c ≠ 0) :
    Function.Injective (columns i b c) := by
  have h2 : (2 : E) ≠ 0 := by
    intro h
    have h3 : (3 : E) = 0 := CharP.cast_eq_zero E 3
    apply one_ne_zero (α := E)
    linear_combination h3-h
  have hi0 : i ≠ 0 := by intro h; simp [h] at hi
  have hi1 : 1+i ≠ 0 := by
    intro h
    have hh : i = -1 := by linear_combination h
    rw [hh] at hi
    norm_num only [neg_one_sq, one_pow] at hi
    apply h2
    linear_combination hi
  have hi2 : 1-i ≠ 0 := by
    intro h
    have hh : i = 1 := by linear_combination -h
    rw [hh] at hi
    norm_num only [neg_one_sq, one_pow] at hi
    apply h2
    linear_combination hi
  have hp (x : E) (hx : x ≠ 0) : x ≠ -x := by
    intro h
    apply mul_ne_zero h2 hx
    linear_combination h
  have huv := hp (b*i) (mul_ne_zero hb hi0)
  have hu := hp (c*(1+i)) (mul_ne_zero hc hi1)
  have hv := hp (c*(1-i)) (mul_ne_zero hc hi2)
  intro j k h
  fin_cases j <;> fin_cases k <;>
    simp only [columns, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Prod.mk.injEq, neg_mul] at h
  all_goals first
    | rfl
    | exact (hu h.1).elim
    | exact (hu h.1.symm).elim
    | exact (hv h.1).elim
    | exact (hv h.1.symm).elim
    | exact (huv h.2).elim
    | exact (huv h.2.symm).elim

/-- Four distinct fixed scalars satisfying the quartic and the open condition
supply a genuine injective K44 copy in the original varying-form graph. -/
def quarticCopy (τ : E →+* E) (hτ : Function.Involutive τ)
    (i b c : E) (hi : i^2 = -1) (hτi : τ i = -i)
    (hb : τ b = b) (hc : τ c = c) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (t : Fin 4 ↪ E) (ht : ∀ j, τ (t j) = t j)
    (hop : ∀ j, (t j)^2+b^2 ≠ 1) (hroot : ∀ j, quartic b c (t j) = 0) :
    Copy (completeBipartiteGraph (Fin 4) (Fin 4)) (graph τ) := by
  let L : Fin 4 ↪ E × E := ⟨fun j => (0,t j), by
    intro j k h
    exact t.injective (congrArg Prod.snd h)⟩
  let R : Fin 4 ↪ E × E := ⟨columns i b c, columns_injective i b c hi hb0 hc0⟩
  have he (j k : Fin 4) : (graph τ).Adj (.inl (L j)) (.inr (R k)) := by
    have h := (slice_equation τ i b c (t j) hi hτi hb hc (ht j)).mpr ⟨hop j,hroot j⟩
    have hn := (relation_neg τ (c*(1+i)) (t j+b*i)).mpr h
    have hconj := (relation_conjugate τ hτ (c*(1+i)) (t j+b*i)).mpr h
    have hconj' : relation τ (c*(1-i)) (t j-b*i) := by
      simpa only [map_mul, map_add, map_one, hc, hb, ht j, hτi, mul_neg, sub_eq_add_neg] using hconj
    have hconjneg := (relation_neg τ (c*(1-i)) (t j-b*i)).mpr hconj'
    fin_cases k
    · simpa [graph, L, R, columns] using h
    · simpa [graph, L, R, columns, neg_mul] using hn
    · simpa [graph, L, R, columns, sub_eq_add_neg] using hconj'
    · simpa [graph, L, R, columns, sub_eq_add_neg, neg_mul] using hconjneg
  refine ⟨⟨L.sumMap R, ?_⟩,(L.sumMap R).injective⟩
  intro x y hxy
  cases x with
  | inl j =>
    cases y with
    | inl k => simp at hxy
    | inr k => exact he j k
  | inr k =>
    cases y with
    | inr j => simp at hxy
    | inl j => exact (he j k).symm

#print axioms transform_injective
#print axioms transform_bijective
#print axioms norm_pair
#print axioms slice_equation
#print axioms columns_injective
#print axioms quarticCopy
end Erdos714VariableQuadratic
