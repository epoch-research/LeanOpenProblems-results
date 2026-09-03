import FormalConjecturesUtil

/-! Divisor-closed irredundant completion of a uniform-width box family.
The family is deliberately noncovering. This is a structural test construction,
not an odd-covering witness. -/
namespace Erdos7UniformSupportCompletion
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

section
variable {I J : Type*} [Fintype I] [DecidableEq I]

abbrev Index (w : ℕ) := J ⊕ {s : Finset I // s.Nonempty ∧ s.card < w}

def support (w : ℕ) (S : J → Finset I) (k : Index (I := I) (J := J) w) : Finset I :=
  match k with | .inl j => S j | .inr s => s.val

def residue (w : ℕ) (b : J → I → Fin 2) (k : Index (I := I) (J := J) w) (i : I) : ℤ :=
  match k with | .inl j => (b j i).val-2 | .inr s => (s.val.card : ℤ)-1

lemma support_nonempty (w : ℕ) (hw : 0 < w) (S : J → Finset I)
    (hS : ∀ j, (S j).card = w) (k : Index (I := I) (J := J) w) :
    (support w S k).Nonempty := by
  cases k with
  | inl j => exact Finset.card_pos.mp (by simpa only [support,hS] using hw)
  | inr s => exact s.property.1

lemma support_card_le (w : ℕ) (S : J → Finset I) (hS : ∀ j, (S j).card = w)
    (k : Index (I := I) (J := J) w) : (support w S k).card ≤ w := by
  cases k with
  | inl j => exact (hS j).le
  | inr s => exact s.property.2.le

lemma support_injective (w : ℕ) (S : J → Finset I) (hS : ∀ j, (S j).card = w)
    (hinj : Function.Injective S) : Function.Injective (support w S) := by
  intro k l h
  cases k with
  | inl j =>
    cases l with
    | inl t => exact congrArg Sum.inl (hinj h)
    | inr t =>
      have hh := congrArg Finset.card h
      have ht := t.property.2
      simp only [support,hS] at hh
      omega
  | inr s =>
    cases l with
    | inl t =>
      have hh := congrArg Finset.card h
      have hs := s.property.2
      simp only [support,hS] at hh
      omega
    | inr t => exact congrArg Sum.inr (Subtype.ext h)

lemma residue_bounds (w : ℕ) (hw : 0 < w) (b : J → I → Fin 2)
    (k : Index (I := I) (J := J) w) (i : I) :
    -2 ≤ residue w b k i ∧ residue w b k i < (w : ℤ)-1 := by
  cases k with
  | inl j => have := (b j i).isLt; simp only [residue]; omega
  | inr s =>
    have hs := Finset.card_pos.mpr s.property.1
    have ht := s.property.2
    simp only [residue]
    omega

def privatePoint (w : ℕ) (S : J → Finset I) (b : J → I → Fin 2)
    (k : Index (I := I) (J := J) w) (i : I) : ℤ :=
  if i ∈ support w S k then residue w b k i else -3

/-- Every completed box has a private point, even when the original Boolean
family is extremely redundant. The extra symbol -3 outside its support isolates
it from incomparable supports; rank labels distinguish comparable supports. -/
theorem private_points (w : ℕ) (hw : 0 < w) (S : J → Finset I)
    (hS : ∀ j, (S j).card = w) (hinj : Function.Injective S) (b : J → I → Fin 2)
    (k l : Index (I := I) (J := J) w) :
    (∀ i ∈ support w S l, privatePoint w S b k i = residue w b l i) ↔ l = k := by
  constructor
  · intro h
    have hsub : support w S l ⊆ support w S k := by
      intro i hi
      by_contra hn
      have hh := h i hi
      simp only [privatePoint, if_neg hn] at hh
      have hb := (residue_bounds w hw b l i).1
      omega
    have heq (i : I) (hi : i ∈ support w S l) : residue w b k i = residue w b l i := by
      simpa only [privatePoint, if_pos (hsub hi)] using h i hi
    obtain ⟨i,hi⟩ := support_nonempty w hw S hS l
    cases k with
    | inl j =>
      cases l with
      | inl t =>
        apply congrArg Sum.inl
        apply hinj
        exact Finset.eq_of_subset_of_card_le hsub (by simp [hS])
      | inr t =>
        have hh := heq i hi
        have hc := Finset.card_pos.mpr t.property.1
        have hb := (b j i).isLt
        simp only [residue] at hh
        omega
    | inr s =>
      cases l with
      | inl t =>
        have hh := Finset.card_le_card hsub
        have hs := s.property.2
        simp only [support,hS] at hh
        omega
      | inr t =>
        have hh := heq i hi
        have hc : t.val.card = s.val.card := by simp only [residue] at hh; omega
        exact congrArg Sum.inr (Subtype.ext (Finset.eq_of_subset_of_card_le hsub hc.ge))
  · intro h
    subst l
    intro i hi
    simp [privatePoint,hi]

/-- Every nonempty subset of every support is represented. -/
theorem divisor_closed (w : ℕ) (S : J → Finset I) (hS : ∀ j, (S j).card = w)
    (k : Index (I := I) (J := J) w) (T : Finset I) (hT : T.Nonempty)
    (hsub : T ⊆ support w S k) : ∃ l, support w S l = T := by
  by_cases htw : T.card < w
  · exact ⟨.inr ⟨T,hT,htw⟩,rfl⟩
  · have hk := support_card_le w S hS k
    have he := Finset.eq_of_subset_of_card_le hsub (by omega)
    exact ⟨k,he.symm⟩

/-- The constant point -3 misses the entire completed family. -/
theorem minus_three_uncovered (w : ℕ) (hw : 0 < w) (S : J → Finset I)
    (hS : ∀ j, (S j).card = w) (b : J → I → Fin 2)
    (k : Index (I := I) (J := J) w) :
    ¬ ∀ i ∈ support w S k, (-3 : ℤ) = residue w b k i := by
  intro h
  obtain ⟨i,hi⟩ := support_nonempty w hw S hS k
  have hb := (residue_bounds w hw b k i).1
  have hh := h i hi
  omega

lemma private_bounds (w : ℕ) (hw : 0 < w) (S : J → Finset I) (b : J → I → Fin 2)
    (k : Index (I := I) (J := J) w) (i : I) :
    -3 ≤ privatePoint w S b k i ∧ privatePoint w S b k i < (w : ℤ)-1 := by
  unfold privatePoint
  split_ifs
  · have hh := residue_bounds w hw b k i; omega
  · omega

/-- Singleton classes are already normalized to residue zero. -/
lemma singleton_residue (w : ℕ) (hw : 2 ≤ w) (S : J → Finset I)
    (hS : ∀ j, (S j).card = w) (b : J → I → Fin 2)
    (k : Index (I := I) (J := J) w) (hk : (support w S k).card = 1) (i : I) :
    residue w b k i = 0 := by
  cases k with
  | inl j => simp only [support,hS] at hk; omega
  | inr s => change (s.val.card : ℤ)-1=0; change s.val.card=1 at hk; simp [hk]

end
#print axioms private_points
#print axioms divisor_closed
#print axioms minus_three_uncovered
end Erdos7UniformSupportCompletion
