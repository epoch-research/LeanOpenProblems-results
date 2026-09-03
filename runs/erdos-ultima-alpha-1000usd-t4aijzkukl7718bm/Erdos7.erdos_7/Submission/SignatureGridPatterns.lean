import Submission.PrimePowerBoxRealization

/-! Finite pattern data for testing injective charges from signature events.
The grid is not a covering system of integers. -/
namespace Erdos7SignatureGridPatterns
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

abbrev Coord := Fin 3
abbrev Grid := Coord → Fin 14
abbrev Choice := Coord → Fin 2 → Fin 7
abbrev Cell := (u : Fin 74) × Fin (74 - u.val)
abbrev DegreePattern := (u : Fin 83) × (v : Fin (83 - u.val)) × Fin (83 - u.val - v.val)

def zeroPattern : DegreePattern := ⟨⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩⟩
abbrev Pattern := {d : DegreePattern // d ≠ zeroPattern}

lemma cell_card : Fintype.card Cell = 2775 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  decide +kernel

lemma degreePattern_card : Fintype.card DegreePattern = 98770 := by
  rw [Fintype.card_sigma]
  simp_rw [Fintype.card_sigma, Fintype.card_fin]
  decide +kernel

lemma pattern_card_le : Fintype.card Pattern ≤ 98770 := by
  rw [← degreePattern_card]
  exact Fintype.card_subtype_le _

lemma grid_card : Fintype.card Grid = 2744 := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  decide

lemma choice_card : Fintype.card Choice = 117649 := by
  simp only [Choice, Fintype.card_fun, Fintype.card_fin]
  norm_num

/-- Only a finite cardinality comparison is used to assign distinct grid
points to constant-total-degree exponent triples. -/
noncomputable def gridCell : Grid ↪ Cell := Classical.choice
  (Function.Embedding.nonempty_of_card_le (by rw [grid_card, cell_card]; decide))

def exponentRaw (d : DegreePattern) : Coord → ℕ := ![d.1.val, d.2.1.val, d.2.2.val]
def exponent (d : Pattern) : Coord → ℕ := exponentRaw d.val

lemma exponentRaw_sum (d : DegreePattern) : ∑ i, exponentRaw d i ≤ 82 := by
  have h₀ := d.1.isLt
  have h₁ := d.2.1.isLt
  have h₂ := d.2.2.isLt
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, exponentRaw,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  omega

lemma exponentRaw_injective : Function.Injective exponentRaw := by
  intro d e h
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  have h₂ := congrFun h 2
  rcases d with ⟨u, v, w⟩
  rcases e with ⟨u', v', w'⟩
  dsimp [exponentRaw] at h₀ h₁ h₂
  have hu : u = u' := Fin.ext h₀
  subst u'
  have hv : v = v' := Fin.ext h₁
  subst v'
  have hw : w = w' := Fin.ext h₂
  subst w'
  rfl

lemma exponent_injective : Function.Injective exponent := by
  intro d e h
  exact Subtype.ext (exponentRaw_injective h)

lemma exponent_nonzero (d : Pattern) : ∃ i, exponent d i ≠ 0 := by
  by_contra! h
  apply d.property
  apply exponentRaw_injective
  funext i
  have hh := h i
  fin_cases i <;> simpa [exponent, exponentRaw, zeroPattern] using hh

lemma exists_pattern_of_bound (f : Coord → ℕ) (hsum : ∑ i, f i ≤ 82)
    (hf : ∃ i, f i ≠ 0) : ∃ d : Pattern, exponent d = f := by
  have hs : f 0 + f 1 + f 2 ≤ 82 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hsum
  let d : DegreePattern := ⟨⟨f 0, by omega⟩,
    ⟨f 1, by change f 1 < 83 - f 0; omega⟩,
    ⟨f 2, by change f 2 < 83 - f 0 - f 1; omega⟩⟩
  have he : exponentRaw d = f := by funext i; fin_cases i <;> rfl
  have hn : d ≠ zeroPattern := by
    intro h
    obtain ⟨i, hi⟩ := hf
    apply hi
    have hh := congrFun he i
    rw [h] at hh
    fin_cases i <;> simpa [exponentRaw, zeroPattern] using hh.symm
  exact ⟨⟨d, hn⟩, he⟩

lemma exponent_bound (d : Pattern) (i : Coord) : exponent d i ≤ 82 := by
  have hh := exponentRaw_sum d.val
  have hi : exponent d i ≤ ∑ j, exponent d j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  exact hi.trans hh

def prime : Coord → ℕ := ![3, 5, 7]
def depth : Coord → ℕ := ![4, 3, 2]

lemma prime_properties : Function.Injective prime ∧ ∀ i, (prime i).Prime ∧ Odd (prime i) ∧ 3 ≤ prime i := by
  decide +kernel

/-- The support-three antichain has degree82, leaving all smaller patterns
available for divisor closure. -/
noncomputable def gridPattern (g : Grid) : Pattern := by
  let c := gridCell g
  have hu := c.1.isLt
  have hv := c.2.isLt
  let d : DegreePattern :=
    ⟨⟨4 + c.1.val, by omega⟩,
      ⟨3 + c.2.val, by change 3 + c.2.val < 83 - (4 + c.1.val); omega⟩,
      ⟨2 + (73 - c.1.val - c.2.val), by
        change 2 + (73 - c.1.val - c.2.val) < 83 - (4 + c.1.val) - (3 + c.2.val)
        omega⟩⟩
  exact ⟨d, by
    intro h
    have he := congrArg (fun d : DegreePattern => d.1.val) h
    dsimp [d, zeroPattern] at he
    omega⟩

lemma gridPattern_exponent (g : Grid) : exponent (gridPattern g) =
    ![4 + (gridCell g).1.val, 3 + (gridCell g).2.val,
      2 + (73 - (gridCell g).1.val - (gridCell g).2.val)] := rfl

lemma gridPattern_injective : Function.Injective gridPattern := by
  intro g h he
  apply gridCell.injective
  have hx := congrArg exponent he
  rw [gridPattern_exponent, gridPattern_exponent] at hx
  have hu := congrFun hx 0
  have hv := congrFun hx 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.add_left_cancel_iff] at hu hv
  apply Sigma.ext (Fin.ext hu)
  exact (Fin.heq_ext_iff (by rw [hu])).mpr hv

lemma gridPattern_bounds (g : Grid) :
    (∀ i, depth i ≤ exponent (gridPattern g) i) ∧
      ∑ i, exponent (gridPattern g) i = 82 := by
  have hu := (gridCell g).1.isLt
  have hv := (gridCell g).2.isLt
  rw [gridPattern_exponent]
  constructor
  · intro i
    fin_cases i <;> simp [depth]
  · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    omega

lemma choice_count_gt_patterns : Fintype.card Pattern < Fintype.card Choice := by
  rw [choice_card]
  have := pattern_card_le
  omega

#print axioms gridCell
#print axioms gridPattern_injective
#print axioms gridPattern_bounds
#print axioms choice_count_gt_patterns
end Erdos7SignatureGridPatterns
