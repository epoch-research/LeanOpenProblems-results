import Submission.MengerPaths

/-! First-return segments of a finite permutation and a clean-segment pigeonhole lemma. -/
open scoped Classical
namespace Erdos184.CyclicSegments
variable {V : Type*}

structure Segment (f : Equiv.Perm V) (R : Set V) (a : R) where
  length : ℕ
  pos : 0 < length
  last : (f : V → V)^[length] a.val ∈ R
  first : ∀ n, 0 < n → n < length → (f : V → V)^[n] a.val ∉ R

lemma exists_segment [Fintype V] (f : Equiv.Perm V) (R : Set V) (a : R) :
    Nonempty (Segment f R a) := by
  have hp : (f : V → V)^[orderOf f] a.val = a.val := by
    rw [← Equiv.Perm.coe_pow,pow_orderOf_eq_one]
    rfl
  have hex : ∃ n : ℕ, 0 < n ∧ (f : V → V)^[n] a.val ∈ R :=
    ⟨orderOf f,orderOf_pos f,by rw [hp]; exact a.property⟩
  refine ⟨⟨Nat.find hex,(Nat.find_spec hex).1,(Nat.find_spec hex).2,?_⟩⟩
  intro n hn hlt hR
  exact Nat.find_min hex hlt ⟨hn,hR⟩

/-- Distinct first-return arcs have disjoint interiors, including their
initial marked vertices but excluding their final marked vertices. -/
lemma before_return_injective (f : Equiv.Perm V) {R : Set V} {a b : R}
    (p : Segment f R a) (q : Segment f R b) {i j : ℕ}
    (hi : i < p.length) (hj : j < q.length)
    (he : (f : V → V)^[i] a.val = (f : V → V)^[j] b.val) : i = j ∧ a = b := by
  have aux {a b : R} (q : Segment f R b) {i j : ℕ}
      (hj : j < q.length) (hij : i ≤ j)
      (he : (f : V → V)^[i] a.val = (f : V → V)^[j] b.val) : i = j ∧ a = b := by
    have hh : a.val = (f : V → V)^[j-i] b.val := by
      apply f.injective.iterate i
      rw [← Function.iterate_add_apply]
      simpa only [Nat.add_sub_of_le hij] using he
    have hsame : i = j := by
      by_contra hn
      exact q.first (j-i) (by omega) (by omega) (hh ▸ a.property)
    subst j
    simp only [Nat.sub_self,Function.iterate_zero,Function.id_def] at hh
    exact ⟨rfl,Subtype.ext hh⟩
  by_cases hij : i ≤ j
  · exact aux q hj hij he
  · obtain ⟨h,h'⟩ := aux p hi (by omega) he.symm
    exact ⟨h.symm,h'.symm⟩

/-- In a single permutation orbit with another marked vertex, a first-return
segment cannot return to its starting point. -/
lemma last_ne_start (f : Equiv.Perm V) {R : Set V} {a : R} (p : Segment f R a)
    (htrans : ∀ x y : V, ∃ n : ℕ, (f : V → V)^[n] x = y)
    (hother : ∃ b : R, b ≠ a) : (f : V → V)^[p.length] a.val ≠ a.val := by
  intro hlast
  obtain ⟨b,hba⟩ := hother
  have hex := htrans a.val b.val
  let n := Nat.find hex
  have hn : (f : V → V)^[n] a.val = b.val := Nat.find_spec hex
  have hnpos : 0 < n := by
    by_contra! hz
    have hn0 : n = 0 := by omega
    simp only [hn0,Function.iterate_zero,Function.id_def] at hn
    exact hba (Subtype.ext hn.symm)
  have hlen : p.length ≤ n := by
    by_contra! h
    exact p.first n hnpos h (by rw [hn]; exact b.property)
  have hshort : (f : V → V)^[n-p.length] a.val = b.val := by
    rw [← hlast,← Function.iterate_add_apply,Nat.sub_add_cancel hlen]
    exact hn
  have hpos := p.pos
  exact Nat.find_min hex (show n-p.length < Nat.find hex from by dsimp [n] at *; omega) hshort

lemma vertex_injective (f : Equiv.Perm V) {R : Set V} {a : R} (p : Segment f R a)
    (hend : (f : V → V)^[p.length] a.val ≠ a.val) :
    Set.InjOn (fun n : ℕ => (f : V → V)^[n] a.val) {n | n ≤ p.length} := by
  intro i hi j hj he
  change i ≤ p.length at hi
  change j ≤ p.length at hj
  have internal {i : ℕ} (hi : i < p.length)
      (he : (f : V → V)^[i] a.val = (f : V → V)^[p.length] a.val) : False := by
    by_cases hz : i = 0
    · subst i
      exact hend he.symm
    · exact p.first i (by omega) hi (by rw [he]; exact p.last)
  by_cases hi' : i = p.length
  · by_cases hj' : j = p.length
    · omega
    · exact (internal (i := j) (by omega) (by simpa only [hi'] using he.symm)).elim
  · by_cases hj' : j = p.length
    · exact (internal (i := i) (by omega) (by simpa only [hj'] using he)).elim
    · exact (before_return_injective f p p (by omega) (by omega) he).1

lemma length_lt_card [Fintype V] (f : Equiv.Perm V) {R : Set V} {a : R} (p : Segment f R a)
    (hend : (f : V → V)^[p.length] a.val ≠ a.val) : p.length < Fintype.card V := by
  have hi : Function.Injective (fun i : Fin (p.length+1) => (f : V → V)^[i.val] a.val) := by
    intro i j hij
    apply Fin.ext
    exact vertex_injective f p hend (by change i.val ≤ p.length; omega)
      (by change j.val ≤ p.length; omega) hij
  have hh := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_fin] using hh

/-- If there are more marked starting points than forbidden internal points,
some first-return segment has no forbidden internal vertex. -/
lemma exists_clean_segment [Fintype V] (f : Equiv.Perm V) (R T : Set V)
    (p : ∀ a : R, Segment f R a) (hcard : (T \ R).ncard < R.ncard) :
    ∃ a : R, ∀ n, 0 < n → n < (p a).length → (f : V → V)^[n] a.val ∉ T := by
  by_contra! hn
  choose n hnpos hnlen hnT using hn
  let g : R → ↥(T \ R) := fun a =>
    ⟨(f : V → V)^[n a] a.val,hnT a,(p a).first (n a) (hnpos a) (hnlen a)⟩
  have hg : Function.Injective g := by
    intro a b hab
    exact (before_return_injective f (p a) (p b) (hnlen a) (hnlen b)
      (congrArg Subtype.val hab)).2
  have hh := Fintype.card_le_of_injective g hg
  simp only [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hh
  omega

end Erdos184.CyclicSegments
