import Submission.FractionalCyclePartition

/-! Rational feasibility of finite rational linear inequalities, proved by
Fourier--Motzkin elimination. This is not an integral-rounding theorem. -/
open scoped Classical BigOperators
namespace Erdos184.RationalLinearFeasibility
set_option maxHeartbeats 1000000

lemma normalized_pos {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a y c b : K} (ha : 0 < a) :
    a*y+c ≤ b ↔ y ≤ b/a-c/a := by
  rw [← sub_div,le_div_iff₀ ha]
  constructor <;> intro h <;> nlinarith

lemma normalized_neg {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a y c b : K} (ha : a < 0) :
    a*y+c ≤ b ↔ b/a-c/a ≤ y := by
  rw [← sub_div,div_le_iff_of_neg ha]
  constructor <;> intro h <;> nlinarith

lemma between_finite_bounds {I J : Type*} [Fintype I] [Fintype J]
    (l : I → ℚ) (u : J → ℚ) (h : ∀ i j, l i ≤ u j) :
    ∃ q : ℚ, (∀ i, l i ≤ q) ∧ ∀ j, q ≤ u j := by
  cases isEmpty_or_nonempty I with
  | inl hI =>
    haveI := hI
    cases isEmpty_or_nonempty J with
    | inl hJ =>
      haveI := hJ
      exact ⟨0,fun i => isEmptyElim i,fun j => isEmptyElim j⟩
    | inr hJ =>
      haveI := hJ
      obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ u Finset.univ_nonempty
      exact ⟨u j,fun i => isEmptyElim i,fun k => hj k (Finset.mem_univ _)⟩
  | inr hI =>
    haveI := hI
    obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ l Finset.univ_nonempty
    exact ⟨l i,fun k => hi k (Finset.mem_univ _),h i⟩

lemma normalized_sum_real {I : Type*} [Fintype I] (a : I → ℚ) (d : ℚ) (x : I → ℝ) :
    (∑ j, ((a j / d : ℚ) : ℝ) * x j) = (∑ j, (a j : ℝ) * x j)/(d : ℝ) := by
  simp only [Rat.cast_div,div_mul_eq_mul_div,Finset.sum_div]

lemma normalized_sum_rat {I : Type*} [Fintype I] (a : I → ℚ) (d : ℚ) (x : I → ℚ) :
    (∑ j, (a j / d) * x j) = (∑ j, a j * x j)/d := by
  simp only [div_mul_eq_mul_div,Finset.sum_div]

/-- No irrational witness is needed for a feasible finite rational system. -/
theorem exists_rat_solution (n : ℕ) {I : Type*} [Fintype I]
    (A : I → Fin n → ℚ) (b : I → ℚ)
    (h : ∃ x : Fin n → ℝ, ∀ i, (∑ j, (A i j : ℝ) * x j) ≤ (b i : ℝ)) :
    ∃ q : Fin n → ℚ, ∀ i, (∑ j, A i j * q j) ≤ b i := by
  induction n generalizing I with
  | zero =>
    obtain ⟨x,hx⟩ := h
    refine ⟨fun j => Fin.elim0 j,?_⟩
    intro i
    have hh := hx i
    simpa using hh
  | succ n ih =>
    obtain ⟨x,hx⟩ := h
    let Z := {i : I // A i 0 = 0}
    let N := {i : I // A i 0 < 0}
    let P := {i : I // 0 < A i 0}
    let J := Z ⊕ (N × P)
    let B : J → Fin n → ℚ := fun i j => match i with
      | .inl i => A i.val j.succ
      | .inr i => A i.2.val j.succ / A i.2.val 0 - A i.1.val j.succ / A i.1.val 0
    let c : J → ℚ := fun i => match i with
      | .inl i => b i.val
      | .inr i => b i.2.val / A i.2.val 0 - b i.1.val / A i.1.val 0
    have hnorm (i : I) : (A i 0 : ℝ) * x 0 +
        (∑ j : Fin n, (A i j.succ : ℝ) * x j.succ) ≤ (b i : ℝ) := by
      simpa only [Fin.sum_univ_succ] using hx i
    have hproj : ∃ y : Fin n → ℝ, ∀ i, (∑ j, (B i j : ℝ) * y j) ≤ (c i : ℝ) := by
      refine ⟨fun j => x j.succ,?_⟩
      intro i
      cases i with
      | inl i =>
        have hh := hnorm i.val
        simpa only [i.property,Rat.cast_zero,zero_mul,zero_add,B,c] using hh
      | inr i =>
        obtain ⟨lo,up⟩ := i
        have hl := (normalized_neg (show (A lo.val 0 : ℝ) < 0 by exact_mod_cast lo.property)).mp (hnorm lo.val)
        have hu := (normalized_pos (show (0 : ℝ) < (A up.val 0 : ℝ) by exact_mod_cast up.property)).mp (hnorm up.val)
        simp only [B,c,Rat.cast_sub,Rat.cast_div,sub_mul,Finset.sum_sub_distrib]
        rw [show (∑ j : Fin n, ((A up.val j.succ : ℝ) / (A up.val 0 : ℝ)) * x j.succ) =
            (∑ j : Fin n, (A up.val j.succ : ℝ) * x j.succ)/(A up.val 0 : ℝ) by
              simp only [div_mul_eq_mul_div,Finset.sum_div]]
        rw [show (∑ j : Fin n, ((A lo.val j.succ : ℝ) / (A lo.val 0 : ℝ)) * x j.succ) =
            (∑ j : Fin n, (A lo.val j.succ : ℝ) * x j.succ)/(A lo.val 0 : ℝ) by
              simp only [div_mul_eq_mul_div,Finset.sum_div]]
        linarith
    obtain ⟨q,hq⟩ := ih B c hproj
    let r (i : I) := b i / A i 0 - (∑ j : Fin n, A i j.succ * q j) / A i 0
    have hr : ∀ lo : N, ∀ up : P, r lo.val ≤ r up.val := by
      intro lo up
      have hh := hq (.inr (lo,up))
      simp only [B,c,sub_mul,Finset.sum_sub_distrib,normalized_sum_rat] at hh
      dsimp only [r]
      linarith
    obtain ⟨y,hylo,hyup⟩ := between_finite_bounds (fun lo : N => r lo.val) (fun up : P => r up.val) hr
    refine ⟨Fin.cons y q,?_⟩
    intro i
    simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    rcases lt_trichotomy (A i 0) 0 with hi | hi | hi
    · apply (normalized_neg hi).mpr
      exact hylo ⟨i,hi⟩
    · have hh := hq (.inl ⟨i,hi⟩)
      simpa only [B,c,hi,zero_mul,zero_add] using hh
    · apply (normalized_pos hi).mpr
      exact hyup ⟨i,hi⟩

lemma exists_rat_solution_fintype {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℚ) (b : I → ℚ)
    (h : ∃ x : J → ℝ, ∀ i, (∑ j, (A i j : ℝ) * x j) ≤ (b i : ℝ)) :
    ∃ q : J → ℚ, ∀ i, (∑ j, A i j * q j) ≤ b i := by
  let e := Fintype.equivFin J
  obtain ⟨x,hx⟩ := h
  have h' : ∃ y : Fin (Fintype.card J) → ℝ,
      ∀ i, (∑ j, (A i (e.symm j) : ℝ) * y j) ≤ (b i : ℝ) := by
    refine ⟨fun j => x (e.symm j),?_⟩
    intro i
    simpa only [e.symm.sum_comp (fun j => (A i j : ℝ) * x j)] using hx i
  obtain ⟨q,hq⟩ := exists_rat_solution (Fintype.card J) (fun i j => A i (e.symm j)) b h'
  refine ⟨fun j => q (e j),?_⟩
  intro i
  have heq : (∑ j, A i j * q (e j)) = ∑ j, A i (e.symm j) * q j := by
    exact Fintype.sum_equiv e _ _ (by intro j; simp)
  rw [heq]
  exact hq i

/-- Nonnegativity, exact equations, and a rational cost bound can all be
preserved when rationalizing a real solution. -/
lemma exists_nonnegative_rat_combination {I J : Type*} [Fintype I] [Fintype J]
    (A : I → J → ℚ) (b : I → ℚ) (K : ℚ) (x : J → ℝ)
    (hx : ∀ j, 0 ≤ x j)
    (hA : ∀ i, (∑ j, (A i j : ℝ) * x j) = (b i : ℝ))
    (hK : (∑ j, x j) ≤ (K : ℝ)) :
    ∃ q : J → ℚ, (∀ j, 0 ≤ q j) ∧
      (∀ i, (∑ j, A i j * q j) = b i) ∧ (∑ j, q j) ≤ K := by
  let L := J ⊕ ((I × Bool) ⊕ Unit)
  let B : L → J → ℚ := fun i j => match i with
    | .inl k => if j = k then -1 else 0
    | .inr (.inl (k,d)) => if d then A k j else -A k j
    | .inr (.inr _) => 1
  let c : L → ℚ := fun i => match i with
    | .inl _ => 0
    | .inr (.inl (k,d)) => if d then b k else -b k
    | .inr (.inr _) => K
  have hb : ∃ y : J → ℝ, ∀ i, (∑ j, (B i j : ℝ) * y j) ≤ (c i : ℝ) := by
    refine ⟨x,?_⟩
    intro i
    rcases i with k | ⟨k,d⟩ | u
    · simpa [B,c,apply_ite,ite_mul] using neg_nonpos.mpr (hx k)
    · cases d
      · simpa [B,c,Finset.sum_neg_distrib] using neg_le_neg (hA k).ge
      · simpa [B,c] using (hA k).le
    · simpa [B,c] using hK
  obtain ⟨q,hq⟩ := exists_rat_solution_fintype B c hb
  refine ⟨q,?_,?_,?_⟩
  · intro j
    have hh := hq (.inl j)
    simpa [B,c,ite_mul] using hh
  · intro i
    have h₁ := hq (.inr (.inl (i,true)))
    have h₂ := hq (.inr (.inl (i,false)))
    simp only [B,c,Bool.false_eq_true,if_false,neg_mul,Finset.sum_neg_distrib,if_true] at h₁ h₂
    linarith
  · simpa [B,c] using hq (.inr (.inr ()))

/-- Clear all denominators simultaneously with a positive common multiplier. -/
lemma clear_nonnegative_denominators {I : Type*} [Fintype I]
    (q : I → ℚ) (hq : ∀ i, 0 ≤ q i) :
    ∃ (m : ℕ) (k : I → ℕ), 0 < m ∧ ∀ i, (k i : ℚ) = m * q i := by
  let m : ℕ := ∏ i, (q i).den
  have hm : 0 < m := Finset.prod_pos (fun i _ => (q i).den_pos)
  let k (i : I) := (m / (q i).den) * (q i).num.toNat
  refine ⟨m,k,hm,?_⟩
  intro i
  have hd : (q i).den ∣ m := Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
  have hden : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_pos.ne'
  have hn : (((q i).num.toNat : ℕ) : ℚ) = ((q i).num : ℚ) := by
    have hh := Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hq i))
    exact_mod_cast hh
  dsimp only [k]
  rw [Nat.cast_mul,Nat.cast_div hd hden,hn]
  rw [← (q i).mul_den_eq_num]
  field_simp


end Erdos184.RationalLinearFeasibility
