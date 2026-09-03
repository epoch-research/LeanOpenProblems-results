import FormalConjecturesUtil

/-!
# Sharp finite-path Gaussian residue packing

Here `z.norm : ℤ` is the **squared** Euclidean norm of a Gaussian integer.
Coordinatewise Cauchy--Schwarz and telescoping give
`norm (x j - x i) ≤ (j-i) * ∑ k ∈ Ico i j, norm (x (k+1) - x k)`.
Consequently, strict step bounds `< C` give a strict endpoint bound
`< (j-i)^2 * C`, with no extra factor of two.

If an injective path has `m+1` vertices, all its steps have squared norm `< C`,
and `m^2 * C ≤ d.norm`, no two vertices can have the same label when equality
of their labels implies divisibility of their difference by `d`. In particular,
at most `m` labels cannot suffice. The kernel assumption is required only on
path points; the label space need not be finite for the image-cardinality API.
No positivity assumption on `C` or `m` is needed.

These are generic geometric and counting statements, with no primality
hypotheses. They are partial infrastructure, not an unrestricted Gaussian moat
result. This file neither imports nor modifies `Submission.Spec`.
-/

namespace Erdos952.ResiduePacking

open scoped BigOperators

/-- Coordinatewise Cauchy--Schwarz for Gaussian integers, using their squared
norms. This also holds for the empty sum. -/
theorem norm_finset_sum_le_card_mul_sum_norm {ι : Type*}
    (s : Finset ι) (f : ι → GaussianInt) :
    ((∑ i ∈ s, f i).norm : ℝ) ≤
      (s.card : ℝ) * ∑ i ∈ s, ((f i).norm : ℝ) := by
  have hsum : ((∑ i ∈ s, f i : GaussianInt) : ℂ) =
      ∑ i ∈ s, (f i : ℂ) := map_sum GaussianInt.toComplex f s
  have hre := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => (f i : ℂ).re)
  have him := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => (f i : ℂ).im)
  simpa only [GaussianInt.intCast_real_norm, hsum, Complex.normSq_apply,
    Complex.re_sum, Complex.im_sum, pow_two, Finset.sum_add_distrib, mul_add]
    using add_le_add hre him

/-- The same finite-sum estimate entirely in `ℤ`. -/
theorem norm_finset_sum_le_card_mul_sum_norm_int {ι : Type*}
    (s : Finset ι) (f : ι → GaussianInt) :
    (∑ i ∈ s, f i).norm ≤ (s.card : ℤ) * ∑ i ∈ s, (f i).norm := by
  exact_mod_cast norm_finset_sum_le_card_mul_sum_norm s f

/-- Telescoping and Cauchy--Schwarz on a segment of a sequence. The segment
may have length zero. -/
theorem norm_sub_le_length_mul_sum_step_norm (x : ℕ → GaussianInt)
    {i j : ℕ} (hij : i ≤ j) :
    ((x j - x i).norm : ℝ) ≤
      ((j - i : ℕ) : ℝ) * ∑ k ∈ Finset.Ico i j, ((x (k + 1) - x k).norm : ℝ) := by
  simpa only [Finset.sum_Ico_sub x hij, Nat.card_Ico] using
    norm_finset_sum_le_card_mul_sum_norm (Finset.Ico i j) (fun k => x (k + 1) - x k)

/-- Strict step bounds imply the sharp strict endpoint bound on a nonempty
segment. No injectivity or positivity assumption on `C` is needed. -/
theorem norm_sub_lt_length_sq_mul_of_steps_lt (x : ℕ → GaussianInt)
    {i j : ℕ} {C : ℝ} (hij : i < j)
    (hstep : ∀ k ∈ Finset.Ico i j, ((x (k + 1) - x k).norm : ℝ) < C) :
    ((x j - x i).norm : ℝ) < ((j - i : ℕ) : ℝ) ^ 2 * C := by
  have hlen : (0 : ℝ) < ((j - i : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hij
  have hsum : (∑ k ∈ Finset.Ico i j, ((x (k + 1) - x k).norm : ℝ)) <
      ((j - i : ℕ) : ℝ) * C := by
    simpa only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] using
      Finset.sum_lt_sum_of_nonempty
        (show (Finset.Ico i j).Nonempty from ⟨i, Finset.mem_Ico.mpr ⟨le_rfl, hij⟩⟩)
        hstep
  calc
    ((x j - x i).norm : ℝ) ≤
        ((j - i : ℕ) : ℝ) * ∑ k ∈ Finset.Ico i j, ((x (k + 1) - x k).norm : ℝ) :=
      norm_sub_le_length_mul_sum_step_norm x hij.le
    _ < ((j - i : ℕ) : ℝ) * (((j - i : ℕ) : ℝ) * C) :=
      mul_lt_mul_of_pos_left hsum hlen
    _ = ((j - i : ℕ) : ℝ) ^ 2 * C := by ring

/-- Every nonempty subsegment of the first `m` steps has endpoint squared
norm `< m^2 * C`. Positivity of `C` follows from the step at `i`. -/
theorem norm_sub_lt_sq_mul_of_steps_lt (x : ℕ → GaussianInt)
    {m i j : ℕ} {C : ℝ} (hij : i < j) (hjm : j ≤ m)
    (hstep : ∀ k < m, ((x (k + 1) - x k).norm : ℝ) < C) :
    ((x j - x i).norm : ℝ) < (m : ℝ) ^ 2 * C := by
  have hC : 0 < C := lt_of_le_of_lt
    (by exact_mod_cast GaussianInt.norm_nonneg (x (i + 1) - x i))
    (hstep i (hij.trans_le hjm))
  have hlen : ((j - i : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.sub_le j i).trans hjm
  have hsq : ((j - i : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ ((j - i : ℕ) : ℝ) by positivity]
  exact (norm_sub_lt_length_sq_mul_of_steps_lt x hij
    (fun k hk => hstep k ((Finset.mem_Ico.mp hk).2.trans_le hjm))).trans_le
      (mul_le_mul_of_nonneg_right hsq hC.le)

/-- The sharp endpoint estimate in the `Fin (m+1)` path API. -/
theorem fin_norm_sub_lt_sq_mul_of_steps_lt {m : ℕ} (x : Fin (m + 1) → GaussianInt)
    {C : ℝ} {i j : Fin (m + 1)} (hij : i < j)
    (hstep : ∀ k : Fin m, ((x k.succ - x k.castSucc).norm : ℝ) < C) :
    ((x j - x i).norm : ℝ) < (m : ℝ) ^ 2 * C := by
  let y : ℕ → GaussianInt := fun n => if h : n < m + 1 then x ⟨n, h⟩ else 0
  have hy (k : Fin (m + 1)) : y k.val = x k := by
    dsimp only [y]
    rw [dif_pos k.isLt]
  have hstep' : ∀ k < m, ((y (k + 1) - y k).norm : ℝ) < C := by
    intro k hk
    simpa only [← hy (Fin.succ ⟨k, hk⟩), ← hy (Fin.castSucc ⟨k, hk⟩)] using
      hstep ⟨k, hk⟩
  simpa only [hy] using
    norm_sub_lt_sq_mul_of_steps_lt y (show i.val < j.val from hij)
      (Nat.le_of_lt_succ j.isLt) hstep'

/-- A nonzero Gaussian multiple of a nonzero `d` has squared norm at least
`d.norm`: its nonzero quotient has positive integral norm, hence norm at least one. -/
theorem norm_le_norm_of_dvd {d z : GaussianInt} (hd : d ≠ 0) (hz : z ≠ 0)
    (hdiv : d ∣ z) : d.norm ≤ z.norm := by
  obtain ⟨q, rfl⟩ := hdiv
  have hq : q ≠ 0 := by
    intro h
    apply hz
    simp [h]
  have hqnorm : 1 ≤ q.norm := GaussianInt.norm_pos.mpr hq
  simpa only [Zsqrtd.norm_mul, mul_one] using
    mul_le_mul_of_nonneg_left hqnorm (GaussianInt.norm_pos.mpr hd).le

/-- Pigeonhole obstruction for an injective finite path with at most `m`
labels in its image. The label space can be infinite, and the divisibility
hypothesis is imposed only on pairs of path vertices. -/
theorem false_of_residue_image_card_le {α : Type*} [DecidableEq α]
    {m : ℕ} {d : GaussianInt} {C : ℝ} (hd : d ≠ 0)
    (x : Fin (m + 1) → GaussianInt) (hx : Function.Injective x)
    (r : GaussianInt → α)
    (hcard : (Finset.univ.image (fun i => r (x i))).card ≤ m)
    (hkernel : ∀ i j, r (x i) = r (x j) → d ∣ (x i - x j))
    (hstep : ∀ i : Fin m, ((x i.succ - x i.castSucc).norm : ℝ) < C)
    (hscale : (m : ℝ) ^ 2 * C ≤ (d.norm : ℝ)) : False := by
  have hcollision : (Finset.univ.image (fun i => r (x i))).card <
      (Finset.univ : Finset (Fin (m + 1))).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Nat.lt_succ_of_le hcard
  obtain ⟨i, _, j, _, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_image_lt hcollision
  have impossible (a b : Fin (m + 1)) (hab : a < b) (he : r (x a) = r (x b)) :
      False := by
    have hpoints : x b ≠ x a := fun h => (ne_of_gt hab) (hx h)
    have hlower : (d.norm : ℝ) ≤ ((x b - x a).norm : ℝ) := by
      exact_mod_cast norm_le_norm_of_dvd hd (sub_ne_zero.mpr hpoints)
        (hkernel b a he.symm)
    exact (not_lt_of_ge hlower)
      ((fin_norm_sub_lt_sq_mul_of_steps_lt x hab hstep).trans_le hscale)
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact impossible i j hij heq
  · exact impossible j i hji heq.symm

/-- With the geometric hypotheses, all `m+1` vertices have different labels. -/
theorem residue_image_card_eq_of_steps_lt {α : Type*} [DecidableEq α]
    {m : ℕ} {d : GaussianInt} {C : ℝ} (hd : d ≠ 0)
    (x : Fin (m + 1) → GaussianInt) (hx : Function.Injective x)
    (r : GaussianInt → α)
    (hkernel : ∀ i j, r (x i) = r (x j) → d ∣ (x i - x j))
    (hstep : ∀ i : Fin m, ((x i.succ - x i.castSucc).norm : ℝ) < C)
    (hscale : (m : ℝ) ^ 2 * C ≤ (d.norm : ℝ)) :
    (Finset.univ.image (fun i => r (x i))).card = m + 1 := by
  have hupper : (Finset.univ.image (fun i => r (x i))).card ≤ m + 1 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := Finset.univ) (f := fun i => r (x i)))
  by_contra hne
  exact false_of_residue_image_card_le hd x hx r (by omega) hkernel hstep hscale

/-- The requested finite-label obstruction with a real strict step bound.
It includes `m = 0`, by pigeonhole, without any separate positivity hypothesis. -/
theorem false_of_finite_labels {α : Type*} [Fintype α]
    {m : ℕ} {d : GaussianInt} {C : ℝ} (hd : d ≠ 0)
    (x : Fin (m + 1) → GaussianInt) (hx : Function.Injective x)
    (r : GaussianInt → α) (hcard : Fintype.card α ≤ m)
    (hkernel : ∀ i j, r (x i) = r (x j) → d ∣ (x i - x j))
    (hstep : ∀ i : Fin m, ((x i.succ - x i.castSucc).norm : ℝ) < C)
    (hscale : (m : ℝ) ^ 2 * C ≤ (d.norm : ℝ)) : False := by
  classical
  exact false_of_residue_image_card_le hd x hx r
    ((Finset.card_le_univ _).trans hcard) hkernel hstep hscale

/-- Positive cardinality form of the finite-label obstruction. -/
theorem card_le_of_finite_path {α : Type*} [Fintype α]
    {m : ℕ} {d : GaussianInt} {C : ℝ} (hd : d ≠ 0)
    (x : Fin (m + 1) → GaussianInt) (hx : Function.Injective x)
    (r : GaussianInt → α)
    (hkernel : ∀ i j, r (x i) = r (x j) → d ∣ (x i - x j))
    (hstep : ∀ i : Fin m, ((x i.succ - x i.castSucc).norm : ℝ) < C)
    (hscale : (m : ℝ) ^ 2 * C ≤ (d.norm : ℝ)) : m + 1 ≤ Fintype.card α := by
  by_contra h
  exact false_of_finite_labels hd x hx r (by omega) hkernel hstep hscale

/-- The finite-label obstruction with all norm inequalities in `ℤ`. -/
theorem false_of_finite_labels_int {α : Type*} [Fintype α]
    {m : ℕ} {d : GaussianInt} {C : ℤ} (hd : d ≠ 0)
    (x : Fin (m + 1) → GaussianInt) (hx : Function.Injective x)
    (r : GaussianInt → α) (hcard : Fintype.card α ≤ m)
    (hkernel : ∀ i j, r (x i) = r (x j) → d ∣ (x i - x j))
    (hstep : ∀ i : Fin m, (x i.succ - x i.castSucc).norm < C)
    (hscale : (m : ℤ) ^ 2 * C ≤ d.norm) : False := by
  apply false_of_finite_labels (C := (C : ℝ)) hd x hx r hcard hkernel
  · intro i
    exact_mod_cast hstep i
  · exact_mod_cast hscale

/-- The image-cardinality obstruction with an integral strict step bound. -/
theorem false_of_residue_image_card_le_int {α : Type*} [DecidableEq α]
    {m : ℕ} {d : GaussianInt} {C : ℤ} (hd : d ≠ 0)
    (x : Fin (m + 1) → GaussianInt) (hx : Function.Injective x)
    (r : GaussianInt → α)
    (hcard : (Finset.univ.image (fun i => r (x i))).card ≤ m)
    (hkernel : ∀ i j, r (x i) = r (x j) → d ∣ (x i - x j))
    (hstep : ∀ i : Fin m, (x i.succ - x i.castSucc).norm < C)
    (hscale : (m : ℤ) ^ 2 * C ≤ d.norm) : False := by
  apply false_of_residue_image_card_le (C := (C : ℝ)) hd x hx r hcard hkernel
  · intro i
    exact_mod_cast hstep i
  · exact_mod_cast hscale

/-- Sequence API: only the first `m+1` points must be injective, only their
label image must have cardinality at most `m`, and only the first `m` steps
and pairs of initial-segment vertices are constrained. -/
theorem false_of_initial_segment_residue_card_le {α : Type*} [DecidableEq α]
    {m : ℕ} {d : GaussianInt} {C : ℝ} (hd : d ≠ 0)
    (x : ℕ → GaussianInt) (hx : Set.InjOn x (Set.Iic m))
    (r : GaussianInt → α)
    (hcard : ((Finset.range (m + 1)).image (fun i => r (x i))).card ≤ m)
    (hkernel : ∀ i ≤ m, ∀ j ≤ m, r (x i) = r (x j) → d ∣ (x i - x j))
    (hstep : ∀ i < m, ((x (i + 1) - x i).norm : ℝ) < C)
    (hscale : (m : ℝ) ^ 2 * C ≤ (d.norm : ℝ)) : False := by
  let y : Fin (m + 1) → GaussianInt := fun i => x i.val
  have hy : Function.Injective y := by
    intro i j hij
    exact Fin.ext (hx (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) hij)
  have himage : (Finset.univ.image (fun i => r (y i))) =
      (Finset.range (m + 1)).image (fun i => r (x i)) := by
    ext a
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨i, _, hi⟩
      exact ⟨i.val, Finset.mem_range.mpr i.isLt, hi⟩
    · rintro ⟨i, hi, ha⟩
      exact ⟨⟨i, Finset.mem_range.mp hi⟩, Finset.mem_univ _, ha⟩
  apply false_of_residue_image_card_le hd y hy r (himage.symm ▸ hcard) ?_ ?_ hscale
  · intro i j hij
    exact hkernel i.val (Nat.le_of_lt_succ i.isLt) j.val (Nat.le_of_lt_succ j.isLt) hij
  · intro i
    exact hstep i.val i.isLt

namespace Tests

/-- The non-strict endpoint estimate includes a zero-length segment. -/
theorem zero_length_segment (x : ℕ → GaussianInt) (i : ℕ) :
    ((x i - x i).norm : ℝ) ≤
      ((i - i : ℕ) : ℝ) * ∑ k ∈ Finset.Ico i i, ((x (k + 1) - x k).norm : ℝ) :=
  norm_sub_le_length_mul_sum_step_norm x le_rfl

/-- `m = 0` is ruled out by the finite-label theorem itself: a singleton
path cannot be labeled in a type of cardinality zero. The bound `C = 0`
and the empty collection of steps require no positivity assumptions. -/
theorem zero_steps {α : Type*} [Fintype α]
    (r : GaussianInt → α) (hcard : Fintype.card α ≤ 0) : False := by
  apply false_of_finite_labels (m := 0) (d := 1) (C := 0) one_ne_zero
    (fun _ => 0) (fun i j _ => by apply Fin.ext; omega) r hcard
  · intro i j _
    simp
  · intro i
    exact Fin.elim0 i
  · norm_num

/-- Boundary counterexample to replacing `< C` by `≤ C`: for `m = 1`,
`d = 1+i`, `x = [0,d]`, and one constant label, all the weak-bound
hypotheses hold with `C = d.norm = 2`. The path-local kernel condition is
satisfied, and the strict step condition is false. -/
theorem equality_threshold_example :
    let d : GaussianInt := ⟨1, 1⟩
    let x : Fin 2 → GaussianInt := ![0, d]
    let r : GaussianInt → Unit := fun _ => ()
    d ≠ 0 ∧ Function.Injective x ∧ Fintype.card Unit ≤ 1 ∧
      (∀ i j, r (x i) = r (x j) → d ∣ (x i - x j)) ∧
      (∀ i : Fin 1, ((x i.succ - x i.castSucc).norm : ℝ) ≤ (d.norm : ℝ)) ∧
      (1 : ℝ) ^ 2 * (d.norm : ℝ) ≤ (d.norm : ℝ) ∧
      d.norm = 2 ∧ (x 1 - x 0).norm = d.norm ∧
      ¬ (∀ i : Fin 1, ((x i.succ - x i.castSucc).norm : ℝ) < (d.norm : ℝ)) := by
  dsimp only
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, by decide, ?_, ?_⟩
  · intro i j _
    fin_cases i <;> fin_cases j <;> simp
  · intro i
    fin_cases i
    simp
  · simp
  · simp
  · intro h
    simpa using h 0

/-- Injectivity really is needed. A constant two-vertex path has strict
step bound `< 1`, one label, and `1^2 * 1 ≤ norm (1+i)`. -/
theorem constant_path_example :
    let d : GaussianInt := ⟨1, 1⟩
    let x : Fin 2 → GaussianInt := fun _ => 0
    let r : GaussianInt → Unit := fun _ => ()
    d ≠ 0 ∧ Fintype.card Unit ≤ 1 ∧
      (∀ i j, r (x i) = r (x j) → d ∣ (x i - x j)) ∧
      (∀ i : Fin 1, ((x i.succ - x i.castSucc).norm : ℝ) < 1) ∧
      (1 : ℝ) ^ 2 * 1 ≤ (d.norm : ℝ) ∧ ¬ Function.Injective x := by
  dsimp only
  refine ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩
  · intro i j _
    simp
  · intro i
    norm_num
  · norm_num [Zsqrtd.norm]
  · intro h
    have : (0 : Fin 2) = 1 := h rfl
    exact (by decide : (0 : Fin 2) ≠ 1) this

end Tests

#print axioms norm_finset_sum_le_card_mul_sum_norm
#print axioms norm_finset_sum_le_card_mul_sum_norm_int
#print axioms norm_sub_le_length_mul_sum_step_norm
#print axioms norm_sub_lt_length_sq_mul_of_steps_lt
#print axioms norm_sub_lt_sq_mul_of_steps_lt
#print axioms fin_norm_sub_lt_sq_mul_of_steps_lt
#print axioms norm_le_norm_of_dvd
#print axioms false_of_residue_image_card_le
#print axioms residue_image_card_eq_of_steps_lt
#print axioms false_of_finite_labels
#print axioms card_le_of_finite_path
#print axioms false_of_finite_labels_int
#print axioms false_of_residue_image_card_le_int
#print axioms false_of_initial_segment_residue_card_le
#print axioms Tests.zero_length_segment
#print axioms Tests.zero_steps
#print axioms Tests.equality_threshold_example
#print axioms Tests.constant_path_example

end Erdos952.ResiduePacking
