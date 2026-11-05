import Submission.TreeBasic

/-! The unbounded integral short-vector theorem for the path-feedback matrix.

The key invariant permits nonnegative ghost masses supported at absorbing
leaves.  Induction visits the right child first, then adds its nonnegative
feedback source to the left child's ghost vector.  The adjusted root bound
eliminates all timeout coefficients, after which ordinary Haar splitting
leaves only zero or one signed absorbing path.
-/

namespace ErdosDSS.TreeCode

open scoped BigOperators

namespace Short

open Tree

noncomputable section

lemma sum_fork (l r : Tree) (v : (fork l r).Leaf → ℤ) :
    charge v = charge (fun a => v (Sum.inl a)) + charge (fun a => v (Sum.inr a)) := by
  simp [charge, Leaf, Fintype.sum_sum_type]

lemma charge_add {t : Tree} (v w : t.Leaf → ℤ) :
    charge (v + w) = charge v + charge w := by
  simp [charge, Finset.sum_add_distrib]

lemma charge_neg {t : Tree} (v : t.Leaf → ℤ) :
    charge (-v) = -charge v := by
  simp [charge, Finset.sum_neg_distrib]

lemma integer_split {a b : ℤ} (hs : 0 ≤ a + b) (hd : -1 ≤ a - b ∧ a - b ≤ 1) :
    0 ≤ a ∧ 0 ≤ b := by
  omega

lemma firstAbs_absorbed (t : Tree) (h : t.hasAbs = true) :
    t.absorbed t.firstAbs = true := by
  induction t with
  | tip b => simpa [hasAbs, firstAbs, absorbed] using h
  | fork l r ihl ihr =>
    by_cases hl : l.hasAbs = true
    · simpa [firstAbs, hl, absorbed] using ihl hl
    · have hl' : l.hasAbs = false := by cases hla : l.hasAbs <;> simp_all
      have hr : r.hasAbs = true := by simpa [hasAbs, hl'] using h
      simpa [firstAbs, hl', absorbed] using ihr hr

lemma lastTime_timeout (t : Tree) (h : t.hasTime = true) :
    t.absorbed t.lastTime = false := by
  induction t with
  | tip b => cases b <;> simp_all [hasTime, absorbed]
  | fork l r ihl ihr =>
    by_cases hr : r.hasTime = true
    · simpa [lastTime, hr, absorbed] using ihr hr
    · have hr' : r.hasTime = false := by cases hra : r.hasTime <;> simp_all
      have hl : l.hasTime = true := by simpa [hasTime, hr'] using h
      simpa [lastTime, hr', absorbed] using ihl hl

lemma mixed_has_both (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) :
    t.hasAbs = true ∧ t.hasTime = true := by
  induction t with
  | tip b => simp [isNode] at hn
  | fork l r ihl ihr =>
    obtain ⟨hml, hmr, hch⟩ := hm
    cases l with
    | fork ll lr =>
      obtain ⟨ha, ht⟩ := ihl hml rfl
      rw [hasAbs, hasTime, ha, ht]
      simp
    | tip a =>
      cases r with
      | fork rl rr =>
        obtain ⟨ha, ht⟩ := ihr hmr rfl
        rw [hasAbs, hasTime, ha, ht]
        simp
      | tip b =>
        have hab : a ≠ b := hch rfl rfl
        cases a <;> cases b <;> simp_all [hasAbs, hasTime]

lemma mixed_firstCherry_timeout (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) :
    t.absorbed t.firstCherry = false := by
  induction t with
  | tip b => simp [isNode] at hn
  | fork l r ihl ihr =>
    obtain ⟨hml, hmr, hch⟩ := hm
    cases l with
    | fork ll lr =>
      simpa [firstCherry, isNode, absorbed] using ihl hml rfl
    | tip a =>
      cases r with
      | fork rl rr =>
        simpa [firstCherry, isNode, absorbed] using ihr hmr rfl
      | tip b =>
        have hab : a ≠ b := hch rfl rfl
        cases a <;> cases b <;> simp_all [firstCherry, isNode, hasAbs, root, absorbed]

lemma mixed_firstAbs_absorbed (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) :
    t.absorbed t.firstAbs = true :=
  firstAbs_absorbed t (mixed_has_both t hm hn).1

lemma mixed_lastTime_timeout (t : Tree) (hm : t.Mixed) (hn : t.isNode = true) :
    t.absorbed t.lastTime = false :=
  lastTime_timeout t (mixed_has_both t hm hn).2

lemma path_root (t : Tree) (a : t.Leaf) : t.path t.root a = 1 := by
  cases t with
  | tip b => rfl
  | fork l r => simp [path, root]

lemma feedback_root (t : Tree) (a : t.Leaf) : t.feedback t.root a = 0 := by
  cases t with
  | tip b => rfl
  | fork l r => simp [feedback, root]

lemma core_root_mulVec (t : Tree) (y : t.Leaf → ℤ) :
    (t.core.mulVec y) t.root = charge y := by
  simp [core, Matrix.mulVec, dotProduct, path_root, feedback_root, charge]

lemma path_root_mulVec (t : Tree) (y : t.Leaf → ℤ) :
    (t.path.mulVec y) t.root = charge y := by
  simp [Matrix.mulVec, dotProduct, path_root, charge]

lemma path_query (l r : Tree) (v : (fork l r).Leaf → ℤ) :
    ((fork l r).path.mulVec v) (Sum.inr r.root) =
      charge (fun a => v (Sum.inl a)) - charge (fun a => v (Sum.inr a)) := by
  simp [Matrix.mulVec, dotProduct, Leaf, Fintype.sum_sum_type, path, charge,
    Finset.sum_neg_distrib, sub_eq_add_neg]

lemma feedback_query (l r : Tree) (v : (fork l r).Leaf → ℤ) :
    ((fork l r).feedback.mulVec v) (Sum.inr r.root) = 0 := by
  simp [Matrix.mulVec, dotProduct, Leaf, feedback]

lemma core_query (l r : Tree) (v : (fork l r).Leaf → ℤ) :
    ((fork l r).core.mulVec v) (Sum.inr r.root) =
      charge (fun a => v (Sum.inl a)) - charge (fun a => v (Sum.inr a)) := by
  rw [core, Matrix.add_mulVec]
  simp [path_query, feedback_query]

lemma path_left (l r : Tree) (v : (fork l r).Leaf → ℤ)
    (i : l.Leaf) (hi : i ≠ l.root) :
    ((fork l r).path.mulVec v) (Sum.inl i) =
      (l.path.mulVec (fun a => v (Sum.inl a))) i := by
  simp [Matrix.mulVec, dotProduct, Leaf, Fintype.sum_sum_type, path, hi]

lemma path_right (l r : Tree) (v : (fork l r).Leaf → ℤ)
    (i : r.Leaf) (hi : i ≠ r.root) :
    ((fork l r).path.mulVec v) (Sum.inr i) =
      (r.path.mulVec (fun a => v (Sum.inr a))) i := by
  simp [Matrix.mulVec, dotProduct, Leaf, Fintype.sum_sum_type, path, hi]

lemma feedback_right (l r : Tree) (v : (fork l r).Leaf → ℤ)
    (i : r.Leaf) (hi : i ≠ r.root) :
    ((fork l r).feedback.mulVec v) (Sum.inr i) =
      (r.feedback.mulVec (fun a => v (Sum.inr a))) i := by
  simp [Matrix.mulVec, dotProduct, Leaf, Fintype.sum_sum_type, feedback, hi]

lemma feedback_left (l r : Tree) (v : (fork l r).Leaf → ℤ)
    (i : l.Leaf) (hi : i ≠ l.root) :
    ((fork l r).feedback.mulVec v) (Sum.inl i) =
      (l.feedback.mulVec (fun a => v (Sum.inl a))) i +
        l.path i l.firstAbs * (if l.isNode && r.isNode then v (Sum.inr r.firstCherry) else 0) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Leaf, Fintype.sum_sum_type, feedback, if_neg hi]
  by_cases hb : (l.isNode && r.isNode) = true
  · simp [hb, Finset.sum_ite_eq', mul_comm]
  · have hb' : (l.isNode && r.isNode) = false := by
      cases h : (l.isNode && r.isNode) <;> simp_all
    simp [hb']

lemma core_right (l r : Tree) (v : (fork l r).Leaf → ℤ)
    (i : r.Leaf) (hi : i ≠ r.root) :
    ((fork l r).core.mulVec v) (Sum.inr i) =
      (r.core.mulVec (fun a => v (Sum.inr a))) i := by
  simp only [core, Matrix.add_mulVec, Pi.add_apply]
  rw [path_right l r v i hi, feedback_right l r v i hi]

lemma core_left (l r : Tree) (v : (fork l r).Leaf → ℤ)
    (i : l.Leaf) (hi : i ≠ l.root) :
    ((fork l r).core.mulVec v) (Sum.inl i) =
      (l.core.mulVec (fun a => v (Sum.inl a))) i +
        l.path i l.firstAbs * (if l.isNode && r.isNode then v (Sum.inr r.firstCherry) else 0) := by
  simp only [core, Matrix.add_mulVec, Pi.add_apply]
  rw [path_left l r v i hi, feedback_left l r v i hi]
  ring

/-- Only the query rows, not the distinguished mass row, are constrained. -/
def QueryTernary (t : Tree) (v : t.Leaf → ℤ) : Prop :=
  ∀ i, i ≠ t.root → -1 ≤ v i ∧ v i ≤ 1

lemma path_add_single (t : Tree) (w : t.Leaf → ℤ) (a : t.Leaf) (c : ℤ)
    (i : t.Leaf) :
    (t.path.mulVec (w + Pi.single a c)) i = (t.path.mulVec w) i + t.path i a * c := by
  classical
  simp [Matrix.mulVec]

/-- Nonnegative absorbing ghost masses propagate to nonnegative timeout
coefficients.  The right subtree is treated before the left subtree, so every
new feedback injection has a nonnegative source. -/
theorem ghost_timeout_nonneg (t : Tree) :
    t.Mixed → ∀ y w : t.Leaf → ℤ,
      (∀ a, 0 ≤ w a) →
      (∀ a, t.absorbed a = false → w a = 0) →
      0 ≤ charge y + charge w →
      QueryTernary t (t.core.mulVec y + t.path.mulVec w) →
      ∀ a, t.absorbed a = false → 0 ≤ y a := by
  induction t with
  | tip b =>
    intro hm y w hw hws hM hv a ha
    have hw0 := hws a ha
    have hyM : charge y = y a := by cases a; simp [charge, Leaf]
    have hwM : charge w = w a := by cases a; simp [charge, Leaf]
    omega
  | fork l r ihl ihr =>
    intro hm y w hw hws hM hv
    obtain ⟨hml, hmr, hch⟩ := hm
    let yL : l.Leaf → ℤ := fun a => y (Sum.inl a)
    let yR : r.Leaf → ℤ := fun a => y (Sum.inr a)
    let wL : l.Leaf → ℤ := fun a => w (Sum.inl a)
    let wR : r.Leaf → ℤ := fun a => w (Sum.inr a)
    have hsplit : 0 ≤ charge yL + charge wL ∧ 0 ≤ charge yR + charge wR := by
      have hyM := sum_fork l r y
      have hwM := sum_fork l r w
      have hq := hv (Sum.inr r.root) (by simp [root])
      simp only [Pi.add_apply, core_query, path_query] at hq
      apply integer_split
      · dsimp only [yL, yR, wL, wR]
        omega
      · dsimp only [yL, yR, wL, wR]
        constructor <;> omega
    have hright : ∀ a, r.absorbed a = false → 0 ≤ yR a := by
      apply ihr hmr yR wR
      · intro a; exact hw (Sum.inr a)
      · intro a ha; exact hws (Sum.inr a) ha
      · exact hsplit.2
      · intro i hi
        have h := hv (Sum.inr i) (by simp [root])
        simpa only [Pi.add_apply, core_right l r y i hi, path_right l r w i hi,
          yR, wR] using h
    let c : ℤ := if l.isNode && r.isNode then yR r.firstCherry else 0
    have hc : 0 ≤ c := by
      by_cases hb : (l.isNode && r.isNode) = true
      · have hnr : r.isNode = true := (Bool.and_eq_true_iff.mp hb).2
        simpa [c, hb] using hright r.firstCherry (mixed_firstCherry_timeout r hmr hnr)
      · have hb' : (l.isNode && r.isNode) = false := by
          cases h : (l.isNode && r.isNode) <;> simp_all
        simp [c, hb']
    let wL' : l.Leaf → ℤ := wL + Pi.single l.firstAbs c
    have hwL' : ∀ a, 0 ≤ wL' a := by
      intro a
      apply add_nonneg (hw (Sum.inl a))
      by_cases ha : a = l.firstAbs
      · subst a; simpa using hc
      · simp [Pi.single_eq_of_ne ha]
    have hwsL' : ∀ a, l.absorbed a = false → wL' a = 0 := by
      intro a ha
      have hw0 : wL a = 0 := hws (Sum.inl a) ha
      by_cases hn : l.isNode = true
      · have hab := mixed_firstAbs_absorbed l hml hn
        have hne : a ≠ l.firstAbs := by intro he; subst a; simp_all
        simp [wL', hw0, Pi.single_eq_of_ne hne]
      · have hn' : l.isNode = false := by cases h : l.isNode <;> simp_all
        have hc0 : c = 0 := by simp [c, hn']
        simp [wL', hw0, hc0]
    have hwL'M : charge wL' = charge wL + c := by
      classical
      simp [wL', charge, Finset.sum_add_distrib]
    have hleft : ∀ a, l.absorbed a = false → 0 ≤ yL a := by
      apply ihl hml yL wL' hwL' hwsL'
      · rw [hwL'M]
        omega
      · intro i hi
        have h := hv (Sum.inl i) (by intro he; exact hi (Sum.inl.inj he))
        simp only [Pi.add_apply, core_left l r y i hi, path_left l r w i hi] at h
        have hwl := path_add_single l wL l.firstAbs c i
        change (l.path.mulVec wL') i = (l.path.mulVec wL) i + l.path i l.firstAbs * c at hwl
        simp only [Pi.add_apply]
        rw [hwl]
        dsimp only [yL, wL, c, yR]
        constructor <;> linarith [h.1, h.2]
    intro a ha
    cases a with
    | inl a => exact hleft a ha
    | inr a => exact hright a ha

lemma adjusted_nonroot (t : Tree) (u : ℕ) (y : t.Leaf → ℤ)
    (i : t.Leaf) (hi : i ≠ t.root) :
    ((t.adjusted u).mulVec y) i = (t.core.mulVec y) i := by
  simp only [Matrix.mulVec, dotProduct, adjusted, if_neg hi, add_zero]

lemma adjusted_query_ternary (t : Tree) (u : ℕ) (y : t.Leaf → ℤ)
    (hy : Ternary ((t.adjusted u).mulVec y)) : QueryTernary t (t.core.mulVec y) := by
  intro i hi
  simpa only [adjusted_nonroot t u y i hi] using hy i

lemma ternary_neg {ι : Type*} (v : ι → ℤ) (hv : Ternary v) : Ternary (-v) := by
  intro i
  have h := hv i
  change -1 ≤ -v i ∧ -v i ≤ 1
  omega

lemma adjusted_timeout_nonneg (t : Tree) (hm : t.Mixed) (u : ℕ)
    (y : t.Leaf → ℤ) (hy : Ternary ((t.adjusted u).mulVec y))
    (hM : 0 ≤ charge y) : ∀ a, t.absorbed a = false → 0 ≤ y a := by
  apply ghost_timeout_nonneg t hm y 0
  · intro a; simp
  · intro a ha; simp
  · simpa [charge] using hM
  · simpa only [Matrix.mulVec_zero, add_zero] using adjusted_query_ternary t u y hy

/-- The ordinary Haar maximum principle, for all leaves and without any
structural restriction on the tree. -/
lemma path_coeff_nonneg (t : Tree) : ∀ y : t.Leaf → ℤ,
    0 ≤ charge y → QueryTernary t (t.path.mulVec y) → ∀ a, 0 ≤ y a := by
  induction t with
  | tip b =>
    intro y hM hv a
    have h : charge y = y a := by cases a; simp [charge, Leaf]
    omega
  | fork l r ihl ihr =>
    intro y hM hv
    let yL : l.Leaf → ℤ := fun a => y (Sum.inl a)
    let yR : r.Leaf → ℤ := fun a => y (Sum.inr a)
    have hsplit : 0 ≤ charge yL ∧ 0 ≤ charge yR := by
      have htotal := sum_fork l r y
      have hq := hv (Sum.inr r.root) (by simp [root])
      rw [path_query] at hq
      apply integer_split
      · dsimp only [yL, yR]; omega
      · exact hq
    have hleft : ∀ a, 0 ≤ yL a := by
      apply ihl yL hsplit.1
      intro i hi
      have h := hv (Sum.inl i) (by intro he; exact hi (Sum.inl.inj he))
      simpa only [path_left l r y i hi, yL] using h
    have hright : ∀ a, 0 ≤ yR a := by
      apply ihr yR hsplit.2
      intro i hi
      have h := hv (Sum.inr i) (by simp [root])
      simpa only [path_right l r y i hi, yR] using h
    intro a
    cases a with
    | inl a => exact hleft a
    | inr a => exact hright a

lemma feedback_absorbing (t : Tree) : t.Mixed → ∀ i a : t.Leaf,
    t.absorbed a = true → t.feedback i a = 0 := by
  induction t with
  | tip b => intro hm i a ha; rfl
  | fork l r ihl ihr =>
    intro hm i a ha
    obtain ⟨hml, hmr, hch⟩ := hm
    cases i with
    | inr i =>
      cases a with
      | inl a => simp [feedback]
      | inr a => simp [feedback, ihr hmr i a ha]
    | inl i =>
      cases a with
      | inl a => simp [feedback, ihl hml i a ha]
      | inr a =>
        have hsource : (l.isNode && r.isNode && decide (a = r.firstCherry)) = false := by
          by_cases hn : r.isNode = true
          · have ht := mixed_firstCherry_timeout r hmr hn
            have hne : a ≠ r.firstCherry := by intro he; subst a; simp_all [absorbed]
            simp [hne]
          · have hn' : r.isNode = false := by cases h : r.isNode <;> simp_all
            simp [hn']
        simp [feedback, hsource]

lemma adjusted_absorbing_column (t : Tree) (hm : t.Mixed) (hn : t.isNode = true)
    (u : ℕ) (a : t.Leaf) (ha : t.absorbed a = true) :
    (t.adjusted u).col a = t.path.col a := by
  have ht := mixed_lastTime_timeout t hm hn
  have hne : a ≠ t.lastTime := by intro he; subst a; simp_all
  funext i
  simp [Matrix.col, adjusted, core, feedback_absorbing t hm i a ha, ha, hne]

lemma adjusted_eq_path_of_timeout_zero (t : Tree) (hm : t.Mixed) (hn : t.isNode = true)
    (u : ℕ) (y : t.Leaf → ℤ) (hz : ∀ a, t.absorbed a = false → y a = 0) :
    (t.adjusted u).mulVec y = t.path.mulVec y := by
  classical
  funext i
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : t.absorbed a = true
  · have hcol := congrFun (adjusted_absorbing_column t hm hn u a ha) i
    change t.adjusted u i a = t.path i a at hcol
    rw [hcol]
  · have ha' : t.absorbed a = false := by cases h : t.absorbed a <;> simp_all
    simp [hz a ha']

def timeoutMass (t : Tree) (y : t.Leaf → ℤ) : ℤ :=
  ∑ a, if t.absorbed a then 0 else y a

lemma adjusted_root_mulVec (t : Tree) (u : ℕ) (y : t.Leaf → ℤ) :
    ((t.adjusted u).mulVec y) t.root =
      charge y + timeoutMass t y + 2 * (u : ℤ) * y t.lastTime := by
  classical
  simp [adjusted, Matrix.mulVec, dotProduct, core, path_root, feedback_root,
    charge, timeoutMass, add_mul, Finset.sum_add_distrib, ite_mul, add_assoc]

lemma timeoutMass_nonneg (t : Tree) (y : t.Leaf → ℤ)
    (hy : ∀ a, t.absorbed a = false → 0 ≤ y a) : 0 ≤ timeoutMass t y := by
  apply Finset.sum_nonneg
  intro a _
  cases h : t.absorbed a with
  | true => simp
  | false => simpa [h] using hy a h

lemma timeoutMass_zero (t : Tree) (y : t.Leaf → ℤ)
    (hy : ∀ a, t.absorbed a = false → 0 ≤ y a) (hs : timeoutMass t y = 0) :
    ∀ a, t.absorbed a = false → y a = 0 := by
  have hnonneg : ∀ a ∈ (Finset.univ : Finset t.Leaf),
      0 ≤ (if t.absorbed a then 0 else y a) := by
    intro a _
    cases h : t.absorbed a with
    | true => simp
    | false => simpa [h] using hy a h
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hs
  intro a ha
  simpa [ha] using hzero a (Finset.mem_univ a)

lemma nonneg_charge_zero {ι : Type*} [Fintype ι] (y : ι → ℤ)
    (hy : ∀ a, 0 ≤ y a) (hs : charge y = 0) : y = 0 := by
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hy a)).mp hs
  funext a
  exact hzero a (Finset.mem_univ a)

/-- This uses nonnegative *integer* masses, not signed-binary uniqueness. -/
lemma nonneg_charge_one {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → ℤ)
    (hy : ∀ a, 0 ≤ y a) (hs : charge y = 1) : ∃ a, y = Pi.single a 1 := by
  classical
  have hle (a : ι) : y a ≤ charge y :=
    Finset.single_le_sum (fun b _ => hy b) (Finset.mem_univ a)
  have hex : ∃ a, y a = 1 := by
    by_contra h
    have hz : y = 0 := by
      funext a
      change y a = 0
      have hna : y a ≠ 1 := fun ha => h ⟨a, ha⟩
      have ha0 := hy a
      have ha1 := hle a
      omega
    simp [hz, charge] at hs
  obtain ⟨a, ha⟩ := hex
  have hrest : ∑ b ∈ (Finset.univ : Finset ι).erase a, y b = 0 := by
    have hsum := Finset.sum_erase_add (Finset.univ : Finset ι) y (Finset.mem_univ a)
    change (∑ b ∈ (Finset.univ : Finset ι).erase a, y b) + y a = charge y at hsum
    omega
  have hrzero := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hy b)).mp hrest
  refine ⟨a, ?_⟩
  funext b
  by_cases hb : b = a
  · subst b; simp [ha]
  · rw [Pi.single_eq_of_ne hb]
    exact hrzero b (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩)

/-- With nonnegative total mass, a ternary adjusted image has either no
coefficient or exactly one absorbing coefficient equal to one. -/
theorem adjusted_positive (t : Tree) (hm : t.Mixed) (hn : t.isNode = true)
    (u : ℕ) (y : t.Leaf → ℤ) (hy : Ternary ((t.adjusted u).mulVec y))
    (hM : 0 ≤ charge y) :
    y = 0 ∨ ∃ a, t.absorbed a = true ∧ y = Pi.single a 1 := by
  have htime := adjusted_timeout_nonneg t hm u y hy hM
  have hT : 0 ≤ timeoutMass t y := timeoutMass_nonneg t y htime
  have hlast : 0 ≤ y t.lastTime := htime t.lastTime (mixed_lastTime_timeout t hm hn)
  have hU : 0 ≤ 2 * (u : ℤ) * y t.lastTime :=
    mul_nonneg (mul_nonneg (by norm_num) (Int.natCast_nonneg u)) hlast
  have hroot := (hy t.root).2
  rw [adjusted_root_mulVec] at hroot
  have hMle : charge y ≤ 1 := by omega
  have hz : ∀ a, t.absorbed a = false → y a = 0 := by
    by_cases hM0 : charge y = 0
    · have hneg : Ternary ((t.adjusted u).mulVec (-y)) := by
        rw [Matrix.mulVec_neg]
        exact ternary_neg _ hy
      have hnegM : 0 ≤ charge (-y) := by rw [charge_neg, hM0]; omega
      have htneg := adjusted_timeout_nonneg t hm u (-y) hneg hnegM
      intro a ha
      have hplus := htime a ha
      have hminus := htneg a ha
      change 0 ≤ -y a at hminus
      omega
    · have hM1 : charge y = 1 := by omega
      have hT0 : timeoutMass t y = 0 := by omega
      exact timeoutMass_zero t y htime hT0
  have himage := adjusted_eq_path_of_timeout_zero t hm hn u y hz
  have hpath : Ternary (t.path.mulVec y) := by rw [← himage]; exact hy
  have hcoeff : ∀ a, 0 ≤ y a := path_coeff_nonneg t y hM (fun i _ => hpath i)
  by_cases hM0 : charge y = 0
  · exact Or.inl (nonneg_charge_zero y hcoeff hM0)
  · have hM1 : charge y = 1 := by omega
    obtain ⟨a, hya⟩ := nonneg_charge_one y hcoeff hM1
    have ha : t.absorbed a = true := by
      cases hab : t.absorbed a with
      | true => rfl
      | false =>
        have hza := hz a hab
        rw [hya, Pi.single_eq_same] at hza
        omega
    exact Or.inr ⟨a, ha, hya⟩

/-- The complete classification is uniform in unbounded integral leaf
coefficients and in every nonnegative even root adjustment. -/
theorem adjusted_coefficients (t : Tree) (hm : t.Mixed) (hn : t.isNode = true)
    (u : ℕ) (y : t.Leaf → ℤ) (hy : Ternary ((t.adjusted u).mulVec y)) :
    y = 0 ∨ ∃ a, t.absorbed a = true ∧
      (y = Pi.single a 1 ∨ y = -Pi.single a 1) := by
  by_cases hM : 0 ≤ charge y
  · rcases adjusted_positive t hm hn u y hy hM with hz | ⟨a, ha, hya⟩
    · exact Or.inl hz
    · exact Or.inr ⟨a, ha, Or.inl hya⟩
  · have hneg : Ternary ((t.adjusted u).mulVec (-y)) := by
      rw [Matrix.mulVec_neg]
      exact ternary_neg _ hy
    have hnegM : 0 ≤ charge (-y) := by rw [charge_neg]; omega
    rcases adjusted_positive t hm hn u (-y) hneg hnegM with hz | ⟨a, ha, hya⟩
    · exact Or.inl (neg_eq_zero.mp hz)
    · refine Or.inr ⟨a, ha, Or.inr ?_⟩
      simpa only [neg_neg] using congrArg Neg.neg hya

end
end Short

/-- Every ternary image of the adjusted integral matrix is zero or has
one of the two prescribed absorbing-path charges.  The leaf coefficients
are arbitrary integers; no bound on them is assumed. -/
theorem adjusted_ternary_image (t : Tree) (hm : t.Mixed) (hn : t.isNode = true)
    (q : ℕ) (_hq : 2 ≤ q)
    (hcharge : ∀ a : t.Leaf, t.absorbed a = true →
      charge (fun i => t.path i a) = (q : ℤ) ∨
        charge (fun i => t.path i a) = -(q : ℤ)) :
    ∀ (u : ℕ) (y : t.Leaf → ℤ), Ternary ((t.adjusted u).mulVec y) →
      (t.adjusted u).mulVec y = 0 ∨
        charge ((t.adjusted u).mulVec y) = (q : ℤ) ∨
        charge ((t.adjusted u).mulVec y) = -(q : ℤ) := by
  intro u y hy
  rcases Short.adjusted_coefficients t hm hn u y hy with hz | ⟨a, ha, hpos | hneg⟩
  · exact Or.inl (by simp [hz])
  · right
    rw [hpos, Matrix.mulVec_single_one, Short.adjusted_absorbing_column t hm hn u a ha]
    exact hcharge a ha
  · right
    rw [hneg, Matrix.mulVec_neg, Matrix.mulVec_single_one,
      Short.adjusted_absorbing_column t hm hn u a ha, Short.charge_neg]
    rcases hcharge a ha with hq | hq
    · exact Or.inr (congrArg Neg.neg hq)
    · exact Or.inl (by simpa only [neg_neg] using congrArg Neg.neg hq)

end ErdosDSS.TreeCode
