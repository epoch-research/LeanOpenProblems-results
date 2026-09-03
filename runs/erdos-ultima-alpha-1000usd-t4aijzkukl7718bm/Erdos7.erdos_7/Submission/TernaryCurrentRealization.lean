import Submission.ChainCapSharpness

/-! A concrete partial family realizing the troublesome ternary current
profile in the limit of increasing five-adic depth. The current boxes are
pairwise disjoint, and a whole first-digit cylinder remains available.
This is NOT a covering system or a disproof of the conjecture. -/
namespace Erdos7TernaryCurrentRealization
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The four current rows use three different final five-adic digits;
rows1 and3 may share a digit because their ternary projections are disjoint. -/
def label (u : Fin 4) : Fin 3 := ⟨if u.val = 0 then 0 else if u.val = 2 then 2 else 1, by split_ifs <;> omega⟩

def oldHit (u : Fin 4) (x : Fin 27) : Prop :=
  if u.val = 0 then True else if u.val = 1 then x.val % 3 = 2
  else if u.val = 2 then x.val % 9 = 2 else x.val = 13

instance (u : Fin 4) (x : Fin 27) : Decidable (oldHit u x) := by
  unfold oldHit
  infer_instance

def count (x : Fin 27) : ℕ :=
  1 + (if x.val % 3 = 2 then 1 else 0) +
    (if x.val % 9 = 2 then 1 else 0) + (if x.val = 13 then 1 else 0)

def survivor (x : Fin 27) : Prop :=
  x.val % 3 ≠ 0 ∧ x.val % 9 ≠ 1 ∧ x.val ≠ 4

instance (x : Fin 27) : Decidable (survivor x) := by unfold survivor; infer_instance

lemma old_count (x : Fin 27) : (∑ u : Fin 4, if oldHit u x then 1 else 0) = count x := by
  revert x
  decide +kernel

lemma same_label_disjoint : ∀ u v : Fin 4, u ≠ v → label u = label v →
    ∀ x : Fin 27, ¬ (oldHit u x ∧ oldHit v x) := by
  decide +kernel

lemma survivor_profile :
    (Finset.univ.filter survivor).card = 14 ∧
    (Finset.univ.filter (fun x => survivor x ∧ count x = 1)).card = 4 ∧
    (Finset.univ.filter (fun x => survivor x ∧ count x = 2)).card = 7 ∧
    (Finset.univ.filter (fun x => survivor x ∧ count x = 3)).card = 3 := by
  decide +kernel

/-- A stem of fours terminated by the selected digit0,1,or2. -/
def codeEvent {E : ℕ} (c : Fin 3) (b : Fin E) (y : Fin E → Fin 5) : Prop :=
  ∀ j, j.val ≤ b.val → (y j).val = if j = b then c.val else 4

instance {E : ℕ} (c : Fin 3) (b : Fin E) (y : Fin E → Fin 5) :
    Decidable (codeEvent c b y) := by unfold codeEvent; infer_instance

lemma code_depth_disjoint {E : ℕ} (c d : Fin 3) {b e : Fin E} (hbe : b.val < e.val)
    (y : Fin E → Fin 5) (hb : codeEvent c b y) (he : codeEvent d e y) : False := by
  have h₁ := hb b (by omega)
  have h₂ := he b (by omega)
  simp only [ite_true] at h₁
  simp only [if_neg (show b ≠ e by intro h; subst e; omega)] at h₂
  have hc := c.isLt
  omega

lemma code_same_depth {E : ℕ} (c d : Fin 3) (b : Fin E)
    (y : Fin E → Fin 5) (hc : codeEvent c b y) (hd : codeEvent d b y) : c = d := by
  have h₁ := hc b (by omega)
  have h₂ := hd b (by omega)
  simp only [ite_true] at h₁ h₂
  apply Fin.ext
  omega

def fiberBox {E : ℕ} (u : Fin 4) (b : Fin E) (x : Fin 27) (y : Fin E → Fin 5) : Prop :=
  oldHit u x ∧ codeEvent (label u) b y

instance {E : ℕ} (u : Fin 4) (b : Fin E) (x : Fin 27) (y : Fin E → Fin 5) :
    Decidable (fiberBox u b x y) := by unfold fiberBox; infer_instance

lemma fiber_disjoint {E : ℕ} {i j : Fin 4 × Fin E} (hij : i ≠ j)
    (x : Fin 27) (y : Fin E → Fin 5) :
    ¬ (fiberBox i.1 i.2 x y ∧ fiberBox j.1 j.2 x y) := by
  rintro ⟨⟨hi, hci⟩, ⟨hj, hcj⟩⟩
  rcases lt_trichotomy i.2.val j.2.val with h | h | h
  · exact code_depth_disjoint _ _ h y hci hcj
  · have he : i.2 = j.2 := Fin.ext h
    have hlabel : label i.1 = label j.1 := code_same_depth _ _ i.2 y hci (he ▸ hcj)
    have hfirst : i.1 ≠ j.1 := fun h' => hij (Prod.ext h' he)
    exact same_label_disjoint i.1 j.1 hfirst hlabel x ⟨hi, hj⟩
  · exact code_depth_disjoint _ _ h y hcj hci

lemma card_codeEvent {E : ℕ} (c : Fin 3) (b : Fin E) :
    (Finset.univ.filter (codeEvent c b)).card = 5 ^ (E - (b.val + 1)) := by
  classical
  let v : Fin E → Fin 5 := fun j => ⟨if j = b then c.val else 4, by split_ifs <;> omega⟩
  have he : Finset.univ.filter (codeEvent c b) =
      Finset.univ.filter (fun y : Fin E → Fin 5 => ∀ j, j.val < b.val+1 → y j = v j) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, codeEvent, Fin.ext_iff, v]
    constructor <;> intro h j hj <;> exact h j (by omega)
  rw [he]
  exact Erdos7ChainSharpness.card_cylinder 5 E (b.val+1) (by omega) v

lemma card_fiberBox {E : ℕ} (u : Fin 4) (b : Fin E) (x : Fin 27) :
    (Finset.univ.filter (fiberBox u b x)).card =
      if oldHit u x then 5 ^ (E - (b.val+1)) else 0 := by
  classical
  by_cases h : oldHit u x
  · have he : fiberBox u b x = codeEvent (label u) b := by
      funext y
      apply propext
      simp [fiberBox, h]
    simpa only [he, if_pos h] using card_codeEvent (label u) b
  · change (Finset.univ.filter (fun y => oldHit u x ∧ codeEvent (label u) b y)).card = _
    simp [h]

noncomputable def badFiber {E : ℕ} (x : Fin 27) : Finset (Fin E → Fin 5) := by
  classical
  exact Finset.univ.biUnion (fun i : Fin 4 × Fin E => Finset.univ.filter (fiberBox i.1 i.2 x))

/-- The fiber union bound is attained exactly by this partial family. -/
theorem card_badFiber {E : ℕ} (x : Fin 27) :
    (badFiber (E := E) x).card = count x * ∑ b : Fin E, 5 ^ (E - (b.val+1)) := by
  classical
  have hdis : (↑(Finset.univ : Finset (Fin 4 × Fin E)) : Set (Fin 4 × Fin E)).PairwiseDisjoint
      (fun i => Finset.univ.filter (fiberBox i.1 i.2 x)) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro y hi hj
    exact fiber_disjoint hij x y ⟨(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩
  unfold badFiber
  rw [Finset.card_biUnion hdis, Fintype.sum_prod_type]
  simp_rw [card_fiberBox]
  calc
    _ = ∑ u : Fin 4, (if oldHit u x then 1 else 0) *
        ∑ b : Fin E, 5 ^ (E - (b.val+1)) := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : oldHit u x <;> simp [h]
    _ = _ := by rw [← Finset.sum_mul, old_count]

lemma geometric_card (E : ℕ) :
    4 * (∑ b : Fin E, 5 ^ (E - (b.val+1))) + 1 = 5^E := by
  induction E with
  | zero => simp
  | succ E ih =>
    rw [Fin.sum_univ_succ]
    have he : (∑ b : Fin E, 5 ^ (E+1 - (b.succ.val+1))) =
        ∑ b : Fin E, 5 ^ (E - (b.val+1)) := by
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      simp only [Fin.val_succ]
      omega
    simp only [Fin.val_zero, zero_add, Nat.add_sub_cancel] at *
    rw [he, pow_succ]
    nlinarith

/-- Exact rational density for every finite five-adic depth. -/
theorem badFiber_density (E : ℕ) (x : Fin 27) :
    ((badFiber (E := E) x).card : ℚ) / (5 : ℚ)^E =
      (count x : ℚ) / 4 * (1 - 1 / (5 : ℚ)^E) := by
  have hg := geometric_card E
  have he : 4 * (badFiber (E := E) x).card + count x = count x * 5^E := by
    rw [card_badFiber]
    nlinarith
  have heq : 4 * ((badFiber (E := E) x).card : ℚ) + (count x : ℚ) =
      (count x : ℚ) * (5 : ℚ)^E := by exact_mod_cast he
  have hp : (5 : ℚ)^E ≠ 0 := by positivity
  field_simp
  nlinarith

/-- A whole first-digit3 cylinder avoids every current row at every depth. -/
theorem first_digit_three_free {E : ℕ} (hE : 0 < E) (x : Fin 27)
    (y : Fin E → Fin 5) (hy : (y ⟨0, hE⟩).val = 3) : y ∉ badFiber x := by
  classical
  intro h
  obtain ⟨⟨u, b⟩, _, h⟩ := Finset.mem_biUnion.mp h
  obtain ⟨_, _, hc⟩ := Finset.mem_filter.mp h
  have hh := hc ⟨0, hE⟩ (by simp)
  split_ifs at hh <;> have hl := (label u).isLt <;> omega

/-- The three retained first digits are encoded by `c+1`. Digit four is
excluded so that no positive-depth stem can meet these coarse points. -/
def coarseAllowed (x : Fin 27) (c : Fin 3) : Prop :=
  survivor x ∧ (c.val = 0 → ¬ (x.val % 3 = 2 ∨ x.val = 13)) ∧
    (c.val = 1 → x.val % 9 ≠ 2)

instance (x : Fin 27) (c : Fin 3) : Decidable (coarseAllowed x c) := by
  unfold coarseAllowed
  infer_instance

lemma coarse_card :
    (Finset.univ.filter (fun z : Fin 27 × Fin 3 => coarseAllowed z.1 z.2)).card = 29 := by
  decide +kernel

lemma coarse_disjoint_row : ∀ (x : Fin 27) (c : Fin 3) (u : Fin 4),
    coarseAllowed x c → oldHit u x → (label u).val ≠ c.val+1 := by
  decide +kernel

/-- Every one of the29 allowed coarse points avoids the entire current
family, for arbitrary finite high-digit depth. This concerns only the
specified stem construction, not arbitrary covering-system residues. -/
theorem coarse_avoids {E : ℕ} (hE : 0 < E) (x : Fin 27) (c : Fin 3)
    (hc : coarseAllowed x c) (y : Fin E → Fin 5)
    (hy : (y ⟨0,hE⟩).val = c.val+1) : y ∉ badFiber x := by
  classical
  intro h
  obtain ⟨⟨u,b⟩, _, h⟩ := Finset.mem_biUnion.mp h
  obtain ⟨_, ho, hb⟩ := Finset.mem_filter.mp h
  have hh := hb ⟨0,hE⟩ (by simp)
  split_ifs at hh with hzero
  · change (y ⟨0,hE⟩).val = (label u).val at hh
    exact coarse_disjoint_row x c u hc ho (hh.symm.trans hy)
  · have hclt := c.isLt
    omega

#print axioms card_badFiber
#print axioms badFiber_density
#print axioms first_digit_three_free
#print axioms coarse_card
#print axioms coarse_avoids
end Erdos7TernaryCurrentRealization
