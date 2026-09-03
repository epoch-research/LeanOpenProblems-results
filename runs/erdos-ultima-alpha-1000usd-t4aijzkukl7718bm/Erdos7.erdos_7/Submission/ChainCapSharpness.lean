import FormalConjecturesUtil

/-! A sharpness example for a single prefix-coordinate count bound.
This is not an odd arithmetic covering system. It shows why a cap on the
number of simultaneous hits alone need not improve a low stop-loss bound. -/
namespace Erdos7ChainSharpness
open scoped BigOperators
set_option maxHeartbeats 1500000
noncomputable section
local instance : Decidable (p : Prop) := Classical.propDecidable p

/-- The all-zero prefix cylinder of length `a`. -/
def prefixEvent {p E : ℕ} (a : ℕ) (x : Fin E → Fin p) : Prop :=
  ∀ j, j.val < a → (x j).val = 0

/-- A prefix of zeros terminated by a one. Different positive lengths give
pairwise disjoint cylinders. -/
def tailEvent {p E : ℕ} (a : ℕ) (x : Fin E → Fin p) : Prop :=
  ∀ j, j.val < a → (x j).val = if j.val + 1 = a then 1 else 0

def hit {p E : ℕ} (t a : ℕ) (x : Fin E → Fin p) : Prop :=
  if a < t then prefixEvent a x else tailEvent a x

noncomputable def active {p E : ℕ} (t : ℕ) (x : Fin E → Fin p) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 E).filter (fun a => hit t a x)

noncomputable def tailActive {p E : ℕ} (t : ℕ) (x : Fin E → Fin p) : Finset ℕ := by
  classical
  exact (Finset.Icc t E).filter (fun a => tailEvent a x)

lemma tail_disjoint {p E a b : ℕ} (ha : 1 ≤ a) (haE : a ≤ E) (hab : a < b)
    (x : Fin E → Fin p) (hax : tailEvent a x) (hbx : tailEvent b x) : False := by
  let j : Fin E := ⟨a - 1, by omega⟩
  have h₁ := hax j (by dsimp [j]; omega)
  have h₂ := hbx j (by dsimp [j]; omega)
  have he : j.val + 1 = a := by dsimp [j]; omega
  have hn : j.val + 1 ≠ b := by omega
  rw [if_pos he] at h₁
  rw [if_neg hn] at h₂
  omega

lemma tail_implies_prefix {p E a b : ℕ} (hba : b < a) (x : Fin E → Fin p)
    (ha : tailEvent a x) : prefixEvent b x := by
  intro j hj
  have hh := ha j (by omega)
  rw [if_neg (by omega : j.val + 1 ≠ a)] at hh
  exact hh

lemma tailActive_card_le_one {p E t : ℕ} (ht : 1 ≤ t) (x : Fin E → Fin p) :
    (tailActive t x).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨ha, hax⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb, hbx⟩ := Finset.mem_filter.mp hb
  obtain ⟨hta, haE⟩ := Finset.mem_Icc.mp ha
  obtain ⟨htb, hbE⟩ := Finset.mem_Icc.mp hb
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (tail_disjoint (by omega) haE hab x hax hbx).elim
  · exact hab
  · exact (tail_disjoint (by omega) hbE hab x hbx hax).elim

lemma active_card_of_tail {p E t a : ℕ} (ht : 1 ≤ t) (htE : t ≤ E)
    (x : Fin E → Fin p) (ha : a ∈ tailActive t x) : (active t x).card = t := by
  classical
  obtain ⟨haI, hax⟩ := Finset.mem_filter.mp ha
  obtain ⟨hta, haE⟩ := Finset.mem_Icc.mp haI
  have heq : active t x = insert a (Finset.Icc 1 (t - 1)) := by
    ext b
    simp only [active, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hb, hbE⟩, hbx⟩
      by_cases hbt : b < t
      · exact Or.inr ⟨hb, by omega⟩
      · have hbTail : b ∈ tailActive t x := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_Icc.mpr ⟨by omega, hbE⟩, by simpa [hit, hbt] using hbx⟩
        exact Or.inl (Finset.card_le_one.mp (tailActive_card_le_one ht x) b hbTail a
          (Finset.mem_filter.mpr ⟨haI, hax⟩))
    · intro hb
      rcases hb with rfl | ⟨hb, hbt⟩
      · exact ⟨⟨by omega, haE⟩, by simpa [hit, show ¬ b < t by omega] using hax⟩
      · have hbt' : b < t := by omega
        exact ⟨⟨hb, by omega⟩, by
          simpa [hit, hbt'] using tail_implies_prefix (by omega : b < a) x hax⟩
  rw [heq, Finset.card_insert_of_notMem (by simp only [Finset.mem_Icc]; omega)]
  simp only [Nat.card_Icc]
  omega

lemma active_card_of_no_tail {p E t : ℕ} (ht : 1 ≤ t) (x : Fin E → Fin p)
    (he : tailActive t x = ∅) : (active t x).card ≤ t - 1 := by
  classical
  have hs : active t x ⊆ Finset.Icc 1 (t - 1) := by
    intro a ha
    obtain ⟨haI, hax⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha, haE⟩ := Finset.mem_Icc.mp haI
    by_cases hat : a < t
    · exact Finset.mem_Icc.mpr ⟨ha, by omega⟩
    · have hm : a ∈ tailActive t x := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, haE⟩, by simpa [hit, hat] using hax⟩
      rw [he] at hm
      exact (Finset.notMem_empty a hm).elim
  have hh := Finset.card_le_card hs
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hh

/-- A cap of `t` is compatible with the exact tail-union value of the hinge
at `t-1`, not merely a smaller upper estimate. -/
theorem capped_hinge_identity {p E t : ℕ} (ht : 1 ≤ t) (htE : t ≤ E)
    (x : Fin E → Fin p) :
    (active t x).card ≤ t ∧
      max ((active t x).card - ((t - 1 : ℕ) : ℚ)) 0 = ((tailActive t x).card : ℚ) := by
  classical
  rcases (tailActive t x).eq_empty_or_nonempty with he | hn
  · have hh := active_card_of_no_tail ht x he
    constructor
    · omega
    · rw [he, Finset.card_empty, Nat.cast_zero]
      exact max_eq_right (sub_nonpos.mpr (by exact_mod_cast hh))
  · obtain ⟨a, ha⟩ := hn
    have hc := active_card_of_tail ht htE x ha
    have htc : (tailActive t x).card = 1 := by
      have h₁ := tailActive_card_le_one ht x
      have h₂ := Finset.card_pos.mpr ⟨a, ha⟩
      omega
    constructor
    · omega
    · rw [hc, htc, Nat.cast_one]
      have he : (t : ℚ) - ((t - 1 : ℕ) : ℚ) = 1 := by
        have hh : t = (t - 1) + 1 := by omega
        exact_mod_cast (show (t : ℤ) - (t - 1 : ℕ) = 1 by omega)
      rw [he]
      norm_num


/-- The unconstrained suffix parametrizes a fixed-prefix cylinder. -/
noncomputable def cylinderEquiv (p E a : ℕ) (ha : a ≤ E)
    (v : Fin E → Fin p) :
    {x : Fin E → Fin p // ∀ j, j.val < a → x j = v j} ≃
      (Fin (E - a) → Fin p) := by
  classical
  refine {
    toFun := fun x j => x.val ⟨a + j.val, by omega⟩
    invFun := fun y => ⟨fun j => if h : j.val < a then v j else y ⟨j.val - a, by omega⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro j hj
    simp [hj]
  · intro x
    apply Subtype.ext
    funext j
    by_cases hj : j.val < a
    · simp [hj, x.property j hj]
    · simp only [dif_neg hj]
      have he : (⟨a + (j.val - a), by omega⟩ : Fin E) = j := by
        apply Fin.ext
        simp only [Fin.val_mk]
        omega
      rw [he]
  · intro y
    funext j
    simp only [show ¬ a + j.val < a by omega, ↓reduceDIte]
    congr 1
    apply Fin.ext
    simp

lemma card_cylinder (p E a : ℕ) (ha : a ≤ E) (v : Fin E → Fin p) :
    ((Finset.univ : Finset (Fin E → Fin p)).filter
      (fun x => ∀ j, j.val < a → x j = v j)).card = p ^ (E - a) := by
  classical
  calc
    _ = Fintype.card {x : Fin E → Fin p // ∀ j, j.val < a → x j = v j} := by
      exact (Fintype.card_subtype _).symm
    _ = Fintype.card (Fin (E - a) → Fin p) := Fintype.card_congr (cylinderEquiv p E a ha v)
    _ = _ := by simp

lemma card_tailEvent {p E : ℕ} (hp : 2 ≤ p) (a : ℕ) (ha : a ≤ E) :
    ((Finset.univ : Finset (Fin E → Fin p)).filter (tailEvent a)).card =
      p ^ (E - a) := by
  classical
  let v : Fin E → Fin p := fun j => ⟨if j.val + 1 = a then 1 else 0, by split_ifs <;> omega⟩
  have hh := card_cylinder p E a ha v
  have he : ((Finset.univ : Finset (Fin E → Fin p)).filter (tailEvent a)) =
      Finset.univ.filter (fun x => ∀ j, j.val < a → x j = v j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, tailEvent, Fin.ext_iff]
    rfl
  rw [he]
  exact hh

lemma card_prefixEvent {p E : ℕ} (hp : 1 ≤ p) (a : ℕ) (ha : a ≤ E) :
    ((Finset.univ : Finset (Fin E → Fin p)).filter (prefixEvent a)).card =
      p ^ (E - a) := by
  classical
  let v : Fin E → Fin p := fun _ => ⟨0, by omega⟩
  have hh := card_cylinder p E a ha v
  have he : ((Finset.univ : Finset (Fin E → Fin p)).filter (prefixEvent a)) =
      Finset.univ.filter (fun x => ∀ j, j.val < a → x j = v j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, prefixEvent, Fin.ext_iff]
    rfl
  rw [he]
  exact hh

/-- Every member of the capped family still has exactly its usual cylinder
cardinality; the cap was not obtained by shrinking individual events. -/
theorem card_hit {p E : ℕ} (hp : 2 ≤ p) (t a : ℕ) (ha : a ≤ E) :
    ((Finset.univ : Finset (Fin E → Fin p)).filter (hit t a)).card =
      p ^ (E - a) := by
  classical
  by_cases h : a < t
  · have he : @hit p E t a = prefixEvent a := by funext x; exact if_pos h
    rw [he]
    exact card_prefixEvent (by omega : 1 ≤ p) a ha
  · have he : @hit p E t a = tailEvent a := by funext x; exact if_neg h
    rw [he]
    exact card_tailEvent hp a ha

/-- Exact unnormalized average of the capped hinge. Dividing by `p^E` gives
precisely the finite geometric tail starting at exponent `t`. -/
theorem capped_hinge_sum {p E t : ℕ} (hp : 2 ≤ p) (ht : 1 ≤ t) (htE : t ≤ E) :
    (∑ x : Fin E → Fin p, max ((active t x).card - ((t - 1 : ℕ) : ℚ)) 0) =
      ∑ a ∈ Finset.Icc t E, (p : ℚ) ^ (E - a) := by
  classical
  calc
    _ = ∑ x : Fin E → Fin p, ((tailActive t x).card : ℚ) :=
      Finset.sum_congr rfl (fun x _ => (capped_hinge_identity ht htE x).2)
    _ = ∑ x : Fin E → Fin p, ∑ a ∈ Finset.Icc t E,
        (if tailEvent a x then (1 : ℚ) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      simp [tailActive]
    _ = ∑ a ∈ Finset.Icc t E, ∑ x : Fin E → Fin p,
        (if tailEvent a x then (1 : ℚ) else 0) := Finset.sum_comm
    _ = ∑ a ∈ Finset.Icc t E,
        ((((Finset.univ : Finset (Fin E → Fin p)).filter (tailEvent a)).card : ℚ)) := by
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [card_tailEvent hp a (Finset.mem_Icc.mp ha).2, Nat.cast_pow]

#print axioms card_hit
#print axioms capped_hinge_sum
#print axioms capped_hinge_identity
end
end Erdos7ChainSharpness
