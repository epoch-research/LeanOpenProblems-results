import FormalConjectures.Util.ProblemImports
open Nat

noncomputable def A264025 (n : ℕ) : ℕ :=
  Nat.card { p : ℕ × ℕ × ℕ //
    let (x, y, z) := p
    x ^ 2 + y * (2 * y + 1) + z * (z + 1) / 2 = n ∧
    (Nat.Prime z ∨ Nat.Prime (z + 1)) }

def Pred (n : ℕ) (p : ℕ × ℕ × ℕ) : Prop :=
  p.1 ^ 2 + p.2.1 * (2 * p.2.1 + 1) + p.2.2 * (p.2.2 + 1) / 2 = n ∧
    (Nat.Prime p.2.2 ∨ Nat.Prime (p.2.2 + 1))
instance (n : ℕ) (p : ℕ × ℕ × ℕ) : Decidable (Pred n p) := by unfold Pred; infer_instance

def box (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (n+1)) ×ˢ (Finset.range (n+1)) ×ˢ (Finset.range (n+1))

lemma bound (n : ℕ) (p : ℕ × ℕ × ℕ) (h : Pred n p) :
    p.1 ≤ n ∧ p.2.1 ≤ n ∧ p.2.2 ≤ n := by
  obtain ⟨heq, -⟩ := h
  rcases p with ⟨x, y, z⟩
  simp only at heq ⊢
  have hx : x ≤ x ^ 2 := Nat.le_self_pow (by norm_num) x
  have hy : y ≤ y * (2 * y + 1) := by nlinarith
  have hz : z ≤ z * (z + 1) / 2 := by
    rcases Nat.eq_zero_or_pos z with hz0 | hz0
    · simp [hz0]
    · have hle : z * 2 ≤ z * (z + 1) := by nlinarith
      calc z = z * 2 / 2 := by omega
        _ ≤ z * (z + 1) / 2 := Nat.div_le_div_right hle
  omega

lemma mem_box (n : ℕ) (p : ℕ × ℕ × ℕ) (h : p.1 ≤ n ∧ p.2.1 ≤ n ∧ p.2.2 ≤ n) : p ∈ box n := by
  rcases p with ⟨x, y, z⟩
  simp only [box, Finset.mem_product, Finset.mem_range] at *
  omega

lemma pred_iff_mem (n : ℕ) (p : ℕ × ℕ × ℕ) : Pred n p ↔ p ∈ (box n).filter (Pred n) := by
  rw [Finset.mem_filter]
  exact ⟨fun h => ⟨mem_box n p (bound n p h), h⟩, fun h => h.2⟩

lemma bridge (n : ℕ) : A264025 n = ((box n).filter (Pred n)).card := by
  show Nat.card {p : ℕ × ℕ × ℕ // Pred n p} = _
  rw [Nat.card_congr (Equiv.subtypeEquivRight (pred_iff_mem n)),
    Nat.card_eq_fintype_card, Fintype.card_coe]

-- Per-n lower bound is cheap: two explicit witnesses, no enumeration.
lemma a1345 : 2 ≤ A264025 1345 := by
  rw [bridge]
  apply Finset.one_lt_card.mpr
  refine ⟨(2, 25, 11), ?_, (4, 24, 17), ?_, ?_⟩
  · rw [← pred_iff_mem]; refine ⟨by norm_num, Or.inl (by norm_num)⟩
  · rw [← pred_iff_mem]; refine ⟨by norm_num, Or.inl (by norm_num)⟩
  · decide
