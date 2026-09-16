import Submission.ProofLength
import Mathlib

theorem map1_inj {L : ℕ} : Function.Injective (@map1 L) := by
  intro a b h
  have h1 : shift_seq a 1 = shift_seq b 1 := (Fin.snoc_inj.mp h).1
  ext i
  have ha : shift_seq a 1 i = a i + 1 := rfl
  have hb : shift_seq b 1 i = b i + 1 := rfl
  have h2 : a i + 1 = b i + 1 := by rw [←ha, ←hb, h1]
  omega

theorem map2_inj {L : ℕ} : Function.Injective (@map2 L) := by
  intro a b h
  exact (Fin.snoc_inj.mp h).1

theorem map3_inj {L : ℕ} : Function.Injective (@map3 L) := by
  intro a b h
  have h1 := (Fin.snoc_inj.mp h).1
  have h2 := (Fin.snoc_inj.mp h1).1
  ext i
  have ha : shift_seq a 1 i = a i + 1 := rfl
  have hb : shift_seq b 1 i = b i + 1 := rfl
  have h3 : a i + 1 = b i + 1 := by rw [←ha, ←hb, h2]
  omega

theorem map4_inj {L : ℕ} : Function.Injective (@map4 L) := by
  intro a b h
  have h1 := (Fin.snoc_inj.mp h).1
  have h2 := (Fin.snoc_inj.mp h1).1
  ext i
  have ha : shift_seq a 2 i = a i + 2 := rfl
  have hb : shift_seq b 2 i = b i + 2 := rfl
  have h3 : a i + 2 = b i + 2 := by rw [←ha, ←hb, h2]
  omega

theorem disjoint_map1_map2 {L : ℕ} (a b : Fin L → ℕ) (ha_pos : ∀ i, a i > 0) (hb : ∃ i, b i = 1) :
  map1 a ≠ map2 b := by
  intro h
  unfold map1 map2 at h
  have h1 : shift_seq a 1 = b := (Fin.snoc_inj.mp h).1
  rcases hb with ⟨i, hi⟩
  have h2 : shift_seq a 1 i = b i := by rw [h1]
  have ha : shift_seq a 1 i = a i + 1 := rfl
  rw [ha, hi] at h2
  have h3 := ha_pos i
  omega

theorem disjoint_map3_map4 {L : ℕ} (a b : Fin L → ℕ) (hb_pos : ∀ i, b i > 0) (ha : ∃ i, a i = 1) :
  map3 a ≠ map4 b := by
  intro h
  unfold map3 map4 at h
  have h1 := (Fin.snoc_inj.mp h).1
  have h2 := (Fin.snoc_inj.mp h1).1
  rcases ha with ⟨i, hi⟩
  have h3 : shift_seq a 1 i = shift_seq b 2 i := by rw [h2]
  have ha_def : shift_seq a 1 i = a i + 1 := rfl
  have hb_def : shift_seq b 2 i = b i + 2 := rfl
  rw [ha_def, hb_def, hi] at h3
  have h4 := hb_pos i
  omega

theorem disjoint_map1_map3 {L : ℕ} (a : Fin (L + 1) → ℕ) (b : Fin L → ℕ) :
  map1 a ≠ map3 b := by
  intro h
  unfold map1 map3 at h
  have h1 := (Fin.snoc_inj.mp h).2
  omega

theorem disjoint_map1_map4 {L : ℕ} (a : Fin (L + 1) → ℕ) (b : Fin L → ℕ) :
  map1 a ≠ map4 b := by
  intro h
  unfold map1 map4 at h
  have h1 := (Fin.snoc_inj.mp h).2
  omega

theorem disjoint_map2_map3 {L : ℕ} (a : Fin (L + 1) → ℕ) (b : Fin L → ℕ) :
  map2 a ≠ map3 b := by
  intro h
  unfold map2 map3 at h
  have h1 := (Fin.snoc_inj.mp h).2
  omega

theorem disjoint_map2_map4 {L : ℕ} (a : Fin (L + 1) → ℕ) (b : Fin L → ℕ) :
  map2 a ≠ map4 b := by
  intro h
  unfold map2 map4 at h
  have h1 := (Fin.snoc_inj.mp h).2
  omega
