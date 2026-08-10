import FormalConjectures.Util.ProblemImports
open List Nat Function Set

noncomputable section

def F : ℕ → ℕ → ℕ → ℕ
| n, 0, 0 => n
| n, 0, _+1 => 0
| n, t+1, 0 => n
| n, t+1, i+1 => F n t (i+1) + (F n t i - F n t (i+1))/2

lemma F_zero (n t) : F n t 0 = n := by
  cases t <;> rfl

lemma F_mono_index (n t i) : F n t (i+1) ≤ F n t i := by
  induction t generalizing i with
  | zero => cases i <;> simp [F]
  | succ t ih =>
      cases i with
      | zero => simp [F, F_zero]
      | succ i =>
          simp [F]
          have h1 := ih (i+1)
          have h0 := ih i
          -- H(b,c) <= H(a,b) for a>=b>=c
          omega

lemma lower_shift (n t i) : F (n+1) (t+1) (i+1) ≤ F n t i := by
  induction t generalizing i with
  | zero =>
      cases i <;> simp [F]
      omega
  | succ t ih =>
      cases i with
      | zero =>
          simp [F, F_zero]
          have hmono := F_mono_index (n+1) (t+1) 1
          omega
      | succ i =>
          simp [F]
          have hA := ih i
          have hB := ih (i+1)
          have hm1 := F_mono_index n t i
          have hm2 := F_mono_index n t (i+1)
          have hm3 := F_mono_index (n+1) (t+1) (i+1)
          omega

lemma upper_pos_shift (n t i) : 0 < F n t i → 0 < F (n+1) (t+2) (i+1) := by
  induction t generalizing i with
  | zero =>
      intro h
      cases i with
      | zero => simp [F]
      | succ i => simp [F] at h
  | succ t ih =>
      intro h
      cases i with
      | zero => simp [F]
      | succ i =>
          simp [F] at h ⊢
          by_cases hpos : 0 < F n t (i+1)
          · have := ih (i+1) hpos
            -- tail is nondecreasing in time
            sorry
          · have hz : F n t (i+1) = 0 := by omega
            have hdiff : 2 ≤ F n t i := by omega
            have posD := ih i (by omega : 0 < F n t i)
            -- need quantitative D >= 2 if next tail zero
            sorry

end
