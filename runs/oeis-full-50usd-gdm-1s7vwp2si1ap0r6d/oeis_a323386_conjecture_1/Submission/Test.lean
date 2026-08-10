import FormalConjectures.Util.ProblemImports
import Submission.Spec

open Nat Int Real

lemma key_lemma_combined (n : ℕ) (hn : 1 ≤ n) (q : ℕ) [hq : Fact q.Prime] (hq_le : q^2 ≤ (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast)))) :
    (padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) ≤ padicValNat q (b n) + 1) ∧
    (q^2 < (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) → padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 1).cast))) ≤ padicValNat q (b n)) := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      -- Base case: n + 1 = 1
      have h_cast : (1 + 1 : ℕ).cast = (2 : ℝ) := by norm_num
      have h_floor : Int.floor (Real.sqrt 2 * (1 + 1 : ℕ).cast) = 2 := by
        rw [h_cast]
        exact floor_sqrt_two_mul_two
      have h_M : (Int.toNat (Int.floor (Real.sqrt 2 * (1 + 1 : ℕ).cast))) = 2 := by
        rw [h_floor]
        rfl
      rw [h_M] at hq_le
      have hq_ge : 2 ≤ q := hq.out.two_le
      have hq2_ge : 4 ≤ q^2 := by
        have : 2^2 ≤ q^2 := Nat.pow_le_pow_left hq_ge 2
        exact this
      omega
    · have hn_pos : 1 ≤ n := by omega
      have ih_val := ih hn_pos
      change (padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) ≤ padicValNat q (b (n + 1)) + 1) ∧
             (q^2 < (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) → padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) ≤ padicValNat q (b (n + 1)))
      by_cases hq2 : q = 2
      · subst hq2
        have h_v2_b_ge : n + 1 ≤ padicValNat 2 (b (n + 1)) := padicValNat_two_b_ge (n + 1) (by omega)
        have h_M_lt := M_lt_two_pow n
        have h_M_pos : 0 < (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) := M_pos (n + 1) (by omega)
        have h_v_M_le : padicValNat 2 (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) ≤ n + 1 := by
          by_contra h_contr
          have h_lt : n + 1 < padicValNat 2 (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) := by omega
          have h_dvd : 2^(n + 2) ∣ (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) := by
            rwa [padicValNat_dvd_iff_le h_M_pos.ne']
          have h_le := Nat.le_of_dvd h_M_pos h_dvd
          omega
        constructor
        · omega
        · intro _
          omega
      · have h_or := valuation_M_curr_M_next n hn_pos q hq2
        rcases h_or with h_next | h_curr
        · constructor
          · rw [h_next]
            omega
          · intro _
            rw [h_next]
            omega
          -- This handles the case where valuation_M_next = 0.
        · -- Now we have valuation_M_curr = 0, which is h_curr
          have h_strict_lemma : q^2 < (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) → padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) ≤ padicValNat q (b (n + 1)) := by
            intro h_strict
            sorry
          constructor
          · by_cases h_le1 : padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) ≤ 1
            · have : 1 ≤ padicValNat q (b (n + 1)) + 1 := Nat.le_add_left 1 _
              omega
            · -- padicValNat q M(n+2) >= 2
              have h_M_pos : 0 < (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) := M_pos (n + 1) (by omega)
              have h_dvd : q^2 ∣ (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) := by
                have : 2 ≤ padicValNat q (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) := by omega
                exact (padicValNat_dvd_iff_le h_M_pos.ne').mpr this
              have h_le_next : q^2 ≤ (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast))) := Nat.le_of_dvd h_M_pos h_dvd
              by_cases h_strict2 : q^2 < (Int.toNat (Int.floor (Real.sqrt 2 * (n + 2).cast)))
              · have := h_strict_lemma h_strict2
                omega
              · -- q^2 = M(n+2)
                sorry
          · exact h_strict_lemma
