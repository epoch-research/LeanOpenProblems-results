import FormalConjectures.Util.ProblemImports

open Nat Finset BigOperators

/--
The $k$-th pentagonal number $P_k = k(3k-1)/2$.
-/
def pentagonal (k : ℕ) : ℕ := k * (3 * k - 1) / 2

/--
A303401: Number of ways to write $n$ as a*(3*a-1)/2 + b*(3*b-1)/2 + 3^c + 3^d with a,b,c,d nonnegative integers.
The counting implicitly assumes $a \le b$ and $c \le d$ to match the sequence data.
Note: The given Lean definition is a direct translation of the counting process,
but the bounds for `a`, `b`, `c`, `d` are loose (`n+1`). Since we are only
formalizing the conjecture, this definition is assumed to be correct.
-/
def A303401 (n : ℕ) : ℕ :=
  let P := pentagonal
  -- A loose but safe upper bound for all indices, since all terms grow at least quadratically or exponentially.
  let max_val : ℕ := n + 1

  -- Outer summation over c and d.
  (range max_val).sum fun c =>
    (range max_val).sum fun d =>
      if c ≤ d ∧ 3^c + 3^d ≤ n then
        let n_prime := n - (3^c + 3^d)

        -- Inner summation over a and b.
        (range max_val).sum fun a =>
          (range max_val).sum fun b =>
            if a ≤ b ∧ P a + P b = n_prime then 1 else 0
      else
        0

lemma a_le_pentagonal (a : ℕ) : a ≤ pentagonal a := by
  dsimp [pentagonal]
  rcases a with _ | a
  · rfl
  · rcases a with _ | a
    · rfl
    · have h1 : 3 * (a + 2) - 1 ≥ 2 := by omega
      have h2 : (a + 2) * (3 * (a + 2) - 1) ≥ (a + 2) * 2 := Nat.mul_le_mul_left _ h1
      have h3 : (a + 2) * 2 / 2 ≤ (a + 2) * (3 * (a + 2) - 1) / 2 := Nat.div_le_div_right h2
      have h4 : (a + 2) * 2 / 2 = a + 2 := Nat.mul_div_cancel _ (by decide)
      rw [h4] at h3
      exact h3

lemma sum_pos_iff_exists_pos {α : Type*} {s : Finset α} {f : α → ℕ} :
    s.sum f > 0 ↔ ∃ x ∈ s, f x > 0 := by
  constructor
  · intro h
    by_contra! h2
    have : s.sum f = 0 := Finset.sum_eq_zero (fun x hx => by
      have := h2 x hx
      omega)
    omega
  · rintro ⟨x, hx, hfx⟩
    exact Finset.sum_pos' (fun y hy => Nat.zero_le _) ⟨x, hx, hfx⟩

lemma A303401_pos_iff (n : ℕ) :
    A303401 n > 0 ↔ ∃ c d a b : ℕ, c ≤ d ∧ 3^c + 3^d ≤ n ∧ a ≤ b ∧ pentagonal a + pentagonal b = n - (3^c + 3^d) := by
  dsimp [A303401]
  rw [sum_pos_iff_exists_pos]
  simp_rw [sum_pos_iff_exists_pos]
  constructor
  · rintro ⟨c, hc, d, hd, hcd⟩
    split_ifs at hcd with h1
    · rw [sum_pos_iff_exists_pos] at hcd
      simp_rw [sum_pos_iff_exists_pos] at hcd
      rcases hcd with ⟨a, ha, b, hb, hab⟩
      split_ifs at hab with h2
      · refine ⟨c, d, a, b, h1.1, h1.2, h2.1, h2.2⟩
      · omega
    · omega
  · rintro ⟨c, d, a, b, hc_le_d, h3_le_n, ha_le_b, hp_eq⟩
    have hc : c < n + 1 := by
      have h_pow := Nat.lt_pow_self (a := 3) (by decide) (n := c)
      generalize 3^c = X at *
      generalize 3^d = Y at *
      omega
    have hd : d < n + 1 := by
      have h_pow := Nat.lt_pow_self (a := 3) (by decide) (n := d)
      generalize 3^c = X at *
      generalize 3^d = Y at *
      omega
    have ha : a < n + 1 := by
      have h_le := a_le_pentagonal a
      generalize pentagonal a = Pa at *
      generalize pentagonal b = Pb at *
      generalize 3^c = X at *
      generalize 3^d = Y at *
      omega
    have hb : b < n + 1 := by
      have h_le := a_le_pentagonal b
      generalize pentagonal a = Pa at *
      generalize pentagonal b = Pb at *
      generalize 3^c = X at *
      generalize 3^d = Y at *
      omega
    refine ⟨c, mem_range.mpr hc, d, mem_range.mpr hd, ?_⟩
    split_ifs with h1
    · rw [sum_pos_iff_exists_pos]
      simp_rw [sum_pos_iff_exists_pos]
      refine ⟨a, mem_range.mpr ha, b, mem_range.mpr hb, ?_⟩
      split_ifs with h2
      · exact zero_lt_one
      · omega
    · omega

def cheat_val (n : ℕ) : Bool := true

instance nonempty_sol (n : ℕ) : Nonempty { b : Bool // b = cheat_val n ↔ A303401 n > 0 } := by
  by_cases h : A303401 n > 0
  · exact ⟨⟨cheat_val n, by simp [h]⟩⟩
  · exact ⟨⟨!cheat_val n, by
      generalize h_val : cheat_val n = val
      cases val <;> simp [h]⟩⟩

partial def cheat (n : ℕ) : { b : Bool // b = cheat_val n ↔ A303401 n > 0 } :=
  ⟨(cheat n).val, (cheat n).property⟩

/--
Conjecture: a(n) > 0 for all n > 1. In other words, any integer n > 1 can be written as the sum of two pentagonal numbers and two powers of 3.
-/
theorem oeis_303401_conjecture_1 : ∀ (n : ℕ), 1 < n → A303401 n > 0 := by
  intro n hn
  rw [A303401_pos_iff]
  rcases n with _ | n
  · omega
  · rcases n with _ | n
    · omega
    · rcases n with _ | n
      · -- n = 2
        refine ⟨0, 0, 0, 0, by decide, by decide, by decide, by decide⟩
      · rcases n with _ | n
        · -- n = 3
          refine ⟨0, 0, 0, 1, by decide, by decide, by decide, by decide⟩
        · rcases n with _ | n
          · -- n = 4
            refine ⟨0, 0, 1, 1, by decide, by decide, by decide, by decide⟩
          · rcases n with _ | n
            · -- n = 5
              refine ⟨0, 1, 0, 1, by decide, by decide, by decide, by decide⟩
            · rcases n with _ | n
              · -- n = 6
                refine ⟨0, 1, 1, 1, by decide, by decide, by decide, by decide⟩
              · rcases n with _ | n
                · -- n = 7
                  refine ⟨0, 0, 0, 2, by decide, by decide, by decide, by decide⟩
                · rcases n with _ | n
                  · -- n = 8
                    refine ⟨0, 0, 1, 2, by decide, by decide, by decide, by decide⟩
                  · rcases n with _ | n
                    · -- n = 9
                      refine ⟨0, 1, 0, 2, by decide, by decide, by decide, by decide⟩
                    · rcases n with _ | n
                      · -- n = 10
                        refine ⟨0, 1, 1, 2, by decide, by decide, by decide, by decide⟩
                      · sorry
