import FormalConjectures.Util.ProblemImports
open Nat Finset

def A308934 (n : ℕ) : ℕ :=
  let max_e2 := (Nat.log 2 n / 2) + 1
  let max_e3 := (Nat.log 3 n / 2) + 1
  let max_y := Nat.sqrt (n / 2)
  let r (k l : ℕ) : ℕ := (2^k * 3^l)
  let is_square (m : ℕ) : Prop := (Nat.sqrt m) ^ 2 = m
  Finset.sum (range max_e2) fun a =>
    Finset.sum (range max_e3) fun b =>
      let r_val := r a b
      Finset.sum (range max_e2) fun c =>
        Finset.sum (range max_e3) fun d =>
          let s_val := r c d
          if r_val < s_val then 0 else
          if r_val^2 + s_val^2 > n then 0 else
          Finset.card $ Finset.filter (fun y =>
            let k := r_val^2 + s_val^2 + 2 * y^2
            k ≤ n ∧ is_square (n - k)
          ) (range (max_y + 1))

lemma exists_mem_of_sum_pos {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (h : 0 < ∑ x ∈ s, f x) : ∃ a ∈ s, 0 < f a := by
  by_contra H
  push_neg at H
  have hz : ∑ x ∈ s, f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact Nat.eq_zero_of_le_zero (H x hx)
  omega

lemma A308934_pos_iff_exists_witness (n : ℕ) :
    A308934 n > 0 ↔ ∃ a b c d x y : ℕ,
      a < Nat.log 2 n / 2 + 1 ∧ b < Nat.log 3 n / 2 + 1 ∧
      c < Nat.log 2 n / 2 + 1 ∧ d < Nat.log 3 n / 2 + 1 ∧
      ¬ (2^a * 3^b < 2^c * 3^d) ∧
      y < Nat.sqrt (n / 2) + 1 ∧
      (2^a * 3^b)^2 + (2^c * 3^d)^2 + x^2 + 2*y^2 = n := by
  constructor
  · intro h
    unfold A308934 at h
    dsimp only at h
    obtain ⟨a, ha, h1⟩ := exists_mem_of_sum_pos _ _ h
    obtain ⟨b, hb, h2⟩ := exists_mem_of_sum_pos _ _ h1
    obtain ⟨c, hc, h3⟩ := exists_mem_of_sum_pos _ _ h2
    obtain ⟨d, hd, h4⟩ := exists_mem_of_sum_pos _ _ h3
    by_cases hlt : 2 ^ a * 3 ^ b < 2 ^ c * 3 ^ d
    · simp [hlt] at h4
    · rw [if_neg hlt] at h4
      by_cases hgt : n < (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 3 ^ d) ^ 2
      · simp [hgt] at h4
      · rw [if_neg hgt] at h4
        have hcard : 0 < (filter (fun y =>
            (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 3 ^ d) ^ 2 + 2 * y ^ 2 ≤ n ∧
              (n - ((2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 3 ^ d) ^ 2 + 2 * y ^ 2)).sqrt ^ 2 =
                n - ((2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 3 ^ d) ^ 2 + 2 * y ^ 2))
            (range ((n / 2).sqrt + 1))).card := by simpa using h4
        obtain ⟨y, hy⟩ := Finset.card_pos.mp hcard
        simp only [mem_filter, mem_range] at hy
        rcases hy with ⟨hyr, hle, hsqrt⟩
        refine ⟨a,b,c,d, Nat.sqrt (n - ((2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 3 ^ d) ^ 2 + 2 * y ^ 2)), y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa using ha
        · simpa using hb
        · simpa using hc
        · simpa using hd
        · exact hlt
        · simpa using hyr
        · have hle' : (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 3 ^ d) ^ 2 + 2 * y ^ 2 ≤ n := hle
          rw [hsqrt]
          omega
  · rintro ⟨a,b,c,d,x,y,ha,hb,hc,hd,hge,hy,heq⟩
    -- use previous witness lemma could be copied; leave as exact? for now
    sorry
