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

lemma sum_pos_of_mem {α} [DecidableEq α] (s : Finset α) (f : α → ℕ) {a : α}
    (ha : a ∈ s) (hpos : 0 < f a) : 0 < ∑ x ∈ s, f x := by
  exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨a, ha, hpos⟩

lemma A308934_pos_of_witness (n a b c d x y : ℕ)
    (ha : a < Nat.log 2 n / 2 + 1)
    (hb : b < Nat.log 3 n / 2 + 1)
    (hc : c < Nat.log 2 n / 2 + 1)
    (hd : d < Nat.log 3 n / 2 + 1)
    (hge : ¬ (2^a * 3^b < 2^c * 3^d))
    (hy : y < Nat.sqrt (n / 2) + 1)
    (heq : (2^a * 3^b)^2 + (2^c * 3^d)^2 + x^2 + 2 * y^2 = n) :
    A308934 n > 0 := by
  unfold A308934
  dsimp only
  -- need prove nested sum positive by selecting a,b,c,d and card positive by selecting y
  apply sum_pos_of_mem
  · simpa using ha
  · apply sum_pos_of_mem
    · simpa using hb
    · apply sum_pos_of_mem
      · simpa using hc
      · apply sum_pos_of_mem
        · simpa using hd
        · rw [if_neg hge]
          have hbasele : (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 3 ^ d) ^ 2 ≤ n := by
            rw [← heq]
            omega
          rw [if_neg (not_lt.mpr hbasele)]
          apply Finset.card_pos.mpr
          refine ⟨y, ?_⟩
          simp only [mem_filter, mem_range]
          constructor
          · exact hy
          · constructor
            · rw [← heq]
              omega
            · have hsub : n - ((2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 3 ^ d) ^ 2 + 2 * y ^ 2) = x^2 := by
                rw [← heq]
                omega
              rw [hsub, Nat.sqrt_eq']
