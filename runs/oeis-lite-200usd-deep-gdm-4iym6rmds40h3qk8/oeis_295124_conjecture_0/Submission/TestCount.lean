import FormalConjectures.Util.ProblemImports

open Nat Finset

def count_divisors_aux (n : ℕ) (d : ℕ) (fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => 0
  | f + 1 =>
    if d * d > n then 0
    else if d * d == n then 1
    else if n % d == 0 then 2 + count_divisors_aux n (d + 1) f
    else count_divisors_aux n (d + 1) f

lemma count_divisors_aux_le (n : ℕ) (hn : n > 0) (d f : ℕ) :
    count_divisors_aux n d f ≤ 2 * ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f)).card := by
  induction f generalizing d with
  | zero =>
    unfold count_divisors_aux
    simp
  | succ f ih =>
    unfold count_divisors_aux
    have h_range : d + 1 + f = d + f + 1 := by ring
    split_ifs with h1 h2 h3
    · simp
    · -- d * d == n
      have h_eq : d * d = n := of_decide_eq_true h2
      have hd_dvd : d ∣ n := by
        use d
        exact h_eq.symm
      have hd_mem : d ∈ Nat.divisors n := by
        rw [Nat.mem_divisors]
        exact ⟨hd_dvd, hn.ne'⟩
      have hd_filter : d ∈ ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)) := by
        simp only [mem_filter]
        refine ⟨hd_mem, by omega, by omega⟩
      have h_card_pos : 0 < ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)).card := by
        exact card_pos.mpr ⟨d, hd_filter⟩
      change 1 ≤ 2 * ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)).card
      omega
    · -- n % d == 0
      have hd_dvd : d ∣ n := by
        exact Nat.dvd_of_mod_eq_zero (of_decide_eq_true h3)
      have hd_mem : d ∈ Nat.divisors n := by
        rw [Nat.mem_divisors]
        exact ⟨hd_dvd, hn.ne'⟩
      have hd_mem_S2 : d ∈ ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)) := by
        simp only [mem_filter]
        refine ⟨hd_mem, by omega, by omega⟩
      have hd_not_mem_S1 : d ∉ ((Nat.divisors n).filter (fun x => d + 1 ≤ x ∧ x < d + 1 + f)) := by
        simp only [mem_filter]
        rintro ⟨_, h_le, _⟩
        omega
      have h_eq_insert : ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)) =
          insert d ((Nat.divisors n).filter (fun x => d + 1 ≤ x ∧ x < d + 1 + f)) := by
        ext x
        simp only [mem_filter, mem_insert]
        constructor
        · rintro ⟨hx_mem, hx_ge, hx_lt⟩
          have h_cases : x = d ∨ x ≥ d + 1 := by omega
          rcases h_cases with rfl | h_ge
          · left; rfl
          · right
            refine ⟨hx_mem, by omega, by omega⟩
        · rintro (rfl | ⟨hx_mem, hx_ge, hx_lt⟩)
          · refine ⟨hd_mem, by omega, by omega⟩
          · refine ⟨hx_mem, by omega, by omega⟩
      have h_card : ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)).card =
          ((Nat.divisors n).filter (fun x => d + 1 ≤ x ∧ x < d + 1 + f)).card + 1 := by
        rw [h_eq_insert, card_insert_of_notMem hd_not_mem_S1]
      have ih_val := ih (d + 1)
      change 2 + count_divisors_aux n (d + 1) f ≤ 2 * ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)).card
      rw [h_card]
      omega
    · -- n % d != 0
      have hd_not_mem : d ∉ Nat.divisors n := by
        rw [Nat.mem_divisors]
        rintro ⟨hd_dvd, _⟩
        have h_mod_0 : n % d = 0 := Nat.mod_eq_zero_of_dvd hd_dvd
        have h3_eq : (n % d == 0) = true := by
          exact decide_eq_true_iff.mpr h_mod_0
        rw [h3_eq] at h3
        contradiction
      have h_eq : ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)) =
          ((Nat.divisors n).filter (fun x => d + 1 ≤ x ∧ x < d + 1 + f)) := by
        ext x
        simp only [mem_filter]
        constructor
        · rintro ⟨hx_mem, hx_ge, hx_lt⟩
          have h_ne : x ≠ d := by
            intro h_eq
            subst h_eq
            exact hd_not_mem hx_mem
          refine ⟨hx_mem, by omega, by omega⟩
        · rintro ⟨hx_mem, hx_ge, hx_lt⟩
          refine ⟨hx_mem, by omega, by omega⟩
      have ih_val := ih (d+1)
      change count_divisors_aux n (d + 1) f ≤ 2 * ((Nat.divisors n).filter (fun x => d ≤ x ∧ x < d + f + 1)).card
      rw [h_eq]
      omega

