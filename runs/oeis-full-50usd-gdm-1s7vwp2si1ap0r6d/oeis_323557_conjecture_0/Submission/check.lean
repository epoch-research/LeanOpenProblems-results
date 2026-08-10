import Mathlib

open Nat

-- Include necessary lemmas from Scratch
lemma div2_lt_self_of_pos {n : ℕ} (h : 0 < n) : div2 n < n := by
  have h1 := bodd_add_div2 n
  have hb : n.bodd.toNat ≤ 1 := by
    cases n.bodd <;> decide
  omega

#check Nat.and_ldiff_self_right
#check Nat.and_ldiff_self_left
#check Nat.ldiff_and_self_right
#check Nat.ldiff_self_and
#check Nat.ldiff_self_right
#check Nat.ldiff_self_left
lemma choose_mod_two_eq (n k : ℕ) : (n.choose k : ZMod 2) = (n % 2).choose (k % 2) * (n / 2).choose (k / 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h_rhs : ((n % 2).choose (k % 2) * (n / 2).choose (k / 2) : ZMod 2) = (((n % 2).choose (k % 2) * (n / 2).choose (k / 2) : ℕ) : ZMod 2) := by push_cast; rfl
  rw [h_rhs]
  rw [ZMod.natCast_eq_natCast_iff]
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

lemma and_eq_self_of_choose_mod_two_eq_one (n k : ℕ) (h : (n.choose k : ZMod 2) = 1) : k &&& n = k := by
  induction n using Nat.strong_induction_on generalizing k with
  | h n ih =>
    by_cases hn : n = 0
    · rw [hn] at h
      have hk : k = 0 := by
        by_contra hk_ne
        have : Nat.choose 0 k = 0 := Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk_ne)
        rw [this] at h
        exact zero_ne_one h
      rw [hk]
      change bitwise and 0 n = 0
      rw [bitwise_zero_left]
      rfl
    · rw [choose_mod_two_eq] at h
      have h_mul : ∀ (x y : ZMod 2), x * y = 1 → x = 1 ∧ y = 1 := by
        decide
      rcases h_mul _ _ h with ⟨h1, h2⟩
      have h_div_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)
      have h_div2 : div2 n = n / 2 := div2_val n
      have h_k_div2 : div2 k = k / 2 := div2_val k
      have h2_eq : ((n / 2).choose (k / 2) : ZMod 2) = 1 := h2
      have ih_res := ih (n / 2) h_div_lt (k / 2) h2_eq
      have h_bodd : (bodd k = false) ∨ (bodd k = true ∧ bodd n = true) := by
        cases hk : bodd k <;> cases hn2 : bodd n
        · left; rfl
        · left; rfl
        · have h_n_mod_eq : n % 2 = n.bodd.toNat := by
            have := bodd_add_div2 n
            omega
          have h_k_mod_eq : k % 2 = k.bodd.toNat := by
            have := bodd_add_div2 k
            omega
          rw [h_n_mod_eq, hn2, h_k_mod_eq, hk] at h1
          simp at h1
        · right; exact ⟨rfl, rfl⟩
      have h_k_eq : k = bit (bodd k) (div2 k) := (bit_bodd_div2 k).symm
      have h_n_eq : n = bit (bodd n) (div2 n) := (bit_bodd_div2 n).symm
      rw [h_k_eq, h_n_eq]
      rw [land_bit]
      rw [h_div2, h_k_div2]
      rw [ih_res]
      rcases h_bodd with hk_false | ⟨hk_true, hn_true⟩
      · rw [hk_false]
        simp
      · rw [hk_true, hn_true]
        simp

lemma land_zero_of_and_add_eq_self (n j : ℕ) (h : j &&& (n + j) = j) : n &&& j = 0 := by
  generalize h_sum : n + j = sum
  induction sum using Nat.strong_induction_on generalizing n j with
  | h sum ih =>
    by_cases hj : j = 0
    · rw [hj]
      rw [hj] at h
      change bitwise and n 0 = 0
      rw [bitwise_zero_right]
      rfl
    · by_cases hn : n = 0
      · rw [hn]
        change bitwise and 0 j = 0
        rw [bitwise_zero_left]
        rfl
      · have h_sum_pos : 0 < n + j := by omega
        have h_div_lt : div2 (n + j) < n + j := div2_lt_self_of_pos h_sum_pos
        have h_j_eq : j = bit (bodd j) (div2 j) := (bit_bodd_div2 j).symm
        have h_n_eq : n = bit (bodd n) (div2 n) := (bit_bodd_div2 n).symm
        have h_sum_eq : n + j = bit (bodd (n + j)) (div2 (n + j)) := (bit_bodd_div2 (n + j)).symm
        have h_and : bit (bodd j) (div2 j) &&& bit (bodd (n + j)) (div2 (n + j)) = bit (bodd j) (div2 j) := by
          rw [← h_j_eq, ← h_sum_eq]
          exact h
        rw [land_bit] at h_and
        have h_bodd : (bodd j && bodd (n + j)) = bodd j := by
          have h_b := congr_arg bodd h_and
          rw [bodd_bit, bodd_bit] at h_b
          exact h_b
        have h_div : div2 j &&& div2 (n + j) = div2 j := by
          have h_d := congr_arg div2 h_and
          rw [div2_bit, div2_bit] at h_d
          exact h_d
        have h_bodd_n_j : (bodd n && bodd j) = false := by
          cases h_bj : bodd j
          · cases bodd n <;> rfl
          · cases h_bn : bodd n
            · rfl
            · have h_b_add : bodd (n + j) = false := by
                rw [bodd_add, h_bj, h_bn]
                rfl
              rw [h_bj, h_b_add] at h_bodd
              contradiction
        have h_div_add : div2 (n + j) = div2 n + div2 j := by
          have h_add_eq : n + j = 2 * div2 n + (bodd n).toNat + (2 * div2 j + (bodd j).toNat) := by
            have h1 := bodd_add_div2 n
            have h2 := bodd_add_div2 j
            omega
          have h_div_eq : div2 (n + j) = (n + j) / 2 := div2_val (n + j)
          rw [h_div_eq, h_add_eq]
          cases h_b : bodd n <;> cases h_bj : bodd j
          · simp; omega
          · simp; omega
          · simp; omega
          · rw [h_b, h_bj] at h_bodd_n_j
            contradiction
        rw [h_div_add] at h_div
        have h_lt : div2 n + div2 j < sum := by
          rw [← h_sum, ← h_div_add]
          exact h_div_lt
        have h_ih := ih (div2 n + div2 j) h_lt (div2 n) (div2 j) h_div rfl
        rw [h_n_eq, h_j_eq]
        rw [land_bit]
        rw [h_bodd_n_j, h_ih]
        rfl

lemma sum_mod2_eq_zero_of_free_involution {α : Type*} [DecidableEq α] (S : Finset α)
  (g : α → α) (hg : ∀ x ∈ S, g x ∈ S ∧ g (g x) = x ∧ g x ≠ x)
  (f : α → ZMod 2) (hf : ∀ x ∈ S, f (g x) = f x) :
  S.sum f = 0 := by
  generalize h_card : S.card = c
  induction c using Nat.strong_induction_on generalizing S with
  | h c ih =>
  by_cases hS : S.Nonempty
  · obtain ⟨x, hx⟩ := hS
    have hgx : g x ∈ S := (hg x hx).1
    have hggx : g (g x) = x := (hg x hx).2.1
    have hg_ne : g x ≠ x := (hg x hx).2.2
    let S' := S.erase x |>.erase (g x)
    have h_S'_card : S'.card < S.card := by
      have hg_mem : g x ∈ S.erase x := by
        rw [Finset.mem_erase]
        exact ⟨hg_ne, hgx⟩
      rw [Finset.card_erase_of_mem hg_mem, Finset.card_erase_of_mem hx]
      have : S.card > 0 := Finset.card_pos.mpr ⟨x, hx⟩
      omega
    have hg' : ∀ y ∈ S', g y ∈ S' ∧ g (g y) = y ∧ g y ≠ y := by
      intro y hy
      rw [Finset.mem_erase, Finset.mem_erase] at hy
      have hy_S : y ∈ S := hy.2.2
      have hgy : g y ∈ S := (hg y hy_S).1
      have hggy : g (g y) = y := (hg y hy_S).2.1
      have hgy_ne : g y ≠ y := (hg y hy_S).2.2
      refine ⟨?_, hggy, hgy_ne⟩
      rw [Finset.mem_erase, Finset.mem_erase]
      refine ⟨?_, ?_, hgy⟩
      · intro h
        have h_eq : g (g y) = g (g x) := congr_arg g h
        rw [hggy, hggx] at h_eq
        exact hy.2.1 h_eq
      · intro h
        have h_eq : g (g y) = g x := congr_arg g h
        rw [hggy] at h_eq
        exact hy.1 h_eq
    have hf' : ∀ y ∈ S', f (g y) = f y := by
      intro y hy
      rw [Finset.mem_erase, Finset.mem_erase] at hy
      exact hf y hy.2.2
    have h_S'_card_c : S'.card < c := by
      rw [← h_card]
      exact h_S'_card
    have h_sum_S' := ih S'.card h_S'_card_c S' hg' hf' rfl
    have h_split : S = S' ∪ {x, g x} := by
      ext y
      simp [S']
      by_cases h_yx : y = x
      · simp [h_yx, hx]
      · by_cases h_ygx : y = g x
        · simp [h_ygx, hgx]
        · simp [h_yx, h_ygx]
    rw [h_split]
    have h_disj : Disjoint S' {x, g x} := by
      rw [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]
      simp [S']
    rw [Finset.sum_union h_disj]
    rw [h_sum_S']
    have h_sum_doublet : ({x, g x} : Finset α).sum f = 0 := by
      rw [Finset.sum_pair hg_ne.symm]
      rw [hf x hx]
      have h_double : ∀ (y : ZMod 2), y + y = 0 := by decide
      exact h_double (f x)
    rw [h_sum_doublet, zero_add]
  · rw [Finset.not_nonempty_iff_eq_empty] at hS
    rw [hS]
    exact Finset.sum_empty











