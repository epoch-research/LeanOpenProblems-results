import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 200000

open Nat Finset

def totient_leaf_loop (n : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, L, R =>
    if L > R then 0
    else
      let count := if L.Coprime n then 1 else 0
      count + totient_leaf_loop n fuel (L + 1) R

def totient_range (n : Nat) : Nat → Nat → Nat → Nat
  | 0, L, R => totient_leaf_loop n 2050 L R
  | fuel + 1, L, R =>
    if L > R then 0
    else if L = R then
      if L.Coprime n then 1 else 0
    else
      let mid := (L + R) / 2
      totient_range n fuel L mid + totient_range n fuel (mid + 1) R

def totient_fast (n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else totient_range n 10 1 (n - 1)

lemma Ico_split {L mid R : ℕ} (h1 : L ≤ mid) (h2 : mid < R) :
    Ico L R = Ico L (mid + 1) ∪ Ico (mid + 1) R := by
  ext x
  simp only [mem_Ico, mem_union]
  omega

lemma card_filter_union_disjoint {α : Type _} [DecidableEq α] (s1 s2 : Finset α) (p : α → Prop) [DecidablePred p]
    (h : Disjoint s1 s2) :
    (filter p (s1 ∪ s2)).card = (filter p s1).card + (filter p s2).card := by
  rw [filter_union, card_union_of_disjoint]
  rw [disjoint_iff_ne]
  intro x hx y hy hxy
  simp only [mem_filter] at hx hy
  rw [disjoint_iff_ne] at h
  exact @h x hx.left y hy.left hxy

lemma totient_leaf_loop_gt (n : Nat) (fuel : Nat) : ∀ L R, L > R → totient_leaf_loop n fuel L R = 0 := by
  induction fuel with
  | zero => intro L R h; rfl
  | succ f ih =>
    intro L R h
    dsimp [totient_leaf_loop]
    rw [if_pos h]

lemma totient_leaf_loop_eq (n : Nat) (fuel : Nat) : ∀ L R, R - L < fuel →
    (L > R → totient_leaf_loop n fuel L R = 0) ∧
    (L ≤ R → totient_leaf_loop n fuel L R = ((Ico L (R + 1)).filter (·.Coprime n)).card) := by
  induction fuel with
  | zero =>
    intro L R h_lt
    omega
  | succ fuel ih =>
    intro L R h_lt
    constructor
    · intro h_gt
      exact totient_leaf_loop_gt n (fuel + 1) L R h_gt
    · intro h_le
      dsimp [totient_leaf_loop]
      rw [if_neg (by omega)]
      by_cases h_cop : L.Coprime n
      · rw [if_pos h_cop]
        by_cases h_eq : L = R
        · rw [h_eq] at h_cop ⊢
          have h_range : Ico R (R + 1) = {R} := by ext x; simp
          rw [h_range, filter_singleton, if_pos h_cop]
          have h_zero : totient_leaf_loop n fuel (R + 1) R = 0 := totient_leaf_loop_gt n fuel (R + 1) R (by omega)
          rw [h_zero]
          rfl
        · have h_lt_next : R - (L + 1) < fuel := by omega
          have ih_val := (ih (L + 1) R h_lt_next).right (by omega)
          rw [ih_val]
          have h_split : Ico L (R + 1) = {L} ∪ Ico (L + 1) (R + 1) := by
            ext x
            simp only [mem_Ico, mem_union, mem_singleton]
            omega
          rw [h_split, filter_union, card_union_of_disjoint]
          · simp only [filter_singleton, if_pos h_cop, card_singleton]
          · rw [disjoint_iff_ne]
            intro x hx y hy hxy
            simp only [mem_filter, mem_singleton, mem_Ico] at hx hy
            omega
      · rw [if_neg h_cop]
        by_cases h_eq : L = R
        · rw [h_eq] at h_cop ⊢
          have h_range : Ico R (R + 1) = {R} := by ext x; simp
          rw [h_range, filter_singleton, if_neg h_cop]
          have h_zero : totient_leaf_loop n fuel (R + 1) R = 0 := totient_leaf_loop_gt n fuel (R + 1) R (by omega)
          rw [h_zero]
          rfl
        · have h_lt_next : R - (L + 1) < fuel := by omega
          have ih_val := (ih (L + 1) R h_lt_next).right (by omega)
          rw [ih_val]
          have h_split : Ico L (R + 1) = {L} ∪ Ico (L + 1) (R + 1) := by
            ext x
            simp only [mem_Ico, mem_union, mem_singleton]
            omega
          rw [h_split, filter_union, card_union_of_disjoint]
          · simp only [filter_singleton, if_neg h_cop, card_empty, zero_add]
          · rw [disjoint_iff_ne]
            intro x hx y hy hxy
            simp only [mem_filter, mem_singleton, mem_Ico] at hx hy
            omega

lemma totient_range_eq (n : Nat) (fuel : Nat) : ∀ L R, R - L < 2050 * 2 ^ fuel →
    (L > R → totient_range n fuel L R = 0) ∧
    (L ≤ R → totient_range n fuel L R = ((Ico L (R + 1)).filter (·.Coprime n)).card) := by
  induction fuel with
  | zero =>
    intro L R h_lt
    simp only [Nat.pow_zero, mul_one] at h_lt
    constructor
    · intro h_gt; dsimp [totient_range]
      exact (totient_leaf_loop_eq n 2050 L R h_lt).left h_gt
    · intro h_le; dsimp [totient_range]
      exact (totient_leaf_loop_eq n 2050 L R h_lt).right h_le
  | succ fuel ih =>
    intro L R h_lt
    constructor
    · intro h_gt
      dsimp [totient_range]
      rw [if_pos h_gt]
    · intro h_le
      dsimp [totient_range]
      by_cases h_eq : L = R
      · rw [if_neg (by omega), if_pos h_eq]
        rw [h_eq]
        by_cases h_cop : R.Coprime n
        · have h_range : Ico R (R + 1) = {R} := by ext x; simp
          rw [if_pos h_cop]
          simp [h_range, filter_singleton, h_cop, if_pos h_cop]
        · have h_range : Ico R (R + 1) = {R} := by ext x; simp
          rw [if_neg h_cop]
          simp [h_range, filter_singleton, h_cop]
      · have h_lt_R : L < R := by omega
        rw [if_neg (by omega), if_neg h_eq]
        let mid := (L + R) / 2
        have h_mid_ge : L ≤ mid := by omega
        have h_mid_lt : mid < R := by omega
        have h_lt_left : mid - L < 2050 * 2 ^ fuel := by
          have : 2050 * 2 ^ (fuel + 1) = 2050 * 2 ^ fuel * 2 := by ring
          omega
        have h_lt_right : R - (mid + 1) < 2050 * 2 ^ fuel := by
          have : 2050 * 2 ^ (fuel + 1) = 2050 * 2 ^ fuel * 2 := by ring
          omega
        have ih_left := (ih L mid h_lt_left).right h_mid_ge
        rw [ih_left]
        have ih_right := (ih (mid + 1) R h_lt_right).right (by omega)
        rw [ih_right]
        have h_split : Ico L (R + 1) = Ico L (mid + 1) ∪ Ico (mid + 1) (R + 1) := by
          apply Ico_split h_mid_ge (by omega)
        rw [h_split]
        have h_disj : Disjoint (Ico L (mid + 1)) (Ico (mid + 1) (R + 1)) := by
          rw [disjoint_iff_ne]
          intro x hx y hy hxy
          simp only [mem_Ico] at hx hy
          omega
        rw [card_filter_union_disjoint _ _ _ h_disj]

theorem totient_fast_eq_totient (n : Nat) (h_lim : n ≤ 2 * 10^6) : totient_fast n = Nat.totient n := by
  by_cases h0 : n = 0
  · rw [h0]
    rfl
  · by_cases h1 : n = 1
    · rw [h1]
      rfl
    · have hn : n > 1 := by omega
      dsimp [totient_fast]
      rw [if_neg h0, if_neg h1]
      have h_eq := (totient_range_eq n 10 1 (n - 1) (by omega)).right (by omega)
      rw [h_eq]
      have h_sub : n - 1 + 1 = n := by omega
      rw [h_sub]
      rw [Nat.totient]
      have h_range : range n = insert 0 (Ico 1 n) := by
        ext x
        simp only [mem_range, mem_insert, mem_Ico]
        omega
      rw [h_range, filter_insert]
      have h_not_cop : ¬ n.Coprime 0 := by
        intro hc
        rw [Nat.Coprime] at hc
        rw [Nat.gcd_zero_right] at hc
        omega
      rw [if_neg h_not_cop]
      congr 1
      ext x
      simp only [mem_filter, mem_Ico]
      rw [Nat.coprime_comm]

theorem test_eval_large : totient_fast 10000 = 4000 := by decide
