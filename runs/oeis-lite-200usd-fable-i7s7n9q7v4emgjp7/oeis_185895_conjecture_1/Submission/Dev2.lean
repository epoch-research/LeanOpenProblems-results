import Submission.Dev1

open Polynomial Nat Finset

namespace A185895Pf

/-! ### More position arithmetic -/

lemma T_pred (K : ℕ) (h : 1 ≤ K) : T K - K = T (K-1) := by
  have h2 : T ((K-1)+1) = T (K-1) + ((K-1)+1) := T_succ (K-1)
  have h3 : (K-1)+1 = K := by omega
  rw [h3] at h2
  omega

lemma T_ge_self (m : ℕ) : m ≤ T m := by
  induction m with
  | zero => simp [T]
  | succ m ih => rw [T_succ]; omega

lemma blk_mono : Monotone blk := by
  intro a b hab
  by_contra h
  push_neg at h
  have h1 : blk b + 1 ≤ blk a := h
  have h2 := T_mono h1
  have h3 := lt_T_blk_succ b
  have h4 := T_blk_le a
  omega

lemma blk_zero_iff (n : ℕ) : blk n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have h2 := lt_T_blk_succ n
    rw [h] at h2
    have h3 : T (0+1) = 1 := rfl
    omega
  · intro h; subst h
    have := blk_T 0
    simpa [T] using this

lemma nuu_pos_blk_pos (n : ℕ) (h : nuu n ≠ 0) : 1 ≤ blk n := by
  have := nuu_le n
  omega

lemma K0_le_self (n : ℕ) : K0 n ≤ n := by
  unfold K0
  split
  · rename_i h
    have h1 := T_blk_le n
    have h2 := T_ge_self (blk n)
    omega
  · rename_i h
    have h1 := T_blk_le n
    have h2 := T_ge_self (blk n)
    unfold nuu at h
    omega

lemma nuu_add (n : ℕ) : n = T (blk n) + nuu n := by
  have := T_blk_le n
  unfold nuu
  omega

lemma rq_add (n : ℕ) (h : nuu n ≠ 0) : rq n + nuu n = blk n + 1 := by
  have h1 := rq_eq n h
  have h2 := nuu_le n
  omega

lemma rq_le_K0 (n : ℕ) : rq n ≤ K0 n := by
  by_cases h : nuu n = 0
  · rw [rq_zero n h]; omega
  · have h1 := rq_eq n h
    have h2 := nuu_le n
    unfold K0
    rw [if_neg h]
    omega

/-- Parent position: for n ≥ 1, p = n - K0 n sits one block down. -/
lemma parent_blk (n : ℕ) (h : 1 ≤ n) : blk (n - K0 n) = blk n - 1 := by
  by_cases hv : nuu n = 0
  · -- n = T m, m ≥ 1, p = T (m-1)
    have hm : 1 ≤ blk n := by
      by_contra hb
      push_neg at hb
      have : blk n = 0 := by omega
      rw [blk_zero_iff] at this
      omega
    have hK : K0 n = blk n := by unfold K0; rw [if_pos hv]
    have hn : n = T (blk n) := by
      have := nuu_add n
      omega
    have hp : n - K0 n = T (blk n - 1) := by
      rw [hK]
      have h2 : T ((blk n - 1)+1) = T (blk n -1) + ((blk n -1)+1) := T_succ _
      have h3 : (blk n -1)+1 = blk n := by omega
      rw [h3] at h2
      omega
    rw [hp, blk_T]
  · -- p = T (m-1) + (nuu n - 1)
    have hm : 1 ≤ blk n := nuu_pos_blk_pos n hv
    have hK : K0 n = blk n + 1 := by unfold K0; rw [if_neg hv]
    have hnu := nuu_le n
    have h2 : T ((blk n - 1)+1) = T (blk n -1) + ((blk n -1)+1) := T_succ _
    have h3 : (blk n -1)+1 = blk n := by omega
    rw [h3] at h2
    have hp : n - K0 n = T (blk n - 1) + (nuu n - 1) := by
      have := nuu_add n
      omega
    have hb : blk (n - K0 n) = blk n - 1 := by
      apply blk_eq_of
      · omega
      · rw [h3]
        have := nuu_add n
        omega
    exact hb

lemma parent_nuu (n : ℕ) (h : 1 ≤ n) : nuu (n - K0 n) = nuu n - 1 := by
  have hb := parent_blk n h
  have h1 := T_blk_le n
  have hm : 1 ≤ blk n := by
    by_contra hbb
    push_neg at hbb
    have hz : blk n = 0 := by omega
    rw [blk_zero_iff] at hz
    omega
  have h2 : T ((blk n - 1)+1) = T (blk n -1) + ((blk n -1)+1) := T_succ _
  have h3 : (blk n -1)+1 = blk n := by omega
  rw [h3] at h2
  have hnuu : nuu n = n - T (blk n) := rfl
  have hnup : nuu (n - K0 n) = (n - K0 n) - T (blk (n - K0 n)) := rfl
  rw [hb] at hnup
  have hnl := nuu_le n
  by_cases hv : nuu n = 0
  · have hK : K0 n = blk n := by unfold K0; rw [if_pos hv]
    omega
  · have hK : K0 n = blk n + 1 := by unfold K0; rw [if_neg hv]
    omega

/-! ### The weight β -/

def pf : ℕ → ℕ
  | 0 => 1
  | (K+1) => pf K * (K+1)!

lemma pf_pos (K : ℕ) : 0 < pf K := by
  induction K with
  | zero => simp [pf]
  | succ K ih => unfold pf; positivity

def Bq (n : ℕ) : ℚ := ((rq n)! : ℚ) / (pf (K0 n) : ℚ)

lemma Bq_pos (n : ℕ) : 0 < Bq n := by
  unfold Bq
  have h1 := pf_pos (K0 n)
  have h2 := Nat.factorial_pos (rq n)
  positivity

/-- The key seed transfer: β(parent) = K0! * β(n). -/
lemma Bq_parent (n : ℕ) (h : 1 ≤ n) :
    Bq (n - K0 n) = ((K0 n)! : ℚ) * Bq n := by
  have hb := parent_blk n h
  have hn := parent_nuu n h
  set p := n - K0 n with hp
  by_cases hv : nuu n = 0
  · -- n = T m: K0 n = m, parent = T(m-1): rq p = 0, K0 p = m-1
    have hm : 1 ≤ blk n := by
      by_contra hbb
      push_neg at hbb
      have : blk n = 0 := by omega
      rw [blk_zero_iff] at this
      omega
    have hK : K0 n = blk n := by unfold K0; rw [if_pos hv]
    have hnp : nuu p = 0 := by rw [hn, hv]
    have hKp : K0 p = blk n - 1 := by unfold K0; rw [if_pos hnp, hb]
    have hrn : rq n = 0 := rq_zero n hv
    have hrp : rq p = 0 := rq_zero p hnp
    unfold Bq
    rw [hrn, hrp, hKp, hK]
    have hexp : blk n = (blk n - 1) + 1 := by omega
    rw [hexp]
    show (1:ℚ)/ (pf (blk n - 1) : ℚ) = (((blk n - 1) + 1)! : ℚ) * ((1:ℚ) / (pf ((blk n -1)+1) : ℚ))
    have : pf ((blk n - 1)+1) = pf (blk n -1) * ((blk n -1)+1)! := rfl
    rw [this]
    have h1 : (0:ℚ) < (pf (blk n -1) : ℚ) := by exact_mod_cast pf_pos _
    have h2 : (0:ℚ) < (((blk n -1)+1)! : ℚ) := by exact_mod_cast Nat.factorial_pos _
    push_cast
    field_simp
  · have hm : 1 ≤ blk n := nuu_pos_blk_pos n hv
    have hK : K0 n = blk n + 1 := by unfold K0; rw [if_neg hv]
    by_cases hv1 : nuu n = 1
    · -- parent at own triangular: rq p = 0, K0 p = blk n - 1
      have hnp : nuu p = 0 := by rw [hn, hv1]
      have hKp : K0 p = blk n - 1 := by unfold K0; rw [if_pos hnp, hb]
      have hrp : rq p = 0 := rq_zero p hnp
      have hrn : rq n = blk n := by have := rq_eq n hv; omega
      unfold Bq
      rw [hrn, hrp, hKp, hK]
      have hexp1 : blk n + 1 = ((blk n - 1) + 1) + 1 := by omega
      rw [hexp1]
      have e1 : pf (((blk n -1)+1)+1) = pf ((blk n -1)+1) * (((blk n-1)+1)+1)! := rfl
      have e2 : pf ((blk n - 1)+1) = pf (blk n -1) * ((blk n -1)+1)! := rfl
      rw [e1, e2]
      have hbn : blk n = (blk n - 1) + 1 := by omega
      rw [hbn]
      have h1 : (0:ℚ) < (pf (blk n -1) : ℚ) := by exact_mod_cast pf_pos _
      have h2 : (0:ℚ) < ((((blk n -1))+1)! : ℚ) := by exact_mod_cast Nat.factorial_pos _
      have h3 : (0:ℚ) < (((((blk n -1))+1)+1)! : ℚ) := by exact_mod_cast Nat.factorial_pos _
      push_cast
      field_simp
      try ring
    · -- nuu n ≥ 2: rq p = rq n, K0 p = blk n
      have hnp : nuu p = nuu n - 1 := hn
      have hnp0 : nuu p ≠ 0 := by omega
      have hKp : K0 p = blk n := by
        unfold K0
        rw [if_neg hnp0, hb]
        omega
      have hrp : rq p = rq n := by
        have e1 := rq_eq p hnp0
        have e2 := rq_eq n hv
        have e3 := nuu_le n
        rw [hnp, hb] at e1
        omega
      unfold Bq
      rw [hrp, hKp, hK]
      have e1 : pf (blk n + 1) = pf (blk n) * (blk n + 1)! := rfl
      rw [e1]
      have h1 : (0:ℚ) < (pf (blk n) : ℚ) := by exact_mod_cast pf_pos _
      have h2 : (0:ℚ) < ((blk n +1)! : ℚ) := by exact_mod_cast Nat.factorial_pos _
      have h3 : (0:ℚ) < ((rq n)! : ℚ) := by exact_mod_cast Nat.factorial_pos (rq n)
      push_cast
      field_simp
      try ring

end A185895Pf
