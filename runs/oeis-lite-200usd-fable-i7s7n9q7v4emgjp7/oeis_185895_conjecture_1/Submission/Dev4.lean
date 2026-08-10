import Submission.Dev3

open Polynomial Nat Finset

namespace A185895Pf

/-! ### Table facts extracted from the kernel checks -/

lemma xtlr_ok (c : ℕ) (h : c ≤ 527) : XTLR.getD (527-c) 0 = XTL.getD c 0 := by
  have h1 := xtlr_ok_b
  rw [List.all_eq_true] at h1
  exact of_decide_eq_true (h1 c (List.mem_range.mpr (by omega)))

lemma prlr_ok (c : ℕ) (h : c ≤ 527) : PRLR.getD (527-c) 0 = blk c := by
  have h1 := prlr_ok_b
  rw [List.all_eq_true] at h1
  exact of_decide_eq_true (h1 c (List.mem_range.mpr (by omega)))

lemma xi_eq_getD (c : ℕ) (h : c ≤ 527) : Xi c = XTL.getD c 1 := by
  unfold Xi
  rw [if_pos h]

lemma xi_eq_getD0 (c : ℕ) (h : c ≤ 527) : Xi c = XTL.getD c 0 := by
  have hlen : c < XTL.length := by rw [xtl_len]; omega
  rw [xi_eq_getD c h, List.getD_eq_getElem XTL 1 hlen, List.getD_eq_getElem XTL 0 hlen]

lemma xi_pos_low (c : ℕ) (h : c ≤ 527) : 0 < Xi c := by
  rw [xi_eq_getD0 c h]
  have hlen : c < XTL.length := by rw [xtl_len]; omega
  rw [List.getD_eq_getElem XTL 0 hlen]
  have h1 := xtl_pos_b
  rw [List.all_eq_true] at h1
  exact of_decide_eq_true (h1 _ (XTL.getElem_mem hlen))

/-! ### foldr-min helpers -/

lemma pos_foldr_min (l : List ℚ) (a : ℚ) (ha : 0 < a) (h : ∀ y ∈ l, 0 < y) :
    0 < l.foldr min a := by
  induction l with
  | nil => simpa using ha
  | cons x xs ih =>
    simp only [List.foldr_cons]
    exact lt_min (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

lemma foldr_min_le_mem (l : List ℚ) (a y : ℚ) (h : y ∈ l) : l.foldr min a ≤ y := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with h1 | h1
    · subst h1; exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (ih h1)

lemma le_foldr_min (l : List ℚ) (a x : ℚ) (ha : x ≤ a) (h : ∀ y ∈ l, x ≤ y) :
    x ≤ l.foldr min a := by
  induction l with
  | nil => simpa using ha
  | cons z zs ih =>
    simp only [List.foldr_cons]
    exact le_min (h z (by simp)) (ih (fun y hy => h y (by simp [hy])))

lemma planes_pos : ∀ P ∈ planes, 0 < P.1 ∧ 0 < P.2 := by decide +kernel

lemma pval_pos (P : ℚ × ℚ) (n : ℕ) (h : 0 < P.1 ∧ 0 < P.2) : 0 < pval P n := by
  unfold pval
  have := h.1
  have := h.2
  positivity

lemma pmin_pos (n : ℕ) : 0 < pmin n := by
  unfold pmin
  apply pos_foldr_min
  · exact pval_pos _ _ (by norm_num)
  · intro y hy
    rw [List.mem_map] at hy
    obtain ⟨P, hP, hPy⟩ := hy
    rw [← hPy]
    exact pval_pos _ _ (planes_pos P hP)

lemma xi_pos (n : ℕ) : 0 < Xi n := by
  by_cases h : n ≤ 527
  · exact xi_pos_low n h
  · unfold Xi
    rw [if_neg h]
    exact pmin_pos n

lemma xi_le_pval (n : ℕ) (hn : 527 < n) (P : ℚ × ℚ) (hP : P ∈ planes) :
    Xi n ≤ pval P n := by
  unfold Xi
  rw [if_neg (by omega)]
  exact foldr_min_le_mem _ _ _ (List.mem_map.mpr ⟨P, hP, rfl⟩)

lemma le_xi_of_planes (n : ℕ) (hn : 527 < n) (x : ℚ)
    (h : ∀ P ∈ planes, x ≤ pval P n) : x ≤ Xi n := by
  unfold Xi
  rw [if_neg (by omega)]
  exact le_foldr_min _ _ _ (h _ (by decide +kernel)) (fun y hy => by
    rw [List.mem_map] at hy
    obtain ⟨P, hP, hPy⟩ := hy
    rw [← hPy]
    exact h P hP)

/-! ### The dyadic rounding and the β-ratio identity -/

lemma le_r45 (x : ℚ) : x ≤ r45 x := by
  unfold r45
  have h45 : (0:ℚ) < 2^45 := by positivity
  rw [le_div_iff₀ h45]
  have h := Int.lt_floor_add_one (x * 2^45)
  have h2 : x * 2^45 ≤ ((⌊x * 2^45⌋ + 1 : ℤ) : ℚ) := by
    push_cast
    exact le_of_lt h
  exact h2

/-- the fundamental one-step β ratio -/
lemma Bq_pred (c : ℕ) (h : 1 ≤ c) : Bq (c-1) = fdefFrom c (blk c) * Bq c := by
  have hT : T (blk c) = blk c * (blk c + 1)/2 := rfl
  have hnu : nuu c = c - blk c * (blk c + 1)/2 := rfl
  by_cases h2 : 2 ≤ nuu c
  · -- same block, rq increments
    have hm : 1 ≤ blk c := nuu_pos_blk_pos c (by omega)
    have hb1 := T_blk_le c
    have hb2 := lt_T_blk_succ c
    have hTs : T (blk c + 1) = T (blk c) + (blk c + 1) := T_succ _
    have hbc : blk (c-1) = blk c := by
      apply blk_eq_of
      · unfold nuu at h2; omega
      · omega
    have hnuc : nuu (c-1) = nuu c - 1 := by
      unfold nuu
      rw [hbc]
      unfold nuu at h2
      omega
    have hK : K0 c = blk c + 1 := by unfold K0; rw [if_neg (by omega)]
    have hKc : K0 (c-1) = blk c + 1 := by
      unfold K0
      rw [if_neg (by omega), hbc]
    have hrq : rq (c-1) = rq c + 1 := by
      unfold rq
      rw [hKc, hK]
      have := n_le_T_K0 c
      rw [hK] at this
      omega
    have hf : fdefFrom c (blk c) = ((rq c + 1 : ℕ) : ℚ) := by
      unfold fdefFrom
      rw [if_pos (by rw [← hT, ← hnu] at *; exact h2)]
      congr 1
      unfold rq
      rw [hK]
      have hT2 : T (blk c + 1) = (blk c + 1) * (blk c + 2)/2 := rfl
      have := n_le_T_K0 c
      rw [hK] at this
      rw [hT2] at this ⊢
      omega
    unfold Bq
    rw [hrq, hKc, hK, hf]
    have h1 : (0:ℚ) < (pf (blk c + 1) : ℚ) := by exact_mod_cast pf_pos _
    rw [Nat.factorial_succ]
    push_cast
    ring
  · by_cases h1 : nuu c = 1
    · -- c - 1 = T (blk c)
      have hm : 1 ≤ blk c := nuu_pos_blk_pos c (by omega)
      have hb1 := T_blk_le c
      have hc1 : c - 1 = T (blk c) := by unfold nuu at h1; omega
      have hbc : blk (c-1) = blk c := by rw [hc1, blk_T]
      have hnuc : nuu (c-1) = 0 := by
        unfold nuu
        rw [hbc, hc1]
        omega
      have hK : K0 c = blk c + 1 := by unfold K0; rw [if_neg (by omega)]
      have hKc : K0 (c-1) = blk c := by unfold K0; rw [if_pos hnuc, hbc]
      have hrqc : rq (c-1) = 0 := by
        unfold rq
        rw [hKc, hc1]
        omega
      have hrq : rq c = blk c := by
        unfold rq
        rw [hK]
        rw [T_succ]
        unfold nuu at h1
        omega
      have hf : fdefFrom c (blk c) = ((blk c + 1 : ℕ) : ℚ) := by
        unfold fdefFrom
        rw [if_neg (by rw [← hT, ← hnu] at *; omega), if_pos (by rw [← hT, ← hnu] at *; exact h1)]
      unfold Bq
      rw [hrqc, hKc, hK, hrq, hf]
      have e1 : pf (blk c + 1) = pf (blk c) * (blk c + 1)! := rfl
      rw [e1, Nat.factorial_succ]
      have p1 : (0:ℚ) < (pf (blk c) : ℚ) := by exact_mod_cast pf_pos _
      have p2 : (0:ℚ) < ((blk c)! : ℚ) := by exact_mod_cast Nat.factorial_pos _
      push_cast
      field_simp
      ring
    · -- nuu c = 0 : c = T (blk c), ratio 1
      have hnu0 : nuu c = 0 := by omega
      have hm : 1 ≤ blk c := by
        by_contra hb
        push_neg at hb
        have hz : blk c = 0 := by omega
        have := T_blk_le c
        have := nuu_add c
        rw [hz] at this
        simp [T] at this
        omega
      have hc : c = T (blk c) := by
        have := nuu_add c
        omega
      have hf : fdefFrom c (blk c) = 1 := by
        unfold fdefFrom
        rw [if_neg (by rw [← hT, ← hnu] at *; omega), if_neg (by rw [← hT, ← hnu] at *; omega)]
      rw [hf, one_mul]
      -- c - 1 = T (blk c - 1) + (blk c - 1)
      have hTs : T ((blk c - 1) + 1) = T (blk c - 1) + ((blk c -1)+1) := T_succ _
      have he : (blk c - 1) + 1 = blk c := by omega
      rw [he] at hTs
      by_cases hm2 : 2 ≤ blk c
      · have hbc : blk (c-1) = blk c - 1 := by
          apply blk_eq_of
          · omega
          · rw [he]; omega
        have hnuc : nuu (c-1) = blk c - 1 := by
          unfold nuu
          rw [hbc]
          omega
        have hKc : K0 (c-1) = blk c := by
          unfold K0
          rw [if_neg (by omega), hbc, he]
        have hrqc : rq (c-1) = 1 := by
          unfold rq
          rw [hKc]
          omega
        have hK : K0 c = blk c := by unfold K0; rw [if_pos hnu0]
        have hrq : rq c = 0 := rq_zero c hnu0
        unfold Bq
        rw [hrqc, hKc, hK, hrq]
        norm_num [Nat.factorial]
      · -- blk c = 1, c = 1
        have hb1 : blk c = 1 := by omega
        have hc1 : c = 1 := by rw [hc, hb1]; rfl
        subst hc1
        norm_num
        unfold Bq
        have e0 : blk 0 = 0 := by
          have := blk_T 0
          simpa [T] using this
        have hnu00 : nuu 0 = 0 := by unfold nuu; omega
        have hK00 : K0 0 = 0 := by unfold K0; rw [if_pos hnu00, e0]
        have hnu1 : nuu 1 = 0 := by
          unfold nuu
          rw [hb1]
          rfl
        have hK1 : K0 1 = 1 := by unfold K0; rw [if_pos hnu1, hb1]
        have hr0 : rq 0 = 0 := rq_zero 0 hnu00
        have hr1 : rq 1 = 0 := rq_zero 1 hnu1
        rw [hr0, hr1, hK00, hK1]
        show ((1:ℕ):ℚ)/(pf 0 : ℚ) = ((1:ℕ):ℚ)/(pf 1 : ℚ)
        have : pf 1 = pf 0 * 1 ! := rfl
        rw [this]
        norm_num [pf]

lemma fdefFrom_nonneg (c p : ℕ) : 0 ≤ fdefFrom c p := by
  unfold fdefFrom
  split
  · positivity
  · split
    · positivity
    · norm_num

/-! ### SOE2 bridge -/

lemma drop_cons_q (l : List ℚ) (c : ℕ) (h : c < l.length) :
    l.drop c = l.getD c 0 :: l.drop (c+1) := by
  rw [List.getD_eq_getElem l 0 h]
  exact List.drop_eq_getElem_cons h

lemma drop_cons_n (l : List ℕ) (c : ℕ) (h : c < l.length) :
    l.drop c = l.getD c 0 :: l.drop (c+1) := by
  rw [List.getD_eq_getElem l 0 h]
  exact List.drop_eq_getElem_cons h

lemma Ioc_split (kk n : ℕ) (h : kk < n) :
    Ioc kk n = insert (kk+1) (Ioc (kk+1) n) := by
  ext x
  simp only [Finset.mem_Ioc, Finset.mem_insert]
  omega

lemma SOE2_spec (n : ℕ) (hn : n ≤ 527) (hn1 : 1 ≤ n) :
    ∀ (steps kk : ℕ) (tau so se : ℚ), kk + steps = n → K0 n ≤ kk →
      (1 ≤ steps → Bq (n - (kk+1)) ≤ tau * (((kk+1))! : ℚ) * Bq n) →
      0 ≤ tau →
      so * Bq n + (∑ Kp ∈ Ioc kk n, if (blk (n-Kp) + blk n) % 2 = 1 then termQ n Kp else 0)
        ≤ (SOE2 n (blk n) (XTLR.drop (528 - steps)) (PRLR.drop (528 - steps)) steps (kk+1) tau so se).1 * Bq n ∧
      se * Bq n + (∑ Kp ∈ Ioc kk n, if (blk (n-Kp) + blk n) % 2 = 0 then termQ n Kp else 0)
        ≤ (SOE2 n (blk n) (XTLR.drop (528 - steps)) (PRLR.drop (528 - steps)) steps (kk+1) tau so se).2 * Bq n := by
  intro steps
  induction steps with
  | zero =>
    intro kk tau so se hkk hK0 hinv htau
    have hkn : kk = n := by omega
    subst hkn
    simp [SOE2, Finset.Ioc_self]
  | succ steps ih =>
    intro kk tau so se hkk hK0 hinv htau
    have hkkn : kk < n := by omega
    set c := n - (kk+1) with hc
    have hc527 : c ≤ 527 := by omega
    have hidx : 528 - (steps+1) = 527 - c := by omega
    have hxlen : 527 - c < XTLR.length := by rw [xtlr_len]; omega
    have hplen : 527 - c < PRLR.length := by rw [prlr_len]; omega
    have hidx2 : (527 - c) + 1 = 528 - steps := by omega
    rw [hidx, drop_cons_q XTLR _ hxlen, drop_cons_n PRLR _ hplen, hidx2]
    rw [xtlr_ok c hc527, prlr_ok c hc527]
    have hxi : XTL.getD c 0 = Xi c := (xi_eq_getD0 c hc527).symm
    rw [hxi]
    have hinv1 := hinv (by omega)
    have hxipos := xi_pos c
    have hbqn := Bq_pos n
    have hbqc := Bq_pos c
    have hfacpos : (0:ℚ) < (((kk+1))! : ℚ) := by exact_mod_cast Nat.factorial_pos _
    -- the head term bound: termQ n (kk+1) ≤ tau * Xi c * Bq n
    have hterm : termQ n (kk+1) ≤ tau * Xi c * Bq n := by
      unfold termQ
      rw [← hc]
      rw [div_le_iff₀ hfacpos]
      calc Bq c * Xi c ≤ (tau * (((kk+1))! : ℚ) * Bq n) * Xi c := by
            apply mul_le_mul_of_nonneg_right hinv1 (le_of_lt hxipos)
        _ = tau * Xi c * Bq n * ((kk+1))! := by ring
    -- new tau invariant
    have hnewinv : 1 ≤ steps → Bq (n - (kk+1+1)) ≤
        (r45 (tau * fdefFrom (n - (kk+1)) (blk c) / ((kk+1+1:ℕ):ℚ))) * (((kk+1+1))! : ℚ) * Bq n := by
      intro hst
      have hcge : 1 ≤ c := by omega
      have hcm : n - (kk+1+1) = c - 1 := by omega
      rw [hcm]
      rw [Bq_pred c hcge]
      have hfle := le_r45 (tau * fdefFrom c (blk c) / ((kk+2:ℕ):ℚ))
      have hf2 : (0:ℚ) < ((kk+2:ℕ):ℚ) := by positivity
      have hfacs : (((kk+2))! : ℚ) = ((kk+2:ℕ):ℚ) * (((kk+1))! : ℚ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have step1 : fdefFrom c (blk c) * Bq c ≤ fdefFrom c (blk c) * (tau * (((kk+1))! : ℚ) * Bq n) :=
        mul_le_mul_of_nonneg_left hinv1 (fdefFrom_nonneg c (blk c))
      have step2 : fdefFrom c (blk c) * (tau * (((kk+1))! : ℚ) * Bq n)
          = (tau * fdefFrom c (blk c) / ((kk+2:ℕ):ℚ)) * (((kk+2))! : ℚ) * Bq n := by
        rw [hfacs]
        field_simp
        try ring
      have step3 : (tau * fdefFrom c (blk c) / ((kk+2:ℕ):ℚ)) * (((kk+2))! : ℚ) * Bq n
          ≤ (r45 (tau * fdefFrom c (blk c) / ((kk+2:ℕ):ℚ))) * (((kk+2))! : ℚ) * Bq n := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hbqn)
        apply mul_le_mul_of_nonneg_right hfle
        exact le_of_lt (by exact_mod_cast Nat.factorial_pos (kk+2))
      calc fdefFrom c (blk c) * Bq c ≤ _ := step1
        _ = _ := step2
        _ ≤ _ := by
              have : ((kk+1+1) : ℕ) = (kk+2 : ℕ) := rfl
              rw [this]
              exact step3
    have hnewtau : 0 ≤ r45 (tau * fdefFrom (n - (kk+1)) (blk c) / ((kk+1+1:ℕ):ℚ)) := by
      refine le_trans ?_ (le_r45 _)
      have := fdefFrom_nonneg (n-(kk+1)) (blk c)
      positivity
    -- sum split
    rw [Ioc_split kk n hkkn]
    have hnotmem : (kk+1) ∉ Ioc (kk+1) n := by simp
    rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem]
    rw [← hc]
    by_cases hp : (blk c + blk n) % 2 = 1
    · rw [show SOE2 n (blk n) (Xi c :: XTLR.drop (528 - steps)) (blk c :: PRLR.drop (528 - steps))
            (steps+1) (kk+1) tau so se
          = SOE2 n (blk n) (XTLR.drop (528 - steps)) (PRLR.drop (528 - steps)) steps (kk+1+1)
              (r45 (tau * fdefFrom (n-(kk+1)) (blk c) / ((kk+1+1:ℕ):ℚ))) (so + tau * Xi c) se from by
        rw [SOE2]
        rw [if_pos hp]]
      have ihh := ih (kk+1) _ (so + tau * Xi c) se (by omega) (by omega) hnewinv hnewtau
      constructor
      · refine le_trans ?_ ihh.1
        rw [if_pos hp]
        have : (so + tau * Xi c) * Bq n = so * Bq n + tau * Xi c * Bq n := by ring
        rw [this]
        have h5 := hterm
        push_cast at h5 ⊢
        linarith
      · refine le_trans ?_ ihh.2
        rw [if_neg (by omega)]
        linarith
    · rw [show SOE2 n (blk n) (Xi c :: XTLR.drop (528 - steps)) (blk c :: PRLR.drop (528 - steps))
            (steps+1) (kk+1) tau so se
          = SOE2 n (blk n) (XTLR.drop (528 - steps)) (PRLR.drop (528 - steps)) steps (kk+1+1)
              (r45 (tau * fdefFrom (n-(kk+1)) (blk c) / ((kk+1+1:ℕ):ℚ))) so (se + tau * Xi c) from by
        rw [SOE2]
        rw [if_neg hp]]
      have ihh := ih (kk+1) _ so (se + tau * Xi c) (by omega) (by omega) hnewinv hnewtau
      constructor
      · refine le_trans ?_ ihh.1
        rw [if_neg hp]
        linarith
      · refine le_trans ?_ ihh.2
        rw [if_pos (by omega)]
        have : (se + tau * Xi c) * Bq n = se * Bq n + tau * Xi c * Bq n := by ring
        rw [this]
        linarith

/-! ### The decide-zone theorems -/

lemma SO_eq_sum_full (n : ℕ) :
    SO n n = ∑ Kp ∈ Ioc (K0 n) n, (if (blk (n-Kp) + blk n) % 2 = 1 then termQ n Kp else 0) := by
  unfold SO
  apply Finset.sum_congr rfl
  intro Kp hKp
  rw [Finset.mem_Ioc] at hKp
  by_cases hp : (blk (n-Kp) + blk n) % 2 = 1
  · rw [if_pos ⟨hKp.2, hp⟩, if_pos hp]
  · rw [if_neg (by tauto), if_neg hp]

lemma SE_eq_sum_full (n : ℕ) :
    SE n n = ∑ Kp ∈ Ioc (K0 n) n, (if (blk (n-Kp) + blk n) % 2 = 0 then termQ n Kp else 0) := by
  unfold SE
  apply Finset.sum_congr rfl
  intro Kp hKp
  rw [Finset.mem_Ioc] at hKp
  by_cases hp : (blk (n-Kp) + blk n) % 2 = 0
  · rw [if_pos ⟨hKp.2, hp⟩, if_pos hp]
  · rw [if_neg (by tauto), if_neg hp]

theorem chk_all_true (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 527) : chk n = true := by
  have key : ∀ i, ((List.range 132).all fun j => (132*i+j) == 0 || chk (132*i+j)) = true →
      132*i ≤ n → n < 132*(i+1) → chk n = true := by
    intro i hall hlo hhi
    rw [List.all_eq_true] at hall
    have h3 := hall (n - 132*i) (List.mem_range.mpr (by omega))
    have h4 : 132*i + (n - 132*i) = n := by omega
    rw [h4] at h3
    have hne : (n == 0) = false := by simp; omega
    rw [hne, Bool.false_or] at h3
    exact h3
  rcases Nat.lt_or_ge n 132 with h | h
  · exact key 0 chk_all_0 (by omega) (by omega)
  rcases Nat.lt_or_ge n 264 with h' | h'
  · exact key 1 chk_all_1 (by omega) (by omega)
  rcases Nat.lt_or_ge n 396 with h'' | h''
  · exact key 2 chk_all_2 (by omega) (by omega)
  exact key 3 chk_all_3 (by omega) (by omega)

theorem step_g2_low (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 527) : StepP n ∧ G2P n := by
  have hcn := chk_all_true n h1 h2
  unfold chk at hcn
  have hbqn := Bq_pos n
  by_cases hnk : n ≤ K0 n
  · rw [if_pos hnk] at hcn
    rw [Bool.and_eq_true] at hcn
    obtain ⟨hs, hg⟩ := hcn
    have hs' := of_decide_eq_true hs
    have hg' := of_decide_eq_true hg
    have hKn : K0 n = n := le_antisymm (K0_le_self n) hnk
    have hempty : Ioc (K0 n) n = ∅ := by rw [hKn]; exact Finset.Ioc_self n
    constructor
    · unfold StepP
      unfold SO
      rw [hempty, Finset.sum_empty, add_zero]
      rw [← xi_eq_getD n h2] at hs'
      nlinarith
    · unfold G2P
      unfold SE
      rw [hempty, Finset.sum_empty]
      positivity
  · rw [if_neg hnk] at hcn
    push_neg at hnk
    have hK0 := K0_le_self n
    have hp : 1 ≤ n - K0 n := by omega
    -- initial tau invariant
    have hinv : 1 ≤ n - K0 n → Bq (n - (K0 n + 1)) ≤
        (r45 (fdefFrom (n - K0 n) (blk (n - K0 n)) / ((K0 n + 1:ℕ):ℚ))) * (((K0 n + 1))! : ℚ) * Bq n := by
      intro _
      have hpar := Bq_parent n (by omega)
      have hpred := Bq_pred (n - K0 n) hp
      have he : n - K0 n - 1 = n - (K0 n + 1) := by omega
      rw [he] at hpred
      rw [hpred, hpar]
      have hfle := le_r45 (fdefFrom (n - K0 n) (blk (n - K0 n)) / ((K0 n + 1:ℕ):ℚ))
      have hK1pos : (0:ℚ) < ((K0 n + 1:ℕ):ℚ) := by positivity
      have hfacs : (((K0 n + 1))! : ℚ) = ((K0 n + 1:ℕ):ℚ) * (((K0 n))! : ℚ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have heq : fdefFrom (n - K0 n) (blk (n - K0 n)) * (((K0 n))! * Bq n)
          = (fdefFrom (n - K0 n) (blk (n - K0 n)) / ((K0 n + 1:ℕ):ℚ)) * (((K0 n + 1))! : ℚ) * Bq n := by
        rw [hfacs]
        field_simp
      rw [heq]
      apply mul_le_mul_of_nonneg_right _ (le_of_lt (Bq_pos n))
      apply mul_le_mul_of_nonneg_right hfle
      exact le_of_lt (by exact_mod_cast Nat.factorial_pos (K0 n + 1))
    have htau0 : 0 ≤ r45 (fdefFrom (n - K0 n) (blk (n - K0 n)) / ((K0 n + 1:ℕ):ℚ)) := by
      refine le_trans ?_ (le_r45 _)
      have := fdefFrom_nonneg (n - K0 n) (blk (n - K0 n))
      positivity
    have hspec := SOE2_spec n h2 h1 (n - K0 n) (K0 n) _ 0 0 (by omega) (le_refl _) hinv htau0
    have hidx : 528 - (n - K0 n) = 528 - (n - K0 n) := rfl
    rw [Bool.and_eq_true] at hcn
    obtain ⟨hs, hg⟩ := hcn
    have hs' := of_decide_eq_true hs
    have hg' := of_decide_eq_true hg
    rw [← xi_eq_getD n h2] at hs'
    constructor
    · unfold StepP
      rw [SO_eq_sum_full]
      have h6 := hspec.1
      rw [zero_mul, zero_add] at h6
      nlinarith
    · unfold G2P
      rw [SE_eq_sum_full]
      have h6 := hspec.2
      rw [zero_mul, zero_add] at h6
      nlinarith

end A185895Pf
