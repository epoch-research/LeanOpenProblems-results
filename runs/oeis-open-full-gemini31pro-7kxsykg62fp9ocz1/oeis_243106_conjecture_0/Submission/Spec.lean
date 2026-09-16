import FormalConjectures.Util.ProblemImports

open Finset

def a_seq (n : ℕ) : Int :=
  (Icc 1 n).sum fun k : ℕ =>
    (if Nat.Prime k then (-1 : Int) else 1) * (10 : Int) ^ k

lemma Icc_sum_eq (n : ℕ) (f : ℕ → Int) :
  (Icc 1 n).sum f = (range n).sum (fun k ↦ f (k + 1)) := by
  induction' n with n ih
  · simp
  · have h1 : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    have h2 : n + 1 ∉ Icc 1 n := by simp
    rw [h1, sum_insert h2, sum_range_succ, ih]
    ring

lemma helper_induction (b : ℕ) (hb : b ≥ 5) (n : ℕ) :
  ∀ (d : ℕ → Int) (hd : ∀ k < n, d k = 1 ∨ d k = -1) (c : Int) (hc : c = 0 ∨ c = -1),
  ∃ (a : ℕ → ℕ) (C : Int),
    (∀ k < n, a k = 0 ∨ a k = 1 ∨ a k = b - 2 ∨ a k = b - 1) ∧
    (C = 0 ∨ C = -1) ∧
    (∀ k < n, a k < b) ∧
    c + (range n).sum (fun k ↦ d k * (b : Int) ^ k) = (range n).sum (fun k ↦ (a k : Int) * (b : Int) ^ k) + C * (b : Int) ^ n := by
  induction' n with n ih
  · intro d hd c hc
    use (fun _ ↦ 0), c
    refine ⟨by simp, hc, by simp, ?_⟩
    simp
  · intro d hd c hc
    have hv0 : c + d 0 = 1 ∨ c + d 0 = 0 ∨ c + d 0 = -1 ∨ c + d 0 = -2 := by
      have hd0 := hd 0 (Nat.zero_lt_succ _)
      rcases hc with h1 | h1 <;> rcases hd0 with h2 | h2 <;> omega
    obtain ⟨a0, c', ha01, hc'1, ha02, heq⟩ : ∃ (a0 : ℕ) (c' : Int),
        (a0 = 0 ∨ a0 = 1 ∨ a0 = b - 2 ∨ a0 = b - 1) ∧
        (c' = 0 ∨ c' = -1) ∧
        a0 < b ∧
        c + d 0 = (a0 : Int) + c' * b := by
      rcases hv0 with h | h | h | h
      · use 1, 0; refine ⟨by tauto, by tauto, by omega, by omega⟩
      · use 0, 0; refine ⟨by tauto, by tauto, by omega, by omega⟩
      · use b - 1, -1; refine ⟨by tauto, by tauto, by omega, by omega⟩
      · use b - 2, -1; refine ⟨by tauto, by tauto, by omega, by omega⟩
    
    have hd' : ∀ k < n, d (k + 1) = 1 ∨ d (k + 1) = -1 := fun k hk ↦ hd (k + 1) (by omega)
    rcases ih (fun k ↦ d (k + 1)) hd' c' hc'1 with ⟨a', C', ha', hC', ha'2, hIH⟩
    
    use (fun k ↦ if k = 0 then a0 else a' (k - 1)), C'
    refine ⟨?_, hC', ?_, ?_⟩
    · intro k hk
      by_cases hk0 : k = 0
      · simp [hk0, ha01]
      · have : k - 1 < n := by omega
        simp [hk0, ha' (k - 1) this]
    · intro k hk
      by_cases hk0 : k = 0
      · simp [hk0, ha02]
      · have : k - 1 < n := by omega
        simp [hk0, ha'2 (k - 1) this]
    · rw [sum_range_succ', sum_range_succ']
      have h1 : ∀ x, (if x + 1 = 0 then (a0 : Int) else (a' (x + 1 - 1) : Int)) = a' x := by
        intro x
        have : x + 1 ≠ 0 := by omega
        simp [this]
      simp only [Nat.cast_ite, pow_zero, mul_one, pow_succ, if_true, h1]
      have h2 : (range n).sum (fun x ↦ d (x + 1) * ((b : Int) ^ x * (b : Int))) = ((range n).sum (fun x ↦ d (x + 1) * (b : Int) ^ x)) * (b : Int) := by
        rw [sum_mul]
        apply sum_congr rfl
        intro x _
        ring
      have h3 : (range n).sum (fun x ↦ (a' x : Int) * ((b : Int) ^ x * (b : Int))) = ((range n).sum (fun x ↦ (a' x : Int) * (b : Int) ^ x)) * (b : Int) := by
        rw [sum_mul]
        apply sum_congr rfl
        intro x _
        ring
      rw [h2, h3]
      calc
        c + (((range n).sum fun x ↦ d (x + 1) * (b : Int) ^ x) * b + d 0)
          = (c + d 0) + ((range n).sum fun x ↦ d (x + 1) * (b : Int) ^ x) * b := by ring
        _ = (a0 : Int) + c' * b + ((range n).sum fun x ↦ d (x + 1) * (b : Int) ^ x) * b := by rw [heq]
        _ = (a0 : Int) + (c' + (range n).sum fun x ↦ d (x + 1) * (b : Int) ^ x) * b := by ring
        _ = (a0 : Int) + (((range n).sum fun x ↦ (a' x : Int) * (b : Int) ^ x) + C' * (b : Int) ^ n) * b := by rw [hIH]
        _ = ((range n).sum fun x ↦ (a' x : Int) * (b : Int) ^ x) * b + (a0 : Int) + C' * ((b : Int) ^ n * b) := by ring

lemma sum_bound (b : ℕ) (hb : b ≥ 5) (n : ℕ) (a : ℕ → ℕ) (ha : ∀ k < n, a k < b) :
  (range n).sum (fun k ↦ (a k : Int) * (b : Int) ^ k) < (b : Int) ^ n := by
  revert a
  induction' n with n ih
  · intro a ha
    simp
  · intro a ha
    have h_split : (range (n + 1)).sum (fun k ↦ (a k : Int) * (b : Int) ^ k) = (a 0 : Int) + ((range n).sum (fun x ↦ (a (x + 1) : Int) * (b : Int) ^ x)) * (b : Int) := by
      rw [sum_range_succ']
      simp only [pow_zero, mul_one, pow_succ]
      have h2 : (range n).sum (fun x ↦ (a (x + 1) : Int) * ((b : Int) ^ x * (b : Int))) = ((range n).sum (fun x ↦ (a (x + 1) : Int) * (b : Int) ^ x)) * (b : Int) := by
        rw [sum_mul]
        apply sum_congr rfl
        intro x _
        ring
      rw [h2]
      ring
    rw [h_split]
    have ha0 : (a 0 : Int) ≤ (b : Int) - 1 := by
      have : a 0 < b := ha 0 (by omega)
      omega
    have ha' : ∀ k < n, a (k + 1) < b := fun k hk ↦ ha (k + 1) (by omega)
    have h_ih : (range n).sum (fun x ↦ (a (x + 1) : Int) * (b : Int) ^ x) ≤ (b : Int) ^ n - 1 := by
      linarith [ih (fun k ↦ a (k + 1)) ha']
    have hz : (0 : Int) ≤ (b : Int) := by omega
    have h_pow : (b : Int) ^ (n + 1) = (b : Int) ^ n * (b : Int) := by ring
    rw [h_pow]
    nlinarith

lemma val_mod_div (b n : ℕ) (a : ℕ → ℕ) :
  (range (n + 1)).sum (fun k ↦ a k * b ^ k) = a 0 + (range n).sum (fun k ↦ a (k + 1) * b ^ k) * b := by
  rw [sum_range_succ']
  simp only [pow_zero, mul_one, pow_succ]
  have h2 : (range n).sum (fun x ↦ a (x + 1) * (b ^ x * b)) = ((range n).sum (fun x ↦ a (x + 1) * b ^ x)) * b := by
    rw [sum_mul]
    apply sum_congr rfl
    intro x _
    ring
  rw [h2]
  ring

lemma digits_subset (b : ℕ) (hb : b ≥ 2) (n : ℕ) (a : ℕ → ℕ) (ha : ∀ k < n, a k < b) :
  ∀ d ∈ Nat.digits b ((range n).sum (fun k ↦ a k * b ^ k)), (∃ k < n, d = a k) := by
  revert a
  induction' n with n ih
  · intro a ha d hd
    simp at hd
  · intro a ha d hd
    have hV := val_mod_div b n a
    set V := (range (n + 1)).sum (fun k ↦ a k * b ^ k)
    by_cases hV0 : V = 0
    · rw [hV0, Nat.digits_zero] at hd
      simp at hd
    · have h_pos : 0 < V := Nat.pos_of_ne_zero hV0
      rw [Nat.digits_def' (by omega) h_pos] at hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · use 0
        refine ⟨by omega, ?_⟩
        rw [hV]
        have : a 0 < b := ha 0 (by omega)
        rw [Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt this
      · have hd' : d ∈ Nat.digits b ((range n).sum (fun k ↦ a (k + 1) * b ^ k)) := by
          have h_div : V / b = (range n).sum (fun k ↦ a (k + 1) * b ^ k) := by
            rw [hV]
            have : a 0 < b := ha 0 (by omega)
            rw [Nat.add_mul_div_right (a 0) _ (by omega)]
            have : a 0 / b = 0 := Nat.div_eq_of_lt this
            rw [this, zero_add]
          rw [← h_div]
          exact hd
        have ha' : ∀ k < n, a (k + 1) < b := fun k hk ↦ ha (k + 1) (by omega)
        have ih_res := ih (fun k ↦ a (k + 1)) ha' d hd'
        rcases ih_res with ⟨k, hk, rfl⟩
        use k + 1
        refine ⟨by omega, rfl⟩

lemma abs_val_repr (b : ℕ) (hb : b ≥ 5) (n : ℕ) (d : ℕ → Int) (hd : ∀ k < n, d k = 1 ∨ d k = -1) :
  ∃ (a : ℕ → ℕ),
    (∀ k < n, a k = 0 ∨ a k = 1 ∨ a k = b - 2 ∨ a k = b - 1) ∧
    (∀ k < n, a k < b) ∧
    ((range n).sum (fun k ↦ d k * (b : Int) ^ k)).natAbs = (range n).sum (fun k ↦ a k * b ^ k) := by
  set V := (range n).sum (fun k ↦ d k * (b : Int) ^ k)
  by_cases hV : 0 ≤ V
  · rcases helper_induction b hb n d hd 0 (by tauto) with ⟨a, C, ha1, hC, ha2, heq⟩
    rw [zero_add] at heq
    have hC0 : C = 0 := by
      rcases hC with rfl | rfl
      · rfl
      · have h_bound := sum_bound b hb n a ha2
        linarith
    use a
    refine ⟨ha1, ha2, ?_⟩
    rw [hC0] at heq
    simp only [zero_mul, add_zero] at heq
    dsimp [V]
    rw [heq]
    have heq_cast : (∑ k ∈ range n, ↑(a k) * (b : Int) ^ k) = ↑(∑ k ∈ range n, a k * b ^ k) := by
      push_cast
      rfl
    rw [heq_cast, Int.natAbs_natCast]
  · set d' := fun k ↦ - d k
    have hd' : ∀ k < n, d' k = 1 ∨ d' k = -1 := by
      intro k hk
      dsimp [d']
      rcases hd k hk with h | h
      · right; simp [h]
      · left; simp [h]
    rcases helper_induction b hb n d' hd' 0 (by tauto) with ⟨a, C, ha1, hC, ha2, heq⟩
    rw [zero_add] at heq
    have hC0 : C = 0 := by
      rcases hC with rfl | rfl
      · rfl
      · have h_bound := sum_bound b hb n a ha2
        have h_sum : (range n).sum (fun k ↦ d' k * (b : Int) ^ k) = - V := by
          dsimp [V, d']
          rw [← sum_neg_distrib]
          apply sum_congr rfl
          intro x _
          ring
        linarith
    use a
    refine ⟨ha1, ha2, ?_⟩
    rw [hC0] at heq
    simp only [zero_mul, add_zero] at heq
    have h_sum : (range n).sum (fun k ↦ d' k * (b : Int) ^ k) = - ((range n).sum (fun k ↦ d k * (b : Int) ^ k)) := by
      dsimp [d']
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro x _
      ring
    have heq3 : ((range n).sum (fun k ↦ d k * (b : Int) ^ k)) = - ((range n).sum (fun k ↦ (a k : Int) * (b : Int) ^ k)) := by linarith
    dsimp [V]
    rw [heq3]
    have heq_cast : (∑ k ∈ range n, ↑(a k) * (b : Int) ^ k) = ↑(∑ k ∈ range n, a k * b ^ k) := by
      push_cast
      rfl
    rw [heq_cast, Int.natAbs_neg, Int.natAbs_natCast]

theorem oeis_243106_conjecture_0 (b n : ℕ) (hb : b ≥ 5) :
  ∀ (σ : ℕ → Int) (hσ : ∀ k ∈ Icc 1 n, σ k = 1 ∨ σ k = -1),
    let x : Int := (Icc 1 n).sum fun k ↦ σ k * (b : Int) ^ k;
    ∀ d ∈ (b.digits x.natAbs),
      d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1 := by
  intro σ hσ x d hd
  set d_seq := fun k ↦ σ (k + 1)
  have hd_seq : ∀ k < n, d_seq k = 1 ∨ d_seq k = -1 := by
    intro k hk
    have := hσ (k + 1) (by rw [mem_Icc]; omega)
    exact this
  rcases abs_val_repr b hb n d_seq hd_seq with ⟨a, ha1, ha2, h_abs⟩
  have hx : x = ((range n).sum (fun k ↦ d_seq k * (b : Int) ^ k)) * b := by
    dsimp [x, d_seq]
    rw [Icc_sum_eq]
    have h_pow : (range n).sum (fun k ↦ σ (k + 1) * (b : Int) ^ (k + 1)) = (range n).sum (fun k ↦ σ (k + 1) * ((b : Int) ^ k * b)) := by
      apply sum_congr rfl
      intro x hx
      rw [pow_succ]
    rw [h_pow]
    rw [sum_mul]
    apply sum_congr rfl
    intro x _
    ring
  have hx_abs : x.natAbs = ((range n).sum (fun k ↦ a k * b ^ k)) * b := by
    rw [hx]
    rw [Int.natAbs_mul]
    rw [h_abs]
    rfl
  rw [hx_abs] at hd
  by_cases h_zero : ((range n).sum (fun k ↦ a k * b ^ k)) = 0
  · rw [h_zero, zero_mul] at hd
    rw [Nat.digits_zero] at hd
    simp at hd
  · have h_pos : 0 < ((range n).sum (fun k ↦ a k * b ^ k)) * b := by
      have h1 : 0 < (range n).sum (fun k ↦ a k * b ^ k) := Nat.pos_of_ne_zero h_zero
      have h2 : 0 < b := by omega
      exact Nat.mul_pos h1 h2
    rw [Nat.digits_def' (by omega) h_pos] at hd
    simp only [List.mem_cons] at hd
    rcases hd with rfl | hd
    · have h_mod : (((range n).sum (fun k ↦ a k * b ^ k)) * b) % b = 0 := by
        exact Nat.mul_mod_left _ _
      rw [h_mod]
      left; rfl
    · have h_div : (((range n).sum (fun k ↦ a k * b ^ k)) * b) / b = ((range n).sum (fun k ↦ a k * b ^ k)) := by
        exact Nat.mul_div_cancel _ (by omega)
      rw [h_div] at hd
      have hd_sub := digits_subset b (by omega) n a ha2 d hd
      rcases hd_sub with ⟨k, hk, rfl⟩
      rcases ha1 k hk with h | h | h | h
      · left; exact h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; exact h

theorem oeis_243106_conjecture_0.disproof : ¬ (type_of% @oeis_243106_conjecture_0) := sorry
