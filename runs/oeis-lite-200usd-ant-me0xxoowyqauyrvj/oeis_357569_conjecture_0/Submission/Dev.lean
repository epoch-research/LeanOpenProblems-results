import FormalConjectures.Util.ProblemImports
open Nat Finset

-- experiment: factorial split lemma
example (p X : ℕ) :
    (∏ m ∈ Finset.Icc 1 X, m) =
      (∏ m ∈ (Finset.Icc 1 X).filter (fun m => p ∣ m), m) *
      (∏ m ∈ (Finset.Icc 1 X).filter (fun m => ¬ p ∣ m), m) := by
  rw [Finset.prod_filter_mul_prod_filter_not]

-- choose * fact * fact
example (P : ℕ) : (3*P).choose P * P ! * (2*P)! = (3*P)! := by
  have h : P ≤ 3 * P := by omega
  have := Nat.choose_mul_factorial_mul_factorial h
  rw [show 3*P - P = 2*P by omega] at this
  exact this

-- product of multiples of p
theorem prod_mul_eq (p q : ℕ) :
    (∏ i ∈ Finset.Icc 1 q, (p * i)) = p^q * q ! := by
  induction q with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, pow_succ, Nat.factorial_succ]
    ring

-- multiples of p in [1,X] are the image of [1, X/p] under (p * ·)
theorem filter_dvd_eq_image (p X : ℕ) (hp : 0 < p) :
    (Finset.Icc 1 X).filter (fun m => p ∣ m) = (Finset.Icc 1 (X/p)).image (fun i => p * i) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, c, rfl⟩
    refine ⟨c, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at h1
      · exact h
    · rw [Nat.le_div_iff_mul_le hp, Nat.mul_comm]; exact h2
  · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
    rw [Nat.le_div_iff_mul_le hp] at hi2
    refine ⟨⟨?_, ?_⟩, ⟨i, rfl⟩⟩
    · calc 1 ≤ p * 1 := by omega
        _ ≤ p * i := by exact Nat.mul_le_mul_left p hi1
    · rw [Nat.mul_comm]; exact hi2

theorem prod_Icc_id (X : ℕ) : (∏ m ∈ Finset.Icc 1 X, m) = X ! := by
  induction X with
  | zero => simp
  | succ k ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]; ring

noncomputable def Pistar (p X : ℕ) : ℕ := ∏ m ∈ (Finset.Icc 1 X).filter (fun m => ¬ p ∣ m), m

noncomputable def Uset (p P : ℕ) : Finset ℕ := (Finset.Icc 1 P).filter (fun k => ¬ p ∣ k)

noncomputable def Wfun (p M P : ℕ) : ℕ := ∏ k ∈ Uset p P, (M + k)

theorem telescope (p M P : ℕ) (hM : p ∣ M) :
    Pistar p (M + P) = Pistar p M * Wfun p M P := by
  unfold Pistar Wfun Uset
  have hsplit : Finset.Icc 1 (M + P) = Finset.Icc 1 M ∪ Finset.Ioc M (M + P) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
  rw [hsplit, Finset.filter_union, Finset.prod_union]
  · congr 1
    -- reindex the second product
    rw [show Finset.Ioc M (M + P) = (Finset.Icc 1 P).image (fun k => M + k) by
          ext x
          simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_Icc]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨x - M, ⟨by omega, by omega⟩, by omega⟩
          · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩; exact ⟨by omega, by omega⟩]
    rw [Finset.filter_image, Finset.prod_image (by intro a _ b _ h; exact Nat.add_left_cancel h)]
    apply Finset.prod_congr
    · ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨h, hd⟩; exact ⟨h, fun hc => hd (Dvd.dvd.add hM hc)⟩
      · rintro ⟨h, hd⟩; refine ⟨h, fun hc => hd ?_⟩
        have : p ∣ (M + k) - M := (Nat.dvd_sub hc hM)
        simpa using this
    · intro k _; rfl
  · apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hb
    omega

theorem choose_id (a b : ℕ) (h : b ≤ a) : a.choose b * b ! * (a - b)! = a ! :=
  Nat.choose_mul_factorial_mul_factorial h

theorem factsplit (p X : ℕ) (hp : 0 < p) :
    Pistar p X * (p^(X/p) * (X/p)!) = X ! := by
  have hsplit : (∏ m ∈ Finset.Icc 1 X, m) =
      (∏ m ∈ (Finset.Icc 1 X).filter (fun m => p ∣ m), m) *
      (∏ m ∈ (Finset.Icc 1 X).filter (fun m => ¬ p ∣ m), m) := by
    rw [Finset.prod_filter_mul_prod_filter_not]
  have hfact : (∏ m ∈ Finset.Icc 1 X, m) = X ! := prod_Icc_id X
  rw [filter_dvd_eq_image p X hp] at hsplit
  rw [Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h)] at hsplit
  rw [prod_mul_eq] at hsplit
  unfold Pistar
  rw [hfact] at hsplit
  linarith [hsplit]

-- A' W0 = A W2
theorem prodid3 (p n : ℕ) (hp : 0 < p) :
    Pistar p (p*n) * (3*(p*n)).choose (p*n) = (3*n).choose n * Wfun p (2*(p*n)) (p*n) := by
  set P := p * n with hP
  have hdvd : p ∣ P := ⟨n, hP⟩
  have fs_P : Pistar p P * (p^n * n !) = P ! := by
    have := factsplit p P hp
    rwa [hP, Nat.mul_div_cancel_left n hp] at this
  have fs_2P : Pistar p (2*P) * (p^(2*n) * (2*n) !) = (2*P) ! := by
    have := factsplit p (2*P) hp
    rwa [show (2*P)/p = 2*n by rw [hP]; rw [show 2*(p*n) = p*(2*n) by ring, Nat.mul_div_cancel_left _ hp]] at this
  have fs_3P : Pistar p (3*P) * (p^(3*n) * (3*n) !) = (3*P) ! := by
    have := factsplit p (3*P) hp
    rwa [show (3*P)/p = 3*n by rw [hP]; rw [show 3*(p*n) = p*(3*n) by ring, Nat.mul_div_cancel_left _ hp]] at this
  have tele : Pistar p (2*P) * Wfun p (2*P) P = Pistar p (3*P) := by
    have := telescope p (2*P) P (Dvd.dvd.mul_left hdvd 2)
    rw [show 2*P + P = 3*P by ring] at this; omega
  have cha : (3*P).choose P * P ! * (2*P) ! = (3*P)! := by
    have := choose_id (3*P) P (by omega); rwa [show 3*P - P = 2*P by omega] at this
  have chb : (3*n).choose n * n ! * (2*n) ! = (3*n)! := by
    have := choose_id (3*n) n (by omega); rwa [show 3*n - n = 2*n by omega] at this
  -- cancel by K = p^n * n! * (2P)!
  apply Nat.eq_of_mul_eq_mul_right (show 0 < p^n * n ! * (2*P)! by positivity)
  have lhs : Pistar p P * (3*P).choose P * (p^n * n ! * (2*P)!) = (3*P)! := by
    calc Pistar p P * (3*P).choose P * (p^n * n ! * (2*P)!)
        = (Pistar p P * (p^n * n !)) * ((3*P).choose P * (2*P)!) := by ring
      _ = P ! * ((3*P).choose P * (2*P)!) := by rw [fs_P]
      _ = (3*P).choose P * P ! * (2*P)! := by ring
      _ = (3*P)! := cha
  have rhs : (3*n).choose n * Wfun p (2*P) P * (p^n * n ! * (2*P)!) = (3*P)! := by
    calc (3*n).choose n * Wfun p (2*P) P * (p^n * n ! * (2*P)!)
        = (3*n).choose n * (p^n * n !) * (Wfun p (2*P) P * (2*P)!) := by ring
      _ = (3*n).choose n * (p^n * n !) * (Wfun p (2*P) P * (Pistar p (2*P) * (p^(2*n) * (2*n)!))) := by rw [fs_2P]
      _ = (3*n).choose n * (p^n * n !) * ((Pistar p (2*P) * Wfun p (2*P) P) * (p^(2*n) * (2*n)!)) := by ring
      _ = (3*n).choose n * (p^n * n !) * (Pistar p (3*P) * (p^(2*n) * (2*n)!)) := by rw [tele]
      _ = Pistar p (3*P) * (p^(3*n)) * ((3*n).choose n * n ! * (2*n)!) := by rw [show 3*n = n + 2*n by ring, pow_add]; ring
      _ = Pistar p (3*P) * (p^(3*n)) * (3*n)! := by rw [chb]
      _ = Pistar p (3*P) * (p^(3*n) * (3*n)!) := by ring
      _ = (3*P)! := fs_3P
  rw [lhs, rhs]

-- B' W0 = B W1
theorem prodid2 (p n : ℕ) (hp : 0 < p) :
    Pistar p (p*n) * (2*(p*n)).choose (p*n) = (2*n).choose n * Wfun p (p*n) (p*n) := by
  set P := p * n with hP
  have hdvd : p ∣ P := ⟨n, hP⟩
  have fs_P : Pistar p P * (p^n * n !) = P ! := by
    have := factsplit p P hp
    rwa [hP, Nat.mul_div_cancel_left n hp] at this
  have fs_2P : Pistar p (2*P) * (p^(2*n) * (2*n) !) = (2*P) ! := by
    have := factsplit p (2*P) hp
    rwa [show (2*P)/p = 2*n by rw [hP]; rw [show 2*(p*n) = p*(2*n) by ring, Nat.mul_div_cancel_left _ hp]] at this
  have tele : Pistar p P * Wfun p P P = Pistar p (2*P) := by
    have := telescope p P P hdvd
    rw [show P + P = 2*P by ring] at this; omega
  have cha : (2*P).choose P * P ! * P ! = (2*P)! := by
    have := choose_id (2*P) P (by omega); rwa [show 2*P - P = P by omega] at this
  have chb : (2*n).choose n * n ! * n ! = (2*n)! := by
    have := choose_id (2*n) n (by omega); rwa [show 2*n - n = n by omega] at this
  apply Nat.eq_of_mul_eq_mul_right (show 0 < p^n * n ! * Nat.factorial P by positivity)
  have lhs : Pistar p P * (2*P).choose P * (p^n * n ! * P !) = (2*P)! := by
    calc Pistar p P * (2*P).choose P * (p^n * n ! * P !)
        = (Pistar p P * (p^n * n !)) * ((2*P).choose P * P !) := by ring
      _ = P ! * ((2*P).choose P * P !) := by rw [fs_P]
      _ = (2*P).choose P * P ! * P ! := by ring
      _ = (2*P)! := cha
  have rhs : (2*n).choose n * Wfun p P P * (p^n * n ! * P !) = (2*P)! := by
    calc (2*n).choose n * Wfun p P P * (p^n * n ! * P !)
        = (2*n).choose n * (p^n * n !) * (Wfun p P P * P !) := by ring
      _ = (2*n).choose n * (p^n * n !) * (Wfun p P P * (Pistar p P * (p^n * n !))) := by rw [fs_P]
      _ = (2*n).choose n * (p^n * n !) * ((Pistar p P * Wfun p P P) * (p^n * n !)) := by ring
      _ = (2*n).choose n * (p^n * n !) * (Pistar p (2*P) * (p^n * n !)) := by rw [tele]
      _ = Pistar p (2*P) * (p^(2*n)) * ((2*n).choose n * n ! * n !) := by rw [show 2*n = n + n by ring, pow_add]; ring
      _ = Pistar p (2*P) * (p^(2*n)) * (2*n)! := by rw [chb]
      _ = Pistar p (2*P) * (p^(2*n) * (2*n)!) := by ring
      _ = (2*P)! := fs_2P
  rw [lhs, rhs]

noncomputable def Lset (p P : ℕ) : Finset ℕ :=
  (Finset.Icc 1 P).filter (fun k => ¬ p ∣ k ∧ 2 * k < P)

theorem mem_Lset {p P k : ℕ} : k ∈ Lset p P ↔ (1 ≤ k ∧ k ≤ P) ∧ ¬ p ∣ k ∧ 2 * k < P := by
  unfold Lset
  rw [Finset.mem_filter, Finset.mem_Icc]

theorem mem_Uset {p P k : ℕ} : k ∈ Uset p P ↔ (1 ≤ k ∧ k ≤ P) ∧ ¬ p ∣ k := by
  unfold Uset
  rw [Finset.mem_filter, Finset.mem_Icc]

theorem lower_eq (p P : ℕ) :
    (Uset p P).filter (fun k => 2 * k < P) = Lset p P := by
  unfold Uset Lset
  rw [Finset.filter_filter]

theorem upper_eq_image (p P : ℕ) (hp : p.Prime) (hpP : p ∣ P) (hp2 : ¬ p ∣ 2) :
    (Uset p P).filter (fun k => ¬ 2 * k < P) = (Lset p P).image (fun l => P - l) := by
  ext k
  simp only [Finset.mem_filter, mem_Uset, mem_Lset, Finset.mem_image]
  constructor
  · rintro ⟨⟨⟨hk1, hk2⟩, hpk⟩, hle⟩
    -- 2k ≥ P; show 2k ≠ P, so 2k > P, k > P/2
    have hne : 2 * k ≠ P := by
      intro h
      have : p ∣ 2 * k := h ▸ hpP
      rcases (hp.dvd_mul.mp this) with h2 | hk
      · exact hp2 h2
      · exact hpk hk
    have hkP : k < P := by
      rcases lt_or_eq_of_le hk2 with h | h
      · exact h
      · exfalso; apply hpk; rw [h]; exact hpP
    refine ⟨P - k, ⟨⟨by omega, by omega⟩, ?_, by omega⟩, by omega⟩
    intro hd
    apply hpk
    have : p ∣ P - (P - k) := Nat.dvd_sub hpP hd
    rwa [show P - (P - k) = k by omega] at this
  · rintro ⟨l, ⟨⟨hl1, hl2⟩, hpl, hl3⟩, rfl⟩
    have hlP : l < P := by omega
    refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
    intro hd
    apply hpl
    have : p ∣ P - (P - l) := Nat.dvd_sub hpP hd
    rwa [show P - (P - l) = l by omega] at this

theorem pairing (p P t : ℕ) (hp : p.Prime) (hpP : p ∣ P) (hp2 : ¬ p ∣ 2) :
    (Wfun p (t*P) P : ℤ) =
      ∏ l ∈ Lset p P, ((l:ℤ) * ((P:ℤ) - (l:ℤ)) + (t:ℤ) * ((t:ℤ)+1) * (P:ℤ)^2) := by
  unfold Wfun
  push_cast
  rw [← Finset.prod_filter_mul_prod_filter_not (Uset p P) (fun k => 2 * k < P)]
  rw [lower_eq, upper_eq_image p P hp hpP hp2]
  rw [Finset.prod_image (by
    intro a ha b hb h
    have ha' : a ≤ P := (mem_Lset.mp ha).1.2
    have hb' : b ≤ P := (mem_Lset.mp hb).1.2
    have hh : P - a = P - b := h
    omega)]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l hl
  have hl' := mem_Lset.mp hl
  have hlP : l ≤ P := hl'.1.2
  rw [Nat.cast_sub hlP]
  push_cast
  ring

theorem sumsq6 (N : ℕ) : 6 * ∑ x ∈ Finset.range (N+1), x^2 = N*(N+1)*(2*N+1) := by
  induction N with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, Nat.mul_add, ih]; ring

theorem Uset_eq_range_filter (p P : ℕ) (hp : 0 < p) (hpP : p ∣ P) :
    Uset p P = (Finset.range P).filter (fun x => ¬ p ∣ x) := by
  ext x
  rw [mem_Uset, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, hpx⟩
    refine ⟨?_, hpx⟩
    rcases lt_or_eq_of_le h2 with h | h
    · exact h
    · exact absurd (h ▸ hpP) hpx
  · rintro ⟨h1, hpx⟩
    refine ⟨⟨?_, by omega⟩, hpx⟩
    rcases Nat.eq_zero_or_pos x with h | h
    · exact absurd (h ▸ Dvd.intro 0 rfl) hpx
    · exact h

theorem sum_filter_dvd (p P : ℕ) (hp : 0 < p) (hpP : p ∣ P) :
    ∑ x ∈ (Finset.range P).filter (fun x => p ∣ x), x^2 = p^2 * ∑ i ∈ Finset.range (P/p), i^2 := by
  obtain ⟨Q, hQ⟩ := hpP
  have hPQ : P / p = Q := by rw [hQ, Nat.mul_div_cancel_left _ hp]
  rw [Finset.mul_sum]
  rw [show (Finset.range P).filter (fun x => p ∣ x) = (Finset.range (P/p)).image (fun i => p * i) by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hx, c, rfl⟩
      refine ⟨c, ?_, rfl⟩
      rw [hPQ]
      have : p * c < p * Q := by rw [← hQ]; exact hx
      exact Nat.lt_of_mul_lt_mul_left this
    · rintro ⟨i, hi, rfl⟩
      rw [hPQ] at hi
      exact ⟨by rw [hQ]; exact (Nat.mul_lt_mul_left hp).mpr hi, ⟨i, rfl⟩⟩]
  rw [Finset.sum_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h)]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem Usq_split (p P : ℕ) (hp : 0 < p) (hpP : p ∣ P) :
    ∑ x ∈ Finset.range P, x^2 = p^2 * (∑ i ∈ Finset.range (P/p), i^2) + ∑ x ∈ Uset p P, x^2 := by
  rw [Uset_eq_range_filter p P hp hpP]
  rw [← sum_filter_dvd p P hp hpP]
  rw [Finset.sum_filter_add_sum_filter_not (Finset.range P) (fun x => p ∣ x)]

theorem sumsq6Z (N : ℕ) :
    (6:ℤ) * ∑ x ∈ Finset.range N, (x:ℤ)^2 = ((N:ℤ)-1)*(N:ℤ)*(2*(N:ℤ)-1) := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

-- Elementary symmetric: Esym q s j = e_j of the multiset {q i : i ∈ s}
noncomputable def Esym (q : ℕ → ℤ) (s : Finset ℕ) (j : ℕ) : ℤ :=
  ∑ t ∈ s.powersetCard j, ∏ i ∈ t, q i

theorem expand_master (q : ℕ → ℤ) (s : Finset ℕ) (c : ℤ) :
    ∏ i ∈ s, (q i + c)
      = ∑ i ∈ Finset.range (s.card + 1), (Esym q s i) * c ^ (s.card - i) := by
  rw [Finset.prod_add]
  rw [Finset.powerset_card_disjiUnion, Finset.sum_disjiUnion]
  apply Finset.sum_congr rfl
  intro i _
  unfold Esym
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_powersetCard] at ht
  obtain ⟨hts, htc⟩ := ht
  rw [Finset.prod_const]
  rw [Finset.card_sdiff_of_subset hts, htc]

theorem Esym_top (q : ℕ → ℤ) (s : Finset ℕ) : Esym q s s.card = ∏ i ∈ s, q i := by
  unfold Esym
  rw [Finset.powersetCard_self, Finset.sum_singleton]

theorem expand_trunc (q : ℕ → ℤ) (s : Finset ℕ) (c : ℤ) (hs : 2 ≤ s.card) :
    ∏ i ∈ s, (q i + c) ≡
      (∏ j ∈ s, q j) + c * Esym q s (s.card-1) + c^2 * Esym q s (s.card-2) [ZMOD c^3] := by
  obtain ⟨m, hm⟩ : ∃ m, s.card = m + 2 := ⟨s.card - 2, by omega⟩
  have htop : Esym q s (m+2) = ∏ j ∈ s, q j := by rw [← hm]; exact Esym_top q s
  rw [expand_master q s c, hm]
  rw [show m + 2 - 1 = m+1 by omega, show m + 2 - 2 = m by omega]
  rw [show m + 2 + 1 = m+3 by omega]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  rw [show m+2-(m+2) = 0 by omega, show m+2-(m+1) = 1 by omega, show m+2-m = 2 by omega]
  rw [pow_zero, pow_one, htop]
  have hdvd : (c^3) ∣ ∑ i ∈ Finset.range m, Esym q s i * c ^ (m + 2 - i) := by
    apply Finset.dvd_sum
    intro i hi
    rw [Finset.mem_range] at hi
    exact Dvd.dvd.mul_left (pow_dvd_pow c (by omega)) _
  rw [Int.modEq_iff_dvd]
  convert (dvd_neg.mpr hdvd) using 1
  ring

noncomputable def qfun (P : ℕ) : ℕ → ℤ := fun l => (l:ℤ) * ((P:ℤ) - (l:ℤ))

noncomputable def S1 (p P : ℕ) : ℤ := Esym (qfun P) (Lset p P) ((Lset p P).card - 1)
noncomputable def S2 (p P : ℕ) : ℤ := Esym (qfun P) (Lset p P) ((Lset p P).card - 2)

theorem Lcard_ge2 (p r : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hr : r ≥ 2) :
    2 ≤ (Lset p (p^r)).card := by
  have hPbig : 9 ≤ p^r := by
    calc (9:ℕ) = 3^2 := by norm_num
    _ ≤ p^2 := Nat.pow_le_pow_left hp3 2
    _ ≤ p^r := Nat.pow_le_pow_right (by omega) hr
  rw [show (2:ℕ) = 1 + 1 by rfl, Nat.add_one_le_iff, Finset.one_lt_card]
  refine ⟨1, ?_, 2, ?_, by omega⟩
  · rw [mem_Lset]; refine ⟨⟨le_refl 1, by omega⟩, ?_, by omega⟩
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  · rw [mem_Lset]; refine ⟨⟨by omega, by omega⟩, ?_, by omega⟩
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega

theorem hp_not_dvd_two {p : ℕ} (hp : p.Prime) (hp3 : p ≥ 3) : ¬ p ∣ 2 := by
  intro h; have := Nat.le_of_dvd (by norm_num) h; omega

theorem Wt_expand (p r t : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hr : r ≥ 2) :
    (Wfun p (t * p^r) (p^r) : ℤ)
      ≡ (Wfun p 0 (p^r) : ℤ)
        + ((t:ℤ)*((t:ℤ)+1) * (p:ℤ)^(2*r)) * S1 p (p^r)
        + ((t:ℤ)*((t:ℤ)+1) * (p:ℤ)^(2*r))^2 * S2 p (p^r)
        [ZMOD (p:ℤ)^(3*r+3)] := by
  set P := p^r with hP
  have hp2 : ¬ p ∣ 2 := hp_not_dvd_two hp hp3
  have hpP : p ∣ P := by rw [hP]; exact dvd_pow_self p (by omega)
  have hcard : 2 ≤ (Lset p P).card := Lcard_ge2 p r hp hp3 hr
  -- P^2 = p^(2r)
  have hPsq : (P:ℤ)^2 = (p:ℤ)^(2*r) := by rw [hP]; push_cast; rw [← pow_mul]; congr 1; ring
  set c : ℤ := (t:ℤ)*((t:ℤ)+1)*(P:ℤ)^2 with hc
  -- pairing
  have hpair := pairing p P t hp hpP hp2
  -- product is ∏ (qfun P l + c)
  have hprod : (Wfun p (t*P) P : ℤ) = ∏ l ∈ Lset p P, (qfun P l + c) := by
    rw [hpair]; apply Finset.prod_congr rfl; intro l _; unfold qfun; rw [hc]
  -- expansion
  have hexp := expand_trunc (qfun P) (Lset p P) c hcard
  -- W0 = ∏ qfun
  have hW0 : (Wfun p 0 P : ℤ) = ∏ l ∈ Lset p P, qfun P l := by
    have h0 := pairing p P 0 hp hpP hp2
    rw [Nat.zero_mul] at h0
    rw [h0]; apply Finset.prod_congr rfl; intro l _; unfold qfun; push_cast; ring
  -- c^3 divisible by M
  have hMc3 : (p:ℤ)^(3*r+3) ∣ c^3 := by
    have hc6 : c^3 = ((t:ℤ)*((t:ℤ)+1))^3 * ((p:ℤ)^(2*r))^3 := by rw [hc, hPsq]; ring
    rw [hc6, ← pow_mul]
    exact Dvd.dvd.mul_left (pow_dvd_pow (p:ℤ) (by omega)) _
  -- combine
  rw [hprod]
  calc ∏ l ∈ Lset p P, (qfun P l + c)
      ≡ (∏ j ∈ Lset p P, qfun P j) + c * Esym (qfun P) (Lset p P) ((Lset p P).card-1)
          + c^2 * Esym (qfun P) (Lset p P) ((Lset p P).card-2) [ZMOD (p:ℤ)^(3*r+3)] :=
        (hexp.of_dvd hMc3)
    _ = (Wfun p 0 P : ℤ) + c * S1 p P + c^2 * S2 p P := by
          rw [← hW0]; rfl
    _ = (Wfun p 0 P : ℤ) + ((t:ℤ)*((t:ℤ)+1) * (p:ℤ)^(2*r)) * S1 p P
          + ((t:ℤ)*((t:ℤ)+1) * (p:ℤ)^(2*r))^2 * S2 p P := by rw [hc, hPsq]

theorem Pistar_eq_Wfun0 (p P : ℕ) : Pistar p P = Wfun p 0 P := by
  unfold Pistar Wfun Uset
  apply Finset.prod_congr rfl
  intro k _; rw [Nat.zero_add]

theorem Z_modEq (p r : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hr : r ≥ 2) :
    ((3*p^(r-1)).choose (p^(r-1)) : ℤ)^2
        * ((Wfun p (2*p^r) (p^r):ℤ)^2 - (Wfun p 0 (p^r):ℤ)^2)
      - 27 * (Wfun p 0 (p^r):ℤ) * ((2*p^(r-1)).choose (p^(r-1)):ℤ)
          * ((Wfun p (1*p^r) (p^r):ℤ) - (Wfun p 0 (p^r):ℤ))
    ≡ 6*(p:ℤ)^(2*r)*(S1 p (p^r))*(Wfun p 0 (p^r):ℤ)
        *(2*((3*p^(r-1)).choose (p^(r-1)):ℤ)^2 - 9*((2*p^(r-1)).choose (p^(r-1)):ℤ))
      + 36*((p:ℤ)^(2*r))^2*((3*p^(r-1)).choose (p^(r-1)):ℤ)^2*(S1 p (p^r))^2
      + 36*((p:ℤ)^(2*r))^2*(S2 p (p^r))*(Wfun p 0 (p^r):ℤ)
        *(2*((3*p^(r-1)).choose (p^(r-1)):ℤ)^2 - 3*((2*p^(r-1)).choose (p^(r-1)):ℤ))
    [ZMOD (p:ℤ)^(3*r+3)] := by
  have h1 := Wt_expand p r 1 hp hp3 hr
  have h2 := Wt_expand p r 2 hp hp3 hr
  set M := (p:ℤ)^(3*r+3) with hM
  set P := p^r with hP
  set n := p^(r-1) with hn
  set e := (p:ℤ)^(2*r) with he
  set W0 := (Wfun p 0 P : ℤ) with hW0d
  set s1 := S1 p P with hs1
  set s2 := S2 p P with hs2
  set A := ((3*n).choose n : ℤ) with hA
  set B := ((2*n).choose n : ℤ) with hB
  -- expansions
  have hW1 : (Wfun p (1*P) P:ℤ) ≡ W0 + 2*e*s1 + 4*e^2*s2 [ZMOD M] :=
    calc (Wfun p (1*P) P:ℤ) ≡ _ [ZMOD M] := h1
      _ = W0 + 2*e*s1 + 4*e^2*s2 := by push_cast; ring
  have hW2 : (Wfun p (2*P) P:ℤ) ≡ W0 + 6*e*s1 + 36*e^2*s2 [ZMOD M] :=
    calc (Wfun p (2*P) P:ℤ) ≡ _ [ZMOD M] := h2
      _ = W0 + 6*e*s1 + 36*e^2*s2 := by push_cast; ring
  -- substitute into Z
  have hZsub : A^2 * ((Wfun p (2*P) P:ℤ)^2 - W0^2)
        - 27 * W0 * B * ((Wfun p (1*P) P:ℤ) - W0)
      ≡ A^2 * ((W0 + 6*e*s1 + 36*e^2*s2)^2 - W0^2)
        - 27 * W0 * B * ((W0 + 2*e*s1 + 4*e^2*s2) - W0) [ZMOD M] := by
    apply Int.ModEq.sub
    · exact Int.ModEq.mul_left _ (Int.ModEq.sub (hW2.pow 2) (Int.ModEq.refl _))
    · exact Int.ModEq.mul_left _ (Int.ModEq.sub hW1 (Int.ModEq.refl _))
  -- polynomial identity
  have hpoly : A^2 * ((W0 + 6*e*s1 + 36*e^2*s2)^2 - W0^2)
        - 27 * W0 * B * ((W0 + 2*e*s1 + 4*e^2*s2) - W0)
      = (6*e*s1*W0*(2*A^2-9*B) + 36*e^2*A^2*s1^2 + 36*e^2*s2*W0*(2*A^2-3*B))
        + 432*A^2*s2*s1*e^3 + 1296*A^2*s2^2*e^4 := by ring
  -- e^3, e^4 vanish mod M
  have he3 : M ∣ e^3 := by
    rw [he, ← pow_mul]; exact pow_dvd_pow (p:ℤ) (by omega)
  have he4 : M ∣ e^4 := by
    rw [he, ← pow_mul]; exact pow_dvd_pow (p:ℤ) (by omega)
  have htail : (6*e*s1*W0*(2*A^2-9*B) + 36*e^2*A^2*s1^2 + 36*e^2*s2*W0*(2*A^2-3*B))
        + 432*A^2*s2*s1*e^3 + 1296*A^2*s2^2*e^4
      ≡ (6*e*s1*W0*(2*A^2-9*B) + 36*e^2*A^2*s1^2 + 36*e^2*s2*W0*(2*A^2-3*B)) [ZMOD M] := by
    rw [Int.modEq_iff_dvd]
    have hd : M ∣ (432*A^2*s2*s1*e^3 + 1296*A^2*s2^2*e^4) :=
      dvd_add (he3.mul_left _) (he4.mul_left _)
    convert (dvd_neg.mpr hd) using 1
    ring
  exact ((hpoly ▸ hZsub).trans htail)

theorem Usq_int (p r : ℕ) (hp : 0 < p) (hr : 1 ≤ r) :
    (6:ℤ) * ∑ x ∈ Uset p (p^r), (x:ℤ)^2
      = (p:ℤ)^r * ((p:ℤ)-1) * (2*(p:ℤ)^(2*r-1) - 1) := by
  set P := p^r with hP
  have hpP : p ∣ P := by rw [hP]; exact dvd_pow_self p (by omega)
  have hPp : P / p = p^(r-1) := by
    have hpe : p^r = p^(r-1)*p := by rw [← pow_succ]; congr 1; omega
    rw [hP, hpe, Nat.mul_div_cancel _ hp]
  have hsplit := Usq_split p P hp hpP
  have hZ : ∑ x ∈ Finset.range P, (x:ℤ)^2
      = (p:ℤ)^2 * ∑ i ∈ Finset.range (P/p), (i:ℤ)^2 + ∑ x ∈ Uset p P, (x:ℤ)^2 := by
    have := congrArg (fun z : ℕ => (z:ℤ)) hsplit
    push_cast at this
    convert this using 2
  have hval : (6:ℤ) * ∑ x ∈ Uset p P, (x:ℤ)^2
      = ((P:ℤ)-1)*(P:ℤ)*(2*(P:ℤ)-1)
        - (p:ℤ)^2 * (((P/p:ℕ):ℤ)-1)*((P/p:ℕ):ℤ)*(2*((P/p:ℕ):ℤ)-1) := by
    have a1 := sumsq6Z P
    have a2 := sumsq6Z (P/p)
    have hexp : (6:ℤ) * ∑ x ∈ Finset.range P, (x:ℤ)^2
        = (p:ℤ)^2 * (6 * ∑ i ∈ Finset.range (P/p), (i:ℤ)^2) + 6 * ∑ x ∈ Uset p P, (x:ℤ)^2 := by
      rw [hZ]; ring
    rw [a1, a2] at hexp
    linarith [hexp]
  rw [hval, hPp]
  -- now algebra: substitute P = p^r, p^(r-1)
  have hr1 : r = (r-1) + 1 := by omega
  have e2 : ((p^(r-1):ℕ):ℤ) = (p:ℤ)^(r-1) := by push_cast; ring
  have e3 : (p:ℤ)^r = (p:ℤ) * (p:ℤ)^(r-1) := by
    conv_lhs => rw [hr1]
    rw [_root_.pow_succ']
  have e1 : (P:ℤ) = (p:ℤ) * (p:ℤ)^(r-1) := by
    rw [hP]; push_cast; exact e3
  have e4 : (p:ℤ)^(2*r-1) = (p:ℤ) * ((p:ℤ)^(r-1))^2 := by
    rw [← pow_mul]
    have : 2*r-1 = 2*(r-1) + 1 := by omega
    rw [this, _root_.pow_succ']
    congr 2
    omega
  rw [e2, e1, e3, e4]
  ring

def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

theorem powersetCard_sub_one_eq_image (s : Finset ℕ) (hs : 1 ≤ s.card) :
    s.powersetCard (s.card-1) = s.image (fun i => s.erase i) := by
  ext t
  rw [Finset.mem_powersetCard, Finset.mem_image]
  constructor
  · rintro ⟨hts, htc⟩
    have hcard : (s \ t).card = 1 := by
      rw [Finset.card_sdiff_of_subset hts, htc]; omega
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
    refine ⟨i, ?_, ?_⟩
    · have : i ∈ s \ t := by rw [hi]; exact Finset.mem_singleton_self i
      exact (Finset.mem_sdiff.mp this).1
    · rw [← Finset.sdiff_sdiff_eq_self hts, hi, ← Finset.erase_eq]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨Finset.erase_subset _ _, ?_⟩
    rw [Finset.card_erase_of_mem hi]

theorem esym_card_sub_one {R} [CommRing R] (f : ℕ → R) (s : Finset ℕ) (hs : 1 ≤ s.card) :
    ∑ t ∈ s.powersetCard (s.card-1), ∏ i ∈ t, f i = ∑ i ∈ s, ∏ j ∈ s.erase i, f j := by
  rw [powersetCard_sub_one_eq_image s hs]
  rw [Finset.sum_image]
  intro a ha b hb hab
  simp only [] at hab
  by_contra hne
  have : a ∈ s.erase b := Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp ha⟩
  rw [← hab] at this
  exact (Finset.notMem_erase a s) this

theorem PowerSumInv (p r k : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hr : r ≥ 1) :
    ∑ x ∈ Uset p (p^r), ((x:ZMod (p^r))⁻¹)^k = ∑ x ∈ Uset p (p^r), (x:ZMod (p^r))^k := by
  set N := p^r with hN
  have hN1 : 1 < N := by
    have : (3:ℕ) ≤ p^1 := by simpa using hp3
    calc 1 < 3 := by norm_num
    _ ≤ p^1 := this
    _ ≤ p^r := Nat.pow_le_pow_right (by omega) hr
  haveI : NeZero N := ⟨by rw [hN]; exact pow_ne_zero r (by omega)⟩
  haveI : Fact (1 < N) := ⟨hN1⟩
  -- coprimality of members
  have hcop : ∀ x ∈ Uset p N, Nat.Coprime x N := by
    intro x hx; rw [mem_Uset] at hx
    rw [hN]
    exact (Nat.Coprime.pow_right r ((hp.coprime_iff_not_dvd.mpr hx.2).symm))
  have hmulinv : ∀ x ∈ Uset p N, (x:ZMod N) * (x:ZMod N)⁻¹ = 1 := fun x hx =>
    ZMod.coe_mul_inv_eq_one x (hcop x hx)
  have hunit : ∀ x ∈ Uset p N, IsUnit (x:ZMod N) := fun x hx =>
    IsUnit.of_mul_eq_one _ (hmulinv x hx)
  have hval : ∀ x ∈ Uset p N, (x:ZMod N).val = x := by
    intro x hx; rw [mem_Uset] at hx
    apply ZMod.val_cast_of_lt
    rcases lt_or_eq_of_le hx.1.2 with h | h
    · exact h
    · exfalso; apply hx.2; rw [h, hN]; exact dvd_pow_self p (by omega)
  -- fv x = val of inverse
  set fv : ℕ → ℕ := fun x => ((x:ZMod N)⁻¹).val with hfv
  have hfvbar : ∀ x ∈ Uset p N, ((fv x : ℕ):ZMod N) = (x:ZMod N)⁻¹ := by
    intro x hx; rw [hfv]; exact ZMod.natCast_zmod_val _
  have hfvinvunit : ∀ x ∈ Uset p N, IsUnit ((x:ZMod N)⁻¹) :=
    fun x hx => IsUnit.of_mul_eq_one _ (ZMod.inv_mul_of_unit _ (hunit x hx))
  have hfvmem : ∀ x ∈ Uset p N, fv x ∈ Uset p N := by
    intro x hx
    rw [mem_Uset]
    have hbar := hfvbar x hx
    have hunitfv : IsUnit ((fv x : ℕ):ZMod N) := by rw [hbar]; exact hfvinvunit x hx
    have hcopfv : Nat.Coprime (fv x) N := (ZMod.isUnit_iff_coprime _ _).mp hunitfv
    have hne : fv x ≠ 0 := by
      intro h0
      have hz : ((fv x:ℕ):ZMod N) = 0 := by rw [h0]; simp
      rw [hbar] at hz
      have hm := hmulinv x hx
      rw [hz, mul_zero] at hm
      exact one_ne_zero hm.symm
    have hub : fv x ≤ N := by rw [hfv]; exact le_of_lt (ZMod.val_lt _)
    refine ⟨⟨by omega, hub⟩, ?_⟩
    intro hpd
    have hpN : p ∣ N := by rw [hN]; exact dvd_pow_self p (by omega)
    have hdg : p ∣ Nat.gcd (fv x) N := Nat.dvd_gcd hpd hpN
    rw [hcopfv] at hdg
    have := Nat.le_of_dvd one_pos hdg
    omega
  have hinvol : ∀ x ∈ Uset p N, fv (fv x) = x := by
    intro x hx
    have hbar := hfvbar x hx
    have hinv2 : ((fv x:ZMod N))⁻¹ = (x:ZMod N) := by
      rw [hbar]
      exact ZMod.inv_eq_of_mul_eq_one N _ _ (ZMod.inv_mul_of_unit _ (hunit x hx))
    show ((fv x : ZMod N)⁻¹).val = x
    rw [hinv2, hval x hx]
  refine Finset.sum_nbij' fv fv hfvmem hfvmem hinvol hinvol ?_
  intro x hx
  rw [hfvbar x hx]

theorem cast_inv_unit (p a r x : ℕ) (h : p^a ∣ p^r)
    (hcop : Nat.Coprime x (p^r)) :
    (ZMod.castHom h (ZMod (p^a))) ((x:ZMod (p^r))⁻¹) = (x:ZMod (p^a))⁻¹ := by
  have hunit_r : IsUnit (x:ZMod (p^r)) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
  have hmul : (x:ZMod (p^r)) * (x:ZMod (p^r))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunit_r
  have happ := congrArg (ZMod.castHom h (ZMod (p^a))) hmul
  rw [map_mul, map_one, map_natCast] at happ
  exact (ZMod.inv_eq_of_mul_eq_one (p^a) (x:ZMod (p^a)) _ happ).symm

theorem PowerSumInv_mod (p r a k : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hr : r ≥ 1) (ha : a ≤ r) :
    ∑ x ∈ Uset p (p^r), ((x:ZMod (p^a))⁻¹)^k = ∑ x ∈ Uset p (p^r), (x:ZMod (p^a))^k := by
  have hdvd : p^a ∣ p^r := pow_dvd_pow p ha
  have base := PowerSumInv p r k hp hp3 hr
  have hcop : ∀ x ∈ Uset p (p^r), Nat.Coprime x (p^r) := by
    intro x hx; rw [mem_Uset] at hx
    exact Nat.Coprime.pow_right r ((hp.coprime_iff_not_dvd.mpr hx.2).symm)
  calc ∑ x ∈ Uset p (p^r), ((x:ZMod (p^a))⁻¹)^k
      = ∑ x ∈ Uset p (p^r), (ZMod.castHom hdvd (ZMod (p^a))) (((x:ZMod (p^r))⁻¹)^k) := by
        apply Finset.sum_congr rfl; intro x hx
        rw [map_pow, cast_inv_unit p a r x hdvd (hcop x hx)]
    _ = (ZMod.castHom hdvd (ZMod (p^a))) (∑ x ∈ Uset p (p^r), ((x:ZMod (p^r))⁻¹)^k) := by
        rw [map_sum]
    _ = (ZMod.castHom hdvd (ZMod (p^a))) (∑ x ∈ Uset p (p^r), (x:ZMod (p^r))^k) := by rw [base]
    _ = ∑ x ∈ Uset p (p^r), (x:ZMod (p^a))^k := by
        rw [map_sum]; apply Finset.sum_congr rfl; intro x _
        rw [map_pow, map_natCast]

theorem pairing_invk (p r a k : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hr : r ≥ 1)
    (ha : a ≤ r) (hk : Even k) :
    ∑ x ∈ Uset p (p^r), ((x:ZMod (p^a))⁻¹)^k
      = 2 * ∑ i ∈ Lset p (p^r), ((i:ZMod (p^a))⁻¹)^k := by
  set P := p^r with hP
  have hpP : p ∣ P := dvd_pow_self p (by omega)
  have hp2 : ¬ p ∣ 2 := hp_not_dvd_two hp hp3
  have hPzero : (P:ZMod (p^a)) = 0 := by
    rw [hP]; exact (ZMod.natCast_eq_zero_iff (p^r) (p^a)).mpr (pow_dvd_pow p ha)
  rw [← Finset.sum_filter_add_sum_filter_not (Uset p P) (fun j => 2 * j < P)]
  rw [lower_eq, upper_eq_image p P hp hpP hp2]
  rw [Finset.sum_image (by
    intro x hx y hy h
    simp only [] at h
    have hx' : x ≤ P := (mem_Lset.mp hx).1.2
    have hy' : y ≤ P := (mem_Lset.mp hy).1.2
    omega)]
  rw [two_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mem_Lset] at hi
  have hiP : i ≤ P := hi.1.2
  have hunit : IsUnit (i:ZMod (p^a)) :=
    (ZMod.isUnit_iff_coprime i (p^a)).mpr (Nat.Coprime.pow_right a ((hp.coprime_iff_not_dvd.mpr hi.2.1).symm))
  have hcast : (((P - i:ℕ)):ZMod (p^a)) = -(i:ZMod (p^a)) := by
    rw [Nat.cast_sub hiP, hPzero]; ring
  rw [hcast]
  have hneg : ((-(i:ZMod (p^a)))⁻¹) = -((i:ZMod (p^a))⁻¹) :=
    ZMod.inv_eq_of_mul_eq_one (p^a) _ _ (by rw [neg_mul_neg]; exact ZMod.mul_inv_of_unit _ hunit)
  rw [hneg, hk.neg_pow]

theorem sumU_sq_zmod (p r a : ℕ) (hdiv : (p:ℤ)^a ∣ ∑ x ∈ Uset p (p^r), (x:ℤ)^2) :
    ∑ x ∈ Uset p (p^r), (x:ZMod (p^a))^2 = 0 := by
  obtain ⟨m, hm⟩ := hdiv
  have hcast : ((∑ x ∈ Uset p (p^r), (x:ℤ)^2 : ℤ) : ZMod (p^a))
       = ∑ x ∈ Uset p (p^r), (x:ZMod (p^a))^2 := by push_cast; rfl
  rw [← hcast, hm]
  have hp0 : (p:ZMod (p^a))^a = 0 := by
    rw [show (p:ZMod (p^a))^a = ((p^a : ℕ):ZMod (p^a)) by push_cast; ring]
    exact ZMod.natCast_self _
  push_cast
  rw [hp0, zero_mul]

theorem faulhaber_dvd_ge5 (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    (p:ℤ)^r ∣ ∑ x ∈ Uset p (p^r), (x:ℤ)^2 := by
  have hu := Usq_int p r hp.pos hr
  have hdvd6 : (p:ℤ)^r ∣ 6 * ∑ x ∈ Uset p (p^r), (x:ℤ)^2 :=
    ⟨((p:ℤ)-1) * (2*(p:ℤ)^(2*r-1) - 1), by rw [hu]; ring⟩
  have hnd_nat : ¬ p ∣ 6 := by
    intro h
    rcases (hp.prime.dvd_mul.mp (show p ∣ 2*3 by norm_num at h ⊢; exact h)) with h2 | h3
    · exact absurd (Nat.le_of_dvd (by norm_num) h2) (by omega)
    · exact absurd (Nat.le_of_dvd (by norm_num) h3) (by omega)
  have hcop : IsCoprime ((p:ℤ)^r) (6:ℤ) := by
    apply IsCoprime.pow_left
    rw [(Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
    rw [show (6:ℤ)=((6:ℕ):ℤ) by norm_num, Int.natCast_dvd_natCast]
    exact hnd_nat
  exact hcop.dvd_of_dvd_mul_left hdvd6

theorem faulhaber_dvd_3 (r : ℕ) (hr : 1 ≤ r) :
    (3:ℤ)^(r-1) ∣ ∑ x ∈ Uset 3 (3^r), (x:ℤ)^2 := by
  have hu := Usq_int 3 r (by norm_num) hr
  -- 6 * ∑ = 3^r * 2 * (2*3^{2r-1}-1)
  have h2 : (2:ℤ) * ∑ x ∈ Uset 3 (3^r), (x:ℤ)^2
      = (3:ℤ)^(r-1) * (2 * (2*(3:ℤ)^(2*r-1) - 1)) := by
    have h3ne : (3:ℤ) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h3ne
    rw [show (3:ℤ) * (2 * ∑ x ∈ Uset 3 (3^r), (x:ℤ)^2) = 6 * ∑ x ∈ Uset 3 (3^r), (x:ℤ)^2 by ring]
    rw [hu]
    push_cast
    rw [show (3:ℤ)^r = 3 * (3:ℤ)^(r-1) by
      conv_lhs => rw [show r = (r-1)+1 by omega]
      rw [_root_.pow_succ']]
    ring
  have hdvd2 : (3:ℤ)^(r-1) ∣ 2 * ∑ x ∈ Uset 3 (3^r), (x:ℤ)^2 :=
    ⟨2 * (2*(3:ℤ)^(2*r-1) - 1), h2⟩
  have hcop : IsCoprime ((3:ℤ)^(r-1)) (2:ℤ) := by
    apply IsCoprime.pow_left
    rw [Int.isCoprime_iff_gcd_eq_one]; decide
  exact hcop.dvd_of_dvd_mul_left hdvd2

theorem invsum_zero_k (p r a k : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hr : r ≥ 1)
    (ha : a ≤ r) (hk : Even k)
    (hfaul : ∑ x ∈ Uset p (p^r), (x:ZMod (p^a))^k = 0) :
    ∑ i ∈ Lset p (p^r), ((i:ZMod (p^a))⁻¹)^k = 0 := by
  have h2 : (2:ZMod (p^a)) * ∑ i ∈ Lset p (p^r), ((i:ZMod (p^a))⁻¹)^k = 0 := by
    rw [← pairing_invk p r a k hp hp3 hr ha hk,
        PowerSumInv_mod p r a k hp hp3 (by omega) ha]
    exact hfaul
  have hunit2 : IsUnit (2:ZMod (p^a)) :=
    (ZMod.isUnit_iff_coprime 2 (p^a)).mpr
      (Nat.Coprime.pow_right a ((hp.coprime_iff_not_dvd.mpr (hp_not_dvd_two hp hp3)).symm))
  exact (hunit2.mul_right_eq_zero).mp h2

theorem G1' (p P a : ℕ) (hp : p.Prime) (hp3 : p ≥ 3)
    (hcard : 2 ≤ (Lset p P).card)
    (hPdvd : (p^a : ℕ) ∣ P)
    (hinvsum : ∑ i ∈ Lset p P, ((i:ZMod (p^a))⁻¹)^2 = 0) :
    (p:ℤ)^a ∣ (S1 p P) := by
  rw [show ((p:ℤ)^a) = (((p^a:ℕ)):ℤ) by push_cast; ring]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set qb : ℕ → ZMod (p^a) := fun j => ((qfun P j : ℤ) : ZMod (p^a)) with hqb
  set L := Lset p P with hLdef
  have hPzero : (↑P:ZMod (p^a)) = 0 :=
    (ZMod.natCast_eq_zero_iff P (p^a)).mpr hPdvd
  have hqval : ∀ i ∈ L, qb i = -(i:ZMod (p^a))^2 := by
    intro i _; rw [hqb]; simp only [qfun]; push_cast; rw [hPzero]; ring
  have hiunit : ∀ i ∈ L, IsUnit (i:ZMod (p^a)) := by
    intro i hi; rw [hLdef, mem_Lset] at hi
    exact (ZMod.isUnit_iff_coprime i (p^a)).mpr
      (Nat.Coprime.pow_right a ((hp.coprime_iff_not_dvd.mpr hi.2.1).symm))
  have hqunit : ∀ i ∈ L, IsUnit (qb i) := by
    intro i hi; rw [hqval i hi]; exact ((hiunit i hi).pow 2).neg
  have hS1img : ((S1 p P : ℤ):ZMod (p^a)) = ∑ i ∈ L, ∏ j ∈ L.erase i, qb j := by
    show ((Esym (qfun P) L (L.card-1) : ℤ):ZMod (p^a)) = _
    unfold Esym
    rw [Int.cast_sum]
    simp_rw [Int.cast_prod]
    exact esym_card_sub_one qb L (by omega)
  have hinvval : ∀ i ∈ L, (qb i)⁻¹ = -((i:ZMod (p^a))⁻¹)^2 := by
    intro i hi
    rw [hqval i hi]
    apply ZMod.inv_eq_of_mul_eq_one
    rw [neg_mul_neg, ← mul_pow, ZMod.mul_inv_of_unit _ (hiunit i hi), one_pow]
  have hsuminv : ∑ i ∈ L, (qb i)⁻¹ = 0 := by
    rw [Finset.sum_congr rfl hinvval, Finset.sum_neg_distrib, hinvsum, neg_zero]
  have hfactor : ∀ i ∈ L, ∏ j ∈ L.erase i, qb j = (∏ j ∈ L, qb j) * (qb i)⁻¹ := by
    intro i hi
    have hmp := Finset.mul_prod_erase L qb hi
    rw [← hmp, mul_comm (qb i) (∏ j ∈ L.erase i, qb j), mul_assoc,
        ZMod.mul_inv_of_unit _ (hqunit i hi), mul_one]
  rw [hS1img, Finset.sum_congr rfl hfactor, ← Finset.mul_sum, hsuminv, mul_zero]

theorem G1 (p r a : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hr : r ≥ 2) (ha : a ≤ r)
    (hfaul : ∑ x ∈ Uset p (p^r), (x:ZMod (p^a))^2 = 0) :
    (p:ℤ)^a ∣ (S1 p (p^r)) :=
  G1' p (p^r) a hp hp3 (Lcard_ge2 p r hp hp3 hr) (pow_dvd_pow p ha)
    (invsum_zero_k p r a 2 hp hp3 (by omega) ha (by norm_num) hfaul)

theorem coprime_pW (p P : ℕ) (hp : p.Prime) : IsCoprime (p:ℤ) (Wfun p 0 P : ℤ) := by
  rw [(Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd, Int.natCast_dvd_natCast]
  unfold Wfun
  rw [hp.prime.dvd_finset_prod_iff]
  push_neg
  intro k hk
  rw [Nat.zero_add]
  rw [mem_Uset] at hk
  exact hk.2

-- ============ C lemma: p^3 ∣ 2A^2 - 9B ============

theorem Lcardp_ge2 (p : ℕ) (hp5 : 5 ≤ p) : 2 ≤ (Lset p p).card := by
  rw [show (2:ℕ)=1+1 by rfl, Nat.add_one_le_iff, Finset.one_lt_card]
  refine ⟨1, ?_, 2, ?_, by omega⟩
  · rw [mem_Lset]; refine ⟨⟨le_refl 1, by omega⟩, ?_, by omega⟩
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  · rw [mem_Lset]; refine ⟨⟨by omega, by omega⟩, ?_, by omega⟩
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega

theorem S1p_dvd (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) : (p:ℤ) ∣ S1 p p := by
  have hfaulint : (p:ℤ)^1 ∣ ∑ x ∈ Uset p (p^1), (x:ℤ)^2 :=
    faulhaber_dvd_ge5 p 1 hp hp5 (le_refl 1)
  have hfaul : ∑ x ∈ Uset p (p^1), (x:ZMod (p^1))^2 = 0 := sumU_sq_zmod p 1 1 hfaulint
  have hinv := invsum_zero_k p 1 1 2 hp (by omega) (le_refl 1) (le_refl 1) (by norm_num) hfaul
  have hres := G1' p (p^1) 1 hp (by omega) (by rw [pow_one]; exact Lcardp_ge2 p hp5)
    (dvd_refl _) hinv
  rw [pow_one] at hres
  rw [pow_one] at hres
  exact hres

theorem Wexp_p (p t : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hp5 : 5 ≤ p) :
    (Wfun p (t*p) p:ℤ) ≡ (Wfun p 0 p:ℤ) + ((t:ℤ)*((t:ℤ)+1)*(p:ℤ)^2)*S1 p p [ZMOD (p:ℤ)^3] := by
  have hp2 : ¬ p ∣ 2 := hp_not_dvd_two hp hp3
  have hpP : p ∣ p := dvd_refl p
  have hcard : 2 ≤ (Lset p p).card := Lcardp_ge2 p hp5
  set c : ℤ := (t:ℤ)*((t:ℤ)+1)*(p:ℤ)^2 with hc
  have hpair := pairing p p t hp hpP hp2
  have hprod : (Wfun p (t*p) p : ℤ) = ∏ l ∈ Lset p p, (qfun p l + c) := by
    rw [hpair]; apply Finset.prod_congr rfl; intro l _; unfold qfun; rw [hc]
  have hexp := expand_trunc (qfun p) (Lset p p) c hcard
  have hW0 : (Wfun p 0 p : ℤ) = ∏ l ∈ Lset p p, qfun p l := by
    have h0 := pairing p p 0 hp hpP hp2
    rw [Nat.zero_mul] at h0
    rw [h0]; apply Finset.prod_congr rfl; intro l _; unfold qfun; push_cast; ring
  have hMc3 : (p:ℤ)^3 ∣ c^3 := by
    have hh : c^3 = ((t:ℤ)*((t:ℤ)+1))^3 * ((p:ℤ)^2)^3 := by rw [hc]; ring
    rw [hh, ← pow_mul]; exact Dvd.dvd.mul_left (pow_dvd_pow (p:ℤ) (by omega)) _
  have hdrop : (p:ℤ)^3 ∣ c^2 * S2 p p := by
    have hh : c^2 = ((t:ℤ)*((t:ℤ)+1))^2 * ((p:ℤ)^2)^2 := by rw [hc]; ring
    rw [hh]
    have h4 : (p:ℤ)^3 ∣ ((p:ℤ)^2)^2 := by rw [← pow_mul]; exact pow_dvd_pow (p:ℤ) (by omega)
    exact (h4.mul_left _).mul_right _
  rw [hprod]
  have step : ∏ l ∈ Lset p p, (qfun p l + c)
      ≡ (Wfun p 0 p:ℤ) + c * S1 p p + c^2 * S2 p p [ZMOD (p:ℤ)^3] :=
    calc ∏ l ∈ Lset p p, (qfun p l + c)
        ≡ (∏ j ∈ Lset p p, qfun p j) + c * Esym (qfun p) (Lset p p) ((Lset p p).card-1)
            + c^2 * Esym (qfun p) (Lset p p) ((Lset p p).card-2) [ZMOD (p:ℤ)^3] := hexp.of_dvd hMc3
      _ = (Wfun p 0 p:ℤ) + c * S1 p p + c^2 * S2 p p := by rw [← hW0]; rfl
  refine step.trans (Int.modEq_iff_dvd.mpr ?_)
  have heq : ((Wfun p 0 p:ℤ) + c * S1 p p)
      - ((Wfun p 0 p:ℤ) + c * S1 p p + c^2 * S2 p p) = -(c^2 * S2 p p) := by ring
  rw [heq]; exact dvd_neg.mpr hdrop

theorem Wcong0_p (p t : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (Wfun p (t*p) p:ℤ) ≡ (Wfun p 0 p:ℤ) [ZMOD (p:ℤ)^3] := by
  refine (Wexp_p p t hp (by omega) hp5).trans (Int.modEq_iff_dvd.mpr ?_)
  obtain ⟨m, hm⟩ := S1p_dvd p hp hp5
  have heq : (Wfun p 0 p:ℤ) - ((Wfun p 0 p:ℤ) + ((t:ℤ)*((t:ℤ)+1)*(p:ℤ)^2)*S1 p p)
      = -(((t:ℤ)*((t:ℤ)+1)*(p:ℤ)^2)*(S1 p p)) := by ring
  rw [heq, hm]
  exact dvd_neg.mpr ⟨(t:ℤ)*((t:ℤ)+1)*m, by ring⟩

theorem A1cong3 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((3*p).choose p:ℤ) ≡ 3 [ZMOD (p:ℤ)^3] := by
  have hid := prodid3 p 1 hp.pos
  rw [Nat.mul_one] at hid
  rw [Pistar_eq_Wfun0] at hid
  have h31 : (3*1).choose 1 = 3 := by decide
  rw [h31] at hid
  have hidZ : (Wfun p 0 p:ℤ) * ((3*p).choose p:ℤ) = 3 * (Wfun p (2*p) p:ℤ) := by exact_mod_cast hid
  have hmod : (Wfun p 0 p:ℤ)*((3*p).choose p:ℤ) ≡ (Wfun p 0 p:ℤ)*3 [ZMOD (p:ℤ)^3] := by
    rw [hidZ]
    calc (3:ℤ)*(Wfun p (2*p) p:ℤ) ≡ 3*(Wfun p 0 p:ℤ) [ZMOD (p:ℤ)^3] :=
          Int.ModEq.mul_left 3 (Wcong0_p p 2 hp hp5)
      _ = (Wfun p 0 p:ℤ)*3 := by ring
  rw [Int.modEq_iff_dvd] at hmod ⊢
  rw [← mul_sub] at hmod
  exact ((coprime_pW p p hp).pow_left).dvd_of_dvd_mul_left hmod

theorem B1cong2 (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ((2*p).choose p:ℤ) ≡ 2 [ZMOD (p:ℤ)^3] := by
  have hid := prodid2 p 1 hp.pos
  rw [Nat.mul_one] at hid
  rw [Pistar_eq_Wfun0] at hid
  have h21 : (2*1).choose 1 = 2 := by decide
  rw [h21] at hid
  have hidZ : (Wfun p 0 p:ℤ) * ((2*p).choose p:ℤ) = 2 * (Wfun p p p:ℤ) := by exact_mod_cast hid
  have hW1cong : (Wfun p p p:ℤ) ≡ (Wfun p 0 p:ℤ) [ZMOD (p:ℤ)^3] := by
    have h := Wcong0_p p 1 hp hp5; rwa [one_mul] at h
  have hmod : (Wfun p 0 p:ℤ)*((2*p).choose p:ℤ) ≡ (Wfun p 0 p:ℤ)*2 [ZMOD (p:ℤ)^3] := by
    rw [hidZ]
    calc (2:ℤ)*(Wfun p p p:ℤ) ≡ 2*(Wfun p 0 p:ℤ) [ZMOD (p:ℤ)^3] := Int.ModEq.mul_left 2 hW1cong
      _ = (Wfun p 0 p:ℤ)*2 := by ring
  rw [Int.modEq_iff_dvd] at hmod ⊢
  rw [← mul_sub] at hmod
  exact ((coprime_pW p p hp).pow_left).dvd_of_dvd_mul_left hmod

theorem Wcong0 (p k t : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hk : k ≥ 2) :
    (Wfun p (t*p^k) (p^k):ℤ) ≡ (Wfun p 0 (p^k):ℤ) [ZMOD (p:ℤ)^3] := by
  have hexp := (Wt_expand p k t hp hp3 hk).of_dvd
    (pow_dvd_pow (p:ℤ) (show 3 ≤ 3*k+3 by omega))
  refine hexp.trans (Int.modEq_iff_dvd.mpr ?_)
  set c : ℤ := (t:ℤ)*((t:ℤ)+1) * (p:ℤ)^(2*k) with hc
  have hcdvd : (p:ℤ)^3 ∣ c := by
    rw [hc, show ((t:ℤ)*((t:ℤ)+1) * (p:ℤ)^(2*k)) = ((t:ℤ)*((t:ℤ)+1)) * (p:ℤ)^(2*k) by ring]
    exact dvd_mul_of_dvd_right (pow_dvd_pow (p:ℤ) (by omega)) _
  have hd : (p:ℤ)^3 ∣ c * S1 p (p^k) + c^2 * S2 p (p^k) :=
    dvd_add (dvd_mul_of_dvd_left hcdvd _)
      (dvd_mul_of_dvd_left (dvd_trans hcdvd (dvd_pow_self c (by norm_num))) _)
  have heq : (Wfun p 0 (p^k):ℤ)
      - ((Wfun p 0 (p^k):ℤ) + c * S1 p (p^k) + c^2 * S2 p (p^k))
      = -(c * S1 p (p^k) + c^2 * S2 p (p^k)) := by ring
  rw [heq]; exact dvd_neg.mpr hd

theorem Cstep3 (p k : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hk : k ≥ 2) :
    ((3*p^k).choose (p^k):ℤ) ≡ ((3*p^(k-1)).choose (p^(k-1)):ℤ) [ZMOD (p:ℤ)^3] := by
  have hpos := hp.pos
  have hpn : p * p^(k-1) = p^k := by rw [← _root_.pow_succ']; congr 1; omega
  have hid := prodid3 p (p^(k-1)) hpos
  rw [hpn] at hid
  rw [Pistar_eq_Wfun0] at hid
  have hidZ : (Wfun p 0 (p^k):ℤ) * ((3*p^k).choose (p^k):ℤ)
      = ((3*p^(k-1)).choose (p^(k-1)):ℤ) * (Wfun p (2*p^k) (p^k):ℤ) := by exact_mod_cast hid
  have hWcong := Wcong0 p k 2 hp hp3 hk
  have hmod : (Wfun p 0 (p^k):ℤ) * ((3*p^k).choose (p^k):ℤ)
      ≡ (Wfun p 0 (p^k):ℤ) * ((3*p^(k-1)).choose (p^(k-1)):ℤ) [ZMOD (p:ℤ)^3] := by
    rw [hidZ]
    calc ((3*p^(k-1)).choose (p^(k-1)):ℤ) * (Wfun p (2*p^k) (p^k):ℤ)
        ≡ ((3*p^(k-1)).choose (p^(k-1)):ℤ) * (Wfun p 0 (p^k):ℤ) [ZMOD (p:ℤ)^3] :=
          Int.ModEq.mul_left _ hWcong
      _ = (Wfun p 0 (p^k):ℤ) * ((3*p^(k-1)).choose (p^(k-1)):ℤ) := by ring
  rw [Int.modEq_iff_dvd] at hmod ⊢
  rw [← mul_sub] at hmod
  exact ((coprime_pW p (p^k) hp).pow_left).dvd_of_dvd_mul_left hmod

theorem Cstep2 (p k : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hk : k ≥ 2) :
    ((2*p^k).choose (p^k):ℤ) ≡ ((2*p^(k-1)).choose (p^(k-1)):ℤ) [ZMOD (p:ℤ)^3] := by
  have hpos := hp.pos
  have hpn : p * p^(k-1) = p^k := by rw [← _root_.pow_succ']; congr 1; omega
  have hid := prodid2 p (p^(k-1)) hpos
  rw [hpn] at hid
  rw [Pistar_eq_Wfun0] at hid
  have hidZ : (Wfun p 0 (p^k):ℤ) * ((2*p^k).choose (p^k):ℤ)
      = ((2*p^(k-1)).choose (p^(k-1)):ℤ) * (Wfun p (p^k) (p^k):ℤ) := by exact_mod_cast hid
  have hWcong : (Wfun p (p^k) (p^k):ℤ) ≡ (Wfun p 0 (p^k):ℤ) [ZMOD (p:ℤ)^3] := by
    have h := Wcong0 p k 1 hp hp3 hk; rwa [one_mul] at h
  have hmod : (Wfun p 0 (p^k):ℤ) * ((2*p^k).choose (p^k):ℤ)
      ≡ (Wfun p 0 (p^k):ℤ) * ((2*p^(k-1)).choose (p^(k-1)):ℤ) [ZMOD (p:ℤ)^3] := by
    rw [hidZ]
    calc ((2*p^(k-1)).choose (p^(k-1)):ℤ) * (Wfun p (p^k) (p^k):ℤ)
        ≡ ((2*p^(k-1)).choose (p^(k-1)):ℤ) * (Wfun p 0 (p^k):ℤ) [ZMOD (p:ℤ)^3] :=
          Int.ModEq.mul_left _ hWcong
      _ = (Wfun p 0 (p^k):ℤ) * ((2*p^(k-1)).choose (p^(k-1)):ℤ) := by ring
  rw [Int.modEq_iff_dvd] at hmod ⊢
  rw [← mul_sub] at hmod
  exact ((coprime_pW p (p^k) hp).pow_left).dvd_of_dvd_mul_left hmod

theorem Atele (p m : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    ((3*p^(m+1)).choose (p^(m+1)):ℤ) ≡ ((3*p^1).choose (p^1):ℤ) [ZMOD (p:ℤ)^3] := by
  induction m with
  | zero => exact Int.ModEq.refl _
  | succ j ih =>
    have hstep := Cstep3 p (j+2) hp hp3 (by omega)
    rw [show j+2-1 = j+1 by omega] at hstep
    exact hstep.trans ih

theorem Btele (p m : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) :
    ((2*p^(m+1)).choose (p^(m+1)):ℤ) ≡ ((2*p^1).choose (p^1):ℤ) [ZMOD (p:ℤ)^3] := by
  induction m with
  | zero => exact Int.ModEq.refl _
  | succ j ih =>
    have hstep := Cstep2 p (j+2) hp hp3 (by omega)
    rw [show j+2-1 = j+1 by omega] at hstep
    exact hstep.trans ih

theorem Clemma (p r : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hr : r ≥ 2) :
    (p:ℤ)^3 ∣ (2*((3*p^(r-1)).choose (p^(r-1)):ℤ)^2 - 9*((2*p^(r-1)).choose (p^(r-1)):ℤ)) := by
  have hAt : ((3*p^(r-1)).choose (p^(r-1)):ℤ) ≡ ((3*p).choose p:ℤ) [ZMOD (p:ℤ)^3] := by
    have h := Atele p (r-2) hp hp3
    rw [show r-2+1 = r-1 by omega, pow_one] at h
    exact h
  have hBt : ((2*p^(r-1)).choose (p^(r-1)):ℤ) ≡ ((2*p).choose p:ℤ) [ZMOD (p:ℤ)^3] := by
    have h := Btele p (r-2) hp hp3
    rw [show r-2+1 = r-1 by omega, pow_one] at h
    exact h
  rcases eq_or_lt_of_le hp3 with h3 | hgt
  · -- p = 3
    subst h3
    have h3val : ((3*3).choose 3 : ℤ) = 84 := by decide
    have h2val : ((2*3).choose 3 : ℤ) = 20 := by decide
    rw [h3val] at hAt
    rw [h2val] at hBt
    have key : (2*((3*3^(r-1)).choose (3^(r-1)):ℤ)^2 - 9*((2*3^(r-1)).choose (3^(r-1)):ℤ))
        ≡ 0 [ZMOD ((3:ℕ):ℤ)^3] := by
      calc (2*((3*3^(r-1)).choose (3^(r-1)):ℤ)^2 - 9*((2*3^(r-1)).choose (3^(r-1)):ℤ))
          ≡ 2*(84:ℤ)^2 - 9*20 [ZMOD ((3:ℕ):ℤ)^3] :=
            Int.ModEq.sub (Int.ModEq.mul_left 2 (hAt.pow 2)) (Int.ModEq.mul_left 9 hBt)
        _ ≡ 0 [ZMOD ((3:ℕ):ℤ)^3] := by
            rw [Int.modEq_zero_iff_dvd]; norm_num
    exact Int.modEq_zero_iff_dvd.mp key
  · -- p ≥ 5
    have hp5 : 5 ≤ p := by
      by_contra h
      push_neg at h
      interval_cases p
      · exact absurd hp (by decide)
    have hA3 := hAt.trans (A1cong3 p hp hp5)
    have hB2 := hBt.trans (B1cong2 p hp hp5)
    have key : (2*((3*p^(r-1)).choose (p^(r-1)):ℤ)^2 - 9*((2*p^(r-1)).choose (p^(r-1)):ℤ))
        ≡ 0 [ZMOD (p:ℤ)^3] := by
      calc (2*((3*p^(r-1)).choose (p^(r-1)):ℤ)^2 - 9*((2*p^(r-1)).choose (p^(r-1)):ℤ))
          ≡ 2*(3:ℤ)^2 - 9*2 [ZMOD (p:ℤ)^3] :=
            Int.ModEq.sub (Int.ModEq.mul_left 2 (hA3.pow 2)) (Int.ModEq.mul_left 9 hB2)
        _ = 0 := by norm_num
    exact Int.modEq_zero_iff_dvd.mp key

-- ============ G2 : p ∣ S2 (4th-power Faulhaber + Newton) ============

theorem Usum_pow_zmod (p r k : ℕ) (hp : p.Prime) (hr : r ≥ 2) :
    ∑ x ∈ Uset p (p^r), (x:ZMod p)^k = 0 := by
  have hpe : p^(r-1) * p = p^r := by rw [← pow_succ]; congr 1; omega
  set t := Finset.range (p^(r-1)) ×ˢ Finset.Ico 1 p with ht
  have hbij : ∑ x ∈ Uset p (p^r), (x:ZMod p)^k = ∑ b ∈ t, ((b.2:ℕ):ZMod p)^k := by
    refine Finset.sum_nbij' (fun x => (x/p, x%p)) (fun b => b.1*p + b.2) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [mem_Uset] at hx
      obtain ⟨⟨hx1, hx2⟩, hpx⟩ := hx
      rw [ht, Finset.mem_product, Finset.mem_range, Finset.mem_Ico]
      have hxlt : x < p^r := by
        rcases lt_or_eq_of_le hx2 with h | h
        · exact h
        · exact absurd (h ▸ dvd_pow_self p (show r ≠ 0 by omega)) hpx
      refine ⟨?_, ?_, Nat.mod_lt _ hp.pos⟩
      · rw [Nat.div_lt_iff_lt_mul hp.pos, hpe]; exact hxlt
      · rcases Nat.eq_zero_or_pos (x%p) with h | h
        · exact absurd (Nat.dvd_of_mod_eq_zero h) hpx
        · exact h
    · intro b hb
      rw [ht, Finset.mem_product, Finset.mem_range, Finset.mem_Ico] at hb
      obtain ⟨hb1, hb2l, hb2r⟩ := hb
      rw [mem_Uset]
      have hjle : b.1*p + b.2 ≤ p^r := by
        have h1 : b.1*p ≤ (p^(r-1)-1)*p := Nat.mul_le_mul_right _ (by omega)
        have h2 : (p^(r-1)-1)*p = p^r - p := by rw [Nat.sub_mul, one_mul, hpe]
        have hple : p ≤ p^r := Nat.le_of_dvd (pow_pos hp.pos r) (dvd_pow_self p (by omega))
        rw [h2] at h1
        omega
      refine ⟨⟨le_trans hb2l (Nat.le_add_left b.2 (b.1*p)), hjle⟩, ?_⟩
      intro hd
      have : p ∣ b.2 := (Nat.dvd_add_right ⟨b.1, by ring⟩).mp hd
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    · intro x hx
      show (x/p)*p + x%p = x
      rw [mul_comm, Nat.div_add_mod]
    · intro b hb
      rw [ht, Finset.mem_product, Finset.mem_range, Finset.mem_Ico] at hb
      obtain ⟨hb1, hb2l, hb2r⟩ := hb
      have hdiv : (b.1*p + b.2)/p = b.1 := by
        rw [add_comm, Nat.add_mul_div_right _ _ hp.pos, Nat.div_eq_of_lt hb2r, zero_add]
      have hmod : (b.1*p + b.2)%p = b.2 := by
        rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb2r]
      have : ((b.1*p + b.2)/p, (b.1*p + b.2)%p) = b := by
        rw [hdiv, hmod]
      exact this
    · intro x hx
      show (x:ZMod p)^k = ((x%p:ℕ):ZMod p)^k
      rw [ZMod.natCast_mod]
  have hz : ((p^(r-1):ℕ):ZMod p) = 0 := by
    have he : p^(r-1) = p * p^(r-2) := by rw [← _root_.pow_succ']; congr 1; omega
    rw [he]; push_cast; rw [ZMod.natCast_self]; ring
  rw [hbij, ht, Finset.sum_product]
  have hred : (∑ x ∈ Finset.range (p^(r-1)), ∑ y ∈ Finset.Ico 1 p, (((x,y).2 : ℕ):ZMod p) ^ k)
       = ∑ _x ∈ Finset.range (p^(r-1)), ∑ y ∈ Finset.Ico 1 p, ((y:ℕ):ZMod p) ^ k := rfl
  rw [hred, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hz, zero_mul]

theorem esym_card_sub_two {R} [CommRing R] (f : ℕ → R) (s : Finset ℕ) (hs : 2 ≤ s.card) :
    2 * ∑ T ∈ s.powersetCard (s.card-2), ∏ i ∈ T, f i
      = ∑ i ∈ s, ∑ j ∈ s.erase i, ∏ k ∈ (s.erase i).erase j, f k := by
  set m := s.card - 2 with hm
  have hinner : ∀ i ∈ s, ∑ j ∈ s.erase i, ∏ k ∈ (s.erase i).erase j, f k
      = ∑ T ∈ (s.erase i).powersetCard m, ∏ k ∈ T, f k := by
    intro i hi
    have hcard : (s.erase i).card = s.card - 1 := Finset.card_erase_of_mem hi
    have h1 : 1 ≤ (s.erase i).card := by rw [hcard]; omega
    have hh := esym_card_sub_one f (s.erase i) h1
    rw [hcard, show s.card-1-1 = m by omega] at hh
    exact hh.symm
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_comm' (s := s) (t := fun i => (s.erase i).powersetCard m)
        (t' := s.powersetCard m) (s' := fun T => s \ T)
        (by
          intro i T
          simp only [Finset.mem_powersetCard, Finset.mem_sdiff]
          constructor
          · rintro ⟨hi, hsub, hc⟩
            refine ⟨⟨hi, fun hT => (Finset.mem_erase.mp (hsub hT)).1 rfl⟩,
              hsub.trans (Finset.erase_subset i s), hc⟩
          · rintro ⟨⟨hi, hiT⟩, hTs, hc⟩
            refine ⟨hi, fun x hx => Finset.mem_erase.mpr ⟨fun h => hiT (h ▸ hx), hTs hx⟩, hc⟩)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_powersetCard] at hT
  rw [Finset.sum_const, Finset.card_sdiff_of_subset hT.1, hT.2, show s.card - m = 2 by omega,
      nsmul_eq_mul]
  norm_num

theorem G2 (p r : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hp5 : 5 ≤ p) (hr : r ≥ 2) :
    (p:ℤ) ∣ S2 p (p^r) := by
  rw [show (p:ℤ) = ((p^1:ℕ):ℤ) by rw [Nat.cast_pow, pow_one],
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set L := Lset p (p^r) with hL
  set qb : ℕ → ZMod (p^1) := fun i => ((qfun (p^r) i:ℤ):ZMod (p^1)) with hqb
  set u : ℕ → ZMod (p^1) := fun i => (qb i)⁻¹ with hu
  have hcardL : 2 ≤ L.card := Lcard_ge2 p r hp hp3 hr
  have hPzero : (↑p:ZMod (p^1))^r = 0 := by
    rw [show ((p:ZMod (p^1))^r) = ((p^r:ℕ):ZMod (p^1)) by push_cast; ring]
    exact (ZMod.natCast_eq_zero_iff (p^r) (p^1)).mpr (pow_dvd_pow p (by omega))
  have hqval : ∀ i ∈ L, qb i = -(i:ZMod (p^1))^2 := by
    intro i _; rw [hqb]; simp only [qfun]; push_cast; rw [hPzero]; ring
  have hiunit : ∀ i ∈ L, IsUnit (i:ZMod (p^1)) := by
    intro i hi; rw [hL, mem_Lset] at hi
    exact (ZMod.isUnit_iff_coprime i (p^1)).mpr
      (Nat.Coprime.pow_right 1 ((hp.coprime_iff_not_dvd.mpr hi.2.1).symm))
  have hqbunit : ∀ i ∈ L, IsUnit (qb i) := by
    intro i hi; rw [hqval i hi]; exact ((hiunit i hi).pow 2).neg
  have hinvval : ∀ i ∈ L, u i = -((i:ZMod (p^1))⁻¹)^2 := by
    intro i hi
    show (qb i)⁻¹ = -((i:ZMod (p^1))⁻¹)^2
    rw [hqval i hi]
    apply ZMod.inv_eq_of_mul_eq_one
    rw [neg_mul_neg, ← mul_pow, ZMod.mul_inv_of_unit _ (hiunit i hi), one_pow]
  have hfaul2 : ∑ x ∈ Uset p (p^r), (x:ZMod (p^1))^2 = 0 := by
    apply sumU_sq_zmod p r 1
    exact dvd_trans (pow_dvd_pow (p:ℤ) (by omega)) (faulhaber_dvd_ge5 p r hp hp5 (by omega))
  have hfaul4 : ∑ x ∈ Uset p (p^r), (x:ZMod (p^1))^4 = 0 := by
    rw [pow_one]; exact Usum_pow_zmod p r 4 hp hr
  have hsum1 : ∑ i ∈ L, u i = 0 := by
    rw [Finset.sum_congr rfl hinvval, Finset.sum_neg_distrib, hL,
        invsum_zero_k p r 1 2 hp hp3 (by omega) (by omega) (by decide) hfaul2, neg_zero]
  have hsum2 : ∑ i ∈ L, (u i)^2 = 0 := by
    have hcong : ∀ i ∈ L, (u i)^2 = ((i:ZMod (p^1))⁻¹)^4 := by
      intro i hi; rw [hinvval i hi]; ring
    rw [Finset.sum_congr rfl hcong, hL,
        invsum_zero_k p r 1 4 hp hp3 (by omega) (by omega) (by decide) hfaul4]
  have hb : ∑ i ∈ L, ∑ j ∈ L.erase i, u i * u j
      = (∑ i ∈ L, u i)^2 - ∑ i ∈ L, (u i)^2 := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hae := Finset.add_sum_erase L (fun j => u i * u j) hi
    simp only [] at hae
    rw [← hae]; ring
  have ha : ∀ i, i ∈ L → ∀ j, j ∈ L.erase i →
      ∏ k ∈ (L.erase i).erase j, qb k = (∏ k ∈ L, qb k) * u i * u j := by
    intro i hi j hj
    have e1 := Finset.mul_prod_erase L qb hi
    have e2 := Finset.mul_prod_erase (L.erase i) qb hj
    have key : (∏ k ∈ L, qb k) = qb i * qb j * ∏ k ∈ (L.erase i).erase j, qb k := by
      rw [← e1, ← e2]; ring
    show ∏ k ∈ (L.erase i).erase j, qb k = (∏ k ∈ L, qb k) * (qb i)⁻¹ * (qb j)⁻¹
    rw [key,
        show (qb i * qb j * ∏ k ∈ (L.erase i).erase j, qb k) * (qb i)⁻¹ * (qb j)⁻¹
          = (qb i * (qb i)⁻¹) * (qb j * (qb j)⁻¹) * ∏ k ∈ (L.erase i).erase j, qb k by ring,
        ZMod.mul_inv_of_unit _ (hqbunit i hi),
        ZMod.mul_inv_of_unit _ (hqbunit j (Finset.mem_of_mem_erase hj)), one_mul, one_mul]
  have hstep : ∑ i ∈ L, ∑ j ∈ L.erase i, ∏ k ∈ (L.erase i).erase j, qb k
      = (∏ k ∈ L, qb k) * ∑ i ∈ L, ∑ j ∈ L.erase i, u i * u j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j hj
    rw [ha i hi j hj]; ring
  have hS2cast : ((S2 p (p^r):ℤ):ZMod (p^1)) = ∑ T ∈ L.powersetCard (L.card-2), ∏ i ∈ T, qb i := by
    show ((Esym (qfun (p^r)) L (L.card-2):ℤ):ZMod (p^1)) = _
    unfold Esym
    rw [Int.cast_sum]
    apply Finset.sum_congr rfl
    intro T hT
    rw [Int.cast_prod]
  have h2S2 : (2:ZMod (p^1)) * ((S2 p (p^r):ℤ):ZMod (p^1)) = 0 := by
    rw [hS2cast, esym_card_sub_two qb L hcardL, hstep, hb, hsum1, hsum2]
    ring
  have hunit2 : IsUnit (2:ZMod (p^1)) :=
    (ZMod.isUnit_iff_coprime 2 (p^1)).mpr
      (Nat.Coprime.pow_right 1 ((hp.coprime_iff_not_dvd.mpr (hp_not_dvd_two hp hp3)).symm))
  exact (hunit2.mul_right_eq_zero).mp h2S2

theorem main_thm (p r : ℕ) (hp : p.Prime) (hp3 : p ≥ 3) (hr : r ≥ 2) :
    a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  set M := (p:ℤ)^(3*r+3) with hMdef
  have hpos : 0 < p := hp.pos
  have hpn : p * p^(r-1) = p^r := by rw [← _root_.pow_succ']; congr 1; omega
  -- product identities
  have hid3 := prodid3 p (p^(r-1)) hpos
  rw [hpn] at hid3
  have hid2 := prodid2 p (p^(r-1)) hpos
  rw [hpn] at hid2
  rw [Pistar_eq_Wfun0] at hid3 hid2
  -- cast to ℤ
  have he3 : (Wfun p 0 (p^r):ℤ) * ((3*p^r).choose (p^r):ℤ)
      = ((3*p^(r-1)).choose (p^(r-1)):ℤ) * (Wfun p (2*p^r) (p^r):ℤ) := by exact_mod_cast hid3
  have he2 : (Wfun p 0 (p^r):ℤ) * ((2*p^r).choose (p^r):ℤ)
      = ((2*p^(r-1)).choose (p^(r-1)):ℤ) * (Wfun p (p^r) (p^r):ℤ) := by exact_mod_cast hid2
  -- Z_modEq
  have hZmod := Z_modEq p r hp hp3 hr
  rw [Nat.one_mul] at hZmod
  -- a in cast form
  have haP : a (p^r) = ((3*p^r).choose (p^r):ℤ)^2 - 27 * ((2*p^r).choose (p^r):ℤ) := by
    simp [a, Int.ofNat_eq_natCast]
  have han : a (p^(r-1)) = ((3*p^(r-1)).choose (p^(r-1)):ℤ)^2 - 27 * ((2*p^(r-1)).choose (p^(r-1)):ℤ) := by
    simp [a, Int.ofNat_eq_natCast]
  -- Zeq
  have hZeq : (Wfun p 0 (p^r):ℤ)^2 * (a (p^r) - a (p^(r-1)))
      = ((3*p^(r-1)).choose (p^(r-1)):ℤ)^2
          * ((Wfun p (2*p^r) (p^r):ℤ)^2 - (Wfun p 0 (p^r):ℤ)^2)
        - 27 * (Wfun p 0 (p^r):ℤ) * ((2*p^(r-1)).choose (p^(r-1)):ℤ)
            * ((Wfun p (p^r) (p^r):ℤ) - (Wfun p 0 (p^r):ℤ)) := by
    rw [haP, han]
    linear_combination ((Wfun p 0 (p^r):ℤ) * ((3*p^r).choose (p^r):ℤ)
        + ((3*p^(r-1)).choose (p^(r-1)):ℤ) * (Wfun p (2*p^r) (p^r):ℤ)) * he3
      + (-27 * (Wfun p 0 (p^r):ℤ)) * he2
  -- term divisibility: RHS of Z_modEq divisible by M
  have hRHSdvd : M ∣ (6*(p:ℤ)^(2*r)*(S1 p (p^r))*(Wfun p 0 (p^r):ℤ)
        *(2*((3*p^(r-1)).choose (p^(r-1)):ℤ)^2 - 9*((2*p^(r-1)).choose (p^(r-1)):ℤ))
      + 36*((p:ℤ)^(2*r))^2*((3*p^(r-1)).choose (p^(r-1)):ℤ)^2*(S1 p (p^r))^2
      + 36*((p:ℤ)^(2*r))^2*(S2 p (p^r))*(Wfun p 0 (p^r):ℤ)
        *(2*((3*p^(r-1)).choose (p^(r-1)):ℤ)^2 - 3*((2*p^(r-1)).choose (p^(r-1)):ℤ))) := by
    have hClem := Clemma p r hp hp3 hr
    rcases eq_or_lt_of_le hp3 with h3 | hgt
    · -- p = 3
      subst h3
      set A := ((3*3^(r-1)).choose (3^(r-1)):ℤ) with hA
      set B := ((2*3^(r-1)).choose (3^(r-1)):ℤ) with hB
      set W0 := (Wfun 3 0 (3^r):ℤ) with hW0
      set s1 := S1 3 (3^r) with hs1d
      set s2 := S2 3 (3^r) with hs2d
      set e := (3:ℤ)^(2*r) with hed
      have hs1 : (3:ℤ)^(r-1) ∣ s1 :=
        G1 3 r (r-1) hp hp3 hr (by omega) (sumU_sq_zmod 3 r (r-1) (faulhaber_dvd_3 r (by omega)))
      obtain ⟨c1, hc1⟩ := hs1
      obtain ⟨c2, hc2⟩ := hClem
      have hT1 : M ∣ 6*e*s1*W0*(2*A^2-9*B) := by
        rw [hMdef]
        rw [show (6*e*s1*W0*(2*A^2-9*B):ℤ) = (3:ℤ)^(3*r+3)*(2*c1*W0*c2) by
          rw [hc1, hc2, hed,
            show (3:ℤ)^(3*r+3)=(3:ℤ)^1*(3:ℤ)^(2*r)*(3:ℤ)^(r-1)*(3:ℤ)^3 by
              rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega]
          ring]
        exact Dvd.dvd.mul_right (dvd_refl _) _
      have hT2 : M ∣ 36*e^2*A^2*s1^2 := by
        rw [hMdef]
        rw [show (36*e^2*A^2*s1^2:ℤ) = (3:ℤ)^(6*r-2)*(36*A^2*c1^2) by
          rw [hc1, hed,
            show (3:ℤ)^(6*r-2)=(3:ℤ)^(2*r)*(3:ℤ)^(2*r)*(3:ℤ)^(r-1)*(3:ℤ)^(r-1) by
              rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega]
          ring]
        exact Dvd.dvd.mul_right (pow_dvd_pow (3:ℤ) (by omega)) _
      have hT3 : M ∣ 36*e^2*s2*W0*(2*A^2-3*B) := by
        rw [hMdef]
        rw [show (36*e^2*s2*W0*(2*A^2-3*B):ℤ) = (3:ℤ)^(4*r+2)*(4*s2*W0*(2*A^2-3*B)) by
          rw [hed,
            show (3:ℤ)^(4*r+2)=(3:ℤ)^(2*r)*(3:ℤ)^(2*r)*(3:ℤ)^2 by
              rw [← pow_add, ← pow_add]; congr 1; omega]
          ring]
        exact Dvd.dvd.mul_right (pow_dvd_pow (3:ℤ) (by omega)) _
      exact dvd_add (dvd_add hT1 hT2) hT3
    · -- p ≥ 5
      have hp5 : 5 ≤ p := by
        by_contra h; push_neg at h; interval_cases p
        · exact absurd hp (by decide)
      set A := ((3*p^(r-1)).choose (p^(r-1)):ℤ) with hA
      set B := ((2*p^(r-1)).choose (p^(r-1)):ℤ) with hB
      set W0 := (Wfun p 0 (p^r):ℤ) with hW0
      set s1 := S1 p (p^r) with hs1d
      set s2 := S2 p (p^r) with hs2d
      set e := (p:ℤ)^(2*r) with hed
      have hs1 : (p:ℤ)^r ∣ s1 :=
        G1 p r r hp hp3 hr (le_refl r) (sumU_sq_zmod p r r (faulhaber_dvd_ge5 p r hp hp5 (by omega)))
      obtain ⟨c1, hc1⟩ := hs1
      obtain ⟨c2, hc2⟩ := hClem
      obtain ⟨c3, hc3⟩ := G2 p r hp hp3 hp5 hr
      rw [← hs2d] at hc3
      have hT1 : M ∣ 6*e*s1*W0*(2*A^2-9*B) := by
        rw [hMdef]
        rw [show (6*e*s1*W0*(2*A^2-9*B):ℤ) = (p:ℤ)^(3*r+3)*(6*c1*W0*c2) by
          rw [hc1, hc2, hed,
            show (p:ℤ)^(3*r+3)=(p:ℤ)^(2*r)*(p:ℤ)^r*(p:ℤ)^3 by
              rw [← pow_add, ← pow_add]; congr 1; omega]
          ring]
        exact Dvd.dvd.mul_right (dvd_refl _) _
      have hT2 : M ∣ 36*e^2*A^2*s1^2 := by
        rw [hMdef]
        rw [show (36*e^2*A^2*s1^2:ℤ) = (p:ℤ)^(6*r)*(36*A^2*c1^2) by
          rw [hc1, hed,
            show (p:ℤ)^(6*r)=(p:ℤ)^(2*r)*(p:ℤ)^(2*r)*(p:ℤ)^r*(p:ℤ)^r by
              rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega]
          ring]
        exact Dvd.dvd.mul_right (pow_dvd_pow (p:ℤ) (by omega)) _
      have hT3 : M ∣ 36*e^2*s2*W0*(2*A^2-3*B) := by
        rw [hMdef]
        rw [show (36*e^2*s2*W0*(2*A^2-3*B):ℤ) = (p:ℤ)^(4*r+1)*(36*c3*W0*(2*A^2-3*B)) by
          rw [hc3, hed,
            show (p:ℤ)^(4*r+1)=(p:ℤ)^(2*r)*(p:ℤ)^(2*r)*(p:ℤ)^1 by
              rw [← pow_add, ← pow_add]; congr 1; omega]
          ring]
        exact Dvd.dvd.mul_right (pow_dvd_pow (p:ℤ) (by omega)) _
      exact dvd_add (dvd_add hT1 hT2) hT3
  -- so M ∣ Z
  have hZdvd : M ∣ (((3*p^(r-1)).choose (p^(r-1)):ℤ)^2
          * ((Wfun p (2*p^r) (p^r):ℤ)^2 - (Wfun p 0 (p^r):ℤ)^2)
        - 27 * (Wfun p 0 (p^r):ℤ) * ((2*p^(r-1)).choose (p^(r-1)):ℤ)
            * ((Wfun p (p^r) (p^r):ℤ) - (Wfun p 0 (p^r):ℤ))) := by
    have : _ ≡ 0 [ZMOD M] := hZmod.trans (Int.modEq_zero_iff_dvd.mpr hRHSdvd)
    exact (Int.modEq_zero_iff_dvd).mp this
  -- M ∣ W0^2 * (a P - a n)
  rw [← hZeq] at hZdvd
  -- coprimality
  have hcop : IsCoprime M ((Wfun p 0 (p^r):ℤ)^2) := by
    rw [hMdef]
    exact (coprime_pW p (p^r) hp).pow
  have hfin : M ∣ (a (p^r) - a (p^(r-1))) := hcop.dvd_of_dvd_mul_left hZdvd
  exact Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp hfin)
