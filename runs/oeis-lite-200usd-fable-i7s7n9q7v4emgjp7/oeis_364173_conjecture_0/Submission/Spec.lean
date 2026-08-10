import FormalConjectures.Util.ProblemImports

/--
A364173: The sequence defined by the factorial ratio
$$a(n) = \frac{(9n)! (2n)! (3n/2)!}{(9n/2)! (4n)! (3n)! n!}$$
where fractional factorials $x!$ are defined as $\Gamma(x+1)$.
-/
noncomputable def a (n : ℕ) : ℝ :=
  let n_r : ℝ := n
  (Real.Gamma (9 * n_r + 1) * Real.Gamma (2 * n_r + 1) * Real.Gamma (3 / 2 * n_r + 1)) /
  (Real.Gamma (9 / 2 * n_r + 1) * Real.Gamma (4 * n_r + 1) * Real.Gamma (3 * n_r + 1) * Real.Gamma (n_r + 1))

set_option maxHeartbeats 20000000 in
/--
Conjecture: the supercongruences a(n*p^r) == a(n*p^(r-1)) (mod p^(3*r)) hold for all primes p >= 5 and all positive integers n and r.
Note: This conjecture requires that a(n) is an integer for all n, which is only conjectural.
We assume integrality for the purpose of stating the congruence.
-/
theorem oeis_364173_conjecture_0
    (h_int : ∀ m : ℕ, a m ∈ (Set.range (fun (x : ℤ) => (x : ℝ)))) :
  ∀ (p : ℕ) (hp : Nat.Prime p) (h_p_ge_5 : 5 ≤ p)
    (n r : ℕ) (hn : n > 0) (hr : r > 0),
  (Classical.choose (h_int (n * p ^ r)) : ℤ)
  ≡ (Classical.choose (h_int (n * p ^ (r - 1))) : ℤ)
  [ZMOD ((p : ℤ) ^ (3 * r))] := by
  open Finset in
  open scoped Nat in
  intro p hpp hp5 n r hn hr
  haveI hp : Fact p.Prime := ⟨hpp⟩


  have norm_int_dvd_le {k : ℤ} {n : ℕ} (h : (p:ℤ)^n ∣ k) : ‖(k : ℚ_[p])‖ ≤ (p:ℝ)^(-(n:ℤ)) := by
    exact (Padic.norm_int_le_pow_iff_dvd k n).2 (by exact_mod_cast h)

  have norm_nat_dvd_le {k : ℕ} {n : ℕ} (h : p^n ∣ k) : ‖(k : ℚ_[p])‖ ≤ (p:ℝ)^(-(n:ℤ)) := by
    have : ((k:ℤ) : ℚ_[p]) = (k : ℚ_[p]) := by push_cast; ring
    rw [← this]
    exact norm_int_dvd_le (by exact_mod_cast h)

  have norm_nat_le_one (k : ℕ) : ‖(k : ℚ_[p])‖ ≤ 1 := by
    have : ((k:ℤ) : ℚ_[p]) = (k : ℚ_[p]) := by push_cast; ring
    rw [← this]; exact Padic.norm_int_le_one _

  have nun {u : ℕ} (hu : ¬ p ∣ u) : ‖(u : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hp.out).2 hu

  have nuz {u : ℕ} (hu : ¬ p ∣ u) : (u : ℚ_[p]) ≠ 0 := by
    intro h
    have := nun hu
    rw [h, norm_zero] at this; norm_num at this

  have nsl (s : Finset ℕ) {f : ℕ → ℚ_[p]} {C : ℝ} (hC : 0 ≤ C)
      (h : ∀ i ∈ s, ‖f i‖ ≤ C) : ‖∑ i ∈ s, f i‖ ≤ C := by
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, norm_zero]; exact hC
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine le_trans (Padic.nonarchimedean _ _) (max_le (h a (mem_insert_self a s)) ?_)
      exact ih fun i hi => h i (mem_insert_of_mem hi)

  obtain ⟨pe, pe_def⟩ : ∃ f : ℕ → ℕ → ℝ, f = fun (p k : ℕ) => (p:ℝ)^(-(k:ℤ)) := ⟨_, rfl⟩

  have one_lt_p : (1:ℝ) < (p:ℝ) := by
    exact_mod_cast hp.out.one_lt

  have p_pos : (0:ℝ) < (p:ℝ) := lt_trans one_pos (one_lt_p)

  have pe_pos (k : ℕ) : 0 < pe p k := by
    simp only [pe_def]
    exact zpow_pos (p_pos) _

  have peN (k : ℕ) : 0 ≤ pe p k := (pe_pos k).le

  have pe_mul (a b : ℕ) : pe p a * pe p b = pe p (a + b) := by
    simp only [pe_def]
    rw [← zpow_add₀ (ne_of_gt (p_pos))]
    congr 1
    push_cast
    ring

  have pe_mono {a b : ℕ} (h : a ≤ b) : pe p b ≤ pe p a := by
    simp only [pe_def]
    apply zpow_le_zpow_right₀ (one_lt_p).le
    omega

  have pe_le_one (k : ℕ) : pe p k ≤ 1 := by
    have h := pe_mono (Nat.zero_le k)
    have h0 : pe p 0 = 1 := by
      simp only [pe_def]
      norm_num
    rw [h0] at h
    exact h

  have npp (k : ℕ) : ‖((p^k : ℕ) : ℚ_[p])‖ = pe p k := by
    push_cast
    rw [Padic.norm_p_pow, pe_def]

  /- ### The `Near` predicate: `x` is within `p^(-k)` of `1`. -/

  obtain ⟨Near, Near_def⟩ : ∃ f : ℕ → ℚ_[p] → Prop, f = fun (k : ℕ) (x : ℚ_[p]) => ‖x - 1‖ ≤ pe p k := ⟨_, rfl⟩

  have near_one (k : ℕ) : Near k (1 : ℚ_[p]) := by
    simp only [Near_def]
    rw [sub_self, norm_zero]
    exact peN k

  have Near_norm_le_one {k : ℕ} {x : ℚ_[p]} (h : Near k x) : ‖x‖ ≤ 1 := by
    simp only [Near_def] at h
    have : x = (x - 1) + 1 := by ring
    rw [this]
    refine le_trans (Padic.nonarchimedean _ _) (max_le (le_trans h (pe_le_one k)) norm_one.le)

  have Near_mul {k : ℕ} {x y : ℚ_[p]} (hx : Near k x) (hy : Near k y) : Near k (x * y) := by
    have hy1 : ‖y‖ ≤ 1 := Near_norm_le_one hy
    simp only [Near_def] at hx hy ⊢
    show ‖x * y - 1‖ ≤ pe p k
    have : x * y - 1 = (x - 1) * y + (y - 1) := by ring
    rw [this]
    refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ hy)
    rw [norm_mul]
    calc ‖x - 1‖ * ‖y‖ ≤ pe p k * 1 :=
          mul_le_mul hx hy1 (norm_nonneg _) (peN _)
      _ = pe p k := mul_one _

  have pe_lt_one {k : ℕ} (hk : 1 ≤ k) : pe p k < 1 := by
    refine lt_of_le_of_lt (pe_mono hk) ?_
    simp only [pe_def]
    rw [zpow_neg, inv_lt_one_iff₀]
    right
    calc (1:ℝ) < (p:ℝ) := one_lt_p
      _ = (p:ℝ)^(1:ℤ) := (zpow_one _).symm

  have Near_norm_eq_one {k : ℕ} {x : ℚ_[p]} (hk : 1 ≤ k) (h : Near k x) : ‖x‖ = 1 := by
    simp only [Near_def] at h
    have hlt : ‖x - 1‖ < 1 := lt_of_le_of_lt h (pe_lt_one hk)
    have hx : x = (x - 1) + 1 := by ring
    rw [hx, Padic.add_eq_max_of_ne (by rw [norm_one]; exact ne_of_lt hlt), norm_one]
    exact max_eq_right (le_of_lt hlt)

  have Near_ne_zero {k : ℕ} {x : ℚ_[p]} (hk : 1 ≤ k) (h : Near k x) : x ≠ 0 := by
    intro h0
    have := Near_norm_eq_one hk h
    rw [h0, norm_zero] at this
    norm_num at this

  have Near_inv {k : ℕ} {x : ℚ_[p]} (hk : 1 ≤ k) (h : Near k x) : Near k x⁻¹ := by
    have hx0 : x ≠ 0 := Near_ne_zero hk h
    have hnorm := Near_norm_eq_one hk h
    simp only [Near_def] at h ⊢
    have : x⁻¹ - 1 = -(x - 1) * x⁻¹ := by field_simp; ring
    rw [this, norm_mul, norm_neg, norm_inv, hnorm, inv_one, mul_one]
    exact h

  have Near_pow {k : ℕ} {x : ℚ_[p]} (h : Near k x) (m : ℕ) : Near k (x ^ m) := by
    induction m with
    | zero => rw [pow_zero]; exact near_one k
    | succ m ih => rw [pow_succ]; exact Near_mul ih h

  have Near_prod {k : ℕ} {s : Finset ℕ} {f : ℕ → ℚ_[p]}
      (h : ∀ i ∈ s, Near k (f i)) : Near k (∏ i ∈ s, f i) := by
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty]; exact near_one k
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact Near_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

  have Near_div {k : ℕ} {x y : ℚ_[p]} (hk : 1 ≤ k) (hx : Near k x) (hy : Near k y) :
      Near k (x / y) := by
    rw [div_eq_mul_inv]
    exact Near_mul hx (Near_inv hk hy)

  have Near_of_le {k l : ℕ} {x : ℚ_[p]} (h : Near k x) (hlk : l ≤ k) : Near l x := by
    simp only [Near_def] at h ⊢
    exact le_trans h (pe_mono hlk)

  /- ### Master product expansion lemma -/

  have norm_two_eq_one (hp2 : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
    have : ((2:ℕ) : ℚ_[p]) = (2 : ℚ_[p]) := by norm_num
    rw [← this]
    apply nun
    intro hdvd
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 hdvd
    exact hp2 this

  have norm_div_two (hp2 : p ≠ 2) (x : ℚ_[p]) : ‖x / 2‖ = ‖x‖ := by
    rw [norm_div, norm_two_eq_one hp2, div_one]

  have prod_one_add_expand (hp2 : p ≠ 2) (s : Finset ℕ) (f : ℕ → ℚ_[p]) {ε : ℝ}
      (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hf : ∀ i ∈ s, ‖f i‖ ≤ ε) :
      ‖(∏ i ∈ s, (1 + f i)) -
        (1 + (∑ i ∈ s, f i) + ((∑ i ∈ s, f i)^2 - ∑ i ∈ s, (f i)^2)/2)‖ ≤ ε^3 := by
    classical
    induction s using Finset.induction_on with
    | empty =>
      have hz : (∏ i ∈ (∅:Finset ℕ), (1 + f i)) -
          (1 + (∑ i ∈ (∅:Finset ℕ), f i) + ((∑ i ∈ (∅:Finset ℕ), f i)^2
            - ∑ i ∈ (∅:Finset ℕ), (f i)^2)/2) = 0 := by
        rw [Finset.prod_empty, Finset.sum_empty, Finset.sum_empty]
        ring
      rw [hz, norm_zero]
      exact pow_nonneg hε0 3
    | insert a s ha ih =>
      have hfa : ‖f a‖ ≤ ε := hf a (Finset.mem_insert_self a s)
      have hf' : ∀ i ∈ s, ‖f i‖ ≤ ε := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hA : ‖∑ i ∈ s, f i‖ ≤ ε := nsl s hε0 hf'
      have hB : ‖∑ i ∈ s, (f i)^2‖ ≤ ε^2 := by
        refine nsl s (by positivity) ?_
        intro i hi
        rw [pow_two, norm_mul, ← pow_two]
        exact pow_le_pow_left₀ (norm_nonneg _) (hf' i hi) 2
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
      have key : (1 + f a) * (∏ i ∈ s, (1 + f i)) -
          (1 + (f a + ∑ i ∈ s, f i) +
            ((f a + ∑ i ∈ s, f i)^2 - ((f a)^2 + ∑ i ∈ s, (f i)^2))/2)
          = (1 + f a) * ((∏ i ∈ s, (1 + f i)) -
              (1 + (∑ i ∈ s, f i) + ((∑ i ∈ s, f i)^2 - ∑ i ∈ s, (f i)^2)/2))
            + f a * (((∑ i ∈ s, f i)^2 - ∑ i ∈ s, (f i)^2) / 2) := by
        ring
      rw [key]
      have h1fa : ‖1 + f a‖ ≤ 1 :=
        le_trans (Padic.nonarchimedean _ _) (max_le norm_one.le (le_trans hfa hε1))
      refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ ?_)
      · rw [norm_mul]
        calc ‖1 + f a‖ * ‖_‖ ≤ 1 * ε^3 :=
              mul_le_mul h1fa (ih hf') (norm_nonneg _) (by norm_num)
          _ = ε^3 := one_mul _
      · rw [norm_mul, norm_div_two hp2]
        have hAB : ‖(∑ i ∈ s, f i)^2 - ∑ i ∈ s, (f i)^2‖ ≤ ε^2 := by
          refine le_trans (by rw [sub_eq_add_neg]; exact Padic.nonarchimedean _ _) (max_le ?_ ?_)
          · rw [pow_two, norm_mul, ← pow_two]
            exact pow_le_pow_left₀ (norm_nonneg _) hA 2
          · rw [norm_neg]; exact hB
        calc ‖f a‖ * ‖(∑ i ∈ s, f i)^2 - ∑ i ∈ s, (f i)^2‖ ≤ ε * ε^2 :=
              mul_le_mul hfa hAB (norm_nonneg _) hε0
          _ = ε^3 := by ring

  have prod_one_add_near (hp2 : p ≠ 2) (s : Finset ℕ) (f : ℕ → ℚ_[p]) {ε : ℝ}
      (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hf : ∀ i ∈ s, ‖f i‖ ≤ ε) {η : ℝ} (_hη : η ≤ 1)
      (h1 : ‖∑ i ∈ s, f i‖ ≤ η) (h2 : ‖∑ i ∈ s, (f i)^2‖ ≤ η) (h3 : ε^3 ≤ η) :
      ‖(∏ i ∈ s, (1 + f i)) - 1‖ ≤ η := by
    have hA : ‖∑ i ∈ s, f i‖ ≤ ε := nsl s hε0 hf
    have expand := prod_one_add_expand hp2 s f hε0 hε1 hf
    have step : (∏ i ∈ s, (1 + f i)) - 1 =
        ((∏ i ∈ s, (1 + f i)) -
          (1 + (∑ i ∈ s, f i) + ((∑ i ∈ s, f i)^2 - ∑ i ∈ s, (f i)^2)/2))
        + ((∑ i ∈ s, f i) + ((∑ i ∈ s, f i)^2 - ∑ i ∈ s, (f i)^2)/2) := by ring
    rw [step]
    refine le_trans (Padic.nonarchimedean _ _) (max_le (le_trans expand h3) ?_)
    refine le_trans (Padic.nonarchimedean _ _) (max_le h1 ?_)
    rw [norm_div_two hp2]
    refine le_trans (by rw [sub_eq_add_neg]; exact Padic.nonarchimedean _ _) (max_le ?_ ?_)
    · rw [pow_two, norm_mul]
      calc ‖∑ i ∈ s, f i‖ * ‖∑ i ∈ s, f i‖ ≤ η * 1 :=
            mul_le_mul h1 (le_trans hA hε1) (norm_nonneg _) (le_trans (norm_nonneg _) h1)
        _ = η := mul_one _
    · rw [norm_neg]; exact h2




  obtain ⟨US, US_def⟩ : ∃ f : ℕ → ℕ → Finset ℕ, f = fun (p t : ℕ) => (Finset.Ioc 0 (p^t)).filter (fun u => ¬ p ∣ u) := ⟨_, rfl⟩

  obtain ⟨HS, HS_def⟩ : ∃ f : ℕ → ℕ → Finset ℕ, f = fun (p t : ℕ) => (Finset.Ioc 0 (p^t/2)).filter (fun u => ¬ p ∣ u) := ⟨_, rfl⟩

  obtain ⟨WSet, WSet_def⟩ : ∃ f : ℕ → ℕ → Finset ℕ, f = fun (p t : ℕ) => (Finset.Ioc (p^t/2) (p^t/2 + p^t)).filter (fun u => ¬ p ∣ u) := ⟨_, rfl⟩

  obtain ⟨OSet, OSet_def⟩ : ∃ f : ℕ → ℕ → Finset ℕ, f = fun (p t : ℕ) => (Finset.Ioc 0 (2*p^t)).filter (fun u => ¬ p ∣ u ∧ ¬ 2 ∣ u) := ⟨_, rfl⟩

  have mUS {t u : ℕ} : u ∈ US p t ↔ (0 < u ∧ u ≤ p^t) ∧ ¬ p ∣ u := by
    simp [US_def, Finset.mem_filter, Finset.mem_Ioc, and_assoc]

  have mHS {t u : ℕ} : u ∈ HS p t ↔ (0 < u ∧ u ≤ p^t/2) ∧ ¬ p ∣ u := by
    simp [HS_def, Finset.mem_filter, Finset.mem_Ioc, and_assoc]

  have mem_WSet {t u : ℕ} : u ∈ WSet p t ↔ (p^t/2 < u ∧ u ≤ p^t/2 + p^t) ∧ ¬ p ∣ u := by
    simp [WSet_def, Finset.mem_filter, Finset.mem_Ioc, and_assoc]

  have mem_OSet {t u : ℕ} : u ∈ OSet p t ↔ (0 < u ∧ u ≤ 2*p^t) ∧ (¬ p ∣ u ∧ ¬ 2 ∣ u) := by
    simp [OSet_def, Finset.mem_filter, Finset.mem_Ioc, and_assoc]



  have P_odd (hp2 : p ≠ 2) (t : ℕ) : ¬ 2 ∣ p^t := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).1 (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h)
    exact hp2 this.symm

  have thA (hp2 : p ≠ 2) (t : ℕ) : 2 * (p^t/2) + 1 = p^t := by
    have h1 := Nat.div_add_mod (p^t) 2
    have h2 : p^t % 2 = 1 := Nat.two_dvd_ne_zero.mp (P_odd hp2 t)
    omega

  have p_dvd_P (t : ℕ) (ht : 1 ≤ t) : p ∣ p^t := dvd_pow_self p (by omega)


  have dvA {a b : ℕ} (h : p ∣ a + b) (hb : p ∣ b) : p ∣ a :=
    (Nat.dvd_add_iff_left hb).mpr h

  have not_dvd_sub {P w : ℕ} (hP : p ∣ P) (hw : ¬ p ∣ w) (hle : P ≤ w) : ¬ p ∣ (w - P) := by
    intro h
    exact hw (by
      have : w - P + P = w := Nat.sub_add_cancel hle
      rw [← this]
      exact Nat.dvd_add h hP)

  have norm_three (hp5 : 5 ≤ p) : ‖(3 : ℚ_[p])‖ = 1 := by
    have : ((3:ℕ) : ℚ_[p]) = (3 : ℚ_[p]) := by norm_num
    rw [← this]
    apply nun
    intro hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

  have norm_four (hp5 : 5 ≤ p) : ‖(4 : ℚ_[p])‖ = 1 := by
    have : ((4:ℕ) : ℚ_[p]) = (4 : ℚ_[p]) := by norm_num
    rw [← this]
    apply nun
    intro hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega

  have pn2 (hp5 : 5 ≤ p) : p ≠ 2 := by omega

  have sumU2_bound (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      ‖∑ u ∈ US p t, ((u:ℚ_[p])^2)⁻¹‖ ≤ pe p t := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hPnorm : ‖((p^t : ℕ) : ℚ_[p])‖ ≤ pe p t := le_of_eq (npp t)
    have h4 : (4:ℚ_[p]) ≠ 0 := by norm_num
    set σ : ℕ → ℕ := fun u => if 2*u ≤ p^t then 2*u else 2*u - p^t with hσ
    set τ : ℕ → ℕ := fun w => if 2 ∣ w then w/2 else (w + p^t)/2 with hτ
    have not_dvd_two_mul : ∀ u : ℕ, ¬ p ∣ u → ¬ p ∣ 2*u := by
      intro u hu hdvd
      rcases (Nat.Prime.dvd_mul hp.out).1 hdvd with h | h
      · have := Nat.le_of_dvd (by norm_num) h; omega
      · exact hu h
    have hσ_mem : ∀ u ∈ US p t, σ u ∈ US p t := by
      intro u hu
      rw [mUS] at hu ⊢
      obtain ⟨⟨hu0, huP⟩, hud⟩ := hu
      simp only [hσ]
      by_cases hc : 2*u ≤ p^t
      · rw [if_pos hc]
        exact ⟨⟨by omega, hc⟩, not_dvd_two_mul u hud⟩
      · rw [if_neg hc]
        refine ⟨by omega, not_dvd_sub hpP (not_dvd_two_mul u hud) (by omega)⟩
    have hτ_mem : ∀ w ∈ US p t, τ w ∈ US p t := by
      intro w hw
      rw [mUS] at hw ⊢
      obtain ⟨⟨hw0, hwP⟩, hwd⟩ := hw
      simp only [hτ]
      by_cases hc : 2 ∣ w
      · rw [if_pos hc]
        refine ⟨by omega, ?_⟩
        intro hd
        exact hwd (dvd_trans hd (Nat.div_dvd_of_dvd hc))
      · rw [if_neg hc]
        refine ⟨by omega, ?_⟩
        intro hd
        have h2 : 2 ∣ (w + p^t) := by omega
        have : p ∣ w + p^t := dvd_trans hd (Nat.div_dvd_of_dvd h2)
        exact hwd (dvA this hpP)
    have hτσ : ∀ u ∈ US p t, τ (σ u) = u := by
      intro u hu
      rw [mUS] at hu
      obtain ⟨⟨hu0, huP⟩, hud⟩ := hu
      simp only [hσ, hτ]
      by_cases hc : 2*u ≤ p^t
      · rw [if_pos hc, if_pos (Dvd.intro u rfl)]
        omega
      · rw [if_neg hc, if_neg (by omega : ¬ 2 ∣ (2*u - p^t))]
        omega
    have hστ : ∀ w ∈ US p t, σ (τ w) = w := by
      intro w hw
      rw [mUS] at hw
      obtain ⟨⟨hw0, hwP⟩, hwd⟩ := hw
      simp only [hσ, hτ]
      by_cases hc : 2 ∣ w
      · rw [if_pos hc]
        have h2 : 2 * (w/2) = w := Nat.mul_div_cancel' hc
        rw [h2, if_pos hwP]
      · rw [if_neg hc]
        have h2 : 2 * ((w + p^t)/2) = w + p^t := Nat.mul_div_cancel' (by omega)
        rw [h2, if_neg (by omega)]
        omega
    have reindex : ∑ u ∈ US p t, ((u:ℚ_[p])^2)⁻¹ = ∑ u ∈ US p t, (((σ u : ℕ):ℚ_[p])^2)⁻¹ := by
      refine Finset.sum_nbij' τ σ hτ_mem hσ_mem hστ hτσ ?_
      intro w hw
      rw [hστ w hw]
    have per_term : ∀ u ∈ US p t,
        ‖(((σ u : ℕ):ℚ_[p])^2)⁻¹ - (4:ℚ_[p])⁻¹ * ((u:ℚ_[p])^2)⁻¹‖ ≤ pe p t := by
      intro u hu
      rw [mUS] at hu
      obtain ⟨⟨hu0, huP⟩, hud⟩ := hu
      have hu_ne : ((u:ℚ_[p])) ≠ 0 := nuz hud
      simp only [hσ]
      by_cases hc : 2*u ≤ p^t
      · rw [if_pos hc]
        have : (((2*u : ℕ):ℚ_[p])^2)⁻¹ = (4:ℚ_[p])⁻¹ * ((u:ℚ_[p])^2)⁻¹ := by
          push_cast
          rw [mul_pow, ← mul_inv]
          norm_num
        rw [this, sub_self, norm_zero]
        exact peN t
      · rw [if_neg hc]
        have hPle : p^t ≤ 2*u := by omega
        have hcast : (((2*u - p^t : ℕ)):ℚ_[p]) = 2*(u:ℚ_[p]) - ((p^t:ℕ):ℚ_[p]) := by
          rw [Nat.cast_sub hPle]
          push_cast
          ring
        have hw_unit : ¬ p ∣ (2*u - p^t) := not_dvd_sub hpP (not_dvd_two_mul u hud) hPle
        have hw_ne : (2*(u:ℚ_[p]) - ((p^t:ℕ):ℚ_[p])) ≠ 0 := by
          rw [← hcast]
          exact nuz hw_unit
        have hw_norm : ‖(2*(u:ℚ_[p]) - ((p^t:ℕ):ℚ_[p]))‖ = 1 := by
          rw [← hcast]
          exact nun hw_unit
        have identity : (((2*u - p^t : ℕ):ℚ_[p])^2)⁻¹ - (4:ℚ_[p])⁻¹ * ((u:ℚ_[p])^2)⁻¹
            = ((p^t:ℕ):ℚ_[p]) * (4*(u:ℚ_[p]) - ((p^t:ℕ):ℚ_[p]))
              / (4 * (u:ℚ_[p])^2 * (2*(u:ℚ_[p]) - ((p^t:ℕ):ℚ_[p]))^2) := by
          rw [hcast]
          field_simp
          ring
        rw [identity, norm_div, norm_mul]
        have h1 : ‖(4*(u:ℚ_[p]) - ((p^t:ℕ):ℚ_[p]))‖ ≤ 1 := by
          have : (4*(u:ℚ_[p]) - ((p^t:ℕ):ℚ_[p])) = (((4*u - p^t : ℤ)):ℚ_[p]) := by push_cast; ring
          rw [this]
          exact Padic.norm_int_le_one _
        have h2 : ‖4 * (u:ℚ_[p])^2 * (2*(u:ℚ_[p]) - ((p^t:ℕ):ℚ_[p]))^2‖ = 1 := by
          rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_four hp5, nun hud, hw_norm]
          norm_num
        rw [h2, div_one]
        calc ‖((p^t:ℕ):ℚ_[p])‖ * ‖4*(u:ℚ_[p]) - ((p^t:ℕ):ℚ_[p])‖ ≤ pe p t * 1 :=
              mul_le_mul hPnorm h1 (norm_nonneg _) (peN _)
          _ = pe p t := mul_one _
    set T := ∑ u ∈ US p t, ((u:ℚ_[p])^2)⁻¹ with hT
    have hdiff : ‖T - (4:ℚ_[p])⁻¹ * T‖ ≤ pe p t := by
      calc ‖T - (4:ℚ_[p])⁻¹ * T‖
          = ‖∑ u ∈ US p t, ((((σ u : ℕ)):ℚ_[p])^2)⁻¹ - (4:ℚ_[p])⁻¹ * ∑ u ∈ US p t, ((u:ℚ_[p])^2)⁻¹‖ := by
            rw [← hT, ← reindex]
        _ = ‖∑ u ∈ US p t, (((((σ u : ℕ)):ℚ_[p])^2)⁻¹ - (4:ℚ_[p])⁻¹ * ((u:ℚ_[p])^2)⁻¹)‖ := by
            rw [Finset.mul_sum, Finset.sum_sub_distrib]
        _ ≤ pe p t := nsl _ (peN t) per_term
    have hfactor : (3:ℚ_[p]) * T = 4 * (T - (4:ℚ_[p])⁻¹ * T) := by
      field_simp
      ring
    have hnorm3 : ‖T‖ = ‖(3:ℚ_[p]) * T‖ := by rw [norm_mul, norm_three hp5, one_mul]
    rw [hnorm3, hfactor, norm_mul, norm_four hp5, one_mul]
    exact hdiff

  have norm_inv_unit_le_one {u : ℕ} (hu : ¬ p ∣ u) : ‖((u:ℚ_[p]))⁻¹‖ ≤ 1 := by
    rw [norm_inv, nun hu]
    norm_num

  have sumU1_bound (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      ‖∑ u ∈ US p t, ((u:ℚ_[p]))⁻¹‖ ≤ pe p (2*t) := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hPnorm : ‖((p^t : ℕ) : ℚ_[p])‖ ≤ pe p t := le_of_eq (npp t)
    have hmem_lt : ∀ u ∈ US p t, u < p^t := by
      intro u hu
      rw [mUS] at hu
      have hne : u ≠ p^t := fun he => hu.2 (he ▸ hpP)
      have := hu.1.2
      omega
    have hρ_mem : ∀ u ∈ US p t, p^t - u ∈ US p t := by
      intro u hu
      have hlt := hmem_lt u hu
      rw [mUS] at hu ⊢
      obtain ⟨⟨hu0, huP⟩, hud⟩ := hu
      refine ⟨by omega, ?_⟩
      intro hdvd
      apply hud
      apply dvA (b := p^t - u)
      · have : u + (p^t - u) = p^t := by omega
        rw [this]; exact hpP
      · exact hdvd
    have hρρ : ∀ u ∈ US p t, p^t - (p^t - u) = u := by
      intro u hu
      have := hmem_lt u hu
      omega
    have reindex : ∑ u ∈ US p t, ((u:ℚ_[p]))⁻¹
        = ∑ u ∈ US p t, (((p^t - u : ℕ):ℚ_[p]))⁻¹ := by
      refine Finset.sum_nbij' (fun u => p^t - u) (fun u => p^t - u) hρ_mem hρ_mem hρρ hρρ ?_
      intro u hu
      rw [hρρ u hu]
    have key : (2:ℚ_[p]) * (∑ u ∈ US p t, ((u:ℚ_[p]))⁻¹)
        = -((p^t:ℕ):ℚ_[p]) * (∑ u ∈ US p t, ((u:ℚ_[p])^2)⁻¹)
          + ((p^t:ℕ):ℚ_[p])^2 * (∑ u ∈ US p t, ((u:ℚ_[p])^2 * (((p^t:ℕ):ℚ_[p]) - u))⁻¹) := by
      rw [two_mul]
      nth_rewrite 2 [reindex]
      rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      have hlt := hmem_lt u hu
      rw [mUS] at hu
      obtain ⟨⟨hu0, huP⟩, hud⟩ := hu
      have hu_ne : ((u:ℚ_[p])) ≠ 0 := nuz hud
      have hcast : (((p^t - u : ℕ)):ℚ_[p]) = ((p^t:ℕ):ℚ_[p]) - u := by
        rw [Nat.cast_sub (by omega)]
      have hres_unit : ¬ p ∣ (p^t - u) := by
        intro hdvd
        apply hud
        apply dvA (b := p^t - u)
        · have : u + (p^t - u) = p^t := by omega
          rw [this]; exact hpP
        · exact hdvd
      have hres_ne : ((p^t:ℕ):ℚ_[p]) - u ≠ 0 := by
        rw [← hcast]; exact nuz hres_unit
      rw [hcast]
      field_simp
      ring
    have hVle : ‖∑ u ∈ US p t, ((u:ℚ_[p])^2 * (((p^t:ℕ):ℚ_[p]) - u))⁻¹‖ ≤ 1 := by
      refine nsl _ (by norm_num) ?_
      intro u hu
      have hlt := hmem_lt u hu
      rw [mUS] at hu
      obtain ⟨⟨hu0, huP⟩, hud⟩ := hu
      have hres_unit : ¬ p ∣ (p^t - u) := by
        intro hdvd
        apply hud
        apply dvA (b := p^t - u)
        · have : u + (p^t - u) = p^t := by omega
          rw [this]; exact hpP
        · exact hdvd
      have hcast : (((p^t - u : ℕ)):ℚ_[p]) = ((p^t:ℕ):ℚ_[p]) - u := by
        rw [Nat.cast_sub (by omega)]
      rw [norm_inv, norm_mul, norm_pow, nun hud, ← hcast, nun hres_unit]
      norm_num
    have hT2le : ‖∑ u ∈ US p t, ((u:ℚ_[p])^2)⁻¹‖ ≤ pe p t := sumU2_bound hp5 ht
    have h2 : ‖(2:ℚ_[p])‖ = 1 := norm_two_eq_one hp2
    have hkey : ‖∑ u ∈ US p t, ((u:ℚ_[p]))⁻¹‖
        = ‖(2:ℚ_[p]) * (∑ u ∈ US p t, ((u:ℚ_[p]))⁻¹)‖ := by rw [norm_mul, h2, one_mul]
    rw [hkey, key]
    refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ ?_)
    · rw [norm_mul, norm_neg]
      calc ‖((p^t:ℕ):ℚ_[p])‖ * ‖∑ u ∈ US p t, ((u:ℚ_[p])^2)⁻¹‖ ≤ pe p t * pe p t :=
            mul_le_mul hPnorm hT2le (norm_nonneg _) (peN _)
        _ = pe p (2*t) := by rw [pe_mul, two_mul]
    · rw [norm_mul, norm_pow]
      calc ‖((p^t:ℕ):ℚ_[p])‖^2 * ‖∑ u ∈ US p t, ((u:ℚ_[p])^2 * (((p^t:ℕ):ℚ_[p]) - u))⁻¹‖
          ≤ (pe p t)^2 * 1 := by
            apply mul_le_mul _ hVle (norm_nonneg _) (by positivity)
            exact pow_le_pow_left₀ (norm_nonneg _) hPnorm 2
        _ = pe p (2*t) := by rw [mul_one, pow_two, pe_mul, two_mul]

  have UfH {t : ℕ} :
      (US p t).filter (fun u => u ≤ p^t/2) = HS p t := by
    ext u
    simp only [Finset.mem_filter, mUS, mHS]
    constructor
    · rintro ⟨⟨⟨h0, hP⟩, hd⟩, hh⟩
      exact ⟨⟨h0, hh⟩, hd⟩
    · rintro ⟨⟨h0, hh⟩, hd⟩
      have : p^t/2 ≤ p^t := Nat.div_le_self _ _
      exact ⟨⟨⟨h0, by omega⟩, hd⟩, hh⟩

  have sum_upper_eq_sum_HSet (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) (f : ℕ → ℚ_[p]) :
      ∑ u ∈ (US p t).filter (fun u => ¬ u ≤ p^t/2), f u
        = ∑ d ∈ HS p t, f (p^t - d) := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    refine Finset.sum_nbij' (fun u => p^t - u) (fun d => p^t - d) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      dsimp only
      simp only [Finset.mem_filter, mUS] at hu
      obtain ⟨⟨⟨h0, hP⟩, hd⟩, hh⟩ := hu
      have hlt : u < p^t := by
        have hne : u ≠ p^t := fun he => hd (he ▸ hpP)
        omega
      rw [mHS]
      refine ⟨by omega, ?_⟩
      intro hdvd
      apply hd
      apply dvA (b := p^t - u)
      · have : u + (p^t - u) = p^t := by omega
        rw [this]; exact hpP
      · exact hdvd
    · intro d hd
      dsimp only
      rw [mHS] at hd
      obtain ⟨⟨h0, hh⟩, hdd⟩ := hd
      simp only [Finset.mem_filter, mUS]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      intro hdvd
      apply hdd
      apply dvA (b := p^t - d)
      · have : d + (p^t - d) = p^t := by omega
        rw [this]; exact hpP
      · exact hdvd
    · intro u hu
      dsimp only
      simp only [Finset.mem_filter, mUS] at hu
      omega
    · intro d hd
      dsimp only
      rw [mHS] at hd
      have : p^t/2 ≤ p^t := Nat.div_le_self _ _
      omega
    · intro u hu
      dsimp only
      congr 1
      simp only [Finset.mem_filter, mUS] at hu
      omega

  have sumH2_bound (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      ‖∑ d ∈ HS p t, ((d:ℚ_[p])^2)⁻¹‖ ≤ pe p t := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    have hPnorm : ‖((p^t : ℕ) : ℚ_[p])‖ ≤ pe p t := le_of_eq (npp t)
    have hsplit := Finset.sum_filter_add_sum_filter_not (US p t) (fun u => u ≤ p^t/2)
        (fun u => ((u:ℚ_[p])^2)⁻¹)
    rw [UfH, sum_upper_eq_sum_HSet hp5 ht] at hsplit
    have hrefl : ∑ d ∈ HS p t, (((p^t - d : ℕ):ℚ_[p])^2)⁻¹
        = ∑ d ∈ HS p t, (((d:ℚ_[p])^2)⁻¹
            + ((p^t:ℕ):ℚ_[p]) * ((2*(d:ℚ_[p]) - ((p^t:ℕ):ℚ_[p])) * (((d:ℚ_[p])^2 * (((p^t:ℕ):ℚ_[p]) - d)^2)⁻¹))) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [mHS] at hd
      obtain ⟨⟨h0, hh⟩, hdd⟩ := hd
      have hlt : d < p^t := by omega
      have hd_ne : ((d:ℚ_[p])) ≠ 0 := nuz hdd
      have hres_unit : ¬ p ∣ (p^t - d) := by
        intro hdvd
        apply hdd
        apply dvA (b := p^t - d)
        · have : d + (p^t - d) = p^t := by omega
          rw [this]; exact hpP
        · exact hdvd
      have hcast : (((p^t - d : ℕ)):ℚ_[p]) = ((p^t:ℕ):ℚ_[p]) - d := by
        rw [Nat.cast_sub (by omega)]
      have hres_ne : ((p^t:ℕ):ℚ_[p]) - d ≠ 0 := by
        rw [← hcast]; exact nuz hres_unit
      rw [hcast]
      field_simp
      ring
    rw [hrefl, Finset.sum_add_distrib] at hsplit
    have herr : ‖∑ d ∈ HS p t, ((p^t:ℕ):ℚ_[p]) * ((2*(d:ℚ_[p]) - ((p^t:ℕ):ℚ_[p])) * (((d:ℚ_[p])^2 * (((p^t:ℕ):ℚ_[p]) - d)^2)⁻¹))‖ ≤ pe p t := by
      refine nsl _ (peN t) ?_
      intro d hd
      rw [mHS] at hd
      obtain ⟨⟨h0, hh⟩, hdd⟩ := hd
      have hlt : d < p^t := by omega
      have hres_unit : ¬ p ∣ (p^t - d) := by
        intro hdvd
        apply hdd
        apply dvA (b := p^t - d)
        · have : d + (p^t - d) = p^t := by omega
          rw [this]; exact hpP
        · exact hdvd
      have hcast : (((p^t - d : ℕ)):ℚ_[p]) = ((p^t:ℕ):ℚ_[p]) - d := by
        rw [Nat.cast_sub (by omega)]
      rw [norm_mul, norm_mul]
      have h1 : ‖2*(d:ℚ_[p]) - ((p^t:ℕ):ℚ_[p])‖ ≤ 1 := by
        have : 2*(d:ℚ_[p]) - ((p^t:ℕ):ℚ_[p]) = (((2*d - p^t : ℤ)):ℚ_[p]) := by push_cast; ring
        rw [this]; exact Padic.norm_int_le_one _
      have h2 : ‖(((d:ℚ_[p])^2 * (((p^t:ℕ):ℚ_[p]) - d)^2)⁻¹)‖ ≤ 1 := by
        rw [norm_inv, norm_mul, norm_pow, norm_pow, nun hdd, ← hcast,
          nun hres_unit]
        norm_num
      calc ‖((p^t:ℕ):ℚ_[p])‖ * (‖2*(d:ℚ_[p]) - ((p^t:ℕ):ℚ_[p])‖ * ‖(((d:ℚ_[p])^2 * (((p^t:ℕ):ℚ_[p]) - d)^2)⁻¹)‖)
          ≤ pe p t * (1 * 1) := by
            apply mul_le_mul hPnorm _ (by positivity) (peN t)
            exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
        _ = pe p t := by ring
    have hT2le : ‖∑ u ∈ US p t, ((u:ℚ_[p])^2)⁻¹‖ ≤ pe p t := sumU2_bound hp5 ht
    have h2n : ‖(2:ℚ_[p])‖ = 1 := norm_two_eq_one hp2
    have key : (2:ℚ_[p]) * (∑ d ∈ HS p t, ((d:ℚ_[p])^2)⁻¹)
        = (∑ u ∈ US p t, ((u:ℚ_[p])^2)⁻¹)
          - ∑ d ∈ HS p t, ((p^t:ℕ):ℚ_[p]) * ((2*(d:ℚ_[p]) - ((p^t:ℕ):ℚ_[p])) * (((d:ℚ_[p])^2 * (((p^t:ℕ):ℚ_[p]) - d)^2)⁻¹)) := by
      rw [← hsplit]; ring
    have hnorm : ‖∑ d ∈ HS p t, ((d:ℚ_[p])^2)⁻¹‖
        = ‖(2:ℚ_[p]) * (∑ d ∈ HS p t, ((d:ℚ_[p])^2)⁻¹)‖ := by rw [norm_mul, h2n, one_mul]
    rw [hnorm, key]
    refine le_trans (by rw [sub_eq_add_neg]; exact Padic.nonarchimedean _ _) (max_le hT2le ?_)
    rw [norm_neg]
    exact herr

  have sum_WSet_split (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) (f : ℕ → ℚ_[p]) :
      ∑ w ∈ WSet p t, f w
        = (∑ d ∈ HS p t, (f (d + p^t) - f d)) + ∑ u ∈ US p t, f u := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    have transfer : ∑ w ∈ WSet p t, f w
        = ∑ u ∈ US p t, f (if u ≤ p^t/2 then u + p^t else u) := by
      refine Finset.sum_nbij' (fun w => if p^t < w then w - p^t else w)
        (fun u => if u ≤ p^t/2 then u + p^t else u) ?_ ?_ ?_ ?_ ?_
      · intro w hw
        dsimp only
        rw [mem_WSet] at hw
        obtain ⟨⟨h1, h2⟩, hd⟩ := hw
        by_cases hc : p^t < w
        · rw [if_pos hc]
          rw [mUS]
          exact ⟨by omega, not_dvd_sub hpP hd (by omega)⟩
        · rw [if_neg hc]
          rw [mUS]
          exact ⟨by omega, hd⟩
      · intro u hu
        dsimp only
        rw [mUS] at hu
        obtain ⟨⟨h1, h2⟩, hd⟩ := hu
        by_cases hc : u ≤ p^t/2
        · rw [if_pos hc, mem_WSet]
          refine ⟨by omega, ?_⟩
          intro hdvd
          exact hd (dvA hdvd hpP)
        · rw [if_neg hc, mem_WSet]
          exact ⟨by omega, hd⟩
      · intro w hw
        dsimp only
        rw [mem_WSet] at hw
        obtain ⟨⟨h1, h2⟩, hd⟩ := hw
        by_cases hc : p^t < w
        · rw [if_pos hc, if_pos (by omega)]
          omega
        · rw [if_neg hc, if_neg (by omega)]
      · intro u hu
        dsimp only
        rw [mUS] at hu
        obtain ⟨⟨h1, h2⟩, hd⟩ := hu
        by_cases hc : u ≤ p^t/2
        · rw [if_pos hc, if_pos (by omega)]
          omega
        · rw [if_neg hc, if_neg (by omega)]
      · intro w hw
        dsimp only
        rw [mem_WSet] at hw
        obtain ⟨⟨h1, h2⟩, hd⟩ := hw
        by_cases hc : p^t < w
        · rw [if_pos hc, if_pos (by omega)]
          congr 1
          omega
        · rw [if_neg hc, if_neg (by omega)]
    rw [transfer]
    have step : ∀ u ∈ US p t, f (if u ≤ p^t/2 then u + p^t else u)
        = (if u ≤ p^t/2 then f (u + p^t) - f u else 0) + f u := by
      intro u hu
      by_cases hc : u ≤ p^t/2
      · rw [if_pos hc, if_pos hc]; ring
      · rw [if_neg hc, if_neg hc]; ring
    rw [Finset.sum_congr rfl step, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter, UfH]

  have sum_OSet_split (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) (f : ℕ → ℚ_[p]) :
      ∑ y ∈ OSet p t, f y
        = (∑ d ∈ (US p t).filter (fun u => 2 ∣ u), (f (d + p^t) - f d)) + ∑ u ∈ US p t, f u := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    have transfer : ∑ y ∈ OSet p t, f y
        = ∑ u ∈ US p t, f (if 2 ∣ u then u + p^t else u) := by
      refine Finset.sum_nbij' (fun y => if p^t < y then y - p^t else y)
        (fun u => if 2 ∣ u then u + p^t else u) ?_ ?_ ?_ ?_ ?_
      · intro y hy
        dsimp only
        rw [mem_OSet] at hy
        obtain ⟨⟨h1, h2⟩, hd, hodd⟩ := hy
        by_cases hc : p^t < y
        · rw [if_pos hc, mUS]
          exact ⟨by omega, not_dvd_sub hpP hd (by omega)⟩
        · rw [if_neg hc, mUS]
          exact ⟨by omega, hd⟩
      · intro u hu
        dsimp only
        rw [mUS] at hu
        obtain ⟨⟨h1, h2⟩, hd⟩ := hu
        by_cases hc : 2 ∣ u
        · rw [if_pos hc, mem_OSet]
          refine ⟨by omega, ?_, by omega⟩
          intro hdvd
          exact hd (dvA hdvd hpP)
        · rw [if_neg hc, mem_OSet]
          exact ⟨by omega, hd, hc⟩
      · intro y hy
        dsimp only
        rw [mem_OSet] at hy
        obtain ⟨⟨h1, h2⟩, hd, hodd⟩ := hy
        by_cases hc : p^t < y
        · rw [if_pos hc, if_pos (by omega)]
          omega
        · rw [if_neg hc, if_neg (by omega)]
      · intro u hu
        dsimp only
        rw [mUS] at hu
        obtain ⟨⟨h1, h2⟩, hd⟩ := hu
        by_cases hc : 2 ∣ u
        · rw [if_pos hc, if_pos (by omega)]
          omega
        · rw [if_neg hc, if_neg (by omega)]
      · intro y hy
        dsimp only
        rw [mem_OSet] at hy
        obtain ⟨⟨h1, h2⟩, hd, hodd⟩ := hy
        by_cases hc : p^t < y
        · rw [if_pos hc, if_pos (by omega)]
          congr 1
          omega
        · rw [if_neg hc, if_neg (by omega)]
    rw [transfer]
    have step : ∀ u ∈ US p t, f (if 2 ∣ u then u + p^t else u)
        = (if 2 ∣ u then f (u + p^t) - f u else 0) + f u := by
      intro u hu
      by_cases hc : 2 ∣ u
      · rw [if_pos hc, if_pos hc]; ring
      · rw [if_neg hc, if_neg hc]; ring
    rw [Finset.sum_congr rfl step, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter]

  have corr1_bound {t : ℕ} (ht : 1 ≤ t) (V : Finset ℕ) (hV : ∀ v ∈ V, ¬ p ∣ v)
      (h2 : ‖∑ v ∈ V, ((v:ℚ_[p])^2)⁻¹‖ ≤ pe p t) :
      ‖∑ v ∈ V, ((((v + p^t : ℕ)):ℚ_[p])⁻¹ - ((v:ℚ_[p]))⁻¹)‖ ≤ pe p (2*t) := by
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hPnorm : ‖((p^t : ℕ) : ℚ_[p])‖ ≤ pe p t := le_of_eq (npp t)
    have key : ∑ v ∈ V, ((((v + p^t : ℕ)):ℚ_[p])⁻¹ - ((v:ℚ_[p]))⁻¹)
        = -((p^t:ℕ):ℚ_[p]) * (∑ v ∈ V, ((v:ℚ_[p])^2)⁻¹)
          + ((p^t:ℕ):ℚ_[p])^2 * (∑ v ∈ V, ((v:ℚ_[p])^2 * ((v:ℚ_[p]) + ((p^t:ℕ):ℚ_[p])))⁻¹) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      have hvd := hV v hv
      have hv_ne : ((v:ℚ_[p])) ≠ 0 := nuz hvd
      have hsum_unit : ¬ p ∣ (v + p^t) := by
        intro hdvd
        exact hvd (dvA hdvd hpP)
      have hcast : (((v + p^t : ℕ)):ℚ_[p]) = (v:ℚ_[p]) + ((p^t:ℕ):ℚ_[p]) := by push_cast; ring
      have hsum_ne : (v:ℚ_[p]) + ((p^t:ℕ):ℚ_[p]) ≠ 0 := by
        rw [← hcast]; exact nuz hsum_unit
      rw [hcast]
      field_simp
      ring
    rw [key]
    refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ ?_)
    · rw [norm_mul, norm_neg]
      calc ‖((p^t:ℕ):ℚ_[p])‖ * ‖∑ v ∈ V, ((v:ℚ_[p])^2)⁻¹‖ ≤ pe p t * pe p t :=
            mul_le_mul hPnorm h2 (norm_nonneg _) (peN _)
        _ = pe p (2*t) := by rw [pe_mul, two_mul]
    · rw [norm_mul, norm_pow]
      have hU : ‖∑ v ∈ V, ((v:ℚ_[p])^2 * ((v:ℚ_[p]) + ((p^t:ℕ):ℚ_[p])))⁻¹‖ ≤ 1 := by
        refine nsl _ (by norm_num) ?_
        intro v hv
        have hvd := hV v hv
        have hsum_unit : ¬ p ∣ (v + p^t) := by
          intro hdvd
          exact hvd (dvA hdvd hpP)
        have hcast : (((v + p^t : ℕ)):ℚ_[p]) = (v:ℚ_[p]) + ((p^t:ℕ):ℚ_[p]) := by push_cast; ring
        rw [norm_inv, norm_mul, norm_pow, nun hvd, ← hcast, nun hsum_unit]
        norm_num
      calc ‖((p^t:ℕ):ℚ_[p])‖^2 * ‖∑ v ∈ V, ((v:ℚ_[p])^2 * ((v:ℚ_[p]) + ((p^t:ℕ):ℚ_[p])))⁻¹‖
          ≤ (pe p t)^2 * 1 := by
            apply mul_le_mul _ hU (norm_nonneg _) (by positivity)
            exact pow_le_pow_left₀ (norm_nonneg _) hPnorm 2
        _ = pe p (2*t) := by rw [mul_one, pow_two, pe_mul, two_mul]

  have corr2_bound {t : ℕ} (ht : 1 ≤ t) (V : Finset ℕ) (hV : ∀ v ∈ V, ¬ p ∣ v) :
      ‖∑ v ∈ V, (((((v + p^t : ℕ)):ℚ_[p])^2)⁻¹ - ((v:ℚ_[p])^2)⁻¹)‖ ≤ pe p t := by
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hPnorm : ‖((p^t : ℕ) : ℚ_[p])‖ ≤ pe p t := le_of_eq (npp t)
    refine nsl _ (peN t) ?_
    intro v hv
    have hvd := hV v hv
    have hv_ne : ((v:ℚ_[p])) ≠ 0 := nuz hvd
    have hsum_unit : ¬ p ∣ (v + p^t) := by
      intro hdvd
      exact hvd (dvA hdvd hpP)
    have hcast : (((v + p^t : ℕ)):ℚ_[p]) = (v:ℚ_[p]) + ((p^t:ℕ):ℚ_[p]) := by push_cast; ring
    have hsum_ne : (v:ℚ_[p]) + ((p^t:ℕ):ℚ_[p]) ≠ 0 := by
      rw [← hcast]; exact nuz hsum_unit
    have identity : ((((v + p^t : ℕ)):ℚ_[p])^2)⁻¹ - ((v:ℚ_[p])^2)⁻¹
        = -(((p^t:ℕ):ℚ_[p]) * ((((p^t:ℕ):ℚ_[p]) + 2*(v:ℚ_[p]))
            * (((v:ℚ_[p])^2 * ((v:ℚ_[p]) + ((p^t:ℕ):ℚ_[p]))^2)⁻¹))) := by
      rw [hcast]
      field_simp
      ring
    rw [identity, norm_neg, norm_mul, norm_mul]
    have h1 : ‖((p^t:ℕ):ℚ_[p]) + 2*(v:ℚ_[p])‖ ≤ 1 := by
      have : ((p^t:ℕ):ℚ_[p]) + 2*(v:ℚ_[p]) = (((p^t + 2*v : ℕ)):ℚ_[p]) := by push_cast; ring
      rw [this]; exact norm_nat_le_one _
    have h2 : ‖(((v:ℚ_[p])^2 * ((v:ℚ_[p]) + ((p^t:ℕ):ℚ_[p]))^2)⁻¹)‖ ≤ 1 := by
      rw [norm_inv, norm_mul, norm_pow, norm_pow, nun hvd, ← hcast,
        nun hsum_unit]
      norm_num
    calc ‖((p^t:ℕ):ℚ_[p])‖ * (‖((p^t:ℕ):ℚ_[p]) + 2*(v:ℚ_[p])‖ * ‖(((v:ℚ_[p])^2 * ((v:ℚ_[p]) + ((p^t:ℕ):ℚ_[p]))^2)⁻¹)‖)
        ≤ pe p t * (1 * 1) := by
          apply mul_le_mul hPnorm _ (by positivity) (peN t)
          exact mul_le_mul h1 h2 (norm_nonneg _) (by norm_num)
      _ = pe p t := by ring

  have sumEven2_bound (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      ‖∑ v ∈ (US p t).filter (fun u => 2 ∣ u), ((v:ℚ_[p])^2)⁻¹‖ ≤ pe p t := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    have transfer : ∑ v ∈ (US p t).filter (fun u => 2 ∣ u), ((v:ℚ_[p])^2)⁻¹
        = ∑ d ∈ HS p t, (((2*d : ℕ):ℚ_[p])^2)⁻¹ := by
      refine Finset.sum_nbij' (fun v => v/2) (fun d => 2*d) ?_ ?_ ?_ ?_ ?_
      · intro v hv
        dsimp only
        simp only [Finset.mem_filter, mUS] at hv
        obtain ⟨⟨⟨h0, hP⟩, hd⟩, he⟩ := hv
        rw [mHS]
        refine ⟨by omega, ?_⟩
        intro hdvd
        exact hd (dvd_trans hdvd (Nat.div_dvd_of_dvd he))
      · intro d hd
        dsimp only
        rw [mHS] at hd
        obtain ⟨⟨h0, hh⟩, hdd⟩ := hd
        simp only [Finset.mem_filter, mUS]
        refine ⟨⟨by omega, ?_⟩, ⟨d, rfl⟩⟩
        intro hdvd
        rcases (Nat.Prime.dvd_mul hp.out).1 hdvd with h | h
        · have := Nat.le_of_dvd (by norm_num) h; omega
        · exact hdd h
      · intro v hv
        dsimp only
        simp only [Finset.mem_filter, mUS] at hv
        obtain ⟨⟨⟨h0, hP⟩, hd⟩, he⟩ := hv
        exact Nat.mul_div_cancel' he
      · intro d hd
        dsimp only
        omega
      · intro v hv
        simp only [Finset.mem_filter, mUS] at hv
        obtain ⟨⟨⟨h0, hP⟩, hd⟩, he⟩ := hv
        dsimp only
        rw [Nat.mul_div_cancel' he]
    rw [transfer]
    have step : ∀ d ∈ HS p t, (((2*d : ℕ):ℚ_[p])^2)⁻¹ = (4:ℚ_[p])⁻¹ * ((d:ℚ_[p])^2)⁻¹ := by
      intro d hd
      push_cast
      rw [mul_pow, ← mul_inv]
      norm_num
    rw [Finset.sum_congr rfl step, ← Finset.mul_sum, norm_mul, norm_inv, norm_four hp5,
      inv_one, one_mul]
    exact sumH2_bound hp5 ht

  have sumW1_bound (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      ‖∑ w ∈ WSet p t, ((w:ℚ_[p]))⁻¹‖ ≤ pe p (2*t) := by
    rw [sum_WSet_split hp5 ht]
    refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ (sumU1_bound hp5 ht))
    have hHV : ∀ d ∈ HS p t, ¬ p ∣ d := by
      intro d hd; rw [mHS] at hd; exact hd.2
    exact corr1_bound ht (HS p t) hHV (sumH2_bound hp5 ht)

  have sumW2_bound (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      ‖∑ w ∈ WSet p t, ((w:ℚ_[p])^2)⁻¹‖ ≤ pe p t := by
    rw [sum_WSet_split hp5 ht (fun w => ((w:ℚ_[p])^2)⁻¹)]
    refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ (sumU2_bound hp5 ht))
    have hHV : ∀ d ∈ HS p t, ¬ p ∣ d := by
      intro d hd; rw [mHS] at hd; exact hd.2
    exact corr2_bound ht (HS p t) hHV

  have sumO1_bound (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      ‖∑ y ∈ OSet p t, ((y:ℚ_[p]))⁻¹‖ ≤ pe p (2*t) := by
    rw [sum_OSet_split hp5 ht]
    refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ (sumU1_bound hp5 ht))
    have hHV : ∀ d ∈ (US p t).filter (fun u => 2 ∣ u), ¬ p ∣ d := by
      intro d hd
      simp only [Finset.mem_filter, mUS] at hd
      exact hd.1.2
    exact corr1_bound ht _ hHV (sumEven2_bound hp5 ht)

  have sumO2_bound (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      ‖∑ y ∈ OSet p t, ((y:ℚ_[p])^2)⁻¹‖ ≤ pe p t := by
    rw [sum_OSet_split hp5 ht (fun y => ((y:ℚ_[p])^2)⁻¹)]
    refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ (sumU2_bound hp5 ht))
    have hHV : ∀ d ∈ (US p t).filter (fun u => 2 ∣ u), ¬ p ∣ d := by
      intro d hd
      simp only [Finset.mem_filter, mUS] at hd
      exact hd.1.2
    exact corr2_bound ht _ hHV

  have window_block_near (hp5 : 5 ≤ p) {t : ℕ} (_ht : 1 ≤ t) (V : Finset ℕ)
      (hV : ∀ v ∈ V, ¬ p ∣ v)
      (h1 : ‖∑ v ∈ V, ((v:ℚ_[p]))⁻¹‖ ≤ pe p (2*t))
      (h2 : ‖∑ v ∈ V, ((v:ℚ_[p])^2)⁻¹‖ ≤ pe p t)
      (Δ : ℕ) (hΔ : p^t ∣ Δ) :
      Near (3*t) (∏ v ∈ V, (((v + Δ : ℕ):ℚ_[p]) / (v:ℚ_[p]))) := by
    have hΔnorm : ‖((Δ:ℕ):ℚ_[p])‖ ≤ pe p t := by simp only [pe_def]; exact norm_nat_dvd_le hΔ
    have hrw : ∀ v ∈ V, (((v + Δ : ℕ):ℚ_[p]) / (v:ℚ_[p])) = 1 + (Δ:ℚ_[p]) * ((v:ℚ_[p]))⁻¹ := by
      intro v hv
      have hv_ne : ((v:ℚ_[p])) ≠ 0 := nuz (hV v hv)
      push_cast
      field_simp
    rw [Finset.prod_congr rfl hrw]
    simp only [Near_def]
    have hbnd : ∀ v ∈ V, ‖(Δ:ℚ_[p]) * ((v:ℚ_[p]))⁻¹‖ ≤ pe p t := by
      intro v hv
      rw [norm_mul]
      calc ‖(Δ:ℚ_[p])‖ * ‖((v:ℚ_[p]))⁻¹‖ ≤ pe p t * 1 :=
            mul_le_mul hΔnorm (norm_inv_unit_le_one (hV v hv)) (norm_nonneg _) (peN _)
        _ = pe p t := mul_one _
    refine prod_one_add_near (pn2 hp5) V _ (peN t) (pe_le_one t)
      hbnd (pe_le_one _) ?_ ?_ ?_
    · rw [← Finset.mul_sum, norm_mul]
      calc ‖(Δ:ℚ_[p])‖ * ‖∑ v ∈ V, ((v:ℚ_[p]))⁻¹‖ ≤ pe p t * pe p (2*t) :=
            mul_le_mul hΔnorm h1 (norm_nonneg _) (peN _)
        _ = pe p (3*t) := by rw [pe_mul]; congr 1; ring
    · have hrw2 : ∀ v ∈ V, ((Δ:ℚ_[p]) * ((v:ℚ_[p]))⁻¹)^2 = (Δ:ℚ_[p])^2 * ((v:ℚ_[p])^2)⁻¹ := by
        intro v hv
        rw [mul_pow, inv_pow]
      rw [Finset.sum_congr rfl hrw2, ← Finset.mul_sum, norm_mul, norm_pow]
      calc ‖(Δ:ℚ_[p])‖^2 * ‖∑ v ∈ V, ((v:ℚ_[p])^2)⁻¹‖ ≤ (pe p t)^2 * pe p t := by
            apply mul_le_mul _ h2 (norm_nonneg _) (by positivity)
            exact pow_le_pow_left₀ (norm_nonneg _) hΔnorm 2
        _ = pe p (3*t) := by rw [pow_two, pe_mul, pe_mul]; congr 1; ring
    · have : (pe p t)^3 = pe p (3*t) := by
        rw [pow_succ, pow_two, pe_mul, pe_mul]
        congr 1
        ring
      rw [this]




  have prod_USet_split {t : ℕ} :
      ∏ u ∈ US p t, u
        = (∏ d ∈ HS p t, d) * ∏ u ∈ (US p t).filter (fun u => ¬ u ≤ p^t/2), u := by
    rw [← UfH]
    exact (Finset.prod_filter_mul_prod_filter_not (US p t) _ _).symm

  have prod_upper_eq (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      ∏ u ∈ (US p t).filter (fun u => ¬ u ≤ p^t/2), u = ∏ d ∈ HS p t, (p^t - d) := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    refine Finset.prod_nbij' (fun u => p^t - u) (fun d => p^t - d) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      dsimp only
      simp only [Finset.mem_filter, mUS] at hu
      obtain ⟨⟨⟨h0, hP⟩, hd⟩, hh⟩ := hu
      have hlt : u < p^t := by
        have hne : u ≠ p^t := fun he => hd (he ▸ hpP)
        omega
      rw [mHS]
      refine ⟨by omega, ?_⟩
      intro hdvd
      apply hd
      apply dvA (b := p^t - u)
      · have : u + (p^t - u) = p^t := by omega
        rw [this]; exact hpP
      · exact hdvd
    · intro d hd
      dsimp only
      rw [mHS] at hd
      obtain ⟨⟨h0, hh⟩, hdd⟩ := hd
      simp only [Finset.mem_filter, mUS]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      intro hdvd
      apply hdd
      apply dvA (b := p^t - d)
      · have : d + (p^t - d) = p^t := by omega
        rw [this]; exact hpP
      · exact hdvd
    · intro u hu
      dsimp only
      simp only [Finset.mem_filter, mUS] at hu
      omega
    · intro d hd
      dsimp only
      rw [mHS] at hd
      have : p^t/2 ≤ p^t := Nat.div_le_self _ _
      omega
    · intro u hu
      dsimp only
      simp only [Finset.mem_filter, mUS] at hu
      omega

  have prod_even_eq {t : ℕ} (hp5 : 5 ≤ p) :
      ∏ u ∈ (US p t).filter (fun u => 2 ∣ u), u
        = 2^((HS p t).card) * ∏ d ∈ HS p t, d := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    have transfer : ∏ u ∈ (US p t).filter (fun u => 2 ∣ u), u
        = ∏ d ∈ HS p t, (2*d) := by
      refine Finset.prod_nbij' (fun v => v/2) (fun d => 2*d) ?_ ?_ ?_ ?_ ?_
      · intro v hv
        dsimp only
        simp only [Finset.mem_filter, mUS] at hv
        obtain ⟨⟨⟨h0, hP⟩, hd⟩, he⟩ := hv
        rw [mHS]
        refine ⟨by omega, ?_⟩
        intro hdvd
        exact hd (dvd_trans hdvd (Nat.div_dvd_of_dvd he))
      · intro d hd
        dsimp only
        rw [mHS] at hd
        obtain ⟨⟨h0, hh⟩, hdd⟩ := hd
        simp only [Finset.mem_filter, mUS]
        refine ⟨⟨by omega, ?_⟩, ⟨d, rfl⟩⟩
        intro hdvd
        rcases (Nat.Prime.dvd_mul hp.out).1 hdvd with h | h
        · have := Nat.le_of_dvd (by norm_num) h; omega
        · exact hdd h
      · intro v hv
        dsimp only
        simp only [Finset.mem_filter, mUS] at hv
        obtain ⟨⟨⟨h0, hP⟩, hd⟩, he⟩ := hv
        exact Nat.mul_div_cancel' he
      · intro d hd
        dsimp only
        omega
      · intro v hv
        simp only [Finset.mem_filter, mUS] at hv
        obtain ⟨⟨⟨h0, hP⟩, hd⟩, he⟩ := hv
        dsimp only
        exact (Nat.mul_div_cancel' he).symm
    rw [transfer, Finset.prod_mul_distrib, Finset.prod_const]

  have prod_odd_eq (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      ∏ u ∈ (US p t).filter (fun u => ¬ 2 ∣ u), u
        = ∏ d ∈ HS p t, (p^t - 2*d) := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    refine Finset.prod_nbij' (fun y => (p^t - y)/2) (fun d => p^t - 2*d) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      dsimp only
      simp only [Finset.mem_filter, mUS] at hy
      obtain ⟨⟨⟨h0, hP⟩, hd⟩, hodd⟩ := hy
      have hlt : y < p^t := by
        have hne : y ≠ p^t := fun he => hd (he ▸ hpP)
        omega
      have hy2 : y ≤ p^t - 2 := by omega
      have heven : 2 ∣ (p^t - y) := by omega
      rw [mHS]
      refine ⟨by omega, ?_⟩
      intro hdvd
      have hPy : p ∣ (p^t - y) := dvd_trans hdvd (Nat.div_dvd_of_dvd heven)
      apply hd
      apply dvA (b := p^t - y)
      · have : y + (p^t - y) = p^t := by omega
        rw [this]; exact hpP
      · exact hPy
    · intro d hd
      dsimp only
      rw [mHS] at hd
      obtain ⟨⟨h0, hh⟩, hdd⟩ := hd
      simp only [Finset.mem_filter, mUS]
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      intro hdvd
      have h2d : p ∣ 2*d := by
        apply dvA (b := p^t - 2*d)
        · have : 2*d + (p^t - 2*d) = p^t := by omega
          rw [this]; exact hpP
        · exact hdvd
      rcases (Nat.Prime.dvd_mul hp.out).1 h2d with h | h
      · have := Nat.le_of_dvd (by norm_num) h; omega
      · exact hdd h
    · intro y hy
      dsimp only
      simp only [Finset.mem_filter, mUS] at hy
      obtain ⟨⟨⟨h0, hP⟩, hd⟩, hodd⟩ := hy
      have hlt : y < p^t := by
        have hne : y ≠ p^t := fun he => hd (he ▸ hpP)
        omega
      omega
    · intro d hd
      dsimp only
      rw [mHS] at hd
      omega
    · intro y hy
      dsimp only
      simp only [Finset.mem_filter, mUS] at hy
      obtain ⟨⟨⟨h0, hP⟩, hd⟩, hodd⟩ := hy
      have hlt : y < p^t := by
        have hne : y ≠ p^t := fun he => hd (he ▸ hpP)
        omega
      omega

  have prod_HSet_pos {t : ℕ} : 0 < ∏ d ∈ HS p t, d := by
    apply Finset.prod_pos
    intro d hd
    rw [mHS] at hd
    omega

  have morley_nat (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      2^((HS p t).card) * ∏ d ∈ HS p t, (p^t - 2*d) = ∏ d ∈ HS p t, (p^t - d) := by
    have parity_split : ∏ u ∈ US p t, u
        = (∏ u ∈ (US p t).filter (fun u => 2 ∣ u), u)
          * ∏ u ∈ (US p t).filter (fun u => ¬ 2 ∣ u), u :=
      (Finset.prod_filter_mul_prod_filter_not (US p t) _ _).symm
    have h1 : (2^((HS p t).card) * ∏ d ∈ HS p t, d) * (∏ d ∈ HS p t, (p^t - 2*d))
        = (∏ d ∈ HS p t, d) * ∏ d ∈ HS p t, (p^t - d) := by
      rw [← prod_even_eq hp5, ← prod_odd_eq hp5 ht, ← parity_split, prod_USet_split,
        prod_upper_eq hp5 ht]
    apply Nat.eq_of_mul_eq_mul_left (prod_HSet_pos (t := t))
    calc (∏ d ∈ HS p t, d) * (2^((HS p t).card) * ∏ d ∈ HS p t, (p^t - 2*d))
        = (2^((HS p t).card) * ∏ d ∈ HS p t, d) * (∏ d ∈ HS p t, (p^t - 2*d)) := by ring
      _ = (∏ d ∈ HS p t, d) * ∏ d ∈ HS p t, (p^t - d) := h1

  have card_USet_double (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      (US p t).card = 2 * (HS p t).card := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := US p t) (p := fun u => u ≤ p^t/2)
    rw [UfH] at hsplit
    have hupper : ((US p t).filter (fun u => ¬ u ≤ p^t/2)).card = (HS p t).card := by
      apply Finset.card_nbij' (fun u => p^t - u) (fun d => p^t - d)
      · intro u hu
        dsimp only
        simp only [Finset.mem_coe, Finset.mem_filter, mUS] at hu
        obtain ⟨⟨⟨h0, hP⟩, hd⟩, hh⟩ := hu
        have hlt : u < p^t := by
          have hne : u ≠ p^t := fun he => hd (he ▸ hpP)
          omega
        rw [Finset.mem_coe, mHS]
        refine ⟨by omega, ?_⟩
        intro hdvd
        apply hd
        apply dvA (b := p^t - u)
        · have : u + (p^t - u) = p^t := by omega
          rw [this]; exact hpP
        · exact hdvd
      · intro d hd
        dsimp only
        rw [Finset.mem_coe, mHS] at hd
        obtain ⟨⟨h0, hh⟩, hdd⟩ := hd
        simp only [Finset.mem_coe, Finset.mem_filter, mUS]
        refine ⟨⟨by omega, ?_⟩, by omega⟩
        intro hdvd
        apply hdd
        apply dvA (b := p^t - d)
        · have : d + (p^t - d) = p^t := by omega
          rw [this]; exact hpP
        · exact hdvd
      · intro u hu
        dsimp only
        simp only [Finset.mem_coe, Finset.mem_filter, mUS] at hu
        omega
      · intro d hd
        dsimp only
        rw [Finset.mem_coe, mHS] at hd
        have : p^t/2 ≤ p^t := Nat.div_le_self _ _
        omega
    omega

  have card_USet (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      (US p t).card = p^t - p^(t-1) := by
    have hppos : 0 < p := by omega
    have hPP : p * p^(t-1) = p^t := by
      rw [← pow_succ']
      congr 1
      omega
    have hcard_mult : ((Finset.Ioc 0 (p^t)).filter (fun u => p ∣ u)).card = p^(t-1) := by
      have : ((Finset.Ioc 0 (p^(t-1))).card) = p^(t-1) := by
        rw [Nat.card_Ioc]; omega
      rw [← this]
      symm
      apply Finset.card_nbij' (fun k => p * k) (fun m => m / p)
      · intro k hk
        simp only [Finset.mem_coe, Finset.mem_Ioc] at hk
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨Nat.mul_pos hppos hk.1, ?_⟩, ⟨k, rfl⟩⟩
        calc p * k ≤ p * p^(t-1) := Nat.mul_le_mul_left p hk.2
          _ = p^t := hPP
      · intro m hm
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hm
        obtain ⟨⟨h0, hP⟩, k, hk⟩ := hm
        subst hk
        simp only [Finset.mem_coe, Finset.mem_Ioc]
        rw [Nat.mul_div_cancel_left k hppos]
        constructor
        · rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · subst hk0; omega
          · exact hk0
        · by_contra h
          push_neg at h
          have : p * p^(t-1) < p * k := (Nat.mul_lt_mul_left hppos).mpr h
          omega
      · intro k hk
        dsimp only
        rw [Nat.mul_div_cancel_left k hppos]
      · intro m hm
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hm
        obtain ⟨⟨h0, hP⟩, k, hk⟩ := hm
        subst hk
        dsimp only
        rw [Nat.mul_div_cancel_left k hppos]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.Ioc 0 (p^t)) (p := fun u => p ∣ u)
    have hIoc : (Finset.Ioc 0 (p^t)).card = p^t := by rw [Nat.card_Ioc]; omega
    have hUS : (US p t).card = ((Finset.Ioc 0 (p^t)).filter (fun u => ¬ p ∣ u)).card := by rw [US_def]
    omega

  have WSet_transfer (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      ∏ w ∈ WSet p t, w
        = ∏ u ∈ US p t, (if u ≤ p^t/2 then u + p^t else u) := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    · 
      refine Finset.prod_nbij' (fun w => if p^t < w then w - p^t else w)
        (fun u => if u ≤ p^t/2 then u + p^t else u) ?_ ?_ ?_ ?_ ?_
      · intro w hw
        dsimp only
        rw [mem_WSet] at hw
        obtain ⟨⟨h1, h2⟩, hd⟩ := hw
        by_cases hc : p^t < w
        · rw [if_pos hc, mUS]
          exact ⟨by omega, not_dvd_sub hpP hd (by omega)⟩
        · rw [if_neg hc, mUS]
          exact ⟨by omega, hd⟩
      · intro u hu
        dsimp only
        rw [mUS] at hu
        obtain ⟨⟨h1, h2⟩, hd⟩ := hu
        by_cases hc : u ≤ p^t/2
        · rw [if_pos hc, mem_WSet]
          refine ⟨by omega, ?_⟩
          intro hdvd
          exact hd (dvA hdvd hpP)
        · rw [if_neg hc, mem_WSet]
          exact ⟨by omega, hd⟩
      · intro w hw
        dsimp only
        rw [mem_WSet] at hw
        obtain ⟨⟨h1, h2⟩, hd⟩ := hw
        by_cases hc : p^t < w
        · rw [if_pos hc, if_pos (by omega)]
          omega
        · rw [if_neg hc, if_neg (by omega)]
      · intro u hu
        dsimp only
        rw [mUS] at hu
        obtain ⟨⟨h1, h2⟩, hd⟩ := hu
        by_cases hc : u ≤ p^t/2
        · rw [if_pos hc, if_pos (by omega)]
          omega
        · rw [if_neg hc, if_neg (by omega)]
      · intro w hw
        dsimp only
        rw [mem_WSet] at hw
        obtain ⟨⟨h1, h2⟩, hd⟩ := hw
        by_cases hc : p^t < w
        · rw [if_pos hc, if_pos (by omega)]
          omega
        · rw [if_neg hc, if_neg (by omega)]

  have prod_WSet_eq (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      ∏ w ∈ WSet p t, w
        = (∏ d ∈ HS p t, (d + p^t)) * ∏ u ∈ (US p t).filter (fun u => ¬ u ≤ p^t/2), u := by
    rw [WSet_transfer hp5 ht, Finset.prod_ite, UfH]

  have prod_BlP_eq (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      ∏ u ∈ US p t, (u + p^t) = 2^((US p t).card) * ∏ y ∈ OSet p t, y := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    have hppos : 0 < p := by omega
    have split1 : ∏ u ∈ (Finset.Ioc 0 (2*p^t)).filter (fun u => ¬ p ∣ u), u
        = (∏ u ∈ US p t, u) * ∏ u ∈ US p t, (u + p^t) := by
      have hunion : Finset.Ioc 0 (2*p^t) = Finset.Ioc 0 (p^t) ∪ Finset.Ioc (p^t) (2*p^t) := by
        rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (by omega)]
      have hdisj : Disjoint ((Finset.Ioc 0 (p^t)).filter (fun u => ¬ p ∣ u))
          ((Finset.Ioc (p^t) (2*p^t)).filter (fun u => ¬ p ∣ u)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hx1 hx2
        omega
      have hshift : ∏ u ∈ (Finset.Ioc (p^t) (2*p^t)).filter (fun u => ¬ p ∣ u), u
          = ∏ u ∈ US p t, (u + p^t) := by
        refine Finset.prod_nbij' (fun w => w - p^t) (fun u => u + p^t) ?_ ?_ ?_ ?_ ?_
        · intro w hw
          dsimp only
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hw
          obtain ⟨⟨h1, h2⟩, hd⟩ := hw
          rw [mUS]
          exact ⟨by omega, not_dvd_sub hpP hd (by omega)⟩
        · intro u hu
          dsimp only
          rw [mUS] at hu
          obtain ⟨⟨h1, h2⟩, hd⟩ := hu
          simp only [Finset.mem_filter, Finset.mem_Ioc]
          refine ⟨by omega, ?_⟩
          intro hdvd
          exact hd (dvA hdvd hpP)
        · intro w hw
          dsimp only
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hw
          omega
        · intro u hu
          dsimp only
          omega
        · intro w hw
          dsimp only
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hw
          omega
      rw [hunion, Finset.filter_union, Finset.prod_union hdisj, hshift]
      simp only [US_def]
    have split2 : ∏ u ∈ (Finset.Ioc 0 (2*p^t)).filter (fun u => ¬ p ∣ u), u
        = (∏ u ∈ ((Finset.Ioc 0 (2*p^t)).filter (fun u => ¬ p ∣ u)).filter (fun u => 2 ∣ u), u)
          * ∏ y ∈ OSet p t, y := by
      have hodd : ((Finset.Ioc 0 (2*p^t)).filter (fun u => ¬ p ∣ u)).filter (fun u => ¬ 2 ∣ u)
          = OSet p t := by
        rw [Finset.filter_filter]
        simp only [OSet_def]
      rw [← hodd]
      exact (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
    have heven : ∏ u ∈ ((Finset.Ioc 0 (2*p^t)).filter (fun u => ¬ p ∣ u)).filter (fun u => 2 ∣ u), u
        = 2^((US p t).card) * ∏ u ∈ US p t, u := by
      have transfer : ∏ u ∈ ((Finset.Ioc 0 (2*p^t)).filter (fun u => ¬ p ∣ u)).filter
          (fun u => 2 ∣ u), u = ∏ u ∈ US p t, (2*u) := by
        refine Finset.prod_nbij' (fun v => v/2) (fun u => 2*u) ?_ ?_ ?_ ?_ ?_
        · intro v hv
          dsimp only
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hv
          obtain ⟨⟨⟨h0, hP⟩, hd⟩, he⟩ := hv
          rw [mUS]
          refine ⟨by omega, ?_⟩
          intro hdvd
          exact hd (dvd_trans hdvd (Nat.div_dvd_of_dvd he))
        · intro u hu
          dsimp only
          rw [mUS] at hu
          obtain ⟨⟨h0, hP⟩, hd⟩ := hu
          simp only [Finset.mem_filter, Finset.mem_Ioc]
          refine ⟨⟨by omega, ?_⟩, ⟨u, rfl⟩⟩
          intro hdvd
          rcases (Nat.Prime.dvd_mul hp.out).1 hdvd with h | h
          · have := Nat.le_of_dvd (by norm_num) h; omega
          · exact hd h
        · intro v hv
          dsimp only
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hv
          obtain ⟨⟨⟨h0, hP⟩, hd⟩, he⟩ := hv
          exact Nat.mul_div_cancel' he
        · intro u hu
          dsimp only
          omega
        · intro v hv
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hv
          obtain ⟨⟨⟨h0, hP⟩, hd⟩, he⟩ := hv
          dsimp only
          exact (Nat.mul_div_cancel' he).symm
      rw [transfer, Finset.prod_mul_distrib, Finset.prod_const]
    have hUpos : 0 < ∏ u ∈ US p t, u := by
      apply Finset.prod_pos
      intro u hu
      rw [mUS] at hu
      omega
    apply Nat.eq_of_mul_eq_mul_left hUpos
    calc (∏ u ∈ US p t, u) * ∏ u ∈ US p t, (u + p^t)
        = ∏ u ∈ (Finset.Ioc 0 (2*p^t)).filter (fun u => ¬ p ∣ u), u := split1.symm
      _ = (2^((US p t).card) * ∏ u ∈ US p t, u) * ∏ y ∈ OSet p t, y := by
          rw [split2, heven]
      _ = (∏ u ∈ US p t, u) * (2^((US p t).card) * ∏ y ∈ OSet p t, y) := by ring




  have HSet_unit {t d : ℕ} (hd : d ∈ HS p t) : ¬ p ∣ d := (mHS.1 hd).2

  have HSet_shift_unit (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) {d : ℕ} (hd : d ∈ HS p t) :
      ¬ p ∣ (p^t - 2*d) := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    rw [mHS] at hd
    obtain ⟨⟨h0, hh⟩, hdd⟩ := hd
    intro hdvd
    have h2d : p ∣ 2*d := by
      apply dvA (b := p^t - 2*d)
      · have : 2*d + (p^t - 2*d) = p^t := by omega
        rw [this]; exact hpP
      · exact hdvd
    rcases (Nat.Prime.dvd_mul hp.out).1 h2d with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · exact hdd h

  have two_d_le (hp5 : 5 ≤ p) {t : ℕ} {d : ℕ} (hd : d ∈ HS p t) : 2*d ≤ p^t := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    rw [mHS] at hd; omega

  have cast_P_sub_two (hp5 : 5 ≤ p) {t : ℕ} {d : ℕ} (hd : d ∈ HS p t) :
      ((p^t - 2*d : ℕ) : ℚ_[p]) = ((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]) := by
    rw [Nat.cast_sub (two_d_le hp5 hd)]
    push_cast
    ring

  have morley_padic (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      ∏ d ∈ HS p t, (((p^t : ℕ) : ℚ_[p]) - (d:ℚ_[p]))
        = 2^((HS p t).card) * ∏ d ∈ HS p t, (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p])) := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    have h := morley_nat hp5 ht
    have hcast := congrArg (fun n : ℕ => (n : ℚ_[p])) h
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_prod] at hcast
    have hL : ∀ d ∈ HS p t, ((p^t - 2*d : ℕ) : ℚ_[p]) = ((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]) :=
      fun d hd => cast_P_sub_two hp5 hd
    have hR : ∀ d ∈ HS p t, ((p^t - d : ℕ) : ℚ_[p]) = ((p^t : ℕ) : ℚ_[p]) - (d:ℚ_[p]) := by
      intro d hd
      rw [mHS] at hd
      rw [Nat.cast_sub (by omega)]
    rw [Finset.prod_congr rfl hL, Finset.prod_congr rfl hR] at hcast
    exact hcast.symm

  obtain ⟨wf, wf_def⟩ : ∃ f : ℕ → ℕ → ℚ_[p], f = fun (t d : ℕ) => (((p^t : ℕ) : ℚ_[p])^2 * (4*((p^t : ℕ) : ℚ_[p]) - 5*(d:ℚ_[p]))) / ((d:ℚ_[p]) * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2) := ⟨_, rfl⟩

  have wf_denom_ne_zero (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) {d : ℕ} (hd : d ∈ HS p t) :
      (d:ℚ_[p]) ≠ 0 ∧ (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p])) ≠ 0 := by
    refine ⟨nuz (HSet_unit hd), ?_⟩
    rw [← cast_P_sub_two hp5 hd]
    exact nuz (HSet_shift_unit hp5 ht hd)

  have norm_P_sub_two (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) {d : ℕ} (hd : d ∈ HS p t) :
      ‖((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p])‖ = 1 := by
    rw [← cast_P_sub_two hp5 hd]
    exact nun (HSet_shift_unit hp5 ht hd)

  have wf_norm_le (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) {d : ℕ} (hd : d ∈ HS p t) :
      ‖wf t d‖ ≤ pe p (2*t) := by
    have hden : ‖(d:ℚ_[p]) * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2‖ = 1 := by
      rw [norm_mul, norm_pow, nun (HSet_unit hd), norm_P_sub_two hp5 ht hd]
      norm_num
    have hnum1 : ‖4*((p^t : ℕ) : ℚ_[p]) - 5*(d:ℚ_[p])‖ ≤ 1 := by
      have hc : ((4*p^t - 5*d : ℤ) : ℚ_[p]) = 4*((p^t : ℕ) : ℚ_[p]) - 5*(d:ℚ_[p]) := by
        push_cast; ring
      rw [← hc]
      exact Padic.norm_int_le_one _
    simp only [wf_def]
    rw [norm_div, hden, div_one, norm_mul, norm_pow, npp]
    calc pe p t ^ 2 * ‖4*((p^t : ℕ) : ℚ_[p]) - 5*(d:ℚ_[p])‖
        ≤ pe p t ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left hnum1 (pow_nonneg (peN t) 2)
      _ = pe p (2*t) := by
          rw [mul_one, sq, pe_mul]
          congr 1
          omega

  have wf_corr_norm_le (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) {d : ℕ} (hd : d ∈ HS p t) :
      ‖wf t d + (5/4) * ((p^t : ℕ) : ℚ_[p])^2 * ((d:ℚ_[p])^2)⁻¹‖ ≤ pe p (3*t) := by
    obtain ⟨hd0, hden0⟩ := wf_denom_ne_zero hp5 ht hd
    have h4 : (4:ℚ_[p]) ≠ 0 := by
      intro h
      have h' := norm_four hp5
      rw [h, norm_zero] at h'
      exact absurd h' (by norm_num)
    have hne : ((d:ℚ_[p]) * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2) ≠ 0 :=
      mul_ne_zero hd0 (pow_ne_zero _ hden0)
    have e1 : wf t d * (4 * (d:ℚ_[p])^2 * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2)
        = (((p^t : ℕ) : ℚ_[p])^2 * (4*((p^t : ℕ) : ℚ_[p]) - 5*(d:ℚ_[p]))) * (4*(d:ℚ_[p])) := by
      have hsplit : (4 * (d:ℚ_[p])^2 * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2)
          = ((d:ℚ_[p]) * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2) * (4*(d:ℚ_[p])) := by ring
      simp only [wf_def]
      rw [hsplit, ← mul_assoc, div_mul_cancel₀ _ hne]
    have e2 : ((5:ℚ_[p])/4) * ((p^t : ℕ) : ℚ_[p])^2 * ((d:ℚ_[p])^2)⁻¹
        * (4 * (d:ℚ_[p])^2 * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2)
        = 5 * (((p^t : ℕ) : ℚ_[p])^2 * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2) := by
      have hd2 : ((d:ℚ_[p])^2) ≠ 0 := pow_ne_zero _ hd0
      have hsplit : ((5:ℚ_[p])/4) * ((p^t : ℕ) : ℚ_[p])^2 * ((d:ℚ_[p])^2)⁻¹
          * (4 * (d:ℚ_[p])^2 * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2)
          = ((d:ℚ_[p])^2)⁻¹ * ((d:ℚ_[p])^2)
            * ((5/4*4) * (((p^t : ℕ) : ℚ_[p])^2 * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2)) := by
        ring
      rw [hsplit, inv_mul_cancel₀ hd2, one_mul]
      congr 1
      rw [div_mul_cancel₀ _ h4]
    have hmul : (wf t d + (5/4) * ((p^t : ℕ) : ℚ_[p])^2 * ((d:ℚ_[p])^2)⁻¹)
        * (4 * (d:ℚ_[p])^2 * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2)
        = ((p^t : ℕ) : ℚ_[p])^3 * (5*((p^t : ℕ) : ℚ_[p]) - 4*(d:ℚ_[p])) := by
      rw [add_mul, e1, e2]
      ring
    have hnormD : ‖4 * (d:ℚ_[p])^2 * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2‖ = 1 := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_four hp5,
        nun (HSet_unit hd), norm_P_sub_two hp5 ht hd]
      norm_num
    have hS : ‖wf t d + (5/4) * ((p^t : ℕ) : ℚ_[p])^2 * ((d:ℚ_[p])^2)⁻¹‖
        = ‖((p^t : ℕ) : ℚ_[p])^3 * (5*((p^t : ℕ) : ℚ_[p]) - 4*(d:ℚ_[p]))‖ := by
      rw [← hmul, norm_mul, hnormD, mul_one]
    have hnum1 : ‖5*((p^t : ℕ) : ℚ_[p]) - 4*(d:ℚ_[p])‖ ≤ 1 := by
      have hc : ((5*p^t - 4*d : ℤ) : ℚ_[p]) = 5*((p^t : ℕ) : ℚ_[p]) - 4*(d:ℚ_[p]) := by
        push_cast; ring
      rw [← hc]
      exact Padic.norm_int_le_one _
    rw [hS, norm_mul, norm_pow, npp]
    calc pe p t ^ 3 * ‖5*((p^t : ℕ) : ℚ_[p]) - 4*(d:ℚ_[p])‖
        ≤ pe p t ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left hnum1 (pow_nonneg (peN t) 3)
      _ = pe p (3*t) := by
          rw [mul_one, pow_succ, sq, pe_mul, pe_mul]
          congr 1
          omega

  have X_eq_prod (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      (2:ℚ_[p])^(4*(HS p t).card) * ∏ d ∈ HS p t, (((d + p^t : ℕ):ℚ_[p]) / (d:ℚ_[p]))
        = ∏ d ∈ HS p t, (1 + wf t d) := by
    have hfac : ∀ d ∈ HS p t, (1 + wf t d)
        = 4*(((p^t : ℕ) : ℚ_[p]) - (d:ℚ_[p]))^2 * (((p^t : ℕ) : ℚ_[p]) + (d:ℚ_[p]))
          / ((d:ℚ_[p]) * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2) := by
      intro d hd
      obtain ⟨hd0, hden0⟩ := wf_denom_ne_zero hp5 ht hd
      have hne : ((d:ℚ_[p]) * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2) ≠ 0 :=
        mul_ne_zero hd0 (pow_ne_zero _ hden0)
      have e0 : wf t d * ((d:ℚ_[p]) * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2)
          = ((p^t : ℕ) : ℚ_[p])^2 * (4*((p^t : ℕ) : ℚ_[p]) - 5*(d:ℚ_[p])) := by
        simp only [wf_def]
        rw [div_mul_cancel₀ _ hne]
      rw [eq_div_iff hne, add_mul, one_mul, e0]
      ring
    rw [Finset.prod_congr rfl hfac]
    have hnum_cast : ∀ d ∈ HS p t, ((d + p^t : ℕ):ℚ_[p]) / (d:ℚ_[p])
        = (((p^t : ℕ) : ℚ_[p]) + (d:ℚ_[p])) / (d:ℚ_[p]) := by
      intro d hd
      congr 1
      push_cast
      ring
    rw [Finset.prod_congr rfl hnum_cast]
    have hd_ne : (∏ d ∈ HS p t, (d:ℚ_[p])) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 (fun d hd => nuz (HSet_unit hd))
    have hD_ne : (∏ d ∈ HS p t, ((d:ℚ_[p]) * (((p^t : ℕ) : ℚ_[p]) - 2*(d:ℚ_[p]))^2)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.2
      intro d hd
      obtain ⟨hd0, hden0⟩ := wf_denom_ne_zero hp5 ht hd
      exact mul_ne_zero hd0 (pow_ne_zero _ hden0)
    rw [Finset.prod_div_distrib, Finset.prod_div_distrib, mul_div_assoc',
      div_eq_div_iff hd_ne hD_ne]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_pow, Finset.prod_pow, morley_padic hp5 ht]
    have h4c : (4:ℚ_[p])^((HS p t).card) = 2^(2*(HS p t).card) := by
      rw [pow_mul]; norm_num
    rw [h4c]
    ring

  have X_near (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      Near (3*t) ((2:ℚ_[p])^(4*(HS p t).card)
        * ∏ d ∈ HS p t, (((d + p^t : ℕ):ℚ_[p]) / (d:ℚ_[p]))) := by
    simp only [Near_def]
    rw [X_eq_prod hp5 ht]
    have h_corr_sum : ‖∑ d ∈ HS p t,
        (wf t d + (5/4) * ((p^t : ℕ) : ℚ_[p])^2 * ((d:ℚ_[p])^2)⁻¹)‖ ≤ pe p (3*t) :=
      nsl _ (peN _) (fun d hd => wf_corr_norm_le hp5 ht hd)
    have h54 : ‖(5:ℚ_[p])/4‖ ≤ 1 := by
      rw [norm_div, norm_four hp5, div_one]
      have : ((5:ℕ) : ℚ_[p]) = (5:ℚ_[p]) := by norm_num
      rw [← this]
      exact norm_nat_le_one 5
    have hB : ‖(5:ℚ_[p])/4 * ((p^t : ℕ) : ℚ_[p])^2 * ∑ d ∈ HS p t, ((d:ℚ_[p])^2)⁻¹‖
        ≤ pe p (3*t) := by
      rw [norm_mul, norm_mul, norm_pow, npp]
      calc ‖(5:ℚ_[p])/4‖ * pe p t ^ 2 * ‖∑ d ∈ HS p t, ((d:ℚ_[p])^2)⁻¹‖
          ≤ 1 * pe p t ^ 2 * pe p t := by
            apply mul_le_mul _ (sumH2_bound hp5 ht) (norm_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_right h54 (pow_nonneg (peN t) 2)
        _ = pe p (3*t) := by
            rw [one_mul, sq, pe_mul, pe_mul]
            congr 1
            ring
    have hsum_split : ∑ d ∈ HS p t, wf t d
        = (∑ d ∈ HS p t, (wf t d + (5/4) * ((p^t : ℕ) : ℚ_[p])^2 * ((d:ℚ_[p])^2)⁻¹))
          - (5:ℚ_[p])/4 * ((p^t : ℕ) : ℚ_[p])^2 * ∑ d ∈ HS p t, ((d:ℚ_[p])^2)⁻¹ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf
    have h1 : ‖∑ d ∈ HS p t, wf t d‖ ≤ pe p (3*t) := by
      rw [hsum_split, sub_eq_add_neg]
      refine le_trans (Padic.nonarchimedean _ _) ?_
      rw [norm_neg]
      exact max_le h_corr_sum hB
    have h2 : ‖∑ d ∈ HS p t, (wf t d)^2‖ ≤ pe p (3*t) := by
      apply nsl _ (peN _)
      intro d hd
      rw [norm_pow]
      calc ‖wf t d‖^2 ≤ (pe p (2*t))^2 :=
            pow_le_pow_left₀ (norm_nonneg _) (wf_norm_le hp5 ht hd) 2
        _ = pe p (4*t) := by rw [sq, pe_mul]; congr 1; ring
        _ ≤ pe p (3*t) := pe_mono (by omega)
    refine prod_one_add_near (pn2 hp5) _ _ (peN (2*t)) (pe_le_one _)
      (fun d hd => wf_norm_le hp5 ht hd) (pe_le_one _) h1 h2 ?_
    have : (pe p (2*t))^3 = pe p (6*t) := by
      rw [pow_succ, pow_two, pe_mul, pe_mul]
      congr 1
      ring
    rw [this]
    exact pe_mono (by omega)




  have dvd_add_iff_of_dvd {c y : ℕ} (hc : p ∣ c) : p ∣ (y + c) ↔ p ∣ y :=
    ⟨fun h => dvA h hc, fun h => Dvd.dvd.add h hc⟩

  have prod_filter_Ioc_shift (Q : ℕ → Prop) [DecidablePred Q] (a L c : ℕ)
      (hshift : ∀ y, a < y → y ≤ a + L → (Q (y + c) ↔ Q y)) :
      ∏ y ∈ (Finset.Ioc (a+c) (a+c+L)).filter (fun y => Q y), y
        = ∏ y ∈ (Finset.Ioc a (a+L)).filter (fun y => Q y), (y + c) := by
    refine Finset.prod_nbij' (fun y => y - c) (fun y => y + c) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      dsimp only
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hy ⊢
      obtain ⟨⟨h1, h2⟩, hQ⟩ := hy
      refine ⟨by omega, ?_⟩
      have he : y - c + c = y := by omega
      rw [← (hshift (y - c) (by omega) (by omega))]
      rw [he]
      exact hQ
    · intro y hy
      dsimp only
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hy ⊢
      obtain ⟨⟨h1, h2⟩, hQ⟩ := hy
      refine ⟨by omega, (hshift y h1 h2).mpr hQ⟩
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hy
      dsimp only
      omega
    · intro y hy
      dsimp only
      omega
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hy
      dsimp only
      omega

  have prod_filter_Ioc_blocks (Q : ℕ → Prop) [DecidablePred Q] (a L : ℕ) (m : ℕ) (c : ℕ)
      (hshift : ∀ y i, i < m → a < y → y ≤ a + L → (Q (y + (c + i*L)) ↔ Q y)) :
      ∏ y ∈ (Finset.Ioc (a+c) (a+c+m*L)).filter (fun y => Q y), y
        = ∏ i ∈ Finset.range m, ∏ y ∈ (Finset.Ioc a (a+L)).filter (fun y => Q y), (y + (c + i*L)) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, ← ih (fun y i hi h1 h2 => hshift y i (by omega) h1 h2)]
      rw [Nat.succ_mul]
      have hsplit : Finset.Ioc (a+c) (a+c+(m*L+L))
          = Finset.Ioc (a+c) (a+c+m*L) ∪ Finset.Ioc (a+c+m*L) (a+c+(m*L+L)) := by
        rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)]
      have hdisj : Disjoint ((Finset.Ioc (a+c) (a+c+m*L)).filter (fun y => Q y))
          ((Finset.Ioc (a+c+m*L) (a+c+(m*L+L))).filter (fun y => Q y)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hx1 hx2
        omega
      rw [hsplit, Finset.filter_union, Finset.prod_union hdisj]
      congr 1
      have hb1 : a+c+m*L = a+(c+m*L) := by omega
      have hb2 : a+c+(m*L+L) = a+(c+m*L)+L := by omega
      rw [hb1, hb2]
      exact prod_filter_Ioc_shift Q a L (c+m*L)
        (fun y h1 h2 => hshift y m (by omega) h1 h2)

  have prod_Ioc_factorial (n : ℕ) : (∏ x ∈ Finset.Ioc 0 n, x) = n ! := by
    have h : Finset.Ioc 0 n = Finset.Ico 1 (n+1) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [h]
    exact Finset.prod_Ico_id_eq_factorial n

  obtain ⟨Ffree, Ffree_def⟩ : ∃ f : ℕ → ℕ → ℕ, f = fun (p M : ℕ) => ∏ j ∈ (Finset.Ioc 0 M).filter (fun j => ¬ p ∣ j), j := ⟨_, rfl⟩

  have Ffree_pos {M : ℕ} : 0 < Ffree p M := by
    simp only [Ffree_def]
    apply Finset.prod_pos
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hj
    omega

  have factorial_decomp (m : ℕ) : (m*p) ! = p^m * m ! * Ffree p (m*p) := by
    have hppos : 0 < p := hp.out.pos
    have hsplit := Finset.prod_filter_mul_prod_filter_not (Finset.Ioc 0 (m*p)) (fun j => p ∣ j)
      (fun j => j)
    have hdvd_part : ∏ j ∈ (Finset.Ioc 0 (m*p)).filter (fun j => p ∣ j), j
        = p^m * m ! := by
      have transfer : ∏ j ∈ (Finset.Ioc 0 (m*p)).filter (fun j => p ∣ j), j
          = ∏ k ∈ Finset.Ioc 0 m, (p*k) := by
        symm
        refine Finset.prod_nbij (fun k => p * k) ?_ ?_ ?_ ?_
        · intro k hk
          simp only [Finset.mem_Ioc] at hk
          simp only [Finset.mem_filter, Finset.mem_Ioc]
          refine ⟨⟨Nat.mul_pos hppos hk.1, ?_⟩, ⟨k, rfl⟩⟩
          calc p * k ≤ p * m := Nat.mul_le_mul_left p hk.2
            _ = m * p := Nat.mul_comm p m
        · intro k1 hk1 k2 hk2 he
          dsimp only at he
          exact Nat.eq_of_mul_eq_mul_left hppos he
        · intro j hj
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hj
          obtain ⟨⟨h0, hle⟩, k, hk⟩ := hj
          refine ⟨k, ?_, hk.symm⟩
          simp only [Finset.mem_coe, Finset.mem_Ioc]
          subst hk
          constructor
          · rcases Nat.eq_zero_or_pos k with h | h
            · subst h; omega
            · exact h
          · by_contra hcon
            push_neg at hcon
            have : p * m < p * k := (Nat.mul_lt_mul_left hppos).mpr hcon
            have hmp : m * p = p * m := Nat.mul_comm m p
            omega
        · intro k hk
          rfl
      rw [transfer, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ioc,
        prod_Ioc_factorial]
      simp
    calc (m*p) ! = ∏ j ∈ Finset.Ioc 0 (m*p), j := (prod_Ioc_factorial (m*p)).symm
      _ = (∏ j ∈ (Finset.Ioc 0 (m*p)).filter (fun j => p ∣ j), j)
          * ∏ j ∈ (Finset.Ioc 0 (m*p)).filter (fun j => ¬ p ∣ j), j := hsplit.symm
      _ = p^m * m ! * Ffree p (m*p) := by rw [hdvd_part]; simp only [Ffree_def]

  have Ffree_blocks {t : ℕ} (ht : 1 ≤ t) (m : ℕ) :
      Ffree p (m * p^t) = ∏ i ∈ Finset.range m, ∏ u ∈ US p t, (u + i*p^t) := by
    have hpP : p ∣ p^t := p_dvd_P t ht
    have h := prod_filter_Ioc_blocks (fun y => ¬ p ∣ y) 0 (p^t) m 0
      (fun y i hi h1 h2 => by
        apply not_congr
        apply dvd_add_iff_of_dvd
        rw [zero_add]
        exact Dvd.dvd.mul_left hpP i)
    simp only [zero_add] at h
    simp only [Ffree_def]
    rw [h]
    refine Finset.prod_congr rfl fun i hi => ?_
    refine Finset.prod_congr (by rw [US_def]) fun u hu => ?_
    rfl

  obtain ⟨Dfun, Dfun_def⟩ : ∃ f : ℕ → ℕ, f = fun (M : ℕ) => ∏ j ∈ Finset.range M, (M+1+2*j) := ⟨_, rfl⟩

  have Dfun_pos {M : ℕ} : 0 < Dfun M := by
    simp only [Dfun_def]
    apply Finset.prod_pos
    intro j hj
    omega

  obtain ⟨DstarP, DstarP_def⟩ : ∃ f : ℕ → ℕ → ℕ, f = fun (p M : ℕ) => ∏ j ∈ (Finset.range (M*p)).filter (fun j => ¬ p ∣ (M*p+1+2*j)), (M*p+1+2*j) := ⟨_, rfl⟩

  have Dstar_div_set (hp5 : 5 ≤ p) (M : ℕ) :
      (Finset.range (M*p)).filter (fun j => p ∣ (M*p+1+2*j))
        = (Finset.range M).image (fun k => (p-1)/2 + k*p) := by
    have hppos : 0 < p := hp.out.pos
    obtain ⟨q, hq⟩ : ∃ q, p = 2*q+1 := by
      have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two (by omega))
      exact ⟨p/2, by omega⟩
    have hq2 : (p-1)/2 = q := by omega
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, hdvd⟩
      have hMp : p ∣ M*p := Dvd.intro_left M rfl
      have h12j : p ∣ 1+2*j := by
        apply dvA (b := M*p)
        · have : 1+2*j + M*p = M*p+1+2*j := by ring
          rw [this]; exact hdvd
        · exact hMp
      obtain ⟨s, hs⟩ := h12j
      have hs2 : 1+2*j = 2*(q*s) + s := by
        rw [hs, hq]; ring
      obtain ⟨k, hk⟩ : ∃ k, s = 2*k+1 := ⟨s/2, by omega⟩
      have hps : p*s = 2*(k*p) + p := by rw [hk]; ring
      refine ⟨k, ?_, ?_⟩
      · rcases Nat.lt_or_ge k M with h | h
        · exact h
        · exfalso
          have : M*p ≤ k*p := Nat.mul_le_mul_right p h
          omega
      · rw [hq2]
        omega
    · rintro ⟨k, hk, rfl⟩
      have h1 : (k+1)*p ≤ M*p := Nat.mul_le_mul_right p (by omega)
      have h2 : (k+1)*p = k*p + p := by ring
      have hexp : p*(M+1+2*k) = M*p + p + 2*(k*p) := by ring
      refine ⟨by omega, ⟨M+1+2*k, by rw [hexp]; omega⟩⟩

  have Dstar_div_injOn (M : ℕ) (hppos : 0 < p) :
      Set.InjOn (fun k => (p-1)/2 + k*p) (Finset.range M) := by
    intro k1 _ k2 _ he
    dsimp only at he
    have : k1 * p = k2 * p := by omega
    exact Nat.eq_of_mul_eq_mul_right hppos this

  have Dstar_div_card (hp5 : 5 ≤ p) (M : ℕ) :
      ((Finset.range (M*p)).filter (fun j => p ∣ (M*p+1+2*j))).card = M := by
    rw [Dstar_div_set hp5 M, Finset.card_image_of_injOn (Dstar_div_injOn M hp.out.pos),
      Finset.card_range]

  have DstarP_card (hp5 : 5 ≤ p) (M : ℕ) :
      ((Finset.range (M*p)).filter (fun j => ¬ p ∣ (M*p+1+2*j))).card = M*p - M := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.range (M*p)) (p := fun j => p ∣ (M*p+1+2*j))
    rw [Dstar_div_card hp5 M, Finset.card_range] at hsplit
    omega

  have Dfun_decomp (hp5 : 5 ≤ p) (M : ℕ) :
      Dfun (M*p) = p^M * Dfun M * DstarP p M := by
    have hppos : 0 < p := hp.out.pos
    obtain ⟨q, hq⟩ : ∃ q, p = 2*q+1 := by
      have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two (by omega))
      exact ⟨p/2, by omega⟩
    have hq2 : (p-1)/2 = q := by omega
    have hsplit := Finset.prod_filter_mul_prod_filter_not (Finset.range (M*p))
      (fun j => p ∣ (M*p+1+2*j)) (fun j => M*p+1+2*j)
    have hdvd_part : ∏ j ∈ (Finset.range (M*p)).filter (fun j => p ∣ (M*p+1+2*j)), (M*p+1+2*j)
        = p^M * Dfun M := by
      rw [Dstar_div_set hp5 M, Finset.prod_image (Dstar_div_injOn M hppos)]
      have hval : ∀ k ∈ Finset.range M, M*p+1+2*((p-1)/2 + k*p) = p*(M+1+2*k) := by
        intro k hk
        have hexp : p*(M+1+2*k) = M*p + p + 2*(k*p) := by ring
        rw [hexp, hq2]
        omega
      rw [Finset.prod_congr rfl hval, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_range]
      simp only [Dfun_def]
    calc Dfun (M*p) = (∏ j ∈ (Finset.range (M*p)).filter (fun j => p ∣ (M*p+1+2*j)), (M*p+1+2*j))
          * ∏ j ∈ (Finset.range (M*p)).filter (fun j => ¬ p ∣ (M*p+1+2*j)), (M*p+1+2*j) := by simp only [Dfun_def]; exact hsplit.symm
      _ = p^M * Dfun M * DstarP p M := by rw [hdvd_part]; simp only [Dfun_def, DstarP_def]

  have DstarP_even (_hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) {m M : ℕ} (hM : M*p = m * p^t)
      (hMp2 : 2 ∣ M*p) :
      DstarP p M = ∏ i ∈ Finset.range m, ∏ y ∈ OSet p t, (y + (M*p + i*(2*p^t))) := by
    have hppos : 0 < p := hp.out.pos
    have hpP : p ∣ p^t := p_dvd_P t ht
    have step1 : DstarP p M
        = ∏ y ∈ (Finset.Ioc (M*p) (M*p + M*p*2)).filter (fun y => ¬ p ∣ y ∧ ¬ 2 ∣ y), y := by
      simp only [DstarP_def]
      refine Finset.prod_nbij (fun j => M*p+1+2*j) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hj ⊢
        obtain ⟨hjr, hnd⟩ := hj
        exact ⟨by omega, hnd, by omega⟩
      · intro j1 _ j2 _ he
        dsimp only at he
        omega
      · intro y hy
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hy
        obtain ⟨⟨h1, h2⟩, hnd, hodd⟩ := hy
        simp only [Set.mem_image, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        refine ⟨(y - M*p - 1)/2, ⟨by omega, ?_⟩, by omega⟩
        have he : M*p+1+2*((y - M*p - 1)/2) = y := by omega
        rw [he]
        exact hnd
      · intro j hj
        rfl
    have hshift : ∀ y i, i < m → 0 < y → y ≤ 0 + 2*p^t →
        ((¬ p ∣ (y + (M*p + i*(2*p^t))) ∧ ¬ 2 ∣ (y + (M*p + i*(2*p^t))))
          ↔ (¬ p ∣ y ∧ ¬ 2 ∣ y)) := by
      intro y i _ _ _
      have hpc : p ∣ M*p + i*(2*p^t) := by
        apply Dvd.dvd.add (Dvd.intro_left M rfl)
        exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hpP 2) i
      have h2c : 2 ∣ M*p + i*(2*p^t) := by
        apply Dvd.dvd.add hMp2
        exact Dvd.dvd.mul_left ⟨p^t, rfl⟩ i
      rw [not_congr ((Nat.dvd_add_iff_left hpc).symm), not_congr ((Nat.dvd_add_iff_left h2c).symm)]
    have step2 := prod_filter_Ioc_blocks (fun y => ¬ p ∣ y ∧ ¬ 2 ∣ y) 0 (2*p^t) m (M*p) hshift
    simp only [zero_add] at step2
    have harg : m*(2*p^t) = M*p*2 := by
      calc m*(2*p^t) = (m*p^t)*2 := by ring
        _ = M*p*2 := by rw [hM]
    rw [harg] at step2
    rw [step1, step2]
    simp only [OSet_def]

  have A_sub_h_eq (hp5 : 5 ≤ p) {t : ℕ} (_ht : 1 ≤ t) {m M A : ℕ} (hM : M*p = m * p^t)
      (hA : 2*A + 1 = M*p) (hmodd : ¬ 2 ∣ m) :
      A - p^t/2 = ((m-1)/2) * p^t := by
    have hp2 : p ≠ 2 := pn2 hp5
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    have hm1 : 1 ≤ m := by
      by_contra h
      push_neg at h
      interval_cases m
      rw [Nat.zero_mul] at hM
      omega
    have hmm : (m-1)*p^t + p^t = m*p^t := by
      have h1 : (m-1)+1 = m := by omega
      calc (m-1)*p^t + p^t = ((m-1)+1)*p^t := by ring
        _ = m*p^t := by rw [h1]
    have hme : 2*((m-1)/2) = m-1 := by omega
    have hhalf : 2*(((m-1)/2)*p^t) = (m-1)*p^t := by
      calc 2*(((m-1)/2)*p^t) = (2*((m-1)/2))*p^t := by ring
        _ = (m-1)*p^t := by rw [hme]
    omega

  have DstarP_odd (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) {m M A : ℕ} (hM : M*p = m * p^t)
      (hA : 2*A + 1 = M*p) (hmodd : ¬ 2 ∣ m) :
      DstarP p M = 2^(M*p - M)
        * ∏ i ∈ Finset.range m, ∏ v ∈ WSet p t, (v + ((A - p^t/2) + i*p^t)) := by
    have hppos : 0 < p := hp.out.pos
    have hp2 : p ≠ 2 := pn2 hp5
    have hpP : p ∣ p^t := p_dvd_P t ht
    have hP2 : 2 * (p^t/2) + 1 = p^t := thA hp2 t
    have hAh : A - p^t/2 = ((m-1)/2) * p^t := A_sub_h_eq hp5 ht hM hA hmodd
    have hm1 : 1 ≤ m := by
      by_contra h
      push_neg at h
      interval_cases m
      rw [Nat.zero_mul] at hM
      omega
    have hPle : p^t ≤ m*p^t := Nat.le_mul_of_pos_left _ (by omega)
    have hhA : p^t/2 ≤ A := by omega
    have hfilter : (Finset.range (M*p)).filter (fun j => ¬ p ∣ (M*p+1+2*j))
        = (Finset.range (M*p)).filter (fun j => ¬ p ∣ (A+1+j)) := by
      apply Finset.filter_congr
      intro j _
      have hval : M*p+1+2*j = 2*(A+1+j) := by omega
      rw [hval]
      constructor
      · intro h hc
        exact h (Dvd.dvd.mul_left hc 2)
      · intro h hc
        rcases (Nat.Prime.dvd_mul hp.out).1 hc with h2 | h2
        · have := Nat.le_of_dvd (by norm_num) h2; omega
        · exact h h2
    have stepa : DstarP p M
        = 2^(M*p - M) * ∏ j ∈ (Finset.range (M*p)).filter (fun j => ¬ p ∣ (A+1+j)), (A+1+j) := by
      simp only [DstarP_def]
      rw [hfilter]
      have hval : ∀ j ∈ (Finset.range (M*p)).filter (fun j => ¬ p ∣ (A+1+j)),
          M*p+1+2*j = 2*(A+1+j) := by
        intro j _
        omega
      rw [Finset.prod_congr rfl hval, Finset.prod_mul_distrib, Finset.prod_const]
      congr 2
      rw [← hfilter]
      exact DstarP_card hp5 M
    have stepb : ∏ j ∈ (Finset.range (M*p)).filter (fun j => ¬ p ∣ (A+1+j)), (A+1+j)
        = ∏ v ∈ (Finset.Ioc A (A + M*p)).filter (fun v => ¬ p ∣ v), v := by
      refine Finset.prod_nbij (fun j => A+1+j) ?_ ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hj ⊢
        exact ⟨by omega, hj.2⟩
      · intro j1 _ j2 _ he
        dsimp only at he
        omega
      · intro v hv
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hv
        obtain ⟨⟨h1, h2⟩, hnd⟩ := hv
        simp only [Set.mem_image, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
        refine ⟨v - A - 1, ⟨by omega, ?_⟩, by omega⟩
        have he : A+1+(v - A - 1) = v := by omega
        rw [he]
        exact hnd
      · intro j hj
        rfl
    have hshift : ∀ v i, i < m → p^t/2 < v → v ≤ p^t/2 + p^t →
        ((¬ p ∣ (v + ((A - p^t/2) + i*p^t))) ↔ (¬ p ∣ v)) := by
      intro v i _ _ _
      have hpc : p ∣ (A - p^t/2) + i*p^t := by
        apply Dvd.dvd.add
        · rw [hAh]
          exact Dvd.dvd.mul_left hpP ((m-1)/2)
        · exact Dvd.dvd.mul_left hpP i
      exact not_congr ((Nat.dvd_add_iff_left hpc).symm)
    have stepc := prod_filter_Ioc_blocks (fun v => ¬ p ∣ v) (p^t/2) (p^t) m (A - p^t/2) hshift
    have hb1 : p^t/2 + (A - p^t/2) = A := by omega
    have hb2 : A + m*p^t = A + M*p := by rw [hM]
    rw [hb1, hb2] at stepc
    rw [stepa, stepb, stepc]
    simp only [WSet_def]




  obtain ⟨qnum, qnum_def⟩ : ∃ f : ℕ → ℕ, f = fun (m : ℕ) => 2^(3*m) * (2*m) ! * Dfun (3*m) := ⟨_, rfl⟩

  obtain ⟨qden, qden_def⟩ : ∃ f : ℕ → ℕ, f = fun (m : ℕ) => (4*m) ! * m ! := ⟨_, rfl⟩

  have qnum_pos (m : ℕ) : 0 < qnum m := by
    simp only [qnum_def]
    exact Nat.mul_pos (Nat.mul_pos (pow_pos (by norm_num) _) (Nat.factorial_pos _)) Dfun_pos

  have qden_pos (m : ℕ) : 0 < qden m := by
    simp only [qden_def]
    exact Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)

  obtain ⟨qp, qp_def⟩ : ∃ f : ℕ → ℚ_[p], f = fun (m : ℕ) => (qnum m : ℚ_[p]) / (qden m : ℚ_[p]) := ⟨_, rfl⟩

  have qp_ne_zero (m : ℕ) : qp m ≠ 0 := by
    simp only [qp_def]
    apply div_ne_zero
    · exact Nat.cast_ne_zero.mpr (qnum_pos m).ne'
    · exact Nat.cast_ne_zero.mpr (qden_pos m).ne'

  have qnum_decomp (hp5 : 5 ≤ p) (N : ℕ) :
      qnum (N*p) = qnum N * (2^(3*N*(p-1)) * Ffree p (2*(N*p)) * DstarP p (3*N)) * p^(5*N) := by
    have hppos : 0 < p := hp.out.pos
    have e1 : 3*(N*p) = (3*N)*p := by ring
    have e2 : 2*(N*p) = (2*N)*p := by ring
    have hms : N*(p-1) = N*p - N := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have hms3 : 3*N*(p-1) = 3*(N*(p-1)) := by ring
    have hle : N ≤ N*p := Nat.le_mul_of_pos_right N hppos
    have e3 : (3*N)*p = 3*N + 3*N*(p-1) := by
      rw [hms3, hms]
      have : (3*N)*p = 3*(N*p) := by ring
      omega
    simp only [qnum_def]
    rw [e1, Dfun_decomp hp5 (3*N), e3, pow_add, e2, factorial_decomp (2*N)]
    ring

  have qden_decomp (N : ℕ) :
      qden (N*p) = qden N * (Ffree p (4*(N*p)) * Ffree p (N*p)) * p^(5*N) := by
    have e1 : 4*(N*p) = (4*N)*p := by ring
    simp only [qden_def]
    rw [e1, factorial_decomp (4*N), factorial_decomp N]
    ring

  have qp_ratio (hp5 : 5 ≤ p) (N : ℕ) :
      qp (N*p) = qp N * ((2:ℚ_[p])^(3*N*(p-1)) * (Ffree p (2*(N*p)) : ℚ_[p])
        * (DstarP p (3*N) : ℚ_[p])
        / ((Ffree p (4*(N*p)) : ℚ_[p]) * (Ffree p (N*p) : ℚ_[p]))) := by
    have hnum := congrArg (fun k : ℕ => (k : ℚ_[p])) (qnum_decomp hp5 N)
    have hden := congrArg (fun k : ℕ => (k : ℚ_[p])) (qden_decomp N)
    push_cast at hnum hden
    simp only [qp_def]
    rw [hnum, hden]
    have h1 : ((qden N : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (qden_pos N).ne'
    have h2 : ((Ffree p (4*(N*p)) : ℕ) : ℚ_[p]) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Ffree_pos).ne'
    have h3 : ((Ffree p (N*p) : ℕ) : ℚ_[p]) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Ffree_pos).ne'
    have h4 : ((p:ℚ_[p]))^(5*N) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
    field_simp

  have prod_shift_split (V : Finset ℕ) (hV : ∀ v ∈ V, ¬ p ∣ v) (Δ : ℕ) :
      (∏ v ∈ V, ((v + Δ : ℕ) : ℚ_[p]))
        = (∏ v ∈ V, (v:ℚ_[p])) * ∏ v ∈ V, (((v + Δ:ℕ):ℚ_[p])/(v:ℚ_[p])) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [mul_comm, div_mul_cancel₀ _ (nuz (hV v hv))]

  have prod_blocks_eq (V : Finset ℕ) (hV : ∀ v ∈ V, ¬ p ∣ v) (m : ℕ) (Δ : ℕ → ℕ) :
      (∏ i ∈ Finset.range m, ∏ v ∈ V, ((v + Δ i : ℕ) : ℚ_[p]))
        = (∏ v ∈ V, (v:ℚ_[p]))^m
          * ∏ i ∈ Finset.range m, ∏ v ∈ V, (((v + Δ i : ℕ):ℚ_[p]) / (v:ℚ_[p])) := by
    have h1 : ∀ i ∈ Finset.range m, (∏ v ∈ V, ((v + Δ i : ℕ) : ℚ_[p]))
        = (∏ v ∈ V, (v:ℚ_[p])) * ∏ v ∈ V, (((v + Δ i:ℕ):ℚ_[p])/(v:ℚ_[p])) :=
      fun i _ => prod_shift_split V hV (Δ i)
    rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

  have blocks_near (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) (V : Finset ℕ)
      (hV : ∀ v ∈ V, ¬ p ∣ v)
      (h1 : ‖∑ v ∈ V, ((v:ℚ_[p]))⁻¹‖ ≤ pe p (2*t))
      (h2 : ‖∑ v ∈ V, ((v:ℚ_[p])^2)⁻¹‖ ≤ pe p t)
      (m : ℕ) (Δ : ℕ → ℕ) (hΔ : ∀ i, i < m → p^t ∣ Δ i) :
      Near (3*t) (∏ i ∈ Finset.range m, ∏ v ∈ V, (((v + Δ i : ℕ):ℚ_[p]) / (v:ℚ_[p]))) :=
    Near_prod fun i hi =>
      window_block_near hp5 ht V hV h1 h2 (Δ i) (hΔ i (Finset.mem_range.1 hi))

  have even_algebra (c O U Y B2 B0 B4 B1 : ℚ_[p]) (n : ℕ)
      (hU : U ≠ 0) (hBlP : c * O = U * Y) :
      c^(3*n) * (U^(2*n) * B2) * (O^(3*n) * B0) / ((U^(4*n) * B4) * (U^n * B1))
        = Y^(3*n) * B2 * B0 / (B4 * B1) := by
    have hmp : c^(3*n) * O^(3*n) = U^(3*n) * Y^(3*n) := by
      rw [← mul_pow, ← mul_pow, hBlP]
    have hnum : c^(3*n) * (U^(2*n) * B2) * (O^(3*n) * B0)
        = U^(5*n) * (Y^(3*n) * B2 * B0) := by
      calc c^(3*n) * (U^(2*n) * B2) * (O^(3*n) * B0)
          = (c^(3*n) * O^(3*n)) * (U^(2*n) * (B2 * B0)) := by ring
        _ = (U^(3*n) * Y^(3*n)) * (U^(2*n) * (B2 * B0)) := by rw [hmp]
        _ = U^(5*n) * (Y^(3*n) * B2 * B0) := by ring
    have hden : (U^(4*n) * B4) * (U^n * B1) = U^(5*n) * (B4 * B1) := by ring
    rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero _ hU)]

  have odd_algebra (c2 U W Y B2 BW B4 B1 : ℚ_[p]) (n e1 e2 c : ℕ)
      (hU : U ≠ 0) (hbW : W = U * Y)
      (hpow : c2^e1 * c2^e2 = (c2^(4*c))^(3*n)) :
      c2^e1 * (U^(2*n) * B2) * (c2^e2 * (W^(3*n) * BW)) / ((U^(4*n) * B4) * (U^n * B1))
        = (c2^(4*c) * Y)^(3*n) * B2 * BW / (B4 * B1) := by
    have hnum : c2^e1 * (U^(2*n) * B2) * (c2^e2 * (W^(3*n) * BW))
        = U^(5*n) * ((c2^(4*c) * Y)^(3*n) * B2 * BW) := by
      calc c2^e1 * (U^(2*n) * B2) * (c2^e2 * (W^(3*n) * BW))
          = (c2^e1 * c2^e2) * (U^(2*n) * W^(3*n) * (B2 * BW)) := by ring
        _ = ((c2^(4*c))^(3*n)) * (U^(2*n) * (U*Y)^(3*n) * (B2 * BW)) := by rw [hpow, hbW]
        _ = U^(5*n) * ((c2^(4*c) * Y)^(3*n) * B2 * BW) := by rw [mul_pow, mul_pow]; ring
    have hden : (U^(4*n) * B4) * (U^n * B1) = U^(5*n) * (B4 * B1) := by ring
    rw [hnum, hden, mul_div_mul_left _ _ (pow_ne_zero _ hU)]

  have U_blocks_near (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) (m : ℕ) :
      Near (3*t) (∏ i ∈ Finset.range m, ∏ u ∈ US p t,
        (((u + i*p^t : ℕ):ℚ_[p]) / (u:ℚ_[p]))) :=
    blocks_near hp5 ht _ (fun _ hu => (mUS.1 hu).2) (sumU1_bound hp5 ht)
      (sumU2_bound hp5 ht) _ _ (fun i _ => Dvd.dvd.mul_left dvd_rfl i)

  have castF_gen (_hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) (k : ℕ) :
      ((Ffree p (k * p^t) : ℕ) : ℚ_[p])
        = (∏ u ∈ US p t, (u:ℚ_[p]))^k * ∏ i ∈ Finset.range k, ∏ u ∈ US p t,
          (((u + i*p^t : ℕ):ℚ_[p]) / (u:ℚ_[p])) := by
    rw [Ffree_blocks ht k, Nat.cast_prod,
      Finset.prod_congr rfl (fun i (_ : i ∈ Finset.range k) => Nat.cast_prod _ _)]
    exact prod_blocks_eq (US p t) (fun u hu => (mUS.1 hu).2) k (fun i => i*p^t)

  have Y_near (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      Near (3*t) (∏ u ∈ US p t, (((u + p^t : ℕ):ℚ_[p]) / (u:ℚ_[p]))) :=
    window_block_near hp5 ht (US p t) (fun _ hu => (mUS.1 hu).2)
      (sumU1_bound hp5 ht) (sumU2_bound hp5 ht) (p^t) dvd_rfl

  have BlP_cast (hp5 : 5 ≤ p) {t : ℕ} (ht : 1 ≤ t) :
      (2:ℚ_[p])^((US p t).card) * (∏ y ∈ OSet p t, (y:ℚ_[p]))
        = (∏ u ∈ US p t, (u:ℚ_[p]))
          * ∏ u ∈ US p t, (((u + p^t : ℕ):ℚ_[p]) / (u:ℚ_[p])) := by
    have h := congrArg (fun k : ℕ => (k : ℚ_[p])) (prod_BlP_eq hp5 ht)
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_prod] at h
    rw [← h]
    exact prod_shift_split (US p t) (fun u hu => (mUS.1 hu).2) (p^t)

  have U0_ne_zero {t : ℕ} : (∏ u ∈ US p t, (u:ℚ_[p])) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun _ hu => nuz ((mUS.1 hu).2))

  have exp_key (hp5 : 5 ≤ p) {n r N : ℕ} (hr : 1 ≤ r) (hN : N = n*p^(r-1))
      (hNp : N*p = n*p^r) :
      N*p - N = n * (US p r).card := by
    rw [card_USet hp5 hr, Nat.mul_sub_left_distrib, ← hNp, ← hN]

  have R_near_even (hp5 : 5 ≤ p) {n r N : ℕ} (_hn : 1 ≤ n) (hr : 1 ≤ r)
      (hN : N = n*p^(r-1)) (hn2 : 2 ∣ n) :
      Near (3*r) ((2:ℚ_[p])^(3*N*(p-1)) * (Ffree p (2*(N*p)) : ℚ_[p])
        * (DstarP p (3*N) : ℚ_[p])
        / ((Ffree p (4*(N*p)) : ℚ_[p]) * (Ffree p (N*p) : ℚ_[p]))) := by
    have hppos : 0 < p := hp.out.pos
    have hNp : N*p = n*p^r := by
      rw [hN, mul_assoc, ← pow_succ]
      congr 2
      omega
    have hOv : ∀ y ∈ OSet p r, ¬ p ∣ y := fun y hy => (mem_OSet.1 hy).2.1
    have hd3Np : (p:ℕ)^r ∣ 3*N*p := ⟨3*n, by rw [mul_assoc, hNp]; ring⟩
    have hB0 : Near (3*r) (∏ i ∈ Finset.range (3*n), ∏ y ∈ OSet p r,
        (((y + (3*N*p + i*(2*p^r)) : ℕ):ℚ_[p]) / (y:ℚ_[p]))) :=
      blocks_near hp5 hr _ hOv (sumO1_bound hp5 hr) (sumO2_bound hp5 hr) _ _
        (fun i _ => Dvd.dvd.add hd3Np ⟨2*i, by ring⟩)
    have hDsn : DstarP p (3*N) = ∏ i ∈ Finset.range (3*n), ∏ y ∈ OSet p r,
        (y + (3*N*p + i*(2*p^r))) := by
      have hM : (3*N)*p = (3*n)*p^r := by rw [mul_assoc, hNp]; ring
      have hMp2 : 2 ∣ (3*N)*p := by
        have hN2 : 2 ∣ N := by rw [hN]; exact Dvd.dvd.mul_right hn2 _
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hN2 3) p
      exact DstarP_even hp5 hr hM hMp2
    have castDs : ((DstarP p (3*N) : ℕ) : ℚ_[p])
        = (∏ y ∈ OSet p r, (y:ℚ_[p]))^(3*n) * ∏ i ∈ Finset.range (3*n), ∏ y ∈ OSet p r,
          (((y + (3*N*p + i*(2*p^r)) : ℕ):ℚ_[p]) / (y:ℚ_[p])) := by
      rw [hDsn, Nat.cast_prod, Finset.prod_congr rfl (fun i _ => Nat.cast_prod _ _)]
      exact prod_blocks_eq (OSet p r) hOv (3*n) (fun i => 3*N*p + i*(2*p^r))
    have hexp : 3*N*(p-1) = (US p r).card * (3*n) := by
      rw [mul_assoc 3 N (p-1), Nat.mul_sub_left_distrib, Nat.mul_one,
        exp_key hp5 hr hN hNp]
      ring
    have hpow : (2:ℚ_[p])^(3*N*(p-1)) = ((2:ℚ_[p])^((US p r).card))^(3*n) := by
      rw [← pow_mul, hexp]
    rw [show 2*(N*p) = (2*n)*p^r from by rw [hNp]; ring,
      show 4*(N*p) = (4*n)*p^r from by rw [hNp]; ring, hNp,
      castF_gen hp5 hr (2*n), castF_gen hp5 hr (4*n), castF_gen hp5 hr n,
      castDs, hpow, even_algebra _ _ _ _ _ _ _ _ n U0_ne_zero (BlP_cast hp5 hr)]
    exact Near_div (by omega) (Near_mul (Near_mul (Near_pow (Y_near hp5 hr) (3*n))
      (U_blocks_near hp5 hr (2*n))) hB0)
      (Near_mul (U_blocks_near hp5 hr (4*n)) (U_blocks_near hp5 hr n))

  have R_near_odd (hp5 : 5 ≤ p) {n r N : ℕ} (_hn : 1 ≤ n) (hr : 1 ≤ r)
      (hN : N = n*p^(r-1)) (hn2 : ¬ 2 ∣ n) :
      Near (3*r) ((2:ℚ_[p])^(3*N*(p-1)) * (Ffree p (2*(N*p)) : ℚ_[p])
        * (DstarP p (3*N) : ℚ_[p])
        / ((Ffree p (4*(N*p)) : ℚ_[p]) * (Ffree p (N*p) : ℚ_[p]))) := by
    have hppos : 0 < p := hp.out.pos
    have hpodd : ¬ 2 ∣ p := by
      intro h
      have h2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp h
      omega
    have hNp : N*p = n*p^r := by
      rw [hN, mul_assoc, ← pow_succ]
      congr 2
      omega
    have hWv : ∀ v ∈ WSet p r, ¬ p ∣ v := fun v hv => (mem_WSet.1 hv).2
    have hHv : ∀ d ∈ HS p r, ¬ p ∣ d := fun d hd => (mHS.1 hd).2
    have hmodd3 : ¬ 2 ∣ 3*n := by
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h2 | h2
      · have := Nat.le_of_dvd (by norm_num) h2; omega
      · exact hn2 h2
    have hM : (3*N)*p = (3*n)*p^r := by rw [mul_assoc, hNp]; ring
    have hA : 2*((3*N*p - 1)/2) + 1 = (3*N)*p := by
      have hNodd : ¬ 2 ∣ N := by
        rw [hN]
        intro h
        rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h2 | h2
        · exact hn2 h2
        · exact hpodd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2)
      have h3Npodd : ¬ 2 ∣ 3*N*p := by
        intro h
        rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h2 | h2
        · rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h3 | h3
          · have := Nat.le_of_dvd (by norm_num) h3; omega
          · exact hNodd h3
        · exact hpodd h2
      omega
    have hAh : (3*N*p - 1)/2 - p^r/2 = ((3*n-1)/2) * p^r :=
      A_sub_h_eq hp5 hr hM hA hmodd3
    have hBW : Near (3*r) (∏ i ∈ Finset.range (3*n), ∏ v ∈ WSet p r,
        (((v + (((3*N*p - 1)/2 - p^r/2) + i*p^r) : ℕ):ℚ_[p]) / (v:ℚ_[p]))) :=
      blocks_near hp5 hr _ hWv (sumW1_bound hp5 hr) (sumW2_bound hp5 hr) _ _
        (fun i _ => Dvd.dvd.add (by rw [hAh]; exact Dvd.dvd.mul_left dvd_rfl _)
          (Dvd.dvd.mul_left dvd_rfl i))
    have hDsn : DstarP p (3*N) = 2^((3*N)*p - 3*N)
        * ∏ i ∈ Finset.range (3*n), ∏ v ∈ WSet p r,
          (v + (((3*N*p - 1)/2 - p^r/2) + i*p^r)) :=
      DstarP_odd hp5 hr hM hA hmodd3
    have castDs : ((DstarP p (3*N) : ℕ) : ℚ_[p])
        = (2:ℚ_[p])^((3*N)*p - 3*N)
          * ((∏ v ∈ WSet p r, (v:ℚ_[p]))^(3*n) * ∏ i ∈ Finset.range (3*n), ∏ v ∈ WSet p r,
            (((v + (((3*N*p - 1)/2 - p^r/2) + i*p^r) : ℕ):ℚ_[p]) / (v:ℚ_[p]))) := by
      rw [hDsn, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_prod,
        Finset.prod_congr rfl (fun i (_ : i ∈ Finset.range (3*n)) => Nat.cast_prod _ _),
        prod_blocks_eq (WSet p r) hWv (3*n) (fun i => ((3*N*p - 1)/2 - p^r/2) + i*p^r)]
    have hbW : (∏ v ∈ WSet p r, (v:ℚ_[p]))
        = (∏ u ∈ US p r, (u:ℚ_[p]))
          * ∏ d ∈ HS p r, (((d + p^r : ℕ):ℚ_[p]) / (d:ℚ_[p])) := by
      have castW := congrArg (fun k : ℕ => (k : ℚ_[p])) (prod_WSet_eq hp5 hr)
      have castU := congrArg (fun k : ℕ => (k : ℚ_[p])) (prod_USet_split (t := r))
      simp only [Nat.cast_mul, Nat.cast_prod] at castW castU
      rw [castW, castU, prod_shift_split (HS p r) hHv (p^r)]
      ring
    have hexp : 3*N*(p-1) + ((3*N)*p - 3*N) = (4*(HS p r).card) * (3*n) := by
      rw [mul_assoc 3 N (p-1), Nat.mul_sub_left_distrib, Nat.mul_one,
        exp_key hp5 hr hN hNp, mul_assoc 3 N p, ← Nat.mul_sub_left_distrib,
        exp_key hp5 hr hN hNp, card_USet_double hp5 hr]
      ring
    have hpow : (2:ℚ_[p])^(3*N*(p-1)) * (2:ℚ_[p])^((3*N)*p - 3*N)
        = (((2:ℚ_[p])^(4*(HS p r).card))^(3*n)) := by
      rw [← pow_add, hexp, pow_mul]
    rw [show 2*(N*p) = (2*n)*p^r from by rw [hNp]; ring,
      show 4*(N*p) = (4*n)*p^r from by rw [hNp]; ring, hNp,
      castF_gen hp5 hr (2*n), castF_gen hp5 hr (4*n), castF_gen hp5 hr n, castDs,
      odd_algebra _ _ _ _ _ _ _ _ n (3*N*(p-1)) ((3*N)*p - 3*N) ((HS p r).card)
        U0_ne_zero hbW hpow]
    exact Near_div (by omega) (Near_mul (Near_mul (Near_pow (X_near hp5 hr) (3*n))
      (U_blocks_near hp5 hr (2*n))) hBW)
      (Near_mul (U_blocks_near hp5 hr (4*n)) (U_blocks_near hp5 hr n))

  have ratio_near (hp5 : 5 ≤ p) {n r N : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r)
      (hN : N = n*p^(r-1)) :
      Near (3*r) (qp (N*p) / qp N) := by
    rw [qp_ratio hp5 N, mul_div_cancel_left₀ _ (qp_ne_zero N)]
    by_cases hn2 : 2 ∣ n
    · exact R_near_even hp5 hn hr hN hn2
    · exact R_near_odd hp5 hn hr hN hn2

  have int_dvd_of_qp (hp5 : 5 ≤ p) {n r N : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r)
      (hN : N = n*p^(r-1)) {A B : ℤ}
      (hA : (A : ℚ_[p]) = qp (N*p)) (hB : (B : ℚ_[p]) = qp N) :
      ((p:ℤ)^(3*r)) ∣ (A - B) := by
    have hnear : ‖qp (N*p) / qp N - 1‖ ≤ pe p (3*r) := by
      simpa only [Near_def] using ratio_near hp5 hn hr hN
    have hBnorm : ‖qp N‖ ≤ 1 := by rw [← hB]; exact Padic.norm_int_le_one B
    have hqne : qp N ≠ 0 := qp_ne_zero N
    have hcancel : qp N * (qp (N*p) / qp N) = qp (N*p) := by
      field_simp
    have hdiff : (A:ℚ_[p]) - (B:ℚ_[p]) = qp N * (qp (N*p) / qp N - 1) := by
      rw [hA, hB, mul_sub, mul_one, hcancel]
    have hnorm : ‖((A - B : ℤ) : ℚ_[p])‖ ≤ pe p (3*r) := by
      push_cast
      rw [hdiff, norm_mul]
      calc ‖qp N‖ * ‖qp (N*p)/qp N - 1‖ ≤ 1 * pe p (3*r) :=
            mul_le_mul hBnorm hnear (norm_nonneg _) zero_le_one
        _ = pe p (3*r) := one_mul _
    simp only [pe_def] at hnorm
    exact (Padic.norm_int_le_pow_iff_dvd _ _).mp hnorm



  have Gamma_shift (x : ℝ) (hx : 0 < x) (k : ℕ) :
      Real.Gamma (x + k) = Real.Gamma x * ∏ j ∈ Finset.range k, (x + j) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hxk : (0:ℝ) < x + k := by positivity
      have h1 : (x + ((k+1 : ℕ):ℝ)) = (x + k) + 1 := by push_cast; ring
      rw [h1, Real.Gamma_add_one (ne_of_gt hxk), ih, Finset.prod_range_succ]
      ring

  have prod_half (M : ℕ) :
      ∏ j ∈ Finset.range M, ((M:ℝ)/2 + 1/2 + j) = (Dfun M : ℝ) / 2^M := by
    have h : ∀ j ∈ Finset.range M, (M:ℝ)/2 + 1/2 + j = ((M+1+2*j : ℕ):ℝ)/2 := by
      intro j _
      push_cast
      ring
    rw [Finset.prod_congr rfl h, Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    simp only [Dfun_def, Nat.cast_prod]

  have a_eq_q (m : ℕ) :
      (Real.Gamma (9*(m:ℝ)+1) * Real.Gamma (2*(m:ℝ)+1) * Real.Gamma (3/2*(m:ℝ)+1)) /
        (Real.Gamma (9/2*(m:ℝ)+1) * Real.Gamma (4*(m:ℝ)+1) * Real.Gamma (3*(m:ℝ)+1)
          * Real.Gamma ((m:ℝ)+1))
        = (qnum m : ℝ) / (qden m : ℝ) := by
    have hspos : (0:ℝ) < ((3*m:ℕ):ℝ)/2 + 1/2 := by positivity
    have hG9 : Real.Gamma (9*(m:ℝ)+1) = ((9*m) ! : ℝ) := by
      rw [show 9*(m:ℝ)+1 = ((9*m:ℕ):ℝ)+1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
    have hG2 : Real.Gamma (2*(m:ℝ)+1) = ((2*m) ! : ℝ) := by
      rw [show 2*(m:ℝ)+1 = ((2*m:ℕ):ℝ)+1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
    have hG4 : Real.Gamma (4*(m:ℝ)+1) = ((4*m) ! : ℝ) := by
      rw [show 4*(m:ℝ)+1 = ((4*m:ℕ):ℝ)+1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
    have hG3 : Real.Gamma (3*(m:ℝ)+1) = ((3*m) ! : ℝ) := by
      rw [show 3*(m:ℝ)+1 = ((3*m:ℕ):ℝ)+1 by push_cast; ring, Real.Gamma_nat_eq_factorial]
    have hG1 : Real.Gamma ((m:ℝ)+1) = (m ! : ℝ) := by
      rw [show (m:ℝ)+1 = ((m:ℕ):ℝ)+1 from rfl, Real.Gamma_nat_eq_factorial]
    have hdup1 := Real.Gamma_mul_Gamma_add_half (((3*m:ℕ):ℝ)/2 + 1/2)
    have he1 : ((3*m:ℕ):ℝ)/2 + 1/2 + 1/2 = 3/2*(m:ℝ)+1 := by push_cast; ring
    have he2 : 2*(((3*m:ℕ):ℝ)/2 + 1/2) = ((3*m:ℕ):ℝ)+1 := by ring
    have he3 : (2:ℝ)^(1 - 2*(((3*m:ℕ):ℝ)/2 + 1/2)) = ((2:ℝ)^(3*m))⁻¹ := by
      rw [show 1 - 2*(((3*m:ℕ):ℝ)/2 + 1/2) = -((3*m:ℕ):ℝ) by ring,
        Real.rpow_neg (by norm_num), Real.rpow_natCast]
    rw [he1, he3, he2, Real.Gamma_nat_eq_factorial] at hdup1
    have hdup2 := Real.Gamma_mul_Gamma_add_half (((9*m:ℕ):ℝ)/2 + 1/2)
    have hf1 : ((9*m:ℕ):ℝ)/2 + 1/2 + 1/2 = 9/2*(m:ℝ)+1 := by push_cast; ring
    have hf2 : 2*(((9*m:ℕ):ℝ)/2 + 1/2) = ((9*m:ℕ):ℝ)+1 := by ring
    have hf3 : (2:ℝ)^(1 - 2*(((9*m:ℕ):ℝ)/2 + 1/2)) = ((2:ℝ)^(9*m))⁻¹ := by
      rw [show 1 - 2*(((9*m:ℕ):ℝ)/2 + 1/2) = -((9*m:ℕ):ℝ) by ring,
        Real.rpow_neg (by norm_num), Real.rpow_natCast]
    rw [hf1, hf3, hf2, Real.Gamma_nat_eq_factorial] at hdup2
    have hshift := Gamma_shift (((3*m:ℕ):ℝ)/2 + 1/2) hspos (3*m)
    have hg1 : ((3*m:ℕ):ℝ)/2 + 1/2 + ((3*m:ℕ):ℝ) = ((9*m:ℕ):ℝ)/2 + 1/2 := by
      push_cast; ring
    have hg2 : ∏ j ∈ Finset.range (3*m), (((3*m:ℕ):ℝ)/2 + 1/2 + j)
        = (Dfun (3*m) : ℝ) / 2^(3*m) := prod_half (3*m)
    rw [hg1, hg2] at hshift
    have hΓs : 0 < Real.Gamma (((3*m:ℕ):ℝ)/2 + 1/2) := Real.Gamma_pos_of_pos hspos
    have hΓ9s : 0 < Real.Gamma (((9*m:ℕ):ℝ)/2 + 1/2) := Real.Gamma_pos_of_pos (by positivity)
    have hsqrtπ : (0:ℝ) < (Real.sqrt Real.pi) := Real.sqrt_pos.mpr Real.pi_pos
    have hD : (0:ℝ) < (Dfun (3*m) : ℝ) := by exact_mod_cast Dfun_pos
    have h2p3 : (0:ℝ) < (2:ℝ)^(3*m) := by positivity
    have h2p9 : (0:ℝ) < (2:ℝ)^(9*m) := by positivity
    have hΓ32 : Real.Gamma (3/2*(m:ℝ)+1)
        = ((3*m) ! : ℝ) * ((2:ℝ)^(3*m))⁻¹ * (Real.sqrt Real.pi) / Real.Gamma (((3*m:ℕ):ℝ)/2 + 1/2) := by
      rw [eq_div_iff (ne_of_gt hΓs), mul_comm]
      exact hdup1
    have hΓ92 : Real.Gamma (9/2*(m:ℝ)+1)
        = ((9*m) ! : ℝ) * ((2:ℝ)^(9*m))⁻¹ * (Real.sqrt Real.pi) / Real.Gamma (((9*m:ℕ):ℝ)/2 + 1/2) := by
      rw [eq_div_iff (ne_of_gt hΓ9s), mul_comm]
      exact hdup2
    rw [hG9, hG2, hG4, hG3, hG1, hΓ32, hΓ92, hshift]
    have hq1 : (qnum m : ℝ) = 2^(3*m) * ((2*m) ! : ℝ) * (Dfun (3*m) : ℝ) := by
      simp only [qnum_def]
      push_cast
      ring
    have hq2 : (qden m : ℝ) = ((4*m) ! : ℝ) * (m ! : ℝ) := by
      simp only [qden_def]
      push_cast
      ring
    rw [hq1, hq2]
    have hfac9 : (0:ℝ) < ((9*m) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hfac4 : (0:ℝ) < ((4*m) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hfac3 : (0:ℝ) < ((3*m) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hfac1 : (0:ℝ) < (m ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    field_simp
    ring

  haveI : Fact (Nat.Prime p) := ⟨hpp⟩
  have key : ∀ m : ℕ, ((Classical.choose (h_int m) : ℤ) : ℚ_[p]) = qp m := by
    intro m
    have hspec := Classical.choose_spec (h_int m)
    simp only at hspec
    have h1 : a m = ((qnum m : ℕ) : ℝ) / ((qden m : ℕ) : ℝ) := a_eq_q m
    have hqd : ((qden m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (qden_pos m).ne'
    have h2 : ((Classical.choose (h_int m) : ℤ) : ℝ) * ((qden m : ℕ) : ℝ)
        = ((qnum m : ℕ) : ℝ) := by
      rw [hspec, h1, div_mul_cancel₀ _ hqd]
    have h3 : (Classical.choose (h_int m)) * (qden m : ℤ) = (qnum m : ℤ) := by
      exact_mod_cast h2
    have h4 : ((Classical.choose (h_int m) : ℤ) : ℚ_[p]) * ((qden m : ℕ) : ℚ_[p])
        = ((qnum m : ℕ) : ℚ_[p]) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ_[p])) h3
    simp only [qp_def]
    rw [eq_div_iff (Nat.cast_ne_zero.mpr (qden_pos m).ne')]
    exact h4
  have hNp : n * p ^ r = (n * p ^ (r-1)) * p := by
    rw [mul_assoc, ← pow_succ]
    congr 2
    omega
  have hA : ((Classical.choose (h_int (n * p ^ r)) : ℤ) : ℚ_[p])
      = qp ((n*p^(r-1))*p) := by
    rw [key (n*p^r)]
    exact congrArg qp hNp
  have hB : ((Classical.choose (h_int (n * p ^ (r-1))) : ℤ) : ℚ_[p])
      = qp (n*p^(r-1)) := key _
  have hdvd := int_dvd_of_qp hp5 hn hr rfl hA hB
  rw [Int.modEq_iff_dvd]
  have h2 : (Classical.choose (h_int (n * p ^ (r-1))) : ℤ)
        - (Classical.choose (h_int (n * p ^ r)) : ℤ)
      = -((Classical.choose (h_int (n * p ^ r)) : ℤ)
        - (Classical.choose (h_int (n * p ^ (r-1))) : ℤ)) := by ring
  rw [h2]
  exact dvd_neg.mpr hdvd
