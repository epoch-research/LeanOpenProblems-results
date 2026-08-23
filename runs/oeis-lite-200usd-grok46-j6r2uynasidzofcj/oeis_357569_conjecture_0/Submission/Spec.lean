import FormalConjectures.Util.ProblemImports
open Nat

/--
A357569: $a(n) = \binom{3n}{n}^2 - 27 \binom{2n}{n}$.
-/
def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

namespace OEIS357569

open Finset

/- Finset helpers -/

lemma Icc_succ_right (k : ℕ) :
    Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) := by
  ext x
  simp only [mem_insert, mem_Icc]
  omega

lemma not_mem_Icc_one_of_succ (k : ℕ) : k + 1 ∉ Icc 1 k := by
  simp [mem_Icc]

lemma mem_Icc_one_iff {k x : ℕ} : x ∈ Icc 1 k ↔ 1 ≤ x ∧ x ≤ k :=
  mem_Icc

/- Product formulae -/

lemma factorial_eq_prod_Icc (k : ℕ) :
    (k ! : ℚ) = ∏ i ∈ Icc 1 k, (i : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Icc_succ_right, prod_insert (not_mem_Icc_one_of_succ k),
      ih, mul_comm]

lemma descFactorial_eq_prod_range {n k : ℕ} (h : k ≤ n) :
    (n.descFactorial k : ℚ) = ∏ j ∈ range k, ((n - j : ℕ) : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : k ≤ n := le_trans (le_succ k) h
    rw [descFactorial_succ, Nat.cast_mul, prod_range_succ, ih hk, mul_comm]

lemma choose_mul_factorial_eq_descFactorial (n k : ℕ) :
    n.choose k * k ! = n.descFactorial k := by
  by_cases h : k ≤ n
  · rw [choose_eq_descFactorial_div_factorial, Nat.div_mul_cancel]
    exact factorial_dvd_descFactorial n k
  · rw [choose_eq_zero_of_lt (lt_of_not_ge h),
      descFactorial_eq_zero_iff_lt.mpr (lt_of_not_ge h), zero_mul]

/-- `k! = ∏_{j < k} (k - j)`. -/
lemma factorial_eq_prod_range_sub (k : ℕ) :
    (k ! : ℚ) = ∏ j ∈ range k, ((k - j : ℕ) : ℚ) := by
  rw [factorial_eq_prod_Icc]
  refine (prod_bij (fun j _ => k - j) ?_ ?_ ?_ ?_).symm
  · intro j hj
    rw [mem_range] at hj
    rw [mem_Icc]
    exact ⟨Nat.succ_le_of_lt (Nat.sub_pos_of_lt hj), Nat.sub_le k j⟩
  · intro j1 hj1 j2 hj2 heq
    rw [mem_range] at hj1 hj2
    have h1 : k - (k - j1) = j1 := Nat.sub_sub_self (le_of_lt hj1)
    have h2 : k - (k - j2) = j2 := Nat.sub_sub_self (le_of_lt hj2)
    have heq' : k - j1 = k - j2 := heq
    calc j1 = k - (k - j1) := h1.symm
      _ = k - (k - j2) := by rw [heq']
      _ = j2 := h2
  · intro b hb
    rw [mem_Icc] at hb
    refine ⟨k - b, ?_, ?_⟩
    · rw [mem_range]
      exact Nat.sub_lt_self (Nat.succ_le_iff.mp hb.1) hb.2
    · exact Nat.sub_sub_self hb.2
  · intro j hj; rfl

lemma choose_eq_prod_range {n k : ℕ} (h : k ≤ n) :
    (n.choose k : ℚ) =
      ∏ j ∈ range k, (((n - j : ℕ) : ℚ) / ((k - j : ℕ) : ℚ)) := by
  have hmul : (n.choose k : ℚ) * (k ! : ℚ) = (n.descFactorial k : ℚ) :=
    mod_cast choose_mul_factorial_eq_descFactorial n k
  have hk0 : (k ! : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have : (n.choose k : ℚ) = (n.descFactorial k : ℚ) / (k ! : ℚ) :=
    (eq_div_iff_mul_eq hk0).mpr hmul
  rw [this, descFactorial_eq_prod_range h, factorial_eq_prod_range_sub k, prod_div_distrib]

/-- `C(α * n, n) = ∏_{i=1}^{n} ((α-1)*n + i) / i`. -/
lemma choose_mul_eq_prod {α n : ℕ} (hα : 1 ≤ α) :
    ((α * n).choose n : ℚ) =
      ∏ i ∈ Icc 1 n, ((((α - 1) * n + i : ℕ) : ℚ) / (i : ℚ)) := by
  by_cases hn : n = 0
  · subst n; simp
  have hle : n ≤ α * n := Nat.le_mul_of_pos_left n hα
  rw [choose_eq_prod_range hle]
  refine prod_bij (fun j _ => n - j) ?_ ?_ ?_ ?_
  · intro j hj
    rw [mem_range] at hj
    rw [mem_Icc]
    exact ⟨Nat.succ_le_of_lt (Nat.sub_pos_of_lt hj), Nat.sub_le n j⟩
  · intro j1 hj1 j2 hj2 heq
    rw [mem_range] at hj1 hj2
    have h1 : n - (n - j1) = j1 := Nat.sub_sub_self (le_of_lt hj1)
    have h2 : n - (n - j2) = j2 := Nat.sub_sub_self (le_of_lt hj2)
    have heq' : n - j1 = n - j2 := heq
    calc j1 = n - (n - j1) := h1.symm
      _ = n - (n - j2) := by rw [heq']
      _ = j2 := h2
  · intro b hb
    rw [mem_Icc] at hb
    refine ⟨n - b, ?_, ?_⟩
    · rw [mem_range]
      exact Nat.sub_lt_self (Nat.succ_le_iff.mp hb.1) hb.2
    · exact Nat.sub_sub_self hb.2
  · intro j hj
    rw [mem_range] at hj
    have hij : (α - 1) * n + (n - j) = α * n - j := by
      have hαn : α * n = (α - 1) * n + n := by
        have := Nat.sub_add_cancel hα
        conv_lhs => rw [← this, Nat.add_mul, one_mul]
      rw [hαn, Nat.add_sub_assoc (le_of_lt hj)]
    simp [hij]

/- Units below p^r and harmonic sums -/

def unitsBelow (p r : ℕ) : Finset ℕ :=
  (Icc 1 (p ^ r)).filter (fun j => ¬ p ∣ j)

lemma mem_unitsBelow {p r j : ℕ} :
    j ∈ unitsBelow p r ↔ 1 ≤ j ∧ j ≤ p ^ r ∧ ¬ p ∣ j := by
  simp only [unitsBelow, mem_filter, mem_Icc]
  tauto

lemma pos_of_mem_unitsBelow {p r j : ℕ} (h : j ∈ unitsBelow p r) : 0 < j :=
  Nat.succ_le_iff.mp (mem_unitsBelow.mp h).1

lemma not_dvd_of_mem_unitsBelow {p r j : ℕ} (h : j ∈ unitsBelow p r) : ¬ p ∣ j :=
  (mem_unitsBelow.mp h).2.2

lemma le_pow_of_mem_unitsBelow {p r j : ℕ} (h : j ∈ unitsBelow p r) : j ≤ p ^ r :=
  (mem_unitsBelow.mp h).2.1

/-- Inverse-power sums over `p`-free residues. -/
def H (t p r : ℕ) : ℚ :=
  ∑ j ∈ unitsBelow p r, (j : ℚ)⁻¹ ^ t

lemma coprime_of_mem_unitsBelow {p r j : ℕ} (hp : p.Prime) (h : j ∈ unitsBelow p r) :
    Nat.Coprime j (p ^ r) :=
  hp.coprime_pow_of_not_dvd (not_dvd_of_mem_unitsBelow h)

/- The product formula splitting p-multiples from p-free terms. -/

/-- Multiples of `p` in `Icc 1 (p^r)` are `p, 2p, …, p^r`. -/
lemma p_multiples_image (p r : ℕ) (hp : 0 < p) (hr : 0 < r) :
    (Icc 1 (p ^ r)).filter (p ∣ ·) = (Icc 1 (p ^ (r - 1))).image (fun t => p * t) := by
  ext j
  constructor
  · intro hj
    rw [mem_filter, mem_Icc] at hj
    obtain ⟨⟨hj1, hj2⟩, hdvd⟩ := hj
    obtain ⟨t, rfl⟩ := hdvd
    refine mem_image.mpr ⟨t, ?_, rfl⟩
    rw [mem_Icc]
    constructor
    · exact Nat.succ_le_iff.mpr (Nat.pos_of_mul_pos_left (Nat.succ_le_iff.mp hj1))
    · have hr' : r = r - 1 + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.mp hr)).symm
      apply Nat.le_of_mul_le_mul_left _ hp
      rwa [hr', Nat.pow_succ'] at hj2
  · intro hj
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hj
    rw [mem_Icc] at ht
    rw [mem_filter, mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨t, rfl⟩⟩
    · exact Nat.succ_le_iff.mpr (Nat.mul_pos hp (Nat.succ_le_iff.mp ht.1))
    · have hr' : r = r - 1 + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.mp hr)).symm
      calc p * t ≤ p * p ^ (r - 1) := Nat.mul_le_mul_left p ht.2
        _ = p ^ r := by rw [hr', Nat.pow_succ', Nat.add_sub_cancel]

lemma image_mul_p_inj {p : ℕ} (hp : 0 < p) :
    Set.InjOn (fun t : ℕ => p * t) Set.univ :=
  fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hp h

/-- The product of `((α-1) N + i)/i` over multiples of `p` recovers the smaller binomial. -/
lemma prod_p_multiples {α p r : ℕ} (hp : 0 < p) (hr : 0 < r) (hα : 1 ≤ α) :
    ∏ i ∈ (Icc 1 (p ^ r)).filter (p ∣ ·),
        ((((α - 1) * p ^ r + i : ℕ) : ℚ) / (i : ℚ)) =
      ((α * p ^ (r - 1)).choose (p ^ (r - 1)) : ℚ) := by
  rw [p_multiples_image p r hp hr, prod_image]
  · have hpr : p ^ r = p * p ^ (r - 1) := by
      cases r with
      | zero => exact absurd hr (lt_irrefl 0)
      | succ r' => simp [Nat.pow_succ']
    have hterm : ∀ t ∈ Icc 1 (p ^ (r - 1)),
        ((((α - 1) * p ^ r + p * t : ℕ) : ℚ) / ((p * t : ℕ) : ℚ)) =
          ((((α - 1) * p ^ (r - 1) + t : ℕ) : ℚ) / (t : ℚ)) := by
      intro t ht
      have ht0 : (t : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.succ_le_iff.mp (mem_Icc.mp ht).1).ne'
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
      have hnum : ((α - 1) * p ^ r + p * t : ℕ) =
          p * ((α - 1) * p ^ (r - 1) + t) := by
        rw [hpr, Nat.mul_add]
        congr 1
        rw [Nat.mul_left_comm]
      simp [hnum, Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
      field_simp [ht0, hp0]
    refine (prod_congr rfl hterm).trans ?_
    exact (choose_mul_eq_prod (α := α) (n := p ^ (r - 1)) hα).symm
  · intro t1 ht1 t2 ht2 h
    exact Nat.eq_of_mul_eq_mul_left hp h

/--
`C(α p^r, p^r) = C(α p^{r-1}, p^{r-1}) * ∏_{p ∤ j} (1 + (α-1) p^r / j)`.
-/
lemma choose_ratio_eq_prod {α p r : ℕ} (hp : p.Prime) (hr : 0 < r) (hα : 1 ≤ α) :
    ((α * p ^ r).choose (p ^ r) : ℚ) =
      ((α * p ^ (r - 1)).choose (p ^ (r - 1)) : ℚ) *
        ∏ j ∈ unitsBelow p r, (1 + ((α - 1 : ℕ) : ℚ) * (p ^ r : ℚ) / (j : ℚ)) := by
  have hN : p ^ r ≤ α * p ^ r := Nat.le_mul_of_pos_left _ hα
  rw [choose_mul_eq_prod hα]
  -- Split Icc 1 (p^r) into p-multiples and p-free
  have hdisj : Disjoint ((Icc 1 (p ^ r)).filter (p ∣ ·)) (unitsBelow p r) := by
    unfold unitsBelow
    rw [disjoint_filter]
    intro _ _ hpj
    exact not_not_intro hpj
  have hunion : (Icc 1 (p ^ r)).filter (p ∣ ·) ∪ unitsBelow p r = Icc 1 (p ^ r) := by
    ext x
    simp only [mem_union, mem_filter, unitsBelow, mem_Icc]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hx
      by_cases hd : p ∣ x
      · exact Or.inl ⟨hx, hd⟩
      · exact Or.inr ⟨hx, hd⟩
  have hsplit := prod_union (f := fun i =>
      ((((α - 1) * p ^ r + i : ℕ) : ℚ) / (i : ℚ))) hdisj
  rw [← hunion, hsplit, prod_p_multiples hp.pos hr hα]
  have hfree : ∏ j ∈ unitsBelow p r,
      ((((α - 1) * p ^ r + j : ℕ) : ℚ) / (j : ℚ)) =
      ∏ j ∈ unitsBelow p r,
        (1 + ((α - 1 : ℕ) : ℚ) * (p : ℚ) ^ r / (j : ℚ)) := by
    refine prod_congr rfl ?_
    intro j hj
    have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_mem_unitsBelow hj).ne'
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, add_div, div_self hj0]
    ring
  rw [hfree, mul_comm]

/- Valuation helpers -/

lemma padicValRat_sum_ge {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ) (m : ℤ)
    (hf : ∀ i ∈ s, f i = 0 ∨ m ≤ padicValRat p (f i)) :
    (∑ i ∈ s, f i) = 0 ∨ m ≤ padicValRat p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => exact Or.inl (by simp)
  | insert a s ha ih =>
    rw [sum_insert ha]
    have ha' := hf a (mem_insert_self a s)
    have hs' : ∀ i ∈ s, f i = 0 ∨ m ≤ padicValRat p (f i) :=
      fun i hi => hf i (mem_insert_of_mem hi)
    rcases ih hs' with hsum | hsum
    · rw [hsum, add_zero]; exact ha'
    · rcases ha' with hfa | hfa
      · rw [hfa, zero_add]; exact Or.inr hsum
      · by_cases h0 : f a + ∑ i ∈ s, f i = 0
        · exact Or.inl h0
        · exact Or.inr (le_trans (le_min hfa hsum) (padicValRat.min_le_padicValRat_add h0))

lemma padicValRat_inv_pow_of_not_dvd {p j t : ℕ} [Fact p.Prime] (hj : ¬ p ∣ j) (hj0 : j ≠ 0) :
    padicValRat p ((j : ℚ)⁻¹ ^ t) = 0 := by
  have hjq : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj0
  rw [padicValRat.pow (inv_ne_zero hjq), padicValRat.inv, padicValRat.of_nat]
  simp [padicValNat.eq_zero_of_not_dvd hj]

lemma padicValRat_H_nonneg {t p r : ℕ} [Fact p.Prime] :
    H t p r = 0 ∨ 0 ≤ padicValRat p (H t p r) := by
  refine padicValRat_sum_ge (unitsBelow p r) (fun j => (j : ℚ)⁻¹ ^ t) 0 ?_
  intro j hj
  refine Or.inr ?_
  rw [padicValRat_inv_pow_of_not_dvd (not_dvd_of_mem_unitsBelow hj)
    (pos_of_mem_unitsBelow hj).ne']

/- Power sums of units in ZMod (p^r) -/

/-- The k-th power map on `(ZMod p)ˣ`, viewed as a monoid hom into the field. -/
def unitsPowHom (p k : ℕ) [Fact p.Prime] : (ZMod p)ˣ →* ZMod p where
  toFun u := (u : ZMod p) ^ k
  map_one' := by simp
  map_mul' := by intros; simp [mul_pow]

lemma unitsPowHom_ne_one {p k : ℕ} [hp : Fact p.Prime] (hk : ¬ (p - 1) ∣ k) :
    unitsPowHom p k ≠ 1 := by
  intro h
  haveI : Fact p.Prime := hp
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have hgk : g ^ k ≠ 1 := by
    intro hgk
    exact hk (by
      have := orderOf_dvd_of_pow_eq_one hgk
      rwa [hord] at this)
  have : unitsPowHom p k g = 1 := by
    rw [h]; rfl
  apply hgk
  exact Units.ext (by simpa [unitsPowHom] using this)

lemma sum_units_pow_mod_p {p k : ℕ} [hp : Fact p.Prime] (hk : ¬ (p - 1) ∣ k) :
    ∑ u : (ZMod p)ˣ, ((u : ZMod p) ^ k) = 0 :=
  sum_hom_units_eq_zero (unitsPowHom p k) (unitsPowHom_ne_one hk)

/-- `∑_{j=1}^{p-1} j^m ≡ 0 (mod p)` if `p-1 ∤ m`. -/
lemma sum_range_pow_mod_p {p m : ℕ} [hp : Fact p.Prime] (hm : ¬ (p - 1) ∣ m) :
    ∑ j ∈ Icc 1 (p - 1), ((j : ZMod p) ^ m) = 0 := by
  trans ∑ u : (ZMod p)ˣ, ((u : ZMod p) ^ m)
  · refine Finset.sum_bij
        (i := fun j hj =>
          ZMod.unitOfCoprime j (by
            rw [mem_Icc] at hj
            exact Nat.coprime_comm.mp ((hp.out.coprime_iff_not_dvd).mpr (fun hdvd =>
              (Nat.le_of_dvd (Nat.succ_le_iff.mp hj.1) hdvd).not_gt
                (Nat.lt_of_le_pred hp.out.pos hj.2)))))
        (fun _ _ => mem_univ _)
        (fun j1 hj1 j2 hj2 h => by
          rw [mem_Icc] at hj1 hj2
          have h1 := ZMod.val_cast_of_lt (Nat.lt_of_le_pred hp.out.pos hj1.2)
          have h2 := ZMod.val_cast_of_lt (Nat.lt_of_le_pred hp.out.pos hj2.2)
          have := congrArg (fun u : (ZMod p)ˣ => ZMod.val (u : ZMod p)) h
          simp only [ZMod.coe_unitOfCoprime] at this
          rwa [h1, h2] at this)
        (fun u _ => by
          refine ⟨ZMod.val (u : ZMod p), ?_, ?_⟩
          · rw [mem_Icc]
            have hne : (u : ZMod p) ≠ 0 := Units.ne_zero u
            have hpos : 0 < ZMod.val (u : ZMod p) :=
              Nat.pos_of_ne_zero (fun h => hne ((ZMod.val_eq_zero (u : ZMod p)).mp h))
            exact ⟨Nat.succ_le_iff.mpr hpos, Nat.le_pred_of_lt (ZMod.val_lt (u : ZMod p))⟩
          · exact Units.ext (by simp [ZMod.natCast_val]))
        (fun j hj => by
          rw [mem_Icc] at hj
          simp [ZMod.coe_unitOfCoprime])
  · exact sum_units_pow_mod_p hm

lemma unitsBelow_one {p : ℕ} (hp : p.Prime) :
    unitsBelow p 1 = Icc 1 (p - 1) := by
  ext j
  simp only [unitsBelow, mem_filter, mem_Icc, pow_one]
  constructor
  · intro ⟨⟨h1, h2⟩, hnd⟩
    exact ⟨h1, Nat.le_pred_of_lt (lt_of_le_of_ne h2 (fun h => hnd (h ▸ dvd_rfl)))⟩
  · intro ⟨h1, h2⟩
    have hjlt : j < p := Nat.lt_of_le_pred hp.pos h2
    exact ⟨⟨h1, hjlt.le⟩, fun hdvd => hjlt.not_ge (Nat.le_of_dvd (Nat.succ_le_iff.mp h1) hdvd)⟩

/- Rewrite helpers for `H` -/

lemma H_eq_sum_div (t p r : ℕ) :
    H t p r = ∑ j ∈ unitsBelow p r, (1 : ℚ) / (j : ℚ) ^ t := by
  simp only [H, inv_pow, one_div]

/- p-adic valuation of integers and congruences -/

lemma dvd_of_padicValRat_int_ge {p : ℕ} [Fact p.Prime] {z : ℤ} {n : ℕ}
    (h : z = 0 ∨ (n : ℤ) ≤ padicValRat p (z : ℚ)) :
    (p : ℤ) ^ n ∣ z := by
  rcases h with h | h
  · simp [h]
  · rw [padicValInt_dvd_iff]
    refine Or.inr ?_
    have heq : padicValRat p (z : ℚ) = (padicValInt p z : ℤ) := padicValRat.of_int
    have : (n : ℤ) ≤ (padicValInt p z : ℤ) := by rwa [heq] at h
    exact Nat.cast_le.mp this

lemma int_modEq_of_padicValRat_ge {p : ℕ} [Fact p.Prime] {a b : ℤ} {n : ℕ}
    (h : a - b = 0 ∨ (n : ℤ) ≤ padicValRat p ((a - b : ℤ) : ℚ)) :
    a ≡ b [ZMOD (p : ℤ) ^ n] := by
  rw [Int.modEq_iff_dvd, ← dvd_neg, neg_sub]
  exact dvd_of_padicValRat_int_ge h

lemma padicValRat_p_pow {p k : ℕ} [hp : Fact p.Prime] :
    padicValRat p ((p : ℚ) ^ k) = k := by
  rw [padicValRat.pow (Nat.cast_ne_zero.mpr hp.out.ne_zero), padicValRat.self hp.out.one_lt,
    mul_one]

lemma prime_not_dvd_two {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) : ¬ p ∣ 2 := by
  intro h
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
  · exact hp.ne_one h
  · omega

lemma padicValRat_of_nat_not_dvd {p n : ℕ} [Fact p.Prime] (h : ¬ p ∣ n) :
    padicValRat p (n : ℚ) = 0 := by
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h]
  simp

lemma padicValRat_two {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) :
    padicValRat p (2 : ℚ) = 0 :=
  padicValRat_of_nat_not_dvd (prime_not_dvd_two hp.out hp3)

lemma prime_not_dvd_three {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ 3 := by
  intro h
  rcases (Nat.dvd_prime Nat.prime_three).mp h with h | h
  · exact hp.ne_one h
  · omega

lemma padicValRat_three {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    padicValRat p (3 : ℚ) = 0 :=
  padicValRat_of_nat_not_dvd (prime_not_dvd_three hp.out hp5)

lemma padicValRat_six {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    padicValRat p (6 : ℚ) = 0 := by
  have h6 : ¬ p ∣ 6 := by
    intro h
    have : p ∣ 2 * 3 := by simpa using h
    rcases hp.out.dvd_mul.mp this with h | h
    · exact prime_not_dvd_two hp.out (by omega) h
    · exact prime_not_dvd_three hp.out hp5 h
  exact padicValRat_of_nat_not_dvd h6

lemma padicValRat_neg {p : ℕ} [Fact p.Prime] (q : ℚ) :
    padicValRat p (-q) = padicValRat p q :=
  padicValRat.neg q

/- Fermat: `p ∣ j^{p-1} - 1` for `p ∤ j`. -/

lemma zmod_nat_ne_zero {p j : ℕ} [hp : Fact p.Prime] (hj : ¬ p ∣ j) :
    (j : ZMod p) ≠ 0 := by
  intro h
  exact hj ((ZMod.natCast_eq_zero_iff j p).mp h)

lemma fermat_pow_sub_one {p j : ℕ} [hp : Fact p.Prime] (hj : ¬ p ∣ j) :
    (p : ℤ) ∣ (j : ℤ) ^ (p - 1) - 1 := by
  have hpow : (j : ZMod p) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one (zmod_nat_ne_zero hj)
  have hcast : (( (j : ℤ) ^ (p - 1) - 1 : ℤ) : ZMod p) = 0 := by
    rw [Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_one, hpow, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((j : ℤ) ^ (p - 1) - 1) p).mp hcast

lemma one_le_padicValRat_of_int_dvd {p : ℕ} [hp : Fact p.Prime] {z : ℤ}
    (hz : z ≠ 0) (hdvd : (p : ℤ) ∣ z) :
    1 ≤ padicValRat p (z : ℚ) := by
  have : 1 ≤ padicValInt p z := by
    have hnat : p ∣ z.natAbs := (Int.natCast_dvd).mp hdvd
    have := one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hz) hnat
    simpa [padicValInt] using this
  simpa [padicValRat.of_int] using this

/- Coprimality of `p-1` and `p-2`. -/

lemma coprime_pred_pred_pred {p : ℕ} (hp : p.Prime) : (p - 1).Coprime (p - 2) := by
  have hp2 : 2 ≤ p := hp.two_le
  have : p - 1 = (p - 2) + 1 := by omega
  rw [this, Nat.coprime_self_add_left]
  exact Nat.coprime_one_left _

lemma not_dvd_mul_p_sub_two {p t : ℕ} (hp : p.Prime) (ht : ¬ (p - 1) ∣ t) :
    ¬ (p - 1) ∣ t * (p - 2) := by
  intro h
  exact ht ((coprime_pred_pred_pred hp).dvd_of_dvd_mul_right h)

lemma not_dvd_pred_factorial {p : ℕ} (hp : p.Prime) : ¬ p ∣ (p - 1)! := by
  rw [hp.dvd_factorial]
  exact Nat.not_le_of_gt (Nat.sub_one_lt (Nat.Prime.ne_zero hp))

/- Inverse of `j` in `ZMod p` is `j^{p-2}`. -/

lemma zmod_mul_pow_p_sub_two {p j : ℕ} [hp : Fact p.Prime] (hj : ¬ p ∣ j)
    (hp2 : 2 ≤ p) :
    (j : ZMod p) * (j : ZMod p) ^ (p - 2) = 1 := by
  have hpe : p - 2 + 1 = p - 1 := by omega
  rw [mul_comm, ← pow_succ, hpe, ZMod.pow_card_sub_one_eq_one (zmod_nat_ne_zero hj)]

/- `v_p(H_t^{(1)}) ≥ 1` when `p-1 ∤ t`. -/

lemma padicValRat_H_one_of_not_dvd {t p : ℕ} [hp : Fact p.Prime]
    (ht : ¬ (p - 1) ∣ t) (hp2 : 2 ≤ p) :
    H t p 1 = 0 ∨ 1 ≤ padicValRat p (H t p 1) := by
  have hp' := hp.out
  have hU : unitsBelow p 1 = Icc 1 (p - 1) := unitsBelow_one hp'
  let D : ℕ := (p - 1)!
  have hDne : D ≠ 0 := Nat.factorial_ne_zero (p - 1)
  have hD0 : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hDne
  have hDv : padicValRat p (D : ℚ) = 0 :=
    padicValRat_of_nat_not_dvd (not_dvd_pred_factorial hp')
  let A : ℕ := ∑ j ∈ Icc 1 (p - 1), (D / j) ^ t
  have hterm_cast : ∀ j ∈ Icc 1 (p - 1),
      ((D / j : ℕ) : ℚ) ^ t = (D : ℚ) ^ t / (j : ℚ) ^ t := by
    intro j hj
    rw [mem_Icc] at hj
    have hj0 : j ≠ 0 := (Nat.succ_le_iff.mp hj.1).ne'
    have hjD : j ∣ D := Nat.dvd_factorial (Nat.succ_le_iff.mp hj.1) hj.2
    have hdiv : ((D / j : ℕ) : ℚ) = (D : ℚ) / (j : ℚ) :=
      Nat.cast_div hjD (Nat.cast_ne_zero.mpr hj0)
    rw [hdiv, div_pow]
  have hA_cast : (A : ℚ) = ∑ j ∈ Icc 1 (p - 1), (D : ℚ) ^ t / (j : ℚ) ^ t := by
    simp only [A, Nat.cast_sum, Nat.cast_pow]
    refine sum_congr rfl ?_
    intro j hj
    exact hterm_cast j hj
  have hH : H t p 1 = ∑ j ∈ Icc 1 (p - 1), (j : ℚ)⁻¹ ^ t := by
    rw [H, hU]
  have hHA : H t p 1 * (D : ℚ) ^ t = A := by
    rw [hH, sum_mul, hA_cast]
    refine sum_congr rfl ?_
    intro j hj
    rw [mem_Icc] at hj
    rw [div_eq_inv_mul, inv_pow]
  -- p ∣ A
  have hAmod : (A : ZMod p) = 0 := by
    have hsum : ∑ j ∈ Icc 1 (p - 1), ((j : ZMod p) ^ (t * (p - 2))) = 0 :=
      sum_range_pow_mod_p (not_dvd_mul_p_sub_two hp' ht)
    have hterm : ∀ j ∈ Icc 1 (p - 1),
        (((D / j : ℕ) : ZMod p) ^ t) =
          (D : ZMod p) ^ t * (j : ZMod p) ^ (t * (p - 2)) := by
      intro j hj
      rw [mem_Icc] at hj
      have hj0 : j ≠ 0 := (Nat.succ_le_iff.mp hj.1).ne'
      have hjD : j ∣ D := Nat.dvd_factorial (Nat.succ_le_iff.mp hj.1) hj.2
      have hjlt : j < p := Nat.lt_of_le_pred hp'.pos hj.2
      have hnd : ¬ p ∣ j := fun hd =>
        hjlt.not_ge (Nat.le_of_dvd (Nat.succ_le_iff.mp hj.1) hd)
      have hmul : (D / j) * j = D := Nat.div_mul_cancel hjD
      have hmul' : ((D / j : ℕ) : ZMod p) * (j : ZMod p) = (D : ZMod p) := by
        rw [← Nat.cast_mul, hmul]
      have hjinv := zmod_mul_pow_p_sub_two hnd hp2
      have : ((D / j : ℕ) : ZMod p) = (D : ZMod p) * (j : ZMod p) ^ (p - 2) := by
        calc ((D / j : ℕ) : ZMod p)
            = ((D / j : ℕ) : ZMod p) * 1 := (mul_one _).symm
          _ = ((D / j : ℕ) : ZMod p) * ((j : ZMod p) * (j : ZMod p) ^ (p - 2)) := by
              rw [hjinv]
          _ = (((D / j : ℕ) : ZMod p) * (j : ZMod p)) * (j : ZMod p) ^ (p - 2) := by
              ac_rfl
          _ = (D : ZMod p) * (j : ZMod p) ^ (p - 2) := by rw [hmul']
      rw [this, mul_pow, ← pow_mul, mul_comm (p - 2) t]
    simp only [A, Nat.cast_sum, Nat.cast_pow]
    rw [sum_congr rfl hterm, ← mul_sum, hsum, mul_zero]
  by_cases h0 : H t p 1 = 0
  · exact Or.inl h0
  · right
    have hA0 : A ≠ 0 := by
      intro hA
      have : H t p 1 * (D : ℚ) ^ t = 0 := by rw [hHA, hA]; simp
      exact h0 (eq_zero_of_ne_zero_of_mul_right_eq_zero (pow_ne_zero t hD0) this)
    have hvA : 1 ≤ padicValRat p (A : ℚ) := by
      have hdvd : p ∣ A := (ZMod.natCast_eq_zero_iff A p).mp hAmod
      have : 1 ≤ padicValNat p A := one_le_padicValNat_of_dvd hA0 hdvd
      simpa [padicValRat.of_nat] using this
    have hdiv : H t p 1 = (A : ℚ) / (D : ℚ) ^ t :=
      (eq_div_iff (pow_ne_zero t hD0)).mpr hHA
    have hA0q : (A : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hA0
    have hDt : (D : ℚ) ^ t ≠ 0 := pow_ne_zero t hD0
    rw [hdiv, padicValRat.div hA0q hDt, padicValRat.pow hD0, hDv, mul_zero, sub_zero]
    exact hvA

lemma p_sub_one_not_dvd_one {p : ℕ} (hp : 3 ≤ p) : ¬ (p - 1) ∣ 1 := by
  intro h
  have := Nat.le_of_dvd (by omega : 0 < 1) h
  omega

lemma p_sub_one_not_dvd_two {p : ℕ} (hp : 5 ≤ p) : ¬ (p - 1) ∣ 2 := by
  intro h
  have := Nat.le_of_dvd (by omega : 0 < 2) h
  omega

lemma p_sub_one_not_dvd_three {p : ℕ} (hp : 5 ≤ p) : ¬ (p - 1) ∣ 3 := by
  intro h
  have := Nat.le_of_dvd (by omega : 0 < 3) h
  omega

lemma padicValRat_H1_one {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) :
    H 1 p 1 = 0 ∨ 1 ≤ padicValRat p (H 1 p 1) :=
  padicValRat_H_one_of_not_dvd (p_sub_one_not_dvd_one hp3) (by omega)

lemma padicValRat_H2_one {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    H 2 p 1 = 0 ∨ 1 ≤ padicValRat p (H 2 p 1) :=
  padicValRat_H_one_of_not_dvd (p_sub_one_not_dvd_two hp5) (by omega)

lemma padicValRat_H3_one {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    H 3 p 1 = 0 ∨ 1 ≤ padicValRat p (H 3 p 1) :=
  padicValRat_H_one_of_not_dvd (p_sub_one_not_dvd_three hp5) (by omega)

/- Pairing j ↔ p^r - j on unitsBelow -/

lemma lt_pow_of_mem_unitsBelow {p r j : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hj : j ∈ unitsBelow p r) : j < p ^ r := by
  obtain ⟨_, h2, hnd⟩ := mem_unitsBelow.mp hj
  exact lt_of_le_of_ne h2 (fun heq => hnd (heq ▸ dvd_pow_self p hr.ne'))

lemma sub_mem_unitsBelow {p r j : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hj : j ∈ unitsBelow p r) : p ^ r - j ∈ unitsBelow p r := by
  obtain ⟨h1, h2, hnd⟩ := mem_unitsBelow.mp hj
  have hjlt : j < p ^ r := lt_pow_of_mem_unitsBelow hp hr hj
  refine mem_unitsBelow.mpr ⟨Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hjlt), Nat.sub_le _ _, ?_⟩
  intro hdvd
  have hpN : p ∣ p ^ r := dvd_pow_self p hr.ne'
  have hN : (p : ℤ) ∣ (p ^ r : ℤ) := by exact_mod_cast hpN
  have hNj : (p : ℤ) ∣ ((p ^ r : ℕ) : ℤ) - (j : ℤ) := by
    have : ((p ^ r - j : ℕ) : ℤ) = (p ^ r : ℕ) - (j : ℤ) :=
      Int.natCast_sub (le_of_lt hjlt)
    rw [← this]
    exact_mod_cast hdvd
  have hjZ : (p : ℤ) ∣ (j : ℤ) := by
    have : (p ^ r : ℤ) - ((p ^ r : ℤ) - (j : ℤ)) = (j : ℤ) := by ring
    rw [← this]
    exact dvd_sub hN hNj
  exact hnd (Int.natCast_dvd_natCast.mp hjZ)

lemma ne_sub_of_mem_unitsBelow {p r j : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 0 < r)
    (hj : j ∈ unitsBelow p r) : j ≠ p ^ r - j := by
  intro h
  have hjle : j ≤ p ^ r := (mem_unitsBelow.mp hj).2.1
  have h2j : 2 * j = p ^ r := by omega
  have hodd : Odd (p ^ r) := (hp.odd_of_ne_two (by omega)).pow
  have heven : Even (p ^ r) := ⟨j, by omega⟩
  exact Nat.not_even_iff_odd.mpr hodd heven

lemma inv_add_inv_sub' {N j : ℕ} (hj0 : 0 < j) (hjN : j < N) :
    (1 : ℚ) / j + 1 / (N - j : ℕ) = (N : ℚ) / ((j : ℚ) * (N - j : ℕ)) := by
  have hjq : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj0.ne'
  have hNq : ((N - j : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.sub_pos_of_lt hjN).ne'
  have hsum : ((N - j : ℕ) : ℚ) + (j : ℚ) = (N : ℚ) := by
    norm_cast
    exact Nat.sub_add_cancel (le_of_lt hjN)
  field_simp [hjq, hNq]
  linarith

lemma inv_pair_eq {N j : ℕ} (hj0 : 0 < j) (hjN : j < N) :
    (1 : ℚ) / ((j : ℚ) * (N - j : ℕ)) =
      (N : ℚ) / ((j : ℚ) ^ 2 * (N - j : ℕ)) - 1 / (j : ℚ) ^ 2 := by
  have hjq : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj0.ne'
  have hNq : ((N - j : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.sub_pos_of_lt hjN).ne'
  have hcast : ((N - j : ℕ) : ℚ) = (N : ℚ) - (j : ℚ) := by
    norm_cast
    exact Int.natCast_sub (le_of_lt hjN) ▸ by norm_cast
  field_simp [hjq, hNq]
  rw [hcast]
  ring

lemma sum_inv_sub_eq_H_one {p r : ℕ} (hp : p.Prime) (hr : 0 < r) :
    ∑ j ∈ unitsBelow p r, ((p ^ r - j : ℕ) : ℚ)⁻¹ = H 1 p r := by
  unfold H
  simp only [pow_one]
  refine Finset.sum_bij (fun j _ => p ^ r - j) ?_ ?_ ?_ ?_
  · intro j hj; exact sub_mem_unitsBelow hp hr hj
  · intro j1 hj1 j2 hj2 heq
    have h1 := le_of_lt (lt_pow_of_mem_unitsBelow hp hr hj1)
    have h2 := le_of_lt (lt_pow_of_mem_unitsBelow hp hr hj2)
    have := congrArg (fun t => p ^ r - t) heq
    simpa [Nat.sub_sub_self h1, Nat.sub_sub_self h2] using this
  · intro b hb
    refine ⟨p ^ r - b, sub_mem_unitsBelow hp hr hb, ?_⟩
    exact Nat.sub_sub_self (le_of_lt (lt_pow_of_mem_unitsBelow hp hr hb))
  · intro j hj
    rfl

/-- `H_1 + N H_2 / 2 = N^2 / 2 * ∑ 1/(j^2 (N-j))`. -/
lemma H_one_add_half_N_H_two {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 0 < r) :
    H 1 p r + (p ^ r : ℚ) * H 2 p r / 2 =
      (p ^ r : ℚ) ^ 2 / 2 *
        ∑ j ∈ unitsBelow p r, (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ)) := by
  have hreind := sum_inv_sub_eq_H_one hp hr
  have hsum2 : ∑ j ∈ unitsBelow p r,
      ((j : ℚ)⁻¹ + ((p ^ r - j : ℕ) : ℚ)⁻¹) = 2 * H 1 p r := by
    rw [sum_add_distrib, hreind]
    unfold H
    simp only [pow_one]
    ring
  have hterm : ∀ j ∈ unitsBelow p r,
      (j : ℚ)⁻¹ + ((p ^ r - j : ℕ) : ℚ)⁻¹ =
        (p ^ r : ℚ) / ((j : ℚ) * ((p ^ r - j : ℕ) : ℚ)) := by
    intro j hj
    have := inv_add_inv_sub' (pos_of_mem_unitsBelow hj) (lt_pow_of_mem_unitsBelow hp hr hj)
    simpa [one_div] using this
  have hsumN : 2 * H 1 p r =
      ∑ j ∈ unitsBelow p r, (p ^ r : ℚ) / ((j : ℚ) * ((p ^ r - j : ℕ) : ℚ)) := by
    rw [← hsum2]
    exact sum_congr rfl hterm
  have hdecomp : ∀ j ∈ unitsBelow p r,
      (1 : ℚ) / ((j : ℚ) * ((p ^ r - j : ℕ) : ℚ)) =
        (p ^ r : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ)) - 1 / (j : ℚ) ^ 2 := by
    intro j hj
    simpa using inv_pair_eq (pos_of_mem_unitsBelow hj) (lt_pow_of_mem_unitsBelow hp hr hj)
  have hsumd :
      ∑ j ∈ unitsBelow p r, (1 : ℚ) / ((j : ℚ) * ((p ^ r - j : ℕ) : ℚ)) =
        (p ^ r : ℚ) * ∑ j ∈ unitsBelow p r,
            (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ)) -
          H 2 p r := by
    rw [sum_congr rfl hdecomp, sum_sub_distrib]
    have hmul : ∑ j ∈ unitsBelow p r,
        (p ^ r : ℚ) * ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ))⁻¹ =
        (p ^ r : ℚ) * ∑ j ∈ unitsBelow p r,
          ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ))⁻¹ := by
      simp [mul_sum]
    simp only [div_eq_mul_inv]
    rw [hmul]
    unfold H
    simp [inv_pow, one_mul]
  have h2H : 2 * H 1 p r = (p ^ r : ℚ) *
      ∑ j ∈ unitsBelow p r, ((j : ℚ) * ((p ^ r - j : ℕ) : ℚ))⁻¹ := by
    rw [hsumN]
    simp only [div_eq_mul_inv, mul_sum]
  -- rewrite 1 / (j * (N-j)) as inverse
  have hsumd' :
      ∑ j ∈ unitsBelow p r, ((j : ℚ) * ((p ^ r - j : ℕ) : ℚ))⁻¹ =
        (p ^ r : ℚ) * ∑ j ∈ unitsBelow p r,
            ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ))⁻¹ - H 2 p r := by
    simpa [one_div, div_eq_mul_inv] using hsumd
  have hH1 : H 1 p r = (2 * H 1 p r) / 2 := by ring
  rw [hH1, h2H, hsumd']
  ring

lemma padicValRat_inv_sq_sub {p r j : ℕ} [Fact p.Prime] (hp : p.Prime) (hr : 0 < r)
    (hj : j ∈ unitsBelow p r) :
    padicValRat p (((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ))⁻¹) = 0 := by
  have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_mem_unitsBelow hj).ne'
  have hN0 : ((p ^ r - j : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.sub_pos_of_lt (lt_pow_of_mem_unitsBelow hp hr hj)).ne'
  have hndj : ¬ p ∣ j := not_dvd_of_mem_unitsBelow hj
  have hndN : ¬ p ∣ (p ^ r - j) := not_dvd_of_mem_unitsBelow (sub_mem_unitsBelow hp hr hj)
  have hvj : padicValRat p (j : ℚ) = 0 := padicValRat_of_nat_not_dvd hndj
  have hvN : padicValRat p ((p ^ r - j : ℕ) : ℚ) = 0 := padicValRat_of_nat_not_dvd hndN
  rw [padicValRat.inv, padicValRat.mul (pow_ne_zero 2 hj0) hN0, padicValRat.pow hj0, hvj, hvN]
  simp

lemma padicValRat_theta_ge {p r : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    H 1 p r + (p : ℚ) ^ r * H 2 p r / 2 = 0 ∨
      (2 * r : ℤ) ≤ padicValRat p (H 1 p r + (p : ℚ) ^ r * H 2 p r / 2) := by
  have hid := H_one_add_half_N_H_two hp.out hp3 hr
  rw [hid]
  let S : ℚ := ∑ j ∈ unitsBelow p r,
    ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ))⁻¹
  have hSeq : ∑ j ∈ unitsBelow p r,
      (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ)) = S := by
    simp [S, one_div]
  rw [hSeq]
  have hS : S = 0 ∨ 0 ≤ padicValRat p S :=
    padicValRat_sum_ge (unitsBelow p r)
      (fun j => ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ))⁻¹) 0
      (fun j hj => Or.inr (le_of_eq (padicValRat_inv_sq_sub hp.out hr hj).symm))
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  have hN : (p : ℚ) ^ r ≠ 0 := pow_ne_zero r (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  by_cases h0 : ((p : ℚ) ^ r) ^ 2 / 2 * S = 0
  · exact Or.inl h0
  · right
    have hS0 : S ≠ 0 := by
      intro hS0; apply h0; simp [hS0]
    have hN2 : ((p : ℚ) ^ r) ^ 2 ≠ 0 := pow_ne_zero 2 hN
    have hvN : padicValRat p (((p : ℚ) ^ r) ^ 2) = (2 * r : ℤ) := by
      rw [padicValRat.pow hN, padicValRat_p_pow]; ring
    have hv2 : padicValRat p (2 : ℚ) = 0 := padicValRat_two hp3
    have hvS : 0 ≤ padicValRat p S := hS.resolve_left (fun h => hS0 h)
    have hval : padicValRat p (((p : ℚ) ^ r) ^ 2 / 2 * S) =
        padicValRat p (((p : ℚ) ^ r) ^ 2) + padicValRat p S - padicValRat p (2 : ℚ) := by
      have hprod : ((p : ℚ) ^ r) ^ 2 / 2 * S = ((p : ℚ) ^ r) ^ 2 * S / 2 := by ring
      rw [hprod, padicValRat.div (mul_ne_zero hN2 hS0) h2, padicValRat.mul hN2 hS0]
    rw [hval, hvN, hv2, sub_zero]
    linarith

/- Decomposition of `unitsBelow p r` for `r ≥ 2`. -/

lemma pow_eq_mul_pow_pred {p r : ℕ} (hr : 1 ≤ r) :
    p ^ r = p * p ^ (r - 1) := by
  rw [← pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hr]

lemma unitsBelow_decomp {p r j : ℕ} (hp : p.Prime) (hr : 2 ≤ r) :
    j ∈ unitsBelow p r ↔
      ∃ b ∈ unitsBelow p (r - 1), ∃ a < p, j = b + a * p ^ (r - 1) := by
  have hr1 : 1 ≤ r := by omega
  have hr1' : 0 < r - 1 := by omega
  set M := p ^ (r - 1) with hM
  have hMpos : 0 < M := pow_pos hp.pos _
  have hpM : p ∣ M := dvd_pow_self p hr1'.ne'
  have hpr : p ^ r = p * M := by rw [hM]; exact pow_eq_mul_pow_pred hr1
  constructor
  · intro hj
    obtain ⟨hj1, hj2, hnd⟩ := mem_unitsBelow.mp hj
    have hjlt : j < p ^ r := lt_pow_of_mem_unitsBelow hp (by omega) hj
    have hdiv : j = j % M + (j / M) * M := by
      rw [mul_comm, Nat.mod_add_div]
    have ha : j / M < p := by
      have hlt : j < M * p := by
        rw [mul_comm, ← hpr]
        exact hjlt
      exact Nat.div_lt_of_lt_mul hlt
    have hb0 : j % M ≠ 0 := by
      intro h
      have : M ∣ j := Nat.dvd_of_mod_eq_zero h
      exact hnd (hpM.trans this)
    have hbU : j % M ∈ unitsBelow p (r - 1) := by
      refine mem_unitsBelow.mpr ⟨Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hb0),
        (Nat.mod_lt j hMpos).le, ?_⟩
      intro hpb
      have : p ∣ M * (j / M) + j % M :=
        dvd_add (dvd_mul_of_dvd_left hpM _) hpb
      rw [Nat.div_add_mod] at this
      exact hnd this
    exact ⟨j % M, hbU, j / M, ha, hdiv⟩
  · rintro ⟨b, hb, a, ha, rfl⟩
    obtain ⟨hb1, hb2, hbnd⟩ := mem_unitsBelow.mp hb
    refine mem_unitsBelow.mpr ⟨?_, ?_, ?_⟩
    · exact le_trans hb1 (Nat.le_add_right _ _)
    · calc b + a * M
          ≤ M + a * M := Nat.add_le_add_right hb2 _
        _ = (1 + a) * M := by ring
        _ ≤ p * M := Nat.mul_le_mul_right _ (by omega)
        _ = p ^ r := hpr.symm
    · intro h
      have hZ : (p : ℤ) ∣ (b : ℤ) := by
        have h1 : (p : ℤ) ∣ (b : ℤ) + (a : ℤ) * (M : ℤ) := by
          exact_mod_cast h
        have h2 : (p : ℤ) ∣ (a : ℤ) * (M : ℤ) := by
          exact_mod_cast (dvd_mul_of_dvd_right hpM a)
        convert dvd_sub h1 h2 using 1
        ring
      exact hbnd (Int.natCast_dvd_natCast.mp hZ)

lemma b_lt_pow_of_mem {p r b : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hb : b ∈ unitsBelow p r) : b < p ^ r :=
  lt_pow_of_mem_unitsBelow hp hr hb

lemma H_succ_eq {t p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r) :
    H t p r =
      ∑ b ∈ unitsBelow p (r - 1),
        ∑ a ∈ range p, (((b + a * p ^ (r - 1) : ℕ) : ℚ)⁻¹ ^ t) := by
  unfold H
  have hmem : ∀ b ∈ unitsBelow p (r - 1), ∀ a ∈ range p,
      b + a * p ^ (r - 1) ∈ unitsBelow p r := by
    intro b hb a ha
    exact (unitsBelow_decomp hp hr).mpr ⟨b, hb, a, mem_range.mp ha, rfl⟩
  classical
  refine Eq.symm ?_
  rw [← sum_product' (f := fun b a =>
    (((b + a * p ^ (r - 1) : ℕ) : ℚ)⁻¹ ^ t))]
  refine Finset.sum_bij
    (fun (x : ℕ × ℕ) _ => x.1 + x.2 * p ^ (r - 1)) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hb, ha⟩ := mem_product.mp hx
    exact hmem x.1 hb x.2 ha
  · intro x hx y hy heq
    obtain ⟨hb, ha⟩ := mem_product.mp hx
    obtain ⟨hb', ha'⟩ := mem_product.mp hy
    have hxle := (mem_unitsBelow.mp hb).2.1
    have hyle := (mem_unitsBelow.mp hb').2.1
    have hr1 : 0 < r - 1 := by omega
    have hxlt : x.1 < p ^ (r - 1) :=
      lt_of_le_of_ne hxle (fun h =>
        (not_dvd_of_mem_unitsBelow hb)
          (h ▸ dvd_pow_self p hr1.ne'))
    have hylt : y.1 < p ^ (r - 1) :=
      lt_of_le_of_ne hyle (fun h =>
        (not_dvd_of_mem_unitsBelow hb')
          (h ▸ dvd_pow_self p hr1.ne'))
    have hMpos : 0 < p ^ (r - 1) := pow_pos hp.pos _
    have heq' : x.1 + x.2 * p ^ (r - 1) = y.1 + y.2 * p ^ (r - 1) := heq
    have hb_eq : x.1 = y.1 := by
      have hxmod := Nat.add_mul_mod_self_right x.1 x.2 (p ^ (r - 1))
      have hymod := Nat.add_mul_mod_self_right y.1 y.2 (p ^ (r - 1))
      rw [Nat.mod_eq_of_lt hxlt] at hxmod
      rw [Nat.mod_eq_of_lt hylt] at hymod
      rw [← hxmod, ← hymod, heq']
    have ha_eq : x.2 = y.2 := by
      have hxdiv : (x.1 + x.2 * p ^ (r - 1)) / p ^ (r - 1) = x.2 := by
        rw [Nat.add_mul_div_right _ _ hMpos, Nat.div_eq_of_lt hxlt, zero_add]
      have hydiv : (y.1 + y.2 * p ^ (r - 1)) / p ^ (r - 1) = y.2 := by
        rw [Nat.add_mul_div_right _ _ hMpos, Nat.div_eq_of_lt hylt, zero_add]
      rw [← hxdiv, ← hydiv, heq']
    exact Prod.ext hb_eq ha_eq
  · intro j hj
    obtain ⟨b, hb, a, ha, rfl⟩ := (unitsBelow_decomp hp hr).mp hj
    exact ⟨(b, a), mem_product.mpr ⟨hb, mem_range.mpr ha⟩, rfl⟩
  · intro x hx
    rfl

/- Algebraic expansion of `(1+x)^{-2}`. -/

lemma inv_sq_expand (x : ℚ) (hx : 1 + x ≠ 0) :
    (1 + x)⁻¹ ^ 2 = 1 - 2 * x + (3 * x ^ 2 + 2 * x ^ 3) / (1 + x) ^ 2 := by
  field_simp [hx]
  ring

lemma inv_sq_of_add (b a M : ℕ) (hb : 0 < b) :
    ((b + a * M : ℕ) : ℚ)⁻¹ ^ 2 =
      (b : ℚ)⁻¹ ^ 2 * (1 + (a : ℚ) * M / b)⁻¹ ^ 2 := by
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hcast : ((b + a * M : ℕ) : ℚ) = (b : ℚ) + (a : ℚ) * (M : ℚ) := by norm_cast
  rw [hcast]
  field_simp [hb0]

lemma one_add_div_ne_zero {b a M : ℕ} (hb : 0 < b)
    (hsum : (b + a * M : ℕ) ≠ 0) :
    (1 : ℚ) + (a : ℚ) * M / b ≠ 0 := by
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have : ((b + a * M : ℕ) : ℚ) = (b : ℚ) * (1 + (a : ℚ) * M / b) := by
    have hcast : ((b + a * M : ℕ) : ℚ) = (b : ℚ) + (a : ℚ) * (M : ℚ) := by norm_cast
    rw [hcast]
    field_simp [hb0]
  intro h
  have : ((b + a * M : ℕ) : ℚ) = 0 := by rw [this, h, mul_zero]
  exact (Nat.cast_ne_zero.mpr hsum) this

/-! ### Elementary power-sum and inverse-power expansions -/

lemma sum_range_id_eq (n : ℕ) :
    ∑ a ∈ range n, (a : ℚ) = (n : ℚ) * ((n - 1 : ℕ) : ℚ) / 2 := by
  have heven : 2 ∣ n * (n - 1) := even_iff_two_dvd.mp (Nat.even_mul_pred_self n)
  calc ∑ a ∈ range n, (a : ℚ)
      = ((∑ a ∈ range n, a : ℕ) : ℚ) := by simp
    _ = ((n * (n - 1) / 2 : ℕ) : ℚ) := by rw [sum_range_id]
    _ = ((n * (n - 1) : ℕ) : ℚ) / 2 := Nat.cast_div heven two_ne_zero
    _ = (n : ℚ) * ((n - 1 : ℕ) : ℚ) / 2 := by push_cast; rfl

lemma padicValRat_sum_range_id {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) :
    padicValRat p (∑ a ∈ range p, (a : ℚ)) = 1 := by
  rw [sum_range_id_eq]
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hpm0 : ((p - 1 : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hp.out.one_lt).ne'
  have hnum0 : (p : ℚ) * ((p - 1 : ℕ) : ℚ) ≠ 0 := mul_ne_zero hp0 hpm0
  rw [padicValRat.div hnum0 h2, padicValRat.mul hp0 hpm0, padicValRat.self hp.out.one_lt,
    padicValRat_two hp3]
  have hvpm : padicValRat p ((p - 1 : ℕ) : ℚ) = 0 := by
    refine padicValRat_of_nat_not_dvd ?_
    intro h
    have : p ≤ p - 1 := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.out.one_lt) h
    omega
  rw [hvpm, add_zero, sub_zero]

/-- `(1+x)^t = 1 + t x + ∑_{k=2}^t C(t,k) x^k`. -/
lemma one_add_pow_eq (t : ℕ) (x : ℚ) :
    (1 + x) ^ t = 1 + (t : ℚ) * x + ∑ k ∈ Icc 2 t, (t.choose k : ℚ) * x ^ k := by
  rw [add_comm 1 x, add_pow]
  by_cases ht : t ≤ 1
  · have hI : Icc 2 t = ∅ := by
      ext k; simp [mem_Icc]; omega
    rw [hI, sum_empty]
    interval_cases t <;> simp [range]; ring
  · have h2 : 2 ≤ t := by omega
    have hrange : range (t + 1) = insert 0 (insert 1 (Icc 2 t)) := by
      ext k
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    have h0 : 0 ∉ insert 1 (Icc 2 t) := by simp [mem_Icc]
    have h1 : 1 ∉ Icc 2 t := by simp [mem_Icc]
    rw [hrange, sum_insert h0, sum_insert h1]
    simp [choose_zero_right, choose_one_right, one_pow]
    ring

lemma one_add_pow_sub_linear (t : ℕ) (x : ℚ) :
    (1 + x) ^ t - 1 - (t : ℚ) * x = ∑ k ∈ Icc 2 t, (t.choose k : ℚ) * x ^ k := by
  linarith [one_add_pow_eq t x]

lemma padicValRat_choose_mul_pow {p t k : ℕ} [Fact p.Prime] {x : ℚ}
    (hx0 : x ≠ 0) (hk : 2 ≤ k) (hx : 1 ≤ padicValRat p x) :
    (t.choose k : ℚ) * x ^ k = 0 ∨
      2 * padicValRat p x ≤ padicValRat p ((t.choose k : ℚ) * x ^ k) := by
  by_cases h0 : (t.choose k : ℚ) * x ^ k = 0
  · exact Or.inl h0
  · right
    have hxk : x ^ k ≠ 0 := pow_ne_zero k hx0
    have hch : (t.choose k : ℚ) ≠ 0 := fun h => h0 (by simp [h])
    rw [padicValRat.mul hch hxk, padicValRat.pow hx0]
    have hch0 : 0 ≤ padicValRat p (t.choose k : ℚ) :=
      zero_le_padicValRat_of_nat _
    have hk2 : (2 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    nlinarith

lemma padicValRat_one_add_pow_sub_linear {p t : ℕ} [Fact p.Prime] {x : ℚ}
    (hx0 : x ≠ 0) (hx : 1 ≤ padicValRat p x) :
    (1 + x) ^ t - 1 - (t : ℚ) * x = 0 ∨
      2 * padicValRat p x ≤ padicValRat p ((1 + x) ^ t - 1 - (t : ℚ) * x) := by
  rw [one_add_pow_sub_linear]
  refine padicValRat_sum_ge (Icc 2 t) (fun k => (t.choose k : ℚ) * x ^ k)
    (2 * padicValRat p x) ?_
  intro k hk
  rw [mem_Icc] at hk
  exact padicValRat_choose_mul_pow hx0 hk.1 hx

lemma padicValRat_nat_nonneg {p n : ℕ} [Fact p.Prime] :
    0 ≤ padicValRat p (n : ℚ) :=
  zero_le_padicValRat_of_nat n

lemma padicValRat_mul_nat_left {p : ℕ} [Fact p.Prime] (n : ℕ) {x : ℚ}
    (hx0 : x ≠ 0) :
    (n : ℚ) * x = 0 ∨ padicValRat p x ≤ padicValRat p ((n : ℚ) * x) := by
  by_cases hn : (n : ℚ) = 0
  · left; simp [hn]
  · right
    rw [padicValRat.mul hn hx0]
    linarith [padicValRat_nat_nonneg (p := p) (n := n)]

/-- If `v(A) ≥ m` and `v(B) ≥ m` then `v(A+B) ≥ m`. -/
lemma padicValRat_add_ge {p : ℕ} [Fact p.Prime] {A B : ℚ} {m : ℤ}
    (hA : A = 0 ∨ m ≤ padicValRat p A)
    (hB : B = 0 ∨ m ≤ padicValRat p B) :
    A + B = 0 ∨ m ≤ padicValRat p (A + B) := by
  rcases hA with hA | hA
  · simpa [hA] using hB
  · rcases hB with hB | hB
    · simpa [hB] using Or.inr hA
    · by_cases h0 : A + B = 0
      · exact Or.inl h0
      · exact Or.inr (le_trans (le_min hA hB) (padicValRat.min_le_padicValRat_add h0))

/-- If `v(x) ≥ 1` then `v((1+x)^t - 1) ≥ v(x)`. -/
lemma padicValRat_one_add_pow_sub_one {p t : ℕ} [Fact p.Prime] {x : ℚ}
    (hx0 : x ≠ 0) (hx : 1 ≤ padicValRat p x) :
    (1 + x) ^ t - 1 = 0 ∨ padicValRat p x ≤ padicValRat p ((1 + x) ^ t - 1) := by
  have : (1 + x) ^ t - 1 = (t : ℚ) * x + ((1 + x) ^ t - 1 - (t : ℚ) * x) := by ring
  rw [this]
  refine padicValRat_add_ge (padicValRat_mul_nat_left t hx0) ?_
  rcases padicValRat_one_add_pow_sub_linear (p := p) (t := t) hx0 hx with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans (by nlinarith) h)

/-- If `v(x) ≥ 1` and `1+x` is a `p`-unit then `v((1+x)^{-t} - 1 + t x) ≥ 2 v(x)`. -/
lemma padicValRat_inv_pow_sub_linear {p t : ℕ} [Fact p.Prime] {x : ℚ}
    (hx0 : x ≠ 0) (hx : 1 ≤ padicValRat p x)
    (h1x : 1 + x ≠ 0) (hv1x : padicValRat p (1 + x) = 0) :
    (1 + x)⁻¹ ^ t - 1 + (t : ℚ) * x = 0 ∨
      2 * padicValRat p x ≤ padicValRat p ((1 + x)⁻¹ ^ t - 1 + (t : ℚ) * x) := by
  have hu : (1 + x) ^ t ≠ 0 := pow_ne_zero t h1x
  have hid : (1 + x)⁻¹ ^ t - 1 + (t : ℚ) * x =
      (1 - (1 + x) ^ t + (t : ℚ) * x * (1 + x) ^ t) / (1 + x) ^ t := by
    have hinv : (1 + x)⁻¹ ^ t = ((1 + x) ^ t)⁻¹ := by rw [inv_pow]
    rw [hinv, inv_eq_one_div]
    field_simp [hu]
  have hvden : padicValRat p ((1 + x) ^ t) = 0 := by
    rw [padicValRat.pow h1x, hv1x, mul_zero]
  have hnum_eq : 1 - (1 + x) ^ t + (t : ℚ) * x * (1 + x) ^ t =
      -((1 + x) ^ t - 1 - (t : ℚ) * x) + (t : ℚ) * x * ((1 + x) ^ t - 1) := by
    ring
  have hA : -((1 + x) ^ t - 1 - (t : ℚ) * x) = 0 ∨
      2 * padicValRat p x ≤ padicValRat p (-((1 + x) ^ t - 1 - (t : ℚ) * x)) := by
    rw [padicValRat_neg, neg_eq_zero]
    exact padicValRat_one_add_pow_sub_linear (p := p) (t := t) hx0 hx
  have hB : (t : ℚ) * x * ((1 + x) ^ t - 1) = 0 ∨
      2 * padicValRat p x ≤ padicValRat p ((t : ℚ) * x * ((1 + x) ^ t - 1)) := by
    by_cases h0 : (t : ℚ) * x * ((1 + x) ^ t - 1) = 0
    · exact Or.inl h0
    · right
      have htx0 : (t : ℚ) * x ≠ 0 := fun h => h0 (by simp [h])
      have hpm0 : (1 + x) ^ t - 1 ≠ 0 := fun h => h0 (by simp [h])
      rw [padicValRat.mul htx0 hpm0]
      have hvtx : padicValRat p x ≤ padicValRat p ((t : ℚ) * x) :=
        (padicValRat_mul_nat_left t hx0).resolve_left (fun h => htx0 h)
      have hvpm : padicValRat p x ≤ padicValRat p ((1 + x) ^ t - 1) :=
        (padicValRat_one_add_pow_sub_one (p := p) (t := t) hx0 hx).resolve_left hpm0
      nlinarith
  have hvnum : 1 - (1 + x) ^ t + (t : ℚ) * x * (1 + x) ^ t = 0 ∨
      2 * padicValRat p x ≤
        padicValRat p (1 - (1 + x) ^ t + (t : ℚ) * x * (1 + x) ^ t) := by
    rw [hnum_eq]
    exact padicValRat_add_ge hA hB
  rw [hid]
  rcases hvnum with h0 | hge
  · left; simp [h0]
  · by_cases hz : (1 - (1 + x) ^ t + (t : ℚ) * x * (1 + x) ^ t) / (1 + x) ^ t = 0
    · left; exact hz
    · right
      have hnum0 : 1 - (1 + x) ^ t + (t : ℚ) * x * (1 + x) ^ t ≠ 0 := by
        intro h; exact hz (by simp [h])
      rw [padicValRat.div hnum0 hu, hvden, sub_zero]
      exact hge

lemma inv_pow_of_add (b a M t : ℕ) (hb : 0 < b) :
    ((b + a * M : ℕ) : ℚ)⁻¹ ^ t =
      (b : ℚ)⁻¹ ^ t * (1 + (a : ℚ) * (M : ℚ) / (b : ℚ))⁻¹ ^ t := by
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb.ne'
  have hcast : ((b + a * M : ℕ) : ℚ) = (b : ℚ) + (a : ℚ) * (M : ℚ) := by norm_cast
  rw [hcast]
  have : (b : ℚ) + (a : ℚ) * (M : ℚ) =
      (b : ℚ) * (1 + (a : ℚ) * (M : ℚ) / (b : ℚ)) := by field_simp [hb0]
  rw [this, mul_inv, mul_pow, inv_pow, inv_pow]

/-- Local coordinate `x = a * p^{r-1} / b`. -/
def localX (p r b a : ℕ) : ℚ :=
  (a : ℚ) * ((p ^ (r - 1) : ℕ) : ℚ) / (b : ℚ)

lemma localX_ne_zero {p r b a : ℕ} [hp : Fact p.Prime]
    (hb : b ∈ unitsBelow p (r - 1)) (ha0 : a ≠ 0) :
    localX p r b a ≠ 0 := by
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_mem_unitsBelow hb).ne'
  have ha0q : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha0
  have hM0 : ((p ^ (r - 1) : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.out.ne_zero)
  exact div_ne_zero (mul_ne_zero ha0q hM0) hb0

lemma padicValRat_localX {p r b a : ℕ} [hp : Fact p.Prime]
    (hb : b ∈ unitsBelow p (r - 1)) (ha0 : a ≠ 0) :
    padicValRat p (localX p r b a) =
      padicValRat p (a : ℚ) + ((r - 1 : ℕ) : ℤ) := by
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_mem_unitsBelow hb).ne'
  have ha0q : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ha0
  have hM0 : ((p ^ (r - 1) : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.out.ne_zero)
  have hvM : padicValRat p ((p : ℚ) ^ (r - 1)) = ((r - 1 : ℕ) : ℤ) := padicValRat_p_pow
  have hvb : padicValRat p (b : ℚ) = 0 :=
    padicValRat_of_nat_not_dvd (not_dvd_of_mem_unitsBelow hb)
  unfold localX
  rw [padicValRat.div (mul_ne_zero ha0q hM0) hb0, padicValRat.mul ha0q hM0,
    Nat.cast_pow, hvM, hvb]
  ring

lemma padicValRat_localX_ge {p r b a : ℕ} [hp : Fact p.Prime]
    (hr : 2 ≤ r) (hb : b ∈ unitsBelow p (r - 1)) (ha0 : a ≠ 0) :
    1 ≤ padicValRat p (localX p r b a) := by
  rw [padicValRat_localX hb ha0]
  have hva : 0 ≤ padicValRat p (a : ℚ) := padicValRat_nat_nonneg
  have : (1 : ℤ) ≤ ((r - 1 : ℕ) : ℤ) := by
    have : 1 ≤ r - 1 := by omega
    exact_mod_cast this
  linarith

lemma one_add_localX_spec {p r b a : ℕ} [hp : Fact p.Prime]
    (hr : 2 ≤ r) (hb : b ∈ unitsBelow p (r - 1)) (ha : a < p) :
    1 + localX p r b a ≠ 0 ∧ padicValRat p (1 + localX p r b a) = 0 := by
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_mem_unitsBelow hb).ne'
  have hmem : b + a * p ^ (r - 1) ∈ unitsBelow p r :=
    (unitsBelow_decomp hp.out hr).mpr ⟨b, hb, a, ha, rfl⟩
  have hsum0 : (b + a * p ^ (r - 1) : ℕ) ≠ 0 := (pos_of_mem_unitsBelow hmem).ne'
  have hcast : ((b + a * p ^ (r - 1) : ℕ) : ℚ) = (b : ℚ) * (1 + localX p r b a) := by
    unfold localX
    have : ((b + a * p ^ (r - 1) : ℕ) : ℚ) =
        (b : ℚ) + (a : ℚ) * ((p ^ (r - 1) : ℕ) : ℚ) := by norm_cast
    field_simp [hb0]
    exact this
  have hxne : 1 + localX p r b a ≠ 0 := by
    intro h
    have : ((b + a * p ^ (r - 1) : ℕ) : ℚ) = 0 := by rw [hcast, h, mul_zero]
    exact (Nat.cast_ne_zero.mpr hsum0) this
  have hvb : padicValRat p (b : ℚ) = 0 :=
    padicValRat_of_nat_not_dvd (not_dvd_of_mem_unitsBelow hb)
  have hvsum : padicValRat p ((b + a * p ^ (r - 1) : ℕ) : ℚ) = 0 :=
    padicValRat_of_nat_not_dvd (not_dvd_of_mem_unitsBelow hmem)
  have hv1x : padicValRat p (1 + localX p r b a) = 0 := by
    have : 1 + localX p r b a = ((b + a * p ^ (r - 1) : ℕ) : ℚ) / (b : ℚ) := by
      rw [eq_div_iff_mul_eq hb0, mul_comm, hcast]
    rw [this, padicValRat.div (Nat.cast_ne_zero.mpr hsum0) hb0, hvsum, hvb, sub_zero]
  exact ⟨hxne, hv1x⟩

def remLocal (p r b a t : ℕ) : ℚ :=
  (1 + localX p r b a)⁻¹ ^ t - 1 + (t : ℚ) * localX p r b a

lemma remLocal_eq (p r b a t : ℕ) :
    (1 + localX p r b a)⁻¹ ^ t =
      1 - (t : ℚ) * localX p r b a + remLocal p r b a t := by
  simp [remLocal]

lemma padicValRat_remLocal {p r b a t : ℕ} [hp : Fact p.Prime]
    (hr : 2 ≤ r) (hb : b ∈ unitsBelow p (r - 1)) (ha : a < p) :
    remLocal p r b a t = 0 ∨
      2 * ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (remLocal p r b a t) := by
  by_cases ha0 : a = 0
  · subst ha0
    have hx : localX p r b 0 = 0 := by simp [localX]
    simp [remLocal, hx]
  · have hx0 := localX_ne_zero (p := p) (r := r) hb ha0
    have hxge := padicValRat_localX_ge (p := p) hr hb ha0
    obtain ⟨h1x, hv1x⟩ := one_add_localX_spec (p := p) hr hb ha
    have h := padicValRat_inv_pow_sub_linear (p := p) (t := t) hx0 hxge h1x hv1x
    have h2 : 2 * ((r - 1 : ℕ) : ℤ) ≤ 2 * padicValRat p (localX p r b a) := by
      have : ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (localX p r b a) := by
        rw [padicValRat_localX hb ha0]
        have hva : 0 ≤ padicValRat p (a : ℚ) := padicValRat_nat_nonneg
        linarith
      nlinarith
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans h2 h)

lemma padicValRat_sum_remLocal {p r b t : ℕ} [hp : Fact p.Prime]
    (hr : 2 ≤ r) (hb : b ∈ unitsBelow p (r - 1)) :
    ∑ a ∈ range p, remLocal p r b a t = 0 ∨
      (r : ℤ) ≤ padicValRat p (∑ a ∈ range p, remLocal p r b a t) := by
  have hge := padicValRat_sum_ge (range p) (fun a => remLocal p r b a t)
    (2 * ((r - 1 : ℕ) : ℤ))
    (fun a ha => by
      rw [mem_range] at ha
      exact padicValRat_remLocal hr hb ha)
  have hr2 : (r : ℤ) ≤ 2 * ((r - 1 : ℕ) : ℤ) := by
    have : r ≤ 2 * (r - 1) := by omega
    exact_mod_cast this
  rcases hge with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans hr2 h)

lemma padicValRat_sum_localX {p r b : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p)
    (hr : 2 ≤ r) (hb : b ∈ unitsBelow p (r - 1)) :
    ∑ a ∈ range p, localX p r b a = 0 ∨
      (r : ℤ) ≤ padicValRat p (∑ a ∈ range p, localX p r b a) := by
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_mem_unitsBelow hb).ne'
  have hM0 : ((p ^ (r - 1) : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ hp.out.ne_zero)
  have hfactor : ∑ a ∈ range p, localX p r b a =
      ((p ^ (r - 1) : ℕ) : ℚ) / (b : ℚ) * ∑ a ∈ range p, (a : ℚ) := by
    unfold localX
    calc ∑ a ∈ range p, (a : ℚ) * ((p ^ (r - 1) : ℕ) : ℚ) / (b : ℚ)
        = (∑ a ∈ range p, (a : ℚ) * ((p ^ (r - 1) : ℕ) : ℚ)) / (b : ℚ) := by
          rw [← Finset.sum_div]
      _ = (((p ^ (r - 1) : ℕ) : ℚ) * ∑ a ∈ range p, (a : ℚ)) / (b : ℚ) := by
          congr 1
          refine (Finset.sum_congr rfl (fun _ _ => mul_comm _ _)).trans ?_
          exact (Finset.mul_sum (range p) (fun a => (a : ℚ))
            ((p ^ (r - 1) : ℕ) : ℚ)).symm
      _ = ((p ^ (r - 1) : ℕ) : ℚ) / (b : ℚ) * ∑ a ∈ range p, (a : ℚ) := by
          field_simp [hb0]
  rw [hfactor]
  have hsa := padicValRat_sum_range_id (p := p) hp3
  have hsa0 : ∑ a ∈ range p, (a : ℚ) ≠ 0 := by
    intro h
    have : padicValRat p (0 : ℚ) = 1 := by rw [← h]; exact hsa
    simp at this
  have hvb : padicValRat p (b : ℚ) = 0 :=
    padicValRat_of_nat_not_dvd (not_dvd_of_mem_unitsBelow hb)
  have hvM : padicValRat p ((p : ℚ) ^ (r - 1)) = ((r - 1 : ℕ) : ℤ) := padicValRat_p_pow
  have hquot0 : ((p ^ (r - 1) : ℕ) : ℚ) / (b : ℚ) ≠ 0 := div_ne_zero hM0 hb0
  by_cases h0 : ((p ^ (r - 1) : ℕ) : ℚ) / (b : ℚ) * ∑ a ∈ range p, (a : ℚ) = 0
  · exact Or.inl h0
  · right
    rw [padicValRat.mul hquot0 hsa0, padicValRat.div hM0 hb0, Nat.cast_pow, hvM, hvb, hsa]
    have : ((r - 1 : ℕ) : ℤ) + 1 = (r : ℤ) := by
      have : r - 1 + 1 = r := Nat.sub_add_cancel (by omega)
      exact_mod_cast this
    linarith

/-- Inner fibre: `∑_a (b+aM)^{-t} = b^{-t} (p + δ)` with `v(δ) ≥ r`. -/
lemma inner_sum_delta {p r b t : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p)
    (hr : 2 ≤ r) (hb : b ∈ unitsBelow p (r - 1)) :
    ∃ δ : ℚ, (δ = 0 ∨ (r : ℤ) ≤ padicValRat p δ) ∧
      ∑ a ∈ range p, (((b + a * p ^ (r - 1) : ℕ) : ℚ)⁻¹ ^ t) =
        (b : ℚ)⁻¹ ^ t * ((p : ℚ) + δ) := by
  have hbpos : 0 < b := pos_of_mem_unitsBelow hb
  have hterm : ∀ a ∈ range p,
      (((b + a * p ^ (r - 1) : ℕ) : ℚ)⁻¹ ^ t) =
        (b : ℚ)⁻¹ ^ t * (1 + localX p r b a)⁻¹ ^ t := by
    intro a ha
    simpa [localX] using inv_pow_of_add b a (p ^ (r - 1)) t hbpos
  rw [sum_congr rfl hterm, ← mul_sum]
  refine ⟨-((t : ℚ) * ∑ a ∈ range p, localX p r b a) +
      ∑ a ∈ range p, remLocal p r b a t, ?_, ?_⟩
  · have hS := padicValRat_sum_localX (p := p) (r := r) (b := b) hp3 hr hb
    have hR := padicValRat_sum_remLocal (p := p) (r := r) (b := b) (t := t) hr hb
    have hnegS : -((t : ℚ) * ∑ a ∈ range p, localX p r b a) = 0 ∨
        (r : ℤ) ≤ padicValRat p (-((t : ℚ) * ∑ a ∈ range p, localX p r b a)) := by
      rw [padicValRat_neg, neg_eq_zero]
      rcases hS with hS | hS
      · left; simp [hS]
      · by_cases ht0 : (t : ℚ) = 0
        · left; simp [ht0]
        · by_cases hs0 : ∑ a ∈ range p, localX p r b a = 0
          · left; simp [hs0]
          · right
            rw [padicValRat.mul ht0 hs0]
            have : 0 ≤ padicValRat p (t : ℚ) := padicValRat_nat_nonneg
            linarith
    exact padicValRat_add_ge hnegS hR
  · have : ∑ a ∈ range p, (1 + localX p r b a)⁻¹ ^ t =
        ∑ a ∈ range p, (1 - (t : ℚ) * localX p r b a + remLocal p r b a t) :=
      sum_congr rfl (fun a _ => remLocal_eq p r b a t)
    rw [this, sum_add_distrib, sum_sub_distrib]
    have hones : ∑ _a ∈ range p, (1 : ℚ) = (p : ℚ) := by simp
    have hlin : ∑ a ∈ range p, (t : ℚ) * localX p r b a =
        (t : ℚ) * ∑ a ∈ range p, localX p r b a := by
      simp [mul_sum]
    rw [hones, hlin]
    ring

lemma padicValRat_inv_pow_mem {p r j t : ℕ} [Fact p.Prime]
    (hj : j ∈ unitsBelow p r) :
    padicValRat p (((j : ℚ)⁻¹) ^ t) = 0 :=
  padicValRat_inv_pow_of_not_dvd (not_dvd_of_mem_unitsBelow hj)
    (pos_of_mem_unitsBelow hj).ne'

/-- `H t p r = p · H t p (r-1) + Δ` with `v(Δ) ≥ r`. -/
lemma H_eq_p_H_add {p r t : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 2 ≤ r) :
    ∃ Δ : ℚ, (Δ = 0 ∨ (r : ℤ) ≤ padicValRat p Δ) ∧
      H t p r = (p : ℚ) * H t p (r - 1) + Δ := by
  have hdecomp := H_succ_eq (p := p) (r := r) (t := t) hp.out hr
  -- For each b obtain δ_b
  classical
  let δb : ℕ → ℚ := fun b =>
    if hb : b ∈ unitsBelow p (r - 1) then
      Classical.choose (inner_sum_delta (p := p) (r := r) (b := b) (t := t) hp3 hr hb)
    else 0
  have hδ : ∀ b (hb : b ∈ unitsBelow p (r - 1)),
      (δb b = 0 ∨ (r : ℤ) ≤ padicValRat p (δb b)) ∧
      ∑ a ∈ range p, (((b + a * p ^ (r - 1) : ℕ) : ℚ)⁻¹ ^ t) =
        (b : ℚ)⁻¹ ^ t * ((p : ℚ) + δb b) := by
    intro b hb
    simp only [δb, dif_pos hb]
    exact Classical.choose_spec (inner_sum_delta (p := p) (r := r) (b := b) (t := t) hp3 hr hb)
  refine ⟨∑ b ∈ unitsBelow p (r - 1), (b : ℚ)⁻¹ ^ t * δb b, ?_, ?_⟩
  · refine padicValRat_sum_ge (unitsBelow p (r - 1))
        (fun b => (b : ℚ)⁻¹ ^ t * δb b) r ?_
    intro b hb
    obtain ⟨hval, _⟩ := hδ b hb
    have hvb : padicValRat p (((b : ℚ)⁻¹) ^ t) = 0 :=
      padicValRat_inv_pow_mem hb
    rcases hval with h0 | hge
    · left; simp [h0]
    · by_cases hδ0 : δb b = 0
      · left; simp [hδ0]
      · right
        have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_mem_unitsBelow hb).ne'
        rw [padicValRat.mul (pow_ne_zero t (inv_ne_zero hb0)) hδ0, hvb, zero_add]
        exact hge
  · rw [hdecomp]
    have : ∑ b ∈ unitsBelow p (r - 1),
        ∑ a ∈ range p, (((b + a * p ^ (r - 1) : ℕ) : ℚ)⁻¹ ^ t) =
      ∑ b ∈ unitsBelow p (r - 1), (b : ℚ)⁻¹ ^ t * ((p : ℚ) + δb b) :=
      sum_congr rfl (fun b hb => (hδ b hb).2)
    rw [this]
    simp only [mul_add, sum_add_distrib]
    have hpH : ∑ b ∈ unitsBelow p (r - 1), (b : ℚ)⁻¹ ^ t * (p : ℚ) =
        (p : ℚ) * H t p (r - 1) := by
      unfold H
      simp [mul_comm, Finset.mul_sum]
    rw [hpH]

/-- If `v(H_t^{(s)}) ≥ m` then `v(H_t^{(s+1)}) ≥ min(1+m, s+1)` (here `r = s+1`). -/
lemma padicValRat_H_lift {p r t : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p)
    (hr : 2 ≤ r)
    {m : ℤ} (hprev : H t p (r - 1) = 0 ∨ m ≤ padicValRat p (H t p (r - 1))) :
    H t p r = 0 ∨ min (1 + m) (r : ℤ) ≤ padicValRat p (H t p r) := by
  obtain ⟨Δ, hΔ, hEq⟩ := H_eq_p_H_add (p := p) (r := r) (t := t) hp3 hr
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hleft : (p : ℚ) * H t p (r - 1) = 0 ∨
      1 + m ≤ padicValRat p ((p : ℚ) * H t p (r - 1)) := by
    rcases hprev with h0 | hge
    · left; simp [h0]
    · by_cases hH0 : H t p (r - 1) = 0
      · left; simp [hH0]
      · right
        rw [padicValRat.mul hp0 hH0, padicValRat.self hp.out.one_lt]
        linarith
  have hleft' : (p : ℚ) * H t p (r - 1) = 0 ∨
      min (1 + m) (r : ℤ) ≤ padicValRat p ((p : ℚ) * H t p (r - 1)) := by
    rcases hleft with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (min_le_left _ _) h)
  have hΔ' : Δ = 0 ∨ min (1 + m) (r : ℤ) ≤ padicValRat p Δ := by
    rcases hΔ with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (min_le_right _ _) h)
  rw [hEq]
  exact padicValRat_add_ge hleft' hΔ'

/-- `v(H_t^{(r)}) ≥ r` whenever `p-1 ∤ t`. -/
lemma padicValRat_H_of_not_dvd {p r t : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p)
    (hr : 0 < r) (ht : ¬ (p - 1) ∣ t) :
    H t p r = 0 ∨ (r : ℤ) ≤ padicValRat p (H t p r) := by
  induction r with
  | zero => exact absurd hr (lt_irrefl _)
  | succ r ih =>
    cases r with
    | zero =>
      -- r+1 = 1
      simpa using padicValRat_H_one_of_not_dvd (p := p) (t := t) ht (by omega)
    | succ r' =>
      -- r+1 ≥ 2
      have hr2 : 2 ≤ r' + 1 + 1 := by omega
      have hprev := ih (by omega)
      have hlift := padicValRat_H_lift (p := p) (r := r' + 1 + 1) (t := t) hp3 hr2
        (m := ((r' + 1 : ℕ) : ℤ)) (by
          simpa using hprev)
      have hmin : min (1 + ((r' + 1 : ℕ) : ℤ)) ((r' + 1 + 1 : ℕ) : ℤ) =
          ((r' + 1 + 1 : ℕ) : ℤ) := by
        have heq : (1 : ℤ) + (r' + 1 : ℕ) = ((r' + 1 + 1 : ℕ) : ℤ) := by
          push_cast; ring
        simp [heq]
      simpa [hmin] using hlift

/-- `v(H_t^{(r)}) ≥ r-1` for all `t` (using only `v ≥ 0` at `r = 1`). -/
lemma padicValRat_H_ge_pred {p r t : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p)
    (hr : 0 < r) :
    H t p r = 0 ∨ ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (H t p r) := by
  induction r with
  | zero => exact absurd hr (lt_irrefl _)
  | succ r ih =>
    cases r with
    | zero =>
      simpa using padicValRat_H_nonneg (t := t) (p := p) (r := 1)
    | succ r' =>
      have hr2 : 2 ≤ r' + 1 + 1 := by omega
      have hprev := ih (by omega)
      have hlift := padicValRat_H_lift (p := p) (r := r' + 1 + 1) (t := t) hp3 hr2
        (m := ((r' : ℕ) : ℤ)) (by
          -- v(H^{(r'+1)}) ≥ r'  (since (r'+1)-1 = r')
          simpa using hprev)
      -- min(1+r', r'+2) = 1+r' = (r'+2)-1
      have hmin : min (1 + ((r' : ℕ) : ℤ)) ((r' + 1 + 1 : ℕ) : ℤ) =
          ((r' + 1 : ℕ) : ℤ) := by
        have hle : (1 : ℤ) + (r' : ℤ) ≤ ((r' + 1 + 1 : ℕ) : ℤ) := by
          push_cast; linarith
        have heq : (1 : ℤ) + (r' : ℤ) = ((r' + 1 : ℕ) : ℤ) := by
          push_cast; ring
        rw [min_eq_left hle, heq]
      have : ((r' + 1 + 1 - 1 : ℕ) : ℤ) = ((r' + 1 : ℕ) : ℤ) := by simp
      rw [this]
      exact hlift.elim Or.inl (fun h => Or.inr (hmin ▸ h))

/- Convenient special cases -/

lemma padicValRat_H1 {p r : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    H 1 p r = 0 ∨ (r : ℤ) ≤ padicValRat p (H 1 p r) :=
  padicValRat_H_of_not_dvd hp3 hr (p_sub_one_not_dvd_one (by omega))

lemma padicValRat_H2 {p r : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    H 2 p r = 0 ∨ (r : ℤ) ≤ padicValRat p (H 2 p r) :=
  padicValRat_H_of_not_dvd (by omega) hr (p_sub_one_not_dvd_two hp5)

lemma p_sub_one_not_dvd_three' {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) : ¬ (p - 1) ∣ 3 := by
  intro h
  have hle : p - 1 ≤ 3 := Nat.le_of_dvd (by omega) h
  have hp2 : 2 ≤ p - 1 := by omega
  have : p - 1 = 2 ∨ p - 1 = 3 := by omega
  rcases this with h2 | h3
  · have : 2 ∣ 3 := by simpa [h2] using h
    omega
  · have : p = 4 := by omega
    subst this
    exact (by decide : ¬ Nat.Prime 4) hp

lemma padicValRat_H3 {p r : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    H 3 p r = 0 ∨ (r : ℤ) ≤ padicValRat p (H 3 p r) :=
  padicValRat_H_of_not_dvd hp3 hr (p_sub_one_not_dvd_three' hp.out hp3)

lemma padicValRat_H1_wolstenholme {p r : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hr : 0 < r) :
    H 1 p r = 0 ∨ (2 * r : ℤ) ≤ padicValRat p (H 1 p r) := by
  have hθ := padicValRat_theta_ge (p := p) (r := r) (by omega) hr
  have h2 := padicValRat_H2 (p := p) (r := r) hp5 hr
  have hN : (p : ℚ) ^ r ≠ 0 := pow_ne_zero r (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hhalf : ((p : ℚ) ^ r) * H 2 p r / 2 = 0 ∨
      (2 * r : ℤ) ≤ padicValRat p ((p : ℚ) ^ r * H 2 p r / 2) := by
    rcases h2 with h0 | hge
    · left; simp [h0]
    · by_cases hH0 : H 2 p r = 0
      · left; simp [hH0]
      · right
        have h2ne : (2 : ℚ) ≠ 0 := two_ne_zero
        rw [padicValRat.div (mul_ne_zero hN hH0) h2ne, padicValRat.mul hN hH0,
          padicValRat_p_pow, padicValRat_two (by omega)]
        linarith
  -- H1 = θ - N H2 / 2
  have hid : H 1 p r =
      (H 1 p r + (p : ℚ) ^ r * H 2 p r / 2) +
        (-((p : ℚ) ^ r * H 2 p r / 2)) := by ring
  rw [hid]
  refine padicValRat_add_ge ?_ ?_
  · exact hθ
  · rw [padicValRat_neg, neg_eq_zero]
    exact hhalf

/- Product `P_α` and its expansion -/

def Pprod (α p r : ℕ) : ℚ :=
  ∏ j ∈ unitsBelow p r, (1 + ((α - 1 : ℕ) : ℚ) * (p ^ r : ℚ) / (j : ℚ))

lemma choose_eq_Pprod {α p r : ℕ} (hp : p.Prime) (hr : 0 < r) (hα : 1 ≤ α) :
    ((α * p ^ r).choose (p ^ r) : ℚ) =
      ((α * p ^ (r - 1)).choose (p ^ (r - 1)) : ℚ) * Pprod α p r :=
  choose_ratio_eq_prod hp hr hα

lemma a_diff_eq {p r : ℕ} (hp : p.Prime) (hr : 0 < r) :
    (a (p ^ r) : ℚ) - (a (p ^ (r - 1)) : ℚ) =
      (((3 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℚ) ^ 2) *
          (Pprod 3 p r ^ 2 - 1) -
        27 * ((2 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℚ) *
          (Pprod 2 p r - 1) := by
  have h3 := choose_eq_Pprod (α := 3) hp hr (by omega)
  have h2 := choose_eq_Pprod (α := 2) hp hr (by omega)
  have haN : (a (p ^ r) : ℚ) =
      (((3 * p ^ r).choose (p ^ r) : ℚ) ^ 2) -
        27 * ((2 * p ^ r).choose (p ^ r) : ℚ) := by
    simp [a]
  have haM : (a (p ^ (r - 1)) : ℚ) =
      (((3 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℚ) ^ 2) -
        27 * ((2 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℚ) := by
    simp [a]
  rw [haN, haM, h3, h2]
  ring

/-- Symmetric means of the inverses. -/
def eSym (m p r : ℕ) : ℚ :=
  ∑ s ∈ (unitsBelow p r).powersetCard m, ∏ j ∈ s, (j : ℚ)⁻¹

lemma eSym_zero (p r : ℕ) : eSym 0 p r = 1 := by
  simp [eSym, powersetCard_zero, prod_empty]

lemma eSym_one (p r : ℕ) : eSym 1 p r = H 1 p r := by
  unfold eSym H
  refine Eq.symm (Finset.sum_bij (fun j _ => ({j} : Finset ℕ)) ?_ ?_ ?_ ?_)
  · intro j hj
    exact mem_powersetCard.mpr ⟨singleton_subset_iff.mpr hj, card_singleton _⟩
  · intro j1 _ j2 _ h
    exact singleton_injective h
  · intro s hs
    obtain ⟨j, hj, rfl⟩ := card_eq_one.mp (mem_powersetCard.mp hs).2
    exact ⟨j, (mem_powersetCard.mp hs).1 (by simp), rfl⟩
  · intro j hj
    simp [pow_one]

lemma padicValRat_prod_nonneg {p : ℕ} [Fact p.Prime] {ι : Type*}
    (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, f i = 0 ∨ 0 ≤ padicValRat p (f i)) :
    (∏ i ∈ s, f i) = 0 ∨ 0 ≤ padicValRat p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => right; simp
  | insert a s ha ih =>
    rw [prod_insert ha]
    have ha' := hf a (mem_insert_self a s)
    have ih' := ih (fun i hi => hf i (mem_insert_of_mem hi))
    rcases ha' with ha0 | hage
    · left; simp [ha0]
    · rcases ih' with ih0 | ihge
      · left; simp [ih0]
      · by_cases h0 : f a * ∏ i ∈ s, f i = 0
        · left; exact h0
        · right
          have ha0 : f a ≠ 0 := fun h => h0 (by simp [h])
          have hp0 : (∏ i ∈ s, f i) ≠ 0 := fun h => h0 (by simp [h])
          rw [padicValRat.mul ha0 hp0]
          linarith

lemma padicValRat_eSym {p r m : ℕ} [Fact p.Prime] :
    eSym m p r = 0 ∨ 0 ≤ padicValRat p (eSym m p r) := by
  refine padicValRat_sum_ge ((unitsBelow p r).powersetCard m)
    (fun s => ∏ j ∈ s, (j : ℚ)⁻¹) 0 ?_
  intro s hs
  refine padicValRat_prod_nonneg s (fun j => (j : ℚ)⁻¹) ?_
  intro j hj
  have hjU : j ∈ unitsBelow p r := (mem_powersetCard.mp hs).1 hj
  right
  have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pos_of_mem_unitsBelow hjU).ne'
  rw [padicValRat.inv, padicValRat_of_nat_not_dvd (not_dvd_of_mem_unitsBelow hjU)]
  simp

lemma Pprod_eq_sum_powerset (α p r : ℕ) :
    Pprod α p r =
      ∑ s ∈ (unitsBelow p r).powerset,
        ∏ j ∈ s, (((α - 1 : ℕ) : ℚ) * (p ^ r : ℚ) / (j : ℚ)) := by
  unfold Pprod
  exact prod_one_add (unitsBelow p r)

lemma prod_y_eq {α p r : ℕ} (s : Finset ℕ) :
    ∏ j ∈ s, (((α - 1 : ℕ) : ℚ) * (p ^ r : ℚ) / (j : ℚ)) =
      (((α - 1 : ℕ) : ℚ) * (p ^ r : ℚ)) ^ s.card * ∏ j ∈ s, (j : ℚ)⁻¹ := by
  simp [div_eq_mul_inv, prod_mul_distrib, prod_const, mul_pow, mul_left_comm, mul_comm]

lemma Pprod_eq_sum_eSym (α p r : ℕ) :
    Pprod α p r =
      ∑ m ∈ range ((unitsBelow p r).card + 1),
        (((α - 1 : ℕ) : ℚ) * (p ^ r : ℚ)) ^ m * eSym m p r := by
  rw [Pprod_eq_sum_powerset, sum_powerset]
  refine Finset.sum_congr rfl ?_
  intro m hm
  simp only [eSym]
  trans ∑ s ∈ (unitsBelow p r).powersetCard m,
      (((α - 1 : ℕ) : ℚ) * (p ^ r : ℚ)) ^ m * ∏ j ∈ s, (j : ℚ)⁻¹
  · refine Finset.sum_congr rfl ?_
    intro s hs
    have hcard : s.card = m := (mem_powersetCard.mp hs).2
    rw [prod_y_eq, hcard]
  · rw [← mul_sum]

lemma padicValRat_term_eSym {p r m β : ℕ} [hp : Fact p.Prime] :
    ((β : ℚ) * ((p ^ r : ℕ) : ℚ)) ^ m * eSym m p r = 0 ∨
      (m * r : ℤ) ≤ padicValRat p
        (((β : ℚ) * ((p ^ r : ℕ) : ℚ)) ^ m * eSym m p r) := by
  by_cases h0 : ((β : ℚ) * ((p ^ r : ℕ) : ℚ)) ^ m * eSym m p r = 0
  · exact Or.inl h0
  · right
    have he : eSym m p r ≠ 0 := fun h => h0 (by simp [h])
    have hpow0 : ((β : ℚ) * ((p ^ r : ℕ) : ℚ)) ^ m ≠ 0 :=
      fun h => h0 (by rw [h, zero_mul])
    rw [padicValRat.mul hpow0 he]
    have hvE : 0 ≤ padicValRat p (eSym m p r) :=
      (padicValRat_eSym (p := p) (r := r) (m := m)).resolve_left he
    have hN0 : ((p ^ r : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (pow_ne_zero r hp.out.ne_zero)
    by_cases hm : m = 0
    · subst m
      simp
      exact hvE
    · have hβ : (β : ℚ) ≠ 0 := by
        intro h
        exact hpow0 (by rw [h, zero_mul, zero_pow hm])
      have hmul0 : (β : ℚ) * ((p ^ r : ℕ) : ℚ) ≠ 0 := mul_ne_zero hβ hN0
      have hva : 0 ≤ padicValRat p (β : ℚ) := padicValRat_nat_nonneg
      have hvN : padicValRat p ((p : ℚ) ^ r) = r := padicValRat_p_pow
      rw [padicValRat.pow hmul0, padicValRat.mul hβ hN0, Nat.cast_pow, hvN]
      nlinarith

/- Valuation arithmetic utilities -/

lemma padicValRat_mul_ge {p : ℕ} [Fact p.Prime] {A B : ℚ} {m n : ℤ}
    (hA : A = 0 ∨ m ≤ padicValRat p A)
    (hB : B = 0 ∨ n ≤ padicValRat p B) :
    A * B = 0 ∨ m + n ≤ padicValRat p (A * B) := by
  rcases hA with hA | hA
  · left; simp [hA]
  · rcases hB with hB | hB
    · left; simp [hB]
    · by_cases h0 : A * B = 0
      · exact Or.inl h0
      · right
        have hA0 : A ≠ 0 := left_ne_zero_of_mul h0
        have hB0 : B ≠ 0 := right_ne_zero_of_mul h0
        rw [padicValRat.mul hA0 hB0]
        linarith

lemma padicValRat_div_ge {p : ℕ} [Fact p.Prime] {A B : ℚ} {m n : ℤ}
    (hA : A = 0 ∨ m ≤ padicValRat p A) (hB0 : B ≠ 0)
    (hB : padicValRat p B = n) :
    A / B = 0 ∨ m - n ≤ padicValRat p (A / B) := by
  rcases hA with hA | hA
  · left; simp [hA]
  · by_cases h0 : A / B = 0
    · exact Or.inl h0
    · right
      have hA0 : A ≠ 0 := fun h => h0 (by simp [h])
      rw [padicValRat.div hA0 hB0, hB]
      linarith

lemma padicValRat_pow_ge {p : ℕ} [Fact p.Prime] {A : ℚ} {m : ℤ} (k : ℕ)
    (hA : A = 0 ∨ m ≤ padicValRat p A) :
    A ^ k = 0 ∨ (k : ℤ) * m ≤ padicValRat p (A ^ k) := by
  rcases hA with hA | hA
  · cases k with
    | zero => right; simp
    | succ k => left; simp [hA]
  · by_cases h0 : A ^ k = 0
    · exact Or.inl h0
    · right
      by_cases hk : k = 0
      · subst k; simp
      · have hA0 : A ≠ 0 := fun h => h0 (by rw [h, zero_pow hk])
        rw [padicValRat.pow hA0]
        nlinarith

lemma padicValRat_mul_nat_ge {p : ℕ} [Fact p.Prime] (c : ℕ) {A : ℚ} {m : ℤ}
    (hA : A = 0 ∨ m ≤ padicValRat p A) :
    (c : ℚ) * A = 0 ∨ m ≤ padicValRat p ((c : ℚ) * A) := by
  have hc : (c : ℚ) = 0 ∨ 0 ≤ padicValRat p (c : ℚ) := Or.inr padicValRat_nat_nonneg
  have h := padicValRat_mul_ge hc hA
  simpa using h

lemma padicValRat_neg_ge {p : ℕ} [Fact p.Prime] {A : ℚ} {m : ℤ}
    (hA : A = 0 ∨ m ≤ padicValRat p A) :
    -A = 0 ∨ m ≤ padicValRat p (-A) := by
  simpa [padicValRat_neg, neg_eq_zero] using hA

lemma unitsBelow_cast_ne_zero {p r j : ℕ} (hj : j ∈ unitsBelow p r) :
    (j : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (pos_of_mem_unitsBelow hj).ne'

lemma sub_cast_ne_zero {p r j : ℕ} (hp : p.Prime) (hr : 0 < r)
    (hj : j ∈ unitsBelow p r) :
    ((p ^ r - j : ℕ) : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.sub_pos_of_lt (lt_pow_of_mem_unitsBelow hp hr hj)).ne'

lemma padicValRat_mem_units {p r j : ℕ} [Fact p.Prime] (hj : j ∈ unitsBelow p r) :
    padicValRat p (j : ℚ) = 0 :=
  padicValRat_of_nat_not_dvd (not_dvd_of_mem_unitsBelow hj)

lemma padicValRat_sub_mem_units {p r j : ℕ} [hp : Fact p.Prime] (hr : 0 < r)
    (hj : j ∈ unitsBelow p r) :
    padicValRat p ((p ^ r - j : ℕ) : ℚ) = 0 :=
  padicValRat_of_nat_not_dvd
    (not_dvd_of_mem_unitsBelow (sub_mem_unitsBelow hp.out hr hj))

lemma one_mem_unitsBelow {p r : ℕ} (hp : p.Prime) (hr : 0 < r) :
    1 ∈ unitsBelow p r := by
  refine mem_unitsBelow.mpr ⟨by omega, Nat.one_le_pow r p hp.pos, ?_⟩
  exact Nat.not_dvd_of_pos_of_lt (by omega) hp.one_lt

lemma two_mem_unitsBelow {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 0 < r) :
    2 ∈ unitsBelow p r := by
  have hpr : 2 ≤ p ^ r :=
    (by omega : 2 ≤ p).trans (Nat.le_self_pow hr.ne' p)
  exact mem_unitsBelow.mpr ⟨by omega, hpr, prime_not_dvd_two hp hp3⟩

lemma four_mem_unitsBelow {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) :
    4 ∈ unitsBelow p r := by
  have hpr : 4 ≤ p ^ r := by
    have hpow : p ^ 2 ≤ p ^ r := Nat.pow_le_pow_right hp.pos hr
    have h4 : 4 ≤ p ^ 2 :=
      calc 4 ≤ 9 := by omega
        _ = 3 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
    exact h4.trans hpow
  refine mem_unitsBelow.mpr ⟨by omega, hpr, ?_⟩
  intro hdvd
  have : p ∣ 2 * 2 := by simpa using hdvd
  have hp2 : p = 2 := by
    rcases hp.dvd_mul.mp this with h | h
    · rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
      · exact absurd h hp.ne_one
      · exact h
    · rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
      · exact absurd h hp.ne_one
      · exact h
  omega

lemma card_unitsBelow_ge_two {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 0 < r) :
    2 ≤ (unitsBelow p r).card := by
  have hsub : ({1, 2} : Finset ℕ) ⊆ unitsBelow p r := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact one_mem_unitsBelow hp hr
    · exact two_mem_unitsBelow hp hp3 hr
  have hcard : ({1, 2} : Finset ℕ).card = 2 := by simp
  exact hcard ▸ card_le_card hsub

lemma card_unitsBelow_ge_three {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 2 ≤ r) :
    3 ≤ (unitsBelow p r).card := by
  have hsub : ({1, 2, 4} : Finset ℕ) ⊆ unitsBelow p r := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact one_mem_unitsBelow hp (by omega)
    · exact two_mem_unitsBelow hp hp3 (by omega)
    · exact four_mem_unitsBelow hp hp3 hr
  have hcard : ({1, 2, 4} : Finset ℕ).card = 3 := by simp
  exact hcard ▸ card_le_card hsub

/- Pairing identities for inverse cubes -/

lemma inv_cube_pair {N j : ℕ} (hj0 : 0 < j) (hjN : j < N) :
    (1 : ℚ) / (j : ℚ) ^ 3 + 1 / ((N - j : ℕ) : ℚ) ^ 3 =
      (N : ℚ) * (-3 / ((j : ℚ) ^ 2 * ((N - j : ℕ) : ℚ) ^ 2) +
        (N : ℚ) ^ 2 / ((j : ℚ) ^ 3 * ((N - j : ℕ) : ℚ) ^ 3)) := by
  have hjq : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj0.ne'
  have hNq : ((N - j : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.sub_pos_of_lt hjN).ne'
  have hcast : ((N - j : ℕ) : ℚ) = (N : ℚ) - (j : ℚ) := by
    norm_cast
    exact Int.natCast_sub (le_of_lt hjN) ▸ by norm_cast
  have hN0 : (N : ℚ) = ((N - j : ℕ) : ℚ) + (j : ℚ) := by
    rw [hcast]; ring
  field_simp [hjq, hNq]
  rw [hcast]
  ring

lemma inv_sq_sub_cube {N j : ℕ} (hj0 : 0 < j) (hjN : j < N) :
    (1 : ℚ) / ((j : ℚ) ^ 2 * ((N - j : ℕ) : ℚ)) + 1 / (j : ℚ) ^ 3 =
      (N : ℚ) / ((j : ℚ) ^ 3 * ((N - j : ℕ) : ℚ)) := by
  have hjq : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj0.ne'
  have hNq : ((N - j : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.sub_pos_of_lt hjN).ne'
  have hcast : ((N - j : ℕ) : ℚ) = (N : ℚ) - (j : ℚ) := by
    norm_cast
    exact Int.natCast_sub (le_of_lt hjN) ▸ by norm_cast
  field_simp [hjq, hNq]
  rw [hcast]
  ring

lemma inv_sq_sub_cube_fourth {N j : ℕ} (hj0 : 0 < j) (hjN : j < N) :
    (1 : ℚ) / ((j : ℚ) ^ 2 * ((N - j : ℕ) : ℚ)) + 1 / (j : ℚ) ^ 3 +
        (N : ℚ) / (j : ℚ) ^ 4 =
      (N : ℚ) ^ 2 / ((j : ℚ) ^ 4 * ((N - j : ℕ) : ℚ)) := by
  have hjq : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj0.ne'
  have hNq : ((N - j : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.sub_pos_of_lt hjN).ne'
  have hcast : ((N - j : ℕ) : ℚ) = (N : ℚ) - (j : ℚ) := by
    norm_cast
    exact Int.natCast_sub (le_of_lt hjN) ▸ by norm_cast
  field_simp [hjq, hNq]
  rw [hcast]
  ring

lemma inv_sq_sq_sub_fourth {N j : ℕ} (hj0 : 0 < j) (hjN : j < N) :
    (1 : ℚ) / ((j : ℚ) ^ 2 * ((N - j : ℕ) : ℚ) ^ 2) - 1 / (j : ℚ) ^ 4 =
      (N : ℚ) * ((2 : ℚ) * j - N) /
        ((j : ℚ) ^ 4 * ((N - j : ℕ) : ℚ) ^ 2) := by
  have hjq : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hj0.ne'
  have hNq : ((N - j : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.sub_pos_of_lt hjN).ne'
  have hcast : ((N - j : ℕ) : ℚ) = (N : ℚ) - (j : ℚ) := by
    norm_cast
    exact Int.natCast_sub (le_of_lt hjN) ▸ by norm_cast
  field_simp [hjq, hNq]
  rw [hcast]
  ring

/- Two-fold elementary symmetric identity: `2 e_2 = H_1² - H_2`. -/

lemma pair_subset_of_mem {U : Finset ℕ} {i j : ℕ} (hi : i ∈ U) (hj : j ∈ U) :
    ({i, j} : Finset ℕ) ⊆ U := by
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact hi
  · exact hj

lemma image_offDiag_powersetCard_two (U : Finset ℕ) :
    U.offDiag.image (fun p : ℕ × ℕ => ({p.1, p.2} : Finset ℕ)) = U.powersetCard 2 := by
  ext s
  simp only [mem_image, mem_offDiag, mem_powersetCard]
  constructor
  · rintro ⟨⟨i, j⟩, ⟨hi, hj, hij⟩, rfl⟩
    exact ⟨pair_subset_of_mem hi hj, card_pair hij⟩
  · intro ⟨hsub, hcard⟩
    obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp hcard
    refine ⟨(i, j), ⟨hsub (by simp), hsub (by simp), hij⟩, rfl⟩

lemma offDiag_fiber_pair {U : Finset ℕ} {i j : ℕ} (hi : i ∈ U) (hj : j ∈ U) (hij : i ≠ j) :
    U.offDiag.filter (fun p : ℕ × ℕ => ({p.1, p.2} : Finset ℕ) = {i, j}) =
      {(i, j), (j, i)} := by
  ext p
  rcases p with ⟨a, b⟩
  simp only [mem_filter, mem_offDiag, mem_insert, mem_singleton]
  constructor
  · intro ⟨⟨ha, hb, hne⟩, heq⟩
    have ha' : a ∈ ({i, j} : Finset ℕ) := by rw [← heq]; simp
    have hb' : b ∈ ({i, j} : Finset ℕ) := by rw [← heq]; simp
    simp only [mem_insert, mem_singleton] at ha' hb'
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hne
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hne
  · intro h
    rcases h with h | h
    · cases h
      exact ⟨⟨hi, hj, hij⟩, rfl⟩
    · cases h
      exact ⟨⟨hj, hi, hij.symm⟩, by ext x; simp [or_comm]⟩

lemma sum_offDiag_inv (U : Finset ℕ) :
    ∑ p ∈ U.offDiag, (p.1 : ℚ)⁻¹ * (p.2 : ℚ)⁻¹ =
      (2 : ℚ) * ∑ s ∈ U.powersetCard 2, ∏ k ∈ s, (k : ℚ)⁻¹ := by
  classical
  have hmaps : ∀ p ∈ U.offDiag, ({p.1, p.2} : Finset ℕ) ∈ U.powersetCard 2 := by
    intro p hp
    have hp' := mem_offDiag.mp hp
    exact mem_powersetCard.mpr ⟨pair_subset_of_mem hp'.1 hp'.2.1, card_pair hp'.2.2⟩
  have hfib :
      ∑ p ∈ U.offDiag, (p.1 : ℚ)⁻¹ * (p.2 : ℚ)⁻¹ =
        ∑ s ∈ U.powersetCard 2,
          ∑ p ∈ U.offDiag.filter (fun p : ℕ × ℕ => ({p.1, p.2} : Finset ℕ) = s),
            (p.1 : ℚ)⁻¹ * (p.2 : ℚ)⁻¹ :=
    (sum_fiberwise_of_maps_to (s := U.offDiag) (t := U.powersetCard 2)
      (g := fun p : ℕ × ℕ => ({p.1, p.2} : Finset ℕ)) hmaps
      (fun p => (p.1 : ℚ)⁻¹ * (p.2 : ℚ)⁻¹)).symm
  refine hfib.trans ?_
  have hterm : ∀ s ∈ U.powersetCard 2,
      ∑ p ∈ U.offDiag.filter (fun p : ℕ × ℕ => ({p.1, p.2} : Finset ℕ) = s),
        (p.1 : ℚ)⁻¹ * (p.2 : ℚ)⁻¹ =
      (2 : ℚ) * ∏ k ∈ s, (k : ℚ)⁻¹ := by
    intro s hs
    obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp (mem_powersetCard.mp hs).2
    have hsub := (mem_powersetCard.mp hs).1
    have hi : i ∈ U := hsub (by simp)
    have hj : j ∈ U := hsub (by simp)
    rw [offDiag_fiber_pair hi hj hij, sum_pair (by intro h; exact hij (Prod.ext_iff.mp h).1)]
    simp [prod_pair hij]
    ring
  refine (sum_congr rfl hterm).trans ?_
  simp [mul_sum]

lemma sum_diag_inv (U : Finset ℕ) :
    ∑ p ∈ U.diag, (p.1 : ℚ)⁻¹ * (p.2 : ℚ)⁻¹ =
      ∑ j ∈ U, (j : ℚ)⁻¹ ^ 2 := by
  refine sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
  · intro p hp
    exact (mem_diag.mp hp).1
  · intro p1 hp1 p2 hp2 h
    have e1 := (mem_diag.mp hp1).2
    have e2 := (mem_diag.mp hp2).2
    apply Prod.ext
    · exact h
    · exact e1.symm.trans (h.trans e2)
  · intro j hj
    exact ⟨(j, j), mem_diag.mpr ⟨hj, rfl⟩, rfl⟩
  · intro p hp
    have hp' := (mem_diag.mp hp).2
    simp [hp', pow_two]

lemma eSym_two (p r : ℕ) :
    (2 : ℚ) * eSym 2 p r = H 1 p r ^ 2 - H 2 p r := by
  classical
  have hprod : H 1 p r ^ 2 =
      ∑ p ∈ (unitsBelow p r) ×ˢ (unitsBelow p r),
        (p.1 : ℚ)⁻¹ * (p.2 : ℚ)⁻¹ := by
    unfold H
    rw [sq, sum_mul, Finset.sum_product]
    refine sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine sum_congr rfl (fun i _ => ?_)
    simp [pow_one]
  have hunion : (unitsBelow p r) ×ˢ (unitsBelow p r) =
      (unitsBelow p r).diag ∪ (unitsBelow p r).offDiag :=
    (diag_union_offDiag (s := unitsBelow p r)).symm
  have hH2 : ∑ p ∈ (unitsBelow p r).diag, (p.1 : ℚ)⁻¹ * (p.2 : ℚ)⁻¹ = H 2 p r := by
    rw [sum_diag_inv]
    unfold H; rfl
  rw [hprod, hunion, sum_union (disjoint_diag_offDiag (s := unitsBelow p r)),
    hH2, sum_offDiag_inv]
  unfold eSym
  ring

lemma padicValRat_N {p r : ℕ} [hp : Fact p.Prime] :
    padicValRat p ((p ^ r : ℕ) : ℚ) = r := by
  rw [Nat.cast_pow, padicValRat_p_pow]

lemma padicValRat_int_nonneg {p : ℕ} [Fact p.Prime] (z : ℤ) :
    (z : ℚ) = 0 ∨ 0 ≤ padicValRat p (z : ℚ) := by
  by_cases hz : z = 0
  · left; simp [hz]
  · right
    simpa [padicValRat.of_int] using (Nat.cast_nonneg (padicValInt p z) : (0 : ℤ) ≤ _)

/- Pairing for cubes and the upgrade `v(H_3) ≥ 2r-1`. -/

lemma sum_inv_cube_sub_eq_H3 {p r : ℕ} (hp : p.Prime) (hr : 0 < r) :
    ∑ j ∈ unitsBelow p r, ((p ^ r - j : ℕ) : ℚ)⁻¹ ^ 3 = H 3 p r := by
  unfold H
  refine Finset.sum_bij (fun j _ => p ^ r - j) ?_ ?_ ?_ ?_
  · intro j hj; exact sub_mem_unitsBelow hp hr hj
  · intro j1 hj1 j2 hj2 heq
    have h1 := le_of_lt (lt_pow_of_mem_unitsBelow hp hr hj1)
    have h2 := le_of_lt (lt_pow_of_mem_unitsBelow hp hr hj2)
    have := congrArg (fun t => p ^ r - t) heq
    simpa [Nat.sub_sub_self h1, Nat.sub_sub_self h2] using this
  · intro b hb
    refine ⟨p ^ r - b, sub_mem_unitsBelow hp hr hb, ?_⟩
    exact Nat.sub_sub_self (le_of_lt (lt_pow_of_mem_unitsBelow hp hr hb))
  · intro j hj; rfl

lemma H3_pair_identity {p r : ℕ} (hp : p.Prime) (hr : 0 < r) :
    (2 : ℚ) * H 3 p r =
      (p ^ r : ℚ) *
        (-(3 : ℚ) * ∑ j ∈ unitsBelow p r,
            (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2) +
          (p ^ r : ℚ) ^ 2 * ∑ j ∈ unitsBelow p r,
            (1 : ℚ) / ((j : ℚ) ^ 3 * ((p ^ r - j : ℕ) : ℚ) ^ 3)) := by
  have hsum : ∑ j ∈ unitsBelow p r,
      ((j : ℚ)⁻¹ ^ 3 + ((p ^ r - j : ℕ) : ℚ)⁻¹ ^ 3) = (2 : ℚ) * H 3 p r := by
    rw [sum_add_distrib, sum_inv_cube_sub_eq_H3 hp hr]
    unfold H
    ring
  have hterm : ∀ j ∈ unitsBelow p r,
      (j : ℚ)⁻¹ ^ 3 + ((p ^ r - j : ℕ) : ℚ)⁻¹ ^ 3 =
        (p ^ r : ℚ) * (-(3 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2) +
          (p ^ r : ℚ) ^ 2 / ((j : ℚ) ^ 3 * ((p ^ r - j : ℕ) : ℚ) ^ 3)) := by
    intro j hj
    have := inv_cube_pair (pos_of_mem_unitsBelow hj) (lt_pow_of_mem_unitsBelow hp hr hj)
    simpa [inv_pow, one_div, div_eq_mul_inv, mul_add, mul_neg] using this
  have hsum' := sum_congr rfl hterm
  have hLHS : (2 : ℚ) * H 3 p r =
      ∑ j ∈ unitsBelow p r,
        (p ^ r : ℚ) * (-(3 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2) +
          (p ^ r : ℚ) ^ 2 / ((j : ℚ) ^ 3 * ((p ^ r - j : ℕ) : ℚ) ^ 3)) := by
    rw [← hsum, hsum']
  rw [hLHS, ← mul_sum]
  refine congrArg ((p ^ r : ℚ) * ·) ?_
  simp only [mul_add, div_eq_mul_inv]
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  simp [mul_left_comm, mul_assoc, mul_comm]

lemma two_mul_sub_N_ne_zero {p r j : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 0 < r)
    (hj : j ∈ unitsBelow p r) :
    (2 : ℚ) * j - (p ^ r : ℚ) ≠ 0 := by
  intro h
  have hcast : (2 : ℚ) * j = (p ^ r : ℚ) := by linarith
  have hN : ((2 * j : ℕ) : ℚ) = (p ^ r : ℕ) := by
    push_cast at hcast ⊢
    exact hcast
  have hN' : 2 * j = p ^ r := Nat.cast_injective hN
  have hodd : Odd (p ^ r) := (hp.odd_of_ne_two (by omega)).pow
  have heven : Even (p ^ r) := ⟨j, by omega⟩
  exact Nat.not_even_iff_odd.mpr hodd heven

lemma padicValRat_two_mul_sub_N {p r j : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p)
    (hr : 0 < r) (hj : j ∈ unitsBelow p r) :
    (2 : ℚ) * j - (p ^ r : ℚ) = 0 ∨
      0 ≤ padicValRat p ((2 : ℚ) * j - (p ^ r : ℚ)) := by
  have h : (2 : ℚ) * j - (p ^ r : ℚ) = ((2 * j : ℤ) - (p ^ r : ℤ) : ℤ) := by
    push_cast; rfl
  rw [h]
  exact padicValRat_int_nonneg _

lemma padicValRat_inv_sq_sq {p r j : ℕ} [hp : Fact p.Prime] (hr : 0 < r)
    (hj : j ∈ unitsBelow p r) :
    padicValRat p (((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2)⁻¹) = 0 := by
  have hj0 := unitsBelow_cast_ne_zero hj
  have hN0 := sub_cast_ne_zero hp.out hr hj
  have hvj := padicValRat_mem_units hj
  have hvN := padicValRat_sub_mem_units hr hj
  rw [padicValRat.inv, padicValRat.mul (pow_ne_zero 2 hj0) (pow_ne_zero 2 hN0),
    padicValRat.pow hj0, padicValRat.pow hN0, hvj, hvN]
  simp

lemma padicValRat_sum_inv_sq_sq {p r : ℕ} [hp : Fact p.Prime] (hr : 0 < r) :
    (∑ j ∈ unitsBelow p r,
        (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2)) = 0 ∨
      0 ≤ padicValRat p
        (∑ j ∈ unitsBelow p r,
          (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2)) := by
  refine padicValRat_sum_ge (unitsBelow p r)
    (fun j => (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2)) 0 ?_
  intro j hj
  refine Or.inr ?_
  simpa [one_div] using (le_of_eq (padicValRat_inv_sq_sq hr hj).symm)

lemma padicValRat_sum_inv_cube_cube {p r : ℕ} [hp : Fact p.Prime] (hr : 0 < r) :
    (∑ j ∈ unitsBelow p r,
        (1 : ℚ) / ((j : ℚ) ^ 3 * ((p ^ r - j : ℕ) : ℚ) ^ 3)) = 0 ∨
      0 ≤ padicValRat p
        (∑ j ∈ unitsBelow p r,
          (1 : ℚ) / ((j : ℚ) ^ 3 * ((p ^ r - j : ℕ) : ℚ) ^ 3)) := by
  refine padicValRat_sum_ge (unitsBelow p r)
    (fun j => (1 : ℚ) / ((j : ℚ) ^ 3 * ((p ^ r - j : ℕ) : ℚ) ^ 3)) 0 ?_
  intro j hj
  have hj0 := unitsBelow_cast_ne_zero hj
  have hN0 := sub_cast_ne_zero hp.out hr hj
  have hvj := padicValRat_mem_units hj
  have hvN := padicValRat_sub_mem_units hr hj
  refine Or.inr ?_
  have : padicValRat p (((j : ℚ) ^ 3 * ((p ^ r - j : ℕ) : ℚ) ^ 3)⁻¹) = 0 := by
    rw [padicValRat.inv, padicValRat.mul (pow_ne_zero 3 hj0) (pow_ne_zero 3 hN0),
      padicValRat.pow hj0, padicValRat.pow hN0, hvj, hvN]
    simp
  simpa [one_div] using (le_of_eq this.symm)

lemma padicValRat_H4 {p r : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    H 4 p r = 0 ∨ ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (H 4 p r) :=
  padicValRat_H_ge_pred hp3 hr

lemma rem_S_eq {p r j : ℕ} (hj : j ∈ unitsBelow p r) (hp : p.Prime) (hr : 0 < r) :
    (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2) - 1 / (j : ℚ) ^ 4 =
      (p : ℚ) ^ r * ((2 : ℚ) * j - (p : ℚ) ^ r) /
        ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ) ^ 2) := by
  have h := inv_sq_sq_sub_fourth (pos_of_mem_unitsBelow hj)
    (lt_pow_of_mem_unitsBelow hp hr hj)
  have hcast : ((p ^ r : ℕ) : ℚ) = (p : ℚ) ^ r := Nat.cast_pow p r
  rw [hcast] at h
  exact h

lemma padicValRat_rem_S {p r j : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r)
    (hj : j ∈ unitsBelow p r) :
    (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2) - 1 / (j : ℚ) ^ 4 = 0 ∨
      (r : ℤ) ≤ padicValRat p
        ((1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2) - 1 / (j : ℚ) ^ 4) := by
  rw [rem_S_eq hj hp.out hr]
  have hj0 := unitsBelow_cast_ne_zero hj
  have hNj0 := sub_cast_ne_zero hp.out hr hj
  have hnum := two_mul_sub_N_ne_zero hp.out hp3 hr hj
  have hN : (p : ℚ) ^ r ≠ 0 := pow_ne_zero r (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hden : (j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 4 hj0) (pow_ne_zero 2 hNj0)
  have hfrac0 :
      ((2 : ℚ) * j - (p : ℚ) ^ r) / ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ) ^ 2) ≠ 0 :=
    div_ne_zero hnum hden
  refine Or.inr ?_
  have hvN : padicValRat p ((p : ℚ) ^ r) = r := padicValRat_p_pow
  have hvnum := padicValRat_two_mul_sub_N (p := p) (r := r) (j := j) hp3 hr hj
  have hvden : padicValRat p ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ) ^ 2) = 0 := by
    rw [padicValRat.mul (pow_ne_zero 4 hj0) (pow_ne_zero 2 hNj0),
      padicValRat.pow hj0, padicValRat.pow hNj0, padicValRat_mem_units hj,
      padicValRat_sub_mem_units hr hj]
    simp
  have hvfrac :
      padicValRat p (((2 : ℚ) * j - (p : ℚ) ^ r) /
        ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ) ^ 2)) =
      padicValRat p ((2 : ℚ) * j - (p : ℚ) ^ r) := by
    rw [padicValRat.div hnum hden, hvden, sub_zero]
  have hmul :
      (p : ℚ) ^ r * ((2 : ℚ) * j - (p : ℚ) ^ r) /
        ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ) ^ 2) =
      (p : ℚ) ^ r * (((2 : ℚ) * j - (p : ℚ) ^ r) /
        ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ) ^ 2)) := by
    ring
  rw [hmul, padicValRat.mul hN hfrac0, hvN, hvfrac]
  rcases hvnum with h0 | hge
  · exact absurd h0 hnum
  · linarith

/-- `v(∑ 1/(j²(N-j)²)) ≥ r-1`. -/
lemma padicValRat_S_ge {p r : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    (∑ j ∈ unitsBelow p r,
        (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2)) = 0 ∨
      ((r - 1 : ℕ) : ℤ) ≤ padicValRat p
        (∑ j ∈ unitsBelow p r,
          (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2)) := by
  have hid : ∑ j ∈ unitsBelow p r,
      (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2) =
        H 4 p r + ∑ j ∈ unitsBelow p r,
          ((1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2) - 1 / (j : ℚ) ^ 4) := by
    unfold H
    rw [← sum_add_distrib]
    refine sum_congr rfl ?_
    intro j hj
    ring
  have hsumR := padicValRat_sum_ge (unitsBelow p r)
    (fun j => (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2) - 1 / (j : ℚ) ^ 4) r
    (fun j hj => padicValRat_rem_S hp3 hr hj)
  rw [hid]
  refine padicValRat_add_ge (padicValRat_H4 hp3 hr) ?_
  rcases hsumR with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans (by exact_mod_cast Nat.sub_le r 1) h)

lemma padicValRat_mul_three {p : ℕ} [Fact p.Prime] {A : ℚ} {m : ℤ}
    (hA : A = 0 ∨ m ≤ padicValRat p A) :
    (3 : ℚ) * A = 0 ∨ m + padicValRat p (3 : ℚ) ≤ padicValRat p ((3 : ℚ) * A) := by
  rcases hA with hA | hA
  · left; simp [hA]
  · by_cases h0 : (3 : ℚ) * A = 0
    · exact Or.inl h0
    · right
      have h3 : (3 : ℚ) ≠ 0 := by norm_num
      have hA0 : A ≠ 0 := right_ne_zero_of_mul h0
      rw [padicValRat.mul h3 hA0]
      linarith

lemma two_r_sub_one_eq (r : ℕ) (hr : 0 < r) :
    (r : ℤ) + ((r - 1 : ℕ) : ℤ) = (2 * r - 1 : ℤ) := by
  cases r with
  | zero => omega
  | succ r => push_cast; ring

/-- `v(H_3) ≥ 2r-1`. -/
lemma padicValRat_H3_ge {p r : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    H 3 p r = 0 ∨ (2 * r - 1 : ℤ) ≤ padicValRat p (H 3 p r) := by
  have hid := H3_pair_identity hp.out hr
  have hS := padicValRat_S_ge (p := p) (r := r) hp3 hr
  have hT := padicValRat_sum_inv_cube_cube (p := p) (r := r) hr
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  have hN : (p : ℚ) ^ r ≠ 0 := pow_ne_zero r (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hvN : padicValRat p ((p : ℚ) ^ r) = r := padicValRat_p_pow
  have hv2 : padicValRat p (2 : ℚ) = 0 := padicValRat_two hp3
  have h3n : 0 ≤ padicValRat p (3 : ℚ) := padicValRat_nat_nonneg
  -- Work with the explicit sums from `hid`.
  set S := ∑ j ∈ unitsBelow p r,
    (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ) ^ 2) with hSdef
  set T := ∑ j ∈ unitsBelow p r,
    (1 : ℚ) / ((j : ℚ) ^ 3 * ((p ^ r - j : ℕ) : ℚ) ^ 3) with hTdef
  have hform : (2 : ℚ) * H 3 p r =
      (p : ℚ) ^ r * (-(3 : ℚ) * S + ((p : ℚ) ^ r) ^ 2 * T) := by
    have hcast : ((p ^ r : ℕ) : ℚ) = (p : ℚ) ^ r := Nat.cast_pow p r
    rw [hSdef, hTdef]
    convert hid using 2 <;> simp [hcast, div_eq_mul_inv, mul_comm, mul_left_comm]
  have h3S : -(3 : ℚ) * S = 0 ∨
      ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (-(3 : ℚ) * S) := by
    have hpos : (3 : ℚ) * S = 0 ∨
        ((r - 1 : ℕ) : ℤ) ≤ padicValRat p ((3 : ℚ) * S) :=
      padicValRat_mul_nat_ge 3 (by simpa [hSdef] using hS)
    simpa [padicValRat_neg, neg_mul] using hpos
  have hNT : ((p : ℚ) ^ r) ^ 2 * T = 0 ∨
      (2 * r : ℤ) ≤ padicValRat p (((p : ℚ) ^ r) ^ 2 * T) := by
    have hT' : T = 0 ∨ 0 ≤ padicValRat p T := by simpa [hTdef] using hT
    have hpow := padicValRat_pow_ge (p := p) (A := (p : ℚ) ^ r) (m := (r : ℤ)) 2
      (Or.inr (le_of_eq hvN.symm))
    have := padicValRat_mul_ge hpow hT'
    simpa using this
  have hinner : -(3 : ℚ) * S + ((p : ℚ) ^ r) ^ 2 * T = 0 ∨
      ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (-(3 : ℚ) * S + ((p : ℚ) ^ r) ^ 2 * T) := by
    refine padicValRat_add_ge h3S ?_
    rcases hNT with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by
        exact_mod_cast (Nat.sub_le r 1).trans (by omega)) h)
  by_cases hH0 : H 3 p r = 0
  · exact Or.inl hH0
  · right
    have h2H : (2 : ℚ) * H 3 p r ≠ 0 := mul_ne_zero h2 hH0
    have hinter0 : -(3 : ℚ) * S + ((p : ℚ) ^ r) ^ 2 * T ≠ 0 := by
      intro h; apply h2H; rw [hform, h, mul_zero]
    have : (r : ℤ) + ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (H 3 p r) := by
      have hv := padicValRat.mul (p := p) hN hinter0
      have hv2H : padicValRat p ((2 : ℚ) * H 3 p r) = padicValRat p (H 3 p r) := by
        rw [padicValRat.mul h2 hH0, hv2, zero_add]
      have hinter_ge := hinner.resolve_left (fun h => hinter0 h)
      have : padicValRat p ((2 : ℚ) * H 3 p r) =
          r + padicValRat p (-(3 : ℚ) * S + ((p : ℚ) ^ r) ^ 2 * T) := by
        rw [hform, hv, hvN]
      linarith
    have hrw := two_r_sub_one_eq r hr
    linarith

/- Upgrade `θ = H_1 + N H_2 / 2` to valuation `4r-1`. -/

lemma sum_theta_expand {p r : ℕ} (hp : p.Prime) (hr : 0 < r) :
    ∑ j ∈ unitsBelow p r,
        (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ)) =
      - H 3 p r - (p : ℚ) ^ r * H 4 p r +
        ((p : ℚ) ^ r) ^ 2 * ∑ j ∈ unitsBelow p r,
          (1 : ℚ) / ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ)) := by
  have hterm : ∀ j ∈ unitsBelow p r,
      (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ)) =
        - (1 / (j : ℚ) ^ 3) - (p : ℚ) ^ r / (j : ℚ) ^ 4 +
          ((p : ℚ) ^ r) ^ 2 / ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ)) := by
    intro j hj
    have h := inv_sq_sub_cube_fourth (pos_of_mem_unitsBelow hj)
      (lt_pow_of_mem_unitsBelow hp hr hj)
    have hcast : ((p ^ r : ℕ) : ℚ) = (p : ℚ) ^ r := Nat.cast_pow p r
    rw [hcast] at h
    linarith
  rw [sum_congr rfl hterm]
  have hsplit : ∑ j ∈ unitsBelow p r,
      (-(1 / (j : ℚ) ^ 3) - (p : ℚ) ^ r / (j : ℚ) ^ 4 +
        ((p : ℚ) ^ r) ^ 2 / ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ))) =
    ∑ j ∈ unitsBelow p r, (-(1 / (j : ℚ) ^ 3)) +
      ∑ j ∈ unitsBelow p r, (-((p : ℚ) ^ r / (j : ℚ) ^ 4)) +
      ∑ j ∈ unitsBelow p r,
        ((p : ℚ) ^ r) ^ 2 / ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ)) := by
    simp [sum_add_distrib, sub_eq_add_neg]
  rw [hsplit]
  unfold H
  simp [div_eq_mul_inv, mul_sum, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    neg_mul]

lemma padicValRat_sum_inv_fourth_sub {p r : ℕ} [hp : Fact p.Prime] (hr : 0 < r) :
    (∑ j ∈ unitsBelow p r,
        (1 : ℚ) / ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ))) = 0 ∨
      0 ≤ padicValRat p
        (∑ j ∈ unitsBelow p r,
          (1 : ℚ) / ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ))) := by
  refine padicValRat_sum_ge (unitsBelow p r)
    (fun j => (1 : ℚ) / ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ))) 0 ?_
  intro j hj
  have hj0 := unitsBelow_cast_ne_zero hj
  have hN0 := sub_cast_ne_zero hp.out hr hj
  refine Or.inr ?_
  have : padicValRat p (((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ))⁻¹) = 0 := by
    rw [padicValRat.inv, padicValRat.mul (pow_ne_zero 4 hj0) hN0,
      padicValRat.pow hj0, padicValRat_mem_units hj, padicValRat_sub_mem_units hr hj]
    simp
  simpa [one_div] using (le_of_eq this.symm)

lemma padicValRat_sum_theta_core {p r : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    (∑ j ∈ unitsBelow p r,
        (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ))) = 0 ∨
      (2 * r - 1 : ℤ) ≤ padicValRat p
        (∑ j ∈ unitsBelow p r,
          (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ))) := by
  rw [sum_theta_expand hp.out hr]
  have h3 := padicValRat_neg_ge (padicValRat_H3_ge (p := p) (r := r) hp3 hr)
  have h4 : (p : ℚ) ^ r * H 4 p r = 0 ∨
      (2 * r - 1 : ℤ) ≤ padicValRat p ((p : ℚ) ^ r * H 4 p r) := by
    have hN : (p : ℚ) ^ r ≠ 0 := pow_ne_zero r (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    have h4' := padicValRat_H4 (p := p) (r := r) hp3 hr
    have hmul := padicValRat_mul_ge
      (Or.inr (le_of_eq (padicValRat_p_pow (p := p) (k := r)).symm)) h4'
    rcases hmul with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h)
      have : ((r - 1 : ℕ) : ℤ) + r = (2 * r - 1 : ℤ) := by
        have := two_r_sub_one_eq r hr; linarith
      linarith
  have h4neg := padicValRat_neg_ge h4
  have hN2T : ((p : ℚ) ^ r) ^ 2 * ∑ j ∈ unitsBelow p r,
      (1 : ℚ) / ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ)) = 0 ∨
      (2 * r : ℤ) ≤ padicValRat p (((p : ℚ) ^ r) ^ 2 *
        ∑ j ∈ unitsBelow p r, (1 : ℚ) / ((j : ℚ) ^ 4 * ((p ^ r - j : ℕ) : ℚ))) := by
    have hT := padicValRat_sum_inv_fourth_sub (p := p) (r := r) hr
    have hpow := padicValRat_pow_ge (p := p) (A := (p : ℚ) ^ r) (m := (r : ℤ)) 2
      (Or.inr (le_of_eq (padicValRat_p_pow (p := p) (k := r)).symm))
    simpa using padicValRat_mul_ge hpow hT
  have h34 : - H 3 p r - (p : ℚ) ^ r * H 4 p r = 0 ∨
      (2 * r - 1 : ℤ) ≤ padicValRat p (- H 3 p r - (p : ℚ) ^ r * H 4 p r) := by
    simpa [sub_eq_add_neg] using padicValRat_add_ge h3 h4neg
  refine padicValRat_add_ge h34 ?_
  rcases hN2T with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans (by
      have := two_r_sub_one_eq r hr; linarith) h)

lemma padicValRat_theta_ge4 {p r : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    H 1 p r + (p : ℚ) ^ r * H 2 p r / 2 = 0 ∨
      (4 * r - 1 : ℤ) ≤ padicValRat p (H 1 p r + (p : ℚ) ^ r * H 2 p r / 2) := by
  have hid := H_one_add_half_N_H_two hp.out hp3 hr
  have hcast : ((p ^ r : ℕ) : ℚ) = (p : ℚ) ^ r := Nat.cast_pow p r
  have hsum := padicValRat_sum_theta_core (p := p) (r := r) hp3 hr
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  have hN : (p : ℚ) ^ r ≠ 0 := pow_ne_zero r (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hvN2 : padicValRat p (((p : ℚ) ^ r) ^ 2) = (2 * r : ℤ) := by
    rw [padicValRat.pow hN, padicValRat_p_pow]; ring
  have hv2 : padicValRat p (2 : ℚ) = 0 := padicValRat_two hp3
  have hθ : H 1 p r + (p : ℚ) ^ r * H 2 p r / 2 =
      ((p : ℚ) ^ r) ^ 2 / 2 *
        ∑ j ∈ unitsBelow p r, (1 : ℚ) / ((j : ℚ) ^ 2 * ((p ^ r - j : ℕ) : ℚ)) := by
    rw [← hcast] at hid
    simpa [hcast, pow_two] using hid
  rw [hθ]
  have hprod := padicValRat_mul_ge
    (padicValRat_div_ge (Or.inr (le_of_eq hvN2.symm)) h2 hv2) hsum
  rcases hprod with h | h
  · exact Or.inl h
  · refine Or.inr (le_trans ?_ h)
    have : (2 * r : ℤ) + (2 * r - 1 : ℤ) = (4 * r - 1 : ℤ) := by ring
    linarith

/-- `v(H_1) ≥ 2r-1` for all `p ≥ 3`. -/
lemma padicValRat_H1_ge {p r : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    H 1 p r = 0 ∨ (2 * r - 1 : ℤ) ≤ padicValRat p (H 1 p r) := by
  have hid : H 1 p r =
      (H 1 p r + (p : ℚ) ^ r * H 2 p r / 2) +
        (-((p : ℚ) ^ r * H 2 p r / 2)) := by ring
  rw [hid]
  have hθ := padicValRat_theta_ge (p := p) (r := r) hp3 hr
  have h2 := padicValRat_H_ge_pred (p := p) (r := r) (t := 2) hp3 hr
  have hN : (p : ℚ) ^ r ≠ 0 := pow_ne_zero r (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hhalf : (p : ℚ) ^ r * H 2 p r / 2 = 0 ∨
      (2 * r - 1 : ℤ) ≤ padicValRat p ((p : ℚ) ^ r * H 2 p r / 2) := by
    have hmul := padicValRat_mul_ge
      (Or.inr (le_of_eq (padicValRat_p_pow (p := p) (k := r)).symm)) h2
    have hdiv := padicValRat_div_ge hmul two_ne_zero (padicValRat_two hp3)
    rcases hdiv with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h)
      have : (r : ℤ) + ((r - 1 : ℕ) : ℤ) = (2 * r - 1 : ℤ) := two_r_sub_one_eq r hr
      linarith
  refine padicValRat_add_ge ?_ (padicValRat_neg_ge hhalf)
  rcases hθ with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans (by
      have := two_r_sub_one_eq r hr; linarith) h)

/-- `v(e_2) ≥ r-1`. -/
lemma padicValRat_e2 {p r : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    eSym 2 p r = 0 ∨ ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (eSym 2 p r) := by
  have hid := eSym_two p r
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  have hv2 : padicValRat p (2 : ℚ) = 0 := padicValRat_two hp3
  have hH1sq : H 1 p r ^ 2 = 0 ∨
      (2 * (2 * r - 1) : ℤ) ≤ padicValRat p (H 1 p r ^ 2) :=
    padicValRat_pow_ge 2 (padicValRat_H1_ge (p := p) (r := r) hp3 hr)
  have hH2 := padicValRat_H_ge_pred (p := p) (r := r) (t := 2) hp3 hr
  have hdiff : H 1 p r ^ 2 - H 2 p r = 0 ∨
      ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (H 1 p r ^ 2 - H 2 p r) := by
    have hneg := padicValRat_neg_ge hH2
    have hadd : H 1 p r ^ 2 + (- H 2 p r) = 0 ∨
        ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (H 1 p r ^ 2 + (- H 2 p r)) := by
      refine padicValRat_add_ge ?_ hneg
      rcases hH1sq with h | h
      · exact Or.inl h
      · exact Or.inr (le_trans (by
          have := two_r_sub_one_eq r hr; linarith) h)
    simpa [sub_eq_add_neg] using hadd
  have : (2 : ℚ) * eSym 2 p r = H 1 p r ^ 2 - H 2 p r := hid
  have hmul : (2 : ℚ) * eSym 2 p r = 0 ∨
      ((r - 1 : ℕ) : ℤ) ≤ padicValRat p ((2 : ℚ) * eSym 2 p r) := by
    rw [this]; exact hdiff
  by_cases he : eSym 2 p r = 0
  · exact Or.inl he
  · right
    have hne : (2 : ℚ) * eSym 2 p r ≠ 0 := mul_ne_zero h2 he
    have hge := hmul.resolve_left hne
    have : padicValRat p ((2 : ℚ) * eSym 2 p r) = padicValRat p (eSym 2 p r) := by
      rw [padicValRat.mul h2 he, hv2, zero_add]
    linarith

/- Newton identity for `e_3`. -/

lemma H1_mul_H2_sub_H3 (p r : ℕ) :
    H 1 p r * H 2 p r - H 3 p r =
      ∑ a ∈ unitsBelow p r, ∑ b ∈ (unitsBelow p r).erase a,
        (a : ℚ)⁻¹ ^ 2 * (b : ℚ)⁻¹ := by
  classical
  have hsum : ∑ a ∈ unitsBelow p r,
      (a : ℚ)⁻¹ ^ 2 * ∑ b ∈ (unitsBelow p r).erase a, (b : ℚ)⁻¹ =
      ∑ a ∈ unitsBelow p r, (a : ℚ)⁻¹ ^ 2 * (H 1 p r - (a : ℚ)⁻¹) := by
    refine sum_congr rfl (fun a ha => ?_)
    have : ∑ b ∈ (unitsBelow p r).erase a, (b : ℚ)⁻¹ = H 1 p r - (a : ℚ)⁻¹ := by
      unfold H
      rw [← sum_erase_add (s := unitsBelow p r) (a := a)
        (f := fun j => (j : ℚ)⁻¹ ^ 1) ha]
      simp [pow_one]
    rw [this]
  have hdouble : ∑ a ∈ unitsBelow p r, ∑ b ∈ (unitsBelow p r).erase a,
      (a : ℚ)⁻¹ ^ 2 * (b : ℚ)⁻¹ =
      ∑ a ∈ unitsBelow p r,
        (a : ℚ)⁻¹ ^ 2 * ∑ b ∈ (unitsBelow p r).erase a, (b : ℚ)⁻¹ := by
    refine sum_congr rfl (fun a _ => by rw [← mul_sum])
  rw [hdouble, hsum]
  unfold H
  simp only [pow_one, pow_two, mul_sub, sum_sub_distrib]
  rw [← sum_mul]
  ring

lemma e2_inside_sum (p r : ℕ) :
    ∑ s ∈ (unitsBelow p r).powersetCard 2,
        ∑ a ∈ s, (a : ℚ)⁻¹ * ∏ k ∈ s, (k : ℚ)⁻¹ =
      H 1 p r * H 2 p r - H 3 p r := by
  classical
  have hterm : ∑ s ∈ (unitsBelow p r).powersetCard 2,
      ∑ a ∈ s, (a : ℚ)⁻¹ * ∏ k ∈ s, (k : ℚ)⁻¹ =
      ∑ p ∈ (unitsBelow p r).offDiag, (p.1 : ℚ)⁻¹ ^ 2 * (p.2 : ℚ)⁻¹ := by
    have hmaps : ∀ q ∈ (unitsBelow p r).offDiag,
        ({q.1, q.2} : Finset ℕ) ∈ (unitsBelow p r).powersetCard 2 := by
      intro q hq
      have hq' := mem_offDiag.mp hq
      exact mem_powersetCard.mpr ⟨pair_subset_of_mem hq'.1 hq'.2.1, card_pair hq'.2.2⟩
    have hfib :=
      (sum_fiberwise_of_maps_to (s := (unitsBelow p r).offDiag)
        (t := (unitsBelow p r).powersetCard 2)
        (g := fun q : ℕ × ℕ => ({q.1, q.2} : Finset ℕ)) hmaps
        (fun q => (q.1 : ℚ)⁻¹ ^ 2 * (q.2 : ℚ)⁻¹)).symm
    refine Eq.trans ?_ hfib.symm
    refine sum_congr rfl (fun s hs => ?_)
    obtain ⟨i, j, hij, rfl⟩ := card_eq_two.mp (mem_powersetCard.mp hs).2
    have hsub := (mem_powersetCard.mp hs).1
    rw [sum_pair hij, prod_pair hij,
      offDiag_fiber_pair (hsub (by simp)) (hsub (by simp)) hij,
      sum_pair (by intro h; exact hij (Prod.ext_iff.mp h).1)]
    simp [pow_two]
    ring
  have hR : ∑ q ∈ (unitsBelow p r).offDiag, (q.1 : ℚ)⁻¹ ^ 2 * (q.2 : ℚ)⁻¹ =
      ∑ a ∈ unitsBelow p r, ∑ b ∈ (unitsBelow p r).erase a,
        (a : ℚ)⁻¹ ^ 2 * (b : ℚ)⁻¹ := by
    have : (unitsBelow p r).offDiag =
        ((unitsBelow p r) ×ˢ (unitsBelow p r)).filter (fun q => q.1 ≠ q.2) := by
      ext q
      simp [mem_offDiag, mem_filter, mem_product, and_assoc]
    rw [this, sum_filter, Finset.sum_product]
    refine sum_congr rfl (fun a ha => ?_)
    rw [← sum_erase_add (s := unitsBelow p r) (a := a)
      (f := fun b => if a ≠ b then (a : ℚ)⁻¹ ^ 2 * (b : ℚ)⁻¹ else 0) ha]
    simp
    refine sum_congr rfl (fun b hb => ?_)
    have : a ≠ b := (mem_erase.mp hb).1.symm
    simp [this]
  rw [hterm, hR, H1_mul_H2_sub_H3]

lemma e2_outside_sum (p r : ℕ) :
    ∑ s ∈ (unitsBelow p r).powersetCard 2,
        ∑ a ∈ unitsBelow p r \ s, (a : ℚ)⁻¹ * ∏ k ∈ s, (k : ℚ)⁻¹ =
      (3 : ℚ) * eSym 3 p r := by
  classical
  -- each 3-set T contributes ∏T once for each a ∈ T (with s = T.erase a)
  have hmaps : ∀ T ∈ (unitsBelow p r).powersetCard 3, T ⊆ unitsBelow p r :=
    fun T hT => (mem_powersetCard.mp hT).1
  have hterm : ∀ T ∈ (unitsBelow p r).powersetCard 3,
      (3 : ℚ) * ∏ k ∈ T, (k : ℚ)⁻¹ =
        ∑ a ∈ T, (a : ℚ)⁻¹ * ∏ k ∈ T.erase a, (k : ℚ)⁻¹ := by
    intro T hT
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
      card_eq_three.mp (mem_powersetCard.mp hT).2
    have ha : a ∈ ({a, b, c} : Finset ℕ) := by simp
    have hb : b ∈ ({a, b, c} : Finset ℕ) := by simp
    have hc : c ∈ ({a, b, c} : Finset ℕ) := by simp
    have habc : a ≠ b ∧ a ≠ c ∧ b ≠ c := ⟨hab, hac, hbc⟩
    rw [sum_insert (by simp [hab, hac]), sum_insert (by simp [hbc]), sum_singleton]
    have er_a : ({a, b, c} : Finset ℕ).erase a = {b, c} := by
      have : a ∉ ({b, c} : Finset ℕ) := by simp [hab, hac]
      simpa using (erase_insert (s := ({b, c} : Finset ℕ)) this)
    have er_b : ({a, b, c} : Finset ℕ).erase b = {a, c} := by
      have hmem : b ∈ ({a, b, c} : Finset ℕ) := by simp
      ext x
      simp only [mem_erase, mem_insert, mem_singleton]
      constructor
      · intro ⟨hne, hx⟩
        rcases hx with hx | hx | hx
        · exact Or.inl hx
        · exact absurd hx hne
        · exact Or.inr hx
      · intro hx
        rcases hx with rfl | rfl
        · exact ⟨hab, by simp⟩
        · exact ⟨hbc.symm, by simp⟩
    have er_c : ({a, b, c} : Finset ℕ).erase c = {a, b} := by
      ext x
      simp only [mem_erase, mem_insert, mem_singleton]
      constructor
      · intro ⟨hne, hx⟩
        rcases hx with hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr hx
        · exact absurd hx hne
      · intro hx
        rcases hx with rfl | rfl
        · exact ⟨hac, by simp⟩
        · exact ⟨hbc, by simp⟩
    rw [er_a, er_b, er_c, prod_insert (by simp [hab, hac]),
      prod_insert (by simp [hbc]), prod_singleton,
      prod_pair hac, prod_pair hab]
    ring
  unfold eSym
  rw [mul_sum]
  refine Eq.symm ?_
  refine (sum_congr rfl hterm).trans ?_
  -- reindex (T, a∈T) to (s = T.erase a, a ∉ s)
  have hre : ∑ T ∈ (unitsBelow p r).powersetCard 3,
      ∑ a ∈ T, (a : ℚ)⁻¹ * ∏ k ∈ T.erase a, (k : ℚ)⁻¹ =
      ∑ s ∈ (unitsBelow p r).powersetCard 2,
        ∑ a ∈ unitsBelow p r \ s, (a : ℚ)⁻¹ * ∏ k ∈ s, (k : ℚ)⁻¹ := by
    rw [sum_sigma']
    refine Eq.trans ?_
      (sum_sigma' (s := (unitsBelow p r).powersetCard 2)
        (fun s : Finset ℕ => unitsBelow p r \ s)
        (fun (s : Finset ℕ) (a : ℕ) =>
          (a : ℚ)⁻¹ * ∏ k ∈ s, (k : ℚ)⁻¹)).symm
    refine sum_bij (fun p _ =>
        ⟨p.1.erase p.2, p.2⟩) ?_ ?_ ?_ ?_
    · intro p hp
      rcases p with ⟨T, a⟩
      simp only [mem_sigma] at hp ⊢
      have hT := mem_powersetCard.mp hp.1
      have ha := hp.2
      have hcard : (T.erase a).card = 2 := by
        rw [card_erase_of_mem ha, hT.2]
      have hsub : T.erase a ⊆ unitsBelow p r :=
        (erase_subset a T).trans hT.1
      have haU : a ∈ unitsBelow p r := hT.1 ha
      have hanot : a ∉ T.erase a := notMem_erase a T
      exact ⟨mem_powersetCard.mpr ⟨hsub, hcard⟩, mem_sdiff.mpr ⟨haU, hanot⟩⟩
    · intro p1 hp1 p2 hp2 h
      rcases p1 with ⟨T1, a1⟩
      rcases p2 with ⟨T2, a2⟩
      simp only [Sigma.mk.inj_iff] at h
      obtain ⟨hs, ha⟩ := h
      subst ha
      have hT1 := (mem_sigma.mp hp1).2
      have hT2 := (mem_sigma.mp hp2).2
      have : T1 = insert a1 (T1.erase a1) := (insert_erase hT1).symm
      have : T2 = insert a1 (T2.erase a1) := (insert_erase hT2).symm
      -- hs : T1.erase a1 = T2.erase a1 after cast
      apply Sigma.ext
      · -- T1 = T2
        have hs' : T1.erase a1 = T2.erase a1 := by
          simpa using hs
        calc T1 = insert a1 (T1.erase a1) := (insert_erase hT1).symm
          _ = insert a1 (T2.erase a1) := by rw [hs']
          _ = T2 := insert_erase hT2
      · simp
    · intro q hq
      rcases q with ⟨s, a⟩
      simp only [mem_sigma] at hq
      have hs := mem_powersetCard.mp hq.1
      have ha := mem_sdiff.mp hq.2
      refine ⟨⟨insert a s, a⟩, ?_, ?_⟩
      · simp only [mem_sigma]
        have hcard : (insert a s).card = 3 := by
          rw [card_insert_of_notMem ha.2, hs.2]
        have hsub : insert a s ⊆ unitsBelow p r :=
          insert_subset ha.1 hs.1
        exact ⟨mem_powersetCard.mpr ⟨hsub, hcard⟩, mem_insert_self a s⟩
      · have : (insert a s).erase a = s := erase_insert ha.2
        simp [this]
    · intro p hp
      rcases p with ⟨T, a⟩
      simp
  exact hre

lemma eSym_three (p r : ℕ) :
    (3 : ℚ) * eSym 3 p r =
      eSym 2 p r * H 1 p r - H 1 p r * H 2 p r + H 3 p r := by
  classical
  have hprod : eSym 2 p r * H 1 p r =
      ∑ s ∈ (unitsBelow p r).powersetCard 2,
        ∑ a ∈ unitsBelow p r, (a : ℚ)⁻¹ * ∏ k ∈ s, (k : ℚ)⁻¹ := by
    unfold eSym H
    rw [sum_mul]
    refine sum_congr rfl (fun s _ => ?_)
    rw [Finset.mul_sum]
    refine sum_congr rfl (fun a _ => ?_)
    simp [pow_one, mul_comm]
  have hsplit : ∑ s ∈ (unitsBelow p r).powersetCard 2,
      ∑ a ∈ unitsBelow p r, (a : ℚ)⁻¹ * ∏ k ∈ s, (k : ℚ)⁻¹ =
      ∑ s ∈ (unitsBelow p r).powersetCard 2,
          ∑ a ∈ s, (a : ℚ)⁻¹ * ∏ k ∈ s, (k : ℚ)⁻¹ +
        ∑ s ∈ (unitsBelow p r).powersetCard 2,
          ∑ a ∈ unitsBelow p r \ s, (a : ℚ)⁻¹ * ∏ k ∈ s, (k : ℚ)⁻¹ := by
    have hinner : ∀ s ∈ (unitsBelow p r).powersetCard 2,
        ∑ a ∈ unitsBelow p r, (a : ℚ)⁻¹ * ∏ k ∈ s, (k : ℚ)⁻¹ =
          ∑ a ∈ s, (a : ℚ)⁻¹ * ∏ k ∈ s, (k : ℚ)⁻¹ +
            ∑ a ∈ unitsBelow p r \ s, (a : ℚ)⁻¹ * ∏ k ∈ s, (k : ℚ)⁻¹ := by
      intro s hs
      have hsub : s ⊆ unitsBelow p r := (mem_powersetCard.mp hs).1
      rw [← sum_union (disjoint_sdiff (s := s) (t := unitsBelow p r)),
        union_sdiff_of_subset hsub]
    rw [sum_congr rfl hinner, sum_add_distrib]
  rw [hprod, hsplit, e2_inside_sum, e2_outside_sum]
  ring


/- Newton for `e_4` via MvPolynomial. -/

lemma eval_esymm_eq_eSym (p r k : ℕ) :
    MvPolynomial.eval (fun i : {j // j ∈ unitsBelow p r} => (i.val : ℚ)⁻¹)
      (MvPolynomial.esymm _ ℚ k) = eSym k p r := by
  classical
  rw [MvPolynomial.esymm, map_sum]
  unfold eSym
  refine Finset.sum_bij (fun t _ => t.image Subtype.val) ?_ ?_ ?_ ?_
  · intro t ht
    have hcard : (t.image Subtype.val).card = k := by
      rw [Finset.card_image_of_injective t Subtype.val_injective]
      exact (mem_powersetCard.mp ht).2
    have hsub : t.image Subtype.val ⊆ unitsBelow p r := by
      intro x hx
      rcases mem_image.mp hx with ⟨i, _, rfl⟩
      exact i.property
    exact mem_powersetCard.mpr ⟨hsub, hcard⟩
  · intro t1 _ t2 _ h
    exact Finset.image_injective Subtype.val_injective h
  · intro s hs
    have hsub := (mem_powersetCard.mp hs).1
    refine ⟨s.subtype (fun j => j ∈ unitsBelow p r), ?_, ?_⟩
    · have hcard : (s.subtype (fun j => j ∈ unitsBelow p r)).card = k := by
        rw [card_subtype]
        have hf : s.filter (fun j => j ∈ unitsBelow p r) = s :=
          filter_eq_self.mpr (fun x hx => hsub hx)
        rw [hf]
        exact (mem_powersetCard.mp hs).2
      exact mem_powersetCard_univ.mpr hcard
    · ext x
      simp only [mem_image]
      constructor
      · intro hx
        rcases hx with ⟨i, hi, hix⟩
        rw [← hix]
        exact mem_subtype.mp hi
      · intro hx
        refine ⟨⟨x, hsub hx⟩, mem_subtype.mpr hx, rfl⟩
  · intro t _ht
    rw [map_prod]
    simp only [MvPolynomial.eval_X]
    have hinj : Set.InjOn (Subtype.val : {j // j ∈ unitsBelow p r} → ℕ) t :=
      Subtype.val_injective.injOn
    exact (Finset.prod_image (f := fun j : ℕ => (j : ℚ)⁻¹) hinj).symm

lemma eval_psum_eq_H (p r k : ℕ) :
    MvPolynomial.eval (fun i : {j // j ∈ unitsBelow p r} => (i.val : ℚ)⁻¹)
      (MvPolynomial.psum _ ℚ k) = H k p r := by
  rw [MvPolynomial.psum, map_sum]
  unfold H
  refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
  · intro i _; exact i.property
  · intro i _ j _ h; exact Subtype.ext h
  · intro b hb; exact ⟨⟨b, hb⟩, mem_univ _, rfl⟩
  · intro i _
    simp [MvPolynomial.eval_X]

lemma antidiagonal_four_filter :
    (antidiagonal 4).filter (fun a => a.1 < 4) = {(0, 4), (1, 3), (2, 2), (3, 1)} := by
  ext a
  simp only [mem_filter, mem_antidiagonal, mem_insert, mem_singleton]
  constructor
  · intro ⟨hs, hlt⟩
    have : a.1 = 0 ∨ a.1 = 1 ∨ a.1 = 2 ∨ a.1 = 3 := by omega
    rcases this with h | h | h | h
    · left; ext <;> omega
    · right; left; ext <;> omega
    · right; right; left; ext <;> omega
    · right; right; right; ext <;> omega
  · intro h
    rcases h with h | h | h | h
    · constructor <;> (cases h; simp)
    · constructor <;> (cases h; simp)
    · constructor <;> (cases h; simp)
    · constructor <;> (cases h; simp)

lemma sum_newton_four (f : ℕ × ℕ → ℚ) :
    ∑ a ∈ {(0, 4), (1, 3), (2, 2), (3, 1)}, f a =
      f (0, 4) + f (1, 3) + f (2, 2) + f (3, 1) := by
  simp [sum_insert, sum_singleton]
  ring

lemma eSym_four (p r : ℕ) :
    (4 : ℚ) * eSym 4 p r =
      eSym 3 p r * H 1 p r - eSym 2 p r * H 2 p r +
        H 1 p r * H 3 p r - H 4 p r := by
  classical
  let σ := {j // j ∈ unitsBelow p r}
  let ev : MvPolynomial σ ℚ →+* ℚ :=
    MvPolynomial.eval (fun i : σ => (i.val : ℚ)⁻¹)
  have hN := MvPolynomial.mul_esymm_eq_sum σ ℚ 4
  have hev := congrArg ev hN
  have hlhs : ev ((4 : ℕ) * MvPolynomial.esymm σ ℚ 4) = (4 : ℚ) * eSym 4 p r := by
    rw [map_mul, map_natCast, eval_esymm_eq_eSym]
    norm_cast
  have hrhs :
      ev ((-1) ^ (4 + 1) *
        ∑ a ∈ antidiagonal 4 with a.1 < 4,
          (-1) ^ a.1 * MvPolynomial.esymm σ ℚ a.1 * MvPolynomial.psum σ ℚ a.2) =
      - (H 4 p r - H 1 p r * H 3 p r + eSym 2 p r * H 2 p r -
          eSym 3 p r * H 1 p r) := by
    rw [map_mul, map_pow, map_neg, map_one, map_sum]
    have hsum :
        ∑ a ∈ (antidiagonal 4).filter (fun a => a.1 < 4),
          ev ((-1) ^ a.1 * MvPolynomial.esymm σ ℚ a.1 * MvPolynomial.psum σ ℚ a.2) =
        ∑ a ∈ {(0, 4), (1, 3), (2, 2), (3, 1)},
          (-1 : ℚ) ^ a.1 * eSym a.1 p r * H a.2 p r := by
      rw [antidiagonal_four_filter]
      refine sum_congr rfl (fun a _ => ?_)
      rw [map_mul, map_mul, map_pow, map_neg, map_one, eval_esymm_eq_eSym, eval_psum_eq_H]
    rw [hsum, sum_newton_four]
    simp only [eSym_zero, eSym_one, pow_zero, pow_one, one_mul]
    ring
  have : (4 : ℚ) * eSym 4 p r =
      - (H 4 p r - H 1 p r * H 3 p r + eSym 2 p r * H 2 p r -
          eSym 3 p r * H 1 p r) := by
    rw [← hlhs, hev, hrhs]
  linarith

/- Valuations of `e_3` and `e_4`. -/

lemma padicValRat_three_le_one {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) :
    padicValRat p (3 : ℚ) ≤ 1 := by
  by_cases h : p = 3
  · subst p
    have : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by norm_num : 1 < 3)
    linarith
  · have : ¬ p ∣ 3 := by
      intro hd
      have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hd
      have : p = 3 := by
        have hppos : 2 ≤ p := hp.out.two_le
        omega
      exact h this
    have eq0 : padicValRat p (3 : ℚ) = 0 := by
      simpa using padicValRat_of_nat_not_dvd (n := 3) this
    rw [eq0]
    norm_num

lemma padicValRat_e3 {p r : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    eSym 3 p r = 0 ∨
      (2 * r - 1 : ℤ) - padicValRat p (3 : ℚ) ≤ padicValRat p (eSym 3 p r) := by
  have hid := eSym_three p r
  have h2 := padicValRat_e2 (p := p) (r := r) hp3 hr
  have h1 := padicValRat_H1_ge (p := p) (r := r) hp3 hr
  have hH2 := padicValRat_H_ge_pred (p := p) (r := r) (t := 2) hp3 hr
  have hH3 := padicValRat_H3_ge (p := p) (r := r) hp3 hr
  have hrw := two_r_sub_one_eq r hr
  have hrhs : eSym 2 p r * H 1 p r - H 1 p r * H 2 p r + H 3 p r = 0 ∨
      (2 * r - 1 : ℤ) ≤ padicValRat p
        (eSym 2 p r * H 1 p r - H 1 p r * H 2 p r + H 3 p r) := by
    have hA := padicValRat_mul_ge h2 h1
    have hB := padicValRat_neg_ge (padicValRat_mul_ge h1 hH2)
    have hAB : eSym 2 p r * H 1 p r + - (H 1 p r * H 2 p r) = 0 ∨
        (2 * r - 1 : ℤ) ≤ padicValRat p
          (eSym 2 p r * H 1 p r + - (H 1 p r * H 2 p r)) := by
      refine padicValRat_add_ge ?_ ?_
      · rcases hA with h | h
        · exact Or.inl h
        · exact Or.inr (le_trans (by linarith) h)
      · rcases hB with h | h
        · exact Or.inl h
        · exact Or.inr (le_trans (by linarith) h)
    have hAB' : eSym 2 p r * H 1 p r - H 1 p r * H 2 p r = 0 ∨
        (2 * r - 1 : ℤ) ≤ padicValRat p
          (eSym 2 p r * H 1 p r - H 1 p r * H 2 p r) := by
      simpa [sub_eq_add_neg] using hAB
    refine padicValRat_add_ge hAB' hH3
  have h3 : (3 : ℚ) ≠ 0 := by norm_num
  by_cases he : eSym 3 p r = 0
  · exact Or.inl he
  · right
    have hne : (3 : ℚ) * eSym 3 p r ≠ 0 := mul_ne_zero h3 he
    have hrhs' : (3 : ℚ) * eSym 3 p r = 0 ∨
        (2 * r - 1 : ℤ) ≤ padicValRat p ((3 : ℚ) * eSym 3 p r) := by
      rwa [hid]
    have hge := hrhs'.resolve_left hne
    have : padicValRat p ((3 : ℚ) * eSym 3 p r) =
        padicValRat p (3 : ℚ) + padicValRat p (eSym 3 p r) :=
      padicValRat.mul (p := p) h3 he
    linarith

lemma padicValRat_e4 {p r : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    eSym 4 p r = 0 ∨ ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (eSym 4 p r) := by
  have hid := eSym_four p r
  have h3 := padicValRat_e3 (p := p) (r := r) hp3 hr
  have h1 := padicValRat_H1_ge (p := p) (r := r) hp3 hr
  have h2 := padicValRat_e2 (p := p) (r := r) hp3 hr
  have hH2 := padicValRat_H_ge_pred (p := p) (r := r) (t := 2) hp3 hr
  have hH3 := padicValRat_H3_ge (p := p) (r := r) hp3 hr
  have hH4 := padicValRat_H4 (p := p) (r := r) hp3 hr
  have hv3le := padicValRat_three_le_one (p := p) hp3
  have hrw := two_r_sub_one_eq r hr
  have hrhs : eSym 3 p r * H 1 p r - eSym 2 p r * H 2 p r +
      H 1 p r * H 3 p r - H 4 p r = 0 ∨
      ((r - 1 : ℕ) : ℤ) ≤ padicValRat p
        (eSym 3 p r * H 1 p r - eSym 2 p r * H 2 p r +
          H 1 p r * H 3 p r - H 4 p r) := by
    have hA := padicValRat_mul_ge h3 h1
    have hB := padicValRat_neg_ge (padicValRat_mul_ge h2 hH2)
    have hC := padicValRat_mul_ge h1 hH3
    have hD := padicValRat_neg_ge hH4
    have hA' : eSym 3 p r * H 1 p r = 0 ∨
        ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (eSym 3 p r * H 1 p r) := by
      rcases hA with h | h
      · exact Or.inl h
      · exact Or.inr (le_trans (by linarith) h)
    have hB' : -(eSym 2 p r * H 2 p r) = 0 ∨
        ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (-(eSym 2 p r * H 2 p r)) := by
      rcases hB with h | h
      · exact Or.inl h
      · exact Or.inr (le_trans (by linarith) h)
    have hC' : H 1 p r * H 3 p r = 0 ∨
        ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (H 1 p r * H 3 p r) := by
      rcases hC with h | h
      · exact Or.inl h
      · exact Or.inr (le_trans (by linarith) h)
    have hD' : - H 4 p r = 0 ∨
        ((r - 1 : ℕ) : ℤ) ≤ padicValRat p (- H 4 p r) := hD
    simpa [sub_eq_add_neg] using
      padicValRat_add_ge
        (padicValRat_add_ge (padicValRat_add_ge hA' hB') hC') hD'
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  by_cases he : eSym 4 p r = 0
  · exact Or.inl he
  · right
    have hne : (4 : ℚ) * eSym 4 p r ≠ 0 := mul_ne_zero h4 he
    have hrhs' : (4 : ℚ) * eSym 4 p r = 0 ∨
        ((r - 1 : ℕ) : ℤ) ≤ padicValRat p ((4 : ℚ) * eSym 4 p r) := by
      rwa [hid]
    have hge := hrhs'.resolve_left hne
    have hv4 : padicValRat p (4 : ℚ) = 0 := by
      have : ¬ p ∣ 4 := by
        intro hdvd
        have : p ∣ 2 * 2 := by simpa using hdvd
        rcases hp.out.dvd_mul.mp this with h | h
        · exact prime_not_dvd_two hp.out hp3 h
        · exact prime_not_dvd_two hp.out hp3 h
      simpa using padicValRat_of_nat_not_dvd (n := 4) this
    have : padicValRat p ((4 : ℚ) * eSym 4 p r) = padicValRat p (eSym 4 p r) := by
      rw [padicValRat.mul h4 he, hv4, zero_add]
    linarith

/-- For `p = 3`, the pairing identity gives the extra factor of `3`, so `v(H_3) ≥ 2r`. -/
lemma padicValRat_H3_of_three {r : ℕ} [hp : Fact (3 : ℕ).Prime] (hr : 0 < r) :
    H 3 3 r = 0 ∨ (2 * r : ℤ) ≤ padicValRat 3 (H 3 3 r) := by
  have hid := H3_pair_identity (show Nat.Prime 3 from hp.out) hr
  have hS := padicValRat_S_ge (p := 3) (r := r) (by norm_num) hr
  have hT := padicValRat_sum_inv_cube_cube (p := 3) (r := r) hr
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  have hN : (3 : ℚ) ^ r ≠ 0 := pow_ne_zero r (by norm_num)
  have hvN : padicValRat 3 ((3 : ℚ) ^ r) = r := padicValRat_p_pow
  have hv2 : padicValRat 3 (2 : ℚ) = 0 := padicValRat_two (by norm_num)
  have hv3 : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by norm_num : 1 < 3)
  set S := ∑ j ∈ unitsBelow 3 r,
    (1 : ℚ) / ((j : ℚ) ^ 2 * ((3 ^ r - j : ℕ) : ℚ) ^ 2) with hSdef
  set T := ∑ j ∈ unitsBelow 3 r,
    (1 : ℚ) / ((j : ℚ) ^ 3 * ((3 ^ r - j : ℕ) : ℚ) ^ 3) with hTdef
  have hform : (2 : ℚ) * H 3 3 r =
      (3 : ℚ) ^ r * (-(3 : ℚ) * S + ((3 : ℚ) ^ r) ^ 2 * T) := by
    have hcast : ((3 ^ r : ℕ) : ℚ) = (3 : ℚ) ^ r := Nat.cast_pow 3 r
    rw [hSdef, hTdef]
    convert hid using 2 <;> simp [hcast, div_eq_mul_inv, mul_comm, mul_left_comm]
  have h3S : -(3 : ℚ) * S = 0 ∨
      (r : ℤ) ≤ padicValRat 3 (-(3 : ℚ) * S) := by
    have hpos : (3 : ℚ) * S = 0 ∨
        (1 + ((r - 1 : ℕ) : ℤ)) ≤ padicValRat 3 ((3 : ℚ) * S) := by
      have hS' : S = 0 ∨ ((r - 1 : ℕ) : ℤ) ≤ padicValRat 3 S := by
        simpa [hSdef] using hS
      have hmul := padicValRat_mul_ge
        (Or.inr (le_of_eq hv3.symm) : (3 : ℚ) = 0 ∨ (1 : ℤ) ≤ padicValRat 3 (3 : ℚ)) hS'
      simpa using hmul
    have : (1 + ((r - 1 : ℕ) : ℤ)) = (r : ℤ) := by
      cases r with
      | zero => omega
      | succ r => push_cast; ring
    simpa [padicValRat_neg, neg_mul, this] using hpos
  have hNT : ((3 : ℚ) ^ r) ^ 2 * T = 0 ∨
      (2 * r : ℤ) ≤ padicValRat 3 (((3 : ℚ) ^ r) ^ 2 * T) := by
    have hT' : T = 0 ∨ 0 ≤ padicValRat 3 T := by simpa [hTdef] using hT
    have hpow := padicValRat_pow_ge (p := 3) (A := (3 : ℚ) ^ r) (m := (r : ℤ)) 2
      (Or.inr (le_of_eq hvN.symm))
    have := padicValRat_mul_ge hpow hT'
    simpa using this
  have hinner : -(3 : ℚ) * S + ((3 : ℚ) ^ r) ^ 2 * T = 0 ∨
      (r : ℤ) ≤ padicValRat 3 (-(3 : ℚ) * S + ((3 : ℚ) ^ r) ^ 2 * T) := by
    refine padicValRat_add_ge h3S ?_
    rcases hNT with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by linarith) h)
  by_cases hH0 : H 3 3 r = 0
  · exact Or.inl hH0
  · right
    have h2H : (2 : ℚ) * H 3 3 r ≠ 0 := mul_ne_zero h2 hH0
    have hinter0 : -(3 : ℚ) * S + ((3 : ℚ) ^ r) ^ 2 * T ≠ 0 := by
      intro h; apply h2H; rw [hform, h, mul_zero]
    have hinter_ge := hinner.resolve_left (fun h => hinter0 h)
    have hv2H : padicValRat 3 ((2 : ℚ) * H 3 3 r) = padicValRat 3 (H 3 3 r) := by
      rw [padicValRat.mul h2 hH0, hv2, zero_add]
    have : padicValRat 3 ((2 : ℚ) * H 3 3 r) =
        r + padicValRat 3 (-(3 : ℚ) * S + ((3 : ℚ) ^ r) ^ 2 * T) := by
      rw [hform, padicValRat.mul hN hinter0, hvN]
    linarith

/-- Stronger `e_3` bound when `p = 3`: `v(e_3) ≥ 2r - 1`. -/
lemma padicValRat_e3_of_three {r : ℕ} [hp : Fact (3 : ℕ).Prime] (hr : 2 ≤ r) :
    eSym 3 3 r = 0 ∨ (2 * r - 1 : ℤ) ≤ padicValRat 3 (eSym 3 3 r) := by
  have hr0 : 0 < r := by omega
  have hid := eSym_three 3 r
  have h2 := padicValRat_e2 (p := 3) (r := r) (by norm_num) hr0
  have h1 := padicValRat_H1_ge (p := 3) (r := r) (by norm_num) hr0
  have hH2 := padicValRat_H_ge_pred (p := 3) (r := r) (t := 2) (by norm_num) hr0
  have hH3 := padicValRat_H3_of_three (r := r) hr0
  have hrw := two_r_sub_one_eq r hr0
  have hrhs : eSym 2 3 r * H 1 3 r - H 1 3 r * H 2 3 r + H 3 3 r = 0 ∨
      (2 * r : ℤ) ≤ padicValRat 3
        (eSym 2 3 r * H 1 3 r - H 1 3 r * H 2 3 r + H 3 3 r) := by
    have hA := padicValRat_mul_ge h2 h1
    have hB := padicValRat_neg_ge (padicValRat_mul_ge h1 hH2)
    have hAB : eSym 2 3 r * H 1 3 r + - (H 1 3 r * H 2 3 r) = 0 ∨
        (2 * r : ℤ) ≤ padicValRat 3
          (eSym 2 3 r * H 1 3 r + - (H 1 3 r * H 2 3 r)) := by
      refine padicValRat_add_ge ?_ ?_
      · rcases hA with h | h
        · exact Or.inl h
        · exact Or.inr (le_trans (by linarith) h)
      · rcases hB with h | h
        · exact Or.inl h
        · exact Or.inr (le_trans (by linarith) h)
    have hAB' : eSym 2 3 r * H 1 3 r - H 1 3 r * H 2 3 r = 0 ∨
        (2 * r : ℤ) ≤ padicValRat 3
          (eSym 2 3 r * H 1 3 r - H 1 3 r * H 2 3 r) := by
      simpa [sub_eq_add_neg] using hAB
    refine padicValRat_add_ge hAB' hH3
  have h3 : (3 : ℚ) ≠ 0 := by norm_num
  have hv3 : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by norm_num : 1 < 3)
  by_cases he : eSym 3 3 r = 0
  · exact Or.inl he
  · right
    have hne : (3 : ℚ) * eSym 3 3 r ≠ 0 := mul_ne_zero h3 he
    have hrhs' : (3 : ℚ) * eSym 3 3 r = 0 ∨
        (2 * r : ℤ) ≤ padicValRat 3 ((3 : ℚ) * eSym 3 3 r) := by
      rwa [hid]
    have hge := hrhs'.resolve_left hne
    have : padicValRat 3 ((3 : ℚ) * eSym 3 3 r) =
        1 + padicValRat 3 (eSym 3 3 r) := by
      rw [padicValRat.mul h3 he, hv3]
    linarith

/- Truncation of `Pprod` and remainder valuations. -/

lemma Pprod_trunc (α p r : ℕ) (hcard : 2 ≤ (unitsBelow p r).card) :
    Pprod α p r =
      1 + ((α - 1 : ℕ) : ℚ) * (p : ℚ) ^ r * H 1 p r +
        (((α - 1 : ℕ) : ℚ) * (p : ℚ) ^ r) ^ 2 * eSym 2 p r +
        ∑ m ∈ Icc 3 (unitsBelow p r).card,
          (((α - 1 : ℕ) : ℚ) * (p : ℚ) ^ r) ^ m * eSym m p r := by
  have hcast : (p ^ r : ℚ) = (p : ℚ) ^ r := by
    simp [Nat.cast_pow]
  rw [Pprod_eq_sum_eSym, hcast]
  have hdecomp : range ((unitsBelow p r).card + 1) =
      {0, 1, 2} ∪ Icc 3 (unitsBelow p r).card := by
    ext m
    simp only [mem_range, mem_union, mem_insert, mem_singleton, mem_Icc]
    omega
  have hdisj : Disjoint ({0, 1, 2} : Finset ℕ) (Icc 3 (unitsBelow p r).card) := by
    simp [disjoint_left, mem_Icc]
  rw [hdecomp, sum_union hdisj]
  have hsmall : ∑ m ∈ ({0, 1, 2} : Finset ℕ),
      (((α - 1 : ℕ) : ℚ) * (p : ℚ) ^ r) ^ m * eSym m p r =
      1 + ((α - 1 : ℕ) : ℚ) * (p : ℚ) ^ r * H 1 p r +
        (((α - 1 : ℕ) : ℚ) * (p : ℚ) ^ r) ^ 2 * eSym 2 p r := by
    simp [sum_insert, sum_singleton, eSym_zero, eSym_one, pow_zero, pow_one]
    ring
  rw [hsmall]

lemma padicValRat_pow_mul_eSym {p r m β : ℕ} [hp : Fact p.Prime]
    {bnd : ℤ}
    (he : eSym m p r = 0 ∨ bnd ≤ padicValRat p (eSym m p r)) :
    (((β : ℚ) * (p : ℚ) ^ r) ^ m * eSym m p r) = 0 ∨
      ((m * r : ℤ) + bnd) ≤
        padicValRat p (((β : ℚ) * (p : ℚ) ^ r) ^ m * eSym m p r) := by
  have hβ : (β : ℚ) = 0 ∨ 0 ≤ padicValRat p (β : ℚ) :=
    Or.inr padicValRat_nat_nonneg
  have hN : (p : ℚ) ^ r = 0 ∨ (r : ℤ) ≤ padicValRat p ((p : ℚ) ^ r) :=
    Or.inr (le_of_eq (padicValRat_p_pow (p := p) (k := r)).symm)
  have hβN := padicValRat_mul_ge hβ hN
  have hpow := padicValRat_pow_ge m hβN
  have h := padicValRat_mul_ge hpow he
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr (le_trans ?_ h)
    nlinarith

lemma padicValRat_term_m_ge_five {p r m β : ℕ} [hp : Fact p.Prime]
    (hm : 5 ≤ m) :
    (((β : ℚ) * (p : ℚ) ^ r) ^ m * eSym m p r) = 0 ∨
      (5 * r : ℤ) ≤
        padicValRat p (((β : ℚ) * (p : ℚ) ^ r) ^ m * eSym m p r) := by
  have h := padicValRat_pow_mul_eSym (p := p) (r := r) (m := m) (β := β)
    (bnd := 0) (padicValRat_eSym (p := p) (r := r) (m := m))
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr (le_trans ?_ h)
    nlinarith

/-- Remainder after the quadratic truncation, generic bound. -/
lemma padicValRat_Pprod_rem {p r β : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    (∑ m ∈ Icc 3 (unitsBelow p r).card,
        (((β : ℚ) * (p : ℚ) ^ r) ^ m * eSym m p r)) = 0 ∨
      (5 * r - 1 - padicValRat p (3 : ℚ) : ℤ) ≤
        padicValRat p (∑ m ∈ Icc 3 (unitsBelow p r).card,
          (((β : ℚ) * (p : ℚ) ^ r) ^ m * eSym m p r)) := by
  have hv3le := padicValRat_three_le_one (p := p) hp3
  have hv3n : 0 ≤ padicValRat p (3 : ℚ) := padicValRat_nat_nonneg
  have hrw := two_r_sub_one_eq r hr
  refine padicValRat_sum_ge (Icc 3 (unitsBelow p r).card)
    (fun m => (((β : ℚ) * (p : ℚ) ^ r) ^ m * eSym m p r))
    (5 * r - 1 - padicValRat p (3 : ℚ)) ?_
  intro m hm
  have hm3 : 3 ≤ m := (mem_Icc.mp hm).1
  by_cases h5 : 5 ≤ m
  · have h := padicValRat_term_m_ge_five (p := p) (r := r) (m := m) (β := β) h5
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by linarith) h)
  · have hmle : m ≤ 4 := by omega
    interval_cases m
    · -- m = 3
      have he := padicValRat_e3 (p := p) (r := r) hp3 hr
      have h := padicValRat_pow_mul_eSym (p := p) (r := r) (m := 3) (β := β) he
      rcases h with h | h
      · exact Or.inl h
      · refine Or.inr (le_trans ?_ h)
        have heq : ((3 : ℕ) : ℤ) * (r : ℤ) + ((2 * r - 1 : ℤ) - padicValRat p (3 : ℚ)) =
            (5 * r - 1 - padicValRat p (3 : ℚ) : ℤ) := by
          push_cast
          ring
        exact le_of_eq heq.symm
    · -- m = 4
      have he := padicValRat_e4 (p := p) (r := r) hp3 hr
      have h := padicValRat_pow_mul_eSym (p := p) (r := r) (m := 4) (β := β) he
      rcases h with h | h
      · exact Or.inl h
      · refine Or.inr (le_trans ?_ h)
        have heq : ((4 : ℕ) : ℤ) * (r : ℤ) + ((r - 1 : ℕ) : ℤ) = (5 * r - 1 : ℤ) := by
          have := two_r_sub_one_eq r hr
          push_cast
          cases r with
          | zero => omega
          | succ r => push_cast; ring
        have : (5 * r - 1 : ℤ) - padicValRat p (3 : ℚ) ≤ (5 * r - 1 : ℤ) := by
          linarith [hv3n]
        linarith

/-- Stronger remainder when `p = 3`. -/
lemma padicValRat_Pprod_rem_three {r β : ℕ} [hp : Fact (3 : ℕ).Prime] (hr : 2 ≤ r) :
    (∑ m ∈ Icc 3 (unitsBelow 3 r).card,
        (((β : ℚ) * (3 : ℚ) ^ r) ^ m * eSym m 3 r)) = 0 ∨
      (5 * r - 1 : ℤ) ≤
        padicValRat 3 (∑ m ∈ Icc 3 (unitsBelow 3 r).card,
          (((β : ℚ) * (3 : ℚ) ^ r) ^ m * eSym m 3 r)) := by
  have hr0 : 0 < r := by omega
  have hv3 : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by norm_num : 1 < 3)
  refine padicValRat_sum_ge (Icc 3 (unitsBelow 3 r).card)
    (fun m => (((β : ℚ) * (3 : ℚ) ^ r) ^ m * eSym m 3 r)) (5 * r - 1) ?_
  intro m hm
  have hm3 : 3 ≤ m := (mem_Icc.mp hm).1
  by_cases h5 : 5 ≤ m
  · have h := padicValRat_term_m_ge_five (p := 3) (r := r) (m := m) (β := β) h5
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by linarith) h)
  · have hmle : m ≤ 4 := by omega
    interval_cases m
    · have he := padicValRat_e3_of_three (r := r) hr
      have h := padicValRat_pow_mul_eSym (p := 3) (r := r) (m := 3) (β := β) he
      rcases h with h | h
      · exact Or.inl h
      · refine Or.inr (le_trans ?_ h)
        have heq : ((3 : ℕ) : ℤ) * (r : ℤ) + (2 * r - 1 : ℤ) = (5 * r - 1 : ℤ) := by
          push_cast
          ring
        exact le_of_eq heq.symm
    · have he := padicValRat_e4 (p := 3) (r := r) (by norm_num) hr0
      have h := padicValRat_pow_mul_eSym (p := 3) (r := r) (m := 4) (β := β) he
      rcases h with h | h
      · exact Or.inl h
      · refine Or.inr (le_trans ?_ h)
        have heq : ((4 : ℕ) : ℤ) * (r : ℤ) + ((r - 1 : ℕ) : ℤ) = (5 * r - 1 : ℤ) := by
          have := two_r_sub_one_eq r hr0
          cases r with
          | zero => omega
          | succ r => push_cast; ring
        exact le_of_eq heq.symm

/- Expansion `P - 1 = Main + E`. -/

/-- `θ = H_1 + N H_2 / 2`. -/
def theta (p r : ℕ) : ℚ :=
  H 1 p r + (p : ℚ) ^ r * H 2 p r / 2

lemma H1_eq_theta_sub (p r : ℕ) :
    H 1 p r = theta p r - (p : ℚ) ^ r * H 2 p r / 2 := by
  unfold theta
  ring

lemma e2_eq_H1sq_sub_H2 (p r : ℕ) :
    eSym 2 p r = (H 1 p r ^ 2 - H 2 p r) / 2 := by
  have h := eSym_two p r
  linarith

/-- Main term ` - β(β+1)/2 N² H_2`. -/
def Pmain (β p r : ℕ) : ℚ :=
  - ((β : ℚ) * ((β : ℚ) + 1) / 2) * ((p : ℚ) ^ r) ^ 2 * H 2 p r

/-- Error after extracting the main term. -/
def Perr (β p r : ℕ) : ℚ :=
  (β : ℚ) * (p : ℚ) ^ r * theta p r +
    ((β : ℚ) ^ 2 / 2) * ((p : ℚ) ^ r) ^ 2 * H 1 p r ^ 2 +
    ∑ m ∈ Icc 3 (unitsBelow p r).card,
      (((β : ℚ) * (p : ℚ) ^ r) ^ m * eSym m p r)

lemma Pprod_eq_one_add_main_err {α p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hr : 0 < r) (hα : 1 ≤ α) :
    Pprod α p r = 1 + Pmain (α - 1) p r + Perr (α - 1) p r := by
  have hcard : 2 ≤ (unitsBelow p r).card :=
    card_unitsBelow_ge_two hp hp3 hr
  rw [Pprod_trunc α p r hcard]
  set β : ℕ := α - 1
  have hlin : ((β : ℚ) * (p : ℚ) ^ r) * H 1 p r =
      ((β : ℚ) * (p : ℚ) ^ r) * theta p r -
        ((β : ℚ) * (p : ℚ) ^ r) * ((p : ℚ) ^ r * H 2 p r / 2) := by
    rw [H1_eq_theta_sub]
    ring
  have hquad : (((β : ℚ) * (p : ℚ) ^ r) ^ 2) * eSym 2 p r =
      (((β : ℚ) * (p : ℚ) ^ r) ^ 2) * ((H 1 p r ^ 2 - H 2 p r) / 2) := by
    rw [e2_eq_H1sq_sub_H2]
  unfold Pmain Perr
  rw [hlin, hquad]
  ring

lemma padicValRat_theta {p r : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    theta p r = 0 ∨ (4 * r - 1 : ℤ) ≤ padicValRat p (theta p r) := by
  simpa [theta] using padicValRat_theta_ge4 (p := p) (r := r) hp3 hr

lemma padicValRat_Pmain {p r β : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    Pmain β p r = 0 ∨
      (2 * r + ((r - 1 : ℕ) : ℤ)) ≤ padicValRat p (Pmain β p r) := by
  unfold Pmain
  have hN2 : ((p : ℚ) ^ r) ^ 2 = 0 ∨
      (2 * r : ℤ) ≤ padicValRat p (((p : ℚ) ^ r) ^ 2) :=
    padicValRat_pow_ge 2 (Or.inr (le_of_eq (padicValRat_p_pow (p := p) (k := r)).symm))
  have hH2 := padicValRat_H_ge_pred (p := p) (r := r) (t := 2) hp3 hr
  have hcoeff : - ((β : ℚ) * ((β : ℚ) + 1) / 2) = 0 ∨
      0 ≤ padicValRat p (- ((β : ℚ) * ((β : ℚ) + 1) / 2)) := by
    by_cases h0 : - ((β : ℚ) * ((β : ℚ) + 1) / 2) = 0
    · exact Or.inl h0
    · right
      have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
      have hv2 : padicValRat p (2 : ℚ) = 0 := padicValRat_two hp3
      have hβ : (β : ℚ) = 0 ∨ 0 ≤ padicValRat p (β : ℚ) :=
        Or.inr padicValRat_nat_nonneg
      have hβ1 : ((β : ℚ) + 1) = 0 ∨ 0 ≤ padicValRat p ((β : ℚ) + 1) := by
        have : ((β : ℚ) + 1) = ((β + 1 : ℕ) : ℚ) := by push_cast; rfl
        rw [this]
        exact Or.inr padicValRat_nat_nonneg
      have hmul := padicValRat_mul_ge hβ hβ1
      have hdiv := padicValRat_div_ge hmul h2 hv2
      have hpos : (β : ℚ) * ((β : ℚ) + 1) / 2 ≠ 0 := by
        intro h; exact h0 (by simp [h])
      have : 0 ≤ padicValRat p ((β : ℚ) * ((β : ℚ) + 1) / 2) :=
        hdiv.resolve_left hpos
      simpa [padicValRat_neg] using this
  have h := padicValRat_mul_ge (padicValRat_mul_ge hcoeff hN2) hH2
  simpa [mul_assoc] using h

lemma padicValRat_Pmain_five {p r β : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    Pmain β p r = 0 ∨ (3 * r : ℤ) ≤ padicValRat p (Pmain β p r) := by
  unfold Pmain
  have hN2 : ((p : ℚ) ^ r) ^ 2 = 0 ∨
      (2 * r : ℤ) ≤ padicValRat p (((p : ℚ) ^ r) ^ 2) :=
    padicValRat_pow_ge 2 (Or.inr (le_of_eq (padicValRat_p_pow (p := p) (k := r)).symm))
  have hH2 := padicValRat_H2 (p := p) (r := r) hp5 hr
  have hcoeff : - ((β : ℚ) * ((β : ℚ) + 1) / 2) = 0 ∨
      0 ≤ padicValRat p (- ((β : ℚ) * ((β : ℚ) + 1) / 2)) := by
    by_cases h0 : - ((β : ℚ) * ((β : ℚ) + 1) / 2) = 0
    · exact Or.inl h0
    · right
      have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
      have hv2 : padicValRat p (2 : ℚ) = 0 := padicValRat_two (by omega)
      have hβ : (β : ℚ) = 0 ∨ 0 ≤ padicValRat p (β : ℚ) :=
        Or.inr padicValRat_nat_nonneg
      have hβ1 : ((β : ℚ) + 1) = 0 ∨ 0 ≤ padicValRat p ((β : ℚ) + 1) := by
        have : ((β : ℚ) + 1) = ((β + 1 : ℕ) : ℚ) := by push_cast; rfl
        rw [this]
        exact Or.inr padicValRat_nat_nonneg
      have hmul := padicValRat_mul_ge hβ hβ1
      have hdiv := padicValRat_div_ge hmul h2 hv2
      have hpos : (β : ℚ) * ((β : ℚ) + 1) / 2 ≠ 0 := by
        intro h; exact h0 (by simp [h])
      have : 0 ≤ padicValRat p ((β : ℚ) * ((β : ℚ) + 1) / 2) :=
        hdiv.resolve_left hpos
      simpa [padicValRat_neg] using this
  have h := padicValRat_mul_ge (padicValRat_mul_ge hcoeff hN2) hH2
  rcases h with h | h
  · exact Or.inl (by simpa [mul_assoc] using h)
  · refine Or.inr (le_trans ?_ (by simpa [mul_assoc] using h))
    linarith

lemma padicValRat_N_theta {p r β : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    (β : ℚ) * (p : ℚ) ^ r * theta p r = 0 ∨
      (5 * r - 1 : ℤ) ≤ padicValRat p ((β : ℚ) * (p : ℚ) ^ r * theta p r) := by
  have hβ : (β : ℚ) = 0 ∨ 0 ≤ padicValRat p (β : ℚ) :=
    Or.inr padicValRat_nat_nonneg
  have hN : (p : ℚ) ^ r = 0 ∨ (r : ℤ) ≤ padicValRat p ((p : ℚ) ^ r) :=
    Or.inr (le_of_eq (padicValRat_p_pow (p := p) (k := r)).symm)
  have hθ := padicValRat_theta (p := p) (r := r) hp3 hr
  have h := padicValRat_mul_ge (padicValRat_mul_ge hβ hN) hθ
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr (le_trans ?_ h)
    linarith

lemma padicValRat_N2_H1sq {p r β : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 0 < r) :
    ((β : ℚ) ^ 2 / 2) * ((p : ℚ) ^ r) ^ 2 * H 1 p r ^ 2 = 0 ∨
      (6 * r - 2 : ℤ) ≤
        padicValRat p (((β : ℚ) ^ 2 / 2) * ((p : ℚ) ^ r) ^ 2 * H 1 p r ^ 2) := by
  have hβ : (β : ℚ) ^ 2 = 0 ∨ 0 ≤ padicValRat p ((β : ℚ) ^ 2) :=
    padicValRat_pow_ge 2 (Or.inr padicValRat_nat_nonneg)
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  have hv2 : padicValRat p (2 : ℚ) = 0 := padicValRat_two hp3
  have hcoeff := padicValRat_div_ge hβ h2 hv2
  have hN2 : ((p : ℚ) ^ r) ^ 2 = 0 ∨
      (2 * r : ℤ) ≤ padicValRat p (((p : ℚ) ^ r) ^ 2) :=
    padicValRat_pow_ge 2 (Or.inr (le_of_eq (padicValRat_p_pow (p := p) (k := r)).symm))
  have hH1sq := padicValRat_pow_ge 2 (padicValRat_H1_ge (p := p) (r := r) hp3 hr)
  have h := padicValRat_mul_ge (padicValRat_mul_ge hcoeff hN2) hH1sq
  rcases h with h | h
  · exact Or.inl h
  · refine Or.inr (le_trans ?_ h)
    have heq : (0 : ℤ) - 0 + (2 * r : ℤ) + ((2 : ℕ) : ℤ) * (2 * r - 1) =
        (6 * r - 2 : ℤ) := by
      push_cast
      ring
    exact le_of_eq heq.symm

lemma padicValRat_Perr {p r β : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hr : 2 ≤ r) :
    Perr β p r = 0 ∨
      (5 * r - 1 - padicValRat p (3 : ℚ) : ℤ) ≤ padicValRat p (Perr β p r) := by
  have hr0 : 0 < r := by omega
  have hv3le := padicValRat_three_le_one (p := p) hp3
  have hv3n : 0 ≤ padicValRat p (3 : ℚ) := padicValRat_nat_nonneg
  unfold Perr
  have h1 := padicValRat_N_theta (p := p) (r := r) (β := β) hp3 hr0
  have h2 := padicValRat_N2_H1sq (p := p) (r := r) (β := β) hp3 hr0
  have h3 := padicValRat_Pprod_rem (p := p) (r := r) (β := β) hp3 hr0
  have h1' : (β : ℚ) * (p : ℚ) ^ r * theta p r = 0 ∨
      (5 * r - 1 - padicValRat p (3 : ℚ) : ℤ) ≤
        padicValRat p ((β : ℚ) * (p : ℚ) ^ r * theta p r) := by
    rcases h1 with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by linarith) h)
  have h2' : ((β : ℚ) ^ 2 / 2) * ((p : ℚ) ^ r) ^ 2 * H 1 p r ^ 2 = 0 ∨
      (5 * r - 1 - padicValRat p (3 : ℚ) : ℤ) ≤
        padicValRat p (((β : ℚ) ^ 2 / 2) * ((p : ℚ) ^ r) ^ 2 * H 1 p r ^ 2) := by
    rcases h2 with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by linarith) h)
  exact padicValRat_add_ge (padicValRat_add_ge h1' h2') h3

lemma padicValRat_Perr_three {r β : ℕ} [hp : Fact (3 : ℕ).Prime] (hr : 2 ≤ r) :
    Perr β 3 r = 0 ∨ (5 * r - 1 : ℤ) ≤ padicValRat 3 (Perr β 3 r) := by
  have hr0 : 0 < r := by omega
  unfold Perr
  have h1 := padicValRat_N_theta (p := 3) (r := r) (β := β) (by norm_num) hr0
  have h2 := padicValRat_N2_H1sq (p := 3) (r := r) (β := β) (by norm_num) hr0
  have h3 := padicValRat_Pprod_rem_three (r := r) (β := β) hr
  have h1' : (β : ℚ) * (3 : ℚ) ^ r * theta 3 r = 0 ∨
      (5 * r - 1 : ℤ) ≤ padicValRat 3 ((β : ℚ) * (3 : ℚ) ^ r * theta 3 r) := h1
  have h2' : ((β : ℚ) ^ 2 / 2) * ((3 : ℚ) ^ r) ^ 2 * H 1 3 r ^ 2 = 0 ∨
      (5 * r - 1 : ℤ) ≤
        padicValRat 3 (((β : ℚ) ^ 2 / 2) * ((3 : ℚ) ^ r) ^ 2 * H 1 3 r ^ 2) := by
    rcases h2 with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by linarith) h)
  exact padicValRat_add_ge (padicValRat_add_ge h1' h2') h3

lemma padicValRat_Pprod_sub_one {p r α : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p)
    (hr : 2 ≤ r) (hα : 1 ≤ α) :
    Pprod α p r - 1 = 0 ∨
      (2 * r + ((r - 1 : ℕ) : ℤ)) ≤ padicValRat p (Pprod α p r - 1) := by
  have hr0 : 0 < r := by omega
  have hv3n : 0 ≤ padicValRat p (3 : ℚ) := padicValRat_nat_nonneg
  have hv3le := padicValRat_three_le_one (p := p) hp3
  have hexp := Pprod_eq_one_add_main_err hp.out hp3 hr0 hα
  have : Pprod α p r - 1 = Pmain (α - 1) p r + Perr (α - 1) p r := by
    linarith
  rw [this]
  have hM := padicValRat_Pmain (p := p) (r := r) (β := α - 1) hp3 hr0
  have hE := padicValRat_Perr (p := p) (r := r) (β := α - 1) hp3 hr
  have hE' : Perr (α - 1) p r = 0 ∨
      (2 * r + ((r - 1 : ℕ) : ℤ)) ≤ padicValRat p (Perr (α - 1) p r) := by
    rcases hE with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by
        have := two_r_sub_one_eq r hr0
        linarith) h)
  exact padicValRat_add_ge hM hE'


/- Binomial congruences. -/

lemma padicValRat_of_int_modEq {p : ℕ} [Fact p.Prime] {a b : ℤ} {n : ℕ}
    (h : a ≡ b [ZMOD (p : ℤ) ^ n]) :
    a - b = 0 ∨ (n : ℤ) ≤ padicValRat p ((a - b : ℤ) : ℚ) := by
  rw [Int.modEq_iff_dvd, ← dvd_neg, neg_sub] at h
  have := (padicValInt_dvd_iff (p := p) n (a - b)).mp h
  rcases this with h0 | hle
  · exact Or.inl h0
  · right
    have heq : padicValRat p ((a - b : ℤ) : ℚ) = (padicValInt p (a - b) : ℤ) :=
      padicValRat.of_int
    rw [heq]
    exact_mod_cast hle

lemma nat_int_sub_cast (a b : ℕ) :
    (((a : ℤ) - (b : ℤ) : ℤ) : ℚ) = (a : ℚ) - (b : ℚ) := by
  push_cast; rfl

lemma padicValRat_of_nat_modEq {p : ℕ} [Fact p.Prime] {a b n : ℕ}
    (h : (a : ℤ) ≡ b [ZMOD (p : ℤ) ^ n]) :
    (a : ℚ) - (b : ℚ) = 0 ∨ (n : ℤ) ≤ padicValRat p ((a : ℚ) - (b : ℚ)) := by
  have h' := padicValRat_of_int_modEq (p := p) (a := (a : ℤ)) (b := (b : ℤ)) (n := n) h
  rcases h' with h0 | hge
  · left
    have hab : (a : ℤ) = (b : ℤ) := sub_eq_zero.mp h0
    have : (a : ℚ) = (b : ℚ) := by exact_mod_cast hab
    linarith
  · right
    rwa [nat_int_sub_cast] at hge

lemma int_modEq_of_nat_padic {p : ℕ} [Fact p.Prime] {a b n : ℕ}
    (h : (a : ℚ) - (b : ℚ) = 0 ∨ (n : ℤ) ≤ padicValRat p ((a : ℚ) - (b : ℚ))) :
    (a : ℤ) ≡ b [ZMOD (p : ℤ) ^ n] := by
  refine int_modEq_of_padicValRat_ge ?_
  rcases h with h0 | hge
  · left
    have hab : (a : ℚ) = (b : ℚ) := sub_eq_zero.mp h0
    have : (a : ℤ) = (b : ℤ) := by exact_mod_cast hab
    linarith
  · right
    rwa [nat_int_sub_cast]

lemma padicValRat_e2_five {p r : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    eSym 2 p r = 0 ∨ (r : ℤ) ≤ padicValRat p (eSym 2 p r) := by
  have hid := eSym_two p r
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  have hv2 : padicValRat p (2 : ℚ) = 0 := padicValRat_two (by omega)
  have hH1sq := padicValRat_pow_ge 2
    (padicValRat_H1_wolstenholme (p := p) (r := r) hp5 hr)
  have hH2 := padicValRat_H2 (p := p) (r := r) hp5 hr
  have hdiff : H 1 p r ^ 2 - H 2 p r = 0 ∨
      (r : ℤ) ≤ padicValRat p (H 1 p r ^ 2 - H 2 p r) := by
    have hneg := padicValRat_neg_ge hH2
    have hadd : H 1 p r ^ 2 + (- H 2 p r) = 0 ∨
        (r : ℤ) ≤ padicValRat p (H 1 p r ^ 2 + (- H 2 p r)) := by
      refine padicValRat_add_ge ?_ hneg
      rcases hH1sq with h | h
      · exact Or.inl h
      · refine Or.inr (le_trans ?_ h)
        have : ((2 : ℕ) : ℤ) * (2 * (r : ℤ)) = 4 * (r : ℤ) := by push_cast; ring
        linarith
    simpa [sub_eq_add_neg] using hadd
  have hmul : (2 : ℚ) * eSym 2 p r = 0 ∨
      (r : ℤ) ≤ padicValRat p ((2 : ℚ) * eSym 2 p r) := by
    rw [hid]; exact hdiff
  by_cases he : eSym 2 p r = 0
  · exact Or.inl he
  · right
    have hne : (2 : ℚ) * eSym 2 p r ≠ 0 := mul_ne_zero h2 he
    have hge := hmul.resolve_left hne
    have : padicValRat p ((2 : ℚ) * eSym 2 p r) = padicValRat p (eSym 2 p r) := by
      rw [padicValRat.mul h2 he, hv2, zero_add]
    linarith

lemma padicValRat_Pprod_sub_one_five {p r α : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hr : 0 < r) (hα : 1 ≤ α) :
    Pprod α p r - 1 = 0 ∨ (3 : ℤ) ≤ padicValRat p (Pprod α p r - 1) := by
  have hp3 : 3 ≤ p := by omega
  have hcard : 2 ≤ (unitsBelow p r).card := card_unitsBelow_ge_two hp.out hp3 hr
  set β : ℕ := α - 1
  have hlin : ((β : ℚ) * (p : ℚ) ^ r) * H 1 p r = 0 ∨
      (3 : ℤ) ≤ padicValRat p (((β : ℚ) * (p : ℚ) ^ r) * H 1 p r) := by
    have hβ : (β : ℚ) = 0 ∨ 0 ≤ padicValRat p (β : ℚ) :=
      Or.inr padicValRat_nat_nonneg
    have hN : (p : ℚ) ^ r = 0 ∨ (r : ℤ) ≤ padicValRat p ((p : ℚ) ^ r) :=
      Or.inr (le_of_eq (padicValRat_p_pow (p := p) (k := r)).symm)
    have h1 := padicValRat_H1_wolstenholme (p := p) (r := r) hp5 hr
    have h := padicValRat_mul_ge (padicValRat_mul_ge hβ hN) h1
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by linarith) h)
  have hquad : (((β : ℚ) * (p : ℚ) ^ r) ^ 2) * eSym 2 p r = 0 ∨
      (3 : ℤ) ≤ padicValRat p ((((β : ℚ) * (p : ℚ) ^ r) ^ 2) * eSym 2 p r) := by
    have hβ : (β : ℚ) = 0 ∨ 0 ≤ padicValRat p (β : ℚ) :=
      Or.inr padicValRat_nat_nonneg
    have hN : (p : ℚ) ^ r = 0 ∨ (r : ℤ) ≤ padicValRat p ((p : ℚ) ^ r) :=
      Or.inr (le_of_eq (padicValRat_p_pow (p := p) (k := r)).symm)
    have hβN := padicValRat_mul_ge hβ hN
    have hpow := padicValRat_pow_ge 2 hβN
    have he := padicValRat_e2_five (p := p) (r := r) hp5 hr
    have h := padicValRat_mul_ge hpow he
    rcases h with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h)
      have heq : ((2 : ℕ) : ℤ) * (r : ℤ) + (r : ℤ) = 3 * (r : ℤ) := by
        push_cast; ring
      linarith
  have hrem := padicValRat_Pprod_rem (p := p) (r := r) (β := β) hp3 hr
  have hv3 : padicValRat p (3 : ℚ) = 0 := padicValRat_three hp5
  have hrem' : (∑ m ∈ Icc 3 (unitsBelow p r).card,
      (((β : ℚ) * (p : ℚ) ^ r) ^ m * eSym m p r)) = 0 ∨
      (3 : ℤ) ≤ padicValRat p (∑ m ∈ Icc 3 (unitsBelow p r).card,
        (((β : ℚ) * (p : ℚ) ^ r) ^ m * eSym m p r)) := by
    rcases hrem with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h)
      rw [hv3]
      linarith
  have hexp : Pprod α p r - 1 =
      ((β : ℚ) * (p : ℚ) ^ r) * H 1 p r +
        (((β : ℚ) * (p : ℚ) ^ r) ^ 2) * eSym 2 p r +
        ∑ m ∈ Icc 3 (unitsBelow p r).card,
          (((β : ℚ) * (p : ℚ) ^ r) ^ m * eSym m p r) := by
    rw [Pprod_trunc α p r hcard]
    ring
  rw [hexp]
  exact padicValRat_add_ge (padicValRat_add_ge hlin hquad) hrem'

lemma choose_pow_modEq_p3 {p s α : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hα : 1 ≤ α) :
    ((α * p ^ s).choose (p ^ s) : ℤ) ≡ (α : ℤ) [ZMOD (p : ℤ) ^ 3] := by
  induction s with
  | zero =>
    simp [pow_zero]
  | succ s ih =>
    have hr : 0 < s + 1 := by omega
    have hP := padicValRat_Pprod_sub_one_five (p := p) (r := s + 1) (α := α) hp5 hr hα
    have hmul := choose_eq_Pprod (α := α) (p := p) (r := s + 1) hp.out hr hα
    have hC : (((α * p ^ (s + 1)).choose (p ^ (s + 1)) : ℕ) : ℚ) =
        (((α * p ^ s).choose (p ^ s) : ℕ) : ℚ) * Pprod α p (s + 1) := by
      simpa [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hmul
    have hdiff :
        (((α * p ^ (s + 1)).choose (p ^ (s + 1)) : ℕ) : ℚ) - (α : ℚ) = 0 ∨
          (3 : ℤ) ≤ padicValRat p
            ((((α * p ^ (s + 1)).choose (p ^ (s + 1)) : ℕ) : ℚ) - (α : ℚ)) := by
      rw [hC]
      have hid :
          (((α * p ^ s).choose (p ^ s) : ℕ) : ℚ) * Pprod α p (s + 1) - (α : ℚ) =
            (((α * p ^ s).choose (p ^ s) : ℕ) : ℚ) * (Pprod α p (s + 1) - 1) +
              ((((α * p ^ s).choose (p ^ s) : ℕ) : ℚ) - (α : ℚ)) := by
        ring
      rw [hid]
      have hold := padicValRat_of_nat_modEq (p := p) (n := 3) ih
      have hC0 : (((α * p ^ s).choose (p ^ s) : ℕ) : ℚ) = 0 ∨
          0 ≤ padicValRat p (((α * p ^ s).choose (p ^ s) : ℕ) : ℚ) :=
        Or.inr padicValRat_nat_nonneg
      have hmulP := padicValRat_mul_ge hC0 hP
      exact padicValRat_add_ge hmulP hold
    exact int_modEq_of_nat_padic (p := p) (n := 3) hdiff

lemma padicValRat_Pprod_sub_one_ge_two {p r α : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p)
    (hr : 0 < r) (hα : 1 ≤ α) :
    Pprod α p r - 1 = 0 ∨ (2 : ℤ) ≤ padicValRat p (Pprod α p r - 1) := by
  by_cases hr2 : 2 ≤ r
  · have h := padicValRat_Pprod_sub_one (p := p) (r := r) (α := α) hp3 hr2 hα
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by
        have := two_r_sub_one_eq r hr
        linarith) h)
  · have hr1 : r = 1 := by omega
    subst r
    have hcard : 2 ≤ (unitsBelow p 1).card :=
      card_unitsBelow_ge_two hp.out hp3 (by omega)
    set β : ℕ := α - 1
    have hlin : ((β : ℚ) * (p : ℚ) ^ 1) * H 1 p 1 = 0 ∨
        (2 : ℤ) ≤ padicValRat p (((β : ℚ) * (p : ℚ) ^ 1) * H 1 p 1) := by
      have hβ : (β : ℚ) = 0 ∨ 0 ≤ padicValRat p (β : ℚ) :=
        Or.inr padicValRat_nat_nonneg
      have hN : (p : ℚ) ^ 1 = 0 ∨ (1 : ℤ) ≤ padicValRat p ((p : ℚ) ^ 1) :=
        Or.inr (le_of_eq (padicValRat_p_pow (p := p) (k := 1)).symm)
      have h1 := padicValRat_H1_ge (p := p) (r := 1) hp3 (by omega)
      have h := padicValRat_mul_ge (padicValRat_mul_ge hβ hN) h1
      rcases h with h | h
      · exact Or.inl h
      · refine Or.inr (le_trans ?_ h)
        have h1 : ((1 : ℕ) : ℤ) = 1 := rfl
        linarith
    have hquad : (((β : ℚ) * (p : ℚ) ^ 1) ^ 2) * eSym 2 p 1 = 0 ∨
        (2 : ℤ) ≤ padicValRat p ((((β : ℚ) * (p : ℚ) ^ 1) ^ 2) * eSym 2 p 1) := by
      have hβ : (β : ℚ) = 0 ∨ 0 ≤ padicValRat p (β : ℚ) :=
        Or.inr padicValRat_nat_nonneg
      have hN : (p : ℚ) ^ 1 = 0 ∨ (1 : ℤ) ≤ padicValRat p ((p : ℚ) ^ 1) :=
        Or.inr (le_of_eq (padicValRat_p_pow (p := p) (k := 1)).symm)
      have hβN := padicValRat_mul_ge hβ hN
      have hpow := padicValRat_pow_ge 2 hβN
      have he := padicValRat_e2 (p := p) (r := 1) hp3 (by omega)
      have h := padicValRat_mul_ge hpow he
      rcases h with h | h
      · exact Or.inl h
      · refine Or.inr (le_trans ?_ h)
        have : ((2 : ℕ) : ℤ) * (0 + 1) + ((1 - 1 : ℕ) : ℤ) = 2 := by norm_num
        linarith
    have hrem := padicValRat_Pprod_rem (p := p) (r := 1) (β := β) hp3 (by omega)
    have hrem' : (∑ m ∈ Icc 3 (unitsBelow p 1).card,
        (((β : ℚ) * (p : ℚ) ^ 1) ^ m * eSym m p 1)) = 0 ∨
        (2 : ℤ) ≤ padicValRat p (∑ m ∈ Icc 3 (unitsBelow p 1).card,
          (((β : ℚ) * (p : ℚ) ^ 1) ^ m * eSym m p 1)) := by
      rcases hrem with h | h
      · exact Or.inl h
      · refine Or.inr (le_trans ?_ h)
        have hv3le := padicValRat_three_le_one (p := p) hp3
        have : (2 : ℤ) ≤ 5 * (1 : ℤ) - 1 - padicValRat p (3 : ℚ) := by linarith
        exact this
    have hexp : Pprod α p 1 - 1 =
        ((β : ℚ) * (p : ℚ) ^ 1) * H 1 p 1 +
          (((β : ℚ) * (p : ℚ) ^ 1) ^ 2) * eSym 2 p 1 +
          ∑ m ∈ Icc 3 (unitsBelow p 1).card,
            (((β : ℚ) * (p : ℚ) ^ 1) ^ m * eSym m p 1) := by
      rw [Pprod_trunc α p 1 hcard]
      ring
    rw [hexp]
    exact padicValRat_add_ge (padicValRat_add_ge hlin hquad) hrem'

lemma padicValRat_choose_three_ge_one {s : ℕ} [hp : Fact (3 : ℕ).Prime]
    (hmod : ((3 * 3 ^ s).choose (3 ^ s) : ℤ) ≡ 3 [ZMOD 27]) :
    (((3 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) = 0 ∨
      (1 : ℤ) ≤ padicValRat 3 (((3 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) := by
  have hmod' : ((3 * 3 ^ s).choose (3 ^ s) : ℤ) ≡ 3 [ZMOD (3 : ℤ) ^ 3] := by
    simpa using hmod
  have hsub := padicValRat_of_nat_modEq (p := 3) (n := 3)
    (a := (3 * 3 ^ s).choose (3 ^ s)) (b := 3) hmod'
  rcases hsub with h0 | hge
  · have : (((3 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) = (3 : ℚ) :=
      sub_eq_zero.mp h0
    rw [this]
    refine Or.inr ?_
    have : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by norm_num)
    linarith
  · have hC : (((3 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) =
        ((((3 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) - 3) + 3 := by ring
    rw [hC]
    have h3 : (3 : ℚ) = 0 ∨ (1 : ℤ) ≤ padicValRat 3 (3 : ℚ) :=
      Or.inr (le_of_eq (padicValRat.self (by norm_num : 1 < 3)).symm)
    have hge' : (((3 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) - 3 = 0 ∨
        (1 : ℤ) ≤ padicValRat 3
          ((((3 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) - 3) :=
      Or.inr (le_trans (by
        have : ((3 : ℕ) : ℤ) = 3 := rfl
        linarith) hge)
    exact padicValRat_add_ge hge' h3

lemma choose_three_pow_modEq {s : ℕ} [hp : Fact (3 : ℕ).Prime] :
    ((3 * 3 ^ s).choose (3 ^ s) : ℤ) ≡ 3 [ZMOD 27] := by
  induction s with
  | zero =>
    simp [pow_zero]
  | succ s ih =>
    have hr : 0 < s + 1 := by omega
    have hP := padicValRat_Pprod_sub_one_ge_two (p := 3) (r := s + 1) (α := 3)
      (by norm_num) hr (by omega)
    have hmul := choose_eq_Pprod (α := 3) (p := 3) (r := s + 1)
      (show Nat.Prime 3 from hp.out) hr (by omega)
    have hC : (((3 * 3 ^ (s + 1)).choose (3 ^ (s + 1)) : ℕ) : ℚ) =
        (((3 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) * Pprod 3 3 (s + 1) := by
      simpa [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hmul
    have hdiff :
        (((3 * 3 ^ (s + 1)).choose (3 ^ (s + 1)) : ℕ) : ℚ) - 3 = 0 ∨
          (3 : ℤ) ≤ padicValRat 3
            ((((3 * 3 ^ (s + 1)).choose (3 ^ (s + 1)) : ℕ) : ℚ) - 3) := by
      rw [hC]
      have hid :
          (((3 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) * Pprod 3 3 (s + 1) - 3 =
            (((3 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) * (Pprod 3 3 (s + 1) - 1) +
              ((((3 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) - 3) := by
        ring
      rw [hid]
      have hold := padicValRat_of_nat_modEq (p := 3) (n := 3)
        (a := (3 * 3 ^ s).choose (3 ^ s)) (b := 3) (by simpa using ih)
      have hvC := padicValRat_choose_three_ge_one (s := s) ih
      have hmulP := padicValRat_mul_ge hvC hP
      exact padicValRat_add_ge hmulP hold
    exact int_modEq_of_nat_padic (p := 3) (n := 3)
      (a := (3 * 3 ^ (s + 1)).choose (3 ^ (s + 1))) (b := 3) hdiff

lemma choose_two_pow_modEq {s : ℕ} [hp : Fact (3 : ℕ).Prime] :
    ((2 * 3 ^ s).choose (3 ^ s) : ℤ) ≡ 2 [ZMOD 9] := by
  induction s with
  | zero =>
    simp [pow_zero]
  | succ s ih =>
    have hr : 0 < s + 1 := by omega
    have hP := padicValRat_Pprod_sub_one_ge_two (p := 3) (r := s + 1) (α := 2)
      (by norm_num) hr (by omega)
    have hmul := choose_eq_Pprod (α := 2) (p := 3) (r := s + 1)
      (show Nat.Prime 3 from hp.out) hr (by omega)
    have hC : (((2 * 3 ^ (s + 1)).choose (3 ^ (s + 1)) : ℕ) : ℚ) =
        (((2 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) * Pprod 2 3 (s + 1) := by
      simpa [Nat.succ_eq_add_one, Nat.add_sub_cancel] using hmul
    have hdiff :
        (((2 * 3 ^ (s + 1)).choose (3 ^ (s + 1)) : ℕ) : ℚ) - 2 = 0 ∨
          (2 : ℤ) ≤ padicValRat 3
            ((((2 * 3 ^ (s + 1)).choose (3 ^ (s + 1)) : ℕ) : ℚ) - 2) := by
      rw [hC]
      have hid :
          (((2 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) * Pprod 2 3 (s + 1) - 2 =
            (((2 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) * (Pprod 2 3 (s + 1) - 1) +
              ((((2 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) - 2) := by
        ring
      rw [hid]
      have hold := padicValRat_of_nat_modEq (p := 3) (n := 2)
        (a := (2 * 3 ^ s).choose (3 ^ s)) (b := 2) (by simpa using ih)
      have hC0 : (((2 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) = 0 ∨
          0 ≤ padicValRat 3 (((2 * 3 ^ s).choose (3 ^ s) : ℕ) : ℚ) :=
        Or.inr padicValRat_nat_nonneg
      have hmulP := padicValRat_mul_ge hC0 hP
      exact padicValRat_add_ge hmulP hold
    exact int_modEq_of_nat_padic (p := 3) (n := 2)
      (a := (2 * 3 ^ (s + 1)).choose (3 ^ (s + 1))) (b := 2) hdiff

/- Leading coefficient `6 C3² - 27 C2`. -/

lemma padicValRat_lead_five {p r : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hr : 0 < r) :
    let C3 := ((3 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℚ)
    let C2 := ((2 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℚ)
    (6 : ℚ) * C3 ^ 2 - 27 * C2 = 0 ∨
      (3 : ℤ) ≤ padicValRat p ((6 : ℚ) * C3 ^ 2 - 27 * C2) := by
  intro C3 C2
  have hC3 := choose_pow_modEq_p3 (p := p) (s := r - 1) (α := 3) hp5 (by omega)
  have hC2 := choose_pow_modEq_p3 (p := p) (s := r - 1) (α := 2) hp5 (by omega)
  have h3 : (C3 - 3 : ℚ) = 0 ∨ (3 : ℤ) ≤ padicValRat p (C3 - 3) :=
    padicValRat_of_nat_modEq (p := p) (n := 3) hC3
  have h2 : (C2 - 2 : ℚ) = 0 ∨ (3 : ℤ) ≤ padicValRat p (C2 - 2) :=
    padicValRat_of_nat_modEq (p := p) (n := 3) hC2
  have hid : (6 : ℚ) * C3 ^ 2 - 27 * C2 =
      (6 : ℚ) * (C3 - 3) * (C3 + 3) - 27 * (C2 - 2) := by
    ring
  rw [hid]
  have h6 : padicValRat p (6 : ℚ) = 0 := padicValRat_six hp5
  have h27 : padicValRat p (27 : ℚ) = 0 := by
    have : ¬ p ∣ 27 := by
      intro hd
      have : p ∣ 3 * 9 := by simpa using hd
      rcases hp.out.dvd_mul.mp this with h | h
      · exact prime_not_dvd_three hp.out hp5 h
      · have : p ∣ 3 * 3 := by simpa using h
        rcases hp.out.dvd_mul.mp this with h | h
        · exact prime_not_dvd_three hp.out hp5 h
        · exact prime_not_dvd_three hp.out hp5 h
    exact padicValRat_of_nat_not_dvd this
  have hC3p : C3 + 3 = 0 ∨ 0 ≤ padicValRat p (C3 + 3) := by
    have : C3 + 3 = (((3 * p ^ (r - 1)).choose (p ^ (r - 1)) + 3 : ℕ) : ℚ) := by
      push_cast; rfl
    rw [this]
    exact Or.inr padicValRat_nat_nonneg
  have hA : (6 : ℚ) * (C3 - 3) * (C3 + 3) = 0 ∨
      (3 : ℤ) ≤ padicValRat p ((6 : ℚ) * (C3 - 3) * (C3 + 3)) := by
    have h6' : (6 : ℚ) = 0 ∨ 0 ≤ padicValRat p (6 : ℚ) := Or.inr (le_of_eq h6.symm)
    have h := padicValRat_mul_ge (padicValRat_mul_ge h6' h3) hC3p
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by linarith) h)
  have hB : -((27 : ℚ) * (C2 - 2)) = 0 ∨
      (3 : ℤ) ≤ padicValRat p (-((27 : ℚ) * (C2 - 2))) := by
    have h27' : (27 : ℚ) = 0 ∨ 0 ≤ padicValRat p (27 : ℚ) :=
      Or.inr (le_of_eq h27.symm)
    have h := padicValRat_neg_ge (padicValRat_mul_ge h27' h2)
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by linarith) h)
  simpa [sub_eq_add_neg] using padicValRat_add_ge hA hB

lemma padicValRat_lead_three {r : ℕ} [hp : Fact (3 : ℕ).Prime] (hr : 0 < r) :
    let C3 := ((3 * 3 ^ (r - 1)).choose (3 ^ (r - 1)) : ℚ)
    let C2 := ((2 * 3 ^ (r - 1)).choose (3 ^ (r - 1)) : ℚ)
    (6 : ℚ) * C3 ^ 2 - 27 * C2 = 0 ∨
      (5 : ℤ) ≤ padicValRat 3 ((6 : ℚ) * C3 ^ 2 - 27 * C2) := by
  intro C3 C2
  have hC3 := choose_three_pow_modEq (s := r - 1)
  have hC2 := choose_two_pow_modEq (s := r - 1)
  have h3 : (C3 - 3 : ℚ) = 0 ∨ (3 : ℤ) ≤ padicValRat 3 (C3 - 3) :=
    padicValRat_of_nat_modEq (p := 3) (n := 3) (by simpa using hC3)
  have h2 : (C2 - 2 : ℚ) = 0 ∨ (2 : ℤ) ≤ padicValRat 3 (C2 - 2) :=
    padicValRat_of_nat_modEq (p := 3) (n := 2) (by simpa using hC2)
  have hid : (6 : ℚ) * C3 ^ 2 - 27 * C2 =
      (6 : ℚ) * (C3 - 3) * (C3 + 3) - 27 * (C2 - 2) := by
    ring
  rw [hid]
  have hv3 : padicValRat 3 (3 : ℚ) = 1 := padicValRat.self (by norm_num)
  have hv6 : padicValRat 3 (6 : ℚ) = 1 := by
    have h6 : (6 : ℚ) = 2 * 3 := by norm_num
    rw [h6, padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) (by norm_num : (3 : ℚ) ≠ 0),
      padicValRat_two (by norm_num), hv3]
    norm_num
  have hv27 : padicValRat 3 (27 : ℚ) = 3 := by
    have : (27 : ℚ) = (3 : ℚ) ^ 3 := by norm_num
    rw [this, padicValRat.pow (by norm_num : (3 : ℚ) ≠ 0), hv3]
    norm_num
  have hC3p : C3 + 3 = 0 ∨ (1 : ℤ) ≤ padicValRat 3 (C3 + 3) := by
    have : C3 + 3 = (C3 - 3) + 6 := by ring
    rw [this]
    have h6 : (6 : ℚ) = 0 ∨ (1 : ℤ) ≤ padicValRat 3 (6 : ℚ) :=
      Or.inr (le_of_eq hv6.symm)
    have h3' : C3 - 3 = 0 ∨ (1 : ℤ) ≤ padicValRat 3 (C3 - 3) := by
      rcases h3 with h | h
      · exact Or.inl h
      · exact Or.inr (le_trans (by linarith) h)
    exact padicValRat_add_ge h3' h6
  have hA : (6 : ℚ) * (C3 - 3) * (C3 + 3) = 0 ∨
      (5 : ℤ) ≤ padicValRat 3 ((6 : ℚ) * (C3 - 3) * (C3 + 3)) := by
    have h6' : (6 : ℚ) = 0 ∨ (1 : ℤ) ≤ padicValRat 3 (6 : ℚ) :=
      Or.inr (le_of_eq hv6.symm)
    have h := padicValRat_mul_ge (padicValRat_mul_ge h6' h3) hC3p
    rcases h with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h)
      have : ((3 : ℕ) : ℤ) = 3 := rfl
      linarith
  have hB : -((27 : ℚ) * (C2 - 2)) = 0 ∨
      (5 : ℤ) ≤ padicValRat 3 (-((27 : ℚ) * (C2 - 2))) := by
    have h27' : (27 : ℚ) = 0 ∨ (3 : ℤ) ≤ padicValRat 3 (27 : ℚ) :=
      Or.inr (le_of_eq hv27.symm)
    have h := padicValRat_neg_ge (padicValRat_mul_ge h27' h2)
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by linarith) h)
  simpa [sub_eq_add_neg] using padicValRat_add_ge hA hB

/- Algebraic identity for `a(N) - a(M)`. -/

lemma a_diff_expanded {p r : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hr : 0 < r) :
    let C3 := ((3 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℚ)
    let C2 := ((2 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℚ)
    (a (p ^ r) : ℚ) - (a (p ^ (r - 1)) : ℚ) =
      -(((p : ℚ) ^ r) ^ 2 * H 2 p r * ((6 : ℚ) * C3 ^ 2 - 27 * C2)) +
        (2 : ℚ) * C3 ^ 2 * Perr 2 p r - 27 * C2 * Perr 1 p r +
        C3 ^ 2 * (Pprod 3 p r - 1) ^ 2 := by
  intro C3 C2
  have hα3 : 1 ≤ 3 := by omega
  have hα2 : 1 ≤ 2 := by omega
  have hexp3 := Pprod_eq_one_add_main_err (α := 3) hp hp3 hr hα3
  have hexp2 := Pprod_eq_one_add_main_err (α := 2) hp hp3 hr hα2
  have ha := a_diff_eq (p := p) (r := r) hp hr
  have hP3 : Pprod 3 p r - 1 = Pmain 2 p r + Perr 2 p r := by
    have : (3 - 1 : ℕ) = 2 := rfl
    rw [this] at hexp3
    linarith
  have hP2 : Pprod 2 p r - 1 = Pmain 1 p r + Perr 1 p r := by
    have : (2 - 1 : ℕ) = 1 := rfl
    rw [this] at hexp2
    linarith
  have hsq : Pprod 3 p r ^ 2 - 1 =
      2 * (Pprod 3 p r - 1) + (Pprod 3 p r - 1) ^ 2 := by ring
  have hM3 : Pmain 2 p r = - (3 : ℚ) * ((p : ℚ) ^ r) ^ 2 * H 2 p r := by
    unfold Pmain
    ring
  have hM2 : Pmain 1 p r = - ((p : ℚ) ^ r) ^ 2 * H 2 p r := by
    unfold Pmain
    ring
  -- unfold C3, C2 in a_diff_eq
  have ha' : (a (p ^ r) : ℚ) - (a (p ^ (r - 1)) : ℚ) =
      C3 ^ 2 * (Pprod 3 p r ^ 2 - 1) - 27 * C2 * (Pprod 2 p r - 1) := ha
  rw [ha', hsq, hP3, hP2, hM3, hM2]
  ring

lemma padicValRat_choose_cast {p n k : ℕ} [Fact p.Prime] :
    ((n.choose k : ℕ) : ℚ) = 0 ∨ 0 ≤ padicValRat p ((n.choose k : ℕ) : ℚ) :=
  Or.inr padicValRat_nat_nonneg

lemma padicValRat_Pprod_sub_one_five_strong {p r α : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hr : 2 ≤ r) (hα : 1 ≤ α) :
    Pprod α p r - 1 = 0 ∨ (3 * r : ℤ) ≤ padicValRat p (Pprod α p r - 1) := by
  have hr0 : 0 < r := by omega
  have hexp := Pprod_eq_one_add_main_err hp.out (by omega) hr0 hα
  have : Pprod α p r - 1 = Pmain (α - 1) p r + Perr (α - 1) p r := by
    linarith
  rw [this]
  have hM := padicValRat_Pmain_five (p := p) (r := r) (β := α - 1) hp5 hr0
  have hE := padicValRat_Perr (p := p) (r := r) (β := α - 1) (by omega) hr
  have hv3 : padicValRat p (3 : ℚ) = 0 := padicValRat_three hp5
  have hE' : Perr (α - 1) p r = 0 ∨
      (3 * r : ℤ) ≤ padicValRat p (Perr (α - 1) p r) := by
    rcases hE with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h)
      rw [hv3]
      linarith
  exact padicValRat_add_ge hM hE'

lemma padicValRat_a_diff_five {p r : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hr : 2 ≤ r) :
    (a (p ^ r) : ℚ) - (a (p ^ (r - 1)) : ℚ) = 0 ∨
      ((3 * r + 3 : ℕ) : ℤ) ≤
        padicValRat p ((a (p ^ r) : ℚ) - (a (p ^ (r - 1)) : ℚ)) := by
  have hr0 : 0 < r := by omega
  have hp3 : 3 ≤ p := by omega
  have hexp := a_diff_expanded (p := p) (r := r) hp.out hp3 hr0
  set C3 := ((3 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℚ)
  set C2 := ((2 * p ^ (r - 1)).choose (p ^ (r - 1)) : ℚ)
  rw [hexp]
  have hC3 : C3 = 0 ∨ 0 ≤ padicValRat p C3 := padicValRat_choose_cast
  have hC2 : C2 = 0 ∨ 0 ≤ padicValRat p C2 := padicValRat_choose_cast
  have hC3sq := padicValRat_pow_ge 2 hC3
  have hlead := padicValRat_lead_five (p := p) (r := r) hp5 hr0
  have hN2H2 : ((p : ℚ) ^ r) ^ 2 * H 2 p r = 0 ∨
      (3 * r : ℤ) ≤ padicValRat p (((p : ℚ) ^ r) ^ 2 * H 2 p r) := by
    have hN2 : ((p : ℚ) ^ r) ^ 2 = 0 ∨
        (2 * r : ℤ) ≤ padicValRat p (((p : ℚ) ^ r) ^ 2) :=
      padicValRat_pow_ge 2 (Or.inr (le_of_eq (padicValRat_p_pow (p := p) (k := r)).symm))
    have hH2 := padicValRat_H2 (p := p) (r := r) hp5 hr0
    have h := padicValRat_mul_ge hN2 hH2
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans (by linarith) h)
  have hterm1 : -(((p : ℚ) ^ r) ^ 2 * H 2 p r * ((6 : ℚ) * C3 ^ 2 - 27 * C2)) = 0 ∨
      ((3 * r + 3 : ℕ) : ℤ) ≤ padicValRat p
        (-(((p : ℚ) ^ r) ^ 2 * H 2 p r * ((6 : ℚ) * C3 ^ 2 - 27 * C2))) := by
    have h := padicValRat_neg_ge (padicValRat_mul_ge hN2H2 hlead)
    rcases h with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h)
      have : ((3 * r + 3 : ℕ) : ℤ) = 3 * r + 3 := by push_cast; rfl
      linarith
  have hE3 := padicValRat_Perr (p := p) (r := r) (β := 2) hp3 hr
  have hv3 : padicValRat p (3 : ℚ) = 0 := padicValRat_three hp5
  have hterm2 : (2 : ℚ) * C3 ^ 2 * Perr 2 p r = 0 ∨
      ((3 * r + 3 : ℕ) : ℤ) ≤ padicValRat p ((2 : ℚ) * C3 ^ 2 * Perr 2 p r) := by
    have h2 : (2 : ℚ) = 0 ∨ 0 ≤ padicValRat p (2 : ℚ) :=
      Or.inr (le_of_eq (padicValRat_two hp3).symm)
    have hE' : Perr 2 p r = 0 ∨
        (5 * r - 1 : ℤ) ≤ padicValRat p (Perr 2 p r) := by
      rcases hE3 with h | h
      · exact Or.inl h
      · refine Or.inr (le_trans ?_ h)
        rw [hv3]; linarith
    have h := padicValRat_mul_ge (padicValRat_mul_ge h2 hC3sq) hE'
    rcases h with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h)
      have : ((3 * r + 3 : ℕ) : ℤ) = 3 * r + 3 := by push_cast; rfl
      linarith
  have hE2 := padicValRat_Perr (p := p) (r := r) (β := 1) hp3 hr
  have hterm3 : -((27 : ℚ) * C2 * Perr 1 p r) = 0 ∨
      ((3 * r + 3 : ℕ) : ℤ) ≤ padicValRat p (-((27 : ℚ) * C2 * Perr 1 p r)) := by
    have h27 : (27 : ℚ) = 0 ∨ 0 ≤ padicValRat p (27 : ℚ) :=
      Or.inr padicValRat_nat_nonneg
    have hE' : Perr 1 p r = 0 ∨
        (5 * r - 1 : ℤ) ≤ padicValRat p (Perr 1 p r) := by
      rcases hE2 with h | h
      · exact Or.inl h
      · refine Or.inr (le_trans ?_ h)
        rw [hv3]; linarith
    have h := padicValRat_neg_ge (padicValRat_mul_ge (padicValRat_mul_ge h27 hC2) hE')
    rcases h with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h)
      have : ((3 * r + 3 : ℕ) : ℤ) = 3 * r + 3 := by push_cast; rfl
      linarith
  have hP := padicValRat_Pprod_sub_one_five_strong (p := p) (r := r) (α := 3) hp5 hr (by omega)
  have hterm4 : C3 ^ 2 * (Pprod 3 p r - 1) ^ 2 = 0 ∨
      ((3 * r + 3 : ℕ) : ℤ) ≤ padicValRat p (C3 ^ 2 * (Pprod 3 p r - 1) ^ 2) := by
    have hP2 := padicValRat_pow_ge 2 hP
    have h := padicValRat_mul_ge hC3sq hP2
    rcases h with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h)
      have heq : ((2 : ℕ) : ℤ) * (3 * r) = 6 * r := by push_cast; ring
      have : ((3 * r + 3 : ℕ) : ℤ) = 3 * r + 3 := by push_cast; rfl
      linarith
  have h12 := padicValRat_add_ge hterm1 hterm2
  have h123 : -(((p : ℚ) ^ r) ^ 2 * H 2 p r * ((6 : ℚ) * C3 ^ 2 - 27 * C2)) +
      (2 : ℚ) * C3 ^ 2 * Perr 2 p r - 27 * C2 * Perr 1 p r = 0 ∨
      ((3 * r + 3 : ℕ) : ℤ) ≤ padicValRat p
        (-(((p : ℚ) ^ r) ^ 2 * H 2 p r * ((6 : ℚ) * C3 ^ 2 - 27 * C2)) +
          (2 : ℚ) * C3 ^ 2 * Perr 2 p r - 27 * C2 * Perr 1 p r) := by
    simpa [sub_eq_add_neg] using padicValRat_add_ge h12 hterm3
  exact padicValRat_add_ge h123 hterm4

lemma padicValRat_a_diff_three {r : ℕ} [hp : Fact (3 : ℕ).Prime] (hr : 2 ≤ r) :
    (a (3 ^ r) : ℚ) - (a (3 ^ (r - 1)) : ℚ) = 0 ∨
      ((3 * r + 3 : ℕ) : ℤ) ≤
        padicValRat 3 ((a (3 ^ r) : ℚ) - (a (3 ^ (r - 1)) : ℚ)) := by
  have hr0 : 0 < r := by omega
  have hexp := a_diff_expanded (p := 3) (r := r) hp.out (by norm_num) hr0
  set C3 := ((3 * 3 ^ (r - 1)).choose (3 ^ (r - 1)) : ℚ)
  set C2 := ((2 * 3 ^ (r - 1)).choose (3 ^ (r - 1)) : ℚ)
  rw [hexp]
  have hC3 : C3 = 0 ∨ 0 ≤ padicValRat 3 C3 := padicValRat_choose_cast
  have hC2 : C2 = 0 ∨ 0 ≤ padicValRat 3 C2 := padicValRat_choose_cast
  have hC3sq := padicValRat_pow_ge 2 hC3
  have hlead := padicValRat_lead_three (r := r) hr0
  have hN2H2 : ((3 : ℚ) ^ r) ^ 2 * H 2 3 r = 0 ∨
      (2 * r + ((r - 1 : ℕ) : ℤ)) ≤ padicValRat 3 (((3 : ℚ) ^ r) ^ 2 * H 2 3 r) := by
    have hN2 : ((3 : ℚ) ^ r) ^ 2 = 0 ∨
        (2 * r : ℤ) ≤ padicValRat 3 (((3 : ℚ) ^ r) ^ 2) :=
      padicValRat_pow_ge 2 (Or.inr (le_of_eq (padicValRat_p_pow (p := 3) (k := r)).symm))
    have hH2 := padicValRat_H_ge_pred (p := 3) (r := r) (t := 2) (by norm_num) hr0
    exact padicValRat_mul_ge hN2 hH2
  have hterm1 : -(((3 : ℚ) ^ r) ^ 2 * H 2 3 r * ((6 : ℚ) * C3 ^ 2 - 27 * C2)) = 0 ∨
      ((3 * r + 3 : ℕ) : ℤ) ≤ padicValRat 3
        (-(((3 : ℚ) ^ r) ^ 2 * H 2 3 r * ((6 : ℚ) * C3 ^ 2 - 27 * C2))) := by
    have h := padicValRat_neg_ge (padicValRat_mul_ge hN2H2 hlead)
    rcases h with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h)
      have hrw := two_r_sub_one_eq r hr0
      have : ((3 * r + 3 : ℕ) : ℤ) = 3 * r + 3 := by push_cast; rfl
      linarith
  have hE3 := padicValRat_Perr_three (r := r) (β := 2) hr
  have hterm2 : (2 : ℚ) * C3 ^ 2 * Perr 2 3 r = 0 ∨
      ((3 * r + 3 : ℕ) : ℤ) ≤ padicValRat 3 ((2 : ℚ) * C3 ^ 2 * Perr 2 3 r) := by
    have h2 : (2 : ℚ) = 0 ∨ 0 ≤ padicValRat 3 (2 : ℚ) :=
      Or.inr (le_of_eq (padicValRat_two (by norm_num)).symm)
    have h := padicValRat_mul_ge (padicValRat_mul_ge h2 hC3sq) hE3
    rcases h with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h)
      have : ((3 * r + 3 : ℕ) : ℤ) = 3 * r + 3 := by push_cast; rfl
      linarith
  have hE2 := padicValRat_Perr_three (r := r) (β := 1) hr
  have hterm3 : -((27 : ℚ) * C2 * Perr 1 3 r) = 0 ∨
      ((3 * r + 3 : ℕ) : ℤ) ≤ padicValRat 3 (-((27 : ℚ) * C2 * Perr 1 3 r)) := by
    have h27 : (27 : ℚ) = 0 ∨ 0 ≤ padicValRat 3 (27 : ℚ) :=
      Or.inr padicValRat_nat_nonneg
    have h := padicValRat_neg_ge (padicValRat_mul_ge (padicValRat_mul_ge h27 hC2) hE2)
    rcases h with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h)
      have : ((3 * r + 3 : ℕ) : ℤ) = 3 * r + 3 := by push_cast; rfl
      linarith
  have hP := padicValRat_Pprod_sub_one (p := 3) (r := r) (α := 3) (by norm_num) hr (by omega)
  have hterm4 : C3 ^ 2 * (Pprod 3 3 r - 1) ^ 2 = 0 ∨
      ((3 * r + 3 : ℕ) : ℤ) ≤ padicValRat 3 (C3 ^ 2 * (Pprod 3 3 r - 1) ^ 2) := by
    have hP2 := padicValRat_pow_ge 2 hP
    have h := padicValRat_mul_ge hC3sq hP2
    rcases h with h | h
    · exact Or.inl h
    · refine Or.inr (le_trans ?_ h)
      have h2c : ((2 : ℕ) : ℤ) = 2 := rfl
      have hcast : ((3 * r + 3 : ℕ) : ℤ) = 3 * (r : ℤ) + 3 := by push_cast; rfl
      have hrw := two_r_sub_one_eq r hr0
      have : (2 : ℤ) * (2 * (r : ℤ) + ((r - 1 : ℕ) : ℤ)) = 6 * (r : ℤ) - 2 := by
        linarith
      nlinarith
  have h12 := padicValRat_add_ge hterm1 hterm2
  have h123 : -(((3 : ℚ) ^ r) ^ 2 * H 2 3 r * ((6 : ℚ) * C3 ^ 2 - 27 * C2)) +
      (2 : ℚ) * C3 ^ 2 * Perr 2 3 r - 27 * C2 * Perr 1 3 r = 0 ∨
      ((3 * r + 3 : ℕ) : ℤ) ≤ padicValRat 3
        (-(((3 : ℚ) ^ r) ^ 2 * H 2 3 r * ((6 : ℚ) * C3 ^ 2 - 27 * C2)) +
          (2 : ℚ) * C3 ^ 2 * Perr 2 3 r - 27 * C2 * Perr 1 3 r) := by
    simpa [sub_eq_add_neg] using padicValRat_add_ge h12 hterm3
  exact padicValRat_add_ge h123 hterm4

end OEIS357569

/-- Conjecture 1: a(p^r) \equiv a(p^(r-1)) ( mod p^(3*r+3) ) for r >= 2 and all primes p >= 3. -/
theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcast :
      (((a (p ^ r) : ℤ) - (a (p ^ (r - 1)) : ℤ) : ℤ) : ℚ) =
        (a (p ^ r) : ℚ) - (a (p ^ (r - 1)) : ℚ) := by
    push_cast; rfl
  by_cases hp5 : 5 ≤ p
  · have h := OEIS357569.padicValRat_a_diff_five (p := p) (r := r) hp5 hr
    refine OEIS357569.int_modEq_of_padicValRat_ge ?_
    rcases h with h0 | hge
    · left
      have hab : (a (p ^ r) : ℚ) = (a (p ^ (r - 1)) : ℚ) := sub_eq_zero.mp h0
      have : a (p ^ r) = a (p ^ (r - 1)) := by exact_mod_cast hab
      linarith
    · right
      rwa [hcast]
  · have hp3eq : p = 3 := by
      have hlt : p < 5 := lt_of_not_ge hp5
      have : p = 3 ∨ p = 4 := by omega
      rcases this with rfl | rfl
      · rfl
      · exact absurd hp (by decide : ¬ Nat.Prime 4)
    subst p
    haveI : Fact (3 : ℕ).Prime := ⟨hp⟩
    have h := OEIS357569.padicValRat_a_diff_three (r := r) hr
    refine OEIS357569.int_modEq_of_padicValRat_ge (p := 3) (n := 3 * r + 3) ?_
    rcases h with h0 | hge
    · left
      have hab : (a (3 ^ r) : ℚ) = (a (3 ^ (r - 1)) : ℚ) := sub_eq_zero.mp h0
      have : a (3 ^ r) = a (3 ^ (r - 1)) := by exact_mod_cast hab
      linarith
    · right
      rwa [hcast]
