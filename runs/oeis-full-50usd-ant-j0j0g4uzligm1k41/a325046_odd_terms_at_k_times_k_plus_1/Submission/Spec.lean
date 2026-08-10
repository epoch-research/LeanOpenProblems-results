import FormalConjectures.Util.ProblemImports

open Nat
open Finset

/--
A325046: G.f.: $\sum_{n \ge 0} x^n \cdot \frac{(1 + x^n)^n}{(1 - x^{n+1})^{n+1}}$.

The term $a(N)$ is the coefficient of $x^N$ in the generating function.
Expanding the terms, we get a formula for $a(N)$:
$$a(N) = \sum_{n=0}^N \sum_{k=0}^n \mathbf{1}_{n + nk + (n+1)j = N} \binom{n}{k} \binom{n+j}{j}$$
where $j = \frac{N - n(k+1)}{n+1}$.
-/
def a (N : ℕ) : ℕ :=
  -- The outer sum runs over $n$ from $0$ to $N$.
  (range (N + 1)).sum (fun n =>
    -- The inner sum runs over $k$ from $0$ to $n$.
    (range (n + 1)).sum (fun k =>
      let R : ℕ := N - n * (k + 1)
      let m : ℕ := n + 1
      -- We require $R = N - n(k+1) \ge 0$ and $m = n+1$ must divide $R$.
      if n * (k + 1) ≤ N ∧ R % m = 0 then
        -- $j = R / m$.
        let j : ℕ := R / m
        -- The summand is $\binom{n}{k} \binom{n+j}{j}$.
        n.choose k * (n + j).choose j
      else
        0
    )
  )

theorem forall_testBit_split (a b : ℕ) :
    (∀ i, b.testBit i = true → a.testBit i = true) ↔
    ((b.testBit 0 = true → a.testBit 0 = true) ∧
     (∀ i, (b/2).testBit i = true → (a/2).testBit i = true)) := by
  constructor
  · intro h
    refine ⟨h 0, fun i hi => ?_⟩
    have := h (i+1)
    rw [Nat.testBit_succ, Nat.testBit_succ] at this
    exact this hi
  · rintro ⟨h0, hs⟩ i hi
    cases i with
    | zero => exact h0 hi
    | succ j => rw [Nat.testBit_succ] at hi ⊢; exact hs j hi

theorem odd_choose_bit0 (a b : ℕ) :
    Odd ((a%2).choose (b%2)) ↔ (b.testBit 0 = true → a.testBit 0 = true) := by
  rw [Nat.testBit_zero, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> rw [ha, hb] <;> decide

theorem odd_choose_iff (a b : ℕ) :
    Odd (a.choose b) ↔ ∀ i, b.testBit i = true → a.testBit i = true := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have key : (∀ i, b.testBit i = true → (0:ℕ).testBit i = true) ↔ b = 0 := by
      constructor
      · intro h; apply Nat.zero_of_testBit_eq_false; intro i
        have := h i; simp only [Nat.zero_testBit, Bool.false_eq_true, imp_false] at this
        simpa using this
      · rintro rfl i; simp
    rw [key]
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; simp
    · rw [Nat.choose_eq_zero_of_lt hb, Nat.odd_iff]; omega
  · have hrec : a.choose b % 2 = ((a%2).choose (b%2) * (a/2).choose (b/2)) % 2 :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat (p:=2)
    rw [Nat.odd_iff, hrec, ← Nat.odd_iff, Nat.odd_mul,
        ih (a/2) (Nat.div_lt_self ha (by norm_num)) (b/2),
        odd_choose_bit0, ← forall_testBit_split]

theorem land_eq_zero_iff (a b : ℕ) :
    a &&& b = 0 ↔ ∀ i, (a.testBit i && b.testBit i) = false := by
  constructor
  · intro h i; rw [← Nat.testBit_land, h, Nat.zero_testBit]
  · intro h; apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_land, Nat.zero_testBit]; exact h i

theorem noCommon_split (a b : ℕ) :
    (∀ i, (a.testBit i && b.testBit i) = false) ↔
    ((a.testBit 0 && b.testBit 0) = false ∧
     ∀ i, ((a/2).testBit i && (b/2).testBit i) = false) := by
  constructor
  · intro h; exact ⟨h 0, fun i => by have := h (i+1); rwa [Nat.testBit_succ, Nat.testBit_succ] at this⟩
  · rintro ⟨h0, hs⟩ i; cases i with
    | zero => exact h0
    | succ j => rw [Nat.testBit_succ, Nat.testBit_succ]; exact hs j

theorem add_choose_odd_iff (n j : ℕ) :
    Odd ((n+j).choose j) ↔ n &&& j = 0 := by
  rw [land_eq_zero_iff]
  have H : ∀ s (n j : ℕ), n + j ≤ s → (Odd ((n+j).choose j) ↔ ∀ i, (n.testBit i && j.testBit i) = false) := by
    intro s
    induction s with
    | zero => intro n j h
              obtain ⟨rfl, rfl⟩ : n = 0 ∧ j = 0 := by omega
              simp
    | succ s ih =>
      intro n j h
      have hrec : (n+j).choose j % 2 = (((n+j)%2).choose (j%2) * ((n+j)/2).choose (j/2)) % 2 :=
        Choose.choose_modEq_choose_mod_mul_choose_div_nat (p:=2)
      rw [Nat.odd_iff, hrec, ← Nat.odd_iff, Nat.odd_mul, noCommon_split,
          Nat.testBit_zero, Nat.testBit_zero]
      have hrec2 := ih (n/2) (j/2) (by omega)
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
        rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · have e1 : (n+j) % 2 = 0 := by omega
        have e2 : (n+j) / 2 = n/2 + j/2 := by omega
        rw [e1, e2, hrec2]; simp [hn, hj]
      · have e1 : (n+j) % 2 = 1 := by omega
        have e2 : (n+j) / 2 = n/2 + j/2 := by omega
        rw [e1, e2, hrec2]; simp [hn, hj]
      · have e1 : (n+j) % 2 = 1 := by omega
        have e2 : (n+j) / 2 = n/2 + j/2 := by omega
        rw [e1, e2, hrec2]; simp [hn, hj]
      · have e1 : (n+j) % 2 = 0 := by omega
        rw [e1]; simp [hn, hj]
  exact H (n+j) n j le_rfl

theorem disjoint_add_eq_lor (a b : ℕ) (hd : a &&& b = 0) : a + b = a ||| b := by
  have H : ∀ s (a b : ℕ), a+b ≤ s → a &&& b = 0 → a + b = a ||| b := by
    intro s
    induction s with
    | zero =>
      intro a b hle _
      have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha; subst hb; rfl
    | succ s ih =>
      intro a b hle hd
      have hd2 := hd
      rw [land_eq_zero_iff, noCommon_split] at hd2
      obtain ⟨h0, hrest⟩ := hd2
      have h0' : a % 2 = 0 ∨ b % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one a with ha|ha
        · exact Or.inl ha
        · refine Or.inr ?_
          rcases Nat.mod_two_eq_zero_or_one b with hb|hb
          · exact hb
          · rw [Nat.testBit_zero, Nat.testBit_zero, ha, hb] at h0; simp at h0
      have hcarry : (a + b)/2 = a/2 + b/2 := by omega
      have ihab : a/2 + b/2 = a/2 ||| b/2 :=
        ih (a/2) (b/2) (by omega) (by rw [land_eq_zero_iff]; exact hrest)
      have hdiv : (a ||| b)/2 = a/2 ||| b/2 := by
        apply Nat.eq_of_testBit_eq; intro i
        rw [← Nat.testBit_succ, Nat.testBit_lor, Nat.testBit_lor,
            Nat.testBit_succ, Nat.testBit_succ]
      have hbit : ((a ||| b) % 2 = 1) ↔ (a % 2 = 1 ∨ b % 2 = 1) := by
        rw [← decide_eq_decide, Bool.decide_or]
        have h := Nat.testBit_lor a b 0
        rwa [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at h
      have hmod : (a ||| b) % 2 = (a + b) % 2 := by omega
      have key : a ||| b = 2*(a/2+b/2) + (a+b)%2 := by
        conv_lhs => rw [← Nat.div_add_mod (a ||| b) 2]
        rw [hdiv, ihab, hmod]
      rw [key]; omega
  exact H (a+b) a b le_rfl hd

/-- The pairwise-disjointness propagation that powers the involution. -/
theorem derive (k p j : ℕ) (hpk : p &&& k = 0) (hj : (k+p) &&& j = 0) :
    j &&& k = 0 ∧ (j+k) &&& p = 0 := by
  have hkp : k + p = k ||| p := disjoint_add_eq_lor k p (by rw [Nat.land_comm]; exact hpk)
  rw [hkp, land_eq_zero_iff] at hj
  have kj0 : k &&& j = 0 := by
    rw [land_eq_zero_iff]; intro i; have := hj i
    rw [Nat.testBit_lor] at this
    revert this; cases k.testBit i <;> cases p.testBit i <;> cases j.testBit i <;> decide
  have pj0 : p &&& j = 0 := by
    rw [land_eq_zero_iff]; intro i; have := hj i
    rw [Nat.testBit_lor] at this
    revert this; cases k.testBit i <;> cases p.testBit i <;> cases j.testBit i <;> decide
  refine ⟨by rw [Nat.land_comm]; exact kj0, ?_⟩
  have hjk : j + k = j ||| k := disjoint_add_eq_lor j k (by rw [Nat.land_comm] at kj0; exact kj0)
  rw [hjk, land_eq_zero_iff]; intro i
  rw [Nat.testBit_lor]
  have h1 := (land_eq_zero_iff p j).1 pj0 i
  have h2 := (land_eq_zero_iff p k).1 hpk i
  revert h1 h2; cases j.testBit i <;> cases k.testBit i <;> cases p.testBit i <;> decide

/-- `JJ N n k` is the inner index `j`. -/
def JJ (N n k : ℕ) : ℕ := (N - n*(k+1)) / (n+1)

/-- `FF N n k` is the summand. -/
def FF (N n k : ℕ) : ℕ :=
  if n*(k+1) ≤ N ∧ (N - n*(k+1)) % (n+1) = 0 then
    n.choose k * (n + JJ N n k).choose (JJ N n k)
  else 0

/-- `cont N n k` says the summand `FF N n k` is odd. -/
def cont (N n k : ℕ) : Prop :=
  n*(k+1) ≤ N ∧ (N - n*(k+1)) % (n+1) = 0 ∧
  n.choose k % 2 = 1 ∧ (n + JJ N n k).choose (JJ N n k) % 2 = 1

instance (N n k : ℕ) : Decidable (cont N n k) := by unfold cont; infer_instance

theorem FF_odd_iff (N n k : ℕ) : FF N n k % 2 = 1 ↔ cont N n k := by
  unfold FF cont
  by_cases h : n*(k+1) ≤ N ∧ (N - n*(k+1)) % (n+1) = 0
  · rw [if_pos h, ← Nat.odd_iff, Nat.odd_mul, Nat.odd_iff, Nat.odd_iff]
    constructor
    · rintro ⟨ha, hb⟩; exact ⟨h.1, h.2, ha, hb⟩
    · rintro ⟨-, -, ha, hb⟩; exact ⟨ha, hb⟩
  · rw [if_neg h]
    constructor
    · intro hh; simp at hh
    · rintro ⟨h1, h2, -, -⟩; exact absurd ⟨h1, h2⟩ h

theorem cont_le (N n k : ℕ) (hc : cont N n k) : k ≤ n := by
  by_contra hh; push_neg at hh
  obtain ⟨-, -, h3, -⟩ := hc
  rw [Nat.choose_eq_zero_of_lt hh] at h3; simp at h3

theorem partner_spec (N n k : ℕ) (hc : cont N n k) :
    cont N (JJ N n k + k) k ∧ JJ N (JJ N n k + k) k = n - k := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have hkn : k ≤ n := cont_le N n k ⟨h1, h2, h3, h4⟩
  obtain ⟨q, hq⟩ : ∃ q, n = q + k := ⟨n - k, by omega⟩
  set j := JJ N n k with hjdef
  -- disjointness facts
  have pk0 : q &&& k = 0 := (add_choose_odd_iff q k).1 (by
    rw [← hq]; exact Nat.odd_iff.2 h3)
  have nj0 : n &&& j = 0 := (add_choose_odd_iff n j).1 (Nat.odd_iff.2 h4)
  have hkpj : (k + q) &&& j = 0 := by rw [show k + q = n from by omega]; exact nj0
  obtain ⟨jk0, jq0⟩ := derive k q j pk0 hkpj
  -- equation
  have hjm : j * (n+1) = N - n*(k+1) := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h2)
  have EQ : n*(k+1) + j*(n+1) = N := by omega
  have ESym : (j+k)*(k+1) + (j+k+1)*q = N := by
    rw [hq] at EQ; linear_combination EQ
  have cond1 : (j+k)*(k+1) ≤ N := by omega
  have newR : N - (j+k)*(k+1) = ((j+k)+1)*q := by omega
  have Jval : JJ N (j+k) k = q := by
    rw [JJ, newR]; exact Nat.mul_div_cancel_left q (Nat.succ_pos _)
  refine ⟨⟨cond1, ?_, ?_, ?_⟩, by rw [Jval]; omega⟩
  · rw [newR]; exact Nat.mul_mod_right _ _
  · -- (j+k).choose k % 2 = 1
    exact Nat.odd_iff.1 ((add_choose_odd_iff j k).2 jk0)
  · -- ((j+k) + JJ N (j+k) k).choose (JJ N (j+k) k) % 2 = 1
    rw [Jval]
    exact Nat.odd_iff.1 ((add_choose_odd_iff (j+k) q).2 jq0)

theorem fixed_point (N n k : ℕ) (hc : cont N n k) (hfix : JJ N n k + k = n) :
    N = k * (k + 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have hkn : k ≤ n := cont_le N n k ⟨h1, h2, h3, h4⟩
  set j := JJ N n k with hjdef
  have hjk : j + k = n := hfix
  -- j is disjoint from k (from Odd C(n,k))
  have pk0 : (n-k) &&& k = 0 := (add_choose_odd_iff (n-k) k).1 (by
    rw [Nat.sub_add_cancel hkn]; exact Nat.odd_iff.2 h3)
  have jeq : j = n - k := by omega
  have jk0 : j &&& k = 0 := by rw [jeq]; exact pk0
  have nj0 : n &&& j = 0 := (add_choose_odd_iff n j).1 (Nat.odd_iff.2 h4)
  -- n = j ||| k
  have hor : n = j ||| k := by rw [← hjk]; exact disjoint_add_eq_lor j k jk0
  -- n &&& j = j  (absorption), combined with n &&& j = 0 gives j = 0
  have absorb : n &&& j = j := by
    rw [hor]; apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_land, Nat.testBit_lor]
    cases j.testBit i <;> cases k.testBit i <;> decide
  have hj0 : j = 0 := by rw [absorb] at nj0; exact nj0.symm ▸ nj0 ▸ rfl
  -- so n = k
  have hnk : n = k := by omega
  -- equation
  have hjm : j * (n+1) = N - n*(k+1) := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h2)
  have EQ : n*(k+1) + j*(n+1) = N := by omega
  rw [hnk, hj0] at EQ; omega

/-- The partner map. -/
def g (N : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if cont N p.1 p.2 then (JJ N p.1 p.2 + p.2, p.2) else p

theorem cast_zmod2 (m : ℕ) : (m : ZMod 2) = if m % 2 = 1 then 1 else 0 := by
  rw [← ZMod.natCast_mod m 2]
  rcases Nat.mod_two_eq_zero_or_one m with h|h <;> rw [h] <;> simp

theorem FF_zero_of_lt (N n k : ℕ) (h : n < k) : FF N n k = 0 := by
  unfold FF; rw [Nat.choose_eq_zero_of_lt h]; simp

theorem a_eq (N : ℕ) : a N = ∑ p ∈ (range (N+1) ×ˢ range (N+1)), FF N p.1 p.2 := by
  rw [Finset.sum_product]
  have h0 : a N = ∑ n ∈ range (N+1), ∑ k ∈ range (n+1), FF N n k := rfl
  rw [h0]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mem_range] at hn
  apply Finset.sum_subset
  · intro k hk; rw [mem_range] at hk ⊢; omega
  · intro k _ hk2; rw [mem_range] at hk2
    exact FF_zero_of_lt N n k (by omega)

theorem a_even (N : ℕ) (hN : ¬ ∃ k, N = k*(k+1)) : a N % 2 = 0 := by
  have hf : ∀ n k, ((FF N n k : ℕ) : ZMod 2) = if cont N n k then 1 else 0 := by
    intro n k; rw [cast_zmod2]
    by_cases hc : cont N n k
    · rw [if_pos hc, if_pos ((FF_odd_iff N n k).2 hc)]
    · rw [if_neg hc, if_neg (fun h => hc ((FF_odd_iff N n k).1 h))]
  have hsum : (a N : ZMod 2) = 0 := by
    rw [a_eq, Nat.cast_sum]
    apply Finset.sum_involution (fun p _ => g N p)
    · -- hg₁ : f p + f (g p) = 0
      rintro ⟨n, k⟩ hp
      by_cases hc : cont N n k
      · have hg : g N (n, k) = (JJ N n k + k, k) := by simp only [g]; rw [if_pos hc]
        simp only [hg, hf, if_pos hc, if_pos (partner_spec N n k hc).1]
        decide
      · have hg : g N (n, k) = (n, k) := by simp only [g]; rw [if_neg hc]
        simp only [hg, hf, if_neg hc]
        decide
    · -- hg₃ : f p ≠ 0 → g p ≠ p
      rintro ⟨n, k⟩ hp hfne
      have hc : cont N n k := by
        by_contra hc; apply hfne; simp only [hf, if_neg hc]
      have hg : g N (n, k) = (JJ N n k + k, k) := by simp only [g]; rw [if_pos hc]
      rw [hg]
      intro heq
      have hfst : JJ N n k + k = n := congrArg Prod.fst heq
      exact hN ⟨k, fixed_point N n k hc hfst⟩
    · -- g_mem
      rintro ⟨n, k⟩ hp
      by_cases hc : cont N n k
      · have hg : g N (n, k) = (JJ N n k + k, k) := by simp only [g]; rw [if_pos hc]
        rw [hg]
        have hpart := (partner_spec N n k hc).1
        have hbig : (JJ N n k + k) ≤ (JJ N n k + k) * (k + 1) :=
          Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
        have hle : (JJ N n k + k) ≤ N := le_trans hbig hpart.1
        simp only [Finset.mem_product, Finset.mem_range]
        omega
      · have hg : g N (n, k) = (n, k) := by simp only [g]; rw [if_neg hc]
        rw [hg]; exact hp
    · -- hg₄ : g (g p) = p
      rintro ⟨n, k⟩ hp
      by_cases hc : cont N n k
      · have hg : g N (n, k) = (JJ N n k + k, k) := by simp only [g]; rw [if_pos hc]
        have hpart := partner_spec N n k hc
        have hkn : k ≤ n := cont_le N n k hc
        rw [hg]
        have hg2 : g N (JJ N n k + k, k) = (JJ N (JJ N n k + k) k + k, k) := by
          simp only [g]; rw [if_pos hpart.1]
        rw [hg2, hpart.2, Nat.sub_add_cancel hkn]
      · have hg : g N (n, k) = (n, k) := by simp only [g]; rw [if_neg hc]
        rw [hg, hg]
  have hdvd : (2 : ℕ) ∣ a N := (ZMod.natCast_eq_zero_iff (a N) 2).mp hsum
  omega


/-- oeis_325046_conjecture_0: Odd terms occur only at positions n*(n+1) for n >= 0 (conjecture). -/
theorem a325046_odd_terms_at_k_times_k_plus_1 (N : ℕ) :
  a N % 2 = 1 → ∃ k : ℕ, N = k * (k + 1) :=
by
  intro h
  by_contra hN
  have hz : a N % 2 = 0 := a_even N hN
  omega
