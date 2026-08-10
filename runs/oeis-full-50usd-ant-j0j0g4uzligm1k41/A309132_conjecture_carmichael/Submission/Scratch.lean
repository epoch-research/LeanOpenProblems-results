import FormalConjectures.Util.ProblemImports

open Rat Nat Finset

/-- Binomial absorption: for `i ≤ n`, `(n+1).choose i * (n+1-i) = (n+1) * n.choose i`. -/
theorem choose_absorb (n i : ℕ) (hi : i ≤ n) :
    (n + 1).choose i * (n + 1 - i) = (n + 1) * n.choose i := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_succ_of_le hi)  -- i ≤ n+1
  have h2 := Nat.choose_mul_factorial_mul_factorial hi
  -- (n+1-i)! = (n+1-i) * (n-i)!
  have h3 : (n + 1 - i)! = (n + 1 - i) * (n - i)! := by
    have : n + 1 - i = (n - i) + 1 := by omega
    rw [this, Nat.factorial_succ]
  have hK : 0 < i ! * (n - i)! := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_right hK
  have e1 : (n + 1).choose i * (n + 1 - i) * (i ! * (n - i)!)
      = (n + 1).choose i * i ! * (n + 1 - i)! := by rw [h3]; ring
  have e2 : (n + 1) * n.choose i * (i ! * (n - i)!) = (n + 1) * (n.choose i * i ! * (n - i)!) := by
    ring
  rw [e1, e2, h2, h1, Nat.factorial_succ]

/-- For `m ≥ 2`, `m + 1 < 2 ^ m`. -/
theorem succ_lt_two_pow (m : ℕ) (hm : 2 ≤ m) : m + 1 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by ring
    have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

/-- `2 ^ (padicValNat p j) ≤ j` for prime `p` and `j ≥ 1`. -/
theorem two_pow_padicVal_le (p j : ℕ) [Fact p.Prime] (hj : 1 ≤ j) :
    2 ^ padicValNat p j ≤ j := by
  have hdvd : p ^ padicValNat p j ∣ j := pow_padicValNat_dvd
  have hle : p ^ padicValNat p j ≤ j := Nat.le_of_dvd (by omega) hdvd
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  exact le_trans (Nat.pow_le_pow_left hp2 _) hle

/-- L1: `padicValNat p j ≤ j - 1` for prime `p`, `j ≥ 1`. -/
theorem padicVal_le_pred (p j : ℕ) [Fact p.Prime] (hj : 1 ≤ j) :
    padicValNat p j ≤ j - 1 := by
  by_contra h
  push_neg at h
  -- h : j - 1 < padicValNat p j, so j ≤ padicValNat p j
  have hjle : j ≤ padicValNat p j := by omega
  have h2 := two_pow_padicVal_le p j hj
  have : 2 ^ j ≤ 2 ^ padicValNat p j := Nat.pow_le_pow_right (by norm_num) hjle
  have hlt : j < 2 ^ j := Nat.lt_two_pow_self
  omega

/-- L2: `padicValNat p j ≤ j - 2` for prime `p`, `j ≥ 3`. -/
theorem padicVal_le_pred2 (p j : ℕ) [Fact p.Prime] (hj : 3 ≤ j) :
    padicValNat p j ≤ j - 2 := by
  by_contra h
  push_neg at h
  have hjle : j - 1 ≤ padicValNat p j := by omega
  have h2 := two_pow_padicVal_le p j (by omega)
  have : 2 ^ (j - 1) ≤ 2 ^ padicValNat p j := Nat.pow_le_pow_right (by norm_num) hjle
  have hlt : (j - 1) + 1 < 2 ^ (j - 1) := succ_lt_two_pow (j - 1) (by omega)
  omega

/-- Rewrite of the Faulhaber term using binomial absorption. -/
theorem term_rewrite (pr n i : ℕ) (hi : i ≤ n) :
    bernoulli i * ((n + 1).choose i : ℚ) * (pr : ℚ) ^ (n + 1 - i) / ((n : ℚ) + 1)
      = bernoulli i * (n.choose i : ℚ) * (pr : ℚ) ^ (n + 1 - i) / ((n + 1 - i : ℕ) : ℚ) := by
  have hca := choose_absorb n i hi
  have hcast : ((n + 1).choose i : ℚ) * ((n + 1 - i : ℕ) : ℚ)
      = ((n + 1 : ℕ) : ℚ) * (n.choose i : ℚ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hca
  have h1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((n + 1 - i : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : n + 1 - i ≠ 0)
  rw [div_eq_div_iff h1 h2]
  have hcast' : ((n + 1).choose i : ℚ) * ((n + 1 - i : ℕ) : ℚ)
      = ((n : ℚ) + 1) * (n.choose i : ℚ) := by push_cast at hcast ⊢; linarith [hcast]
  linear_combination (bernoulli i * (pr : ℚ) ^ (n + 1 - i)) * hcast'

/-- Value of the p-adic valuation of a single term in the Faulhaber sum (rewritten form). -/
theorem term_val_eq (p : ℕ) [hp : Fact p.Prime] (n i : ℕ) (hi : i ≤ n)
    (hb : bernoulli i ≠ 0) :
    padicValRat p (bernoulli i * (n.choose i : ℚ) * (p : ℚ) ^ (n + 1 - i) / ((n + 1 - i : ℕ) : ℚ))
      = padicValRat p (bernoulli i) + (padicValNat p (n.choose i) : ℤ)
        + ((n + 1 - i : ℕ) : ℤ) - (padicValNat p (n + 1 - i) : ℤ) := by
  have hp1 : (1 : ℕ) < p := hp.out.one_lt
  set J := n + 1 - i with hJ
  have hJ1 : 1 ≤ J := by omega
  have hcne : (n.choose i : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi).ne'
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.pos.ne'
  have hppow : ((p : ℚ)) ^ J ≠ 0 := pow_ne_zero _ hpne
  have hJne : ((J : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : J ≠ 0)
  have hnum : bernoulli i * (n.choose i : ℚ) * (p : ℚ) ^ J ≠ 0 :=
    mul_ne_zero (mul_ne_zero hb hcne) hppow
  rw [padicValRat.div hnum hJne, padicValRat.mul (mul_ne_zero hb hcne) hppow,
    padicValRat.mul hb hcne, padicValRat.pow hpne, padicValRat.self hp1,
    padicValRat.of_nat, padicValRat.of_nat]
  push_cast
  ring

/-- Lower bound for the `p`-adic valuation of a Faulhaber term, in terms of `J = n+1-i`. -/
theorem term_bound (p : ℕ) [Fact p.Prime] (n i : ℕ) (hi : i < n)
    (hIH : (-1 : ℤ) ≤ padicValRat p (bernoulli i)) :
    bernoulli i * ((n + 1).choose i : ℚ) * (p : ℚ) ^ (n + 1 - i) / ((n : ℚ) + 1) = 0 ∨
    (-1 : ℤ) + (((n + 1 - i : ℕ) : ℤ) - (padicValNat p (n + 1 - i) : ℤ))
      ≤ padicValRat p (bernoulli i * ((n + 1).choose i : ℚ) * (p : ℚ) ^ (n + 1 - i) / ((n : ℚ) + 1)) := by
  by_cases hb : bernoulli i = 0
  · left; rw [hb]; ring
  · right
    rw [term_rewrite p n i (le_of_lt hi), term_val_eq p n i (le_of_lt hi) hb]
    have h1 : (0 : ℤ) ≤ (padicValNat p (n.choose i) : ℤ) := Int.natCast_nonneg _
    linarith [hIH, h1]

theorem sum_neg_eq (s : Finset ℕ) (f : ℕ → ℚ) : ∑ i ∈ s, (-(f i)) = -(∑ i ∈ s, f i) := by
  simp [Finset.sum_neg_distrib]

/-- The key rearrangement of Faulhaber's formula isolating `bernoulli n`. -/
theorem bernoulli_mul_prime_eq (p n : ℕ) (hn : 1 ≤ n) :
    bernoulli n * (p : ℚ) = (∑ k ∈ range p, (k : ℚ) ^ n)
      - ∑ i ∈ range n, bernoulli i * ((n + 1).choose i : ℚ) * (p : ℚ) ^ (n + 1 - i) / ((n : ℚ) + 1) := by
  have key := sum_range_pow p n
  rw [Finset.sum_range_succ] at key
  have hfn : bernoulli n * ((n + 1).choose n : ℚ) * (p : ℚ) ^ (n + 1 - n) / ((n : ℚ) + 1)
      = bernoulli n * (p : ℚ) := by
    rw [Nat.choose_succ_self_right]
    have h1 : n + 1 - n = 1 := by omega
    rw [h1]
    have h2 : ((n : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [hfn] at key
  linarith [key]

/-- A finite sum of rationals, each either zero or with `p`-adic valuation `≥ c`, is itself
either zero or has `p`-adic valuation `≥ c`. -/
theorem val_sum_lb (p : ℕ) [Fact p.Prime] (c : ℤ) (s : Finset ℕ) (F : ℕ → ℚ)
    (h : ∀ i ∈ s, F i = 0 ∨ c ≤ padicValRat p (F i)) :
    (∑ i ∈ s, F i) = 0 ∨ c ≤ padicValRat p (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => left; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have ha' := h a (Finset.mem_insert_self a s)
    have ih' := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    rcases ha' with h0 | hv
    · rw [h0, zero_add]; exact ih'
    · rcases ih' with h0 | hv2
      · rw [h0, add_zero]; exact Or.inr hv
      · by_cases hsum : F a + ∑ i ∈ s, F i = 0
        · exact Or.inl hsum
        · refine Or.inr (le_trans ?_ (padicValRat.min_le_padicValRat_add hsum))
          exact le_min hv hv2

/-- **Integrality part of von Staudt–Clausen**: `padicValRat p (bernoulli n) ≥ -1`. -/
theorem bernoulli_padicVal_ge (p : ℕ) [hp : Fact p.Prime] :
    ∀ n, (-1 : ℤ) ≤ padicValRat p (bernoulli n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0; rw [bernoulli_zero]; simp
    · by_cases hbn : bernoulli n = 0
      · rw [hbn]; simp
      · have hppos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
        have hmul : padicValRat p (bernoulli n * (p : ℚ))
            = padicValRat p (bernoulli n) + 1 := by
          rw [padicValRat.mul hbn (ne_of_gt hppos), padicValRat.self hp.out.one_lt]
        suffices h : (0 : ℤ) ≤ padicValRat p (bernoulli n * (p : ℚ)) by linarith [hmul]
        rw [bernoulli_mul_prime_eq p n hn1]
        -- A := nat power sum, B := -(sum of Faulhaber terms)
        set A : ℚ := ∑ k ∈ range p, (k : ℚ) ^ n with hA
        have hAnat : A = ((∑ k ∈ range p, k ^ n : ℕ) : ℚ) := by rw [hA]; push_cast; ring
        have hAval : (0 : ℤ) ≤ padicValRat p A := by
          rw [hAnat, padicValRat.of_nat]; exact Int.natCast_nonneg _
        -- per-term bound for the (negated) Faulhaber terms
        have hterm : ∀ i ∈ range n,
            (-(bernoulli i * ((n + 1).choose i : ℚ) * (p : ℚ) ^ (n + 1 - i) / ((n : ℚ) + 1))) = 0 ∨
            (0 : ℤ) ≤ padicValRat p (-(bernoulli i * ((n + 1).choose i : ℚ) * (p : ℚ) ^ (n + 1 - i) / ((n : ℚ) + 1))) := by
          intro i hi
          rw [Finset.mem_range] at hi
          rcases term_bound p n i hi (IH i hi) with h0 | hv
          · left; rw [h0]; ring
          · right
            rw [padicValRat.neg]
            refine le_trans ?_ hv
            have hge : padicValNat p (n + 1 - i) ≤ (n + 1 - i) - 1 :=
              padicVal_le_pred p (n + 1 - i) (by omega)
            have : (padicValNat p (n + 1 - i) : ℤ) ≤ ((n + 1 - i : ℕ) : ℤ) - 1 := by
              have h2 : 1 ≤ n + 1 - i := by omega
              omega
            linarith
        have hB := val_sum_lb p 0 (range n)
          (fun i => -(bernoulli i * ((n + 1).choose i : ℚ) * (p : ℚ) ^ (n + 1 - i) / ((n : ℚ) + 1))) hterm
        rw [sum_neg_eq] at hB
        set B : ℚ := ∑ i ∈ range n, bernoulli i * ((n + 1).choose i : ℚ) * (p : ℚ) ^ (n + 1 - i) / ((n : ℚ) + 1) with hBdef
        -- hB : -B = 0 ∨ 0 ≤ padicValRat p (-B)
        have hgoal : (0 : ℤ) ≤ padicValRat p (A + (-B)) := by
          rcases hB with hB0 | hBv
          · rw [hB0, add_zero]; exact hAval
          · by_cases hsum : A + (-B) = 0
            · rw [hsum]; simp
            · exact le_trans (le_min hAval hBv) (padicValRat.min_le_padicValRat_add hsum)
        rw [sub_eq_add_neg]
        exact hgoal

/-- Power sum modulo `p`. -/
theorem power_sum_zmod (p n : ℕ) [Fact p.Prime] (hn : 1 ≤ n) :
    ((∑ k ∈ range p, k ^ n : ℕ) : ZMod p) = if (p - 1) ∣ n then -1 else 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hbij : ∑ x : ZMod p, x ^ n = ∑ b ∈ range p, ((b : ZMod p)) ^ n := by
    refine Finset.sum_bij' (fun a _ => (ZMod.val a)) (fun b _ => (b : ZMod p)) ?_ ?_ ?_ ?_ ?_
    · intro a _; rw [Finset.mem_range]; exact ZMod.val_lt a
    · intro b _; exact Finset.mem_univ _
    · intro a _; exact ZMod.natCast_rightInverse a
    · intro b hb; rw [Finset.mem_range] at hb; exact ZMod.val_natCast_of_lt hb
    · intro a _; rw [ZMod.natCast_rightInverse a]
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have h0 : (0 : ZMod p) ^ n = 0 := zero_pow (by omega)
  let embU : (ZMod p)ˣ ↪ ZMod p := ⟨fun x => x, Units.val_injective⟩
  have himg : Finset.univ.map embU = Finset.univ \ {(0 : ZMod p)} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, embU] using isUnit_iff_ne_zero
  have hsplit : ∑ x : ZMod p, x ^ n = ∑ x : (ZMod p)ˣ, ((x : ZMod p)) ^ n := by
    calc ∑ x : ZMod p, x ^ n = ∑ x ∈ Finset.univ \ {(0:ZMod p)}, x ^ n := by
          rw [← Finset.sum_sdiff ({0} : Finset (ZMod p)).subset_univ, sum_singleton, h0, add_zero]
      _ = ∑ x : (ZMod p)ˣ, ((x:ZMod p)) ^ n := by rw [← himg, univ.sum_map embU]; rfl
  have hunits := FiniteField.sum_pow_units (ZMod p) n
  rw [hcard] at hunits
  have hcast : ((∑ k ∈ range p, k ^ n : ℕ) : ZMod p) = ∑ b ∈ range p, ((b : ZMod p)) ^ n := by
    push_cast; rfl
  rw [hcast, ← hbij, hsplit, hunits]

/-- `p`-adic valuation of the integer power sum `A = ∑_{k<p} k^n`. -/
theorem powersum_padicVal (p n : ℕ) [hp : Fact p.Prime] (hn : 1 ≤ n) :
    ((p - 1) ∣ n → padicValRat p (∑ k ∈ range p, (k : ℚ) ^ n) = 0) ∧
    (¬ (p - 1) ∣ n → 1 ≤ padicValRat p (∑ k ∈ range p, (k : ℚ) ^ n)) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : Nontrivial (ZMod p) := by
    haveI := Fact.mk hp.out; exact inferInstance
  set Aq : ℚ := ∑ k ∈ range p, (k : ℚ) ^ n with hAq
  have hAeq : Aq = ((∑ k ∈ range p, k ^ n : ℕ) : ℚ) := by rw [hAq]; push_cast; rfl
  have hApos : 1 ≤ (∑ k ∈ range p, k ^ n : ℕ) := by
    have h1mem : 1 ∈ range p := Finset.mem_range.mpr (by have := hp.out.two_le; omega)
    have := Finset.single_le_sum (f := fun k => k ^ n) (fun i _ => Nat.zero_le _) h1mem
    simpa using this
  have hAne : (∑ k ∈ range p, k ^ n : ℕ) ≠ 0 := by omega
  have hval : padicValRat p Aq = (padicValNat p (∑ k ∈ range p, k ^ n) : ℤ) := by
    rw [hAeq, padicValRat.of_nat]
  have hz := power_sum_zmod p n hn
  constructor
  · intro hdvd
    rw [if_pos hdvd] at hz
    have hnd : ¬ (p ∣ (∑ k ∈ range p, k ^ n)) := by
      rw [← ZMod.natCast_eq_zero_iff, hz]
      exact neg_ne_zero.mpr one_ne_zero
    rw [hval, padicValNat.eq_zero_of_not_dvd hnd]; rfl
  · intro hndvd
    rw [if_neg hndvd] at hz
    have hdvd : p ∣ (∑ k ∈ range p, k ^ n) := by
      rw [← ZMod.natCast_eq_zero_iff]; exact hz
    rw [hval]
    exact_mod_cast one_le_padicValNat_of_dvd hAne hdvd

/-- For even `n ≥ 4`, the Faulhaber correction sum `B` is `0` or has valuation `≥ 1`. -/
theorem faulhaber_sum_crit (p n : ℕ) [Fact p.Prime] (hn : 4 ≤ n) (hne : Even n) :
    (∑ i ∈ range n, bernoulli i * ((n + 1).choose i : ℚ) * (p : ℚ) ^ (n + 1 - i) / ((n : ℚ) + 1)) = 0 ∨
    (1 : ℤ) ≤ padicValRat p (∑ i ∈ range n, bernoulli i * ((n + 1).choose i : ℚ) * (p : ℚ) ^ (n + 1 - i) / ((n : ℚ) + 1)) := by
  apply val_sum_lb p 1 (range n)
  intro i hi
  rw [Finset.mem_range] at hi
  by_cases hb : bernoulli i = 0
  · left; rw [hb]; ring
  · right
    have hJ3 : 3 ≤ n + 1 - i := by
      rcases Nat.lt_or_ge i (n - 1) with h | h
      · omega
      · exfalso; apply hb
        have hi1 : i = n - 1 := by omega
        rw [hi1]
        have hodd : Odd (n - 1) := by
          rcases hne with ⟨m, hm⟩
          exact ⟨m - 1, by omega⟩
        exact bernoulli_eq_zero_of_odd hodd (by omega)
    rw [term_rewrite p n i (le_of_lt hi), term_val_eq p n i (le_of_lt hi) hb]
    have hge := bernoulli_padicVal_ge p i
    have hL2 := padicVal_le_pred2 p (n + 1 - i) hJ3
    have h1 : (0 : ℤ) ≤ (padicValNat p (n.choose i) : ℤ) := Int.natCast_nonneg _
    have hL2' : (padicValNat p (n + 1 - i) : ℤ) ≤ ((n + 1 - i : ℕ) : ℤ) - 2 := by
      have : 2 ≤ n + 1 - i := by omega
      omega
    linarith

/-- **von Staudt–Clausen criterion** (`p`-adic valuation form) for even `n ≥ 4`. -/
theorem bernoulli_padicVal_crit (p n : ℕ) [hp : Fact p.Prime] (hn : 4 ≤ n) (hne : Even n) :
    ((p - 1) ∣ n → padicValRat p (bernoulli n) = -1) ∧
    (¬ (p - 1) ∣ n → 0 ≤ padicValRat p (bernoulli n)) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hppos : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.out.pos
  have hpne : (p : ℚ) ≠ 0 := ne_of_gt hppos
  have heq := bernoulli_mul_prime_eq p n (by omega)
  set A : ℚ := ∑ k ∈ range p, (k : ℚ) ^ n with hA
  set B : ℚ := ∑ i ∈ range n, bernoulli i * ((n + 1).choose i : ℚ) * (p : ℚ) ^ (n + 1 - i) / ((n : ℚ) + 1) with hB
  have hAne : A ≠ 0 := by
    have hAeq : A = ((∑ k ∈ range p, k ^ n : ℕ) : ℚ) := by rw [hA]; push_cast; rfl
    have h1mem : 1 ∈ range p := Finset.mem_range.mpr (by have := hp.out.two_le; omega)
    have hpos := Finset.single_le_sum (f := fun k => k ^ n) (fun i _ => Nat.zero_le _) h1mem
    simp only [one_pow] at hpos
    rw [hAeq]; exact_mod_cast (by omega : (∑ k ∈ range p, k ^ n : ℕ) ≠ 0)
  have hcritB := faulhaber_sum_crit p n hn hne
  rw [← hB] at hcritB
  have hpsum := powersum_padicVal p n (by omega)
  rw [← hA] at hpsum
  have hmulval : ∀ q : ℚ, q ≠ 0 → padicValRat p (q * (p : ℚ)) = padicValRat p q + 1 := by
    intro q hq; rw [padicValRat.mul hq hpne, padicValRat.self hp.out.one_lt]
  constructor
  · -- (p-1) ∣ n
    intro hdvd
    have hA0 : padicValRat p A = 0 := hpsum.1 hdvd
    have hABne : A - B ≠ 0 := by
      rcases hcritB with hB0 | hBv
      · rw [hB0, sub_zero]; exact hAne
      · intro hc
        have hAB : A = B := by linarith [hc]
        rw [hAB] at hA0; linarith [hBv]
    have hABval : padicValRat p (A - B) = 0 := by
      rcases hcritB with hB0 | hBv
      · rw [hB0, sub_zero]; exact hA0
      · have hBne : B ≠ 0 := by intro h; rw [h] at hBv; simp at hBv
        rw [sub_eq_add_neg]
        rw [padicValRat.add_eq_of_lt (by rwa [← sub_eq_add_neg]) hAne
          (neg_ne_zero.mpr hBne) (by rw [padicValRat.neg]; rw [hA0]; linarith [hBv])]
        exact hA0
    have hbnp_ne : bernoulli n * (p : ℚ) ≠ 0 := by rw [heq]; exact hABne
    have hbn_ne : bernoulli n ≠ 0 := fun h => by rw [h, zero_mul] at hbnp_ne; exact hbnp_ne rfl
    have : padicValRat p (bernoulli n * (p : ℚ)) = 0 := by rw [heq]; exact hABval
    rw [hmulval _ hbn_ne] at this
    linarith
  · -- ¬ (p-1) ∣ n
    intro hndvd
    have hA1 : 1 ≤ padicValRat p A := hpsum.2 hndvd
    by_cases hbn : bernoulli n = 0
    · rw [hbn]; simp
    · have hbnp_ne : bernoulli n * (p : ℚ) ≠ 0 := mul_ne_zero hbn hpne
      have hABne : A - B ≠ 0 := by rw [← heq]; exact hbnp_ne
      have hABval : 1 ≤ padicValRat p (A - B) := by
        rcases hcritB with hB0 | hBv
        · rw [hB0, sub_zero]; exact hA1
        · rw [sub_eq_add_neg]
          refine le_trans (le_min hA1 ?_) (padicValRat.min_le_padicValRat_add (by rwa [← sub_eq_add_neg]))
          rw [padicValRat.neg]; exact hBv
      have hval : padicValRat p (bernoulli n * (p : ℚ)) = padicValRat p (bernoulli n) + 1 :=
        hmulval _ hbn
      rw [heq] at hval
      linarith [hABval, hval]

/-- Squarefreeness via `p`-adic valuations. -/
theorem squarefree_iff_padic (m : ℕ) (hm : m ≠ 0) :
    Squarefree m ↔ ∀ p, p.Prime → padicValNat p m ≤ 1 := by
  rw [Nat.squarefree_iff_factorization_le_one hm]
  constructor
  · intro h p pp; rw [← Nat.factorization_def m pp]; exact h p
  · intro h p
    by_cases pp : p.Prime
    · rw [Nat.factorization_def m pp]; exact h p pp
    · rw [Nat.factorization_eq_zero_of_non_prime m pp]; exact Nat.zero_le _

/-- The `p`-adic valuation of the denominator is `≤ 1` iff the rational has valuation `≥ -1`. -/
theorem den_padic_le_one (q : ℚ) (p : ℕ) [hp : Fact p.Prime] :
    padicValNat p q.den ≤ 1 ↔ -1 ≤ padicValRat p q := by
  have hkey : padicValNat p q.den = 0 ∨ padicValInt p q.num = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hd, hm⟩ := hcon
    have hdvd_den : p ∣ q.den := dvd_of_one_le_padicValNat (by omega)
    have hdvd_num : p ∣ q.num.natAbs := by
      have : padicValNat p q.num.natAbs ≠ 0 := hm
      exact dvd_of_one_le_padicValNat (by omega)
    have hco : Nat.gcd q.num.natAbs q.den = 1 := q.reduced
    have : p ∣ 1 := hco ▸ Nat.dvd_gcd hdvd_num hdvd_den
    exact Nat.Prime.one_lt hp.out |>.ne' (Nat.dvd_one.mp this)
  have hdef : padicValRat p q = (padicValInt p q.num : ℤ) - (padicValNat p q.den : ℤ) :=
    padicValRat_def p q
  rcases hkey with h0 | h0 <;> rw [hdef, h0] <;> omega

open ArithmeticFunction in
/-- The Carmichael lambda of a prime is `p - 1`. -/
theorem carmichael_prime {p : ℕ} (hp : p.Prime) : Carmichael p = p - 1 := by
  rcases eq_or_ne p 2 with h2 | h2
  · subst h2
    have he : Carmichael 2 = Carmichael (2 ^ 1) := by norm_num
    rw [he, carmichael_two_pow_of_le_two (by norm_num)]
    norm_num
  · have he : p = p ^ 1 := (pow_one p).symm
    rw [he, carmichael_pow_of_prime_ne_two 1 hp h2, pow_one, Nat.totient_prime hp]

open ArithmeticFunction in
/-- `p` divides the Carmichael lambda of `p²`. -/
theorem carmichael_psq_dvd {p : ℕ} (hp : p.Prime) : p ∣ Carmichael (p ^ 2) := by
  rcases eq_or_ne p 2 with h2 | h2
  · subst h2
    rw [carmichael_two_pow_of_le_two (by norm_num)]; norm_num
  · rw [carmichael_pow_of_prime_ne_two 2 hp h2, Nat.totient_prime_pow hp (by norm_num)]
    exact (dvd_pow_self p (by norm_num)).mul_right _

open ArithmeticFunction in
/-- The Fermat (all-bases) condition is equivalent to `λ(n) ∣ n-1`. -/
theorem fermat_iff_carmichael_dvd (n : ℕ) (hn : 1 ≤ n) :
    (∀ b : ℕ, Nat.gcd b n = 1 → b ^ (n - 1) ≡ 1 [MOD n]) ↔ Carmichael n ∣ (n - 1) := by
  haveI : NeZero n := ⟨by omega⟩
  rw [carmichael_eq_exponent (by omega), Monoid.exponent_dvd_iff_forall_pow_eq_one]
  constructor
  · intro h u
    have hb := h (u : ZMod n).val (ZMod.val_coe_unit_coprime u)
    rw [← ZMod.natCast_eq_natCast_iff] at hb
    push_cast at hb
    rw [ZMod.natCast_val, ZMod.cast_id] at hb
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hb
  · intro h b hb
    have hco : Nat.Coprime b n := hb
    have hu := h (ZMod.unitOfCoprime b hco)
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    have h2 := congrArg (Units.val) hu
    rw [Units.val_pow_eq_pow_val, Units.val_one, ZMod.coe_unitOfCoprime] at h2
    exact h2

open ArithmeticFunction in
/-- **Korselt's criterion** (in `λ`-form): `λ(n) ∣ n-1` iff `n` is squarefree and `(p-1)∣(n-1)`
for every prime `p ∣ n`. -/
theorem korselt (n : ℕ) (hn : 1 ≤ n) :
    Carmichael n ∣ (n - 1) ↔
      (Squarefree n ∧ ∀ p, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)) := by
  haveI : NeZero n := ⟨by omega⟩
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [Nat.squarefree_iff_prime_squarefree]
      intro p hp hpsq
      have hp2 : p ^ 2 ∣ n := by rwa [sq]
      have hd1 : Carmichael (p ^ 2) ∣ Carmichael n := carmichael_dvd hp2
      have hpdvd : p ∣ Carmichael (p ^ 2) := carmichael_psq_dvd hp
      have hpn1 : p ∣ (n - 1) := dvd_trans hpdvd (dvd_trans hd1 h)
      have hpn : p ∣ n := dvd_trans (dvd_pow_self p (by norm_num)) hp2
      have hp1 : p ∣ 1 := by
        have hsub := Nat.dvd_sub hpn hpn1
        rwa [Nat.sub_sub_self hn] at hsub
      exact hp.one_lt.ne' (Nat.dvd_one.mp hp1)
    · intro p hp hpn
      have hcp : Carmichael p = p - 1 := carmichael_prime hp
      have hdd : (p - 1) ∣ Carmichael n := hcp ▸ carmichael_dvd hpn
      exact dvd_trans hdd h
  · rintro ⟨hsqf, hdvd⟩
    rw [carmichael_factorization n]
    apply Finset.lcm_dvd
    intro p hpmem
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
    have hfact : n.factorization p = 1 := by
      have hle : n.factorization p ≤ 1 := hsqf.natFactorization_le_one p
      have hpos : 0 < n.factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpn
      omega
    rw [hfact, pow_one, carmichael_prime hp]
    exact hdvd p hp hpn

/-- For any rational, the numerator and denominator are not both divisible by `p`. -/
theorem padic_num_or_den_zero (q : ℚ) (p : ℕ) [hp : Fact p.Prime] :
    padicValNat p q.den = 0 ∨ padicValInt p q.num = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hd, hm⟩ := hcon
  have hdvd_den : p ∣ q.den := dvd_of_one_le_padicValNat (by omega)
  have hm' : padicValNat p q.num.natAbs ≠ 0 := hm
  have hdvd_num : p ∣ q.num.natAbs := dvd_of_one_le_padicValNat (by omega)
  have hco : Nat.gcd q.num.natAbs q.den = 1 := q.reduced
  have : p ∣ 1 := hco ▸ Nat.dvd_gcd hdvd_num hdvd_den
  exact Nat.Prime.one_lt hp.out |>.ne' (Nat.dvd_one.mp this)

/-- An even Bernoulli number with index `≥ 4` is nonzero. -/
theorem bernoulli_even_ne_zero (k : ℕ) (hk4 : 4 ≤ k) (hke : Even k) : bernoulli k ≠ 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (bernoulli_padicVal_crit 2 k hk4 hke).1 (one_dvd k)
  intro h0
  rw [h0, padicValRat.zero] at h
  norm_num at h

/-- von Staudt–Clausen facts about the numerator and denominator of an even Bernoulli number. -/
theorem bernoulli_num_den_padic (k : ℕ) (hk4 : 4 ≤ k) (hke : Even k) (p : ℕ) [Fact p.Prime] :
    ((p - 1) ∣ k → padicValInt p (bernoulli k).num = 0 ∧ padicValNat p (bernoulli k).den = 1) ∧
    (¬ (p - 1) ∣ k → padicValNat p (bernoulli k).den = 0) := by
  have hdef : padicValRat p (bernoulli k)
      = (padicValInt p (bernoulli k).num : ℤ) - (padicValNat p (bernoulli k).den : ℤ) :=
    padicValRat_def p _
  have hcop := padic_num_or_den_zero (bernoulli k) p
  have hcrit := bernoulli_padicVal_crit p k hk4 hke
  refine ⟨fun hdvd => ?_, fun hndvd => ?_⟩
  · have h := hcrit.1 hdvd
    rw [hdef] at h
    rcases hcop with hc | hc <;> omega
  · have h := hcrit.2 hndvd
    rw [hdef] at h
    rcases hcop with hc | hc <;> omega

/-- The core per-prime equivalence for `F_n` (odd composite case, `n-1` even `≥ 4`). -/
theorem Fn_val_iff (n : ℕ) (hn1 : 1 ≤ n) (hk4 : 4 ≤ n - 1) (hke : Even (n - 1))
    (p : ℕ) [hp : Fact p.Prime] :
    (-1 ≤ padicValRat p (((bernoulli (n - 1)).num : ℚ) / (n : ℚ)
        + ((bernoulli (n - 1)).den : ℚ) / ((n : ℚ) * (n : ℚ))))
    ↔ (padicValNat p n ≤ 1 ∧ (p ∣ n → (p - 1) ∣ (n - 1))) := by
  set B := bernoulli (n - 1) with hB
  have hBne : B ≠ 0 := bernoulli_even_ne_zero (n - 1) hk4 hke
  have hnum_ne : (B.num : ℚ) ≠ 0 := by exact_mod_cast Rat.num_ne_zero.mpr hBne
  have hden_ne : (B.den : ℚ) ≠ 0 := by exact_mod_cast B.den_nz
  have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  set t1 : ℚ := (B.num : ℚ) / (n : ℚ) with ht1
  set t2 : ℚ := (B.den : ℚ) / ((n : ℚ) * (n : ℚ)) with ht2
  have ht1ne : t1 ≠ 0 := div_ne_zero hnum_ne hn_ne
  have ht2ne : t2 ≠ 0 := div_ne_zero hden_ne (mul_ne_zero hn_ne hn_ne)
  have hv1 : padicValRat p t1 = (padicValInt p B.num : ℤ) - (padicValNat p n : ℤ) := by
    rw [ht1, padicValRat.div hnum_ne hn_ne, padicValRat.of_int, padicValRat.of_nat]
  have hv2 : padicValRat p t2 = (padicValNat p B.den : ℤ) - 2 * (padicValNat p n : ℤ) := by
    rw [ht2, padicValRat.div hden_ne (mul_ne_zero hn_ne hn_ne),
        padicValRat.mul hn_ne hn_ne, padicValRat.of_nat, padicValRat.of_nat]; ring
  have hbnd := bernoulli_num_den_padic (n - 1) hk4 hke p
  rw [← hB] at hbnd
  have hadd_ne : ∀ a b : ℚ, a ≠ 0 → b ≠ 0 → padicValRat p a ≠ padicValRat p b → a + b ≠ 0 := by
    intro a b ha hb hne hab
    exact hne (by rw [eq_neg_of_add_eq_zero_left hab, padicValRat.neg])
  have combine : (-1 ≤ padicValRat p t1) → (-1 ≤ padicValRat p t2) →
      -1 ≤ padicValRat p (t1 + t2) := by
    intro h1 h2
    by_cases h0 : t1 + t2 = 0
    · rw [h0, padicValRat.zero]; norm_num
    · exact le_trans (le_min h1 h2) (padicValRat.min_le_padicValRat_add h0)
  by_cases hpn : p ∣ n
  · have hw1 : 1 ≤ padicValNat p n := one_le_padicValNat_of_dvd (by omega) hpn
    by_cases hdk : (p - 1) ∣ (n - 1)
    · obtain ⟨hdN0, hdD1⟩ := hbnd.1 hdk
      by_cases hw : padicValNat p n = 1
      · -- both true
        constructor
        · intro _; exact ⟨by omega, fun _ => hdk⟩
        · intro _; exact combine (by omega) (by omega)
      · -- w ≥ 2, both false
        have hlt : padicValRat p t2 < padicValRat p t1 := by omega
        have hsumne : t2 + t1 ≠ 0 := hadd_ne t2 t1 ht2ne ht1ne (ne_of_lt hlt)
        have hexact : padicValRat p (t1 + t2) = padicValRat p t2 := by
          rw [add_comm]; exact padicValRat.add_eq_of_lt hsumne ht2ne ht1ne hlt
        rw [hexact]
        constructor
        · intro hle; exfalso; omega
        · rintro ⟨hle, _⟩; exfalso; omega
    · -- ¬(p-1)|k, both false
      have hdD0 := hbnd.2 hdk
      have hlt : padicValRat p t2 < padicValRat p t1 := by omega
      have hsumne : t2 + t1 ≠ 0 := hadd_ne t2 t1 ht2ne ht1ne (ne_of_lt hlt)
      have hexact : padicValRat p (t1 + t2) = padicValRat p t2 := by
        rw [add_comm]; exact padicValRat.add_eq_of_lt hsumne ht2ne ht1ne hlt
      rw [hexact]
      constructor
      · intro hle; exfalso; omega
      · rintro ⟨_, himp⟩; exact absurd (himp hpn) hdk
  · -- p ∤ n, both true
    have hw0 : padicValNat p n = 0 := padicValNat.eq_zero_of_not_dvd hpn
    have hdNnn : 0 ≤ (padicValInt p B.num : ℤ) := Int.natCast_nonneg _
    have hdDnn : 0 ≤ (padicValNat p B.den : ℤ) := Int.natCast_nonneg _
    constructor
    · intro _; exact ⟨by omega, fun h => absurd h hpn⟩
    · intro _; exact combine (by omega) (by omega)

noncomputable def a (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    let n_q : ℚ := n
    let B_nm1 : ℚ := bernoulli (n - 1)
    let F_n : ℚ := (B_nm1.num : ℚ) / n_q + (B_nm1.den : ℚ) / (n_q * n_q)
    F_n.den

def is_carmichael_number (n : ℕ) : Prop :=
  (¬ Nat.Prime n ∧ n > 1) ∧ (∀ b : ℕ, Nat.gcd b n = 1 → b ^ (n - 1) ≡ 1 [MOD n])

def is_composite (n : ℕ) : Prop := ¬ Nat.Prime n ∧ n > 1

theorem a_eq (n : ℕ) (hn : n ≠ 0) :
    a n = (((bernoulli (n - 1)).num : ℚ) / (n : ℚ)
        + ((bernoulli (n - 1)).den : ℚ) / ((n : ℚ) * (n : ℚ))).den := by
  rw [a, dif_neg hn]

theorem main_reduction_odd (n : ℕ) (hcomp : is_composite n) (hodd : Odd n) :
    Squarefree (a n) ↔ (∀ b : ℕ, Nat.gcd b n = 1 → b ^ (n - 1) ≡ 1 [MOD n]) := by
  obtain ⟨hnp, hn1⟩ := hcomp
  obtain ⟨k, hk⟩ := hodd
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · exfalso
      interval_cases k
      · omega
      · exact hnp (by rw [hk]; norm_num)
    · exact h
  have hne0 : n ≠ 0 := by omega
  have hk4 : 4 ≤ n - 1 := by omega
  have hke : Even (n - 1) := ⟨k, by omega⟩
  set E : ℚ := ((bernoulli (n - 1)).num : ℚ) / (n : ℚ)
      + ((bernoulli (n - 1)).den : ℚ) / ((n : ℚ) * (n : ℚ)) with hE
  rw [a_eq n hne0, ← hE, squarefree_iff_padic _ (Rat.den_nz _),
    fermat_iff_carmichael_dvd n (by omega), korselt n (by omega)]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [squarefree_iff_padic n hne0]
      intro p pp
      haveI : Fact p.Prime := ⟨pp⟩
      exact ((Fn_val_iff n (by omega) hk4 hke p).mp ((den_padic_le_one E p).mp (h p pp))).1
    · intro p pp hpn
      haveI : Fact p.Prime := ⟨pp⟩
      exact ((Fn_val_iff n (by omega) hk4 hke p).mp ((den_padic_le_one E p).mp (h p pp))).2 hpn
  · rintro ⟨hsq, h2⟩ p pp
    haveI : Fact p.Prime := ⟨pp⟩
    rw [den_padic_le_one E p, Fn_val_iff n (by omega) hk4 hke p]
    refine ⟨?_, ?_⟩
    · rw [squarefree_iff_padic n hne0] at hsq; exact hsq p pp
    · intro hpn; exact h2 p pp hpn

theorem main_reduction_even (n : ℕ) (hcomp : is_composite n) (heven : Even n) :
    Squarefree (a n) ↔ (∀ b : ℕ, Nat.gcd b n = 1 → b ^ (n - 1) ≡ 1 [MOD n]) := by
  obtain ⟨hnp, hn1⟩ := hcomp
  obtain ⟨j, hj⟩ := heven
  have hj2 : 2 ≤ j := by
    rcases Nat.lt_or_ge j 2 with h | h
    · exfalso; interval_cases j
      · omega
      · exact hnp (by rw [hj]; norm_num)
    · exact h
  have hn4 : 4 ≤ n := by omega
  have hne0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨hne0⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- B = bernoulli (n-1) = 0
  have hodd : Odd (n - 1) := ⟨j - 1, by omega⟩
  have hB0 : bernoulli (n - 1) = 0 := bernoulli_eq_zero_of_odd hodd (by omega)
  set E : ℚ := ((bernoulli (n - 1)).num : ℚ) / (n : ℚ)
      + ((bernoulli (n - 1)).den : ℚ) / ((n : ℚ) * (n : ℚ)) with hE
  have hn_ne : (n : ℚ) ≠ 0 := by exact_mod_cast hne0
  have hEval : E = 1 / ((n : ℚ) * (n : ℚ)) := by
    rw [hE, hB0]; simp
  have hval2 : padicValRat 2 E ≤ -2 := by
    rw [hEval, one_div, padicValRat.inv, padicValRat.mul hn_ne hn_ne]
    simp only [padicValRat.of_nat]
    have h2n : 1 ≤ padicValNat 2 n := one_le_padicValNat_of_dvd hne0 (by rw [hj]; exact ⟨j, by ring⟩)
    omega
  have hnotsq : ¬ Squarefree (a n) := by
    rw [a_eq n hne0, ← hE, squarefree_iff_padic _ (Rat.den_nz _)]
    intro hall
    have h2 := hall 2 Nat.prime_two
    rw [den_padic_le_one E 2] at h2
    omega
  have hnotf : ¬ (∀ b : ℕ, Nat.gcd b n = 1 → b ^ (n - 1) ≡ 1 [MOD n]) := by
    intro hf
    have hco : Nat.gcd (n - 1) n = 1 := by
      have e1 : Nat.gcd (n-1) n = Nat.gcd (n-1) (n - (n-1)) := (Nat.gcd_sub_self_right (by omega)).symm
      have e2 : n - (n-1) = 1 := by omega
      rw [e1, e2, Nat.gcd_one_right]
    have hmod := hf (n - 1) hco
    rw [← ZMod.natCast_eq_natCast_iff] at hmod
    push_cast at hmod
    have hcast : ((n - 1 : ℕ) : ZMod n) = -1 := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self]; simp
    rw [hcast, hodd.neg_one_pow] at hmod
    -- hmod : (-1 : ZMod n) = 1
    have h20 : ((2 : ℕ) : ZMod n) = 0 := by push_cast; linear_combination -hmod
    rw [ZMod.natCast_eq_zero_iff] at h20
    have : n ≤ 2 := Nat.le_of_dvd (by norm_num) h20
    omega
  exact iff_of_false hnotsq hnotf

theorem A309132_conjecture_carmichael : ∀ (n : ℕ),
  (is_composite n ∧ Squarefree (a n)) ↔ is_carmichael_number n := by
  intro n
  constructor
  · rintro ⟨hc, hsq⟩
    refine ⟨hc, ?_⟩
    rcases Nat.even_or_odd n with he | ho
    · exact (main_reduction_even n hc he).mp hsq
    · exact (main_reduction_odd n hc ho).mp hsq
  · rintro ⟨hc, hf⟩
    refine ⟨hc, ?_⟩
    rcases Nat.even_or_odd n with he | ho
    · exact (main_reduction_even n hc he).mpr hf
    · exact (main_reduction_odd n hc ho).mpr hf
