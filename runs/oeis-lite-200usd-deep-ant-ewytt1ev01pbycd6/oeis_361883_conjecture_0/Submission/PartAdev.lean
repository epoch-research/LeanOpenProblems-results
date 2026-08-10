import FormalConjectures.Util.ProblemImports

open Nat Finset

/-! ## Wolstenholme H2 : sum of squares of units is zero -/

/-- Wolstenholme H2: the sum of squares of units in `ZMod n` is zero,
provided `n` is coprime to `2` and `3`. -/
lemma sum_units_sq_zero (n : ℕ) [NeZero n] (h2 : Nat.Coprime 2 n) (h3 : Nat.Coprime 3 n) :
    ∑ x : (ZMod n)ˣ, ((x : ZMod n) ^ 2) = 0 := by
  set R := ZMod n
  set Sig := ∑ x : Rˣ, ((x : R) ^ 2) with hSig
  set u : Rˣ := ZMod.unitOfCoprime 2 h2 with hu
  have hval : (u : R) = (2 : R) := by rw [hu]; exact ZMod.coe_unitOfCoprime 2 h2
  have hperm : ∑ x : Rˣ, ((↑(u * x) : R) ^ 2) = Sig := by
    rw [hSig]; exact Equiv.sum_comp (Equiv.mulLeft u) (fun x : Rˣ => ((x : R) ^ 2))
  have hexp : ∑ x : Rˣ, ((↑(u * x) : R) ^ 2) = (↑u : R) ^ 2 * Sig := by
    rw [hSig, Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; rw [Units.val_mul, mul_pow]
  have hkey : ((↑u : R) ^ 2 - 1) * Sig = 0 := by
    have h : (↑u : R) ^ 2 * Sig = Sig := by rw [← hexp, hperm]
    linear_combination h
  have h3eq : (↑u : R) ^ 2 - 1 = 3 := by rw [hval]; ring
  rw [h3eq] at hkey
  have h3unit : IsUnit (3 : R) := ⟨ZMod.unitOfCoprime 3 h3, by rw [ZMod.coe_unitOfCoprime]; norm_num⟩
  obtain ⟨v, hv⟩ := h3unit
  calc Sig = (↑v⁻¹ : R) * ((3 : R) * Sig) := by rw [← mul_assoc, ← hv]; simp
    _ = 0 := by rw [hkey]; ring

/-- For a prime `p ≥ 5`, the sum of squares of units of `ZMod (p^s)` is zero. -/
lemma units_sq_sum_ppow (p s : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : (ZMod (p ^ s))ˣ, ((x : ZMod (p ^ s)) ^ 2) = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hp2 : ¬ (2 ∣ p) := by
    intro h; have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h; omega
  have hp3 : ¬ (3 ∣ p) := by
    intro h; have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h; omega
  have h2 : Nat.Coprime 2 (p ^ s) := (Nat.prime_two.coprime_iff_not_dvd.mpr hp2).pow_right s
  have h3 : Nat.Coprime 3 (p ^ s) := (Nat.prime_three.coprime_iff_not_dvd.mpr hp3).pow_right s
  exact sum_units_sq_zero (p ^ s) h2 h3

/-- For a prime `p ≥ 5`, the sum of *inverse* squares of units of `ZMod (p^s)` is zero. -/
lemma units_inv_sq_sum_ppow (p s : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : (ZMod (p ^ s))ˣ, ((x : ZMod (p ^ s))⁻¹ ^ 2) = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hbase := units_sq_sum_ppow p s hp5
  calc ∑ x : (ZMod (p ^ s))ˣ, ((x : ZMod (p ^ s))⁻¹ ^ 2)
      = ∑ x : (ZMod (p ^ s))ˣ, (((x⁻¹ : (ZMod (p ^ s))ˣ) : ZMod (p ^ s)) ^ 2) := by
        apply Finset.sum_congr rfl; intro x _; rw [ZMod.inv_coe_unit]
    _ = ∑ x : (ZMod (p ^ s))ˣ, ((x : ZMod (p ^ s)) ^ 2) :=
        Equiv.sum_comp (Equiv.inv (ZMod (p ^ s))ˣ)
          (fun y : (ZMod (p ^ s))ˣ => ((y : ZMod (p ^ s)) ^ 2))
    _ = 0 := hbase

/- ## Elementary binomial / product identities -/

/-- Symmetry of the binomial coefficient in the index form appearing in the problem. -/
lemma choose_symm_index (M k : ℕ) (hM : 1 ≤ M) :
    Nat.choose (M + k - 1) (M - 1) = Nat.choose (M + k - 1) k := by
  have h : M - 1 ≤ M + k - 1 := by omega
  have hh := Nat.choose_symm h
  have e : (M + k - 1) - (M - 1) = k := by omega
  rw [e] at hh
  exact hh.symm

/-- Division-free product identity: `∏_{i<k}(M+i) = k! · C(M+k-1, k)` for `M ≥ 1`. -/
lemma prod_range_add_eq (M k : ℕ) (hM : 1 ≤ M) :
    (∏ i ∈ Finset.range k, (M + i)) = k ! * Nat.choose (M + k - 1) k := by
  have h1 := Nat.ascFactorial_eq_prod_range M k
  have h2 := Nat.ascFactorial_eq_factorial_mul_choose (M - 1) k
  have e1 : M - 1 + 1 = M := by omega
  rw [e1] at h2
  have e2 : M - 1 + k = M + k - 1 := by omega
  rw [e2] at h2
  rw [← h1, h2]

/- ## p-adic bridges -/

/-- `toZModPow s x = 0` iff `p^s ∣ x` in `ℤ_[p]`. -/
lemma toZModPow_eq_zero_iff_dvd (p : ℕ) [Fact p.Prime] (s : ℕ) (x : ℤ_[p]) :
    PadicInt.toZModPow s x = 0 ↔ (p : ℤ_[p]) ^ s ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

/-- Bridge: `p^s ∣ m` in `ℕ` iff `p^s ∣ (m : ℤ_[p])`. -/
lemma nat_dvd_iff_padic_dvd (p : ℕ) [Fact p.Prime] (s m : ℕ) :
    p ^ s ∣ m ↔ (p : ℤ_[p]) ^ s ∣ (m : ℤ_[p]) := by
  haveI : NeZero (p ^ s) := ⟨pow_ne_zero _ (Nat.Prime.ne_zero Fact.out)⟩
  rw [← toZModPow_eq_zero_iff_dvd, map_natCast]
  rw [ZMod.natCast_eq_zero_iff]

/-- `toZModPow` sends `Ring.inverse` of a unit to `Ring.inverse` of its image. -/
lemma toZModPow_inverse (p : ℕ) [Fact p.Prime] (s : ℕ) {x : ℤ_[p]} (hx : IsUnit x) :
    PadicInt.toZModPow s (Ring.inverse x) = Ring.inverse (PadicInt.toZModPow s x) := by
  have h1 : Ring.inverse x * x = 1 := Ring.inverse_mul_cancel x hx
  have hfx : IsUnit (PadicInt.toZModPow s x) := hx.map _
  have h2 : PadicInt.toZModPow s x * Ring.inverse (PadicInt.toZModPow s x) = 1 :=
    Ring.mul_inverse_cancel _ hfx
  calc PadicInt.toZModPow s (Ring.inverse x)
      = PadicInt.toZModPow s (Ring.inverse x)
          * (PadicInt.toZModPow s x * Ring.inverse (PadicInt.toZModPow s x)) := by rw [h2, mul_one]
    _ = PadicInt.toZModPow s (Ring.inverse x * x) * Ring.inverse (PadicInt.toZModPow s x) := by
        rw [map_mul]; ring
    _ = Ring.inverse (PadicInt.toZModPow s x) := by rw [h1, map_one, one_mul]

/-- On a unit of `ZMod m`, `Ring.inverse` agrees with the `ZMod` inverse. -/
lemma ring_inverse_eq_inv_zmod (m : ℕ) {a : ZMod m} (hu : IsUnit a) :
    Ring.inverse a = a⁻¹ := by
  obtain ⟨u, rfl⟩ := hu
  rw [Ring.inverse_unit]; exact (ZMod.inv_coe_unit u).symm

/-- A natural number not divisible by `p` gives a unit in `ℤ_[p]`. -/
lemma isUnit_nat_of_not_dvd (p : ℕ) [Fact p.Prime] {n : ℕ} (h : ¬ p ∣ n) :
    IsUnit (n : ℤ_[p]) := by
  rw [PadicInt.isUnit_iff]
  have hle : ‖(n : ℤ_[p])‖ ≤ 1 := PadicInt.norm_le_one _
  rcases lt_or_eq_of_le hle with hlt | heq
  · exfalso
    have hcast : (n : ℤ_[p]) = ((n : ℤ) : ℤ_[p]) := by push_cast; ring
    rw [hcast, PadicInt.norm_int_lt_one_iff_dvd] at hlt
    exact h (by exact_mod_cast hlt)
  · exact heq

/- ## H2 block bridge -/

/-- If `f` is periodic with period `m ≥ 1`, its sum over any block of `m` consecutive
integers equals its sum over `range m`. -/
lemma sum_Ico_periodic {N : Type*} [AddCommMonoid N] (f : ℕ → N) (m : ℕ) (hm : 1 ≤ m)
    (hper : ∀ n, f (n + m) = f n) (a : ℕ) :
    ∑ n ∈ Finset.Ico a (a + m), f n = ∑ n ∈ Finset.range m, f n := by
  induction a with
  | zero => rw [Nat.zero_add, Finset.range_eq_Ico]
  | succ k ih =>
    have h1 : ∑ n ∈ Finset.Ico k (k + m), f n = f k + ∑ n ∈ Finset.Ico (k + 1) (k + m), f n :=
      Finset.sum_eq_sum_Ico_succ_bot (by omega) f
    have h2 : ∑ n ∈ Finset.Ico (k + 1) (k + 1 + m), f n
            = ∑ n ∈ Finset.Ico (k + 1) (k + m), f n + f (k + m) := by
      have he : k + 1 + m = (k + m) + 1 := by omega
      rw [he]; exact Finset.sum_Ico_succ_top (by omega) f
    calc ∑ n ∈ Finset.Ico (k + 1) (k + 1 + m), f n
        = ∑ n ∈ Finset.Ico (k + 1) (k + m), f n + f (k + m) := h2
      _ = ∑ n ∈ Finset.Ico (k + 1) (k + m), f n + f k := by rw [hper k]
      _ = ∑ n ∈ Finset.Ico k (k + m), f n := by rw [h1]; abel
      _ = ∑ n ∈ Finset.range m, f n := ih

/-- H2 block bridge (range form): the inverse–square sum over a `p^s`-block based at `0`,
restricted to entries coprime to `p`, vanishes in `ZMod (p^s)`. -/
lemma block_range_inv_sq (p s : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hs : 1 ≤ s) :
    ∑ n ∈ (Finset.range (p ^ s)).filter (fun n => ¬ p ∣ n),
      ((n : ZMod (p ^ s))⁻¹) ^ 2 = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set m := p ^ s with hm
  classical
  set toUnit : ℕ → (ZMod m)ˣ := fun n => if h : IsUnit (n : ZMod m) then h.unit else 1 with htu
  rw [← units_inv_sq_sum_ppow p s hp5]
  symm
  apply Finset.sum_nbij' (fun x : (ZMod m)ˣ => (x : ZMod m).val) toUnit
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt _, ?_⟩
    have hcop : Nat.Coprime (x : ZMod m).val m := ZMod.val_coe_unit_coprime x
    intro hpv
    have hpm : p ∣ m := dvd_pow_self p (by omega)
    have hg : p ∣ Nat.gcd (x : ZMod m).val m := Nat.dvd_gcd hpv hpm
    rw [hcop] at hg
    have := Nat.eq_one_of_dvd_one hg
    omega
  · intro n _; exact Finset.mem_univ _
  · intro x _
    have hval : (((x : ZMod m).val : ℕ) : ZMod m) = (x : ZMod m) := ZMod.natCast_zmod_val _
    have hu : IsUnit (((x : ZMod m).val : ℕ) : ZMod m) := by rw [hval]; exact x.isUnit
    simp only [htu, dif_pos hu]
    apply Units.ext
    rw [IsUnit.unit_spec, hval]
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnlt, hpn⟩ := hn
    have hu : IsUnit ((n : ℕ) : ZMod m) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (((hp.coprime_iff_not_dvd).mpr hpn).symm.pow_right s)
    simp only [htu, dif_pos hu]
    rw [IsUnit.unit_spec]
    exact ZMod.val_cast_of_lt hnlt
  · intro x _
    rw [ZMod.natCast_zmod_val]

/-- H2 block bridge (`Ico` form): the inverse–square sum over any `p^s`-block based at `a`,
restricted to entries coprime to `p`, vanishes in `ZMod (p^s)`. -/
lemma block_Ico_inv_sq (p s a : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hs : 1 ≤ s) :
    ∑ n ∈ (Finset.Ico a (a + p ^ s)).filter (fun n => ¬ p ∣ n),
      ((n : ZMod (p ^ s))⁻¹) ^ 2 = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ s) := ⟨pow_ne_zero _ hp.ne_zero⟩
  set m := p ^ s with hm
  have hpm : p ∣ m := dvd_pow_self p (by omega)
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
  set F : ℕ → ZMod m := fun n => if ¬ p ∣ n then ((n : ZMod m)⁻¹) ^ 2 else 0 with hF
  have hFper : ∀ n, F (n + m) = F n := by
    intro n
    have hdvd : (p ∣ (n + m)) ↔ (p ∣ n) := by
      rw [Nat.add_comm]; exact Nat.dvd_add_right hpm
    have hcast : ((n + m : ℕ) : ZMod m) = (n : ZMod m) := by
      rw [Nat.cast_add, ZMod.natCast_self, add_zero]
    simp only [hF, hcast, hdvd]
  rw [Finset.sum_filter]
  have hstep : (∑ n ∈ Finset.Ico a (a + m), F n) = ∑ n ∈ Finset.range m, F n :=
    sum_Ico_periodic F m hm1 hFper a
  calc ∑ n ∈ Finset.Ico a (a + m), (if ¬ p ∣ n then ((n : ZMod m)⁻¹) ^ 2 else 0)
      = ∑ n ∈ Finset.Ico a (a + m), F n := by rw [hF]
    _ = ∑ n ∈ Finset.range m, F n := hstep
    _ = ∑ n ∈ (Finset.range m).filter (fun n => ¬ p ∣ n), ((n : ZMod m)⁻¹) ^ 2 := by
        rw [Finset.sum_filter]
    _ = 0 := block_range_inv_sq p s hp5 hs

/-- H2 block bridge in `ℤ_[p]`: the `ℤ_[p]`-inverse–square sum over any `p^s`-block based at
`a`, restricted to entries coprime to `p`, is `≡ 0 mod p^s` (its image under `toZModPow s`
vanishes). -/
lemma block_Ico_padic (p s a : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hs : 1 ≤ s) :
    PadicInt.toZModPow s
      (∑ n ∈ (Finset.Ico a (a + p ^ s)).filter (fun n => ¬ p ∣ n),
        (Ring.inverse (n : ℤ_[p])) ^ 2) = 0 := by
  rw [map_sum]
  have hcongr : ∀ n ∈ (Finset.Ico a (a + p ^ s)).filter (fun n => ¬ p ∣ n),
      PadicInt.toZModPow s ((Ring.inverse (n : ℤ_[p])) ^ 2)
        = ((n : ZMod (p ^ s))⁻¹) ^ 2 := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    have hunit : IsUnit (n : ℤ_[p]) := isUnit_nat_of_not_dvd p hn.2
    have huz : IsUnit ((n : ℕ) : ZMod (p ^ s)) := by
      rw [ZMod.isUnit_iff_coprime]
      exact (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr hn.2).symm.pow_right s
    rw [map_pow, toZModPow_inverse p s hunit, map_natCast, ring_inverse_eq_inv_zmod _ huz]
  rw [Finset.sum_congr rfl hcongr]
  exact block_Ico_inv_sq p s a hp5 hs

/- ## Kummer / Lucas : the relevant binomial coefficients are units -/

/-- Lucas/Kummer no-carry lemma: adding `l < p^r` to `c·p^r` produces no carries in base `p`,
hence `p ∤ C(c·p^r + l, l)`. -/
lemma not_dvd_choose_ppow_add (p : ℕ) [Fact p.Prime] (c r l : ℕ) (hl : l < p ^ r) :
    ¬ p ∣ Nat.choose (c * p ^ r + l) l := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  induction r generalizing c l with
  | zero =>
    have hl0 : l = 0 := Nat.lt_one_iff.mp (by simpa using hl)
    subst hl0
    simpa using hp.not_dvd_one
  | succ r ih =>
    intro hdvd
    -- key arithmetic rewrites
    have hn : c * p ^ (r + 1) + l = l + c * p ^ r * p := by ring
    have hnmod : (c * p ^ (r + 1) + l) % p = l % p := by
      rw [hn, Nat.add_mul_mod_self_right]
    have hndiv : (c * p ^ (r + 1) + l) / p = l / p + c * p ^ r := by
      rw [hn, Nat.add_mul_div_right _ _ hp0]
    have hldiv : l / p < p ^ r := by
      rw [Nat.div_lt_iff_lt_mul hp0]
      simpa [pow_succ] using hl
    have hih : ¬ p ∣ Nat.choose (c * p ^ r + l / p) (l / p) := ih c (l / p) hldiv
    -- Lucas one-step
    have hmod := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := p) (n := c * p ^ (r + 1) + l) (k := l)
    rw [hnmod, hndiv] at hmod
    have hself : Nat.choose (l % p) (l % p) = 1 := Nat.choose_self _
    rw [hself, one_mul] at hmod
    -- from p ∣ choose n l and the congruence, deduce p ∣ choose (n/p) (l/p)
    have h0 : Nat.choose (c * p ^ (r + 1) + l) l ≡ 0 [MOD p] :=
      (Nat.modEq_zero_iff_dvd).mpr hdvd
    have hdvd2 : p ∣ Nat.choose (l / p + c * p ^ r) (l / p) :=
      (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans h0)
    exact hih (by rwa [Nat.add_comm (c * p ^ r) (l / p)])

/-- The binomial coefficient `C(c·p^r + l, l)` is a unit in `ℤ_[p]` when `l < p^r`. -/
lemma isUnit_choose_ppow_add (p : ℕ) [Fact p.Prime] (c r l : ℕ) (hl : l < p ^ r) :
    IsUnit ((Nat.choose (c * p ^ r + l) l : ℤ_[p])) :=
  isUnit_nat_of_not_dvd p (not_dvd_choose_ppow_add p c r l hl)

/- ## Core congruence : definitions -/

/-- `Wblk p s l`: the inverse–square sum over the `p^s`-block based at `p^s·l`, restricted to
entries coprime to `p`. This is `W_s(l)` from the task. -/
noncomputable def Wblk (p : ℕ) [Fact p.Prime] (s l : ℕ) : ℤ_[p] :=
  ∑ n ∈ (Finset.Ico (p ^ s * l) (p ^ s * l + p ^ s)).filter (fun n => ¬ p ∣ n),
    (Ring.inverse (n : ℤ_[p])) ^ 2

/-- `Qstar p c w r l = C((c+w)·p^r + l, l) / C(c·p^r + l, l)` in `ℤ_[p]` (a unit for `l < p^r`).
This is `Q*_{r,l}` from the task. -/
noncomputable def Qstar (p : ℕ) [Fact p.Prime] (c w r l : ℕ) : ℤ_[p] :=
  (Nat.choose ((c + w) * p ^ r + l) l : ℤ_[p]) *
    Ring.inverse (Nat.choose (c * p ^ r + l) l : ℤ_[p])

/-- `Phi p c w r s = ∑_{l < p^r} (Q*_{r,l})^3 · W_s(l)`. This is `Φ_r^{(s)}` from the task. -/
noncomputable def Phi (p : ℕ) [Fact p.Prime] (c w r s : ℕ) : ℤ_[p] :=
  ∑ l ∈ Finset.range (p ^ r), (Qstar p c w r l) ^ 3 * Wblk p s l

/- ## Core congruence : elementary support lemmas -/

/-- `v_p(W_s(l)) ≥ s`: the block sum is divisible by `p^s` (from `block_Ico_padic`). -/
lemma dvd_Wblk (p s l : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hs : 1 ≤ s) :
    (p : ℤ_[p]) ^ s ∣ Wblk p s l := by
  rw [← toZModPow_eq_zero_iff_dvd]
  unfold Wblk
  exact block_Ico_padic p s (p ^ s * l) hp5 hs

/-- Reindexing `range (p*q)` as a double sum. -/
lemma sum_range_reindex {A : Type*} [AddCommMonoid A] (p q : ℕ) (g : ℕ → A) :
    ∑ l ∈ Finset.range (p * q), g l
      = ∑ μ ∈ Finset.range q, ∑ σ ∈ Finset.range p, g (p * μ + σ) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show p * (q + 1) = p * q + p from by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ]

/-- Merging `q` consecutive length-`d` blocks starting at `a` into one block of length `d*q`. -/
lemma sum_Ico_block_merge {A : Type*} [AddCommMonoid A] (a d q : ℕ) (h : ℕ → A) :
    ∑ σ ∈ Finset.range q, ∑ n ∈ Finset.Ico (a + d * σ) (a + d * σ + d), h n
      = ∑ n ∈ Finset.Ico a (a + d * q), h n := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, ih,
      Finset.sum_Ico_consecutive h (by omega) (by omega),
      show a + d * q + d = a + d * (q + 1) from by ring]

/-- The `p` sub-blocks `W_s(p·μ+σ)` (for `σ < p`) merge into a single `W_{s+1}(μ)`. -/
lemma Wblk_merge (p s μ : ℕ) [Fact p.Prime] :
    ∑ σ ∈ Finset.range p, Wblk p s (p * μ + σ) = Wblk p (s + 1) μ := by
  have hW : ∀ t l, Wblk p t l
      = ∑ n ∈ Finset.Ico (p ^ t * l) (p ^ t * l + p ^ t),
          (if ¬ p ∣ n then (Ring.inverse (n : ℤ_[p])) ^ 2 else 0) := by
    intro t l; unfold Wblk; rw [Finset.sum_filter]
  have hps : p ^ (s + 1) = p ^ s * p := pow_succ p s
  calc ∑ σ ∈ Finset.range p, Wblk p s (p * μ + σ)
      = ∑ σ ∈ Finset.range p, ∑ n ∈ Finset.Ico (p ^ s * p * μ + p ^ s * σ)
            (p ^ s * p * μ + p ^ s * σ + p ^ s),
            (if ¬ p ∣ n then (Ring.inverse (n : ℤ_[p])) ^ 2 else 0) := by
        apply Finset.sum_congr rfl; intro σ _
        rw [hW s (p * μ + σ), show p ^ s * (p * μ + σ) = p ^ s * p * μ + p ^ s * σ from by ring]
    _ = ∑ n ∈ Finset.Ico (p ^ s * p * μ) (p ^ s * p * μ + p ^ s * p),
            (if ¬ p ∣ n then (Ring.inverse (n : ℤ_[p])) ^ 2 else 0) :=
        sum_Ico_block_merge (p ^ s * p * μ) (p ^ s) p _
    _ = Wblk p (s + 1) μ := by rw [hW (s + 1) μ, hps]

/-- `Qstar` is a unit for `l < p^r` (both binomials are units by Kummer). -/
lemma isUnit_Qstar (p c w r l : ℕ) [Fact p.Prime] (hl : l < p ^ r) :
    IsUnit (Qstar p c w r l) := by
  unfold Qstar
  refine (isUnit_choose_ppow_add p (c + w) r l hl).mul ?_
  obtain ⟨u, hu⟩ := isUnit_choose_ppow_add p c r l hl
  rw [← hu, Ring.inverse_unit]
  exact u⁻¹.isUnit

/-- If `p^t ∣ a - b` then `p^t ∣ a^3 - b^3`. -/
lemma dvd_cube_sub_cube {p : ℕ} [Fact p.Prime] {t : ℕ} {a b : ℤ_[p]}
    (h : (p : ℤ_[p]) ^ t ∣ (a - b)) : (p : ℤ_[p]) ^ t ∣ (a ^ 3 - b ^ 3) := by
  have he : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
  rw [he]; exact h.mul_right _

/-- Natural-number **peel identity**: splitting the product `∏_{i=1}^l (a'p+i)` by whether `p ∣ i`,
the `p ∣ i` part telescopes to the lower binomial. -/
lemma peel_nat (p a' : ℕ) (hp0 : 0 < p) : ∀ l : ℕ,
    Nat.choose (a' * p + l) l * (∏ i ∈ Finset.Icc 1 l, (if p ∣ i then 1 else i))
      = Nat.choose (a' + l / p) (l / p)
        * (∏ i ∈ Finset.Icc 1 l, (if p ∣ i then 1 else a' * p + i)) := by
  intro l
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ l + 1),
        Finset.prod_Icc_succ_top (by omega : 1 ≤ l + 1)]
    by_cases hd : p ∣ (l + 1)
    · simp only [hd, if_true, mul_one]
      obtain ⟨m, hm⟩ := hd
      have hmpos : 1 ≤ m := by nlinarith [hp0]
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hpm : p * (m' + 1) = p * m' + p := by ring
      have hl : l = p * m' + (p - 1) := by omega
      have hdivl1 : (l + 1) / p = m' + 1 := by
        rw [hm, hpm, Nat.mul_add_div hp0, Nat.div_self hp0]
      have hdivl : l / p = m' := by
        rw [hl, Nat.mul_add_div hp0, Nat.div_eq_of_lt (by omega : p - 1 < p), Nat.add_zero]
      rw [hdivl1]
      set I := ∏ i ∈ Finset.Icc 1 l, (if p ∣ i then 1 else i) with hI
      set Q := ∏ i ∈ Finset.Icc 1 l, (if p ∣ i then 1 else a' * p + i) with hQ
      have R1 : Nat.choose (a' * p + (l + 1)) (l + 1) * (l + 1)
          = (a' * p + l + 1) * Nat.choose (a' * p + l) l := by
        have h := Nat.add_one_mul_choose_eq (a' * p + l) l
        rw [show a' * p + (l + 1) = a' * p + l + 1 from by ring]
        omega
      have R2 : Nat.choose (a' + (m' + 1)) (m' + 1) * (m' + 1)
          = (a' + (m' + 1)) * Nat.choose (a' + m') m' := by
        have h := Nat.add_one_mul_choose_eq (a' + m') m'
        rw [show a' + (m' + 1) = a' + m' + 1 from by ring]
        omega
      have ih' : Nat.choose (a' * p + l) l * I = Nat.choose (a' + m') m' * Q := by
        rw [hI, hQ, ih, hdivl]
      have hAP : a' * p + l + 1 = p * (a' + (m' + 1)) := by
        rw [show a' * p + l + 1 = a' * p + (l + 1) from by ring, hm]; ring
      have hcancel : Nat.choose (a' * p + (l + 1)) (l + 1) * I * (l + 1)
          = Nat.choose (a' + (m' + 1)) (m' + 1) * Q * (l + 1) := by
        calc Nat.choose (a' * p + (l + 1)) (l + 1) * I * (l + 1)
            = (Nat.choose (a' * p + (l + 1)) (l + 1) * (l + 1)) * I := by ring
          _ = ((a' * p + l + 1) * Nat.choose (a' * p + l) l) * I := by rw [R1]
          _ = (a' * p + l + 1) * (Nat.choose (a' * p + l) l * I) := by ring
          _ = (a' * p + l + 1) * (Nat.choose (a' + m') m' * Q) := by rw [ih']
          _ = (p * (a' + (m' + 1))) * (Nat.choose (a' + m') m' * Q) := by rw [hAP]
          _ = p * ((a' + (m' + 1)) * Nat.choose (a' + m') m') * Q := by ring
          _ = p * (Nat.choose (a' + (m' + 1)) (m' + 1) * (m' + 1)) * Q := by rw [R2]
          _ = Nat.choose (a' + (m' + 1)) (m' + 1) * Q * (p * (m' + 1)) := by ring
          _ = Nat.choose (a' + (m' + 1)) (m' + 1) * Q * (l + 1) := by rw [← hm]
      exact Nat.eq_of_mul_eq_mul_right (by omega) hcancel
    · simp only [hd, if_false]
      have hdivl : (l + 1) / p = l / p := by rw [Nat.succ_div]; simp [hd]
      rw [hdivl]
      have key : Nat.choose (a' * p + l + 1) (l + 1) * (l + 1)
          = (a' * p + l + 1) * Nat.choose (a' * p + l) l := by
        have h := Nat.add_one_mul_choose_eq (a' * p + l) l
        omega
      calc Nat.choose (a' * p + (l + 1)) (l + 1)
            * ((∏ i ∈ Finset.Icc 1 l, (if p ∣ i then 1 else i)) * (l + 1))
          = (Nat.choose (a' * p + l + 1) (l + 1) * (l + 1))
              * (∏ i ∈ Finset.Icc 1 l, (if p ∣ i then 1 else i)) := by
                rw [show a' * p + (l + 1) = a' * p + l + 1 from by ring]; ring
        _ = ((a' * p + l + 1) * Nat.choose (a' * p + l) l)
              * (∏ i ∈ Finset.Icc 1 l, (if p ∣ i then 1 else i)) := by rw [key]
        _ = (a' * p + l + 1)
              * (Nat.choose (a' * p + l) l
                  * (∏ i ∈ Finset.Icc 1 l, (if p ∣ i then 1 else i))) := by ring
        _ = (a' * p + l + 1)
              * (Nat.choose (a' + l / p) (l / p)
                  * (∏ i ∈ Finset.Icc 1 l, (if p ∣ i then 1 else a' * p + i))) := by rw [ih]
        _ = Nat.choose (a' + l / p) (l / p)
              * ((∏ i ∈ Finset.Icc 1 l, (if p ∣ i then 1 else a' * p + i)) * (a' * p + (l + 1))) := by
                rw [show a' * p + (l + 1) = a' * p + l + 1 from by ring]; ring

/-- Product congruence: if each factor difference is divisible by `d`, so is the product
difference. -/
lemma dvd_prod_sub_prod {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (d : R) (f g : ι → R) :
    (∀ i ∈ s, d ∣ (f i - g i)) → d ∣ (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | @insert a s ha ih =>
    intro h
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
        = f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [e]
    exact dvd_add (Dvd.dvd.mul_left (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))) _)
      (Dvd.dvd.mul_right (h a (Finset.mem_insert_self a s)) _)

/-- Abstract algebraic core of the peel congruence. -/
lemma peel_algebra {R : Type*} [CommRing R] (pt : R)
    (CT1 CT0 D1 D0 Iz QcwZ QcZ : R)
    (hCT0u : IsUnit CT0) (hD0u : IsUnit D0) (hIzu : IsUnit Iz)
    (e1 : CT1 * Iz = D1 * QcwZ) (e0 : CT0 * Iz = D0 * QcZ)
    (hQ : pt ∣ (QcwZ - QcZ)) :
    pt ∣ (CT1 * Ring.inverse CT0 - D1 * Ring.inverse D0) := by
  have hcc : CT0 * Ring.inverse CT0 = 1 := Ring.mul_inverse_cancel CT0 hCT0u
  have hdd : D0 * Ring.inverse D0 = 1 := Ring.mul_inverse_cancel D0 hD0u
  have hAeq : (CT1 * D0 - D1 * CT0) * Iz = (D1 * D0) * (QcwZ - QcZ) := by
    have h : (CT1 * D0 - D1 * CT0) * Iz = (CT1 * Iz) * D0 - D1 * (CT0 * Iz) := by ring
    rw [h, e1, e0]; ring
  have hAdvd : pt ∣ (CT1 * D0 - D1 * CT0) * Iz := by
    rw [hAeq]; exact (hQ.mul_left (D1 * D0))
  have hA : pt ∣ (CT1 * D0 - D1 * CT0) := by
    have hmul := hAdvd.mul_right (Ring.inverse Iz)
    rwa [mul_assoc, Ring.mul_inverse_cancel Iz hIzu, mul_one] at hmul
  have hBeq : CT1 * Ring.inverse CT0 - D1 * Ring.inverse D0
      = (CT1 * D0 - D1 * CT0) * (Ring.inverse CT0 * Ring.inverse D0) := by
    calc CT1 * Ring.inverse CT0 - D1 * Ring.inverse D0
        = CT1 * Ring.inverse CT0 * (D0 * Ring.inverse D0)
          - D1 * Ring.inverse D0 * (CT0 * Ring.inverse CT0) := by rw [hcc, hdd]; ring
      _ = (CT1 * D0 - D1 * CT0) * (Ring.inverse CT0 * Ring.inverse D0) := by ring
  rw [hBeq]
  exact hA.mul_right _

/-- **PEEL congruence** (isolated).  For `l < p^{r+1}`,
`Q*_{r+1,l} ≡ Q*_{r,⌊l/p⌋}  (mod p^{r+1})`.

NEEDS: the multiplicative "peel" identity
`C(c·p^{r+1}+l, l) = C(c·p^r + ⌊l/p⌋, ⌊l/p⌋) · ∏_{p∤i, 1≤i≤l} (c·p^{r+1}+i)/i`
in `ℤ_[p]` (both for `c` and for `c+w`), whence
`Q*_{r+1,l} = Q*_{r,⌊l/p⌋} · ∏_{p∤i,1≤i≤l} ((c+w)p^{r+1}+i)·(c·p^{r+1}+i)⁻¹`, and each factor is
`≡ 1 mod p^{r+1}` since the numerator and denominator differ by `w·p^{r+1}` and the denominator
is a unit (`p∤i`). -/
lemma Qstar_peel (p c w r l : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hl : l < p ^ (r + 1)) :
    (p : ℤ_[p]) ^ (r + 1) ∣ (Qstar p c w (r + 1) l - Qstar p c w r (l / p)) := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  have hlp : l / p < p ^ r := by rw [Nat.div_lt_iff_lt_mul hp0]; simpa [pow_succ] using hl
  have he1nat : (c + w) * p ^ (r + 1) = (c + w) * p ^ r * p := by rw [pow_succ]; ring
  have he0nat : c * p ^ (r + 1) = c * p ^ r * p := by rw [pow_succ]; ring
  have pn1 := peel_nat p ((c + w) * p ^ r) hp0 l
  have pn0 := peel_nat p (c * p ^ r) hp0 l
  set Inat : ℕ := ∏ i ∈ Finset.Icc 1 l, (if p ∣ i then 1 else i) with hInat
  set Qcw : ℕ := ∏ i ∈ Finset.Icc 1 l, (if p ∣ i then 1 else (c + w) * p ^ r * p + i) with hQcw
  set Qc : ℕ := ∏ i ∈ Finset.Icc 1 l, (if p ∣ i then 1 else c * p ^ r * p + i) with hQc
  have e1 : (Nat.choose ((c + w) * p ^ r * p + l) l : ℤ_[p]) * (Inat : ℤ_[p])
      = (Nat.choose ((c + w) * p ^ r + l / p) (l / p) : ℤ_[p]) * (Qcw : ℤ_[p]) := by
    exact_mod_cast pn1
  have e0 : (Nat.choose (c * p ^ r * p + l) l : ℤ_[p]) * (Inat : ℤ_[p])
      = (Nat.choose (c * p ^ r + l / p) (l / p) : ℤ_[p]) * (Qc : ℤ_[p]) := by
    exact_mod_cast pn0
  have hCT0u : IsUnit (Nat.choose (c * p ^ r * p + l) l : ℤ_[p]) := by
    have h := isUnit_choose_ppow_add p c (r + 1) l hl; rwa [he0nat] at h
  have hD0u : IsUnit (Nat.choose (c * p ^ r + l / p) (l / p) : ℤ_[p]) :=
    isUnit_choose_ppow_add p c r (l / p) hlp
  have hIzu : IsUnit (Inat : ℤ_[p]) := by
    apply isUnit_nat_of_not_dvd
    rw [hInat, ← hp.coprime_iff_not_dvd]
    apply Nat.Coprime.prod_right
    intro i _
    by_cases hd : p ∣ i
    · simp [hd]
    · simpa [hd] using (hp.coprime_iff_not_dvd).mpr hd
  have hQdiff : (p : ℤ_[p]) ^ (r + 1) ∣ ((Qcw : ℤ_[p]) - (Qc : ℤ_[p])) := by
    rw [hQcw, hQc, Nat.cast_prod, Nat.cast_prod]
    apply dvd_prod_sub_prod
    intro i _
    by_cases hd : p ∣ i
    · simp [hd]
    · simp only [hd, if_false]
      refine ⟨(w : ℤ_[p]), ?_⟩
      have hnat : (c + w) * p ^ r * p + i = (c * p ^ r * p + i) + w * p ^ (r + 1) := by
        rw [pow_succ]; ring
      rw [hnat]; push_cast; ring
  unfold Qstar
  rw [he1nat, he0nat]
  exact peel_algebra ((p : ℤ_[p]) ^ (r + 1))
    (Nat.choose ((c + w) * p ^ r * p + l) l : ℤ_[p])
    (Nat.choose (c * p ^ r * p + l) l : ℤ_[p])
    (Nat.choose ((c + w) * p ^ r + l / p) (l / p) : ℤ_[p])
    (Nat.choose (c * p ^ r + l / p) (l / p) : ℤ_[p])
    (Inat : ℤ_[p]) (Qcw : ℤ_[p]) (Qc : ℤ_[p])
    hCT0u hD0u hIzu e1 e0 hQdiff

/-- **Core congruence**: for all `r` and `s ≥ 1`, `p^{r+s} ∣ Φ_r^{(s)}`.
Proved by induction on `r` using `Qstar_peel`, `Wblk_merge` and `dvd_Wblk`. -/
lemma dvd_Phi (p c w : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∀ r s, 1 ≤ s → (p : ℤ_[p]) ^ (r + s) ∣ Phi p c w r s := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  intro r
  induction r with
  | zero =>
    intro s hs
    have hQ : Qstar p c w 0 0 = 1 := by
      simp [Qstar, Ring.inverse_one]
    have hPhi : Phi p c w 0 s = Wblk p s 0 := by
      unfold Phi
      rw [pow_zero, Finset.sum_range_one, hQ, one_pow, one_mul]
    rw [hPhi, zero_add]
    exact dvd_Wblk p s 0 hp5 hs
  | succ r ih =>
    intro s hs
    -- reindex the outer sum
    have hkey : Phi p c w (r + 1) s
        = ∑ μ ∈ Finset.range (p ^ r), ∑ σ ∈ Finset.range p,
            (Qstar p c w (r + 1) (p * μ + σ)) ^ 3 * Wblk p s (p * μ + σ) := by
      unfold Phi
      rw [pow_succ']
      exact sum_range_reindex p (p ^ r) (fun l => (Qstar p c w (r + 1) l) ^ 3 * Wblk p s l)
    -- rewrite `Φ_r^{(s+1)}` using the block merge
    have hPhi_r : Phi p c w r (s + 1)
        = ∑ μ ∈ Finset.range (p ^ r), ∑ σ ∈ Finset.range p,
            (Qstar p c w r μ) ^ 3 * Wblk p s (p * μ + σ) := by
      unfold Phi
      apply Finset.sum_congr rfl; intro μ _
      rw [← Wblk_merge p s μ, Finset.mul_sum]
    -- the difference is divisible by `p^{(r+1)+s}`
    have hdiff : (p : ℤ_[p]) ^ (r + 1 + s) ∣ (Phi p c w (r + 1) s - Phi p c w r (s + 1)) := by
      rw [hkey, hPhi_r, ← Finset.sum_sub_distrib]
      apply Finset.dvd_sum; intro μ hμ
      rw [← Finset.sum_sub_distrib]
      apply Finset.dvd_sum; intro σ hσ
      rw [← sub_mul, pow_add]
      apply mul_dvd_mul
      · apply dvd_cube_sub_cube
        have hσp : σ < p := Finset.mem_range.mp hσ
        have hμp : μ < p ^ r := Finset.mem_range.mp hμ
        have hlt : p * μ + σ < p ^ (r + 1) := by
          calc p * μ + σ < p * μ + p := by omega
            _ = p * (μ + 1) := by ring
            _ ≤ p * p ^ r := mul_le_mul_left' hμp p
            _ = p ^ (r + 1) := (pow_succ' p r).symm
        have hpeel := Qstar_peel p c w r (p * μ + σ) hp5 hlt
        have hdiv : (p * μ + σ) / p = μ := by
          rw [Nat.mul_add_div hp0, Nat.div_eq_of_lt hσp, Nat.add_zero]
        rwa [hdiv] at hpeel
      · exact dvd_Wblk p s (p * μ + σ) hp5 hs
    -- combine with the induction hypothesis on `s+1`
    have hih := ih (s + 1) (by omega)
    rw [show r + (s + 1) = r + 1 + s from by omega] at hih
    have key2 : Phi p c w (r + 1) s
        = (Phi p c w (r + 1) s - Phi p c w r (s + 1)) + Phi p c w r (s + 1) := by ring
    rw [show r + 1 + s = (r + 1) + s from rfl, key2]
    exact dvd_add hdiff hih

/- ## Part A : block factorization bridge -/

/-- **Key identity (KI)** in `ℕ`: `k · C(M+k-1, k) = M · C(M+k-1, k-1)`. -/
lemma key_ki (M k : ℕ) (hM : 1 ≤ M) (hk : 1 ≤ k) :
    k * Nat.choose (M + k - 1) k = M * Nat.choose (M + k - 1) (k - 1) := by
  have h := Nat.choose_succ_right_eq (M + k - 1) (k - 1)
  have e1 : (k - 1) + 1 = k := by omega
  have e2 : (M + k - 1) - (k - 1) = M := by omega
  rw [e1, e2] at h
  calc k * Nat.choose (M + k - 1) k = Nat.choose (M + k - 1) k * k := by ring
    _ = Nat.choose (M + k - 1) (k - 1) * M := h
    _ = M * Nat.choose (M + k - 1) (k - 1) := by ring

/-- The `p`-adic form of KI: for `p ∤ k`, `C(M+k-1,k) = k⁻¹ · M · C(M+k-1,k-1)` in `ℤ_[p]`. -/
lemma ki_padic (p M k : ℕ) [Fact p.Prime] (hM : 1 ≤ M) (hk : 1 ≤ k) (hpk : ¬ p ∣ k) :
    (Nat.choose (M + k - 1) k : ℤ_[p])
      = Ring.inverse (k : ℤ_[p]) * (M : ℤ_[p]) * (Nat.choose (M + k - 1) (k - 1) : ℤ_[p]) := by
  have hunit : IsUnit (k : ℤ_[p]) := isUnit_nat_of_not_dvd p hpk
  have hnat := key_ki M k hM hk
  have hcast : (k : ℤ_[p]) * (Nat.choose (M + k - 1) k : ℤ_[p])
      = (M : ℤ_[p]) * (Nat.choose (M + k - 1) (k - 1) : ℤ_[p]) := by exact_mod_cast hnat
  have hinv : Ring.inverse (k : ℤ_[p]) * (k : ℤ_[p]) = 1 := Ring.inverse_mul_cancel _ hunit
  calc (Nat.choose (M + k - 1) k : ℤ_[p])
      = (Ring.inverse (k : ℤ_[p]) * (k : ℤ_[p])) * (Nat.choose (M + k - 1) k : ℤ_[p]) := by
        rw [hinv, one_mul]
    _ = Ring.inverse (k : ℤ_[p]) * ((k : ℤ_[p]) * (Nat.choose (M + k - 1) k : ℤ_[p])) := by ring
    _ = Ring.inverse (k : ℤ_[p]) * ((M : ℤ_[p]) * (Nat.choose (M + k - 1) (k - 1) : ℤ_[p])) := by
        rw [hcast]
    _ = Ring.inverse (k : ℤ_[p]) * (M : ℤ_[p]) * (Nat.choose (M + k - 1) (k - 1) : ℤ_[p]) := by ring

/-- The summand of the reduced sum `G`. -/
noncomputable def Gterm (p M k : ℕ) [Fact p.Prime] : ℤ_[p] :=
  ((M : ℤ_[p]) + 2 * (k : ℤ_[p])) * (Nat.choose (M + k - 1) (k - 1) : ℤ_[p]) ^ 3
    * (Ring.inverse (k : ℤ_[p])) ^ 3

/-- The reduced sum `G = S₀ / M³`. -/
noncomputable def Gsum (p M : ℕ) [Fact p.Prime] : ℤ_[p] :=
  ∑ k ∈ (Finset.range (M + 1)).filter (fun k => ¬ p ∣ k), Gterm p M k

/-- The "H" summand `2 · C(M+j-1,j-1)³ · (j⁻¹)²`. -/
noncomputable def Hterm (p M j : ℕ) [Fact p.Prime] : ℤ_[p] :=
  2 * (Nat.choose (M + j - 1) (j - 1) : ℤ_[p]) ^ 3 * (Ring.inverse (j : ℤ_[p])) ^ 2

/-- `S₀ = M³ · G` in `ℤ_[p]`. -/
lemma S0_padic_eq (p M : ℕ) [Fact p.Prime] (hM : 1 ≤ M) :
    ((((Finset.filter (fun k => ¬ p ∣ k) (Finset.range (M + 1))).sum
       (fun k => (M + 2 * k) * (Nat.choose (M + k - 1) (M - 1)) ^ 3)) : ℕ) : ℤ_[p])
      = (M : ℤ_[p]) ^ 3 * Gsum p M := by
  rw [Nat.cast_sum]
  unfold Gsum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_filter, Finset.mem_range] at hk
  obtain ⟨hkr, hpk⟩ := hk
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exact absurd (h0 ▸ dvd_zero p) hpk
    · exact h0
  rw [choose_symm_index M k hM]
  unfold Gterm
  push_cast
  rw [ki_padic p M k hM hk1 hpk]
  ring

/-- Reindexing a `p∤·`-filtered sum over `range (a*b)` into blocks of length `a`
(requires `p ∣ a`). -/
lemma reindex_filter (p a b : ℕ) [Fact p.Prime] (hpa : p ∣ a) (f : ℕ → ℤ_[p]) :
    ∑ k ∈ (Finset.range (a * b)).filter (fun n => ¬ p ∣ n), f k
      = ∑ μ ∈ Finset.range b, ∑ σ ∈ (Finset.range a).filter (fun n => ¬ p ∣ n), f (a * μ + σ) := by
  rw [Finset.sum_filter, sum_range_reindex a b (fun k => if ¬ p ∣ k then f k else 0)]
  apply Finset.sum_congr rfl
  intro μ _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : p ∣ σ
  · have h1 : p ∣ (a * μ + σ) := dvd_add (hpa.mul_right μ) hσ
    rw [if_neg (not_not.mpr h1), if_neg (not_not.mpr hσ)]
  · have h1 : ¬ p ∣ (a * μ + σ) := by
      intro h
      apply hσ
      have hd : p ∣ (a * μ + σ) - a * μ := Nat.dvd_sub h (hpa.mul_right μ)
      have h2 : (a * μ + σ) - a * μ = σ := by omega
      rwa [h2] at hd
    rw [if_pos h1, if_pos hσ]

/-- `W_1(l)` written as an explicit filtered sum over `{p·l+1,…,p·l+p-1}`. -/
lemma Wblk_one (p l : ℕ) [Fact p.Prime] :
    Wblk p 1 l = ∑ ρ ∈ (Finset.range p).filter (fun n => ¬ p ∣ n),
      (Ring.inverse ((p * l + ρ : ℕ) : ℤ_[p])) ^ 2 := by
  unfold Wblk
  rw [pow_one, Finset.sum_filter, Finset.sum_filter, Finset.sum_Ico_eq_sum_range]
  have hpp : p * l + p - p * l = p := by omega
  rw [hpp]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hd : p ∣ i
  · have h1 : p ∣ (p * l + i) := dvd_add (dvd_mul_right p l) hd
    rw [if_neg (not_not.mpr h1), if_neg (not_not.mpr hd)]
  · have h1 : ¬ p ∣ (p * l + i) := by
      intro h
      apply hd
      have hsub : p ∣ (p * l + i) - p * l := Nat.dvd_sub h (dvd_mul_right p l)
      have h2 : (p * l + i) - p * l = i := by omega
      rwa [h2] at hsub
    rw [if_pos h1, if_pos hd]

/-- If `pᵗ ∣ (a - b)` for units `a,b`, then `pᵗ ∣ (a⁻¹ - b⁻¹)`. -/
lemma dvd_inverse_sub_inverse (p : ℕ) [Fact p.Prime] (t : ℕ) {a b : ℤ_[p]}
    (ha : IsUnit a) (hb : IsUnit b) (h : (p : ℤ_[p]) ^ t ∣ (a - b)) :
    (p : ℤ_[p]) ^ t ∣ (Ring.inverse a - Ring.inverse b) := by
  have hia : Ring.inverse a * a = 1 := Ring.inverse_mul_cancel a ha
  have hib : b * Ring.inverse b = 1 := Ring.mul_inverse_cancel b hb
  have e : Ring.inverse a - Ring.inverse b = Ring.inverse a * (b - a) * Ring.inverse b := by
    have h2 : Ring.inverse a * (b - a) * Ring.inverse b
        = Ring.inverse a * (b * Ring.inverse b) - (Ring.inverse a * a) * Ring.inverse b := by ring
    rw [h2, hib, hia]; ring
  rw [e]
  have hba : (p : ℤ_[p]) ^ t ∣ (b - a) := by
    have h2 : b - a = -(a - b) := by ring
    rw [h2]; exact dvd_neg.mpr h
  exact (hba.mul_left _).mul_right _

/-- **Scale descent** (Jacobsthal-type, one level).  For `B ≤ A`, `e ≥ 1`, any `x`,
`C(A p^e + x, B p^e + x) ≡ C(A p^{e-1} + ⌊x/p⌋, B p^{e-1} + ⌊x/p⌋) (mod p^e)`.
Proved from the file's `peel_nat` identity: the `p ∤ i` factors of the peeled product differ from
the `A p^e + i` numerator factors by `(A-B) p^e`, hence agree mod `p^e`, and the whole product is a
unit. -/
lemma scale_descent (p : ℕ) [Fact p.Prime] (A B e x : ℕ) (hBA : B ≤ A) (he : 1 ≤ e) :
    (p : ℤ_[p]) ^ e ∣
      ((Nat.choose (A * p ^ e + x) (B * p ^ e + x) : ℤ_[p])
        - (Nat.choose (A * p ^ (e - 1) + x / p) (B * p ^ (e - 1) + x / p) : ℤ_[p])) := by
  have hp := (Fact.out : p.Prime)
  have hp0 : 0 < p := hp.pos
  obtain ⟨s, rfl⟩ : ∃ s, e = s + 1 := ⟨e - 1, by omega⟩
  have hpeel := peel_nat p ((A - B) * p ^ s) hp0 (B * p ^ (s + 1) + x)
  -- the two binomials
  have htop : (A - B) * p ^ s * p + (B * p ^ (s + 1) + x) = A * p ^ (s + 1) + x := by
    rw [show (A - B) * p ^ s * p = (A - B) * p ^ (s + 1) from by rw [pow_succ]; ring,
      ← Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel hBA]
  have hlp : (B * p ^ (s + 1) + x) / p = B * p ^ s + x / p := by
    rw [show B * p ^ (s + 1) + x = p * (B * p ^ s) + x from by rw [pow_succ]; ring,
      Nat.mul_add_div hp0]
  have hbot : (A - B) * p ^ s + (B * p ^ s + x / p) = A * p ^ s + x / p := by
    rw [← Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel hBA]
  rw [htop, hlp, hbot] at hpeel
  set Pn : ℕ := ∏ i ∈ Finset.Icc 1 (B * p ^ (s + 1) + x), (if p ∣ i then 1 else i) with hPn
  set Qn : ℕ := ∏ i ∈ Finset.Icc 1 (B * p ^ (s + 1) + x),
      (if p ∣ i then 1 else (A - B) * p ^ s * p + i) with hQn
  have hsimp : s + 1 - 1 = s := by omega
  rw [hsimp]
  -- cast the peel identity to ℤ_[p]
  have hcast : (Nat.choose (A * p ^ (s + 1) + x) (B * p ^ (s + 1) + x) : ℤ_[p]) * (Pn : ℤ_[p])
      = (Nat.choose (A * p ^ s + x / p) (B * p ^ s + x / p) : ℤ_[p]) * (Qn : ℤ_[p]) := by
    rw [hPn, hQn]
    exact_mod_cast hpeel
  -- `Pn` is a unit
  have hPnu : IsUnit (Pn : ℤ_[p]) := by
    apply isUnit_nat_of_not_dvd
    rw [hPn, ← hp.coprime_iff_not_dvd]
    apply Nat.Coprime.prod_right
    intro i _
    by_cases hd : p ∣ i
    · simp [hd]
    · simpa [hd] using (hp.coprime_iff_not_dvd).mpr hd
  -- `p^{s+1} ∣ Qn - Pn`
  have hdiff : (p : ℤ_[p]) ^ (s + 1) ∣ ((Qn : ℤ_[p]) - (Pn : ℤ_[p])) := by
    rw [hQn, hPn, Nat.cast_prod, Nat.cast_prod]
    apply dvd_prod_sub_prod
    intro i _
    by_cases hd : p ∣ i
    · simp [hd]
    · simp only [hd, if_false]
      refine ⟨((A - B : ℕ) : ℤ_[p]), ?_⟩
      have hii : (A - B) * p ^ s * p + i = i + (A - B) * p ^ (s + 1) := by
        rw [pow_succ]; ring
      rw [hii]; push_cast; ring
  -- assemble
  set X := (Nat.choose (A * p ^ (s + 1) + x) (B * p ^ (s + 1) + x) : ℤ_[p]) with hX
  set Y := (Nat.choose (A * p ^ s + x / p) (B * p ^ s + x / p) : ℤ_[p]) with hY
  have hmul : (p : ℤ_[p]) ^ (s + 1) ∣ (X - Y) * (Pn : ℤ_[p]) := by
    have e2 : (X - Y) * (Pn : ℤ_[p]) = Y * ((Qn : ℤ_[p]) - (Pn : ℤ_[p])) := by
      have : X * (Pn : ℤ_[p]) = Y * (Qn : ℤ_[p]) := hcast
      linear_combination this
    rw [e2]; exact hdiff.mul_left _
  obtain ⟨v, hv⟩ := hPnu
  obtain ⟨w, hw⟩ := hmul
  refine ⟨w * (↑v⁻¹ : ℤ_[p]), ?_⟩
  have : (X - Y) * (Pn : ℤ_[p]) * (↑v⁻¹ : ℤ_[p]) = (X - Y) := by
    rw [← hv]; rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  rw [← this, hw]; ring

lemma STAR_padic (p r u K lam rho : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hu1 : 1 ≤ u) (hpu : ¬ p ∣ u) (hK : K < u)
    (hlam : lam < p ^ r) (hrho : rho ∈ (Finset.range p).filter (fun n => ¬ p ∣ n)) :
    (p : ℤ_[p]) ^ (r + 1) ∣
      ((Nat.choose (p ^ (r + 1) * u + (p ^ (r + 1) * K + (p * lam + rho)) - 1)
          (p ^ (r + 1) * K + (p * lam + rho) - 1) : ℤ_[p])
        - (Nat.choose ((u + K) * p ^ (r + 1)) (K * p ^ (r + 1)) : ℤ_[p]) * Qstar p K u r lam) := by
  have hp := (Fact.out : p.Prime)
  have hp0 : 0 < p := hp.pos
  rw [Finset.mem_filter, Finset.mem_range] at hrho
  obtain ⟨hrholt, hprho⟩ := hrho
  have hrho1 : 1 ≤ rho := by
    rcases Nat.eq_zero_or_pos rho with h | h
    · exact absurd (h ▸ dvd_zero p) hprho
    · exact h
  set x := p * lam + rho - 1 with hx
  -- rewrite the two indices of `δ_k`
  have e_top : p ^ (r + 1) * u + (p ^ (r + 1) * K + (p * lam + rho)) - 1 = (u + K) * p ^ (r + 1) + x := by
    rw [show p ^ (r + 1) * u + (p ^ (r + 1) * K + (p * lam + rho))
        = (u + K) * p ^ (r + 1) + (p * lam + rho) from by ring, hx]; omega
  have e_bot : p ^ (r + 1) * K + (p * lam + rho) - 1 = K * p ^ (r + 1) + x := by
    rw [hx, Nat.mul_comm (p ^ (r + 1)) K]; omega
  rw [e_top, e_bot]
  -- `x / p = lam`
  have hxp : x / p = lam := by
    have hxe : x = p * lam + (rho - 1) := by rw [hx]; omega
    rw [hxe, Nat.mul_add_div hp0, Nat.div_eq_of_lt (by omega : rho - 1 < p), Nat.add_zero]
  -- the two scale-descent congruences
  have hd1 := scale_descent p (u + K) K (r + 1) x (by omega) (by omega)
  rw [show r + 1 - 1 = r from by omega, hxp] at hd1
  have hd0 := scale_descent p (u + K) K (r + 1) 0 (by omega) (by omega)
  rw [show r + 1 - 1 = r from by omega] at hd0
  simp only [Nat.add_zero, Nat.zero_div] at hd0
  -- names
  set C1 : ℕ := Nat.choose (K * p ^ r + lam) lam with hC1
  set C2 : ℕ := Nat.choose ((K + u) * p ^ r + lam) lam with hC2
  set dk : ℤ_[p] := (Nat.choose ((u + K) * p ^ (r + 1) + x) (K * p ^ (r + 1) + x) : ℤ_[p]) with hdk
  set dp : ℤ_[p] := (Nat.choose ((u + K) * p ^ r + lam) (K * p ^ r + lam) : ℤ_[p]) with hdp
  set bK : ℤ_[p] := (Nat.choose ((u + K) * p ^ (r + 1)) (K * p ^ (r + 1)) : ℤ_[p]) with hbK
  set d1 : ℤ_[p] := (Nat.choose ((u + K) * p ^ r) (K * p ^ r) : ℤ_[p]) with hd1'
  -- C1 is a unit
  have hC1u : IsUnit (C1 : ℤ_[p]) := by
    rw [hC1]; exact isUnit_choose_ppow_add p K r lam hlam
  -- Vandermonde: dp * C1 = C2 * d1
  have hvand : (dp : ℤ_[p]) * (C1 : ℤ_[p]) = (C2 : ℤ_[p]) * (d1 : ℤ_[p]) := by
    have hnat : Nat.choose ((u + K) * p ^ r + lam) (K * p ^ r + lam) * Nat.choose (K * p ^ r + lam) lam
        = Nat.choose ((u + K) * p ^ r + lam) lam * Nat.choose ((u + K) * p ^ r) (K * p ^ r) := by
      have h := Nat.choose_mul (n := (u + K) * p ^ r + lam) (k := K * p ^ r + lam) (s := lam)
        (by omega)
      rw [show (u + K) * p ^ r + lam - lam = (u + K) * p ^ r from by omega,
          show K * p ^ r + lam - lam = K * p ^ r from by omega] at h
      exact h
    rw [hdp, hC1, hC2, hd1', show ((K + u) : ℕ) = (u + K) from by ring]
    exact_mod_cast hnat
  -- Qstar in terms of C1, C2
  have hQ : Qstar p K u r lam = (C2 : ℤ_[p]) * Ring.inverse (C1 : ℤ_[p]) := by
    rw [Qstar, hC1, hC2]
  rw [hQ]
  -- reduce to divisibility of `dk * C1 - bK * C2`
  have hkey : (p : ℤ_[p]) ^ (r + 1) ∣ ((dk : ℤ_[p]) * (C1 : ℤ_[p]) - (bK : ℤ_[p]) * (C2 : ℤ_[p])) := by
    have hsplit : (dk : ℤ_[p]) * (C1 : ℤ_[p]) - (bK : ℤ_[p]) * (C2 : ℤ_[p])
        = ((dk : ℤ_[p]) - dp) * (C1 : ℤ_[p]) + ((dp : ℤ_[p]) * (C1 : ℤ_[p]) - (C2 : ℤ_[p]) * (d1 : ℤ_[p]))
          + (d1 - (bK : ℤ_[p])) * (C2 : ℤ_[p]) := by ring
    rw [hsplit, hvand, sub_self, add_zero]
    apply dvd_add
    · exact (hd1.mul_right _)
    · have : (d1 : ℤ_[p]) - bK = -(bK - d1) := by ring
      rw [this]; exact ((hd0.neg_right).mul_right _)
  -- divide by the unit C1
  have hfin : (dk : ℤ_[p]) - bK * ((C2 : ℤ_[p]) * Ring.inverse (C1 : ℤ_[p]))
      = ((dk : ℤ_[p]) * (C1 : ℤ_[p]) - bK * (C2 : ℤ_[p])) * Ring.inverse (C1 : ℤ_[p]) := by
    have hcc : (C1 : ℤ_[p]) * Ring.inverse (C1 : ℤ_[p]) = 1 := Ring.mul_inverse_cancel _ hC1u
    linear_combination (-(dk : ℤ_[p])) * hcc
  rw [hfin]
  exact hkey.mul_right _

/-- Per-`(λ,ρ)` divisibility used to assemble a block. -/
lemma block_term_dvd (p r u K lam rho : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hu1 : 1 ≤ u) (hpu : ¬ p ∣ u) (hK : K < u)
    (hlam : lam < p ^ r) (hrho : rho ∈ (Finset.range p).filter (fun n => ¬ p ∣ n)) :
    (p : ℤ_[p]) ^ (r + 1) ∣
      (Hterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + (p * lam + rho))
        - 2 * (Nat.choose ((u + K) * p ^ (r + 1)) (K * p ^ (r + 1)) : ℤ_[p]) ^ 3 * (Qstar p K u r lam) ^ 3
            * (Ring.inverse ((p * lam + rho : ℕ) : ℤ_[p])) ^ 2) := by
  have hp := (Fact.out : p.Prime)
  rw [Finset.mem_filter, Finset.mem_range] at hrho
  obtain ⟨hrho_lt, hprho⟩ := hrho
  -- p ∤ L  and  p ∤ j
  have hpL : ¬ p ∣ (p * lam + rho) := by
    intro h; apply hprho
    have hsub : p ∣ (p * lam + rho) - p * lam := Nat.dvd_sub h (dvd_mul_right p lam)
    have h2 : (p * lam + rho) - p * lam = rho := by omega
    rwa [h2] at hsub
  have hpj : ¬ p ∣ (p ^ (r + 1) * K + (p * lam + rho)) := by
    intro h; apply hpL
    have hdiv : p ∣ p ^ (r + 1) * K := (dvd_pow_self p (by omega)).mul_right K
    have hsub : p ∣ (p ^ (r + 1) * K + (p * lam + rho)) - p ^ (r + 1) * K := Nat.dvd_sub h hdiv
    have h2 : (p ^ (r + 1) * K + (p * lam + rho)) - p ^ (r + 1) * K = p * lam + rho := by omega
    rwa [h2] at hsub
  have huL : IsUnit ((p * lam + rho : ℕ) : ℤ_[p]) := isUnit_nat_of_not_dvd p hpL
  have huj : IsUnit ((p ^ (r + 1) * K + (p * lam + rho) : ℕ) : ℤ_[p]) :=
    isUnit_nat_of_not_dvd p hpj
  -- STAR and its cube
  have hstar := STAR_padic p r u K lam rho hp5 hu1 hpu hK hlam
    (by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hrho_lt, hprho⟩)
  have hcube := dvd_cube_sub_cube hstar
  -- inverse congruence and its square
  have hjLdvd : (p : ℤ_[p]) ^ (r + 1) ∣
      (((p ^ (r + 1) * K + (p * lam + rho) : ℕ) : ℤ_[p]) - ((p * lam + rho : ℕ) : ℤ_[p])) := by
    have e : ((p ^ (r + 1) * K + (p * lam + rho) : ℕ) : ℤ_[p]) - ((p * lam + rho : ℕ) : ℤ_[p])
        = (p : ℤ_[p]) ^ (r + 1) * (K : ℤ_[p]) := by push_cast; ring
    rw [e]; exact dvd_mul_right _ _
  have hinv := dvd_inverse_sub_inverse p (r + 1) huj huL hjLdvd
  have hsq : (p : ℤ_[p]) ^ (r + 1) ∣
      ((Ring.inverse ((p ^ (r + 1) * K + (p * lam + rho) : ℕ) : ℤ_[p])) ^ 2
        - (Ring.inverse ((p * lam + rho : ℕ) : ℤ_[p])) ^ 2) := by
    have e : (Ring.inverse ((p ^ (r + 1) * K + (p * lam + rho) : ℕ) : ℤ_[p])) ^ 2
          - (Ring.inverse ((p * lam + rho : ℕ) : ℤ_[p])) ^ 2
        = (Ring.inverse ((p ^ (r + 1) * K + (p * lam + rho) : ℕ) : ℤ_[p])
            - Ring.inverse ((p * lam + rho : ℕ) : ℤ_[p]))
          * (Ring.inverse ((p ^ (r + 1) * K + (p * lam + rho) : ℕ) : ℤ_[p])
            + Ring.inverse ((p * lam + rho : ℕ) : ℤ_[p])) := by ring
    rw [e]; exact hinv.mul_right _
  -- combine
  have hcomb : (p : ℤ_[p]) ^ (r + 1) ∣
      ((Nat.choose (p ^ (r + 1) * u + (p ^ (r + 1) * K + (p * lam + rho)) - 1)
            (p ^ (r + 1) * K + (p * lam + rho) - 1) : ℤ_[p]) ^ 3
          * (Ring.inverse ((p ^ (r + 1) * K + (p * lam + rho) : ℕ) : ℤ_[p])) ^ 2
        - ((Nat.choose ((u + K) * p ^ (r + 1)) (K * p ^ (r + 1)) : ℤ_[p]) * Qstar p K u r lam) ^ 3
            * (Ring.inverse ((p * lam + rho : ℕ) : ℤ_[p])) ^ 2) := by
    have e2 : (Nat.choose (p ^ (r + 1) * u + (p ^ (r + 1) * K + (p * lam + rho)) - 1)
              (p ^ (r + 1) * K + (p * lam + rho) - 1) : ℤ_[p]) ^ 3
            * (Ring.inverse ((p ^ (r + 1) * K + (p * lam + rho) : ℕ) : ℤ_[p])) ^ 2
          - ((Nat.choose ((u + K) * p ^ (r + 1)) (K * p ^ (r + 1)) : ℤ_[p]) * Qstar p K u r lam) ^ 3
              * (Ring.inverse ((p * lam + rho : ℕ) : ℤ_[p])) ^ 2
        = (Nat.choose (p ^ (r + 1) * u + (p ^ (r + 1) * K + (p * lam + rho)) - 1)
              (p ^ (r + 1) * K + (p * lam + rho) - 1) : ℤ_[p]) ^ 3
            * ((Ring.inverse ((p ^ (r + 1) * K + (p * lam + rho) : ℕ) : ℤ_[p])) ^ 2
              - (Ring.inverse ((p * lam + rho : ℕ) : ℤ_[p])) ^ 2)
          + ((Nat.choose (p ^ (r + 1) * u + (p ^ (r + 1) * K + (p * lam + rho)) - 1)
                (p ^ (r + 1) * K + (p * lam + rho) - 1) : ℤ_[p]) ^ 3
              - ((Nat.choose ((u + K) * p ^ (r + 1)) (K * p ^ (r + 1)) : ℤ_[p]) * Qstar p K u r lam) ^ 3)
            * (Ring.inverse ((p * lam + rho : ℕ) : ℤ_[p])) ^ 2 := by ring
    rw [e2]
    exact dvd_add (hsq.mul_left _) (hcube.mul_right _)
  have hreshape : Hterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + (p * lam + rho))
        - 2 * (Nat.choose ((u + K) * p ^ (r + 1)) (K * p ^ (r + 1)) : ℤ_[p]) ^ 3 * (Qstar p K u r lam) ^ 3
            * (Ring.inverse ((p * lam + rho : ℕ) : ℤ_[p])) ^ 2
      = 2 * ((Nat.choose (p ^ (r + 1) * u + (p ^ (r + 1) * K + (p * lam + rho)) - 1)
              (p ^ (r + 1) * K + (p * lam + rho) - 1) : ℤ_[p]) ^ 3
            * (Ring.inverse ((p ^ (r + 1) * K + (p * lam + rho) : ℕ) : ℤ_[p])) ^ 2
          - ((Nat.choose ((u + K) * p ^ (r + 1)) (K * p ^ (r + 1)) : ℤ_[p]) * Qstar p K u r lam) ^ 3
              * (Ring.inverse ((p * lam + rho : ℕ) : ℤ_[p])) ^ 2) := by
    unfold Hterm; ring
  rw [hreshape]
  exact hcomb.mul_left 2

/-- Per-block divisibility: `p^{r+1} ∣ ∑_{L, p∤L} Gterm` for each block index `K < u`. -/
lemma dvd_block (p r u K : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hu1 : 1 ≤ u)
    (hpu : ¬ p ∣ u) (hK : K < u) :
    (p : ℤ_[p]) ^ (r + 1) ∣
      ∑ L ∈ (Finset.range (p ^ (r + 1))).filter (fun n => ¬ p ∣ n),
        Gterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + L) := by
  have hp := (Fact.out : p.Prime)
  -- step 1 : the `M·δ³·(j⁻¹)³` remainder is divisible
  have step1 : (p : ℤ_[p]) ^ (r + 1) ∣
      ∑ L ∈ (Finset.range (p ^ (r + 1))).filter (fun n => ¬ p ∣ n),
        (Gterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + L)
          - Hterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + L)) := by
    apply Finset.dvd_sum
    intro L hL
    rw [Finset.mem_filter, Finset.mem_range] at hL
    obtain ⟨hLlt, hpL⟩ := hL
    have hpj : ¬ p ∣ (p ^ (r + 1) * K + L) := by
      intro h; apply hpL
      have hdiv : p ∣ p ^ (r + 1) * K := (dvd_pow_self p (by omega)).mul_right K
      have hsub : p ∣ (p ^ (r + 1) * K + L) - p ^ (r + 1) * K := Nat.dvd_sub h hdiv
      have h2 : (p ^ (r + 1) * K + L) - p ^ (r + 1) * K = L := by omega
      rwa [h2] at hsub
    have hjunit : IsUnit ((p ^ (r + 1) * K + L : ℕ) : ℤ_[p]) := isUnit_nat_of_not_dvd p hpj
    have hjinv : ((p ^ (r + 1) * K + L : ℕ) : ℤ_[p]) * Ring.inverse ((p ^ (r + 1) * K + L : ℕ) : ℤ_[p]) = 1 :=
      Ring.mul_inverse_cancel _ hjunit
    have key : Gterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + L)
          - Hterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + L)
        = ((p ^ (r + 1) * u : ℕ) : ℤ_[p])
          * (Nat.choose (p ^ (r + 1) * u + (p ^ (r + 1) * K + L) - 1) (p ^ (r + 1) * K + L - 1) : ℤ_[p]) ^ 3
          * (Ring.inverse ((p ^ (r + 1) * K + L : ℕ) : ℤ_[p])) ^ 3 := by
      unfold Gterm Hterm
      linear_combination (2 * (Nat.choose (p ^ (r + 1) * u + (p ^ (r + 1) * K + L) - 1) (p ^ (r + 1) * K + L - 1) : ℤ_[p]) ^ 3
        * (Ring.inverse ((p ^ (r + 1) * K + L : ℕ) : ℤ_[p])) ^ 2) * hjinv
    rw [key]
    have hpM : (p : ℤ_[p]) ^ (r + 1) ∣ ((p ^ (r + 1) * u : ℕ) : ℤ_[p]) := by
      rw [← nat_dvd_iff_padic_dvd]
      exact dvd_mul_right _ _
    exact (hpM.mul_right _).mul_right _
  -- step 2 : the `H` sum is divisible
  have hset : (Finset.range (p ^ (r + 1))).filter (fun n => ¬ p ∣ n)
            = (Finset.range (p * p ^ r)).filter (fun n => ¬ p ∣ n) := by rw [pow_succ']
  have hreidx : ∑ L ∈ (Finset.range (p ^ (r + 1))).filter (fun n => ¬ p ∣ n),
          Hterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + L)
      = ∑ lam ∈ Finset.range (p ^ r), ∑ rho ∈ (Finset.range p).filter (fun n => ¬ p ∣ n),
          Hterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + (p * lam + rho)) := by
    rw [hset]
    exact reindex_filter p p (p ^ r) (dvd_refl p)
      (fun L => Hterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + L))
  have hPhi_expand : 2 * (Nat.choose ((u + K) * p ^ (r + 1)) (K * p ^ (r + 1)) : ℤ_[p]) ^ 3 * Phi p K u r 1
      = ∑ lam ∈ Finset.range (p ^ r), ∑ rho ∈ (Finset.range p).filter (fun n => ¬ p ∣ n),
          2 * (Nat.choose ((u + K) * p ^ (r + 1)) (K * p ^ (r + 1)) : ℤ_[p]) ^ 3 * (Qstar p K u r lam) ^ 3
            * (Ring.inverse ((p * lam + rho : ℕ) : ℤ_[p])) ^ 2 := by
    unfold Phi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro lam _
    rw [Wblk_one p lam, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho _
    ring
  have hPhidvd : (p : ℤ_[p]) ^ (r + 1) ∣ 2 * (Nat.choose ((u + K) * p ^ (r + 1)) (K * p ^ (r + 1)) : ℤ_[p]) ^ 3 * Phi p K u r 1 :=
    (dvd_Phi p K u hp5 r 1 (le_refl 1)).mul_left _
  have hdiff : (p : ℤ_[p]) ^ (r + 1) ∣
      ((∑ lam ∈ Finset.range (p ^ r), ∑ rho ∈ (Finset.range p).filter (fun n => ¬ p ∣ n),
          Hterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + (p * lam + rho)))
        - 2 * (Nat.choose ((u + K) * p ^ (r + 1)) (K * p ^ (r + 1)) : ℤ_[p]) ^ 3 * Phi p K u r 1) := by
    rw [hPhi_expand, ← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro lam hlam
    rw [Finset.mem_range] at hlam
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro rho hrho
    exact block_term_dvd p r u K lam rho hp5 hu1 hpu hK hlam hrho
  have step2 : (p : ℤ_[p]) ^ (r + 1) ∣
      ∑ L ∈ (Finset.range (p ^ (r + 1))).filter (fun n => ¬ p ∣ n),
        Hterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + L) := by
    rw [hreidx]
    have hcombine : (∑ lam ∈ Finset.range (p ^ r), ∑ rho ∈ (Finset.range p).filter (fun n => ¬ p ∣ n),
            Hterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + (p * lam + rho)))
        = (((∑ lam ∈ Finset.range (p ^ r), ∑ rho ∈ (Finset.range p).filter (fun n => ¬ p ∣ n),
              Hterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + (p * lam + rho)))
             - 2 * (Nat.choose ((u + K) * p ^ (r + 1)) (K * p ^ (r + 1)) : ℤ_[p]) ^ 3 * Phi p K u r 1)
            + 2 * (Nat.choose ((u + K) * p ^ (r + 1)) (K * p ^ (r + 1)) : ℤ_[p]) ^ 3 * Phi p K u r 1) := by ring
    rw [hcombine]
    exact dvd_add hdiff hPhidvd
  -- assemble
  have hsplit : ∑ L ∈ (Finset.range (p ^ (r + 1))).filter (fun n => ¬ p ∣ n),
        Gterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + L)
      = (∑ L ∈ (Finset.range (p ^ (r + 1))).filter (fun n => ¬ p ∣ n),
          (Gterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + L)
            - Hterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + L)))
        + ∑ L ∈ (Finset.range (p ^ (r + 1))).filter (fun n => ¬ p ∣ n),
          Hterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + L) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro L _; ring
  rw [hsplit]
  exact dvd_add step1 step2

/-- `p^e ∣ G` (the reduced sum). -/
lemma dvd_Gsum (p M u e : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (he1 : 1 ≤ e)
    (hpu : ¬ p ∣ u) (hu1 : 1 ≤ u) (hMeq : M = p ^ e * u) :
    (p : ℤ_[p]) ^ e ∣ Gsum p M := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨r, rfl⟩ : ∃ r, e = r + 1 := ⟨e - 1, by omega⟩
  unfold Gsum
  have hfilter : (Finset.range (M + 1)).filter (fun k => ¬ p ∣ k)
      = (Finset.range M).filter (fun k => ¬ p ∣ k) := by
    rw [Finset.range_succ, Finset.filter_insert]
    have hpM : p ∣ M := by rw [hMeq]; exact (dvd_pow_self p (by omega)).mul_right u
    simp [hpM]
  rw [hfilter, hMeq]
  have hreidxG : ∑ k ∈ (Finset.range (p ^ (r + 1) * u)).filter (fun k => ¬ p ∣ k),
        Gterm p (p ^ (r + 1) * u) k
      = ∑ K ∈ Finset.range u, ∑ L ∈ (Finset.range (p ^ (r + 1))).filter (fun k => ¬ p ∣ k),
          Gterm p (p ^ (r + 1) * u) (p ^ (r + 1) * K + L) :=
    reindex_filter p (p ^ (r + 1)) u (dvd_pow_self p (Nat.succ_ne_zero r))
      (fun k => Gterm p (p ^ (r + 1) * u) k)
  rw [hreidxG]
  apply Finset.dvd_sum
  intro K hK
  rw [Finset.mem_range] at hK
  exact dvd_block p r u K hp5 hu1 hpu hK

/-- Part A core with an explicit `p`-adic valuation `e` and unit part `u`. -/
lemma partA_core (p M u e : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hM : 1 ≤ M) (he1 : 1 ≤ e)
    (hpu : ¬ p ∣ u) (hu1 : 1 ≤ u) (hMeq : M = p ^ e * u) :
    (p : ℤ_[p]) ^ (4 * e) ∣
      ((((Finset.filter (fun k => ¬ p ∣ k) (Finset.range (M + 1))).sum
         (fun k => (M + 2 * k) * (Nat.choose (M + k - 1) (M - 1)) ^ 3)) : ℕ) : ℤ_[p]) := by
  rw [S0_padic_eq p M hM]
  obtain ⟨g, hg⟩ := dvd_Gsum p M u e hp5 he1 hpu hu1 hMeq
  have hMcast : (M : ℤ_[p]) = (u : ℤ_[p]) * (p : ℤ_[p]) ^ e := by rw [hMeq]; push_cast; ring
  have h4 : (p : ℤ_[p]) ^ (4 * e) = ((p : ℤ_[p]) ^ e) ^ 4 := by rw [mul_comm, pow_mul]
  refine ⟨(u : ℤ_[p]) ^ 3 * g, ?_⟩
  rw [hMcast, hg, h4]; ring



/- ## Part A -/

/-- The genuine `p`-adic content of Part A, isolated.

NEEDS: the block factorization (STEP 1–3 of the task) rewriting
`S₀ = ∑_{K<u} p^{3e}·u^3·C(u+K,K)^3·Σ_K` with `Σ_K ≡ 0 mod p^e`, where `Σ_K` reduces (mod `p^e`)
to `2·A_K^3·Φ_{e-1}^{(1)}` for `c := K`, `w := u`, `r := e-1`, and then applies `dvd_Phi`. -/
lemma partA_padic (p M : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hM : 1 ≤ M) (hpM : p ∣ M) :
    (p : ℤ_[p]) ^ (4 * M.factorization p) ∣
      ((((Finset.filter (fun k => ¬ p ∣ k) (Finset.range (M + 1))).sum
         (fun k => (M + 2 * k) * (Nat.choose (M + k - 1) (M - 1)) ^ 3)) : ℕ) : ℤ_[p]) := by
  have hp := (Fact.out : p.Prime)
  set e := M.factorization p with he
  have he1 : 1 ≤ e := by
    have h := hp.factorization_pos_of_dvd (show M ≠ 0 by omega) hpM
    rw [he]; omega
  obtain ⟨u, hpu, hu1, hMeq⟩ : ∃ u, ¬ p ∣ u ∧ 1 ≤ u ∧ M = p ^ e * u := by
    refine ⟨M / p ^ e, ?_, ?_, ?_⟩
    · have h := Nat.not_dvd_ordCompl hp (show M ≠ 0 by omega)
      rw [← he] at h; exact h
    · have h := Nat.ordCompl_pos p (show M ≠ 0 by omega)
      rw [← he] at h; omega
    · have h := (Nat.ordProj_mul_ordCompl_eq_self M p).symm
      rw [← he] at h; exact h
  exact partA_core p M u e hp5 hM he1 hpu hu1 hMeq

/-- Part A: `p^{4e}` divides the sum over the terms with `p ∤ k`.

The `p`-adic core congruence (`dvd_Phi`, including the `Qstar_peel` induction step) is fully
proved above.  The remaining gap is the block-factorization bridge `partA_padic` connecting the
concrete sum `S₀` to `Φ`. -/
lemma partA (p M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hM : 1 ≤ M) (hpM : p ∣ M) :
    (↑(p ^ (4 * M.factorization p)) : ℤ) ∣
      (((Finset.sum (Finset.filter (fun k => ¬ p ∣ k) (Finset.range (M+1)))
         (fun k => (M + 2*k) * (Nat.choose (M+k-1) (M-1))^3)) : ℕ) : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Reduce `ℤ`-divisibility of the natural-number sum to `ℕ`-divisibility, then to
  -- `ℤ_[p]`-divisibility via the bridge `nat_dvd_iff_padic_dvd`.
  rw [Int.natCast_dvd_natCast, nat_dvd_iff_padic_dvd p (4 * M.factorization p)]
  -- Remaining goal (the genuine number-theoretic content):
  --   `(p : ℤ_[p]) ^ (4 * v_p M) ∣ (S₀ : ℤ_[p])`,
  -- discharged by the isolated `p`-adic lemma below.
  exact partA_padic p M hp5 hM hpM
