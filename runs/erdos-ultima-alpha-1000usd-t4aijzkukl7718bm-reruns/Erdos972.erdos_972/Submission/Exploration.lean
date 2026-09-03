import FormalConjecturesUtil

namespace Explore972

def primeSet (α : ℝ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime ⌊(α * p)⌋₊}

theorem infinite_iff_prime_pairs {α : ℝ} (hα : 1 < α) (hi : Irrational α) :
    (primeSet α).Infinite ↔
      ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p.Prime ∧ q.Prime ∧
        (q : ℝ) < α * p ∧ α * p < q + 1 := by
  constructor
  · intro h N
    obtain ⟨p, hp, hNp⟩ := h.exists_gt N
    rcases hp with ⟨hp, hq⟩
    refine ⟨p, ⌊(α * p)⌋₊, hNp, hp, hq, ?_, Nat.lt_floor_add_one _⟩
    exact lt_of_le_of_ne (Nat.floor_le (mul_nonneg (by linarith) (Nat.cast_nonneg p)))
      ((hi.mul_natCast hp.ne_zero).ne_nat _).symm
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨p, q, hNp, hp, hq, hlow, hupp⟩ := h N
    refine ⟨p, ⟨hp, ?_⟩, hNp⟩
    have hfloor : ⌊(α * p)⌋₊ = q :=
      (Nat.floor_eq_iff (mul_nonneg (by linarith) (Nat.cast_nonneg p))).2
        ⟨hlow.le, hupp⟩
    rwa [hfloor]

theorem primeSet_nat_eq_empty {m : ℕ} (hm : 1 < m) :
    primeSet (m : ℝ) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  rcases hp with ⟨hp, hmp⟩
  have heq : ⌊((m : ℝ) * p)⌋₊ = m * p := by
    rw [← Nat.cast_mul, Nat.floor_natCast]
  rw [heq] at hmp
  exact Nat.not_prime_mul (by omega) hp.ne_one hmp

theorem negation_iff_bounded_counterexample :
    (¬ ∀ α > 1, Irrational α → (primeSet α).Infinite) ↔
      ∃ α > 1, Irrational α ∧ ∃ N : ℕ,
        ∀ p : ℕ, N < p → p.Prime → ¬ Nat.Prime ⌊(α * p)⌋₊ := by
  constructor
  · intro h
    push_neg at h
    obtain ⟨α, hα, hi, hf⟩ := h
    refine ⟨α, hα, hi, ?_⟩
    have hb := mt (Set.infinite_iff_exists_gt (s := primeSet α)).mpr hf.not_infinite
    push_neg at hb
    obtain ⟨N, hN⟩ := hb
    refine ⟨N, ?_⟩
    intro p hNp hp hq
    have := hN p ⟨hp, hq⟩
    omega
  · rintro ⟨α, hα, hi, N, hN⟩ h
    obtain ⟨p, hp, hNp⟩ := (h α hα hi).exists_gt N
    exact hN p hNp hp.1 hp.2

/-- Arbitrarily long initial prime-free segments exist even for irrational slopes.
This is not a counterexample: the slope here depends on the segment length. -/
theorem exists_irrational_initial_gap (N : ℕ) :
    ∃ α > 1, Irrational α ∧ ∀ p : ℕ, p ≤ N → p ∉ primeSet α := by
  have hden : (0 : ℝ) < N + 1 := by positivity
  have hinterval : (2 : ℝ) < 2 + 1 / ((N : ℝ) + 1) := by
    linarith [one_div_pos.mpr hden]
  obtain ⟨α, hi, hlow, hupp⟩ := exists_irrational_btwn hinterval
  refine ⟨α, by linarith, hi, ?_⟩
  intro p hpN hp
  rcases hp with ⟨hp, hq⟩
  have ha : (α - 2) * ((N : ℝ) + 1) < 1 :=
    (lt_div_iff₀ hden).mp (by linarith)
  have hpn : (p : ℝ) ≤ N := by exact_mod_cast hpN
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hlower : (2 : ℝ) * p ≤ α * p := by nlinarith
  have hupper : α * p < (2 : ℝ) * p + 1 := by
    nlinarith [mul_nonneg (show 0 ≤ α - 2 by linarith) (sub_nonneg.mpr hpn)]
  have hfloor : ⌊(α * p)⌋₊ = 2 * p := by
    apply (Nat.floor_eq_iff (mul_nonneg (by linarith) hp0)).mpr
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using And.intro hlower hupper
  rw [hfloor] at hq
  exact Nat.not_prime_mul (by omega) hp.ne_one hq

/-- Avoidance of any fixed modulus is possible at arbitrarily large integer
indices. This does not assert that either value is prime. -/
theorem simultaneous_coprime_indices {α : ℝ} (hα : 1 < α) (hi : Irrational α)
    (M : ℕ) (hM : 0 < M) (N : ℕ) :
    ∃ n : ℕ, N < n ∧ n.Coprime M ∧ (⌊(α * n)⌋₊).Coprime M := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hM0 : (M : ℝ) ≠ 0 := ne_of_gt hMr
  letI : Fact ((0 : ℝ) < M) := ⟨hMr⟩
  have hd : DenseRange (fun k : ℕ => k • ((α * M : ℝ) : AddCircle (M : ℝ))) := by
    apply denseRange_zsmul_iff_nsmul.mp
    apply AddCircle.denseRange_zsmul_coe_iff.mpr
    simpa [hM0] using hi
  let β : ℝ := α * ((M : ℝ) * ((N : ℝ) + 1) + 1)
  let τ := Homeomorph.addRight (β : AddCircle (M : ℝ))
  have hd' : DenseRange (fun k : ℕ =>
      k • ((α * M : ℝ) : AddCircle (M : ℝ)) + (β : AddCircle (M : ℝ))) :=
    τ.surjective.denseRange.comp hd τ.continuous
  let S : Set (AddCircle (M : ℝ)) :=
    ((↑) : ℝ → AddCircle (M : ℝ)) '' Set.Ioo (1 : ℝ) 2
  have hS : IsOpen S := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hSne : S.Nonempty := ⟨((3 / 2 : ℝ) : AddCircle (M : ℝ)),
    3 / 2, by norm_num, rfl⟩
  obtain ⟨k, x, hx, hxeq⟩ := hd'.exists_mem_open hS hSne
  let n : ℕ := M * (k + N + 1) + 1
  have hlarge : N < n := by
    have hmul := Nat.le_mul_of_pos_left (k + N + 1) hM
    dsimp [n]
    omega
  have hnM : n.Coprime M := by
    simpa [n, Nat.add_comm] using
      (Nat.coprime_add_mul_left_left 1 M (k + N + 1)).mpr (Nat.coprime_one_left M)
  have hreal : (k : ℝ) * (α * M) + β = α * n := by
    dsimp [β, n]
    push_cast
    ring
  have hco : (((k : ℝ) * (α * M) + β : ℝ) : AddCircle (M : ℝ)) =
      k • ((α * M : ℝ) : AddCircle (M : ℝ)) + (β : AddCircle (M : ℝ)) := by
    rw [AddCircle.coe_add, ← nsmul_eq_mul, AddCircle.coe_nsmul]
  rw [← hco, hreal] at hxeq
  obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp hxeq)
  simp only [zsmul_eq_mul] at hz
  have hprod : α * n = x + ((z * (M : ℤ) : ℤ) : ℝ) := by
    push_cast
    linarith
  have hfx : ⌊x⌋ = (1 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    norm_num at hx ⊢
    exact ⟨hx.1.le, hx.2⟩
  have hf : ⌊(α * n)⌋ = 1 + z * (M : ℤ) := by
    rw [hprod, Int.floor_add_intCast, hfx]
  have hfnat : (⌊(α * n)⌋₊ : ℤ) = 1 + z * (M : ℤ) := by
    rw [Int.natCast_floor_eq_floor (mul_nonneg (by linarith) (Nat.cast_nonneg n)), hf]
  have hfmod : (⌊(α * n)⌋₊ : ZMod M) = 1 := by
    have he := congrArg (fun t : ℤ => (t : ZMod M)) hfnat
    simpa using he
  refine ⟨n, hlarge, hnM, (ZMod.isUnit_iff_coprime _ _).mp ?_⟩
  rw [hfmod]
  exact isUnit_one

open Filter in
open scoped Topology in
/-- A successful fixed prime remains successful under small perturbations of
an irrational slope. -/
theorem eventually_mem_primeSet_of_tendsto {α : ℝ} {a : ℕ → ℝ}
    (hα : 1 < α) (hi : Irrational α) (hlim : Tendsto a atTop (𝓝 α))
    {p : ℕ} (hp : p ∈ primeSet α) :
    ∀ᶠ n in atTop, p ∈ primeSet (a n) := by
  let q : ℕ := ⌊(α * p)⌋₊
  have hq : q.Prime := hp.2
  have hlow : (q : ℝ) < α * p :=
    lt_of_le_of_ne (Nat.floor_le (mul_nonneg (by linarith) (Nat.cast_nonneg p)))
      ((hi.mul_natCast hp.1.ne_zero).ne_nat _).symm
  have hupp : α * p < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hprod := hlim.mul_const (p : ℝ)
  filter_upwards [hprod.eventually_const_lt hlow, hprod.eventually_lt_const hupp]
    with n hnlow hnupp
  refine ⟨hp.1, ?_⟩
  have hfloor : ⌊(a n * p)⌋₊ = q :=
    (Nat.floor_eq_iff' hq.ne_zero).mpr ⟨hnlow.le, hnupp⟩
  rwa [hfloor]

open Filter in
open scoped Topology in
/-- A convergent family of finite-window counterexamples gives a genuine
counterexample if the limiting slope is irrational. -/
theorem finite_primeSet_of_irrational_limit {α : ℝ} {a : ℕ → ℝ}
    (hα : 1 < α) (hi : Irrational α) (hlim : Tendsto a atTop (𝓝 α))
    (B : ℕ) (hgap : ∀ n p : ℕ, B < p → p ≤ n → p ∉ primeSet (a n)) :
    (primeSet α).Finite := by
  apply (Set.finite_Iic B).subset
  intro p hp
  change p ≤ B
  by_contra! hBp
  have hev := eventually_mem_primeSet_of_tendsto hα hi hlim hp
  obtain ⟨n, hmem, hpn⟩ := (hev.and (eventually_ge_atTop p)).exists
  exact hgap n p hBp hpn hmem

open Filter in
open scoped Topology in
theorem counterexample_criterion {α : ℝ} {a : ℕ → ℝ}
    (hα : 1 < α) (hi : Irrational α) (hlim : Tendsto a atTop (𝓝 α))
    (B : ℕ) (hgap : ∀ n p : ℕ, B < p → p ≤ n → p ∉ primeSet (a n)) :
    ¬ ∀ β > 1, Irrational β → (primeSet β).Infinite := by
  intro h
  exact (finite_primeSet_of_irrational_limit hα hi hlim B hgap).not_infinite (h α hα hi)


/-- The quantitative cutoff needed to turn finite sieve avoidance into primality. -/
lemma prime_of_coprime_factorial_of_lt_sq {q M : ℕ} (hq : 2 ≤ q)
    (hc : q.Coprime M.factorial) (hbound : q < (M + 1) ^ 2) : q.Prime := by
  by_contra hprime
  have hmin := (Nat.coprime_factorial_iff (by omega : q ≠ 1)).mp hc
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < q) hprime
  have hmin' : M + 1 ≤ q.minFac := by omega
  nlinarith

lemma sq_succ_le_factorial {M : ℕ} (hM : 5 ≤ M) : (M + 1) ^ 2 ≤ M.factorial := by
  induction M, hM using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Nat.factorial_succ]
    have h₁ : (n + 1 + 1) ^ 2 ≤ 3 * (n + 1) ^ 2 := by nlinarith
    have h₂ : 3 * (n + 1) ^ 2 ≤ (n + 1) * (n + 1) ^ 2 :=
      Nat.mul_le_mul_right _ (by omega)
    exact h₁.trans (h₂.trans (Nat.mul_le_mul_left (n + 1) ih))

/-- The witnesses produced by the earlier dense-rotation construction are
already beyond the primality cutoff when the modulus is `M!`. -/
lemma rotation_witness_exceeds_sieve_cutoff {α : ℝ} (hα : 1 < α)
    (M k N : ℕ) (hM : 5 ≤ M) :
    (M + 1) ^ 2 ≤ ⌊(α * (M.factorial * (k + N + 1) + 1 : ℕ))⌋₊ := by
  calc
    (M + 1) ^ 2 ≤ M.factorial := sq_succ_le_factorial hM
    _ ≤ M.factorial * (k + N + 1) + 1 := by
      have := Nat.le_mul_of_pos_right M.factorial (by omega : 0 < k + N + 1)
      omega
    _ ≤ ⌊(α * (M.factorial * (k + N + 1) + 1 : ℕ))⌋₊ := by
      apply Nat.le_floor
      have hnonneg : (0 : ℝ) ≤ (M.factorial * (k + N + 1) + 1 : ℕ) := Nat.cast_nonneg _
      nlinarith

#print axioms rotation_witness_exceeds_sieve_cutoff


/-- An exact quantitative reformulation. The size bound is essential; finite
modulus avoidance alone does not supply it. -/
theorem infinite_iff_bounded_sieve_witnesses {α : ℝ} (hα : 1 < α) :
    (primeSet α).Infinite ↔
      ∀ N : ℕ, ∃ M p : ℕ, N < p ∧ p.Prime ∧
        (⌊(α * p)⌋₊).Coprime M.factorial ∧ ⌊(α * p)⌋₊ < (M + 1) ^ 2 := by
  constructor
  · intro h N
    obtain ⟨p, hp, hNp⟩ := h.exists_gt N
    let q : ℕ := ⌊(α * p)⌋₊
    have hq : q.Prime := hp.2
    refine ⟨q - 1, p, hNp, hp.1, ?_, ?_⟩
    · exact hq.coprime_factorial_of_lt (by have := hq.two_le; omega)
    · change q < (q - 1 + 1) ^ 2
      have hq2 := hq.two_le
      have he : q - 1 + 1 = q := by omega
      rw [he]
      nlinarith
  · intro h
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨M, p, hNp, hp, hc, hbound⟩ := h N
    have hpq : p ≤ ⌊(α * p)⌋₊ := by
      apply Nat.le_floor
      nlinarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg p]
    exact ⟨p, ⟨hp, prime_of_coprime_factorial_of_lt_sq
      (hp.two_le.trans hpq) hc hbound⟩, hNp⟩

/-- Arbitrarily rough composite outputs occur at prime indices for suitably
chosen irrational slopes. The slope depends on `M` and `N`; this is not a
disproof of Erdős 972. -/
theorem exists_irrational_rough_composite_output (M N : ℕ) :
    ∃ α > 1, Irrational α ∧ ∃ p : ℕ, N < p ∧ p.Prime ∧
      (⌊(α * p)⌋₊).Coprime M.factorial ∧ ¬ (⌊(α * p)⌋₊).Prime := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 1)
  obtain ⟨r, hrM, hr⟩ := Nat.exists_infinite_primes (max M p + 1)
  have hrp : p < r := by omega
  have hMr : M < r := by omega
  have hr2 := hr.two_le
  let q : ℕ := r ^ 2
  have hpq : p < q := by dsimp [q]; nlinarith
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqr : (p : ℝ) < q := by exact_mod_cast hpq
  have hinter : (q : ℝ) / p < ((q : ℝ) + 1) / p := by
    apply (div_lt_div_iff_of_pos_right hpr).mpr
    linarith
  obtain ⟨α, hi, hlow, hupp⟩ := exists_irrational_btwn hinter
  have hα : 1 < α := lt_trans ((lt_div_iff₀ hpr).mpr (by simpa using hqr)) hlow
  have hf : ⌊(α * p)⌋₊ = q := by
    apply (Nat.floor_eq_iff (mul_nonneg (by linarith) hpr.le)).mpr
    exact ⟨((div_lt_iff₀ hpr).mp hlow).le, (lt_div_iff₀ hpr).mp hupp⟩
  refine ⟨α, hα, hi, p, by omega, hp, ?_, ?_⟩
  · rw [hf]
    exact (hr.coprime_factorial_of_lt hMr).pow_left 2
  · rw [hf]
    exact Nat.Prime.not_prime_pow (by norm_num : 2 ≤ 2)

#print axioms prime_of_coprime_factorial_of_lt_sq
#print axioms infinite_iff_bounded_sieve_witnesses
#print axioms exists_irrational_rough_composite_output

#print axioms eventually_mem_primeSet_of_tendsto
#print axioms finite_primeSet_of_irrational_limit
#print axioms counterexample_criterion

#print axioms simultaneous_coprime_indices

#print axioms negation_iff_bounded_counterexample
#print axioms exists_irrational_initial_gap

#print axioms infinite_iff_prime_pairs
#print axioms primeSet_nat_eq_empty

end Explore972
