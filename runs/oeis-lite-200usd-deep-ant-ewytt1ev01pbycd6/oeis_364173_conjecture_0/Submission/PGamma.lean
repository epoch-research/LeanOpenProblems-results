import Mathlib

open Finset

namespace PGamma

/-- In `ZMod (p^k)` for an odd prime `p`, the only square roots of unity are `±1`. -/
lemma sq_eq_one_of_odd {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (k : ℕ) {x : ZMod (p ^ k)}
    (hx : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    left
    exact Subsingleton.elim _ _
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  -- integer representative
  set a : ℤ := (x.val : ℤ) with ha
  have hxa : ((a : ZMod (p ^ k))) = x := by
    rw [ha, Int.cast_natCast, ZMod.natCast_zmod_val]
  -- p^k ∣ (a-1)*(a+1)
  have hdvd : ((p : ℤ) ^ k) ∣ (a - 1) * (a + 1) := by
    have h0 : (((a - 1) * (a + 1) : ℤ) : ZMod (p ^ k)) = 0 := by
      push_cast
      rw [hxa]
      linear_combination hx
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ k)).mp h0
    rwa [Nat.cast_pow] at this
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp2 : ¬ (p : ℤ) ∣ (2 : ℤ) := by
    intro h
    have h2 : p ∣ 2 := by exact_mod_cast h
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  by_cases hd1 : (p : ℤ) ∣ (a - 1)
  · -- then p ∤ (a+1), so p^k ∣ (a-1), so x = 1
    have hd2 : ¬ (p : ℤ) ∣ (a + 1) := by
      intro h2
      apply hp2
      have : (p : ℤ) ∣ ((a + 1) - (a - 1)) := dvd_sub h2 hd1
      simpa using this
    have hk1 : ((p : ℤ) ^ k) ∣ (a - 1) :=
      hpZ.pow_dvd_of_dvd_mul_left k hd2 (by rw [mul_comm] at hdvd; exact hdvd)
    left
    have hz : ((a - 1 : ℤ) : ZMod (p ^ k)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]; exact hk1
    push_cast at hz
    rw [hxa] at hz
    exact sub_eq_zero.mp hz
  · -- p ∤ (a-1), so p^k ∣ (a+1), so x = -1
    have hk1 : ((p : ℤ) ^ k) ∣ (a + 1) :=
      hpZ.pow_dvd_of_dvd_mul_left k hd1 hdvd
    right
    have hz : ((a + 1 : ℤ) : ZMod (p ^ k)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]; exact hk1
    push_cast at hz
    rw [hxa] at hz
    exact add_eq_zero_iff_eq_neg.mp hz

/-- Units version: the only square roots of unity in `(ZMod (p^k))ˣ` are `±1`. -/
lemma units_sq_eq_one {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (k : ℕ)
    {a : (ZMod (p ^ k))ˣ} (ha : a ^ 2 = 1) : a = 1 ∨ a = -1 := by
  have h1 : ((a : ZMod (p ^ k))) ^ 2 = 1 := by
    have := congrArg (Units.val) ha
    push_cast at this
    simpa using this
  rcases sq_eq_one_of_odd hp hodd k h1 with h | h
  · left; exact Units.ext (by simpa using h)
  · right; exact Units.ext (by simpa using h)

/-- The product of all units of `ZMod (p^k)` (for `p` an odd prime) is `-1`. -/
lemma prod_units_eq_neg_one {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (k : ℕ) [NeZero (p ^ k)] :
    ∏ x : (ZMod (p ^ k))ˣ, (x : ZMod (p ^ k)) = -1 := by
  -- product of the units (as units) is -1
  have key : (∏ x ∈ (univ : Finset (ZMod (p ^ k))ˣ).erase (-1), x) = 1 := by
    apply prod_involution (fun x _ => x⁻¹)
    · intro a _; simp
    · intro a ha hne' heq
      apply hne'
      have hinv : a * a⁻¹ = 1 := mul_inv_cancel a
      rw [heq] at hinv
      have hsq : a ^ 2 = 1 := by rw [sq]; exact hinv
      rcases units_sq_eq_one hp hodd k hsq with h | h
      · exact h
      · exact absurd h (mem_erase.mp ha).1
    · intro a _; simp
    · intro a ha
      rw [mem_erase]
      refine ⟨?_, mem_univ _⟩
      intro hcontra
      exact (mem_erase.mp ha).1 (by rw [← inv_inv a, hcontra]; simp)
  have hU : ∏ x : (ZMod (p ^ k))ˣ, x = -1 := by
    rw [← insert_erase (mem_univ (-1 : (ZMod (p ^ k))ˣ)), prod_insert (notMem_erase _ _), key,
      mul_one]
  have := congrArg (Units.val) hU
  rw [Units.val_neg, Units.val_one] at this
  rw [← this, Units.coe_prod]

/-- **Generalized Wilson theorem for odd prime powers.**
The product of the residues `0 < j < p^k` with `p ∤ j`, taken in `ZMod (p^k)`, equals `-1`. -/
theorem wilson_prime_pow {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) {k : ℕ} (hk : 1 ≤ k) :
    ∏ j ∈ (range (p ^ k)).filter (fun j => ¬ p ∣ j), (j : ZMod (p ^ k)) = -1 := by
  have hne : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  rw [← prod_units_eq_neg_one hp hodd k]
  symm
  apply prod_bij (fun (x : (ZMod (p ^ k))ˣ) _ => ((x : ZMod (p ^ k)).val : ℕ))
  · -- image lands in the filtered range
    intro x _
    rw [mem_filter, mem_range]
    refine ⟨ZMod.val_lt _, ?_⟩
    intro hpv
    have hpk : p ∣ p ^ k := dvd_pow_self p (by omega)
    have hg := ZMod.val_coe_unit_coprime x
    have : p ∣ Nat.gcd ((x : ZMod (p ^ k)).val) (p ^ k) := Nat.dvd_gcd hpv hpk
    rw [hg] at this
    have := Nat.le_of_dvd one_pos this
    have h2 := hp.two_le
    omega
  · -- injectivity
    intro x₁ _ x₂ _ h
    have : ((x₁ : ZMod (p ^ k))) = ((x₂ : ZMod (p ^ k))) := ZMod.val_injective _ h
    exact Units.ext this
  · -- surjectivity
    intro j hj
    rw [mem_filter, mem_range] at hj
    obtain ⟨hjlt, hjp⟩ := hj
    have hcop : j.Coprime (p ^ k) := (((hp.coprime_iff_not_dvd).2 hjp).symm).pow_right k
    refine ⟨ZMod.unitOfCoprime j hcop, mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hjlt]
  · -- value compatibility
    intro x _
    rw [ZMod.natCast_zmod_val]

/-- Reindexing: a product over `range M` of a function of `(i : ZMod M)` equals the product
over all of `ZMod M`. -/
lemma prod_range_natCast_eq_univ {M : ℕ} [NeZero M] {R : Type*} [CommMonoid R]
    (h : ZMod M → R) : ∏ i ∈ range M, h (i : ZMod M) = ∏ y : ZMod M, h y := by
  symm
  apply prod_bij (fun (y : ZMod M) _ => y.val)
  · intro y _; rw [mem_range]; exact ZMod.val_lt y
  · intro y₁ _ y₂ _ hh; exact ZMod.val_injective _ hh
  · intro a ha
    rw [mem_range] at ha
    exact ⟨(a : ZMod M), mem_univ _, by rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha]⟩
  · intro y _; rw [ZMod.natCast_zmod_val]

/-- The product of the residues coprime to `p` in an interval `[n, n+p^k)` (taken in `ZMod (p^k)`)
equals `-1`. This is the shifted version of the generalized Wilson theorem. -/
lemma prod_Ico_filter_eq_neg_one {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) {k : ℕ} (hk : 1 ≤ k)
    [NeZero (p ^ k)] (n : ℕ) :
    ∏ j ∈ (Ico n (n + p ^ k)).filter (fun j => ¬ p ∣ j), (j : ZMod (p ^ k)) = -1 := by
  set M := p ^ k with hM
  haveI : NeZero M := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have hpk : p ∣ M := by rw [hM]; exact dvd_pow_self p (by omega)
  set h : ZMod M → ZMod M := fun y => if ¬ p ∣ y.val then y else 1 with hh
  have term_eq : ∀ j : ℕ, (if ¬ p ∣ j then (j : ZMod M) else 1) = h (j : ZMod M) := by
    intro j
    have hcond : (¬ p ∣ j) ↔ (¬ p ∣ (j : ZMod M).val) := by
      rw [ZMod.val_natCast]
      exact not_congr (Nat.dvd_mod_iff hpk).symm
    simp only [hh]
    exact if_congr hcond rfl rfl
  have huniv : ∏ y : ZMod M, h y = -1 := by
    rw [← prod_range_natCast_eq_univ h]
    rw [Finset.prod_congr rfl (fun j _ => (term_eq j).symm)]
    rw [← prod_filter]
    exact wilson_prime_pow hp hodd hk
  rw [prod_filter]
  rw [prod_Ico_eq_prod_range (fun j => if ¬ p ∣ j then (j : ZMod M) else 1) n (n + M)]
  simp only [Nat.add_sub_cancel_left]
  rw [Finset.prod_congr rfl (fun i _ => by rw [term_eq (n + i), Nat.cast_add])]
  rw [prod_range_natCast_eq_univ (fun y => h ((n : ZMod M) + y))]
  have hc := Equiv.prod_comp (Equiv.addLeft (n : ZMod M)) h
  simp only [Equiv.coe_addLeft] at hc
  rw [hc]
  exact huniv

/-! ### The p-adic Gamma function -/

section Padic

variable {p : ℕ} [hp : Fact p.Prime]

/-- The partial product `∏_{0<j<n, p∤j} j` in `ℤ_[p]`. -/
noncomputable def pgP (n : ℕ) : ℤ_[p] := ∏ j ∈ (range n).filter (fun j => ¬ p ∣ j), (j : ℤ_[p])

/-- Morita's approximating sequence `f(n) = (-1)^n ∏_{0<j<n, p∤j} j`. -/
noncomputable def pgf (n : ℕ) : ℤ_[p] := (-1) ^ n * pgP n

lemma toZModPow_pgf (k n : ℕ) :
    PadicInt.toZModPow (p := p) k (pgf n) =
      (-1) ^ n * ∏ j ∈ (range n).filter (fun j => ¬ p ∣ j), (j : ZMod (p ^ k)) := by
  unfold pgf pgP
  rw [map_mul, map_pow, map_neg, map_one, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [map_natCast]

/-- The key congruence: `f(n + p^k) ≡ f(n)` modulo `p^k` (as elements of `ZMod (p^k)`). -/
lemma pgf_toZModPow_add (hodd : p ≠ 2) (k n : ℕ) :
    PadicInt.toZModPow (p := p) k (pgf (n + p ^ k)) = PadicInt.toZModPow (p := p) k (pgf n) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · subst hk0
    have : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.pos.ne'⟩
  rw [toZModPow_pgf, toZModPow_pgf]
  -- split the range
  have hsplit : (range (n + p ^ k)).filter (fun j => ¬ p ∣ j)
      = (range n).filter (fun j => ¬ p ∣ j) ∪ (Ico n (n + p ^ k)).filter (fun j => ¬ p ∣ j) := by
    ext j
    simp only [mem_union, mem_filter, mem_range, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_or_ge j n with h | h
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨⟨h, h1⟩, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨⟨_, h1'⟩, h2⟩)
      · exact ⟨by omega, h2⟩
      · exact ⟨h1', h2⟩
  have hdisj : Disjoint ((range n).filter (fun j => ¬ p ∣ j))
      ((Ico n (n + p ^ k)).filter (fun j => ¬ p ∣ j)) := by
    apply Finset.disjoint_filter_filter
    rw [range_eq_Ico]
    exact Ico_disjoint_Ico_consecutive 0 n (n + p ^ k)
  rw [hsplit, prod_union hdisj, prod_Ico_filter_eq_neg_one hp.out hodd hk1 n]
  have hModd : Odd (p ^ k) := (hp.out.odd_of_ne_two hodd).pow
  rw [pow_add, Odd.neg_one_pow hModd]
  ring

/-- Iterated version of the congruence. -/
lemma pgf_toZModPow_add_mul (hodd : p ≠ 2) (k : ℕ) :
    ∀ (t n : ℕ), PadicInt.toZModPow (p := p) k (pgf (n + p ^ k * t)) = PadicInt.toZModPow (p := p) k (pgf n) := by
  intro t
  induction t with
  | zero => intro n; simp
  | succ t ih =>
    intro n
    have : n + p ^ k * (t + 1) = (n + p ^ k * t) + p ^ k := by ring
    rw [this, pgf_toZModPow_add hodd k, ih]

/-- If `a ≡ b (mod p^k)` (as naturals), then `f(a) ≡ f(b) (mod p^k)`. -/
lemma pgf_toZModPow_eq_of_cast (hodd : p ≠ 2) (k : ℕ) {a b : ℕ}
    (hcong : (a : ZMod (p ^ k)) = (b : ZMod (p ^ k))) :
    PadicInt.toZModPow (p := p) k (pgf a) = PadicInt.toZModPow (p := p) k (pgf b) := by
  have hmod : a ≡ b [MOD p ^ k] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcong
  rcases le_total b a with hba | hab
  · obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hba).mp hmod.symm
    rw [show a = b + p ^ k * t from by omega]
    exact pgf_toZModPow_add_mul hodd k t b
  · obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hab).mp hmod
    rw [show b = a + p ^ k * t from by omega]
    exact (pgf_toZModPow_add_mul hodd k t a).symm

/-- Uniform-continuity estimate: `|f(a) - f(b)|_p ≤ p^{-k}` whenever `a ≡ b (mod p^k)`. -/
lemma pgf_norm_sub_le (hodd : p ≠ 2) (k : ℕ) {a b : ℕ}
    (hcong : (a : ZMod (p ^ k)) = (b : ZMod (p ^ k))) :
    ‖pgf (p := p) a - pgf (p := p) b‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_sub, sub_eq_zero]
  exact pgf_toZModPow_eq_of_cast hodd k hcong

/-- `pgf` transported to the range of `Nat.cast`, used for the dense extension. -/
noncomputable def pgfS : (Set.range (Nat.cast : ℕ → ℤ_[p])) → ℤ_[p] :=
  fun y => pgf (Classical.choose y.2)

lemma pgfS_apply (m : ℕ) (hm : (Nat.cast m : ℤ_[p]) ∈ Set.range (Nat.cast : ℕ → ℤ_[p])) :
    pgfS ⟨(m : ℤ_[p]), hm⟩ = pgf m := by
  have hc : ((Classical.choose hm : ℕ) : ℤ_[p]) = (m : ℤ_[p]) := Classical.choose_spec hm
  have heq : Classical.choose hm = m := Nat.cast_injective hc
  simp only [pgfS]
  rw [heq]

lemma uniformContinuous_pgfS (hodd : p ≠ 2) :
    UniformContinuous (pgfS : (Set.range (Nat.cast : ℕ → ℤ_[p])) → ℤ_[p]) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-(k : ℤ)) :=
    zpow_pos (by exact_mod_cast hp.out.pos) _
  refine ⟨(p : ℝ) ^ (-(k : ℤ)), hpos, ?_⟩
  intro a b hab
  set m := Classical.choose a.2 with hm
  set m' := Classical.choose b.2 with hm'
  have ha : ((m : ℤ_[p])) = a.1 := Classical.choose_spec a.2
  have hb : ((m' : ℤ_[p])) = b.1 := Classical.choose_spec b.2
  -- translate the hypothesis distance
  rw [Subtype.dist_eq, dist_eq_norm, ← ha, ← hb] at hab
  have hle : ‖((m : ℤ_[p]) - (m' : ℤ_[p]))‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := le_of_lt hab
  have hcong : (m : ZMod (p ^ k)) = (m' : ZMod (p ^ k)) := by
    have h0 : PadicInt.toZModPow (p := p) k ((m : ℤ_[p]) - (m' : ℤ_[p])) = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
      exact hle
    rw [map_sub, map_natCast, map_natCast, sub_eq_zero] at h0
    exact h0
  -- conclude
  have : dist (pgfS a) (pgfS b) = ‖pgf (p := p) m - pgf (p := p) m'‖ := by
    rw [dist_eq_norm]; rfl
  rw [this]
  exact lt_of_le_of_lt (pgf_norm_sub_le hodd k hcong) hk

/-- **Morita's `p`-adic Gamma function** `Γ_p : ℤ_[p] → ℤ_[p]`, defined for odd `p` as the
continuous extension of `f(n) = (-1)^n ∏_{0<j<n, p∤j} j` from `ℕ` to `ℤ_[p]`. -/
noncomputable def padicGamma (x : ℤ_[p]) : ℤ_[p] :=
  Dense.extend PadicInt.denseRange_natCast pgfS x

/-- `Γ_p` agrees with the approximating sequence `f` at natural numbers. -/
theorem padicGamma_natCast (hodd : p ≠ 2) (m : ℕ) :
    padicGamma (m : ℤ_[p]) = pgf m := by
  have hx : (Nat.cast m : ℤ_[p]) ∈ Set.range (Nat.cast : ℕ → ℤ_[p]) := ⟨m, rfl⟩
  unfold padicGamma
  have hind : Dense.extend PadicInt.denseRange_natCast pgfS ((m : ℤ_[p])) = pgfS ⟨(m : ℤ_[p]), hx⟩ :=
    Dense.extend_of_ind PadicInt.denseRange_natCast (uniformContinuous_pgfS hodd) ⟨(m : ℤ_[p]), hx⟩
  rw [hind, pgfS_apply]

/-- `Γ_p` is continuous. -/
theorem continuous_padicGamma (hodd : p ≠ 2) :
    Continuous (padicGamma : ℤ_[p] → ℤ_[p]) := by
  unfold padicGamma
  exact (Dense.uniformContinuous_extend PadicInt.denseRange_natCast
    (uniformContinuous_pgfS hodd)).continuous

/-- Each `pgf m` is a unit in `ℤ_[p]`. -/
lemma isUnit_pgf (m : ℕ) : IsUnit (pgf (p := p) m) := by
  have hprod : (∏ j ∈ (range m).filter (fun j => ¬ p ∣ j), (j : ℤ_[p]))
      ∈ IsUnit.submonoid ℤ_[p] := by
    refine prod_mem (fun j hj => ?_)
    rw [mem_filter, mem_range] at hj
    show IsUnit (j : ℤ_[p])
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.out.coprime_iff_not_dvd.mpr hj.2
  have hu : IsUnit (∏ j ∈ (range m).filter (fun j => ¬ p ∣ j), (j : ℤ_[p])) := hprod
  exact (isUnit_one.neg.pow m).mul hu

/-- **`Γ_p(x)` is a unit** (equivalently `‖Γ_p(x)‖ = 1`) for every `x`. -/
theorem padicGamma_isUnit (hodd : p ≠ 2) (x : ℤ_[p]) : IsUnit (padicGamma x) := by
  rw [PadicInt.isUnit_iff]
  have hcont : Continuous (fun y => ‖padicGamma (p := p) y‖) :=
    continuous_norm.comp (continuous_padicGamma hodd)
  have key : (fun y => ‖padicGamma (p := p) y‖) = (fun _ => (1 : ℝ)) := by
    apply DenseRange.equalizer PadicInt.denseRange_natCast hcont continuous_const
    funext m
    simp only [Function.comp_apply]
    rw [padicGamma_natCast hodd, PadicInt.isUnit_iff.mp (isUnit_pgf m)]
  exact congrFun key x

/-- Recurrence for the partial product `P`. -/
lemma pgP_succ (m : ℕ) :
    pgP (p := p) (m + 1) = pgP (p := p) m * (if ¬ p ∣ m then (m : ℤ_[p]) else 1) := by
  unfold pgP
  rw [prod_filter, prod_filter, Finset.prod_range_succ]

open Classical in
/-- **Functional equation** of Morita's `p`-adic Gamma function:
`Γ_p(x+1) = (if ‖x‖ = 1 then -x else -1) · Γ_p(x)`. -/
theorem padicGamma_functional_eq (hodd : p ≠ 2) (x : ℤ_[p]) :
    padicGamma (x + 1) = (if ‖x‖ = 1 then -x else (-1 : ℤ_[p])) * padicGamma x := by
  -- the unit set `{‖x‖ = 1}` is clopen
  have hnorm_lt : ∀ y : ℤ_[p], ‖y‖ < 1 ↔ ‖y‖ ≤ (p : ℝ) ^ (-(1 : ℕ) : ℤ) := by
    intro y
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, pow_one, Ideal.mem_span_singleton,
      PadicInt.norm_lt_one_iff_dvd]
  have hset : {y : ℤ_[p] | ‖y‖ < 1} = Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(1 : ℕ) : ℤ)) := by
    ext y
    simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
    exact hnorm_lt y
  have hclopen_lt : IsClopen {y : ℤ_[p] | ‖y‖ < 1} := by
    rw [hset]
    exact IsUltrametricDist.isClopen_closedBall 0
      (zpow_pos (by exact_mod_cast hp.out.pos) _).ne'
  have hUeq : {y : ℤ_[p] | ‖y‖ = 1} = {y : ℤ_[p] | ‖y‖ < 1}ᶜ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    constructor
    · intro h; rw [h]
    · intro h; exact le_antisymm (PadicInt.norm_le_one y) h
  have hclopen : IsClopen {y : ℤ_[p] | ‖y‖ = 1} := by
    rw [hUeq]; exact hclopen_lt.compl
  -- continuity of both sides
  have hcont_if : Continuous (fun y : ℤ_[p] => if ‖y‖ = 1 then -y else (-1 : ℤ_[p])) := by
    apply Continuous.if _ continuous_neg continuous_const
    intro a ha
    rw [hclopen.frontier_eq] at ha
    exact absurd ha (Set.notMem_empty a)
  have hcontF : Continuous (fun y : ℤ_[p] => padicGamma (y + 1)) :=
    (continuous_padicGamma hodd).comp (continuous_id.add continuous_const)
  have hcontG : Continuous
      (fun y : ℤ_[p] => (if ‖y‖ = 1 then -y else (-1 : ℤ_[p])) * padicGamma y) :=
    hcont_if.mul (continuous_padicGamma hodd)
  -- equality on `ℕ`
  have hcond : ∀ m : ℕ, (‖(m : ℤ_[p])‖ = 1) ↔ (¬ p ∣ m) := by
    intro m
    rw [PadicInt.norm_natCast_eq_one_iff]
    exact hp.out.coprime_iff_not_dvd
  have key : (fun y : ℤ_[p] => padicGamma (y + 1))
      = (fun y : ℤ_[p] => (if ‖y‖ = 1 then -y else (-1 : ℤ_[p])) * padicGamma y) := by
    apply DenseRange.equalizer PadicInt.denseRange_natCast hcontF hcontG
    funext m
    simp only [Function.comp_apply]
    have e1 : (m : ℤ_[p]) + 1 = ((m + 1 : ℕ) : ℤ_[p]) := by push_cast; ring
    rw [e1, padicGamma_natCast hodd, padicGamma_natCast hodd]
    simp only [pgf]
    rw [pgP_succ]
    have hfac : (if ‖(m : ℤ_[p])‖ = 1 then (-(m : ℤ_[p])) else (-1 : ℤ_[p]))
        = -(if ¬ p ∣ m then (m : ℤ_[p]) else 1) := by
      by_cases hpm : p ∣ m
      · rw [if_neg (by rw [hcond]; exact not_not.mpr hpm), if_neg (not_not.mpr hpm)]
      · rw [if_pos ((hcond m).mpr hpm), if_pos hpm]
    rw [hfac]
    ring
  exact congrFun key x

end Padic

end PGamma

-- Axiom checks (main results)
#print axioms PGamma.wilson_prime_pow
#print axioms PGamma.pgf_norm_sub_le
#print axioms PGamma.padicGamma
#print axioms PGamma.padicGamma_natCast
#print axioms PGamma.padicGamma_functional_eq
#print axioms PGamma.padicGamma_isUnit
