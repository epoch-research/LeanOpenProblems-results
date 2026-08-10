import FormalConjectures.Util.ProblemImports

/-!
Proof of the supercongruence conjecture for OEIS A357569:
`a(p^r) ≡ a(p^{r-1}) (mod p^{3r+3})` for primes `p ≥ 3` and `r ≥ 2`,
where `a(n) = C(3n,n)^2 - 27·C(2n,n)`.

Strategy (all computations take place in `ℚ_p`): with `N = p^m`, `n = p^{m-1}`,
`S = {k ≤ N : p ∤ k}` and `B_t = ∏_{k∈S}(k + tN)`, one has the exact identities
`B₀·C(3N,N) = B₂·C(3n,n)` and `B₀·C(2N,N) = B₁·C(2n,n)`, so with
`β_t = B_t/B₀ = ∏_{k∈S}(1 + tN/k)` everything reduces to `p`-adic bounds on the
power sums `s_j = Σ_{k∈S} k^{-j}`.  These are obtained from:
* a multiplication-by-2 rearrangement argument giving `‖3 s₂‖, ‖15 s₄‖ ≤ p^{-m}`;
* reflection `k ↦ N - k` giving exact formulas for `2s₁ + N s₂` and `2s₃`;
* a quartic truncation `Fpoly` of the product `∏(1 + tN/k)` with ultrametric
  error control (a Newton-identity induction).
The heart of the matter is that in `F₂ - 3F₁ + 2` all terms of valuation
below `5m - 1` cancel, which yields the extra three powers of `p` beyond the
classical Jacobsthal-type bound.
-/

set_option linter.unusedSectionVars false

open Finset

namespace A357569

variable {p : ℕ} [hp : Fact p.Prime]

/-- `D p c x` means `‖x‖ ≤ p^{-c}`, i.e. `v_p(x) ≥ c`. -/
def D (p : ℕ) [Fact p.Prime] (c : ℤ) (x : ℚ_[p]) : Prop := ‖x‖ ≤ (p : ℝ) ^ (-c)

variable {c d : ℤ} {x y : ℚ_[p]}

lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

lemma p_pos : (0 : ℝ) < p := lt_trans one_pos one_lt_p

lemma D.mono (h : D p c x) (hle : d ≤ c) : D p d x :=
  h.trans <| zpow_le_zpow_right₀ one_lt_p.le (by omega)

lemma D.of_eq {c d : ℤ} {x y : ℚ_[p]} (h : D p c x) (hxy : x = y) (hcc : d ≤ c) : D p d y :=
  hxy ▸ (h.mono hcc)

lemma D_zero (c : ℤ) : D p c (0 : ℚ_[p]) := by
  simp only [D, norm_zero]
  positivity

lemma D.add (hx : D p c x) (hy : D p c y) : D p c (x + y) :=
  (Padic.nonarchimedean x y).trans (max_le hx hy)

lemma D.neg (hx : D p c x) : D p c (-x) := by simpa only [D, norm_neg] using hx

lemma D.sub (hx : D p c x) (hy : D p c y) : D p c (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

lemma D.mul (hx : D p c x) (hy : D p d y) : D p (c + d) (x * y) := by
  unfold D at *
  rw [norm_mul, neg_add, zpow_add₀ (ne_of_gt p_pos)]
  exact mul_le_mul hx hy (norm_nonneg y) (zpow_nonneg p_pos.le _)

lemma D.sum {ι : Type*} {s : Finset ι} {f : ι → ℚ_[p]}
    (h : ∀ i ∈ s, D p c (f i)) : D p c (∑ i ∈ s, f i) :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) h

lemma D_of_norm_le_one (h : ‖x‖ ≤ 1) : D p 0 x := by
  simpa only [D, neg_zero, zpow_zero] using h

lemma D_int (z : ℤ) : D p 0 (z : ℚ_[p]) := D_of_norm_le_one (Padic.norm_int_le_one z)

lemma D_nat (n : ℕ) : D p 0 (n : ℚ_[p]) := by
  simpa using D_int (p := p) (n : ℤ)

lemma D_one : D p 0 (1 : ℚ_[p]) := by simpa using D_nat 1

lemma norm_nat_unit {k : ℕ} (hk : ¬ p ∣ k) : ‖(k : ℚ_[p])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hk

lemma norm_int_unit {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) : ‖(z : ℚ_[p])‖ = 1 :=
  le_antisymm (Padic.norm_int_le_one z) <|
    le_of_not_gt fun hlt => hz (Padic.norm_intCast_lt_one_iff.mp hlt)

lemma D_inv_nat {k : ℕ} (hk : ¬ p ∣ k) : D p 0 ((k : ℚ_[p])⁻¹) :=
  D_of_norm_le_one <| by rw [norm_inv, norm_nat_unit hk]; norm_num

lemma D_p_pow (m : ℕ) : D p (m : ℤ) ((p : ℚ_[p]) ^ m) :=
  le_of_eq (Padic.norm_p_pow m)

lemma D.div_unit (hx : D p c x) {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) : D p c (x / (z : ℚ_[p])) := by
  unfold D at *
  rwa [norm_div, norm_int_unit hz, div_one]

lemma norm_int_ge_of_not_sq {z : ℤ} (hz : ¬ ((p : ℤ)^2 ∣ z)) : ((p:ℝ))⁻¹ ≤ ‖(z : ℚ_[p])‖ := by
  by_cases hdvd : (p : ℤ) ∣ z
  · obtain ⟨w, rfl⟩ := hdvd
    have hw : ¬ (p : ℤ) ∣ w := by
      intro hw
      exact hz (by calc ((p:ℤ))^2 = p * p := sq (p:ℤ) ▸ rfl
                      _ ∣ (p : ℤ) * w := mul_dvd_mul_left _ hw)
    have hcast : ((((p:ℤ)) * w : ℤ) : ℚ_[p]) = ((p:ℚ_[p])) * (w : ℚ_[p]) := by push_cast; ring
    rw [hcast, norm_mul, norm_int_unit hw, mul_one, Padic.norm_p]
  · rw [norm_int_unit hdvd]
    exact inv_le_one_of_one_le₀ one_lt_p.le



/-! ### The set S of units in [1, p^m] -/

/-- Integers in `[1, p^m]` not divisible by `p`. -/
def S (p m : ℕ) : Finset ℕ := (Finset.Ioc 0 (p^m)).filter (fun k => ¬ p ∣ k)

lemma mem_S {m k : ℕ} : k ∈ S p m ↔ (0 < k ∧ k ≤ p^m) ∧ ¬ p ∣ k := by
  simp [S, Finset.mem_filter, Finset.mem_Ioc]

lemma S_pos {m k : ℕ} (h : k ∈ S p m) : 0 < k := (mem_S.mp h).1.1

lemma S_le {m k : ℕ} (h : k ∈ S p m) : k ≤ p^m := (mem_S.mp h).1.2

lemma S_not_dvd {m k : ℕ} (h : k ∈ S p m) : ¬ p ∣ k := (mem_S.mp h).2

lemma S_lt {m k : ℕ} (hm : 1 ≤ m) (h : k ∈ S p m) : k < p^m := by
  rcases lt_or_eq_of_le (S_le h) with h' | h'
  · exact h'
  · exact absurd (h' ▸ dvd_pow_self p (by omega)) (S_not_dvd h)

lemma S_cast_ne {m k : ℕ} (h : k ∈ S p m) : (k : ℚ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (S_pos h).ne'

lemma S_refl_mem {m k : ℕ} (hm : 1 ≤ m) (h : k ∈ S p m) : p^m - k ∈ S p m := by
  have hlt := S_lt hm h
  refine mem_S.mpr ⟨⟨by omega, by omega⟩, fun hdvd => S_not_dvd h ?_⟩
  have hpm : p ∣ p^m := dvd_pow_self p (by omega)
  have : p ∣ p^m - (p^m - k) := Nat.dvd_sub hpm hdvd
  rwa [Nat.sub_sub_self (S_le h)] at this

lemma S_refl_cast {m k : ℕ} (h : k ∈ S p m) :
    ((p^m - k : ℕ) : ℚ_[p]) = (p : ℚ_[p])^m - (k : ℚ_[p]) := by
  push_cast [Nat.cast_sub (S_le h)]
  ring

lemma S_refl_refl {m k : ℕ} (h : k ∈ S p m) : p^m - (p^m - k) = k :=
  Nat.sub_sub_self (S_le h)

/-- Reflection `k ↦ p^m - k` preserves sums over `S`. -/
lemma sum_reflect {m : ℕ} (hm : 1 ≤ m) (F : ℕ → ℚ_[p]) :
    ∑ k ∈ S p m, F (p^m - k) = ∑ k ∈ S p m, F k := by
  apply Finset.sum_nbij' (fun k => p^m - k) (fun k => p^m - k)
  · intro a ha; exact S_refl_mem hm ha
  · intro a ha; exact S_refl_mem hm ha
  · intro a ha; exact S_refl_refl ha
  · intro a ha; exact S_refl_refl ha
  · intro a ha; rfl


/-! ### Doubling bijection -/

lemma coprime_two_pow {m : ℕ} (hp2 : p ≠ 2) : Nat.Coprime 2 (p^m) :=
  (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
    (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.out).mp h2).symm) |>.pow_right m

lemma not_dvd_two_mul {m k : ℕ} (hp2 : p ≠ 2) (h : k ∈ S p m) : ¬ p ∣ 2 * k := by
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp.out).mp hdvd with h2 | hk
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h2)
  · exact S_not_dvd h hk

lemma dbl_mem {m k : ℕ} (hp2 : p ≠ 2) (hm : 1 ≤ m) (h : k ∈ S p m) :
    (2 * k) % p^m ∈ S p m := by
  have hN : 0 < p^m := pow_pos hp.out.pos m
  have hnd : ¬ p ∣ 2 * k := not_dvd_two_mul hp2 h
  have hmod : ¬ p ∣ (2 * k) % p^m := by
    intro hdvd
    apply hnd
    have hsplit := Nat.div_add_mod (2 * k) (p^m)
    calc p ∣ p^m * (2 * k / p^m) + (2 * k) % p^m :=
          dvd_add ((dvd_pow_self p (by omega : m ≠ 0)).mul_right _) hdvd
      _ = 2 * k := hsplit
  exact mem_S.mpr ⟨⟨Nat.pos_of_ne_zero (fun h0 => hmod (h0 ▸ dvd_zero p)),
    (Nat.mod_lt _ hN).le⟩, hmod⟩


lemma dbl_injOn {m : ℕ} (hp2 : p ≠ 2) (hm : 1 ≤ m) :
    Set.InjOn (fun k => (2 * k) % p^m) (S p m) := by
  intro k1 h1 k2 h2 heq
  simp only at heq
  have hco : Nat.Coprime 2 (p^m) := coprime_two_pow hp2
  have hmodeq : k1 ≡ k2 [MOD p^m] :=
    Nat.ModEq.cancel_left_of_coprime (by simpa using hco) (heq : 2 * k1 ≡ 2 * k2 [MOD p^m])
  have e1 : k1 % p^m = k1 := Nat.mod_eq_of_lt (S_lt hm (by simpa using h1))
  have e2 : k2 % p^m = k2 := Nat.mod_eq_of_lt (S_lt hm (by simpa using h2))
  rwa [Nat.ModEq, e1, e2] at hmodeq

/-- Doubling mod `p^m` preserves sums over `S`. -/
lemma sum_dbl {m : ℕ} (hp2 : p ≠ 2) (hm : 1 ≤ m) (F : ℕ → ℚ_[p]) :
    ∑ k ∈ S p m, F ((2 * k) % p^m) = ∑ k ∈ S p m, F k := by
  have himg : (S p m).image (fun k => (2 * k) % p^m) = S p m := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      exact dbl_mem hp2 hm hk
    · rw [Finset.card_image_of_injOn (dbl_injOn hp2 hm)]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image (fun x hx y hy => dbl_injOn hp2 hm hx hy)]

/-! ### Power sums and tau sums -/

/-- Power sums of inverses: `ps p m j = Σ_{k ∈ S} k^{-j}`. -/
noncomputable def ps (p : ℕ) [Fact p.Prime] (m j : ℕ) : ℚ_[p] := ∑ k ∈ S p m, ((k : ℚ_[p])⁻¹)^j

/-- `tau p m i j = Σ_{k ∈ S} k^{-i} (p^m - k)^{-j}`. -/
noncomputable def tau (p : ℕ) [Fact p.Prime] (m i j : ℕ) : ℚ_[p] :=
  ∑ k ∈ S p m, ((k : ℚ_[p])⁻¹)^i * (((p : ℚ_[p])^m - (k : ℚ_[p]))⁻¹)^j

lemma D_zero_pow {x : ℚ_[p]} (h : D p 0 x) (n : ℕ) : D p 0 (x^n) := by
  have hx : ‖x‖ ≤ 1 := by simpa [D] using h
  apply D_of_norm_le_one
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg x) hx

lemma D_inv_S {m k : ℕ} (h : k ∈ S p m) : D p 0 ((k : ℚ_[p])⁻¹) := D_inv_nat (S_not_dvd h)

lemma D_rinv_S {m k : ℕ} (hm : 1 ≤ m) (h : k ∈ S p m) :
    D p 0 (((p : ℚ_[p])^m - (k : ℚ_[p]))⁻¹) := by
  rw [← S_refl_cast h]
  exact D_inv_nat (S_not_dvd (S_refl_mem hm h))

lemma rk_ne {m k : ℕ} (hm : 1 ≤ m) (h : k ∈ S p m) :
    (p : ℚ_[p])^m - (k : ℚ_[p]) ≠ 0 := by
  rw [← S_refl_cast h]
  exact S_cast_ne (S_refl_mem hm h)

lemma D_ps (m j : ℕ) : D p 0 (ps p m j) :=
  D.sum (fun k hk => D_zero_pow (D_inv_S hk) j)

lemma D_tau {m : ℕ} (hm : 1 ≤ m) (i j : ℕ) : D p 0 (tau p m i j) :=
  D.sum (fun k hk => by
    simpa using (D_zero_pow (D_inv_S hk) i).mul (D_zero_pow (D_rinv_S hm hk) j))

/-! ### Division helpers -/

lemma D.divn {c : ℤ} {x : ℚ_[p]} (hx : D p c x) {n : ℕ} (hn : ¬ p ∣ n) :
    D p c (x / (n : ℚ_[p])) := by
  have := hx.div_unit (z := (n:ℤ)) (by exact_mod_cast hn)
  simpa using this

lemma D.divn' {c : ℤ} {x : ℚ_[p]} (hx : D p c x) {n : ℕ} (hn : ¬ p^2 ∣ n) :
    D p (c - 1) (x / (n : ℚ_[p])) := by
  have hge : ((p:ℝ))⁻¹ ≤ ‖((n:ℤ) : ℚ_[p])‖ :=
    norm_int_ge_of_not_sq (by exact_mod_cast hn)
  have hnorm : ‖x / (n : ℚ_[p])‖ ≤ (p:ℝ)^(-c) / (p:ℝ)⁻¹ := by
    rw [norm_div]
    push_cast at hge
    exact div_le_div₀ (zpow_nonneg p_pos.le _) hx (inv_pos.mpr p_pos) hge
  refine hnorm.trans (le_of_eq ?_)
  rw [← zpow_neg_one (p:ℝ), ← zpow_sub₀ (ne_of_gt p_pos)]
  ring_nf

lemma not_sq_dvd_small (hp2 : p ≠ 2) {n : ℕ} (h0 : 0 < n) (hlt : n < 49)
    (h9 : ¬ 9 ∣ n) (h25 : ¬ 25 ∣ n) : ¬ p^2 ∣ n := by
  intro h
  have hple : p^2 ≤ n := Nat.le_of_dvd h0 h
  have hp2le : 2 ≤ p := hp.out.two_le
  have hp6 : p ≤ 6 := by nlinarith
  have hp3 : 3 ≤ p := by omega
  interval_cases p
  · exact h9 (by simpa using h)
  · exact absurd hp.out (by norm_num)
  · exact h25 (by simpa using h)
  · exact absurd hp.out (by norm_num)

lemma p_not_dvd_two (hp2 : p ≠ 2) : ¬ p ∣ 2 :=
  fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)

lemma D.half {c : ℤ} {x : ℚ_[p]} (hx : D p c x) (hp2 : p ≠ 2) : D p c (x / 2) := by
  have := hx.divn (n := 2) (p_not_dvd_two hp2)
  push_cast at this
  exact this

/-! ### Doubling argument: bounds on ps 2 and ps 4 -/

lemma D_shift_pow_sub {m k : ℕ} (j : ℕ) (hp2 : p ≠ 2) (hm : 1 ≤ m) (hk : k ∈ S p m) :
    D p m (((((2*k) % p^m : ℕ) : ℚ_[p])⁻¹)^j - (((2*k : ℕ) : ℚ_[p])⁻¹)^j) := by
  set a : ℕ := (2*k) % p^m with ha
  set b : ℕ := 2*k with hb
  have hia : ¬ p ∣ a := S_not_dvd (dbl_mem hp2 hm hk)
  have hib : ¬ p ∣ b := not_dvd_two_mul hp2 hk
  have ha0 : (a : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hia (h0 ▸ dvd_zero p))
  have hb0 : (b : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (fun h0 => hib (h0 ▸ dvd_zero p))
  have hsplit : (b : ℚ_[p]) = (p:ℚ_[p])^m * ((b / p^m : ℕ) : ℚ_[p]) + (a : ℚ_[p]) := by
    have hnat : p^m * (b / p^m) + b % p^m = b := Nat.div_add_mod b (p^m)
    calc (b : ℚ_[p]) = ((p^m * (b / p^m) + b % p^m : ℕ) : ℚ_[p]) := by rw [hnat]
      _ = (p:ℚ_[p])^m * ((b / p^m : ℕ) : ℚ_[p]) + (a : ℚ_[p]) := by push_cast; ring
  have hDab : D p m ((a:ℚ_[p]) - (b:ℚ_[p])) := by
    have heq : (a:ℚ_[p]) - (b:ℚ_[p]) = -((p:ℚ_[p])^m * ((b / p^m : ℕ) : ℚ_[p])) := by
      rw [hsplit]; ring
    rw [heq]
    exact (((D_p_pow m).mul (D_nat _)).mono (by omega)).neg
  have hDinv : D p m ((a:ℚ_[p])⁻¹ - (b:ℚ_[p])⁻¹) := by
    have heq : (a:ℚ_[p])⁻¹ - (b:ℚ_[p])⁻¹ = ((b:ℚ_[p]) - (a:ℚ_[p])) * ((a:ℚ_[p])⁻¹ * (b:ℚ_[p])⁻¹) := by
      field_simp
    rw [heq]
    have := (hDab.neg.mul ((D_inv_nat hia).mul (D_inv_nat hib))).mono (le_of_eq (by ring))
    simpa [neg_sub] using this
  have hgeom : ((a:ℚ_[p])⁻¹)^j - ((b:ℚ_[p])⁻¹)^j =
      ((a:ℚ_[p])⁻¹ - (b:ℚ_[p])⁻¹) * ∑ i ∈ Finset.range j, ((a:ℚ_[p])⁻¹)^i * ((b:ℚ_[p])⁻¹)^(j-1-i) := by
    rw [← geom_sum₂_mul]
    ring
  rw [hgeom]
  have hsum : D p 0 (∑ i ∈ Finset.range j, ((a:ℚ_[p])⁻¹)^i * ((b:ℚ_[p])⁻¹)^(j-1-i)) :=
    D.sum (fun i _ => by
      simpa using (D_zero_pow (D_inv_nat hia) i).mul (D_zero_pow (D_inv_nat hib) (j-1-i)))
  simpa using hDinv.mul hsum

lemma D_two_pow_sub_one_mul_ps (j : ℕ) {m : ℕ} (hp2 : p ≠ 2) (hm : 1 ≤ m) :
    D p m (((2:ℚ_[p])^j - 1) * ps p m j) := by
  have h1 : ∑ k ∈ S p m, ((((2*k) % p^m : ℕ):ℚ_[p])⁻¹)^j = ps p m j :=
    sum_dbl hp2 hm (fun k => ((k:ℚ_[p])⁻¹)^j)
  have h2 : ∑ k ∈ S p m, (((2*k : ℕ):ℚ_[p])⁻¹)^j = ((2:ℚ_[p])⁻¹)^j * ps p m j := by
    rw [ps, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    rw [mul_inv, mul_pow]
  have hDsum : D p m (ps p m j - ((2:ℚ_[p])⁻¹)^j * ps p m j) := by
    rw [← h2, ← h1, ← Finset.sum_sub_distrib]
    exact D.sum (fun k hk => D_shift_pow_sub j hp2 hm hk)
  have h2j : D p 0 ((2:ℚ_[p])^j) :=
    D_zero_pow (by simpa using D_nat (p := p) 2) j
  have := h2j.mul hDsum
  have h2ne : (2:ℚ_[p]) ≠ 0 := two_ne_zero
  have heq : (2:ℚ_[p])^j * (ps p m j - ((2:ℚ_[p])⁻¹)^j * ps p m j) =
      ((2:ℚ_[p])^j - 1) * ps p m j := by
    rw [mul_sub, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow, one_mul,
      sub_mul, one_mul]
  rw [heq] at this
  simpa using this

lemma D_three_mul_ps2 {m : ℕ} (hp2 : p ≠ 2) (hm : 1 ≤ m) : D p m (3 * ps p m 2) := by
  have := D_two_pow_sub_one_mul_ps 2 hp2 hm
  norm_num at this
  exact this

lemma D_fifteen_mul_ps4 {m : ℕ} (hp2 : p ≠ 2) (hm : 1 ≤ m) : D p m (15 * ps p m 4) := by
  have := D_two_pow_sub_one_mul_ps 4 hp2 hm
  norm_num at this
  exact this

lemma D_ps2 {m : ℕ} (hp2 : p ≠ 2) (hm : 1 ≤ m) : D p ((m:ℤ) - 1) (ps p m 2) := by
  have h := (D_three_mul_ps2 hp2 hm).divn' (n := 3)
    (not_sq_dvd_small hp2 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  push_cast at h
  rwa [mul_div_cancel_left₀ _ (by norm_num : (3:ℚ_[p]) ≠ 0)] at h

lemma D_ps4 {m : ℕ} (hp2 : p ≠ 2) (hm : 1 ≤ m) : D p ((m:ℤ) - 1) (ps p m 4) := by
  have h := (D_fifteen_mul_ps4 hp2 hm).divn' (n := 15)
    (not_sq_dvd_small hp2 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  push_cast at h
  rwa [mul_div_cancel_left₀ _ (by norm_num : (15:ℚ_[p]) ≠ 0)] at h

/-! ### Norm of powers of N = p^m -/

lemma D_Npow (m j : ℕ) : D p ((j*m : ℕ) : ℤ) (((p:ℚ_[p])^m)^j) := by
  unfold D
  rw [norm_pow, Padic.norm_p_pow]
  rw [← zpow_natCast ((p:ℝ)^(-(m:ℤ))) j, ← zpow_mul]
  apply le_of_eq
  congr 1
  push_cast
  ring

/-! ### Reflection identities -/

lemma sum_refl_inv_pow {m : ℕ} (hm : 1 ≤ m) (j : ℕ) :
    ∑ k ∈ S p m, (((p:ℚ_[p])^m - (k:ℚ_[p]))⁻¹)^j = ps p m j := by
  rw [ps, ← sum_reflect hm (fun k => ((k:ℚ_[p])⁻¹)^j)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [S_refl_cast hk]

/-- H1: `2 s₁ + N s₂ = N² τ₂₁`. -/
lemma H1 {m : ℕ} (hm : 1 ≤ m) :
    2 * ps p m 1 + (p:ℚ_[p])^m * ps p m 2 = ((p:ℚ_[p])^m)^2 * tau p m 2 1 := by
  have h2 : 2 * ps p m 1 = ps p m 1 + ∑ k ∈ S p m, (((p:ℚ_[p])^m - (k:ℚ_[p]))⁻¹)^1 := by
    rw [sum_refl_inv_pow hm 1, two_mul]
  rw [h2, ps, ps, tau, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 := S_cast_ne hk
  have hr0 := rk_ne hm hk
  field_simp
  ring

/-- H2: `2 s₃ + 3 N s₄ + 3 N² τ₃₂ = 3 N² τ₄₁ + N³ τ₃₃`. -/
lemma H2 {m : ℕ} (hm : 1 ≤ m) :
    2 * ps p m 3 + 3 * (p:ℚ_[p])^m * ps p m 4 + 3 * ((p:ℚ_[p])^m)^2 * tau p m 3 2 =
      3 * ((p:ℚ_[p])^m)^2 * tau p m 4 1 + ((p:ℚ_[p])^m)^3 * tau p m 3 3 := by
  have h2 : 2 * ps p m 3 = ps p m 3 + ∑ k ∈ S p m, (((p:ℚ_[p])^m - (k:ℚ_[p]))⁻¹)^3 := by
    rw [sum_refl_inv_pow hm 3, two_mul]
  rw [h2, ps, ps, tau, tau, tau, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 := S_cast_ne hk
  have hr0 := rk_ne hm hk
  field_simp
  ring

/-- Hu: `τ₂₁ + s₃ + N s₄ = N² τ₄₁`. -/
lemma Hu {m : ℕ} (hm : 1 ≤ m) :
    tau p m 2 1 + ps p m 3 + (p:ℚ_[p])^m * ps p m 4 = ((p:ℚ_[p])^m)^2 * tau p m 4 1 := by
  rw [ps, ps, tau, tau, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 := S_cast_ne hk
  have hr0 := rk_ne hm hk
  field_simp
  ring

/-! ### Derived bounds on power sums -/

lemma D_ps3_div3 {m : ℕ} (hp2 : p ≠ 2) (hm : 1 ≤ m) :
    D p (2*(m:ℤ) - 1) (ps p m 3 / 3) := by
  have hkey : ps p m 3 / 3 =
      (-( (p:ℚ_[p])^m * ps p m 4) + ((p:ℚ_[p])^m)^2 * (tau p m 4 1 - tau p m 3 2)
        + ((p:ℚ_[p])^m)^3 * (tau p m 3 3 / 3)) / 2 := by
    have h := H2 (p := p) hm
    linear_combination (1/6 : ℚ_[p]) * h
  rw [hkey]
  have t1 : D p (2*(m:ℤ) - 1) (-((p:ℚ_[p])^m * ps p m 4)) := by
    have := (D_p_pow m).mul (D_ps4 hp2 hm)
    exact (this.mono (by omega)).neg
  have t2 : D p (2*(m:ℤ) - 1) (((p:ℚ_[p])^m)^2 * (tau p m 4 1 - tau p m 3 2)) := by
    have := (D_Npow (p := p) m 2).mul ((D_tau hm 4 1).sub (D_tau hm 3 2))
    exact this.mono (by push_cast; omega)
  have t3 : D p (2*(m:ℤ) - 1) (((p:ℚ_[p])^m)^3 * (tau p m 3 3 / 3)) := by
    have h33 : D p (0 - 1) (tau p m 3 3 / (3:ℚ_[p])) := by
      have := (D_tau hm 3 3).divn' (n := 3)
        (not_sq_dvd_small hp2 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      simpa using this
    have := (D_Npow (p := p) m 3).mul h33
    exact this.mono (by push_cast; omega)
  exact ((t1.add t2).add t3).half hp2

lemma D_ps3 {m : ℕ} (hp2 : p ≠ 2) (hm : 1 ≤ m) : D p (2*(m:ℤ) - 1) (ps p m 3) := by
  have h := (D_nat (p := p) 3).mul (D_ps3_div3 hp2 hm)
  have heq : ((3:ℕ):ℚ_[p]) * (ps p m 3 / 3) = ps p m 3 := by
    push_cast
    rw [mul_div_cancel₀]
    norm_num
  rw [heq] at h
  exact h.mono (by omega)

lemma D_tau21 {m : ℕ} (hp2 : p ≠ 2) (hm : 1 ≤ m) : D p (2*(m:ℤ) - 1) (tau p m 2 1) := by
  have hkey : tau p m 2 1 =
      ((p:ℚ_[p])^m)^2 * tau p m 4 1 - ps p m 3 - (p:ℚ_[p])^m * ps p m 4 := by
    linear_combination Hu (p := p) hm
  rw [hkey]
  have t1 := (D_Npow (p := p) m 2).mul (D_tau hm 4 1)
  have t2 := D_ps3 hp2 hm
  have t3 := (D_p_pow m).mul (D_ps4 hp2 hm)
  exact ((t1.mono (by push_cast; omega)).sub t2).sub (t3.mono (by omega))

lemma D_ps1 {m : ℕ} (hp2 : p ≠ 2) (hm : 1 ≤ m) : D p (2*(m:ℤ) - 1) (ps p m 1) := by
  have hkey : ps p m 1 =
      (((p:ℚ_[p])^m)^2 * tau p m 2 1 - (p:ℚ_[p])^m * ps p m 2) / 2 := by
    have h := H1 (p := p) hm
    linear_combination (1/2 : ℚ_[p]) * h
  rw [hkey]
  have t1 := (D_Npow (p := p) m 2).mul (D_tau21 hp2 hm)
  have t2 := (D_p_pow m).mul (D_ps2 hp2 hm)
  have := (t1.mono (show 2*(m:ℤ)-1 ≤ ((2*m:ℕ):ℤ) + (2*(m:ℤ)-1) by push_cast; omega)).sub
    (t2.mono (by omega))
  exact this.half hp2

/-! ### Product approximation -/

/-- Degree-4 truncation of `∏(1+f)` in terms of power sums (Newton). -/
noncomputable def Fpoly (a b c d : ℚ_[p]) : ℚ_[p] :=
  1 + a + (a^2 - b)/2 + (a^3 - 3*a*b + 2*c)/6 + (a^4 - 6*a^2*b + 3*b^2 + 8*a*c - 6*d)/24

lemma Fpoly_shift (a b c d x : ℚ_[p]) :
    (1 + x) * Fpoly a b c d - Fpoly (x + a) (x^2 + b) (x^3 + c) (x^4 + d) =
      x * ((a^4 - 6*a^2*b + 3*b^2 + 8*a*c - 6*d)/24) := by
  unfold Fpoly
  ring

lemma not_dvd_pow_two (hp2 : p ≠ 2) (k : ℕ) : ¬ p ∣ 2^k :=
  fun h => p_not_dvd_two hp2 (hp.out.dvd_of_dvd_pow h)

lemma D_E4 (hp2 : p ≠ 2) {c : ℤ} {a b c' d : ℚ_[p]}
    (ha : D p c a) (hb : D p (2*c) b) (hc' : D p (3*c) c') (hd : D p (4*c) d) :
    D p (4*c - 1) ((a^4 - 6*a^2*b + 3*b^2 + 8*a*c' - 6*d)/24) := by
  have h1 : D p (4*c) (a^4) :=
    (((ha.mul ha).mul ha).mul ha).of_eq (by ring) (by omega)
  have h2 : D p (4*c) (6*a^2*b) :=
    ((D_nat (p := p) 6).mul ((ha.mul ha).mul hb)).of_eq (by push_cast; ring) (by omega)
  have h3 : D p (4*c) (3*b^2) :=
    ((D_nat (p := p) 3).mul (hb.mul hb)).of_eq (by push_cast; ring) (by omega)
  have h4 : D p (4*c) (8*a*c') :=
    ((D_nat (p := p) 8).mul (ha.mul hc')).of_eq (by push_cast; ring) (by omega)
  have h5 : D p (4*c) (6*d) :=
    ((D_nat (p := p) 6).mul hd).of_eq (by push_cast; ring) (by omega)
  have hsum : D p (4*c) (a^4 - 6*a^2*b + 3*b^2 + 8*a*c' - 6*d) :=
    (((h1.sub h2).add h3).add h4).sub h5
  have := hsum.divn' (n := 24)
    (not_sq_dvd_small hp2 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  push_cast at this
  exact this

/-- Key product approximation: if all `‖f i‖ ≤ p^{-c}` then
`∏ (1 + f i)` equals `Fpoly` of the power sums up to `p^{-(5c-1)}`. -/
lemma prod_approx {ι : Type*} [DecidableEq ι] (hp2 : p ≠ 2) {c : ℤ} (hc : 1 ≤ c)
    (A : Finset ι) (f : ι → ℚ_[p]) (hf : ∀ i ∈ A, D p c (f i)) :
    D p (5*c - 1) (∏ i ∈ A, (1 + f i) -
      Fpoly (∑ i ∈ A, f i) (∑ i ∈ A, (f i)^2) (∑ i ∈ A, (f i)^3) (∑ i ∈ A, (f i)^4)) := by
  induction A using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    have : Fpoly (p := p) 0 0 0 0 = 1 := by unfold Fpoly; ring
    rw [this, sub_self]
    exact D_zero _
  | insert i₀ A hi₀ IH =>
    rw [Finset.prod_insert hi₀, Finset.sum_insert hi₀, Finset.sum_insert hi₀,
      Finset.sum_insert hi₀, Finset.sum_insert hi₀]
    set x := f i₀ with hx
    set a := ∑ i ∈ A, f i
    set b := ∑ i ∈ A, (f i)^2
    set c'' := ∑ i ∈ A, (f i)^3
    set d := ∑ i ∈ A, (f i)^4
    set P := ∏ i ∈ A, (1 + f i)
    have hIH := IH (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hxD : D p c x := hf i₀ (Finset.mem_insert_self i₀ A)
    have expand : (1 + x) * P - Fpoly (x + a) (x^2 + b) (x^3 + c'') (x^4 + d) =
        (1 + x) * (P - Fpoly a b c'' d) +
          x * ((a^4 - 6*a^2*b + 3*b^2 + 8*a*c'' - 6*d)/24) := by
      have hs := Fpoly_shift (p := p) a b c'' d x
      linear_combination hs
    rw [expand]
    have hD1x : D p 0 (1 + x) := D_one.add (hxD.mono (by omega))
    have hDa : D p c a := D.sum (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hDb : D p (2*c) b := D.sum (fun i hi => by
      have := (hf i (Finset.mem_insert_of_mem hi)).mul (hf i (Finset.mem_insert_of_mem hi))
      have heq : f i * f i = (f i)^2 := by ring
      rw [heq] at this
      exact this.mono (by omega))
    have hDc : D p (3*c) c'' := D.sum (fun i hi => by
      have h1 := hf i (Finset.mem_insert_of_mem hi)
      have := (h1.mul h1).mul h1
      have heq : f i * f i * f i = (f i)^3 := by ring
      rw [heq] at this
      exact this.mono (by omega))
    have hDd : D p (4*c) d := D.sum (fun i hi => by
      have h1 := hf i (Finset.mem_insert_of_mem hi)
      have := ((h1.mul h1).mul h1).mul h1
      have heq : f i * f i * f i * f i = (f i)^4 := by ring
      rw [heq] at this
      exact this.mono (by omega))
    have hterm1 : D p (5*c - 1) ((1 + x) * (P - Fpoly a b c'' d)) := by
      have := hD1x.mul hIH
      exact this.mono (by omega)
    have hterm2 : D p (5*c - 1)
        (x * ((a^4 - 6*a^2*b + 3*b^2 + 8*a*c'' - 6*d)/24)) := by
      have := hxD.mul (D_E4 hp2 hDa hDb hDc hDd)
      exact this.mono (by omega)
    exact hterm1.add hterm2

/-! ### The beta products -/

/-- `beta p m t = ∏_{k ∈ S} (1 + t p^m / k)`. -/
noncomputable def beta (p : ℕ) [Fact p.Prime] (m t : ℕ) : ℚ_[p] :=
  ∏ k ∈ S p m, (1 + (t:ℚ_[p]) * (p:ℚ_[p])^m * ((k:ℚ_[p]))⁻¹)

lemma D_beta_approx (hp2 : p ≠ 2) {m : ℕ} (hm : 1 ≤ m) (t : ℕ) :
    D p (5*(m:ℤ) - 1) (beta p m t - Fpoly
      ((t:ℚ_[p]) * (p:ℚ_[p])^m * ps p m 1)
      ((t:ℚ_[p])^2 * ((p:ℚ_[p])^m)^2 * ps p m 2)
      ((t:ℚ_[p])^3 * ((p:ℚ_[p])^m)^3 * ps p m 3)
      ((t:ℚ_[p])^4 * ((p:ℚ_[p])^m)^4 * ps p m 4)) := by
  have happrox := prod_approx hp2 (c := (m:ℤ)) (by exact_mod_cast hm) (S p m)
    (fun k => (t:ℚ_[p]) * (p:ℚ_[p])^m * ((k:ℚ_[p]))⁻¹)
    (fun k hk => (((D_nat t).mul (D_p_pow m)).mul (D_inv_S hk)).of_eq rfl (by omega))
  have hsum : ∀ j, ∑ k ∈ S p m, ((t:ℚ_[p]) * (p:ℚ_[p])^m * ((k:ℚ_[p]))⁻¹)^j
      = (t:ℚ_[p])^j * ((p:ℚ_[p])^m)^j * ps p m j := by
    intro j
    rw [ps, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow, mul_pow]
  have hsum1 : ∑ k ∈ S p m, (t:ℚ_[p]) * (p:ℚ_[p])^m * ((k:ℚ_[p]))⁻¹
      = (t:ℚ_[p]) * (p:ℚ_[p])^m * ps p m 1 := by
    have := hsum 1
    simpa using this
  rw [hsum1, hsum 2, hsum 3, hsum 4] at happrox
  exact happrox

/-! ### Factorial decomposition -/

/-- `B p m t = ∏_{k ∈ S} (k + t p^m)` as a natural number. -/
def B (p m t : ℕ) : ℕ := ∏ k ∈ S p m, (k + t * p^m)

lemma B_pos (m t : ℕ) : 0 < B p m t :=
  Finset.prod_pos (fun k hk => by have := S_pos hk; omega)

lemma B_zero (m : ℕ) : B p m 0 = ∏ k ∈ S p m, k := by
  unfold B
  simp

lemma cast_B_eq (m t : ℕ) : ((B p m t : ℕ) : ℚ_[p]) =
    ((B p m 0 : ℕ) : ℚ_[p]) * beta p m t := by
  rw [B_zero, B, beta, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  have hk0 := S_cast_ne hk
  push_cast
  field_simp

lemma cast_B0_ne (m : ℕ) : ((B p m 0 : ℕ) : ℚ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (B_pos m 0).ne'

lemma beta_ne (m t : ℕ) : beta p m t ≠ 0 := by
  intro h0
  have := cast_B_eq (p := p) m t
  rw [h0, mul_zero] at this
  exact (Nat.cast_ne_zero.mpr (B_pos m t).ne' : ((B p m t : ℕ):ℚ_[p]) ≠ 0) this

lemma prod_Ioc_eq_factorial (n : ℕ) : ∏ k ∈ Finset.Ioc 0 n, k = Nat.factorial n := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [Finset.prod_Ioc_succ_top (Nat.zero_le _), IH, Nat.factorial_succ, mul_comm]

/-- Factorial decomposition: `M! = p^{M/p} (M/p)! ∏_{k ≤ M, p ∤ k} k`. -/
lemma factorial_split (M : ℕ) :
    Nat.factorial M = p ^ (M / p) * Nat.factorial (M / p) *
      ∏ k ∈ (Finset.Ioc 0 M).filter (fun k => ¬ p ∣ k), k := by
  have hfact : ∏ k ∈ Finset.Ioc 0 M, k = Nat.factorial M := prod_Ioc_eq_factorial M
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Finset.Ioc 0 M)
    (fun k => p ∣ k) (fun k => k)
  have hmult : ∏ k ∈ (Finset.Ioc 0 M).filter (fun k => p ∣ k), k
      = p ^ (M / p) * Nat.factorial (M / p) := by
    have himg : (Finset.Ioc 0 M).filter (fun k => p ∣ k)
        = (Finset.Ioc 0 (M / p)).image (fun j => p * j) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hx0, hxM⟩, j, rfl⟩
        refine ⟨j, ⟨Nat.pos_of_ne_zero (fun h0 => by simp [h0] at hx0), ?_⟩, rfl⟩
        exact (Nat.le_div_iff_mul_le hp.out.pos).mpr (by rw [mul_comm]; exact hxM)
      · rintro ⟨j, ⟨hj0, hjM⟩, rfl⟩
        refine ⟨⟨Nat.mul_pos hp.out.pos hj0, ?_⟩, dvd_mul_right p j⟩
        have := (Nat.le_div_iff_mul_le hp.out.pos).mp hjM
        rw [mul_comm p j]
        exact this
    rw [himg, Finset.prod_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.out.pos h)]
    rw [Finset.prod_mul_distrib, Finset.prod_const]
    congr 1
    · congr 1
      simp [Nat.card_Ioc]
    · exact prod_Ioc_eq_factorial (M/p)
  calc Nat.factorial M = ∏ k ∈ Finset.Ioc 0 M, k := hfact.symm
    _ = (∏ k ∈ (Finset.Ioc 0 M).filter (fun k => p ∣ k), k) *
        ∏ k ∈ (Finset.Ioc 0 M).filter (fun k => ¬ p ∣ k), k := hsplit.symm
    _ = p ^ (M / p) * Nat.factorial (M / p) *
        ∏ k ∈ (Finset.Ioc 0 M).filter (fun k => ¬ p ∣ k), k := by
        rw [hmult]

/-- Splitting the unit product over `[1, c p^m]` into `c` blocks. -/
lemma prod_units_split {m : ℕ} (hm : 1 ≤ m) (c : ℕ) :
    ∏ k ∈ (Finset.Ioc 0 (c * p^m)).filter (fun k => ¬ p ∣ k), k
      = ∏ t ∈ Finset.range c, B p m t := by
  induction c with
  | zero => simp
  | succ c IH =>
    have hpm : 0 < p^m := pow_pos hp.out.pos m
    have hunion : Finset.Ioc 0 ((c+1) * p^m)
        = Finset.Ioc 0 (c * p^m) ∪ Finset.Ioc (c * p^m) ((c+1) * p^m) := by
      rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by nlinarith)]
    have hdisj : Disjoint ((Finset.Ioc 0 (c * p^m)).filter (fun k => ¬ p ∣ k))
        ((Finset.Ioc (c * p^m) ((c+1) * p^m)).filter (fun k => ¬ p ∣ k)) := by
      apply Finset.disjoint_filter_filter
      exact Finset.Ioc_disjoint_Ioc_of_le le_rfl
    have hpd : p ∣ c * p^m := Dvd.dvd.mul_left (dvd_pow_self p (by omega)) c
    have hblock : ∏ k ∈ (Finset.Ioc (c * p^m) ((c+1) * p^m)).filter (fun k => ¬ p ∣ k), k
        = B p m c := by
      have hshift : Finset.Ioc (c * p^m) ((c+1) * p^m)
          = (Finset.Ioc 0 (p^m)).image (fun k => k + c * p^m) := by
        rw [show (fun k => k + c * p^m) = (· + c * p^m) from rfl,
          Finset.image_add_right_Ioc]
        congr 1 <;> ring
      have hdvd_iff : ∀ x : ℕ, (p ∣ x + c * p^m) ↔ p ∣ x := by
        intro x
        rw [add_comm]
        exact Nat.dvd_add_right hpd
      rw [hshift, Finset.filter_image]
      have hfc : Finset.filter (fun a => ¬ p ∣ (a + c * p^m)) (Finset.Ioc 0 (p^m))
          = S p m := by
        unfold S
        apply Finset.filter_congr
        intro x _
        simp [hdvd_iff x]
      rw [hfc, Finset.prod_image (fun a _ b _ h => by omega)]
      rfl
    rw [hunion, Finset.filter_union, Finset.prod_union hdisj, IH, hblock,
      Finset.prod_range_succ]

/-! ### Choose ratios -/

lemma factorial_split_cast {m : ℕ} (hm : 1 ≤ m) (c : ℕ) :
    ((Nat.factorial (c * p^m) : ℕ) : ℚ_[p]) =
      (p:ℚ_[p])^(c * p^(m-1)) * (Nat.factorial (c * p^(m-1)) : ℚ_[p]) *
        ∏ t ∈ Finset.range c, ((B p m t : ℕ) : ℚ_[p]) := by
  have hdiv : (c * p^m) / p = c * p^(m-1) := by
    conv_lhs => rw [show p^m = p^(m-1) * p by rw [← pow_succ]; congr 1; omega]
    rw [← mul_assoc, Nat.mul_div_cancel _ hp.out.pos]
  have h := factorial_split (p := p) (c * p^m)
  rw [prod_units_split hm c, hdiv] at h
  rw [h]
  push_cast
  ring

lemma cast_fact_pm {m : ℕ} (hm : 1 ≤ m) :
    ((Nat.factorial (p^m) : ℕ) : ℚ_[p]) =
      (p:ℚ_[p])^(p^(m-1)) * (Nat.factorial (p^(m-1)) : ℚ_[p]) * ((B p m 0 : ℕ) : ℚ_[p]) := by
  have h := factorial_split_cast (p := p) hm 1
  simpa using h

lemma cast_fact_2pm {m : ℕ} (hm : 1 ≤ m) :
    ((Nat.factorial (2 * p^m) : ℕ) : ℚ_[p]) =
      (p:ℚ_[p])^(2 * p^(m-1)) * (Nat.factorial (2 * p^(m-1)) : ℚ_[p]) *
        (((B p m 0 : ℕ) : ℚ_[p]) * (((B p m 0 : ℕ) : ℚ_[p]) * beta p m 1)) := by
  have h := factorial_split_cast (p := p) hm 2
  rw [show Finset.range 2 = {0, 1} by rfl] at h
  rw [Finset.prod_insert (by norm_num), Finset.prod_singleton] at h
  rw [h, cast_B_eq m 1]

lemma cast_fact_3pm {m : ℕ} (hm : 1 ≤ m) :
    ((Nat.factorial (3 * p^m) : ℕ) : ℚ_[p]) =
      (p:ℚ_[p])^(3 * p^(m-1)) * (Nat.factorial (3 * p^(m-1)) : ℚ_[p]) *
        (((B p m 0 : ℕ) : ℚ_[p]) * (((B p m 0 : ℕ) : ℚ_[p]) * beta p m 1) *
          (((B p m 0 : ℕ) : ℚ_[p]) * beta p m 2)) := by
  have h := factorial_split_cast (p := p) hm 3
  rw [show Finset.range 3 = {0, 1, 2} by rfl] at h
  rw [Finset.prod_insert (by norm_num), Finset.prod_insert (by norm_num),
    Finset.prod_singleton] at h
  rw [h, cast_B_eq m 1, cast_B_eq m 2]
  ring

lemma cast_choose_mul {c : ℕ} (hc : 1 ≤ c) (n : ℕ) :
    (((c * n).choose n : ℕ) : ℚ_[p]) * (Nat.factorial n : ℚ_[p]) *
      (Nat.factorial ((c-1) * n) : ℚ_[p]) = (Nat.factorial (c * n) : ℚ_[p]) := by
  have hle : n ≤ c * n := by nlinarith
  have h := Nat.choose_mul_factorial_mul_factorial hle
  have h2 : c * n - n = (c-1) * n := by
    cases c with
    | zero => omega
    | succ c => simp [Nat.succ_mul]
  rw [h2] at h
  exact_mod_cast congrArg (fun z : ℕ => (z : ℚ_[p])) h

/-- The fundamental recursion: `C(2p^m, p^m) = C(2p^{m-1}, p^{m-1}) β₁`. -/
lemma choose2_ratio {m : ℕ} (hm : 1 ≤ m) :
    (((2 * p^m).choose (p^m) : ℕ) : ℚ_[p]) =
      (((2 * p^(m-1)).choose (p^(m-1)) : ℕ) : ℚ_[p]) * beta p m 1 := by
  set n' := p^(m-1) with hn'
  set X : ℚ_[p] := (p:ℚ_[p])^(n') * (Nat.factorial n' : ℚ_[p]) * ((B p m 0 : ℕ) : ℚ_[p])
    with hX
  have hXne : X ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero _ _) (cast_B0_ne m)
    · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.pos.ne')
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  apply mul_right_cancel₀ (pow_ne_zero 2 hXne)
  have e1 := cast_choose_mul (p := p) (show (1:ℕ) ≤ 2 by norm_num) (p^m)
  have e2 := cast_choose_mul (p := p) (show (1:ℕ) ≤ 2 by norm_num) n'
  simp only [show (2:ℕ) - 1 = 1 by rfl, one_mul] at e1 e2
  have f1 := cast_fact_pm (p := p) hm
  have f2 := cast_fact_2pm (p := p) hm
  calc (((2 * p^m).choose (p^m) : ℕ) : ℚ_[p]) * X^2
      = (((2 * p^m).choose (p^m) : ℕ) : ℚ_[p]) *
          ((Nat.factorial (p^m) : ℚ_[p]) * (Nat.factorial (p^m) : ℚ_[p])) := by
        rw [f1]; ring
    _ = ((Nat.factorial (2 * p^m) : ℕ) : ℚ_[p]) := by rw [← e1]; push_cast; ring
    _ = (p:ℚ_[p])^(2 * n') * (Nat.factorial (2 * n') : ℚ_[p]) *
          (((B p m 0 : ℕ) : ℚ_[p]) * (((B p m 0 : ℕ) : ℚ_[p]) * beta p m 1)) := by
        rw [f2]
    _ = (p:ℚ_[p])^(2 * n') *
          ((((2 * n').choose n' : ℕ) : ℚ_[p]) * (Nat.factorial n' : ℚ_[p]) *
            (Nat.factorial n' : ℚ_[p])) *
          (((B p m 0 : ℕ) : ℚ_[p]) * (((B p m 0 : ℕ) : ℚ_[p]) * beta p m 1)) := by
        rw [show (((2 * n').choose n' : ℕ) : ℚ_[p]) * (Nat.factorial n' : ℚ_[p]) *
            (Nat.factorial n' : ℚ_[p]) = (Nat.factorial (2 * n') : ℚ_[p]) from e2]
    _ = (((2 * n').choose n' : ℕ) : ℚ_[p]) * beta p m 1 * X^2 := by
        rw [hX, show 2 * n' = n' * 2 from mul_comm 2 n', pow_mul]
        ring

/-- The fundamental recursion: `C(3p^m, p^m) = C(3p^{m-1}, p^{m-1}) β₂`. -/
lemma choose3_ratio {m : ℕ} (hm : 1 ≤ m) :
    (((3 * p^m).choose (p^m) : ℕ) : ℚ_[p]) =
      (((3 * p^(m-1)).choose (p^(m-1)) : ℕ) : ℚ_[p]) * beta p m 2 := by
  set n' := p^(m-1) with hn'
  set Z : ℚ_[p] := (p:ℚ_[p])^(3 * n') * (Nat.factorial n' : ℚ_[p]) *
      (Nat.factorial (2 * n') : ℚ_[p]) * ((B p m 0 : ℕ) : ℚ_[p])^3 * beta p m 1 with hZ
  have hZne : Z ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero _ _) _) _) (beta_ne m 1)
    · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.pos.ne')
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
    · exact Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
    · exact pow_ne_zero _ (cast_B0_ne m)
  apply mul_right_cancel₀ hZne
  have e1 := cast_choose_mul (p := p) (show (1:ℕ) ≤ 3 by norm_num) (p^m)
  have e2 := cast_choose_mul (p := p) (show (1:ℕ) ≤ 3 by norm_num) n'
  simp only [show (3:ℕ) - 1 = 2 by rfl] at e1 e2
  have f1 := cast_fact_pm (p := p) hm
  have f2 := cast_fact_2pm (p := p) hm
  have f3 := cast_fact_3pm (p := p) hm
  calc (((3 * p^m).choose (p^m) : ℕ) : ℚ_[p]) * Z
      = (((3 * p^m).choose (p^m) : ℕ) : ℚ_[p]) *
          ((Nat.factorial (p^m) : ℚ_[p]) * (Nat.factorial (2 * p^m) : ℚ_[p])) := by
        rw [hZ, f1, f2]; ring
    _ = ((Nat.factorial (3 * p^m) : ℕ) : ℚ_[p]) := by rw [← e1]; push_cast; ring
    _ = (p:ℚ_[p])^(3 * n') * (Nat.factorial (3 * n') : ℚ_[p]) *
          (((B p m 0 : ℕ) : ℚ_[p]) * (((B p m 0 : ℕ) : ℚ_[p]) * beta p m 1) *
            (((B p m 0 : ℕ) : ℚ_[p]) * beta p m 2)) := by rw [f3]
    _ = (p:ℚ_[p])^(3 * n') *
          ((((3 * n').choose n' : ℕ) : ℚ_[p]) * (Nat.factorial n' : ℚ_[p]) *
            (Nat.factorial (2 * n') : ℚ_[p])) *
          (((B p m 0 : ℕ) : ℚ_[p]) * (((B p m 0 : ℕ) : ℚ_[p]) * beta p m 1) *
            (((B p m 0 : ℕ) : ℚ_[p]) * beta p m 2)) := by
        rw [show (((3 * n').choose n' : ℕ) : ℚ_[p]) * (Nat.factorial n' : ℚ_[p]) *
            (Nat.factorial (2 * n') : ℚ_[p]) = (Nat.factorial (3 * n') : ℚ_[p]) from e2]
    _ = (((3 * n').choose n' : ℕ) : ℚ_[p]) * beta p m 2 * Z := by
        rw [hZ]; ring

/-! ### Bounds on beta - 1 -/

lemma D_beta1 (hp2 : p ≠ 2) {m : ℕ} (hm : 1 ≤ m) :
    D p (3*(m:ℤ)) (3 * (beta p m 1 - 1)) := by
  have hm' : (1:ℤ) ≤ (m:ℤ) := by exact_mod_cast hm
  have happ := D_beta_approx hp2 hm 1
  simp only [Nat.cast_one, one_pow, one_mul] at happ
  have hH1 : 2 * (ps p m 1) + ((p:ℚ_[p])^m) * (ps p m 2) = ((p:ℚ_[p])^m)^2 * (tau p m 2 1) := H1 hm
  have hdec : 3 * (Fpoly (((p:ℚ_[p])^m)*(ps p m 1)) (((p:ℚ_[p])^m)^2*(ps p m 2)) (((p:ℚ_[p])^m)^3*(ps p m 3)) (((p:ℚ_[p])^m)^4*(ps p m 4)) - 1) =
      -(((p:ℚ_[p])^m)^2 * (3*(ps p m 2))) + ((p:ℚ_[p])^m)^3 * (tau p m 2 1) * 3 / 2 + ((p:ℚ_[p])^m)^2 * (ps p m 1)^2 * 3 / 2 + ((p:ℚ_[p])^m)^3 * (ps p m 1)^3 / 2
      + -(((p:ℚ_[p])^m)^3 * (ps p m 1) * (3*(ps p m 2)) / 2) + ((p:ℚ_[p])^m)^3 * (ps p m 3) + ((p:ℚ_[p])^m)^4 * (ps p m 1)^4 / 8
      + -(((p:ℚ_[p])^m)^4 * (ps p m 1)^2 * (3*(ps p m 2)) / 4) + ((p:ℚ_[p])^m)^4 * (3*(ps p m 2)) * (ps p m 2) / 8 + ((p:ℚ_[p])^m)^4 * (ps p m 1) * (ps p m 3)
      + -(((p:ℚ_[p])^m)^4 * (ps p m 4) * 3 / 4) := by
    unfold Fpoly
    linear_combination ((3:ℚ_[p]) * ((p:ℚ_[p])^m) / 2) * hH1
  have hs2 := D_three_mul_ps2 hp2 hm
  have hs2' := D_ps2 hp2 hm
  have hs1 := D_ps1 hp2 hm
  have hs3 := D_ps3 hp2 hm
  have hs4 := D_ps4 hp2 hm
  have hu := D_tau21 hp2 hm
  have hT1 : D p (3*(m:ℤ)) (-(((p:ℚ_[p])^m)^2 * (3*(ps p m 2)))) :=
    (((D_Npow (p := p) m 2).mul hs2).of_eq rfl (by push_cast; omega)).neg
  have hT2 : D p (3*(m:ℤ)) (((p:ℚ_[p])^m)^3 * (tau p m 2 1) * 3 / 2) :=
    ((((D_Npow (p := p) m 3).mul hu).mul (D_nat 3)).of_eq (by push_cast; ring)
      (by push_cast; omega)).half hp2
  have hT3 : D p (3*(m:ℤ)) (((p:ℚ_[p])^m)^2 * (ps p m 1)^2 * 3 / 2) :=
    ((((D_Npow (p := p) m 2).mul (hs1.mul hs1)).mul (D_nat 3)).of_eq (by push_cast; ring)
      (by push_cast; omega)).half hp2
  have hT4 : D p (3*(m:ℤ)) (((p:ℚ_[p])^m)^3 * (ps p m 1)^3 / 2) :=
    (((D_Npow (p := p) m 3).mul ((hs1.mul hs1).mul hs1)).of_eq (by push_cast; ring)
      (by push_cast; omega)).half hp2
  have hT5 : D p (3*(m:ℤ)) (-(((p:ℚ_[p])^m)^3 * (ps p m 1) * (3*(ps p m 2)) / 2)) :=
    ((((D_Npow (p := p) m 3).mul hs1).mul hs2).of_eq (by push_cast; ring)
      (by push_cast; omega)).half hp2 |>.neg
  have hT6 : D p (3*(m:ℤ)) (((p:ℚ_[p])^m)^3 * (ps p m 3)) :=
    ((D_Npow (p := p) m 3).mul hs3).of_eq rfl (by push_cast; omega)
  have hT7 : D p (3*(m:ℤ)) (((p:ℚ_[p])^m)^4 * (ps p m 1)^4 / 8) := by
    have h := ((D_Npow (p := p) m 4).mul (((hs1.mul hs1).mul hs1).mul hs1)).of_eq
      (show _ = ((p:ℚ_[p])^m)^4 * (ps p m 1)^4 by push_cast; ring) (le_refl _)
    have h8 := h.divn (n := 8) (not_dvd_pow_two hp2 3)
    exact (h8.of_eq (by norm_num) (by push_cast; omega))
  have hT8 : D p (3*(m:ℤ)) (-(((p:ℚ_[p])^m)^4 * (ps p m 1)^2 * (3*(ps p m 2)) / 4)) := by
    have h := (((D_Npow (p := p) m 4).mul (hs1.mul hs1)).mul hs2).of_eq
      (show _ = ((p:ℚ_[p])^m)^4 * (ps p m 1)^2 * (3*(ps p m 2)) by push_cast; ring) (le_refl _)
    have h4 := h.divn (n := 4) (not_dvd_pow_two hp2 2)
    exact (h4.of_eq (by norm_num) (by push_cast; omega)).neg
  have hT9 : D p (3*(m:ℤ)) (((p:ℚ_[p])^m)^4 * (3*(ps p m 2)) * (ps p m 2) / 8) := by
    have h := (((D_Npow (p := p) m 4).mul hs2).mul hs2').of_eq
      (show _ = ((p:ℚ_[p])^m)^4 * (3*(ps p m 2)) * (ps p m 2) by push_cast; ring) (le_refl _)
    have h8 := h.divn (n := 8) (not_dvd_pow_two hp2 3)
    exact (h8.of_eq (by norm_num) (by push_cast; omega))
  have hT10 : D p (3*(m:ℤ)) (((p:ℚ_[p])^m)^4 * (ps p m 1) * (ps p m 3)) :=
    (((D_Npow (p := p) m 4).mul hs1).mul hs3).of_eq rfl (by push_cast; omega)
  have hT11 : D p (3*(m:ℤ)) (-(((p:ℚ_[p])^m)^4 * (ps p m 4) * 3 / 4)) := by
    have h := (((D_Npow (p := p) m 4).mul hs4).mul (D_nat 3)).of_eq
      (show _ = ((p:ℚ_[p])^m)^4 * (ps p m 4) * 3 by push_cast; ring) (le_refl _)
    have h4 := h.divn (n := 4) (not_dvd_pow_two hp2 2)
    exact (h4.of_eq (by norm_num) (by push_cast; omega)).neg
  have hmain : D p (3*(m:ℤ)) (3 * (Fpoly (((p:ℚ_[p])^m)*(ps p m 1)) (((p:ℚ_[p])^m)^2*(ps p m 2)) (((p:ℚ_[p])^m)^3*(ps p m 3)) (((p:ℚ_[p])^m)^4*(ps p m 4)) - 1)) := by
    rw [hdec]
    exact ((((((((((hT1.add hT2).add hT3).add hT4).add hT5).add hT6).add hT7).add
      hT8).add hT9).add hT10).add hT11)
  have herr : D p (3*(m:ℤ)) (3 * (beta p m 1 - Fpoly (((p:ℚ_[p])^m)*(ps p m 1)) (((p:ℚ_[p])^m)^2*(ps p m 2)) (((p:ℚ_[p])^m)^3*(ps p m 3)) (((p:ℚ_[p])^m)^4*(ps p m 4)))) :=
    ((D_nat (p := p) 3).mul happ).of_eq (by push_cast; ring) (by push_cast; omega)
  exact (hmain.add herr).of_eq (by ring) (le_refl _)

lemma D_beta2 (hp2 : p ≠ 2) {m : ℕ} (hm : 1 ≤ m) :
    D p (3*(m:ℤ)) (beta p m 2 - 1) := by
  have hm' : (1:ℤ) ≤ (m:ℤ) := by exact_mod_cast hm
  have happ := D_beta_approx hp2 hm 2
  have hc2 : ((2:ℕ):ℚ_[p]) = (2:ℚ_[p]) := by norm_num
  rw [hc2] at happ
  have hH1 : 2 * (ps p m 1) + ((p:ℚ_[p])^m) * (ps p m 2) = ((p:ℚ_[p])^m)^2 * (tau p m 2 1) := H1 hm
  have hdec : Fpoly (2*((p:ℚ_[p])^m)*(ps p m 1)) (2^2*((p:ℚ_[p])^m)^2*(ps p m 2)) (2^3*((p:ℚ_[p])^m)^3*(ps p m 3)) (2^4*((p:ℚ_[p])^m)^4*(ps p m 4)) - 1 =
      ((p:ℚ_[p])^m)^3 * (tau p m 2 1) + -(((p:ℚ_[p])^m)^2 * (3*(ps p m 2))) + ((p:ℚ_[p])^m)^2 * (ps p m 1)^2 * 2 + ((p:ℚ_[p])^m)^3 * (ps p m 1)^3 * 4 / 3
      + -(((p:ℚ_[p])^m)^3 * (ps p m 1) * (ps p m 2) * 4) + ((p:ℚ_[p])^m)^3 * ((ps p m 3)/3) * 8 + ((p:ℚ_[p])^m)^4 * (ps p m 1)^4 * 2 / 3
      + -(((p:ℚ_[p])^m)^4 * (ps p m 1)^2 * (ps p m 2) * 4) + ((p:ℚ_[p])^m)^4 * (ps p m 2)^2 * 2 + ((p:ℚ_[p])^m)^4 * (ps p m 1) * ((ps p m 3)/3) * 16
      + -(((p:ℚ_[p])^m)^4 * (ps p m 4) * 4) := by
    unfold Fpoly
    linear_combination ((p:ℚ_[p])^m) * hH1
  have hs2 := D_three_mul_ps2 hp2 hm
  have hs2' := D_ps2 hp2 hm
  have hs1 := D_ps1 hp2 hm
  have hs33 := D_ps3_div3 hp2 hm
  have hs4 := D_ps4 hp2 hm
  have hu := D_tau21 hp2 hm
  have hU1 : D p (3*(m:ℤ)) (((p:ℚ_[p])^m)^3 * (tau p m 2 1)) :=
    ((D_Npow (p := p) m 3).mul hu).of_eq rfl (by push_cast; omega)
  have hU2 : D p (3*(m:ℤ)) (-(((p:ℚ_[p])^m)^2 * (3*(ps p m 2)))) :=
    (((D_Npow (p := p) m 2).mul hs2).of_eq rfl (by push_cast; omega)).neg
  have hU3 : D p (3*(m:ℤ)) (((p:ℚ_[p])^m)^2 * (ps p m 1)^2 * 2) :=
    (((D_Npow (p := p) m 2).mul (hs1.mul hs1)).mul (D_nat 2)).of_eq (by push_cast; ring)
      (by push_cast; omega)
  have hU4 : D p (3*(m:ℤ)) (((p:ℚ_[p])^m)^3 * (ps p m 1)^3 * 4 / 3) := by
    have h := (((D_Npow (p := p) m 3).mul ((hs1.mul hs1).mul hs1)).mul (D_nat 4)).of_eq
      (show _ = ((p:ℚ_[p])^m)^3 * (ps p m 1)^3 * 4 by push_cast; ring) (le_refl _)
    have h3 := h.divn' (n := 3)
      (not_sq_dvd_small hp2 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    exact h3.of_eq (by norm_num) (by push_cast; omega)
  have hU5 : D p (3*(m:ℤ)) (-(((p:ℚ_[p])^m)^3 * (ps p m 1) * (ps p m 2) * 4)) :=
    ((((D_Npow (p := p) m 3).mul hs1).mul hs2').mul (D_nat 4)).of_eq (by push_cast; ring)
      (by push_cast; omega) |>.neg
  have hU6 : D p (3*(m:ℤ)) (((p:ℚ_[p])^m)^3 * ((ps p m 3)/3) * 8) :=
    (((D_Npow (p := p) m 3).mul hs33).mul (D_nat 8)).of_eq (by push_cast; ring)
      (by push_cast; omega)
  have hU7 : D p (3*(m:ℤ)) (((p:ℚ_[p])^m)^4 * (ps p m 1)^4 * 2 / 3) := by
    have h := (((D_Npow (p := p) m 4).mul (((hs1.mul hs1).mul hs1).mul hs1)).mul
      (D_nat 2)).of_eq (show _ = ((p:ℚ_[p])^m)^4 * (ps p m 1)^4 * 2 by push_cast; ring) (le_refl _)
    have h3 := h.divn' (n := 3)
      (not_sq_dvd_small hp2 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    exact h3.of_eq (by norm_num) (by push_cast; omega)
  have hU8 : D p (3*(m:ℤ)) (-(((p:ℚ_[p])^m)^4 * (ps p m 1)^2 * (ps p m 2) * 4)) :=
    ((((D_Npow (p := p) m 4).mul (hs1.mul hs1)).mul hs2').mul (D_nat 4)).of_eq
      (by push_cast; ring) (by push_cast; omega) |>.neg
  have hU9 : D p (3*(m:ℤ)) (((p:ℚ_[p])^m)^4 * (ps p m 2)^2 * 2) :=
    (((D_Npow (p := p) m 4).mul (hs2'.mul hs2')).mul (D_nat 2)).of_eq (by push_cast; ring)
      (by push_cast; omega)
  have hU10 : D p (3*(m:ℤ)) (((p:ℚ_[p])^m)^4 * (ps p m 1) * ((ps p m 3)/3) * 16) :=
    ((((D_Npow (p := p) m 4).mul hs1).mul hs33).mul (D_nat 16)).of_eq (by push_cast; ring)
      (by push_cast; omega)
  have hU11 : D p (3*(m:ℤ)) (-(((p:ℚ_[p])^m)^4 * (ps p m 4) * 4)) :=
    (((D_Npow (p := p) m 4).mul hs4).mul (D_nat 4)).of_eq (by push_cast; ring)
      (by push_cast; omega) |>.neg
  have hmain : D p (3*(m:ℤ))
      (Fpoly (2*((p:ℚ_[p])^m)*(ps p m 1)) (2^2*((p:ℚ_[p])^m)^2*(ps p m 2)) (2^3*((p:ℚ_[p])^m)^3*(ps p m 3)) (2^4*((p:ℚ_[p])^m)^4*(ps p m 4)) - 1) := by
    rw [hdec]
    exact ((((((((((hU1.add hU2).add hU3).add hU4).add hU5).add hU6).add hU7).add
      hU8).add hU9).add hU10).add hU11)
  have herr : D p (3*(m:ℤ))
      (beta p m 2 - Fpoly (2*((p:ℚ_[p])^m)*(ps p m 1)) (2^2*((p:ℚ_[p])^m)^2*(ps p m 2)) (2^3*((p:ℚ_[p])^m)^3*(ps p m 3)) (2^4*((p:ℚ_[p])^m)^4*(ps p m 4))) :=
    (happ.of_eq (by push_cast; ring) (by push_cast; omega))
  exact (hmain.add herr).of_eq (by ring) (le_refl _)

/-! ### Wolstenholme-type congruences -/

lemma W3 (hp2 : p ≠ 2) : ∀ k : ℕ, D p 3 ((((3*p^k).choose (p^k) : ℕ) : ℚ_[p]) - 3)
  | 0 => by
    norm_num
    exact D_zero 3
  | (k+1) => by
    have hm1 : 1 ≤ k + 1 := by omega
    have hrat := choose3_ratio (p := p) (m := k+1) hm1
    simp only [Nat.add_sub_cancel] at hrat
    have hb2 := D_beta2 hp2 hm1
    have hb0 : D p 0 (beta p (k+1) 2) :=
      (D_one.add (hb2.mono (by push_cast; omega))).of_eq (by ring) (le_refl _)
    have h3b : D p 3 (3 * (beta p (k+1) 2 - 1)) :=
      ((D_nat (p := p) 3).mul hb2).of_eq (by push_cast; ring) (by push_cast; omega)
    have IH := W3 hp2 k
    rw [hrat]
    exact ((IH.mul hb0).add h3b).of_eq (by ring) (by omega)

lemma W2 (hp2 : p ≠ 2) : ∀ k : ℕ, D p 3 (9 * ((((2*p^k).choose (p^k) : ℕ) : ℚ_[p]) - 2))
  | 0 => by
    norm_num
    exact D_zero 3
  | (k+1) => by
    have hm1 : 1 ≤ k + 1 := by omega
    have hrat := choose2_ratio (p := p) (m := k+1) hm1
    simp only [Nat.add_sub_cancel] at hrat
    have hb1 := D_beta1 hp2 hm1
    have hbm : D p 0 (beta p (k+1) 1 - 1) := by
      have h := hb1.divn' (n := 3)
        (not_sq_dvd_small hp2 (by norm_num) (by norm_num) (by norm_num) (by norm_num))
      have heq : 3 * (beta p (k+1) 1 - 1) / ((3:ℕ):ℚ_[p]) = beta p (k+1) 1 - 1 := by
        push_cast
        rw [mul_div_cancel_left₀ _ (by norm_num : (3:ℚ_[p]) ≠ 0)]
      rw [heq] at h
      exact h.mono (by push_cast; omega)
    have hb0 : D p 0 (beta p (k+1) 1) :=
      (D_one.add hbm).of_eq (by ring) (le_refl _)
    have h6b : D p 3 (6 * (3 * (beta p (k+1) 1 - 1))) :=
      ((D_nat (p := p) 6).mul hb1).of_eq (by push_cast; ring) (by push_cast; omega)
    have IH := W2 hp2 k
    rw [hrat]
    exact ((IH.mul hb0).add h6b).of_eq (by ring) (by omega)

/-! ### The main cancellation -/

lemma D_Texpr (hp2 : p ≠ 2) {m : ℕ} (hm2 : 2 ≤ m) :
    D p (3*(m:ℤ) + 3)
      (Fpoly (2*((p:ℚ_[p])^m)*(ps p m 1)) (2^2*((p:ℚ_[p])^m)^2*(ps p m 2)) (2^3*((p:ℚ_[p])^m)^3*(ps p m 3)) (2^4*((p:ℚ_[p])^m)^4*(ps p m 4))
        - 3 * Fpoly (((p:ℚ_[p])^m)*(ps p m 1)) (((p:ℚ_[p])^m)^2*(ps p m 2)) (((p:ℚ_[p])^m)^3*(ps p m 3)) (((p:ℚ_[p])^m)^4*(ps p m 4)) + 2) := by
  have hm : 1 ≤ m := by omega
  have hm' : (2:ℤ) ≤ (m:ℤ) := by exact_mod_cast hm2
  have hH1 : 2 * (ps p m 1) + ((p:ℚ_[p])^m) * (ps p m 2) = ((p:ℚ_[p])^m)^2 * (tau p m 2 1) := H1 hm
  have hH2 := H2 (p := p) hm
  have hdec : Fpoly (2*((p:ℚ_[p])^m)*(ps p m 1)) (2^2*((p:ℚ_[p])^m)^2*(ps p m 2)) (2^3*((p:ℚ_[p])^m)^3*(ps p m 3)) (2^4*((p:ℚ_[p])^m)^4*(ps p m 4))
        - 3 * Fpoly (((p:ℚ_[p])^m)*(ps p m 1)) (((p:ℚ_[p])^m)^2*(ps p m 2)) (((p:ℚ_[p])^m)^3*(ps p m 3)) (((p:ℚ_[p])^m)^4*(ps p m 4)) + 2 =
      -(((p:ℚ_[p])^m)^3 * (tau p m 2 1) / 2) + ((p:ℚ_[p])^m)^2 * (ps p m 1)^2 / 2 + ((p:ℚ_[p])^m)^3 * (ps p m 1)^3 * 5 / 6
      + -(((p:ℚ_[p])^m)^3 * (ps p m 1) * (ps p m 2) * 5 / 2) + -(((p:ℚ_[p])^m)^4 * (ps p m 4) * 5 / 2)
      + ((p:ℚ_[p])^m)^5 * (tau p m 4 1 - tau p m 3 2) * 5 / 2 + ((p:ℚ_[p])^m)^6 * tau p m 3 3 * 5 / 6
      + ((p:ℚ_[p])^m)^4 * (ps p m 1)^4 * 13 / 24 + -(((p:ℚ_[p])^m)^4 * (ps p m 1)^2 * (ps p m 2) * 13 / 4)
      + ((p:ℚ_[p])^m)^4 * (ps p m 2)^2 * 13 / 8 + ((p:ℚ_[p])^m)^4 * (ps p m 1) * ((ps p m 3)/3) * 13
      + -(((p:ℚ_[p])^m)^4 * (ps p m 4) * 13 / 4) := by
    unfold Fpoly
    linear_combination (-(((p:ℚ_[p])^m)/2)) * hH1 + ((5:ℚ_[p]) * ((p:ℚ_[p])^m)^3 / 6) * hH2
  have hs2' := D_ps2 hp2 hm
  have hs1 := D_ps1 hp2 hm
  have hs33 := D_ps3_div3 hp2 hm
  have hs4 := D_ps4 hp2 hm
  have hu := D_tau21 hp2 hm
  have ht41 := D_tau (p := p) hm 4 1
  have ht32 := D_tau (p := p) hm 3 2
  have ht33 := D_tau (p := p) hm 3 3
  have not9 : ¬ p^2 ∣ 6 :=
    not_sq_dvd_small hp2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have not24 : ¬ p^2 ∣ 24 :=
    not_sq_dvd_small hp2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have ht1 : D p (3*(m:ℤ) + 3) (-(((p:ℚ_[p])^m)^3 * (tau p m 2 1) / 2)) :=
    ((((D_Npow (p := p) m 3).mul hu).of_eq rfl (by push_cast; omega)).half hp2).neg
  have ht2 : D p (3*(m:ℤ) + 3) (((p:ℚ_[p])^m)^2 * (ps p m 1)^2 / 2) :=
    ((((D_Npow (p := p) m 2).mul (hs1.mul hs1)).of_eq (by push_cast; ring)
      (by push_cast; omega)).half hp2)
  have ht3 : D p (3*(m:ℤ) + 3) (((p:ℚ_[p])^m)^3 * (ps p m 1)^3 * 5 / 6) := by
    have h := ((((D_Npow (p := p) m 3).mul ((hs1.mul hs1).mul hs1)).mul (D_nat 5)).of_eq
      (show _ = ((p:ℚ_[p])^m)^3 * (ps p m 1)^3 * 5 by push_cast; ring) (le_refl _)).divn' (n := 6) not9
    exact h.of_eq (by norm_num) (by push_cast; omega)
  have ht4 : D p (3*(m:ℤ) + 3) (-(((p:ℚ_[p])^m)^3 * (ps p m 1) * (ps p m 2) * 5 / 2)) :=
    ((((((D_Npow (p := p) m 3).mul hs1).mul hs2').mul (D_nat 5)).of_eq
      (show _ = ((p:ℚ_[p])^m)^3 * (ps p m 1) * (ps p m 2) * 5 by push_cast; ring)
      (by push_cast; omega)).half hp2).neg
  have ht5 : D p (3*(m:ℤ) + 3) (-(((p:ℚ_[p])^m)^4 * (ps p m 4) * 5 / 2)) :=
    (((((D_Npow (p := p) m 4).mul hs4).mul (D_nat 5)).of_eq
      (show _ = ((p:ℚ_[p])^m)^4 * (ps p m 4) * 5 by push_cast; ring)
      (by push_cast; omega)).half hp2).neg
  have ht6 : D p (3*(m:ℤ) + 3) (((p:ℚ_[p])^m)^5 * (tau p m 4 1 - tau p m 3 2) * 5 / 2) :=
    ((((D_Npow (p := p) m 5).mul (ht41.sub ht32)).mul (D_nat 5)).of_eq
      (show _ = ((p:ℚ_[p])^m)^5 * (tau p m 4 1 - tau p m 3 2) * 5 by push_cast; ring)
      (by push_cast; omega)).half hp2
  have ht7 : D p (3*(m:ℤ) + 3) (((p:ℚ_[p])^m)^6 * tau p m 3 3 * 5 / 6) := by
    have h := ((((D_Npow (p := p) m 6).mul ht33).mul (D_nat 5)).of_eq
      (show _ = ((p:ℚ_[p])^m)^6 * tau p m 3 3 * 5 by push_cast; ring) (le_refl _)).divn' (n := 6) not9
    exact h.of_eq (by norm_num) (by push_cast; omega)
  have ht8 : D p (3*(m:ℤ) + 3) (((p:ℚ_[p])^m)^4 * (ps p m 1)^4 * 13 / 24) := by
    have h := ((((D_Npow (p := p) m 4).mul (((hs1.mul hs1).mul hs1).mul hs1)).mul
      (D_nat 13)).of_eq (show _ = ((p:ℚ_[p])^m)^4 * (ps p m 1)^4 * 13 by push_cast; ring)
      (le_refl _)).divn' (n := 24) not24
    exact h.of_eq (by norm_num) (by push_cast; omega)
  have ht9 : D p (3*(m:ℤ) + 3) (-(((p:ℚ_[p])^m)^4 * (ps p m 1)^2 * (ps p m 2) * 13 / 4)) := by
    have h := (((((D_Npow (p := p) m 4).mul (hs1.mul hs1)).mul hs2').mul (D_nat 13)).of_eq
      (show _ = ((p:ℚ_[p])^m)^4 * (ps p m 1)^2 * (ps p m 2) * 13 by push_cast; ring)
      (le_refl _)).divn (n := 4) (not_dvd_pow_two hp2 2)
    exact (h.of_eq (by norm_num) (by push_cast; omega)).neg
  have ht10 : D p (3*(m:ℤ) + 3) (((p:ℚ_[p])^m)^4 * (ps p m 2)^2 * 13 / 8) := by
    have h := ((((D_Npow (p := p) m 4).mul (hs2'.mul hs2')).mul (D_nat 13)).of_eq
      (show _ = ((p:ℚ_[p])^m)^4 * (ps p m 2)^2 * 13 by push_cast; ring)
      (le_refl _)).divn (n := 8) (not_dvd_pow_two hp2 3)
    exact h.of_eq (by norm_num) (by push_cast; omega)
  have ht11 : D p (3*(m:ℤ) + 3) (((p:ℚ_[p])^m)^4 * (ps p m 1) * ((ps p m 3)/3) * 13) :=
    ((((D_Npow (p := p) m 4).mul hs1).mul hs33).mul (D_nat 13)).of_eq
      (by push_cast; ring) (by push_cast; omega)
  have ht12 : D p (3*(m:ℤ) + 3) (-(((p:ℚ_[p])^m)^4 * (ps p m 4) * 13 / 4)) := by
    have h := ((((D_Npow (p := p) m 4).mul hs4).mul (D_nat 13)).of_eq
      (show _ = ((p:ℚ_[p])^m)^4 * (ps p m 4) * 13 by push_cast; ring)
      (le_refl _)).divn (n := 4) (not_dvd_pow_two hp2 2)
    exact (h.of_eq (by norm_num) (by push_cast; omega)).neg
  rw [hdec]
  exact (((((((((((ht1.add ht2).add ht3).add ht4).add ht5).add ht6).add ht7).add
    ht8).add ht9).add ht10).add ht11).add ht12)

/-! ### Final assembly -/

lemma main_bound (hp2 : p ≠ 2) {r : ℕ} (hr : 2 ≤ r) :
    D p (3*(r:ℤ) + 3)
      (((((3*p^r).choose (p^r) : ℕ) : ℚ_[p])^2 - 27 * (((2*p^r).choose (p^r) : ℕ) : ℚ_[p])) - ((((3*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p])^2 - 27 * (((2*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p]))) := by
  have hm : 1 ≤ r := by omega
  have h3 := choose3_ratio (p := p) (m := r) hm
  have h2 := choose2_ratio (p := p) (m := r) hm
  have hX := D_beta2 hp2 hm
  have hY := D_beta1 hp2 hm
  have hW3 := W3 hp2 (r-1)
  have hW2 := W2 hp2 (r-1)
  have hT := D_Texpr (p := p) hp2 hr
  have happ1 := D_beta_approx hp2 hm 1
  simp only [Nat.cast_one, one_pow, one_mul] at happ1
  have happ2 := D_beta_approx hp2 hm 2
  have hc2 : ((2:ℕ):ℚ_[p]) = (2:ℚ_[p]) := by norm_num
  rw [hc2] at happ2
  have key : ((((3*p^r).choose (p^r) : ℕ) : ℚ_[p])^2 - 27 * (((2*p^r).choose (p^r) : ℕ) : ℚ_[p])) - ((((3*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p])^2 - 27 * (((2*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p])) =
      (((3*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p])^2 * ((beta p r 2) - 1)^2
      + 2 * (((((3*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p]) - 3) * ((((3*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p]) + 3)) * ((beta p r 2) - 1)
      + 18 * ((Fpoly (2*((p:ℚ_[p])^r)*(ps p r 1)) (2^2*((p:ℚ_[p])^r)^2*(ps p r 2)) (2^3*((p:ℚ_[p])^r)^3*(ps p r 3)) (2^4*((p:ℚ_[p])^r)^4*(ps p r 4))) - 3 * (Fpoly (((p:ℚ_[p])^r)*(ps p r 1)) (((p:ℚ_[p])^r)^2*(ps p r 2)) (((p:ℚ_[p])^r)^3*(ps p r 3)) (((p:ℚ_[p])^r)^4*(ps p r 4))) + 2)
      + 18 * ((beta p r 2) - (Fpoly (2*((p:ℚ_[p])^r)*(ps p r 1)) (2^2*((p:ℚ_[p])^r)^2*(ps p r 2)) (2^3*((p:ℚ_[p])^r)^3*(ps p r 3)) (2^4*((p:ℚ_[p])^r)^4*(ps p r 4))))
      - 54 * ((beta p r 1) - (Fpoly (((p:ℚ_[p])^r)*(ps p r 1)) (((p:ℚ_[p])^r)^2*(ps p r 2)) (((p:ℚ_[p])^r)^3*(ps p r 3)) (((p:ℚ_[p])^r)^4*(ps p r 4))))
      - 9 * ((((2*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p]) - 2) * (3 * ((beta p r 1) - 1)) := by
    rw [h3, h2]
    ring
  rw [key]
  have hP1 : D p (3*(r:ℤ) + 3) ((((3*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p])^2 * ((beta p r 2) - 1)^2) :=
    (((D_nat (p := p) _).mul (D_nat (p := p) _)).mul (hX.mul hX)).of_eq
      (by push_cast; ring) (by push_cast; omega)
  have hplus : D p 0 ((((3*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p]) + 3) :=
    ((D_nat (p := p) _).add ((D_nat (p := p) 3).of_eq (by push_cast; ring) (le_refl _)))
  have hP2 : D p (3*(r:ℤ) + 3) (2 * (((((3*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p]) - 3) * ((((3*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p]) + 3)) * ((beta p r 2) - 1)) :=
    (((D_nat (p := p) 2).mul ((hW3.mul hplus).mul hX)).of_eq (by push_cast; ring)
      (by push_cast; omega))
  have hP3 : D p (3*(r:ℤ) + 3) (18 * ((Fpoly (2*((p:ℚ_[p])^r)*(ps p r 1)) (2^2*((p:ℚ_[p])^r)^2*(ps p r 2)) (2^3*((p:ℚ_[p])^r)^3*(ps p r 3)) (2^4*((p:ℚ_[p])^r)^4*(ps p r 4))) - 3 * (Fpoly (((p:ℚ_[p])^r)*(ps p r 1)) (((p:ℚ_[p])^r)^2*(ps p r 2)) (((p:ℚ_[p])^r)^3*(ps p r 3)) (((p:ℚ_[p])^r)^4*(ps p r 4))) + 2)) :=
    ((D_nat (p := p) 18).mul hT).of_eq (by push_cast; ring) (by push_cast; omega)
  have hP4 : D p (3*(r:ℤ) + 3) (18 * ((beta p r 2) - (Fpoly (2*((p:ℚ_[p])^r)*(ps p r 1)) (2^2*((p:ℚ_[p])^r)^2*(ps p r 2)) (2^3*((p:ℚ_[p])^r)^3*(ps p r 3)) (2^4*((p:ℚ_[p])^r)^4*(ps p r 4))))) :=
    ((D_nat (p := p) 18).mul happ2).of_eq (by push_cast; ring) (by push_cast; omega)
  have hP5 : D p (3*(r:ℤ) + 3) (54 * ((beta p r 1) - (Fpoly (((p:ℚ_[p])^r)*(ps p r 1)) (((p:ℚ_[p])^r)^2*(ps p r 2)) (((p:ℚ_[p])^r)^3*(ps p r 3)) (((p:ℚ_[p])^r)^4*(ps p r 4))))) :=
    ((D_nat (p := p) 54).mul happ1).of_eq (by push_cast; ring) (by push_cast; omega)
  have hP6 : D p (3*(r:ℤ) + 3) (9 * ((((2*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p]) - 2) * (3 * ((beta p r 1) - 1))) :=
    (hW2.mul hY).of_eq (by push_cast; ring) (by push_cast; omega)
  exact ((((hP1.add hP2).add hP3).add hP4).sub hP5).sub hP6

end A357569

open Nat

/--
A357569: $a(n) = \binom{3n}{n}^2 - 27 \binom{2n}{n}$.
-/
def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

/-- Conjecture 1: a(p^r) \equiv a(p^(r-1)) ( mod p^(3*r+3) ) for r >= 2 and all primes p >= 3. -/
theorem oeis_357569_conjecture_0 (p r : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (hr : r ≥ 2) :
  a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hb := A357569.main_bound (p := p) hp2 hr
  have hdvd : ((p : ℤ) ^ (3 * r + 3)) ∣ (a (p ^ r) - a (p ^ (r - 1))) := by
    have hiff := Padic.norm_int_le_pow_iff_dvd (p := p) (a (p ^ r) - a (p ^ (r - 1))) (3*r+3)
    have hle : ‖((a (p ^ r) - a (p ^ (r - 1)) : ℤ) : ℚ_[p])‖ ≤ (p:ℝ) ^ (-(3*r+3 : ℕ) : ℤ) := by
      have hcast : (((a (p ^ r) - a (p ^ (r - 1)) : ℤ)) : ℚ_[p]) =
          (((((3*p^r).choose (p^r) : ℕ) : ℚ_[p])^2 - 27 * (((2*p^r).choose (p^r) : ℕ) : ℚ_[p]))
           - ((((3*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p])^2
              - 27 * (((2*p^(r-1)).choose (p^(r-1)) : ℕ) : ℚ_[p]))) := by
        unfold a
        simp only [Int.ofNat_eq_natCast]
        push_cast
        ring
      rw [hcast]
      have hexp : (-(3*r+3 : ℕ) : ℤ) = -(3*(r:ℤ) + 3) := by push_cast; ring
      rw [hexp]
      exact hb
    have := hiff.mp hle
    exact_mod_cast this
  exact ((Int.modEq_iff_dvd).mpr hdvd).symm
