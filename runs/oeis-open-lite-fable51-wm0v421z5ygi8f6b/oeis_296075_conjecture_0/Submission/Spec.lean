import FormalConjectures.Util.ProblemImports

open Nat

set_option Elab.async false

/--
A296075: Sum of deficiencies of divisors of $n$.
The deficiency of a number $d$ is $2d - \sigma_1(d)$, where $\sigma_1(d)$ is the sum of the divisors of $d$.
$$a(n) = \sum_{d|n} (2d - \sigma_1(d))$$
-/
def a (n : ℕ) : ℤ :=
  (divisors n).sum fun d =>
    -- Deficiency of d: 2*d - sigma_1(d)
    (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)

/--
Conjecture from OEIS A296075, by Robert Israel:
Are 1 and 12 the only solutions to a(n)=1?
-/
theorem oeis_296075_conjecture_0 : ∀ n : ℕ,
  a n = 1 ↔ n = 1 ∨ n = 12 := by
  sorry

/-!
## Disproof

The number `n = 2 ^ 14 * 4409 * 458009 = 33085221781504` satisfies `a n = 1`.
Indeed `a n = 2 σ(n) - Σ_{d ∣ n} σ(d)`, and both `n ↦ σ(n)` and `n ↦ Σ_{d ∣ n} σ(d)` are
multiplicative, with `σ(2^14) = 32767`, `Σ_{d ∣ 2^14} σ(d) = 65519`, `σ(p) = p + 1`,
`Σ_{d ∣ p} σ(d) = p + 2` for primes `p`, so
`a n = 2 * 32767 * 4410 * 458010 - 65519 * 4411 * 458011 = 1`.
-/

open ArithmeticFunction ArithmeticFunction.sigma

/- ### Multiplying by a number `p` whose only divisors are `1` and `p` -/

theorem divisors_mul_val {m p : ℕ} (hp : 2 ≤ p) (hd : (divisors p).val = 1 ::ₘ {p})
    (hc : Nat.Coprime m p) :
    (divisors (m * p)).val = (divisors m).val + (divisors m).val.map (· * p) := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp
  have hmem : ∀ x, x ∣ p → x = 1 ∨ x = p := by
    intro x hx
    have h := Finset.mem_def.1 (Nat.mem_divisors.2 ⟨hx, Nat.ne_of_gt hp0⟩)
    rw [hd, Multiset.mem_cons, Multiset.mem_singleton] at h
    exact h
  apply (Multiset.Nodup.ext (Finset.nodup _) ?_).2 ?_
  · rw [Multiset.nodup_add]
    refine ⟨Finset.nodup _,
      Multiset.Nodup.map (fun x y h => Nat.eq_of_mul_eq_mul_right hp0 h) (Finset.nodup _), ?_⟩
    rw [Multiset.disjoint_left]
    intro x hx hx'
    rw [Multiset.mem_map] at hx'
    obtain ⟨d, -, rfl⟩ := hx'
    have h1 : p ∣ m :=
      Nat.dvd_trans (Nat.dvd_mul_left p d) (Nat.mem_divisors.1 (Finset.mem_def.2 hx)).1
    exact absurd (hc.symm.eq_one_of_dvd h1) (Nat.ne_of_gt hp)
  · intro x
    rw [Multiset.mem_add, Multiset.mem_map, ← Finset.mem_def, ← Finset.mem_def, Nat.mem_divisors,
      Nat.mem_divisors]
    constructor
    · rintro ⟨hx, hmp⟩
      have hm0 : m ≠ 0 := fun h => hmp (h ▸ Nat.zero_mul p)
      rcases hmem _ (Nat.gcd_dvd_right x p) with h1 | h1
      · exact Or.inl ⟨Nat.Coprime.dvd_of_dvd_mul_right h1 hx, hm0⟩
      · have hpx : p ∣ x := h1 ▸ Nat.gcd_dvd_left x p
        obtain ⟨d, rfl⟩ := hpx
        refine Or.inr ⟨d, ⟨Finset.mem_def.1 (Nat.mem_divisors.2 ⟨?_, hm0⟩), Nat.mul_comm d p⟩⟩
        rw [Nat.mul_comm p d] at hx
        exact Nat.dvd_of_mul_dvd_mul_right hp0 hx
    · rintro (⟨hx, hm0⟩ | ⟨d, hdm, rfl⟩)
      · exact ⟨Nat.dvd_trans hx (Nat.dvd_mul_right m p), Nat.mul_ne_zero hm0 (Nat.ne_of_gt hp0)⟩
      · have hdm' := Nat.mem_divisors.1 (Finset.mem_def.2 hdm)
        exact ⟨Nat.mul_dvd_mul hdm'.1 (Nat.dvd_refl p), Nat.mul_ne_zero hdm'.2 (Nat.ne_of_gt hp0)⟩

theorem sum_divisors_mul {m p : ℕ} (f : ℕ → ℕ) (hp : 2 ≤ p) (hd : (divisors p).val = 1 ::ₘ {p})
    (hc : Nat.Coprime m p) (hf : ∀ d, d ∣ m → f (d * p) = f d * f p) :
    ∑ x ∈ divisors (m * p), f x = (∑ d ∈ divisors m, f d) * (1 + f p) := by
  rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum, divisors_mul_val hp hd hc,
    Multiset.map_add, Multiset.sum_add, Multiset.map_map, Nat.mul_add, Nat.mul_one,
    ← Multiset.sum_map_mul_right]
  exact congrArg _ (congrArg _ (Multiset.map_congr rfl fun d hd =>
    hf d (Nat.mem_divisors.1 (Finset.mem_def.2 hd)).1))

/- ### Divisors of powers of two -/

theorem dvd_two_pow {d : ℕ} : ∀ k, d ∣ 2 ^ k → ∃ i, i ≤ k ∧ d = 2 ^ i
  | 0, h => ⟨0, Nat.le_refl 0, Nat.eq_one_of_dvd_one h⟩
  | k + 1, h => by
    rw [Nat.pow_succ] at h
    rcases Nat.mod_two_eq_zero_or_one d with h2 | h2
    · have hd : 2 * (d / 2) = d := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h2)
      have h' : d / 2 ∣ 2 ^ k := by
        apply Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 2)
        rw [Nat.mul_comm (d / 2) 2, hd]
        exact h
      obtain ⟨i, hi, hdi⟩ := dvd_two_pow k h'
      exact ⟨i + 1, Nat.succ_le_succ hi, by rw [Nat.pow_succ, ← hdi, Nat.mul_comm, hd]⟩
    · have hc : Nat.Coprime d 2 := by
        show Nat.gcd d 2 = 1
        rw [Nat.gcd_comm, Nat.gcd_rec, h2]
        exact Nat.gcd_one_left 2
      obtain ⟨i, hi, hdi⟩ := dvd_two_pow k (hc.dvd_of_dvd_mul_right h)
      exact ⟨i, Nat.le_succ_of_le hi, hdi⟩

theorem divisors_two_pow_succ_val (k : ℕ) :
    (divisors (2 ^ (k + 1))).val = 2 ^ (k + 1) ::ₘ (divisors (2 ^ k)).val := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hlt : 2 ^ k < 2 ^ (k + 1) := by
    rw [Nat.pow_succ, Nat.mul_two]
    exact Nat.lt_add_of_pos_right hpos
  apply (Multiset.Nodup.ext (Finset.nodup _) ?_).2 ?_
  · rw [Multiset.nodup_cons]
    refine ⟨fun h => ?_, Finset.nodup _⟩
    have := Nat.le_of_dvd hpos (Nat.mem_divisors.1 (Finset.mem_def.2 h)).1
    exact absurd hlt (Nat.not_lt_of_le this)
  · intro x
    rw [Multiset.mem_cons, ← Finset.mem_def, ← Finset.mem_def, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · rintro ⟨hx, -⟩
      obtain ⟨i, hi, rfl⟩ := dvd_two_pow (k + 1) hx
      rcases Nat.lt_or_ge i (k + 1) with h | h
      · exact Or.inr ⟨Nat.pow_dvd_pow 2 (Nat.lt_succ_iff.1 h), Nat.ne_of_gt hpos⟩
      · exact Or.inl (by rw [Nat.le_antisymm hi h])
    · rintro (rfl | ⟨hx, -⟩)
      · exact ⟨Nat.dvd_refl _, Nat.ne_of_gt (Nat.two_pow_pos _)⟩
      · exact ⟨Nat.dvd_trans hx (Nat.pow_dvd_pow 2 (Nat.le_succ k)), Nat.ne_of_gt (Nat.two_pow_pos _)⟩

theorem sum_divisors_two_pow (f : ℕ → ℕ) :
    ∀ k, ∑ d ∈ divisors (2 ^ k), f d = ∑ i ∈ Finset.range (k + 1), f (2 ^ i)
  | 0 => by
    rw [Nat.pow_zero, Nat.divisors_one]
    rfl
  | k + 1 => by
    have ih := sum_divisors_two_pow f k
    rw [Finset.sum_eq_multiset_sum] at ih ⊢
    rw [divisors_two_pow_succ_val, Multiset.map_cons, Multiset.sum_cons, ih]
    show _ = (Multiset.map (fun i => f (2 ^ i)) (Multiset.range (k + 1 + 1))).sum
    rw [Multiset.range_succ (k + 1), Multiset.map_cons, Multiset.sum_cons]
    rfl

theorem sigma_two_pow (i : ℕ) : σ 1 (2 ^ i) = ∑ j ∈ Finset.range (i + 1), 2 ^ j := by
  rw [sigma_one_apply]
  exact sum_divisors_two_pow (fun d => d) i

theorem sigma_two_pow_14 : σ 1 (2 ^ 14) = 32767 :=
  (sigma_two_pow 14).trans (by decide)

theorem sum_sigma_two_pow_14 : ∑ d ∈ divisors (2 ^ 14), σ 1 d = 65519 := by
  rw [sum_divisors_two_pow (σ 1) 14]
  exact (Finset.sum_congr rfl fun i _ => sigma_two_pow i).trans (by decide)

/- ### Primality by trial division -/

/-- `noDivBelow p k = true` iff no `m` with `2 ≤ m ≤ k + 1` divides `p`
(a bare `Nat.rec` so that the kernel can evaluate it cheaply). -/
def noDivBelow (p k : ℕ) : Bool :=
  Nat.rec true (fun k acc => (p % (k + 2) != 0) && acc) k

theorem noDivBelow_succ (p k : ℕ) :
    noDivBelow p (k + 1) = ((p % (k + 2) != 0) && noDivBelow p k) := rfl

theorem noDivBelow_spec (p : ℕ) :
    ∀ k, noDivBelow p k = true → ∀ m, 2 ≤ m → m ≤ k + 1 → ¬ m ∣ p
  | 0, _, m, h2, h1, _ => absurd (Nat.le_trans h2 h1) (by decide)
  | k + 1, h, m, h2, h1, hd => by
    rw [noDivBelow_succ, Bool.and_eq_true_iff, bne_iff_ne] at h
    rcases Nat.lt_or_ge m (k + 2) with hlt | hge
    · exact noDivBelow_spec p k h.2 m h2 (Nat.lt_succ_iff.1 hlt) hd
    · exact h.1 ((Nat.le_antisymm h1 hge) ▸ Nat.mod_eq_zero_of_dvd hd)

theorem divisors_val_eq_pair {p b : ℕ} (hp : 2 ≤ p) (hb : p < (b + 2) * (b + 2))
    (h : noDivBelow p b = true) : (divisors p).val = 1 ::ₘ {p} := by
  apply (Multiset.Nodup.ext (Finset.nodup _) ?_).2 ?_
  · rw [Multiset.nodup_cons, Multiset.mem_singleton]
    exact ⟨Nat.ne_of_lt hp, Multiset.nodup_singleton p⟩
  · intro x
    rw [Multiset.mem_cons, Multiset.mem_singleton, ← Finset.mem_def, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨k, hk⟩, -⟩
      rcases Nat.lt_or_ge x 2 with hx2 | hx2
      · rcases Nat.lt_or_ge x 1 with hx1 | hx1
        · rw [Nat.lt_one_iff.1 hx1, Nat.zero_mul] at hk
          exact absurd (hk ▸ hp) (by decide)
        · exact Or.inl (Nat.le_antisymm (Nat.lt_succ_iff.1 hx2) hx1)
      · rcases Nat.lt_or_ge x (b + 2) with hxb | hxb
        · exact absurd ⟨k, hk⟩ (noDivBelow_spec p b h x hx2 (Nat.lt_succ_iff.1 hxb))
        · rcases Nat.lt_or_ge k 2 with hk2 | hk2
          · rcases Nat.lt_or_ge k 1 with hk1 | hk1
            · rw [Nat.lt_one_iff.1 hk1, Nat.mul_zero] at hk
              exact absurd (hk ▸ hp) (by decide)
            · have hk1' : k = 1 := Nat.le_antisymm (Nat.lt_succ_iff.1 hk2) hk1
              rw [hk1', Nat.mul_one] at hk
              exact Or.inr hk.symm
          · have hkb : k < b + 2 := by
              rcases Nat.lt_or_ge k (b + 2) with hlt | hge
              · exact hlt
              · exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mul_le_mul hxb hge) hk.ge) hb)
                  (Nat.lt_irrefl _)
            exact absurd ⟨x, hk.trans (Nat.mul_comm x k)⟩
              (noDivBelow_spec p b h k hk2 (Nat.lt_succ_iff.1 hkb))
    · rintro (rfl | rfl)
      · exact ⟨Nat.one_dvd _, fun h0 => absurd (h0 ▸ hp) (by decide)⟩
      · exact ⟨Nat.dvd_refl _, fun h0 => absurd (h0 ▸ hp) (by decide)⟩

theorem sigma_one_one : σ 1 1 = 1 := by decide

theorem sigma_of_pair {p : ℕ} (hd : (divisors p).val = 1 ::ₘ {p}) : σ 1 p = p + 1 := by
  rw [sigma_one_apply, Finset.sum_eq_multiset_sum, hd, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton, Nat.add_comm]

theorem sum_sigma_of_pair {p : ℕ} (hd : (divisors p).val = 1 ::ₘ {p}) :
    ∑ d ∈ divisors p, σ 1 d = p + 2 := by
  rw [Finset.sum_eq_multiset_sum, hd, Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
    Multiset.sum_singleton, sigma_of_pair hd, sigma_one_one, Nat.add_comm]

/- ### The counterexample `2 ^ 14 * 4409 * 458009` -/

theorem divisors_4409 : (divisors 4409).val = 1 ::ₘ {4409} :=
  divisors_val_eq_pair (b := 65) (by decide) (by decide) (by decide)

theorem divisors_458009 : (divisors 458009).val = 1 ::ₘ {458009} :=
  divisors_val_eq_pair (b := 675) (by decide) (by decide) (by decide +kernel)

theorem coprime_1 : Nat.Coprime (2 ^ 14) 4409 := by decide
theorem coprime_2 : Nat.Coprime (2 ^ 14 * 4409) 458009 := by decide

theorem sigma_mul_pair {m p : ℕ} (hp : 2 ≤ p) (hd : (divisors p).val = 1 ::ₘ {p})
    (hc : Nat.Coprime m p) : σ 1 (m * p) = σ 1 m * (1 + p) := by
  rw [sigma_one_apply, sigma_one_apply]
  exact sum_divisors_mul (fun d => d) hp hd hc fun _ _ => rfl

theorem sum_sigma_mul_pair {m p : ℕ} (hp : 2 ≤ p) (hd : (divisors p).val = 1 ::ₘ {p})
    (hc : Nat.Coprime m p) :
    ∑ d ∈ divisors (m * p), σ 1 d = (∑ d ∈ divisors m, σ 1 d) * (1 + σ 1 p) :=
  sum_divisors_mul (σ 1) hp hd hc fun d hdm => by
    rw [sigma_mul_pair hp hd (hc.coprime_dvd_left hdm), sigma_of_pair hd, Nat.add_comm 1 p]

theorem sigma_value : σ 1 (2 ^ 14 * 4409 * 458009) = 32767 * (1 + 4409) * (1 + 458009) := by
  rw [sigma_mul_pair (by decide) divisors_458009 coprime_2,
    sigma_mul_pair (by decide) divisors_4409 coprime_1, sigma_two_pow_14]

theorem sum_sigma_value :
    ∑ d ∈ divisors (2 ^ 14 * 4409 * 458009), σ 1 d =
      65519 * (1 + (4409 + 1)) * (1 + (458009 + 1)) := by
  rw [sum_sigma_mul_pair (by decide) divisors_458009 coprime_2,
    sum_sigma_mul_pair (by decide) divisors_4409 coprime_1, sum_sigma_two_pow_14,
    sigma_of_pair divisors_4409, sigma_of_pair divisors_458009]

/- ### Relating `a` to `σ` -/

theorem cast_sum_nat (s : Multiset ℕ) (g : ℕ → ℕ) :
    (s.map fun d => (g d : ℤ)).sum = ((s.map g).sum : ℤ) := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons, Nat.cast_add, ih]

theorem a_eq (n : ℕ) :
    a n = 2 * (σ 1 n : ℤ) - ((∑ d ∈ divisors n, σ 1 d : ℕ) : ℤ) := by
  have key : a n + ((∑ d ∈ divisors n, σ 1 d : ℕ) : ℤ) = 2 * (σ 1 n : ℤ) := by
    unfold a
    rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum, ← cast_sum_nat,
      ← Multiset.sum_map_add,
      Multiset.map_congr rfl fun (d : ℕ) _ => Int.sub_add_cancel (2 * (d : ℤ)) (σ 1 d : ℤ),
      Multiset.map_congr rfl fun (d : ℕ) _ => Int.two_mul (d : ℤ),
      Multiset.sum_map_add, ← Int.two_mul, cast_sum_nat, sigma_one_apply,
      Finset.sum_eq_multiset_sum]
  rw [← key, Int.add_sub_cancel]

theorem a_counterexample : a (2 ^ 14 * 4409 * 458009) = 1 := by
  rw [a_eq, sigma_value, sum_sigma_value]
  decide

theorem oeis_296075_conjecture_0.disproof : ¬ (type_of% @oeis_296075_conjecture_0) := by
  intro h
  exact absurd ((h _).1 a_counterexample) (by decide)
