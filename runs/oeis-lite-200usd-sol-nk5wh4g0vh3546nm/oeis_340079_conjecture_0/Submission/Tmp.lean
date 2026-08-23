import FormalConjectures.Util.ProblemImports
open Nat BigOperators Finset

def aa (n : ℕ) : ℕ :=
  let A018804_n : ℕ := (Finset.Ico 1 (n + 1)).sum fun k => Nat.gcd k n
  n / Nat.gcd n (1 + A018804_n)

lemma sum_gcd_prime {p : ℕ} (hp : Nat.Prime p) :
    (Finset.Ico 1 (p + 1)).sum (fun k => Nat.gcd k p) = 2 * p - 1 := by
  have hg : ∀ k ∈ Finset.Ico 1 (p + 1), Nat.gcd k p = if k = p then p else 1 := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    split_ifs with h
    · subst k; simp
    · have hkp : k < p := by omega
      have hnd : ¬ p ∣ k := by
        intro hd
        have := Nat.le_of_dvd (by omega : 0 < k) hd
        omega
      exact (hp.coprime_iff_not_dvd.mpr hnd).symm.gcd_eq_one
  rw [Finset.sum_congr rfl hg, Finset.sum_ite]
  have heq : {k ∈ Finset.Ico 1 (p + 1) | k = p} = {p} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl
      exact ⟨⟨hp.one_le, by omega⟩, rfl⟩
  have hne : {k ∈ Finset.Ico 1 (p + 1) | ¬k = p} = Finset.Ico 1 p := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [heq, hne]
  simp [Nat.card_Ico]
  omega

lemma aa_prime {p : ℕ} (hp : Nat.Prime p) : aa p = 1 := by
  unfold aa
  rw [sum_gcd_prime hp]
  dsimp
  have hp2 := hp.two_le
  have : 1 + (2 * p - 1) = 2 * p := by omega
  rw [this]
  rw [Nat.gcd_eq_left_iff_dvd.mpr (by exact ⟨2, by omega⟩)]
  exact Nat.div_self hp.pos

private def phiAF : ArithmeticFunction ℕ :=
  ⟨Nat.totient, Nat.totient_zero⟩

private lemma phiAF_mult : phiAF.IsMultiplicative := by
  constructor
  · exact Nat.totient_one
  · intro m n h
    exact Nat.totient_mul h

private def gcdSumAF : ArithmeticFunction ℕ :=
  ArithmeticFunction.id * phiAF

private lemma gcdSumAF_mult : gcdSumAF.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_id.mul phiAF_mult

private def gcdSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, Nat.gcd k n

private lemma gcdSum_eq_divisor_sum (n : ℕ) :
    gcdSum n = ∑ d ∈ n.divisors, d * Nat.totient (n / d) := by
  unfold gcdSum
  rw [← Finset.sum_fiberwise_of_maps_to
    (t := n.divisors) (g := fun k => Nat.gcd n k) (f := fun k => Nat.gcd k n) (by
      intro k hk
      rw [Nat.mem_divisors]
      exact ⟨Nat.gcd_dvd_left _ _, by
        intro hn
        subst n
        simpa using hk⟩)]
  apply Finset.sum_congr rfl
  intro d hd
  have hconst :
      (∑ k ∈ Finset.range n with Nat.gcd n k = d, Nat.gcd k n) =
        #{k ∈ Finset.range n | Nat.gcd n k = d} * d := by
    apply Finset.sum_const_nat
    intro k hk
    rw [Nat.gcd_comm]
    exact (Finset.mem_filter.mp hk).2
  rw [hconst, ← Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]
  exact Nat.mul_comm _ _

private lemma gcdSum_eq_af (n : ℕ) : gcdSum n = gcdSumAF n := by
  rw [gcdSum_eq_divisor_sum]
  simp only [gcdSumAF, ArithmeticFunction.mul_apply, phiAF,
    ArithmeticFunction.id_apply, ZeroHom.coe_mk, Function.comp_apply]
  change (∑ d ∈ n.divisors, d * Nat.totient (n / d)) =
    ∑ x ∈ n.divisorsAntidiagonal, x.1 * Nat.totient x.2
  exact (Nat.sum_divisorsAntidiagonal (fun d q => d * Nat.totient q)).symm

private lemma gcdSum_mul {m n : ℕ} (h : Nat.Coprime m n) :
    gcdSum (m * n) = gcdSum m * gcdSum n := by
  simp only [gcdSum_eq_af]
  exact gcdSumAF_mult.map_mul_of_coprime h

private lemma shifted_gcdSum (n : ℕ) :
    (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n) = gcdSum n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [gcdSum]
  · rw [Finset.sum_Ico_succ_top hn (fun k => Nat.gcd k n)]
    have hrange : Finset.range n = insert 0 (Finset.Ico 1 n) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
      omega
    unfold gcdSum
    rw [hrange, Finset.sum_insert]
    · simp [Nat.add_comm]
    · simp

private lemma gcdSum_prime {p : ℕ} (hp : Nat.Prime p) :
    gcdSum p = 2 * p - 1 := by
  rw [← shifted_gcdSum]
  exact sum_gcd_prime hp

example : gcdSum 23492890653051 = 610815156979325 := by
  rw [show 23492890653051 = (((3 * 37) * 43) * 42307) * 116341 by norm_num]
  rw [gcdSum_mul (by norm_num [Nat.Coprime]),
    gcdSum_mul (by norm_num [Nat.Coprime]),
    gcdSum_mul (by norm_num [Nat.Coprime]),
    gcdSum_mul (by norm_num [Nat.Coprime])]
  rw [gcdSum_prime (by norm_num), gcdSum_prime (by norm_num),
    gcdSum_prime (by norm_num), gcdSum_prime (by norm_num),
    gcdSum_prime (by norm_num)]

private lemma witness_sum :
    (Finset.Ico 1 (23492890653051 + 1)).sum
      (fun k => Nat.gcd k 23492890653051) = 610815156979325 := by
  rw [shifted_gcdSum]
  rw [show 23492890653051 = (((3 * 37) * 43) * 42307) * 116341 by norm_num]
  rw [gcdSum_mul (by norm_num [Nat.Coprime]),
    gcdSum_mul (by norm_num [Nat.Coprime]),
    gcdSum_mul (by norm_num [Nat.Coprime]),
    gcdSum_mul (by norm_num [Nat.Coprime])]
  rw [gcdSum_prime (by norm_num), gcdSum_prime (by norm_num),
    gcdSum_prime (by norm_num), gcdSum_prime (by norm_num),
    gcdSum_prime (by norm_num)]

private lemma div_gcd_eq_one_of_dvd {n x : ℕ} (hn : 0 < n) (h : n ∣ x) :
    n / Nat.gcd n x = 1 := by
  rw [Nat.gcd_eq_left_iff_dvd.mpr h]
  exact Nat.div_self hn

private lemma aa_eq_one_of_dvd {n : ℕ} (hn : 0 < n)
    (h : n ∣ 1 + (Finset.Ico 1 (n + 1)).sum (fun k => Nat.gcd k n)) : aa n = 1 := by
  unfold aa
  exact div_gcd_eq_one_of_dvd hn h

private lemma witness_aa : aa 23492890653051 = 1 := by
  apply aa_eq_one_of_dvd (by norm_num)
  rw [witness_sum]
  exact ⟨26, by norm_num⟩

example : ¬ (∀ n : ℕ, aa n = 1 ↔ (n = 1 ∨ Nat.Prime n)) := by
  intro h
  have hc := (h 23492890653051).mp witness_aa
  rcases hc with h1 | hp
  · norm_num at h1
  · have hd : 3 ∣ 23492890653051 := by norm_num
    have := (Nat.dvd_prime hp).mp hd
    norm_num at this
