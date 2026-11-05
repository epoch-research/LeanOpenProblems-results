import Submission.FactorTrisection

/-!
# Unimodular auxiliary factors and exact Type-I / Type-II translations

These are unconditional identities and conditional certificates, **not** an
all-prime solution of the Erdős–Straus conjecture. In particular this file
never imports `Submission.Spec` or assumes its open theorem. The full
Type-I-or-Type-II obligation is in `Submission/CoveringGap.lean`.
-/

namespace Erdos242

/-- For a hard integer `p=24k+1`, the auxiliary numbers
`((4i+3)p+1)/4`, written without truncating natural division. -/
def auxiliaryFactor (k i : ℕ) : ℕ := (4 * i + 3) * (6 * k) + i + 1

theorem auxiliaryFactor_identity (k i : ℕ) :
    4 * auxiliaryFactor k i = (4 * i + 3) * (24 * k + 1) + 1 := by
  unfold auxiliaryFactor
  ring

/-- The auxiliary numbers are consecutive terms of an arithmetic progression
with step exactly `p`, not with a fixed small step. -/
theorem auxiliaryFactor_increment (k i : ℕ) :
    auxiliaryFactor k (i + 1) = auxiliaryFactor k i + (24 * k + 1) := by
  unfold auxiliaryFactor
  ring

/-- A determinant-one relation between any two auxiliary factors; adjacent
indices in particular yield coprime factors. This identity alone does not
put any divisor in a prescribed residue class. -/
theorem auxiliaryFactor_det (k i j : ℕ) :
    (4 * j + 3) * auxiliaryFactor k i + i =
      (4 * i + 3) * auxiliaryFactor k j + j := by
  unfold auxiliaryFactor
  ring

theorem auxiliaryFactor_adjacent (k i : ℕ) :
    (4 * (i + 1) + 3) * auxiliaryFactor k i =
      (4 * i + 3) * auxiliaryFactor k (i + 1) + 1 := by
  have h := auxiliaryFactor_det k i (i + 1)
  omega

/-- Consecutive auxiliary factors are coprime for *every* `k`, even when
`24k+1` is not prime. -/
theorem auxiliaryFactor_coprime (k i : ℕ) :
    (auxiliaryFactor k i).Coprime (auxiliaryFactor k (i + 1)) := by
  apply Nat.coprime_of_dvd
  intro q hq hqi hqj
  have hleft : q ∣ (4 * (i + 1) + 3) * auxiliaryFactor k i := hqi.mul_left _
  have hright : q ∣ (4 * i + 3) * auxiliaryFactor k (i + 1) := hqj.mul_left _
  rw [auxiliaryFactor_adjacent] at hleft
  have hqone : q ∣ 1 := (Nat.dvd_add_iff_left hright).mpr (by
    simpa only [add_comm] using hleft)
  exact (ne_of_gt hq.one_lt) (Nat.dvd_one.mp hqone)

/-- More generally, the gcd of factors indexed by `i` and `j` divides their
index gap. This is a global statement about *all* consecutive offsets. -/
theorem auxiliaryFactor_gcd_dvd_gap (k i j : ℕ) (hij : i ≤ j) :
    Nat.gcd (auxiliaryFactor k i) (auxiliaryFactor k j) ∣ j - i := by
  let g := Nat.gcd (auxiliaryFactor k i) (auxiliaryFactor k j)
  have hgi : g ∣ auxiliaryFactor k i := Nat.gcd_dvd_left _ _
  have hgj : g ∣ auxiliaryFactor k j := Nat.gcd_dvd_right _ _
  have hdet : (4 * j + 3) * auxiliaryFactor k i =
      (4 * i + 3) * auxiliaryFactor k j + (j - i) := by
    have h := auxiliaryFactor_det k i j
    omega
  have hleft : g ∣ (4 * i + 3) * auxiliaryFactor k j + (j - i) := by
    rw [← hdet]
    exact hgi.mul_left _
  have hright : g ∣ (4 * i + 3) * auxiliaryFactor k j := hgj.mul_left _
  exact (Nat.dvd_add_iff_left hright).mpr (by
    simpa only [add_comm] using hleft)

private theorem residue_before_multiple (q h t : ℕ) (hhpos : 0 < h)
    (hqt : q + 1 = h * t) : q % h = h - 1 := by
  have ht : 0 < t := by
    by_contra hn
    have h0 : t = 0 := Nat.eq_zero_of_not_pos hn
    rw [h0, mul_zero] at hqt
    omega
  have hqform : q = (h - 1) + h * (t - 1) := by
    have hts : t - 1 + 1 = t := by omega
    have hhs : h - 1 + 1 = h := by omega
    have heq : h * (t - 1) + h = h * t := by
      calc
        h * (t - 1) + h = h * (t - 1 + 1) := by ring
        _ = h * t := by rw [hts]
    omega
  rw [hqform]
  simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : h - 1 < h)]


/-- An eligible (possibly composite) divisor of an auxiliary factor gives an
*ordered* Type-I solution with its witnessing `c` dividing `x` itself.  In
particular it also satisfies the weaker original condition `c ∣ x²`.
There is no assertion that such a divisor exists for every `k`. -/
theorem simple_typeI_of_auxiliary_divisor (k i q : ℕ)
    (hq : 1 < q) (hdiv : q ∣ auxiliaryFactor k i)
    (hres : q % (4 * i + 3) = 4 * i + 2) :
    ∃ x c : ℕ, 0 < c ∧ c ∣ x ∧ TypeI (24 * k + 1) x ∧
      24 * k + 1 < 4 * x ∧ 2 * x < 24 * k + 1 ∧
      (4 * x - (24 * k + 1)) ∣ 4 * c + 1 ∧ Good (24 * k + 1) := by
  let h := 4 * i + 3
  let c := auxiliaryFactor k i / q
  let t := (q + 1) / h
  have hhp : 0 < h := by dsimp [h]; omega
  have hqdiv : h ∣ q + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    change (q + 1) % (4 * i + 3) = 0
    rw [Nat.add_mod, hres, Nat.mod_eq_of_lt (by omega : 1 < 4 * i + 3)]
    have heq : 4 * i + 2 + 1 = 4 * i + 3 := by omega
    rw [heq, Nat.mod_self]
  have hqt : q + 1 = h * t := (Nat.mul_div_cancel' hqdiv).symm
  have hprod : q * c = auxiliaryFactor k i := Nat.mul_div_cancel' hdiv
  have hc : 0 < c := by
    have hM : 0 < auxiliaryFactor k i := by dsimp [auxiliaryFactor]; omega
    by_contra hn
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hn
    rw [hc0, mul_zero] at hprod
    omega
  have ht : 0 < t := by
    by_contra hn
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos hn
    rw [ht0, mul_zero] at hqt
    omega
  have hpc : h * (24 * k + 1) + 1 = 4 * q * c := by
    have hmain := auxiliaryFactor_identity k i
    dsimp [h] at *
    nlinarith only [hmain, hprod]
  obtain ⟨hI, hx, hxy, hyz, heq⟩ :=
    typeI_ordered_of_factor_product (24 * k + 1) h q c t
      (by omega) (by dsimp [h]; omega) hq hc ht hqt hpc
  have hG : Good (24 * k + 1) :=
    ⟨t * c, q * (t * c), (24 * k + 1) * q * c,
      hx, hxy, hyz, by simpa only [Nat.cast_mul] using heq⟩
  have hfac : h * (4 * (t * c)) = h * (24 * k + 1) + 4 * c + 1 := by
    calc
      h * (4 * (t * c)) = 4 * c * (h * t) := by ring
      _ = 4 * c * (q + 1) := by rw [← hqt]
      _ = h * (24 * k + 1) + 4 * c + 1 := by nlinarith only [hpc]
  have hlow : 24 * k + 1 < 4 * (t * c) := by nlinarith [hfac]
  have hhigh : 2 * (t * c) < 24 * k + 1 := by
    have hsum : h * (2 * (t * c)) = 2 * c * (q + 1) := by
      calc
        h * (2 * (t * c)) = 2 * c * (h * t) := by ring
        _ = 2 * c * (q + 1) := by rw [← hqt]
    have hqc : 2 * c ≤ q * c := Nat.mul_le_mul_right c (by omega : 2 ≤ q)
    nlinarith [hsum, hpc, hqc]
  have hdivc : (4 * (t * c) - (24 * k + 1)) ∣ 4 * c + 1 := by
    have hsub : (4 * (t * c) - (24 * k + 1)) + (24 * k + 1) =
        4 * (t * c) := Nat.sub_add_cancel (by omega)
    have hmul := congrArg (fun n : ℕ => h * n) hsub
    have heq : h * (4 * (t * c) - (24 * k + 1)) = 4 * c + 1 := by
      nlinarith only [hmul, hfac]
    exact ⟨h, by simpa only [mul_comm] using heq.symm⟩
  refine ⟨t * c, c, hc, ?_, hI, hlow, hhigh, hdivc, hG⟩
  exact ⟨t, by ring⟩

/-- The converse to `typeI_ordered_of_factor_product` for its **precise**
subfamily `c ∣ x`: each simple Type-I witness for `p ≡ 1 (mod 4)`
arises from an auxiliary factor `(hp+1)/4` with `h ≡ 3 (mod 4)`.
The assumption `c ∣ x`, not merely `c ∣ x²`, is indispensable. -/
theorem simple_typeI_factor_product (p x c : ℕ)
    (hp : p % 4 = 1) (hlo : p < 4 * x)
    (hcx : c ∣ x) (hac : 4 * x - p ∣ 4 * c + 1) :
    ∃ i q t : ℕ, 0 < t ∧ 1 < q ∧ x = t * c ∧
      q + 1 = (4 * i + 3) * t ∧ (4 * i + 3) * p + 1 = 4 * q * c := by
  let a := 4 * x - p
  let h := (4 * c + 1) / a
  let t := x / c
  have ha : 0 < a := by dsimp [a]; omega
  have hax : a + p = 4 * x := by dsimp [a]; omega
  have hca : a * h = 4 * c + 1 := Nat.mul_div_cancel' hac
  have hmoda : a % 4 = 3 := by dsimp [a]; omega
  have hmodh : h % 4 = 3 := by
    have hprod : (a % 4 * (h % 4)) % 4 = 1 := by
      rw [← Nat.mul_mod, hca]
      omega
    rw [hmoda] at hprod
    omega
  have hhge : 3 ≤ h := by
    calc
      3 = h % 4 := hmodh.symm
      _ ≤ h := Nat.mod_le h 4
  have hform : h = 4 * (h / 4) + 3 := by omega
  have hcxprod : c * t = x := Nat.mul_div_cancel' hcx
  have ht : 0 < t := by
    by_contra hn
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos hn
    rw [ht0, mul_zero] at hcxprod
    omega
  have hhtge : 3 ≤ h * t := by
    simpa only [mul_one] using Nat.mul_le_mul hhge (show 1 ≤ t by omega)
  let q := h * t - 1
  have hqt : q + 1 = h * t := by dsimp [q]; omega
  have hq : 1 < q := by dsimp [q]; omega
  have hpcadd : h * p + 1 + 4 * c = 4 * q * c + 4 * c := by
    calc
      h * p + 1 + 4 * c = h * (p + a) := by nlinarith only [hca]
      _ = h * (4 * x) := by rw [add_comm, hax]
      _ = 4 * c * (h * t) := by rw [← hcxprod]; ring
      _ = 4 * c * (q + 1) := by rw [← hqt]
      _ = 4 * q * c + 4 * c := by ring
  have hpc : h * p + 1 = 4 * q * c := by omega
  refine ⟨h / 4, q, t, ht, hq, ?_, ?_, ?_⟩
  · simpa only [mul_comm] using hcxprod.symm
  · rw [← hform]
    exact hqt
  · rw [← hform]
    exact hpc

/-- An exact location bound for the auxiliary factor of any simple Type-I
product: `7i + 3 ≤ 6k`. The case `4x-p=3` requires the additional
observation that `x=6k+1` is odd and the cofactor `t=x/c` cannot be 1.
The `4x-p=7`, `t=1` family below attains equality, including for
infinitely many hard primes. -/
theorem factor_product_index_sharp (k i q c t : ℕ)
    (ht : 0 < t)
    (hqt : q + 1 = (4 * i + 3) * t)
    (hpc : (4 * i + 3) * (24 * k + 1) + 1 = 4 * q * c) :
    7 * i + 3 ≤ 6 * k := by
  let h := 4 * i + 3
  let p := 24 * k + 1
  let x := t * c
  have hsum : h * (4 * x) = h * p + 4 * c + 1 := by
    calc
      h * (4 * x) = 4 * c * (h * t) := by dsimp [x]; ring
      _ = 4 * c * (q + 1) := by rw [← hqt]
      _ = h * p + 4 * c + 1 := by dsimp [h, p]; nlinarith only [hpc]
  have hlo : p < 4 * x := by
    have hhpos : 0 < h := by dsimp [h]; omega
    nlinarith only [hsum, hhpos]
  let a := 4 * x - p
  have haeq : a + p = 4 * x := by dsimp [a]; omega
  have hca : h * a = 4 * c + 1 := by
    have hmul := congrArg (fun n : ℕ => h * n) haeq
    nlinarith only [hsum, hmul]
  have hamod : a % 4 = 3 := by dsimp [a, p]; omega
  have ha3 : 3 ≤ a := by
    calc
      3 = a % 4 := hamod.symm
      _ ≤ a := Nat.mod_le a 4
  have hcle : c ≤ x := by
    dsimp [x]
    have hmult := Nat.mul_le_mul_right c (show 1 ≤ t by omega)
    calc
      c = 1 * c := by ring
      _ ≤ t * c := hmult
  have hcd : 4 * c ≤ 4 * x := Nat.mul_le_mul_left 4 hcle
  have habound : (4 * i + 2) * a ≤ p + 1 := by
    dsimp [h] at hca
    nlinarith only [hca, haeq, hcd]
  by_cases heq : a = 3
  · have hxval : x = 6 * k + 1 := by dsimp [p] at haeq; omega
    have hlin : 3 * (4 * i + 3) = 4 * c + 1 := by
      simpa only [heq, h, mul_comm] using hca
    have ht3 : 3 ≤ t := by
      by_contra hn
      have hcases : t = 1 ∨ t = 2 := by omega
      rcases hcases with h1 | h2
      · have hcval : x = c := by simp [x, h1]
        omega
      · have hx_even : x = 2 * c := by simp [x, h2]
        omega
    have htc : 3 * c ≤ x := by
      dsimp [x]
      exact Nat.mul_le_mul_right c ht3
    nlinarith only [hlin, htc, hxval]
  · have ha7 : 7 ≤ a := by omega
    have hsmall7 : 7 * (4 * i + 2) ≤ a * (4 * i + 2) :=
      Nat.mul_le_mul_right _ ha7
    dsimp [p] at habound
    nlinarith only [habound, hsmall7]


/-- The weaker `i<2k` search cutoff follows immediately from the
sharper `7i+3≤6k` theorem. -/
theorem factor_product_index_bound (k i q c t : ℕ)
    (ht : 0 < t)
    (hqt : q + 1 = (4 * i + 3) * t)
    (hpc : (4 * i + 3) * (24 * k + 1) + 1 = 4 * q * c) :
    i < 2 * k := by
  have hs := factor_product_index_sharp k i q c t ht hqt hpc
  omega
/-- The index bound holds for **every** eligible divisor, not only for the
one produced by the reverse Type-I translation. Consequently *no* divisor
at a later auxiliary factor can meet its `-1` residue target. -/
theorem auxiliary_divisor_index_sharp (k i q : ℕ)
    (hdiv : q ∣ auxiliaryFactor k i)
    (hres : q % (4 * i + 3) = 4 * i + 2) :
    7 * i + 3 ≤ 6 * k := by
  let h := 4 * i + 3
  let c := auxiliaryFactor k i / q
  let t := (q + 1) / h
  have hhdvd : h ∣ q + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    change (q + 1) % (4 * i + 3) = 0
    rw [Nat.add_mod, hres, Nat.mod_eq_of_lt (by omega : 1 < 4 * i + 3)]
    have heq : 4 * i + 2 + 1 = 4 * i + 3 := by omega
    rw [heq, Nat.mod_self]
  have hqt : q + 1 = h * t := (Nat.mul_div_cancel' hhdvd).symm
  have ht : 0 < t := by
    by_contra hn
    have hzero : t = 0 := Nat.eq_zero_of_not_pos hn
    rw [hzero, mul_zero] at hqt
    omega
  have hprod : q * c = auxiliaryFactor k i := Nat.mul_div_cancel' hdiv
  have hpc : h * (24 * k + 1) + 1 = 4 * q * c := by
    have hmain := auxiliaryFactor_identity k i
    dsimp [h] at *
    nlinarith only [hmain, hprod]
  exact factor_product_index_sharp k i q c t ht hqt hpc




/-- **Exact** finite (but growing with `k`) factor test for the simple
`c ∣ x` subfamily of Type I at a hard integer. Only indices satisfying
`7i+3≤6k` need be searched. In contrast, the original conjecture
allows *all* `c ∣ x²` and all Type-II divisors, so this restricted
equivalence is **not** a characterization of `Good p`. -/
theorem simple_typeI_iff_auxiliary_divisor (k : ℕ) :
    (∃ x c : ℕ, 0 < c ∧ c ∣ x ∧
        24 * k + 1 < 4 * x ∧ 2 * x < 24 * k + 1 ∧
        (4 * x - (24 * k + 1)) ∣ 4 * c + 1) ↔
      ∃ i q : ℕ, 7 * i + 3 ≤ 6 * k ∧ 1 < q ∧ q ∣ auxiliaryFactor k i ∧
        q % (4 * i + 3) = 4 * i + 2 := by
  constructor
  · rintro ⟨x, c, hc, hcx, hlo, hhi, hdiv⟩
    obtain ⟨i, q, t, ht, hq, hxt, hqt, hpc⟩ :=
      simple_typeI_factor_product (24 * k + 1) x c
        (by omega) hlo hcx hdiv
    have hi : 7 * i + 3 ≤ 6 * k := factor_product_index_sharp k i q c t ht hqt hpc
    have hM : q * c = auxiliaryFactor k i := by
      have heq := auxiliaryFactor_identity k i
      nlinarith only [heq, hpc]
    have hres := residue_before_multiple q (4 * i + 3) t (by omega) hqt
    have hsub : (4 * i + 3) - 1 = 4 * i + 2 := by omega
    rw [hsub] at hres
    exact ⟨i, q, hi, hq, ⟨c, hM.symm⟩, hres⟩
  · rintro ⟨i, q, hi, hq, hdiv, hres⟩
    obtain ⟨x, c, hc, hcx, hI, hlo, hhi, hmod, hgood⟩ :=
      simple_typeI_of_auxiliary_divisor k i q hq hdiv hres
    exact ⟨x, c, hc, hcx, hlo, hhi, hmod⟩


/-- The factor-index bound `7i+3≤6k` is attained by an explicit Type-I
family. Here `a=4x-p=7`, `c=x=42n+26`, `h=24n+15`, and `q=h-1`.
Selected prime values give strictly ordered solutions, not an all-prime
argument. -/
theorem auxiliary_sharp_family (n : ℕ) :
    7 * (6 * n + 3) + 3 = 6 * (7 * n + 4) ∧
      (24 * n + 14) ∣ auxiliaryFactor (7 * n + 4) (6 * n + 3) ∧
      (24 * n + 14) % (4 * (6 * n + 3) + 3) = 4 * (6 * n + 3) + 2 ∧
      TypeI (168 * n + 97) (42 * n + 26) ∧ Good (168 * n + 97) := by
  have hax : 4 * (42 * n + 26) - (168 * n + 97) = 7 := by omega
  have hI : TypeI (168 * n + 97) (42 * n + 26) := by
    refine ⟨42 * n + 26, by omega, ?_, ?_⟩
    · exact ⟨42 * n + 26, by ring⟩
    · rw [hax]
      exact ⟨24 * n + 15, by ring⟩
  have hG : Good (168 * n + 97) :=
    good_of_typeI (168 * n + 97) (42 * n + 26)
      (by omega) (by omega) (by omega) hI
  refine ⟨by omega, ?_, ?_, hI, hG⟩
  · refine ⟨42 * n + 26, ?_⟩
    unfold auxiliaryFactor
    ring
  · rw [Nat.mod_eq_of_lt (by omega : 24 * n + 14 < 4 * (6 * n + 3) + 3)]
    omega

/-- Dirichlet supplies arbitrarily large *prime* equality cases, since
`gcd(97,168)=1`. Equality in the new bound holds for their indicated
Type-I factors; primes outside this progression remain unrestricted. -/
theorem infinitely_many_sharp_auxiliary (N : ℕ) :
    ∃ p k i q : ℕ, N < p ∧ p.Prime ∧ p = 24 * k + 1 ∧
      7 * i + 3 = 6 * k ∧ q ∣ auxiliaryFactor k i ∧
      q % (4 * i + 3) = 4 * i + 2 ∧ Good p := by
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := 168) (a := 97)
      (by decide) (by decide)
  have hrem : p % 168 = 97 := by simpa [Nat.ModEq] using hmod
  let n := p / 168
  have hpform : p = 168 * n + 97 := by dsimp [n]; omega
  obtain ⟨hsharp, hdiv, hres, hI, hgood⟩ := auxiliary_sharp_family n
  refine ⟨p, 7 * n + 4, 6 * n + 3, 24 * n + 14, hpN, hp, ?_,
    hsharp, hdiv, hres, ?_⟩
  · omega
  · rwa [hpform]

/-- **Bidirectional** shifted-divisor duality for every `p` and `m>0`,
without assuming that `p` is prime. Put `h=4m-1` and `e=m²/d`.
The congruence `h∣p+4d` is *equivalent*, not merely sufficient, to
`h∣4pe+1`. This uses `16m² = (4m-1)(4m+1)+1` and the essential
coprimality `gcd(4m-1,4e)=1`. It does not ensure that either factor
exists for an arbitrary hard prime. -/
theorem typeII_modular_dual (p m d : ℕ) (hm : 0 < m) (hdsq : d ∣ m ^ 2) :
    (4 * m - 1 ∣ p + 4 * d) ↔
      (4 * m - 1 ∣ 4 * p * (m ^ 2 / d) + 1) := by
  let h := 4 * m - 1
  let e := m ^ 2 / d
  have hh : h + 1 = 4 * m := by dsimp [h]; omega
  have hde : d * e = m ^ 2 := Nat.mul_div_cancel' hdsq
  have hcop4m : h.Coprime (4 * m) := by
    have hc : h.Coprime (h + 1) :=
      (Nat.coprime_self_add_right).mpr (by simp)
    rwa [hh] at hc
  have hcop4 : h.Coprime 4 := hcop4m.of_dvd_right (dvd_mul_right 4 m)
  have hcopm : h.Coprime m := hcop4m.of_dvd_right (dvd_mul_left m 4)
  have hediv : e ∣ m ^ 2 := ⟨d, by nlinarith only [hde]⟩
  have hcope : h.Coprime e := (hcopm.pow_right 2).of_dvd_right hediv
  have hcop4e : h.Coprime (4 * e) := hcop4.mul_right hcope
  have hident : h * (4 * m + 1) + 1 = 16 * m ^ 2 := by
    have hmul := congrArg (fun n : ℕ => n * (4 * m + 1)) hh
    nlinarith only [hmul]
  have hkey : 4 * e * (p + 4 * d) =
      (4 * p * e + 1) + h * (4 * m + 1) := by
    calc
      4 * e * (p + 4 * d) = 4 * p * e + 16 * (d * e) := by ring
      _ = 4 * p * e + 16 * m ^ 2 := by rw [hde]
      _ = (4 * p * e + 1) + h * (4 * m + 1) := by omega
  change (h ∣ p + 4 * d) ↔ (h ∣ 4 * p * e + 1)
  constructor
  · intro hd
    have hmul : h ∣ 4 * e * (p + 4 * d) := hd.mul_left _
    rw [hkey] at hmul
    exact (Nat.dvd_add_iff_left (dvd_mul_right h _)).mpr (by
      simpa only [add_comm] using hmul)
  · intro he
    have hsum : h ∣ (4 * p * e + 1) + h * (4 * m + 1) :=
      dvd_add he (dvd_mul_right h _)
    rw [← hkey] at hsum
    exact hcop4e.dvd_of_dvd_mul_left hsum

section FiniteObstruction
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- A certified *local* failure of a tempting adjacent-factor shortcut:
`p=2521=24*105+1` is prime, and the first **three** coprime auxiliary
factors miss their respective required divisor classes. The fourth works.
This is not an Erdős–Straus counterexample. -/
theorem auxiliary_2521_first_three_miss (i q : ℕ)
    (hi : i < 3) (hqd : q ∣ auxiliaryFactor 105 i) :
    q % (4 * i + 3) ≠ 4 * i + 2 := by
  interval_cases i
  · have hd : q ∣ 1891 := by simpa [auxiliaryFactor] using hqd
    have hmem : q ∈ Nat.divisors 1891 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    have hlist : (Nat.divisors 1891 : Finset ℕ) = {1, 31, 61, 1891} := by decide
    rw [hlist] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h <;> simp [h]
  · have hd : q ∣ 4412 := by simpa [auxiliaryFactor] using hqd
    have hmem : q ∈ Nat.divisors 4412 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    have hlist : (Nat.divisors 4412 : Finset ℕ) = {1, 2, 4, 1103, 2206, 4412} := by decide
    rw [hlist] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h <;> simp [h]
  · have hd : q ∣ 6933 := by simpa [auxiliaryFactor] using hqd
    have hmem : q ∈ Nat.divisors 6933 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    have hlist : (Nat.divisors 6933 : Finset ℕ) = {1, 3, 2311, 6933} := by decide
    rw [hlist] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h <;> simp [h]

/-- At the *next* auxiliary factor of the same soluble prime, `29 ∣ 9454`
and `29 ≡ -1 (mod 15)` yield the genuine ordered Type-I identity with
`x=652,c=326` (already obtained by another construction in
`FactorTrisection.lean`). -/
theorem auxiliary_2521_fourth_works :
    29 ∣ auxiliaryFactor 105 3 ∧
      29 % (4 * 3 + 3) = 4 * 3 + 2 ∧ Good 2521 := by
  have hd : 29 ∣ auxiliaryFactor 105 3 := by norm_num [auxiliaryFactor]
  have hr : 29 % (4 * 3 + 3) = 4 * 3 + 2 := by decide
  obtain ⟨x, c, hc, hcx, hI, hlo, hhi, hdiv, hG⟩ :=
    simple_typeI_of_auxiliary_divisor 105 3 29 (by decide) hd hr
  exact ⟨hd, hr, by simpa using hG⟩

end FiniteObstruction







end Erdos242
