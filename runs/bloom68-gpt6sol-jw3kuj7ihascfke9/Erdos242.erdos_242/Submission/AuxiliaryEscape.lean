import Submission.AdjacentFactor

/-!
# A pointwise limitation of bounded auxiliary-divisor searches

For every fixed bound `B`, infinitely many hard **primes** avoid eligible
auxiliary divisors `q ≤ B` at *every* auxiliary index.  This does not avoid
larger divisors: a second Dirichlet construction below gives primes in the
very same factorial congruence class with a genuine eligible `q > B` and an
ordered Type-I solution.  Neither construction proves nor refutes the
unbounded auxiliary-divisor claim or the full Erdős–Straus conjecture.
`Submission.Spec` is not imported.
-/

namespace Erdos242

/-- Any divisor in the exact target class is too large to divide `6k`:
from `q ∣ M_i` and `q ∣ 6k` we would get `q ∣ i+1`, whereas
`q ≡ -1 (mod 4i+3)` forces `q ≥ 4i+2 > i+1`. -/
theorem eligible_auxiliary_not_dvd_six_k (k i q : ℕ)
    (hq : 1 < q) (hdiv : q ∣ auxiliaryFactor k i)
    (hres : q % (4 * i + 3) = 4 * i + 2) :
    ¬ q ∣ 6 * k := by
  intro hk
  have hprod : q ∣ (4 * i + 3) * (6 * k) := hk.mul_left _
  have hsum : q ∣ (4 * i + 3) * (6 * k) + (i + 1) := by
    simpa only [auxiliaryFactor] using hdiv
  have hidx : q ∣ i + 1 := (Nat.dvd_add_iff_left hprod).mpr (by
    simpa only [add_comm] using hsum)
  have hlarge : 4 * i + 2 ≤ q := by
    have hle := Nat.mod_le q (4 * i + 3)
    omega
  have hsmall : q ≤ i + 1 := Nat.le_of_dvd (by omega) hidx
  omega

/-- If `k` is a multiple of `B!`, no eligible divisor `q ≤ B` can occur
at *any* index, not just the first `B` indices. -/
theorem no_bounded_auxiliary_divisor_of_factorial (B s i q : ℕ)
    (hq : 1 < q) (hsmall : q ≤ B) :
    ¬(q ∣ auxiliaryFactor (B.factorial * s) i ∧
      q % (4 * i + 3) = 4 * i + 2) := by
  rintro ⟨hdiv, hres⟩
  have hqF : q ∣ B.factorial := Nat.dvd_factorial (by omega) hsmall
  have hk : q ∣ 6 * (B.factorial * s) := (hqF.mul_right s).mul_left 6
  exact (eligible_auxiliary_not_dvd_six_k (B.factorial * s) i q hq hdiv hres) hk

/-- For each fixed divisor cutoff and threshold, Dirichlet produces a
hard prime with **no eligible factor at or below that cutoff anywhere**.
The index `i` remains unrestricted. This rules out a bounded-`q` proof,
not the target existential statement with `q` allowed to grow with `p`. -/
theorem hard_primes_escape_bounded_auxiliary_divisors (B N : ℕ) :
    ∃ p k : ℕ, N < p ∧ p.Prime ∧ p = 24 * k + 1 ∧
      ∀ i q : ℕ, q ∣ auxiliaryFactor k i →
        q % (4 * i + 3) = 4 * i + 2 → B < q := by
  let F := B.factorial
  let A := 24 * F
  have hA : A ≠ 0 := by dsimp [A, F]; positivity
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := A) (a := 1) hA (by simp)
  have hA1 : 1 < A := by
    have hF : 0 < F := by dsimp [F]; exact Nat.factorial_pos _
    dsimp [A]
    omega
  have hpmod : p % A = 1 := by
    change p % A = 1 % A at hmod
    simpa only [Nat.mod_eq_of_lt hA1] using hmod
  let s := p / A
  have hpform : p = A * s + 1 := by
    calc
      p = p % A + A * (p / A) := (Nat.mod_add_div p A).symm
      _ = A * s + 1 := by rw [hpmod]; dsimp [s]; omega
  let k := F * s
  have hpk : p = 24 * k + 1 := by
    rw [hpform]
    dsimp [A, k]
    ring
  refine ⟨p, k, hpN, hp, hpk, ?_⟩
  intro i q hdiv hres
  have hq : 1 < q := by
    have hle := Nat.mod_le q (4 * i + 3)
    omega
  by_contra hn
  have hsmall : q ≤ B := by omega
  change q ∣ auxiliaryFactor (B.factorial * s) i at hdiv
  exact no_bounded_auxiliary_divisor_of_factorial B s i q hq hsmall ⟨hdiv, hres⟩

/-- The factorial congruence class above is **not** a source of global
counterexamples: for any `B` it also contains arbitrarily large hard primes
with an actual index-zero eligible divisor `q>B` and a restricted Type-I
ordered solution.  We use `F=(B+2)!=2(u+1)`, `q=6u+5`, `v=5u+4`,
`r=30u+29`.  Then `M₀(Fv)=qr`, `p₀=24Fv+1`, and the progression
`p=p₀+24Fq*w` is reduced modulo `24Fq`; Dirichlet supplies its primes.
All its eligible divisors, even at other indices, are `>B`. -/
theorem soluble_hard_primes_escaping_bounded_auxiliary_divisors (B N : ℕ) :
    ∃ p k q : ℕ, N < p ∧ p.Prime ∧ p = 24 * k + 1 ∧
      p % (24 * (B + 2).factorial) = 1 ∧
      B < q ∧ q ∣ auxiliaryFactor k 0 ∧ q % 3 = 2 ∧ Good p ∧
      ∀ i q' : ℕ, q' ∣ auxiliaryFactor k i →
        q' % (4 * i + 3) = 4 * i + 2 → B < q' := by
  let F := (B + 2).factorial
  have htwo : 2 ∣ F := Nat.dvd_factorial (by decide) (by omega)
  have hFpos : 0 < F := by dsimp [F]; exact Nat.factorial_pos _
  have hFdiv : 0 < F / 2 := by
    have hprod : 2 * (F / 2) = F := Nat.mul_div_cancel' htwo
    omega
  let u := F / 2 - 1
  have hF : F = 2 * (u + 1) := by
    have hu : u + 1 = F / 2 := by dsimp [u]; omega
    rw [hu]
    exact (Nat.mul_div_cancel' htwo).symm
  let q := 6 * u + 5
  let r := 30 * u + 29
  let v := 5 * u + 4
  let L := 24 * F
  let A := L * q
  let p₀ := L * v + 1
  have hM : auxiliaryFactor (F * v) 0 = q * r := by
    dsimp [auxiliaryFactor]
    rw [hF]
    dsimp [q, r, v]
    ring
  have hpq : 3 * p₀ + 1 = 4 * q * r := by
    calc
      3 * p₀ + 1 = (4 * 0 + 3) * (24 * (F * v) + 1) + 1 := by
        dsimp [p₀, L]
        ring
      _ = 4 * auxiliaryFactor (F * v) 0 :=
        (auxiliaryFactor_identity (F * v) 0).symm
      _ = 4 * q * r := by rw [hM]; ring
  have hA : A ≠ 0 := by dsimp [A, L, q]; positivity
  have hgap : p₀ + (48 * u ^ 2 + 96 * u + 47) = A := by
    dsimp [p₀, A, L, v, q]
    rw [hF]
    ring
  have hp₀lt : p₀ < A := by omega
  have hcop : p₀.Coprime A := by
    apply Nat.coprime_of_dvd
    intro ell hell hpdiv hAdiv
    have hor : ell ∣ L ∨ ell ∣ q :=
      (hell.dvd_mul).mp (by simpa only [A] using hAdiv)
    have hellone : ell ∣ 1 := by
      rcases hor with hL | hq
      · have hLV : ell ∣ L * v := hL.mul_right v
        have hsum : ell ∣ L * v + 1 := by simpa only [p₀] using hpdiv
        exact (Nat.dvd_add_iff_left hLV).mpr (by
          simpa only [add_comm] using hsum)
      · have hthree : ell ∣ 3 * p₀ := hpdiv.mul_left 3
        have hfour : ell ∣ 3 * p₀ + 1 := by
          rw [hpq]
          exact (hq.mul_left 4).mul_right r
        exact (Nat.dvd_add_iff_left hthree).mpr (by
          simpa only [add_comm] using hfour)
    exact (ne_of_gt hell.one_lt) (Nat.dvd_one.mp hellone)
  obtain ⟨p, hpN, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq N (q := A) (a := p₀) hA hcop
  have hpmod : p % A = p₀ := by
    change p % A = p₀ % A at hmod
    simpa only [Nat.mod_eq_of_lt hp₀lt] using hmod
  let w := p / A
  have hpform : p = A * w + p₀ := by
    calc
      p = p % A + A * (p / A) := (Nat.mod_add_div p A).symm
      _ = A * w + p₀ := by rw [hpmod]; dsimp [w]; omega
  let k := F * (v + q * w)
  have hpk : p = 24 * k + 1 := by
    calc
      p = A * w + p₀ := hpform
      _ = 24 * k + 1 := by dsimp [A, L, p₀, k]; ring
  have hqdiv : q ∣ auxiliaryFactor k 0 := by
    have heq : auxiliaryFactor k 0 = q * (r + 18 * F * w) := by
      calc
        auxiliaryFactor k 0 = auxiliaryFactor (F * v) 0 + q * (18 * F * w) := by
          dsimp [auxiliaryFactor, k]
          ring
        _ = q * r + q * (18 * F * w) := by rw [hM]
        _ = q * (r + 18 * F * w) := by ring
    exact ⟨r + 18 * F * w, heq⟩
  have hqres : q % (4 * 0 + 3) = 4 * 0 + 2 := by dsimp [q]; omega
  have hq : 1 < q := by dsimp [q]; omega
  have hAvoid : ∀ i q' : ℕ, q' ∣ auxiliaryFactor k i →
      q' % (4 * i + 3) = 4 * i + 2 → B < q' := by
    intro i q' hdiv hres
    have hq' : 1 < q' := by
      have hle := Nat.mod_le q' (4 * i + 3)
      omega
    by_contra hn
    have hsmall : q' ≤ B + 2 := by omega
    change q' ∣ auxiliaryFactor ((B + 2).factorial * (v + q * w)) i at hdiv
    exact no_bounded_auxiliary_divisor_of_factorial
      (B + 2) (v + q * w) i q' hq' hsmall ⟨hdiv, hres⟩
  have hL1 : 1 < L := by dsimp [L]; omega
  have hpformL : p = L * (v + q * w) + 1 := by rw [hpk]; dsimp [L, k]; ring
  have hpL : p % (24 * (B + 2).factorial) = 1 := by
    change p % L = 1
    rw [hpformL]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hL1]
  obtain ⟨x, c, hc, hcx, hI, hlo, hhi, hcong, hgood⟩ :=
    simple_typeI_of_auxiliary_divisor k 0 q hq hqdiv hqres
  have hgoodp : Good p := by rw [hpk]; exact hgood
  exact ⟨p, k, q, hpN, hp, hpk, hpL, hAvoid 0 q hqdiv hqres,
    hqdiv, by simpa only [zero_mul, zero_add] using hqres,
    hgoodp, hAvoid⟩

section CharacterConverseCounterexample
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- A concrete failure of the converse of the necessary Jacobi condition:
`p=193=24*8+1` is prime, `5 | M₅=1110`, and `(5/193)=-1`, but
**no** divisor of `M₅` is `-1 (mod 23)`.  The index 5 is within the
sharp range `7i+3≤6k`; the *different* index 0 does work, so `Good 193`.
An arbitrary nonresidue divisor must never be called an eligible divisor. -/
theorem jacobi_nonresidue_not_eligible_193 :
    (193).Prime ∧ 7 * 5 + 3 ≤ 6 * 8 ∧
      5 ∣ auxiliaryFactor 8 5 ∧ jacobiSym (5 : ℤ) 193 = -1 ∧
      (∀ q : ℕ, q ∣ auxiliaryFactor 8 5 →
        q % (4 * 5 + 3) ≠ 4 * 5 + 2) ∧ Good 193 := by
  have hmiss : ∀ q : ℕ, q ∣ auxiliaryFactor 8 5 →
      q % (4 * 5 + 3) ≠ 4 * 5 + 2 := by
    intro q hq
    have hdiv : q ∣ 1110 := by simpa [auxiliaryFactor] using hq
    have hmem : q ∈ Nat.divisors 1110 := Nat.mem_divisors.mpr ⟨hdiv, by norm_num⟩
    have hlist : (Nat.divisors 1110 : Finset ℕ) =
        {1, 2, 3, 5, 6, 10, 15, 30, 37, 74, 111, 185, 222, 370, 555, 1110} := by decide
    rw [hlist] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  have hgood : Good 193 := by
    have hd : 5 ∣ auxiliaryFactor 8 0 := by norm_num [auxiliaryFactor]
    have hr : 5 % (4 * 0 + 3) = 4 * 0 + 2 := by decide
    obtain ⟨_, _, _, _, _, _, _, _, hg⟩ :=
      simple_typeI_of_auxiliary_divisor 8 0 5 (by decide) hd hr
    simpa using hg
  exact ⟨by norm_num, by norm_num, by norm_num [auxiliaryFactor], by norm_num,
    hmiss, hgood⟩

end CharacterConverseCounterexample

end Erdos242
