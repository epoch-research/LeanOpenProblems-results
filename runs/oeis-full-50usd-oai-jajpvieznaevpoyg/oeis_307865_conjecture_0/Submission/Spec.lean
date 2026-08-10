import FormalConjectures.Util.ProblemImports

open Nat Finset ZMod
open scoped ArithmeticFunction.Carmichael

/--
A307865: $a(n)$ is the number of natural bases $b < 2n+1$ such that $b^n \equiv -1 \pmod{2n+1}$.
The bases $b$ are interpreted as $b \in \{1, 2, \dots, 2n\}$. We check the condition in the ring $\mathbb{Z}/(2n+1)\mathbb{Z}$.
-/
def a (n : ℕ) : ℕ :=
  let m : ℕ := 2 * n + 1
  -- The set of bases is $\{1, 2, \dots, 2n\} = \text{Ico } 1 m$.
  (Ico 1 m).filter (fun b : ℕ => (b : ZMod m) ^ n = (-1 : ZMod m)) |>.card

variable {n : ℕ}

/--
A natural number $m > 1$ is an absolute Euler pseudoprime if it is composite and
for all $b$ coprime to $m$, $b^{(m-1)/2} \equiv \pm 1 \pmod m$.
-/
def IsAbsoluteEulerPseudoprime (m : ℕ) : Prop :=
  m > 1 ∧ ¬ Nat.Prime m ∧
  (∀ b : ℕ, Nat.Coprime b m → (b : ZMod m) ^ ((m - 1) / 2) = 1 ∨ (b : ZMod m) ^ ((m - 1) / 2) = -1)

private lemma coprime_of_pow_eq_neg_one {m b k : ℕ} (hk : k ≠ 0)
    (hb : (b : ZMod m) ^ k = (-1 : ZMod m)) : Nat.Coprime b m := by
  have hp : (b : ZMod m) ^ (2 * k) = 1 := by
    rw [show (b : ZMod m) ^ (2 * k) = ((b : ZMod m) ^ k) ^ 2 by ring_nf]
    rw [hb]
    simp
  have h2k : 2 * k ≠ 0 := by omega
  have hub : IsUnit (b : ZMod m) := IsUnit.of_pow_eq_one hp h2k
  exact (ZMod.isUnit_iff_coprime b m).mp hub

private lemma carmichael_dvd_two_mul_of_abs {n : ℕ}
    (h : IsAbsoluteEulerPseudoprime (2 * n + 1)) :
    ArithmeticFunction.Carmichael (2 * n + 1) ∣ 2 * n := by
  have hm0 : 2 * n + 1 ≠ 0 := by omega
  haveI : NeZero (2 * n + 1) := ⟨hm0⟩
  rw [ArithmeticFunction.carmichael_eq_exponent hm0]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro u
  have hu := h.2.2 (u : ZMod (2 * n + 1)).val (ZMod.val_coe_unit_coprime u)
  have hv : (((u : ZMod (2 * n + 1)).val : ℕ) : ZMod (2 * n + 1)) = (u : ZMod (2 * n + 1)) :=
    ZMod.natCast_zmod_val _
  have hpow : (u : ZMod (2 * n + 1)) ^ n = 1 ∨ (u : ZMod (2 * n + 1)) ^ n = -1 := by
    have hhalf : ((2 * n + 1 - 1) / 2) = n := by omega
    simpa [hv, hhalf] using hu
  ext
  change ((u : ZMod (2 * n + 1)) ^ (2 * n) : ZMod (2 * n + 1)) = 1
  rw [show (u : ZMod (2 * n + 1)) ^ (2 * n) = ((u : ZMod (2 * n + 1)) ^ n) ^ 2 by ring_nf]
  rcases hpow with hp | hp <;> rw [hp] <;> simp

private lemma squarefree_of_abs {n : ℕ} (h : IsAbsoluteEulerPseudoprime (2 * n + 1)) :
    Squarefree (2 * n + 1) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hp2dvd
  have hcm : ArithmeticFunction.Carmichael (2 * n + 1) ∣ (2 * n + 1) - 1 := by
    simpa using carmichael_dvd_two_mul_of_abs h
  have hp_dvd_m : p ∣ 2 * n + 1 := by
    exact dvd_trans (dvd_mul_right p p) hp2dvd
  have hp2pow : p ^ 2 ∣ 2 * n + 1 := by
    simpa [pow_two] using hp2dvd
  have hpne2 : p ≠ 2 := by
    intro hpeq
    have h2dvd : 2 ∣ 2 * n + 1 := by simpa [hpeq] using hp_dvd_m
    rcases (even_iff_two_dvd.mpr h2dvd) with ⟨k, hk⟩
    omega
  have hp_pred : p ∣ (2 * n + 1) - 1 := by
    have hcdvd : ArithmeticFunction.Carmichael (p ^ 2) ∣ ArithmeticFunction.Carmichael (2 * n + 1) :=
      ArithmeticFunction.carmichael_dvd hp2pow
    have hval : ArithmeticFunction.Carmichael (p ^ 2) = p * (p - 1) := by
      rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two 2 hp hpne2]
      rw [Nat.totient_prime_pow hp (by norm_num : 0 < 2)]
      ring_nf
    have hmul : p * (p - 1) ∣ (2 * n + 1) - 1 := by
      rw [← hval]
      exact dvd_trans hcdvd hcm
    exact dvd_trans (dvd_mul_right p (p - 1)) hmul
  have hp_one : p = 1 := by
    have hsub : p ∣ (2 * n + 1) - ((2 * n + 1) - 1) := Nat.dvd_sub hp_dvd_m hp_pred
    have hdiff : (2 * n + 1) - ((2 * n + 1) - 1) = 1 := by omega
    simpa [hdiff] using hsub
  exact hp.ne_one hp_one

private lemma crt_mixed_not_pm_one {d e b n : ℕ} (hde : Nat.Coprime d e)
    (hd3 : 3 ≤ d) (he3 : 3 ≤ e)
    (hbd : (b : ZMod d) ^ n = (-1 : ZMod d)) :
    let cr := ZMod.chineseRemainder hde
    let x : ZMod (d * e) := cr.symm ((b : ZMod d), (1 : ZMod e))
    x ^ n ≠ (1 : ZMod (d * e)) ∧ x ^ n ≠ (-1 : ZMod (d * e)) := by
  intro cr x
  constructor
  · intro hx
    have hx1 := congrArg (fun z => (cr z).1) hx
    have hone : (-1 : ZMod d) = 1 := by
      simpa [x, hbd] using hx1
    have hz : (2 : ZMod d) = 0 := by
      linear_combination -hone
    have hdvd : d ∣ 2 := by
      simpa using (ZMod.natCast_eq_zero_iff 2 d).mp hz
    have hdle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · intro hx
    have hx2 := congrArg (fun z => (cr z).2) hx
    have hone : (1 : ZMod e) = -1 := by
      simpa [x] using hx2
    have hz : (2 : ZMod e) = 0 := by
      linear_combination hone
    have hdvd : e ∣ 2 := by
      simpa using (ZMod.natCast_eq_zero_iff 2 e).mp hz
    have hele : e ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega

private lemma crt_mixed_coprime {d e b : ℕ} (hde : Nat.Coprime d e) (hde0 : d * e ≠ 0)
    (hbde : Nat.Coprime b (d * e)) :
    let cr := ZMod.chineseRemainder hde
    let x : ZMod (d * e) := cr.symm ((b : ZMod d), (1 : ZMod e))
    Nat.Coprime x.val (d * e) := by
  intro cr x
  haveI : NeZero (d * e) := ⟨hde0⟩
  have hbd : Nat.Coprime b d := hbde.coprime_dvd_right (dvd_mul_right d e)
  have hunitb : IsUnit (b : ZMod d) := (ZMod.isUnit_iff_coprime b d).mpr hbd
  rcases hunitb with ⟨ub, hub⟩
  let up : (ZMod d × ZMod e)ˣ :=
    { val := ((ub : ZMod d), (1 : ZMod e))
      inv := ((↑(ub⁻¹) : ZMod d), (1 : ZMod e))
      val_inv := by ext <;> simp
      inv_val := by ext <;> simp }
  have hpair : IsUnit (((b : ZMod d), (1 : ZMod e)) : ZMod d × ZMod e) := by
    refine ⟨up, ?_⟩
    ext <;> simp [up, hub]
  have hxunit : IsUnit x := by
    simpa [x] using (RingHom.isUnit_map (cr.symm : ZMod d × ZMod e →+* ZMod (d * e)) hpair)
  exact (ZMod.isUnit_iff_coprime x.val (d * e)).mp (by simpa [ZMod.natCast_zmod_val] using hxunit)

private lemma no_neg_one_of_abs {n b : ℕ} (h : IsAbsoluteEulerPseudoprime (2 * n + 1)) :
    (b : ZMod (2 * n + 1)) ^ n ≠ (-1 : ZMod (2 * n + 1)) := by
  intro hb
  have hnpos : n ≠ 0 := by
    have := h.1
    omega
  have hbcoprime : Nat.Coprime b (2 * n + 1) := coprime_of_pow_eq_neg_one hnpos hb
  have hsquare : Squarefree (2 * n + 1) := squarefree_of_abs h
  have hm2 : 2 ≤ 2 * n + 1 := by omega
  rcases (Nat.not_prime_iff_exists_mul_eq hm2).mp h.2.1 with ⟨d, e, hdlt, helt, hmul⟩
  have hdpos : 0 < d := by
    by_contra hd0
    have : d = 0 := by omega
    subst d
    omega
  have hepos : 0 < e := by
    by_contra he0
    have : e = 0 := by omega
    subst e
    omega
  have hdne0 : d ≠ 0 := by omega
  have hene0 : e ≠ 0 := by omega
  have hdne1 : d ≠ 1 := by
    intro hd1
    subst d
    omega
  have hene1 : e ≠ 1 := by
    intro he1
    subst e
    omega
  have hd2 : 2 ≤ d := by omega
  have he2 : 2 ≤ e := by omega
  have hde : Nat.Coprime d e := by
    have : Squarefree (d * e) := by simpa [hmul] using hsquare
    exact Nat.coprime_of_squarefree_mul this
  have hnot2dvd_m : ¬ 2 ∣ 2 * n + 1 := by
    intro h2dvd
    rcases (even_iff_two_dvd.mpr h2dvd) with ⟨k, hk⟩
    omega
  have hd3 : 3 ≤ d := by
    have hdne2 : d ≠ 2 := by
      intro hd
      apply hnot2dvd_m
      subst d
      exact ⟨e, hmul.symm⟩
    omega
  have he3 : 3 ≤ e := by
    have hene2 : e ≠ 2 := by
      intro he
      apply hnot2dvd_m
      subst e
      exact ⟨d, by simpa [mul_comm] using hmul.symm⟩
    omega
  -- transport `hb` to the first CRT component
  have hbd : (b : ZMod d) ^ n = (-1 : ZMod d) := by
    let cr := ZMod.chineseRemainder hde
    have hbde : (b : ZMod (d * e)) ^ n = (-1 : ZMod (d * e)) := by
      rw [hmul]
      exact hb
    have hh := congrArg (fun z => (cr z).1) hbde
    simpa [cr, ZMod.chineseRemainder, map_pow] using hh
  let cr := ZMod.chineseRemainder hde
  let x : ZMod (d * e) := cr.symm ((b : ZMod d), (1 : ZMod e))
  haveI : NeZero (d * e) := ⟨mul_ne_zero hdne0 hene0⟩
  let c : ℕ := x.val
  have hxcoprime : Nat.Coprime c (d * e) := by
    dsimp [c]
    exact crt_mixed_coprime hde (mul_ne_zero hdne0 hene0) (by simpa [hmul] using hbcoprime)
  have habs_de : IsAbsoluteEulerPseudoprime (d * e) := by
    rw [hmul]
    exact h
  have hxpm := habs_de.2.2 c hxcoprime
  have hxpm' : x ^ n = (1 : ZMod (d * e)) ∨ x ^ n = (-1 : ZMod (d * e)) := by
    have hhalf : ((d * e - 1) / 2) = n := by
      rw [hmul]
      omega
    have hxval : ((c : ℕ) : ZMod (d * e)) = x := by
      dsimp [c]
      exact ZMod.natCast_zmod_val x
    simpa [hhalf, hxval] using hxpm
  have hxnot := crt_mixed_not_pm_one hde hd3 he3 hbd
  exact hxpm'.elim hxnot.1 hxnot.2

/--
oeis_307865_conjecture_0: Conjecture: if $2n+1$ is an absolute Euler pseudoprime, then $a(n) = 0$.
Note: this conjecture trivially holds for $n=0$ since $2 \cdot 0 + 1 = 1$, which is not an absolute Euler pseudoprime.
For a meaningful statement, one usually considers $n>3$.
-/
theorem oeis_307865_conjecture_0 (h : IsAbsoluteEulerPseudoprime (2 * n + 1)) : a n = 0 := by
  rw [a]
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro b hbmem hbpow
  exact no_neg_one_of_abs h hbpow
