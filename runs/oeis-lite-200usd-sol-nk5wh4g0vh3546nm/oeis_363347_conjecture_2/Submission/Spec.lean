import FormalConjectures.Util.ProblemImports

open Rat Nat

/--
Helper function for A363347, which computes the denominator $R_k(n)$ of the continued fraction expression.
For $2 \le k \le n-1$, $R_k(n)$ is defined recursively:
$$R_k(n) = k - \frac{k+1}{R_{k+1}(n)}$$
The base case is $R_{n-1}(n) = (n-1) - \frac{n}{-4}$.
-/
def continued_fraction_denominator (n k : ℕ) : ℚ :=
  if n ≤ 2 then 0
  else
    -- The recursive descent involves terms from $k=n-1$ down to $k=2$.
    if 2 ≤ k ∧ k ≤ n - 1 then
      -- Base Case: k = n - 1.
      if k = n - 1 then
        -- R_{n-1} = (n-1) + n/4
        (k : ℚ) + (n : ℚ) / 4
      -- Recursive Step: 2 <= k < n - 1.
      else
        let R_next := continued_fraction_denominator n (k + 1)
        -- R_k = k - (k+1) / R_{k+1}
        (k : ℚ) - (k + 1 : ℚ) / R_next
    else 0
termination_by n - k

/--
A363347: Denominator of the continued fraction
$$\frac{1}{2 - \frac{3}{3 - \frac{4}{4 - \frac{5}{\dots - \frac{n-1}{(n-1) - \frac{n}{-4}}}}}} $$
The value of the continued fraction is $C_n = 1/R_2(n)$. If $R_2(n) = N/D$ in reduced form, $C_n = D/N$.
The sequence $a(n)$ is the denominator of the final fraction, which is $\vert N \vert$.
-/
noncomputable def A363347 (n : ℕ) : ℕ :=
  if n ≤ 2 then 0 -- The sequence is indexed starting from $n=3$.
  else
    let R2 := continued_fraction_denominator n 2
    R2.num.natAbs


private def cpair (n : ℕ) : ℕ → ℤ × ℤ
  | 0 => (5 * (n : ℤ) - 4, 4)
  | t + 1 =>
      let u := cpair n t
      let k : ℤ := (n - 2 - t : ℕ)
      (k * u.1 - (k + 1) * u.2, u.1)

#eval cpair 10 7

private lemma cpair_succ (n t : ℕ) :
    cpair n (t+1) =
      let u := cpair n t
      let k : ℤ := (n - 2 - t : ℕ)
      (k * u.1 - (k+1)*u.2, u.1) := by
  rw [cpair]

private lemma base_invariant (n : ℕ) (hn : 3 ≤ n) :
    let u := cpair n 0
    let k : ℤ := n-1
    (k-1) * u.1 - k * (k-2) * u.2
      = (n : ℤ)^2 + 2*n - 4 := by
  dsimp [cpair]
  ring

private lemma cpair_invariant (n t : ℕ) (hn : 3 ≤ n) (ht : t ≤ n-3) :
    let u := cpair n t
    let k : ℤ := n-1-t
    (k-1) * u.1 - k * (k-2) * u.2
      = (n : ℤ)^2 + 2*n - 4 := by
  induction t with
  | zero => simpa using base_invariant n hn
  | succ t ih =>
    have ht' : t ≤ n-3 := by omega
    have htn : t ≤ n-4 := by omega
    specialize ih ht'
    rw [cpair_succ]
    dsimp only
    dsimp only at ih
    have hcoef : ((n - 2 - t : ℕ) : ℤ) =
        (n : ℤ) - 2 - (t : ℤ) := by omega
    rw [hcoef]
    push_cast
    push_cast at ih
    ring_nf at ih ⊢
    exact ih

private lemma cpair_final_fst (n : ℕ) (hn : 3 ≤ n) :
    (cpair n (n-3)).1 = (n : ℤ)^2 + 2*n - 4 := by
  have h := cpair_invariant n (n-3) hn (by omega)
  dsimp only at h
  have hk : (n : ℤ) - 1 - ((n-3 : ℕ) : ℤ) = 2 := by omega
  rw [hk] at h
  norm_num at h
  exact h

private lemma cpair_pos (n t : ℕ) (hn : 3 ≤ n) (ht : t ≤ n-3) :
    0 < (cpair n t).1 ∧ 0 < (cpair n t).2 := by
  induction t with
  | zero =>
      simp [cpair]
      omega
  | succ t ih =>
      have ht' : t ≤ n-3 := by omega
      have htn : t ≤ n-4 := by omega
      specialize ih ht'
      have hinv := cpair_invariant n (t+1) hn ht
      rw [cpair_succ]
      rw [cpair_succ] at hinv
      dsimp only at hinv ⊢
      have hcoef : ((n - 2 - t : ℕ) : ℤ) =
          (n : ℤ) - 2 - (t : ℤ) := by omega
      rw [hcoef] at hinv ⊢
      push_cast at hinv
      constructor
      · have hk : (2 : ℤ) ≤ (n : ℤ) - 2 - t := by omega
        have hf : 0 < (n : ℤ)^2 + 2*n - 4 := by nlinarith
        have hb : 0 ≤ ((n : ℤ) - 2 - t) * ((n : ℤ) - 2 - t - 2) *
            (cpair n t).1 := by
          exact mul_nonneg (mul_nonneg (by omega) (by omega)) ih.1.le
        nlinarith
      · exact ih.1

private lemma continued_eq_cpair (n t : ℕ) (hn : 3 ≤ n) (ht : t ≤ n-3) :
    continued_fraction_denominator n (n-1-t) =
      ((cpair n t).1 : ℚ) / (cpair n t).2 := by
  induction t with
  | zero =>
      rw [continued_fraction_denominator]
      simp only [show ¬n ≤ 2 by omega, ↓reduceIte]
      have hk : n - 1 - 0 = n - 1 := by omega
      rw [hk]
      simp only [show 2 ≤ n-1 by omega, le_refl, and_self, ↓reduceIte]
      norm_num [cpair]
      have hncast : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hncast]
      ring
  | succ t ih =>
      have ht' : t ≤ n-3 := by omega
      have htn : t ≤ n-4 := by omega
      specialize ih ht'
      rw [continued_fraction_denominator]
      simp only [show ¬n ≤ 2 by omega, ↓reduceIte]
      have hk2 : 2 ≤ n - 1 - (t+1) := by omega
      have hkle : n - 1 - (t+1) ≤ n-1 := by omega
      simp only [hk2, hkle, and_self, ↓reduceIte]
      have hkne : n - 1 - (t+1) ≠ n-1 := by omega
      simp only [hkne, ↓reduceIte]
      have hks : n - 1 - (t+1) + 1 = n-1-t := by omega
      rw [hks, ih, cpair_succ]
      dsimp only
      have hcoef : ((n - 2 - t : ℕ) : ℤ) =
          (n : ℤ) - 2 - (t : ℤ) := by omega
      have hkcast : ((n - 1 - (t+1) : ℕ) : ℚ) =
          ((n - 2 - t : ℕ) : ℚ) := by congr 1 <;> omega
      rw [hkcast]
      have ha := (cpair_pos n t hn ht').1
      have haq : ((cpair n t).1 : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
      field_simp
      push_cast
      ring

private def pseq (n j : ℕ) : ℤ := (cpair n (n-3-j)).1

private lemma pseq_zero (n : ℕ) (hn : 3 ≤ n) :
    pseq n 0 = (n : ℤ)^2 + 2*n-4 := by
  simp only [pseq, Nat.sub_zero]
  exact cpair_final_fst n hn

private lemma pseq_one (n : ℕ) (hn : 4 ≤ n) :
    pseq n 1 = (cpair n (n-3)).2 := by
  rw [show n-3 = (n-4)+1 by omega, cpair_succ]
  simp only [pseq]
  congr 1

private lemma pseq_rec (n j : ℕ) (hn : 3 ≤ n) (hj : j+2 ≤ n-3) :
    pseq n j = (j+2 : ℤ) * pseq n (j+1) -
      (j+3 : ℤ) * pseq n (j+2) := by
  have hr : n-3-j = (n-3-(j+1)) + 1 := by omega
  rw [pseq, hr, cpair_succ]
  dsimp only
  rw [show (cpair n (n - 3 - (j+1))).2 =
      (cpair n (n - 3 - (j+2))).1 by
    rw [show n-3-(j+1) = (n-3-(j+2))+1 by omega, cpair_succ]]
  simp only [pseq]
  have hcNat : n - 2 - (n - 3 - (j+1)) = j+2 := by omega
  have hc : ((n - 2 - (n - 3 - (j+1)) : ℕ) : ℤ) = (j+2 : ℤ) := by
    exact_mod_cast hcNat
  rw [hc]
  ring

private lemma factorial_relation
    (a : ℕ → ℤ) (m : ℕ)
    (hrec : ∀ j, j+2 ≤ m →
      a j = (j+2 : ℤ)*a (j+1) - (j+3 : ℤ)*a (j+2)) :
    ∀ j, j < m → ∃ z : ℤ,
      ((j+1)! : ℤ) * a j = 2*(j : ℤ)*a 1 + a 0*z := by
  intro j
  induction j using Nat.twoStepInduction with
  | zero =>
      intro _
      refine ⟨1, ?_⟩
      norm_num
  | one =>
      intro _
      refine ⟨0, ?_⟩
      norm_num
  | more j ih0 ih1 =>
      intro hj
      obtain ⟨z0, hz0⟩ := ih0 (by omega)
      obtain ⟨z1, hz1⟩ := ih1 (by omega)
      have hr := hrec j (by omega)
      refine ⟨(j+2 : ℤ)*z1 - (j+2 : ℤ)*z0, ?_⟩
      rw [Nat.factorial_succ, Nat.factorial_succ]
      rw [Nat.factorial_succ] at hz1
      push_cast at hz1 ⊢
      simp only [Nat.add_comm j 1, Nat.add_comm j 2] at hz0 hz1 hr ⊢
      ring_nf at hz0 hz1 hr ⊢
      linear_combination (j+2 : ℤ) * hz1 - (j+2 : ℤ) * hz0 +
        (j+2 : ℤ) * ((1+j)! : ℤ) * hr

private lemma prime_ge_eleven_of_mod (p : ℕ) (hp : p.Prime)
    (hmod : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) : 11 ≤ p := by
  rcases hmod with h | h
  · have hm : p % 10 = 1 := by simpa [Nat.ModEq] using h
    have hp2 := hp.two_le
    have hpne : p ≠ 2 := by omega
    have hpne3 : p ≠ 3 := by omega
    have hpne5 : p ≠ 5 := by omega
    have hpne7 : p ≠ 7 := by omega
    omega
  · have hm : p % 10 = 9 := by simpa [Nat.ModEq] using h
    have hpne9 : p ≠ 9 := by
      intro he
      subst p
      norm_num at hp
    omega

private lemma exists_even_sqrt_five (p : ℕ) (hp : p.Prime)
    (hmod : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) :
    ∃ x : ℕ, Even x ∧ 4 ≤ x ∧ x < p ∧ x*x ≡ 5 [MOD p] := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp11 := prime_ge_eleven_of_mod p hp hmod
  have hp2 : p ≠ 2 := by omega
  have hs5 : IsSquare (5 : ZMod p) := by
    refine (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one
      (p := 5) (q := p) (by norm_num) hp2).mp ?_
    rw [isSquare_iff_exists_sq]
    rcases hmod with h | h
    · refine ⟨1, ?_⟩
      have h5 := h.of_dvd (by norm_num : 5 ∣ 10)
      apply (ZMod.natCast_eq_natCast_iff p 1 5).2
      simpa using h5
    · refine ⟨2, ?_⟩
      have h5 := h.of_dvd (by norm_num : 5 ∣ 10)
      have heq : p ≡ 4 [MOD 5] := by simpa using h5
      change (p : ZMod 5) = (4 : ZMod 5)
      exact (ZMod.natCast_eq_natCast_iff p 4 5).2 heq
  rw [isSquare_iff_exists_sq] at hs5
  obtain ⟨y, hy⟩ := hs5
  let r := y.val
  have hrp : r < p := ZMod.val_lt y
  have hrroot : r*r ≡ 5 [MOD p] := by
    apply (ZMod.eq_iff_modEq_nat p).mp
    push_cast
    rw [ZMod.natCast_zmod_val]
    simpa [pow_two] using hy.symm
  rcases Nat.even_or_odd r with hre | hro
  · refine ⟨r, hre, ?_, hrp, hrroot⟩
    rcases hre with ⟨s, hs⟩
    by_contra h4
    have hrle : r ≤ 2 := by omega
    have heq := hrroot.eq_of_lt_of_lt (by nlinarith) (by omega)
    nlinarith
  · let x := p-r
    have hrpos : 0 < r := hro.pos
    have hxp : x < p := by dsimp [x]; omega
    have hxe : Even x := by
      dsimp [x]
      exact Nat.Odd.sub_odd (hp.odd_of_ne_two hp2) hro
    have hxroot : x*x ≡ 5 [MOD p] := by
      apply (ZMod.eq_iff_modEq_nat p).mp
      dsimp [x]
      push_cast [Nat.cast_sub (Nat.le_of_lt hrp)]
      rw [ZMod.natCast_self, ZMod.natCast_zmod_val]
      have hyr : (y : ZMod p)^2 = 5 := hy.symm
      rw [zero_sub, neg_mul, mul_neg, neg_neg]
      simpa [pow_two] using hyr
    refine ⟨x, hxe, ?_, hxp, hxroot⟩
    rcases hxe with ⟨s, hs⟩
    by_contra h4
    have hxle : x ≤ 2 := by omega
    have heq := hxroot.eq_of_lt_of_lt (by nlinarith) (by omega)
    nlinarith

private lemma root_data (p : ℕ) (hp : p.Prime)
    (hmod : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) (hp11 : p ≠ 11) :
    ∃ x q : ℕ, Even x ∧ Odd q ∧ 6 ≤ x ∧ x < p ∧ 0 < q ∧
      q ≤ x-4 ∧ p*q = x*x-5 := by
  have hpge : 11 ≤ p := prime_ge_eleven_of_mod p hp hmod
  obtain ⟨x, hxe, hx4, hxp, hxroot⟩ := exists_even_sqrt_five p hp hmod
  have hpgt : x < p := hxp
  have hx5 : 5 ≤ x*x := by nlinarith
  have hpdvd : p ∣ x*x-5 :=
    (Nat.modEq_iff_dvd' hx5).mp hxroot.symm
  let q := (x*x-5)/p
  have heq : p*q = x*x-5 := by
    dsimp [q]
    exact Nat.mul_div_cancel' hpdvd
  have heq' : p*q + 5 = x*x := by omega
  have hp0 : 0 < p := hp.pos
  have hq0 : 0 < q := by
    by_contra h
    have : q = 0 := Nat.eq_zero_of_not_pos h
    rw [this, mul_zero] at heq'
    nlinarith
  have hdiffodd : Odd (x*x-5) := by
    rw [Nat.odd_sub hx5]
    constructor
    · intro hodd
      exact False.elim ((Nat.not_odd_iff_even.mpr hxe) (Nat.odd_mul.mp hodd).1)
    · intro h
      norm_num at h
  have hqo : Odd q := by
    have hpqo : Odd (p*q) := by rwa [heq]
    exact (Nat.odd_mul.mp hpqo).2
  have hx6 : 6 ≤ x := by
    obtain ⟨a, ha⟩ := hxe
    have hxne4 : x ≠ 4 := by
      intro hx
      subst x
      norm_num at heq'
      have hp11eq : p = 11 := by nlinarith
      exact hp11 hp11eq
    omega
  have hq_lt : q < x := by
    have hpx1 : x+1 ≤ p := by omega
    nlinarith
  have hqbound : q ≤ x-4 := by
    by_contra hb
    have hlow : x-3 ≤ q := by omega
    obtain ⟨a, ha⟩ := hxe
    obtain ⟨b, hbodd⟩ := hqo
    have hcases : q = x-3 ∨ q = x-1 := by omega
    rcases hcases with hcase | hcase
    · have hsum : x = q+3 := by omega
      have hpcoef : q+6 ≤ p := by
        rw [hsum] at heq'
        nlinarith
      obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hpcoef
      have hfour : q*c = 4 := by
        rw [hsum, hc] at heq'
        nlinarith
      have hqle4 : q ≤ 4 :=
        Nat.le_of_dvd (by norm_num) ⟨c, hfour.symm⟩
      have hq1 : q = 1 := by
        interval_cases q <;> omega
      have hxval : x = 4 := by omega
      have heqcopy := heq'
      rw [hq1, hxval] at heqcopy
      norm_num at heqcopy
      have hpval : p = 11 := by omega
      exact hp11 hpval
    · have hsum : x = q+1 := by omega
      have hpx1 : x+1 ≤ p := by omega
      rw [hsum] at heq'
      nlinarith
  exact ⟨x, q, hxe, hqo, hx6, hxp, hq0, hqbound, heq⟩


private lemma small_odd_divisor_dvd_den (n q : ℕ) (hn : 4 ≤ n)
    (hq0 : 0 < q) (hqo : Odd q) (hqle : q ≤ n-3)
    (hqF : (q : ℤ) ∣ pseq n 0) :
    (q : ℤ) ∣ (cpair n (n-3)).2 := by
  have hfac := factorial_relation (pseq n) (n-3)
    (fun j hj => pseq_rec n j (by omega) hj) (q-1) (by omega)
  obtain ⟨z, hz⟩ := hfac
  have hqsub : q-1+1 = q := by omega
  rw [hqsub, pseq_one n hn] at hz
  have hqdvdFacNat : q ∣ q.factorial := Nat.dvd_factorial hq0 (by rfl)
  have hqdvdFac : (q : ℤ) ∣ (q.factorial : ℤ) := by
    exact_mod_cast hqdvdFacNat
  let D := (cpair n (n-3)).2
  have hleft : (q : ℤ) ∣ (q.factorial : ℤ) * pseq n (q-1) :=
    dvd_mul_of_dvd_left hqdvdFac _
  have hFz : (q : ℤ) ∣ pseq n 0 * z := dvd_mul_of_dvd_left hqF _
  have hsum : (q : ℤ) ∣ 2 * ((q-1 : ℕ) : ℤ) * D + pseq n 0*z := by
    rw [← hz]
    exact hleft
  have hprod : (q : ℤ) ∣ 2 * ((q-1 : ℕ) : ℤ) * D := by
    have := hsum.sub hFz
    convert this using 1 <;> ring
  have hqcast : ((q-1 : ℕ) : ℤ) = (q : ℤ)-1 := by omega
  rw [hqcast] at hprod
  have hbig : (q : ℤ) ∣ 2*(q : ℤ)*D := by
    convert dvd_mul_right (q : ℤ) (2*D) using 1 <;> ring
  have htwo : (q : ℤ) ∣ 2*D := by
    have := hbig.sub hprod
    convert this using 1 <;> ring
  have habs : q ∣ (2*D).natAbs := by
    exact_mod_cast ((Int.dvd_natAbs).2 htwo)
  have habs' : q ∣ 2 * D.natAbs := by
    simpa [Int.natAbs_mul] using habs
  have hcop : q.Coprime 2 := Nat.coprime_two_right.mpr hqo
  have hdabs : q ∣ D.natAbs := hcop.dvd_of_dvd_mul_left habs'
  exact (Int.natAbs_dvd_natAbs.mp (by simpa using hdabs))

private lemma large_prime_not_dvd_den (n p : ℕ) (hn : 4 ≤ n)
    (hp : p.Prime) (hnp : n < p) (hpge : 11 ≤ p) (hp11 : p ≠ 11)
    (hpF : (p : ℤ) ∣ pseq n 0) :
    ¬(p : ℤ) ∣ (cpair n (n-3)).2 := by
  intro hpD
  have hpone : (p : ℤ) ∣ pseq n 1 := by
    rw [pseq_one n hn]
    exact hpD
  have hall : ∀ j, j ≤ n-3 → (p : ℤ) ∣ pseq n j := by
    intro j
    induction j using Nat.twoStepInduction with
    | zero => intro _; exact hpF
    | one => intro _; exact hpone
    | more j ih0 ih1 =>
        intro hj
        have hjrec : j+2 ≤ n-3 := hj
        have hd0 := ih0 (by omega)
        have hd1 := ih1 (by omega)
        have hr := pseq_rec n j (by omega) hjrec
        have hmul : (p : ℤ) ∣ (j+3 : ℤ) * pseq n (j+2) := by
          have hfirst : (p : ℤ) ∣ (j+2 : ℤ) * pseq n (j+1) :=
            dvd_mul_of_dvd_right hd1 _
          have hsub := hfirst.sub hd0
          convert hsub using 1
          rw [hr]
          ring
        have habs : p ∣ (j+3) * (pseq n (j+2)).natAbs := by
          have hzabs : p ∣ (((j+3 : ℤ) * pseq n (j+2)).natAbs) := by
            exact_mod_cast ((Int.dvd_natAbs).2 hmul)
          simpa [Int.natAbs_mul] using hzabs
        rcases hp.dvd_mul.mp habs with hcoeff | hval
        · have hlt : j+3 < p := by omega
          exact False.elim (Nat.not_dvd_of_pos_of_lt (by omega) hlt hcoeff)
        · exact Int.natAbs_dvd_natAbs.mp (by simpa using hval)
  have hpbase := hall (n-3) (by rfl)
  simp only [pseq, Nat.sub_self, cpair] at hpbase
  have hpF' : (p : ℤ) ∣ (n : ℤ)^2 + 2*n-4 := by
    rw [← pseq_zero n (by omega)]
    exact hpF
  have hcomb : (p : ℤ) ∣ (-44 : ℤ) := by
    have h1 : (p : ℤ) ∣ 25 * ((n : ℤ)^2 + 2*n-4) :=
      dvd_mul_of_dvd_right hpF' 25
    have h2 : (p : ℤ) ∣ ((5*(n : ℤ)+14) * (5*(n : ℤ)-4)) :=
      dvd_mul_of_dvd_right hpbase _
    have := h1.sub h2
    convert this using 1 <;> ring
  have hp44z : (p : ℤ) ∣ (44 : ℤ) := (dvd_neg.mp (by simpa using hcomb))
  have hp44 : p ∣ 44 := Int.ofNat_dvd.mp hp44z
  have hp411 : p ∣ 4*11 := by norm_num at hp44 ⊢; exact hp44
  rcases hp.dvd_mul.mp hp411 with hp4 | hp11dvd
  · have := Nat.le_of_dvd (by norm_num : 0 < 4) hp4
    omega
  · have hple := Nat.le_of_dvd (by norm_num : 0 < 11) hp11dvd
    exact hp11 (by omega)


private lemma occurs_of_ne_eleven (p : ℕ) (hp : p.Prime)
    (hmod : p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10]) (hp11 : p ≠ 11) :
    ∃ n : ℕ, A363347 n = p := by
  obtain ⟨x, q, hxe, hqo, hx6, hxp, hq0, hqle, heq⟩ :=
    root_data p hp hmod hp11
  let n := x-1
  have hn : 4 ≤ n := by dsimp [n]; omega
  have hnp : n < p := by dsimp [n]; omega
  have hn3 : n-3 = x-4 := by dsimp [n]; omega
  have hx5 : 5 ≤ x*x := by nlinarith
  have hFInt : (n : ℤ)^2 + 2*n-4 = (p : ℤ)*(q : ℤ) := by
    have heq' : p*q + 5 = x*x := by omega
    have heqInt : (p : ℤ)*(q : ℤ) + 5 = (x : ℤ)*(x : ℤ) := by
      exact_mod_cast heq'
    have hncast : (n : ℤ) = (x : ℤ)-1 := by
      dsimp [n]
      omega
    rw [hncast]
    nlinarith
  have hqF : (q : ℤ) ∣ pseq n 0 := by
    rw [pseq_zero n (by omega), hFInt]
    exact dvd_mul_left _ _
  have hqD := small_odd_divisor_dvd_den n q hn hq0 hqo (by omega) hqF
  let D := (cpair n (n-3)).2
  obtain ⟨d, hd⟩ := hqD
  have hD : D = (q : ℤ)*d := by simpa [D] using hd
  have hDpos : 0 < D := by
    dsimp [D]
    exact (cpair_pos n (n-3) (by omega) (by omega)).2
  have hdpos : 0 < d := by
    by_contra hd0
    have hdle : d ≤ 0 := le_of_not_gt hd0
    have hqz : 0 < (q : ℤ) := by exact_mod_cast hq0
    nlinarith
  have hpF : (p : ℤ) ∣ pseq n 0 := by
    rw [pseq_zero n (by omega), hFInt]
    exact dvd_mul_right _ _
  have hpnotD := large_prime_not_dvd_den n p hn hp hnp
    (prime_ge_eleven_of_mod p hp hmod) hp11 hpF
  have hcop : (p : ℤ).natAbs.Coprime d.natAbs := by
    rw [Int.natAbs_natCast]
    apply hp.coprime_iff_not_dvd.mpr
    intro hpd
    have hpdz : (p : ℤ) ∣ d := by
      apply Int.natAbs_dvd_natAbs.mp
      simpa using hpd
    apply hpnotD
    change (p : ℤ) ∣ D
    rw [hD]
    exact dvd_mul_of_dvd_right hpdz _
  have hR : continued_fraction_denominator n 2 = (p : ℚ) / (d : ℚ) := by
    have h := continued_eq_cpair n (n-3) (by omega) (by omega)
    have hk : n-1-(n-3) = 2 := by omega
    rw [hk, cpair_final_fst n (by omega)] at h
    rw [h, hFInt, show (cpair n (n-3)).2 = (q : ℤ)*d by exact hD]
    push_cast
    have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
    field_simp
  have hnum : (continued_fraction_denominator n 2).num = (p : ℤ) := by
    rw [hR]
    exact Rat.num_div_eq_of_coprime hdpos hcop
  refine ⟨n, ?_⟩
  rw [A363347]
  simp only [show ¬n ≤ 2 by omega, ↓reduceIte]
  rw [hnum, Int.natAbs_natCast]


/--
A363347 Conjecture 2: The sequence contains all prime numbers which end with a 1 or 9.
-/
theorem oeis_363347_conjecture_2 :
  ∀ p : ℕ,
    (p.Prime ∧ (p ≡ 1 [MOD 10] ∨ p ≡ 9 [MOD 10])) →
    ∃ n : ℕ, A363347 n = p := by
  intro p hpall
  rcases hpall with ⟨hp, hmod⟩
  by_cases h11 : p = 11
  · subst p
    refine ⟨3, ?_⟩
    have h := continued_eq_cpair 3 0 (by omega) (by omega)
    norm_num [cpair] at h
    rw [A363347]
    norm_num only
    rw [h]
    norm_num
  · exact occurs_of_ne_eleven p hp hmod h11




