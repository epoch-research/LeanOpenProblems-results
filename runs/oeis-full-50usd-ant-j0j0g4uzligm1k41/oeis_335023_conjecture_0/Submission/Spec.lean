import FormalConjectures.Util.ProblemImports

open Nat Int Finset

/-- The auxiliary integer sequence $F(n) = n! \sum_{k=2}^n \frac{(-1)^k}{k}$, corresponding to OEIS A024168. -/
def F_aux (n : ℕ) : ℤ :=
  if n < 2 then 0 else
  Finset.sum (Icc 2 n) $ fun k : ℕ =>
    let n_fact : ℤ := n.factorial
    let k_int : ℤ := k
    -- Term is $\frac{n!}{k} (-1)^{k}$.
    let quotient : ℤ := n_fact / k_int
    quotient * (if k % 2 = 0 then 1 else -1)

/--
A335023: Ratios of consecutive terms of A334958.
$$a(n) = \frac{A334958(n+1)}{A334958(n)}$$
where $A334958(m) = \gcd(F(m+1), F(m))$.
-/
def a (n : ℕ) : ℕ :=
  let A334958 (m : ℕ) : ℕ := Int.gcd (F_aux (m + 1)) (F_aux m)

  let g_n := A334958 n
  let g_n_plus_1 := A334958 (n + 1)

  -- A334958(n) is non-zero for $n \ge 1$.
  if g_n = 0 then 0 else g_n_plus_1 / g_n

/-! ## Auxiliary lemmas towards settling the conjecture. -/

/-- `F_aux` as a plain sum (the `if n < 2` branch coincides with the empty sum). -/
theorem F_aux_eq (n : ℕ) :
    F_aux n = ∑ k ∈ Icc 2 n, ((n ! : ℤ) / (k : ℤ)) * (if k % 2 = 0 then 1 else -1) := by
  unfold F_aux
  split
  · next h =>
    have : Icc 2 n = ∅ := by rw [Finset.Icc_eq_empty]; omega
    rw [this]; simp
  · rfl

/-- The recurrence `F(n+1) = (n+1) F(n) + (-1)^{n+1} n!`. -/
theorem F_rec (n : ℕ) (hn : 1 ≤ n) :
    F_aux (n + 1) = (n + 1 : ℤ) * F_aux n + (n ! : ℤ) * (if (n+1) % 2 = 0 then 1 else -1) := by
  rw [F_aux_eq, F_aux_eq]
  rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
  have htop : ((n+1)! : ℤ) / ((n : ℤ) + 1) = (n ! : ℤ) := by
    rw [Nat.factorial_succ]
    push_cast
    rw [Int.mul_ediv_cancel_left]
    positivity
  have hinner : ∀ k ∈ Icc 2 n, (((n+1)! : ℤ) / (k:ℤ)) * (if k % 2 = 0 then 1 else -1)
      = (n+1 : ℤ) * (((n ! : ℤ) / (k:ℤ)) * (if k % 2 = 0 then 1 else -1)) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hdvd : (k : ℤ) ∣ (n ! : ℤ) := by
      rw [Int.natCast_dvd_natCast]; exact Nat.dvd_factorial (by omega) hk.2
    rw [Nat.factorial_succ]
    push_cast
    rw [Int.mul_ediv_assoc _ hdvd]
    ring
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]
  push_cast
  rw [htop]

/-- `gcd` is invariant under adding a multiple of the second argument. -/
theorem gcd_add_mul_helper (a b k : ℤ) : Int.gcd (a + k * b) b = Int.gcd a b := by
  apply Nat.dvd_antisymm
  · apply Int.natCast_dvd_natCast.mp
    apply Int.dvd_coe_gcd
    · have h1 : (Int.gcd (a + k*b) b : ℤ) ∣ (a + k*b) := Int.gcd_dvd_left _ _
      have h2 : (Int.gcd (a + k*b) b : ℤ) ∣ b := Int.gcd_dvd_right _ _
      have : (Int.gcd (a + k*b) b : ℤ) ∣ (a + k*b) - k * b := by
        exact dvd_sub h1 (Dvd.dvd.mul_left h2 k)
      simpa using this
    · exact Int.gcd_dvd_right _ _
  · apply Int.natCast_dvd_natCast.mp
    apply Int.dvd_coe_gcd
    · exact dvd_add (Int.gcd_dvd_left _ _) (Dvd.dvd.mul_left (Int.gcd_dvd_right _ _) k)
    · exact Int.gcd_dvd_right _ _

theorem gcd_sign (N b : ℤ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) :
    Int.gcd (N * σ) b = Int.gcd N b := by
  rcases hσ with h | h <;> subst h <;> simp [Int.gcd]

/-- `gcd(F(m+1), F(m)) = gcd(m!, F(m))`. -/
theorem gcd_step (m : ℕ) (hm : 1 ≤ m) :
    Int.gcd (F_aux (m+1)) (F_aux m) = Int.gcd ((m ! : ℤ)) (F_aux m) := by
  rw [F_rec m hm]
  have : ((m:ℤ) + 1) * F_aux m + (m ! : ℤ) * (if (m+1) % 2 = 0 then 1 else -1)
       = (m ! : ℤ) * (if (m+1) % 2 = 0 then 1 else -1) + ((m:ℤ)+1) * F_aux m := by ring
  rw [this, gcd_add_mul_helper]
  apply gcd_sign
  split <;> simp

/-- Elementary coprimality used in the main `gcd` computation. -/
theorem coprime_lemma (p : ℕ) (hp : p.Prime) (x y : ℤ)
    (hcop : Int.gcd x y = 1) (hx : ¬ (p : ℤ) ∣ x) :
    Int.gcd ((p : ℤ)^2 * x) ((p : ℤ)^2 * y - x) = 1 := by
  by_contra hd
  set d := Int.gcd ((p : ℤ)^2 * x) ((p : ℤ)^2 * y - x) with hddef
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd
  have hqint : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hq1 : (q : ℤ) ∣ (p : ℤ)^2 * x := by
    have : (q : ℤ) ∣ (d : ℤ) := Int.natCast_dvd_natCast.mpr hqd
    exact this.trans (Int.gcd_dvd_left _ _)
  have hq2 : (q : ℤ) ∣ (p : ℤ)^2 * y - x := by
    have : (q : ℤ) ∣ (d : ℤ) := Int.natCast_dvd_natCast.mpr hqd
    exact this.trans (Int.gcd_dvd_right _ _)
  have hqp2_to_eq : (q : ℤ) ∣ (p : ℤ)^2 → q = p := by
    intro h
    rw [sq] at h
    rcases hqint.dvd_mul.mp h with h' | h' <;>
    · have : (q : ℤ) ∣ (p : ℤ) := h'
      have : q ∣ p := Int.natCast_dvd_natCast.mp this
      exact (Nat.prime_dvd_prime_iff_eq hq hp).mp this
  rcases hqint.dvd_mul.mp hq1 with hqp2 | hqx
  · have hqeqp : q = p := hqp2_to_eq hqp2
    subst hqeqp
    have hqPy : (q : ℤ) ∣ (q : ℤ)^2 * y := ⟨(q : ℤ) * y, by ring⟩
    have : (q : ℤ) ∣ x := by
      have := dvd_sub hqPy hq2
      simpa using this
    exact hx this
  · have hqPy : (q : ℤ) ∣ (p : ℤ)^2 * y := by
      have := dvd_add hq2 hqx
      simpa using this
    have hqny : ¬ (q : ℤ) ∣ y := by
      intro hqy
      have : (q : ℤ) ∣ (Int.gcd x y : ℤ) := Int.dvd_coe_gcd hqx hqy
      rw [hcop] at this
      have : (q : ℤ) ∣ 1 := by simpa using this
      exact hq.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
    have hqp2 : (q : ℤ) ∣ (p : ℤ)^2 := by
      rcases hqint.dvd_mul.mp hqPy with h | h
      · exact h
      · exact absurd h hqny
    have hqeqp : q = p := hqp2_to_eq hqp2
    subst hqeqp
    exact hx hqx

/-- The core `gcd` identity: with `P = p^2`, `gcd(P X, P Y - X) = gcd(X, Y)` provided
`p^{p-1} ∣ X`, `p^{p-1} ∣ Y` and `p^p ∤ X` (so that the `p`-part does not interfere). -/
theorem crux (p : ℕ) (hp : p.Prime) (X Y : ℤ) (hX : X ≠ 0)
    (hpX : (p : ℤ)^(p-1) ∣ X) (hpY : (p : ℤ)^(p-1) ∣ Y) (hpnX : ¬ (p : ℤ)^p ∣ X) :
    Int.gcd ((p : ℤ)^2 * X) ((p : ℤ)^2 * Y - X) = Int.gcd X Y := by
  have hgpos : 0 < Int.gcd X Y := by
    rcases Nat.eq_zero_or_pos (Int.gcd X Y) with h | h
    · rw [Int.gcd_eq_zero_iff] at h; exact absurd h.1 hX
    · exact h
  obtain ⟨g, x', y', hg0, hcop, hXeq, hYeq⟩ := Int.exists_gcd_one' hgpos
  have hgcdXY : Int.gcd X Y = g := by
    rw [hXeq, hYeq, Int.gcd_mul_right, hcop, one_mul, Int.natAbs_natCast]
  have hpg : (p : ℤ)^(p-1) ∣ (g : ℤ) := by
    have := Int.dvd_coe_gcd hpX hpY
    rwa [hgcdXY] at this
  have hpx : ¬ (p : ℤ) ∣ x' := by
    rintro ⟨t, ht⟩
    obtain ⟨w, hw⟩ := hpg
    apply hpnX
    have hpp : (p : ℤ)^p = (p : ℤ)^(p-1) * (p : ℤ) := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le]
    refine ⟨t * w, ?_⟩
    rw [hXeq, ht, hw, hpp]; ring
  have e1 : (p : ℤ)^2 * X = (g : ℤ) * ((p : ℤ)^2 * x') := by rw [hXeq]; ring
  have e2 : (p : ℤ)^2 * Y - X = (g : ℤ) * ((p : ℤ)^2 * y' - x') := by rw [hXeq, hYeq]; ring
  rw [e1, e2, Int.gcd_mul_left, coprime_lemma p hp x' y' hcop hpx, mul_one,
      Int.natAbs_natCast, hgcdXY]

/-- Legendre's formula gives `v_p((p^2-1)!) = p - 1`. -/
theorem legendre_val (p : ℕ) (hp : p.Prime) :
    padicValNat p ((p^2-1)!) = p - 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  have hone : 2 ≤ p^2 := Nat.one_lt_pow (by omega) (by omega)
  have hlog : Nat.log p (p^2-1) < 2 :=
    Nat.log_lt_of_lt_pow (by omega) (by simpa using (by omega : p^2 - 1 < p^2))
  rw [padicValNat_factorial hlog]
  rw [show (2:ℕ) = 1 + 1 from rfl, Finset.sum_Ico_succ_top (by omega),
      Finset.Ico_self, Finset.sum_empty, zero_add, pow_one]
  have hge : p ≤ p * p := Nat.le_mul_of_pos_left p (by omega)
  have key : p^2 - 1 = (p-1) + (p-1)*p := by
    rw [sq, Nat.sub_one_mul]; omega
  rw [key, Nat.add_mul_div_right _ _ (by omega : 0 < p), Nat.div_eq_of_lt (by omega)]
  omega

theorem pow_dvd_fact (p : ℕ) (hp : p.Prime) : p^(p-1) ∣ (p^2-1)! := by
  have hfac : ((p^2-1)!).factorization p = p - 1 := by
    rw [Nat.factorization_def _ hp]; exact legendre_val p hp
  rw [hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _), hfac]

theorem pow_ndvd_fact (p : ℕ) (hp : p.Prime) : ¬ p^p ∣ (p^2-1)! := by
  have hfac : ((p^2-1)!).factorization p = p - 1 := by
    rw [Nat.factorization_def _ hp]; exact legendre_val p hp
  rw [hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _), hfac]
  have := hp.two_le
  omega

theorem pow_dvd_fact_int (p : ℕ) (hp : p.Prime) : (p:ℤ)^(p-1) ∣ ((p^2-1)! : ℤ) := by
  have := pow_dvd_fact p hp
  have := Int.natCast_dvd_natCast.mpr this
  simpa using this

theorem pow_ndvd_fact_int (p : ℕ) (hp : p.Prime) : ¬ (p:ℤ)^p ∣ ((p^2-1)! : ℤ) := by
  intro h
  apply pow_ndvd_fact p hp
  have : ((p^p : ℕ) : ℤ) ∣ ((p^2-1)! : ℤ) := by push_cast; exact h
  exact Int.natCast_dvd_natCast.mp this

/-- Reindex the "multiples of `p`" part of the sum over `Icc 2 (p^2-1)` to `Icc 1 (p-1)`. -/
theorem reindex_mult (p : ℕ) (hp : p.Prime) (g : ℕ → ℤ) :
    ∑ k ∈ (Icc 2 (p^2-1)).filter (fun k => p ∣ k), g k
    = ∑ j ∈ Icc 1 (p-1), g (j * p) := by
  have hp2 := hp.two_le
  have hpp : p^2 = p * p := sq p
  apply Finset.sum_bij' (i := fun k _ => k / p) (j := fun j _ => j * p)
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    obtain ⟨⟨hk2, hkm⟩, c, rfl⟩ := hk
    rw [Nat.mul_div_cancel_left _ (by omega)]
    have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hk2)
    have hpp1 : 1 ≤ p * p := by nlinarith
    have hlt : p * c < p * p := by omega
    have : c < p := Nat.lt_of_mul_lt_mul_left hlt
    omega
  · intro j hj
    simp only [Finset.mem_Icc, Finset.mem_filter] at hj ⊢
    obtain ⟨hj1, hjp⟩ := hj
    have hle : j * p ≤ (p-1) * p := Nat.mul_le_mul_right _ hjp
    have : (p-1)*p ≤ p*p - 1 := by
      have : (p-1)*p = p*p - p := by rw [Nat.sub_one_mul]
      omega
    refine ⟨⟨?_, ?_⟩, ⟨j, by ring⟩⟩
    · nlinarith
    · omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨_, c, rfl⟩ := hk
    rw [Nat.mul_div_cancel_left _ (by omega), mul_comm]
  · intro j hj
    rw [Nat.mul_div_cancel _ (by omega)]
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨_, c, rfl⟩ := hk
    rw [Nat.mul_div_cancel_left _ (by omega), mul_comm]

/-- The key divisibility `p^{p-1} ∣ F(p^2-1)`, granted the (Wieferich-type) modular hypothesis
`∑_{j=1}^{p-1} (-1)^j j^{-1} = 0` in `ZMod p`. -/
theorem key_dvd (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hS : (∑ j ∈ Icc 1 (p-1), ((-1 : ZMod p))^j * ((j:ℕ):ZMod p)⁻¹) = 0) :
    (p:ℤ)^(p-1) ∣ F_aux (p^2 - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  have hp3 : 3 ≤ p := by rcases hodd with ⟨t, ht⟩; omega
  set M : ℤ := ((p^2-1)! : ℤ) with hMdef
  have hpM : (p:ℤ)^(p-1) ∣ M := pow_dvd_fact_int p hp
  have hpne : (p:ℤ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hppowne : (p:ℤ)^(p-1) ≠ 0 := pow_ne_zero _ hpne
  have hpowrel : (p:ℤ)^(p-1) = (p:ℤ)^(p-2) * (p:ℤ) := by
    rw [← pow_succ]; congr 1; omega
  set U : ℤ := M / (p:ℤ)^(p-1) with hUdef
  rw [F_aux_eq]
  set f : ℕ → ℤ := fun k => ((p^2-1)! : ℤ) / (k : ℤ) * (if k % 2 = 0 then 1 else -1) with hfdef
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 2 (p^2-1)) (fun k => p ∣ k) f]
  apply dvd_add
  · rw [reindex_mult p hp f]
    have hterm : ∀ j ∈ Icc 1 (p-1),
        f (j * p) = (p:ℤ)^(p-2) * ((M / ((j:ℤ) * (p:ℤ)^(p-1))) * (-1:ℤ)^j) := by
      intro j hj
      simp only [Finset.mem_Icc] at hj
      have hnpj : ¬ p ∣ j := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
      have hjle : j ≤ p^2 - 1 := by
        have : p ≤ p^2 := Nat.le_self_pow (by omega) p
        omega
      have hcopjp : IsCoprime (j:ℤ) (p:ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        simpa [Int.gcd] using (hp.coprime_iff_not_dvd.mpr hnpj).symm
      have hjdvdM : (j:ℤ) ∣ M := by
        rw [hMdef]; exact_mod_cast Nat.dvd_factorial (by omega) hjle
      have hjpp_dvd : ((j:ℤ) * (p:ℤ)^(p-1)) ∣ M :=
        (hcopjp.pow_right).mul_dvd hjdvdM hpM
      set qj : ℤ := M / ((j:ℤ) * (p:ℤ)^(p-1)) with hqjdef
      have hMeq : M = ((j:ℤ) * (p:ℤ)^(p-1)) * qj := by
        rw [mul_comm]; exact (Int.ediv_mul_cancel hjpp_dvd).symm
      have hjpne : ((j*p : ℕ) : ℤ) ≠ 0 := by
        have : j * p ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
        exact_mod_cast this
      have hMeq2 : M = ((j*p : ℕ):ℤ) * ((p:ℤ)^(p-2) * qj) := by
        push_cast
        rw [hMeq, hpowrel]; ring
      have hdiv : M / ((j*p : ℕ):ℤ) = (p:ℤ)^(p-2) * qj := by
        rw [hMeq2, Int.mul_ediv_cancel_left _ hjpne]
      have hc : (if (j*p) % 2 = 0 then (1:ℤ) else -1) = (-1:ℤ)^j := by
        have hpmod : p % 2 = 1 := Nat.odd_iff.mp hodd
        have hpar : (j * p) % 2 = j % 2 := by
          rw [Nat.mul_mod, hpmod, mul_one, Nat.mod_mod_of_dvd j (dvd_refl 2)]
        rw [hpar]
        rcases Nat.even_or_odd j with he | ho
        · simp [Nat.even_iff.mp he, he.neg_one_pow]
        · simp [Nat.odd_iff.mp ho, ho.neg_one_pow]
      show ((p^2-1)! : ℤ) / ((j*p:ℕ):ℤ) * (if (j*p) % 2 = 0 then 1 else -1) = _
      rw [← hMdef, hdiv, hc]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    set T : ℤ := ∑ j ∈ Icc 1 (p-1), (M / ((j:ℤ) * (p:ℤ)^(p-1))) * (-1:ℤ)^j with hTdef
    have hpT : (p:ℤ) ∣ T := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hcast : ((T:ℤ):ZMod p)
          = (↑U:ZMod p) * ∑ j ∈ Icc 1 (p-1), ((-1:ZMod p))^j * ((j:ℕ):ZMod p)⁻¹ := by
        rw [hTdef]
        push_cast
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Finset.mem_Icc] at hj
        have hnpj : ¬ p ∣ j := fun hd => by have := Nat.le_of_dvd (by omega) hd; omega
        have hjne : (j : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hnpj
        have hcopjp : IsCoprime (j:ℤ) (p:ℤ) := by
          rw [Int.isCoprime_iff_gcd_eq_one]
          simpa [Int.gcd] using (hp.coprime_iff_not_dvd.mpr hnpj).symm
        have hjdvdM : (j:ℤ) ∣ M := by
          rw [hMdef]
          exact_mod_cast Nat.dvd_factorial (by omega)
            (by have : p ≤ p^2 := Nat.le_self_pow (by omega) p; omega)
        have hjpp_dvd : ((j:ℤ) * (p:ℤ)^(p-1)) ∣ M :=
          (hcopjp.pow_right).mul_dvd hjdvdM hpM
        set qj : ℤ := M / ((j:ℤ) * (p:ℤ)^(p-1)) with hqjdef
        have hMeq : M = ((j:ℤ) * (p:ℤ)^(p-1)) * qj := by
          rw [mul_comm]; exact (Int.ediv_mul_cancel hjpp_dvd).symm
        have hjU : (j:ℤ) * qj = U := by
          rw [hUdef, show M = (p:ℤ)^(p-1) * ((j:ℤ) * qj) by rw [hMeq]; ring,
              Int.mul_ediv_cancel_left _ hppowne]
        have hzj : (j : ZMod p) * ((qj:ℤ):ZMod p) = ((U:ℤ):ZMod p) := by
          have := congrArg (fun x : ℤ => ((x:ℤ):ZMod p)) hjU
          push_cast at this ⊢
          convert this using 2
        have hqc : ((qj:ℤ):ZMod p) = (j:ZMod p)⁻¹ * ((U:ℤ):ZMod p) := by
          rw [← hzj, inv_mul_cancel_left₀ hjne]
        rw [hqc]; ring
      rw [hcast, hS, mul_zero]
    obtain ⟨T', hT'⟩ := hpT
    exact ⟨T', by rw [hT', hpowrel]; ring⟩
  · apply Finset.dvd_sum
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk2, hkm⟩, hnpk⟩ := hk
    have hkdvdM : (k:ℤ) ∣ M := by
      rw [hMdef]; exact_mod_cast Nat.dvd_factorial (by omega) hkm
    have hcoppk : IsCoprime ((p:ℤ)^(p-1)) (k:ℤ) := by
      have : IsCoprime (p:ℤ) (k:ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        simpa [Int.gcd] using hp.coprime_iff_not_dvd.mpr hnpk
      exact this.pow_left
    have hdvd_quot : (p:ℤ)^(p-1) ∣ ((p^2-1)! : ℤ) / (k:ℤ) := by
      apply hcoppk.dvd_of_dvd_mul_right
      rw [Int.ediv_mul_cancel hkdvdM]; exact hpM
    show (p:ℤ)^(p-1) ∣ ((p^2-1)! : ℤ) / (k:ℤ) * (if k % 2 = 0 then 1 else -1)
    exact hdvd_quot.mul_right _

/-- For an odd prime `p` satisfying the modular (Wieferich-type) hypothesis, `a(p^2-1) = 1`,
even though `p^2` is composite. -/
theorem a_at (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hS : (∑ j ∈ Icc 1 (p-1), ((-1 : ZMod p))^j * ((j:ℕ):ZMod p)⁻¹) = 0) :
    a (p^2 - 1) = 1 := by
  have hp2 := hp.two_le
  have hp3 : 3 ≤ p := by rcases hodd with ⟨t, ht⟩; omega
  have hposp2 : 1 ≤ p^2 := Nat.one_le_pow _ _ (by omega)
  have hpos1 : 1 ≤ p^2 - 1 := by
    have : 4 ≤ p^2 := by nlinarith [sq p]
    omega
  set X : ℤ := ((p^2-1)! : ℤ) with hXdef
  set Y : ℤ := F_aux (p^2-1) with hYdef
  have hX0 : X ≠ 0 := by rw [hXdef]; exact_mod_cast Nat.factorial_ne_zero _
  have hdvdX : (p:ℤ)^(p-1) ∣ X := pow_dvd_fact_int p hp
  have hndvdX : ¬ (p:ℤ)^p ∣ X := pow_ndvd_fact_int p hp
  have hdvdY : (p:ℤ)^(p-1) ∣ Y := key_dvd p hp hodd hS
  have hgcdpos : 0 < Int.gcd X Y := by
    rcases Nat.eq_zero_or_pos (Int.gcd X Y) with h | h
    · rw [Int.gcd_eq_zero_iff] at h; exact absurd h.1 hX0
    · exact h
  have hN1 : (p^2 - 1) + 1 = p^2 := by omega
  have hgN : Int.gcd (F_aux ((p^2-1)+1)) (F_aux (p^2-1)) = Int.gcd X Y := by
    rw [gcd_step (p^2-1) hpos1]
  have hFp2 : F_aux ((p^2-1)+1) = (p:ℤ)^2 * Y - X := by
    rw [F_rec (p^2-1) hpos1]
    have hcond : ((p^2-1)+1) % 2 = 1 := by
      rw [hN1]; exact Nat.odd_iff.mp hodd.pow
    rw [hcond]
    have hne : ¬ (1:ℕ) = 0 := by norm_num
    rw [if_neg hne]
    rw [hYdef, hXdef]
    have hcast : ((p^2-1 : ℕ):ℤ) + 1 = (p:ℤ)^2 := by
      calc ((p^2-1 : ℕ):ℤ) + 1 = (((p^2-1)+1 : ℕ):ℤ) := by push_cast; ring
        _ = ((p^2 : ℕ):ℤ) := by rw [hN1]
        _ = (p:ℤ)^2 := by push_cast; ring
    rw [hcast]; ring
  have hgN1 : Int.gcd (F_aux ((p^2-1)+2)) (F_aux ((p^2-1)+1)) = Int.gcd X Y := by
    have hstep : Int.gcd (F_aux (((p^2-1)+1)+1)) (F_aux ((p^2-1)+1))
        = Int.gcd (((p^2-1)+1)! : ℤ) (F_aux ((p^2-1)+1)) :=
      gcd_step ((p^2-1)+1) (by omega)
    have h2 : ((p^2-1)+2) = ((p^2-1)+1)+1 := by omega
    rw [h2, hstep, hFp2]
    have hfact : (((p^2-1)+1)! : ℤ) = (p:ℤ)^2 * X := by
      rw [hXdef, Nat.factorial_succ]
      push_cast
      have hcast : ((p^2-1 : ℕ):ℤ) + 1 = (p:ℤ)^2 := by
        calc ((p^2-1 : ℕ):ℤ) + 1 = (((p^2-1)+1 : ℕ):ℤ) := by push_cast; ring
          _ = ((p^2 : ℕ):ℤ) := by rw [hN1]
          _ = (p:ℤ)^2 := by push_cast; ring
      rw [hcast]
    rw [hfact]
    exact crux p hp X Y hX0 hdvdX hdvdY hndvdX
  show (if Int.gcd (F_aux ((p^2-1)+1)) (F_aux (p^2-1)) = 0 then 0
        else Int.gcd (F_aux ((p^2-1)+2)) (F_aux ((p^2-1)+1))
              / Int.gcd (F_aux ((p^2-1)+1)) (F_aux (p^2-1))) = 1
  rw [hgN, hgN1, if_neg (by omega : ¬ Int.gcd X Y = 0)]
  exact Nat.div_self hgcdpos

set_option maxRecDepth 100000 in
/-- The conjecture `a(n) = 1 ↔ n+1 prime` is **false**: it fails at `n = 1093^2 - 1`, because
`1093` is a Wieferich prime, so `a(1093^2 - 1) = 1` while `1093^2` is composite. -/
theorem oeis_335023_conjecture_0.disproof :
    ¬ ∀ (n : ℕ), n > 0 → (a n = 1 ↔ Nat.Prime (n + 1)) := by
  intro H
  have hp : Nat.Prime 1093 := by norm_num
  have hodd : Odd 1093 := ⟨546, by norm_num⟩
  have hS : (∑ j ∈ Icc 1 (1093-1), ((-1:ZMod 1093))^j * ((j:ℕ):ZMod 1093)⁻¹) = 0 := by decide
  have hpos : 1093^2 - 1 > 0 := by norm_num
  have ha : a (1093^2 - 1) = 1 := a_at 1093 hp hodd hS
  have hnp : ¬ Nat.Prime (1093^2 - 1 + 1) := by
    have heq : 1093^2 - 1 + 1 = 1093 * 1093 := by norm_num
    rw [heq]
    intro hpr
    rcases (hpr.eq_one_or_self_of_dvd 1093 ⟨1093, rfl⟩) with h | h <;> omega
  exact hnp ((H (1093^2 - 1) hpos).mp ha)
