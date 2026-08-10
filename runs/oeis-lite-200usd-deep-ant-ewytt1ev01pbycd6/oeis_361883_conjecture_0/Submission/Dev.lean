import FormalConjectures.Util.ProblemImports

open Nat Finset

/-- Same definition as in `Spec.lean`. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3
    S / n

/-- The manifestly-integer form of `a`. -/
def aint (n : ℕ) : ℕ :=
  Finset.sum (range (n + 1)) fun k =>
    (Nat.choose (n + k - 1) (n - 1)) ^ 3
      + 2 * (Nat.choose (n + k - 1) n) * (Nat.choose (n + k - 1) (n - 1)) ^ 2

/-- Key termwise identity: `k * C(n+k-1, n-1) = n * C(n+k-1, n)` for `n ≥ 1`. -/
lemma key_absorb (n k : ℕ) (hn : 1 ≤ n) :
    k * (Nat.choose (n + k - 1) (n - 1)) = n * (Nat.choose (n + k - 1) n) := by
  have h := Nat.choose_succ_right_eq (n + k - 1) (n - 1)
  -- h : (n+k-1).choose (n-1+1) * (n-1+1) = (n+k-1).choose (n-1) * ((n+k-1) - (n-1))
  have e1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
  have e2 : (n + k - 1) - (n - 1) = k := by omega
  rw [e1, e2] at h
  -- h : (n+k-1).choose n * n = (n+k-1).choose (n-1) * k
  -- goal : k * (n+k-1).choose (n-1) = n * (n+k-1).choose n
  calc k * (Nat.choose (n + k - 1) (n - 1))
      = (Nat.choose (n + k - 1) (n - 1)) * k := by ring
    _ = (Nat.choose (n + k - 1) n) * n := h.symm
    _ = n * (Nat.choose (n + k - 1) n) := by ring

/-- The summand of `a`'s numerator equals `n` times the summand of `aint`. -/
lemma summand_factor (n k : ℕ) (hn : 1 ≤ n) :
    (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3
      = n * ((Nat.choose (n + k - 1) (n - 1)) ^ 3
          + 2 * (Nat.choose (n + k - 1) n) * (Nat.choose (n + k - 1) (n - 1)) ^ 2) := by
  set C := Nat.choose (n + k - 1) (n - 1) with hC
  set C' := Nat.choose (n + k - 1) n with hC'
  have habs : k * C = n * C' := key_absorb n k hn
  -- LHS = n*C^3 + 2k*C^3 ; RHS = n*C^3 + 2n*C'*C^2 ; need 2k*C^3 = 2n*C'*C^2
  have : (n + 2 * k) * C ^ 3 = n * C ^ 3 + 2 * (k * C) * C ^ 2 := by ring
  rw [this, habs]
  ring

/-- `S n = n * aint n`. -/
lemma S_eq (n : ℕ) (hn : 1 ≤ n) :
    (Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3) = n * aint n := by
  rw [aint, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact summand_factor n k hn

/-- For `n ≥ 1`, `a n = aint n`. -/
lemma a_eq_aint (n : ℕ) (hn : 1 ≤ n) : a n = aint n := by
  rw [a]
  have hn0 : n ≠ 0 := by omega
  simp only [hn0, if_false]
  rw [S_eq n hn]
  exact Nat.mul_div_cancel_left _ hn

/-- `bb N` is the numerator sum in `a`. -/
def bb (N : ℕ) : ℕ :=
  Finset.sum (range (N + 1)) fun k =>
    (N + 2 * k) * (Nat.choose (N + k - 1) (N - 1)) ^ 3

lemma bb_eq (N : ℕ) (hN : 1 ≤ N) : bb N = N * aint N := S_eq N hN

/-- Part A: `p^{4e}` divides the sum over the terms with `p ∤ k`. -/
lemma partA (p M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hM : 1 ≤ M) (hpM : p ∣ M) :
    (↑(p ^ (4 * M.factorization p)) : ℤ) ∣
      (((Finset.sum (Finset.filter (fun k => ¬ p ∣ k) (Finset.range (M+1)))
         (fun k => (M + 2*k) * (Nat.choose (M+k-1) (M-1))^3)) : ℕ) : ℤ) := sorry

/-- Part B: `p^{4e}` divides `p` times the sum of the "differences" `D_j`. -/
lemma partB (p M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hM : 1 ≤ M) (hpM : p ∣ M) :
    (↑(p ^ (4 * M.factorization p)) : ℤ) ∣
      ((p : ℤ) * Finset.sum (Finset.range (M/p + 1))
        (fun j => ((M/p + 2*j : ℕ) : ℤ) *
          (((Nat.choose (M + p*j - 1) (M-1))^3 : ℤ) - ((Nat.choose (M/p + j - 1) (M/p-1))^3 : ℤ)))) := sorry

/-- DEEP divisibility (Part A + Part B): for `p ≥ 5`, `M ≥ 1`, `p ∣ M`, with `e = v_p(M)`,
`p^{4e} ∣ bb M - p·bb (M/p)`. -/
lemma master_b (p M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hM : 1 ≤ M) (hpM : p ∣ M) :
    (↑(p ^ (4 * M.factorization p)) : ℤ) ∣ ((bb M : ℤ) - p * (bb (M / p) : ℤ)) := by
  have hp0 : 0 < p := hp.pos
  have hpm : p * (M / p) = M := Nat.mul_div_cancel' hpM
  have hmpos : 1 ≤ M / p := (Nat.one_le_div_iff hp0).mpr (Nat.le_of_dvd (by omega) hpM)
  -- Split `bb M` over divisibility by `p` (the `¬ p ∣ k` part first).
  have hsplit :
      (bb M : ℤ)
        = ((Finset.sum (Finset.filter (fun k => ¬ p ∣ k) (Finset.range (M+1)))
              (fun k => (M + 2*k) * (Nat.choose (M+k-1) (M-1))^3) : ℕ) : ℤ)
          + ((Finset.sum (Finset.filter (fun k => p ∣ k) (Finset.range (M+1)))
              (fun k => (M + 2*k) * (Nat.choose (M+k-1) (M-1))^3) : ℕ) : ℤ) := by
    have hsum := Finset.sum_filter_add_sum_filter_not (Finset.range (M+1)) (fun k => p ∣ k)
              (fun k => (M + 2*k) * (Nat.choose (M+k-1) (M-1))^3)
    have hbb : bb M
        = Finset.sum (Finset.range (M+1))
            (fun k => (M + 2*k) * (Nat.choose (M+k-1) (M-1))^3) := rfl
    rw [hbb, ← hsum]
    push_cast
    ring
  -- The bijection `{k ∈ range (M+1) : p ∣ k} = image (p * ·) (range (M/p+1))`.
  have hset : Finset.filter (fun k => p ∣ k) (Finset.range (M+1))
      = Finset.image (fun j => p * j) (Finset.range (M/p + 1)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, hd⟩
      obtain ⟨t, rfl⟩ := hd
      have hle : p * t ≤ p * (M / p) := by rw [hpm]; omega
      have ht : t ≤ M / p := Nat.le_of_mul_le_mul_left hle hp0
      exact ⟨t, by omega, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, dvd_mul_right p j⟩
      have hle : p * j ≤ p * (M / p) := mul_le_mul_left' (by omega) p
      rw [hpm] at hle
      omega
  -- Injectivity of `p * ·`.
  have hinj : Set.InjOn (fun j => p * j) (↑(Finset.range (M/p + 1)) : Set ℕ) := by
    intro x _ y _ h
    exact Nat.eq_of_mul_eq_mul_left hp0 h
  -- Reindex the `p ∣ k` sum and pull out a factor of `p`.
  have hfilterp :
      ((Finset.sum (Finset.filter (fun k => p ∣ k) (Finset.range (M+1)))
          (fun k => (M + 2*k) * (Nat.choose (M+k-1) (M-1))^3) : ℕ) : ℤ)
        = (p : ℤ) * Finset.sum (Finset.range (M/p + 1))
            (fun j => ((M/p + 2*j : ℕ) : ℤ) * ((Nat.choose (M + p*j - 1) (M-1))^3 : ℤ)) := by
    rw [hset, Finset.sum_image hinj, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hfac : M + 2 * (p * j) = p * (M / p + 2 * j) := by
      have hexp : p * (M / p + 2 * j) = p * (M / p) + 2 * (p * j) := by ring
      rw [hexp, hpm]
    rw [hfac]
    push_cast
    ring
  -- Cast `bb (M/p)` into the target's summand form.
  have hbbm : (bb (M/p) : ℤ)
      = Finset.sum (Finset.range (M/p + 1))
          (fun j => ((M/p + 2*j : ℕ) : ℤ) * ((Nat.choose (M/p + j - 1) (M/p-1))^3 : ℤ)) := by
    have hbb : bb (M/p)
        = Finset.sum (Finset.range (M/p + 1))
            (fun k => (M/p + 2*k) * (Nat.choose (M/p + k - 1) (M/p-1))^3) := rfl
    rw [hbb, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  -- Combine the two sums-of-cubes into one sum of differences.
  have hsub :
      Finset.sum (Finset.range (M/p + 1))
        (fun j => ((M/p + 2*j : ℕ) : ℤ) *
          (((Nat.choose (M + p*j - 1) (M-1))^3 : ℤ) - ((Nat.choose (M/p + j - 1) (M/p-1))^3 : ℤ)))
      = Finset.sum (Finset.range (M/p + 1))
          (fun j => ((M/p + 2*j : ℕ) : ℤ) * ((Nat.choose (M + p*j - 1) (M-1))^3 : ℤ))
        - Finset.sum (Finset.range (M/p + 1))
          (fun j => ((M/p + 2*j : ℕ) : ℤ) * ((Nat.choose (M/p + j - 1) (M/p-1))^3 : ℤ)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- The decomposition identity.
  have hdecomp :
      (bb M : ℤ) - (p : ℤ) * (bb (M/p) : ℤ)
        = ((Finset.sum (Finset.filter (fun k => ¬ p ∣ k) (Finset.range (M+1)))
              (fun k => (M + 2*k) * (Nat.choose (M+k-1) (M-1))^3) : ℕ) : ℤ)
          + ((p : ℤ) * Finset.sum (Finset.range (M/p + 1))
              (fun j => ((M/p + 2*j : ℕ) : ℤ) *
                (((Nat.choose (M + p*j - 1) (M-1))^3 : ℤ) - ((Nat.choose (M/p + j - 1) (M/p-1))^3 : ℤ)))) := by
    rw [hsplit, hfilterp, hbbm, hsub]
    ring
  rw [hdecomp]
  exact dvd_add (partA p M hp hp5 hM hpM) (partB p M hp hp5 hM hpM)

/-- Clean form: `p^{3e} ∣ aint M - aint (M/p)`. -/
lemma clean_aint (p M : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hM : 1 ≤ M) (hpM : p ∣ M) :
    (↑(p ^ (3 * M.factorization p)) : ℤ) ∣ ((aint M : ℤ) - (aint (M / p) : ℤ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hMne : M ≠ 0 := by omega
  have hMfact : p ^ (M.factorization p) * (M / p ^ (M.factorization p)) = M :=
    Nat.ordProj_mul_ordCompl_eq_self M p
  have hpu : ¬ p ∣ (M / p ^ (M.factorization p)) := Nat.not_dvd_ordCompl hp hMne
  set e := M.factorization p
  set u := M / p ^ e with hu
  -- bb M = M * aint M, bb (M/p) = (M/p) * aint (M/p)
  have hmpos : 1 ≤ M / p :=
    (Nat.one_le_div_iff hp.pos).mpr (Nat.le_of_dvd (by omega) hpM)
  have hbbM : (bb M : ℤ) = (M : ℤ) * (aint M : ℤ) := by
    rw [bb_eq M hM]; push_cast; ring
  have hbbm : (bb (M / p) : ℤ) = ((M / p : ℕ) : ℤ) * (aint (M / p) : ℤ) := by
    rw [bb_eq (M / p) hmpos]; push_cast; ring
  set D : ℤ := (aint M : ℤ) - (aint (M / p) : ℤ) with hD
  have hpMdiv : (p : ℤ) * ((M / p : ℕ) : ℤ) = (M : ℤ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hpM]
  have hX : (bb M : ℤ) - p * (bb (M / p) : ℤ) = (M : ℤ) * D := by
    rw [hbbM, hbbm, hD]
    rw [show (p:ℤ) * (((M/p:ℕ):ℤ) * (aint (M/p):ℤ))
        = ((p:ℤ) * ((M/p:ℕ):ℤ)) * (aint (M/p):ℤ) by ring, hpMdiv]
    ring
  have hdvd4 : (↑(p ^ (4 * e)) : ℤ) ∣ (M : ℤ) * D := by
    rw [← hX]; exact master_b p M hp hp5 hM hpM
  have hMcast : (M : ℤ) = (p : ℤ) ^ e * (u : ℤ) := by
    rw [← hMfact]; push_cast; ring
  rw [hMcast] at hdvd4
  have hsplit : (p : ℤ) ^ (4 * e) = (p:ℤ)^e * (p:ℤ)^(3*e) := by
    rw [← pow_add]; ring_nf
  rw [Nat.cast_pow] at hdvd4 ⊢
  rw [hsplit] at hdvd4
  have hpne : (p:ℤ)^e ≠ 0 := by positivity
  rw [mul_assoc, mul_dvd_mul_iff_left hpne] at hdvd4
  have hcop : IsCoprime ((p:ℤ)^(3*e)) (u : ℤ) := by
    apply IsCoprime.pow_left
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hpu
  exact hcop.dvd_of_dvd_mul_left hdvd4

lemma master (p n r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    (↑(p ^ (3 * r)) : ℤ) ∣ (↑(aint (n * p ^ (r - 1))) - ↑(aint (n * p ^ r))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set M := n * p ^ r with hMdef
  have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hpM : p ∣ M := by
    rw [hMdef]
    have : p ∣ p ^ r := dvd_pow_self p (by omega)
    exact Dvd.dvd.mul_left this n
  have hfac : (n * p ^ (r - 1)) * p = n * p ^ r := by
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hr]
  have hMp : M / p = n * p ^ (r - 1) := by
    rw [hMdef, ← hfac, Nat.mul_div_cancel _ hp.pos]
  -- e = v_p(M) ≥ r
  have he_ge : r ≤ M.factorization p := by
    rw [hMdef, Nat.factorization_mul (by omega) (by positivity)]
    simp only [Finsupp.coe_add, Pi.add_apply, Nat.Prime.factorization_pow hp,
      Finsupp.single_eq_same]
    omega
  have hclean := clean_aint p M hp hp5 hM hpM
  rw [hMp] at hclean
  -- p^{3r} ∣ p^{3e} ∣ (aint M - aint (np^{r-1}))
  have hdvd : (↑(p ^ (3 * r)) : ℤ) ∣ (↑(aint M) - ↑(aint (n * p ^ (r-1)))) := by
    refine dvd_trans ?_ hclean
    rw [Nat.cast_pow, Nat.cast_pow]
    exact pow_dvd_pow _ (by omega)
  -- goal has the difference in opposite order
  rw [hMdef] at hdvd
  rw [show (↑(aint (n * p ^ (r - 1))) : ℤ) - ↑(aint (n * p ^ r))
      = -(↑(aint (n * p ^ r)) - ↑(aint (n * p ^ (r-1)))) by ring]
  exact Dvd.dvd.neg_right hdvd

theorem main (p n r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  have hp1 : 1 ≤ p := by omega
  have hM : 1 ≤ n * p ^ r := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hm : 1 ≤ n * p ^ (r - 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  rw [a_eq_aint _ hM, a_eq_aint _ hm]
  rw [Nat.modEq_iff_dvd]
  exact master p n r hp hp5 hn hr
