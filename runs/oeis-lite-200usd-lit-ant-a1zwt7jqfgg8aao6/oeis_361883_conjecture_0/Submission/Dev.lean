import FormalConjectures.Util.ProblemImports

open Nat Finset

def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3
    S / n

/-- Absorption identity: `(j+1) * C(m+j+1, j+1) = (m+1) * C(m+j+1, j)`. -/
lemma absorb (m j : ℕ) :
    (j + 1) * (m + j + 1).choose (j + 1) = (m + 1) * (m + j + 1).choose j := by
  have h := Nat.choose_succ_right_eq (m + j + 1) j
  -- h : (m+j+1).choose (j+1) * (j+1) = (m+j+1).choose j * ((m+j+1) - j)
  have hsub : (m + j + 1) - j = m + 1 := by omega
  rw [hsub] at h
  -- h : (m+j+1).choose (j+1) * (j+1) = (m+j+1).choose j * (m+1)
  calc (j + 1) * (m + j + 1).choose (j + 1)
      = (m + j + 1).choose (j + 1) * (j + 1) := by ring
    _ = (m + j + 1).choose j * (m + 1) := h
    _ = (m + 1) * (m + j + 1).choose j := by ring

/-- The numerator sum `S`, rewritten with the symmetric lower index `k`. -/
lemma choose_rewrite (m k : ℕ) :
    (Nat.choose (m + 1 + k - 1) (m + 1 - 1)) = (m + k).choose k := by
  have h1 : m + 1 + k - 1 = m + k := by omega
  have h2 : m + 1 - 1 = m := by omega
  rw [h1, h2]
  exact Nat.choose_symm_add

/-- Division-free value of `a` for `n = m+1 ≥ 1`. -/
lemma a_val (m : ℕ) :
    a (m + 1) = (∑ k ∈ range (m + 2), ((m + k).choose k) ^ 3)
      + 2 * (∑ k ∈ range (m + 1), (m + k + 1).choose k * ((m + k + 1).choose (k + 1)) ^ 2) := by
  have hne : m + 1 ≠ 0 := by omega
  -- Rewrite the raw numerator using the symmetric lower index.
  have hnum : (∑ k ∈ range (m + 1 + 1),
        (m + 1 + 2 * k) * (Nat.choose (m + 1 + k - 1) (m + 1 - 1)) ^ 3)
      = ∑ k ∈ range (m + 2), (m + 1 + 2 * k) * ((m + k).choose k) ^ 3 := by
    have : m + 1 + 1 = m + 2 := rfl
    rw [this]
    apply Finset.sum_congr rfl
    intro k _
    rw [choose_rewrite]
  -- Split (m+1+2k) = (m+1) + 2k and reindex the k-weighted part.
  have hsum : (∑ k ∈ range (m + 2), (m + 1 + 2 * k) * ((m + k).choose k) ^ 3)
      = (m + 1) * ((∑ k ∈ range (m + 2), ((m + k).choose k) ^ 3)
        + 2 * (∑ k ∈ range (m + 1), (m + k + 1).choose k * ((m + k + 1).choose (k + 1)) ^ 2)) := by
    -- distribute the summand
    have hsplit : (∑ k ∈ range (m + 2), (m + 1 + 2 * k) * ((m + k).choose k) ^ 3)
        = (m + 1) * (∑ k ∈ range (m + 2), ((m + k).choose k) ^ 3)
          + 2 * (∑ k ∈ range (m + 2), k * ((m + k).choose k) ^ 3) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsplit]
    -- reindex the k-weighted sum, dropping the k=0 term
    have hre : (∑ k ∈ range (m + 2), k * ((m + k).choose k) ^ 3)
        = (m + 1) * (∑ k ∈ range (m + 1), (m + k + 1).choose k * ((m + k + 1).choose (k + 1)) ^ 2) := by
      rw [show m + 2 = (m + 1) + 1 from rfl, Finset.sum_range_succ']
      simp only [Nat.zero_mul, Nat.add_zero]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      -- (k+1) * ((m+(k+1)).choose (k+1))^3 = (m+1) * C(m+k+1,k) * C(m+k+1,k+1)^2
      have hc : m + (k + 1) = m + k + 1 := by ring
      rw [hc]
      have hab := absorb m k
      -- hab : (k+1) * (m+k+1).choose (k+1) = (m+1) * (m+k+1).choose k
      have : (k + 1) * ((m + k + 1).choose (k + 1)) ^ 3
          = ((k + 1) * (m + k + 1).choose (k + 1)) * ((m + k + 1).choose (k + 1)) ^ 2 := by ring
      rw [this, hab]
      ring
    rw [hre]; ring
  -- Conclude via exact division.
  rw [a]
  simp only [hne, if_false]
  rw [hnum, hsum, Nat.mul_div_cancel_left _ (by omega : 0 < m + 1)]

/-- Absorption in `(N,k)` form: `k · C(N+k-1, k) = N · C(N+k-1, k-1)` for `N,k ≥ 1`. -/
lemma absorb' (N k : ℕ) (hN : 1 ≤ N) (hk : 1 ≤ k) :
    k * (N + k - 1).choose k = N * (N + k - 1).choose (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have e1 : m + 1 + (j + 1) - 1 = m + j + 1 := by omega
  have e2 : j + 1 - 1 = j := by omega
  rw [e1, e2]
  exact absorb m j

/-- Binomial recurrence in the diagonal direction:
`(i+1)·C(X+i+1, i+1) = (X+i+1)·C(X+i, i)`. -/
lemma choose_rec (X i : ℕ) :
    (i + 1) * (X + i + 1).choose (i + 1) = (X + i + 1) * (X + i).choose i := by
  have h := Nat.add_one_mul_choose_eq (X + i) i
  -- h : (X+i+1) * (X+i).choose i = (X+i+1).choose (i+1) * (i+1)
  rw [mul_comm (i + 1), ← h]

/-- Key divisibility (no Kummer needed): if `p^t ∣ N` and `p ∤ k` (`k ≥ 1`), then
`p^t ∣ C(N+k-1, k)`.  This is immediate from absorption `k·C = N·C(N+k-1,k-1)`. -/
lemma pow_dvd_choose (p t N k : ℕ) (hp : p.Prime) (hN : p ^ t ∣ N)
    (hk : 1 ≤ k) (hpk : ¬ p ∣ k) : p ^ t ∣ (N + k - 1).choose k := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    -- C(k-1, k) = 0 since k > k-1
    have : (0 + k - 1).choose k = 0 := by
      apply Nat.choose_eq_zero_of_lt; omega
    rw [this]; exact dvd_zero _
  · have habs := absorb' N k hNpos hk
    -- p^t ∣ N * C(..k-1) = k * C(..k)
    have hdvd : p ^ t ∣ k * (N + k - 1).choose k := by
      rw [habs]; exact Dvd.dvd.mul_right hN _
    have hcop : (p ^ t).Coprime k :=
      Nat.Coprime.pow_left t ((hp.coprime_iff_not_dvd).mpr hpk)
    exact (Nat.Coprime.dvd_of_dvd_mul_left hcop hdvd)

/-- One within-block step of the Lucas lifting: if `p^t ∣ X` and `p ∤ j` (`j ≥ 1`),
then `C(X+j, j) ≡ C(X+j-1, j-1) (mod p^t)`. -/
lemma block_step (p t X j : ℕ) (hp : p.Prime) (ht : p ^ t ∣ X) (hj : 1 ≤ j)
    (hpj : ¬ p ∣ j) :
    ((X + j).choose j : ZMod (p ^ t)) = ((X + j - 1).choose (j - 1) : ZMod (p ^ t)) := by
  haveI : NeZero (p ^ t) := ⟨pow_ne_zero t hp.pos.ne'⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hrec := choose_rec X i
  have hcast : ((i + 1 : ℕ) : ZMod (p ^ t)) * (((X + i + 1).choose (i + 1) : ℕ) : ZMod (p ^ t))
      = ((X + i + 1 : ℕ) : ZMod (p ^ t)) * (((X + i).choose i : ℕ) : ZMod (p ^ t)) := by
    exact_mod_cast congrArg (Nat.cast (R := ZMod (p ^ t))) hrec
  have hX0 : ((X : ℕ) : ZMod (p ^ t)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]; exact ht
  have hXi : ((X + i + 1 : ℕ) : ZMod (p ^ t)) = ((i + 1 : ℕ) : ZMod (p ^ t)) := by
    push_cast; rw [hX0]; ring
  rw [hXi] at hcast
  have hcop : Nat.Coprime (i + 1) (p ^ t) :=
    (Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hpj)).pow_right t
  have hu : IsUnit ((i + 1 : ℕ) : ZMod (p ^ t)) :=
    (ZMod.isUnit_iff_coprime (i + 1) (p ^ t)).mpr hcop
  have e1 : X + (i + 1) - 1 = X + i := by omega
  have e2 : (i + 1) - 1 = i := by omega
  rw [e1, e2]
  exact hu.mul_right_injective hcast

/-- Wolstenholme mod `p` (base form): `∑_{x ∈ ZMod p} x^(p-3) = 0` for a prime `p ≥ 5`.
Since `x^(p-3) = x^{-2}` on units, this is `∑_{a=1}^{p-1} 1/a² ≡ 0 (mod p)`. -/
lemma wolstenholme_base (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ x : ZMod p, x ^ (p - 3) = 0 := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  apply FiniteField.sum_pow_lt_card_sub_one
  rw [hcard]
  omega



lemma prod_Icc_id (B:ℕ) : ∏ i ∈ Icc 1 B, i = B ! := by
  induction B with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]; ring

lemma range_to_Icc (c n : ℕ) : ∏ i ∈ range n, (c + 1 + i) = ∏ j ∈ Icc 1 n, (c + j) := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.prod_range_succ, ih, Finset.prod_Icc_succ_top (by omega)]; ring

lemma descFact_Icc (A B p : ℕ) (h : B ≤ A) :
    (p*A).descFactorial (p*B) = ∏ j ∈ Icc 1 (p*B), (p*(A-B) + j) := by
  rw [Nat.descFactorial_eq_prod_range, ← Finset.prod_range_reflect, ← range_to_Icc]
  apply Finset.prod_congr rfl
  intro i hi; simp only [Finset.mem_range] at hi
  have hle : p*B ≤ p*A := Nat.mul_le_mul_left p h
  rw [Nat.mul_sub]; omega

lemma filter_dvd_eq_image (p B : ℕ) (hp : 0 < p) :
    (Icc 1 (p*B)).filter (fun i => p ∣ i) = (Icc 1 B).image (fun l => p * l) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, l, rfl⟩
    exact ⟨l, ⟨by nlinarith, by nlinarith⟩, rfl⟩
  · rintro ⟨l, ⟨hl1, hl2⟩, rfl⟩
    exact ⟨⟨by nlinarith, by nlinarith⟩, ⟨l, rfl⟩⟩

lemma prod_mult_id (p B : ℕ) (hp : 0 < p) :
    ∏ i ∈ (Icc 1 (p*B)).filter (fun i => p ∣ i), i = p^B * B ! := by
  rw [filter_dvd_eq_image p B hp,
      Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h),
      Finset.prod_mul_distrib, prod_Icc_id]
  simp [Finset.prod_const, Nat.card_Icc]

lemma prod_mult_shift (p B D : ℕ) (hp : 0 < p) :
    ∏ i ∈ (Icc 1 (p*B)).filter (fun i => p ∣ i), (p*D + i)
      = p^B * ∏ l ∈ Icc 1 B, (D + l) := by
  rw [filter_dvd_eq_image p B hp,
      Finset.prod_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h)]
  have : ∀ x, p*D + p*x = p*(D+x) := fun x => by ring
  simp_rw [this]
  rw [Finset.prod_mul_distrib]
  simp [Finset.prod_const, Nat.card_Icc]

lemma prod_Icc_shift_choose (B D : ℕ) :
    ∏ l ∈ Icc 1 B, (D + l) = B ! * (D + B).choose B := by
  have h := descFact_Icc (D+B) B 1 (by omega)
  simp only [one_mul, Nat.add_sub_cancel] at h
  rw [← h, Nat.descFactorial_eq_factorial_mul_choose]

/-- The product identity: `C(pA,pB) · P = C(A,B) · Q`, where
`P = ∏_{i≤pB, p∤i} i` and `Q = ∏_{i≤pB, p∤i}(p(A-B)+i)`. -/
theorem prod_identity (p A B : ℕ) (hp : 0 < p) (h : B ≤ A) :
    (p*A).choose (p*B) * (∏ i ∈ (Icc 1 (p*B)).filter (fun i => ¬ p ∣ i), i)
      = A.choose B * (∏ i ∈ (Icc 1 (p*B)).filter (fun i => ¬ p ∣ i), (p*(A-B) + i)) := by
  set P := ∏ i ∈ (Icc 1 (p*B)).filter (fun i => ¬ p ∣ i), i with hP
  set Q := ∏ i ∈ (Icc 1 (p*B)).filter (fun i => ¬ p ∣ i), (p*(A-B) + i) with hQ
  -- (pB)! * C(pA,pB) = ∏ (pD + j)
  have key : (p*B)! * (p*A).choose (p*B) = ∏ j ∈ Icc 1 (p*B), (p*(A-B) + j) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose, descFact_Icc A B p h]
  -- split LHS factorial product
  have hfac : (p*B)! = (p^B * B !) * P := by
    rw [← prod_Icc_id, ← Finset.prod_filter_mul_prod_filter_not (Icc 1 (p*B)) (fun i => p ∣ i) (fun i => i),
        prod_mult_id p B hp]
  -- split RHS shifted product
  have hshift : (∏ j ∈ Icc 1 (p*B), (p*(A-B) + j)) = (p^B * ∏ l ∈ Icc 1 B, ((A-B) + l)) * Q := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Icc 1 (p*B)) (fun i => p ∣ i) (fun j => p*(A-B) + j),
        prod_mult_shift p B (A-B) hp]
  rw [prod_Icc_shift_choose B (A-B)] at hshift
  have hAB : (A - B) + B = A := by omega
  rw [hAB] at hshift
  -- Now: P*(p^B B!) * C(pA,pB) = Q * (p^B * (B! * C(A,B)))
  rw [hfac] at key
  rw [hshift] at key
  -- key : P * (p^B * B!) * C(pA,pB) = Q * (p^B * (B! * C(A,B)))
  have hpos : 0 < p^B * B ! := by positivity
  -- cancel p^B * B!
  have hc : (p^B * B !) * (P * (p*A).choose (p*B)) = (p^B * B !) * (Q * (A.choose B)) := by
    ring_nf; ring_nf at key; linarith [key]
  have := Nat.eq_of_mul_eq_mul_left hpos hc
  linarith [this]

-- Lucas lifting
theorem lucas_lift (p A B t : ℕ) (hp : p.Prime) (h : B ≤ A) (ht : 1 ≤ t)
    (hd : p^(t-1) ∣ (A - B)) :
    ((p*A).choose (p*B) : ZMod (p^t)) = (A.choose B : ZMod (p^t)) := by
  haveI : NeZero (p^t) := ⟨pow_ne_zero t hp.pos.ne'⟩
  have hpp : 0 < p := hp.pos
  have key := prod_identity p A B hpp h
  set S := (Icc 1 (p*B)).filter (fun i => ¬ p ∣ i) with hS
  -- cast identity to ZMod
  have hcast := congrArg (Nat.cast (R := ZMod (p^t))) key
  push_cast at hcast
  -- hcast : ↑C(pA,pB) * ∏ i∈S, ↑i = ↑C(A,B) * ∏ x∈S, (↑p*↑(A-B)+↑x)
  -- Q ≡ P : each term ≡ i
  have hpD : (p^t) ∣ p*(A-B) := by
    obtain ⟨c, hc⟩ := hd
    have hpe : p^t = p * p^(t-1) := by
      conv_lhs => rw [show t = 1+(t-1) from by omega]
      rw [pow_add, pow_one]
    rw [hc, ← mul_assoc, ← hpe]
    exact dvd_mul_right _ c
  have hpD0 : ((p:ZMod (p^t))) * ((A-B:ℕ):ZMod (p^t)) = 0 := by
    have : ((p*(A-B):ℕ):ZMod (p^t)) = 0 := by rw [ZMod.natCast_eq_zero_iff]; exact hpD
    push_cast at this; exact this
  have hQP : (∏ x ∈ S, ((p:ZMod (p^t)) * ((A-B:ℕ):ZMod (p^t)) + (x:ZMod (p^t))))
      = ∏ i ∈ S, (i:ZMod (p^t)) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [hpD0]; ring
  rw [hQP] at hcast
  -- P is a unit
  have hprodcast : (∏ i ∈ S, (i:ZMod (p^t))) = ((∏ i ∈ S, i : ℕ):ZMod (p^t)) := by
    rw [Nat.cast_prod]
  have hcop : Nat.Coprime (∏ i ∈ S, i) (p^t) := by
    apply Nat.Coprime.prod_left
    intro i hi
    simp only [hS, Finset.mem_filter, Finset.mem_Icc] at hi
    exact (Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hi.2)).pow_right t
  have hunit : IsUnit (∏ i ∈ S, (i:ZMod (p^t))) := by
    rw [hprodcast, ZMod.isUnit_iff_coprime]; exact hcop
  exact hunit.mul_left_injective hcast

-- ===== Wolstenholme mod p^2 machinery =====
lemma sum_Icc_one {R:Type*}[AddCommMonoid R] (m:ℕ) (g:ℕ→R) :
    ∑ k ∈ Icc 1 m, g k = ∑ i ∈ range m, g (i+1) := by
  induction m with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma sum_range_eq_Icc {R:Type*}[AddCommMonoid R] (p:ℕ) (hp:1≤p) (g : ℕ → R) (h0 : g 0 = 0) :
    ∑ k ∈ range p, g k = ∑ k ∈ Icc 1 (p-1), g k := by
  rw [sum_Icc_one]
  conv_lhs => rw [show p = (p-1)+1 from by omega, Finset.sum_range_succ']
  rw [h0, add_zero]

lemma zmod_sum_range (p:ℕ)[NeZero p] (f : ZMod p → ZMod p) :
    ∑ x : ZMod p, f x = ∑ k ∈ range p, f (k:ZMod p) := by
  apply Finset.sum_nbij' (i := fun x => ZMod.val x) (j := fun k => ((k:ℕ):ZMod p))
  · intro x _; simp [Finset.mem_range, ZMod.val_lt]
  · intro k hk; exact Finset.mem_univ _
  · intro x _; simp [ZMod.natCast_val, ZMod.cast_id]
  · intro k hk; simp only [Finset.mem_range] at hk; rw [ZMod.val_cast_of_lt hk]
  · intro x _; rw [ZMod.natCast_val, ZMod.cast_id]

lemma inv_sq_sum (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∑ k ∈ Icc 1 (p-1), (((k:ZMod p))⁻¹)^2 = 0 := by
  have hb : ∑ x : ZMod p, x ^ (p - 3) = 0 := by
    apply FiniteField.sum_pow_lt_card_sub_one
    rw [ZMod.card]; omega
  rw [zmod_sum_range] at hb
  rw [sum_range_eq_Icc p (by omega) _ (by simp [zero_pow (by omega : p - 3 ≠ 0)])] at hb
  rw [← hb]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_Icc] at hk
  have hne : ((k:ZMod p)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff k p]
    intro hdvd
    have : p ≤ k := Nat.le_of_dvd (by omega) hdvd
    omega
  have hfermat : ((k:ZMod p))^(p-1) = 1 := ZMod.pow_card_sub_one_eq_one hne
  have h2 : ((k:ZMod p))^(p-3) * ((k:ZMod p))^2 = 1 := by
    rw [← pow_add, show (p-3)+2 = p-1 from by omega, hfermat]
  field_simp
  rw [← h2]; ring

lemma reindex_pk {R : Type*} [AddCommMonoid R] (p : ℕ) (f : ℕ → R) :
    ∑ k ∈ Icc 1 (p-1), f k = ∑ k ∈ Icc 1 (p-1), f (p - k) := by
  apply Finset.sum_nbij' (fun k => p - k) (fun k => p - k)
  · intro k hk; simp only [Finset.mem_Icc] at *; omega
  · intro k hk; simp only [Finset.mem_Icc] at *; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; congr 1; omega

lemma pmul_eq_zero (p : ℕ) (hp: 0<p) (a : ZMod (p^2)) (h : p ∣ a.val) :
    (p : ZMod (p^2)) * a = 0 := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.ne'⟩
  conv_lhs => rw [← ZMod.natCast_rightInverse a]
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  obtain ⟨m, hm⟩ := h
  exact ⟨m, by rw [hm]; ring⟩

lemma pair_inv (n:ℕ) (a b : ZMod n) (ha:IsUnit a)(hb:IsUnit b)(hab:IsUnit (a*b)) :
    a⁻¹ + b⁻¹ = (a+b) * (a*b)⁻¹ := by
  have hai : a⁻¹ * a = 1 := ZMod.inv_mul_of_unit a ha
  have hbi : b⁻¹ * b = 1 := ZMod.inv_mul_of_unit b hb
  have habi : (a*b)⁻¹ * (a*b) = 1 := ZMod.inv_mul_of_unit _ hab
  have h1 : (a⁻¹+b⁻¹)*(a*b) = a+b := by
    calc (a⁻¹+b⁻¹)*(a*b) = (a⁻¹*a)*b + (b⁻¹*b)*a := by ring
      _ = 1*b + 1*a := by rw [hai,hbi]
      _ = a+b := by ring
  have h2 : ((a+b)*(a*b)⁻¹)*(a*b) = a+b := by
    calc ((a+b)*(a*b)⁻¹)*(a*b) = (a+b)*((a*b)⁻¹*(a*b)) := by ring
      _ = (a+b)*1 := by rw [habi]
      _ = a+b := by ring
  exact hab.mul_left_injective (h1.trans h2.symm)

lemma wolstenholme_p2 (p:ℕ)[hpp:Fact p.Prime] (hp5:5≤p) :
    ∑ k ∈ Icc 1 (p-1), ((k:ZMod (p^2)))⁻¹ = 0 := by
  have hpprime := (Fact.out : p.Prime)
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hpprime.pos.ne'⟩
  -- units
  have hunit : ∀ k ∈ Icc 1 (p-1), IsUnit ((k:ZMod (p^2))) := by
    intro k hk; rw [ZMod.isUnit_iff_coprime]
    simp only [Finset.mem_Icc] at hk
    refine (Nat.coprime_comm.mp ?_).pow_right 2
    rw [hpprime.coprime_iff_not_dvd]; intro h
    have := Nat.le_of_dvd (by omega) h; omega
  have hbunit : ∀ k ∈ Icc 1 (p-1), IsUnit (((p-k:ℕ):ZMod (p^2))) := by
    intro k hk; apply hunit; simp only [Finset.mem_Icc] at *; omega
  have hSrev : (∑ k ∈ Icc 1 (p-1), ((k:ZMod (p^2)))⁻¹)
      = ∑ k ∈ Icc 1 (p-1), (((p-k:ℕ):ZMod (p^2)))⁻¹ :=
    reindex_pk p (fun k => ((k:ZMod (p^2)))⁻¹)
  -- 2S = ↑p * T
  have key : (2:ZMod (p^2)) * (∑ k ∈ Icc 1 (p-1), ((k:ZMod (p^2)))⁻¹)
      = (p:ZMod (p^2)) * (∑ k ∈ Icc 1 (p-1), ((((k*(p-k)):ℕ):ZMod (p^2)))⁻¹) := by
    rw [two_mul]
    nth_rewrite 2 [hSrev]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hak := hunit k hk
    have hbk := hbunit k hk
    have habk : IsUnit ((k:ZMod (p^2)) * ((p-k:ℕ):ZMod (p^2))) := hak.mul hbk
    rw [pair_inv _ _ _ hak hbk habk]
    have hsum : ((k:ZMod (p^2))) + ((p-k:ℕ):ZMod (p^2)) = (p:ZMod (p^2)) := by
      rw [← Nat.cast_add]; congr 1; simp only [Finset.mem_Icc] at hk; omega
    have hprod : ((k:ZMod (p^2))) * ((p-k:ℕ):ZMod (p^2)) = (((k*(p-k)):ℕ):ZMod (p^2)) := by
      rw [Nat.cast_mul]
    rw [hsum, hprod]
  -- T maps to 0 mod p
  set phi := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) with hphidef
  have hcastinv : ∀ u : ZMod (p^2), IsUnit u → phi u⁻¹ = (phi u)⁻¹ := by
    intro u hu
    have h1 : phi u * phi u⁻¹ = 1 := by rw [← map_mul, ZMod.mul_inv_of_unit u hu, map_one]
    exact (inv_eq_of_mul_eq_one_right h1).symm
  have hTval : (p:ℕ) ∣ (∑ k ∈ Icc 1 (p-1), ((((k*(p-k)):ℕ):ZMod (p^2)))⁻¹).val := by
    rw [← ZMod.natCast_eq_zero_iff]
    have : ((∑ k ∈ Icc 1 (p-1), ((((k*(p-k)):ℕ):ZMod (p^2)))⁻¹).val : ZMod p)
        = phi (∑ k ∈ Icc 1 (p-1), ((((k*(p-k)):ℕ):ZMod (p^2)))⁻¹) := by
      rw [ZMod.natCast_val, hphidef, ZMod.castHom_apply]
    rw [this, map_sum]
    -- each term phi ((↑(k(p-k)))⁻¹) = -((↑k)⁻¹)^2 in ZMod p
    have hterm : ∀ k ∈ Icc 1 (p-1),
        phi ((((k*(p-k)):ℕ):ZMod (p^2)))⁻¹ = -(((k:ZMod p))⁻¹)^2 := by
      intro k hk
      have hkmem := hk
      simp only [Finset.mem_Icc] at hkmem
      have hak := hunit k hk
      have hbk := hbunit k hk
      have habk : IsUnit ((((k*(p-k)):ℕ):ZMod (p^2))) := by rw [Nat.cast_mul]; exact hak.mul hbk
      rw [hcastinv _ habk]
      -- phi (↑(k(p-k))) = ↑k * ↑(p-k) = ↑k*(-↑k) = -↑k^2 in ZMod p
      have hphikk : phi (((k*(p-k)):ℕ):ZMod (p^2)) = -((k:ZMod p))^2 := by
        rw [map_natCast]
        push_cast
        have hpk : ((p-k:ℕ):ZMod p) = -(k:ZMod p) := by
          have : ((p-k:ℕ):ZMod p) = (p:ZMod p) - (k:ZMod p) := by
            rw [← Nat.cast_sub (by omega)]
          rw [this, ZMod.natCast_self]; ring
        rw [hpk]; ring
      rw [hphikk]
      have hkne : ((k:ZMod p)) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff k p]; intro hd
        have := Nat.le_of_dvd (by omega) hd; omega
      rw [inv_pow]
      field_simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, inv_sq_sum p hp5, neg_zero]
  have hpT : (p:ZMod (p^2)) * (∑ k ∈ Icc 1 (p-1), ((((k*(p-k)):ℕ):ZMod (p^2)))⁻¹) = 0 :=
    pmul_eq_zero p hpprime.pos _ hTval
  rw [hpT] at key
  -- 2 * S = 0, 2 is a unit
  have h2unit : IsUnit (2:ZMod (p^2)) := by
    rw [show (2:ZMod (p^2)) = ((2:ℕ):ZMod (p^2)) by push_cast; ring, ZMod.isUnit_iff_coprime]
    refine (Nat.coprime_comm.mp ?_).pow_right 2
    rw [hpprime.coprime_iff_not_dvd]; intro h
    have := (Nat.prime_dvd_prime_iff_eq hpprime Nat.prime_two).mp h; omega
  have : (2:ZMod (p^2)) * (∑ k ∈ Icc 1 (p-1), ((k:ZMod (p^2)))⁻¹) = (2:ZMod (p^2)) * 0 := by
    rw [mul_zero]; exact key
  exact h2unit.mul_right_injective this

-- ===== Generalized Lucas via iterated block_step =====
lemma iter_block_step (p t Z : ℕ) (hp : p.Prime) (ht : p ^ t ∣ Z) :
    ∀ r j : ℕ, r ≤ j → (∀ i, 1 ≤ i → i ≤ r → ¬ p ∣ (j - i + 1)) →
    ((Z + j).choose j : ZMod (p ^ t)) = ((Z + j - r).choose (j - r) : ZMod (p ^ t)) := by
  intro r
  induction r with
  | zero => intro j _ _; simp
  | succ n ih =>
    intro j hj hcond
    have hpj : ¬ p ∣ j := by
      have := hcond 1 (by omega) (by omega)
      rw [show j-1+1 = j from by omega] at this; exact this
    have hstep := block_step p t Z j hp ht (by omega) hpj
    rw [hstep]
    have e1 : Z + j - 1 = Z + (j-1) := by omega
    rw [e1]
    have hih := ih (j-1) (by omega)
      (by intro i hi1 hir
          have := hcond (i+1) (by omega) (by omega)
          rw [show j-1-i+1 = j-(i+1)+1 from by omega]; exact this)
    rw [hih]
    congr 2 <;> omega

/-- Generalized Lucas: `C(pM' + pq' + b, pq'+b) ≡ C(M'+q', q') (mod p^s)` for `b < p`,
`p^{s-1} ∣ M'`. -/
lemma gen_lucas (p s M' q' b : ℕ) (hp : p.Prime) (hs : 1 ≤ s) (hM' : p^(s-1) ∣ M') (hb : b < p) :
    ((p*M' + p*q' + b).choose (p*q'+b) : ZMod (p^s))
      = ((M'+q').choose q' : ZMod (p^s)) := by
  have hpe : p^s = p * p^(s-1) := by
    conv_lhs => rw [show s = 1+(s-1) from by omega]
    rw [pow_add, pow_one]
  have hZ : p^s ∣ p*M' := by
    obtain ⟨c, hc⟩ := hM'
    exact ⟨c, by rw [hc, hpe]; ring⟩
  -- rewrite the choose as C(Z+j, j) with Z = p*M', j = p*q'+b
  have hrw : p*M' + p*q' + b = p*M' + (p*q'+b) := by ring
  rw [hrw]
  have hstep := iter_block_step p s (p*M') hp hZ b (p*q'+b) (by omega)
    (by intro i hi1 hib
        rw [show p*q'+b - i + 1 = p*q' + (b-i+1) from by omega]
        intro hdvd
        have : p ∣ (b - i + 1) := by
          have := (Nat.dvd_add_right ⟨q', rfl⟩).mp hdvd; exact this
        have := Nat.le_of_dvd (by omega) this; omega)
  rw [hstep]
  -- now C(p*M' + (p*q'+b) - b, (p*q'+b) - b) = C(p*M' + p*q', p*q')
  have e1 : p*M' + (p*q'+b) - b = p*M' + p*q' := by omega
  have e2 : (p*q'+b) - b = p*q' := by omega
  rw [e1, e2]
  -- C(p*(M'+q'), p*q') ≡ C(M'+q', q') mod p^s
  have hrw2 : p*M' + p*q' = p*(M'+q') := by ring
  rw [hrw2, show p*q' = p*q' from rfl]
  have := lucas_lift p (M'+q') q' s hp (by omega) hs (by rw [show M'+q'-q' = M' from by omega]; exact hM')
  exact this

-- ===== Sub-lemma L: p^(s-j) ∣ Σ_{q<M} C(M+q,q)^3 q^j =====
lemma sum_range_block {R : Type*} [AddCommMonoid R] (M' p : ℕ) (f : ℕ → R) :
    ∑ q ∈ range (p*M'), f q = ∑ q' ∈ range M', ∑ b ∈ range p, f (p*q'+b) := by
  induction M' with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, show p*(n+1) = p*n + p from by ring, Finset.sum_range_add]

lemma L_sub (p : ℕ) (hp : p.Prime) :
    ∀ s : ℕ, ∀ M : ℕ, p^s ∣ M → ∀ j : ℕ,
      (p:ℤ)^(s - j) ∣ ∑ q ∈ range M, ((M+q).choose q : ℤ)^3 * (q:ℤ)^j := by
  intro s
  induction s with
  | zero => intro M _ j; simp
  | succ s ih =>
    intro M hM j
    have hpM : p ∣ M := dvd_trans (dvd_pow_self p (Nat.succ_ne_zero s)) hM
    obtain ⟨M', rfl⟩ := hpM
    have hM' : p^s ∣ M' := by
      have : p^(s+1) ∣ p * M' := hM
      rw [pow_succ'] at this
      exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.pos.ne')).mp this
    -- reindex
    rw [sum_range_block]
    -- correction congruence: c_q^3 ≡ c'^3 mod p^{s+1}
    have hcorr : ∀ q' b, b < p →
        (p:ℤ)^(s+1) ∣ (((p*M' + (p*q'+b)).choose (p*q'+b) : ℤ)^3 - ((M'+q').choose q' : ℤ)^3) := by
      intro q' b hb
      have hgl := gen_lucas p (s+1) M' q' b hp (by omega) (by simpa using hM') hb
      -- turn ZMod equality into Nat.ModEq then ℤ dvd
      have hmod : (p*M' + p*q' + b).choose (p*q'+b) ≡ (M'+q').choose q' [MOD p^(s+1)] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mp hgl
      rw [show p*M'+(p*q'+b) = p*M'+p*q'+b from by ring]
      have hz : (p:ℤ)^(s+1) ∣ (((p*M' + p*q'+b).choose (p*q'+b) : ℤ) - ((M'+q').choose q' : ℤ)) := by
        have hd := Nat.modEq_iff_dvd.mp hmod
        push_cast at hd
        exact dvd_sub_comm.mp hd
      obtain ⟨c, hc⟩ := hz
      refine ⟨c * (((p*M'+p*q'+b).choose (p*q'+b):ℤ)^2 + ((p*M'+p*q'+b).choose (p*q'+b):ℤ)*((M'+q').choose q':ℤ) + ((M'+q').choose q':ℤ)^2), ?_⟩
      have hfac : (((p*M'+p*q'+b).choose (p*q'+b):ℤ)^3 - ((M'+q').choose q':ℤ)^3)
          = (((p*M'+p*q'+b).choose (p*q'+b):ℤ) - ((M'+q').choose q':ℤ)) * (((p*M'+p*q'+b).choose (p*q'+b):ℤ)^2 + ((p*M'+p*q'+b).choose (p*q'+b):ℤ)*((M'+q').choose q':ℤ) + ((M'+q').choose q':ℤ)^2) := by ring
      rw [hfac, hc]; ring
    -- split the double sum into FIRST + CORRECTION
    have key : (∑ q' ∈ range M', ∑ b ∈ range p,
          ((p*M'+(p*q'+b)).choose (p*q'+b):ℤ)^3 * ((p*q'+b:ℕ):ℤ)^j)
        = (∑ q' ∈ range M', ∑ b ∈ range p, ((M'+q').choose q':ℤ)^3 * ((p*q'+b:ℕ):ℤ)^j)
          + (∑ q' ∈ range M', ∑ b ∈ range p,
              (((p*M'+(p*q'+b)).choose (p*q'+b):ℤ)^3 - ((M'+q').choose q':ℤ)^3) * ((p*q'+b:ℕ):ℤ)^j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro q' _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro b _; ring
    rw [key]
    apply dvd_add
    · -- FIRST
      have hexp : (∑ q' ∈ range M', ∑ b ∈ range p, ((M'+q').choose q':ℤ)^3 * ((p*q'+b:ℕ):ℤ)^j)
          = ∑ i ∈ range (j+1),
              ((j.choose i:ℤ)*(p:ℤ)^i*(∑ b ∈ range p,(b:ℤ)^(j-i)))
                *(∑ q' ∈ range M',((M'+q').choose q':ℤ)^3*(q':ℤ)^i) := by
        have expand : ∀ q' b : ℕ, ((M'+q').choose q':ℤ)^3 * ((p*q'+b:ℕ):ℤ)^j
            = ∑ i ∈ range (j+1),
                ((M'+q').choose q':ℤ)^3 * ((q':ℤ)*p)^i * (b:ℤ)^(j-i) * (j.choose i) := by
          intro q' b
          rw [show ((p*q'+b:ℕ):ℤ) = (q':ℤ)*p + (b:ℤ) from by push_cast; ring, add_pow, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _; ring
        simp_rw [expand]
        rw [Finset.sum_comm]
        conv_lhs => enter [2, b]; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro q' _
        ring
      rw [hexp]
      apply Finset.dvd_sum; intro i hi
      simp only [Finset.mem_range] at hi
      have hS := ih M' hM' i
      by_cases hj : j = 0
      · have hi0 : i = 0 := by omega
        subst hj; subst hi0
        simp only [Nat.sub_zero, Nat.choose_self, Nat.cast_one, pow_zero, one_mul, mul_one]
        have hP : (∑ x ∈ range p, (1:ℤ)) = (p:ℤ) := by simp
        rw [hP]
        have hS' : (p:ℤ)^s ∣ ∑ x ∈ range M', ((M'+x).choose x:ℤ)^3 := by simpa using hS
        obtain ⟨k, hk⟩ := hS'
        rw [hk]
        exact ⟨k, by rw [pow_succ]; ring⟩
      · -- j ≥ 1
        have hdvd1 : (p:ℤ)^(s+1-j) ∣ (p:ℤ)^i * (∑ q' ∈ range M',((M'+q').choose q':ℤ)^3*(q':ℤ)^i) := by
          obtain ⟨k, hk⟩ := hS
          rw [hk, ← mul_assoc]
          refine dvd_mul_of_dvd_left ?_ k
          rw [← pow_add]; exact pow_dvd_pow _ (by omega)
        have hfac : ((j.choose i:ℤ)*(p:ℤ)^i*(∑ b ∈ range p,(b:ℤ)^(j-i)))
              *(∑ q' ∈ range M',((M'+q').choose q':ℤ)^3*(q':ℤ)^i)
            = ((j.choose i:ℤ)*(∑ b ∈ range p,(b:ℤ)^(j-i)))
              * ((p:ℤ)^i*(∑ q' ∈ range M',((M'+q').choose q':ℤ)^3*(q':ℤ)^i)) := by ring
        rw [hfac]
        exact Dvd.dvd.mul_left hdvd1 _
    · -- CORRECTION
      apply Finset.dvd_sum; intro q' _
      apply Finset.dvd_sum; intro b hb
      simp only [Finset.mem_range] at hb
      exact dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow (p:ℤ) (Nat.sub_le _ _)) (hcorr q' b hb)) _

-- ============================================================================
-- p-adic toolkit (ℚ_[p]) for harmonic-sum valuations
-- ============================================================================

/-- `PD p t x` means "p^t divides x", encoded p-adically as `‖x‖ ≤ p^(-t)`. -/
def PD (p : ℕ) [Fact p.Prime] (t : ℤ) (x : ℚ_[p]) : Prop := ‖x‖ ≤ (p : ℝ) ^ (-t)

section Ptoolkit
variable {p : ℕ} [hp : Fact p.Prime]

lemma pR1 : (1:ℝ) ≤ (p:ℝ) := by
  have := hp.out.two_le; exact_mod_cast le_trans (by norm_num) this

lemma pR_ne : (p:ℝ) ≠ 0 := by
  have := hp.out.pos; positivity

lemma zpow_nonneg' (t : ℤ) : (0:ℝ) ≤ (p:ℝ) ^ (-t) := by
  have := hp.out.pos; positivity

lemma PD_mul {s t : ℤ} {a b : ℚ_[p]} (ha : PD p s a) (hb : PD p t b) :
    PD p (s + t) (a * b) := by
  unfold PD at *
  rw [norm_mul, neg_add, zpow_add₀ pR_ne]
  exact mul_le_mul ha hb (norm_nonneg _) (zpow_nonneg' _)

lemma PD_mul_right {t : ℤ} {a b : ℚ_[p]} (ha : PD p t a) (hb : ‖b‖ ≤ 1) :
    PD p t (a * b) := by
  unfold PD at *
  rw [norm_mul]
  calc ‖a‖ * ‖b‖ ≤ (p:ℝ)^(-t) * 1 := mul_le_mul ha hb (norm_nonneg _) (zpow_nonneg' _)
    _ = (p:ℝ)^(-t) := by ring

lemma PD_mul_left {t : ℤ} {a b : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hb : PD p t b) :
    PD p t (a * b) := by
  rw [mul_comm]; exact PD_mul_right hb ha

lemma PD_sum {t : ℤ} {ι : Type*} (s : Finset ι) (f : ι → ℚ_[p])
    (h : ∀ i ∈ s, PD p t (f i)) : PD p t (∑ i ∈ s, f i) := by
  unfold PD at *
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (zpow_nonneg' _) h

lemma PD_mono {s t : ℤ} {x : ℚ_[p]} (hst : s ≤ t) (h : PD p t x) : PD p s x := by
  unfold PD at *
  exact le_trans h (zpow_le_zpow_right₀ (by exact_mod_cast pR1) (by omega))

lemma PD_p : PD p 1 (p : ℚ_[p]) := by
  unfold PD; rw [Padic.norm_p]; simp

lemma norm_natCast_coprime {i : ℕ} (hi : ¬ p ∣ i) : ‖(i : ℚ_[p])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]; exact (hp.out.coprime_iff_not_dvd).2 hi

lemma norm_inv_natCast_coprime {i : ℕ} (hi : ¬ p ∣ i) : ‖(i : ℚ_[p])⁻¹‖ = 1 := by
  rw [norm_inv, norm_natCast_coprime hi]; norm_num

end Ptoolkit

/-- Bridge: a p-adic sum of `k`-th powers of inverses of units has `‖·‖ ≤ p^(-1)`
whenever the corresponding `ZMod p` sum vanishes. -/
lemma zmod_bridge (p k : ℕ) [hp : Fact p.Prime] (s : Finset ℕ)
    (hs : ∀ i ∈ s, ¬ p ∣ i)
    (hz : (∑ i ∈ s, ((i : ZMod p)⁻¹) ^ k) = 0) :
    PD p 1 (∑ i ∈ s, ((i : ℚ_[p])⁻¹) ^ k) := by
  set X : ℚ_[p] := ∑ i ∈ s, ((i : ℚ_[p])⁻¹) ^ k with hX
  set B : ℕ := ∏ i ∈ s, i with hB
  have hcop : Nat.Coprime p B :=
    Nat.Coprime.prod_right (fun i hi => (hp.out.coprime_iff_not_dvd).2 (hs i hi))
  have hBcop : ¬ p ∣ B := (hp.out.coprime_iff_not_dvd).1 hcop
  -- integer A
  set A : ℕ := ∑ i ∈ s, (B / i) ^ k with hA
  -- divisibility i ∣ B
  have hdvd : ∀ i ∈ s, i ∣ B := fun i hi => Finset.dvd_prod_of_mem _ hi
  -- key identity: (B:ℚ_[p])^k * X = A
  have hkey : (B : ℚ_[p]) ^ k * X = (A : ℚ_[p]) := by
    rw [hX, hA, Finset.mul_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    have hiB : i * (B / i) = B := Nat.mul_div_cancel' (hdvd i hi)
    have hine : (i : ℚ_[p]) ≠ 0 := by
      have := norm_natCast_coprime (p := p) (hs i hi)
      intro h; rw [h] at this; simp at this
    have hcast : (B : ℚ_[p]) = (i : ℚ_[p]) * ((B / i : ℕ) : ℚ_[p]) := by
      rw [← Nat.cast_mul, hiB]
    rw [hcast, mul_pow, mul_right_comm, ← mul_pow, mul_inv_cancel₀ hine, one_pow, one_mul]
  -- norm of B^k is 1
  have hBnorm : ‖(B : ℚ_[p]) ^ k‖ = 1 := by
    rw [norm_pow, norm_natCast_coprime (p := p) hBcop, one_pow]
  have hXnorm : ‖X‖ = ‖(A : ℚ_[p])‖ := by
    have : ‖(B : ℚ_[p]) ^ k * X‖ = ‖(A : ℚ_[p])‖ := by rw [hkey]
    rwa [norm_mul, hBnorm, one_mul] at this
  -- p ∣ A via ZMod
  have hpA : p ∣ A := by
    rw [← ZMod.natCast_eq_zero_iff]
    rw [hA]
    push_cast
    have : (∑ i ∈ s, ((B / i : ℕ) : ZMod p) ^ k) = (B : ZMod p) ^ k * (∑ i ∈ s, ((i : ZMod p)⁻¹) ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hiu : IsUnit (i : ZMod p) := by
        rw [ZMod.isUnit_iff_coprime]
        exact (Nat.coprime_comm.mp ((hp.out.coprime_iff_not_dvd).2 (hs i hi)))
      have hiB : i * (B / i) = B := Nat.mul_div_cancel' (hdvd i hi)
      have hcast : (B : ZMod p) = (i : ZMod p) * ((B / i : ℕ) : ZMod p) := by
        rw [← Nat.cast_mul, hiB]
      have : ((B / i : ℕ) : ZMod p) = (i : ZMod p)⁻¹ * (B : ZMod p) := by
        rw [hcast, ← mul_assoc, ZMod.inv_mul_of_unit _ hiu, one_mul]
      rw [this, mul_pow]; ring
    rw [this, hz, mul_zero]
  -- conclude
  unfold PD
  rw [hXnorm]
  have : ‖((A : ℤ) : ℚ_[p])‖ ≤ (p:ℝ)^(-(1:ℕ):ℤ) ↔ (p^1 : ℤ) ∣ (A : ℤ) :=
    Padic.norm_int_le_pow_iff_dvd (A : ℤ) 1
  have h2 : ‖((A : ℤ) : ℚ_[p])‖ ≤ (p:ℝ)^(-(1:ℤ)) := by
    rw [show (-(1:ℤ)) = (-(1:ℕ):ℤ) by norm_num]
    rw [this]
    simpa using (Int.natCast_dvd_natCast.mpr hpA)
  have h3 : ((A : ℤ) : ℚ_[p]) = (A : ℚ_[p]) := by push_cast; ring
  rwa [h3] at h2

/-- Harmonic-type sum `∑_{i<pn, p∤i} i^{-k}` in `ℚ_[p]`. -/
noncomputable def SH (p : ℕ) [Fact p.Prime] (k n : ℕ) : ℚ_[p] :=
  ∑ i ∈ (range (p * n)).filter (fun i => ¬ p ∣ i), ((i : ℚ_[p])⁻¹) ^ k

/-- The `ZMod p` reduction of `∑_{i<pn, p∤i} i^{-2}` vanishes (base Wolstenholme). -/
lemma zmod_S2_zero (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) (n : ℕ) :
    (∑ i ∈ (range (p * n)).filter (fun i => ¬ p ∣ i), ((i : ZMod p)⁻¹) ^ 2) = 0 := by
  rw [Finset.sum_filter]
  rw [sum_range_block n p (fun i => if ¬ p ∣ i then ((i : ZMod p)⁻¹) ^ 2 else 0)]
  have hpp : 0 < p := hp.out.pos
  have : ∀ t ∈ range n,
      (∑ b ∈ range p, (if ¬ p ∣ (p*t+b) then (((p*t+b : ℕ) : ZMod p)⁻¹) ^ 2 else 0))
        = ∑ c ∈ Icc 1 (p-1), (((c : ℕ) : ZMod p)⁻¹) ^ 2 := by
    intro t _
    -- reduce range p to Icc 1 (p-1); for b, condition ⟺ b≠0
    rw [sum_range_eq_Icc p (by omega) _ (by simp)]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [Finset.mem_Icc] at hb
    have hb0 : ¬ p ∣ b := by intro h; have := Nat.le_of_dvd (by omega) h; omega
    have hpb : ¬ p ∣ (p*t+b) := by
      rw [Nat.dvd_add_right ⟨t, rfl⟩]; exact hb0
    rw [if_pos hpb]
    congr 2
    have : ((p*t+b : ℕ) : ZMod p) = (b : ZMod p) := by
      push_cast; simp [ZMod.natCast_self]
    rw [this]
  rw [Finset.sum_congr rfl this]
  rw [Finset.sum_const, inv_sq_sum p hp5, smul_zero]

/-- Base case of higher Wolstenholme for `S_2`: `p ∣ SH p 2 n` for all `n`. -/
lemma S2_base (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) (n : ℕ) :
    PD p 1 (SH p 2 n) := by
  rw [SH]
  apply zmod_bridge p 2
  · intro i hi; simp only [Finset.mem_filter] at hi; exact hi.2
  · exact zmod_S2_zero p hp5 n

/-- General block decomposition: split `range (A*C)` into `A` blocks of size `C`. -/
lemma gen_block {R : Type*} [AddCommMonoid R] (A C : ℕ) (f : ℕ → R) :
    ∑ i ∈ range (A*C), f i = ∑ a ∈ range A, ∑ c ∈ range C, f (C*a + c) := by
  induction A with
  | zero => simp
  | succ n ih =>
    rw [show (n+1)*C = n*C + C from by ring, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    ring

/-- Second-order remainder identity for inverse squares. -/
lemma rem_identity2 {p : ℕ} [Fact p.Prime] (a x : ℚ_[p]) (ha : a ≠ 0) (hax : a + x ≠ 0) :
    (a+x)⁻¹^2 - a⁻¹^2 = -(2*x)*a⁻¹^3 + (a+x)⁻¹^2 * a⁻¹^3 * x^2 * (3*a + 2*x) := by
  have h1 : (a+x) ≠ 0 := hax
  field_simp
  ring

lemma PD_natCast_of_dvd {p : ℕ} [Fact p.Prime] (e n : ℕ) (h : p^e ∣ n) : PD p e (n : ℚ_[p]) := by
  unfold PD
  rw [show ((n:ℚ_[p])) = (((n:ℤ)):ℚ_[p]) by push_cast; ring]
  rw [show (-(e:ℤ)) = (-(e:ℕ):ℤ) by norm_num]
  rw [Padic.norm_int_le_pow_iff_dvd]
  exact_mod_cast h

lemma PD_norm_le_one {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (h : ‖x‖ ≤ 1) : PD p 0 x := by
  unfold PD; simpa using h

lemma norm_le_one_of_PD {p : ℕ} [Fact p.Prime] {t : ℤ} {x : ℚ_[p]} (ht : 0 ≤ t) (h : PD p t x) : ‖x‖ ≤ 1 := by
  have := PD_mono (p := p) (x := x) ht h
  unfold PD at this; simpa using this

lemma norm_natCast_le_one (p : ℕ) [Fact p.Prime] (n : ℕ) : ‖(n : ℚ_[p])‖ ≤ 1 := by
  rw [show ((n:ℚ_[p])) = (((n:ℤ)):ℚ_[p]) by push_cast; ring]
  exact Padic.norm_int_le_one _

lemma SH_norm_le_one (p : ℕ) [hp : Fact p.Prime] (k n : ℕ) : ‖SH p k n‖ ≤ 1 := by
  rw [SH]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro i hi
  simp only [Finset.mem_filter] at hi
  rw [norm_pow]
  have := norm_inv_natCast_coprime (p := p) hi.2
  rw [this]; simp

lemma PD_add {p : ℕ} [Fact p.Prime] {t : ℤ} {a b : ℚ_[p]} (ha : PD p t a) (hb : PD p t b) :
    PD p t (a + b) := by
  unfold PD at *
  exact le_trans (IsUltrametricDist.norm_add_le_max a b) (max_le ha hb)

lemma PD_neg {p : ℕ} [Fact p.Prime] {t : ℤ} {a : ℚ_[p]} (ha : PD p t a) : PD p t (-a) := by
  unfold PD at *; rwa [norm_neg]

/-- Inductive step of higher Wolstenholme for `S_2`. -/
lemma S2_step (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) (e n' : ℕ) (hn' : 1 ≤ n')
    (hdvd : p^e ∣ n') (ih : PD p (1+e) (SH p 2 n')) :
    PD p (2+e) (SH p 2 (p*n')) := by
  set Hs' := (range (p*n')).filter (fun i => ¬ p ∣ i) with hHs'
  have hpe : ((1:ℤ)+e) = ((1+e : ℕ):ℤ) := by push_cast; ring
  -- key valuation facts
  have hval_pna : ∀ a : ℕ, PD p (1+e) ((p*n'*a : ℕ) : ℚ_[p]) := by
    intro a; apply PD_natCast_of_dvd
    rw [pow_add, pow_one]; exact Dvd.dvd.mul_right (mul_dvd_mul_left p hdvd) a
  -- membership fact: c ∈ Hs' → p ∤ c
  have hcp : ∀ c ∈ Hs', ¬ p ∣ c := by intro c hc; rw [hHs', Finset.mem_filter] at hc; exact hc.2
  -- SH p 2 n' as sum over Hs'
  have hSHn' : SH p 2 n' = ∑ c ∈ Hs', ((c:ℚ_[p])⁻¹)^2 := by rw [SH, hHs']
  -- reindex SH p 2 (p*n')
  have hexp : SH p 2 (p*n') = ∑ a ∈ range p, ∑ c ∈ Hs', ((↑(p*n'*a+c):ℚ_[p])⁻¹)^2 := by
    rw [SH, Finset.sum_filter, gen_block p (p*n')]
    apply Finset.sum_congr rfl
    intro a _
    rw [hHs', Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : p ∣ c
    · have hd : p ∣ (p*n'*a+c) := (Nat.dvd_add_right ⟨n'*a, by ring⟩).mpr hc
      rw [if_neg (not_not.mpr hd), if_neg (not_not.mpr hc)]
    · have hd : ¬ p ∣ (p*n'*a+c) := fun h => hc ((Nat.dvd_add_right ⟨n'*a, by ring⟩).mp h)
      rw [if_pos hd, if_pos hc]
  -- split each summand via the remainder identity
  have hsplit : SH p 2 (p*n')
      = ((p:ℚ_[p]) * SH p 2 n')
        + (∑ a ∈ range p, ∑ c ∈ Hs', (-(2*(↑(p*n'*a):ℚ_[p]))*((c:ℚ_[p])⁻¹)^3))
        + (∑ a ∈ range p, ∑ c ∈ Hs',
            (((c:ℚ_[p])+(↑(p*n'*a)))⁻¹^2 * (c:ℚ_[p])⁻¹^3 * (↑(p*n'*a):ℚ_[p])^2
              * (3*(c:ℚ_[p]) + 2*(↑(p*n'*a))))) := by
    rw [hexp]
    rw [hSHn']
    -- rewrite ↑p * Σ = Σ_a Σ_c (as constant sum)
    have hconst : (p:ℚ_[p]) * (∑ c ∈ Hs', ((c:ℚ_[p])⁻¹)^2)
        = ∑ a ∈ range p, ∑ c ∈ Hs', ((c:ℚ_[p])⁻¹)^2 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hconst]
    -- now combine three double-sums
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    have hcne : (c:ℚ_[p]) ≠ 0 := by
      have := norm_natCast_coprime (p := p) (hcp c hc); intro h; rw [h] at this; simp at this
    have hsum : ((↑(p*n'*a+c):ℚ_[p])) = (c:ℚ_[p]) + (↑(p*n'*a):ℚ_[p]) := by push_cast; ring
    have hcxne : (c:ℚ_[p]) + (↑(p*n'*a):ℚ_[p]) ≠ 0 := by
      rw [← hsum]
      have hd : ¬ p ∣ (p*n'*a+c) := fun h => (hcp c hc) ((Nat.dvd_add_right ⟨n'*a, by ring⟩).mp h)
      have := norm_natCast_coprime (p := p) hd; intro h; rw [h] at this; simp at this
    rw [hsum]
    have := rem_identity2 (c:ℚ_[p]) (↑(p*n'*a):ℚ_[p]) hcne hcxne
    linear_combination this
  have hSH3 : SH p 3 n' = ∑ c ∈ Hs', ((c:ℚ_[p])⁻¹)^3 := by rw [SH, hHs']
  rw [hsplit]
  apply PD_add
  apply PD_add
  · -- ↑p * SH p 2 n'
    have := PD_mul (PD_p (p := p)) ih
    rwa [show (1:ℤ)+(1+(e:ℤ)) = 2+(e:ℤ) from by ring] at this
  · -- T1 : the -2x c^{-3} sum
    have hT1eq : (∑ a ∈ range p, ∑ c ∈ Hs', (-(2*(↑(p*n'*a):ℚ_[p]))*((c:ℚ_[p])⁻¹)^3))
        = (∑ a ∈ range p, (-(2*(↑(p*n'*a):ℚ_[p])))) * (∑ c ∈ Hs', ((c:ℚ_[p])⁻¹)^3) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
    rw [hT1eq]
    -- coefficient equals -↑(pn') * (2 * Σ_a ↑a)
    have hcoeff : (∑ a ∈ range p, (-(2*(↑(p*n'*a):ℚ_[p]))))
        = -((↑(p*n':ℕ):ℚ_[p]) * (2 * ∑ a ∈ range p, (a:ℚ_[p]))) := by
      have heq : -((↑(p*n':ℕ):ℚ_[p]) * (2 * ∑ a ∈ range p, (a:ℚ_[p])))
          = ∑ a ∈ range p, (-(2*(↑(p*n'*a):ℚ_[p]))) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro a _
        push_cast; ring
      rw [heq]
    rw [hcoeff]
    apply PD_mul_right _ (by rw [← hSH3]; exact SH_norm_le_one p 3 n')
    apply PD_neg
    have hgauss : (2 * ∑ a ∈ range p, (a:ℚ_[p])) = ((p*(p-1) : ℕ) : ℚ_[p]) := by
      have h2 : (∑ i ∈ range p, i) * 2 = p*(p-1) := Finset.sum_range_id_mul_two p
      rw [show (2 * ∑ a ∈ range p, (a:ℚ_[p])) = ((2 * ∑ a ∈ range p, a : ℕ):ℚ_[p]) from by push_cast; ring]
      rw [show 2 * ∑ a ∈ range p, a = (∑ i ∈ range p, i) * 2 from by ring, h2]
    rw [hgauss]
    have hp1 : PD p (1+e) ((↑(p*n':ℕ):ℚ_[p])) := by
      apply PD_natCast_of_dvd; rw [pow_add, pow_one]; exact mul_dvd_mul_left p hdvd
    have hp2 : PD p 1 (((p*(p-1) : ℕ) : ℚ_[p])) := by
      apply PD_natCast_of_dvd; simpa using Dvd.intro (p-1) rfl
    have := PD_mul hp1 hp2
    rwa [show (1:ℤ)+(e:ℤ)+1 = 2+(e:ℤ) from by ring] at this
  · -- REM : bounded by PD (2+2e), hence PD (2+e)
    apply PD_mono (by push_cast; omega : (2:ℤ)+(e:ℤ) ≤ 2+2*(e:ℤ))
    apply PD_sum
    intro a _
    apply PD_sum
    intro c hc
    -- term = A⁻¹² c⁻¹³ x² (3c+2x); bound ‖term‖ ≤ ‖x‖² ≤ p^{-(2+2e)}
    set x : ℚ_[p] := (↑(p*n'*a):ℚ_[p]) with hx
    have hcne : (c:ℚ_[p]) ≠ 0 := by
      have := norm_natCast_coprime (p := p) (hcp c hc); intro h; rw [h] at this; simp at this
    have hAne : ¬ p ∣ (p*n'*a+c) := fun h => (hcp c hc) ((Nat.dvd_add_right ⟨n'*a, by ring⟩).mp h)
    have hcxsum : (c:ℚ_[p]) + x = (↑(p*n'*a+c):ℚ_[p]) := by rw [hx]; push_cast; ring
    -- rewrite term as x^2 * BIG
    have hterm : ((c:ℚ_[p])+x)⁻¹^2 * (c:ℚ_[p])⁻¹^3 * x^2 * (3*(c:ℚ_[p]) + 2*x)
        = x^2 * (((c:ℚ_[p])+x)⁻¹^2 * (c:ℚ_[p])⁻¹^3 * (3*(c:ℚ_[p]) + 2*x)) := by ring
    rw [hterm]
    -- PD (2+2e) of x^2
    have hx2 : PD p (2+2*e) (x^2) := by
      rw [hx, ← Nat.cast_pow]
      apply PD_natCast_of_dvd
      have hd1 : p^(1+e) ∣ p*n'*a := by
        rw [pow_add, pow_one]; exact Dvd.dvd.mul_right (mul_dvd_mul_left p hdvd) a
      calc p^(2+2*e) = (p^(1+e))^2 := by rw [← pow_mul]; congr 1; ring
        _ ∣ (p*n'*a)^2 := pow_dvd_pow_of_dvd hd1 2
    -- BIG has norm ≤ 1
    apply PD_mul_right hx2
    rw [hcxsum]
    rw [norm_mul, norm_mul, norm_pow, norm_pow,
        norm_inv_natCast_coprime (p := p) hAne, norm_inv_natCast_coprime (p := p) (hcp c hc)]
    simp only [one_pow, one_mul]
    have h3c : 3*(c:ℚ_[p]) + 2*x = ((3*c + 2*(p*n'*a) : ℕ):ℚ_[p]) := by rw [hx]; push_cast; ring
    rw [h3c]
    exact norm_natCast_le_one _ _

/-- Higher Wolstenholme for `S_2`: `p^{1+e} ∣ SH p 2 n` whenever `p^e ∣ n`. -/
lemma S2_bound (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) :
    ∀ e n : ℕ, 1 ≤ n → p^e ∣ n → PD p (1+e) (SH p 2 n) := by
  intro e
  induction e with
  | zero => intro n hn _; simpa using S2_base p hp5 n
  | succ k ih =>
    intro n hn hdvd
    have hp1 : p ∣ n := dvd_trans (dvd_pow_self p (Nat.succ_ne_zero k)) hdvd
    obtain ⟨n', rfl⟩ := hp1
    have hn' : 1 ≤ n' := by
      rcases Nat.eq_zero_or_pos n' with h|h
      · simp [h] at hn
      · exact h
    have hdvd' : p^k ∣ n' := by
      have h2 : p^(k+1) ∣ p*n' := hdvd
      rw [pow_succ'] at h2
      exact (mul_dvd_mul_iff_left (a:=p) (by exact_mod_cast hp.out.pos.ne')).mp h2
    have key := S2_step p hp5 k n' hn' hdvd' (ih n' hn' hdvd')
    have heq : (1:ℤ) + ((k+1:ℕ):ℤ) = 2 + (k:ℤ) := by push_cast; ring
    rw [heq]; exact key

/-- Reflection `i ↦ pn - i` is a bijection of `{i < pn : p∤i}`. -/
lemma refl_sum (p n : ℕ) [Fact p.Prime] (g : ℕ → ℚ_[p]) :
    (∑ i ∈ (range (p*n)).filter (fun i => ¬ p ∣ i), g (p*n - i))
      = ∑ i ∈ (range (p*n)).filter (fun i => ¬ p ∣ i), g i := by
  apply Finset.sum_nbij' (fun i => p*n - i) (fun i => p*n - i)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at *
    have ha0 : ¬ p ∣ a := ha.2
    have hane : a ≠ 0 := by rintro rfl; exact ha0 (dvd_zero p)
    refine ⟨by omega, ?_⟩
    intro h
    have : p ∣ (p*n - (p*n - a)) := Nat.dvd_sub ⟨n, by ring⟩ h
    rw [show p*n - (p*n - a) = a from by omega] at this
    exact ha0 this
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at *
    have ha0 : ¬ p ∣ a := ha.2
    have hane : a ≠ 0 := by rintro rfl; exact ha0 (dvd_zero p)
    refine ⟨by omega, ?_⟩
    intro h
    have : p ∣ (p*n - (p*n - a)) := Nat.dvd_sub ⟨n, by ring⟩ h
    rw [show p*n - (p*n - a) = a from by omega] at this
    exact ha0 this
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    omega
  · intro a _; rfl

/-- Pairing identity used for the first harmonic sum. -/
lemma pair_identity2 {p : ℕ} [Fact p.Prime] (a b : ℚ_[p]) (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ + b⁻¹ = -((a+b)*a⁻¹^2) - (a+b)^2*a⁻¹^3 + (a+b)^3*a⁻¹^3*b⁻¹ := by
  field_simp
  ring

/-- Higher Wolstenholme for `S_1`: `p^{2+2e} ∣ SH p 1 n` whenever `p^e ∣ n`. -/
lemma S1_bound (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) (e n : ℕ) (hn : 1 ≤ n)
    (hdvd : p^e ∣ n) : PD p (2+2*e) (SH p 1 n) := by
  set Hs := (range (p*n)).filter (fun i => ¬ p ∣ i) with hHs
  set P : ℚ_[p] := ((p*n:ℕ):ℚ_[p]) with hP
  set W : ℚ_[p] := ∑ i ∈ Hs, ((i:ℚ_[p])⁻¹^3 * ((p*n-i:ℕ):ℚ_[p])⁻¹) with hW
  have hcp : ∀ c ∈ Hs, ¬ p ∣ c := by intro c hc; rw [hHs, Finset.mem_filter] at hc; exact hc.2
  have hSH2 : SH p 2 n = ∑ i ∈ Hs, ((i:ℚ_[p])⁻¹)^2 := by rw [SH, hHs]
  have hSH3 : SH p 3 n = ∑ i ∈ Hs, ((i:ℚ_[p])⁻¹)^3 := by rw [SH, hHs]
  -- 2·SH1 = Σ (i⁻¹ + (pn-i)⁻¹)
  have e1 : (2:ℚ_[p]) * SH p 1 n = ∑ i ∈ Hs, ((i:ℚ_[p])⁻¹ + ((p*n-i:ℕ):ℚ_[p])⁻¹) := by
    rw [Finset.sum_add_distrib, refl_sum p n (fun i => ((i:ℚ_[p]))⁻¹), SH, hHs]
    simp only [pow_one]
    rw [two_mul]
  -- main pairing equation
  have hmain : (2:ℚ_[p]) * SH p 1 n = -(P * SH p 2 n) - (P^2 * SH p 3 n) + (P^3 * W) := by
    rw [e1, hSH2, hSH3, hW]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hine : (i:ℚ_[p]) ≠ 0 := by
      have := norm_natCast_coprime (p := p) (hcp i hi); intro h; rw [h] at this; simp at this
    have hib : ¬ p ∣ (p*n - i) := by
      simp only [hHs, Finset.mem_filter, Finset.mem_range] at hi
      have hane : i ≠ 0 := by rintro rfl; exact hi.2 (dvd_zero p)
      intro h
      have : p ∣ (p*n - (p*n - i)) := Nat.dvd_sub ⟨n, by ring⟩ h
      rw [show p*n - (p*n - i) = i from by omega] at this
      exact hi.2 this
    have hbne : ((p*n-i:ℕ):ℚ_[p]) ≠ 0 := by
      have := norm_natCast_coprime (p := p) hib; intro h; rw [h] at this; simp at this
    have hab : (i:ℚ_[p]) + ((p*n-i:ℕ):ℚ_[p]) = P := by
      simp only [hHs, Finset.mem_filter, Finset.mem_range] at hi
      rw [hP, ← Nat.cast_add, show i + (p*n - i) = p*n from by omega]
    rw [pair_identity2 _ _ hine hbne, hab]
    ring
  -- norm bounds
  have hWnorm : ‖W‖ ≤ 1 := by
    rw [hW]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num)
    intro i hi
    have hib : ¬ p ∣ (p*n - i) := by
      simp only [hHs, Finset.mem_filter, Finset.mem_range] at hi
      have hane : i ≠ 0 := by rintro rfl; exact hi.2 (dvd_zero p)
      intro h
      have : p ∣ (p*n - (p*n - i)) := Nat.dvd_sub ⟨n, by ring⟩ h
      rw [show p*n - (p*n - i) = i from by omega] at this
      exact hi.2 this
    rw [norm_mul, norm_pow, norm_inv_natCast_coprime (p := p) (hcp i hi),
        norm_inv_natCast_coprime (p := p) hib]; simp
  have hP1 : PD p (1+e) P := by
    apply PD_natCast_of_dvd; rw [pow_add, pow_one]; exact mul_dvd_mul_left p hdvd
  have hP2 : PD p (2+2*e) (P^2) := by
    rw [hP, ← Nat.cast_pow]
    apply PD_natCast_of_dvd
    have hd1 : p^(1+e) ∣ p*n := by rw [pow_add, pow_one]; exact mul_dvd_mul_left p hdvd
    calc p^(2+2*e) = (p^(1+e))^2 := by rw [← pow_mul]; congr 1; ring
      _ ∣ (p*n)^2 := pow_dvd_pow_of_dvd hd1 2
  have hP3 : PD p (3+3*e) (P^3) := by
    rw [hP, ← Nat.cast_pow]
    apply PD_natCast_of_dvd
    have hd1 : p^(1+e) ∣ p*n := by rw [pow_add, pow_one]; exact mul_dvd_mul_left p hdvd
    calc p^(3+3*e) = (p^(1+e))^3 := by rw [← pow_mul]; congr 1; ring
      _ ∣ (p*n)^3 := pow_dvd_pow_of_dvd hd1 3
  -- bound the RHS
  have hrhs : PD p (2+2*e) ((2:ℚ_[p]) * SH p 1 n) := by
    rw [hmain, sub_eq_add_neg]
    apply PD_add
    apply PD_add
    · apply PD_neg
      have := PD_mul hP1 (S2_bound p hp5 e n hn hdvd)
      rwa [show (1:ℤ)+(e:ℤ)+(1+(e:ℤ)) = 2+2*(e:ℤ) from by ring] at this
    · apply PD_neg
      exact PD_mul_right hP2 (by rw [hSH3] at *; exact SH_norm_le_one p 3 n)
    · apply PD_mono (by push_cast; omega : (2:ℤ)+2*(e:ℤ) ≤ 3+3*(e:ℤ))
      exact PD_mul_right hP3 hWnorm
  -- conclude
  have h2u : ‖(2:ℚ_[p])‖ = 1 := by
    rw [show (2:ℚ_[p]) = ((2:ℕ):ℚ_[p]) by norm_num]
    exact norm_natCast_coprime (p := p) (by intro h; have := Nat.le_of_dvd (by norm_num) h; omega)
  unfold PD at hrhs ⊢
  rwa [norm_mul, h2u, one_mul] at hrhs

/-- Upward absorption: `m·C(m+j,j) = (m+j)·C(m+j-1,j)`. -/
lemma absorb_up (m j : ℕ) (hm : 1 ≤ m) : m * (m+j).choose j = (m+j) * (m+j-1).choose j := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m'+1 := ⟨m-1, by omega⟩
  have key := Nat.succ_mul_choose_eq (m'+j) m'
  have e1 : (m'+j).choose m' = (m'+j).choose j := Nat.choose_symm_add
  have e2 : (m'+j).succ.choose m'.succ = ((m'+1)+j).choose j := by
    rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, show m'+j+1 = (m'+1)+j from by ring]
    exact Nat.choose_symm_add
  rw [e1, e2, Nat.succ_eq_add_one, Nat.succ_eq_add_one, show m'+j+1 = (m'+1)+j from by ring] at key
  have e3 : (m'+1) + j - 1 = m'+j := by omega
  rw [e3]
  linear_combination -key

lemma prod_norm_le_one {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι) (w : ι → ℚ_[p])
    (hw : ∀ i ∈ s, ‖w i‖ ≤ 1) : ‖∏ i ∈ s, (1 + w i)‖ ≤ 1 := by
  rw [norm_prod]
  apply Finset.prod_le_one (fun i _ => norm_nonneg _)
  intro i hi
  exact le_trans (IsUltrametricDist.norm_add_le_max 1 (w i)) (max_le (by norm_num) (hw i hi))

lemma prod_taylor1 {p : ℕ} [Fact p.Prime] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w : ι → ℚ_[p]) (t : ℤ) (ht : 0 ≤ t) (hw : ∀ i ∈ s, PD p t (w i)) :
    PD p t (∏ i ∈ s, (1 + w i) - 1) := by
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty, sub_self]; unfold PD; rw [norm_zero]; positivity
  | insert a s' ha ih =>
    rw [Finset.prod_insert ha]
    have hnorm : ‖∏ i ∈ s', (1 + w i)‖ ≤ 1 :=
      prod_norm_le_one s' w (fun i hi => norm_le_one_of_PD ht (hw i (Finset.mem_insert_of_mem hi)))
    have key : (1 + w a) * ∏ i ∈ s', (1 + w i) - 1
        = (∏ i ∈ s', (1 + w i) - 1) + w a * (∏ i ∈ s', (1 + w i)) := by ring
    rw [key]
    apply PD_add
    · exact ih (fun i hi => hw i (Finset.mem_insert_of_mem hi))
    · exact PD_mul_right (hw a (Finset.mem_insert_self a s')) hnorm

lemma prod_taylor2 {p : ℕ} [Fact p.Prime] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w : ι → ℚ_[p]) (t : ℤ) (ht : 0 ≤ t) (hw : ∀ i ∈ s, PD p t (w i)) :
    PD p (2*t) (∏ i ∈ s, (1 + w i) - 1 - ∑ i ∈ s, w i) := by
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, sub_self]; unfold PD; rw [norm_zero]; positivity
  | insert a s' ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have key : (1 + w a) * ∏ i ∈ s', (1 + w i) - 1 - (w a + ∑ i ∈ s', w i)
        = (∏ i ∈ s', (1 + w i) - 1 - ∑ i ∈ s', w i) + w a * (∏ i ∈ s', (1 + w i) - 1) := by ring
    rw [key]
    apply PD_add
    · exact ih (fun i hi => hw i (Finset.mem_insert_of_mem hi))
    · have h1 : PD p t (∏ i ∈ s', (1 + w i) - 1) :=
        prod_taylor1 s' w t ht (fun i hi => hw i (Finset.mem_insert_of_mem hi))
      have := PD_mul (hw a (Finset.mem_insert_self a s')) h1
      rw [two_mul]; exact this

/-- The `(-1)`-shifted product identity: `C(pA-1,pj)·D = C(A-1,j)·N`. -/
lemma hID_lemma (p m j : ℕ) (hp : 0 < p) (hm : 1 ≤ m) :
    (p*(m+j)-1).choose (p*j) * (∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), i)
      = (m+j-1).choose j * (∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), (p*m+i)) := by
  set D := ∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), i with hD
  set N := ∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), (p*m+i) with hN
  -- prod_identity: C(p(m+j),pj)·D = C(m+j,j)·N
  have hpid := prod_identity p (m+j) j hp (by omega)
  rw [show (m+j) - j = m from by omega] at hpid
  -- hpid : C(p(m+j),pj)*D = C(m+j,j)*N
  -- (I): m·C(m+j,j)=(m+j)·C(m+j-1,j)
  have hI := absorb_up m j hm
  -- (II): m·C(p(m+j),pj)=(m+j)·C(p(m+j)-1,pj)
  have hII : m * (p*(m+j)).choose (p*j) = (m+j) * (p*(m+j)-1).choose (p*j) := by
    have h := absorb_up (p*m) (p*j) (Nat.mul_pos hp hm)
    rw [show p*m + p*j = p*(m+j) from by ring] at h
    -- h : (p*m)*C(p(m+j),pj) = (p*(m+j))*C(p(m+j)-1,pj)
    have h2 : p * (m * (p*(m+j)).choose (p*j)) = p * ((m+j) * (p*(m+j)-1).choose (p*j)) := by
      rw [← mul_assoc, ← mul_assoc]; rw [show p*(m+j) = p*m+p*j from by ring] at h ⊢
      · linarith [h]
    exact Nat.eq_of_mul_eq_mul_left hp h2
  -- (IV'): C(p(m+j),pj)·C(m+j-1,j) = C(m+j,j)·C(p(m+j)-1,pj)
  have hIV : (p*(m+j)).choose (p*j) * (m+j-1).choose j = (m+j).choose j * (p*(m+j)-1).choose (p*j) := by
    have e1 : m * ((p*(m+j)).choose (p*j) * (m+j-1).choose j)
        = (m+j) * ((p*(m+j)-1).choose (p*j) * (m+j-1).choose j) := by
      rw [← mul_assoc, hII, mul_assoc]
    have e2 : m * ((m+j).choose j * (p*(m+j)-1).choose (p*j))
        = (m+j) * ((m+j-1).choose j * (p*(m+j)-1).choose (p*j)) := by
      rw [← mul_assoc, hI, mul_assoc]
    have e3 : m * ((p*(m+j)).choose (p*j) * (m+j-1).choose j)
        = m * ((m+j).choose j * (p*(m+j)-1).choose (p*j)) := by
      rw [e1, e2]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) e3
  -- now: multiply hID goal by C(m+j,j) and cancel
  have hcancel : ((p*(m+j)-1).choose (p*j) * D) * (m+j).choose j
      = ((m+j-1).choose j * N) * (m+j).choose j := by
    calc ((p*(m+j)-1).choose (p*j) * D) * (m+j).choose j
        = ((m+j).choose j * (p*(m+j)-1).choose (p*j)) * D := by ring
      _ = ((p*(m+j)).choose (p*j) * (m+j-1).choose j) * D := by rw [← hIV]
      _ = (m+j-1).choose j * ((p*(m+j)).choose (p*j) * D) := by ring
      _ = (m+j-1).choose j * ((m+j).choose j * N) := by rw [hpid]
      _ = ((m+j-1).choose j * N) * (m+j).choose j := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.choose_pos (by omega)) hcancel

/-- Kummer-type divisibility for the central binomial factor. -/
lemma choose_kummer (p m j e : ℕ) (hp : p.Prime) (hm : 1 ≤ m) (hj : 1 ≤ j)
    (hje : p^e ∣ j) (hj0 : ¬ p ∣ (j / p^e)) (s : ℕ) (hs : p^s ∣ m) (hes : e ≤ s) :
    p^(s-e) ∣ (m+j-1).choose j := by
  have habs := absorb' m j hm hj
  set C := (m+j-1).choose j with hCdef
  have h1 : p^s ∣ j * C := by
    rw [habs]; exact Dvd.dvd.mul_right hs _
  set j0 := j / p^e with hj0def
  have hjeq : j = p^e * j0 := (Nat.mul_div_cancel' hje).symm
  rw [hjeq] at h1
  have hpe_pos : 0 < p^e := pow_pos hp.pos e
  have hsplit : p^s = p^e * p^(s-e) := by rw [← pow_add]; congr 1; omega
  rw [hsplit] at h1
  rw [mul_assoc] at h1
  have h2 : p^(s-e) ∣ j0 * C := (mul_dvd_mul_iff_left (show (p^e:ℕ)≠0 by positivity)).mp h1
  have hcop : (p^(s-e)).Coprime j0 := Nat.Coprime.pow_left _ ((hp.coprime_iff_not_dvd).mpr hj0)
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop h2

/-- The two descriptions of the "coprime residues below `p*j`" set agree. -/
lemma filter_set_eq (p j : ℕ) (hp : 1 ≤ p) :
    (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i) = (range (p*j)).filter (fun i => ¬ p ∣ i) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, hnd⟩
    refine ⟨?_, hnd⟩
    rcases lt_or_eq_of_le h2 with h | h
    · exact h
    · exfalso; apply hnd; rw [h]; exact ⟨j, rfl⟩
  · rintro ⟨h1, hnd⟩
    have hine : i ≠ 0 := by rintro rfl; exact hnd (dvd_zero p)
    exact ⟨⟨by omega, by omega⟩, hnd⟩

/-- Product reflection over the coprime-residue set. -/
lemma prod_refl (p j : ℕ) [Fact p.Prime] (g : ℕ → ℚ_[p]) :
    (∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), g (p*j - i))
      = ∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), g i := by
  apply Finset.prod_nbij' (fun i => p*j - i) (fun i => p*j - i)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at *
    obtain ⟨⟨h1, h2⟩, hnd⟩ := ha
    have hane : a ≠ 0 := by rintro rfl; exact hnd (dvd_zero p)
    have hlt : a < p*j := by rcases lt_or_eq_of_le h2 with h | h; exact h; exact absurd (h ▸ ⟨j, rfl⟩) hnd
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro h
    have : p ∣ (p*j - (p*j - a)) := Nat.dvd_sub ⟨j, by ring⟩ h
    rw [show p*j - (p*j - a) = a from by omega] at this
    exact hnd this
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at *
    obtain ⟨⟨h1, h2⟩, hnd⟩ := ha
    have hane : a ≠ 0 := by rintro rfl; exact hnd (dvd_zero p)
    have hlt : a < p*j := by rcases lt_or_eq_of_le h2 with h | h; exact h; exact absurd (h ▸ ⟨j, rfl⟩) hnd
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro h
    have : p ∣ (p*j - (p*j - a)) := Nat.dvd_sub ⟨j, by ring⟩ h
    rw [show p*j - (p*j - a) = a from by omega] at this
    exact hnd this
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨h1, h2⟩, _⟩ := ha; omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨h1, h2⟩, _⟩ := ha; omega
  · intro a _; rfl

/-- `SH p 1 j` written as a sum over the `Icc`-filter set. -/
lemma SH1_as_Icc (p j : ℕ) [Fact p.Prime] (hp : 1 ≤ p) :
    SH p 1 j = ∑ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), (i:ℚ_[p])⁻¹ := by
  rw [SH, filter_set_eq p j hp]
  apply Finset.sum_congr rfl
  intro i _; rw [pow_one]

/-- `R` in product-of-fractions form. -/
lemma aligned_R_eq (p m j : ℕ) [Fact p.Prime] :
    (∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), (1 + ((p*m:ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹))
      = ((∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), (p*m+i):ℕ):ℚ_[p])
        * (((∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), i:ℕ):ℚ_[p]))⁻¹ := by
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hcp : ¬ p ∣ i := (Finset.mem_filter.mp hi).2
  have hine : ((i:ℕ):ℚ_[p]) ≠ 0 := by
    have := norm_natCast_coprime (p:=p) hcp; intro h; rw [h] at this; simp at this
  rw [Nat.cast_add]
  field_simp
  ring

/-- Cast of `D = ∏ i` is a unit. -/
lemma aligned_D_ne (p j : ℕ) [Fact p.Prime] :
    ((∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), i : ℕ):ℚ_[p]) ≠ 0 := by
  have hnorm : ‖((∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), i : ℕ):ℚ_[p])‖ = 1 := by
    rw [Nat.cast_prod, norm_prod]
    apply Finset.prod_eq_one
    intro i hi
    exact norm_natCast_coprime (p:=p) (Finset.mem_filter.mp hi).2
  intro h; rw [h, norm_zero] at hnorm; norm_num at hnorm

/-- `C1 = C0 · R`. -/
lemma aligned_C1_eq (p m j : ℕ) [Fact p.Prime] (hp : 0 < p) (hm : 1 ≤ m) :
    ((p*(m+j)-1).choose (p*j) : ℚ_[p])
      = ((m+j-1).choose j : ℚ_[p]) *
        (∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), (1 + ((p*m:ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹)) := by
  have hID := hID_lemma p m j hp hm
  have hIDcast : ((p*(m+j)-1).choose (p*j) : ℚ_[p]) * ((∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), i : ℕ):ℚ_[p])
      = ((m+j-1).choose j : ℚ_[p]) * ((∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), (p*m+i) : ℕ):ℚ_[p]) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, hID]
  rw [aligned_R_eq]
  have hDne := aligned_D_ne p j
  rw [← mul_assoc, ← hIDcast, mul_assoc, mul_inv_cancel₀ hDne, mul_one]

/-- `R²` as a single product `∏(1 + z_i)`. -/
lemma aligned_Rsq (p m j : ℕ) [Fact p.Prime] (hp : 1 ≤ p) :
    (∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), (1 + ((p*m:ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹))^2
      = ∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i),
          (1 + ((p^2*m*(m+j):ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹*(((p*j-i:ℕ):ℚ_[p]))⁻¹) := by
  set Si := (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i) with hSi
  have hrefl : (∏ i ∈ Si, (1 + ((p*m:ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹))
      = ∏ i ∈ Si, (1 + ((p*m:ℕ):ℚ_[p])*(((p*j-i:ℕ):ℚ_[p]))⁻¹) :=
    (prod_refl p j (fun x => (1 + ((p*m:ℕ):ℚ_[p])*((x:ℕ):ℚ_[p])⁻¹))).symm
  rw [sq]
  nth_rewrite 2 [hrefl]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hmem := Finset.mem_filter.mp hi
  have hnd : ¬ p ∣ i := hmem.2
  have hle : i ≤ p*j := (Finset.mem_Icc.mp hmem.1).2
  have hine : ((i:ℕ):ℚ_[p]) ≠ 0 := by
    have := norm_natCast_coprime (p:=p) hnd; intro h; rw [h] at this; simp at this
  have hnd2 : ¬ p ∣ (p*j - i) := by
    have hane : i ≠ 0 := by rintro rfl; exact hnd (dvd_zero p)
    have hlt : i < p*j := by
      rcases lt_or_eq_of_le hle with h | h; exact h; exact absurd (h ▸ ⟨j, rfl⟩) hnd
    intro h
    have : p ∣ (p*j - (p*j - i)) := Nat.dvd_sub ⟨j, by ring⟩ h
    rw [show p*j - (p*j - i) = i from by omega] at this
    exact hnd this
  have hbne : ((p*j-i:ℕ):ℚ_[p]) ≠ 0 := by
    have := norm_natCast_coprime (p:=p) hnd2; intro h; rw [h] at this; simp at this
  have hcast : ((p*j-i:ℕ):ℚ_[p]) = ((p*j:ℕ):ℚ_[p]) - (i:ℚ_[p]) := by
    rw [Nat.cast_sub hle]
  rw [hcast] at hbne ⊢
  push_cast at hbne ⊢
  field_simp
  ring

/-- Sum reflection over the coprime-residue set. -/
lemma sum_refl (p j : ℕ) [Fact p.Prime] (g : ℕ → ℚ_[p]) :
    (∑ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), g (p*j - i))
      = ∑ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i), g i := by
  apply Finset.sum_nbij' (fun i => p*j - i) (fun i => p*j - i)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at *
    obtain ⟨⟨h1, h2⟩, hnd⟩ := ha
    have hane : a ≠ 0 := by rintro rfl; exact hnd (dvd_zero p)
    have hlt : a < p*j := by rcases lt_or_eq_of_le h2 with h | h; exact h; exact absurd (h ▸ ⟨j, rfl⟩) hnd
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro h
    have : p ∣ (p*j - (p*j - a)) := Nat.dvd_sub ⟨j, by ring⟩ h
    rw [show p*j - (p*j - a) = a from by omega] at this
    exact hnd this
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at *
    obtain ⟨⟨h1, h2⟩, hnd⟩ := ha
    have hane : a ≠ 0 := by rintro rfl; exact hnd (dvd_zero p)
    have hlt : a < p*j := by rcases lt_or_eq_of_le h2 with h | h; exact h; exact absurd (h ▸ ⟨j, rfl⟩) hnd
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro h
    have : p ∣ (p*j - (p*j - a)) := Nat.dvd_sub ⟨j, by ring⟩ h
    rw [show p*j - (p*j - a) = a from by omega] at this
    exact hnd this
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨h1, h2⟩, _⟩ := ha; omega
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨h1, h2⟩, _⟩ := ha; omega
  · intro a _; rfl

/-- The sum of the `z_i`. -/
lemma aligned_sumz (p m j : ℕ) [Fact p.Prime] (hp : 1 ≤ p) (hj : 1 ≤ j) :
    ∑ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i),
        ((p^2*m*(m+j):ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹*(((p*j-i:ℕ):ℚ_[p]))⁻¹
      = 2 * ((p*m*(m+j):ℕ):ℚ_[p]) * ((j:ℕ):ℚ_[p])⁻¹ * SH p 1 j := by
  set Si := (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i) with hSi
  have hpne : ((p:ℕ):ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hjne : ((j:ℕ):ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpjne : ((p*j:ℕ):ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by positivity)
  -- inner partial-fraction identity
  have hkey : ∑ i ∈ Si, ((i:ℚ_[p])⁻¹*((p*j-i:ℕ):ℚ_[p])⁻¹)
      = ((p*j:ℕ):ℚ_[p])⁻¹ * (2 * SH p 1 j) := by
    have step1 : ∑ i ∈ Si, ((i:ℚ_[p])⁻¹*((p*j-i:ℕ):ℚ_[p])⁻¹)
        = ∑ i ∈ Si, ((p*j:ℕ):ℚ_[p])⁻¹ * ((i:ℚ_[p])⁻¹ + ((p*j-i:ℕ):ℚ_[p])⁻¹) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hmem := Finset.mem_filter.mp hi
      have hnd : ¬ p ∣ i := hmem.2
      have hle : i ≤ p*j := (Finset.mem_Icc.mp hmem.1).2
      have hine : ((i:ℕ):ℚ_[p]) ≠ 0 := by
        have := norm_natCast_coprime (p:=p) hnd; intro h; rw [h] at this; simp at this
      have hnd2 : ¬ p ∣ (p*j - i) := by
        have hane : i ≠ 0 := by rintro rfl; exact hnd (dvd_zero p)
        have hlt : i < p*j := by
          rcases lt_or_eq_of_le hle with h | h; exact h; exact absurd (h ▸ ⟨j, rfl⟩) hnd
        intro h
        have : p ∣ (p*j - (p*j - i)) := Nat.dvd_sub ⟨j, by ring⟩ h
        rw [show p*j - (p*j - i) = i from by omega] at this
        exact hnd this
      have hbne : ((p*j-i:ℕ):ℚ_[p]) ≠ 0 := by
        have := norm_natCast_coprime (p:=p) hnd2; intro h; rw [h] at this; simp at this
      have hcast : ((p*j-i:ℕ):ℚ_[p]) = ((p*j:ℕ):ℚ_[p]) - (i:ℚ_[p]) := by rw [Nat.cast_sub hle]
      rw [hcast] at hbne ⊢
      field_simp
      ring
    rw [step1, ← Finset.mul_sum, Finset.sum_add_distrib,
        sum_refl p j (fun x => ((x:ℕ):ℚ_[p])⁻¹), ← SH1_as_Icc p j hp]
    ring
  -- factor out the constant
  rw [show (∑ i ∈ Si, ((p^2*m*(m+j):ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹*(((p*j-i:ℕ):ℚ_[p]))⁻¹)
      = ∑ i ∈ Si, ((p^2*m*(m+j):ℕ):ℚ_[p])*((i:ℚ_[p])⁻¹*((p*j-i:ℕ):ℚ_[p])⁻¹)
      from Finset.sum_congr rfl (fun i _ => by ring)]
  rw [← Finset.mul_sum, hkey]
  push_cast
  field_simp

/-- Multiply by something of norm at most `p^e`, dropping the exponent by `e`. -/
lemma PD_mul_inv {p : ℕ} [Fact p.Prime] {t e : ℤ} {x y : ℚ_[p]}
    (hx : PD p t x) (hy : ‖y‖ ≤ (p:ℝ)^e) : PD p (t-e) (x*y) := by
  have hpne : (p:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).pos.ne'
  unfold PD at hx ⊢
  rw [norm_mul]
  calc ‖x‖*‖y‖ ≤ (p:ℝ)^(-t)*(p:ℝ)^e :=
        mul_le_mul hx hy (norm_nonneg _) (by positivity)
    _ = (p:ℝ)^(-(t-e)) := by rw [← zpow_add₀ hpne]; congr 1; ring

/-- Exact norm of `(↑j)⁻¹`. -/
lemma norm_inv_natCast_eq (p j e : ℕ) [Fact p.Prime] (hj : 1 ≤ j)
    (he : p^e ∣ j) (hj0 : ¬ p ∣ (j / p^e)) :
    ‖((j:ℕ):ℚ_[p])⁻¹‖ = (p:ℝ)^(e:ℤ) := by
  set j0 := j / p^e with hj0def
  have hjeq : j = p^e * j0 := (Nat.mul_div_cancel' he).symm
  have hcast : ((j:ℕ):ℚ_[p]) = ((p:ℕ):ℚ_[p])^e * ((j0:ℕ):ℚ_[p]) := by
    rw [hjeq]; push_cast; ring
  rw [norm_inv, hcast, norm_mul, norm_pow, Padic.norm_p, norm_natCast_coprime (p:=p) hj0,
      mul_one, inv_pow, inv_inv, zpow_natCast]

/-- Key bound: `p^{s+2a+3} ∣ R² - 1`. -/
lemma aligned_Rsq_bound (p m j s a e : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hj : 1 ≤ j)
    (hs : p^s ∣ m) (hA : p^a ∣ (m+j)) (he : p^e ∣ j) (hj0 : ¬ p ∣ (j / p^e))
    (hae : a ≤ e) (has : a ≤ s) :
    PD p ((s:ℤ)+2*a+3)
      ((∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i),
          (1 + ((p*m:ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹))^2 - 1) := by
  have hp : 1 ≤ p := by omega
  set Si := (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i) with hSi
  -- z_i bound
  have hzpd : ∀ i ∈ Si, PD p ((2+s+a : ℕ):ℤ)
      (((p^2*m*(m+j):ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹*(((p*j-i:ℕ):ℚ_[p]))⁻¹) := by
    intro i hi
    have hmem := Finset.mem_filter.mp hi
    have hnd : ¬ p ∣ i := hmem.2
    have hle : i ≤ p*j := (Finset.mem_Icc.mp hmem.1).2
    have hnd2 : ¬ p ∣ (p*j - i) := by
      have hane : i ≠ 0 := by rintro rfl; exact hnd (dvd_zero p)
      have hlt : i < p*j := by
        rcases lt_or_eq_of_le hle with h | h; exact h; exact absurd (h ▸ ⟨j, rfl⟩) hnd
      intro h
      have : p ∣ (p*j - (p*j - i)) := Nat.dvd_sub ⟨j, by ring⟩ h
      rw [show p*j - (p*j - i) = i from by omega] at this
      exact hnd this
    have hK : p^(2+s+a) ∣ p^2*m*(m+j) := by
      rw [show 2+s+a = 2+(s+a) from by ring, pow_add, pow_add,
          show p^2*m*(m+j)=p^2*(m*(m+j)) from by ring]
      exact mul_dvd_mul (dvd_refl _) (mul_dvd_mul hs hA)
    apply PD_mul_right
    apply PD_mul_right
    · exact PD_natCast_of_dvd (2+s+a) _ hK
    · rw [norm_inv_natCast_coprime (p:=p) hnd]
    · rw [norm_inv_natCast_coprime (p:=p) hnd2]
  -- sum of z bound
  have hpm : PD p ((1+s+a:ℕ):ℤ) (((p*m*(m+j):ℕ):ℚ_[p])) := by
    apply PD_natCast_of_dvd
    rw [show 1+s+a = 1+(s+a) from by ring, pow_add, pow_add, pow_one,
        show p*m*(m+j)=p*(m*(m+j)) from by ring]
    exact mul_dvd_mul (dvd_refl _) (mul_dvd_mul hs hA)
  have hSH1 := S1_bound p hp5 e j hj he
  have hjinv : ‖((j:ℕ):ℚ_[p])⁻¹‖ ≤ (p:ℝ)^(e:ℤ) := le_of_eq (norm_inv_natCast_eq p j e hj he hj0)
  have hw1 : PD p ((2+e:ℕ):ℤ) (SH p 1 j * ((j:ℕ):ℚ_[p])⁻¹) := by
    have h := PD_mul_inv hSH1 hjinv
    have hexp : (2+2*(e:ℤ)) - (e:ℤ) = ((2+e:ℕ):ℤ) := by push_cast; ring
    rwa [hexp] at h
  have hsumz : PD p ((3+s+a+e:ℕ):ℤ)
      (∑ i ∈ Si, ((p^2*m*(m+j):ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹*(((p*j-i:ℕ):ℚ_[p]))⁻¹) := by
    rw [aligned_sumz p m j hp hj]
    have hrw : 2 * ((p*m*(m+j):ℕ):ℚ_[p]) * ((j:ℕ):ℚ_[p])⁻¹ * SH p 1 j
        = 2 * (((p*m*(m+j):ℕ):ℚ_[p]) * (SH p 1 j * ((j:ℕ):ℚ_[p])⁻¹)) := by ring
    rw [hrw]
    apply PD_mul_left (by
      rw [show (2:ℚ_[p]) = ((2:ℕ):ℚ_[p]) by norm_num]; exact norm_natCast_le_one p 2)
    have h := PD_mul hpm hw1
    have hexp : ((1+s+a:ℕ):ℤ) + ((2+e:ℕ):ℤ) = ((3+s+a+e:ℕ):ℤ) := by push_cast; ring
    rwa [hexp] at h
  -- combine
  rw [aligned_Rsq p m j hp]
  have hsplit : (∏ i ∈ Si, (1 + ((p^2*m*(m+j):ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹*(((p*j-i:ℕ):ℚ_[p]))⁻¹)) - 1
      = ((∏ i ∈ Si, (1 + ((p^2*m*(m+j):ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹*(((p*j-i:ℕ):ℚ_[p]))⁻¹)) - 1
          - (∑ i ∈ Si, ((p^2*m*(m+j):ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹*(((p*j-i:ℕ):ℚ_[p]))⁻¹))
        + (∑ i ∈ Si, ((p^2*m*(m+j):ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹*(((p*j-i:ℕ):ℚ_[p]))⁻¹) := by ring
  rw [hsplit]
  apply PD_add
  · apply PD_mono (show (s:ℤ)+2*a+3 ≤ 2*((2+s+a:ℕ):ℤ) by push_cast; omega)
    exact prod_taylor2 Si (fun i => ((p^2*m*(m+j):ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹*(((p*j-i:ℕ):ℚ_[p]))⁻¹)
      ((2+s+a:ℕ):ℤ) (by positivity) hzpd
  · apply PD_mono (show (s:ℤ)+2*a+3 ≤ ((3+s+a+e:ℕ):ℤ) by push_cast; omega)
    exact hsumz

/-- If `‖x-1‖ < 1` then `‖x³-1‖ = ‖x²-1‖` (for `p ≥ 5`). -/
lemma cube_norm_eq {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (x : ℚ_[p]) (h : ‖x-1‖ < 1) :
    ‖x^3 - 1‖ = ‖x^2 - 1‖ := by
  have h2 : ‖(2:ℚ_[p])‖ = 1 := by
    rw [show (2:ℚ_[p]) = ((2:ℕ):ℚ_[p]) by norm_num]
    exact norm_natCast_coprime (p:=p) (by intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega)
  have h3 : ‖(3:ℚ_[p])‖ = 1 := by
    rw [show (3:ℚ_[p]) = ((3:ℕ):ℚ_[p]) by norm_num]
    exact norm_natCast_coprime (p:=p) (by intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega)
  have hx1 : ‖x+1‖ = 1 := by
    have he : x + 1 = (x-1) + 2 := by ring
    rw [he, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h2]; exact ne_of_lt h), h2,
        max_eq_right (le_of_lt h)]
  have hx2 : ‖x+2‖ = 1 := by
    have he : x + 2 = (x-1) + 3 := by ring
    rw [he, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h3]; exact ne_of_lt h), h3,
        max_eq_right (le_of_lt h)]
  have hxx1 : ‖x^2+x+1‖ = 1 := by
    have he : x^2 + x + 1 = (x-1)*(x+2) + 3 := by ring
    have hlt : ‖(x-1)*(x+2)‖ < 1 := by rw [norm_mul, hx2, mul_one]; exact h
    rw [he, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h3]; exact ne_of_lt hlt), h3,
        max_eq_right (le_of_lt hlt)]
  have e3 : x^3 - 1 = (x-1)*(x^2+x+1) := by ring
  have e2 : x^2 - 1 = (x-1)*(x+1) := by ring
  rw [e3, e2, norm_mul, norm_mul, hxx1, hx1]

/-- Bound `p^{s+2a+3} ∣ R³ - 1`. -/
lemma aligned_R3_bound (p m j s a e : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hj : 1 ≤ j)
    (hs : p^s ∣ m) (hA : p^a ∣ (m+j)) (he : p^e ∣ j) (hj0 : ¬ p ∣ (j / p^e))
    (hae : a ≤ e) (has : a ≤ s) :
    PD p ((s:ℤ)+2*a+3)
      ((∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i),
          (1 + ((p*m:ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹))^3 - 1) := by
  have hp : 1 ≤ p := by omega
  set R := ∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i),
          (1 + ((p*m:ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹) with hRdef
  -- R - 1 bound
  have hR1 : PD p ((1+s:ℕ):ℤ) (R - 1) := by
    have hw : ∀ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i),
        PD p ((1+s:ℕ):ℤ) (((p*m:ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹) := by
      intro i hi
      have hnd : ¬ p ∣ i := (Finset.mem_filter.mp hi).2
      have hpm : PD p ((1+s:ℕ):ℤ) (((p*m:ℕ):ℚ_[p])) := by
        apply PD_natCast_of_dvd; rw [pow_add, pow_one]; exact mul_dvd_mul (dvd_refl p) hs
      exact PD_mul_right hpm (le_of_eq (norm_inv_natCast_coprime (p:=p) hnd))
    have := prod_taylor1 ((Icc 1 (p*j)).filter (fun i => ¬ p ∣ i))
      (fun i => ((p*m:ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹) ((1+s:ℕ):ℤ) (by positivity) hw
    rw [← hRdef] at this
    exact this
  -- ‖R-1‖ < 1
  have hlt : ‖R - 1‖ < 1 := by
    have hR1' : ‖R - 1‖ ≤ (p:ℝ)^(-((1+s:ℕ):ℤ)) := hR1
    refine lt_of_le_of_lt hR1' ?_
    have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
    calc (p:ℝ)^(-((1+s:ℕ):ℤ)) ≤ (p:ℝ)^(-(1:ℤ)) := by
          apply zpow_le_zpow_right₀ (le_of_lt hp1); push_cast; omega
      _ = ((p:ℝ))⁻¹ := by rw [zpow_neg, zpow_one]
      _ < 1 := by rw [inv_lt_one₀ (by linarith)]; exact hp1
  -- R² - 1 bound
  have hRsq := aligned_Rsq_bound p m j s a e hp5 hj hs hA he hj0 hae has
  rw [← hRdef] at hRsq
  unfold PD at hRsq ⊢
  rw [cube_norm_eq hp5 R hlt]
  exact hRsq

/-- The aligned term is divisible by `p^{4·v_p(m)+4}`. -/
lemma aligned_term (p m j : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hm : 1 ≤ m) (hj : 1 ≤ j) :
    PD p (4*(padicValNat p m)+4)
      (((p*(m+2*j):ℕ):ℚ_[p]) *
        (((p*(m+j)-1).choose (p*j):ℚ_[p])^3 - ((m+j-1).choose j:ℚ_[p])^3)) := by
  have hp : 1 ≤ p := by omega
  set s := padicValNat p m with hsdef
  set e := padicValNat p j with hedef
  set a := min s e with hadef
  have hjne : j ≠ 0 := by omega
  have hs : p^s ∣ m := pow_padicValNat_dvd
  have he : p^e ∣ j := pow_padicValNat_dvd
  have hj0 : ¬ p ∣ (j / p^e) := by
    intro hd
    obtain ⟨c, hc⟩ := hd
    have hjeq : j = p^e*(j/p^e) := (Nat.mul_div_cancel' he).symm
    have hpow : p^(padicValNat p j + 1) ∣ j := by
      rw [← hedef]; exact ⟨c, by rw [hjeq, hc, pow_succ]; ring⟩
    exact pow_succ_padicValNat_not_dvd hjne hpow
  have has : a ≤ s := min_le_left _ _
  have hae : a ≤ e := min_le_right _ _
  have hAm : p^a ∣ m := dvd_trans (pow_dvd_pow p has) hs
  have hAj : p^a ∣ j := dvd_trans (pow_dvd_pow p hae) he
  have hA : p^a ∣ (m+j) := dvd_add hAm hAj
  have hmij : p^a ∣ (m+2*j) := dvd_add hAm (hAj.mul_left 2)
  have hC0 : p^(s-a) ∣ (m+j-1).choose j := by
    by_cases hse : s ≤ e
    · rw [show s - a = 0 from by omega, pow_zero]; exact one_dvd _
    · rw [show a = e from by omega]
      exact choose_kummer p m j e Fact.out hm hj he hj0 s hs (by omega)
  have hPmij : PD p ((a:ℕ):ℤ) (((m+2*j:ℕ):ℚ_[p])) := PD_natCast_of_dvd a _ hmij
  have hPC0 : PD p ((s-a:ℕ):ℤ) (((m+j-1).choose j : ℚ_[p])) := PD_natCast_of_dvd (s-a) _ hC0
  have hR3 := aligned_R3_bound p m j s a e hp5 hj hs hA he hj0 hae has
  have hcast : ((p*(m+2*j):ℕ):ℚ_[p]) = (p:ℚ_[p])*((m+2*j:ℕ):ℚ_[p]) := by push_cast; ring
  rw [aligned_C1_eq p m j (by omega) hm, hcast]
  set Rexp := ∏ i ∈ (Icc 1 (p*j)).filter (fun i => ¬ p ∣ i),
          (1 + ((p*m:ℕ):ℚ_[p])*((i:ℕ):ℚ_[p])⁻¹) with hRe
  have hEq : (p:ℚ_[p])*((m+2*j:ℕ):ℚ_[p]) *
        ((((m+j-1).choose j:ℚ_[p]) * Rexp)^3 - ((m+j-1).choose j:ℚ_[p])^3)
      = (p:ℚ_[p]) * (((m+2*j:ℕ):ℚ_[p]) *
          ((((m+j-1).choose j:ℚ_[p])*((((m+j-1).choose j:ℚ_[p]))*(((m+j-1).choose j:ℚ_[p]))))
            * (Rexp^3 - 1))) := by ring
  rw [hEq]
  have hca : ((s-a:ℕ):ℤ) = (s:ℤ) - (a:ℤ) := by rw [Nat.cast_sub has]
  have hmul := PD_mul (PD_p (p:=p))
    (PD_mul hPmij (PD_mul (PD_mul hPC0 (PD_mul hPC0 hPC0)) hR3))
  apply PD_mono ?_ hmul
  rw [hca]
  push_cast
  omega

/-- `p ∣ ∑_{b<p} b` for odd primes. -/
lemma p_dvd_sum_range (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : (p:ℤ) ∣ ∑ b ∈ range p, (b:ℤ) := by
  have h := Finset.sum_range_id_mul_two p
  have hcast : (∑ b ∈ range p, (b:ℤ)) * 2 = (p:ℤ) * ((p:ℤ) - 1) := by
    have : ((∑ i ∈ range p, i) * 2 : ℤ) = ((p * (p-1) : ℕ) : ℤ) := by exact_mod_cast congrArg (Nat.cast) h
    push_cast at this ⊢
    rw [this]
    have hp1 : 1 ≤ p := hp.pos
    push_cast [Nat.cast_sub hp1]
    ring
  have hd2 : (p:ℤ) ∣ (∑ b ∈ range p, (b:ℤ)) * 2 := by rw [hcast]; exact ⟨(p:ℤ)-1, rfl⟩
  have hcop : IsCoprime (p:ℤ) 2 := by
    have : Nat.Coprime p 2 := by
      rw [Nat.coprime_primes hp Nat.prime_two]; exact hp2
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by exact_mod_cast this)
  exact hcop.dvd_of_dvd_mul_right hd2

-- ===== Strengthened master lemma: p^(s+1-ℓ) ∣ Σ C^3 q^ℓ for ℓ ≥ 1 =====
lemma L_sub_plus (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ s : ℕ, ∀ M : ℕ, p^s ∣ M → ∀ ℓ : ℕ, 1 ≤ ℓ →
      (p:ℤ)^(s + 1 - ℓ) ∣ ∑ q ∈ range M, ((M+q).choose q : ℤ)^3 * (q:ℤ)^ℓ := by
  intro s
  induction s with
  | zero => intro M _ ℓ hℓ; rw [show 0+1-ℓ = 0 from by omega, pow_zero]; exact one_dvd _
  | succ s ih =>
    intro M hM ℓ hℓ
    have hpM : p ∣ M := dvd_trans (dvd_pow_self p (Nat.succ_ne_zero s)) hM
    obtain ⟨M', rfl⟩ := hpM
    have hM' : p^s ∣ M' := by
      have : p^(s+1) ∣ p * M' := hM
      rw [pow_succ'] at this
      exact (mul_dvd_mul_iff_left (by exact_mod_cast hp.pos.ne')).mp this
    rw [sum_range_block]
    have hcorr : ∀ q' b, b < p →
        (p:ℤ)^(s+1) ∣ (((p*M' + (p*q'+b)).choose (p*q'+b) : ℤ)^3 - ((M'+q').choose q' : ℤ)^3) := by
      intro q' b hb
      have hgl := gen_lucas p (s+1) M' q' b hp (by omega) (by simpa using hM') hb
      have hmod : (p*M' + p*q' + b).choose (p*q'+b) ≡ (M'+q').choose q' [MOD p^(s+1)] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mp hgl
      rw [show p*M'+(p*q'+b) = p*M'+p*q'+b from by ring]
      have hz : (p:ℤ)^(s+1) ∣ (((p*M' + p*q'+b).choose (p*q'+b) : ℤ) - ((M'+q').choose q' : ℤ)) := by
        have hd := Nat.modEq_iff_dvd.mp hmod
        push_cast at hd
        exact dvd_sub_comm.mp hd
      obtain ⟨c, hc⟩ := hz
      refine ⟨c * (((p*M'+p*q'+b).choose (p*q'+b):ℤ)^2 + ((p*M'+p*q'+b).choose (p*q'+b):ℤ)*((M'+q').choose q':ℤ) + ((M'+q').choose q':ℤ)^2), ?_⟩
      have hfac : (((p*M'+p*q'+b).choose (p*q'+b):ℤ)^3 - ((M'+q').choose q':ℤ)^3)
          = (((p*M'+p*q'+b).choose (p*q'+b):ℤ) - ((M'+q').choose q':ℤ)) * (((p*M'+p*q'+b).choose (p*q'+b):ℤ)^2 + ((p*M'+p*q'+b).choose (p*q'+b):ℤ)*((M'+q').choose q':ℤ) + ((M'+q').choose q':ℤ)^2) := by ring
      rw [hfac, hc]; ring
    have key : (∑ q' ∈ range M', ∑ b ∈ range p,
          ((p*M'+(p*q'+b)).choose (p*q'+b):ℤ)^3 * ((p*q'+b:ℕ):ℤ)^ℓ)
        = (∑ q' ∈ range M', ∑ b ∈ range p, ((M'+q').choose q':ℤ)^3 * ((p*q'+b:ℕ):ℤ)^ℓ)
          + (∑ q' ∈ range M', ∑ b ∈ range p,
              (((p*M'+(p*q'+b)).choose (p*q'+b):ℤ)^3 - ((M'+q').choose q':ℤ)^3) * ((p*q'+b:ℕ):ℤ)^ℓ) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro q' _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro b _; ring
    rw [key]
    apply dvd_add
    · -- FIRST
      have hexp : (∑ q' ∈ range M', ∑ b ∈ range p, ((M'+q').choose q':ℤ)^3 * ((p*q'+b:ℕ):ℤ)^ℓ)
          = ∑ i ∈ range (ℓ+1),
              ((ℓ.choose i:ℤ)*(p:ℤ)^i*(∑ b ∈ range p,(b:ℤ)^(ℓ-i)))
                *(∑ q' ∈ range M',((M'+q').choose q':ℤ)^3*(q':ℤ)^i) := by
        have expand : ∀ q' b : ℕ, ((M'+q').choose q':ℤ)^3 * ((p*q'+b:ℕ):ℤ)^ℓ
            = ∑ i ∈ range (ℓ+1),
                ((M'+q').choose q':ℤ)^3 * ((q':ℤ)*p)^i * (b:ℤ)^(ℓ-i) * (ℓ.choose i) := by
          intro q' b
          rw [show ((p*q'+b:ℕ):ℤ) = (q':ℤ)*p + (b:ℤ) from by push_cast; ring, add_pow, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i _; ring
        simp_rw [expand]
        rw [Finset.sum_comm]
        conv_lhs => enter [2, b]; rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i _
        rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro q' _
        ring
      rw [hexp]
      apply Finset.dvd_sum; intro i hi
      simp only [Finset.mem_range] at hi
      by_cases hi0 : i = 0
      · subst hi0
        -- term: (ℓchoose 0 * p^0 * Σ_b b^ℓ)*(Σ_{q'} C^3 q'^0)
        simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, mul_one]
        have hLC : (p:ℤ)^s ∣ ∑ q' ∈ range M', ((M'+q').choose q':ℤ)^3 * (q':ℤ)^0 := L_sub p hp s M' hM' 0
        simp only [pow_zero, mul_one] at hLC
        by_cases hl1 : ℓ = 1
        · subst hl1
          simp only [Nat.sub_zero, pow_one]
          have hb : (p:ℤ) ∣ ∑ b ∈ range p, (b:ℤ) := p_dvd_sum_range p hp hp2
          obtain ⟨cb, hcb⟩ := hb
          obtain ⟨cq, hcq⟩ := hLC
          refine ⟨cb * cq, ?_⟩
          rw [hcb, hcq, show s+1+1-1 = s+1 from by omega, pow_succ]
          ring
        · -- ℓ ≥ 2 : s+2-ℓ ≤ s
          have hle : s+1+1-ℓ ≤ s := by omega
          exact dvd_mul_of_dvd_right (dvd_trans (pow_dvd_pow (p:ℤ) hle) hLC) _
      · -- i ≥ 1
        have hi1 : 1 ≤ i := by omega
        have hIH := ih M' hM' i hi1
        have hdvd1 : (p:ℤ)^(s+1+1-ℓ) ∣ (p:ℤ)^i * (∑ q' ∈ range M',((M'+q').choose q':ℤ)^3*(q':ℤ)^i) := by
          obtain ⟨k, hk⟩ := hIH
          rw [hk, ← mul_assoc]
          refine dvd_mul_of_dvd_left ?_ k
          rw [← pow_add]; exact pow_dvd_pow _ (by omega)
        have hfac : ((ℓ.choose i:ℤ)*(p:ℤ)^i*(∑ b ∈ range p,(b:ℤ)^(ℓ-i)))
              *(∑ q' ∈ range M',((M'+q').choose q':ℤ)^3*(q':ℤ)^i)
            = ((ℓ.choose i:ℤ)*(∑ b ∈ range p,(b:ℤ)^(ℓ-i)))
              * ((p:ℤ)^i*(∑ q' ∈ range M',((M'+q').choose q':ℤ)^3*(q':ℤ)^i)) := by ring
        rw [hfac]
        exact Dvd.dvd.mul_left hdvd1 _
    · -- CORRECTION
      apply Finset.dvd_sum; intro q' _
      apply Finset.dvd_sum; intro b hb
      simp only [Finset.mem_range] at hb
      exact dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow (p:ℤ) (by omega)) (hcorr q' b hb)) _

/-- Power sum of inverse powers over `Icc 1 (p-1)` vanishes mod `p` when `(p-1) ∤ m`. -/
lemma inv_pow_sum (p m : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hm : ¬ (p-1) ∣ m) :
    ∑ k ∈ Icc 1 (p-1), (((k:ZMod p))⁻¹)^m = 0 := by
  set j := (p-1) - (m % (p-1)) with hj
  have hpm : 0 < p - 1 := by omega
  have hmod : m % (p-1) ≠ 0 := fun h => hm (Nat.dvd_of_mod_eq_zero h)
  have hml : m % (p-1) < p-1 := Nat.mod_lt m hpm
  have hjlt : j < p - 1 := by omega
  have hj1 : 1 ≤ j := by omega
  have hb : ∑ x : ZMod p, x ^ j = 0 := by
    apply FiniteField.sum_pow_lt_card_sub_one
    rw [ZMod.card]; omega
  rw [zmod_sum_range] at hb
  rw [sum_range_eq_Icc p (by omega) _ (by simp [zero_pow (by omega : j ≠ 0)])] at hb
  rw [← hb]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_Icc] at hk
  have hne : ((k:ZMod p)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff k p]
    intro hdvd; have : p ≤ k := Nat.le_of_dvd (by omega) hdvd; omega
  have hfermat : ((k:ZMod p))^(p-1) = 1 := ZMod.pow_card_sub_one_eq_one hne
  have hjm : (p-1) ∣ (j + m) := by
    obtain ⟨Q, hQ⟩ : ∃ Q, m = (p-1)*Q + m%(p-1) := ⟨m/(p-1), (Nat.div_add_mod m (p-1)).symm⟩
    refine ⟨Q+1, ?_⟩
    rw [hj, Nat.mul_add, Nat.mul_one]; omega
  have h2 : ((k:ZMod p))^j * ((k:ZMod p))^m = 1 := by
    rw [← pow_add]
    obtain ⟨t, ht⟩ := hjm
    rw [ht, pow_mul, hfermat, one_pow]
  have h2' : ((k:ZMod p))^m * ((k:ZMod p))^j = 1 := by rw [mul_comm]; exact h2
  rw [inv_pow]
  exact (eq_inv_of_mul_eq_one_right h2').symm

/-- The power sum `∑_c (c⁻¹)^m` in `ℚ_[p]` is `p`-divisible when `(p-1) ∤ m`. -/
lemma Wsum_PD (p m : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hm : ¬ (p-1) ∣ m) :
    PD p 1 (∑ c ∈ Icc 1 (p-1), ((c:ℚ_[p])⁻¹)^m) := by
  apply zmod_bridge p m (Icc 1 (p-1))
  · intro c hc; simp only [Finset.mem_Icc] at hc
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega
  · exact inv_pow_sum p m hp5 hm

/-- The power sum has norm at most 1. -/
lemma Wsum_norm_le_one (p m : ℕ) [Fact p.Prime] :
    ‖∑ c ∈ Icc 1 (p-1), ((c:ℚ_[p])⁻¹)^m‖ ≤ 1 := by
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num)
  intro c hc
  simp only [Finset.mem_Icc] at hc
  rw [norm_pow, norm_inv_natCast_coprime (p:=p) (by intro hd; have := Nat.le_of_dvd (by omega) hd; omega)]
  simp

/-- `L_sub` transported to `ℚ_[p]`. -/
lemma L_sub_PD (p : ℕ) [Fact p.Prime] (hp : p.Prime) (s M : ℕ) (hM : p^s ∣ M) (ℓ : ℕ) :
    PD p ((s-ℓ:ℕ):ℤ) (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ) := by
  have hdvd := L_sub p hp s M hM ℓ
  have hnat : (p^(s-ℓ)) ∣ (∑ q ∈ range M, (M+q).choose q^3 * q^ℓ) := by
    rw [show (∑ q ∈ range M, ((M+q).choose q:ℤ)^3*(q:ℤ)^ℓ)
        = ((∑ q ∈ range M, (M+q).choose q^3 * q^ℓ : ℕ):ℤ) from by push_cast; ring] at hdvd
    exact_mod_cast hdvd
  have hPD := PD_natCast_of_dvd (s-ℓ) _ hnat
  rwa [show ((∑ q ∈ range M, (M+q).choose q^3 * q^ℓ : ℕ):ℚ_[p])
      = ∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3*(q:ℚ_[p])^ℓ from by push_cast; ring] at hPD

/-- `L_sub_plus` transported to `ℚ_[p]`. -/
lemma L_sub_plus_PD (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hp2 : p ≠ 2) (s M : ℕ) (hM : p^s ∣ M)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    PD p ((s+1-ℓ:ℕ):ℤ) (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ) := by
  have hdvd := L_sub_plus p hp hp2 s M hM ℓ hℓ
  have hnat : (p^(s+1-ℓ)) ∣ (∑ q ∈ range M, (M+q).choose q^3 * q^ℓ) := by
    rw [show (∑ q ∈ range M, ((M+q).choose q:ℤ)^3*(q:ℤ)^ℓ)
        = ((∑ q ∈ range M, (M+q).choose q^3 * q^ℓ : ℕ):ℤ) from by push_cast; ring] at hdvd
    exact_mod_cast hdvd
  have hPD := PD_natCast_of_dvd (s+1-ℓ) _ hnat
  rwa [show ((∑ q ∈ range M, (M+q).choose q^3 * q^ℓ : ℕ):ℚ_[p])
      = ∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3*(q:ℚ_[p])^ℓ from by push_cast; ring] at hPD

/-- Finite Taylor identity (polynomial form) for the second-order expansion. -/
lemma taylor_poly_id {R : Type*} [CommRing R] (A c : R) :
    ∀ s : ℕ, (c+A)^2 * (∑ ℓ ∈ range (s+1), ((ℓ+1 : ℕ):R) * (-A)^ℓ * c^(s-ℓ))
        + (-A)^(s+1) * (((s+2:ℕ):R)*c + ((s+1:ℕ):R)*A) = c^(s+2) := by
  intro s
  induction s with
  | zero =>
    rw [show (0:ℕ)+1 = 1 from rfl, Finset.sum_range_one]
    push_cast; ring
  | succ s ih =>
    have hfs : (∑ ℓ ∈ range (s+2), ((ℓ+1:ℕ):R)*(-A)^ℓ*c^(s+1-ℓ))
        = c * (∑ ℓ ∈ range (s+1), ((ℓ+1:ℕ):R)*(-A)^ℓ*c^(s-ℓ)) + ((s+2:ℕ):R)*(-A)^(s+1) := by
      rw [Finset.sum_range_succ, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro ℓ hℓ
        simp only [Finset.mem_range] at hℓ
        rw [show s+1-ℓ = (s-ℓ)+1 from by omega, pow_succ]
        ring
      · rw [show s+1-(s+1) = 0 from by omega, pow_zero]; ring
    rw [hfs]
    have key : (c+A)^2 * (∑ ℓ ∈ range (s+1), ((ℓ+1:ℕ):R)*(-A)^ℓ*c^(s-ℓ))
        = c^(s+2) - (-A)^(s+1) * (((s+2:ℕ):R)*c + ((s+1:ℕ):R)*A) := eq_sub_of_add_eq ih
    have hB2 : (-A)^(s+1+1) = (-A)^(s+1)*(-A) := by rw [pow_succ]
    have hcs : c^(s+1+2) = c*c^(s+2) := by rw [show s+1+2 = (s+2)+1 from by omega, pow_succ]; ring
    have expand : (c+A)^2*(c * (∑ ℓ ∈ range (s+1), ((ℓ+1:ℕ):R)*(-A)^ℓ*c^(s-ℓ)) + ((s+2:ℕ):R)*(-A)^(s+1))
        = c*((c+A)^2 * (∑ ℓ ∈ range (s+1), ((ℓ+1:ℕ):R)*(-A)^ℓ*c^(s-ℓ)))
          + (c+A)^2*(((s+2:ℕ):R)*(-A)^(s+1)) := by ring
    rw [expand, key, hB2, hcs]
    push_cast
    ring

/-- Helper: `γ^(s-ℓ) * (γ⁻¹)^(s+2) = (γ⁻¹)^(ℓ+2)` for `ℓ ≤ s`, `γ ≠ 0`. -/
lemma inv_pow_simp {p : ℕ} [Fact p.Prime] (γ : ℚ_[p]) (hγ : γ ≠ 0) (ℓ s : ℕ) (h : ℓ ≤ s) :
    γ^(s-ℓ) * (γ⁻¹)^(s+2) = (γ⁻¹)^(ℓ+2) := by
  have hsplit : (γ⁻¹)^(s+2) = (γ⁻¹)^(s-ℓ) * (γ⁻¹)^(ℓ+2) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hγ, one_pow, one_mul]

/-- Per-`(q,c)` finite Taylor expansion of `(pq+c)⁻²` in `ℚ_[p]`. -/
lemma pqc_expand (p s q c : ℕ) [Fact p.Prime] (hc : ¬ p ∣ c) (hpqc : ¬ p ∣ (p*q+c)) :
    (((p*q+c:ℕ):ℚ_[p])⁻¹)^2
      = (∑ ℓ ∈ range (s+1), ((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ*((p*q:ℕ):ℚ_[p])^ℓ*(((c:ℕ):ℚ_[p])⁻¹)^(ℓ+2))
        + (-((p*q:ℕ):ℚ_[p]))^(s+1)*(((s+2:ℕ):ℚ_[p])*((c:ℕ):ℚ_[p])+((s+1:ℕ):ℚ_[p])*((p*q:ℕ):ℚ_[p]))
            *(((c:ℕ):ℚ_[p])⁻¹)^(s+2)*((((p*q+c:ℕ):ℚ_[p])⁻¹))^2 := by
  have hγ : ((c:ℕ):ℚ_[p]) ≠ 0 := by
    intro h; have := norm_natCast_coprime (p:=p) hc; rw [h] at this; simp at this
  have hD : ((p*q+c:ℕ):ℚ_[p]) ≠ 0 := by
    intro h; have := norm_natCast_coprime (p:=p) hpqc; rw [h] at this; simp at this
  set A := ((p*q:ℕ):ℚ_[p]) with hA
  set γ := ((c:ℕ):ℚ_[p]) with hγd
  have hDeq : ((p*q+c:ℕ):ℚ_[p]) = γ + A := by rw [hA, hγd]; push_cast; ring
  set F := ∑ ℓ ∈ range (s+1), ((ℓ+1:ℕ):ℚ_[p])*(-A)^ℓ*γ^(s-ℓ) with hFdef
  set REM := (-A)^(s+1)*(((s+2:ℕ):ℚ_[p])*γ+((s+1:ℕ):ℚ_[p])*A) with hREM
  have htaylor : (γ+A)^2 * F + REM = γ^(s+2) := taylor_poly_id (R := ℚ_[p]) A γ s
  have hmain : (∑ ℓ ∈ range (s+1), ((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ*A^ℓ*(γ⁻¹)^(ℓ+2))
      = F * (γ⁻¹)^(s+2) := by
    rw [hFdef, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    simp only [Finset.mem_range] at hℓ
    have h1 : γ^(s-ℓ)*(γ⁻¹)^(s+2) = (γ⁻¹)^(ℓ+2) := inv_pow_simp γ hγ ℓ s (by omega)
    have h2 : (-A)^ℓ = (-1)^ℓ * A^ℓ := by rw [neg_pow]
    rw [h2]
    linear_combination (-(((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ*A^ℓ)) * h1
  rw [hDeq, hmain]
  have hDne : γ + A ≠ 0 := by rw [← hDeq]; exact hD
  have hF : F = (γ+A)⁻¹^2 * (γ^(s+2) - REM) := by
    have h1 : (γ+A)^2 * F = γ^(s+2) - REM := eq_sub_of_add_eq htaylor
    rw [← h1, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hDne, one_pow, one_mul]
  rw [hF]
  set Y := (γ⁻¹)^(s+2) with hYdef
  set G := γ^(s+2) with hGdef
  have hγγ : Y * G = 1 := by rw [hYdef, hGdef, ← mul_pow, inv_mul_cancel₀ hγ, one_pow]
  linear_combination (-(((γ+A)⁻¹)^2)) * hγγ

/-- Power bound for `PD`. -/
lemma PD_pow {p : ℕ} [Fact p.Prime] {t : ℤ} {x : ℚ_[p]} (h : PD p t x) (n : ℕ) :
    PD p (↑n * t) (x^n) := by
  unfold PD at *
  rw [norm_pow]
  have hnn : (0:ℝ) ≤ ‖x‖ := norm_nonneg _
  calc ‖x‖^n ≤ ((p:ℝ)^(-t))^n := by exact pow_le_pow_left₀ hnn h n
    _ = (p:ℝ)^(-(↑n * t)) := by
        rw [← zpow_natCast ((p:ℝ)^(-t)) n, ← zpow_mul]
        congr 1
        push_cast; ring

/-- The key `p`-adic bound `PD p (s+1) G` for the "generating" sum `G`. -/
lemma G_bound (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hp5 : 5 ≤ p) (s M : ℕ) (hM : p^s ∣ M) :
    PD p ((s:ℤ)+1)
      (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3
        * (∑ c ∈ Icc 1 (p-1), (((p*q+c:ℕ):ℚ_[p])⁻¹)^2)) := by
  -- Per-`q` Taylor expansion of the inner sum.
  have hInner : ∀ q : ℕ, (∑ c ∈ Icc 1 (p-1), (((p*q+c:ℕ):ℚ_[p])⁻¹)^2)
      = (∑ ℓ ∈ range (s+1), ((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ*((p*q:ℕ):ℚ_[p])^ℓ
          * (∑ c ∈ Icc 1 (p-1), ((c:ℚ_[p])⁻¹)^(ℓ+2)))
        + (∑ c ∈ Icc 1 (p-1), (-((p*q:ℕ):ℚ_[p]))^(s+1)
            *(((s+2:ℕ):ℚ_[p])*((c:ℕ):ℚ_[p])+((s+1:ℕ):ℚ_[p])*((p*q:ℕ):ℚ_[p]))
            *(((c:ℕ):ℚ_[p])⁻¹)^(s+2)*((((p*q+c:ℕ):ℚ_[p])⁻¹))^2) := by
    intro q
    have hstep : ∀ c ∈ Icc 1 (p-1), (((p*q+c:ℕ):ℚ_[p])⁻¹)^2
        = (∑ ℓ ∈ range (s+1), ((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ*((p*q:ℕ):ℚ_[p])^ℓ*(((c:ℕ):ℚ_[p])⁻¹)^(ℓ+2))
          + (-((p*q:ℕ):ℚ_[p]))^(s+1)*(((s+2:ℕ):ℚ_[p])*((c:ℕ):ℚ_[p])+((s+1:ℕ):ℚ_[p])*((p*q:ℕ):ℚ_[p]))
              *(((c:ℕ):ℚ_[p])⁻¹)^(s+2)*((((p*q+c:ℕ):ℚ_[p])⁻¹))^2 := by
      intro c hc
      simp only [Finset.mem_Icc] at hc
      have hc' : ¬ p ∣ c := by intro hd; have := Nat.le_of_dvd (by omega) hd; omega
      have hpqc' : ¬ p ∣ (p*q+c) := by
        intro hd
        exact hc' ((Nat.dvd_add_right ⟨q, rfl⟩).mp hd)
      exact pqc_expand p s q c hc' hpqc'
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ℓ _
    rw [← Finset.mul_sum]
  -- Split G into MAIN0 + ERR.
  have hsplit : (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3
        * (∑ c ∈ Icc 1 (p-1), (((p*q+c:ℕ):ℚ_[p])⁻¹)^2))
      = (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3
          * (∑ ℓ ∈ range (s+1), ((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ*((p*q:ℕ):ℚ_[p])^ℓ
              * (∑ c ∈ Icc 1 (p-1), ((c:ℚ_[p])⁻¹)^(ℓ+2))))
        + (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3
          * (∑ c ∈ Icc 1 (p-1), (-((p*q:ℕ):ℚ_[p]))^(s+1)
              *(((s+2:ℕ):ℚ_[p])*((c:ℕ):ℚ_[p])+((s+1:ℕ):ℚ_[p])*((p*q:ℕ):ℚ_[p]))
              *(((c:ℕ):ℚ_[p])⁻¹)^(s+2)*((((p*q+c:ℕ):ℚ_[p])⁻¹))^2)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [hInner q, mul_add]
  rw [hsplit]
  apply PD_add
  · -- MAIN0
    have hdist : (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3
          * (∑ ℓ ∈ range (s+1), ((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ*((p*q:ℕ):ℚ_[p])^ℓ
              * (∑ c ∈ Icc 1 (p-1), ((c:ℚ_[p])⁻¹)^(ℓ+2))))
        = ∑ q ∈ range M, ∑ ℓ ∈ range (s+1), ((M+q).choose q:ℚ_[p])^3
              * (((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ*((p*q:ℕ):ℚ_[p])^ℓ
                  * (∑ c ∈ Icc 1 (p-1), ((c:ℚ_[p])⁻¹)^(ℓ+2))) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum]
    rw [hdist, Finset.sum_comm]
    apply PD_sum
    intro ℓ hℓ
    simp only [Finset.mem_range] at hℓ
    set W := ∑ c ∈ Icc 1 (p-1), ((c:ℚ_[p])⁻¹)^(ℓ+2) with hWdef
    -- flatten the ℓ-term
    have hterm_eq : (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3
          * (((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ*((p*q:ℕ):ℚ_[p])^ℓ * W))
        = ((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ*(p:ℚ_[p])^ℓ*W
            *(∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ) := by
      rw [show ((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ*(p:ℚ_[p])^ℓ*W
              *(∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ)
          = ∑ q ∈ range M, ((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ*(p:ℚ_[p])^ℓ*W
              *(((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ)
          from Finset.mul_sum _ _ _]
      apply Finset.sum_congr rfl
      intro q _
      simp only [Nat.cast_mul, mul_pow]
      ring
    rw [hterm_eq]
    have hp_pow : PD p (↑ℓ*1) ((p:ℚ_[p])^ℓ) := PD_pow PD_p ℓ
    by_cases hcrit : (p-1) ∣ (ℓ+2)
    · -- critical: forces ℓ ≥ 1
      have hℓ1 : 1 ≤ ℓ := by
        rcases Nat.eq_zero_or_pos ℓ with h|h
        · exfalso; subst h; simp only [Nat.zero_add] at hcrit
          have := Nat.le_of_dvd (by norm_num) hcrit; omega
        · exact h
      have hWle : ‖W‖ ≤ 1 := by rw [hWdef]; exact Wsum_norm_le_one p (ℓ+2)
      have hS : PD p ((s+1-ℓ:ℕ):ℤ) (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ) :=
        L_sub_plus_PD p hp (by omega) s M hM ℓ hℓ1
      have hpS : PD p (↑ℓ*1 + ((s+1-ℓ:ℕ):ℤ))
          ((p:ℚ_[p])^ℓ * (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ)) := PD_mul hp_pow hS
      have hKW : ‖(((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ * W)‖ ≤ 1 := by
        have e1 : ‖((-1:ℚ_[p]))^ℓ‖ = 1 := by simp
        rw [norm_mul, norm_mul, e1, mul_one]
        exact mul_le_one₀ (norm_natCast_le_one p (ℓ+1)) (norm_nonneg _) hWle
      have hfull : PD p (↑ℓ*1 + ((s+1-ℓ:ℕ):ℤ))
          ((((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ * W) * ((p:ℚ_[p])^ℓ * (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ))) :=
        PD_mul_left hKW hpS
      rw [show ((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ*(p:ℚ_[p])^ℓ*W
              *(∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ)
          = (((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ * W) * ((p:ℚ_[p])^ℓ * (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ))
          from by ring]
      exact PD_mono (by push_cast; omega) hfull
    · -- non-critical
      have hWpd : PD p 1 W := by rw [hWdef]; exact Wsum_PD p (ℓ+2) hp5 hcrit
      have hS : PD p ((s-ℓ:ℕ):ℤ) (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ) :=
        L_sub_PD p hp s M hM ℓ
      have hpS : PD p (↑ℓ*1 + ((s-ℓ:ℕ):ℤ))
          ((p:ℚ_[p])^ℓ * (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ)) := PD_mul hp_pow hS
      have hWpS : PD p (1 + (↑ℓ*1 + ((s-ℓ:ℕ):ℤ)))
          (W * ((p:ℚ_[p])^ℓ * (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ))) := PD_mul hWpd hpS
      have hK : ‖(((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ)‖ ≤ 1 := by
        have e1 : ‖((-1:ℚ_[p]))^ℓ‖ = 1 := by simp
        rw [norm_mul, e1, mul_one]
        exact norm_natCast_le_one p (ℓ+1)
      have hfull : PD p (1 + (↑ℓ*1 + ((s-ℓ:ℕ):ℤ)))
          ((((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ) * (W * ((p:ℚ_[p])^ℓ * (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ)))) :=
        PD_mul_left hK hWpS
      rw [show ((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ*(p:ℚ_[p])^ℓ*W
              *(∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ)
          = (((ℓ+1:ℕ):ℚ_[p])*(-1)^ℓ) * (W * ((p:ℚ_[p])^ℓ * (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (q:ℚ_[p])^ℓ)))
          from by ring]
      exact PD_mono (by push_cast; omega) hfull
  · -- ERR
    apply PD_sum
    intro q _
    apply PD_mul_left
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_natCast_le_one p _)
    · apply PD_sum
      intro c hc
      simp only [Finset.mem_Icc] at hc
      have hc' : ¬ p ∣ c := by intro hd; have := Nat.le_of_dvd (by omega) hd; omega
      have hpqc' : ¬ p ∣ (p*q+c) := by
        intro hd; exact hc' ((Nat.dvd_add_right ⟨q, rfl⟩).mp hd)
      have hApd : PD p 1 (((p*q:ℕ):ℚ_[p])) := PD_natCast_of_dvd 1 (p*q) (by rw [pow_one]; exact ⟨q, rfl⟩)
      have hApow0 : PD p (↑(s+1)*1) ((-((p*q:ℕ):ℚ_[p]))^(s+1)) := PD_pow (PD_neg hApd) (s+1)
      have hApow : PD p ((s:ℤ)+1) ((-((p*q:ℕ):ℚ_[p]))^(s+1)) := by
        have : (↑(s+1)*1 : ℤ) = (s:ℤ)+1 := by push_cast; ring
        rwa [this] at hApow0
      have hM2 : ‖(((s+2:ℕ):ℚ_[p])*((c:ℕ):ℚ_[p])+((s+1:ℕ):ℚ_[p])*((p*q:ℕ):ℚ_[p]))‖ ≤ 1 := by
        refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
        apply max_le
        · rw [norm_mul]; exact mul_le_one₀ (norm_natCast_le_one p _) (norm_nonneg _) (norm_natCast_le_one p _)
        · rw [norm_mul]; exact mul_le_one₀ (norm_natCast_le_one p _) (norm_nonneg _) (norm_natCast_le_one p _)
      have hM3 : ‖(((c:ℕ):ℚ_[p])⁻¹)^(s+2)‖ ≤ 1 :=
        le_of_eq (by rw [norm_pow, norm_inv_natCast_coprime hc', one_pow])
      have hM4 : ‖((((p*q+c:ℕ):ℚ_[p])⁻¹))^2‖ ≤ 1 :=
        le_of_eq (by rw [norm_pow, norm_inv_natCast_coprime hpqc', one_pow])
      exact PD_mul_right (PD_mul_right (PD_mul_right hApow hM2) hM3) hM4

/-- `PD` from integer divisibility. -/
lemma PD_intCast_of_dvd {p : ℕ} [Fact p.Prime] (e : ℕ) (k : ℤ) (h : (p:ℤ)^e ∣ k) :
    PD p (e:ℤ) (k : ℚ_[p]) := by
  unfold PD
  rw [show (-(e:ℤ)) = (-(e:ℕ):ℤ) by norm_num, Padic.norm_int_le_pow_iff_dvd]
  exact h

/-- Difference-of-cubes bound via generalized Lucas. -/
lemma choose_cube_diff_PD (p : ℕ) [Fact p.Prime] (hp : p.Prime) (s M q c : ℕ)
    (hM : p^s ∣ M) (hc1 : 1 ≤ c) (hcp : c ≤ p-1) :
    PD p ((s:ℤ)+1)
      (((p*M+p*q+c-1).choose (p*q+c-1):ℚ_[p])^3 - ((M+q).choose q:ℚ_[p])^3) := by
  have hp2 : 2 ≤ p := hp.two_le
  set b := c - 1 with hbdef
  have hb : b < p := by omega
  have he1 : p*M+p*q+c-1 = p*M+p*q+b := by omega
  have he2 : p*q+c-1 = p*q+b := by omega
  rw [he1, he2]
  have hgl := gen_lucas p (s+1) M q b hp (by omega) (by simpa using hM) hb
  have hmod : (p*M + p*q + b).choose (p*q+b) ≡ (M+q).choose q [MOD p^(s+1)] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hgl
  have hz : (p:ℤ)^(s+1) ∣ (((p*M+p*q+b).choose (p*q+b):ℤ) - ((M+q).choose q:ℤ)) := by
    have hd := Nat.modEq_iff_dvd.mp hmod
    push_cast at hd
    exact dvd_sub_comm.mp hd
  have hz3 : (p:ℤ)^(s+1) ∣ (((p*M+p*q+b).choose (p*q+b):ℤ)^3 - ((M+q).choose q:ℤ)^3) := by
    obtain ⟨d, hd⟩ := hz
    refine ⟨d * (((p*M+p*q+b).choose (p*q+b):ℤ)^2 + ((p*M+p*q+b).choose (p*q+b):ℤ)*((M+q).choose q:ℤ) + ((M+q).choose q:ℤ)^2), ?_⟩
    have hfac : (((p*M+p*q+b).choose (p*q+b):ℤ)^3 - ((M+q).choose q:ℤ)^3)
        = (((p*M+p*q+b).choose (p*q+b):ℤ) - ((M+q).choose q:ℤ)) * (((p*M+p*q+b).choose (p*q+b):ℤ)^2 + ((p*M+p*q+b).choose (p*q+b):ℤ)*((M+q).choose q:ℤ) + ((M+q).choose q:ℤ)^2) := by ring
    rw [hfac, hd]; ring
  have hpd : PD p ((s+1:ℕ):ℤ) ((((p*M+p*q+b).choose (p*q+b):ℤ)^3 - ((M+q).choose q:ℤ)^3 : ℤ):ℚ_[p]) :=
    PD_intCast_of_dvd (s+1) _ hz3
  have hcast : ((((p*M+p*q+b).choose (p*q+b):ℤ)^3 - ((M+q).choose q:ℤ)^3 : ℤ):ℚ_[p])
      = ((p*M+p*q+b).choose (p*q+b):ℚ_[p])^3 - ((M+q).choose q:ℚ_[p])^3 := by push_cast; ring
  rw [hcast] at hpd
  have hlev : ((s+1:ℕ):ℤ) = (s:ℤ)+1 := by push_cast; ring
  rwa [hlev] at hpd

/-- `PD p (s+1) (S - G)`: correction between the true choose-cubes and the reduced ones. -/
lemma SG_bound (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hp5 : 5 ≤ p) (s M : ℕ) (hM : p^s ∣ M) :
    PD p ((s:ℤ)+1)
      (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
        (((p*M+p*q+c-1).choose (p*q+c-1):ℚ_[p])^3 - ((M+q).choose q:ℚ_[p])^3)
          * (((p*q+c:ℕ):ℚ_[p])⁻¹)^2) := by
  apply PD_sum
  intro q _
  apply PD_sum
  intro c hc
  simp only [Finset.mem_Icc] at hc
  have hc' : ¬ p ∣ (p*q+c) := by
    intro hd
    have hcc : ¬ p ∣ c := by intro h; have := Nat.le_of_dvd (by omega) h; omega
    exact hcc ((Nat.dvd_add_right ⟨q, rfl⟩).mp hd)
  apply PD_mul_right (choose_cube_diff_PD p hp s M q c hM (by omega) (by omega))
  exact le_of_eq (by rw [norm_pow, norm_inv_natCast_coprime hc', one_pow])

/-- `PD p (s+1) S` for the full choose-cube inverse-square sum `S`. -/
lemma S_bound (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hp5 : 5 ≤ p) (s M : ℕ) (hM : p^s ∣ M) :
    PD p ((s:ℤ)+1)
      (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
        ((p*M+p*q+c-1).choose (p*q+c-1):ℚ_[p])^3 * (((p*q+c:ℕ):ℚ_[p])⁻¹)^2) := by
  have hsplit : (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
        ((p*M+p*q+c-1).choose (p*q+c-1):ℚ_[p])^3 * (((p*q+c:ℕ):ℚ_[p])⁻¹)^2)
      = (∑ q ∈ range M, ((M+q).choose q:ℚ_[p])^3 * (∑ c ∈ Icc 1 (p-1), (((p*q+c:ℕ):ℚ_[p])⁻¹)^2))
        + (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
            (((p*M+p*q+c-1).choose (p*q+c-1):ℚ_[p])^3 - ((M+q).choose q:ℚ_[p])^3)
              * (((p*q+c:ℕ):ℚ_[p])⁻¹)^2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hsplit]
  exact PD_add (G_bound p hp hp5 s M hM) (SG_bound p hp hp5 s M hM)

/-- The NONALIGNED contribution `Σ_{p∤k} (N+2k)·C(N+k-1,k)³` (with `N = pM`, `k = pq+c`)
has `PD p (4s+4)`. -/
lemma NA_bound (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hp5 : 5 ≤ p) (s M : ℕ) (hM : p^s ∣ M) :
    PD p (4*(s:ℤ)+4)
      (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
        (↑(p*M + 2*(p*q+c)) : ℚ_[p]) * ((p*M+p*q+c-1).choose (p*q+c):ℚ_[p])^3) := by
  have hM1 : p^(s+1) ∣ p*M := by rw [pow_succ']; exact mul_dvd_mul_left p hM
  -- per-term equality
  have hNA : (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
        (↑(p*M + 2*(p*q+c)) : ℚ_[p]) * ((p*M+p*q+c-1).choose (p*q+c):ℚ_[p])^3)
      = (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
          (↑(p*M):ℚ_[p]) * ((p*M+p*q+c-1).choose (p*q+c):ℚ_[p])^3)
        + (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
            (2:ℚ_[p]) * (↑(p*M):ℚ_[p])^3
              * (((p*M+p*q+c-1).choose (p*q+c-1):ℚ_[p])^3 * (((p*q+c:ℕ):ℚ_[p])⁻¹)^2)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro q hq
    simp only [Finset.mem_range] at hq
    have hMpos : 0 < M := by omega
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro c hc
    simp only [Finset.mem_Icc] at hc
    have hpk : ¬ p ∣ (p*q+c) := by
      intro hd
      have hcc : ¬ p ∣ c := by intro h; have := Nat.le_of_dvd (by omega) h; omega
      exact hcc ((Nat.dvd_add_right ⟨q, rfl⟩).mp hd)
    have hkne : ((p*q+c:ℕ):ℚ_[p]) ≠ 0 := by
      intro h; have := norm_natCast_coprime (p:=p) hpk; rw [h] at this; simp at this
    have habs := absorb' (p*M) (p*q+c) (Nat.mul_pos hp.pos hMpos) (by omega)
    rw [show p*M+(p*q+c)-1 = p*M+p*q+c-1 from by omega] at habs
    have hkC : ((p*q+c:ℕ):ℚ_[p]) * ((p*M+p*q+c-1).choose (p*q+c):ℚ_[p])
        = (↑(p*M):ℚ_[p]) * ((p*M+p*q+c-1).choose (p*q+c-1):ℚ_[p]) := by exact_mod_cast habs
    have hcast : (↑(p*M + 2*(p*q+c)):ℚ_[p]) = (↑(p*M):ℚ_[p]) + 2*((p*q+c:ℕ):ℚ_[p]) := by
      push_cast; ring
    rw [hcast, add_mul]
    congr 1
    have hk2 : ((p*q+c:ℕ):ℚ_[p])^2 ≠ 0 := pow_ne_zero _ hkne
    apply mul_left_cancel₀ hk2
    rw [show ((p*q+c:ℕ):ℚ_[p])^2 * (2*((p*q+c:ℕ):ℚ_[p])*((p*M+p*q+c-1).choose (p*q+c):ℚ_[p])^3)
          = 2*(((p*q+c:ℕ):ℚ_[p])*((p*M+p*q+c-1).choose (p*q+c):ℚ_[p]))^3 from by ring,
        show ((p*q+c:ℕ):ℚ_[p])^2 * (2 * (↑(p*M):ℚ_[p])^3
            * (((p*M+p*q+c-1).choose (p*q+c-1):ℚ_[p])^3 * (((p*q+c:ℕ):ℚ_[p])⁻¹)^2))
          = 2*(↑(p*M):ℚ_[p])^3*((p*M+p*q+c-1).choose (p*q+c-1):ℚ_[p])^3
              * (((p*q+c:ℕ):ℚ_[p])^2*(((p*q+c:ℕ):ℚ_[p])⁻¹)^2) from by ring,
        hkC,
        show ((p*q+c:ℕ):ℚ_[p])^2*(((p*q+c:ℕ):ℚ_[p])⁻¹)^2 = 1 from by
          rw [← mul_pow, mul_inv_cancel₀ hkne, one_pow], mul_one]
    ring
  rw [hNA]
  -- factor the second sum
  have hfactor : (2:ℚ_[p]) * ((↑(p*M):ℚ_[p])^3
        * (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
            ((p*M+p*q+c-1).choose (p*q+c-1):ℚ_[p])^3 * (((p*q+c:ℕ):ℚ_[p])⁻¹)^2))
      = ∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
          (2:ℚ_[p]) * (↑(p*M):ℚ_[p])^3
            * (((p*M+p*q+c-1).choose (p*q+c-1):ℚ_[p])^3 * (((p*q+c:ℕ):ℚ_[p])⁻¹)^2) := by
    rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _
    rw [Finset.mul_sum]
  rw [← hfactor]
  apply PD_add
  · -- Part1: Σ ↑(pM)·C_k³
    apply PD_sum; intro q hq
    simp only [Finset.mem_range] at hq
    apply PD_sum; intro c hc
    simp only [Finset.mem_Icc] at hc
    have hpk : ¬ p ∣ (p*q+c) := by
      intro hd
      have hcc : ¬ p ∣ c := by intro h; have := Nat.le_of_dvd (by omega) h; omega
      exact hcc ((Nat.dvd_add_right ⟨q, rfl⟩).mp hd)
    have hC_k_dvd : p^(s+1) ∣ (p*M+p*q+c-1).choose (p*q+c) := by
      have := pow_dvd_choose p (s+1) (p*M) (p*q+c) hp hM1 (by omega) hpk
      rwa [show p*M+(p*q+c)-1 = p*M+p*q+c-1 from by omega] at this
    have hN : PD p ((s+1:ℕ):ℤ) ((p*M:ℕ):ℚ_[p]) := PD_natCast_of_dvd (s+1) (p*M) hM1
    have hCk3 : PD p (↑3 * ((s+1:ℕ):ℤ)) (((p*M+p*q+c-1).choose (p*q+c):ℚ_[p])^3) :=
      PD_pow (PD_natCast_of_dvd (s+1) _ hC_k_dvd) 3
    have := PD_mul hN hCk3
    exact PD_mono (by push_cast; omega) this
  · -- Part2: 2 * (↑(pM)³ * S)
    have h2 : ‖(2:ℚ_[p])‖ ≤ 1 := by
      rw [show (2:ℚ_[p])=((2:ℕ):ℚ_[p]) by norm_num]; exact norm_natCast_le_one p 2
    have hN3 : PD p (↑3 * ((s+1:ℕ):ℤ)) (((p*M:ℕ):ℚ_[p])^3) :=
      PD_pow (PD_natCast_of_dvd (s+1) (p*M) hM1) 3
    have hS : PD p ((s:ℤ)+1)
        (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
          ((p*M+p*q+c-1).choose (p*q+c-1):ℚ_[p])^3 * (((p*q+c:ℕ):ℚ_[p])⁻¹)^2) :=
      S_bound p hp hp5 s M hM
    have hprod := PD_mul hN3 hS
    have := PD_mul_left h2 hprod
    exact PD_mono (by push_cast; omega) this

/-- Split off the `b=0` term of a `range p` sum. -/
lemma sum_range_split0 {R:Type*}[AddCommMonoid R] (p:ℕ)(hp:1≤p)(g:ℕ→R):
    ∑ b ∈ range p, g b = g 0 + ∑ b ∈ Icc 1 (p-1), g b := by
  rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive g (Nat.zero_le 1) hp,
      show Icc 1 (p-1) = Ico 1 p from by rw [← Ico_add_one_right_eq_Icc, show (p-1)+1 = p from by omega],
      ← Finset.range_eq_Ico, Finset.sum_range_one]

/-- The ALIGNED contribution has `PD p (4s+4)`. -/
lemma ALIGNED_bound (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (M : ℕ) (hM : 1 ≤ M) :
    PD p (4*(padicValNat p M)+4)
      (∑ j ∈ range (M+1), ((p*(M+2*j):ℕ):ℚ_[p])
        * (((p*(M+j)-1).choose (p*j):ℚ_[p])^3 - ((M+j-1).choose j:ℚ_[p])^3)) := by
  apply PD_sum
  intro j hj
  rcases Nat.eq_zero_or_pos j with hj0 | hj1
  · subst hj0
    have h0 : (((p*(M+2*0):ℕ):ℚ_[p])
        * (((p*(M+0)-1).choose (p*0):ℚ_[p])^3 - ((M+0-1).choose 0:ℚ_[p])^3)) = 0 := by simp
    rw [h0]; unfold PD; rw [norm_zero]; positivity
  · exact aligned_term p M j hp5 hM hj1

/-- The exact split `f(pM) - p·f(M) = ALIGNED + NONALIGNED` in `ℚ_[p]`. -/
lemma fsplit_padic (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hp5 : 5 ≤ p) (M : ℕ) :
    (∑ k ∈ range (p*M+1), (↑(p*M+2*k):ℚ_[p])*((p*M+k-1).choose k:ℚ_[p])^3)
      - (p:ℚ_[p])*(∑ k ∈ range (M+1), (↑(M+2*k):ℚ_[p])*((M+k-1).choose k:ℚ_[p])^3)
    = (∑ j ∈ range (M+1), ((p*(M+2*j):ℕ):ℚ_[p])
          * (((p*(M+j)-1).choose (p*j):ℚ_[p])^3 - ((M+j-1).choose j:ℚ_[p])^3))
      + (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
          (↑(p*M + 2*(p*q+c)) : ℚ_[p]) * ((p*M+p*q+c-1).choose (p*q+c):ℚ_[p])^3) := by
  have hp1 : 1 ≤ p := by omega
  have hA : (∑ k ∈ range (p*M+1), (↑(p*M+2*k):ℚ_[p])*((p*M+k-1).choose k:ℚ_[p])^3)
      = ((∑ q ∈ range M, (↑(p*M+2*(p*q)):ℚ_[p])*((p*M+p*q-1).choose (p*q):ℚ_[p])^3)
          + (↑(p*M+2*(p*M)):ℚ_[p])*((p*M+p*M-1).choose (p*M):ℚ_[p])^3)
        + (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
            (↑(p*M + 2*(p*q+c)):ℚ_[p])*((p*M+(p*q+c)-1).choose (p*q+c):ℚ_[p])^3) := by
    rw [Finset.sum_range_succ,
        sum_range_block M p (fun k => (↑(p*M+2*k):ℚ_[p])*((p*M+k-1).choose k:ℚ_[p])^3)]
    have hinner : ∀ q ∈ range M,
        (∑ b ∈ range p, (↑(p*M+2*(p*q+b)):ℚ_[p])*((p*M+(p*q+b)-1).choose (p*q+b):ℚ_[p])^3)
        = (↑(p*M+2*(p*q)):ℚ_[p])*((p*M+p*q-1).choose (p*q):ℚ_[p])^3
          + ∑ c ∈ Icc 1 (p-1), (↑(p*M+2*(p*q+c)):ℚ_[p])*((p*M+(p*q+c)-1).choose (p*q+c):ℚ_[p])^3 := by
      intro q _
      rw [sum_range_split0 p hp1
          (fun b => (↑(p*M+2*(p*q+b)):ℚ_[p])*((p*M+(p*q+b)-1).choose (p*q+b):ℚ_[p])^3)]
      simp only [Nat.add_zero]
    rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
    ring
  rw [hA]
  have hB : (p:ℚ_[p])*(∑ k ∈ range (M+1), (↑(M+2*k):ℚ_[p])*((M+k-1).choose k:ℚ_[p])^3)
      = (∑ q ∈ range M, (↑(p*M+2*(p*q)):ℚ_[p])*((M+q-1).choose q:ℚ_[p])^3)
        + (↑(p*M+2*(p*M)):ℚ_[p])*((M+M-1).choose M:ℚ_[p])^3 := by
    rw [Finset.mul_sum, Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro q _
      rw [show (↑(p*M+2*(p*q)):ℚ_[p]) = (p:ℚ_[p])*(↑(M+2*q):ℚ_[p]) from by push_cast; ring]
      ring
    · rw [show (↑(p*M+2*(p*M)):ℚ_[p]) = (p:ℚ_[p])*(↑(M+2*M):ℚ_[p]) from by push_cast; ring]
      ring
  rw [hB]
  have hALIGN : ((∑ q ∈ range M, (↑(p*M+2*(p*q)):ℚ_[p])*((p*M+p*q-1).choose (p*q):ℚ_[p])^3)
        + (↑(p*M+2*(p*M)):ℚ_[p])*((p*M+p*M-1).choose (p*M):ℚ_[p])^3)
      - ((∑ q ∈ range M, (↑(p*M+2*(p*q)):ℚ_[p])*((M+q-1).choose q:ℚ_[p])^3)
        + (↑(p*M+2*(p*M)):ℚ_[p])*((M+M-1).choose M:ℚ_[p])^3)
      = ∑ j ∈ range (M+1), ((p*(M+2*j):ℕ):ℚ_[p])
          * (((p*(M+j)-1).choose (p*j):ℚ_[p])^3 - ((M+j-1).choose j:ℚ_[p])^3) := by
    rw [Finset.sum_range_succ,
        show ((∑ q ∈ range M, (↑(p*M+2*(p*q)):ℚ_[p])*((p*M+p*q-1).choose (p*q):ℚ_[p])^3)
              + (↑(p*M+2*(p*M)):ℚ_[p])*((p*M+p*M-1).choose (p*M):ℚ_[p])^3)
            - ((∑ q ∈ range M, (↑(p*M+2*(p*q)):ℚ_[p])*((M+q-1).choose q:ℚ_[p])^3)
              + (↑(p*M+2*(p*M)):ℚ_[p])*((M+M-1).choose M:ℚ_[p])^3)
          = ((∑ q ∈ range M, (↑(p*M+2*(p*q)):ℚ_[p])*((p*M+p*q-1).choose (p*q):ℚ_[p])^3)
              - (∑ q ∈ range M, (↑(p*M+2*(p*q)):ℚ_[p])*((M+q-1).choose q:ℚ_[p])^3))
            + ((↑(p*M+2*(p*M)):ℚ_[p])*((p*M+p*M-1).choose (p*M):ℚ_[p])^3
              - (↑(p*M+2*(p*M)):ℚ_[p])*((M+M-1).choose M:ℚ_[p])^3) from by ring,
        ← Finset.sum_sub_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      rw [show p*M+2*(p*j) = p*(M+2*j) from by ring, show p*M+p*j-1 = p*(M+j)-1 from by rw [Nat.mul_add]]
      ring
    · rw [show p*M+2*(p*M) = p*(M+2*M) from by ring, show p*M+p*M-1 = p*(M+M)-1 from by rw [Nat.mul_add]]
      ring
  have hNONeq : (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
        (↑(p*M + 2*(p*q+c)):ℚ_[p])*((p*M+(p*q+c)-1).choose (p*q+c):ℚ_[p])^3)
      = ∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
        (↑(p*M + 2*(p*q+c)):ℚ_[p])*((p*M+p*q+c-1).choose (p*q+c):ℚ_[p])^3 := by
    apply Finset.sum_congr rfl; intro q _; apply Finset.sum_congr rfl; intro c _
    rw [show p*M+(p*q+c)-1 = p*M+p*q+c-1 from by rw [← Nat.add_assoc]]
  rw [show (((∑ q ∈ range M, (↑(p*M+2*(p*q)):ℚ_[p])*((p*M+p*q-1).choose (p*q):ℚ_[p])^3)
          + (↑(p*M+2*(p*M)):ℚ_[p])*((p*M+p*M-1).choose (p*M):ℚ_[p])^3)
        + (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
            (↑(p*M + 2*(p*q+c)):ℚ_[p])*((p*M+(p*q+c)-1).choose (p*q+c):ℚ_[p])^3))
      - ((∑ q ∈ range M, (↑(p*M+2*(p*q)):ℚ_[p])*((M+q-1).choose q:ℚ_[p])^3)
          + (↑(p*M+2*(p*M)):ℚ_[p])*((M+M-1).choose M:ℚ_[p])^3)
      = (((∑ q ∈ range M, (↑(p*M+2*(p*q)):ℚ_[p])*((p*M+p*q-1).choose (p*q):ℚ_[p])^3)
            + (↑(p*M+2*(p*M)):ℚ_[p])*((p*M+p*M-1).choose (p*M):ℚ_[p])^3)
          - ((∑ q ∈ range M, (↑(p*M+2*(p*q)):ℚ_[p])*((M+q-1).choose q:ℚ_[p])^3)
            + (↑(p*M+2*(p*M)):ℚ_[p])*((M+M-1).choose M:ℚ_[p])^3))
        + (∑ q ∈ range M, ∑ c ∈ Icc 1 (p-1),
            (↑(p*M + 2*(p*q+c)):ℚ_[p])*((p*M+(p*q+c)-1).choose (p*q+c):ℚ_[p])^3) from by ring,
      hALIGN, hNONeq]


/-- The numerator `f(N) = ∑_{k=0}^N (N+2k)·C(N+k-1,k)³`. -/
def fN (N : ℕ) : ℕ := ∑ k ∈ range (N+1), (N+2*k)*((N+k-1).choose k)^3

/-- Integrality: `N ∣ f(N)`. -/
lemma N_dvd_fN (N : ℕ) : N ∣ fN N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [fN]
  · unfold fN
    apply Finset.dvd_sum
    intro k _
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · have habs := absorb' N k hN hk
      have hid : (N+2*k)*((N+k-1).choose k)^3
          = N * (((N+k-1).choose k)^3 + 2*((N+k-1).choose (k-1))*((N+k-1).choose k)^2) := by
        have h2 : (2*k)*((N+k-1).choose k)^3
            = N*(2*((N+k-1).choose (k-1))*((N+k-1).choose k)^2) := by
          rw [show (2*k)*((N+k-1).choose k)^3
                = 2*(k*(N+k-1).choose k)*((N+k-1).choose k)^2 from by ring, habs]; ring
        calc (N+2*k)*((N+k-1).choose k)^3
            = N*((N+k-1).choose k)^3 + (2*k)*((N+k-1).choose k)^3 := by ring
          _ = N*((N+k-1).choose k)^3 + N*(2*((N+k-1).choose (k-1))*((N+k-1).choose k)^2) := by rw [h2]
          _ = N * (((N+k-1).choose k)^3 + 2*((N+k-1).choose (k-1))*((N+k-1).choose k)^2) := by ring
      rw [hid]; exact dvd_mul_right N _

/-- The numerator of `a n` equals `fN n`. -/
lemma numer_eq (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ range (n+1), (n+2*k)*((n+k-1).choose (n-1))^3) = fN n := by
  unfold fN
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  rw [← Nat.choose_symm (by omega : n-1 ≤ n+k-1), show (n+k-1)-(n-1) = k from by omega]

/-- `a n = fN n / n`, and `n * a n = fN n` for `n ≥ 1`. -/
lemma a_eq (n : ℕ) (hn : 1 ≤ n) : a n = fN n / n := by
  unfold a
  rw [if_neg (by omega)]
  simp only
  rw [numer_eq n hn]

lemma n_mul_a (n : ℕ) (hn : 1 ≤ n) : n * a n = fN n := by
  rw [a_eq n hn, Nat.mul_div_cancel' (N_dvd_fN n)]

/-- Cast of `fN` to `ℚ_[p]`. -/
lemma fN_cast (p : ℕ) [Fact p.Prime] (N : ℕ) :
    ((fN N : ℕ):ℚ_[p]) = ∑ k ∈ range (N+1), (↑(N+2*k):ℚ_[p])*((N+k-1).choose k:ℚ_[p])^3 := by
  unfold fN
  push_cast
  rfl

/-- The `p`-adic bound on the numerator difference. -/
lemma f_diff_bound (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hp5 : 5 ≤ p) (M : ℕ) (hM : 1 ≤ M) :
    PD p (4*(padicValNat p M)+4)
      ((∑ k ∈ range (p*M+1), (↑(p*M+2*k):ℚ_[p])*((p*M+k-1).choose k:ℚ_[p])^3)
        - (p:ℚ_[p])*(∑ k ∈ range (M+1), (↑(M+2*k):ℚ_[p])*((M+k-1).choose k:ℚ_[p])^3)) := by
  rw [fsplit_padic p hp hp5 M]
  apply PD_add
  · exact ALIGNED_bound p hp5 M hM
  · exact NA_bound p hp hp5 (padicValNat p M) M pow_padicValNat_dvd

/-- `PD` implies integer divisibility. -/
lemma dvd_of_PD_intCast {p : ℕ} [Fact p.Prime] (n : ℕ) (D : ℤ) (h : PD p (n : ℤ) ((D : ℤ) : ℚ_[p])) : (p : ℤ) ^ n ∣ D := by
  unfold PD at h
  rwa [show (-(n:ℤ)) = (-(n:ℕ):ℤ) by norm_num, Padic.norm_int_le_pow_iff_dvd] at h

/-- The integer divisibility for the numerator difference. -/
lemma f_diff_dvd (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hp5 : 5 ≤ p) (M : ℕ) (hM : 1 ≤ M) :
    (p:ℤ)^(4*(padicValNat p M)+4) ∣ ((fN (p*M):ℤ) - (p:ℤ)*(fN M:ℤ)) := by
  have hpd := f_diff_bound p hp hp5 M hM
  rw [← fN_cast p (p*M), ← fN_cast p M] at hpd
  have hcast : ((fN (p*M):ℕ):ℚ_[p]) - (p:ℚ_[p])*((fN M:ℕ):ℚ_[p])
      = (((fN (p*M):ℤ) - (p:ℤ)*(fN M:ℤ) : ℤ):ℚ_[p]) := by push_cast; ring
  rw [hcast] at hpd
  have hlev : (4*(padicValNat p M : ℤ)+4) = ((4*(padicValNat p M)+4 : ℕ):ℤ) := by push_cast; ring
  rw [hlev] at hpd
  exact dvd_of_PD_intCast (4*(padicValNat p M)+4) _ hpd

/-- Single Dwork step. -/
lemma single_step (p : ℕ) [Fact p.Prime] (hp : p.Prime) (hp5 : 5 ≤ p) (m : ℕ) (hm : 1 ≤ m) :
    a (m*p) ≡ a m [MOD p^(3*(padicValNat p m + 1))] := by
  set s := padicValNat p m with hsdef
  rw [show m*p = p*m from Nat.mul_comm m p]
  have hmne : m ≠ 0 := by omega
  have hs : p^s ∣ m := by rw [hsdef]; exact pow_padicValNat_dvd
  have hnotdvd : ¬ p^(s+1) ∣ m := by rw [hsdef]; exact pow_succ_padicValNat_not_dvd hmne
  obtain ⟨u, hu_eq⟩ := hs
  have hpu : ¬ p ∣ u := by
    intro hd; obtain ⟨w, hw⟩ := hd
    exact hnotdvd ⟨w, by rw [hu_eq, hw, pow_succ]; ring⟩
  have hpm1 : 1 ≤ p*m := Nat.mul_pos hp.pos (by omega)
  have hkey : ((p*m:ℕ):ℤ) * ((a (p*m):ℤ) - (a m:ℤ)) = ((fN (p*m):ℤ) - (p:ℤ)*(fN m:ℤ)) := by
    have e1 : ((p*m:ℕ):ℤ) * (a (p*m):ℤ) = (fN (p*m):ℤ) := by
      have := n_mul_a (p*m) hpm1; exact_mod_cast this
    have e2 : ((p*m:ℕ):ℤ) * (a m:ℤ) = (p:ℤ)*(fN m:ℤ) := by
      have h := n_mul_a m hm
      rw [show ((p*m:ℕ):ℤ) = (p:ℤ)*(m:ℤ) from by push_cast; ring, mul_assoc,
          show (m:ℤ)*(a m:ℤ) = (fN m:ℤ) from by exact_mod_cast h]
    rw [mul_sub, e1, e2]
  have hfd : (p:ℤ)^(4*s+4) ∣ ((fN (p*m):ℤ) - (p:ℤ)*(fN m:ℤ)) := by
    rw [show 4*s+4 = 4*(padicValNat p m)+4 from by rw [hsdef]]
    exact f_diff_dvd p hp hp5 m hm
  rw [← hkey, show ((p*m:ℕ):ℤ) = (p:ℤ)^(s+1) * (u:ℤ) from by
        rw [show p*m = p^(s+1)*u from by rw [hu_eq, pow_succ]; ring]; push_cast; ring,
      show 4*s+4 = (s+1) + 3*(s+1) from by ring, pow_add, mul_assoc] at hfd
  have hcancel : (p:ℤ)^(3*(s+1)) ∣ (u:ℤ)*((a (p*m):ℤ) - (a m:ℤ)) :=
    (mul_dvd_mul_iff_left (pow_ne_zero (s+1) (by exact_mod_cast hp.pos.ne'))).mp hfd
  have hcop : IsCoprime ((p:ℤ)^(3*(s+1))) ((u:ℕ):ℤ) := by
    rw [show ((p:ℤ)^(3*(s+1))) = ((p^(3*(s+1)):ℕ):ℤ) from by push_cast; ring,
        Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact Nat.Coprime.pow_left _ ((hp.coprime_iff_not_dvd).mpr hpu)
  have hdvd : (p:ℤ)^(3*(s+1)) ∣ ((a (p*m):ℤ) - (a m:ℤ)) := hcop.dvd_of_dvd_mul_left hcancel
  rw [Nat.modEq_iff_dvd, show ((p^(3*(s+1)):ℕ):ℤ) = (p:ℤ)^(3*(s+1)) from by push_cast; ring]
  have hneg := (dvd_neg).mpr hdvd
  rwa [neg_sub] at hneg

theorem main_thm {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  set m := n * p ^ (r-1) with hmdef
  have hm1 : 1 ≤ m := by
    rw [hmdef]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  have hmp : m * p = n * p^r := by
    rw [hmdef, mul_assoc, ← pow_succ, show (r-1)+1 = r from by omega]
  have hstep := single_step p hp hp5 m hm1
  rw [hmp] at hstep
  have hval : padicValNat p m = padicValNat p n + (r-1) := by
    rw [hmdef, padicValNat.mul (by omega) (pow_ne_zero _ (by omega)), padicValNat.prime_pow]
  have hdvd : p^(3*r) ∣ p^(3*(padicValNat p m + 1)) := pow_dvd_pow p (by rw [hval]; omega)
  exact hstep.of_dvd hdvd
