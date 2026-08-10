import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
The sequence $a(n)$ defined by
$$a(n) = \frac{1}{n} \sum_{k = 0}^n (n+2k) \binom{n+k-1}{k}^3$$
for $n \ge 1$.
-/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    -- Calculate the numerator sum S in ℕ
    -- We use binomial(n+k-1, n-1) which is equal to binomial(n+k-1, k)
    -- This makes the dependency on 'n - 1' explicit for the lower index.
    let S : ℕ := Finset.sum (range (n + 1)) fun k =>
      (n + 2 * k) * (Nat.choose (n + k - 1) (n - 1)) ^ 3

    -- Division is exact since a(n) is an integer sequence.
    S / n

/-- Pascal's identity in the form needed to rewrite the summand below. -/
lemma choose_pascal_for_oeis_361883 {n k : ℕ} (hn : 0 < n) :
    Nat.choose (n + k) k =
      Nat.choose (n + k - 1) (n - 1) + Nat.choose (n + k - 1) n := by
  have hnk : 0 < n + k := by omega
  calc
    Nat.choose (n + k) k = Nat.choose (n + k) n := by
      apply Nat.choose_symm_of_eq_add
      omega
    _ = Nat.choose (n + k - 1) (n - 1) + Nat.choose (n + k - 1) n := by
      have hn1 : n - 1 + 1 = n := by omega
      simpa [hn1] using Nat.choose_succ_right (n + k) (n - 1) hnk

/-- The adjacent binomial coefficients occurring in the alternative summand. -/
lemma choose_adjacent_mul_for_oeis_361883 {n k : ℕ} (hn : 0 < n) :
    Nat.choose (n + k - 1) n * n = Nat.choose (n + k - 1) (n - 1) * k := by
  have h := Nat.choose_succ_right_eq (n + k - 1) (n - 1)
  have hsub : n + k - 1 - (n - 1) = k := by omega
  have hn1 : n - 1 + 1 = n := by omega
  simpa [hsub, hn1] using h

/--
Termwise polynomial identity behind the integer summation formula for `a`.
This is the useful rewrite
`(n + 2k) C^3 / n = C * (choose (n+k) k^2 - choose (n+k-1) n^2)`
after clearing the denominator `n`.
-/
lemma oeis_361883_term_identity {n k : ℕ} (hn : 0 < n) :
    n * (Nat.choose (n + k - 1) (n - 1) *
      (Nat.choose (n + k) k ^ 2 - Nat.choose (n + k - 1) n ^ 2)) =
    (n + 2 * k) * Nat.choose (n + k - 1) (n - 1) ^ 3 := by
  let C := Nat.choose (n + k - 1) (n - 1)
  let E := Nat.choose (n + k - 1) n
  have hD : Nat.choose (n + k) k = C + E := by
    dsimp [C, E]
    exact choose_pascal_for_oeis_361883 hn
  have hE : E * n = C * k := by
    dsimp [C, E]
    exact choose_adjacent_mul_for_oeis_361883 hn
  dsimp [C, E] at hD hE ⊢
  rw [hD]
  have hs : (Nat.choose (n + k - 1) (n - 1) + Nat.choose (n + k - 1) n) ^ 2 -
      Nat.choose (n + k - 1) n ^ 2 =
      Nat.choose (n + k - 1) (n - 1) ^ 2 +
        2 * Nat.choose (n + k - 1) (n - 1) * Nat.choose (n + k - 1) n := by
    rw [Nat.sub_eq_iff_eq_add]
    · ring
    · nlinarith [Nat.le_add_left (Nat.choose (n + k - 1) n)
        (Nat.choose (n + k - 1) (n - 1))]
  rw [hs]
  nlinarith

/--
Equivalent denominator-free summation formula for `a`, valid for positive `n`.
This matches the experimentally useful summand
`choose(n+k-1,k) * (choose(n+k,k)^2 - choose(n+k-1,n)^2)`, up to symmetry of
`choose (n+k-1) (n-1)` and `choose (n+k-1) k`.
-/
lemma a_eq_sum_oeis_361883_T (n : ℕ) (hn : 0 < n) :
    a n = Finset.sum (range (n + 1)) (fun k =>
      Nat.choose (n + k - 1) (n - 1) *
        (Nat.choose (n + k) k ^ 2 - Nat.choose (n + k - 1) n ^ 2)) := by
  unfold a
  simp [hn.ne']
  let T : ℕ → ℕ := fun k => Nat.choose (n + k - 1) (n - 1) *
        (Nat.choose (n + k) k ^ 2 - Nat.choose (n + k - 1) n ^ 2)
  have hsum :
      (Finset.sum (range (n + 1)) fun k =>
        (n + 2 * k) * Nat.choose (n + k - 1) (n - 1) ^ 3) =
      n * Finset.sum (range (n + 1)) T := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [T]
    exact (oeis_361883_term_identity (n := n) (k := k) hn).symm
  rw [hsum]
  exact Nat.mul_div_right _ hn


/-- The denominator-free summand used in the positive-`n` formula for `a`. -/
def oeis_361883_T (N k : ℕ) : ℕ :=
  Nat.choose (N + k - 1) (N - 1) *
    (Nat.choose (N + k) k ^ 2 - Nat.choose (N + k - 1) N ^ 2)

/-- A polynomial form of the denominator-free summand. -/
lemma oeis_361883_T_eq_sq_mul (N k : ℕ) (hN : 0 < N) :
    oeis_361883_T N k =
      let A := Nat.choose (N + k - 1) (N - 1)
      let C := Nat.choose (N + k - 1) N
      A ^ 2 * (A + 2 * C) := by
  unfold oeis_361883_T
  let A := Nat.choose (N + k - 1) (N - 1)
  let C := Nat.choose (N + k - 1) N
  have hD : Nat.choose (N + k) k = A + C := by
    dsimp [A, C]
    exact choose_pascal_for_oeis_361883 hN
  change A * (Nat.choose (N + k) k ^ 2 - C ^ 2) = A ^ 2 * (A + 2 * C)
  rw [hD]
  have hs : (A + C) ^ 2 - C ^ 2 = A ^ 2 + 2 * A * C := by
    rw [Nat.sub_eq_iff_eq_add]
    · ring
    · nlinarith [Nat.le_add_left C A]
  rw [hs]
  ring

lemma a_eq_sum_oeis_361883_T_def (n : ℕ) (hn : 0 < n) :
    a n = Finset.sum (range (n + 1)) (fun k => oeis_361883_T n k) := by
  simpa [oeis_361883_T] using a_eq_sum_oeis_361883_T n hn


/-- Clearing the natural denominator in the diagonal summand: the summand can be expressed
using the central binomial `choose (N+k) N` after multiplying by `(N+k)^3`. -/
lemma oeis_361883_T_clear_denominator (N k : ℕ) (hN : 0 < N) :
    (N + k) ^ 3 * oeis_361883_T N k =
      N ^ 2 * (N + 2 * k) * Nat.choose (N + k) N ^ 3 := by
  let A := Nat.choose (N + k - 1) (N - 1)
  let C := Nat.choose (N + k - 1) N
  let U := Nat.choose (N + k) N
  have hT : oeis_361883_T N k = A ^ 2 * (A + 2 * C) := by
    simpa [A, C] using oeis_361883_T_eq_sq_mul (N := N) (k := k) hN
  have hU : U = A + C := by
    dsimp [U, A, C]
    calc
      Nat.choose (N + k) N = Nat.choose (N + k) k := by
        apply Nat.choose_symm_of_eq_add
        omega
      _ = Nat.choose (N + k - 1) (N - 1) + Nat.choose (N + k - 1) N := by
        exact choose_pascal_for_oeis_361883 (n := N) (k := k) hN
  have hA : (N + k) * A = U * N := by
    have hadj := choose_adjacent_mul_for_oeis_361883 (n := N) (k := k) hN
    rw [hU]
    nlinarith
  have hC : (N + k) * C = U * k := by
    have hadj := choose_adjacent_mul_for_oeis_361883 (n := N) (k := k) hN
    rw [hU]
    nlinarith
  have hAC : (N + k) * (A + 2 * C) = U * (N + 2 * k) := by
    nlinarith
  rw [hT]
  calc
    (N + k) ^ 3 * (A ^ 2 * (A + 2 * C))
        = ((N + k) * A) ^ 2 * ((N + k) * (A + 2 * C)) := by ring
    _ = (U * N) ^ 2 * (U * (N + 2 * k)) := by rw [hA, hAC]
    _ = N ^ 2 * (N + 2 * k) * U ^ 3 := by ring


/-- The cleared-denominator identity specialized to the diagonal `p`-multiple argument, with the
common factor `p^3` cancelled. -/
lemma oeis_361883_T_clear_denominator_diag_mul (M p j : ℕ) (hM : 0 < M) (hp : 0 < p) :
    (M + j) ^ 3 * oeis_361883_T (M * p) (p * j) =
      M ^ 2 * (M + 2 * j) * Nat.choose (p * (M + j)) (p * M) ^ 3 := by
  have hMp : 0 < M * p := Nat.mul_pos hM hp
  have h := oeis_361883_T_clear_denominator (N := M * p) (k := p * j) hMp
  have hsum : M * p + p * j = p * (M + j) := by ring
  have hleft : (M * p + p * j) ^ 3 = p ^ 3 * (M + j) ^ 3 := by
    rw [hsum, mul_pow]
  have hright1 : (M * p) ^ 2 * (M * p + 2 * (p * j)) = p ^ 3 * (M ^ 2 * (M + 2 * j)) := by
    ring
  have hchoose : Nat.choose (M * p + p * j) (M * p) = Nat.choose (p * (M + j)) (p * M) := by
    rw [hsum]
    congr 1
    ring
  rw [hleft, hright1, hchoose] at h
  have hp3 : 0 < p ^ 3 := pow_pos hp 3
  apply Nat.eq_of_mul_eq_mul_left hp3
  simpa [mul_assoc, mul_left_comm, mul_comm] using h


/-- If the central binomial coefficients in the diagonal position are congruent modulo `m`, then
the diagonal summands are congruent modulo `m` after clearing the common factor `(M+j)^3`. -/
lemma T_diag_cleared_modEq_of_choose_modEq_oeis_361883 {p M j m : ℕ}
    (hM : 0 < M) (hp : 0 < p)
    (hchoose : Nat.choose (p * (M + j)) (p * M) ≡ Nat.choose (M + j) M [MOD m]) :
    (M + j) ^ 3 * oeis_361883_T (M * p) (p * j) ≡
      (M + j) ^ 3 * oeis_361883_T M j [MOD m] := by
  rw [oeis_361883_T_clear_denominator_diag_mul M p j hM hp]
  rw [oeis_361883_T_clear_denominator M j hM]
  exact (Nat.ModEq.refl (M ^ 2 * (M + 2 * j))).mul (hchoose.pow 3)

/-- In the diagonal case where `M+j` is a unit modulo `p`, a sufficiently strong central
binomial congruence gives the actual (not just cleared) summand congruence. -/
lemma T_diag_unit_modEq_of_choose_modEq_oeis_361883 {p M r j : ℕ} [Fact p.Prime]
    (hM : 0 < M) (hpunit : ¬ p ∣ M + j)
    (hchoose : Nat.choose (p * (M + j)) (p * M) ≡ Nat.choose (M + j) M [MOD p ^ (3 * r)]) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ (3 * r)] := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  have hclear := T_diag_cleared_modEq_of_choose_modEq_oeis_361883
    (p := p) (M := M) (j := j) (m := p ^ (3 * r)) hM hp0 hchoose
  have hcop : Nat.gcd (p ^ (3 * r)) ((M + j) ^ 3) = 1 := by
    rw [Nat.gcd_comm]
    exact (Nat.Coprime.pow_left 3 (Nat.Coprime.pow_right (3 * r)
      (((hp.coprime_iff_not_dvd).2 hpunit).symm)))
  exact Nat.ModEq.cancel_left_of_coprime hcop hclear

/-- A unit diagonal summand congruence from a weaker congruence of central binomial cubes.
The factor `M^2` supplies `p^(2r-2)`, so modulo `p^(r+2)` for the cubes is enough. -/
lemma T_diag_unit_modEq_of_choose_cube_modEq_oeis_361883 {p M r j : ℕ} [Fact p.Prime]
    (hr : 0 < r) (hMpos : 0 < M) (hMdiv : p ^ (r - 1) ∣ M) (hpunit : ¬ p ∣ M + j)
    (hcube : Nat.choose (p * (M + j)) (p * M) ^ 3 ≡
        Nat.choose (M + j) M ^ 3 [MOD p ^ (r + 2)]) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ (3 * r)] := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  have hclear_eq1 := oeis_361883_T_clear_denominator_diag_mul M p j hMpos hp0
  have hclear_eq0 := oeis_361883_T_clear_denominator M j hMpos
  have hfactor : p ^ (3 * r) ∣ M ^ 2 * (p ^ (r + 2)) := by
    rcases hMdiv with ⟨u, hu⟩
    rw [hu]
    refine ⟨u ^ 2, ?_⟩
    rw [mul_pow]
    have hexp : (r - 1) * 2 + (r + 2) = 3 * r := by omega
    calc
      (p ^ (r - 1)) ^ 2 * u ^ 2 * p ^ (r + 2) =
          p ^ ((r - 1) * 2) * p ^ (r + 2) * u ^ 2 := by
        rw [← pow_mul]
        ring
      _ = p ^ ((r - 1) * 2 + (r + 2)) * u ^ 2 := by
        rw [← pow_add]
      _ = p ^ (3 * r) * u ^ 2 := by rw [hexp]
  have hmul : M ^ 2 * (M + 2 * j) * Nat.choose (p * (M + j)) (p * M) ^ 3 ≡
      M ^ 2 * (M + 2 * j) * Nat.choose (M + j) M ^ 3 [MOD p ^ (3 * r)] := by
    have h1 := hcube.mul_left' (M ^ 2 * (M + 2 * j))
    have hdiv : p ^ (3 * r) ∣ (M ^ 2 * (M + 2 * j)) * p ^ (r + 2) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using dvd_mul_of_dvd_left hfactor (M + 2 * j)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h1.of_dvd hdiv
  have hcleared : (M + j) ^ 3 * oeis_361883_T (M * p) (p * j) ≡
      (M + j) ^ 3 * oeis_361883_T M j [MOD p ^ (3 * r)] := by
    rw [hclear_eq1, hclear_eq0]
    exact hmul
  have hcop : Nat.gcd (p ^ (3 * r)) ((M + j) ^ 3) = 1 := by
    rw [Nat.gcd_comm]
    exact (Nat.Coprime.pow_left 3 (Nat.Coprime.pow_right (3 * r)
      (((hp.coprime_iff_not_dvd).2 hpunit).symm)))
  exact Nat.ModEq.cancel_left_of_coprime hcop hcleared




/-- Split a range of length `M * p` into `M` consecutive blocks of length `p`. -/
lemma sum_range_mul_decomp_oeis_361883 {α : Type*} [AddCommMonoid α]
    (M p : ℕ) (F : ℕ → α) :
    Finset.sum (Finset.range (M * p)) F =
      Finset.sum (Finset.range M) (fun j =>
        Finset.sum (Finset.range p) (fun t => F (p * j + t))) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
      congr 1
      exact Finset.sum_congr rfl (by
        intro t ht
        congr 1
        rw [Nat.mul_comm p M])

/-- Split a range of length `M * p + 1` into full blocks and the final endpoint. -/
lemma sum_range_mul_succ_decomp_oeis_361883 {α : Type*} [AddCommMonoid α]
    (M p : ℕ) (F : ℕ → α) :
    Finset.sum (Finset.range (M * p + 1)) F =
      Finset.sum (Finset.range M) (fun j =>
        Finset.sum (Finset.range p) (fun t => F (p * j + t))) + F (M * p) := by
  rw [Finset.sum_range_succ, sum_range_mul_decomp_oeis_361883]

/-- Product analogue of `sum_range_mul_decomp_oeis_361883`: split a range of length `M*p`
into consecutive blocks. This is intended for product-expansion proofs of binomial congruences. -/
lemma prod_range_mul_decomp_oeis_361883 {α : Type*} [CommMonoid α]
    (M p : ℕ) (F : ℕ → α) :
    Finset.prod (Finset.range (M * p)) F =
      Finset.prod (Finset.range M) (fun j =>
        Finset.prod (Finset.range p) (fun t => F (p * j + t))) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Nat.succ_mul, Finset.prod_range_add, ih, Finset.prod_range_succ]
      congr 1
      exact Finset.prod_congr rfl (by
        intro t ht
        congr 1
        rw [Nat.mul_comm p M])



/-- If a positive multiple of `m` is reduced by one, its residue modulo `m` is `m - 1`. -/
lemma nat_mod_sub_one_of_dvd_oeis_361883 {m X : ℕ}
    (hm : 0 < m) (hX : 0 < X) (hdiv : m ∣ X) :
    (X - 1) % m = m - 1 := by
  rcases hdiv with ⟨c, rfl⟩
  have hc : 0 < c := by
    by_contra h
    have : c = 0 := Nat.eq_zero_of_not_pos h
    simp [this] at hX
  have hlt : m - 1 < m := Nat.sub_one_lt hm.ne'
  have hEq : m * c - 1 = m * (c - 1) + (m - 1) := by
    cases c with
    | zero => omega
    | succ c =>
        cases m with
        | zero => omega
        | succ m => simp [Nat.mul_add, Nat.add_mul]
  rw [hEq]
  rw [Nat.add_mod]
  simp [Nat.mul_mod_right, Nat.mod_eq_of_lt hlt]


/-- If `M` contains `p^(r-1)`, then `M * p` contains every `p^i`, `i ≤ r`. -/
lemma pow_dvd_mul_of_pred_pow_dvd_oeis_361883 {p M r i : ℕ} (hr : 0 < r)
    (hM : p ^ (r - 1) ∣ M) (hi : i ≤ r) : p ^ i ∣ M * p := by
  have hr_eq : r - 1 + 1 = r := Nat.succ_pred_eq_of_pos hr
  have hpr : p ^ r ∣ M * p := by
    rw [← hr_eq, pow_succ]
    exact mul_dvd_mul hM (dvd_refl p)
  exact (pow_dvd_pow p hi).trans hpr


/-- A number congruent to a nonzero `t < p` modulo `p` has positive residue modulo `p^i`. -/
lemma mod_pow_pos_of_add_unit_oeis_361883 {p j t i : ℕ}
    (hi : 0 < i) (ht0 : 0 < t) (htp : t < p) :
    0 < (p * j + t) % p ^ i := by
  have hp_dvd_pow : p ∣ p ^ i := by
    cases i with
    | zero => omega
    | succ i => rw [pow_succ]; exact dvd_mul_left p (p ^ i)
  have hnot : ¬ p ∣ p * j + t := by
    intro h
    have ht_dvd : p ∣ t := by
      have hmul : p ∣ p * j := dvd_mul_right p j
      exact (Nat.dvd_add_iff_right hmul).2 h
    exact (Nat.not_dvd_of_pos_of_lt ht0 htp) ht_dvd
  by_contra h
  have hzero : (p * j + t) % p ^ i = 0 := Nat.eq_zero_of_not_pos h
  have hdvd_pow : p ^ i ∣ p * j + t := by
    rwa [Nat.dvd_iff_mod_eq_zero]
  exact hnot (hp_dvd_pow.trans hdvd_pow)



/-- Kummer-theoretic forced divisibility of the off-diagonal binomial factor. -/
lemma offdiag_choose_dvd_oeis_361883 {p M r j t : ℕ} [Fact p.Prime]
    (hr : 0 < r) (hMpos : 0 < M) (hM : p ^ (r - 1) ∣ M)
    (ht0 : 0 < t) (htp : t < p) :
    p ^ r ∣ Nat.choose (M * p + (p * j + t) - 1) (M * p - 1) := by
  let Ntop := M * p + (p * j + t) - 1
  let K := M * p - 1
  have hpgt1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hp0 : 0 < p := by omega
  have hMp_pos : 0 < M * p := Nat.mul_pos hMpos hp0
  have hKle : K ≤ Ntop := by dsimp [K, Ntop]; omega
  have hchoose_ne : Nat.choose Ntop K ≠ 0 := Nat.choose_ne_zero hKle
  rw [padicValNat_dvd_iff_le hchoose_ne]
  let b := Nat.log p Ntop + 1
  have hnb : Nat.log p Ntop < b := by dsimp [b]; omega
  rw [padicValNat_choose (p := p) (n := Ntop) (k := K) (b := b) hKle hnb]
  have hpr_dvd : p ^ r ∣ M * p := pow_dvd_mul_of_pred_pow_dvd_oeis_361883 hr hM (le_refl r)
  have hpr_le_Mp : p ^ r ≤ M * p := Nat.le_of_dvd hMp_pos hpr_dvd
  have htop_ge : M * p ≤ Ntop := by dsimp [Ntop]; omega
  have hr_le_log : r ≤ Nat.log p Ntop := Nat.le_log_of_pow_le hpgt1 (hpr_le_Mp.trans htop_ge)
  have hsubset : Finset.Ico 1 (r + 1) ⊆
      (Finset.Ico 1 b).filter (fun i => p ^ i ≤ K % p ^ i + (Ntop - K) % p ^ i) := by
    intro i hi
    rw [Finset.mem_filter]
    have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have hir1 : i < r + 1 := (Finset.mem_Ico.mp hi).2
    have hir : i ≤ r := Nat.lt_succ_iff.mp hir1
    constructor
    · exact Finset.mem_Ico.mpr ⟨hi1, by dsimp [b]; omega⟩
    · have hpidvd : p ^ i ∣ M * p := pow_dvd_mul_of_pred_pow_dvd_oeis_361883 hr hM hir
      have hpip : 0 < p ^ i := pow_pos hp0 i
      have hKmod : K % p ^ i = p ^ i - 1 := by
        dsimp [K]
        exact nat_mod_sub_one_of_dvd_oeis_361883 hpip hMp_pos hpidvd
      have hNK : Ntop - K = p * j + t := by dsimp [Ntop, K]; omega
      have hposmod : 0 < (p * j + t) % p ^ i :=
        mod_pow_pos_of_add_unit_oeis_361883 (by omega : 0 < i) ht0 htp
      rw [hKmod, hNK]
      omega
  have hcard := Finset.card_le_card hsubset
  simpa [Nat.card_Ico] using hcard

/-- Consequently, each off-diagonal summand carries at least `p^(2*r)`. -/
lemma offdiag_T_dvd_oeis_361883 {p M r j t : ℕ} [Fact p.Prime]
    (hr : 0 < r) (hMpos : 0 < M) (hM : p ^ (r - 1) ∣ M)
    (ht0 : 0 < t) (htp : t < p) :
    p ^ (2 * r) ∣ oeis_361883_T (M * p) (p * j + t) := by
  let A := Nat.choose (M * p + (p * j + t) - 1) (M * p - 1)
  let C := Nat.choose (M * p + (p * j + t) - 1) (M * p)
  have hN : 0 < M * p := Nat.mul_pos hMpos (by
    have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
    omega)
  have hA : p ^ r ∣ A := by
    dsimp [A]
    exact offdiag_choose_dvd_oeis_361883 hr hMpos hM ht0 htp
  rcases hA with ⟨u, hu⟩
  rw [oeis_361883_T_eq_sq_mul (hN := hN)]
  dsimp [A, C] at hu ⊢
  rw [hu]
  use u ^ 2 * (u * p ^ r + 2 * Nat.choose (M * p + (p * j + t) - 1) (M * p))
  rw [pow_mul]
  ring_nf


/-- The number `2` is a unit modulo `p^r` for primes `p ≥ 5`. -/
lemma coprime_two_pow_prime_oeis_361883 {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Nat.Coprime 2 (p ^ r) := by
  exact Nat.Coprime.pow_right r ((Nat.coprime_primes (by norm_num : Nat.Prime 2) hp).2 (by omega))

/-- The number `3` is a unit modulo `p^r` for primes `p ≥ 5`. -/
lemma coprime_three_pow_prime_oeis_361883 {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Nat.Coprime 3 (p ^ r) := by
  exact Nat.Coprime.pow_right r ((Nat.coprime_primes (by norm_num : Nat.Prime 3) hp).2 (by omega))

/-- Sum of inverse squares over the unit group of `ZMod (p^r)` vanishes for `p ≥ 5`. -/
lemma sum_units_inv_sq_zmod_pow_eq_zero_oeis_361883 (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    letI : Fintype (ZMod (p ^ r))ˣ := Fintype.ofFinite (ZMod (p ^ r))ˣ
    (∑ u : (ZMod (p ^ r))ˣ, (((u : ZMod (p ^ r))⁻¹) ^ 2)) = 0 := by
  letI : Fintype (ZMod (p ^ r))ˣ := Fintype.ofFinite (ZMod (p ^ r))ˣ
  let R := ZMod (p ^ r)
  let two : Rˣ := ZMod.unitOfCoprime 2 (coprime_two_pow_prime_oeis_361883 hp hp5)
  let three : Rˣ := ZMod.unitOfCoprime 3 (coprime_three_pow_prime_oeis_361883 hp hp5)
  let f : Rˣ → R := fun u => (((u : R)⁻¹) ^ 2)
  let S : R := ∑ u : Rˣ, f u
  have hperm : S = ∑ u : Rˣ, f (two * u) := by
    dsimp [S]
    exact (Equiv.sum_comp (Equiv.mulLeft two) f).symm
  have hscale : S = ((two : R)⁻¹) ^ 2 * S := by
    calc
      S = ∑ u : Rˣ, f (two * u) := hperm
      _ = ∑ u : Rˣ, (((two : R)⁻¹) ^ 2 * f u) := by
        apply Finset.sum_congr rfl
        intro u hu
        dsimp [f]
        have hinv : (((two * u : Rˣ) : R))⁻¹ = (two : R)⁻¹ * (u : R)⁻¹ := by
          change ((((two * u : Rˣ) : R))⁻¹) = (two : R)⁻¹ * (u : R)⁻¹
          rw [ZMod.inv_coe_unit, ZMod.inv_coe_unit, ZMod.inv_coe_unit]
          rw [mul_inv_rev]
          simp [mul_comm]
        change ((((two * u : Rˣ) : R))⁻¹) ^ 2 = ((two : R)⁻¹) ^ 2 * ((u : R)⁻¹) ^ 2
        rw [hinv]
        ring
      _ = ((two : R)⁻¹) ^ 2 * S := by
        dsimp [S]
        rw [Finset.mul_sum]
  have h4 : ((two : R) ^ 2) * S = S := by
    calc
      ((two : R) ^ 2) * S = ((two : R) ^ 2) * (((two : R)⁻¹) ^ 2 * S) := by rw [← hscale]
      _ = S := by
        have hcoef : ((two : R) ^ 2) * ((two : R)⁻¹) ^ 2 = 1 := by
          rw [pow_two, pow_two]
          have hmul : (two : R) * (two : R)⁻¹ = 1 := Units.mul_inv two
          calc
            (two : R) * (two : R) * ((two : R)⁻¹ * (two : R)⁻¹)
                = ((two : R) * (two : R)⁻¹) * ((two : R) * (two : R)⁻¹) := by ring
            _ = 1 := by simp [hmul]
        rw [← mul_assoc, hcoef, one_mul]
  have h4' : ((2 : R) ^ 2) * S = S := by simpa [two] using h4
  have h3S : (three : R) * S = 0 := by
    have hsub : ((2 : R) ^ 2 - 1) * S = 0 := by
      rw [sub_mul, one_mul, h4', sub_self]
    simpa [three, pow_two, show (2 : R) * 2 - 1 = (3 : R) by norm_num] using hsub
  rw [mul_comm] at h3S
  exact (Units.mul_left_eq_zero three).mp h3S


/-- Sum of inverses over the unit group of `ZMod (p^r)` vanishes for odd primes.
This is the linear analogue of the inverse-square cancellation above. -/
lemma sum_units_inv_zmod_pow_eq_zero_oeis_361883 (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    letI : Fintype (ZMod (p ^ r))ˣ := Fintype.ofFinite (ZMod (p ^ r))ˣ
    (∑ u : (ZMod (p ^ r))ˣ, ((u : ZMod (p ^ r))⁻¹)) = 0 := by
  letI : Fintype (ZMod (p ^ r))ˣ := Fintype.ofFinite (ZMod (p ^ r))ˣ
  let R := ZMod (p ^ r)
  let two : Rˣ := ZMod.unitOfCoprime 2 (coprime_two_pow_prime_oeis_361883 hp hp5)
  let f : Rˣ → R := fun u => ((u : R)⁻¹)
  let S : R := ∑ u : Rˣ, f u
  have hperm : S = ∑ u : Rˣ, f (two * u) := by
    dsimp [S]
    exact (Equiv.sum_comp (Equiv.mulLeft two) f).symm
  have hscale : S = ((two : R)⁻¹) * S := by
    calc
      S = ∑ u : Rˣ, f (two * u) := hperm
      _ = ∑ u : Rˣ, ((two : R)⁻¹ * f u) := by
        apply Finset.sum_congr rfl
        intro u hu
        dsimp [f]
        have hinv : (((two * u : Rˣ) : R))⁻¹ = (two : R)⁻¹ * (u : R)⁻¹ := by
          change ((((two * u : Rˣ) : R))⁻¹) = (two : R)⁻¹ * (u : R)⁻¹
          rw [ZMod.inv_coe_unit, ZMod.inv_coe_unit, ZMod.inv_coe_unit]
          rw [mul_inv_rev]
          simp [mul_comm]
        exact hinv
      _ = ((two : R)⁻¹) * S := by
        dsimp [S]
        rw [Finset.mul_sum]
  have h2 : (two : R) * S = S := by
    calc
      (two : R) * S = (two : R) * ((two : R)⁻¹ * S) := by rw [← hscale]
      _ = S := by
        have hcoef : (two : R) * (two : R)⁻¹ = 1 := Units.mul_inv two
        rw [← mul_assoc, hcoef, one_mul]
  have hsub : ((2 : R) - 1) * S = 0 := by
    have h2' : (2 : R) * S = S := by simpa [two] using h2
    rw [sub_mul, one_mul, h2', sub_self]
  have hone : ((2 : R) - 1) = 1 := by norm_num
  simpa [S, f, R, hone] using hsub


/-- The number `7` is a unit modulo `p^r` for primes `p ≥ 5`, `p ≠ 7`. -/
lemma coprime_seven_pow_prime_oeis_361883 {p r : ℕ} (hp : p.Prime) (hp7 : p ≠ 7) :
    Nat.Coprime 7 (p ^ r) := by
  exact Nat.Coprime.pow_right r
    ((Nat.coprime_primes (by norm_num : Nat.Prime 7) hp).2 (by exact fun h => hp7 h.symm))

/-- Sum of inverse cubes over the unit group of `ZMod (p^r)` vanishes for primes `p ≥ 5`.
This follows by scaling by `2`, except at `p = 7`, where scaling by `3` is used. -/
lemma sum_units_inv_cube_zmod_pow_eq_zero_oeis_361883 (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    letI : Fintype (ZMod (p ^ r))ˣ := Fintype.ofFinite (ZMod (p ^ r))ˣ
    (∑ u : (ZMod (p ^ r))ˣ, (((u : ZMod (p ^ r))⁻¹) ^ 3)) = 0 := by
  letI : Fintype (ZMod (p ^ r))ˣ := Fintype.ofFinite (ZMod (p ^ r))ˣ
  let R := ZMod (p ^ r)
  by_cases hp7 : p = 7
  · subst p
    let three : Rˣ := ZMod.unitOfCoprime 3 (by
      exact Nat.Coprime.pow_right r (by norm_num : Nat.Coprime 3 7))
    let twentySix : Rˣ := ZMod.unitOfCoprime 26 (by
      exact Nat.Coprime.pow_right r (by norm_num : Nat.Coprime 26 7))
    let f : Rˣ → R := fun u => (((u : R)⁻¹) ^ 3)
    let S : R := ∑ u : Rˣ, f u
    have hperm : S = ∑ u : Rˣ, f (three * u) := by
      dsimp [S]
      exact (Equiv.sum_comp (Equiv.mulLeft three) f).symm
    have hscale : S = ((three : R)⁻¹) ^ 3 * S := by
      calc
        S = ∑ u : Rˣ, f (three * u) := hperm
        _ = ∑ u : Rˣ, (((three : R)⁻¹) ^ 3 * f u) := by
          apply Finset.sum_congr rfl
          intro u hu
          dsimp [f]
          have hinv : (((three * u : Rˣ) : R))⁻¹ = (three : R)⁻¹ * (u : R)⁻¹ := by
            change ((((three * u : Rˣ) : R))⁻¹) = (three : R)⁻¹ * (u : R)⁻¹
            rw [ZMod.inv_coe_unit, ZMod.inv_coe_unit, ZMod.inv_coe_unit]
            rw [mul_inv_rev]
            simp [mul_comm]
          have hinv' : ((three : R) * (u : R))⁻¹ = (three : R)⁻¹ * (u : R)⁻¹ := by
            simpa using hinv
          rw [hinv']
          ring
        _ = ((three : R)⁻¹) ^ 3 * S := by
          dsimp [S]
          rw [Finset.mul_sum]
    have h27 : ((three : R) ^ 3) * S = S := by
      calc
        ((three : R) ^ 3) * S = ((three : R) ^ 3) * (((three : R)⁻¹) ^ 3 * S) := by rw [← hscale]
        _ = S := by
          have hcoef : ((three : R) ^ 3) * ((three : R)⁻¹) ^ 3 = 1 := by
            rw [← mul_pow]
            have hmul : (three : R) * (three : R)⁻¹ = 1 := Units.mul_inv three
            rw [hmul, one_pow]
          rw [← mul_assoc, hcoef, one_mul]
    have hsub : (((3 : R) ^ 3 - 1) * S) = 0 := by
      have h27' : ((3 : R) ^ 3) * S = S := by simpa [three] using h27
      rw [sub_mul, one_mul, h27', sub_self]
    have h26S : (twentySix : R) * S = 0 := by
      simpa [twentySix, show ((3 : R) ^ 3 - 1) = (26 : R) by norm_num] using hsub
    rw [mul_comm] at h26S
    exact (Units.mul_left_eq_zero twentySix).mp h26S
  · let two : Rˣ := ZMod.unitOfCoprime 2 (coprime_two_pow_prime_oeis_361883 hp hp5)
    let seven : Rˣ := ZMod.unitOfCoprime 7 (coprime_seven_pow_prime_oeis_361883 hp hp7)
    let f : Rˣ → R := fun u => (((u : R)⁻¹) ^ 3)
    let S : R := ∑ u : Rˣ, f u
    have hperm : S = ∑ u : Rˣ, f (two * u) := by
      dsimp [S]
      exact (Equiv.sum_comp (Equiv.mulLeft two) f).symm
    have hscale : S = ((two : R)⁻¹) ^ 3 * S := by
      calc
        S = ∑ u : Rˣ, f (two * u) := hperm
        _ = ∑ u : Rˣ, (((two : R)⁻¹) ^ 3 * f u) := by
          apply Finset.sum_congr rfl
          intro u hu
          dsimp [f]
          have hinv : (((two * u : Rˣ) : R))⁻¹ = (two : R)⁻¹ * (u : R)⁻¹ := by
            change ((((two * u : Rˣ) : R))⁻¹) = (two : R)⁻¹ * (u : R)⁻¹
            rw [ZMod.inv_coe_unit, ZMod.inv_coe_unit, ZMod.inv_coe_unit]
            rw [mul_inv_rev]
            simp [mul_comm]
          have hinv' : ((two : R) * (u : R))⁻¹ = (two : R)⁻¹ * (u : R)⁻¹ := by
            simpa using hinv
          rw [hinv']
          ring
        _ = ((two : R)⁻¹) ^ 3 * S := by
          dsimp [S]
          rw [Finset.mul_sum]
    have h8 : ((two : R) ^ 3) * S = S := by
      calc
        ((two : R) ^ 3) * S = ((two : R) ^ 3) * (((two : R)⁻¹) ^ 3 * S) := by rw [← hscale]
        _ = S := by
          have hcoef : ((two : R) ^ 3) * ((two : R)⁻¹) ^ 3 = 1 := by
            rw [← mul_pow]
            have hmul : (two : R) * (two : R)⁻¹ = 1 := Units.mul_inv two
            rw [hmul, one_pow]
          rw [← mul_assoc, hcoef, one_mul]
    have hsub : (((2 : R) ^ 3 - 1) * S) = 0 := by
      have h8' : ((2 : R) ^ 3) * S = S := by simpa [two] using h8
      rw [sub_mul, one_mul, h8', sub_self]
    have h7S : (seven : R) * S = 0 := by
      simpa [seven, show ((2 : R) ^ 3 - 1) = (7 : R) by norm_num] using hsub
    rw [mul_comm] at h7S
    exact (Units.mul_left_eq_zero seven).mp h7S

/-- Reindex a sum over units of `ZMod (p^r)` as a sum over coprime natural representatives. -/
lemma sum_range_coprime_inv_pow_eq_sum_units_oeis_361883 (p r m : ℕ) (hp : p.Prime) :
    letI : Fintype (ZMod (p ^ r))ˣ := Fintype.ofFinite (ZMod (p ^ r))ˣ
    (∑ x ∈ (Finset.range (p ^ r)).filter (fun x => Nat.Coprime x (p ^ r)),
      ((x : ZMod (p ^ r))⁻¹) ^ m) =
    (∑ u : (ZMod (p ^ r))ˣ, (((u : ZMod (p ^ r))⁻¹) ^ m)) := by
  letI : Fintype (ZMod (p ^ r))ˣ := Fintype.ofFinite (ZMod (p ^ r))ˣ
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  symm
  refine Finset.sum_bij (fun u _ => (u : ZMod (p ^ r)).val) ?mem ?inj ?surj ?eq
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime u⟩
  · intro u v hu hv hval
    exact Units.ext (ZMod.val_injective (n := p ^ r) (by simpa using hval))
  · intro x hx
    have hxrange : x < p ^ r := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hxc : Nat.Coprime x (p ^ r) := (Finset.mem_filter.mp hx).2
    refine ⟨ZMod.unitOfCoprime x hxc, Finset.mem_univ _, ?_⟩
    simp [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hxrange]
  · intro u hu
    have hcast : (((u : ZMod (p ^ r)).val : ZMod (p ^ r)) = (u : ZMod (p ^ r))) := by
      rw [ZMod.natCast_zmod_val]
    rw [hcast]

/-- Sum of inverse first powers over coprime representatives modulo `p^r` vanishes. -/
lemma sum_range_coprime_inv_zmod_pow_eq_zero_oeis_361883 (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ x ∈ (Finset.range (p ^ r)).filter (fun x => Nat.Coprime x (p ^ r)),
      ((x : ZMod (p ^ r))⁻¹)) = 0 := by
  letI : Fintype (ZMod (p ^ r))ˣ := Fintype.ofFinite (ZMod (p ^ r))ˣ
  have h := sum_range_coprime_inv_pow_eq_sum_units_oeis_361883 (p := p) (r := r) (m := 1) hp
  have hz := sum_units_inv_zmod_pow_eq_zero_oeis_361883 p r hp hp5
  have hz1 : (∑ u : (ZMod (p ^ r))ˣ, (((u : ZMod (p ^ r))⁻¹) ^ 1)) = 0 := by
    simpa [pow_one] using hz
  simpa [pow_one] using h.trans hz1

/-- Sum of inverse squares over coprime representatives modulo `p^r` vanishes. -/
lemma sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ x ∈ (Finset.range (p ^ r)).filter (fun x => Nat.Coprime x (p ^ r)),
      ((x : ZMod (p ^ r))⁻¹) ^ 2) = 0 := by
  have h := sum_range_coprime_inv_pow_eq_sum_units_oeis_361883 (p := p) (r := r) (m := 2) hp
  have hz := sum_units_inv_sq_zmod_pow_eq_zero_oeis_361883 p r hp hp5
  simpa using h.trans hz

/-- Sum of inverse cubes over coprime representatives modulo `p^r` vanishes. -/
lemma sum_range_coprime_inv_cube_zmod_pow_eq_zero_oeis_361883 (p r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ x ∈ (Finset.range (p ^ r)).filter (fun x => Nat.Coprime x (p ^ r)),
      ((x : ZMod (p ^ r))⁻¹) ^ 3) = 0 := by
  have h := sum_range_coprime_inv_pow_eq_sum_units_oeis_361883 (p := p) (r := r) (m := 3) hp
  have hz := sum_units_inv_cube_zmod_pow_eq_zero_oeis_361883 p r hp hp5
  simpa using h.trans hz

/-- A shifted full set of coprime representatives has zero inverse-square sum modulo `p^r`. -/
lemma sum_range_coprime_shift_inv_sq_zmod_pow_eq_zero_oeis_361883
    (p r b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ x ∈ (Finset.range (p ^ r)).filter (fun x => Nat.Coprime x (p ^ r)),
      (((p ^ r * b + x : ℕ) : ZMod (p ^ r))⁻¹) ^ 2) = 0 := by
  calc
    (∑ x ∈ (Finset.range (p ^ r)).filter (fun x => Nat.Coprime x (p ^ r)),
      (((p ^ r * b + x : ℕ) : ZMod (p ^ r))⁻¹) ^ 2)
        = ∑ x ∈ (Finset.range (p ^ r)).filter (fun x => Nat.Coprime x (p ^ r)),
            ((x : ZMod (p ^ r))⁻¹) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          have h : ((p ^ r * b + x : ℕ) : ZMod (p ^ r)) = (x : ZMod (p ^ r)) := by
            simp
          rw [h]
    _ = 0 := sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p r hp hp5

/-- A shifted full set of coprime representatives has zero inverse-cube sum modulo `p^r`. -/
lemma sum_range_coprime_shift_inv_cube_zmod_pow_eq_zero_oeis_361883
    (p r b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ x ∈ (Finset.range (p ^ r)).filter (fun x => Nat.Coprime x (p ^ r)),
      (((p ^ r * b + x : ℕ) : ZMod (p ^ r))⁻¹) ^ 3) = 0 := by
  calc
    (∑ x ∈ (Finset.range (p ^ r)).filter (fun x => Nat.Coprime x (p ^ r)),
      (((p ^ r * b + x : ℕ) : ZMod (p ^ r))⁻¹) ^ 3)
        = ∑ x ∈ (Finset.range (p ^ r)).filter (fun x => Nat.Coprime x (p ^ r)),
            ((x : ZMod (p ^ r))⁻¹) ^ 3 := by
          apply Finset.sum_congr rfl
          intro x hx
          have h : ((p ^ r * b + x : ℕ) : ZMod (p ^ r)) = (x : ZMod (p ^ r)) := by
            simp
          rw [h]
    _ = 0 := sum_range_coprime_inv_cube_zmod_pow_eq_zero_oeis_361883 p r hp hp5



/-- Truncated product expansion for factors `1 + δ f i` when `δ^3 = 0`.
The quadratic term is written as the ordered elementary symmetric sum. -/
lemma finset_prod_one_add_nilpotent_order3_oeis_361883
    {α R : Type*} [LinearOrder α] [CommRing R]
    (s : Finset α) (δ : R) (f : α → R) (hδ3 : δ ^ 3 = 0) :
    (∏ i ∈ s, (1 + δ * f i)) =
      1 + δ * (∑ i ∈ s, f i) +
        δ ^ 2 * (∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), f j * f i) := by
  classical
  refine Finset.induction_on_max s ?h0 ?step
  · simp
  · intro a s hmax ih
    have ha : a ∉ s := by
      intro has
      exact (lt_irrefl a) (hmax a has)
    rw [Finset.prod_insert ha, ih]
    have hsum_insert : (∑ i ∈ insert a s, f i) = f a + ∑ i ∈ s, f i := by
      simp [ha]
    have hpair_insert :
        (∑ i ∈ insert a s, ∑ j ∈ (insert a s).filter (fun j => j < i), f j * f i) =
          (∑ j ∈ s, f j) * f a +
            (∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), f j * f i) := by
      rw [Finset.sum_insert ha]
      congr 1
      · have hfilter : (insert a s).filter (fun j => j < a) = s := by
          ext k
          by_cases hks : k ∈ s
          · simp [hks, hmax k hks]
          · by_cases hka : k = a
            · subst hka
              simp [ha]
            · simp [hks, hka]
        rw [hfilter]
        rw [Finset.sum_mul]
      · apply Finset.sum_congr rfl
        intro i hi
        have hfilter : (insert a s).filter (fun j => j < i) = s.filter (fun j => j < i) := by
          ext k
          by_cases hks : k ∈ s
          · simp [hks]
          · by_cases hka : k = a
            · have hia : i < a := hmax i hi
              simp [hka, not_lt_of_gt hia]
            · simp [hks, hka]
        rw [hfilter]
    rw [hsum_insert, hpair_insert]
    ring_nf
    rw [hδ3]
    ring

/-- Natural representatives coprime to `p^2` are units modulo `p^6`. -/
lemma coprime_p_sq_isUnit_zmod_p6_oeis_361883 {p x : ℕ} (hp : p.Prime)
    (hx : Nat.Coprime x (p ^ 2)) : IsUnit (x : ZMod (p ^ 6)) := by
  have hxp : Nat.Coprime x p := Nat.Coprime.of_dvd_right (by exact dvd_pow_self p (by norm_num : 2 ≠ 0)) hx
  have hnot : ¬ p ∣ x := (hp.coprime_iff_not_dvd).mp hxp.symm
  exact (ZMod.isUnit_iff_coprime _ _).2 (hp.coprime_pow_of_not_dvd hnot)

/-- Unit rewrite for one shifted factor in the superblock. -/
lemma superblock_shift_factor_eq_mul_one_add_oeis_361883 {p b x : ℕ} (hp : p.Prime)
    (hx : Nat.Coprime x (p ^ 2)) :
    (((p ^ 2 * b + x : ℕ) : ZMod (p ^ 6))) =
      ((x : ℕ) : ZMod (p ^ 6)) *
        (1 + (((p ^ 2 * b : ℕ) : ZMod (p ^ 6))) * (((x : ℕ) : ZMod (p ^ 6))⁻¹)) := by
  let R := ZMod (p ^ 6)
  have hunit : IsUnit ((x : ℕ) : R) := coprime_p_sq_isUnit_zmod_p6_oeis_361883 (p := p) hp hx
  rcases hunit with ⟨u, hu⟩
  have hmul : ((x : ℕ) : R) * (((x : ℕ) : R)⁻¹) = 1 := by
    rw [← hu, ZMod.inv_coe_unit]
    exact Units.mul_inv u
  change (((p ^ 2 * b + x : ℕ) : R)) =
      ((x : ℕ) : R) * (1 + (((p ^ 2 * b : ℕ) : R)) * (((x : ℕ) : R)⁻¹))
  rw [Nat.cast_add]
  calc
    (((p ^ 2 * b : ℕ) : R) + ((x : ℕ) : R)) =
        ((x : ℕ) : R) + ((p ^ 2 * b : ℕ) : R) := by ring
    _ = ((x : ℕ) : R) * (1 + (((p ^ 2 * b : ℕ) : R)) * (((x : ℕ) : R)⁻¹)) := by
      rw [mul_add, mul_one]
      calc
        ((x : ℕ) : R) + ((p ^ 2 * b : ℕ) : R) =
            ((x : ℕ) : R) + ((p ^ 2 * b : ℕ) : R) * (((x : ℕ) : R) * (((x : ℕ) : R)⁻¹)) := by
              rw [hmul, mul_one]
        _ = ((x : ℕ) : R) + ((x : ℕ) : R) * (((p ^ 2 * b : ℕ) : R) * (((x : ℕ) : R)⁻¹)) := by
              ring

/-- In `ZMod (p^6)`, a class reducing to zero modulo `p^2` is killed by `p^4`. -/
lemma zmod_p4_mul_eq_zero_of_castHom_p2_eq_zero_oeis_361883 {p : ℕ} (hp : p.Prime)
    (x : ZMod (p ^ 6))
    (hx : ZMod.castHom (show p ^ 2 ∣ p ^ 6 by exact pow_dvd_pow p (by norm_num : 2 ≤ 6))
        (ZMod (p ^ 2)) x = 0) :
    (p ^ 4 : ZMod (p ^ 6)) * x = 0 := by
  haveI : NeZero (p ^ 6) := ⟨pow_ne_zero 6 hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x]
  have hxval0 : ((x.val : ℕ) : ZMod (p ^ 2)) = 0 := by
    simpa [ZMod.castHom_apply] using hx
  have hxdiv : p ^ 2 ∣ x.val := (ZMod.natCast_eq_zero_iff x.val (p ^ 2)).1 hxval0
  rcases hxdiv with ⟨y, hy⟩
  rw [hy, Nat.cast_mul]
  have hzero : ((p ^ 6 : ℕ) : ZMod (p ^ 6)) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (p ^ 6) (p ^ 6)).2 (dvd_refl _)
  calc
    ((p : ZMod (p ^ 6)) ^ 4) * ((((p ^ 2 : ℕ) : ZMod (p ^ 6))) * (y : ZMod (p ^ 6)))
        = (y : ZMod (p ^ 6)) * ((p ^ 6 : ℕ) : ZMod (p ^ 6)) := by
          rw [show (((p ^ 2 : ℕ) : ZMod (p ^ 6))) = (p : ZMod (p ^ 6)) ^ 2 by rw [Nat.cast_pow]]
          ring_nf
          rw [Nat.cast_pow]
          exact mul_comm (((p : ZMod (p ^ 6)) ^ 6)) (y : ZMod (p ^ 6))
    _ = 0 := by rw [hzero, mul_zero]

/-- Reduction from `ZMod (p^6)` to `ZMod (p^2)` commutes with inverses of representatives
coprime to `p^2`. -/
lemma zmod_castHom_inv_p6_to_p2_of_coprime_oeis_361883 {p x : ℕ} (hp : p.Prime)
    (hx : Nat.Coprime x (p ^ 2)) :
    ZMod.castHom (show p ^ 2 ∣ p ^ 6 by exact pow_dvd_pow p (by norm_num : 2 ≤ 6))
      (ZMod (p ^ 2)) (((x : ℕ) : ZMod (p ^ 6))⁻¹) =
      (((x : ℕ) : ZMod (p ^ 2))⁻¹) := by
  let R := ZMod (p ^ 6)
  let S := ZMod (p ^ 2)
  let f := ZMod.castHom (show p ^ 2 ∣ p ^ 6 by exact pow_dvd_pow p (by norm_num : 2 ≤ 6)) S
  have hxp : Nat.Coprime x p := Nat.Coprime.of_dvd_right
    (by exact dvd_pow_self p (by norm_num : 2 ≠ 0)) hx
  have hnot : ¬ p ∣ x := (hp.coprime_iff_not_dvd).mp hxp.symm
  have hcopR : Nat.Coprime x (p ^ 6) := hp.coprime_pow_of_not_dvd hnot
  let uR : Rˣ := ZMod.unitOfCoprime x hcopR
  let uS : Sˣ := ZMod.unitOfCoprime x hx
  have hmapu : Units.map f.toMonoidHom uR = uS := by
    apply Units.ext
    change f (x : R) = (x : S)
    simp [f]
  have hmapinv : f ((uR⁻¹ : Rˣ) : R) = ((uS⁻¹ : Sˣ) : S) := by
    calc
      f ((uR⁻¹ : Rˣ) : R) = ((Units.map f.toMonoidHom uR)⁻¹ : Sˣ) := by
        exact (Units.coe_map_inv f.toMonoidHom uR).symm
      _ = ((uS⁻¹ : Sˣ) : S) := by rw [hmapu]
  have hinvR : ((x : R)⁻¹) = ((uR⁻¹ : Rˣ) : R) := by
    simpa [uR] using ZMod.inv_coe_unit uR
  have hinvS : ((x : S)⁻¹) = ((uS⁻¹ : Sˣ) : S) := by
    simpa [uS] using ZMod.inv_coe_unit uS
  calc
    f (((x : ℕ) : R)⁻¹) = f ((uR⁻¹ : Rˣ) : R) := by rw [hinvR]
    _ = ((uS⁻¹ : Sˣ) : S) := hmapinv
    _ = (((x : ℕ) : S)⁻¹) := by rw [hinvS]

/-- Square of a finite sum split into diagonal terms and ordered off-diagonal pairs. -/
lemma finset_sum_sq_eq_diag_add_two_ordered_pairs_oeis_361883
    {α R : Type*} [LinearOrder α] [CommRing R]
    (s : Finset α) (f : α → R) :
    (∑ i ∈ s, f i) ^ 2 =
      (∑ i ∈ s, (f i) ^ 2) +
        2 * (∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), f j * f i) := by
  classical
  refine Finset.induction_on_max s ?h0 ?step
  · simp
  · intro a s hmax ih
    have ha : a ∉ s := by
      intro has
      exact (lt_irrefl a) (hmax a has)
    have hsum_insert : (∑ i ∈ insert a s, f i) = f a + ∑ i ∈ s, f i := by
      simp [ha]
    have hdiag_insert : (∑ i ∈ insert a s, (f i) ^ 2) = (f a) ^ 2 + ∑ i ∈ s, (f i) ^ 2 := by
      simp [ha]
    have hpair_insert :
        (∑ i ∈ insert a s, ∑ j ∈ (insert a s).filter (fun j => j < i), f j * f i) =
          (∑ j ∈ s, f j) * f a +
            (∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), f j * f i) := by
      rw [Finset.sum_insert ha]
      congr 1
      · have hfilter : (insert a s).filter (fun j => j < a) = s := by
          ext k
          by_cases hks : k ∈ s
          · simp [hks, hmax k hks]
          · by_cases hka : k = a
            · subst hka
              simp [ha]
            · simp [hks, hka]
        rw [hfilter]
        rw [Finset.sum_mul]
      · apply Finset.sum_congr rfl
        intro i hi
        have hfilter : (insert a s).filter (fun j => j < i) = s.filter (fun j => j < i) := by
          ext k
          by_cases hks : k ∈ s
          · simp [hks]
          · by_cases hka : k = a
            · have hia : i < a := hmax i hi
              simp [hka, not_lt_of_gt hia]
            · simp [hks, hka]
        rw [hfilter]
    rw [hsum_insert, hdiag_insert, hpair_insert]
    calc
      (f a + ∑ i ∈ s, f i) ^ 2 =
          (f a) ^ 2 + 2 * (∑ i ∈ s, f i) * f a + (∑ i ∈ s, f i) ^ 2 := by
        ring
      _ = (f a) ^ 2 + ∑ i ∈ s, (f i) ^ 2 +
            2 * ((∑ j ∈ s, f j) * f a +
              ∑ i ∈ s, ∑ j ∈ s.filter (fun j => j < i), f j * f i) := by
        rw [ih]
        ring

/-- The quadratic ordered inverse-pair sum in the `p^2` superblock is annihilated by the
square of the shift in `ZMod (p^6)`. -/
lemma unit_superblock_shift_zmod_p6_hS2_oeis_361883 {p b : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
  ((((p ^ 2 * b : ℕ) : ZMod (p ^ 6))) ^ 2) *
    (∑ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
      ∑ y ∈ ((Finset.range (p ^ 2)).filter (fun y => Nat.Coprime y (p ^ 2))).filter (fun y => y < x),
        (((y : ℕ) : ZMod (p ^ 6))⁻¹) * (((x : ℕ) : ZMod (p ^ 6))⁻¹)) = 0 := by
  classical
  let R := ZMod (p ^ 6)
  let S := ZMod (p ^ 2)
  let s := (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2))
  let fR : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  let fS : ℕ → S := fun x => (((x : ℕ) : S)⁻¹)
  let E : R := ∑ x ∈ s, ∑ y ∈ s.filter (fun y => y < x), fR y * fR x
  let D : R := ∑ x ∈ s, (fR x) ^ 2
  let A : R := ∑ x ∈ s, fR x
  let phi := ZMod.castHom (show p ^ 2 ∣ p ^ 6 by exact pow_dvd_pow p (by norm_num : 2 ≤ 6)) S
  have hphi_f (x : ℕ) (hxmem : x ∈ s) : phi (fR x) = fS x := by
    have hxc : Nat.Coprime x (p ^ 2) := (Finset.mem_filter.mp hxmem).2
    simpa [phi, fR, fS, R, S] using
      zmod_castHom_inv_p6_to_p2_of_coprime_oeis_361883 (p := p) (x := x) hp hxc
  have hphi_A : phi A = 0 := by
    calc
      phi A = ∑ x ∈ s, fS x := by
        dsimp [A]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hxmem
        simpa using hphi_f x hxmem
      _ = 0 := by
        dsimp [s, fS, S]
        exact sum_range_coprime_inv_zmod_pow_eq_zero_oeis_361883 p 2 hp hp5
  have hphi_D : phi D = 0 := by
    calc
      phi D = ∑ x ∈ s, (fS x) ^ 2 := by
        dsimp [D]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hxmem
        rw [map_pow]
        rw [hphi_f x hxmem]
      _ = 0 := by
        dsimp [s, fS, S]
        exact sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p 2 hp hp5
  have hkill_A_sq : (p ^ 4 : R) * (A ^ 2) = 0 := by
    apply zmod_p4_mul_eq_zero_of_castHom_p2_eq_zero_oeis_361883 (p := p) hp
    rw [map_pow, hphi_A, zero_pow (by norm_num : 2 ≠ 0)]
  have hkill_D : (p ^ 4 : R) * D = 0 := by
    apply zmod_p4_mul_eq_zero_of_castHom_p2_eq_zero_oeis_361883 (p := p) hp
    exact hphi_D
  have hpair_id : A ^ 2 = D + 2 * E := by
    dsimp [A, D, E, fR, s]
    exact finset_sum_sq_eq_diag_add_two_ordered_pairs_oeis_361883
      ((Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)))
      (fun x => (((x : ℕ) : R)⁻¹))
  have htwo_mul : (2 : R) * ((p ^ 4 : R) * E) = 0 := by
    have hcalc : (p ^ 4 : R) * (A ^ 2) = (p ^ 4 : R) * D + (2 : R) * ((p ^ 4 : R) * E) := by
      rw [hpair_id]
      ring
    have hsub : (p ^ 4 : R) * (A ^ 2) - (p ^ 4 : R) * D = (2 : R) * ((p ^ 4 : R) * E) := by
      rw [hcalc]
      ring
    rw [← hsub, hkill_A_sq, hkill_D]
    ring
  have htwo_unit : IsUnit (2 : R) := by
    apply (ZMod.isUnit_iff_coprime 2 (p ^ 6)).2
    have hpodd : Nat.Coprime 2 p := by
      have hp_ne_two : p ≠ 2 := by omega
      exact (Nat.coprime_primes (by norm_num : Nat.Prime 2) hp).2 (fun h => hp_ne_two h.symm)
    exact Nat.Coprime.pow_right 6 hpodd
  have hkill_E : (p ^ 4 : R) * E = 0 := by
    rcases htwo_unit with ⟨u, hu⟩
    have h : (u : R) * ((p ^ 4 : R) * E) = 0 := by
      simpa [hu] using htwo_mul
    have h' : ((p ^ 4 : R) * E) * (u : R) = 0 := by
      simpa [mul_comm] using h
    exact (Units.mul_left_eq_zero u).mp h'
  change (((p ^ 2 * b : ℕ) : R) ^ 2) * E = 0
  calc
    (((p ^ 2 * b : ℕ) : R) ^ 2) * E = (b ^ 2 : R) * ((p ^ 4 : R) * E) := by
      rw [Nat.cast_mul]
      rw [show (((p ^ 2 : ℕ) : R)) = (p : R) ^ 2 by rw [Nat.cast_pow]]
      ring
    _ = 0 := by rw [hkill_E, mul_zero]


/-- The linear inverse-sum term in the `p^2` superblock is annihilated by the shift in
`ZMod (p^6)`.  Pairing each unit representative `x` with `p^2 - x` shows that the sum is
`p^2/2` times a product of paired inverses; the latter product-sum reduces modulo `p^2` to
minus the inverse-square sum, hence is killed by the remaining `p^4`. -/
lemma unit_superblock_shift_zmod_p6_hS1_oeis_361883 {p b : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
  (((p ^ 2 * b : ℕ) : ZMod (p ^ 6))) *
    (∑ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
      (((x : ℕ) : ZMod (p ^ 6))⁻¹)) = 0 := by
  classical
  let R := ZMod (p ^ 6)
  let S := ZMod (p ^ 2)
  let s := (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2))
  let c : ℕ → ℕ := fun x => p ^ 2 - x
  let fR : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  let fS : ℕ → S := fun x => (((x : ℕ) : S)⁻¹)
  let A : R := ∑ x ∈ s, fR x
  let T : R := ∑ x ∈ s, fR x * fR (c x)
  let phi := ZMod.castHom (show p ^ 2 ∣ p ^ 6 by exact pow_dvd_pow p (by norm_num : 2 ≤ 6)) S
  have hs_mem_data {x : ℕ} (hx : x ∈ s) : x < p ^ 2 ∧ Nat.Coprime x (p ^ 2) := by
    have h := Finset.mem_filter.mp hx
    exact ⟨Finset.mem_range.mp h.1, h.2⟩
  have hp2_gt_one : 1 < p ^ 2 := by nlinarith [hp5]
  have hpos_of_mem {x : ℕ} (hx : x ∈ s) : 0 < x := by
    have hxc : Nat.Coprime x (p ^ 2) := (hs_mem_data hx).2
    by_contra hx0
    have hxz : x = 0 := Nat.eq_zero_of_not_pos hx0
    subst hxz
    have hbad : p ^ 2 = 1 := by simpa [Nat.Coprime] using hxc
    have hp2gt : 1 < p ^ 2 := by nlinarith [hp5]
    omega
  have hc_mem {x : ℕ} (hx : x ∈ s) : c x ∈ s := by
    have hxlt : x < p ^ 2 := (hs_mem_data hx).1
    have hxc : Nat.Coprime x (p ^ 2) := (hs_mem_data hx).2
    have hxpos : 0 < x := hpos_of_mem hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · dsimp [c]
      omega
    · dsimp [c]
      exact (Nat.coprime_self_sub_left (show x ≤ p ^ 2 by omega)).2 hxc
  have hc_invol {x : ℕ} (hx : x ∈ s) : c (c x) = x := by
    have hxlt : x < p ^ 2 := (hs_mem_data hx).1
    have hxpos : 0 < x := hpos_of_mem hx
    dsimp [c]
    omega
  have hcast_sum {x : ℕ} (hx : x ∈ s) :
      ((x : R) + ((c x : ℕ) : R)) = ((p ^ 2 : ℕ) : R) := by
    have hxlt : x < p ^ 2 := (hs_mem_data hx).1
    have hnat : x + (p ^ 2 - x) = p ^ 2 := Nat.add_sub_of_le (show x ≤ p ^ 2 by omega)
    dsimp [c]
    rw [← Nat.cast_add, hnat]
  have hpair_inv {x : ℕ} (hx : x ∈ s) :
      fR x + fR (c x) = ((p ^ 2 : ℕ) : R) * fR x * fR (c x) := by
    have hxc : Nat.Coprime x (p ^ 2) := (hs_mem_data hx).2
    have hcc : Nat.Coprime (c x) (p ^ 2) := (hs_mem_data (hc_mem hx)).2
    have hxunit : IsUnit ((x : ℕ) : R) := coprime_p_sq_isUnit_zmod_p6_oeis_361883 (p := p) hp hxc
    have hcunit : IsUnit (((c x : ℕ) : R)) := coprime_p_sq_isUnit_zmod_p6_oeis_361883 (p := p) hp hcc
    rcases hxunit with ⟨ux, hux⟩
    rcases hcunit with ⟨uc, huc⟩
    have hxmul : ((x : ℕ) : R) * fR x = 1 := by
      dsimp [fR]
      rw [← hux, ZMod.inv_coe_unit]
      exact Units.mul_inv ux
    have hcmul : (((c x : ℕ) : R)) * fR (c x) = 1 := by
      dsimp [fR]
      rw [← huc, ZMod.inv_coe_unit]
      exact Units.mul_inv uc
    have hmain : (((x : ℕ) : R) + ((c x : ℕ) : R)) * fR x * fR (c x) = fR x + fR (c x) := by
      calc
        (((x : ℕ) : R) + ((c x : ℕ) : R)) * fR x * fR (c x)
            = (((x : ℕ) : R) * fR x) * fR (c x) + (((c x : ℕ) : R) * fR (c x)) * fR x := by ring
        _ = fR x + fR (c x) := by rw [hxmul, hcmul]; ring
    rw [← hmain, hcast_sum hx]
  have hA_comp : A = ∑ x ∈ s, fR (c x) := by
    dsimp [A]
    refine Finset.sum_bij (fun x _ => c x) ?_ ?_ ?_ ?_
    · intro x hx
      exact hc_mem hx
    · intro x hx y hy hxy
      have hxlt : x < p ^ 2 := (hs_mem_data hx).1
      have hylt : y < p ^ 2 := (hs_mem_data hy).1
      dsimp [c] at hxy
      omega
    · intro y hy
      refine ⟨c y, hc_mem hy, ?_⟩
      exact hc_invol hy
    · intro x hx
      rw [hc_invol hx]
  have htwoA : (2 : R) * A = ((p ^ 2 : ℕ) : R) * T := by
    calc
      (2 : R) * A = A + A := by ring
      _ = (∑ x ∈ s, fR x) + A := by rfl
      _ = (∑ x ∈ s, fR x) + (∑ x ∈ s, fR (c x)) := by rw [hA_comp]
      _ = ∑ x ∈ s, (fR x + fR (c x)) := by rw [Finset.sum_add_distrib]
      _ = ∑ x ∈ s, (((p ^ 2 : ℕ) : R) * fR x * fR (c x)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hpair_inv hx
      _ = ((p ^ 2 : ℕ) : R) * T := by
        dsimp [T]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
  have hphi_f {x : ℕ} (hxmem : x ∈ s) : phi (fR x) = fS x := by
    have hxc : Nat.Coprime x (p ^ 2) := (hs_mem_data hxmem).2
    simpa [phi, fR, fS, R, S] using
      zmod_castHom_inv_p6_to_p2_of_coprime_oeis_361883 (p := p) (x := x) hp hxc
  have hphi_T : phi T = 0 := by
    calc
      phi T = ∑ x ∈ s, fS x * fS (c x) := by
        dsimp [T]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [map_mul, hphi_f hx, hphi_f (hc_mem hx)]
      _ = ∑ x ∈ s, - (fS x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt : x < p ^ 2 := (hs_mem_data hx).1
        have hnat : x + (p ^ 2 - x) = p ^ 2 := Nat.add_sub_of_le (show x ≤ p ^ 2 by omega)
        have hsum0 : ((x : ℕ) : S) + ((c x : ℕ) : S) = 0 := by
          dsimp [c]
          rw [← Nat.cast_add, hnat]
          simp [S]
        have hc_eq_neg : ((c x : ℕ) : S) = - ((x : ℕ) : S) := by
          exact eq_neg_of_add_eq_zero_right hsum0
        have hf_neg : fS (c x) = - fS x := by
          dsimp [fS]
          rw [hc_eq_neg]
          have hxc : Nat.Coprime x (p ^ 2) := (hs_mem_data hx).2
          have hxunitS : IsUnit ((x : ℕ) : S) := by
            exact (ZMod.isUnit_iff_coprime x (p ^ 2)).2 hxc
          rcases hxunitS with ⟨u, hu⟩
          rw [← hu, ZMod.inv_coe_unit]
          change (-(u : S))⁻¹ = -↑(u⁻¹)
          rw [show -(u : S) = ((-u : Sˣ) : S) by rfl]
          rw [ZMod.inv_coe_unit]
          rfl
        rw [hf_neg]
        ring
      _ = - (∑ x ∈ s, (fS x) ^ 2) := by rw [Finset.sum_neg_distrib]
      _ = 0 := by
        dsimp [s, fS, S]
        rw [sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p 2 hp hp5, neg_zero]
  have hkill_T : (p ^ 4 : R) * T = 0 := by
    apply zmod_p4_mul_eq_zero_of_castHom_p2_eq_zero_oeis_361883 (p := p) hp
    exact hphi_T
  have htwo_goal : (2 : R) * ((((p ^ 2 * b : ℕ) : R)) * A) = 0 := by
    calc
      (2 : R) * ((((p ^ 2 * b : ℕ) : R)) * A)
          = (((p ^ 2 * b : ℕ) : R)) * ((2 : R) * A) := by ring
      _ = (((p ^ 2 * b : ℕ) : R)) * (((p ^ 2 : ℕ) : R) * T) := by rw [htwoA]
      _ = (b : R) * ((p ^ 4 : R) * T) := by
        rw [Nat.cast_mul]
        rw [show (((p ^ 2 : ℕ) : R)) = (p : R) ^ 2 by rw [Nat.cast_pow]]
        ring
      _ = 0 := by rw [hkill_T, mul_zero]
  have htwo_unit : IsUnit (2 : R) := by
    apply (ZMod.isUnit_iff_coprime 2 (p ^ 6)).2
    exact coprime_two_pow_prime_oeis_361883 (r := 6) hp hp5
  change (((p ^ 2 * b : ℕ) : R)) * A = 0
  rcases htwo_unit with ⟨u, hu⟩
  have h : (u : R) * ((((p ^ 2 * b : ℕ) : R)) * A) = 0 := by
    simpa [hu] using htwo_goal
  have h' : ((((p ^ 2 * b : ℕ) : R)) * A) * (u : R) = 0 := by
    simpa [mul_comm] using h
  exact (Units.mul_left_eq_zero u).mp h'


/-- Conditional superblock product shift: it remains only to verify the two annihilating
inverse-sum conditions.  This is the standalone nilpotent expansion route specialized to
`ZMod (p^6)`. -/
lemma unit_superblock_shift_zmod_p6_oeis_361883_of_inverse_sum_annihilation {p b : ℕ}
    (hp : p.Prime)
    (hS1 : (((p ^ 2 * b : ℕ) : ZMod (p ^ 6))) *
        (∑ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
          (((x : ℕ) : ZMod (p ^ 6))⁻¹)) = 0)
    (hS2 : ((((p ^ 2 * b : ℕ) : ZMod (p ^ 6))) ^ 2) *
        (∑ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
          ∑ y ∈ ((Finset.range (p ^ 2)).filter (fun y => Nat.Coprime y (p ^ 2))).filter (fun y => y < x),
            (((y : ℕ) : ZMod (p ^ 6))⁻¹) * (((x : ℕ) : ZMod (p ^ 6))⁻¹)) = 0) :
    let R := ZMod (p ^ 6)
    (∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)), ((p ^ 2 * b + x : ℕ) : R)) =
    (∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)), ((x : ℕ) : R)) := by
  classical
  let R := ZMod (p ^ 6)
  let s := (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2))
  let δ : R := ((p ^ 2 * b : ℕ) : R)
  let f : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  have hδ3 : δ ^ 3 = 0 := by
    rw [← Nat.cast_pow]
    apply (ZMod.natCast_eq_zero_iff ((p ^ 2 * b) ^ 3) (p ^ 6)).2
    refine ⟨b ^ 3, ?_⟩
    rw [mul_pow]
    ring_nf
  have hratio : (∏ x ∈ s, (1 + δ * f x)) = (1 : R) := by
    have htrunc := finset_prod_one_add_nilpotent_order3_oeis_361883 (s := s) (δ := δ) (f := f) hδ3
    rw [htrunc]
    dsimp [s, δ, f] at hS1 hS2 ⊢
    rw [hS1, hS2]
    simp
  change (∏ x ∈ s, ((p ^ 2 * b + x : ℕ) : R)) = (∏ x ∈ s, ((x : ℕ) : R))
  calc
    (∏ x ∈ s, ((p ^ 2 * b + x : ℕ) : R)) =
        ∏ x ∈ s, (((x : ℕ) : R) * (1 + δ * f x)) := by
          apply Finset.prod_congr rfl
          intro x hx
          have hxc : Nat.Coprime x (p ^ 2) := (Finset.mem_filter.mp hx).2
          dsimp [δ, f]
          exact superblock_shift_factor_eq_mul_one_add_oeis_361883 (p := p) (b := b) (x := x) hp hxc
    _ = (∏ x ∈ s, ((x : ℕ) : R)) * (∏ x ∈ s, (1 + δ * f x)) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ x ∈ s, ((x : ℕ) : R)) := by
          rw [hratio, mul_one]



/-- Standalone `p^2` superblock product shift in `ZMod (p^6)`. -/
lemma unit_superblock_shift_zmod_p6_oeis_361883 {p b : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
  let R := ZMod (p ^ 6)
  (∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)), ((p ^ 2 * b + x : ℕ) : R)) =
  (∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)), ((x : ℕ) : R)) := by
  exact unit_superblock_shift_zmod_p6_oeis_361883_of_inverse_sum_annihilation (p := p) (b := b) hp
    (unit_superblock_shift_zmod_p6_hS1_oeis_361883 (p := p) (b := b) hp hp5)
    (unit_superblock_shift_zmod_p6_hS2_oeis_361883 (p := p) (b := b) hp hp5)


/-- Natural representatives coprime to `p^3` are units modulo `p^9`. -/
lemma coprime_p_cube_isUnit_zmod_p9_oeis_361883 {p x : ℕ} (hp : p.Prime)
    (hx : Nat.Coprime x (p ^ 3)) : IsUnit (x : ZMod (p ^ 9)) := by
  have hxp : Nat.Coprime x p := Nat.Coprime.of_dvd_right
    (by exact dvd_pow_self p (by norm_num : 3 ≠ 0)) hx
  have hnot : ¬ p ∣ x := (hp.coprime_iff_not_dvd).mp hxp.symm
  exact (ZMod.isUnit_iff_coprime _ _).2 (hp.coprime_pow_of_not_dvd hnot)

/-- Unit rewrite for one shifted factor in the `p^3` superblock modulo `p^9`. -/
lemma superblock3_shift_factor_eq_mul_one_add_oeis_361883 {p b x : ℕ} (hp : p.Prime)
    (hx : Nat.Coprime x (p ^ 3)) :
    (((p ^ 3 * b + x : ℕ) : ZMod (p ^ 9))) =
      ((x : ℕ) : ZMod (p ^ 9)) *
        (1 + (((p ^ 3 * b : ℕ) : ZMod (p ^ 9))) * (((x : ℕ) : ZMod (p ^ 9))⁻¹)) := by
  let R := ZMod (p ^ 9)
  have hunit : IsUnit ((x : ℕ) : R) := coprime_p_cube_isUnit_zmod_p9_oeis_361883 (p := p) hp hx
  rcases hunit with ⟨u, hu⟩
  have hmul : ((x : ℕ) : R) * (((x : ℕ) : R)⁻¹) = 1 := by
    rw [← hu, ZMod.inv_coe_unit]
    exact Units.mul_inv u
  change (((p ^ 3 * b + x : ℕ) : R)) =
      ((x : ℕ) : R) * (1 + (((p ^ 3 * b : ℕ) : R)) * (((x : ℕ) : R)⁻¹))
  rw [Nat.cast_add]
  calc
    (((p ^ 3 * b : ℕ) : R) + ((x : ℕ) : R)) =
        ((x : ℕ) : R) + ((p ^ 3 * b : ℕ) : R) := by ring
    _ = ((x : ℕ) : R) * (1 + (((p ^ 3 * b : ℕ) : R)) * (((x : ℕ) : R)⁻¹)) := by
      rw [mul_add, mul_one]
      calc
        ((x : ℕ) : R) + ((p ^ 3 * b : ℕ) : R) =
            ((x : ℕ) : R) + ((p ^ 3 * b : ℕ) : R) * (((x : ℕ) : R) * (((x : ℕ) : R)⁻¹)) := by
              rw [hmul, mul_one]
        _ = ((x : ℕ) : R) + ((x : ℕ) : R) * (((p ^ 3 * b : ℕ) : R) * (((x : ℕ) : R)⁻¹)) := by
              ring

/-- In `ZMod (p^9)`, a class reducing to zero modulo `p^3` is killed by `p^6`. -/
lemma zmod_p6_mul_eq_zero_of_castHom_p3_eq_zero_oeis_361883 {p : ℕ} (hp : p.Prime)
    (x : ZMod (p ^ 9))
    (hx : ZMod.castHom (show p ^ 3 ∣ p ^ 9 by exact pow_dvd_pow p (by norm_num : 3 ≤ 9))
        (ZMod (p ^ 3)) x = 0) :
    (p ^ 6 : ZMod (p ^ 9)) * x = 0 := by
  haveI : NeZero (p ^ 9) := ⟨pow_ne_zero 9 hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x]
  have hxval0 : ((x.val : ℕ) : ZMod (p ^ 3)) = 0 := by
    simpa [ZMod.castHom_apply] using hx
  have hxdiv : p ^ 3 ∣ x.val := (ZMod.natCast_eq_zero_iff x.val (p ^ 3)).1 hxval0
  rcases hxdiv with ⟨y, hy⟩
  rw [hy, Nat.cast_mul]
  have hzero : ((p ^ 9 : ℕ) : ZMod (p ^ 9)) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (p ^ 9) (p ^ 9)).2 (dvd_refl _)
  calc
    ((p : ZMod (p ^ 9)) ^ 6) * ((((p ^ 3 : ℕ) : ZMod (p ^ 9))) * (y : ZMod (p ^ 9)))
        = (y : ZMod (p ^ 9)) * ((p ^ 9 : ℕ) : ZMod (p ^ 9)) := by
          rw [show (((p ^ 3 : ℕ) : ZMod (p ^ 9))) = (p : ZMod (p ^ 9)) ^ 3 by rw [Nat.cast_pow]]
          ring_nf
          rw [Nat.cast_pow]
          exact mul_comm (((p : ZMod (p ^ 9)) ^ 9)) (y : ZMod (p ^ 9))
    _ = 0 := by rw [hzero, mul_zero]

/-- Reduction from `ZMod (p^9)` to `ZMod (p^3)` commutes with inverses of representatives
coprime to `p^3`. -/
lemma zmod_castHom_inv_p9_to_p3_of_coprime_oeis_361883 {p x : ℕ} (hp : p.Prime)
    (hx : Nat.Coprime x (p ^ 3)) :
    ZMod.castHom (show p ^ 3 ∣ p ^ 9 by exact pow_dvd_pow p (by norm_num : 3 ≤ 9))
      (ZMod (p ^ 3)) (((x : ℕ) : ZMod (p ^ 9))⁻¹) =
      (((x : ℕ) : ZMod (p ^ 3))⁻¹) := by
  let R := ZMod (p ^ 9)
  let S := ZMod (p ^ 3)
  let f := ZMod.castHom (show p ^ 3 ∣ p ^ 9 by exact pow_dvd_pow p (by norm_num : 3 ≤ 9)) S
  have hxp : Nat.Coprime x p := Nat.Coprime.of_dvd_right
    (by exact dvd_pow_self p (by norm_num : 3 ≠ 0)) hx
  have hnot : ¬ p ∣ x := (hp.coprime_iff_not_dvd).mp hxp.symm
  have hcopR : Nat.Coprime x (p ^ 9) := hp.coprime_pow_of_not_dvd hnot
  let uR : Rˣ := ZMod.unitOfCoprime x hcopR
  let uS : Sˣ := ZMod.unitOfCoprime x hx
  have hmapu : Units.map f.toMonoidHom uR = uS := by
    apply Units.ext
    change f (x : R) = (x : S)
    simp [f]
  have hmapinv : f ((uR⁻¹ : Rˣ) : R) = ((uS⁻¹ : Sˣ) : S) := by
    calc
      f ((uR⁻¹ : Rˣ) : R) = ((Units.map f.toMonoidHom uR)⁻¹ : Sˣ) := by
        exact (Units.coe_map_inv f.toMonoidHom uR).symm
      _ = ((uS⁻¹ : Sˣ) : S) := by rw [hmapu]
  have hinvR : ((x : R)⁻¹) = ((uR⁻¹ : Rˣ) : R) := by
    simpa [uR] using ZMod.inv_coe_unit uR
  have hinvS : ((x : S)⁻¹) = ((uS⁻¹ : Sˣ) : S) := by
    simpa [uS] using ZMod.inv_coe_unit uS
  calc
    f (((x : ℕ) : R)⁻¹) = f ((uR⁻¹ : Rˣ) : R) := by rw [hinvR]
    _ = ((uS⁻¹ : Sˣ) : S) := hmapinv
    _ = (((x : ℕ) : S)⁻¹) := by rw [hinvS]

/-- The quadratic ordered inverse-pair sum in the `p^3` superblock is annihilated by the
square of the shift in `ZMod (p^9)`. -/
lemma unit_superblock3_shift_zmod_p9_hS2_oeis_361883 {p b : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
  ((((p ^ 3 * b : ℕ) : ZMod (p ^ 9))) ^ 2) *
    (∑ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)),
      ∑ y ∈ ((Finset.range (p ^ 3)).filter (fun y => Nat.Coprime y (p ^ 3))).filter (fun y => y < x),
        (((y : ℕ) : ZMod (p ^ 9))⁻¹) * (((x : ℕ) : ZMod (p ^ 9))⁻¹)) = 0 := by
  classical
  let R := ZMod (p ^ 9)
  let S := ZMod (p ^ 3)
  let s := (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3))
  let fR : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  let fS : ℕ → S := fun x => (((x : ℕ) : S)⁻¹)
  let E : R := ∑ x ∈ s, ∑ y ∈ s.filter (fun y => y < x), fR y * fR x
  let D : R := ∑ x ∈ s, (fR x) ^ 2
  let A : R := ∑ x ∈ s, fR x
  let phi := ZMod.castHom (show p ^ 3 ∣ p ^ 9 by exact pow_dvd_pow p (by norm_num : 3 ≤ 9)) S
  have hphi_f (x : ℕ) (hxmem : x ∈ s) : phi (fR x) = fS x := by
    have hxc : Nat.Coprime x (p ^ 3) := (Finset.mem_filter.mp hxmem).2
    simpa [phi, fR, fS, R, S] using
      zmod_castHom_inv_p9_to_p3_of_coprime_oeis_361883 (p := p) (x := x) hp hxc
  have hphi_A : phi A = 0 := by
    calc
      phi A = ∑ x ∈ s, fS x := by
        dsimp [A]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hxmem
        simpa using hphi_f x hxmem
      _ = 0 := by
        dsimp [s, fS, S]
        exact sum_range_coprime_inv_zmod_pow_eq_zero_oeis_361883 p 3 hp hp5
  have hphi_D : phi D = 0 := by
    calc
      phi D = ∑ x ∈ s, (fS x) ^ 2 := by
        dsimp [D]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hxmem
        rw [map_pow]
        rw [hphi_f x hxmem]
      _ = 0 := by
        dsimp [s, fS, S]
        exact sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p 3 hp hp5
  have hkill_A_sq : (p ^ 6 : R) * (A ^ 2) = 0 := by
    apply zmod_p6_mul_eq_zero_of_castHom_p3_eq_zero_oeis_361883 (p := p) hp
    rw [map_pow, hphi_A, zero_pow (by norm_num : 2 ≠ 0)]
  have hkill_D : (p ^ 6 : R) * D = 0 := by
    apply zmod_p6_mul_eq_zero_of_castHom_p3_eq_zero_oeis_361883 (p := p) hp
    exact hphi_D
  have hpair_id : A ^ 2 = D + 2 * E := by
    dsimp [A, D, E, fR, s]
    exact finset_sum_sq_eq_diag_add_two_ordered_pairs_oeis_361883
      ((Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)))
      (fun x => (((x : ℕ) : R)⁻¹))
  have htwo_mul : (2 : R) * ((p ^ 6 : R) * E) = 0 := by
    have hcalc : (p ^ 6 : R) * (A ^ 2) = (p ^ 6 : R) * D + (2 : R) * ((p ^ 6 : R) * E) := by
      rw [hpair_id]
      ring
    have hsub : (p ^ 6 : R) * (A ^ 2) - (p ^ 6 : R) * D = (2 : R) * ((p ^ 6 : R) * E) := by
      rw [hcalc]
      ring
    rw [← hsub, hkill_A_sq, hkill_D]
    ring
  have htwo_unit : IsUnit (2 : R) := by
    apply (ZMod.isUnit_iff_coprime 2 (p ^ 9)).2
    exact coprime_two_pow_prime_oeis_361883 (r := 9) hp hp5
  have hkill_E : (p ^ 6 : R) * E = 0 := by
    rcases htwo_unit with ⟨u, hu⟩
    have h : (u : R) * ((p ^ 6 : R) * E) = 0 := by
      simpa [hu] using htwo_mul
    have h' : ((p ^ 6 : R) * E) * (u : R) = 0 := by
      simpa [mul_comm] using h
    exact (Units.mul_left_eq_zero u).mp h'
  change (((p ^ 3 * b : ℕ) : R) ^ 2) * E = 0
  calc
    (((p ^ 3 * b : ℕ) : R) ^ 2) * E = (b ^ 2 : R) * ((p ^ 6 : R) * E) := by
      rw [Nat.cast_mul]
      rw [show (((p ^ 3 : ℕ) : R)) = (p : R) ^ 3 by rw [Nat.cast_pow]]
      ring
    _ = 0 := by rw [hkill_E, mul_zero]


/-- The linear inverse-sum term in the `p^3` superblock is annihilated by the shift in
`ZMod (p^9)`.  Pairing each unit representative `x` with `p^3 - x` shows that the sum is
`p^3/2` times a product of paired inverses; the latter product-sum reduces modulo `p^3` to
minus the inverse-square sum, hence is killed by the remaining `p^6`. -/
lemma unit_superblock3_shift_zmod_p9_hS1_oeis_361883 {p b : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
  (((p ^ 3 * b : ℕ) : ZMod (p ^ 9))) *
    (∑ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)),
      (((x : ℕ) : ZMod (p ^ 9))⁻¹)) = 0 := by
  classical
  let R := ZMod (p ^ 9)
  let S := ZMod (p ^ 3)
  let s := (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3))
  let c : ℕ → ℕ := fun x => p ^ 3 - x
  let fR : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  let fS : ℕ → S := fun x => (((x : ℕ) : S)⁻¹)
  let A : R := ∑ x ∈ s, fR x
  let T : R := ∑ x ∈ s, fR x * fR (c x)
  let phi := ZMod.castHom (show p ^ 3 ∣ p ^ 9 by exact pow_dvd_pow p (by norm_num : 3 ≤ 9)) S
  have hs_mem_data {x : ℕ} (hx : x ∈ s) : x < p ^ 3 ∧ Nat.Coprime x (p ^ 3) := by
    have h := Finset.mem_filter.mp hx
    exact ⟨Finset.mem_range.mp h.1, h.2⟩
  have hp3_gt_one : 1 < p ^ 3 := by
    have hp1 : 1 ≤ p := by omega
    have hp_le : p ≤ p ^ 3 := le_self_pow hp1 (by norm_num : (3 : ℕ) ≠ 0)
    omega
  have hpos_of_mem {x : ℕ} (hx : x ∈ s) : 0 < x := by
    have hxc : Nat.Coprime x (p ^ 3) := (hs_mem_data hx).2
    by_contra hx0
    have hxz : x = 0 := Nat.eq_zero_of_not_pos hx0
    subst hxz
    have hbad : p ^ 3 = 1 := by simpa [Nat.Coprime] using hxc
    omega
  have hc_mem {x : ℕ} (hx : x ∈ s) : c x ∈ s := by
    have hxlt : x < p ^ 3 := (hs_mem_data hx).1
    have hxc : Nat.Coprime x (p ^ 3) := (hs_mem_data hx).2
    have hxpos : 0 < x := hpos_of_mem hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · dsimp [c]
      omega
    · dsimp [c]
      exact (Nat.coprime_self_sub_left (show x ≤ p ^ 3 by omega)).2 hxc
  have hc_invol {x : ℕ} (hx : x ∈ s) : c (c x) = x := by
    have hxlt : x < p ^ 3 := (hs_mem_data hx).1
    have hxpos : 0 < x := hpos_of_mem hx
    dsimp [c]
    omega
  have hcast_sum {x : ℕ} (hx : x ∈ s) :
      ((x : R) + ((c x : ℕ) : R)) = ((p ^ 3 : ℕ) : R) := by
    have hxlt : x < p ^ 3 := (hs_mem_data hx).1
    have hnat : x + (p ^ 3 - x) = p ^ 3 := Nat.add_sub_of_le (show x ≤ p ^ 3 by omega)
    dsimp [c]
    rw [← Nat.cast_add, hnat]
  have hpair_inv {x : ℕ} (hx : x ∈ s) :
      fR x + fR (c x) = ((p ^ 3 : ℕ) : R) * fR x * fR (c x) := by
    have hxc : Nat.Coprime x (p ^ 3) := (hs_mem_data hx).2
    have hcc : Nat.Coprime (c x) (p ^ 3) := (hs_mem_data (hc_mem hx)).2
    have hxunit : IsUnit ((x : ℕ) : R) := coprime_p_cube_isUnit_zmod_p9_oeis_361883 (p := p) hp hxc
    have hcunit : IsUnit (((c x : ℕ) : R)) := coprime_p_cube_isUnit_zmod_p9_oeis_361883 (p := p) hp hcc
    rcases hxunit with ⟨ux, hux⟩
    rcases hcunit with ⟨uc, huc⟩
    have hxmul : ((x : ℕ) : R) * fR x = 1 := by
      dsimp [fR]
      rw [← hux, ZMod.inv_coe_unit]
      exact Units.mul_inv ux
    have hcmul : (((c x : ℕ) : R)) * fR (c x) = 1 := by
      dsimp [fR]
      rw [← huc, ZMod.inv_coe_unit]
      exact Units.mul_inv uc
    have hmain : (((x : ℕ) : R) + ((c x : ℕ) : R)) * fR x * fR (c x) = fR x + fR (c x) := by
      calc
        (((x : ℕ) : R) + ((c x : ℕ) : R)) * fR x * fR (c x)
            = (((x : ℕ) : R) * fR x) * fR (c x) + (((c x : ℕ) : R) * fR (c x)) * fR x := by ring
        _ = fR x + fR (c x) := by rw [hxmul, hcmul]; ring
    rw [← hmain, hcast_sum hx]
  have hA_comp : A = ∑ x ∈ s, fR (c x) := by
    dsimp [A]
    refine Finset.sum_bij (fun x _ => c x) ?_ ?_ ?_ ?_
    · intro x hx
      exact hc_mem hx
    · intro x hx y hy hxy
      have hxlt : x < p ^ 3 := (hs_mem_data hx).1
      have hylt : y < p ^ 3 := (hs_mem_data hy).1
      dsimp [c] at hxy
      omega
    · intro y hy
      refine ⟨c y, hc_mem hy, ?_⟩
      exact hc_invol hy
    · intro x hx
      rw [hc_invol hx]
  have htwoA : (2 : R) * A = ((p ^ 3 : ℕ) : R) * T := by
    calc
      (2 : R) * A = A + A := by ring
      _ = (∑ x ∈ s, fR x) + A := by rfl
      _ = (∑ x ∈ s, fR x) + (∑ x ∈ s, fR (c x)) := by rw [hA_comp]
      _ = ∑ x ∈ s, (fR x + fR (c x)) := by rw [Finset.sum_add_distrib]
      _ = ∑ x ∈ s, (((p ^ 3 : ℕ) : R) * fR x * fR (c x)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hpair_inv hx
      _ = ((p ^ 3 : ℕ) : R) * T := by
        dsimp [T]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
  have hphi_f {x : ℕ} (hxmem : x ∈ s) : phi (fR x) = fS x := by
    have hxc : Nat.Coprime x (p ^ 3) := (hs_mem_data hxmem).2
    simpa [phi, fR, fS, R, S] using
      zmod_castHom_inv_p9_to_p3_of_coprime_oeis_361883 (p := p) (x := x) hp hxc
  have hphi_T : phi T = 0 := by
    calc
      phi T = ∑ x ∈ s, fS x * fS (c x) := by
        dsimp [T]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [map_mul, hphi_f hx, hphi_f (hc_mem hx)]
      _ = ∑ x ∈ s, - (fS x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt : x < p ^ 3 := (hs_mem_data hx).1
        have hnat : x + (p ^ 3 - x) = p ^ 3 := Nat.add_sub_of_le (show x ≤ p ^ 3 by omega)
        have hsum0 : ((x : ℕ) : S) + ((c x : ℕ) : S) = 0 := by
          dsimp [c]
          rw [← Nat.cast_add, hnat]
          simp [S]
        have hc_eq_neg : ((c x : ℕ) : S) = - ((x : ℕ) : S) := by
          exact eq_neg_of_add_eq_zero_right hsum0
        have hf_neg : fS (c x) = - fS x := by
          dsimp [fS]
          rw [hc_eq_neg]
          have hxc : Nat.Coprime x (p ^ 3) := (hs_mem_data hx).2
          have hxunitS : IsUnit ((x : ℕ) : S) := by
            exact (ZMod.isUnit_iff_coprime x (p ^ 3)).2 hxc
          rcases hxunitS with ⟨u, hu⟩
          rw [← hu, ZMod.inv_coe_unit]
          change (-(u : S))⁻¹ = -↑(u⁻¹)
          rw [show -(u : S) = ((-u : Sˣ) : S) by rfl]
          rw [ZMod.inv_coe_unit]
          rfl
        rw [hf_neg]
        ring
      _ = - (∑ x ∈ s, (fS x) ^ 2) := by rw [Finset.sum_neg_distrib]
      _ = 0 := by
        dsimp [s, fS, S]
        rw [sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p 3 hp hp5, neg_zero]
  have hkill_T : (p ^ 6 : R) * T = 0 := by
    apply zmod_p6_mul_eq_zero_of_castHom_p3_eq_zero_oeis_361883 (p := p) hp
    exact hphi_T
  have htwo_goal : (2 : R) * ((((p ^ 3 * b : ℕ) : R)) * A) = 0 := by
    calc
      (2 : R) * ((((p ^ 3 * b : ℕ) : R)) * A)
          = (((p ^ 3 * b : ℕ) : R)) * ((2 : R) * A) := by ring
      _ = (((p ^ 3 * b : ℕ) : R)) * (((p ^ 3 : ℕ) : R) * T) := by rw [htwoA]
      _ = (b : R) * ((p ^ 6 : R) * T) := by
        rw [Nat.cast_mul]
        rw [show (((p ^ 3 : ℕ) : R)) = (p : R) ^ 3 by rw [Nat.cast_pow]]
        ring
      _ = 0 := by rw [hkill_T, mul_zero]
  have htwo_unit : IsUnit (2 : R) := by
    apply (ZMod.isUnit_iff_coprime 2 (p ^ 9)).2
    exact coprime_two_pow_prime_oeis_361883 (r := 9) hp hp5
  change (((p ^ 3 * b : ℕ) : R)) * A = 0
  rcases htwo_unit with ⟨u, hu⟩
  have h : (u : R) * ((((p ^ 3 * b : ℕ) : R)) * A) = 0 := by
    simpa [hu] using htwo_goal
  have h' : ((((p ^ 3 * b : ℕ) : R)) * A) * (u : R) = 0 := by
    simpa [mul_comm] using h
  exact (Units.mul_left_eq_zero u).mp h'

/-- Conditional `p^3` superblock product shift in `ZMod (p^9)`: the nilpotent expansion reduces
it to the linear and quadratic inverse-sum annihilation conditions.  The quadratic condition is
proved separately as `unit_superblock3_shift_zmod_p9_hS2_oeis_361883`. -/
lemma unit_superblock3_shift_zmod_p9_oeis_361883_of_inverse_sum_annihilation {p b : ℕ}
    (hp : p.Prime)
    (hS1 : (((p ^ 3 * b : ℕ) : ZMod (p ^ 9))) *
        (∑ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)),
          (((x : ℕ) : ZMod (p ^ 9))⁻¹)) = 0)
    (hS2 : ((((p ^ 3 * b : ℕ) : ZMod (p ^ 9))) ^ 2) *
        (∑ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)),
          ∑ y ∈ ((Finset.range (p ^ 3)).filter (fun y => Nat.Coprime y (p ^ 3))).filter (fun y => y < x),
            (((y : ℕ) : ZMod (p ^ 9))⁻¹) * (((x : ℕ) : ZMod (p ^ 9))⁻¹)) = 0) :
    let R := ZMod (p ^ 9)
    (∏ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)), ((p ^ 3 * b + x : ℕ) : R)) =
    (∏ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)), ((x : ℕ) : R)) := by
  classical
  let R := ZMod (p ^ 9)
  let s := (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3))
  let δ : R := ((p ^ 3 * b : ℕ) : R)
  let f : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  have hδ3 : δ ^ 3 = 0 := by
    rw [← Nat.cast_pow]
    apply (ZMod.natCast_eq_zero_iff ((p ^ 3 * b) ^ 3) (p ^ 9)).2
    refine ⟨b ^ 3, ?_⟩
    rw [mul_pow]
    ring_nf
  have hratio : (∏ x ∈ s, (1 + δ * f x)) = (1 : R) := by
    have htrunc := finset_prod_one_add_nilpotent_order3_oeis_361883 (s := s) (δ := δ) (f := f) hδ3
    rw [htrunc]
    dsimp [s, δ, f] at hS1 hS2 ⊢
    rw [hS1, hS2]
    simp
  change (∏ x ∈ s, ((p ^ 3 * b + x : ℕ) : R)) = (∏ x ∈ s, ((x : ℕ) : R))
  calc
    (∏ x ∈ s, ((p ^ 3 * b + x : ℕ) : R)) =
        ∏ x ∈ s, (((x : ℕ) : R) * (1 + δ * f x)) := by
          apply Finset.prod_congr rfl
          intro x hx
          have hxc : Nat.Coprime x (p ^ 3) := (Finset.mem_filter.mp hx).2
          dsimp [δ, f]
          exact superblock3_shift_factor_eq_mul_one_add_oeis_361883 (p := p) (b := b) (x := x) hp hxc
    _ = (∏ x ∈ s, ((x : ℕ) : R)) * (∏ x ∈ s, (1 + δ * f x)) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ x ∈ s, ((x : ℕ) : R)) := by
          rw [hratio, mul_one]


/-- `p^9` superblock shift with the proved quadratic annihilation built in, conditional on the
linear annihilation `hS1`. -/
lemma unit_superblock3_shift_zmod_p9_oeis_361883_of_hS1 {p b : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hS1 : (((p ^ 3 * b : ℕ) : ZMod (p ^ 9))) *
        (∑ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)),
          (((x : ℕ) : ZMod (p ^ 9))⁻¹)) = 0) :
    let R := ZMod (p ^ 9)
    (∏ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)), ((p ^ 3 * b + x : ℕ) : R)) =
    (∏ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)), ((x : ℕ) : R)) := by
  exact unit_superblock3_shift_zmod_p9_oeis_361883_of_inverse_sum_annihilation (p := p) (b := b) hp
    hS1 (unit_superblock3_shift_zmod_p9_hS2_oeis_361883 (p := p) (b := b) hp hp5)


/-- Standalone `p^3` superblock product shift in `ZMod (p^9)`. -/
lemma unit_superblock3_shift_zmod_p9_oeis_361883 {p b : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
  let R := ZMod (p ^ 9)
  (∏ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)), ((p ^ 3 * b + x : ℕ) : R)) =
  (∏ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)), ((x : ℕ) : R)) := by
  exact unit_superblock3_shift_zmod_p9_oeis_361883_of_hS1 (p := p) (b := b) hp hp5
    (unit_superblock3_shift_zmod_p9_hS1_oeis_361883 (p := p) (b := b) hp hp5)

/-- Rewrite the `p^3` unit superblock as `p^2` consecutive ordinary unit blocks. -/
lemma unit_superblock3_eq_prod_blocks_zmod_p9_oeis_361883 {p d : ℕ} (hp : p.Prime) :
    let R := ZMod (p ^ 9)
    (∏ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)),
        ((p ^ 3 * d + x : ℕ) : R)) =
      ∏ m ∈ Finset.range (p ^ 2),
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p ^ 3 * d + (p * m + t) : ℕ) : R) := by
  classical
  intro R
  let G : ℕ → R := fun x => ((p ^ 3 * d + x : ℕ) : R)
  have hiff : ∀ m ∈ Finset.range (p ^ 2), ∀ t ∈ Finset.range p,
      (Nat.Coprime (p * m + t) (p ^ 3) ↔ 0 < t) := by
    intro m _hm t ht
    have htp : t < p := Finset.mem_range.mp ht
    constructor
    · intro hcop
      by_contra ht0
      have ht_eq : t = 0 := Nat.eq_zero_of_not_pos ht0
      have hdiv : p ∣ p * m + t := by
        rw [ht_eq, add_zero]
        exact dvd_mul_right p m
      have hp_dvd_pow : p ∣ p ^ 3 := dvd_pow_self p (by decide : 3 ≠ 0)
      exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hdiv hp_dvd_pow) hcop
    · intro htpos
      have hnot : ¬ p ∣ p * m + t := by
        intro hdiv
        have hpdm : p ∣ p * m := dvd_mul_right p m
        have htdvd : p ∣ t := (Nat.dvd_add_iff_right hpdm).2 hdiv
        exact (Nat.not_dvd_of_pos_of_lt htpos htp) htdvd
      exact hp.coprime_pow_of_not_dvd hnot
  calc
    (∏ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)), G x)
        = ∏ x ∈ Finset.range (p ^ 3), if Nat.Coprime x (p ^ 3) then G x else 1 := by
          rw [Finset.prod_filter]
    _ = ∏ x ∈ Finset.range ((p ^ 2) * p), if Nat.Coprime x (p ^ 3) then G x else 1 := by
          rw [show p ^ 3 = (p ^ 2) * p by ring_nf]
    _ = ∏ m ∈ Finset.range (p ^ 2),
          ∏ t ∈ Finset.range p, if Nat.Coprime (p * m + t) (p ^ 3) then G (p * m + t) else 1 := by
          rw [prod_range_mul_decomp_oeis_361883]
    _ = ∏ m ∈ Finset.range (p ^ 2),
          ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), G (p * m + t) := by
          apply Finset.prod_congr rfl
          intro m hm
          calc
            (∏ t ∈ Finset.range p, if Nat.Coprime (p * m + t) (p ^ 3) then G (p * m + t) else 1)
                = ∏ t ∈ Finset.range p, if 0 < t then G (p * m + t) else 1 := by
                  apply Finset.prod_congr rfl
                  intro t ht
                  by_cases htpos : 0 < t
                  · have hc : Nat.Coprime (p * m + t) (p ^ 3) := (hiff m hm t ht).2 htpos
                    rw [if_pos hc, if_pos htpos]
                  · have hnc : ¬ Nat.Coprime (p * m + t) (p ^ 3) := by
                      intro hc
                      exact htpos ((hiff m hm t ht).1 hc)
                    rw [if_neg hnc, if_neg htpos]
            _ = ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), G (p * m + t) := by
                  exact (Finset.prod_filter (s := Finset.range p) (p := fun t => 0 < t)
                    (f := fun t => G (p * m + t))).symm
    _ = ∏ m ∈ Finset.range (p ^ 2),
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p ^ 3 * d + (p * m + t) : ℕ) : R) := by
          rfl

/-- A group of `p^2` ordinary unit blocks is invariant modulo `p^9` when shifted by `p^2*b`. -/
lemma unit_block_supergroup_shift_zmod_p9_oeis_361883 {p b v : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    let R := ZMod (p ^ 9)
    (∏ m ∈ Finset.range (p ^ 2),
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p ^ 2 * (b + v) + m) + t : ℕ) : R)) =
      ∏ m ∈ Finset.range (p ^ 2),
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p ^ 2 * v + m) + t : ℕ) : R) := by
  classical
  intro R
  let S : ℕ → R := fun d =>
    ∏ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)),
      ((p ^ 3 * d + x : ℕ) : R)
  have hblocks_left :
      (∏ m ∈ Finset.range (p ^ 2),
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p ^ 2 * (b + v) + m) + t : ℕ) : R)) = S (b + v) := by
    calc
      (∏ m ∈ Finset.range (p ^ 2),
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p ^ 2 * (b + v) + m) + t : ℕ) : R))
          = ∏ m ∈ Finset.range (p ^ 2),
              ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
                ((p ^ 3 * (b + v) + (p * m + t) : ℕ) : R) := by
              apply Finset.prod_congr rfl
              intro m hm
              apply Finset.prod_congr rfl
              intro t ht
              congr 1
              ring_nf
      _ = S (b + v) := by
          dsimp [S]
          rw [unit_superblock3_eq_prod_blocks_zmod_p9_oeis_361883 (p := p) (d := b + v) hp]
  have hblocks_right :
      (∏ m ∈ Finset.range (p ^ 2),
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p ^ 2 * v + m) + t : ℕ) : R)) = S v := by
    calc
      (∏ m ∈ Finset.range (p ^ 2),
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p ^ 2 * v + m) + t : ℕ) : R))
          = ∏ m ∈ Finset.range (p ^ 2),
              ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
                ((p ^ 3 * v + (p * m + t) : ℕ) : R) := by
              apply Finset.prod_congr rfl
              intro m hm
              apply Finset.prod_congr rfl
              intro t ht
              congr 1
              ring_nf
      _ = S v := by
          dsimp [S]
          rw [unit_superblock3_eq_prod_blocks_zmod_p9_oeis_361883 (p := p) (d := v) hp]
  have hshift : S (b + v) = S v := by
    have hleft : S (b + v) = S 0 := by
      dsimp [S]
      simpa using unit_superblock3_shift_zmod_p9_oeis_361883 (p := p) (b := b + v) hp hp5
    have hright : S v = S 0 := by
      dsimp [S]
      simpa using unit_superblock3_shift_zmod_p9_oeis_361883 (p := p) (b := v) hp hp5
    exact hleft.trans hright.symm
  calc
    (∏ m ∈ Finset.range (p ^ 2),
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p ^ 2 * (b + v) + m) + t : ℕ) : R)) = S (b + v) := hblocks_left
    _ = S v := hshift
    _ = ∏ m ∈ Finset.range (p ^ 2),
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p ^ 2 * v + m) + t : ℕ) : R) := hblocks_right.symm


/-- In `ZMod (p^n)`, an element whose reduction modulo `p^m` is zero is killed by
`p^k` as soon as `n ≤ k + m`. -/
lemma zmod_pow_mul_eq_zero_of_castHom_pow_eq_zero_oeis_361883 {p n m k : ℕ}
    (hp : p.Prime) (hmn : m ≤ n) (hkm : n ≤ k + m) (x : ZMod (p ^ n))
    (hx : ZMod.castHom (show p ^ m ∣ p ^ n by exact pow_dvd_pow p hmn)
        (ZMod (p ^ m)) x = 0) :
    ((p ^ k : ℕ) : ZMod (p ^ n)) * x = 0 := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ← Nat.cast_mul]
  apply (ZMod.natCast_eq_zero_iff (p ^ k * x.val) (p ^ n)).2
  have hxval0 : ((x.val : ℕ) : ZMod (p ^ m)) = 0 := by
    simpa [ZMod.castHom_apply] using hx
  have hxdiv : p ^ m ∣ x.val := (ZMod.natCast_eq_zero_iff x.val (p ^ m)).1 hxval0
  rcases hxdiv with ⟨y, hy⟩
  rw [hy]
  have hpow : p ^ n ∣ p ^ (k + m) := pow_dvd_pow p hkm
  refine dvd_trans hpow ?_
  refine ⟨y, ?_⟩
  rw [pow_add]
  ring

/-- Natural representatives congruent to a unit modulo `p^m` are units modulo `p^n`. -/
lemma coprime_add_pow_mul_isUnit_zmod_pow_oeis_361883 {p m n v x : ℕ} (hp : p.Prime)
    (hm : 0 < m) (hx : Nat.Coprime x (p ^ m)) :
    IsUnit (((p ^ m * v + x : ℕ) : ZMod (p ^ n))) := by
  have hxp : Nat.Coprime x p := Nat.Coprime.of_dvd_right
    (by exact dvd_pow_self p (Nat.ne_of_gt hm)) hx
  have hnotx : ¬ p ∣ x := (hp.coprime_iff_not_dvd).mp hxp.symm
  have hpdiva : p ∣ p ^ m * v := by
    exact dvd_mul_of_dvd_left (dvd_pow_self p (Nat.ne_of_gt hm)) v
  have hnot : ¬ p ∣ p ^ m * v + x := by
    intro hdiv
    exact hnotx ((Nat.dvd_add_iff_right hpdiva).2 hdiv)
  exact (ZMod.isUnit_iff_coprime _ _).2 (hp.coprime_pow_of_not_dvd hnot)

/-- Reduction between two prime-power `ZMod`s commutes with inverses of representatives
coprime to the smaller prime power, even after adding a multiple of that smaller prime power. -/
lemma zmod_castHom_inv_pow_to_pow_of_coprime_shift_oeis_361883 {p m n v x : ℕ}
    (hp : p.Prime) (hmn : m ≤ n) (hm : 0 < m) (hx : Nat.Coprime x (p ^ m)) :
    ZMod.castHom (show p ^ m ∣ p ^ n by exact pow_dvd_pow p hmn) (ZMod (p ^ m))
      ((((p ^ m * v + x : ℕ) : ZMod (p ^ n))⁻¹)) =
      (((x : ℕ) : ZMod (p ^ m))⁻¹) := by
  let R := ZMod (p ^ n)
  let S := ZMod (p ^ m)
  let f := ZMod.castHom (show p ^ m ∣ p ^ n by exact pow_dvd_pow p hmn) S
  have hunitR : IsUnit (((p ^ m * v + x : ℕ) : R)) :=
    coprime_add_pow_mul_isUnit_zmod_pow_oeis_361883 (p := p) (m := m) (n := n) (v := v) (x := x) hp hm hx
  have hunitS : IsUnit (((x : ℕ) : S)) := (ZMod.isUnit_iff_coprime x (p ^ m)).2 hx
  rcases hunitR with ⟨uR, huR⟩
  rcases hunitS with ⟨uS, huS⟩
  have hmap_base : f (((p ^ m * v + x : ℕ) : R)) = ((x : ℕ) : S) := by
    rw [Nat.cast_add]
    rw [map_add]
    have hz : f (((p ^ m * v : ℕ) : R)) = 0 := by
      have hdivmn : p ^ m ∣ p ^ n := pow_dvd_pow p hmn
      have hcastpm : (ZMod.cast (((p ^ m : ℕ) : R)) : S) = 0 := by
        rw [ZMod.cast_natCast hdivmn (p ^ m)]
        simp [S]
      calc
        f (((p ^ m * v : ℕ) : R)) = (ZMod.cast ((((p ^ m : ℕ) : R) * ((v : ℕ) : R)) : R) : S) := by
          rw [Nat.cast_mul]
          rfl
        _ = (ZMod.cast (((p ^ m : ℕ) : R)) : S) * (ZMod.cast (((v : ℕ) : R)) : S) := by
          rw [ZMod.cast_mul hdivmn]
        _ = 0 := by rw [hcastpm, zero_mul]
    have hxmap : f (((x : ℕ) : R)) = ((x : ℕ) : S) := by
      simp [f]
    rw [hz, hxmap, zero_add]
  have hmapu : Units.map f.toMonoidHom uR = uS := by
    apply Units.ext
    simpa [huR, huS] using hmap_base
  have hinvR : ((((p ^ m * v + x : ℕ) : R)⁻¹)) = ((uR⁻¹ : Rˣ) : R) := by
    simpa [huR] using ZMod.inv_coe_unit uR
  have hinvS : ((((x : ℕ) : S)⁻¹)) = ((uS⁻¹ : Sˣ) : S) := by
    simpa [huS] using ZMod.inv_coe_unit uS
  calc
    f ((((p ^ m * v + x : ℕ) : R)⁻¹)) = f ((uR⁻¹ : Rˣ) : R) := by rw [hinvR]
    _ = ((Units.map f.toMonoidHom uR)⁻¹ : Sˣ) := by
      exact (Units.coe_map_inv f.toMonoidHom uR).symm
    _ = ((uS⁻¹ : Sˣ) : S) := by rw [hmapu]
    _ = (((x : ℕ) : S)⁻¹) := by rw [hinvS]

/-- Unit rewrite for one factor in an asymmetric shifted superblock with an additional
`p^m`-multiple base point. -/
lemma superblock_shift_factor_eq_mul_one_add_asym_oeis_361883 {p m n k b v x : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hx : Nat.Coprime x (p ^ m)) :
    (((p ^ k * b + (p ^ m * v + x) : ℕ) : ZMod (p ^ n))) =
      (((p ^ m * v + x : ℕ) : ZMod (p ^ n))) *
        (1 + (((p ^ k * b : ℕ) : ZMod (p ^ n))) *
          ((((p ^ m * v + x : ℕ) : ZMod (p ^ n)))⁻¹)) := by
  let R := ZMod (p ^ n)
  have hunit : IsUnit (((p ^ m * v + x : ℕ) : R)) :=
    coprime_add_pow_mul_isUnit_zmod_pow_oeis_361883 (p := p) (m := m) (n := n) (v := v) (x := x) hp hm hx
  rcases hunit with ⟨u, hu⟩
  have hmul : (((p ^ m * v + x : ℕ) : R)) * ((((p ^ m * v + x : ℕ) : R))⁻¹) = 1 := by
    rw [← hu, ZMod.inv_coe_unit]
    exact Units.mul_inv u
  change (((p ^ k * b + (p ^ m * v + x) : ℕ) : R)) =
      (((p ^ m * v + x : ℕ) : R)) *
        (1 + (((p ^ k * b : ℕ) : R)) * ((((p ^ m * v + x : ℕ) : R))⁻¹))
  rw [Nat.cast_add]
  calc
    (((p ^ k * b : ℕ) : R) + (((p ^ m * v + x : ℕ) : R))) =
        (((p ^ m * v + x : ℕ) : R)) + ((p ^ k * b : ℕ) : R) := by ring
    _ = (((p ^ m * v + x : ℕ) : R)) *
        (1 + (((p ^ k * b : ℕ) : R)) * ((((p ^ m * v + x : ℕ) : R))⁻¹)) := by
      rw [mul_add, mul_one]
      calc
        (((p ^ m * v + x : ℕ) : R)) + ((p ^ k * b : ℕ) : R) =
            (((p ^ m * v + x : ℕ) : R)) +
              ((p ^ k * b : ℕ) : R) *
                ((((p ^ m * v + x : ℕ) : R)) * ((((p ^ m * v + x : ℕ) : R))⁻¹)) := by
          rw [hmul, mul_one]
        _ = (((p ^ m * v + x : ℕ) : R)) +
              (((p ^ m * v + x : ℕ) : R)) *
                (((p ^ k * b : ℕ) : R) * ((((p ^ m * v + x : ℕ) : R))⁻¹)) := by
          ring


/-- Generic quadratic inverse-pair annihilation for an asymmetric superblock. -/
lemma unit_superblock_shift_asym_zmod_hS2_oeis_361883 {p s t b : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hst : t ≤ s) :
  let m := t + 1
  let n := s + 2 * t + 3
  ((((p ^ (s + 1) * b : ℕ) : ZMod (p ^ n))) ^ 2) *
    (∑ x ∈ (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)),
      ∑ y ∈ ((Finset.range (p ^ m)).filter (fun y => Nat.Coprime y (p ^ m))).filter (fun y => y < x),
        (((y : ℕ) : ZMod (p ^ n))⁻¹) * (((x : ℕ) : ZMod (p ^ n))⁻¹)) = 0 := by
  classical
  intro m n
  let R := ZMod (p ^ n)
  let S := ZMod (p ^ m)
  let us := (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m))
  let fR : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  let fS : ℕ → S := fun x => (((x : ℕ) : S)⁻¹)
  let E : R := ∑ x ∈ us, ∑ y ∈ us.filter (fun y => y < x), fR y * fR x
  let D : R := ∑ x ∈ us, (fR x) ^ 2
  let A : R := ∑ x ∈ us, fR x
  have hmn : m ≤ n := by dsimp [m, n]; omega
  let phi := ZMod.castHom (show p ^ m ∣ p ^ n by exact pow_dvd_pow p hmn) S
  have hmpos : 0 < m := by dsimp [m]; omega
  have hphi_f (x : ℕ) (hxmem : x ∈ us) : phi (fR x) = fS x := by
    have hxc : Nat.Coprime x (p ^ m) := (Finset.mem_filter.mp hxmem).2
    simpa [phi, fR, fS, R, S] using
      zmod_castHom_inv_pow_to_pow_of_coprime_shift_oeis_361883 (p := p) (m := m) (n := n)
        (v := 0) (x := x) hp hmn hmpos hxc
  have hphi_A : phi A = 0 := by
    calc
      phi A = ∑ x ∈ us, fS x := by
        dsimp [A]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hxmem
        simpa using hphi_f x hxmem
      _ = 0 := by
        dsimp [us, fS, S]
        exact sum_range_coprime_inv_zmod_pow_eq_zero_oeis_361883 p m hp hp5
  have hphi_D : phi D = 0 := by
    calc
      phi D = ∑ x ∈ us, (fS x) ^ 2 := by
        dsimp [D]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hxmem
        rw [map_pow, hphi_f x hxmem]
      _ = 0 := by
        dsimp [us, fS, S]
        exact sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p m hp hp5
  have hpair_id : A ^ 2 = D + 2 * E := by
    dsimp [A, D, E, fR, us]
    exact finset_sum_sq_eq_diag_add_two_ordered_pairs_oeis_361883
      ((Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)))
      (fun x => (((x : ℕ) : R)⁻¹))
  have hphi_E : phi E = 0 := by
    have htwo : (2 : S) * phi E = 0 := by
      have hcalc : phi (A ^ 2) = phi D + (2 : S) * phi E := by
        rw [hpair_id, map_add, map_mul, map_ofNat]
      rw [map_pow, hphi_A, zero_pow (by norm_num : 2 ≠ 0), hphi_D] at hcalc
      simpa using hcalc.symm
    have htwo_unit : IsUnit (2 : S) := by
      apply (ZMod.isUnit_iff_coprime 2 (p ^ m)).2
      exact coprime_two_pow_prime_oeis_361883 (r := m) hp hp5
    rcases htwo_unit with ⟨u, hu⟩
    have h : (u : S) * phi E = 0 := by simpa [hu] using htwo
    have h' : phi E * (u : S) = 0 := by simpa [mul_comm] using h
    exact (Units.mul_left_eq_zero u).mp h'
  have hkill_E : ((p ^ (2 * s + 2) : ℕ) : R) * E = 0 := by
    apply zmod_pow_mul_eq_zero_of_castHom_pow_eq_zero_oeis_361883 (p := p) hp hmn
    · dsimp [m, n]
      omega
    · exact hphi_E
  change (((p ^ (s + 1) * b : ℕ) : R) ^ 2) * E = 0
  calc
    (((p ^ (s + 1) * b : ℕ) : R) ^ 2) * E = (b ^ 2 : R) * (((p ^ (2 * s + 2) : ℕ) : R) * E) := by
      rw [Nat.cast_mul, Nat.cast_pow]
      rw [show (((p ^ (2 * s + 2) : ℕ) : R)) = (p : R) ^ (2 * (s + 1)) by
        rw [show 2 * s + 2 = 2 * (s + 1) by omega, Nat.cast_pow]]
      ring
    _ = 0 := by rw [hkill_E, mul_zero]

/-- Generic linear inverse-sum annihilation for an asymmetric superblock. -/
lemma unit_superblock_shift_asym_zmod_hS1_oeis_361883 {p s t b : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
  let m := t + 1
  let n := s + 2 * t + 3
  (((p ^ (s + 1) * b : ℕ) : ZMod (p ^ n))) *
    (∑ x ∈ (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)),
      (((x : ℕ) : ZMod (p ^ n))⁻¹)) = 0 := by
  classical
  intro m n
  let R := ZMod (p ^ n)
  let S := ZMod (p ^ m)
  let us := (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m))
  let c : ℕ → ℕ := fun x => p ^ m - x
  let fR : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  let fS : ℕ → S := fun x => (((x : ℕ) : S)⁻¹)
  let A : R := ∑ x ∈ us, fR x
  let T : R := ∑ x ∈ us, fR x * fR (c x)
  have hmn : m ≤ n := by dsimp [m, n]; omega
  let phi := ZMod.castHom (show p ^ m ∣ p ^ n by exact pow_dvd_pow p hmn) S
  have hmpos : 0 < m := by dsimp [m]; omega
  have hs_mem_data {x : ℕ} (hx : x ∈ us) : x < p ^ m ∧ Nat.Coprime x (p ^ m) := by
    have h := Finset.mem_filter.mp hx
    exact ⟨Finset.mem_range.mp h.1, h.2⟩
  have hpos_of_mem {x : ℕ} (hx : x ∈ us) : 0 < x := by
    have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hx).2
    by_contra hx0
    have hxz : x = 0 := Nat.eq_zero_of_not_pos hx0
    subst hxz
    have hbad : p ^ m = 1 := by simpa [Nat.Coprime] using hxc
    have hpgt1 : 1 < p ^ m := by
      have hp1 : 1 ≤ p := by omega
      have hple : p ≤ p ^ m := le_self_pow hp1 (Nat.ne_of_gt hmpos)
      omega
    omega
  have hc_mem {x : ℕ} (hx : x ∈ us) : c x ∈ us := by
    have hxlt : x < p ^ m := (hs_mem_data hx).1
    have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hx).2
    have hxpos : 0 < x := hpos_of_mem hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · dsimp [c]; omega
    · dsimp [c]
      exact (Nat.coprime_self_sub_left (show x ≤ p ^ m by omega)).2 hxc
  have hc_invol {x : ℕ} (hx : x ∈ us) : c (c x) = x := by
    have hxlt : x < p ^ m := (hs_mem_data hx).1
    have hxpos : 0 < x := hpos_of_mem hx
    dsimp [c]; omega
  have hcast_sum {x : ℕ} (hx : x ∈ us) :
      ((x : R) + ((c x : ℕ) : R)) = ((p ^ m : ℕ) : R) := by
    have hxlt : x < p ^ m := (hs_mem_data hx).1
    have hnat : x + (p ^ m - x) = p ^ m := Nat.add_sub_of_le (show x ≤ p ^ m by omega)
    dsimp [c]
    rw [← Nat.cast_add, hnat]
  have hpair_inv {x : ℕ} (hx : x ∈ us) :
      fR x + fR (c x) = ((p ^ m : ℕ) : R) * fR x * fR (c x) := by
    have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hx).2
    have hcc : Nat.Coprime (c x) (p ^ m) := (hs_mem_data (hc_mem hx)).2
    have hxunit : IsUnit ((x : ℕ) : R) := by
      simpa using coprime_add_pow_mul_isUnit_zmod_pow_oeis_361883
        (p := p) (m := m) (n := n) (v := 0) (x := x) hp hmpos hxc
    have hcunit : IsUnit (((c x : ℕ) : R)) := by
      simpa using coprime_add_pow_mul_isUnit_zmod_pow_oeis_361883
        (p := p) (m := m) (n := n) (v := 0) (x := c x) hp hmpos hcc
    rcases hxunit with ⟨ux, hux⟩
    rcases hcunit with ⟨uc, huc⟩
    have hxmul : ((x : ℕ) : R) * fR x = 1 := by
      dsimp [fR]; rw [← hux, ZMod.inv_coe_unit]; exact Units.mul_inv ux
    have hcmul : ((c x : ℕ) : R) * fR (c x) = 1 := by
      dsimp [fR]; rw [← huc, ZMod.inv_coe_unit]; exact Units.mul_inv uc
    calc
      fR x + fR (c x) = (((x : ℕ) : R) * fR x) * fR (c x) + (((c x : ℕ) : R) * fR (c x)) * fR x := by
        rw [hxmul, hcmul]
        ring
      _ = (((x : ℕ) : R) + ((c x : ℕ) : R)) * fR x * fR (c x) := by ring
      _ = ((p ^ m : ℕ) : R) * fR x * fR (c x) := by rw [hcast_sum hx]
  have hA_comp : A = ∑ x ∈ us, fR (c x) := by
    dsimp [A]
    refine Finset.sum_bij (fun x _ => c x) ?_ ?_ ?_ ?_
    · intro x hx; exact hc_mem hx
    · intro x hx y hy hxy
      have hxlt : x < p ^ m := (hs_mem_data hx).1
      have hylt : y < p ^ m := (hs_mem_data hy).1
      dsimp [c] at hxy
      omega
    · intro y hy
      refine ⟨c y, hc_mem hy, ?_⟩
      exact hc_invol hy
    · intro x hx
      rw [hc_invol hx]
  have htwoA : (2 : R) * A = ((p ^ m : ℕ) : R) * T := by
    calc
      (2 : R) * A = A + A := by ring
      _ = (∑ x ∈ us, fR x) + (∑ x ∈ us, fR (c x)) := by
        nth_rewrite 2 [hA_comp]
        rfl
      _ = ∑ x ∈ us, (fR x + fR (c x)) := by rw [Finset.sum_add_distrib]
      _ = ∑ x ∈ us, (((p ^ m : ℕ) : R) * fR x * fR (c x)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hpair_inv hx
      _ = ((p ^ m : ℕ) : R) * T := by
        dsimp [T]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
  have hphi_f {x : ℕ} (hxmem : x ∈ us) : phi (fR x) = fS x := by
    have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hxmem).2
    simpa [phi, fR, fS, R, S] using
      zmod_castHom_inv_pow_to_pow_of_coprime_shift_oeis_361883 (p := p) (m := m) (n := n)
        (v := 0) (x := x) hp hmn hmpos hxc
  have hphi_T : phi T = 0 := by
    calc
      phi T = ∑ x ∈ us, fS x * fS (c x) := by
        dsimp [T]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [map_mul, hphi_f hx, hphi_f (hc_mem hx)]
      _ = ∑ x ∈ us, - (fS x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt : x < p ^ m := (hs_mem_data hx).1
        have hnat : x + (p ^ m - x) = p ^ m := Nat.add_sub_of_le (show x ≤ p ^ m by omega)
        have hsum0 : ((x : ℕ) : S) + ((c x : ℕ) : S) = 0 := by
          dsimp [c]
          rw [← Nat.cast_add, hnat]
          simp [S]
        have hc_eq_neg : ((c x : ℕ) : S) = - ((x : ℕ) : S) := eq_neg_of_add_eq_zero_right hsum0
        have hf_neg : fS (c x) = - fS x := by
          dsimp [fS]
          rw [hc_eq_neg]
          have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hx).2
          have hxunitS : IsUnit ((x : ℕ) : S) := (ZMod.isUnit_iff_coprime x (p ^ m)).2 hxc
          rcases hxunitS with ⟨u, hu⟩
          rw [← hu, ZMod.inv_coe_unit]
          change (-(u : S))⁻¹ = -↑(u⁻¹)
          rw [show -(u : S) = ((-u : Sˣ) : S) by rfl]
          rw [ZMod.inv_coe_unit]
          rfl
        rw [hf_neg]
        ring
      _ = - (∑ x ∈ us, (fS x) ^ 2) := by rw [Finset.sum_neg_distrib]
      _ = 0 := by
        dsimp [us, fS, S]
        rw [sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p m hp hp5, neg_zero]
  have hkill_T : ((p ^ (s + t + 2) : ℕ) : R) * T = 0 := by
    apply zmod_pow_mul_eq_zero_of_castHom_pow_eq_zero_oeis_361883 (p := p) hp hmn
    · dsimp [m, n]
      omega
    · exact hphi_T
  have htwo_goal : (2 : R) * ((((p ^ (s + 1) * b : ℕ) : R)) * A) = 0 := by
    calc
      (2 : R) * ((((p ^ (s + 1) * b : ℕ) : R)) * A) = (((p ^ (s + 1) * b : ℕ) : R)) * ((2 : R) * A) := by ring
      _ = (((p ^ (s + 1) * b : ℕ) : R)) * (((p ^ m : ℕ) : R) * T) := by rw [htwoA]
      _ = (b : R) * (((p ^ (s + t + 2) : ℕ) : R) * T) := by
        rw [Nat.cast_mul, Nat.cast_pow]
        rw [show (((p ^ m : ℕ) : R)) = (p : R) ^ (t + 1) by dsimp [m]; rw [Nat.cast_pow]]
        rw [show (((p ^ (s + t + 2) : ℕ) : R)) = (p : R) ^ ((s + 1) + (t + 1)) by
          rw [show s + t + 2 = (s + 1) + (t + 1) by omega, Nat.cast_pow]]
        ring
      _ = 0 := by rw [hkill_T, mul_zero]
  have htwo_unit : IsUnit (2 : R) := by
    apply (ZMod.isUnit_iff_coprime 2 (p ^ n)).2
    exact coprime_two_pow_prime_oeis_361883 (r := n) hp hp5


  change (((p ^ (s + 1) * b : ℕ) : R)) * A = 0
  rcases htwo_unit with ⟨u, hu⟩
  have h : (u : R) * ((((p ^ (s + 1) * b : ℕ) : R)) * A) = 0 := by
    simpa [hu] using htwo_goal
  have h' : ((((p ^ (s + 1) * b : ℕ) : R)) * A) * (u : R) = 0 := by
    simpa [mul_comm] using h
  exact (Units.mul_left_eq_zero u).mp h'

/-- Strong asymmetric unit-superblock product shift.  The block length is `p^(t+1)`,
the shift has valuation `s+1`, and the modulus is `p^(s+2*t+3)` for `t ≤ s`. -/
lemma unit_superblock_shift_asym_zmod_oeis_361883 {p s t b : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hst : t ≤ s) :
  let m := t + 1
  let R := ZMod (p ^ (s + 2 * t + 3))
  (∏ x ∈ (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)),
      ((p ^ (s + 1) * b + x : ℕ) : R)) =
    (∏ x ∈ (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)),
      ((x : ℕ) : R)) := by
  classical
  intro m R
  let n := s + 2 * t + 3
  let us := (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m))
  let δ : R := ((p ^ (s + 1) * b : ℕ) : R)
  let f : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  have hmpos : 0 < m := by dsimp [m]; omega
  have hδ3 : δ ^ 3 = 0 := by
    dsimp [δ, R]
    rw [← Nat.cast_pow]
    apply (ZMod.natCast_eq_zero_iff ((p ^ (s + 1) * b) ^ 3) (p ^ n)).2
    rw [mul_pow]
    have hpowdvd : p ^ n ∣ (p ^ (s + 1)) ^ 3 := by
      rw [← pow_mul]
      apply pow_dvd_pow
      dsimp [n]
      omega
    exact dvd_mul_of_dvd_left hpowdvd (b ^ 3)
  have hS1 : δ * (∑ x ∈ us, f x) = 0 := by
    dsimp [δ, f, us, R, n]
    simpa [m, n] using unit_superblock_shift_asym_zmod_hS1_oeis_361883
      (p := p) (s := s) (t := t) (b := b) hp hp5
  have hS2 : δ ^ 2 * (∑ x ∈ us, ∑ y ∈ us.filter (fun y => y < x), f y * f x) = 0 := by
    dsimp [δ, f, us, R, n]
    simpa [m, n] using unit_superblock_shift_asym_zmod_hS2_oeis_361883
      (p := p) (s := s) (t := t) (b := b) hp hp5 hst
  have hratio : (∏ x ∈ us, (1 + δ * f x)) = (1 : R) := by
    have htrunc := finset_prod_one_add_nilpotent_order3_oeis_361883 (s := us) (δ := δ) (f := f) hδ3
    rw [htrunc]
    rw [hS1, hS2]
    simp
  change (∏ x ∈ us, ((p ^ (s + 1) * b + x : ℕ) : R)) = (∏ x ∈ us, ((x : ℕ) : R))
  calc
    (∏ x ∈ us, ((p ^ (s + 1) * b + x : ℕ) : R)) =
        ∏ x ∈ us, (((x : ℕ) : R) * (1 + δ * f x)) := by
      apply Finset.prod_congr rfl
      intro x hx
      have hxc : Nat.Coprime x (p ^ m) := (Finset.mem_filter.mp hx).2
      dsimp [δ, f, R]
      simpa using superblock_shift_factor_eq_mul_one_add_asym_oeis_361883
        (p := p) (m := m) (n := n) (k := s + 1) (b := b) (v := 0) (x := x) hp hmpos hxc
    _ = (∏ x ∈ us, ((x : ℕ) : R)) * (∏ x ∈ us, (1 + δ * f x)) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ x ∈ us, ((x : ℕ) : R)) := by rw [hratio, mul_one]


/-- Offset quadratic inverse-pair annihilation for an asymmetric superblock. -/
lemma unit_superblock_shift_asym_offset_zmod_hS2_oeis_361883 {p s t b v : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hst : t ≤ s) :
  let m := t + 1
  let n := s + 2 * t + 3
  ((((p ^ (s + 1) * b : ℕ) : ZMod (p ^ n))) ^ 2) *
    (∑ x ∈ (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)),
      ∑ y ∈ ((Finset.range (p ^ m)).filter (fun y => Nat.Coprime y (p ^ m))).filter (fun y => y < x),
        ((((p ^ m * v + y : ℕ) : ZMod (p ^ n)))⁻¹) *
          ((((p ^ m * v + x : ℕ) : ZMod (p ^ n)))⁻¹)) = 0 := by
  classical
  intro m n
  let R := ZMod (p ^ n)
  let S := ZMod (p ^ m)
  let us := (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m))
  let fR : ℕ → R := fun x => ((((p ^ m * v + x : ℕ) : R))⁻¹)
  let fS : ℕ → S := fun x => (((x : ℕ) : S)⁻¹)
  let E : R := ∑ x ∈ us, ∑ y ∈ us.filter (fun y => y < x), fR y * fR x
  let D : R := ∑ x ∈ us, (fR x) ^ 2
  let A : R := ∑ x ∈ us, fR x
  have hmn : m ≤ n := by dsimp [m, n]; omega
  let phi := ZMod.castHom (show p ^ m ∣ p ^ n by exact pow_dvd_pow p hmn) S
  have hmpos : 0 < m := by dsimp [m]; omega
  have hphi_f (x : ℕ) (hxmem : x ∈ us) : phi (fR x) = fS x := by
    have hxc : Nat.Coprime x (p ^ m) := (Finset.mem_filter.mp hxmem).2
    simpa [phi, fR, fS, R, S] using
      zmod_castHom_inv_pow_to_pow_of_coprime_shift_oeis_361883 (p := p) (m := m) (n := n)
        (v := v) (x := x) hp hmn hmpos hxc
  have hphi_A : phi A = 0 := by
    calc
      phi A = ∑ x ∈ us, fS x := by
        dsimp [A]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hxmem
        simpa using hphi_f x hxmem
      _ = 0 := by
        dsimp [us, fS, S]
        exact sum_range_coprime_inv_zmod_pow_eq_zero_oeis_361883 p m hp hp5
  have hphi_D : phi D = 0 := by
    calc
      phi D = ∑ x ∈ us, (fS x) ^ 2 := by
        dsimp [D]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hxmem
        rw [map_pow, hphi_f x hxmem]
      _ = 0 := by
        dsimp [us, fS, S]
        exact sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p m hp hp5
  have hpair_id : A ^ 2 = D + 2 * E := by
    dsimp [A, D, E, fR, us]
    exact finset_sum_sq_eq_diag_add_two_ordered_pairs_oeis_361883
      ((Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)))
      (fun x => ((((p ^ m * v + x : ℕ) : R))⁻¹))
  have hphi_E : phi E = 0 := by
    have htwo : (2 : S) * phi E = 0 := by
      have hcalc : phi (A ^ 2) = phi D + (2 : S) * phi E := by
        rw [hpair_id, map_add, map_mul, map_ofNat]
      rw [map_pow, hphi_A, zero_pow (by norm_num : 2 ≠ 0), hphi_D] at hcalc
      simpa using hcalc.symm
    have htwo_unit : IsUnit (2 : S) := by
      apply (ZMod.isUnit_iff_coprime 2 (p ^ m)).2
      exact coprime_two_pow_prime_oeis_361883 (r := m) hp hp5
    rcases htwo_unit with ⟨u, hu⟩
    have h : (u : S) * phi E = 0 := by simpa [hu] using htwo
    have h' : phi E * (u : S) = 0 := by simpa [mul_comm] using h
    exact (Units.mul_left_eq_zero u).mp h'
  have hkill_E : ((p ^ (2 * s + 2) : ℕ) : R) * E = 0 := by
    apply zmod_pow_mul_eq_zero_of_castHom_pow_eq_zero_oeis_361883 (p := p) hp hmn
    · dsimp [m, n]
      omega
    · exact hphi_E
  change (((p ^ (s + 1) * b : ℕ) : R) ^ 2) * E = 0
  calc
    (((p ^ (s + 1) * b : ℕ) : R) ^ 2) * E = (b ^ 2 : R) * (((p ^ (2 * s + 2) : ℕ) : R) * E) := by
      rw [Nat.cast_mul, Nat.cast_pow]
      rw [show (((p ^ (2 * s + 2) : ℕ) : R)) = (p : R) ^ (2 * (s + 1)) by
        rw [show 2 * s + 2 = 2 * (s + 1) by omega, Nat.cast_pow]]
      ring
    _ = 0 := by rw [hkill_E, mul_zero]

/-- Offset linear inverse-sum annihilation for an asymmetric superblock. -/
lemma unit_superblock_shift_asym_offset_zmod_hS1_oeis_361883 {p s t b v : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
  let m := t + 1
  let n := s + 2 * t + 3
  (((p ^ (s + 1) * b : ℕ) : ZMod (p ^ n))) *
    (∑ x ∈ (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)),
      ((((p ^ m * v + x : ℕ) : ZMod (p ^ n)))⁻¹)) = 0 := by
  classical
  intro m n
  let R := ZMod (p ^ n)
  let S := ZMod (p ^ m)
  let us := (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m))
  let c : ℕ → ℕ := fun x => p ^ m - x
  let fR : ℕ → R := fun x => ((((p ^ m * v + x : ℕ) : R))⁻¹)
  let fS : ℕ → S := fun x => (((x : ℕ) : S)⁻¹)
  let A : R := ∑ x ∈ us, fR x
  let T : R := ∑ x ∈ us, fR x * fR (c x)
  have hmn : m ≤ n := by dsimp [m, n]; omega
  let phi := ZMod.castHom (show p ^ m ∣ p ^ n by exact pow_dvd_pow p hmn) S
  have hmpos : 0 < m := by dsimp [m]; omega
  have hs_mem_data {x : ℕ} (hx : x ∈ us) : x < p ^ m ∧ Nat.Coprime x (p ^ m) := by
    have h := Finset.mem_filter.mp hx
    exact ⟨Finset.mem_range.mp h.1, h.2⟩
  have hpos_of_mem {x : ℕ} (hx : x ∈ us) : 0 < x := by
    have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hx).2
    by_contra hx0
    have hxz : x = 0 := Nat.eq_zero_of_not_pos hx0
    subst hxz
    have hbad : p ^ m = 1 := by simpa [Nat.Coprime] using hxc
    have hpgt1 : 1 < p ^ m := by
      have hp1 : 1 ≤ p := by omega
      have hple : p ≤ p ^ m := le_self_pow hp1 (Nat.ne_of_gt hmpos)
      omega
    omega
  have hc_mem {x : ℕ} (hx : x ∈ us) : c x ∈ us := by
    have hxlt : x < p ^ m := (hs_mem_data hx).1
    have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hx).2
    have hxpos : 0 < x := hpos_of_mem hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · dsimp [c]; omega
    · dsimp [c]
      exact (Nat.coprime_self_sub_left (show x ≤ p ^ m by omega)).2 hxc
  have hc_invol {x : ℕ} (hx : x ∈ us) : c (c x) = x := by
    have hxlt : x < p ^ m := (hs_mem_data hx).1
    have hxpos : 0 < x := hpos_of_mem hx
    dsimp [c]; omega
  have hcast_sum {x : ℕ} (hx : x ∈ us) :
      (((p ^ m * v + x : ℕ) : R) + ((p ^ m * v + c x : ℕ) : R)) =
        ((p ^ m * (2 * v + 1) : ℕ) : R) := by
    have hxlt : x < p ^ m := (hs_mem_data hx).1
    have hnat1 : x + (p ^ m - x) = p ^ m := Nat.add_sub_of_le (show x ≤ p ^ m by omega)
    have hnat : p ^ m * v + x + (p ^ m * v + (p ^ m - x)) = p ^ m * (2 * v + 1) := by
      nlinarith
    dsimp [c]
    rw [← Nat.cast_add, hnat]
  have hpair_inv {x : ℕ} (hx : x ∈ us) :
      fR x + fR (c x) = ((p ^ m * (2 * v + 1) : ℕ) : R) * fR x * fR (c x) := by
    have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hx).2
    have hcc : Nat.Coprime (c x) (p ^ m) := (hs_mem_data (hc_mem hx)).2
    have hxunit : IsUnit (((p ^ m * v + x : ℕ) : R)) :=
      coprime_add_pow_mul_isUnit_zmod_pow_oeis_361883 (p := p) (m := m) (n := n) (v := v) (x := x) hp hmpos hxc
    have hcunit : IsUnit (((p ^ m * v + c x : ℕ) : R)) :=
      coprime_add_pow_mul_isUnit_zmod_pow_oeis_361883 (p := p) (m := m) (n := n) (v := v) (x := c x) hp hmpos hcc
    rcases hxunit with ⟨ux, hux⟩
    rcases hcunit with ⟨uc, huc⟩
    have hxmul : (((p ^ m * v + x : ℕ) : R)) * fR x = 1 := by
      dsimp [fR]; rw [← hux, ZMod.inv_coe_unit]; exact Units.mul_inv ux
    have hcmul : (((p ^ m * v + c x : ℕ) : R)) * fR (c x) = 1 := by
      dsimp [fR]; rw [← huc, ZMod.inv_coe_unit]; exact Units.mul_inv uc
    calc
      fR x + fR (c x) = (((p ^ m * v + x : ℕ) : R) * fR x) * fR (c x) + (((p ^ m * v + c x : ℕ) : R) * fR (c x)) * fR x := by
        rw [hxmul, hcmul]
        ring
      _ = (((p ^ m * v + x : ℕ) : R) + ((p ^ m * v + c x : ℕ) : R)) * fR x * fR (c x) := by ring
      _ = ((p ^ m * (2 * v + 1) : ℕ) : R) * fR x * fR (c x) := by rw [hcast_sum hx]
  have hA_comp : A = ∑ x ∈ us, fR (c x) := by
    dsimp [A]
    refine Finset.sum_bij (fun x _ => c x) ?_ ?_ ?_ ?_
    · intro x hx; exact hc_mem hx
    · intro x hx y hy hxy
      have hxlt : x < p ^ m := (hs_mem_data hx).1
      have hylt : y < p ^ m := (hs_mem_data hy).1
      dsimp [c] at hxy
      omega
    · intro y hy
      refine ⟨c y, hc_mem hy, ?_⟩
      exact hc_invol hy
    · intro x hx
      rw [hc_invol hx]
  have htwoA : (2 : R) * A = ((p ^ m * (2 * v + 1) : ℕ) : R) * T := by
    calc
      (2 : R) * A = A + A := by ring
      _ = (∑ x ∈ us, fR x) + (∑ x ∈ us, fR (c x)) := by
        nth_rewrite 2 [hA_comp]
        rfl
      _ = ∑ x ∈ us, (fR x + fR (c x)) := by rw [Finset.sum_add_distrib]
      _ = ∑ x ∈ us, (((p ^ m * (2 * v + 1) : ℕ) : R) * fR x * fR (c x)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hpair_inv hx
      _ = ((p ^ m * (2 * v + 1) : ℕ) : R) * T := by
        dsimp [T]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
  have hphi_f {x : ℕ} (hxmem : x ∈ us) : phi (fR x) = fS x := by
    have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hxmem).2
    simpa [phi, fR, fS, R, S] using
      zmod_castHom_inv_pow_to_pow_of_coprime_shift_oeis_361883 (p := p) (m := m) (n := n)
        (v := v) (x := x) hp hmn hmpos hxc
  have hphi_T : phi T = 0 := by
    calc
      phi T = ∑ x ∈ us, fS x * fS (c x) := by
        dsimp [T]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [map_mul, hphi_f hx, hphi_f (hc_mem hx)]
      _ = ∑ x ∈ us, - (fS x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt : x < p ^ m := (hs_mem_data hx).1
        have hnat : x + (p ^ m - x) = p ^ m := Nat.add_sub_of_le (show x ≤ p ^ m by omega)
        have hsum0 : ((x : ℕ) : S) + ((c x : ℕ) : S) = 0 := by
          dsimp [c]
          rw [← Nat.cast_add, hnat]
          simp [S]
        have hc_eq_neg : ((c x : ℕ) : S) = - ((x : ℕ) : S) := eq_neg_of_add_eq_zero_right hsum0
        have hf_neg : fS (c x) = - fS x := by
          dsimp [fS]
          rw [hc_eq_neg]
          have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hx).2
          have hxunitS : IsUnit ((x : ℕ) : S) := (ZMod.isUnit_iff_coprime x (p ^ m)).2 hxc
          rcases hxunitS with ⟨u, hu⟩
          rw [← hu, ZMod.inv_coe_unit]
          change (-(u : S))⁻¹ = -↑(u⁻¹)
          rw [show -(u : S) = ((-u : Sˣ) : S) by rfl]
          rw [ZMod.inv_coe_unit]
          rfl
        rw [hf_neg]
        ring
      _ = - (∑ x ∈ us, (fS x) ^ 2) := by rw [Finset.sum_neg_distrib]
      _ = 0 := by
        dsimp [us, fS, S]
        rw [sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p m hp hp5, neg_zero]
  have hkill_T : ((p ^ (s + t + 2) : ℕ) : R) * T = 0 := by
    apply zmod_pow_mul_eq_zero_of_castHom_pow_eq_zero_oeis_361883 (p := p) hp hmn
    · dsimp [m, n]
      omega
    · exact hphi_T
  have htwo_goal : (2 : R) * ((((p ^ (s + 1) * b : ℕ) : R)) * A) = 0 := by
    calc
      (2 : R) * ((((p ^ (s + 1) * b : ℕ) : R)) * A) = (((p ^ (s + 1) * b : ℕ) : R)) * ((2 : R) * A) := by ring
      _ = (((p ^ (s + 1) * b : ℕ) : R)) * (((p ^ m * (2 * v + 1) : ℕ) : R) * T) := by rw [htwoA]
      _ = ((b * (2 * v + 1) : ℕ) : R) * (((p ^ (s + t + 2) : ℕ) : R) * T) := by
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
        rw [show (((p ^ m : ℕ) : R)) = (p : R) ^ (t + 1) by dsimp [m]; rw [Nat.cast_pow]]
        rw [show (((p ^ (s + t + 2) : ℕ) : R)) = (p : R) ^ ((s + 1) + (t + 1)) by
          rw [show s + t + 2 = (s + 1) + (t + 1) by omega, Nat.cast_pow]]
        ring
      _ = 0 := by rw [hkill_T, mul_zero]
  have htwo_unit : IsUnit (2 : R) := by
    apply (ZMod.isUnit_iff_coprime 2 (p ^ n)).2
    exact coprime_two_pow_prime_oeis_361883 (r := n) hp hp5
  change (((p ^ (s + 1) * b : ℕ) : R)) * A = 0
  rcases htwo_unit with ⟨u, hu⟩
  have h : (u : R) * ((((p ^ (s + 1) * b : ℕ) : R)) * A) = 0 := by
    simpa [hu] using htwo_goal
  have h' : ((((p ^ (s + 1) * b : ℕ) : R)) * A) * (u : R) = 0 := by
    simpa [mul_comm] using h
  exact (Units.mul_left_eq_zero u).mp h'

/-- Strong asymmetric unit-superblock product shift with an additional `p^(t+1)`-multiple offset. -/
lemma unit_superblock_shift_asym_offset_zmod_oeis_361883 {p s t b v : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hst : t ≤ s) :
  let R := ZMod (p ^ (s + 2 * t + 3))
  let m := t + 1
  (∏ x ∈ (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)),
      ((p ^ (s + 1) * b + (p ^ m * v + x) : ℕ) : R)) =
    (∏ x ∈ (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)),
      (((p ^ m * v + x : ℕ) : R))) := by
  classical
  intro R m
  let n := s + 2 * t + 3
  let us := (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m))
  let δ : R := ((p ^ (s + 1) * b : ℕ) : R)
  let f : ℕ → R := fun x => ((((p ^ m * v + x : ℕ) : R))⁻¹)
  have hmpos : 0 < m := by dsimp [m]; omega
  have hδ3 : δ ^ 3 = 0 := by
    dsimp [δ, R]
    rw [← Nat.cast_pow]
    apply (ZMod.natCast_eq_zero_iff ((p ^ (s + 1) * b) ^ 3) (p ^ n)).2
    rw [mul_pow]
    have hpowdvd : p ^ n ∣ (p ^ (s + 1)) ^ 3 := by
      rw [← pow_mul]
      apply pow_dvd_pow
      dsimp [n]
      omega
    exact dvd_mul_of_dvd_left hpowdvd (b ^ 3)
  have hS1 : δ * (∑ x ∈ us, f x) = 0 := by
    dsimp [δ, f, us, R, n]
    simpa [m, n] using unit_superblock_shift_asym_offset_zmod_hS1_oeis_361883
      (p := p) (s := s) (t := t) (b := b) (v := v) hp hp5
  have hS2 : δ ^ 2 * (∑ x ∈ us, ∑ y ∈ us.filter (fun y => y < x), f y * f x) = 0 := by
    dsimp [δ, f, us, R, n]
    simpa [m, n] using unit_superblock_shift_asym_offset_zmod_hS2_oeis_361883
      (p := p) (s := s) (t := t) (b := b) (v := v) hp hp5 hst
  have hratio : (∏ x ∈ us, (1 + δ * f x)) = (1 : R) := by
    have htrunc := finset_prod_one_add_nilpotent_order3_oeis_361883 (s := us) (δ := δ) (f := f) hδ3
    rw [htrunc]
    rw [hS1, hS2]
    simp
  change (∏ x ∈ us, ((p ^ (s + 1) * b + (p ^ m * v + x) : ℕ) : R)) =
    (∏ x ∈ us, (((p ^ m * v + x : ℕ) : R)))
  calc
    (∏ x ∈ us, ((p ^ (s + 1) * b + (p ^ m * v + x) : ℕ) : R)) =
        ∏ x ∈ us, ((((p ^ m * v + x : ℕ) : R)) * (1 + δ * f x)) := by
      apply Finset.prod_congr rfl
      intro x hx
      have hxc : Nat.Coprime x (p ^ m) := (Finset.mem_filter.mp hx).2
      dsimp [δ, f, R]
      simpa using superblock_shift_factor_eq_mul_one_add_asym_oeis_361883
        (p := p) (m := m) (n := n) (k := s + 1) (b := b) (v := v) (x := x) hp hmpos hxc
    _ = (∏ x ∈ us, (((p ^ m * v + x : ℕ) : R))) * (∏ x ∈ us, (1 + δ * f x)) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ x ∈ us, (((p ^ m * v + x : ℕ) : R))) := by rw [hratio, mul_one]


/-- Rewrite a general unit superblock of length `p^(t+1)` as `p^t` consecutive ordinary
unit blocks. -/
lemma unit_superblock_asym_offset_eq_prod_blocks_oeis_361883 {p t A v n : ℕ} (hp : p.Prime) :
    let R := ZMod (p ^ n)
    let m := t + 1
    (∏ x ∈ (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)),
        ((A + (p ^ m * v + x) : ℕ) : R)) =
      ∏ u ∈ Finset.range (p ^ t),
        ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0),
          ((A + (p ^ m * v + (p * u + t0)) : ℕ) : R) := by
  classical
  intro R m
  let G : ℕ → R := fun x => ((A + (p ^ m * v + x) : ℕ) : R)
  have hiff : ∀ u ∈ Finset.range (p ^ t), ∀ t0 ∈ Finset.range p,
      (Nat.Coprime (p * u + t0) (p ^ m) ↔ 0 < t0) := by
    intro u _hu t0 ht0
    have ht0p : t0 < p := Finset.mem_range.mp ht0
    constructor
    · intro hcop
      by_contra ht0pos
      have ht0z : t0 = 0 := Nat.eq_zero_of_not_pos ht0pos
      have hdiv : p ∣ p * u + t0 := by
        rw [ht0z, add_zero]
        exact dvd_mul_right p u
      have hp_dvd_pow : p ∣ p ^ m := dvd_pow_self p (by dsimp [m]; omega)
      exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hdiv hp_dvd_pow) hcop
    · intro ht0pos
      have hnot : ¬ p ∣ p * u + t0 := by
        intro hdiv
        have hpu : p ∣ p * u := dvd_mul_right p u
        have htdiv : p ∣ t0 := (Nat.dvd_add_iff_right hpu).2 hdiv
        exact (Nat.not_dvd_of_pos_of_lt ht0pos ht0p) htdiv
      exact hp.coprime_pow_of_not_dvd hnot
  calc
    (∏ x ∈ (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)), G x)
        = ∏ x ∈ Finset.range (p ^ m), if Nat.Coprime x (p ^ m) then G x else 1 := by
          rw [Finset.prod_filter]
    _ = ∏ x ∈ Finset.range ((p ^ t) * p), if Nat.Coprime x (p ^ m) then G x else 1 := by
          rw [show p ^ m = (p ^ t) * p by dsimp [m]; rw [pow_succ']; rw [mul_comm]]
    _ = ∏ u ∈ Finset.range (p ^ t),
          ∏ t0 ∈ Finset.range p, if Nat.Coprime (p * u + t0) (p ^ m) then G (p * u + t0) else 1 := by
          rw [prod_range_mul_decomp_oeis_361883]
    _ = ∏ u ∈ Finset.range (p ^ t),
          ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0), G (p * u + t0) := by
          apply Finset.prod_congr rfl
          intro u hu
          calc
            (∏ t0 ∈ Finset.range p, if Nat.Coprime (p * u + t0) (p ^ m) then G (p * u + t0) else 1)
                = ∏ t0 ∈ Finset.range p, if 0 < t0 then G (p * u + t0) else 1 := by
                  apply Finset.prod_congr rfl
                  intro t0 ht0
                  by_cases ht0pos : 0 < t0
                  · have hc : Nat.Coprime (p * u + t0) (p ^ m) := (hiff u hu t0 ht0).2 ht0pos
                    rw [if_pos hc, if_pos ht0pos]
                  · have hnc : ¬ Nat.Coprime (p * u + t0) (p ^ m) := by
                      intro hc
                      exact ht0pos ((hiff u hu t0 ht0).1 hc)
                    rw [if_neg hnc, if_neg ht0pos]
            _ = ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0), G (p * u + t0) := by
                  exact (Finset.prod_filter (s := Finset.range p) (p := fun t0 => 0 < t0)
                    (f := fun t0 => G (p * u + t0))).symm
    _ = ∏ u ∈ Finset.range (p ^ t),
        ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0),
          ((A + (p ^ m * v + (p * u + t0)) : ℕ) : R) := by
          rfl

/-- A group of `p^t` ordinary unit blocks is invariant under a `p^s` block shift at the
split precision `p^(s+2*t+3)`, for `t ≤ s`. -/
lemma unit_block_supergroup_shift_asym_zmod_oeis_361883 {p s t b v : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hst : t ≤ s) :
    let R := ZMod (p ^ (s + 2 * t + 3))
    (∏ u ∈ Finset.range (p ^ t),
        ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0),
          ((p * (p ^ s * b + (p ^ t * v + u)) + t0 : ℕ) : R)) =
      ∏ u ∈ Finset.range (p ^ t),
        ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0),
          ((p * (p ^ t * v + u) + t0 : ℕ) : R) := by
  classical
  intro R
  let m := t + 1
  let Sshift : R := ∏ x ∈ (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)),
      ((p ^ (s + 1) * b + (p ^ m * v + x) : ℕ) : R)
  let Sbase : R := ∏ x ∈ (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)),
      (((p ^ m * v + x : ℕ) : R))
  have hleft :
      (∏ u ∈ Finset.range (p ^ t),
        ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0),
          ((p * (p ^ s * b + (p ^ t * v + u)) + t0 : ℕ) : R)) = Sshift := by
    calc
      (∏ u ∈ Finset.range (p ^ t),
        ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0),
          ((p * (p ^ s * b + (p ^ t * v + u)) + t0 : ℕ) : R))
        = ∏ u ∈ Finset.range (p ^ t),
            ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0),
              ((p ^ (s + 1) * b + (p ^ m * v + (p * u + t0)) : ℕ) : R) := by
            apply Finset.prod_congr rfl
            intro u hu
            apply Finset.prod_congr rfl
            intro t0 ht0
            congr 1
            dsimp [m]
            rw [pow_succ', pow_succ']
            ring
      _ = Sshift := by
            dsimp [Sshift]
            rw [unit_superblock_asym_offset_eq_prod_blocks_oeis_361883 (p := p) (t := t)
              (A := p ^ (s + 1) * b) (v := v) (n := s + 2 * t + 3) hp]
  have hright :
      (∏ u ∈ Finset.range (p ^ t),
        ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0),
          ((p * (p ^ t * v + u) + t0 : ℕ) : R)) = Sbase := by
    calc
      (∏ u ∈ Finset.range (p ^ t),
        ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0),
          ((p * (p ^ t * v + u) + t0 : ℕ) : R))
        = ∏ u ∈ Finset.range (p ^ t),
            ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0),
              (((p ^ m * v + (p * u + t0) : ℕ) : R)) := by
            apply Finset.prod_congr rfl
            intro u hu
            apply Finset.prod_congr rfl
            intro t0 ht0
            congr 1
            dsimp [m]
            rw [pow_succ']
            ring
      _ = Sbase := by
            simpa [Sbase, m] using
              (unit_superblock_asym_offset_eq_prod_blocks_oeis_361883 (p := p) (t := t)
                (A := 0) (v := v) (n := s + 2 * t + 3) hp).symm
  have hshift : Sshift = Sbase := by
    dsimp [Sshift, Sbase, R, m]
    simpa using unit_superblock_shift_asym_offset_zmod_oeis_361883
      (p := p) (s := s) (t := t) (b := b) (v := v) hp hp5 hst
  exact hleft.trans (hshift.trans hright.symm)










/-- If a natural number is divisible by `p^r`, then its cube vanishes in `ZMod (p^(3*r))`. -/
lemma zmod_nat_cast_pow_three_eq_zero_of_pow_dvd_oeis_361883 {p r N : ℕ}
    (hN : p ^ r ∣ N) :
    ((N : ZMod (p ^ (3 * r))) ^ 3) = 0 := by
  rw [← Nat.cast_pow]
  apply (ZMod.natCast_eq_zero_iff (N ^ 3) (p ^ (3 * r))).2
  rcases hN with ⟨u, rfl⟩
  use u ^ 3
  rw [mul_pow]
  rw [← pow_mul]
  ring_nf


/-- A variant of the nilpotence helper for any modulus exponent at most `3*r`. -/
lemma zmod_nat_cast_pow_three_eq_zero_of_pow_dvd_le_oeis_361883 {p r m N : ℕ}
    (hN : p ^ r ∣ N) (hm : m ≤ 3 * r) :
    ((N : ZMod (p ^ m)) ^ 3) = 0 := by
  rw [← Nat.cast_pow]
  apply (ZMod.natCast_eq_zero_iff (N ^ 3) (p ^ m)).2
  rcases hN with ⟨u, rfl⟩
  refine (pow_dvd_pow p hm).trans ?_
  use u ^ 3
  rw [mul_pow, ← pow_mul]
  ring_nf


/-- If `m ∣ q` and `l` is a unit modulo `m`, then consecutive upper parameters give congruent binomial coefficients. -/
lemma choose_add_modEq_prev_of_dvd_oeis_361883 {m q l : ℕ}
    (hl : 0 < l) (hmq : m ∣ q) (hc : Nat.Coprime l m) :
    Nat.choose (q + l) q ≡ Nat.choose (q + l - 1) q [MOD m] := by
  have hmul : Nat.choose (q + l - 1) q * (q + l) = Nat.choose (q + l) q * l := by
    have h := Nat.choose_mul_succ_eq (q + l - 1) q
    have hsucc : q + l - 1 + 1 = q + l := Nat.succ_pred_eq_of_pos (Nat.add_pos_right q hl)
    have hsub : q + l - q = l := by omega
    simpa [hsucc, hsub] using h
  have hmod : Nat.choose (q + l) q * l ≡ Nat.choose (q + l - 1) q * l [MOD m] := by
    rw [← hmul]
    have hqmod : Nat.choose (q + l - 1) q * (q + l) ≡
        Nat.choose (q + l - 1) q * (0 + l) [MOD m] := by
      apply Nat.ModEq.mul_left
      apply Nat.ModEq.add
      · exact (Nat.modEq_zero_iff_dvd.mpr hmq)
      · rfl
    simpa using hqmod
  exact Nat.ModEq.cancel_right_of_coprime (by rw [Nat.gcd_comm]; exact hc) hmod


/-- Within a block `p*j+t`, the binomial `choose (q+k-1) q` is independent of `t` modulo `p^r`, provided `p^r ∣ q`. -/
lemma choose_block_const_modEq_oeis_361883 {p r q j t : ℕ} (hp : p.Prime) (hq : p ^ r ∣ q)
    (ht0 : 0 < t) (htp : t < p) :
    Nat.choose (q + (p * j + t) - 1) q ≡ Nat.choose (q + p * j) q [MOD p ^ r] := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases htzero : t = 0
      · subst t
        have h : q + (p * j + 1) - 1 = q + p * j := by omega
        rw [h]
      · have htpos : 0 < t := Nat.pos_of_ne_zero htzero
        have htp' : t < p := by omega
        have hstep : Nat.choose (q + (p * j + (t + 1)) - 1) q ≡
            Nat.choose (q + (p * j + t) - 1) q [MOD p ^ r] := by
          have hnot : ¬ p ∣ p * j + t := by
            intro h
            have ht_dvd : p ∣ t := by
              have hmul : p ∣ p * j := dvd_mul_right p j
              exact (Nat.dvd_add_iff_right hmul).2 h
            exact (Nat.not_dvd_of_pos_of_lt htpos htp') ht_dvd
          have hc : Nat.Coprime (p * j + t) (p ^ r) :=
            Nat.Coprime.pow_right r (((hp.coprime_iff_not_dvd).2 hnot).symm)
          have hl : 0 < p * j + t := by omega
          have hsimp1 : q + (p * j + (t + 1)) - 1 = q + (p * j + t) := by omega
          simpa [hsimp1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            choose_add_modEq_prev_of_dvd_oeis_361883 (q := q) (l := p * j + t) hl hq hc
        exact hstep.trans (ih htpos htp')

/-- If two binomial factors are congruent modulo `p^r`, then after multiplying by `q^2` with `p^r ∣ q`, their cubes are congruent modulo `p^(3*r)`. -/
lemma weighted_cube_modEq_of_modEq_of_pow_dvd_oeis_361883 {p r q C D : ℕ}
    (hC : C ≡ D [MOD p ^ r]) (hq : p ^ r ∣ q) :
    q ^ 2 * C ^ 3 ≡ q ^ 2 * D ^ 3 [MOD p ^ (3 * r)] := by
  have hpow : C ^ 3 ≡ D ^ 3 [MOD p ^ r] := hC.pow 3
  have hmul : q ^ 2 * C ^ 3 ≡ q ^ 2 * D ^ 3 [MOD q ^ 2 * p ^ r] := hpow.mul_left' (q ^ 2)
  apply hmul.of_dvd
  rcases hq with ⟨u, rfl⟩
  use u ^ 2
  rw [mul_pow]
  rw [← pow_mul]
  ring_nf



/--
In an off-diagonal position `k = p*j+t`, the summand has a simple form modulo
`p^(3*r)`: after using the adjacent binomial relation, its cubic part vanishes.
-/
lemma offdiag_T_zmod_approx_oeis_361883 {p M r j t : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hMpos : 0 < M) (hM : p ^ (r - 1) ∣ M) (ht0 : 0 < t) (htp : t < p) :
    let k := p * j + t
    let C := Nat.choose (M * p + k - 1) (M * p)
    let u : (ZMod (p ^ (3 * r)))ˣ := ZMod.unitOfCoprime k (by
      have hnot : ¬ p ∣ k := by
        intro h
        have ht_dvd : p ∣ t := by
          have hmul : p ∣ p * j := dvd_mul_right p j
          exact (Nat.dvd_add_iff_right hmul).2 h
        exact (Nat.not_dvd_of_pos_of_lt ht0 htp) ht_dvd
      exact Nat.Coprime.pow_right (3 * r) (((hp.coprime_iff_not_dvd).2 hnot).symm))
    (oeis_361883_T (M * p) k : ZMod (p ^ (3 * r))) =
      2 * (M * p : ZMod (p ^ (3 * r))) ^ 2 * (C : ZMod (p ^ (3 * r))) ^ 3 *
        ((u : ZMod (p ^ (3 * r)))⁻¹) ^ 2 := by
  intro k C u
  let R := ZMod (p ^ (3 * r))
  let A := Nat.choose (M * p + k - 1) (M * p - 1)
  have hp0 : 0 < p := hp.pos
  have hNpos : 0 < M * p := Nat.mul_pos hMpos hp0
  have hT := oeis_361883_T_eq_sq_mul (N := M * p) (k := k) hNpos
  have hrel_nat : A * k = C * (M * p) := by
    dsimp [A, C]
    exact (choose_adjacent_mul_for_oeis_361883 (n := M * p) (k := k) hNpos).symm
  have hrel : (A : R) * (k : R) = (C : R) * (M * p : R) := by
    have hcast := congrArg (fun x : ℕ => (x : R)) hrel_nat
    simpa [Nat.cast_mul] using hcast
  have hu : (u : R) = (k : R) := rfl
  have hAeq : (A : R) = (C : R) * (M * p : R) * ((u : R)⁻¹) := by
    have this := congrArg (fun x : R => x * ((u : R)⁻¹)) hrel
    rw [← hu] at this
    change ((A : R) * (u : R)) * (u : R)⁻¹ = ((C : R) * (M * p : R)) * (u : R)⁻¹ at this
    have hunit : (u : R) * (u : R)⁻¹ = 1 := Units.mul_inv u
    have hleft : (A : R) * (u : R) * (u : R)⁻¹ = (A : R) := by
      calc
        (A : R) * (u : R) * (u : R)⁻¹ = (A : R) * ((u : R) * (u : R)⁻¹) := by ring
        _ = (A : R) := by rw [hunit, mul_one]
    rw [hleft] at this
    rw [this]
  have hNcube : ((M * p : R) ^ 3) = 0 := by
    simpa [Nat.cast_mul] using (zmod_nat_cast_pow_three_eq_zero_of_pow_dvd_oeis_361883 (p := p) (r := r) (N := M * p)
      (pow_dvd_mul_of_pred_pow_dvd_oeis_361883 hr hM (le_refl r)))
  have hT' : oeis_361883_T (M * p) k = A ^ 2 * (A + 2 * C) := by
    simpa [A, C] using hT
  change ((oeis_361883_T (M * p) k : ℕ) : R) =
    2 * (M * p : R) ^ 2 * (C : R) ^ 3 * ((u : R)⁻¹) ^ 2
  rw [hT']
  norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
  rw [hAeq]
  let X : R := (M * p : R)
  let Y : R := (C : R)
  let V : R := ((u : R)⁻¹)
  change (Y * X * V) ^ 2 * (Y * X * V + 2 * Y) = 2 * X ^ 2 * Y ^ 3 * V ^ 2
  have halg : (Y * X * V) ^ 2 * (Y * X * V + 2 * Y) =
      X ^ 3 * Y ^ 3 * V ^ 3 + 2 * X ^ 2 * Y ^ 3 * V ^ 2 := by ring
  rw [halg]
  have hXcube : X ^ 3 = 0 := by simpa [X] using hNcube
  rw [hXcube]
  simp



/--
Combining the off-diagonal approximation with the fact that the remaining binomial factor is
constant inside a nonzero `p`-block modulo `p^r`, the off-diagonal summand depends on `t` only
through the inverse-square unit, modulo `p^(3*r)`.
-/
lemma offdiag_T_zmod_approx_const_oeis_361883 {p M r j t : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hMpos : 0 < M) (hM : p ^ (r - 1) ∣ M) (ht0 : 0 < t) (htp : t < p) :
    let k := p * j + t
    let D := Nat.choose (M * p + p * j) (M * p)
    let u : (ZMod (p ^ (3 * r)))ˣ := ZMod.unitOfCoprime k (by
      have hnot : ¬ p ∣ k := by
        intro h
        have ht_dvd : p ∣ t := by
          have hmul : p ∣ p * j := dvd_mul_right p j
          exact (Nat.dvd_add_iff_right hmul).2 h
        exact (Nat.not_dvd_of_pos_of_lt ht0 htp) ht_dvd
      exact Nat.Coprime.pow_right (3 * r) (((hp.coprime_iff_not_dvd).2 hnot).symm))
    (oeis_361883_T (M * p) k : ZMod (p ^ (3 * r))) =
      2 * (M * p : ZMod (p ^ (3 * r))) ^ 2 * (D : ZMod (p ^ (3 * r))) ^ 3 *
        ((u : ZMod (p ^ (3 * r)))⁻¹) ^ 2 := by
  intro k D u
  let R := ZMod (p ^ (3 * r))
  let C := Nat.choose (M * p + k - 1) (M * p)
  have hqdiv : p ^ r ∣ M * p := pow_dvd_mul_of_pred_pow_dvd_oeis_361883 hr hM (le_refl r)
  have hCmod : C ≡ D [MOD p ^ r] := by
    dsimp [C, D, k]
    exact choose_block_const_modEq_oeis_361883 hp hqdiv ht0 htp
  have hweighted : (M * p) ^ 2 * C ^ 3 ≡ (M * p) ^ 2 * D ^ 3 [MOD p ^ (3 * r)] :=
    weighted_cube_modEq_of_modEq_of_pow_dvd_oeis_361883 hCmod hqdiv
  have hcast0 : (((M * p) ^ 2 * C ^ 3 : ℕ) : R) = (((M * p) ^ 2 * D ^ 3 : ℕ) : R) := by
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hweighted
  have hcast : ((M * p : R) ^ 2 * (C : R) ^ 3) = ((M * p : R) ^ 2 * (D : R) ^ 3) := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hcast0
  have happ := offdiag_T_zmod_approx_oeis_361883 (p := p) (M := M) (r := r) (j := j) (t := t) hp hr hMpos hM ht0 htp
  dsimp at happ
  change (oeis_361883_T (M * p) k : R) = 2 * (M * p : R) ^ 2 * (D : R) ^ 3 * ((u : R)⁻¹) ^ 2
  rw [happ]
  change 2 * (M * p : R) ^ 2 * (C : R) ^ 3 * ((u : R)⁻¹) ^ 2 =
    2 * (M * p : R) ^ 2 * (D : R) ^ 3 * ((u : R)⁻¹) ^ 2
  calc
    2 * (M * p : R) ^ 2 * (C : R) ^ 3 * ((u : R)⁻¹) ^ 2
        = 2 * ((M * p : R) ^ 2 * (C : R) ^ 3) * ((u : R)⁻¹) ^ 2 := by ring
    _ = 2 * ((M * p : R) ^ 2 * (D : R) ^ 3) * ((u : R)⁻¹) ^ 2 := by rw [hcast]
    _ = 2 * (M * p : R) ^ 2 * (D : R) ^ 3 * ((u : R)⁻¹) ^ 2 := by ring


/-- A finite-field power sum used to express inverse-square cancellation modulo `p`. -/
lemma zmod_sum_pow_p_sub_three_eq_zero_oeis_361883 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (∑ x : ZMod p, x ^ (p - 3)) = 0 := by
  have hp3lt : p - 3 < Fintype.card (ZMod p) - 1 := by
    rw [ZMod.card]
    omega
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) (p - 3) hp3lt

/-- General finite-field power-sum vanishing over `ZMod p` for exponents below `p-1`. -/
lemma zmod_sum_pow_lt_p_sub_one_eq_zero_oeis_361883 (p e : ℕ) [Fact p.Prime]
    (he : e < p - 1) :
    (∑ x : ZMod p, x ^ e) = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : e < Fintype.card (ZMod p) - 1 := by
    simpa [ZMod.card] using he
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) e hcard


/-- For nonzero elements of `ZMod p`, inverse-square equals the `p-3` power. -/
lemma zmod_inv_sq_eq_pow_sub_three_oeis_361883 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    {x : ZMod p} (hx : x ≠ 0) :
    x⁻¹ ^ 2 = x ^ (p - 3) := by
  have hfermat : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
  have hsum : 2 + (p - 3) = p - 1 := by omega
  have hmul : x ^ 2 * x ^ (p - 3) = 1 := by
    rw [← pow_add, hsum, hfermat]
  rw [inv_pow]
  exact (eq_inv_of_mul_eq_one_right hmul).symm


/-- The natural representatives `0, ..., p-1` sum over all elements of `ZMod p`. -/
lemma zmod_sum_range_pow_eq_sum_univ_oeis_361883 (p e : ℕ) [NeZero p] :
    (∑ t ∈ Finset.range p, (t : ZMod p) ^ e) = ∑ x : ZMod p, x ^ e := by
  symm
  refine Finset.sum_bij (fun x _ => (x : ZMod p).val) ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro x y hx hy hxy
    exact ZMod.val_injective (n := p) hxy
  · intro t ht
    refine ⟨(t : ZMod p), Finset.mem_univ _, ?_⟩
    exact (ZMod.val_natCast p t).trans (Nat.mod_eq_of_lt (Finset.mem_range.mp ht))
  · intro x hx
    rw [ZMod.natCast_zmod_val]

/-- Representative version of finite-field power-sum vanishing for exponents below `p-1`. -/
lemma zmod_sum_range_pow_lt_p_sub_one_eq_zero_oeis_361883 (p e : ℕ) [Fact p.Prime]
    (he : e < p - 1) :
    (∑ t ∈ Finset.range p, (t : ZMod p) ^ e) = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [zmod_sum_range_pow_eq_sum_univ_oeis_361883 p e]
  exact zmod_sum_pow_lt_p_sub_one_eq_zero_oeis_361883 p e he


/-- The inverse-square sum over representatives modulo `p` is zero in `ZMod p`. -/
lemma zmod_sum_range_inv_sq_eq_zero_oeis_361883 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (∑ t ∈ Finset.range p, ((t : ZMod p)⁻¹) ^ 2) = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpow : (∑ t ∈ Finset.range p, (t : ZMod p) ^ (p - 3)) = 0 := by
    rw [zmod_sum_range_pow_eq_sum_univ_oeis_361883 p (p - 3)]
    exact zmod_sum_pow_p_sub_three_eq_zero_oeis_361883 p hp5
  calc
    (∑ t ∈ Finset.range p, ((t : ZMod p)⁻¹) ^ 2) = ∑ t ∈ Finset.range p, (t : ZMod p) ^ (p - 3) := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases ht0 : (t : ZMod p) = 0
      · rw [ht0]
        have hp3pos : 0 < p - 3 := by omega
        simp [hp3pos.ne']
      · exact zmod_inv_sq_eq_pow_sub_three_oeis_361883 p hp5 ht0
    _ = 0 := hpow

/-- The same inverse-square cancellation with the zero representative removed. -/
lemma zmod_sum_range_pos_inv_sq_eq_zero_oeis_361883 (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (∑ t ∈ (Finset.range p).filter (fun t => 0 < t), ((t : ZMod p)⁻¹) ^ 2) = 0 := by
  have h := zmod_sum_range_inv_sq_eq_zero_oeis_361883 p hp5
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range p) (p := fun t => 0 < t)
    (f := fun t => ((t : ZMod p)⁻¹) ^ 2)] at h
  have hzero : (∑ x ∈ (Finset.range p).filter (fun t => ¬0 < t), ((x : ZMod p)⁻¹) ^ 2) = 0 := by
    rw [Finset.sum_eq_zero]
    intro x hx
    have hx0 : x = 0 := by
      have hnot : ¬0 < x := (Finset.mem_filter.mp hx).2
      exact Nat.eq_zero_of_not_pos hnot
    simp [hx0]
  rw [hzero, add_zero] at h
  exact h


/-- The shifted nonzero block inverse-square sum vanishes modulo `p`. -/
lemma inner_inv_sq_mod_p_zero_oeis_361883 {p j : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    (∑ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * j + t : ZMod p)⁻¹) ^ 2) = 0 := by
  calc
    (∑ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * j + t : ZMod p)⁻¹) ^ 2)
        = ∑ t ∈ (Finset.range p).filter (fun t => 0 < t), ((t : ZMod p)⁻¹) ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      have h : (p * j + t : ZMod p) = (t : ZMod p) := by simp
      rw [h]
    _ = 0 := zmod_sum_range_pos_inv_sq_eq_zero_oeis_361883 p hp5



/-- Sum of a nonzero `p`-block of off-diagonal terms after the preceding reductions. -/
lemma offdiag_block_sum_zmod_eq_coeff_sum_oeis_361883 {p M r j : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hMpos : 0 < M) (hM : p ^ (r - 1) ∣ M) :
    let R := ZMod (p ^ (3 * r))
    let D := Nat.choose (M * p + p * j) (M * p)
    (∑ t ∈ (Finset.range p).filter (fun t => 0 < t), (oeis_361883_T (M * p) (p * j + t) : R)) =
      2 * (M * p : R) ^ 2 * (D : R) ^ 3 *
        (∑ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * j + t : R)⁻¹) ^ 2) := by
  intro R D
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have ht0 : 0 < t := (Finset.mem_filter.mp ht).2
  have htp : t < p := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
  have h := offdiag_T_zmod_approx_const_oeis_361883 (p := p) (M := M) (r := r) (j := j) (t := t) hp hr hMpos hM ht0 htp
  dsimp at h
  dsimp [R, D]
  simpa [mul_assoc] using h


/-- A Lucas-theorem specialization for a top index with a nonzero low digit and a bottom index divisible by `p`. -/
lemma choose_mul_add_mul_modEq_oeis_361883 {p A B s : ℕ} [Fact p.Prime] (hs : s < p) :
    Nat.choose (p * A + s) (p * B) ≡ Nat.choose A B [MOD p] := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := p * A + s) (k := p * B) (p := p)
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos

  have hsmod : (p * A + s) % p = s := by simp [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt hs]
  have hdiv : (p * A + s) / p = A := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hs, zero_add]
  have hkmod : (p * B) % p = 0 := Nat.mul_mod_right p B
  have hkdiv : (p * B) / p = B := Nat.mul_div_right B hp0
  simpa [hsmod, hdiv, hkmod, hkdiv] using h

/-- Reducing a unit inverse-square from `ZMod (p^3)` to `ZMod p` in a nonzero block. -/
lemma zmod_castHom_inv_sq_block_oeis_361883 {p j t : ℕ} (hp : p.Prime)
    (ht0 : 0 < t) (htp : t < p) :
    let R := ZMod (p ^ 3)
    ZMod.castHom (show p ∣ p ^ 3 by exact dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
      (((p * j + t : R)⁻¹) ^ 2) = (((p * j + t : ZMod p)⁻¹) ^ 2) := by
  intro R
  haveI : Fact p.Prime := ⟨hp⟩
  let k := p * j + t
  have hnot : ¬ p ∣ k := by
    intro h
    have ht_dvd : p ∣ t := by
      have hmul : p ∣ p * j := dvd_mul_right p j
      exact (Nat.dvd_add_iff_right hmul).2 h
    exact (Nat.not_dvd_of_pos_of_lt ht0 htp) ht_dvd
  have hcopR : Nat.Coprime k (p ^ 3) :=
    Nat.Coprime.pow_right 3 (((hp.coprime_iff_not_dvd).2 hnot).symm)
  have hcopP : Nat.Coprime k p := ((hp.coprime_iff_not_dvd).2 hnot).symm
  let f := ZMod.castHom (show p ∣ p ^ 3 by exact dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
  let uR : Rˣ := ZMod.unitOfCoprime k hcopR
  let uP : (ZMod p)ˣ := ZMod.unitOfCoprime k hcopP
  have hmapu : Units.map f.toMonoidHom uR = uP := by
    apply Units.ext
    change f (k : R) = (k : ZMod p)
    simp [f]
  have hmapinv : f ((uR⁻¹ : Rˣ) : R) = ((uP⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    calc
      f ((uR⁻¹ : Rˣ) : R) = ((Units.map f.toMonoidHom uR)⁻¹ : (ZMod p)ˣ) := by
        exact (Units.coe_map_inv f.toMonoidHom uR).symm
      _ = ((uP⁻¹ : (ZMod p)ˣ) : ZMod p) := by rw [hmapu]
  have hinvR : ((k : R)⁻¹) = ((uR⁻¹ : Rˣ) : R) := by
    simpa [uR] using ZMod.inv_coe_unit uR
  have hinvP : ((k : ZMod p)⁻¹) = ((uP⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    simp [uP]
  have hcalc : f (((k : R)⁻¹) ^ 2) = (((k : ZMod p)⁻¹) ^ 2) := by
    calc
      f (((k : R)⁻¹) ^ 2) = (f ((k : R)⁻¹)) ^ 2 := by exact map_pow f ((k : R)⁻¹) 2
      _ = (f (((uR⁻¹ : Rˣ) : R))) ^ 2 := by rw [hinvR]
      _ = (((uP⁻¹ : (ZMod p)ˣ) : ZMod p)) ^ 2 := by rw [hmapinv]
      _ = (((k : ZMod p)⁻¹) ^ 2) := by rw [hinvP]
  simpa [k, f, Nat.cast_add, Nat.cast_mul, ZMod.castHom_apply] using hcalc

/-- In `ZMod (p^3)`, a class divisible by `p` is killed by multiplication by `p^2`. -/
lemma zmod_p_sq_mul_eq_zero_of_castHom_p_eq_zero_oeis_361883 {p : ℕ} (hp : p.Prime)
    (x : ZMod (p ^ 3))
    (hx : ZMod.castHom (show p ∣ p ^ 3 by exact dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) x = 0) :
    (p ^ 2 : ZMod (p ^ 3)) * x = 0 := by
  haveI : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x]
  have hxval0 : ((x.val : ℕ) : ZMod p) = 0 := by
    simpa [ZMod.castHom_apply] using hx
  have hxdiv : p ∣ x.val := (ZMod.natCast_eq_zero_iff x.val p).1 hxval0
  rcases hxdiv with ⟨y, hy⟩
  rw [hy, Nat.cast_mul]
  have hzero : ((p ^ 3 : ℕ) : ZMod (p ^ 3)) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (p ^ 3) (p ^ 3)).2 (dvd_refl _)
  calc
    (p ^ 2 : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) * (y : ZMod (p ^ 3)))
        = (y : ZMod (p ^ 3)) * ((p ^ 3 : ℕ) : ZMod (p ^ 3)) := by
          ring_nf
          rw [Nat.cast_pow]
          exact mul_comm (((p : ZMod (p ^ 3)) ^ 3)) (y : ZMod (p ^ 3))
    _ = 0 := by rw [hzero, mul_zero]

/-- The off-diagonal block sum vanishes modulo `p^3` in the first level `r = 1`. -/
lemma offdiag_block_sum_zmod_zero_r_one_oeis_361883 {p M j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hMpos : 0 < M) :
  (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
    (oeis_361883_T (M * p) (p * j + t) : ZMod (p ^ 3))) = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  let R := ZMod (p ^ 3)
  let s := (Finset.range p).filter (fun t => 0 < t)
  let D := Nat.choose (M * p + p * j) (M * p)
  let inner : R := ∑ t ∈ s, ((p * j + t : R)⁻¹) ^ 2
  have hcoeff := offdiag_block_sum_zmod_eq_coeff_sum_oeis_361883
    (p := p) (M := M) (r := 1) (j := j) hp (by norm_num) hMpos (by simp)
  dsimp at hcoeff
  have hmap_inner :
      ZMod.castHom (show p ∣ p ^ 3 by exact dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) inner = 0 := by
    calc
      ZMod.castHom (show p ∣ p ^ 3 by exact dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p) inner
          = ∑ t ∈ s, ZMod.castHom (show p ∣ p ^ 3 by exact dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
              (((p * j + t : R)⁻¹) ^ 2) := by
            simp [inner]
      _ = ∑ t ∈ s, ((p * j + t : ZMod p)⁻¹) ^ 2 := by
            apply Finset.sum_congr rfl
            intro t ht
            have ht0 : 0 < t := (Finset.mem_filter.mp ht).2
            have htp : t < p := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
            simpa [R, Nat.cast_add, Nat.cast_mul] using
              zmod_castHom_inv_sq_block_oeis_361883 (p := p) (j := j) (t := t) hp ht0 htp
      _ = 0 := by
            dsimp [s]
            exact inner_inv_sq_mod_p_zero_oeis_361883 (p := p) (j := j) hp5
  have hkill : (p ^ 2 : R) * inner = 0 :=
    zmod_p_sq_mul_eq_zero_of_castHom_p_eq_zero_oeis_361883 (p := p) hp inner hmap_inner
  have hfactor :
      2 * (M * p : R) ^ 2 * (D : R) ^ 3 * inner =
        (2 * (M : R) ^ 2 * (D : R) ^ 3) * ((p ^ 2 : R) * inner) := by
    dsimp [R]
    ring_nf
  calc
    (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
      (oeis_361883_T (M * p) (p * j + t) : ZMod (p ^ 3)))
        = 2 * (M * p : R) ^ 2 * (D : R) ^ 3 * inner := by
          simpa [R, s, D, inner] using hcoeff
    _ = (2 * (M : R) ^ 2 * (D : R) ^ 3) * ((p ^ 2 : R) * inner) := hfactor
    _ = 0 := by rw [hkill, mul_zero]

/-- The whole off-diagonal contribution vanishes modulo `p^3` at the first level. -/
lemma offdiag_global_modEq_zero_r_one_oeis_361883 {p M : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hMpos : 0 < M) :
    (Finset.sum (Finset.range M) fun j =>
      Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
        oeis_361883_T (M * p) (p * j + t)) ≡ 0 [MOD p ^ 3] := by
  have hzero :
      (((Finset.sum (Finset.range M) fun j =>
        Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
          oeis_361883_T (M * p) (p * j + t) : ℕ) : ZMod (p ^ 3)) = 0) := by
    rw [Nat.cast_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Nat.cast_sum]
    exact offdiag_block_sum_zmod_zero_r_one_oeis_361883 (p := p) (M := M) (j := j) hp hp5 hMpos
  exact (Nat.modEq_zero_iff_dvd).2 ((ZMod.natCast_eq_zero_iff _ _).1 hzero)

/-- In `ZMod (p^2)`, the product of two classes reducing to zero modulo `p` is zero. -/
lemma zmod_p2_mul_eq_zero_of_castHom_p_eq_zero_oeis_361883 {p : ℕ} (hp : p.Prime)
    (x y : ZMod (p ^ 2))
    (hx : ZMod.castHom (show p ∣ p ^ 2 by exact dvd_pow_self p (by norm_num : 2 ≠ 0))
        (ZMod p) x = 0)
    (hy : ZMod.castHom (show p ∣ p ^ 2 by exact dvd_pow_self p (by norm_num : 2 ≠ 0))
        (ZMod p) y = 0) :
    x * y = 0 := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y]
  have hxval0 : ((x.val : ℕ) : ZMod p) = 0 := by
    simpa [ZMod.castHom_apply] using hx
  have hyval0 : ((y.val : ℕ) : ZMod p) = 0 := by
    simpa [ZMod.castHom_apply] using hy
  have hxdiv : p ∣ x.val := (ZMod.natCast_eq_zero_iff x.val p).1 hxval0
  have hydiv : p ∣ y.val := (ZMod.natCast_eq_zero_iff y.val p).1 hyval0
  rcases hxdiv with ⟨a, ha⟩
  rcases hydiv with ⟨b, hb⟩
  rw [ha, hb, Nat.cast_mul, Nat.cast_mul]
  have hzero : ((p ^ 2 : ℕ) : ZMod (p ^ 2)) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (p ^ 2) (p ^ 2)).2 (dvd_refl _)
  calc
    (((p : ℕ) : ZMod (p ^ 2)) * (a : ZMod (p ^ 2))) *
        (((p : ℕ) : ZMod (p ^ 2)) * (b : ZMod (p ^ 2)))
        = (a : ZMod (p ^ 2)) * (b : ZMod (p ^ 2)) * ((p ^ 2 : ℕ) : ZMod (p ^ 2)) := by
          rw [Nat.cast_pow]
          ring
    _ = 0 := by rw [hzero, mul_zero]

/-- Reduction from `ZMod (p^2)` to `ZMod p` commutes with inverse-squares in a nonzero
`p`-block. -/
lemma zmod_castHom_inv_sq_p2_to_p_block_oeis_361883 {p j t : ℕ} (hp : p.Prime)
    (ht0 : 0 < t) (htp : t < p) :
    let R := ZMod (p ^ 2)
    ZMod.castHom (show p ∣ p ^ 2 by exact dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p)
      (((p * j + t : R)⁻¹) ^ 2) = (((p * j + t : ZMod p)⁻¹) ^ 2) := by
  intro R
  haveI : Fact p.Prime := ⟨hp⟩
  let k := p * j + t
  have hnot : ¬ p ∣ k := by
    intro h
    have ht_dvd : p ∣ t := by
      have hmul : p ∣ p * j := dvd_mul_right p j
      exact (Nat.dvd_add_iff_right hmul).2 h
    exact (Nat.not_dvd_of_pos_of_lt ht0 htp) ht_dvd
  have hcopR : Nat.Coprime k (p ^ 2) :=
    Nat.Coprime.pow_right 2 (((hp.coprime_iff_not_dvd).2 hnot).symm)
  have hcopP : Nat.Coprime k p := ((hp.coprime_iff_not_dvd).2 hnot).symm
  let f := ZMod.castHom (show p ∣ p ^ 2 by exact dvd_pow_self p (by norm_num : 2 ≠ 0)) (ZMod p)
  let uR : Rˣ := ZMod.unitOfCoprime k hcopR
  let uP : (ZMod p)ˣ := ZMod.unitOfCoprime k hcopP
  have hmapu : Units.map f.toMonoidHom uR = uP := by
    apply Units.ext
    change f (k : R) = (k : ZMod p)
    simp [f]
  have hmapinv : f ((uR⁻¹ : Rˣ) : R) = ((uP⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    calc
      f ((uR⁻¹ : Rˣ) : R) = ((Units.map f.toMonoidHom uR)⁻¹ : (ZMod p)ˣ) := by
        exact (Units.coe_map_inv f.toMonoidHom uR).symm
      _ = ((uP⁻¹ : (ZMod p)ˣ) : ZMod p) := by rw [hmapu]
  have hinvR : ((k : R)⁻¹) = ((uR⁻¹ : Rˣ) : R) := by
    simpa [uR] using ZMod.inv_coe_unit uR
  have hinvP : ((k : ZMod p)⁻¹) = ((uP⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    simp [uP]
  have hcalc : f (((k : R)⁻¹) ^ 2) = (((k : ZMod p)⁻¹) ^ 2) := by
    calc
      f (((k : R)⁻¹) ^ 2) = (f ((k : R)⁻¹)) ^ 2 := by exact map_pow f ((k : R)⁻¹) 2
      _ = (f (((uR⁻¹ : Rˣ) : R))) ^ 2 := by rw [hinvR]
      _ = (((uP⁻¹ : (ZMod p)ˣ) : ZMod p)) ^ 2 := by rw [hmapinv]
      _ = (((k : ZMod p)⁻¹) ^ 2) := by rw [hinvP]
  simpa [k, f, Nat.cast_add, Nat.cast_mul, ZMod.castHom_apply] using hcalc

/-- The double indexing `(s,t)` with `0 ≤ s < p` and `0 < t < p` enumerates the units
modulo `p^2`, hence their inverse-square sum vanishes in `ZMod (p^2)`. -/
lemma sum_pair_units_inv_sq_zmod_p2_eq_zero_oeis_361883 {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ s ∈ Finset.range p,
      ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
        (((p * s + t : ℕ) : ZMod (p ^ 2))⁻¹) ^ 2) = 0 := by
  classical
  have hunit := sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p 2 hp hp5
  let F : ℕ → ZMod (p ^ 2) := fun x => if Nat.Coprime x (p ^ 2) then ((x : ZMod (p ^ 2))⁻¹) ^ 2 else 0
  have hunitF : (∑ x ∈ Finset.range (p ^ 2), F x) = 0 := by
    calc
      (∑ x ∈ Finset.range (p ^ 2), F x)
          = ∑ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
              ((x : ZMod (p ^ 2))⁻¹) ^ 2 := by
            dsimp [F]
            rw [Finset.sum_filter]
      _ = 0 := hunit
  have hdecomp : (∑ x ∈ Finset.range (p ^ 2), F x) =
      ∑ s ∈ Finset.range p, ∑ t ∈ Finset.range p, F (p * s + t) := by
    simpa [pow_two] using (sum_range_mul_decomp_oeis_361883 p p F)
  have hblocks : (∑ s ∈ Finset.range p, ∑ t ∈ Finset.range p, F (p * s + t)) =
      ∑ s ∈ Finset.range p,
        ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
          (((p * s + t : ℕ) : ZMod (p ^ 2))⁻¹) ^ 2 := by
    apply Finset.sum_congr rfl
    intro s hs
    calc
      (∑ t ∈ Finset.range p, F (p * s + t))
          = ∑ t ∈ Finset.range p,
              if 0 < t then (((p * s + t : ℕ) : ZMod (p ^ 2))⁻¹) ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro t ht
            have htp : t < p := Finset.mem_range.mp ht
            have hiff : Nat.Coprime (p * s + t) (p ^ 2) ↔ 0 < t := by
              constructor
              · intro hcop
                by_contra ht0
                have ht_eq : t = 0 := Nat.eq_zero_of_not_pos ht0
                have hdiv : p ∣ p * s + t := by
                  rw [ht_eq, add_zero]
                  exact dvd_mul_right p s
                have hp_dvd_pow : p ∣ p ^ 2 := dvd_pow_self p (by norm_num : 2 ≠ 0)
                exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hdiv hp_dvd_pow) hcop
              · intro htpos
                have hnot : ¬ p ∣ p * s + t := by
                  intro hdiv
                  have hps : p ∣ p * s := dvd_mul_right p s
                  have htdvd : p ∣ t := (Nat.dvd_add_iff_right hps).2 hdiv
                  exact (Nat.not_dvd_of_pos_of_lt htpos htp) htdvd
                exact hp.coprime_pow_of_not_dvd hnot
            dsimp [F]
            by_cases htpos : 0 < t
            · rw [if_pos (hiff.mpr htpos), if_pos htpos]
            · have hnotcop : ¬ Nat.Coprime (p * s + t) (p ^ 2) := by
                intro hc
                exact htpos ((hiff.mp hc))
              rw [if_neg hnotcop, if_neg htpos]
      _ = ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
          (((p * s + t : ℕ) : ZMod (p ^ 2))⁻¹) ^ 2 := by
            rw [Finset.sum_filter]
  rw [← hblocks, ← hdecomp]
  exact hunitF


/-- The indexing `(a,t)` with `0 ≤ a < p^2` and `0 < t < p` enumerates the units
modulo `p^3`, hence their inverse-square sum vanishes in `ZMod (p^3)`. -/
lemma sum_pair_units_inv_sq_zmod_p3_eq_zero_oeis_361883 {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ a ∈ Finset.range (p ^ 2),
      ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
        (((p * a + t : ℕ) : ZMod (p ^ 3))⁻¹) ^ 2) = 0 := by
  classical
  have hunit := sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p 3 hp hp5
  let F : ℕ → ZMod (p ^ 3) := fun x => if Nat.Coprime x (p ^ 3) then ((x : ZMod (p ^ 3))⁻¹) ^ 2 else 0
  have hunitF : (∑ x ∈ Finset.range (p ^ 3), F x) = 0 := by
    calc
      (∑ x ∈ Finset.range (p ^ 3), F x)
          = ∑ x ∈ (Finset.range (p ^ 3)).filter (fun x => Nat.Coprime x (p ^ 3)),
              ((x : ZMod (p ^ 3))⁻¹) ^ 2 := by
            dsimp [F]
            rw [Finset.sum_filter]
      _ = 0 := hunit
  have hdecomp : (∑ x ∈ Finset.range (p ^ 3), F x) =
      ∑ a ∈ Finset.range (p ^ 2), ∑ t ∈ Finset.range p, F (p * a + t) := by
    have hrange : Finset.range (p ^ 3) = Finset.range (p ^ 2 * p) := by
      congr 1
    rw [hrange]
    exact sum_range_mul_decomp_oeis_361883 (p ^ 2) p F
  have hblocks : (∑ a ∈ Finset.range (p ^ 2), ∑ t ∈ Finset.range p, F (p * a + t)) =
      ∑ a ∈ Finset.range (p ^ 2),
        ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
          (((p * a + t : ℕ) : ZMod (p ^ 3))⁻¹) ^ 2 := by
    apply Finset.sum_congr rfl
    intro a ha
    calc
      (∑ t ∈ Finset.range p, F (p * a + t))
          = ∑ t ∈ Finset.range p,
              if 0 < t then (((p * a + t : ℕ) : ZMod (p ^ 3))⁻¹) ^ 2 else 0 := by
            apply Finset.sum_congr rfl
            intro t ht
            have htp : t < p := Finset.mem_range.mp ht
            have hiff : Nat.Coprime (p * a + t) (p ^ 3) ↔ 0 < t := by
              constructor
              · intro hcop
                by_contra ht0
                have ht_eq : t = 0 := Nat.eq_zero_of_not_pos ht0
                have hdiv : p ∣ p * a + t := by
                  rw [ht_eq, add_zero]
                  exact dvd_mul_right p a
                have hp_dvd_pow : p ∣ p ^ 3 := dvd_pow_self p (by norm_num : 3 ≠ 0)
                exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hdiv hp_dvd_pow) hcop
              · intro htpos
                have hnot : ¬ p ∣ p * a + t := by
                  intro hdiv
                  have hpa : p ∣ p * a := dvd_mul_right p a
                  have htdvd : p ∣ t := (Nat.dvd_add_iff_right hpa).2 hdiv
                  exact (Nat.not_dvd_of_pos_of_lt htpos htp) htdvd
                exact hp.coprime_pow_of_not_dvd hnot
            dsimp [F]
            by_cases htpos : 0 < t
            · rw [if_pos (hiff.mpr htpos), if_pos htpos]
            · have hnotcop : ¬ Nat.Coprime (p * a + t) (p ^ 3) := by
                intro hc
                exact htpos (hiff.mp hc)
              rw [if_neg hnotcop, if_neg htpos]
      _ = ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
          (((p * a + t : ℕ) : ZMod (p ^ 3))⁻¹) ^ 2 := by
            rw [Finset.sum_filter]
  rw [← hblocks, ← hdecomp]
  exact hunitF

/-- The triple indexing `(s,u,t)` with `0 ≤ s,u < p` and `0 < t < p` enumerates the
units modulo `p^3`, hence their inverse-square sum vanishes in `ZMod (p^3)`. -/
lemma sum_triple_units_inv_sq_zmod_p3_eq_zero_oeis_361883 {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ s ∈ Finset.range p,
      ∑ u ∈ Finset.range p,
        ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
          (((p * (p * s + u) + t : ℕ) : ZMod (p ^ 3))⁻¹) ^ 2) = 0 := by
  classical
  have hpair := sum_pair_units_inv_sq_zmod_p3_eq_zero_oeis_361883 (p := p) hp hp5
  let G : ℕ → ZMod (p ^ 3) := fun a =>
    ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
      (((p * a + t : ℕ) : ZMod (p ^ 3))⁻¹) ^ 2
  have hdecomp : (∑ a ∈ Finset.range (p ^ 2), G a) =
      ∑ s ∈ Finset.range p, ∑ u ∈ Finset.range p, G (p * s + u) := by
    simpa [pow_two] using (sum_range_mul_decomp_oeis_361883 p p G)
  rw [← hdecomp]
  simpa [G] using hpair

/-- A `p^2`-superblock of the off-diagonal inverse-square kernel at level `p^3`
is exactly the full unit inverse-square sum modulo `p^3`, and hence vanishes. -/
lemma offdiag_inner_inv_sq_zmod_p3_superblock_eq_zero_oeis_361883 {p q : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    let S := ZMod (p ^ 3)
    (∑ a ∈ Finset.range (p ^ 2),
      ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
        (((p * (p ^ 2 * q + a) + t : ℕ) : S)⁻¹) ^ 2) = 0 := by
  intro S
  calc
    (∑ a ∈ Finset.range (p ^ 2),
      ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
        (((p * (p ^ 2 * q + a) + t : ℕ) : S)⁻¹) ^ 2)
        = ∑ a ∈ Finset.range (p ^ 2),
            ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
              (((p * a + t : ℕ) : S)⁻¹) ^ 2 := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro t ht
          have hcast_nat : ((p * (p ^ 2 * q + a) + t : ℕ) : S) =
              ((p * a + t : ℕ) : S) := by
            have hnat : p * (p ^ 2 * q + a) + t = p ^ 3 * q + (p * a + t) := by ring
            rw [hnat, Nat.cast_add, Nat.cast_mul]
            simp [S]
          rw [hcast_nat]
    _ = 0 := sum_pair_units_inv_sq_zmod_p3_eq_zero_oeis_361883 (p := p) hp hp5


/-- In `ZMod (p^3)`, a class reducing to zero modulo `p^2` is killed by one
factor of `p`. -/
lemma zmod_p_mul_eq_zero_of_castHom_p2_eq_zero_oeis_361883 {p : ℕ} (hp : p.Prime)
    (x : ZMod (p ^ 3))
    (hx : ZMod.castHom (show p ^ 2 ∣ p ^ 3 by exact pow_dvd_pow p (by norm_num : 2 ≤ 3))
        (ZMod (p ^ 2)) x = 0) :
    (p : ZMod (p ^ 3)) * x = 0 := by
  haveI : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x]
  have hxval0 : ((x.val : ℕ) : ZMod (p ^ 2)) = 0 := by
    simpa [ZMod.castHom_apply] using hx
  have hxdiv : p ^ 2 ∣ x.val := (ZMod.natCast_eq_zero_iff x.val (p ^ 2)).1 hxval0
  rcases hxdiv with ⟨y, hy⟩
  rw [hy, Nat.cast_mul]
  have hzero : ((p ^ 3 : ℕ) : ZMod (p ^ 3)) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (p ^ 3) (p ^ 3)).2 (dvd_refl _)
  calc
    (p : ZMod (p ^ 3)) * (((p ^ 2 : ℕ) : ZMod (p ^ 3)) * (y : ZMod (p ^ 3)))
        = (y : ZMod (p ^ 3)) * ((p ^ 3 : ℕ) : ZMod (p ^ 3)) := by
          rw [show (((p ^ 2 : ℕ) : ZMod (p ^ 3))) = (p : ZMod (p ^ 3)) ^ 2 by rw [Nat.cast_pow]]
          ring_nf
          rw [Nat.cast_pow]
          exact mul_comm (((p : ZMod (p ^ 3)) ^ 3)) (y : ZMod (p ^ 3))
    _ = 0 := by rw [hzero, mul_zero]

/-- Reduction from `ZMod (p^3)` to `ZMod (p^2)` commutes with inverse-squares in a
nonzero `p`-block. -/
lemma zmod_castHom_inv_sq_p3_to_p2_block_oeis_361883 {p j t : ℕ} (hp : p.Prime)
    (ht0 : 0 < t) (htp : t < p) :
    let R := ZMod (p ^ 3)
    let S := ZMod (p ^ 2)
    ZMod.castHom (show p ^ 2 ∣ p ^ 3 by exact pow_dvd_pow p (by norm_num : 2 ≤ 3)) S
      (((p * j + t : R)⁻¹) ^ 2) = (((p * j + t : S)⁻¹) ^ 2) := by
  intro R S
  haveI : Fact p.Prime := ⟨hp⟩
  let k := p * j + t
  have hnot : ¬ p ∣ k := by
    intro h
    have ht_dvd : p ∣ t := by
      have hmul : p ∣ p * j := dvd_mul_right p j
      exact (Nat.dvd_add_iff_right hmul).2 h
    exact (Nat.not_dvd_of_pos_of_lt ht0 htp) ht_dvd
  have hcopR : Nat.Coprime k (p ^ 3) :=
    Nat.Coprime.pow_right 3 (((hp.coprime_iff_not_dvd).2 hnot).symm)
  have hcopS : Nat.Coprime k (p ^ 2) :=
    Nat.Coprime.pow_right 2 (((hp.coprime_iff_not_dvd).2 hnot).symm)
  let f := ZMod.castHom (show p ^ 2 ∣ p ^ 3 by exact pow_dvd_pow p (by norm_num : 2 ≤ 3)) S
  let uR : Rˣ := ZMod.unitOfCoprime k hcopR
  let uS : Sˣ := ZMod.unitOfCoprime k hcopS
  have hmapu : Units.map f.toMonoidHom uR = uS := by
    apply Units.ext
    change f (k : R) = (k : S)
    simp [f]
  have hmapinv : f ((uR⁻¹ : Rˣ) : R) = ((uS⁻¹ : Sˣ) : S) := by
    calc
      f ((uR⁻¹ : Rˣ) : R) = ((Units.map f.toMonoidHom uR)⁻¹ : Sˣ) := by
        exact (Units.coe_map_inv f.toMonoidHom uR).symm
      _ = ((uS⁻¹ : Sˣ) : S) := by rw [hmapu]
  have hinvR : ((k : R)⁻¹) = ((uR⁻¹ : Rˣ) : R) := by
    simpa [uR] using ZMod.inv_coe_unit uR
  have hinvS : ((k : S)⁻¹) = ((uS⁻¹ : Sˣ) : S) := by
    simpa [uS] using ZMod.inv_coe_unit uS
  have hcalc : f (((k : R)⁻¹) ^ 2) = (((k : S)⁻¹) ^ 2) := by
    calc
      f (((k : R)⁻¹) ^ 2) = (f ((k : R)⁻¹)) ^ 2 := by exact map_pow f ((k : R)⁻¹) 2
      _ = (f (((uR⁻¹ : Rˣ) : R))) ^ 2 := by rw [hinvR]
      _ = (((uS⁻¹ : Sˣ) : S)) ^ 2 := by rw [hmapinv]
      _ = (((k : S)⁻¹) ^ 2) := by rw [hinvS]
  simpa [k, f, Nat.cast_add, Nat.cast_mul, ZMod.castHom_apply] using hcalc

/-- Each off-diagonal inverse-square block modulo `p^3` is divisible by `p`. -/
lemma offdiag_inner_inv_sq_zmod_p3_castHom_p_eq_zero_oeis_361883 {p j : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    let R := ZMod (p ^ 3)
    let phi := ZMod.castHom (show p ∣ p ^ 3 by exact dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
    phi (∑ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * j + t : R)⁻¹) ^ 2) = 0 := by
  intro R phi
  haveI : Fact p.Prime := ⟨hp⟩
  calc
    phi (∑ t ∈ (Finset.range p).filter (fun t => 0 < t), (((p * j + t : ℕ) : R)⁻¹) ^ 2)
        = ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
            phi ((((p * j + t : ℕ) : R)⁻¹) ^ 2) := by rw [map_sum]
    _ = ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
            ((p * j + t : ZMod p)⁻¹) ^ 2 := by
          apply Finset.sum_congr rfl
          intro t ht
          have ht0 : 0 < t := (Finset.mem_filter.mp ht).2
          have htp : t < p := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
          simpa [R, phi, Nat.cast_add, Nat.cast_mul] using
            zmod_castHom_inv_sq_block_oeis_361883 (p := p) (j := j) (t := t) hp ht0 htp
    _ = 0 := inner_inv_sq_mod_p_zero_oeis_361883 (p := p) (j := j) hp5

/-- A length-`p` block of the `p^3` off-diagonal inverse-square kernel is zero after
reduction modulo `p^2`.  Equivalently, it is divisible by `p^2` in `ZMod (p^3)`. -/
lemma offdiag_inner_inv_sq_zmod_p3_p_block_castHom_p2_eq_zero_oeis_361883 {p b : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    let R := ZMod (p ^ 3)
    let S := ZMod (p ^ 2)
    let phi := ZMod.castHom (show p ^ 2 ∣ p ^ 3 by exact pow_dvd_pow p (by norm_num : 2 ≤ 3)) S
    phi (∑ c ∈ Finset.range p,
      ∑ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * (p * b + c) + t : R)⁻¹) ^ 2) = 0 := by
  intro R S phi
  haveI : Fact p.Prime := ⟨hp⟩
  calc
    phi (∑ c ∈ Finset.range p,
      ∑ t ∈ (Finset.range p).filter (fun t => 0 < t), (((p * (p * b + c) + t : ℕ) : R)⁻¹) ^ 2)
        = ∑ c ∈ Finset.range p,
            ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
              phi (((((p * (p * b + c) + t : ℕ) : R)⁻¹) ^ 2)) := by simp [map_sum]
    _ = ∑ c ∈ Finset.range p,
            ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
              (((p * c + t : ℕ) : S)⁻¹) ^ 2 := by
          apply Finset.sum_congr rfl
          intro c hc
          apply Finset.sum_congr rfl
          intro t ht
          have ht0 : 0 < t := (Finset.mem_filter.mp ht).2
          have htp : t < p := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
          calc
            phi (((((p * (p * b + c) + t : ℕ) : R)⁻¹) ^ 2))
                = (((((p * (p * b + c) + t : ℕ) : S)⁻¹) ^ 2)) := by
                  simpa [R, S, phi, Nat.cast_add, Nat.cast_mul] using
                    zmod_castHom_inv_sq_p3_to_p2_block_oeis_361883
                      (p := p) (j := p * b + c) (t := t) hp ht0 htp
            _ = (((p * c + t : ℕ) : S)⁻¹) ^ 2 := by
                  have hcast : ((p * (p * b + c) + t : ℕ) : S) = ((p * c + t : ℕ) : S) := by
                    have hnat : p * (p * b + c) + t = p ^ 2 * b + (p * c + t) := by ring
                    rw [hnat, Nat.cast_add, Nat.cast_mul]
                    simp [S]
                  rw [hcast]
    _ = 0 := sum_pair_units_inv_sq_zmod_p2_eq_zero_oeis_361883 (p := p) hp hp5

/-- Multiplying a length-`p` block of the `p^3` inverse-square kernel by `p` gives zero. -/
lemma offdiag_inner_inv_sq_zmod_p3_p_mul_p_block_eq_zero_oeis_361883 {p b : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    let R := ZMod (p ^ 3)
    (p : R) * (∑ c ∈ Finset.range p,
      ∑ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * (p * b + c) + t : R)⁻¹) ^ 2) = 0 := by
  intro R
  let S := ZMod (p ^ 2)
  let phi := ZMod.castHom (show p ^ 2 ∣ p ^ 3 by exact pow_dvd_pow p (by norm_num : 2 ≤ 3)) S
  exact zmod_p_mul_eq_zero_of_castHom_p2_eq_zero_oeis_361883 (p := p) hp _
    (by simpa [R, S, phi] using
      offdiag_inner_inv_sq_zmod_p3_p_block_castHom_p2_eq_zero_oeis_361883 (p := p) (b := b) hp hp5)

/-- For `M = p*N`, the weighted off-diagonal inverse-square moment occurring at level `r = 2`
vanishes after reduction to `ZMod (p^2)`. -/
lemma offdiag_weighted_moment_zmod_p2_zero_r_two_oeis_361883 {p M : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hMdiv : p ∣ M) :
    (∑ j ∈ Finset.range M,
      let D := Nat.choose (M * p + p * j) (M * p)
      ((D : ZMod (p ^ 2)) ^ 3) *
        (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * j + t : ZMod (p ^ 2))⁻¹) ^ 2)) = 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let S := ZMod (p ^ 2)
  let P := ZMod p
  let phi := ZMod.castHom (show p ∣ p ^ 2 by exact dvd_pow_self p (by norm_num : 2 ≠ 0)) P
  rcases hMdiv with ⟨N, hMN⟩
  let H : ℕ → S := fun j =>
    ∑ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * j + t : S)⁻¹) ^ 2
  let D : ℕ → ℕ := fun j => Nat.choose (M * p + p * j) (M * p)
  let C : ℕ → S := fun q => (Nat.choose (N + q) N : S) ^ 3
  have hH_mod_p (j : ℕ) : phi (H j) = 0 := by
    calc
      phi (H j) = ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
          phi (((p * j + t : S)⁻¹) ^ 2) := by
            dsimp [H]
            rw [map_sum]
      _ = ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * j + t : P)⁻¹) ^ 2 := by
            apply Finset.sum_congr rfl
            intro t ht
            have ht0 : 0 < t := (Finset.mem_filter.mp ht).2
            have htp : t < p := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
            simpa [S, P, Nat.cast_add, Nat.cast_mul, phi] using
              zmod_castHom_inv_sq_p2_to_p_block_oeis_361883 (p := p) (j := j) (t := t) hp ht0 htp
      _ = 0 := inner_inv_sq_mod_p_zero_oeis_361883 (p := p) (j := j) hp5
  have hH_superblock (q : ℕ) : (∑ s ∈ Finset.range p, H (p * q + s)) = 0 := by
    calc
      (∑ s ∈ Finset.range p, H (p * q + s))
          = ∑ s ∈ Finset.range p,
              ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
                (((p * s + t : ℕ) : S)⁻¹) ^ 2 := by
            apply Finset.sum_congr rfl
            intro s hs
            dsimp [H, S]
            apply Finset.sum_congr rfl
            intro t ht
            have hcast_nat : ((p * (p * q + s) + t : ℕ) : S) =
                ((p * s + t : ℕ) : S) := by
              have hnat : p * (p * q + s) + t = p ^ 2 * q + (p * s + t) := by ring
              rw [hnat, Nat.cast_add, Nat.cast_mul]
              simp [S]
            have hcast : (p : S) * ((p * q + s : ℕ) : S) + (t : S) =
                ((p * s + t : ℕ) : S) := by
              simpa [Nat.cast_add, Nat.cast_mul] using hcast_nat
            rw [hcast]
      _ = 0 := sum_pair_units_inv_sq_zmod_p2_eq_zero_oeis_361883 (p := p) hp hp5
  have hblock (q : ℕ) :
      (∑ s ∈ Finset.range p, ((D (p * q + s) : S) ^ 3) * H (p * q + s)) = 0 := by
    have hconst : (∑ s ∈ Finset.range p, C q * H (p * q + s)) = 0 := by
      rw [← Finset.mul_sum, hH_superblock q, mul_zero]
    have hpoint (s : ℕ) (hs : s ∈ Finset.range p) :
        ((D (p * q + s) : S) ^ 3) * H (p * q + s) = C q * H (p * q + s) := by
      have hslt : s < p := Finset.mem_range.mp hs
      have hDmod : D (p * q + s) ≡ Nat.choose (N + q) N [MOD p] := by
        have h1 : Nat.choose (M * p + p * (p * q + s)) (M * p) ≡
            Nat.choose (p * (N + q) + s) (p * N) [MOD p] := by
          have htop : M * p + p * (p * q + s) = p * (p * (N + q) + s) := by
            rw [hMN]
            ring
          have hbot : M * p = p * (p * N) := by
            rw [hMN]
            ring
          rw [htop, hbot]
          exact choose_mul_add_mul_modEq_oeis_361883 (p := p) (A := p * (N + q) + s) (B := p * N) (s := 0) hp.pos
        have h2 : Nat.choose (p * (N + q) + s) (p * N) ≡ Nat.choose (N + q) N [MOD p] :=
          choose_mul_add_mul_modEq_oeis_361883 (p := p) (A := N + q) (B := N) (s := s) hslt
        exact h1.trans h2
      have hcastD : phi (((D (p * q + s) : S) ^ 3) - C q) = 0 := by
        have heq : ((D (p * q + s) : P) ^ 3) = ((Nat.choose (N + q) N : P) ^ 3) := by
          exact congrArg (fun x : P => x ^ 3) ((ZMod.natCast_eq_natCast_iff _ _ _).2 hDmod)
        simpa [C, phi, S, P] using sub_eq_zero.mpr heq
      have hprod : (((D (p * q + s) : S) ^ 3) - C q) * H (p * q + s) = 0 :=
        zmod_p2_mul_eq_zero_of_castHom_p_eq_zero_oeis_361883 (p := p) hp
          (((D (p * q + s) : S) ^ 3) - C q) (H (p * q + s)) hcastD (hH_mod_p (p * q + s))
      calc
        ((D (p * q + s) : S) ^ 3) * H (p * q + s)
            = C q * H (p * q + s) + ((((D (p * q + s) : S) ^ 3) - C q) * H (p * q + s)) := by ring
        _ = C q * H (p * q + s) := by rw [hprod, add_zero]
    calc
      (∑ s ∈ Finset.range p, ((D (p * q + s) : S) ^ 3) * H (p * q + s))
          = ∑ s ∈ Finset.range p, C q * H (p * q + s) := by
            apply Finset.sum_congr rfl
            intro s hs
            exact hpoint s hs
      _ = 0 := hconst
  subst M
  change (∑ j ∈ Finset.range (p * N), ((D j : S) ^ 3) * H j) = 0
  rw [Nat.mul_comm p N]
  rw [sum_range_mul_decomp_oeis_361883 N p (fun j => ((D j : S) ^ 3) * H j)]
  apply Finset.sum_eq_zero
  intro q hq
  exact hblock q

/-- A first-level Lucas/moment cancellation: in blocks of length `p`, the binomial factor is
constant modulo `p`, while the remaining power has zero sum over `ZMod p` for exponents below
`p-1`.  This is the base case for the higher p-adic moment cancellation needed off-diagonal. -/
lemma lucas_moment_block_sum_zmod_zero_oeis_361883 {p N d : ℕ} [Fact p.Prime]
    (hd : d < p - 1) :
    (∑ k ∈ Finset.range (N * p),
      ((Nat.choose (N * p + k) (N * p) : ZMod p) ^ 3 * (k : ZMod p) ^ d)) = 0 := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let F : ℕ → ZMod p := fun k =>
    (Nat.choose (N * p + k) (N * p) : ZMod p) ^ 3 * (k : ZMod p) ^ d
  change (∑ k ∈ Finset.range (N * p), F k) = 0
  rw [sum_range_mul_decomp_oeis_361883 N p F]
  apply Finset.sum_eq_zero
  intro j hj
  have hinner : (∑ s ∈ Finset.range p, F (p * j + s)) =
      (Nat.choose (N + j) N : ZMod p) ^ 3 *
        (∑ s ∈ Finset.range p, (s : ZMod p) ^ d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hslt : s < p := Finset.mem_range.mp hs
    have htop : N * p + (p * j + s) = p * (N + j) + s := by ring
    have hbot : N * p = p * N := by ring
    have hc_nat : Nat.choose (N * p + (p * j + s)) (N * p) ≡
        Nat.choose (N + j) N [MOD p] := by
      rw [htop, hbot]
      exact choose_mul_add_mul_modEq_oeis_361883 (p := p) (A := N + j) (B := N) (s := s) hslt
    have hc : (Nat.choose (N * p + (p * j + s)) (N * p) : ZMod p) =
        (Nat.choose (N + j) N : ZMod p) := by
      exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hc_nat
    have hk : ((p * j + s : ℕ) : ZMod p) = (s : ZMod p) := by simp
    dsimp [F]
    rw [hc, hk]
  rw [hinner]
  rw [zmod_sum_range_pow_lt_p_sub_one_eq_zero_oeis_361883 p d hd]
  simp


/-- Natural-number divisibility form of the first-level Lucas moment cancellation. -/
lemma lucas_moment_block_sum_dvd_oeis_361883 {p N d : ℕ} [Fact p.Prime]
    (hd : d < p - 1) :
    p ∣ ∑ k ∈ Finset.range (N * p), Nat.choose (N * p + k) (N * p) ^ 3 * k ^ d := by
  have hz := lucas_moment_block_sum_zmod_zero_oeis_361883 (p := p) (N := N) (d := d) hd
  have hcast : ((∑ k ∈ Finset.range (N * p), Nat.choose (N * p + k) (N * p) ^ 3 * k ^ d : ℕ) : ZMod p) = 0 := by
    simpa [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] using hz
  exact (ZMod.natCast_eq_zero_iff _ _).1 hcast


/-- The proposed higher-power Lucas moment cancellation in the trivial level `s = 0`.
This isolates the base of the intended induction, where the modulus is `1`. -/
lemma lucas_moment_pow_dvd_oeis_361883_s_zero {p N d : ℕ} [Fact p.Prime]
    (_hd : d < p - 1) :
    p ^ 0 ∣ ∑ k ∈ Finset.range (N * p ^ 0),
      Nat.choose (N * p ^ 0 + k) (N * p ^ 0) ^ 3 * k ^ d := by
  simp

/-- The proposed higher-power Lucas moment cancellation at level `s = 1` is exactly the
already-proved first-level Lucas block cancellation. -/
lemma lucas_moment_pow_dvd_oeis_361883_s_one {p N d : ℕ} [Fact p.Prime]
    (hd : d < p - 1) :
    p ^ 1 ∣ ∑ k ∈ Finset.range (N * p ^ 1),
      Nat.choose (N * p ^ 1 + k) (N * p ^ 1) ^ 3 * k ^ d := by
  simpa using lucas_moment_block_sum_dvd_oeis_361883 (p := p) (N := N) (d := d) hd

/-- A small verified fragment of the desired induction: the higher-power statement holds
for the two levels currently supplied by the trivial modulus and the first-level Lucas block
cancellation. -/
lemma lucas_moment_pow_dvd_oeis_361883_of_s_le_one {p N s d : ℕ} [Fact p.Prime]
    (hs : s ≤ 1) (hd : d < p - 1) :
    p ^ s ∣ ∑ k ∈ Finset.range (N * p ^ s),
      Nat.choose (N * p ^ s + k) (N * p ^ s) ^ 3 * k ^ d := by
  interval_cases s
  · exact lucas_moment_pow_dvd_oeis_361883_s_zero (p := p) (N := N) (d := d) hd
  · exact lucas_moment_pow_dvd_oeis_361883_s_one (p := p) (N := N) (d := d) hd

/-- The desired higher-power statement is also immediate for the empty range `N = 0`. -/
lemma lucas_moment_pow_dvd_oeis_361883_N_zero {p s d : ℕ} [Fact p.Prime]
    (_hd : d < p - 1) :
    p ^ s ∣ ∑ k ∈ Finset.range (0 * p ^ s),
      Nat.choose (0 * p ^ s + k) (0 * p ^ s) ^ 3 * k ^ d := by
  simp

/-- At every positive level, the existing block cancellation still supplies one factor of `p`.
This is the modulo-`p` shadow of the intended higher `p`-adic induction. -/
lemma lucas_moment_pow_dvd_p_of_pos_oeis_361883 {p N s d : ℕ} [Fact p.Prime]
    (hs : 0 < s) (hd : d < p - 1) :
    p ∣ ∑ k ∈ Finset.range (N * p ^ s),
      Nat.choose (N * p ^ s + k) (N * p ^ s) ^ 3 * k ^ d := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  have h := lucas_moment_block_sum_dvd_oeis_361883 (p := p) (N := N * p ^ r) (d := d) hd
  simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h


/-- Lucas-theorem specialization when both top and bottom indices are divisible by `p`. -/
lemma choose_mul_mul_modEq_oeis_361883 {p A B : ℕ} [Fact p.Prime] :
    Nat.choose (p * A) (p * B) ≡ Nat.choose A B [MOD p] := by
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  simpa using (choose_mul_add_mul_modEq_oeis_361883 (p := p) (A := A) (B := B) (s := 0) hp0)

/-- Lucas specialization for indices one less than multiples of `p`. -/
lemma choose_mul_sub_one_modEq_oeis_361883 {p A B : ℕ} [Fact p.Prime] (hA : 0 < A) (hB : 0 < B) :
    Nat.choose (p * A - 1) (p * B - 1) ≡ Nat.choose (A - 1) (B - 1) [MOD p] := by
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  have htop : p * A - 1 = p * (A - 1) + (p - 1) := by
    cases A with
    | zero => omega
    | succ A =>
        cases p with
        | zero => omega
        | succ p => simp [Nat.mul_add, Nat.add_mul]
  have hbot : p * B - 1 = p * (B - 1) + (p - 1) := by
    cases B with
    | zero => omega
    | succ B =>
        cases p with
        | zero => omega
        | succ p => simp [Nat.mul_add, Nat.add_mul]
  rw [htop, hbot]
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := p * (A - 1) + (p - 1)) (k := p * (B - 1) + (p - 1)) (p := p)
  have hlt : p - 1 < p := Nat.sub_one_lt (Fact.out : Nat.Prime p).ne_zero
  have nmod : (p * (A - 1) + (p - 1)) % p = p - 1 := by
    simp [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt hlt]
  have kmod : (p * (B - 1) + (p - 1)) % p = p - 1 := by
    simp [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt hlt]
  have ndiv : (p * (A - 1) + (p - 1)) / p = A - 1 := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hlt, zero_add]
  have kdiv : (p * (B - 1) + (p - 1)) / p = B - 1 := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hlt, zero_add]
  have choosepp : Nat.choose (p - 1) (p - 1) = 1 := Nat.choose_self _
  simpa [nmod, kmod, ndiv, kdiv, choosepp] using h

/-- Lucas specialization with top index one less than a multiple of `p` and bottom index divisible by `p`. -/
lemma choose_mul_sub_one_right_modEq_oeis_361883 {p A B : ℕ} [Fact p.Prime] (hA : 0 < A) :
    Nat.choose (p * A - 1) (p * B) ≡ Nat.choose (A - 1) B [MOD p] := by
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  have htop : p * A - 1 = p * (A - 1) + (p - 1) := by
    cases A with
    | zero => omega
    | succ A =>
        cases p with
        | zero => omega
        | succ p => simp [Nat.mul_add, Nat.add_mul]
  rw [htop]
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
    (n := p * (A - 1) + (p - 1)) (k := p * B) (p := p)
  have hlt : p - 1 < p := Nat.sub_one_lt (Fact.out : Nat.Prime p).ne_zero
  have nmod : (p * (A - 1) + (p - 1)) % p = p - 1 := by
    simp [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt hlt]
  have kmod : (p * B) % p = 0 := Nat.mul_mod_right p B
  have ndiv : (p * (A - 1) + (p - 1)) / p = A - 1 := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp0, Nat.div_eq_of_lt hlt, zero_add]
  have kdiv : (p * B) / p = B := Nat.mul_div_right B hp0
  have choosep0 : Nat.choose (p - 1) 0 = 1 := Nat.choose_zero_right _
  simpa [nmod, kmod, ndiv, kdiv, choosep0] using h



/-- Lucas specialization for the diagonal binomial factor in a `p`-block. -/
lemma choose_block_diag_mod_p_oeis_361883 {p M j : ℕ} [Fact p.Prime] :
    Nat.choose (M * p + p * j) (M * p) ≡ Nat.choose (M + j) M [MOD p] := by
  have htop : M * p + p * j = p * (M + j) := by ring
  have hbot : M * p = p * M := by ring
  rw [htop, hbot]
  exact choose_mul_mul_modEq_oeis_361883


/-- Diagonal summands satisfy the expected Lucas congruence modulo `p`. -/
lemma T_diag_mod_p_oeis_361883 {p M j : ℕ} [Fact p.Prime] (hM : 0 < M) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p] := by
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  have hMp : 0 < M * p := Nat.mul_pos hM hp0
  rw [oeis_361883_T_eq_sq_mul (M * p) (p * j) hMp]
  rw [oeis_361883_T_eq_sq_mul M j hM]
  let A1 := Nat.choose (M * p + p * j - 1) (M * p - 1)
  let C1 := Nat.choose (M * p + p * j - 1) (M * p)
  let A0 := Nat.choose (M + j - 1) (M - 1)
  let C0 := Nat.choose (M + j - 1) M
  change A1 ^ 2 * (A1 + 2 * C1) ≡ A0 ^ 2 * (A0 + 2 * C0) [MOD p]
  have htop : M * p + p * j - 1 = p * (M + j) - 1 := by ring_nf
  have hbot1 : M * p - 1 = p * M - 1 := by ring_nf
  have hbot2 : M * p = p * M := by ring
  have hA : A1 ≡ A0 [MOD p] := by
    dsimp [A1, A0]
    rw [htop, hbot1]
    simpa [Nat.mul_add, Nat.add_mul] using
      (choose_mul_sub_one_modEq_oeis_361883 (p := p) (A := M + j) (B := M) (by omega) hM)
  have hC : C1 ≡ C0 [MOD p] := by
    dsimp [C1, C0]
    rw [htop, hbot2]
    simpa [Nat.mul_add, Nat.add_mul] using
      (choose_mul_sub_one_right_modEq_oeis_361883 (p := p) (A := M + j) (B := M) (by omega))
  exact (hA.pow 2).mul (hA.add ((Nat.ModEq.refl 2).mul hC))



/-- Global version of the off-diagonal sum reduction, before proving the remaining weighted cancellation. -/
lemma offdiag_global_sum_zmod_eq_coeff_sum_oeis_361883 {p M r : ℕ} (hp : p.Prime)
    (hr : 0 < r) (hMpos : 0 < M) (hM : p ^ (r - 1) ∣ M) :
    let R := ZMod (p ^ (3 * r))
    (∑ j ∈ Finset.range M,
      ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
        (oeis_361883_T (M * p) (p * j + t) : R)) =
    ∑ j ∈ Finset.range M,
      let D := Nat.choose (M * p + p * j) (M * p)
      2 * (M * p : R) ^ 2 * (D : R) ^ 3 *
        (∑ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * j + t : R)⁻¹) ^ 2) := by
  intro R
  apply Finset.sum_congr rfl
  intro j hj
  exact offdiag_block_sum_zmod_eq_coeff_sum_oeis_361883 hp hr hMpos hM


/--
Conditional general off-diagonal cancellation.  The preceding reduction shows that the
remaining obstruction is the weighted inverse-square moment displayed in `hmoment`.
Thus any proof of this moment identity in `ZMod (p^(3*r))` immediately gives the
natural-number congruence required for the off-diagonal part.
-/
lemma offdiag_global_modEq_zero_general_of_weighted_zmod_eq_zero_oeis_361883 {p M r : ℕ}
    (hp : p.Prime) (_hp5 : 5 ≤ p) (hr : 0 < r) (hMpos : 0 < M)
    (hMdiv : p ^ (r - 1) ∣ M)
    (hmoment :
      let R := ZMod (p ^ (3 * r))
      (∑ j ∈ Finset.range M,
        let D := Nat.choose (M * p + p * j) (M * p)
        (D : R) ^ 3 *
          (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
            ((p * j + t : R)⁻¹) ^ 2)) = 0) :
    (Finset.sum (Finset.range M) fun j =>
      Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
        oeis_361883_T (M * p) (p * j + t)) ≡ 0 [MOD p ^ (3 * r)] := by
  have hred := offdiag_global_sum_zmod_eq_coeff_sum_oeis_361883
    (p := p) (M := M) (r := r) hp hr hMpos hMdiv
  let R := ZMod (p ^ (3 * r))
  have hsumR :
      ((Finset.sum (Finset.range M) fun j =>
        Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
          oeis_361883_T (M * p) (p * j + t) : ℕ) : R) = 0 := by
    dsimp at hred hmoment
    rw [Nat.cast_sum]
    change (∑ j ∈ Finset.range M,
      ((Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
          oeis_361883_T (M * p) (p * j + t) : ℕ) : R)) = 0
    rw [show (∑ j ∈ Finset.range M,
        ((Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
            oeis_361883_T (M * p) (p * j + t) : ℕ) : R)) =
        (∑ j ∈ Finset.range M,
          ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
            (oeis_361883_T (M * p) (p * j + t) : R)) by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.cast_sum]]
    rw [hred]
    calc
      (∑ j ∈ Finset.range M,
        2 * (M * p : R) ^ 2 *
            (Nat.choose (M * p + p * j) (M * p) : R) ^ 3 *
            (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
              ((p * j + t : R)⁻¹) ^ 2))
          = 2 * (M * p : R) ^ 2 *
            (∑ j ∈ Finset.range M,
              (Nat.choose (M * p + p * j) (M * p) : R) ^ 3 *
                (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
                  ((p * j + t : R)⁻¹) ^ 2)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = 0 := by rw [hmoment, mul_zero]
  exact Nat.modEq_zero_iff_dvd.mpr ((ZMod.natCast_eq_zero_iff _ _).1 hsumR)




/--
A sharper conditional version of the preceding lemma: since `(M*p)^2` contains the
factor `p^(2*r)` under the hypothesis `p^(r-1) ∣ M`, it is enough to know that
`p^(2*r)` kills the remaining weighted inverse-square moment in
`ZMod (p^(3*r))`.  This is the formal shape of the expected residual
modulo-`p^r` moment cancellation.
-/
lemma offdiag_global_modEq_zero_general_of_weighted_zmod_pPow_mul_eq_zero_oeis_361883
    {p M r : ℕ} (hp : p.Prime) (_hp5 : 5 ≤ p) (hr : 0 < r) (hMpos : 0 < M)
    (hMdiv : p ^ (r - 1) ∣ M)
    (hmoment :
      let R := ZMod (p ^ (3 * r))
      (p ^ (2 * r) : R) *
        (∑ j ∈ Finset.range M,
          let D := Nat.choose (M * p + p * j) (M * p)
          (D : R) ^ 3 *
            (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
              ((p * j + t : R)⁻¹) ^ 2)) = 0) :
    (Finset.sum (Finset.range M) fun j =>
      Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
        oeis_361883_T (M * p) (p * j + t)) ≡ 0 [MOD p ^ (3 * r)] := by
  have hred := offdiag_global_sum_zmod_eq_coeff_sum_oeis_361883
    (p := p) (M := M) (r := r) hp hr hMpos hMdiv
  let R := ZMod (p ^ (3 * r))
  have hMp_factor : (M * p : R) ^ 2 = (p ^ (2 * r) : R) *
      (((M * p) / p ^ r : ℕ) : R) ^ 2 := by
    have hpr_dvd : p ^ r ∣ M * p := pow_dvd_mul_of_pred_pow_dvd_oeis_361883 hr hMdiv (le_refl r)
    rcases hpr_dvd with ⟨u, hu⟩
    have hdiv : (M * p) / p ^ r = u := by
      rw [hu]
      exact Nat.mul_div_right u (pow_pos hp.pos r)
    have hMp_cast : (M : R) * (p : R) = (p : R) ^ r * (u : R) := by
      have hcast := congrArg (fun n : ℕ => (n : R)) hu
      simpa [Nat.cast_mul, Nat.cast_pow] using hcast
    rw [hdiv, hMp_cast]
    have hp2r : ((p : R) ^ r) ^ 2 = (p : R) ^ (2 * r) := by
      rw [pow_two, ← pow_add]
      congr 1
      omega
    calc
      ((p : R) ^ r * (u : R)) ^ 2 = ((p : R) ^ r) ^ 2 * (u : R) ^ 2 := by ring
      _ = (p : R) ^ (2 * r) * (u : R) ^ 2 := by rw [hp2r]
      _ = (p ^ (2 * r) : R) * (u : R) ^ 2 := by simp
  have hsumR :
      ((Finset.sum (Finset.range M) fun j =>
        Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
          oeis_361883_T (M * p) (p * j + t) : ℕ) : R) = 0 := by
    dsimp at hred hmoment
    rw [Nat.cast_sum]
    change (∑ j ∈ Finset.range M,
      ((Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
          oeis_361883_T (M * p) (p * j + t) : ℕ) : R)) = 0
    rw [show (∑ j ∈ Finset.range M,
        ((Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
            oeis_361883_T (M * p) (p * j + t) : ℕ) : R)) =
        (∑ j ∈ Finset.range M,
          ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
            (oeis_361883_T (M * p) (p * j + t) : R)) by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Nat.cast_sum]]
    rw [hred]
    let W : R :=
      ∑ j ∈ Finset.range M,
        (Nat.choose (M * p + p * j) (M * p) : R) ^ 3 *
          (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
            ((p * j + t : R)⁻¹) ^ 2)
    have hfactor_sum :
        (∑ j ∈ Finset.range M,
          2 * (M * p : R) ^ 2 *
              (Nat.choose (M * p + p * j) (M * p) : R) ^ 3 *
              (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
                ((p * j + t : R)⁻¹) ^ 2)) =
        2 * (M * p : R) ^ 2 * W := by
      dsimp [W]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hfactor_sum, hMp_factor]
    change (p ^ (2 * r) : R) * W = 0 at hmoment
    calc
      2 * ((p ^ (2 * r) : R) * (((M * p) / p ^ r : ℕ) : R) ^ 2) * W
          = (2 * (((M * p) / p ^ r : ℕ) : R) ^ 2) * ((p ^ (2 * r) : R) * W) := by ring
      _ = 0 := by rw [hmoment, mul_zero]
  exact Nat.modEq_zero_iff_dvd.mpr ((ZMod.natCast_eq_zero_iff _ _).1 hsumR)

/-- The requested level-`r = 2` off-diagonal cancellation. -/
lemma offdiag_global_modEq_zero_r_two_oeis_361883 {p M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
  (hMpos : 0 < M) (hMdiv : p ∣ M) :
  (Finset.sum (Finset.range M) fun j =>
    Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
      oeis_361883_T (M*p) (p*j+t)) ≡ 0 [MOD p^6] := by
  haveI : Fact p.Prime := ⟨hp⟩
  let R := ZMod (p ^ 6)
  let S := ZMod (p ^ 2)
  let phi := ZMod.castHom (show p ^ 2 ∣ p ^ 6 by exact pow_dvd_pow p (by norm_num : 2 ≤ 6)) S
  let W : R :=
    ∑ j ∈ Finset.range M,
      let D := Nat.choose (M * p + p * j) (M * p)
      (D : R) ^ 3 *
        (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * j + t : R)⁻¹) ^ 2)
  have hphiW : phi W = 0 := by
    calc
      phi W
          = ∑ j ∈ Finset.range M,
              let D := Nat.choose (M * p + p * j) (M * p)
              (D : S) ^ 3 *
                (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
                  ((p * j + t : S)⁻¹) ^ 2) := by
            dsimp [W]
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [map_mul, map_pow, map_sum]
            congr 1
            · simp [R, S, phi]
            · apply Finset.sum_congr rfl
              intro t ht
              rw [map_pow]
              have ht0 : 0 < t := (Finset.mem_filter.mp ht).2
              have htp : t < p := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
              have hcop : Nat.Coprime (p * j + t) (p ^ 2) := by
                have hnot : ¬ p ∣ p * j + t := by
                  intro hdiv
                  have hpj : p ∣ p * j := dvd_mul_right p j
                  have htdvd : p ∣ t := (Nat.dvd_add_iff_right hpj).2 hdiv
                  exact (Nat.not_dvd_of_pos_of_lt ht0 htp) htdvd
                exact hp.coprime_pow_of_not_dvd hnot
              have hinv := zmod_castHom_inv_p6_to_p2_of_coprime_oeis_361883
                (p := p) (x := p * j + t) hp hcop
              simpa [R, S, phi] using congrArg (fun x : S => x ^ 2) hinv
      _ = 0 := offdiag_weighted_moment_zmod_p2_zero_r_two_oeis_361883
          (p := p) (M := M) hp hp5 hMdiv
  have hmomentW : (p ^ 4 : R) * W = 0 :=
    zmod_p4_mul_eq_zero_of_castHom_p2_eq_zero_oeis_361883 (p := p) hp W hphiW
  refine offdiag_global_modEq_zero_general_of_weighted_zmod_pPow_mul_eq_zero_oeis_361883
    (p := p) (M := M) (r := 2) hp hp5 (by norm_num) hMpos (by simpa using hMdiv) ?_
  dsimp
  simpa [R, W] using hmomentW

/-- Conditional level-`r = 3` off-diagonal cancellation: it remains only to prove the
weighted inverse-square moment after reduction to `ZMod (p^3)`. -/
lemma offdiag_global_modEq_zero_r_three_of_weighted_moment_zmod_p3_oeis_361883
    {p M : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hMpos : 0 < M) (hMdiv : p ^ 2 ∣ M)
    (hmoment :
      (∑ j ∈ Finset.range M,
        let D := Nat.choose (M * p + p * j) (M * p)
        (D : ZMod (p ^ 3)) ^ 3 *
          (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
            ((p * j + t : ZMod (p ^ 3))⁻¹) ^ 2)) = 0) :
    (Finset.sum (Finset.range M) fun j =>
      Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
        oeis_361883_T (M * p) (p * j + t)) ≡ 0 [MOD p ^ 9] := by
  haveI : Fact p.Prime := ⟨hp⟩
  let R := ZMod (p ^ 9)
  let S := ZMod (p ^ 3)
  let phi := ZMod.castHom (show p ^ 3 ∣ p ^ 9 by exact pow_dvd_pow p (by norm_num : 3 ≤ 9)) S
  let W : R :=
    ∑ j ∈ Finset.range M,
      let D := Nat.choose (M * p + p * j) (M * p)
      (D : R) ^ 3 *
        (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * j + t : R)⁻¹) ^ 2)
  have hphiW : phi W = 0 := by
    calc
      phi W
          = ∑ j ∈ Finset.range M,
              let D := Nat.choose (M * p + p * j) (M * p)
              (D : S) ^ 3 *
                (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
                  ((p * j + t : S)⁻¹) ^ 2) := by
            dsimp [W]
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro j hj
            rw [map_mul, map_pow, map_sum]
            congr 1
            · simp [R, S, phi]
            · apply Finset.sum_congr rfl
              intro t ht
              rw [map_pow]
              have ht0 : 0 < t := (Finset.mem_filter.mp ht).2
              have htp : t < p := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
              have hcop : Nat.Coprime (p * j + t) (p ^ 3) := by
                have hnot : ¬ p ∣ p * j + t := by
                  intro hdiv
                  have hpj : p ∣ p * j := dvd_mul_right p j
                  have htdvd : p ∣ t := (Nat.dvd_add_iff_right hpj).2 hdiv
                  exact (Nat.not_dvd_of_pos_of_lt ht0 htp) htdvd
                exact hp.coprime_pow_of_not_dvd hnot
              have hinv := zmod_castHom_inv_p9_to_p3_of_coprime_oeis_361883
                (p := p) (x := p * j + t) hp hcop
              simpa [R, S, phi] using congrArg (fun x : S => x ^ 2) hinv
      _ = 0 := hmoment
  have hmomentW : (p ^ 6 : R) * W = 0 :=
    zmod_p6_mul_eq_zero_of_castHom_p3_eq_zero_oeis_361883 (p := p) hp W hphiW
  refine offdiag_global_modEq_zero_general_of_weighted_zmod_pPow_mul_eq_zero_oeis_361883
    (p := p) (M := M) (r := 3) hp hp5 (by norm_num) hMpos (by simpa using hMdiv) ?_
  dsimp
  simpa [R, W] using hmomentW


/-- Split a nonempty finite range sum into the `0` term and the positive terms. -/
lemma sum_range_eq_zero_add_pos_oeis_361883 {α : Type*} [AddCommMonoid α]
    {p : ℕ} (hp : 0 < p) (F : ℕ → α) :
    Finset.sum (Finset.range p) F =
      F 0 + Finset.sum ((Finset.range p).filter (fun t => 0 < t)) F := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range p) (p := fun t => 0 < t)
    (f := F)]
  have hnon : Finset.sum ((Finset.range p).filter (fun t => ¬ 0 < t)) F = F 0 := by
    have hfilter : (Finset.range p).filter (fun t => ¬ 0 < t) = ({0} : Finset ℕ) := by
      apply Finset.ext
      intro x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · intro hx
        exact Nat.eq_zero_of_not_pos hx.2
      · intro hx
        subst x
        exact ⟨hp, by simp⟩
    rw [hfilter]
    simp
  rw [hnon]
  exact add_comm _ _

/-- Denominator-free formula for `a (M*p)` split into diagonal and off-diagonal `p`-blocks. -/
lemma a_mul_p_eq_diag_add_offdiag_oeis_361883 {M p : ℕ} (hM : 0 < M) (hp : 0 < p) :
    a (M * p) =
      (Finset.sum (Finset.range (M + 1)) fun j => oeis_361883_T (M * p) (p * j)) +
      (Finset.sum (Finset.range M) fun j =>
        Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
          oeis_361883_T (M * p) (p * j + t)) := by
  let F : ℕ → ℕ := fun k => oeis_361883_T (M * p) k
  have hMp : 0 < M * p := Nat.mul_pos hM hp
  have hsplit :
      (Finset.sum (Finset.range M) fun j => Finset.sum (Finset.range p) fun t => F (p * j + t)) =
        (Finset.sum (Finset.range M) fun j => F (p * j)) +
        (Finset.sum (Finset.range M) fun j =>
          Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t => F (p * j + t)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [sum_range_eq_zero_add_pos_oeis_361883 hp (fun t => F (p * j + t))]
    simp
  rw [a_eq_sum_oeis_361883_T_def (M * p) hMp]
  rw [sum_range_mul_succ_decomp_oeis_361883 M p F]
  change (Finset.sum (Finset.range M) (fun j => Finset.sum (Finset.range p) fun t => F (p * j + t)) + F (M * p) =
      (Finset.sum (Finset.range (M + 1)) fun j => F (p * j)) +
      (Finset.sum (Finset.range M) fun j =>
        Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t => F (p * j + t))
  )
  rw [Finset.sum_range_succ]
  rw [hsplit]
  have hend : F (M * p) = F (p * M) := by rw [Nat.mul_comm]
  rw [hend]
  ac_rfl

/-- Diagonal part of the denominator-free formula for `a M`. -/
lemma a_eq_diag_T_sum_oeis_361883 {M : ℕ} (hM : 0 < M) :
    a M = Finset.sum (Finset.range (M + 1)) fun j => oeis_361883_T M j := by
  exact a_eq_sum_oeis_361883_T_def M hM

/-- A one-step reduction: after splitting `a (M*p)`, it remains to prove diagonal
supercongruence and off-diagonal cancellation for the denominator-free summand. -/
lemma oeis_361883_step_of_diag_offdiag {p M r : ℕ} (hM : 0 < M) (hp0 : 0 < p)
    (hdiag :
      (Finset.sum (Finset.range (M + 1)) fun j => oeis_361883_T (M * p) (p * j)) ≡
        a M [MOD p ^ (3 * r)])
    (hoffdiag :
      (Finset.sum (Finset.range M) fun j =>
        Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
          oeis_361883_T (M * p) (p * j + t)) ≡ 0 [MOD p ^ (3 * r)]) :
    a (M * p) ≡ a M [MOD p ^ (3 * r)] := by
  rw [a_mul_p_eq_diag_add_offdiag_oeis_361883 hM hp0]
  simpa using hdiag.add hoffdiag

/-- Reindex the conjecture as the one-step congruence with `M = n*p^(r-1)`. -/
lemma oeis_361883_conjecture_reindex {p n r : ℕ} (hr : 0 < r) :
    a (n * p ^ r) = a ((n * p ^ (r - 1)) * p) := by
  have hr_eq : r - 1 + 1 = r := Nat.succ_pred_eq_of_pos hr
  apply congrArg a
  have hpow : p ^ r = p ^ (r - 1) * p := by
    conv_lhs => rw [← hr_eq, pow_succ]
  rw [hpow]
  ring



/-- If the central diagonal binomial coefficient at scale `p` is a multiple `q` of the
unscaled coefficient, then the corresponding denominator-free diagonal summand is multiplied
by `q^3`.  This exact algebraic lemma isolates the p-adic content of the diagonal case. -/
lemma T_diag_eq_quotient_cube_mul_oeis_361883
    {p M j q : ℕ} (hp0 : 0 < p) (hM : 0 < M)
    (hquot : Nat.choose (p * (M + j)) (p * M) = Nat.choose (M + j) M * q) :
    oeis_361883_T (M * p) (p * j) = q ^ 3 * oeis_361883_T M j := by
  have hApos : 0 < M + j := by omega
  have hpApos : 0 < p * (M + j) := Nat.mul_pos hp0 hApos
  have hMp : 0 < M * p := Nat.mul_pos hM hp0
  rw [oeis_361883_T_eq_sq_mul (N := M * p) (k := p * j) hMp]
  rw [oeis_361883_T_eq_sq_mul (N := M) (k := j) hM]
  let U := Nat.choose (p * (M + j)) (p * M)
  let V := Nat.choose (M + j) M
  let A1 := Nat.choose (M * p + p * j - 1) (M * p - 1)
  let C1 := Nat.choose (M * p + p * j - 1) (M * p)
  let A0 := Nat.choose (M + j - 1) (M - 1)
  let C0 := Nat.choose (M + j - 1) M
  have htop : M * p + p * j = p * (M + j) := by ring
  have htopm1 : M * p + p * j - 1 = p * (M + j) - 1 := by rw [htop]
  have hbotm1 : M * p - 1 = p * M - 1 := by ring_nf
  have hbot : M * p = p * M := by ring
  have hquot' : U = V * q := by simpa [U, V] using hquot
  have hA1U : A1 * (M + j) = U * M := by
    have hadj := choose_adjacent_mul_for_oeis_361883 (n := M * p) (k := p * j) hMp
    have hpascal : U = A1 + C1 := by
      calc
        U = Nat.choose (M * p + p * j) (M * p) := by
          dsimp [U]
          rw [← htop, ← hbot]
        _ = Nat.choose (M * p + p * j) (p * j) := by
          apply Nat.choose_symm_of_eq_add
          omega
        _ = A1 + C1 := by
          dsimp [A1, C1]
          exact choose_pascal_for_oeis_361883 (n := M * p) (k := p * j) hMp
    have hstd : U * (M * p) = A1 * (M * p + p * j) := by
      rw [hpascal]
      nlinarith [hadj]
    have hstd' : U * M = A1 * (M + j) := by
      apply Nat.eq_of_mul_eq_mul_left hp0
      calc
        p * (U * M) = U * (M * p) := by ring
        _ = A1 * (M * p + p * j) := hstd
        _ = p * (A1 * (M + j)) := by ring
    simpa [mul_comm] using hstd'.symm
  have hA0V : A0 * (M + j) = V * M := by
    have hadj := choose_adjacent_mul_for_oeis_361883 (n := M) (k := j) hM
    have hpascal : V = A0 + C0 := by
      dsimp [V, A0, C0]
      calc
        Nat.choose (M + j) M = Nat.choose (M + j) j := by
          apply Nat.choose_symm_of_eq_add
          omega
        _ = Nat.choose (M + j - 1) (M - 1) + Nat.choose (M + j - 1) M := by
          exact choose_pascal_for_oeis_361883 (n := M) (k := j) hM
    rw [hpascal]
    nlinarith [hadj]
  have hA1 : A1 = A0 * q := by
    apply Nat.eq_of_mul_eq_mul_right hApos
    calc
      A1 * (M + j) = U * M := hA1U
      _ = (V * q) * M := by rw [hquot']
      _ = (A0 * (M + j)) * q := by rw [hA0V]; ring
      _ = (A0 * q) * (M + j) := by ring
  have hC1 : C1 = C0 * q := by
    have hadj1 := choose_adjacent_mul_for_oeis_361883 (n := M * p) (k := p * j) hMp
    have hadj0 := choose_adjacent_mul_for_oeis_361883 (n := M) (k := j) hM
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hM hp0)
    calc
      C1 * (M * p) = A1 * (p * j) := hadj1
      _ = (A0 * q) * (p * j) := by rw [hA1]
      _ = (C0 * M) * q * p := by rw [hadj0]; ring
      _ = (C0 * q) * (M * p) := by ring
  change A1 ^ 2 * (A1 + 2 * C1) = q ^ 3 * (A0 ^ 2 * (A0 + 2 * C0))
  rw [hA1, hC1]
  ring

/-- A valuation consequence of the adjacent-binomial relation: if `p^m` divides `M`, then
`choose (M+j-1) (M-1)` contains the remaining power after the contribution of `j`. -/
lemma choose_adjacent_dvd_of_M_dvd_oeis_361883
    {p M j m : ℕ} [Fact p.Prime]
    (hMpos : 0 < M) (hj : 0 < j) (hM : p ^ m ∣ M) :
    p ^ (m - padicValNat p j) ∣ Nat.choose (M + j - 1) (M - 1) := by
  let A := Nat.choose (M + j - 1) (M - 1)
  let C := Nat.choose (M + j - 1) M
  have hApos : 0 < A := by
    dsimp [A]
    apply Nat.choose_pos
    omega
  have hCpos : 0 < C := by
    dsimp [C]
    apply Nat.choose_pos
    omega
  have hAne : A ≠ 0 := hApos.ne'
  have hCne : C ≠ 0 := hCpos.ne'
  have hMne : M ≠ 0 := hMpos.ne'
  have hjne : j ≠ 0 := hj.ne'
  have hadj : C * M = A * j := by
    dsimp [A, C]
    exact choose_adjacent_mul_for_oeis_361883 (n := M) (k := j) hMpos
  have hmle : m ≤ padicValNat p M := (padicValNat_dvd_iff_le hMne).1 hM
  have hvEq : padicValNat p C + padicValNat p M = padicValNat p A + padicValNat p j := by
    calc
      padicValNat p C + padicValNat p M = padicValNat p (C * M) := by
        rw [padicValNat.mul hCne hMne]
      _ = padicValNat p (A * j) := by rw [hadj]
      _ = padicValNat p A + padicValNat p j := by
        rw [padicValNat.mul hAne hjne]
  have hle : m - padicValNat p j ≤ padicValNat p A := by
    omega
  exact (padicValNat_dvd_iff_le hAne).2 hle

/-- The diagonal summand itself inherits twice the adjacent-binomial divisibility. -/
lemma T_dvd_from_M_dvd_oeis_361883
    {p M r j : ℕ} [Fact p.Prime]
    (hMpos : 0 < M) (hj : 0 < j)
    (hM : p ^ (r - 1) ∣ M) :
    p ^ (2 * ((r - 1) - padicValNat p j)) ∣ oeis_361883_T M j := by
  let e := (r - 1) - padicValNat p j
  have hA : p ^ e ∣ Nat.choose (M + j - 1) (M - 1) := by
    dsimp [e]
    exact choose_adjacent_dvd_of_M_dvd_oeis_361883 hMpos hj hM
  rw [oeis_361883_T_eq_sq_mul (N := M) (k := j) hMpos]
  dsimp only
  let A := Nat.choose (M + j - 1) (M - 1)
  let C := Nat.choose (M + j - 1) M
  change p ^ (2 * e) ∣ A ^ 2 * (A + 2 * C)
  have hA2 : p ^ (2 * e) ∣ A ^ 2 := by
    change p ^ (2 * e) ∣ (Nat.choose (M + j - 1) (M - 1)) ^ 2
    rcases hA with ⟨u, hu⟩
    rw [hu]
    use u ^ 2
    rw [mul_pow]
    rw [← pow_mul]
    ring
  exact dvd_mul_of_dvd_left hA2 _

/-- If `q ≡ 1` to precision `p^e` and `T` contains `p^d`, then multiplying `T` by
`q^3` is invisible modulo any `p^R` with `R ≤ d+e`. -/
lemma mul_cube_modEq_of_q_modEq_one_and_dvd_oeis_361883
    {p q T e d R : ℕ}
    (hq : q ≡ 1 [MOD p ^ e]) (hT : p ^ d ∣ T) (hde : R ≤ d + e) :
    q ^ 3 * T ≡ T [MOD p ^ R] := by
  have hq3 : q ^ 3 ≡ 1 [MOD p ^ e] := hq.pow 3
  have hmul : q ^ 3 * T ≡ 1 * T [MOD p ^ e * T] := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hq3.mul_right' T
  have hdiv_de : p ^ (d + e) ∣ p ^ e * T := by
    rcases hT with ⟨u, hu⟩
    rw [hu]
    use u
    rw [pow_add]
    ring
  have hdiv_R : p ^ R ∣ p ^ e * T := (pow_dvd_pow p hde).trans hdiv_de
  simpa using hmul.of_dvd hdiv_R


/-- The p-adic exponents from Jacobsthal's quotient and the old summand divisibility add up
to the target diagonal precision. -/
lemma diag_exponent_ineq_oeis_361883
    {p M r j : ℕ} [Fact p.Prime]
    (hr : 0 < r) (hMpos : 0 < M) (hj : 0 < j) (hM : p ^ (r - 1) ∣ M) :
    3 * r ≤
      2 * ((r - 1) - padicValNat p j) +
        (3 + padicValNat p ((M + j) * M * j)) := by
  have hMne : M ≠ 0 := hMpos.ne'
  have hjne : j ≠ 0 := hj.ne'
  have hsumne : M + j ≠ 0 := by omega
  let m := r - 1
  let c := padicValNat p j
  let x := padicValNat p M
  let y := padicValNat p (M + j)
  have hmle : m ≤ x := by
    dsimp [m, x]
    exact (padicValNat_dvd_iff_le hMne).1 hM
  have hminM : p ^ min m c ∣ M := by
    exact (pow_dvd_pow p (min_le_left m c)).trans hM
  have hminj : p ^ min m c ∣ j := by
    exact (pow_dvd_pow p (min_le_right m c)).trans (pow_padicValNat_dvd (p := p) (n := j))
  have hminsum : p ^ min m c ∣ M + j := dvd_add hminM hminj
  have hmyle : min m c ≤ y := by
    dsimp [y]
    exact (padicValNat_dvd_iff_le hsumne).1 hminsum
  have hvprod : padicValNat p ((M + j) * M * j) = y + x + c := by
    dsimp [x, y, c]
    rw [padicValNat.mul]
    · rw [padicValNat.mul hsumne hMne]
    · exact mul_ne_zero hsumne hMne
    · exact hjne
  rw [hvprod]
  dsimp [m, c, x, y] at hmle hmyle ⊢
  have hr_eq : r - 1 + 1 = r := Nat.succ_pred_eq_of_pos hr
  by_cases hc : padicValNat p j ≤ r - 1
  · omega
  · have hcm : r - 1 ≤ padicValNat p j := le_of_lt (Nat.lt_of_not_ge hc)
    omega



/-- A conditional diagonal congruence: the only serious missing mathematical input is the
Jacobsthal--Kazandzidis ratio congruence for the central binomial factor. -/
lemma T_diag_modEq_of_jacobsthal_ratio_oeis_361883
    {p M r j : ℕ} [Fact p.Prime]
    (hr : 0 < r) (hMpos : 0 < M) (hj : 0 < j) (hM : p ^ (r - 1) ∣ M)
    (hJK : ∃ q : ℕ,
      Nat.choose (p * (M + j)) (p * M) = Nat.choose (M + j) M * q ∧
        q ≡ 1 [MOD p ^ (3 + padicValNat p ((M + j) * M * j))]) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ (3 * r)] := by
  rcases hJK with ⟨q, hqeq, hqmod⟩
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  have hscale := T_diag_eq_quotient_cube_mul_oeis_361883
    (p := p) (M := M) (j := j) (q := q) hp0 hMpos hqeq
  rw [hscale]
  exact mul_cube_modEq_of_q_modEq_one_and_dvd_oeis_361883
    (p := p) (q := q) (T := oeis_361883_T M j)
    (e := 3 + padicValNat p ((M + j) * M * j))
    (d := 2 * ((r - 1) - padicValNat p j))
    (R := 3 * r)
    hqmod
    (T_dvd_from_M_dvd_oeis_361883 (p := p) (M := M) (r := r) (j := j) hMpos hj hM)
    (diag_exponent_ineq_oeis_361883 (p := p) (M := M) (r := r) (j := j) hr hMpos hj hM)

/-- If the two adjacent diagonal binomial coefficients satisfy the required high-power
Jacobsthal congruences, then the diagonal summand does too.  This is the integer-congruence
form actually needed for the diagonal part. -/
lemma T_diag_mod_pow_of_adjacent_modEq_oeis_361883 {p M r j : ℕ}
    (hp : 0 < p) (hM : 0 < M)
    (hA : Nat.choose (M * p + p * j - 1) (M * p - 1) ≡
        Nat.choose (M + j - 1) (M - 1) [MOD p ^ (3 * r)])
    (hC : Nat.choose (M * p + p * j - 1) (M * p) ≡
        Nat.choose (M + j - 1) M [MOD p ^ (3 * r)]) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ (3 * r)] := by
  have hMp : 0 < M * p := Nat.mul_pos hM hp
  rw [oeis_361883_T_eq_sq_mul (M * p) (p * j) hMp]
  rw [oeis_361883_T_eq_sq_mul M j hM]
  let A1 := Nat.choose (M * p + p * j - 1) (M * p - 1)
  let C1 := Nat.choose (M * p + p * j - 1) (M * p)
  let A0 := Nat.choose (M + j - 1) (M - 1)
  let C0 := Nat.choose (M + j - 1) M
  change A1 ^ 2 * (A1 + 2 * C1) ≡ A0 ^ 2 * (A0 + 2 * C0) [MOD p ^ (3 * r)]
  have hA' : A1 ≡ A0 [MOD p ^ (3 * r)] := by simpa [A1, A0] using hA
  have hC' : C1 ≡ C0 [MOD p ^ (3 * r)] := by simpa [C1, C0] using hC
  exact (hA'.pow 2).mul (hA'.add ((Nat.ModEq.refl 2).mul hC'))


/-- The zero diagonal summand is exactly one. -/
lemma T_zero_oeis_361883 {N : ℕ} (hN : 0 < N) :
    oeis_361883_T N 0 = 1 := by
  rw [oeis_361883_T_eq_sq_mul (N := N) (k := 0) hN]
  have hchoose : Nat.choose (N - 1) N = 0 := by
    apply Nat.choose_eq_zero_of_lt
    omega
  simp [hchoose]

/-- The `j = 0` diagonal congruence is exact. -/
lemma T_diag_zero_modEq_oeis_361883 {p M r : ℕ} (hM : 0 < M) (hp : 0 < p) :
    oeis_361883_T (M * p) (p * 0) ≡ oeis_361883_T M 0 [MOD p ^ (3 * r)] := by
  have hMp : 0 < M * p := Nat.mul_pos hM hp
  simpa [T_zero_oeis_361883 hMp, T_zero_oeis_361883 hM] using
    (Nat.ModEq.refl 1 : 1 ≡ 1 [MOD p ^ (3 * r)])


/-- If every diagonal summand has the desired congruence, then the whole diagonal part is
congruent to `a M`.  This packages the denominator-free formula for later use in the final
one-step argument. -/
lemma diag_sum_modEq_of_pointwise_oeis_361883 {p M r : ℕ} (hM : 0 < M)
    (hdiag : ∀ j ∈ Finset.range (M + 1),
      oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ (3 * r)]) :
    (Finset.sum (Finset.range (M + 1)) fun j => oeis_361883_T (M * p) (p * j)) ≡
      a M [MOD p ^ (3 * r)] := by
  have hsum := Nat.ModEq.sum (s := Finset.range (M + 1))
    (f := fun j => oeis_361883_T (M * p) (p * j))
    (g := fun j => oeis_361883_T M j) hdiag
  simpa [a_eq_diag_T_sum_oeis_361883 hM] using hsum

/-- The existing conditional Jacobsthal-ratio lemma gives the whole diagonal contribution,
including the exactly trivial `j = 0` term.  This isolates the remaining external input for
the diagonal part as a pointwise Jacobsthal--Kazandzidis quotient congruence. -/
lemma diag_sum_modEq_of_jacobsthal_ratios_oeis_361883
    {p M r : ℕ} [Fact p.Prime]
    (hr : 0 < r) (hMpos : 0 < M) (hMdiv : p ^ (r - 1) ∣ M)
    (hJK : ∀ j ∈ Finset.range (M + 1), 0 < j → ∃ q : ℕ,
      Nat.choose (p * (M + j)) (p * M) = Nat.choose (M + j) M * q ∧
        q ≡ 1 [MOD p ^ (3 + padicValNat p ((M + j) * M * j))]) :
    (Finset.sum (Finset.range (M + 1)) fun j => oeis_361883_T (M * p) (p * j)) ≡
      a M [MOD p ^ (3 * r)] := by
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  refine diag_sum_modEq_of_pointwise_oeis_361883 (p := p) (M := M) (r := r) hMpos ?_
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    exact T_diag_zero_modEq_oeis_361883 (p := p) (M := M) (r := r) hMpos hp0
  · exact T_diag_modEq_of_jacobsthal_ratio_oeis_361883
      (p := p) (M := M) (r := r) (j := j) hr hMpos (Nat.pos_of_ne_zero hj0)
      hMdiv (hJK j hj (Nat.pos_of_ne_zero hj0))

/-- A reindexed conditional version of the target theorem.  After the established block
splitting, it remains only to provide (1) diagonal congruence and (2) off-diagonal cancellation
for `M = n * p^(r-1)`. -/
lemma oeis_361883_conjecture_0_of_diag_offdiag {p n r : ℕ}
    (hp : p.Prime) (hn : 0 < n) (hr : 0 < r)
    (hdiag :
      (Finset.sum (Finset.range (n * p ^ (r - 1) + 1)) fun j =>
        oeis_361883_T ((n * p ^ (r - 1)) * p) (p * j)) ≡
        a (n * p ^ (r - 1)) [MOD p ^ (3 * r)])
    (hoffdiag :
      (Finset.sum (Finset.range (n * p ^ (r - 1))) fun j =>
        Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
          oeis_361883_T ((n * p ^ (r - 1)) * p) (p * j + t)) ≡
        0 [MOD p ^ (3 * r)]) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  let M := n * p ^ (r - 1)
  have hp0 : 0 < p := hp.pos
  have hMpos : 0 < M := Nat.mul_pos hn (pow_pos hp0 (r - 1))
  rw [oeis_361883_conjecture_reindex (p := p) (n := n) (r := r) hr]
  exact oeis_361883_step_of_diag_offdiag (p := p) (M := M) (r := r) hMpos hp0 hdiag hoffdiag

/-- A more arithmetic conditional theorem: the already-proved Jacobsthal-ratio reduction
settles the diagonal part, so only the off-diagonal block cancellation remains as a separate
hypothesis. -/
lemma oeis_361883_conjecture_0_of_jacobsthal_and_offdiag {p n r : ℕ}
    (hp : p.Prime) (hn : 0 < n) (hr : 0 < r)
    (hJK : ∀ j ∈ Finset.range (n * p ^ (r - 1) + 1), 0 < j → ∃ q : ℕ,
      Nat.choose (p * (n * p ^ (r - 1) + j)) (p * (n * p ^ (r - 1))) =
          Nat.choose (n * p ^ (r - 1) + j) (n * p ^ (r - 1)) * q ∧
        q ≡ 1 [MOD p ^ (3 + padicValNat p (((n * p ^ (r - 1) + j) * (n * p ^ (r - 1))) * j))])
    (hoffdiag :
      (Finset.sum (Finset.range (n * p ^ (r - 1))) fun j =>
        Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
          oeis_361883_T ((n * p ^ (r - 1)) * p) (p * j + t)) ≡
        0 [MOD p ^ (3 * r)]) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  let M := n * p ^ (r - 1)
  have hMpos : 0 < M := Nat.mul_pos hn (pow_pos hp.pos (r - 1))
  have hMdiv : p ^ (r - 1) ∣ M := by
    dsimp [M]
    simp
  refine oeis_361883_conjecture_0_of_diag_offdiag (p := p) (n := n) (r := r) hp hn hr ?_ hoffdiag
  exact diag_sum_modEq_of_jacobsthal_ratios_oeis_361883
    (p := p) (M := M) (r := r) hr hMpos hMdiv (by
      intro j hj hjpos
      exact hJK j hj hjpos)




/-- Linearization of a finite product when the perturbation has square zero.  This is a
small algebraic tool for product-block congruences modulo `p^3`: with `δ = p^2`, all terms of
order at least two in `δ` vanish. -/
lemma prod_one_add_square_zero_oeis_361883 {ι R : Type*} [CommRing R] [DecidableEq ι]
    (s : Finset ι) (δ : R) (f : ι → R) (hδ : δ ^ 2 = 0) :
    (∏ i ∈ s, (1 + δ * f i)) = 1 + δ * (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
      calc
        (1 + δ * f a) * (1 + δ * (∑ x ∈ s, f x))
            = 1 + δ * f a + δ * (∑ x ∈ s, f x) + δ ^ 2 * f a * (∑ x ∈ s, f x) := by ring
        _ = 1 + δ * f a + δ * (∑ x ∈ s, f x) + 0 * f a * (∑ x ∈ s, f x) := by rw [hδ]
        _ = 1 + δ * (f a + ∑ x ∈ s, f x) := by ring

/-- A paired product-block reduction in `ZMod (p^3)`.  Pairing the factors `t` and `p-t`
removes the first-order `p*q` term.  The remaining obstruction is exactly the displayed
inverse-pair sum, multiplied by `p^2`; this is the finite-product core of the desired block
lemma `∏ (p*q+t) = ∏ t` modulo `p^3`. -/
lemma paired_product_block_zmod_p3_of_inv_sum_zero_oeis_361883 {p q : ℕ}
    (hp : p.Prime) (_hp5 : 5 ≤ p)
    (hzero :
      let R := ZMod (p ^ 3)
      ((p ^ 2 : ℕ) : R) *
        (∑ t ∈ Finset.Icc 1 (p / 2),
          ((q + q ^ 2 : ℕ) : R) * (((t * (p - t) : ℕ) : R)⁻¹)) = 0) :
    let R := ZMod (p ^ 3)
    (∏ t ∈ Finset.Icc 1 (p / 2),
      (((p * q + t : ℕ) : R) * ((p * q + (p - t) : ℕ) : R))) =
    (∏ t ∈ Finset.Icc 1 (p / 2), ((t * (p - t) : ℕ) : R)) := by
  classical
  intro R
  have hδ2 : ((((p ^ 2 : ℕ) : R)) ^ 2) = 0 := by
    have hδ2' : ((((p ^ 2 : ℕ) : ZMod (p ^ 3))) ^ 2) = 0 := by
      have hdiv : p ^ 3 ∣ p ^ 4 := pow_dvd_pow p (by omega)
      have hcast : ((p ^ 4 : ℕ) : ZMod (p ^ 3)) = 0 :=
        (ZMod.natCast_eq_zero_iff (p ^ 4) (p ^ 3)).2 hdiv
      calc
        ((((p ^ 2 : ℕ) : ZMod (p ^ 3))) ^ 2) = ((p ^ 4 : ℕ) : ZMod (p ^ 3)) := by
          norm_num [Nat.cast_pow]
          ring_nf
        _ = 0 := hcast
    simpa [R] using hδ2'
  let s := Finset.Icc 1 (p / 2)
  let δ : R := ((p ^ 2 : ℕ) : R)
  let c : R := ((q + q ^ 2 : ℕ) : R)
  let B : ℕ → R := fun t => ((t * (p - t) : ℕ) : R)
  have hunit : ∀ t ∈ s, IsUnit (B t) := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    have htle : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
    have htp : t < p := by omega
    have hptpos : 0 < p - t := by omega
    have hptlt : p - t < p := by omega
    have hnot_t : ¬ p ∣ t := Nat.not_dvd_of_pos_of_lt (by omega) htp
    have hnot_pt : ¬ p ∣ p - t := Nat.not_dvd_of_pos_of_lt hptpos hptlt
    have hnot : ¬ p ∣ t * (p - t) := by
      intro h
      rcases hp.dvd_mul.mp h with h | h
      · exact hnot_t h
      · exact hnot_pt h
    have hcop : Nat.Coprime (t * (p - t)) (p ^ 3) :=
      Nat.Coprime.pow_right 3 (((hp.coprime_iff_not_dvd).2 hnot).symm)
    exact (ZMod.isUnit_iff_coprime (t * (p - t)) (p ^ 3)).2 hcop
  have hpair : ∀ t ∈ s,
      (((p * q + t : ℕ) : R) * ((p * q + (p - t) : ℕ) : R)) = B t + δ * c := by
    intro t ht
    have htle : t ≤ p := by
      have htle' : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
      omega
    dsimp [B, δ, c, R]
    have hcast : ((p - t : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) - t := by
      rw [Nat.cast_sub htle]
    rw [show ((p * q + (p - t) : ℕ) : ZMod (p ^ 3)) =
        (p : ZMod (p ^ 3)) * q + ((p - t : ℕ) : ZMod (p ^ 3)) by simp]
    rw [hcast]
    rw [show ((p * q + t : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) * q + t by simp]
    rw [show ((t * (p - t) : ℕ) : ZMod (p ^ 3)) =
        (t : ZMod (p ^ 3)) * ((p - t : ℕ) : ZMod (p ^ 3)) by simp]
    rw [hcast]
    norm_num [Nat.cast_add, Nat.cast_pow]
    ring
  have hpoint : ∀ t ∈ s,
      (((p * q + t : ℕ) : R) * ((p * q + (p - t) : ℕ) : R)) =
        B t * (1 + δ * (c * (B t)⁻¹)) := by
    intro t ht
    rw [hpair t ht]
    have hmul : B t * (B t)⁻¹ = 1 := ZMod.mul_inv_of_unit (B t) (hunit t ht)
    symm
    exact (calc
      B t * (1 + δ * (c * (B t)⁻¹)) = B t + δ * c := by
        rw [mul_add, mul_one]
        rw [show B t * (δ * (c * (B t)⁻¹)) = δ * c * (B t * (B t)⁻¹) by ring]
        rw [hmul]
        ring)
  have hprod_step :
      (∏ t ∈ s, (((p * q + t : ℕ) : R) * ((p * q + (p - t) : ℕ) : R))) =
        ∏ t ∈ s, (B t * (1 + δ * (c * (B t)⁻¹))) := by
    apply Finset.prod_congr rfl
    intro t ht
    exact hpoint t ht
  have hcalc :
      (∏ t ∈ s, (((p * q + t : ℕ) : R) * ((p * q + (p - t) : ℕ) : R))) =
        ∏ t ∈ s, B t := by
    calc
      (∏ t ∈ s, (((p * q + t : ℕ) : R) * ((p * q + (p - t) : ℕ) : R)))
          = ∏ t ∈ s, (B t * (1 + δ * (c * (B t)⁻¹))) := hprod_step
      _ = (∏ t ∈ s, B t) * (∏ t ∈ s, (1 + δ * (c * (B t)⁻¹))) := by
            rw [Finset.prod_mul_distrib]
      _ = (∏ t ∈ s, B t) * (1 + δ * (∑ t ∈ s, c * (B t)⁻¹)) := by
            rw [prod_one_add_square_zero_oeis_361883 s δ (fun t => c * (B t)⁻¹)]
            simpa [δ] using hδ2
      _ = (∏ t ∈ s, B t) := by
            have hz : δ * (∑ t ∈ s, c * (B t)⁻¹) = 0 := by
              simpa [R, s, δ, c, B, Nat.cast_pow, Nat.cast_add] using hzero
            rw [hz, add_zero, mul_one]
  exact (by simpa [s, B] using hcalc)


/-- The upper half of the positive representatives is carried to the lower half by `u ↦ p-u`.
This gives the usual pairing identity for inverse squares modulo an odd prime. -/
lemma zmod_half_pos_inv_sq_eq_zero_oeis_361883 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ t ∈ Finset.Icc 1 (p / 2), ((t : ZMod p)⁻¹) ^ 2) = 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let f : ℕ → ZMod p := fun t => ((t : ZMod p)⁻¹) ^ 2
  let pos : Finset ℕ := (Finset.range p).filter (fun t => 0 < t)
  let half : Finset ℕ := Finset.Icc 1 (p / 2)
  let upper : Finset ℕ := pos.filter (fun t => ¬ t ≤ p / 2)
  have hodd : 2 * (p / 2) + 1 = p := by
    have hpne2 : p ≠ 2 := by omega
    exact Nat.two_mul_div_two_add_one_of_odd (hp.odd_of_ne_two hpne2)
  have hhalf_eq : pos.filter (fun t => t ≤ p / 2) = half := by
    ext t
    constructor
    · intro ht
      have htpos : 0 < t := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
      have htle : t ≤ p / 2 := (Finset.mem_filter.mp ht).2
      exact Finset.mem_Icc.mpr ⟨by omega, htle⟩
    · intro ht
      have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
      have htle : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
      refine Finset.mem_filter.mpr ⟨?_, htle⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, by omega⟩
      omega
  have hupper_sum : (∑ u ∈ upper, f u) = ∑ t ∈ half, f t := by
    refine Finset.sum_bij (fun u hu => p - u) ?_ ?_ ?_ ?_
    · intro u hu
      have hupos : u ∈ pos := (Finset.mem_filter.mp hu).1
      have hu_not : ¬ u ≤ p / 2 := (Finset.mem_filter.mp hu).2
      have hu0 : 0 < u := (Finset.mem_filter.mp hupos).2
      have hup : u < p := Finset.mem_range.mp (Finset.mem_filter.mp hupos).1
      have hu_ge : p / 2 + 1 ≤ u := Nat.succ_le_of_lt (Nat.lt_of_not_ge hu_not)
      refine Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.sub_pos_of_lt hup), ?_⟩
      calc
        p - u ≤ p - (p / 2 + 1) := Nat.sub_le_sub_left hu_ge p
        _ = p / 2 := by omega
    · intro u hu v hv huv
      change p - u = p - v at huv
      have hupos : u ∈ pos := (Finset.mem_filter.mp hu).1
      have hvpos : v ∈ pos := (Finset.mem_filter.mp hv).1
      have hup : u < p := Finset.mem_range.mp (Finset.mem_filter.mp hupos).1
      have hvp : v < p := Finset.mem_range.mp (Finset.mem_filter.mp hvpos).1
      calc
        u = p - (p - u) := (Nat.sub_sub_self (Nat.le_of_lt hup)).symm
        _ = p - (p - v) := by rw [huv]
        _ = v := Nat.sub_sub_self (Nat.le_of_lt hvp)
    · intro t ht
      refine ⟨p - t, ?_, ?_⟩
      · have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
        have htle : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
          · exact Nat.sub_lt hp.pos ht1
          · exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt (by omega : t < p))
        · have hge : p / 2 + 1 ≤ p - t := by
            apply Nat.le_sub_of_add_le
            omega
          exact not_le.mpr (by omega)
      · exact Nat.sub_sub_self (Nat.le_trans (Finset.mem_Icc.mp ht).2 (Nat.div_le_self p 2))
    · intro u hu
      have hupos : u ∈ pos := (Finset.mem_filter.mp hu).1
      have hup : u < p := Finset.mem_range.mp (Finset.mem_filter.mp hupos).1
      have hcast : ((p - u : ℕ) : ZMod p) = -(u : ZMod p) := by
        rw [Nat.cast_sub (by omega : u ≤ p)]
        simp
      dsimp [f]
      rw [hcast, inv_neg]
      ring
  have hfull : (∑ t ∈ pos, f t) = 0 := by
    dsimp [pos, f]
    simpa using zmod_sum_range_pos_inv_sq_eq_zero_oeis_361883 p hp5
  have hsplit : (∑ t ∈ pos, f t) =
      (∑ t ∈ pos.filter (fun t => t ≤ p / 2), f t) + ∑ t ∈ upper, f t := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := pos) (p := fun t => t ≤ p / 2) (f := f)]
  have hdouble : (∑ t ∈ pos, f t) = (∑ t ∈ half, f t) + ∑ t ∈ half, f t := by
    rw [hsplit, hhalf_eq, hupper_sum]
  have htwo_mul : (2 : ZMod p) * (∑ t ∈ half, f t) = 0 := by
    have := hfull
    rw [hdouble] at this
    simpa [two_mul] using this
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h
    have hp_le_two : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hres : (∑ t ∈ half, f t) = 0 := by
    exact (mul_eq_zero.mp htwo_mul).resolve_left htwo_ne
  simpa [half, f] using hres

/-- On the lower half modulo `p`, `(t*(p-t))⁻¹ = - (t⁻¹)^2`; hence its sum vanishes. -/
lemma zmod_half_inv_pair_sum_eq_zero_oeis_361883 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ t ∈ Finset.Icc 1 (p / 2), (((t * (p - t) : ℕ) : ZMod p)⁻¹)) = 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  calc
    (∑ t ∈ Finset.Icc 1 (p / 2), (((t * (p - t) : ℕ) : ZMod p)⁻¹))
        = ∑ t ∈ Finset.Icc 1 (p / 2), -(((t : ZMod p)⁻¹) ^ 2) := by
          apply Finset.sum_congr rfl
          intro t ht
          have htle : t ≤ p := by
            have htle' : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
            omega
          have hprod : (((t * (p - t) : ℕ) : ZMod p)) = -((t : ZMod p) ^ 2) := by
            rw [Nat.cast_mul, Nat.cast_sub htle]
            simp
            ring
          rw [hprod, inv_neg]
          rw [← inv_pow]
    _ = - (∑ t ∈ Finset.Icc 1 (p / 2), ((t : ZMod p)⁻¹) ^ 2) := by
          rw [Finset.sum_neg_distrib]
    _ = 0 := by
          rw [zmod_half_pos_inv_sq_eq_zero_oeis_361883 (p := p) hp hp5, neg_zero]

/-- Reduction of inverses from `ZMod (p^3)` to `ZMod p` for integers prime to `p`. -/
lemma zmod_castHom_inv_p3_to_p_of_not_dvd_oeis_361883 {p k : ℕ} (hp : p.Prime)
    (hnot : ¬ p ∣ k) :
    let R := ZMod (p ^ 3)
    ZMod.castHom (show p ∣ p ^ 3 by exact dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
      (((k : ℕ) : R)⁻¹) = (((k : ℕ) : ZMod p)⁻¹) := by
  intro R
  let f := ZMod.castHom (show p ∣ p ^ 3 by exact dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
  have hcopR : Nat.Coprime k (p ^ 3) :=
    Nat.Coprime.pow_right 3 (((hp.coprime_iff_not_dvd).2 hnot).symm)
  have hcopP : Nat.Coprime k p := ((hp.coprime_iff_not_dvd).2 hnot).symm
  let uR : Rˣ := ZMod.unitOfCoprime k hcopR
  let uP : (ZMod p)ˣ := ZMod.unitOfCoprime k hcopP
  have hmapu : Units.map f.toMonoidHom uR = uP := by
    apply Units.ext
    change f (k : R) = (k : ZMod p)
    simp [f]
  have hmapinv : f ((uR⁻¹ : Rˣ) : R) = ((uP⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    calc
      f ((uR⁻¹ : Rˣ) : R) = ((Units.map f.toMonoidHom uR)⁻¹ : (ZMod p)ˣ) := by
        exact (Units.coe_map_inv f.toMonoidHom uR).symm
      _ = ((uP⁻¹ : (ZMod p)ˣ) : ZMod p) := by rw [hmapu]
  have hinvR : ((k : R)⁻¹) = ((uR⁻¹ : Rˣ) : R) := by
    simpa [uR] using ZMod.inv_coe_unit uR
  have hinvP : ((k : ZMod p)⁻¹) = ((uP⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    simpa [uP] using ZMod.inv_coe_unit uP
  calc
    f (((k : ℕ) : R)⁻¹) = f ((uR⁻¹ : Rˣ) : R) := by rw [hinvR]
    _ = ((uP⁻¹ : (ZMod p)ˣ) : ZMod p) := hmapinv
    _ = (((k : ℕ) : ZMod p)⁻¹) := by rw [hinvP]

/-- The inverse-pair obstruction in the conditional paired-product lemma is zero. -/
lemma paired_product_block_zmod_p3_inv_sum_zero_oeis_361883 {p q : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    let R := ZMod (p ^ 3)
    ((p ^ 2 : ℕ) : R) *
      (∑ t ∈ Finset.Icc 1 (p / 2),
        ((q + q ^ 2 : ℕ) : R) * (((t * (p - t) : ℕ) : R)⁻¹)) = 0 := by
  classical
  intro R
  let s := Finset.Icc 1 (p / 2)
  let cR : R := ((q + q ^ 2 : ℕ) : R)
  let inner : R := ∑ t ∈ s, cR * (((t * (p - t) : ℕ) : R)⁻¹)
  let phi := ZMod.castHom (show p ∣ p ^ 3 by exact dvd_pow_self p (by norm_num : 3 ≠ 0)) (ZMod p)
  have hmap_inner : phi inner = 0 := by
    calc
      phi inner = ∑ t ∈ s, phi (cR * (((t * (p - t) : ℕ) : R)⁻¹)) := by
        simp [inner]
      _ = ∑ t ∈ s, ((q + q ^ 2 : ℕ) : ZMod p) *
            ((((t * (p - t) : ℕ) : ZMod p)⁻¹)) := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
        have htle_half : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
        have htp : t < p := by omega
        have hptpos : 0 < p - t := by omega
        have hptlt : p - t < p := by omega
        have hnot_t : ¬ p ∣ t := Nat.not_dvd_of_pos_of_lt (by omega) htp
        have hnot_pt : ¬ p ∣ p - t := Nat.not_dvd_of_pos_of_lt hptpos hptlt
        have hnot : ¬ p ∣ t * (p - t) := by
          intro h
          rcases hp.dvd_mul.mp h with h | h
          · exact hnot_t h
          · exact hnot_pt h
        have hinvmap :
            phi ((((t * (p - t) : ℕ) : R)⁻¹)) =
              ((((t * (p - t) : ℕ) : ZMod p)⁻¹)) := by
          simpa [phi] using
            zmod_castHom_inv_p3_to_p_of_not_dvd_oeis_361883 (p := p)
              (k := t * (p - t)) hp hnot
        have hcmap : phi cR = ((q + q ^ 2 : ℕ) : ZMod p) := by
          dsimp [phi, cR]
          exact ZMod.cast_natCast
            (show p ∣ p ^ 3 by exact dvd_pow_self p (by norm_num : 3 ≠ 0)) (q + q ^ 2)
        calc
          phi (cR * (((t * (p - t) : ℕ) : R)⁻¹)) =
              phi cR * phi ((((t * (p - t) : ℕ) : R)⁻¹)) := by
            rw [map_mul]
          _ = ((q + q ^ 2 : ℕ) : ZMod p) *
              ((((t * (p - t) : ℕ) : ZMod p)⁻¹)) := by
            rw [hinvmap, hcmap]
      _ = ((q + q ^ 2 : ℕ) : ZMod p) *
            (∑ t ∈ s, ((((t * (p - t) : ℕ) : ZMod p)⁻¹))) := by
        rw [Finset.mul_sum]
      _ = 0 := by
        rw [zmod_half_inv_pair_sum_eq_zero_oeis_361883 (p := p) hp hp5, mul_zero]
  have hkill' :=
    zmod_p_sq_mul_eq_zero_of_castHom_p_eq_zero_oeis_361883 (p := p) hp inner hmap_inner
  have hkill : ((p ^ 2 : ℕ) : R) * inner = 0 := by
    simpa [Nat.cast_pow] using hkill'
  simpa [inner, cR, s, Nat.cast_pow] using hkill

/-- Unconditional paired product-block congruence modulo `p^3` for primes `p ≥ 5`. -/
lemma paired_product_block_zmod_p3_oeis_361883 {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
  let R := ZMod (p ^ 3)
  (∏ t ∈ Finset.Icc 1 (p / 2),
    (((p * q + t : ℕ) : R) * ((p * q + (p - t) : ℕ) : R))) =
  (∏ t ∈ Finset.Icc 1 (p / 2), ((t * (p - t) : ℕ) : R)) := by
  exact paired_product_block_zmod_p3_of_inv_sum_zero_oeis_361883 hp hp5
    (paired_product_block_zmod_p3_inv_sum_zero_oeis_361883 (p := p) (q := q) hp hp5)

/-- Full positive block product modulo `p^3`, obtained by pairing `t` with `p - t`. -/
lemma product_block_zmod_p3_oeis_361883 {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
  let R := ZMod (p ^ 3)
  (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * q + t : ℕ) : R)) =
  (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((t : ℕ) : R)) := by
  classical
  intro R
  let pos : Finset ℕ := (Finset.range p).filter (fun t => 0 < t)
  let half : Finset ℕ := Finset.Icc 1 (p / 2)
  let upper : Finset ℕ := pos.filter (fun t => ¬ t ≤ p / 2)
  have hodd : 2 * (p / 2) + 1 = p := by
    have hpne2 : p ≠ 2 := by omega
    exact Nat.two_mul_div_two_add_one_of_odd (hp.odd_of_ne_two hpne2)
  have hhalf_eq : pos.filter (fun t => t ≤ p / 2) = half := by
    ext t
    constructor
    · intro ht
      have htpos : 0 < t := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
      have htle : t ≤ p / 2 := (Finset.mem_filter.mp ht).2
      exact Finset.mem_Icc.mpr ⟨by omega, htle⟩
    · intro ht
      have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
      have htle : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
      refine Finset.mem_filter.mpr ⟨?_, htle⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, by omega⟩
      omega
  have hprod_pair (g : ℕ → R) :
      (∏ t ∈ pos, g t) = ∏ t ∈ half, g t * g (p - t) := by
    have hupper_prod : (∏ u ∈ upper, g u) = ∏ t ∈ half, g (p - t) := by
      refine Finset.prod_bij (fun u hu => p - u) ?_ ?_ ?_ ?_
      · intro u hu
        have hupos : u ∈ pos := (Finset.mem_filter.mp hu).1
        have hu_not : ¬ u ≤ p / 2 := (Finset.mem_filter.mp hu).2
        have hu0 : 0 < u := (Finset.mem_filter.mp hupos).2
        have hup : u < p := Finset.mem_range.mp (Finset.mem_filter.mp hupos).1
        have hu_ge : p / 2 + 1 ≤ u := Nat.succ_le_of_lt (Nat.lt_of_not_ge hu_not)
        refine Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.sub_pos_of_lt hup), ?_⟩
        calc
          p - u ≤ p - (p / 2 + 1) := Nat.sub_le_sub_left hu_ge p
          _ = p / 2 := by omega
      · intro u hu v hv huv
        change p - u = p - v at huv
        have hupos : u ∈ pos := (Finset.mem_filter.mp hu).1
        have hvpos : v ∈ pos := (Finset.mem_filter.mp hv).1
        have hup : u < p := Finset.mem_range.mp (Finset.mem_filter.mp hupos).1
        have hvp : v < p := Finset.mem_range.mp (Finset.mem_filter.mp hvpos).1
        calc
          u = p - (p - u) := (Nat.sub_sub_self (Nat.le_of_lt hup)).symm
          _ = p - (p - v) := by rw [huv]
          _ = v := Nat.sub_sub_self (Nat.le_of_lt hvp)
      · intro t ht
        refine ⟨p - t, ?_, ?_⟩
        · have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
          have htle : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
          refine Finset.mem_filter.mpr ⟨?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
            · exact Nat.sub_lt hp.pos ht1
            · exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt (by omega : t < p))
          · have hge : p / 2 + 1 ≤ p - t := by
              apply Nat.le_sub_of_add_le
              omega
            exact not_le.mpr (by omega)
        · exact Nat.sub_sub_self (Nat.le_trans (Finset.mem_Icc.mp ht).2 (Nat.div_le_self p 2))
      · intro u hu
        have hupos : u ∈ pos := (Finset.mem_filter.mp hu).1
        have hup : u < p := Finset.mem_range.mp (Finset.mem_filter.mp hupos).1
        have hsub : p - (p - u) = u := Nat.sub_sub_self (Nat.le_of_lt hup)
        dsimp
        rw [hsub]
    calc
      (∏ t ∈ pos, g t)
          = (∏ t ∈ pos.filter (fun t => t ≤ p / 2), g t) *
              ∏ t ∈ upper, g t := by
            exact (Finset.prod_filter_mul_prod_filter_not pos (fun t => t ≤ p / 2) g).symm
      _ = (∏ t ∈ half, g t) * ∏ t ∈ half, g (p - t) := by
            rw [hhalf_eq, hupper_prod]
      _ = ∏ t ∈ half, g t * g (p - t) := by
            rw [Finset.prod_mul_distrib]
  have hleft_pair :
      (∏ t ∈ pos, ((p * q + t : ℕ) : R)) =
        (∏ t ∈ half,
          (((p * q + t : ℕ) : R) * ((p * q + (p - t) : ℕ) : R))) := by
    simpa [pos, half] using hprod_pair (fun t => ((p * q + t : ℕ) : R))
  have hright_pair :
      (∏ t ∈ pos, ((t : ℕ) : R)) =
        (∏ t ∈ half, ((t * (p - t) : ℕ) : R)) := by
    calc
      (∏ t ∈ pos, ((t : ℕ) : R)) = ∏ t ∈ half, ((t : ℕ) : R) * ((p - t : ℕ) : R) := by
        simpa [pos, half] using hprod_pair (fun t => ((t : ℕ) : R))
      _ = ∏ t ∈ half, ((t * (p - t) : ℕ) : R) := by
        apply Finset.prod_congr rfl
        intro t ht
        rw [Nat.cast_mul]
  calc
    (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * q + t : ℕ) : R))
        = (∏ t ∈ Finset.Icc 1 (p / 2),
            (((p * q + t : ℕ) : R) * ((p * q + (p - t) : ℕ) : R))) := by
          simpa [pos, half] using hleft_pair
    _ = (∏ t ∈ Finset.Icc 1 (p / 2), ((t * (p - t) : ℕ) : R)) := by
          simpa using paired_product_block_zmod_p3_oeis_361883 (p := p) (q := q) hp hp5
    _ = (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((t : ℕ) : R)) := by
          simpa [pos, half] using hright_pair.symm


/-- Pair the nonzero residues modulo an odd prime into the lower half `t` and `p - t`.
This standalone form is useful for block-product congruences in several moduli. -/
lemma prod_pos_eq_prod_half_pair_oeis_361883 {M : Type*} [CommMonoid M]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (g : ℕ → M) :
    (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), g t) =
      ∏ t ∈ Finset.Icc 1 (p / 2), g t * g (p - t) := by
  classical
  let pos : Finset ℕ := (Finset.range p).filter (fun t => 0 < t)
  let half : Finset ℕ := Finset.Icc 1 (p / 2)
  let upper : Finset ℕ := pos.filter (fun t => ¬ t ≤ p / 2)
  have hodd : 2 * (p / 2) + 1 = p := by
    have hpne2 : p ≠ 2 := by omega
    exact Nat.two_mul_div_two_add_one_of_odd (hp.odd_of_ne_two hpne2)
  have hhalf_eq : pos.filter (fun t => t ≤ p / 2) = half := by
    ext t
    constructor
    · intro ht
      have htpos : 0 < t := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2
      have htle : t ≤ p / 2 := (Finset.mem_filter.mp ht).2
      exact Finset.mem_Icc.mpr ⟨by omega, htle⟩
    · intro ht
      have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
      have htle : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
      refine Finset.mem_filter.mpr ⟨?_, htle⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, by omega⟩
      omega
  have hupper_prod : (∏ u ∈ upper, g u) = ∏ t ∈ half, g (p - t) := by
    refine Finset.prod_bij (fun u hu => p - u) ?_ ?_ ?_ ?_

    · intro u hu
      have hupos : u ∈ pos := (Finset.mem_filter.mp hu).1
      have hu_not : ¬ u ≤ p / 2 := (Finset.mem_filter.mp hu).2
      have hu0 : 0 < u := (Finset.mem_filter.mp hupos).2
      have hup : u < p := Finset.mem_range.mp (Finset.mem_filter.mp hupos).1
      have hu_ge : p / 2 + 1 ≤ u := Nat.succ_le_of_lt (Nat.lt_of_not_ge hu_not)
      refine Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.sub_pos_of_lt hup), ?_⟩
      calc
        p - u ≤ p - (p / 2 + 1) := Nat.sub_le_sub_left hu_ge p
        _ = p / 2 := by omega
    · intro u hu v hv huv
      change p - u = p - v at huv
      have hupos : u ∈ pos := (Finset.mem_filter.mp hu).1
      have hvpos : v ∈ pos := (Finset.mem_filter.mp hv).1
      have hup : u < p := Finset.mem_range.mp (Finset.mem_filter.mp hupos).1
      have hvp : v < p := Finset.mem_range.mp (Finset.mem_filter.mp hvpos).1
      calc
        u = p - (p - u) := (Nat.sub_sub_self (Nat.le_of_lt hup)).symm
        _ = p - (p - v) := by rw [huv]
        _ = v := Nat.sub_sub_self (Nat.le_of_lt hvp)
    · intro t ht
      refine ⟨p - t, ?_, ?_⟩
      · have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
        have htle : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
          · exact Nat.sub_lt hp.pos ht1
          · exact Nat.succ_le_of_lt (Nat.sub_pos_of_lt (by omega : t < p))
        · have hge : p / 2 + 1 ≤ p - t := by
            apply Nat.le_sub_of_add_le
            omega
          exact not_le.mpr (by omega)
      · exact Nat.sub_sub_self (Nat.le_trans (Finset.mem_Icc.mp ht).2 (Nat.div_le_self p 2))
    · intro u hu
      have hupos : u ∈ pos := (Finset.mem_filter.mp hu).1
      have hup : u < p := Finset.mem_range.mp (Finset.mem_filter.mp hupos).1
      have hsub : p - (p - u) = u := Nat.sub_sub_self (Nat.le_of_lt hup)
      dsimp
      rw [hsub]
  calc
    (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), g t)
        = (∏ t ∈ pos.filter (fun t => t ≤ p / 2), g t) *
            ∏ t ∈ upper, g t := by
          exact (Finset.prod_filter_mul_prod_filter_not pos (fun t => t ≤ p / 2) g).symm
    _ = (∏ t ∈ half, g t) * ∏ t ∈ half, g (p - t) := by
          rw [hhalf_eq, hupper_prod]
    _ = ∏ t ∈ Finset.Icc 1 (p / 2), g t * g (p - t) := by
          rw [Finset.prod_mul_distrib]

/-- Paired block-product congruence modulo `p^(s+2)` when the block parameter is divisible
by `p^s`.  In this modulus the pair perturbation `p^2 * (q + q^2)` vanishes outright. -/
lemma paired_product_block_zmod_pow_s2_of_q_dvd_oeis_361883 {p q s : ℕ}
    (_hp : p.Prime) (hq : p ^ s ∣ q) :
    let R := ZMod (p ^ (s + 2))
    (∏ t ∈ Finset.Icc 1 (p / 2),
      (((p * q + t : ℕ) : R) * ((p * q + (p - t) : ℕ) : R))) =
    (∏ t ∈ Finset.Icc 1 (p / 2), ((t * (p - t) : ℕ) : R)) := by
  classical
  intro R
  have hbase : p ^ (s + 2) ∣ p ^ 2 * q := by
    have hmul : p ^ 2 * p ^ s ∣ p ^ 2 * q := Nat.mul_dvd_mul_left (p ^ 2) hq
    have hpows : p ^ 2 * p ^ s = p ^ (s + 2) := by
      rw [← pow_add]
      congr 1
      omega
    simpa [hpows, mul_assoc, mul_left_comm, mul_comm] using hmul
  have htotal : p ^ (s + 2) ∣ p ^ 2 * (q + q ^ 2) := by
    have hmul : p ^ (s + 2) ∣ (p ^ 2 * q) * (1 + q) := dvd_mul_of_dvd_left hbase (1 + q)
    have heq : p ^ 2 * (q + q ^ 2) = (p ^ 2 * q) * (1 + q) := by ring
    simpa [heq] using hmul
  have hzero : ((p ^ 2 * (q + q ^ 2) : ℕ) : R) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (p ^ 2 * (q + q ^ 2)) (p ^ (s + 2))).2 htotal
  let B : ℕ → R := fun t => ((t * (p - t) : ℕ) : R)
  have hpair : ∀ t ∈ Finset.Icc 1 (p / 2),
      (((p * q + t : ℕ) : R) * ((p * q + (p - t) : ℕ) : R)) = B t := by
    intro t ht
    have htle : t ≤ p := by
      have htle' : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
      omega
    dsimp [B, R]
    have hcast : ((p - t : ℕ) : ZMod (p ^ (s + 2))) = (p : ZMod (p ^ (s + 2))) - t := by
      rw [Nat.cast_sub htle]
    calc
      (((p * q + t : ℕ) : ZMod (p ^ (s + 2))) *
          ((p * q + (p - t) : ℕ) : ZMod (p ^ (s + 2))))
          = ((t * (p - t) : ℕ) : ZMod (p ^ (s + 2))) +
              ((p ^ 2 * (q + q ^ 2) : ℕ) : ZMod (p ^ (s + 2))) := by
            rw [show ((p * q + (p - t) : ℕ) : ZMod (p ^ (s + 2))) =
                (p : ZMod (p ^ (s + 2))) * q + ((p - t : ℕ) : ZMod (p ^ (s + 2))) by simp]
            rw [hcast]
            rw [show ((p * q + t : ℕ) : ZMod (p ^ (s + 2))) =
                (p : ZMod (p ^ (s + 2))) * q + t by simp]
            rw [show ((t * (p - t) : ℕ) : ZMod (p ^ (s + 2))) =
                (t : ZMod (p ^ (s + 2))) * ((p - t : ℕ) : ZMod (p ^ (s + 2))) by simp]
            rw [hcast]
            norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
            ring
      _ = ((t * (p - t) : ℕ) : ZMod (p ^ (s + 2))) := by rw [hzero, add_zero]
  apply Finset.prod_congr rfl
  intro t ht
  exact hpair t ht

/-- Generalized positive block product modulo `p^(s+2)`: if `p^s ∣ q`, then shifting the
block by `p*q` does not change the product of the nonzero residues. -/
lemma product_block_zmod_pow_s2_of_q_dvd_oeis_361883 {p q s : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hq : p ^ s ∣ q) :
    let R := ZMod (p ^ (s + 2))
    (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * q + t : ℕ) : R)) =
    (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((t : ℕ) : R)) := by
  classical
  intro R
  calc
    (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * q + t : ℕ) : R))
        = (∏ t ∈ Finset.Icc 1 (p / 2),
            (((p * q + t : ℕ) : R) * ((p * q + (p - t) : ℕ) : R))) := by
          simpa using prod_pos_eq_prod_half_pair_oeis_361883 (M := R) hp hp5
            (fun t => ((p * q + t : ℕ) : R))
    _ = (∏ t ∈ Finset.Icc 1 (p / 2), ((t * (p - t) : ℕ) : R)) := by
          simpa using paired_product_block_zmod_pow_s2_of_q_dvd_oeis_361883
            (p := p) (q := q) (s := s) hp hq
    _ = (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((t : ℕ) : R)) := by
          have hright := prod_pos_eq_prod_half_pair_oeis_361883 (M := R) hp hp5
            (fun t => ((t : ℕ) : R))
          calc
            (∏ t ∈ Finset.Icc 1 (p / 2), ((t * (p - t) : ℕ) : R))
                = ∏ t ∈ Finset.Icc 1 (p / 2), ((t : ℕ) : R) * ((p - t : ℕ) : R) := by
                  apply Finset.prod_congr rfl
                  intro t ht
                  rw [Nat.cast_mul]
            _ = (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((t : ℕ) : R)) := by
                  rw [hright]


/-- The product of the non-`p`-divisible factors in the block decomposition of `(p*N)!`. -/
def unitPartProd_oeis_361883 (p N : ℕ) : ℕ :=
  ∏ q ∈ Finset.range N, ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), (p * q + t)


/-- Split-valuation unit-part multiplicativity at the asymmetric superblock precision. -/
lemma unitPartProd_zmod_pow_split_add_of_dvd_le_oeis_361883 {p B C s t : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hB : p ^ s ∣ B) (hC : p ^ t ∣ C) (hst : t ≤ s) :
    let R := ZMod (p ^ (s + 2 * t + 3))
    ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
      ((unitPartProd_oeis_361883 p B : ℕ) : R) *
        ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
  classical
  rcases hB with ⟨b, rfl⟩
  rcases hC with ⟨c, rfl⟩
  intro R
  let b' : ℕ := p ^ (s - t) * b
  have hBpow : p ^ s * b = p ^ t * b' := by
    dsimp [b']
    have hpows : p ^ s = p ^ t * p ^ (s - t) := by
      rw [← pow_add, Nat.add_sub_of_le hst]
    rw [hpows]
    ring
  let block : ℕ → R := fun q =>
    ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0), ((p * q + t0 : ℕ) : R)
  let group : ℕ → R := fun v => ∏ u ∈ Finset.range (p ^ t), block (p ^ t * v + u)
  have hunit_mul : ∀ n : ℕ,
      ((unitPartProd_oeis_361883 p (p ^ t * n) : ℕ) : R) = ∏ v ∈ Finset.range n, group v := by
    intro n
    calc
      ((unitPartProd_oeis_361883 p (p ^ t * n) : ℕ) : R)
          = ∏ q ∈ Finset.range (p ^ t * n), block q := by
              simp [unitPartProd_oeis_361883, block, Nat.cast_prod]
      _ = ∏ q ∈ Finset.range (n * p ^ t), block q := by
              rw [show p ^ t * n = n * p ^ t by rw [Nat.mul_comm]]
      _ = ∏ v ∈ Finset.range n, ∏ u ∈ Finset.range (p ^ t), block (p ^ t * v + u) := by
              rw [prod_range_mul_decomp_oeis_361883]
      _ = ∏ v ∈ Finset.range n, group v := by
              rfl
  have hgroup_shift : ∀ v ∈ Finset.range c, group (b' + v) = group v := by
    intro v _hv
    calc
      group (b' + v)
          = ∏ u ∈ Finset.range (p ^ t),
              ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0),
                ((p * (p ^ s * b + (p ^ t * v + u)) + t0 : ℕ) : R) := by
              dsimp [group, block]
              apply Finset.prod_congr rfl
              intro u hu
              apply Finset.prod_congr rfl
              intro t0 ht0
              congr 1
              rw [hBpow]
              ring
      _ = ∏ u ∈ Finset.range (p ^ t),
              ∏ t0 ∈ (Finset.range p).filter (fun t0 => 0 < t0),
                ((p * (p ^ t * v + u) + t0 : ℕ) : R) := by
              exact unit_block_supergroup_shift_asym_zmod_oeis_361883
                (p := p) (s := s) (t := t) (b := b) (v := v) hp hp5 hst
      _ = group v := by
              rfl
  have hBC : p ^ s * b + p ^ t * c = p ^ t * (b' + c) := by
    rw [hBpow]
    ring
  calc
    ((unitPartProd_oeis_361883 p (p ^ s * b + p ^ t * c) : ℕ) : R)
        = ((unitPartProd_oeis_361883 p (p ^ t * (b' + c)) : ℕ) : R) := by
            rw [hBC]
    _ = ∏ v ∈ Finset.range (b' + c), group v := by
            rw [hunit_mul]
    _ = (∏ v ∈ Finset.range b', group v) * ∏ v ∈ Finset.range c, group (b' + v) := by
            rw [Finset.prod_range_add]
    _ = (∏ v ∈ Finset.range b', group v) * ∏ v ∈ Finset.range c, group v := by
            congr 1
            apply Finset.prod_congr rfl
            intro v hv
            exact hgroup_shift v hv
    _ = ((unitPartProd_oeis_361883 p (p ^ s * b) : ℕ) : R) *
          ((unitPartProd_oeis_361883 p (p ^ t * c) : ℕ) : R) := by
            rw [hBpow]
            rw [hunit_mul, hunit_mul]



/-- Unit-part multiplicativity modulo `p^9` when both arguments are divisible by `p^2`. -/
lemma unitPartProd_zmod_p9_add_of_p2_dvd_both_oeis_361883 {p B C : ℕ}
  (hp : p.Prime) (hp5 : 5 ≤ p) (hB : p ^ 2 ∣ B) (hC : p ^ 2 ∣ C) :
  let R := ZMod (p ^ 9)
  ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
    ((unitPartProd_oeis_361883 p B : ℕ) : R) * ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
  classical
  rcases hB with ⟨b, rfl⟩
  rcases hC with ⟨c, rfl⟩
  intro R
  let block : ℕ → R := fun q =>
    ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * q + t : ℕ) : R)
  let group : ℕ → R := fun v => ∏ m ∈ Finset.range (p ^ 2), block (p ^ 2 * v + m)
  have hunit_mul : ∀ n : ℕ,
      ((unitPartProd_oeis_361883 p (p ^ 2 * n) : ℕ) : R) = ∏ v ∈ Finset.range n, group v := by
    intro n
    calc
      ((unitPartProd_oeis_361883 p (p ^ 2 * n) : ℕ) : R)
          = ∏ q ∈ Finset.range (p ^ 2 * n), block q := by
              simp [unitPartProd_oeis_361883, block, Nat.cast_prod]
      _ = ∏ q ∈ Finset.range (n * p ^ 2), block q := by
              rw [Nat.mul_comm]
      _ = ∏ v ∈ Finset.range n, ∏ m ∈ Finset.range (p ^ 2), block (p ^ 2 * v + m) := by
              rw [prod_range_mul_decomp_oeis_361883]
      _ = ∏ v ∈ Finset.range n, group v := by
              rfl
  have hgroup_shift : ∀ v ∈ Finset.range c, group (b + v) = group v := by
    intro v _hv
    dsimp [group, block]
    exact unit_block_supergroup_shift_zmod_p9_oeis_361883 (p := p) (b := b) (v := v) hp hp5
  calc
    ((unitPartProd_oeis_361883 p (p ^ 2 * b + p ^ 2 * c) : ℕ) : R)
        = ((unitPartProd_oeis_361883 p (p ^ 2 * (b + c)) : ℕ) : R) := by
            congr 1
            ring_nf
    _ = ∏ v ∈ Finset.range (b + c), group v := hunit_mul (b + c)
    _ = (∏ v ∈ Finset.range b, group v) * ∏ v ∈ Finset.range c, group (b + v) := by
            rw [Finset.prod_range_add]
    _ = (∏ v ∈ Finset.range b, group v) * ∏ v ∈ Finset.range c, group v := by
            congr 1
            apply Finset.prod_congr rfl
            intro v hv
            exact hgroup_shift v hv
    _ = ((unitPartProd_oeis_361883 p (p ^ 2 * b) : ℕ) : R) *
        ((unitPartProd_oeis_361883 p (p ^ 2 * c) : ℕ) : R) := by
            rw [hunit_mul b, hunit_mul c]


/-- Rewrite the `p^2` unit superblock as `p` consecutive ordinary unit blocks. -/
lemma unit_superblock_eq_prod_blocks_zmod_p6_oeis_361883 {p d : ℕ} (hp : p.Prime) :
    let R := ZMod (p ^ 6)
    (∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
        ((p ^ 2 * d + x : ℕ) : R)) =
      ∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p ^ 2 * d + (p * m + t) : ℕ) : R) := by
  classical
  intro R
  let G : ℕ → R := fun x => ((p ^ 2 * d + x : ℕ) : R)
  have hiff : ∀ m ∈ Finset.range p, ∀ t ∈ Finset.range p,
      (Nat.Coprime (p * m + t) (p ^ 2) ↔ 0 < t) := by
    intro m _hm t ht
    have htp : t < p := Finset.mem_range.mp ht
    constructor
    · intro hcop
      by_contra ht0
      have ht_eq : t = 0 := Nat.eq_zero_of_not_pos ht0
      have hdiv : p ∣ p * m + t := by
        rw [ht_eq, add_zero]
        exact dvd_mul_right p m
      have hp_dvd_pow : p ∣ p ^ 2 := dvd_pow_self p (by decide : 2 ≠ 0)
      exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hdiv hp_dvd_pow) hcop
    · intro htpos
      have hnot : ¬ p ∣ p * m + t := by
        intro hdiv
        have hpdm : p ∣ p * m := dvd_mul_right p m
        have htdvd : p ∣ t := (Nat.dvd_add_iff_right hpdm).2 hdiv
        exact (Nat.not_dvd_of_pos_of_lt htpos htp) htdvd
      exact hp.coprime_pow_of_not_dvd hnot
  calc
    (∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)), G x)
        = ∏ x ∈ Finset.range (p ^ 2), if Nat.Coprime x (p ^ 2) then G x else 1 := by
          rw [Finset.prod_filter]
    _ = ∏ x ∈ Finset.range (p * p), if Nat.Coprime x (p ^ 2) then G x else 1 := by
          rw [show p ^ 2 = p * p by ring_nf]
    _ = ∏ m ∈ Finset.range p,
          ∏ t ∈ Finset.range p, if Nat.Coprime (p * m + t) (p ^ 2) then G (p * m + t) else 1 := by
          rw [prod_range_mul_decomp_oeis_361883]
    _ = ∏ m ∈ Finset.range p,
          ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), G (p * m + t) := by
          apply Finset.prod_congr rfl
          intro m hm
          calc
            (∏ t ∈ Finset.range p, if Nat.Coprime (p * m + t) (p ^ 2) then G (p * m + t) else 1)
                = ∏ t ∈ Finset.range p, if 0 < t then G (p * m + t) else 1 := by
                  apply Finset.prod_congr rfl
                  intro t ht
                  by_cases htpos : 0 < t
                  · have hc : Nat.Coprime (p * m + t) (p ^ 2) := (hiff m hm t ht).2 htpos
                    rw [if_pos hc, if_pos htpos]
                  · have hnc : ¬ Nat.Coprime (p * m + t) (p ^ 2) := by
                      intro hc
                      exact htpos ((hiff m hm t ht).1 hc)
                    rw [if_neg hnc, if_neg htpos]
            _ = ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), G (p * m + t) := by
                  exact (Finset.prod_filter (s := Finset.range p) (p := fun t => 0 < t)
                    (f := fun t => G (p * m + t))).symm
    _ = ∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p ^ 2 * d + (p * m + t) : ℕ) : R) := by
          rfl

/-- A group of `p` ordinary unit blocks is invariant modulo `p^6` when shifted by `p*b`. -/
lemma unit_block_group_shift_zmod_p6_oeis_361883 {p b v : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    let R := ZMod (p ^ 6)
    (∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * (b + v) + m) + t : ℕ) : R)) =
      ∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * v + m) + t : ℕ) : R) := by
  classical
  intro R
  let S : ℕ → R := fun d =>
    ∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
      ((p ^ 2 * d + x : ℕ) : R)
  have hblocks_left :
      (∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * (b + v) + m) + t : ℕ) : R)) = S (b + v) := by
    calc
      (∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * (b + v) + m) + t : ℕ) : R))
          = ∏ m ∈ Finset.range p,
              ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
                ((p ^ 2 * (b + v) + (p * m + t) : ℕ) : R) := by
              apply Finset.prod_congr rfl
              intro m hm
              apply Finset.prod_congr rfl
              intro t ht
              congr 1
              ring_nf
      _ = S (b + v) := by
          dsimp [S]
          rw [unit_superblock_eq_prod_blocks_zmod_p6_oeis_361883 (p := p) (d := b + v) hp]
  have hblocks_right :
      (∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * v + m) + t : ℕ) : R)) = S v := by
    calc
      (∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * v + m) + t : ℕ) : R))
          = ∏ m ∈ Finset.range p,
              ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
                ((p ^ 2 * v + (p * m + t) : ℕ) : R) := by
              apply Finset.prod_congr rfl
              intro m hm
              apply Finset.prod_congr rfl
              intro t ht
              congr 1
              ring_nf
      _ = S v := by
          dsimp [S]
          rw [unit_superblock_eq_prod_blocks_zmod_p6_oeis_361883 (p := p) (d := v) hp]
  have hleft_shift : S (b + v) = S 0 := by
    dsimp [S]
    simpa using unit_superblock_shift_zmod_p6_oeis_361883 (p := p) (b := b + v) hp hp5
  have hright_shift : S v = S 0 := by
    dsimp [S]
    simpa using unit_superblock_shift_zmod_p6_oeis_361883 (p := p) (b := v) hp hp5
  calc
    (∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * (b + v) + m) + t : ℕ) : R)) = S (b + v) := hblocks_left
    _ = S 0 := hleft_shift
    _ = S v := hright_shift.symm
    _ = ∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * v + m) + t : ℕ) : R) := hblocks_right.symm

/-- Unit-part multiplicativity modulo `p^6` when both split points are multiples of `p`. -/
lemma unitPartProd_zmod_p6_add_of_p_dvd_both_oeis_361883 {p B C : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hB : p ∣ B) (hC : p ∣ C) :
    let R := ZMod (p ^ 6)
    ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
      ((unitPartProd_oeis_361883 p B : ℕ) : R) * ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
  classical
  rcases hB with ⟨b, rfl⟩
  rcases hC with ⟨c, rfl⟩
  intro R
  let block : ℕ → R := fun q =>
    ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * q + t : ℕ) : R)
  let group : ℕ → R := fun v => ∏ m ∈ Finset.range p, block (p * v + m)
  have hunit_mul : ∀ n : ℕ,
      ((unitPartProd_oeis_361883 p (p * n) : ℕ) : R) = ∏ v ∈ Finset.range n, group v := by
    intro n
    calc
      ((unitPartProd_oeis_361883 p (p * n) : ℕ) : R)
          = ∏ q ∈ Finset.range (p * n), block q := by
              simp [unitPartProd_oeis_361883, block, Nat.cast_prod]
      _ = ∏ q ∈ Finset.range (n * p), block q := by
              rw [Nat.mul_comm]
      _ = ∏ v ∈ Finset.range n, ∏ m ∈ Finset.range p, block (p * v + m) := by
              rw [prod_range_mul_decomp_oeis_361883]
      _ = ∏ v ∈ Finset.range n, group v := by
              rfl
  have hgroup_shift : ∀ v ∈ Finset.range c, group (b + v) = group v := by
    intro v _hv
    dsimp [group, block]
    exact unit_block_group_shift_zmod_p6_oeis_361883 (p := p) (b := b) (v := v) hp hp5
  calc
    ((unitPartProd_oeis_361883 p (p * b + p * c) : ℕ) : R)
        = ((unitPartProd_oeis_361883 p (p * (b + c)) : ℕ) : R) := by
            congr 1
            ring_nf
    _ = ∏ v ∈ Finset.range (b + c), group v := hunit_mul (b + c)
    _ = (∏ v ∈ Finset.range b, group v) * ∏ v ∈ Finset.range c, group (b + v) := by
            rw [Finset.prod_range_add]
    _ = (∏ v ∈ Finset.range b, group v) * ∏ v ∈ Finset.range c, group v := by
            congr 1
            apply Finset.prod_congr rfl
            intro v hv
            exact hgroup_shift v hv
    _ = ((unitPartProd_oeis_361883 p (p * b) : ℕ) : R) *
        ((unitPartProd_oeis_361883 p (p * c) : ℕ) : R) := by
            rw [hunit_mul b, hunit_mul c]


/-- Natural representatives coprime to `p^2` are units modulo `p^7`. -/
lemma coprime_p_sq_isUnit_zmod_p7_oeis_361883 {p x : ℕ} (hp : p.Prime)
    (hx : Nat.Coprime x (p ^ 2)) : IsUnit (x : ZMod (p ^ 7)) := by
  have hxp : Nat.Coprime x p := Nat.Coprime.of_dvd_right (by exact dvd_pow_self p (by norm_num : 2 ≠ 0)) hx
  have hnot : ¬ p ∣ x := (hp.coprime_iff_not_dvd).mp hxp.symm
  exact (ZMod.isUnit_iff_coprime _ _).2 (hp.coprime_pow_of_not_dvd hnot)

/-- Reduction from `ZMod (p^7)` to `ZMod (p^2)` commutes with inverses of representatives
coprime to `p^2`. -/
lemma zmod_castHom_inv_p7_to_p2_of_coprime_oeis_361883 {p x : ℕ} (hp : p.Prime)
    (hx : Nat.Coprime x (p ^ 2)) :
    ZMod.castHom (show p ^ 2 ∣ p ^ 7 by exact pow_dvd_pow p (by norm_num : 2 ≤ 7))
      (ZMod (p ^ 2)) (((x : ℕ) : ZMod (p ^ 7))⁻¹) =
      (((x : ℕ) : ZMod (p ^ 2))⁻¹) := by
  let R := ZMod (p ^ 7)
  let S := ZMod (p ^ 2)
  let f := ZMod.castHom (show p ^ 2 ∣ p ^ 7 by exact pow_dvd_pow p (by norm_num : 2 ≤ 7)) S
  have hxp : Nat.Coprime x p := Nat.Coprime.of_dvd_right
    (by exact dvd_pow_self p (by norm_num : 2 ≠ 0)) hx
  have hnot : ¬ p ∣ x := (hp.coprime_iff_not_dvd).mp hxp.symm
  have hcopR : Nat.Coprime x (p ^ 7) := hp.coprime_pow_of_not_dvd hnot
  let uR : Rˣ := ZMod.unitOfCoprime x hcopR
  let uS : Sˣ := ZMod.unitOfCoprime x hx
  have hmapu : Units.map f.toMonoidHom uR = uS := by
    apply Units.ext
    change f (x : R) = (x : S)
    simp [f]
  have hmapinv : f ((uR⁻¹ : Rˣ) : R) = ((uS⁻¹ : Sˣ) : S) := by
    calc
      f ((uR⁻¹ : Rˣ) : R) = ((Units.map f.toMonoidHom uR)⁻¹ : Sˣ) := by
        exact (Units.coe_map_inv f.toMonoidHom uR).symm
      _ = ((uS⁻¹ : Sˣ) : S) := by rw [hmapu]
  have hinvR : ((x : R)⁻¹) = ((uR⁻¹ : Rˣ) : R) := by
    simpa [uR] using ZMod.inv_coe_unit uR
  have hinvS : ((x : S)⁻¹) = ((uS⁻¹ : Sˣ) : S) := by
    simpa [uS] using ZMod.inv_coe_unit uS
  calc
    f (((x : ℕ) : R)⁻¹) = f ((uR⁻¹ : Rˣ) : R) := by rw [hinvR]
    _ = ((uS⁻¹ : Sˣ) : S) := hmapinv
    _ = (((x : ℕ) : S)⁻¹) := by rw [hinvS]

/-- In `ZMod (p^7)`, a class reducing to zero modulo `p^2` is killed by `p^5`. -/
lemma zmod_p5_mul_eq_zero_of_castHom_p2_eq_zero_oeis_361883 {p : ℕ} (hp : p.Prime)
    (x : ZMod (p ^ 7))
    (hx : ZMod.castHom (show p ^ 2 ∣ p ^ 7 by exact pow_dvd_pow p (by norm_num : 2 ≤ 7))
        (ZMod (p ^ 2)) x = 0) :
    (p ^ 5 : ZMod (p ^ 7)) * x = 0 := by
  haveI : NeZero (p ^ 7) := ⟨pow_ne_zero 7 hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x]
  have hxval0 : ((x.val : ℕ) : ZMod (p ^ 2)) = 0 := by
    simpa [ZMod.castHom_apply] using hx
  have hxdiv : p ^ 2 ∣ x.val := (ZMod.natCast_eq_zero_iff x.val (p ^ 2)).1 hxval0
  rcases hxdiv with ⟨y, hy⟩
  rw [hy, Nat.cast_mul]
  have hzero : ((p ^ 7 : ℕ) : ZMod (p ^ 7)) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (p ^ 7) (p ^ 7)).2 (dvd_refl _)
  calc
    ((p : ZMod (p ^ 7)) ^ 5) * ((((p ^ 2 : ℕ) : ZMod (p ^ 7))) * (y : ZMod (p ^ 7)))
        = (y : ZMod (p ^ 7)) * ((p ^ 7 : ℕ) : ZMod (p ^ 7)) := by
          rw [show (((p ^ 2 : ℕ) : ZMod (p ^ 7))) = (p : ZMod (p ^ 7)) ^ 2 by rw [Nat.cast_pow]]
          ring_nf
          rw [Nat.cast_pow]
          exact mul_comm (((p : ZMod (p ^ 7)) ^ 7)) (y : ZMod (p ^ 7))
    _ = 0 := by rw [hzero, mul_zero]

/-- Unit rewrite for one factor in the `p^3`-shifted `p^2` superblock modulo `p^7`. -/
lemma superblock3_over_p2_shift_factor_eq_mul_one_add_zmod_p7_oeis_361883 {p b x : ℕ}
    (hp : p.Prime) (hx : Nat.Coprime x (p ^ 2)) :
    (((p ^ 3 * b + x : ℕ) : ZMod (p ^ 7))) =
      ((x : ℕ) : ZMod (p ^ 7)) *
        (1 + (((p ^ 3 * b : ℕ) : ZMod (p ^ 7))) * (((x : ℕ) : ZMod (p ^ 7))⁻¹)) := by
  let R := ZMod (p ^ 7)
  have hunit : IsUnit ((x : ℕ) : R) := coprime_p_sq_isUnit_zmod_p7_oeis_361883 (p := p) hp hx
  rcases hunit with ⟨u, hu⟩
  have hmul : ((x : ℕ) : R) * (((x : ℕ) : R)⁻¹) = 1 := by
    rw [← hu, ZMod.inv_coe_unit]
    exact Units.mul_inv u
  change (((p ^ 3 * b + x : ℕ) : R)) =
      ((x : ℕ) : R) * (1 + (((p ^ 3 * b : ℕ) : R)) * (((x : ℕ) : R)⁻¹))
  rw [Nat.cast_add]
  calc
    (((p ^ 3 * b : ℕ) : R) + ((x : ℕ) : R)) =
        ((x : ℕ) : R) + ((p ^ 3 * b : ℕ) : R) := by ring
    _ = ((x : ℕ) : R) * (1 + (((p ^ 3 * b : ℕ) : R)) * (((x : ℕ) : R)⁻¹)) := by
      rw [mul_add, mul_one]
      calc
        ((x : ℕ) : R) + ((p ^ 3 * b : ℕ) : R) =
            ((x : ℕ) : R) + ((p ^ 3 * b : ℕ) : R) * (((x : ℕ) : R) * (((x : ℕ) : R)⁻¹)) := by
              rw [hmul, mul_one]
        _ = ((x : ℕ) : R) + ((x : ℕ) : R) * (((p ^ 3 * b : ℕ) : R) * (((x : ℕ) : R)⁻¹)) := by
              ring

/-- The linear inverse-sum term for the `p^3` shift of a `p^2` superblock is annihilated
modulo `p^7`. -/
lemma unit_superblock3_over_p2_shift_zmod_p7_hS1_oeis_361883 {p b : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
  (((p ^ 3 * b : ℕ) : ZMod (p ^ 7))) *
    (∑ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
      (((x : ℕ) : ZMod (p ^ 7))⁻¹)) = 0 := by
  classical
  let R := ZMod (p ^ 7)
  let S := ZMod (p ^ 2)
  let s := (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2))
  let c : ℕ → ℕ := fun x => p ^ 2 - x
  let fR : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  let fS : ℕ → S := fun x => (((x : ℕ) : S)⁻¹)
  let A : R := ∑ x ∈ s, fR x
  let T : R := ∑ x ∈ s, fR x * fR (c x)
  let phi := ZMod.castHom (show p ^ 2 ∣ p ^ 7 by exact pow_dvd_pow p (by norm_num : 2 ≤ 7)) S
  have hs_mem_data {x : ℕ} (hx : x ∈ s) : x < p ^ 2 ∧ Nat.Coprime x (p ^ 2) := by
    have h := Finset.mem_filter.mp hx
    exact ⟨Finset.mem_range.mp h.1, h.2⟩
  have hpos_of_mem {x : ℕ} (hx : x ∈ s) : 0 < x := by
    have hxc : Nat.Coprime x (p ^ 2) := (hs_mem_data hx).2
    by_contra hx0
    have hxz : x = 0 := Nat.eq_zero_of_not_pos hx0
    subst hxz
    have hbad : p ^ 2 = 1 := by simpa [Nat.Coprime] using hxc
    have hp2gt : 1 < p ^ 2 := by nlinarith [hp5]
    omega
  have hc_mem {x : ℕ} (hx : x ∈ s) : c x ∈ s := by
    have hxlt : x < p ^ 2 := (hs_mem_data hx).1
    have hxc : Nat.Coprime x (p ^ 2) := (hs_mem_data hx).2
    have hxpos : 0 < x := hpos_of_mem hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · dsimp [c]
      omega
    · dsimp [c]
      exact (Nat.coprime_self_sub_left (show x ≤ p ^ 2 by omega)).2 hxc
  have hc_invol {x : ℕ} (hx : x ∈ s) : c (c x) = x := by
    have hxlt : x < p ^ 2 := (hs_mem_data hx).1
    have hxpos : 0 < x := hpos_of_mem hx
    dsimp [c]
    omega
  have hcast_sum {x : ℕ} (hx : x ∈ s) :
      ((x : R) + ((c x : ℕ) : R)) = ((p ^ 2 : ℕ) : R) := by
    have hxlt : x < p ^ 2 := (hs_mem_data hx).1
    have hnat : x + (p ^ 2 - x) = p ^ 2 := Nat.add_sub_of_le (show x ≤ p ^ 2 by omega)
    dsimp [c]
    rw [← Nat.cast_add, hnat]
  have hpair_inv {x : ℕ} (hx : x ∈ s) :
      fR x + fR (c x) = ((p ^ 2 : ℕ) : R) * fR x * fR (c x) := by
    have hxc : Nat.Coprime x (p ^ 2) := (hs_mem_data hx).2
    have hcc : Nat.Coprime (c x) (p ^ 2) := (hs_mem_data (hc_mem hx)).2
    have hxunit : IsUnit ((x : ℕ) : R) := coprime_p_sq_isUnit_zmod_p7_oeis_361883 (p := p) hp hxc
    have hcunit : IsUnit (((c x : ℕ) : R)) := coprime_p_sq_isUnit_zmod_p7_oeis_361883 (p := p) hp hcc
    rcases hxunit with ⟨ux, hux⟩
    rcases hcunit with ⟨uc, huc⟩
    have hxmul : ((x : ℕ) : R) * fR x = 1 := by
      dsimp [fR]
      rw [← hux, ZMod.inv_coe_unit]
      exact Units.mul_inv ux
    have hcmul : (((c x : ℕ) : R)) * fR (c x) = 1 := by
      dsimp [fR]
      rw [← huc, ZMod.inv_coe_unit]
      exact Units.mul_inv uc
    have hmain : (((x : ℕ) : R) + ((c x : ℕ) : R)) * fR x * fR (c x) = fR x + fR (c x) := by
      calc
        (((x : ℕ) : R) + ((c x : ℕ) : R)) * fR x * fR (c x)
            = (((x : ℕ) : R) * fR x) * fR (c x) + (((c x : ℕ) : R) * fR (c x)) * fR x := by ring
        _ = fR x + fR (c x) := by rw [hxmul, hcmul]; ring
    rw [← hmain, hcast_sum hx]
  have hA_comp : A = ∑ x ∈ s, fR (c x) := by
    dsimp [A]
    refine Finset.sum_bij (fun x _ => c x) ?_ ?_ ?_ ?_
    · intro x hx
      exact hc_mem hx
    · intro x hx y hy hxy
      have hxlt : x < p ^ 2 := (hs_mem_data hx).1
      have hylt : y < p ^ 2 := (hs_mem_data hy).1
      dsimp [c] at hxy
      omega
    · intro y hy
      refine ⟨c y, hc_mem hy, ?_⟩
      exact hc_invol hy
    · intro x hx
      rw [hc_invol hx]
  have htwoA : (2 : R) * A = ((p ^ 2 : ℕ) : R) * T := by
    calc
      (2 : R) * A = A + A := by ring
      _ = (∑ x ∈ s, fR x) + A := by rfl
      _ = (∑ x ∈ s, fR x) + (∑ x ∈ s, fR (c x)) := by rw [hA_comp]
      _ = ∑ x ∈ s, (fR x + fR (c x)) := by rw [Finset.sum_add_distrib]
      _ = ∑ x ∈ s, (((p ^ 2 : ℕ) : R) * fR x * fR (c x)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hpair_inv hx
      _ = ((p ^ 2 : ℕ) : R) * T := by
        dsimp [T]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
  have hphi_f {x : ℕ} (hxmem : x ∈ s) : phi (fR x) = fS x := by
    have hxc : Nat.Coprime x (p ^ 2) := (hs_mem_data hxmem).2
    simpa [phi, fR, fS, R, S] using
      zmod_castHom_inv_p7_to_p2_of_coprime_oeis_361883 (p := p) (x := x) hp hxc
  have hphi_T : phi T = 0 := by
    calc
      phi T = ∑ x ∈ s, fS x * fS (c x) := by
        dsimp [T]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [map_mul, hphi_f hx, hphi_f (hc_mem hx)]
      _ = ∑ x ∈ s, - (fS x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt : x < p ^ 2 := (hs_mem_data hx).1
        have hnat : x + (p ^ 2 - x) = p ^ 2 := Nat.add_sub_of_le (show x ≤ p ^ 2 by omega)
        have hsum0 : ((x : ℕ) : S) + ((c x : ℕ) : S) = 0 := by
          dsimp [c]
          rw [← Nat.cast_add, hnat]
          simp [S]
        have hc_eq_neg : ((c x : ℕ) : S) = - ((x : ℕ) : S) := by
          exact eq_neg_of_add_eq_zero_right hsum0
        have hf_neg : fS (c x) = - fS x := by
          dsimp [fS]
          rw [hc_eq_neg]
          have hxc : Nat.Coprime x (p ^ 2) := (hs_mem_data hx).2
          have hxunitS : IsUnit ((x : ℕ) : S) := by
            exact (ZMod.isUnit_iff_coprime x (p ^ 2)).2 hxc
          rcases hxunitS with ⟨u, hu⟩
          rw [← hu, ZMod.inv_coe_unit]
          change (-(u : S))⁻¹ = -↑(u⁻¹)
          rw [show -(u : S) = ((-u : Sˣ) : S) by rfl]
          rw [ZMod.inv_coe_unit]
          rfl
        rw [hf_neg]
        ring
      _ = - (∑ x ∈ s, (fS x) ^ 2) := by rw [Finset.sum_neg_distrib]
      _ = 0 := by
        dsimp [s, fS, S]
        rw [sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p 2 hp hp5, neg_zero]
  have hkill_T : (p ^ 5 : R) * T = 0 := by
    apply zmod_p5_mul_eq_zero_of_castHom_p2_eq_zero_oeis_361883 (p := p) hp
    exact hphi_T
  have htwo_goal : (2 : R) * ((((p ^ 3 * b : ℕ) : R)) * A) = 0 := by
    calc
      (2 : R) * ((((p ^ 3 * b : ℕ) : R)) * A)
          = (((p ^ 3 * b : ℕ) : R)) * ((2 : R) * A) := by ring
      _ = (((p ^ 3 * b : ℕ) : R)) * (((p ^ 2 : ℕ) : R) * T) := by rw [htwoA]
      _ = (b : R) * ((p ^ 5 : R) * T) := by
        rw [Nat.cast_mul]
        rw [show (((p ^ 3 : ℕ) : R)) = (p : R) ^ 3 by rw [Nat.cast_pow]]
        rw [show (((p ^ 2 : ℕ) : R)) = (p : R) ^ 2 by rw [Nat.cast_pow]]
        ring
      _ = 0 := by rw [hkill_T, mul_zero]
  have htwo_unit : IsUnit (2 : R) := by
    apply (ZMod.isUnit_iff_coprime 2 (p ^ 7)).2
    exact coprime_two_pow_prime_oeis_361883 (r := 7) hp hp5
  change (((p ^ 3 * b : ℕ) : R)) * A = 0
  rcases htwo_unit with ⟨u, hu⟩
  have h : (u : R) * ((((p ^ 3 * b : ℕ) : R)) * A) = 0 := by
    simpa [hu] using htwo_goal
  have h' : ((((p ^ 3 * b : ℕ) : R)) * A) * (u : R) = 0 := by
    simpa [mul_comm] using h
  exact (Units.mul_left_eq_zero u).mp h'

/-- The quadratic inverse-pair term for the `p^3` shift of a `p^2` superblock is annihilated
modulo `p^7`. -/
lemma unit_superblock3_over_p2_shift_zmod_p7_hS2_oeis_361883 {p b : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
  ((((p ^ 3 * b : ℕ) : ZMod (p ^ 7))) ^ 2) *
    (∑ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
      ∑ y ∈ ((Finset.range (p ^ 2)).filter (fun y => Nat.Coprime y (p ^ 2))).filter (fun y => y < x),
        (((y : ℕ) : ZMod (p ^ 7))⁻¹) * (((x : ℕ) : ZMod (p ^ 7))⁻¹)) = 0 := by
  classical
  let R := ZMod (p ^ 7)
  let S := ZMod (p ^ 2)
  let s := (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2))
  let fR : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  let fS : ℕ → S := fun x => (((x : ℕ) : S)⁻¹)
  let E : R := ∑ x ∈ s, ∑ y ∈ s.filter (fun y => y < x), fR y * fR x
  let D : R := ∑ x ∈ s, (fR x) ^ 2
  let A : R := ∑ x ∈ s, fR x
  let phi := ZMod.castHom (show p ^ 2 ∣ p ^ 7 by exact pow_dvd_pow p (by norm_num : 2 ≤ 7)) S
  have hphi_f (x : ℕ) (hxmem : x ∈ s) : phi (fR x) = fS x := by
    have hxc : Nat.Coprime x (p ^ 2) := (Finset.mem_filter.mp hxmem).2
    simpa [phi, fR, fS, R, S] using
      zmod_castHom_inv_p7_to_p2_of_coprime_oeis_361883 (p := p) (x := x) hp hxc
  have hphi_A : phi A = 0 := by
    calc
      phi A = ∑ x ∈ s, fS x := by
        dsimp [A]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hxmem
        simpa using hphi_f x hxmem
      _ = 0 := by
        dsimp [s, fS, S]
        exact sum_range_coprime_inv_zmod_pow_eq_zero_oeis_361883 p 2 hp hp5
  have hphi_D : phi D = 0 := by
    calc
      phi D = ∑ x ∈ s, (fS x) ^ 2 := by
        dsimp [D]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hxmem
        rw [map_pow]
        rw [hphi_f x hxmem]
      _ = 0 := by
        dsimp [s, fS, S]
        exact sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p 2 hp hp5
  have hkill_A_sq : (p ^ 5 : R) * (A ^ 2) = 0 := by
    apply zmod_p5_mul_eq_zero_of_castHom_p2_eq_zero_oeis_361883 (p := p) hp
    rw [map_pow, hphi_A, zero_pow (by norm_num : 2 ≠ 0)]
  have hkill_D : (p ^ 5 : R) * D = 0 := by
    apply zmod_p5_mul_eq_zero_of_castHom_p2_eq_zero_oeis_361883 (p := p) hp
    exact hphi_D
  have hpair_id : A ^ 2 = D + 2 * E := by
    dsimp [A, D, E, fR, s]
    exact finset_sum_sq_eq_diag_add_two_ordered_pairs_oeis_361883
      ((Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)))
      (fun x => (((x : ℕ) : R)⁻¹))
  have htwo_mul : (2 : R) * ((p ^ 5 : R) * E) = 0 := by
    have hcalc : (p ^ 5 : R) * (A ^ 2) = (p ^ 5 : R) * D + (2 : R) * ((p ^ 5 : R) * E) := by
      rw [hpair_id]
      ring
    have hsub : (p ^ 5 : R) * (A ^ 2) - (p ^ 5 : R) * D = (2 : R) * ((p ^ 5 : R) * E) := by
      rw [hcalc]
      ring
    rw [← hsub, hkill_A_sq, hkill_D]
    ring
  have htwo_unit : IsUnit (2 : R) := by
    apply (ZMod.isUnit_iff_coprime 2 (p ^ 7)).2
    exact coprime_two_pow_prime_oeis_361883 (r := 7) hp hp5
  have hkill_E : (p ^ 5 : R) * E = 0 := by
    rcases htwo_unit with ⟨u, hu⟩
    have h : (u : R) * ((p ^ 5 : R) * E) = 0 := by
      simpa [hu] using htwo_mul
    have h' : ((p ^ 5 : R) * E) * (u : R) = 0 := by
      simpa [mul_comm] using h
    exact (Units.mul_left_eq_zero u).mp h'
  change (((p ^ 3 * b : ℕ) : R) ^ 2) * E = 0
  calc
    (((p ^ 3 * b : ℕ) : R) ^ 2) * E = (b ^ 2 : R) * ((p : R) * ((p ^ 5 : R) * E)) := by
      rw [Nat.cast_mul]
      rw [show (((p ^ 3 : ℕ) : R)) = (p : R) ^ 3 by rw [Nat.cast_pow]]
      ring
    _ = 0 := by rw [hkill_E, mul_zero, mul_zero]

/-- `p^3`-shift invariance of a full `p^2` unit superblock in `ZMod (p^7)`. -/
lemma unit_superblock3_over_p2_shift_zmod_p7_oeis_361883 {p b : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
  let R := ZMod (p ^ 7)
  (∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)), ((p ^ 3 * b + x : ℕ) : R)) =
  (∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)), ((x : ℕ) : R)) := by
  classical
  let R := ZMod (p ^ 7)
  let s := (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2))
  let δ : R := ((p ^ 3 * b : ℕ) : R)
  let f : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  have hδ3 : δ ^ 3 = 0 := by
    rw [← Nat.cast_pow]
    apply (ZMod.natCast_eq_zero_iff ((p ^ 3 * b) ^ 3) (p ^ 7)).2
    refine ⟨p ^ 2 * b ^ 3, ?_⟩
    rw [mul_pow]
    ring_nf
  have hratio : (∏ x ∈ s, (1 + δ * f x)) = (1 : R) := by
    have htrunc := finset_prod_one_add_nilpotent_order3_oeis_361883 (s := s) (δ := δ) (f := f) hδ3
    rw [htrunc]
    dsimp [s, δ, f] at ⊢
    rw [unit_superblock3_over_p2_shift_zmod_p7_hS1_oeis_361883 (p := p) (b := b) hp hp5,
      unit_superblock3_over_p2_shift_zmod_p7_hS2_oeis_361883 (p := p) (b := b) hp hp5]
    simp
  change (∏ x ∈ s, ((p ^ 3 * b + x : ℕ) : R)) = (∏ x ∈ s, ((x : ℕ) : R))
  calc
    (∏ x ∈ s, ((p ^ 3 * b + x : ℕ) : R)) =
        ∏ x ∈ s, (((x : ℕ) : R) * (1 + δ * f x)) := by
          apply Finset.prod_congr rfl
          intro x hx
          have hxc : Nat.Coprime x (p ^ 2) := (Finset.mem_filter.mp hx).2
          dsimp [δ, f]
          exact superblock3_over_p2_shift_factor_eq_mul_one_add_zmod_p7_oeis_361883 (p := p) (b := b) (x := x) hp hxc
    _ = (∏ x ∈ s, ((x : ℕ) : R)) * (∏ x ∈ s, (1 + δ * f x)) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ x ∈ s, ((x : ℕ) : R)) := by
          rw [hratio, mul_one]


/-- Base-point version of the `p^3`-shifted `p^2` superblock congruence modulo `p^7`. -/
lemma unit_superblock3_over_p2_shift_base_zmod_p7_oeis_361883 {p b d : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
  let R := ZMod (p ^ 7)
  (∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
      ((p ^ 3 * b + (p ^ 2 * d + x) : ℕ) : R)) =
  (∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
      ((p ^ 2 * d + x : ℕ) : R)) := by
  classical
  let R := ZMod (p ^ 7)
  let S := ZMod (p ^ 2)
  let s := (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2))
  let δ : R := ((p ^ 3 * b : ℕ) : R)
  let a : ℕ → ℕ := fun x => p ^ 2 * d + x
  let fR : ℕ → R := fun x => (((a x : ℕ) : R)⁻¹)
  let fS : ℕ → S := fun x => (((x : ℕ) : S)⁻¹)
  have ha_coprime {x : ℕ} (hx : x ∈ s) : Nat.Coprime (a x) (p ^ 2) := by
    have hxc : Nat.Coprime x (p ^ 2) := (Finset.mem_filter.mp hx).2
    dsimp [a]
    exact (Nat.add_coprime_iff_right (show p ^ 2 ∣ p ^ 2 * d by exact dvd_mul_right _ _)).2 hxc
  let phi := ZMod.castHom (show p ^ 2 ∣ p ^ 7 by exact pow_dvd_pow p (by norm_num : 2 ≤ 7)) S
  have hphi_f {x : ℕ} (hx : x ∈ s) : phi (fR x) = fS x := by
    have hmap := zmod_castHom_inv_p7_to_p2_of_coprime_oeis_361883
      (p := p) (x := a x) hp (ha_coprime hx)
    have hcast : (((a x : ℕ) : S)) = ((x : ℕ) : S) := by
      dsimp [a, S]
      simp [Nat.cast_add, Nat.cast_mul]
    simpa [phi, fR, fS, hcast] using hmap
  have hδ3 : δ ^ 3 = 0 := by
    rw [← Nat.cast_pow]
    apply (ZMod.natCast_eq_zero_iff ((p ^ 3 * b) ^ 3) (p ^ 7)).2
    refine ⟨p ^ 2 * b ^ 3, ?_⟩
    rw [mul_pow]
    ring_nf
  let A : R := ∑ x ∈ s, fR x
  let E : R := ∑ x ∈ s, ∑ y ∈ s.filter (fun y => y < x), fR y * fR x
  let D : R := ∑ x ∈ s, (fR x) ^ 2
  have hS2 : δ ^ 2 * E = 0 := by
    have hphi_A : phi A = 0 := by
      calc
        phi A = ∑ x ∈ s, fS x := by
          dsimp [A]
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro x hx
          exact hphi_f hx
        _ = 0 := by
          dsimp [s, fS, S]
          exact sum_range_coprime_inv_zmod_pow_eq_zero_oeis_361883 p 2 hp hp5
    have hphi_D : phi D = 0 := by
      calc
        phi D = ∑ x ∈ s, (fS x) ^ 2 := by
          dsimp [D]
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro x hx
          rw [map_pow, hphi_f hx]
        _ = 0 := by
          dsimp [s, fS, S]
          exact sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p 2 hp hp5
    have hkill_A_sq : (p ^ 5 : R) * (A ^ 2) = 0 := by
      apply zmod_p5_mul_eq_zero_of_castHom_p2_eq_zero_oeis_361883 (p := p) hp
      rw [map_pow, hphi_A, zero_pow (by norm_num : 2 ≠ 0)]
    have hkill_D : (p ^ 5 : R) * D = 0 := by
      apply zmod_p5_mul_eq_zero_of_castHom_p2_eq_zero_oeis_361883 (p := p) hp
      exact hphi_D
    have hpair_id : A ^ 2 = D + 2 * E := by
      dsimp [A, D, E, fR, s]
      exact finset_sum_sq_eq_diag_add_two_ordered_pairs_oeis_361883
        ((Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)))
        (fun x => ((((p ^ 2 * d + x : ℕ) : R))⁻¹))
    have htwo_mul : (2 : R) * ((p ^ 5 : R) * E) = 0 := by
      have hcalc : (p ^ 5 : R) * (A ^ 2) = (p ^ 5 : R) * D + (2 : R) * ((p ^ 5 : R) * E) := by
        rw [hpair_id]
        ring
      have hsub : (p ^ 5 : R) * (A ^ 2) - (p ^ 5 : R) * D = (2 : R) * ((p ^ 5 : R) * E) := by
        rw [hcalc]
        ring
      rw [← hsub, hkill_A_sq, hkill_D]
      ring
    have htwo_unit : IsUnit (2 : R) := by
      apply (ZMod.isUnit_iff_coprime 2 (p ^ 7)).2
      exact coprime_two_pow_prime_oeis_361883 (r := 7) hp hp5
    have hkill_E : (p ^ 5 : R) * E = 0 := by
      rcases htwo_unit with ⟨u, hu⟩
      have h : (u : R) * ((p ^ 5 : R) * E) = 0 := by
        simpa [hu] using htwo_mul
      have h' : ((p ^ 5 : R) * E) * (u : R) = 0 := by
        simpa [mul_comm] using h
      exact (Units.mul_left_eq_zero u).mp h'
    calc
      δ ^ 2 * E = (b ^ 2 : R) * ((p : R) * ((p ^ 5 : R) * E)) := by
        dsimp [δ]
        rw [Nat.cast_mul]
        rw [show (((p ^ 3 : ℕ) : R)) = (p : R) ^ 3 by rw [Nat.cast_pow]]
        ring
      _ = 0 := by rw [hkill_E, mul_zero, mul_zero]
  have hS1 : δ * A = 0 := by
    let c : ℕ → ℕ := fun x => p ^ 2 - x
    let T : R := ∑ x ∈ s, fR x * fR (c x)
    have hs_mem_data {x : ℕ} (hx : x ∈ s) : x < p ^ 2 ∧ Nat.Coprime x (p ^ 2) := by
      have h := Finset.mem_filter.mp hx
      exact ⟨Finset.mem_range.mp h.1, h.2⟩
    have hpos_of_mem {x : ℕ} (hx : x ∈ s) : 0 < x := by
      have hxc : Nat.Coprime x (p ^ 2) := (hs_mem_data hx).2
      by_contra hx0
      have hxz : x = 0 := Nat.eq_zero_of_not_pos hx0
      subst hxz
      have hbad : p ^ 2 = 1 := by simpa [Nat.Coprime] using hxc
      have hp2gt : 1 < p ^ 2 := by nlinarith [hp5]
      omega
    have hc_mem {x : ℕ} (hx : x ∈ s) : c x ∈ s := by
      have hxlt : x < p ^ 2 := (hs_mem_data hx).1
      have hxc : Nat.Coprime x (p ^ 2) := (hs_mem_data hx).2
      have hxpos : 0 < x := hpos_of_mem hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
      · dsimp [c]
        omega
      · dsimp [c]
        exact (Nat.coprime_self_sub_left (show x ≤ p ^ 2 by omega)).2 hxc
    have hc_invol {x : ℕ} (hx : x ∈ s) : c (c x) = x := by
      have hxlt : x < p ^ 2 := (hs_mem_data hx).1
      have hxpos : 0 < x := hpos_of_mem hx
      dsimp [c]
      omega
    have hsum_pair {x : ℕ} (hx : x ∈ s) :
        ((a x : ℕ) : R) + ((a (c x) : ℕ) : R) = ((p ^ 2 * (2 * d + 1) : ℕ) : R) := by
      have hxlt : x < p ^ 2 := (hs_mem_data hx).1
      have hnat : a x + a (c x) = p ^ 2 * (2 * d + 1) := by
        dsimp [a, c]
        have hxsum : x + (p ^ 2 - x) = p ^ 2 := Nat.add_sub_of_le (show x ≤ p ^ 2 by omega)
        nlinarith [hxsum]
      rw [← Nat.cast_add, hnat]
    have hpair_inv {x : ℕ} (hx : x ∈ s) :
        fR x + fR (c x) = ((p ^ 2 * (2 * d + 1) : ℕ) : R) * fR x * fR (c x) := by
      have hxunit : IsUnit ((a x : ℕ) : R) := coprime_p_sq_isUnit_zmod_p7_oeis_361883 (p := p) hp (ha_coprime hx)
      have hcunit : IsUnit ((a (c x) : ℕ) : R) := coprime_p_sq_isUnit_zmod_p7_oeis_361883 (p := p) hp (ha_coprime (hc_mem hx))
      rcases hxunit with ⟨ux, hux⟩
      rcases hcunit with ⟨uc, huc⟩
      have hxmul : ((a x : ℕ) : R) * fR x = 1 := by
        dsimp [fR]
        rw [← hux, ZMod.inv_coe_unit]
        exact Units.mul_inv ux
      have hcmul : ((a (c x) : ℕ) : R) * fR (c x) = 1 := by
        dsimp [fR]
        rw [← huc, ZMod.inv_coe_unit]
        exact Units.mul_inv uc
      have hmain : (((a x : ℕ) : R) + ((a (c x) : ℕ) : R)) * fR x * fR (c x) = fR x + fR (c x) := by
        calc
          (((a x : ℕ) : R) + ((a (c x) : ℕ) : R)) * fR x * fR (c x)
              = (((a x : ℕ) : R) * fR x) * fR (c x) + (((a (c x) : ℕ) : R) * fR (c x)) * fR x := by ring
          _ = fR x + fR (c x) := by rw [hxmul, hcmul]; ring
      rw [← hmain, hsum_pair hx]
    have hA_comp : A = ∑ x ∈ s, fR (c x) := by
      dsimp [A]
      refine Finset.sum_bij (fun x _ => c x) ?_ ?_ ?_ ?_
      · intro x hx
        exact hc_mem hx
      · intro x hx y hy hxy
        have hxlt : x < p ^ 2 := (hs_mem_data hx).1
        have hylt : y < p ^ 2 := (hs_mem_data hy).1
        dsimp [c] at hxy
        omega
      · intro y hy
        refine ⟨c y, hc_mem hy, ?_⟩
        exact hc_invol hy
      · intro x hx
        rw [hc_invol hx]
    have htwoA : (2 : R) * A = ((p ^ 2 * (2 * d + 1) : ℕ) : R) * T := by
      calc
        (2 : R) * A = A + A := by ring
        _ = (∑ x ∈ s, fR x) + A := by rfl
        _ = (∑ x ∈ s, fR x) + (∑ x ∈ s, fR (c x)) := by rw [hA_comp]
        _ = ∑ x ∈ s, (fR x + fR (c x)) := by rw [Finset.sum_add_distrib]
        _ = ∑ x ∈ s, (((p ^ 2 * (2 * d + 1) : ℕ) : R) * fR x * fR (c x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hpair_inv hx
        _ = ((p ^ 2 * (2 * d + 1) : ℕ) : R) * T := by
          dsimp [T]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring
    have hphi_T : phi T = 0 := by
      calc
        phi T = ∑ x ∈ s, fS x * fS (c x) := by
          dsimp [T]
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro x hx
          rw [map_mul, hphi_f hx, hphi_f (hc_mem hx)]
        _ = ∑ x ∈ s, - (fS x) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxlt : x < p ^ 2 := (hs_mem_data hx).1
          have hnat : x + (p ^ 2 - x) = p ^ 2 := Nat.add_sub_of_le (show x ≤ p ^ 2 by omega)
          have hsum0 : ((x : ℕ) : S) + ((c x : ℕ) : S) = 0 := by
            dsimp [c]
            rw [← Nat.cast_add, hnat]
            simp [S]
          have hc_eq_neg : ((c x : ℕ) : S) = - ((x : ℕ) : S) := by
            exact eq_neg_of_add_eq_zero_right hsum0
          have hf_neg : fS (c x) = - fS x := by
            dsimp [fS]
            rw [hc_eq_neg]
            have hxc : Nat.Coprime x (p ^ 2) := (hs_mem_data hx).2
            have hxunitS : IsUnit ((x : ℕ) : S) := by
              exact (ZMod.isUnit_iff_coprime x (p ^ 2)).2 hxc
            rcases hxunitS with ⟨u, hu⟩
            rw [← hu, ZMod.inv_coe_unit]
            change (-(u : S))⁻¹ = -↑(u⁻¹)
            rw [show -(u : S) = ((-u : Sˣ) : S) by rfl]
            rw [ZMod.inv_coe_unit]
            rfl
          rw [hf_neg]
          ring
        _ = - (∑ x ∈ s, (fS x) ^ 2) := by rw [Finset.sum_neg_distrib]
        _ = 0 := by
          dsimp [s, fS, S]
          rw [sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p 2 hp hp5, neg_zero]
    have hkill_T : (p ^ 5 : R) * T = 0 := by
      apply zmod_p5_mul_eq_zero_of_castHom_p2_eq_zero_oeis_361883 (p := p) hp
      exact hphi_T
    have htwo_goal : (2 : R) * (δ * A) = 0 := by
      calc
        (2 : R) * (δ * A) = δ * ((2 : R) * A) := by ring
        _ = δ * (((p ^ 2 * (2 * d + 1) : ℕ) : R) * T) := by rw [htwoA]
        _ = (b * (2 * d + 1) : R) * ((p ^ 5 : R) * T) := by
          dsimp [δ]
          simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          rw [show (((p ^ 3 : ℕ) : R)) = (p : R) ^ 3 by rw [Nat.cast_pow]]
          rw [show (((p ^ 2 : ℕ) : R)) = (p : R) ^ 2 by rw [Nat.cast_pow]]
          ring
        _ = 0 := by rw [hkill_T, mul_zero]
    have htwo_unit : IsUnit (2 : R) := by
      apply (ZMod.isUnit_iff_coprime 2 (p ^ 7)).2
      exact coprime_two_pow_prime_oeis_361883 (r := 7) hp hp5
    rcases htwo_unit with ⟨u, hu⟩
    have h : (u : R) * (δ * A) = 0 := by
      simpa [hu] using htwo_goal
    have h' : (δ * A) * (u : R) = 0 := by
      simpa [mul_comm] using h
    exact (Units.mul_left_eq_zero u).mp h'
  have hratio : (∏ x ∈ s, (1 + δ * fR x)) = (1 : R) := by
    have htrunc := finset_prod_one_add_nilpotent_order3_oeis_361883 (s := s) (δ := δ) (f := fR) hδ3
    rw [htrunc]
    dsimp [A, E] at hS1 hS2
    rw [hS1, hS2]
    simp
  change (∏ x ∈ s, ((p ^ 3 * b + (p ^ 2 * d + x) : ℕ) : R)) =
      (∏ x ∈ s, ((p ^ 2 * d + x : ℕ) : R))
  calc
    (∏ x ∈ s, ((p ^ 3 * b + (p ^ 2 * d + x) : ℕ) : R)) =
        ∏ x ∈ s, (((a x : ℕ) : R) * (1 + δ * fR x)) := by
          apply Finset.prod_congr rfl
          intro x hx
          have hunit : IsUnit ((a x : ℕ) : R) := coprime_p_sq_isUnit_zmod_p7_oeis_361883 (p := p) hp (ha_coprime hx)
          rcases hunit with ⟨u, hu⟩
          have hmul : ((a x : ℕ) : R) * fR x = 1 := by
            dsimp [fR]
            rw [← hu, ZMod.inv_coe_unit]
            exact Units.mul_inv u
          dsimp [a, δ, fR]
          rw [Nat.cast_add]
          calc
            (((p ^ 3 * b : ℕ) : R) + ((p ^ 2 * d + x : ℕ) : R)) =
                ((p ^ 2 * d + x : ℕ) : R) + ((p ^ 3 * b : ℕ) : R) := by ring
            _ = ((p ^ 2 * d + x : ℕ) : R) *
                (1 + ((p ^ 3 * b : ℕ) : R) * (((p ^ 2 * d + x : ℕ) : R)⁻¹)) := by
              rw [mul_add, mul_one]
              calc
                ((p ^ 2 * d + x : ℕ) : R) + ((p ^ 3 * b : ℕ) : R) =
                    ((p ^ 2 * d + x : ℕ) : R) + ((p ^ 3 * b : ℕ) : R) *
                      (((p ^ 2 * d + x : ℕ) : R) * (((p ^ 2 * d + x : ℕ) : R)⁻¹)) := by
                        rw [hmul, mul_one]
                _ = ((p ^ 2 * d + x : ℕ) : R) + ((p ^ 2 * d + x : ℕ) : R) *
                      (((p ^ 3 * b : ℕ) : R) * (((p ^ 2 * d + x : ℕ) : R)⁻¹)) := by ring
    _ = (∏ x ∈ s, ((a x : ℕ) : R)) * (∏ x ∈ s, (1 + δ * fR x)) := by
          rw [Finset.prod_mul_distrib]
    _ = ∏ x ∈ s, ((a x : ℕ) : R) := by rw [hratio, mul_one]

/-- Rewrite the `p^2` unit superblock as `p` consecutive ordinary unit blocks. -/
lemma unit_superblock_eq_prod_blocks_zmod_p7_oeis_361883 {p d : ℕ} (hp : p.Prime) :
    let R := ZMod (p ^ 7)
    (∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
        ((p ^ 2 * d + x : ℕ) : R)) =
      ∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p ^ 2 * d + (p * m + t) : ℕ) : R) := by
  classical
  intro R
  let G : ℕ → R := fun x => ((p ^ 2 * d + x : ℕ) : R)
  have hiff : ∀ m ∈ Finset.range p, ∀ t ∈ Finset.range p,
      (Nat.Coprime (p * m + t) (p ^ 2) ↔ 0 < t) := by
    intro m _hm t ht
    have htp : t < p := Finset.mem_range.mp ht
    constructor
    · intro hcop
      by_contra ht0
      have ht_eq : t = 0 := Nat.eq_zero_of_not_pos ht0
      have hdiv : p ∣ p * m + t := by
        rw [ht_eq, add_zero]
        exact dvd_mul_right p m
      have hp_dvd_pow : p ∣ p ^ 2 := dvd_pow_self p (by decide : 2 ≠ 0)
      exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hdiv hp_dvd_pow) hcop
    · intro htpos
      have hnot : ¬ p ∣ p * m + t := by
        intro hdiv
        have hpdm : p ∣ p * m := dvd_mul_right p m
        have htdvd : p ∣ t := (Nat.dvd_add_iff_right hpdm).2 hdiv
        exact (Nat.not_dvd_of_pos_of_lt htpos htp) htdvd
      exact hp.coprime_pow_of_not_dvd hnot
  calc
    (∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)), G x)
        = ∏ x ∈ Finset.range (p ^ 2), if Nat.Coprime x (p ^ 2) then G x else 1 := by
          rw [Finset.prod_filter]
    _ = ∏ x ∈ Finset.range (p * p), if Nat.Coprime x (p ^ 2) then G x else 1 := by
          rw [show p ^ 2 = p * p by ring_nf]
    _ = ∏ m ∈ Finset.range p,
          ∏ t ∈ Finset.range p, if Nat.Coprime (p * m + t) (p ^ 2) then G (p * m + t) else 1 := by
          rw [prod_range_mul_decomp_oeis_361883]
    _ = ∏ m ∈ Finset.range p,
          ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), G (p * m + t) := by
          apply Finset.prod_congr rfl
          intro m hm
          calc
            (∏ t ∈ Finset.range p, if Nat.Coprime (p * m + t) (p ^ 2) then G (p * m + t) else 1)
                = ∏ t ∈ Finset.range p, if 0 < t then G (p * m + t) else 1 := by
                  apply Finset.prod_congr rfl
                  intro t ht
                  by_cases htpos : 0 < t
                  · have hc : Nat.Coprime (p * m + t) (p ^ 2) := (hiff m hm t ht).2 htpos
                    rw [if_pos hc, if_pos htpos]
                  · have hnc : ¬ Nat.Coprime (p * m + t) (p ^ 2) := by
                      intro hc
                      exact htpos ((hiff m hm t ht).1 hc)
                    rw [if_neg hnc, if_neg htpos]
            _ = ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), G (p * m + t) := by
                  exact (Finset.prod_filter (s := Finset.range p) (p := fun t => 0 < t)
                    (f := fun t => G (p * m + t))).symm
    _ = ∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p ^ 2 * d + (p * m + t) : ℕ) : R) := by
          rfl


/-- A group of `p` ordinary unit blocks is invariant modulo `p^7` when shifted by `p^2*b`. -/
lemma unit_block_group_shift_zmod_p7_oeis_361883 {p b v : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) :
    let R := ZMod (p ^ 7)
    (∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * (p * b + v) + m) + t : ℕ) : R)) =
      ∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * v + m) + t : ℕ) : R) := by
  classical
  intro R
  let S : ℕ → R := fun d =>
    ∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
      ((p ^ 2 * d + x : ℕ) : R)
  have hblocks_left :
      (∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * (p * b + v) + m) + t : ℕ) : R)) = S (p * b + v) := by
    calc
      (∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * (p * b + v) + m) + t : ℕ) : R))
          = ∏ m ∈ Finset.range p,
              ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
                ((p ^ 2 * (p * b + v) + (p * m + t) : ℕ) : R) := by
              apply Finset.prod_congr rfl
              intro m hm
              apply Finset.prod_congr rfl
              intro t ht
              congr 1
              ring_nf
      _ = S (p * b + v) := by
          dsimp [S]
          rw [unit_superblock_eq_prod_blocks_zmod_p7_oeis_361883 (p := p) (d := p * b + v) hp]
  have hblocks_right :
      (∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * v + m) + t : ℕ) : R)) = S v := by
    calc
      (∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * v + m) + t : ℕ) : R))
          = ∏ m ∈ Finset.range p,
              ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
                ((p ^ 2 * v + (p * m + t) : ℕ) : R) := by
              apply Finset.prod_congr rfl
              intro m hm
              apply Finset.prod_congr rfl
              intro t ht
              congr 1
              ring_nf
      _ = S v := by
          dsimp [S]
          rw [unit_superblock_eq_prod_blocks_zmod_p7_oeis_361883 (p := p) (d := v) hp]
  have hshift : S (p * b + v) = S v := by
    dsimp [S]
    calc
      (∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
          ((p ^ 2 * (p * b + v) + x : ℕ) : R))
        = ∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
          ((p ^ 3 * b + (p ^ 2 * v + x) : ℕ) : R) := by
            apply Finset.prod_congr rfl
            intro x hx
            congr 1
            ring
      _ = ∏ x ∈ (Finset.range (p ^ 2)).filter (fun x => Nat.Coprime x (p ^ 2)),
          ((p ^ 2 * v + x : ℕ) : R) := by
            exact unit_superblock3_over_p2_shift_base_zmod_p7_oeis_361883 (p := p) (b := b) (d := v) hp hp5
  calc
    (∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * (p * b + v) + m) + t : ℕ) : R)) = S (p * b + v) := hblocks_left
    _ = S v := hshift
    _ = ∏ m ∈ Finset.range p,
        ∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (p * v + m) + t : ℕ) : R) := hblocks_right.symm

/-- Unit-part multiplicativity modulo `p^7` for the `r=3` diagonal ingredient. -/
lemma unitPartProd_zmod_p7_add_of_p2_dvd_left_p_dvd_right_oeis_361883 {p B C : ℕ}
  (hp:p.Prime) (hp5:5≤p) (hB:p^2∣B) (hC:p∣C) :
  let R := ZMod (p^7)
  ((unitPartProd_oeis_361883 p (B+C):ℕ):R) =
    ((unitPartProd_oeis_361883 p B:ℕ):R) * ((unitPartProd_oeis_361883 p C:ℕ):R) := by
  classical
  rcases hB with ⟨b, rfl⟩
  rcases hC with ⟨c, rfl⟩
  intro R
  let block : ℕ → R := fun q =>
    ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * q + t : ℕ) : R)
  let group : ℕ → R := fun v => ∏ m ∈ Finset.range p, block (p * v + m)
  have hunit_mul : ∀ n : ℕ,
      ((unitPartProd_oeis_361883 p (p * n) : ℕ) : R) = ∏ v ∈ Finset.range n, group v := by
    intro n
    calc
      ((unitPartProd_oeis_361883 p (p * n) : ℕ) : R)
          = ∏ q ∈ Finset.range (p * n), block q := by
              simp [unitPartProd_oeis_361883, block, Nat.cast_prod]
      _ = ∏ q ∈ Finset.range (n * p), block q := by
              rw [Nat.mul_comm]
      _ = ∏ v ∈ Finset.range n, ∏ m ∈ Finset.range p, block (p * v + m) := by
              rw [prod_range_mul_decomp_oeis_361883]
      _ = ∏ v ∈ Finset.range n, group v := by
              rfl
  have hgroup_shift : ∀ v ∈ Finset.range c, group (p * b + v) = group v := by
    intro v _hv
    dsimp [group, block]
    exact unit_block_group_shift_zmod_p7_oeis_361883 (p := p) (b := b) (v := v) hp hp5
  calc
    ((unitPartProd_oeis_361883 p (p ^ 2 * b + p * c) : ℕ) : R)
        = ((unitPartProd_oeis_361883 p (p * (p * b + c)) : ℕ) : R) := by
            congr 1
            ring_nf
    _ = ∏ v ∈ Finset.range (p * b + c), group v := hunit_mul (p * b + c)
    _ = (∏ v ∈ Finset.range (p * b), group v) * ∏ v ∈ Finset.range c, group (p * b + v) := by
            rw [Finset.prod_range_add]
    _ = (∏ v ∈ Finset.range (p * b), group v) * ∏ v ∈ Finset.range c, group v := by
            congr 1
            apply Finset.prod_congr rfl
            intro v hv
            exact hgroup_shift v hv
    _ = ((unitPartProd_oeis_361883 p (p * (p * b)) : ℕ) : R) *
        ((unitPartProd_oeis_361883 p (p * c) : ℕ) : R) := by
            rw [hunit_mul (p * b), hunit_mul c]
    _ = ((unitPartProd_oeis_361883 p (p ^ 2 * b) : ℕ) : R) *
        ((unitPartProd_oeis_361883 p (p * c) : ℕ) : R) := by
            congr 2
            ring_nf


/-- Shifted block-product congruence modulo `p^(s+2)`: if `p^s ∣ B`, then every
nonzero-residue block at `B + u` has the same product as the block at `u`.  The
paired products differ by a multiple of `p^2 * B`, hence vanish in this modulus. -/
lemma product_block_zmod_pow_s2_shift_of_dvd_oeis_361883 {p B u s : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hB : p ^ s ∣ B) :
    let R := ZMod (p ^ (s + 2))
    (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * (B + u) + t : ℕ) : R)) =
    (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * u + t : ℕ) : R)) := by
  classical
  intro R
  have hbase : p ^ (s + 2) ∣ p ^ 2 * B := by
    have hmul : p ^ 2 * p ^ s ∣ p ^ 2 * B := Nat.mul_dvd_mul_left (p ^ 2) hB
    have hpows : p ^ 2 * p ^ s = p ^ (s + 2) := by
      rw [← pow_add]
      congr 1
      omega
    simpa [hpows, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hzero_nat : ((p ^ 2 * B : ℕ) : R) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (p ^ 2 * B) (p ^ (s + 2))).2 hbase
  have hzero : ((p : R) ^ 2 * (B : R)) = 0 := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hzero_nat
  have hpair : ∀ t ∈ Finset.Icc 1 (p / 2),
      (((p * (B + u) + t : ℕ) : R) * ((p * (B + u) + (p - t) : ℕ) : R)) =
        (((p * u + t : ℕ) : R) * ((p * u + (p - t) : ℕ) : R)) := by
    intro t ht
    have htle : t ≤ p := by
      have htle' : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
      omega
    have hcast : ((p - t : ℕ) : R) = (p : R) - t := by
      rw [Nat.cast_sub htle]
    rw [show ((p * (B + u) + (p - t) : ℕ) : R) =
        (p : R) * ((B : R) + (u : R)) + ((p - t : ℕ) : R) by simp [Nat.cast_add, Nat.cast_mul],
      show ((p * (B + u) + t : ℕ) : R) =
        (p : R) * ((B : R) + (u : R)) + (t : R) by simp [Nat.cast_add, Nat.cast_mul],
      show ((p * u + (p - t) : ℕ) : R) =
        (p : R) * (u : R) + ((p - t : ℕ) : R) by simp [Nat.cast_add, Nat.cast_mul],
      show ((p * u + t : ℕ) : R) =
        (p : R) * (u : R) + (t : R) by simp [Nat.cast_add, Nat.cast_mul],
      hcast]
    calc
      ((p : R) * ((B : R) + (u : R)) + (t : R)) *
          ((p : R) * ((B : R) + (u : R)) + ((p : R) - (t : R)))
          = ((p : R) * (u : R) + (t : R)) *
              ((p : R) * (u : R) + ((p : R) - (t : R))) +
                (p : R) ^ 2 * (B : R) * (1 + 2 * (u : R) + (B : R)) := by ring
      _ = ((p : R) * (u : R) + (t : R)) *
              ((p : R) * (u : R) + ((p : R) - (t : R))) := by
            rw [hzero]
            ring
  calc
    (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * (B + u) + t : ℕ) : R))
        = (∏ t ∈ Finset.Icc 1 (p / 2),
            (((p * (B + u) + t : ℕ) : R) * ((p * (B + u) + (p - t) : ℕ) : R))) := by
          simpa using prod_pos_eq_prod_half_pair_oeis_361883 (M := R) hp hp5
            (fun t => ((p * (B + u) + t : ℕ) : R))
    _ = (∏ t ∈ Finset.Icc 1 (p / 2),
            (((p * u + t : ℕ) : R) * ((p * u + (p - t) : ℕ) : R))) := by
          apply Finset.prod_congr rfl
          intro t ht
          exact hpair t ht
    _ = (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * u + t : ℕ) : R)) := by
          rw [prod_pos_eq_prod_half_pair_oeis_361883 (M := R) hp hp5
            (fun t => ((p * u + t : ℕ) : R))]


/-- Reduction of inverses from `ZMod (p^(s+3))` to `ZMod p` for integers prime to `p`. -/
lemma zmod_castHom_inv_pow_s3_to_p_of_not_dvd_oeis_361883 {p k s : ℕ} (hp : p.Prime)
    (hnot : ¬ p ∣ k) :
    let R := ZMod (p ^ (s + 3))
    ZMod.castHom (show p ∣ p ^ (s + 3) by exact dvd_pow_self p (by omega : s + 3 ≠ 0)) (ZMod p)
      (((k : ℕ) : R)⁻¹) = (((k : ℕ) : ZMod p)⁻¹) := by
  intro R
  let f := ZMod.castHom (show p ∣ p ^ (s + 3) by exact dvd_pow_self p (by omega : s + 3 ≠ 0)) (ZMod p)
  have hcopR : Nat.Coprime k (p ^ (s + 3)) :=
    Nat.Coprime.pow_right (s + 3) (((hp.coprime_iff_not_dvd).2 hnot).symm)
  have hcopP : Nat.Coprime k p := ((hp.coprime_iff_not_dvd).2 hnot).symm
  let uR : Rˣ := ZMod.unitOfCoprime k hcopR
  let uP : (ZMod p)ˣ := ZMod.unitOfCoprime k hcopP
  have hmapu : Units.map f.toMonoidHom uR = uP := by
    apply Units.ext
    change f (k : R) = (k : ZMod p)
    simp [f]
  have hmapinv : f ((uR⁻¹ : Rˣ) : R) = ((uP⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    calc
      f ((uR⁻¹ : Rˣ) : R) = ((Units.map f.toMonoidHom uR)⁻¹ : (ZMod p)ˣ) := by
        exact (Units.coe_map_inv f.toMonoidHom uR).symm
      _ = ((uP⁻¹ : (ZMod p)ˣ) : ZMod p) := by rw [hmapu]
  have hinvR : ((k : R)⁻¹) = ((uR⁻¹ : Rˣ) : R) := by
    simpa [uR] using ZMod.inv_coe_unit uR
  have hinvP : ((k : ZMod p)⁻¹) = ((uP⁻¹ : (ZMod p)ˣ) : ZMod p) := by
    simpa [uP] using ZMod.inv_coe_unit uP
  calc
    f (((k : ℕ) : R)⁻¹) = f ((uR⁻¹ : Rˣ) : R) := by rw [hinvR]
    _ = ((uP⁻¹ : (ZMod p)ˣ) : ZMod p) := hmapinv
    _ = (((k : ℕ) : ZMod p)⁻¹) := by rw [hinvP]

/-- In `ZMod (p^(s+3))`, if `p^s ∣ B`, then `p^2 * B` kills every class whose
reduction modulo `p` is zero. -/
lemma zmod_p_sq_mul_of_dvd_mul_eq_zero_of_castHom_p_eq_zero_oeis_361883 {p B s : ℕ}
    (hp : p.Prime) (hB : p ^ s ∣ B) (x : ZMod (p ^ (s + 3)))
    (hx : ZMod.castHom (show p ∣ p ^ (s + 3) by exact dvd_pow_self p (by omega : s + 3 ≠ 0)) (ZMod p) x = 0) :
    ((p ^ 2 * B : ℕ) : ZMod (p ^ (s + 3))) * x = 0 := by
  haveI : NeZero (p ^ (s + 3)) := ⟨pow_ne_zero (s + 3) hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x]
  have hxval0 : ((x.val : ℕ) : ZMod p) = 0 := by
    simpa [ZMod.castHom_apply] using hx
  have hxdiv : p ∣ x.val := (ZMod.natCast_eq_zero_iff x.val p).1 hxval0
  have hdiv : p ^ (s + 3) ∣ p ^ 2 * B * x.val := by
    rcases hB with ⟨b, hb⟩
    rcases hxdiv with ⟨y, hy⟩
    refine ⟨b * y, ?_⟩
    rw [hb, hy]
    calc
      p ^ 2 * (p ^ s * b) * (p * y) = (p ^ 2 * p ^ s * p) * (b * y) := by ring
      _ = (p ^ (2 + s) * p) * (b * y) := by rw [← pow_add]
      _ = (p ^ (2 + s) * p ^ 1) * (b * y) := by simp
      _ = p ^ (2 + s + 1) * (b * y) := by rw [← pow_add]
      _ = p ^ (s + 3) * (b * y) := by
        have hexp : 2 + s + 1 = s + 3 := by omega
        rw [hexp]
  have hcast : ((p ^ 2 * B * x.val : ℕ) : ZMod (p ^ (s + 3))) = 0 :=
    (ZMod.natCast_eq_zero_iff (p ^ 2 * B * x.val) (p ^ (s + 3))).2 hdiv
  simpa [Nat.cast_mul] using hcast

/-- Shifted block-product congruence modulo `p^(s+3)`: if `p^s ∣ B`, then the
positive-residue block at `B + u` has the same product as the block at `u`. -/
lemma product_block_zmod_pow_s3_shift_of_dvd_oeis_361883 {p B u s : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hB : p ^ s ∣ B) :
    let R := ZMod (p ^ (s + 3))
    (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * (B + u) + t : ℕ) : R)) =
    (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * u + t : ℕ) : R)) := by
  classical
  intro R
  let half : Finset ℕ := Finset.Icc 1 (p / 2)
  let δ : R := ((p ^ 2 * B : ℕ) : R)
  let c : R := ((1 + B + 2 * u : ℕ) : R)
  let Base : ℕ → R := fun t => ((p * u + t : ℕ) : R) * ((p * u + (p - t) : ℕ) : R)
  let phi := ZMod.castHom (show p ∣ p ^ (s + 3) by exact dvd_pow_self p (by omega : s + 3 ≠ 0)) (ZMod p)
  have hδ2 : δ ^ 2 = 0 := by
    have hmapδ : phi δ = 0 := by
      have hpdvd : p ∣ p ^ 2 * B := by
        have hp2 : p ∣ p ^ 2 := by
          simp [pow_two]
        exact dvd_mul_of_dvd_left hp2 B
      have hz : ((p ^ 2 * B : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff (p ^ 2 * B) p).2 hpdvd
      dsimp [phi, δ]
      rw [ZMod.cast_natCast (show p ∣ p ^ (s + 3) by exact dvd_pow_self p (by omega : s + 3 ≠ 0))]
      exact hz
    have hkill := zmod_p_sq_mul_of_dvd_mul_eq_zero_of_castHom_p_eq_zero_oeis_361883
      (p := p) (B := B) (s := s) hp hB δ hmapδ
    simpa [δ, pow_two] using hkill
  have hunit : ∀ t ∈ half, IsUnit (Base t) := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    have htle_half : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
    have htp : t < p := by omega
    have hptpos : 0 < p - t := by omega
    have hptlt : p - t < p := by omega
    have hnot_t : ¬ p ∣ t := Nat.not_dvd_of_pos_of_lt (by omega) htp
    have hnot_pt : ¬ p ∣ p - t := Nat.not_dvd_of_pos_of_lt hptpos hptlt
    have hnot_left : ¬ p ∣ p * u + t := by
      intro h
      have hpdu : p ∣ p * u := dvd_mul_right p u
      have htdvd : p ∣ t := (Nat.dvd_add_iff_right hpdu).2 h
      exact hnot_t htdvd
    have hnot_right : ¬ p ∣ p * u + (p - t) := by
      intro h
      have hpdu : p ∣ p * u := dvd_mul_right p u
      have hptdvd : p ∣ p - t := (Nat.dvd_add_iff_right hpdu).2 h
      exact hnot_pt hptdvd
    have hcop_left : Nat.Coprime (p * u + t) (p ^ (s + 3)) :=
      Nat.Coprime.pow_right (s + 3) (((hp.coprime_iff_not_dvd).2 hnot_left).symm)
    have hcop_right : Nat.Coprime (p * u + (p - t)) (p ^ (s + 3)) :=
      Nat.Coprime.pow_right (s + 3) (((hp.coprime_iff_not_dvd).2 hnot_right).symm)
    dsimp [Base]
    exact ((ZMod.isUnit_iff_coprime (p * u + t) (p ^ (s + 3))).2 hcop_left).mul
      ((ZMod.isUnit_iff_coprime (p * u + (p - t)) (p ^ (s + 3))).2 hcop_right)
  have hpair : ∀ t ∈ half,
      (((p * (B + u) + t : ℕ) : R) * ((p * (B + u) + (p - t) : ℕ) : R)) = Base t + δ * c := by
    intro t ht
    have htle : t ≤ p := by
      have htle' : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
      omega
    have hcast : ((p - t : ℕ) : R) = (p : R) - t := by
      rw [Nat.cast_sub htle]
    dsimp [Base, δ, c, R]
    rw [show ((p * (B + u) + (p - t) : ℕ) : ZMod (p ^ (s + 3))) =
        (p : ZMod (p ^ (s + 3))) * ((B : ZMod (p ^ (s + 3))) + (u : ZMod (p ^ (s + 3)))) + ((p - t : ℕ) : ZMod (p ^ (s + 3))) by simp [Nat.cast_add, Nat.cast_mul],
      show ((p * (B + u) + t : ℕ) : ZMod (p ^ (s + 3))) =
        (p : ZMod (p ^ (s + 3))) * ((B : ZMod (p ^ (s + 3))) + (u : ZMod (p ^ (s + 3)))) + (t : ZMod (p ^ (s + 3))) by simp [Nat.cast_add, Nat.cast_mul],
      show ((p * u + (p - t) : ℕ) : ZMod (p ^ (s + 3))) =
        (p : ZMod (p ^ (s + 3))) * (u : ZMod (p ^ (s + 3))) + ((p - t : ℕ) : ZMod (p ^ (s + 3))) by simp [Nat.cast_add, Nat.cast_mul],
      show ((p * u + t : ℕ) : ZMod (p ^ (s + 3))) =
        (p : ZMod (p ^ (s + 3))) * (u : ZMod (p ^ (s + 3))) + (t : ZMod (p ^ (s + 3))) by simp [Nat.cast_add, Nat.cast_mul],
      hcast]
    norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_pow]
    ring
  have hpoint : ∀ t ∈ half,
      (((p * (B + u) + t : ℕ) : R) * ((p * (B + u) + (p - t) : ℕ) : R)) =
        Base t * (1 + δ * (c * (Base t)⁻¹)) := by
    intro t ht
    rw [hpair t ht]
    have hmul : Base t * (Base t)⁻¹ = 1 := ZMod.mul_inv_of_unit (Base t) (hunit t ht)
    symm
    exact (calc
      Base t * (1 + δ * (c * (Base t)⁻¹)) = Base t + δ * c := by
        rw [mul_add, mul_one]
        rw [show Base t * (δ * (c * (Base t)⁻¹)) = δ * c * (Base t * (Base t)⁻¹) by ring]
        rw [hmul]
        ring)
  let inner : R := ∑ t ∈ half, c * (Base t)⁻¹
  have hmap_inner : phi inner = 0 := by
    calc
      phi inner = ∑ t ∈ half, phi (c * (Base t)⁻¹) := by simp [inner]
      _ = ∑ t ∈ half, ((1 + B + 2 * u : ℕ) : ZMod p) * ((((t * (p - t) : ℕ) : ZMod p)⁻¹)) := by
        apply Finset.sum_congr rfl
        intro t ht
        have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
        have htle_half : t ≤ p / 2 := (Finset.mem_Icc.mp ht).2
        have htp : t < p := by omega
        have hptpos : 0 < p - t := by omega
        have hptlt : p - t < p := by omega
        have hnot_t : ¬ p ∣ t := Nat.not_dvd_of_pos_of_lt (by omega) htp
        have hnot_pt : ¬ p ∣ p - t := Nat.not_dvd_of_pos_of_lt hptpos hptlt
        have hnot_left : ¬ p ∣ p * u + t := by
          intro h
          have hpdu : p ∣ p * u := dvd_mul_right p u
          have htdvd : p ∣ t := (Nat.dvd_add_iff_right hpdu).2 h
          exact hnot_t htdvd
        have hnot_right : ¬ p ∣ p * u + (p - t) := by
          intro h
          have hpdu : p ∣ p * u := dvd_mul_right p u
          have hptdvd : p ∣ p - t := (Nat.dvd_add_iff_right hpdu).2 h
          exact hnot_pt hptdvd
        have hnot_prod : ¬ p ∣ (p * u + t) * (p * u + (p - t)) := by
          intro h
          rcases hp.dvd_mul.mp h with h | h
          · exact hnot_left h
          · exact hnot_right h
        have hinvmap : phi ((Base t)⁻¹) = ((((t * (p - t) : ℕ) : ZMod p)⁻¹)) := by
          have h0 := zmod_castHom_inv_pow_s3_to_p_of_not_dvd_oeis_361883
            (p := p) (k := (p * u + t) * (p * u + (p - t))) (s := s) hp hnot_prod
          have hcast_base : (((((p * u + t) * (p * u + (p - t)) : ℕ) : R)) = Base t) := by
            dsimp [Base]
            rw [Nat.cast_mul]
          have hmodp : (((((p * u + t) * (p * u + (p - t)) : ℕ) : ZMod p)) = ((t * (p - t) : ℕ) : ZMod p)) := by
            rw [Nat.cast_mul, Nat.cast_mul]
            have hleft : ((p * u + t : ℕ) : ZMod p) = (t : ZMod p) := by simp [Nat.cast_add, Nat.cast_mul]
            have hright : ((p * u + (p - t) : ℕ) : ZMod p) = ((p - t : ℕ) : ZMod p) := by simp [Nat.cast_add, Nat.cast_mul]
            rw [hleft, hright]
          simpa [hcast_base, hmodp] using h0
        have hcmap : phi c = ((1 + B + 2 * u : ℕ) : ZMod p) := by
          dsimp [phi, c]
          exact ZMod.cast_natCast
            (show p ∣ p ^ (s + 3) by exact dvd_pow_self p (by omega : s + 3 ≠ 0)) (1 + B + 2 * u)
        calc
          phi (c * (Base t)⁻¹) = phi c * phi ((Base t)⁻¹) := by rw [map_mul]
          _ = ((1 + B + 2 * u : ℕ) : ZMod p) * ((((t * (p - t) : ℕ) : ZMod p)⁻¹)) := by rw [hcmap, hinvmap]
      _ = ((1 + B + 2 * u : ℕ) : ZMod p) *
            (∑ t ∈ half, ((((t * (p - t) : ℕ) : ZMod p)⁻¹))) := by
        rw [Finset.mul_sum]
      _ = 0 := by
        rw [zmod_half_inv_pair_sum_eq_zero_oeis_361883 (p := p) hp hp5, mul_zero]
  have hinner_zero : δ * inner = 0 := by
    have hkill := zmod_p_sq_mul_of_dvd_mul_eq_zero_of_castHom_p_eq_zero_oeis_361883
      (p := p) (B := B) (s := s) hp hB inner hmap_inner
    simpa [δ] using hkill
  have hpaired :
      (∏ t ∈ half, (((p * (B + u) + t : ℕ) : R) * ((p * (B + u) + (p - t) : ℕ) : R))) =
        (∏ t ∈ half, (((p * u + t : ℕ) : R) * ((p * u + (p - t) : ℕ) : R))) := by
    exact (calc
      (∏ t ∈ half, (((p * (B + u) + t : ℕ) : R) * ((p * (B + u) + (p - t) : ℕ) : R)))

          = ∏ t ∈ half, (Base t * (1 + δ * (c * (Base t)⁻¹))) := by
            apply Finset.prod_congr rfl
            intro t ht
            exact hpoint t ht
      _ = (∏ t ∈ half, Base t) * (∏ t ∈ half, (1 + δ * (c * (Base t)⁻¹))) := by
            rw [Finset.prod_mul_distrib]
      _ = (∏ t ∈ half, Base t) * (1 + δ * (∑ t ∈ half, c * (Base t)⁻¹)) := by
            rw [prod_one_add_square_zero_oeis_361883 half δ (fun t => c * (Base t)⁻¹) hδ2]
      _ = (∏ t ∈ half, Base t) := by
            rw [show (∑ t ∈ half, c * (Base t)⁻¹) = inner by rfl, hinner_zero, add_zero, mul_one]
      _ = (∏ t ∈ half, (((p * u + t : ℕ) : R) * ((p * u + (p - t) : ℕ) : R))) := by rfl)
  exact (calc
    (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * (B + u) + t : ℕ) : R))
        = (∏ t ∈ half,
            (((p * (B + u) + t : ℕ) : R) * ((p * (B + u) + (p - t) : ℕ) : R))) := by
          simpa [half] using prod_pos_eq_prod_half_pair_oeis_361883 (M := R) hp hp5
            (fun t => ((p * (B + u) + t : ℕ) : R))
    _ = (∏ t ∈ half,
            (((p * u + t : ℕ) : R) * ((p * u + (p - t) : ℕ) : R))) := hpaired
    _ = (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * u + t : ℕ) : R)) := by
          rw [prod_pos_eq_prod_half_pair_oeis_361883 (M := R) hp hp5
            (fun t => ((p * u + t : ℕ) : R))])

/-- If the splitting point `B` is divisible by `p^s`, the unit-part product is multiplicative
modulo `p^(s+2)` for the split `B + C`. -/
lemma unitPartProd_zmod_pow_s2_add_of_right_dvd_oeis_361883 {p B C s : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hB : p ^ s ∣ B) :
    let R := ZMod (p ^ (s + 2))
    ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
      ((unitPartProd_oeis_361883 p B : ℕ) : R) *
        ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
  classical
  intro R
  let block : ℕ → R := fun q =>
    ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * q + t : ℕ) : R)
  have hshift : ∀ u ∈ Finset.range C, block (B + u) = block u := by
    intro u _hu
    simpa [block] using product_block_zmod_pow_s2_shift_of_dvd_oeis_361883
      (p := p) (B := B) (u := u) (s := s) hp hp5 hB
  calc
    ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R)
        = ∏ q ∈ Finset.range (B + C), block q := by
          simp [unitPartProd_oeis_361883, block, Nat.cast_prod]
    _ = (∏ q ∈ Finset.range B, block q) * ∏ u ∈ Finset.range C, block (B + u) := by
          rw [Finset.prod_range_add]
    _ = (∏ q ∈ Finset.range B, block q) * ∏ u ∈ Finset.range C, block u := by
          congr 1
          apply Finset.prod_congr rfl
          intro u hu
          exact hshift u hu
    _ = ((unitPartProd_oeis_361883 p B : ℕ) : R) *
        ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
          simp [unitPartProd_oeis_361883, block, Nat.cast_prod]

/-- Each unit-part product is a unit modulo `p^(s+2)`. -/
lemma unitPartProd_zmod_pow_s2_isUnit_oeis_361883 {p N s : ℕ} (hp : p.Prime) :
    IsUnit ((unitPartProd_oeis_361883 p N : ℕ) : ZMod (p ^ (s + 2))) := by
  classical
  apply (ZMod.isUnit_iff_coprime (unitPartProd_oeis_361883 p N) (p ^ (s + 2))).2
  rw [unitPartProd_oeis_361883]
  apply Nat.Coprime.prod_left
  intro q hq
  apply Nat.Coprime.prod_left
  intro t ht
  have htpos : 0 < t := (Finset.mem_filter.mp ht).2
  have htp : t < p := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
  have hnot_t : ¬ p ∣ t := Nat.not_dvd_of_pos_of_lt htpos htp
  have hnot : ¬ p ∣ p * q + t := by
    intro hdiv
    have hpq : p ∣ p * q := dvd_mul_right p q
    have htdiv : p ∣ t := by
      simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hdiv hpq
    exact hnot_t htdiv
  have hcop_p : Nat.Coprime (p * q + t) p := ((hp.coprime_iff_not_dvd).2 hnot).symm
  exact hcop_p.pow_right (s + 2)

/-- Cancellation of unit-part factors modulo `p^(s+2)` at a split whose right index is
`p^s`-divisible. -/
lemma unitPartProd_cancel_modEq_pow_s2_of_right_dvd_oeis_361883 {p s B C X Y : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hB : p ^ s ∣ B)
    (hidentity : X * unitPartProd_oeis_361883 p B * unitPartProd_oeis_361883 p C =
      Y * unitPartProd_oeis_361883 p (B + C)) :
    X ≡ Y [MOD p ^ (s + 2)] := by
  classical
  let R := ZMod (p ^ (s + 2))
  let UB : R := (unitPartProd_oeis_361883 p B : ℕ)
  let UC : R := (unitPartProd_oeis_361883 p C : ℕ)
  let V : R := UB * UC
  have hcast := congrArg (fun n : ℕ => (n : R)) hidentity
  have hU : ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) = V := by
    simpa [R, V, UB, UC] using unitPartProd_zmod_pow_s2_add_of_right_dvd_oeis_361883
      (p := p) (B := B) (C := C) (s := s) hp hp5 hB
  have hmain : ((X : ℕ) : R) * V = ((Y : ℕ) : R) * V := by
    simpa [R, V, UB, UC, hU, Nat.cast_mul, mul_assoc] using hcast
  have hV : IsUnit V := by
    dsimp [V, UB, UC]
    exact (unitPartProd_zmod_pow_s2_isUnit_oeis_361883 (p := p) (N := B) (s := s) hp).mul
      (unitPartProd_zmod_pow_s2_isUnit_oeis_361883 (p := p) (N := C) (s := s) hp)
  have hz : ((X : ℕ) : R) = ((Y : ℕ) : R) := hV.mul_right_cancel hmain
  exact (ZMod.natCast_eq_natCast_iff _ _ (p ^ (s + 2))).1 hz


/-- The newly proved block congruence iterated over `N` blocks. -/
lemma unitPartProd_zmod_p3_eq_pow_oeis_361883 {p N : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    let R := ZMod (p ^ 3)
    ((unitPartProd_oeis_361883 p N : ℕ) : R) =
      (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((t : ℕ) : R)) ^ N := by
  classical
  intro R
  induction N with
  | zero =>
      simp [unitPartProd_oeis_361883]
  | succ N ih =>
      have hblock := product_block_zmod_p3_oeis_361883 (p := p) (q := N) hp hp5
      dsimp at hblock
      calc
        ((unitPartProd_oeis_361883 p (N + 1) : ℕ) : R)
            = ((unitPartProd_oeis_361883 p N : ℕ) : R) *
                (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * N + t : ℕ) : R)) := by
              simp [unitPartProd_oeis_361883, Finset.prod_range_succ, Nat.cast_mul]
        _ = ((unitPartProd_oeis_361883 p N : ℕ) : R) *
                (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((t : ℕ) : R)) := by
              rw [hblock]
        _ = (∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((t : ℕ) : R)) ^ (N + 1) := by
              rw [ih]
              ring

/-- Consequently the unit parts are multiplicative in `ZMod (p^3)` after splitting the number
of blocks.  This is the congruence form of `U (B+C) = U B * U C` needed in the factorial route. -/
lemma unitPartProd_zmod_p3_add_oeis_361883 {p B C : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    let R := ZMod (p ^ 3)
    ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
      ((unitPartProd_oeis_361883 p B : ℕ) : R) *
        ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
  classical
  intro R
  let W : R := ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((t : ℕ) : R)
  calc
    ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) = W ^ (B + C) := by
      simpa [W] using unitPartProd_zmod_p3_eq_pow_oeis_361883 (p := p) (N := B + C) hp hp5
    _ = W ^ B * W ^ C := by rw [pow_add]
    _ = ((unitPartProd_oeis_361883 p B : ℕ) : R) *
        ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
      rw [unitPartProd_zmod_p3_eq_pow_oeis_361883 (p := p) (N := B) hp hp5,
        unitPartProd_zmod_p3_eq_pow_oeis_361883 (p := p) (N := C) hp hp5]


/-- Each unit-part product is a unit modulo `p^3`. -/
lemma unitPartProd_zmod_p3_isUnit_oeis_361883 {p N : ℕ} (hp : p.Prime) :
    IsUnit ((unitPartProd_oeis_361883 p N : ℕ) : ZMod (p ^ 3)) := by
  classical
  apply (ZMod.isUnit_iff_coprime (unitPartProd_oeis_361883 p N) (p ^ 3)).2
  rw [unitPartProd_oeis_361883]
  apply Nat.Coprime.prod_left
  intro q hq
  apply Nat.Coprime.prod_left
  intro t ht
  have htpos : 0 < t := (Finset.mem_filter.mp ht).2
  have htp : t < p := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
  have hnot_t : ¬ p ∣ t := Nat.not_dvd_of_pos_of_lt htpos htp
  have hnot : ¬ p ∣ p * q + t := by
    intro hdiv
    have hpq : p ∣ p * q := dvd_mul_right p q
    have htdiv : p ∣ t := by
      simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hdiv hpq
    exact hnot_t htdiv
  have hcop_p : Nat.Coprime (p * q + t) p := ((hp.coprime_iff_not_dvd).2 hnot).symm
  exact hcop_p.pow_right 3


/-- The rising factorial block from `p*N+1` through `p*N+p` splits into the final
multiple of `p` and the nonzero residues in the block. -/
lemma ascFactorial_block_unitPart_oeis_361883 (p N : ℕ) (hp : 0 < p) :
    (p * N + 1).ascFactorial p =
      p * (N + 1) * ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), (p * N + t) := by
  rw [Nat.ascFactorial_eq_prod_range]
  have hfilter : (Finset.range p).filter (fun t => 0 < t) = Finset.Ico 1 p := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  calc
    (∏ i ∈ range p, (p * N + 1 + i)) = ∏ i ∈ range p, (p * N + (1 + i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      omega
    _ = ∏ t ∈ Finset.Ico 1 (p + 1), (p * N + t) := by
      rw [Finset.prod_Ico_eq_prod_range]
      simp
    _ = (∏ t ∈ Finset.Ico 1 p, (p * N + t)) * (p * N + p) := by
      rw [Finset.prod_Ico_succ_top]
      exact hp
    _ = p * (N + 1) * ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), (p * N + t) := by
      rw [hfilter]
      ring

/-- Exact factorial decomposition into the powers of `p`, the smaller factorial, and the
product of non-`p`-divisible block factors.  The positivity assumption is necessary: the
corresponding statement without `0 < p` is false for `p = 0`, `N = 1`. -/
lemma factorial_unitPartProd_decomp_pos_oeis_361883 (p N : ℕ) (hp : 0 < p) :
    (p * N)! = p ^ N * N ! * unitPartProd_oeis_361883 p N := by
  induction N with
  | zero =>
      simp [unitPartProd_oeis_361883]
  | succ N ih =>
      have hfac := Nat.factorial_mul_ascFactorial (p * N) p
      have hblock := ascFactorial_block_unitPart_oeis_361883 p N hp
      have hsucc : p * (N + 1) = p * N + p := by ring
      calc
        (p * (N + 1))! = (p * N + p)! := by rw [hsucc]
        _ = (p * N)! * (p * N + 1).ascFactorial p := by rw [hfac]
        _ = (p ^ N * N ! * unitPartProd_oeis_361883 p N) *
              (p * (N + 1) * ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), (p * N + t)) := by
            rw [ih, hblock]
        _ = p ^ (N + 1) * (N + 1)! * unitPartProd_oeis_361883 p (N + 1) := by
            simp [unitPartProd_oeis_361883, Finset.prod_range_succ, Nat.factorial_succ, pow_succ]
            ring

/-- If the exact factorial/unit-part identity has been established, the block-product congruence
and unit cancellation give the desired `p^3` binomial congruence.  This packages the final
ZMod-cancellation step of the suggested route. -/
lemma choose_mul_mul_modEq_mod_p3_of_unitPart_identity_oeis_361883 {p B C : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hidentity : Nat.choose (p * (B + C)) (p * B) * unitPartProd_oeis_361883 p B *
        unitPartProd_oeis_361883 p C =
      Nat.choose (B + C) B * unitPartProd_oeis_361883 p (B + C)) :
    Nat.choose (p * (B + C)) (p * B) ≡ Nat.choose (B + C) B [MOD p ^ 3] := by
  classical
  let R := ZMod (p ^ 3)
  let UB : R := (unitPartProd_oeis_361883 p B : ℕ)
  let UC : R := (unitPartProd_oeis_361883 p C : ℕ)
  let V : R := UB * UC
  have hcast := congrArg (fun n : ℕ => (n : R)) hidentity
  have hU : ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) = V := by
    simpa [R, V, UB, UC] using unitPartProd_zmod_p3_add_oeis_361883 (p := p) (B := B) (C := C) hp hp5
  have hmain : ((Nat.choose (p * (B + C)) (p * B) : ℕ) : R) * V =
      ((Nat.choose (B + C) B : ℕ) : R) * V := by
    simpa [R, V, UB, UC, hU, Nat.cast_mul, mul_assoc] using hcast
  have hV : IsUnit V := by
    dsimp [V, UB, UC]
    exact (unitPartProd_zmod_p3_isUnit_oeis_361883 (p := p) (N := B) hp).mul
      (unitPartProd_zmod_p3_isUnit_oeis_361883 (p := p) (N := C) hp)
  have hz : ((Nat.choose (p * (B + C)) (p * B) : ℕ) : R) =
      ((Nat.choose (B + C) B : ℕ) : R) := hV.mul_right_cancel hmain
  exact (ZMod.natCast_eq_natCast_iff _ _ (p ^ 3)).1 hz


/-- The exact algebraic cancellation reducing the binomial congruence to the factorial
block decomposition.  The remaining missing ingredient for the full route is the exact formula
`(p*N)! = p^N * N! * U N`. -/
lemma choose_unitPart_identity_of_factorial_decomp_oeis_361883 {p B C : ℕ} (hp : p.Prime)
    (hfac : ∀ N : ℕ, (p * N)! = p ^ N * N ! * unitPartProd_oeis_361883 p N) :
    Nat.choose (p * (B + C)) (p * B) * unitPartProd_oeis_361883 p B *
        unitPartProd_oeis_361883 p C =
      Nat.choose (B + C) B * unitPartProd_oeis_361883 p (B + C) := by
  let UB := unitPartProd_oeis_361883 p B
  let UC := unitPartProd_oeis_361883 p C
  let UA := unitPartProd_oeis_361883 p (B + C)
  let choosep := Nat.choose (p * (B + C)) (p * B)
  let chooseA := Nat.choose (B + C) B
  have hsub : p * (B + C) - p * B = p * C := by
    calc
      p * (B + C) - p * B = (p * B + p * C) - p * B := by ring_nf
      _ = p * C := Nat.add_sub_cancel_left (p * B) (p * C)
  have hpchoose : choosep * (p * B)! * (p * C)! = (p * (B + C))! := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (n := p * (B + C)) (k := p * B) (Nat.mul_le_mul_left p (Nat.le_add_right B C))
    simpa [choosep, hsub] using h
  have hsmall : chooseA * (B !) * (C !) = (B + C)! := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (n := B + C) (k := B) (Nat.le_add_right B C)
    simpa [chooseA] using h
  have hpchoose' : choosep * (p ^ B * (B !) * UB) * (p ^ C * (C !) * UC) =
      p ^ (B + C) * (B + C)! * UA := by
    rw [hfac B, hfac C, hfac (B + C)] at hpchoose
    simpa [UB, UC, UA] using hpchoose
  let K := p ^ (B + C) * (B !) * (C !)
  have hKpos : 0 < K := by
    dsimp [K]
    exact Nat.mul_pos (Nat.mul_pos (pow_pos hp.pos (B + C)) (factorial_pos B)) (factorial_pos C)
  apply Nat.eq_of_mul_eq_mul_left hKpos
  calc
    K * (choosep * UB * UC)
        = choosep * (p ^ B * B ! * UB) * (p ^ C * C ! * UC) := by
          dsimp [K]
          rw [pow_add]
          ring
    _ = p ^ (B + C) * (B + C)! * UA := hpchoose'
    _ = K * (chooseA * UA) := by
          dsimp [K]
          rw [← hsmall]
          ring

/-- Conditional base binomial congruence: with the exact factorial block decomposition in hand,
the proved product-block congruence already gives Jacobsthal--Kazandzidis modulo `p^3`. -/
lemma choose_mul_mul_modEq_mod_p3_of_factorial_decomp_oeis_361883 {p B C : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hfac : ∀ N : ℕ, (p * N)! = p ^ N * N ! * unitPartProd_oeis_361883 p N) :
    Nat.choose (p * (B + C)) (p * B) ≡ Nat.choose (B + C) B [MOD p ^ 3] := by
  exact choose_mul_mul_modEq_mod_p3_of_unitPart_identity_oeis_361883 (p := p) (B := B) (C := C) hp hp5
    (choose_unitPart_identity_of_factorial_decomp_oeis_361883 (p := p) (B := B) (C := C) hp hfac)






/-- Unconditional Jacobsthal--Kazandzidis congruence modulo `p^3` for primes `p ≥ 5`, obtained
from the exact factorial block decomposition. -/
lemma choose_mul_mul_modEq_mod_p3_oeis_361883 {p A B : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    Nat.choose (p * A) (p * B) ≡ Nat.choose A B [MOD p ^ 3] := by
  by_cases hBA : B ≤ A
  · let C := A - B
    have hA : A = B + C := by
      dsimp [C]
      omega
    have hfac : ∀ N : ℕ, (p * N)! = p ^ N * N ! * unitPartProd_oeis_361883 p N := by
      intro N
      exact factorial_unitPartProd_decomp_pos_oeis_361883 p N hp.pos
    have h := choose_mul_mul_modEq_mod_p3_of_factorial_decomp_oeis_361883
      (p := p) (B := B) (C := C) hp hp5 hfac
    rw [hA]
    exact h
  · have hlt : A < B := Nat.lt_of_not_ge hBA
    have hplt : p * A < p * B := Nat.mul_lt_mul_of_pos_left hlt hp.pos
    have hpchoose : Nat.choose (p * A) (p * B) = 0 := Nat.choose_eq_zero_of_lt hplt
    have hchoose : Nat.choose A B = 0 := Nat.choose_eq_zero_of_lt hlt
    rw [hpchoose, hchoose]


/-- Jacobsthal--Kazandzidis-type central binomial congruence with precision depending on the
right index: if `p^s ∣ B`, then `choose (p*A) (p*B)` is congruent to `choose A B`
modulo `p^(s+2)` for primes `p ≥ 5`. -/
lemma choose_mul_mul_modEq_of_right_dvd_oeis_361883 {p A B s : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hB : p ^ s ∣ B) :
    Nat.choose (p * A) (p * B) ≡ Nat.choose A B [MOD p ^ (s + 2)] := by
  by_cases hBA : B ≤ A
  · let C := A - B
    have hA : A = B + C := by
      dsimp [C]
      omega
    have hfac : ∀ N : ℕ, (p * N)! = p ^ N * N ! * unitPartProd_oeis_361883 p N := by
      intro N
      exact factorial_unitPartProd_decomp_pos_oeis_361883 p N hp.pos
    have hidentity := choose_unitPart_identity_of_factorial_decomp_oeis_361883
      (p := p) (B := B) (C := C) hp hfac
    have hcong := unitPartProd_cancel_modEq_pow_s2_of_right_dvd_oeis_361883
      (p := p) (s := s) (B := B) (C := C)
      (X := Nat.choose (p * (B + C)) (p * B)) (Y := Nat.choose (B + C) B)
      hp hp5 hB hidentity
    rw [hA]
    exact hcong
  · have hlt : A < B := Nat.lt_of_not_ge hBA
    have hplt : p * A < p * B := Nat.mul_lt_mul_of_pos_left hlt hp.pos
    have hpchoose : Nat.choose (p * A) (p * B) = 0 := Nat.choose_eq_zero_of_lt hplt
    have hchoose : Nat.choose A B = 0 := Nat.choose_eq_zero_of_lt hlt
    rw [hpchoose, hchoose]


/-- Iterating a conditional `p^(s+3)` shifted-block congruence gives the corresponding
unit-part multiplicativity.  Thus the missing local ingredient can be supplied block-by-block. -/
lemma unitPartProd_zmod_pow_s3_add_of_shift_oeis_361883 {p B C s : ℕ}
    (hshift : ∀ u ∈ Finset.range C, let R := ZMod (p ^ (s + 3))
      (∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (B + u) + t : ℕ) : R)) =
        (∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * u + t : ℕ) : R))) :
    let R := ZMod (p ^ (s + 3))
    ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
      ((unitPartProd_oeis_361883 p B : ℕ) : R) *
        ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
  classical
  intro R
  let block : ℕ → R := fun q =>
    ∏ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * q + t : ℕ) : R)
  have hshift' : ∀ u ∈ Finset.range C, block (B + u) = block u := by
    intro u hu
    simpa [block] using hshift u hu
  calc
    ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R)
        = ∏ q ∈ Finset.range (B + C), block q := by
          simp [unitPartProd_oeis_361883, block, Nat.cast_prod]
    _ = (∏ q ∈ Finset.range B, block q) * ∏ u ∈ Finset.range C, block (B + u) := by
          rw [Finset.prod_range_add]
    _ = (∏ q ∈ Finset.range B, block q) * ∏ u ∈ Finset.range C, block u := by
          congr 1
          apply Finset.prod_congr rfl
          intro u hu
          exact hshift' u hu
    _ = ((unitPartProd_oeis_361883 p B : ℕ) : R) *
        ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
          simp [unitPartProd_oeis_361883, block, Nat.cast_prod]


/-- A low-valuation instance of the requested split-precision unit-part multiplicativity.

This packages the already proved one-sided `p^(s+3)` block-shift result together with the
special grouped-block congruences `p^6` (`s=t=1`), `p^7` (`{s,t}={1,2}`), and `p^9`
(`s=t=2`).  It is the diagonal-sufficient wrapper for all split valuations up to two. -/
lemma unitPartProd_zmod_pow_split_add_of_dvd_oeis_361883_low {p B C s t : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hB : p ^ s ∣ B) (hC : p ^ t ∣ C) (hs : s ≤ 2) (ht : t ≤ 2) :
    let R := ZMod (p ^ (s + t + Nat.min s t + 3))
    ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
      ((unitPartProd_oeis_361883 p B : ℕ) : R) *
        ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
  interval_cases s <;> interval_cases t
  · simpa using unitPartProd_zmod_p3_add_oeis_361883 (p := p) (B := B) (C := C) hp hp5
  · have hU := unitPartProd_zmod_pow_s3_add_of_shift_oeis_361883
      (p := p) (B := C) (C := B) (s := 1) (by
        intro u _hu
        exact product_block_zmod_pow_s3_shift_of_dvd_oeis_361883
          (p := p) (B := C) (u := u) (s := 1) hp hp5 hC)
    simpa [Nat.add_comm] using hU.trans (mul_comm _ _)
  · have hU := unitPartProd_zmod_pow_s3_add_of_shift_oeis_361883
      (p := p) (B := C) (C := B) (s := 2) (by
        intro u _hu
        exact product_block_zmod_pow_s3_shift_of_dvd_oeis_361883
          (p := p) (B := C) (u := u) (s := 2) hp hp5 hC)
    simpa [Nat.add_comm] using hU.trans (mul_comm _ _)
  · have hU := unitPartProd_zmod_pow_s3_add_of_shift_oeis_361883
      (p := p) (B := B) (C := C) (s := 1) (by
        intro u _hu
        exact product_block_zmod_pow_s3_shift_of_dvd_oeis_361883
          (p := p) (B := B) (u := u) (s := 1) hp hp5 hB)
    simpa using hU
  · have hB1 : p ∣ B := by simpa using hB
    have hC1 : p ∣ C := by simpa using hC
    simpa using unitPartProd_zmod_p6_add_of_p_dvd_both_oeis_361883
      (p := p) (B := B) (C := C) hp hp5 hB1 hC1
  · have hB1 : p ∣ B := by simpa using hB
    have hU := unitPartProd_zmod_p7_add_of_p2_dvd_left_p_dvd_right_oeis_361883
      (p := p) (B := C) (C := B) hp hp5 hC hB1
    simpa [Nat.add_comm] using hU.trans (mul_comm _ _)
  · have hU := unitPartProd_zmod_pow_s3_add_of_shift_oeis_361883
      (p := p) (B := B) (C := C) (s := 2) (by
        intro u _hu
        exact product_block_zmod_pow_s3_shift_of_dvd_oeis_361883
          (p := p) (B := B) (u := u) (s := 2) hp hp5 hB)
    simpa using hU
  · have hC1 : p ∣ C := by simpa using hC
    simpa using unitPartProd_zmod_p7_add_of_p2_dvd_left_p_dvd_right_oeis_361883
      (p := p) (B := B) (C := C) hp hp5 hB hC1
  · simpa using unitPartProd_zmod_p9_add_of_p2_dvd_both_oeis_361883
      (p := p) (B := B) (C := C) hp hp5 hB hC


/-- Unit-part cancellation modulo `p^(s+3)`, conditional on the missing strengthened
unit-part multiplicativity.  This packages the exact final ZMod cancellation needed to upgrade
`choose_mul_mul_modEq_of_right_dvd_oeis_361883` by one power of `p`. -/
lemma unitPartProd_cancel_modEq_pow_s3_of_add_congr_oeis_361883 {p s B C X Y : ℕ}
    (hp : p.Prime)
    (hU : let R := ZMod (p ^ (s + 3))
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R))
    (hidentity : X * unitPartProd_oeis_361883 p B * unitPartProd_oeis_361883 p C =
      Y * unitPartProd_oeis_361883 p (B + C)) :
    X ≡ Y [MOD p ^ (s + 3)] := by
  classical
  let R := ZMod (p ^ (s + 3))
  let UB : R := (unitPartProd_oeis_361883 p B : ℕ)
  let UC : R := (unitPartProd_oeis_361883 p C : ℕ)
  let V : R := UB * UC
  have hcast := congrArg (fun n : ℕ => (n : R)) hidentity
  have hU' : ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) = V := by
    simpa [R, V, UB, UC] using hU
  have hmain : ((X : ℕ) : R) * V = ((Y : ℕ) : R) * V := by
    simpa [R, V, UB, UC, hU', Nat.cast_mul, mul_assoc] using hcast
  have hV : IsUnit V := by
    dsimp [V, UB, UC]
    have hBunit : IsUnit ((unitPartProd_oeis_361883 p B : ℕ) : ZMod (p ^ (s + 3))) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (unitPartProd_zmod_pow_s2_isUnit_oeis_361883 (p := p) (N := B) (s := s + 1) hp)
    have hCunit : IsUnit ((unitPartProd_oeis_361883 p C : ℕ) : ZMod (p ^ (s + 3))) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (unitPartProd_zmod_pow_s2_isUnit_oeis_361883 (p := p) (N := C) (s := s + 1) hp)
    exact hBunit.mul hCunit
  have hz : ((X : ℕ) : R) = ((Y : ℕ) : R) := hV.mul_right_cancel hmain
  exact (ZMod.natCast_eq_natCast_iff _ _ (p ^ (s + 3))).1 hz

/-- Conditional strengthened Jacobsthal--Kazandzidis congruence.  The only remaining hypothesis
is precisely the strengthened unit-part multiplicativity modulo `p^(s+3)` for all splits with
fixed right index `B`.  A proof of this hypothesis would immediately yield the requested
unconditional lemma. -/
lemma choose_mul_mul_modEq_of_right_dvd_pow_s3_of_unitPartProd_add_oeis_361883 {p A B s : ℕ}
    (hp : p.Prime)
    (hU : ∀ C : ℕ, let R := ZMod (p ^ (s + 3))
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R)) :
    Nat.choose (p * A) (p * B) ≡ Nat.choose A B [MOD p ^ (s + 3)] := by
  by_cases hBA : B ≤ A
  · let C := A - B
    have hA : A = B + C := by
      dsimp [C]
      omega
    have hfac : ∀ N : ℕ, (p * N)! = p ^ N * N ! * unitPartProd_oeis_361883 p N := by
      intro N
      exact factorial_unitPartProd_decomp_pos_oeis_361883 p N hp.pos
    have hidentity := choose_unitPart_identity_of_factorial_decomp_oeis_361883
      (p := p) (B := B) (C := C) hp hfac
    have hcong := unitPartProd_cancel_modEq_pow_s3_of_add_congr_oeis_361883
      (p := p) (s := s) (B := B) (C := C)
      (X := Nat.choose (p * (B + C)) (p * B)) (Y := Nat.choose (B + C) B)
      hp (hU C) hidentity
    rw [hA]
    exact hcong
  · have hlt : A < B := Nat.lt_of_not_ge hBA
    have hplt : p * A < p * B := Nat.mul_lt_mul_of_pos_left hlt hp.pos
    have hpchoose : Nat.choose (p * A) (p * B) = 0 := Nat.choose_eq_zero_of_lt hplt
    have hchoose : Nat.choose A B = 0 := Nat.choose_eq_zero_of_lt hlt
    rw [hpchoose, hchoose]

/-- Conditional strengthened binomial congruence stated in terms of the missing local shifted-block
congruence modulo `p^(s+3)`.  This is a direct formal reduction from the requested theorem to the
block-product statement suggested in the prompt. -/
lemma choose_mul_mul_modEq_of_right_dvd_pow_s3_of_block_shift_oeis_361883 {p A B s : ℕ}
    (hp : p.Prime) (_hp5 : 5 ≤ p) (_hB : p ^ s ∣ B)
    (hshift : ∀ C u, u ∈ Finset.range C → let R := ZMod (p ^ (s + 3))
      (∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * (B + u) + t : ℕ) : R)) =
        (∏ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((p * u + t : ℕ) : R))) :
    Nat.choose (p * A) (p * B) ≡ Nat.choose A B [MOD p ^ (s + 3)] := by
  refine choose_mul_mul_modEq_of_right_dvd_pow_s3_of_unitPartProd_add_oeis_361883
    (p := p) (A := A) (B := B) (s := s) hp ?_
  intro C
  exact unitPartProd_zmod_pow_s3_add_of_shift_oeis_361883 (p := p) (B := B) (C := C) (s := s)
    (by
      intro u hu
      exact hshift C u hu)


/-- The requested `p^(s+3)` strengthening in the base case `s = 0`; this is exactly the already
proved modulo-`p^3` Jacobsthal--Kazandzidis congruence. -/
lemma choose_mul_mul_modEq_of_right_dvd_pow_s3_s_zero_oeis_361883 {p A B : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (_hB : p ^ 0 ∣ B) :
    Nat.choose (p * A) (p * B) ≡ Nat.choose A B [MOD p ^ (0 + 3)] := by
  simpa using choose_mul_mul_modEq_mod_p3_oeis_361883 (p := p) (A := A) (B := B) hp hp5


/-- Unconditional strengthened Jacobsthal--Kazandzidis congruence with precision depending on
the right index, obtained from the local shifted-block congruence modulo `p^(s+3)`. -/
lemma choose_mul_mul_modEq_of_right_dvd_pow_s3_oeis_361883 {p A B s : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hB : p ^ s ∣ B) :
    Nat.choose (p * A) (p * B) ≡ Nat.choose A B [MOD p ^ (s + 3)] := by
  refine choose_mul_mul_modEq_of_right_dvd_pow_s3_of_block_shift_oeis_361883
    (p := p) (A := A) (B := B) (s := s) hp hp5 hB ?_
  intro C u _hu
  exact product_block_zmod_pow_s3_shift_of_dvd_oeis_361883
    (p := p) (B := B) (u := u) (s := s) hp hp5 hB



/-- General unit diagonal summand congruence obtained by applying the strengthened
Jacobshtal--Kazandzidis congruence to the central binomial coefficient. -/
lemma T_diag_unit_modEq_general_oeis_361883 {p M r j : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hr : 0 < r) (hMpos : 0 < M) (hMdiv : p ^ (r - 1) ∣ M)
    (hpunit : ¬ p ∣ M + j) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ (3 * r)] := by
  have hp : p.Prime := Fact.out
  have hchoose : Nat.choose (p * (M + j)) (p * M) ≡ Nat.choose (M + j) M
      [MOD p ^ ((r - 1) + 3)] := by
    exact choose_mul_mul_modEq_of_right_dvd_pow_s3_oeis_361883
      (p := p) (A := M + j) (B := M) (s := r - 1) hp hp5 hMdiv
  have hcube : Nat.choose (p * (M + j)) (p * M) ^ 3 ≡
      Nat.choose (M + j) M ^ 3 [MOD p ^ (r + 2)] := by
    have hpow := hchoose.pow 3
    have hexp : (r - 1) + 3 = r + 2 := by omega
    simpa [hexp] using hpow
  exact T_diag_unit_modEq_of_choose_cube_modEq_oeis_361883
    (p := p) (M := M) (r := r) (j := j) hr hMpos hMdiv hpunit hcube


/-- In the complementary diagonal case, once `r > 1`, the hypothesis
`p^(r-1) ∣ M` already makes `M` a multiple of `p`; hence `p ∣ M+j` forces
`p ∣ j`.  This isolates the extra divisibility available away from the base
level `r = 1`. -/
lemma dvd_j_of_nonunit_diag_of_r_gt_one_oeis_361883 {p M r j : ℕ} [Fact p.Prime]
    (hrgt : 1 < r) (hMdiv : p ^ (r - 1) ∣ M) (hpdiv : p ∣ M + j) :
    p ∣ j := by
  have hpred_eq : r - 1 = (r - 2) + 1 := by omega
  have hp_dvd_pow : p ∣ p ^ (r - 1) := by
    rw [hpred_eq, pow_succ]
    exact dvd_mul_left p (p ^ (r - 2))
  have hpM : p ∣ M := hp_dvd_pow.trans hMdiv
  rcases hpdiv with ⟨a, ha⟩
  rcases hpM with ⟨b, hb⟩
  have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
  have hba : b ≤ a := by nlinarith
  refine ⟨a - b, ?_⟩
  calc
    j = M + j - M := by omega
    _ = p * a - p * b := by rw [ha, hb]
    _ = p * (a - b) := by rw [Nat.mul_sub_left_distrib]


/-- Unit-part factors are units modulo an arbitrary positive power of `p`.  This is the
cancellation fact needed for any attempted split-valuation strengthening. -/
lemma unitPartProd_zmod_pow_isUnit_oeis_361883 {p N e : ℕ} (hp : p.Prime) :
    IsUnit ((unitPartProd_oeis_361883 p N : ℕ) : ZMod (p ^ e)) := by
  classical
  apply (ZMod.isUnit_iff_coprime (unitPartProd_oeis_361883 p N) (p ^ e)).2
  rw [unitPartProd_oeis_361883]
  apply Nat.Coprime.prod_left
  intro q hq
  apply Nat.Coprime.prod_left
  intro t ht
  have htpos : 0 < t := (Finset.mem_filter.mp ht).2
  have htp : t < p := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
  have hnot_t : ¬ p ∣ t := Nat.not_dvd_of_pos_of_lt htpos htp
  have hnot : ¬ p ∣ p * q + t := by
    intro hdiv
    have hpq : p ∣ p * q := dvd_mul_right p q
    have htdiv : p ∣ t := by
      simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hdiv hpq
    exact hnot_t htdiv
  have hcop_p : Nat.Coprime (p * q + t) p := ((hp.coprime_iff_not_dvd).2 hnot).symm
  exact hcop_p.pow_right e

/-- Full split-valuation binomial congruence reduced to the corresponding full unit-part
multiplicativity.  This packages the exact factorial identity and the final `ZMod` cancellation
for the proposed modulus `p^(s+t+3)`. -/
lemma choose_mul_mul_modEq_of_split_dvd_pow_of_unitPartProd_add_oeis_361883 {p B C s t : ℕ}
    (hp : p.Prime)
    (hU : let R := ZMod (p ^ (s + t + 3))
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R)) :
    Nat.choose (p * (B + C)) (p * B) ≡ Nat.choose (B + C) B [MOD p ^ (s + t + 3)] := by
  classical
  let R := ZMod (p ^ (s + t + 3))
  let UB : R := (unitPartProd_oeis_361883 p B : ℕ)
  let UC : R := (unitPartProd_oeis_361883 p C : ℕ)
  let V : R := UB * UC
  have hfac : ∀ N : ℕ, (p * N)! = p ^ N * N ! * unitPartProd_oeis_361883 p N := by
    intro N
    exact factorial_unitPartProd_decomp_pos_oeis_361883 p N hp.pos
  have hidentity := choose_unitPart_identity_of_factorial_decomp_oeis_361883
    (p := p) (B := B) (C := C) hp hfac
  have hcast := congrArg (fun n : ℕ => (n : R)) hidentity
  have hU' : ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) = V := by
    simpa [R, V, UB, UC] using hU
  have hmain : ((Nat.choose (p * (B + C)) (p * B) : ℕ) : R) * V =
      ((Nat.choose (B + C) B : ℕ) : R) * V := by
    simpa [R, V, UB, UC, hU', Nat.cast_mul, mul_assoc] using hcast
  have hV : IsUnit V := by
    dsimp [V, UB, UC]
    exact (unitPartProd_zmod_pow_isUnit_oeis_361883 (p := p) (N := B) (e := s + t + 3) hp).mul
      (unitPartProd_zmod_pow_isUnit_oeis_361883 (p := p) (N := C) (e := s + t + 3) hp)
  have hz : ((Nat.choose (p * (B + C)) (p * B) : ℕ) : R) =
      ((Nat.choose (B + C) B : ℕ) : R) := hV.mul_right_cancel hmain
  exact (ZMod.natCast_eq_natCast_iff _ _ (p ^ (s + t + 3))).1 hz


/-- Split binomial congruence modulo `p^6` when both split parts are divisible by `p`. -/
lemma choose_mul_mul_modEq_p6_of_p_dvd_both_oeis_361883 {p B C : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hB : p ∣ B) (hC : p ∣ C) :
    Nat.choose (p * (B + C)) (p * B) ≡ Nat.choose (B + C) B [MOD p ^ 6] := by
  have hU : let R := ZMod (p ^ (1 + 2 + 3))
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
    simpa using unitPartProd_zmod_p6_add_of_p_dvd_both_oeis_361883
      (p := p) (B := B) (C := C) hp hp5 hB hC
  simpa using choose_mul_mul_modEq_of_split_dvd_pow_of_unitPartProd_add_oeis_361883
    (p := p) (B := B) (C := C) (s := 1) (t := 2) hp hU

/-- The requested split-valuation statement in the case `t = 0`; this is exactly the existing
one-sided `p^(s+3)` result applied to the right index `B`. -/
lemma choose_mul_mul_modEq_of_split_dvd_pow_t_zero_oeis_361883 {p B C s : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hB : p ^ s ∣ B) (_hC : p ^ 0 ∣ C) :
    Nat.choose (p * (B + C)) (p * B) ≡ Nat.choose (B + C) B [MOD p ^ (s + 0 + 3)] := by
  simpa [Nat.add_assoc] using
    choose_mul_mul_modEq_of_right_dvd_pow_s3_oeis_361883
      (p := p) (A := B + C) (B := B) (s := s) hp hp5 hB

/-- The requested split-valuation statement in the case `s = 0`; by symmetry of binomial
coefficients it is the existing one-sided result applied to the complementary right index `C`. -/
lemma choose_mul_mul_modEq_of_split_dvd_pow_s_zero_oeis_361883 {p B C t : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (_hB : p ^ 0 ∣ B) (hC : p ^ t ∣ C) :
    Nat.choose (p * (B + C)) (p * B) ≡ Nat.choose (B + C) B [MOD p ^ (0 + t + 3)] := by
  have hchoosep : Nat.choose (p * (B + C)) (p * B) = Nat.choose (p * (B + C)) (p * C) := by
    apply Nat.choose_symm_of_eq_add
    ring
  have hchoose : Nat.choose (B + C) B = Nat.choose (B + C) C := by
    apply Nat.choose_symm_of_eq_add
    ring
  rw [hchoosep, hchoose]
  simpa [Nat.add_assoc] using
    choose_mul_mul_modEq_of_right_dvd_pow_s3_oeis_361883
      (p := p) (A := B + C) (B := C) (s := t) hp hp5 hC



/-- Cancellation of the common unit-part factor modulo `p^3`.  This is the ZMod step used for
adjacent binomial congruences once an exact factorial/unit-part identity has been proved. -/
lemma unitPartProd_cancel_modEq_mod_p3_oeis_361883 {p B C X Y : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hidentity : X * unitPartProd_oeis_361883 p B * unitPartProd_oeis_361883 p C =
      Y * unitPartProd_oeis_361883 p (B + C)) :
    X ≡ Y [MOD p ^ 3] := by
  classical
  let R := ZMod (p ^ 3)
  let UB : R := (unitPartProd_oeis_361883 p B : ℕ)
  let UC : R := (unitPartProd_oeis_361883 p C : ℕ)
  let V : R := UB * UC
  have hcast := congrArg (fun n : ℕ => (n : R)) hidentity
  have hU : ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) = V := by
    simpa [R, V, UB, UC] using unitPartProd_zmod_p3_add_oeis_361883 (p := p) (B := B) (C := C) hp hp5
  have hmain : ((X : ℕ) : R) * V = ((Y : ℕ) : R) * V := by
    simpa [R, V, UB, UC, hU, Nat.cast_mul, mul_assoc] using hcast
  have hV : IsUnit V := by
    dsimp [V, UB, UC]
    exact (unitPartProd_zmod_p3_isUnit_oeis_361883 (p := p) (N := B) hp).mul
      (unitPartProd_zmod_p3_isUnit_oeis_361883 (p := p) (N := C) hp)
  have hz : ((X : ℕ) : R) = ((Y : ℕ) : R) := hV.mul_right_cancel hmain
  exact (ZMod.natCast_eq_natCast_iff _ _ (p ^ 3)).1 hz


/-- Cancellation of the common unit-part factor modulo `p^6`, assuming the required
unit-part additivity in `ZMod (p^6)`. -/
lemma unitPartProd_cancel_modEq_p6_of_add_congr_oeis_361883 {p B C X Y : ℕ}
    (hp : p.Prime)
    (hU : let R := ZMod (p ^ 6)
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R))
    (hidentity : X * unitPartProd_oeis_361883 p B * unitPartProd_oeis_361883 p C =
      Y * unitPartProd_oeis_361883 p (B + C)) :
    X ≡ Y [MOD p ^ 6] := by
  classical
  let R := ZMod (p ^ 6)
  let UB : R := (unitPartProd_oeis_361883 p B : ℕ)
  let UC : R := (unitPartProd_oeis_361883 p C : ℕ)
  let V : R := UB * UC
  have hcast := congrArg (fun n : ℕ => (n : R)) hidentity
  have hU' : ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) = V := by
    simpa [R, V, UB, UC] using hU
  have hmain : ((X : ℕ) : R) * V = ((Y : ℕ) : R) * V := by
    simpa [R, V, UB, UC, hU', Nat.cast_mul, mul_assoc] using hcast
  have hV : IsUnit V := by
    dsimp [V, UB, UC]
    exact (unitPartProd_zmod_pow_isUnit_oeis_361883 (p := p) (N := B) (e := 6) hp).mul
      (unitPartProd_zmod_pow_isUnit_oeis_361883 (p := p) (N := C) (e := 6) hp)
  have hz : ((X : ℕ) : R) = ((Y : ℕ) : R) := hV.mul_right_cancel hmain
  exact (ZMod.natCast_eq_natCast_iff _ _ (p ^ 6)).1 hz

/-- Factorial decomposition for the predecessor of a positive multiple of `p`. -/
lemma factorial_mul_sub_one_unitPartProd_decomp_pos_oeis_361883 (p N : ℕ)
    (hp : 0 < p) (hN : 0 < N) :
    (p * N - 1)! = p ^ (N - 1) * (N - 1)! * unitPartProd_oeis_361883 p N := by
  have hpNpos : 0 < p * N := Nat.mul_pos hp hN
  have hfac := factorial_unitPartProd_decomp_pos_oeis_361883 p N hp
  apply Nat.eq_of_mul_eq_mul_left hpNpos
  calc
    p * N * (p * N - 1)! = (p * N)! := by
      have hs : p * N - 1 + 1 = p * N := Nat.sub_add_cancel (Nat.succ_le_of_lt hpNpos)
      rw [← hs, Nat.factorial_succ]
      have hpred : p * N - 1 + 1 - 1 = p * N - 1 := by omega
      rw [hpred]
    _ = p ^ N * N ! * unitPartProd_oeis_361883 p N := hfac
    _ = p * N * (p ^ (N - 1) * (N - 1)! * unitPartProd_oeis_361883 p N) := by
      cases N with
      | zero => omega
      | succ N =>
          simp [Nat.factorial_succ, pow_succ]
          ring

/-- Exact unit-part identity for `choose (p*(B+C)-1) (p*B-1)`. -/
lemma choose_mul_sub_one_unitPart_identity_oeis_361883 {p B C : ℕ} (hp : p.Prime)
    (hB : 0 < B) :
    Nat.choose (p * (B + C) - 1) (p * B - 1) * unitPartProd_oeis_361883 p B *
        unitPartProd_oeis_361883 p C =
      Nat.choose (B + C - 1) (B - 1) * unitPartProd_oeis_361883 p (B + C) := by
  let UB := unitPartProd_oeis_361883 p B
  let UC := unitPartProd_oeis_361883 p C
  let UA := unitPartProd_oeis_361883 p (B + C)
  let choosep := Nat.choose (p * (B + C) - 1) (p * B - 1)
  let chooseA := Nat.choose (B + C - 1) (B - 1)
  have hApos : 0 < B + C := by omega
  have hkle : p * B - 1 ≤ p * (B + C) - 1 := by
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_left p (Nat.le_add_right B C)) 1
  have hsub : p * (B + C) - 1 - (p * B - 1) = p * C := by
    have hrewrite : p * (B + C) = p * B + p * C := by ring
    rw [hrewrite]
    have hpBpos : 0 < p * B := Nat.mul_pos hp.pos hB
    omega
  have hpchoose : choosep * (p * B - 1)! * (p * C)! = (p * (B + C) - 1)! := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (n := p * (B + C) - 1) (k := p * B - 1) hkle
    simpa [choosep, hsub] using h
  have hsmall_sub : B + C - 1 - (B - 1) = C := by omega
  have hsmall_le : B - 1 ≤ B + C - 1 := by omega
  have hsmall : chooseA * (B - 1)! * (C !) = (B + C - 1)! := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (n := B + C - 1) (k := B - 1) hsmall_le
    simpa [chooseA, hsmall_sub] using h
  have hpchoose' : choosep * (p ^ (B - 1) * (B - 1)! * UB) * (p ^ C * (C !) * UC) =
      p ^ (B + C - 1) * (B + C - 1)! * UA := by
    rw [factorial_mul_sub_one_unitPartProd_decomp_pos_oeis_361883 p B hp.pos hB,
      factorial_unitPartProd_decomp_pos_oeis_361883 p C hp.pos,
      factorial_mul_sub_one_unitPartProd_decomp_pos_oeis_361883 p (B + C) hp.pos hApos] at hpchoose
    simpa [UB, UC, UA] using hpchoose
  let K := p ^ (B + C - 1) * (B - 1)! * (C !)
  have hKpos : 0 < K := by
    dsimp [K]
    exact Nat.mul_pos (Nat.mul_pos (pow_pos hp.pos (B + C - 1)) (factorial_pos (B - 1))) (factorial_pos C)
  apply Nat.eq_of_mul_eq_mul_left hKpos
  calc
    K * (choosep * UB * UC)
        = choosep * (p ^ (B - 1) * (B - 1)! * UB) * (p ^ C * C ! * UC) := by
          dsimp [K]
          have hpow : p ^ (B + C - 1) = p ^ (B - 1) * p ^ C := by
            have hidx : B + C - 1 = (B - 1) + C := by omega
            rw [hidx, pow_add]
          rw [hpow]
          ring
    _ = p ^ (B + C - 1) * (B + C - 1)! * UA := hpchoose'
    _ = K * (chooseA * UA) := by
          dsimp [K]
          rw [← hsmall]
          ring

/-- Exact unit-part identity for `choose (p*(B+C)-1) (p*B)`, with `0 < C`. -/
lemma choose_mul_sub_one_right_unitPart_identity_oeis_361883 {p B C : ℕ} (hp : p.Prime)
    (hC : 0 < C) :
    Nat.choose (p * (B + C) - 1) (p * B) * unitPartProd_oeis_361883 p B *
        unitPartProd_oeis_361883 p C =
      Nat.choose (B + C - 1) B * unitPartProd_oeis_361883 p (B + C) := by
  let UB := unitPartProd_oeis_361883 p B
  let UC := unitPartProd_oeis_361883 p C
  let UA := unitPartProd_oeis_361883 p (B + C)
  let choosep := Nat.choose (p * (B + C) - 1) (p * B)
  let chooseA := Nat.choose (B + C - 1) B
  have hApos : 0 < B + C := by omega
  have hkle : p * B ≤ p * (B + C) - 1 := by
    have hpcpos : 0 < p * C := Nat.mul_pos hp.pos hC
    have : p * (B + C) = p * B + p * C := by ring
    omega
  have hsub : p * (B + C) - 1 - p * B = p * C - 1 := by
    have : p * (B + C) = p * B + p * C := by ring
    omega
  have hpchoose : choosep * (p * B)! * (p * C - 1)! = (p * (B + C) - 1)! := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (n := p * (B + C) - 1) (k := p * B) hkle
    simpa [choosep, hsub] using h
  have hsmall_sub : B + C - 1 - B = C - 1 := by omega
  have hsmall_le : B ≤ B + C - 1 := by omega
  have hsmall : chooseA * (B !) * (C - 1)! = (B + C - 1)! := by
    have h := Nat.choose_mul_factorial_mul_factorial
      (n := B + C - 1) (k := B) hsmall_le
    simpa [chooseA, hsmall_sub] using h
  have hpchoose' : choosep * (p ^ B * (B !) * UB) * (p ^ (C - 1) * (C - 1)! * UC) =
      p ^ (B + C - 1) * (B + C - 1)! * UA := by
    rw [factorial_unitPartProd_decomp_pos_oeis_361883 p B hp.pos,
      factorial_mul_sub_one_unitPartProd_decomp_pos_oeis_361883 p C hp.pos hC,
      factorial_mul_sub_one_unitPartProd_decomp_pos_oeis_361883 p (B + C) hp.pos hApos] at hpchoose
    simpa [UB, UC, UA] using hpchoose
  let K := p ^ (B + C - 1) * (B !) * (C - 1)!
  have hKpos : 0 < K := by
    dsimp [K]
    exact Nat.mul_pos (Nat.mul_pos (pow_pos hp.pos (B + C - 1)) (factorial_pos B)) (factorial_pos (C - 1))
  apply Nat.eq_of_mul_eq_mul_left hKpos
  calc
    K * (choosep * UB * UC)
        = choosep * (p ^ B * B ! * UB) * (p ^ (C - 1) * (C - 1)! * UC) := by
          dsimp [K]
          have hpow : p ^ (B + C - 1) = p ^ B * p ^ (C - 1) := by
            have hidx : B + C - 1 = B + (C - 1) := by omega
            rw [hidx, pow_add]
          rw [hpow]
          ring
    _ = p ^ (B + C - 1) * (B + C - 1)! * UA := hpchoose'
    _ = K * (chooseA * UA) := by
          dsimp [K]
          rw [← hsmall]
          ring

/-- Adjacent split congruence modulo `p^6` for indices one less than multiples of `p`,
when both split parts are divisible by `p`. -/
lemma choose_mul_sub_one_modEq_p6_of_p_dvd_both_oeis_361883 {p B C : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hBpos : 0 < B) (hBdvd : p ∣ B) (hCdvd : p ∣ C) :
    Nat.choose (p * (B + C) - 1) (p * B - 1) ≡
      Nat.choose (B + C - 1) (B - 1) [MOD p ^ 6] := by
  have hidentity := choose_mul_sub_one_unitPart_identity_oeis_361883
    (p := p) (B := B) (C := C) hp hBpos
  have hU : let R := ZMod (p ^ 6)
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
    exact unitPartProd_zmod_p6_add_of_p_dvd_both_oeis_361883
      (p := p) (B := B) (C := C) hp hp5 hBdvd hCdvd
  exact unitPartProd_cancel_modEq_p6_of_add_congr_oeis_361883
    (p := p) (B := B) (C := C)
    (X := Nat.choose (p * (B + C) - 1) (p * B - 1))
    (Y := Nat.choose (B + C - 1) (B - 1)) hp hU hidentity

/-- Right adjacent split congruence modulo `p^6` when both split parts are divisible by `p`. -/
lemma choose_mul_sub_one_right_modEq_p6_of_p_dvd_both_oeis_361883 {p B C : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hCpos : 0 < C) (hBdvd : p ∣ B) (hCdvd : p ∣ C) :
    Nat.choose (p * (B + C) - 1) (p * B) ≡ Nat.choose (B + C - 1) B [MOD p ^ 6] := by
  have hidentity := choose_mul_sub_one_right_unitPart_identity_oeis_361883
    (p := p) (B := B) (C := C) hp hCpos
  have hU : let R := ZMod (p ^ 6)
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
    exact unitPartProd_zmod_p6_add_of_p_dvd_both_oeis_361883
      (p := p) (B := B) (C := C) hp hp5 hBdvd hCdvd
  exact unitPartProd_cancel_modEq_p6_of_add_congr_oeis_361883
    (p := p) (B := B) (C := C)
    (X := Nat.choose (p * (B + C) - 1) (p * B))
    (Y := Nat.choose (B + C - 1) B) hp hU hidentity

/-- Adjacent Jacobsthal--Kazandzidis congruence modulo `p^3` for indices one less than multiples
of `p`. -/
lemma choose_mul_sub_one_modEq_mod_p3_oeis_361883 {p A B : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hA : 0 < A) (hB : 0 < B) :
    Nat.choose (p * A - 1) (p * B - 1) ≡ Nat.choose (A - 1) (B - 1) [MOD p ^ 3] := by
  by_cases hBA : B ≤ A
  · let C := A - B
    have hAeq : A = B + C := by
      dsimp [C]
      omega
    have hidentity := choose_mul_sub_one_unitPart_identity_oeis_361883 (p := p) (B := B) (C := C) hp hB
    rw [hAeq]
    exact unitPartProd_cancel_modEq_mod_p3_oeis_361883 (p := p) (B := B) (C := C)
      (X := Nat.choose (p * (B + C) - 1) (p * B - 1))
      (Y := Nat.choose (B + C - 1) (B - 1)) hp hp5 hidentity
  · have hlt : A < B := Nat.lt_of_not_ge hBA
    have hp_lt : p * A - 1 < p * B - 1 := by
      have : p * A < p * B := Nat.mul_lt_mul_of_pos_left hlt hp.pos
      have hpApos : 0 < p * A := Nat.mul_pos hp.pos hA
      have hpBpos : 0 < p * B := Nat.mul_pos hp.pos hB
      omega
    have hsmall_lt : A - 1 < B - 1 := by omega
    rw [Nat.choose_eq_zero_of_lt hp_lt, Nat.choose_eq_zero_of_lt hsmall_lt]

/-- Adjacent Jacobsthal--Kazandzidis congruence modulo `p^3` with right index divisible by `p`. -/
lemma choose_mul_sub_one_right_modEq_mod_p3_oeis_361883 {p A B : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hA : 0 < A) :
    Nat.choose (p * A - 1) (p * B) ≡ Nat.choose (A - 1) B [MOD p ^ 3] := by
  by_cases hBA : B < A
  · let C := A - B
    have hC : 0 < C := by
      dsimp [C]
      omega
    have hAeq : A = B + C := by
      dsimp [C]
      omega
    have hidentity := choose_mul_sub_one_right_unitPart_identity_oeis_361883 (p := p) (B := B) (C := C) hp hC
    rw [hAeq]
    exact unitPartProd_cancel_modEq_mod_p3_oeis_361883 (p := p) (B := B) (C := C)
      (X := Nat.choose (p * (B + C) - 1) (p * B))
      (Y := Nat.choose (B + C - 1) B) hp hp5 hidentity
  · have hle : A ≤ B := Nat.le_of_not_gt hBA
    have hp_lt : p * A - 1 < p * B := by
      have hpApos : 0 < p * A := Nat.mul_pos hp.pos hA
      have : p * A ≤ p * B := Nat.mul_le_mul_left p hle
      omega
    have hsmall_lt : A - 1 < B := by omega
    rw [Nat.choose_eq_zero_of_lt hp_lt, Nat.choose_eq_zero_of_lt hsmall_lt]

/-- Adjacent Jacobsthal--Kazandzidis congruence with precision depending on the right
index: if `p^s ∣ B`, then `choose (p*A-1) (p*B-1)` is congruent to
`choose (A-1) (B-1)` modulo `p^(s+3)`. -/
lemma choose_mul_sub_one_modEq_of_right_dvd_pow_s3_oeis_361883 {p A B s : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hA : 0 < A) (hBpos : 0 < B) (hB : p ^ s ∣ B) :
    Nat.choose (p * A - 1) (p * B - 1) ≡ Nat.choose (A - 1) (B - 1) [MOD p ^ (s + 3)] := by
  by_cases hBA : B ≤ A
  · let C := A - B
    have hAeq : A = B + C := by
      dsimp [C]
      omega
    have hidentity := choose_mul_sub_one_unitPart_identity_oeis_361883
      (p := p) (B := B) (C := C) hp hBpos
    have hU : let R := ZMod (p ^ (s + 3))
        ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
          ((unitPartProd_oeis_361883 p B : ℕ) : R) *
            ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
      exact unitPartProd_zmod_pow_s3_add_of_shift_oeis_361883
        (p := p) (B := B) (C := C) (s := s) (by
          intro u _hu
          exact product_block_zmod_pow_s3_shift_of_dvd_oeis_361883
            (p := p) (B := B) (u := u) (s := s) hp hp5 hB)
    have hcong := unitPartProd_cancel_modEq_pow_s3_of_add_congr_oeis_361883
      (p := p) (s := s) (B := B) (C := C)
      (X := Nat.choose (p * (B + C) - 1) (p * B - 1))
      (Y := Nat.choose (B + C - 1) (B - 1)) hp hU hidentity
    rw [hAeq]
    exact hcong
  · have hlt : A < B := Nat.lt_of_not_ge hBA
    have hp_lt : p * A - 1 < p * B - 1 := by
      have : p * A < p * B := Nat.mul_lt_mul_of_pos_left hlt hp.pos
      have hpApos : 0 < p * A := Nat.mul_pos hp.pos hA
      have hpBpos : 0 < p * B := Nat.mul_pos hp.pos hBpos
      omega
    have hsmall_lt : A - 1 < B - 1 := by omega
    rw [Nat.choose_eq_zero_of_lt hp_lt, Nat.choose_eq_zero_of_lt hsmall_lt]

/-- Adjacent Jacobsthal--Kazandzidis congruence with precision depending on the right
index, for the right adjacent binomial coefficient. -/
lemma choose_mul_sub_one_right_modEq_of_right_dvd_pow_s3_oeis_361883 {p A B s : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hA : 0 < A) (hB : p ^ s ∣ B) :
    Nat.choose (p * A - 1) (p * B) ≡ Nat.choose (A - 1) B [MOD p ^ (s + 3)] := by
  by_cases hBA : B < A
  · let C := A - B
    have hC : 0 < C := by
      dsimp [C]
      omega
    have hAeq : A = B + C := by
      dsimp [C]
      omega
    have hidentity := choose_mul_sub_one_right_unitPart_identity_oeis_361883
      (p := p) (B := B) (C := C) hp hC
    have hU : let R := ZMod (p ^ (s + 3))
        ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
          ((unitPartProd_oeis_361883 p B : ℕ) : R) *
            ((unitPartProd_oeis_361883 p C : ℕ) : R) := by
      exact unitPartProd_zmod_pow_s3_add_of_shift_oeis_361883
        (p := p) (B := B) (C := C) (s := s) (by
          intro u _hu
          exact product_block_zmod_pow_s3_shift_of_dvd_oeis_361883
            (p := p) (B := B) (u := u) (s := s) hp hp5 hB)
    have hcong := unitPartProd_cancel_modEq_pow_s3_of_add_congr_oeis_361883
      (p := p) (s := s) (B := B) (C := C)
      (X := Nat.choose (p * (B + C) - 1) (p * B))
      (Y := Nat.choose (B + C - 1) B) hp hU hidentity
    rw [hAeq]
    exact hcong
  · have hle : A ≤ B := Nat.le_of_not_gt hBA
    have hp_lt : p * A - 1 < p * B := by
      have hpApos : 0 < p * A := Nat.mul_pos hp.pos hA
      have : p * A ≤ p * B := Nat.mul_le_mul_left p hle
      omega
    have hsmall_lt : A - 1 < B := by omega
    rw [Nat.choose_eq_zero_of_lt hp_lt, Nat.choose_eq_zero_of_lt hsmall_lt]


/-- The requested complementary (non-unit) diagonal congruence at the base level `r = 1`.
At this precision the adjacent Jacobsthal--Kazandzidis congruences modulo `p^3` prove the
pointwise diagonal congruence directly, so no cancellation by `M+j` is needed. -/
lemma T_diag_nonunit_modEq_general_r_one_oeis_361883 {p M j : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hMpos : 0 < M) (_hpdiv : p ∣ M + j) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ (3 * 1)] := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  have hApos : 0 < M + j := by omega
  refine T_diag_mod_pow_of_adjacent_modEq_oeis_361883
    (p := p) (M := M) (r := 1) (j := j) hp0 hMpos ?_ ?_
  · have h := choose_mul_sub_one_modEq_mod_p3_oeis_361883
      (p := p) (A := M + j) (B := M) hp hp5 hApos hMpos
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using h
  · have h := choose_mul_sub_one_right_modEq_mod_p3_oeis_361883
      (p := p) (A := M + j) (B := M) hp hp5 hApos
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using h

/-- A formulation matching the general non-unit statement when the exponent is known to be
`r = 1`.  This is the verified base case of the complementary diagonal term congruence. -/
lemma T_diag_nonunit_modEq_general_of_r_eq_one_oeis_361883 {p M r j : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (_hr : 0 < r) (hMpos : 0 < M) (_hMdiv : p ^ (r - 1) ∣ M)
    (hpdiv : p ∣ M + j) (hr_eq : r = 1) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ (3 * r)] := by
  subst r
  exact T_diag_nonunit_modEq_general_r_one_oeis_361883
    (p := p) (M := M) (j := j) hp5 hMpos hpdiv

/-- The `p^6` diagonal congruence in the non-unit case `p ∣ M` and `p ∣ M+j`.
Here the divisibility assumptions force `p ∣ j`; for `j > 0`, the two adjacent
binomial congruences follow from the exact unit-part identities and the `p^6`
unit-part product congruence for two `p`-divisible split parts. -/
lemma T_diag_nonunit_modEq_r_two_oeis_361883 {p M j : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hMpos : 0 < M) (hMdiv : p ∣ M) (hpdiv : p ∣ M + j) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ 6] := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  by_cases hjzero : j = 0
  · subst j
    simpa using T_diag_zero_modEq_oeis_361883 (p := p) (M := M) (r := 2) hMpos hp0
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
    have hjdiv : p ∣ j := by
      simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hpdiv hMdiv
    have hdiag := T_diag_mod_pow_of_adjacent_modEq_oeis_361883
      (p := p) (M := M) (r := 2) (j := j) hp0 hMpos
      (by
        have h := choose_mul_sub_one_modEq_p6_of_p_dvd_both_oeis_361883
          (p := p) (B := M) (C := j) hp hp5 hMpos hMdiv hjdiv
        simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc] using h)
      (by
        have h := choose_mul_sub_one_right_modEq_p6_of_p_dvd_both_oeis_361883
          (p := p) (B := M) (C := j) hp hp5 hjpos hMdiv hjdiv
        simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc] using h)
    simpa using hdiag

/-- Exponent bookkeeping obstruction for the currently available one-sided high-precision
adjacent congruences in the higher non-unit case: for `r ≥ 2`, a congruence modulo
`p^(r+2)` plus only the two powers coming from a `p^(r-2)`-divisible adjacent factor reaches
`p^(3*r-2)`, still short of the target `p^(3*r)`. -/
lemma diag_nonunit_one_sided_adjacent_precision_insufficient_oeis_361883 {r : ℕ}
    (hr : 2 ≤ r) :
    ¬ 3 * r ≤ (r + 2) + 2 * (r - 2) := by
  omega




/-- The diagonal contribution at the first level follows from the adjacent Jacobsthal congruences
modulo `p^3`. -/
lemma diag_sum_modEq_r_one_oeis_361883 {p M : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hM : 0 < M) :
    (Finset.sum (Finset.range (M + 1)) fun j => oeis_361883_T (M * p) (p * j)) ≡
      a M [MOD p ^ 3] := by
  refine diag_sum_modEq_of_pointwise_oeis_361883 (p := p) (M := M) (r := 1) hM ?_
  intro j hj
  have hp0 : 0 < p := hp.pos
  have hApos : 0 < M + j := by omega
  refine T_diag_mod_pow_of_adjacent_modEq_oeis_361883 (p := p) (M := M) (r := 1) (j := j) hp0 hM ?_ ?_
  · have h := choose_mul_sub_one_modEq_mod_p3_oeis_361883
      (p := p) (A := M + j) (B := M) hp hp5 hApos hM

    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using h
  · have h := choose_mul_sub_one_right_modEq_mod_p3_oeis_361883
      (p := p) (A := M + j) (B := M) hp hp5 hApos
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using h


/-- Formal record of the exponent obstruction in the naive attempt to lift the
modulo-`p^3` adjacent congruences using only two powers coming from the adjacent
binomial coefficient.  For every genuinely higher level `r ≥ 2`, the bound
`3 + 2*(r-1)` is still strictly below the target exponent `3*r`. -/
lemma diag_base_p3_square_exponent_insufficient_oeis_361883 {r : ℕ} (hr : 2 ≤ r) :
    ¬ 3 * r ≤ 3 + 2 * (r - 1) := by
  omega


/-- Cancellation of the common unit-part factor modulo `p^9`, assuming the required
unit-part additivity in `ZMod (p^9)`.  This is the p^9 analogue of the final
cancellation step used in the verified `r = 2` non-unit diagonal argument. -/
lemma unitPartProd_cancel_modEq_p9_of_add_congr_oeis_361883 {p B C X Y : ℕ}
    (hp : p.Prime)
    (hU : let R := ZMod (p ^ 9)
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R))
    (hidentity : X * unitPartProd_oeis_361883 p B * unitPartProd_oeis_361883 p C =
      Y * unitPartProd_oeis_361883 p (B + C)) :
    X ≡ Y [MOD p ^ 9] := by
  classical
  let R := ZMod (p ^ 9)
  let UB : R := (unitPartProd_oeis_361883 p B : ℕ)
  let UC : R := (unitPartProd_oeis_361883 p C : ℕ)
  let V : R := UB * UC
  have hcast := congrArg (fun n : ℕ => (n : R)) hidentity
  have hU' : ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) = V := by
    simpa [R, V, UB, UC] using hU
  have hmain : ((X : ℕ) : R) * V = ((Y : ℕ) : R) * V := by
    simpa [R, V, UB, UC, hU', Nat.cast_mul, mul_assoc] using hcast
  have hV : IsUnit V := by
    dsimp [V, UB, UC]
    exact (unitPartProd_zmod_pow_isUnit_oeis_361883 (p := p) (N := B) (e := 9) hp).mul
      (unitPartProd_zmod_pow_isUnit_oeis_361883 (p := p) (N := C) (e := 9) hp)
  have hz : ((X : ℕ) : R) = ((Y : ℕ) : R) := hV.mul_right_cancel hmain
  exact (ZMod.natCast_eq_natCast_iff _ _ (p ^ 9)).1 hz

/-- Adjacent split congruence modulo `p^9` for indices one less than multiples of `p`,
conditional on the precise p^9 unit-part multiplicativity for the split. -/
lemma choose_mul_sub_one_modEq_p9_of_unitPartProd_add_oeis_361883 {p B C : ℕ}
    (hp : p.Prime) (hBpos : 0 < B)
    (hU : let R := ZMod (p ^ 9)
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R)) :
    Nat.choose (p * (B + C) - 1) (p * B - 1) ≡
      Nat.choose (B + C - 1) (B - 1) [MOD p ^ 9] := by
  have hidentity := choose_mul_sub_one_unitPart_identity_oeis_361883
    (p := p) (B := B) (C := C) hp hBpos
  exact unitPartProd_cancel_modEq_p9_of_add_congr_oeis_361883
    (p := p) (B := B) (C := C)
    (X := Nat.choose (p * (B + C) - 1) (p * B - 1))
    (Y := Nat.choose (B + C - 1) (B - 1)) hp hU hidentity

/-- Right-adjacent split congruence modulo `p^9`, conditional on p^9 unit-part
multiplicativity for the split. -/
lemma choose_mul_sub_one_right_modEq_p9_of_unitPartProd_add_oeis_361883 {p B C : ℕ}
    (hp : p.Prime) (hCpos : 0 < C)
    (hU : let R := ZMod (p ^ 9)
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R)) :
    Nat.choose (p * (B + C) - 1) (p * B) ≡ Nat.choose (B + C - 1) B [MOD p ^ 9] := by
  have hidentity := choose_mul_sub_one_right_unitPart_identity_oeis_361883
    (p := p) (B := B) (C := C) hp hCpos
  exact unitPartProd_cancel_modEq_p9_of_add_congr_oeis_361883
    (p := p) (B := B) (C := C)
    (X := Nat.choose (p * (B + C) - 1) (p * B))
    (Y := Nat.choose (B + C - 1) B) hp hU hidentity


/-- Adjacent split congruence modulo `p^7` for indices one less than multiples of `p`,
conditional on the minimal (`p^7`) unit-part multiplicativity for the split.  This is
the lower-precision replacement for the earlier `p^9` adjacent hypothesis. -/
lemma choose_mul_sub_one_modEq_p7_of_unitPartProd_add_oeis_361883 {p B C : ℕ}
    (hp : p.Prime) (hBpos : 0 < B)
    (hU : let R := ZMod (p ^ 7)
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R)) :
    Nat.choose (p * (B + C) - 1) (p * B - 1) ≡
      Nat.choose (B + C - 1) (B - 1) [MOD p ^ 7] := by
  have hidentity := choose_mul_sub_one_unitPart_identity_oeis_361883
    (p := p) (B := B) (C := C) hp hBpos
  simpa using unitPartProd_cancel_modEq_pow_s3_of_add_congr_oeis_361883
    (p := p) (s := 4) (B := B) (C := C)
    (X := Nat.choose (p * (B + C) - 1) (p * B - 1))
    (Y := Nat.choose (B + C - 1) (B - 1)) hp hU hidentity

/-- Right-adjacent split congruence modulo `p^7`, conditional on the minimal (`p^7`)
unit-part multiplicativity for the split. -/
lemma choose_mul_sub_one_right_modEq_p7_of_unitPartProd_add_oeis_361883 {p B C : ℕ}
    (hp : p.Prime) (hCpos : 0 < C)
    (hU : let R := ZMod (p ^ 7)
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R)) :
    Nat.choose (p * (B + C) - 1) (p * B) ≡ Nat.choose (B + C - 1) B [MOD p ^ 7] := by
  have hidentity := choose_mul_sub_one_right_unitPart_identity_oeis_361883
    (p := p) (B := B) (C := C) hp hCpos
  simpa using unitPartProd_cancel_modEq_pow_s3_of_add_congr_oeis_361883
    (p := p) (s := 4) (B := B) (C := C)
    (X := Nat.choose (p * (B + C) - 1) (p * B))
    (Y := Nat.choose (B + C - 1) B) hp hU hidentity


/-- If two natural numbers are congruent modulo `p^8`, then after multiplication by a
`p`-divisible factor they are equal in `ZMod (p^9)`. -/
lemma zmod_mul_eq_of_modEq_p8_of_p_dvd_oeis_361883 {p a b x : ℕ}
    (h : a ≡ b [MOD p ^ 8]) (hx : p ∣ x) :
    let R := ZMod (p ^ 9)
    ((x : ℕ) : R) * ((a : ℕ) : R) = ((x : ℕ) : R) * ((b : ℕ) : R) := by
  intro R
  rcases hx with ⟨y, rfl⟩
  have hpa : p * a ≡ p * b [MOD p ^ 9] := by
    have h' := h.mul_left' p
    have hmod : p * p ^ 8 = p ^ 9 := by
      simpa using (show p ^ 1 * p ^ 8 = p ^ (1 + 8) by rw [← pow_add])
    simpa [hmod] using h'
  have hz : ((p * a : ℕ) : R) = ((p * b : ℕ) : R) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hpa
  calc
    (((p * y : ℕ) : R) * ((a : ℕ) : R)) = ((y : R) * ((p * a : ℕ) : R)) := by
      simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = ((y : R) * ((p * b : ℕ) : R)) := by rw [hz]
    _ = (((p * y : ℕ) : R) * ((b : ℕ) : R)) := by
      simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]

/-- If two natural numbers are congruent modulo `p^7`, then after multiplication by a
`p^2`-divisible factor they are equal in `ZMod (p^9)`. -/
lemma zmod_mul_eq_of_modEq_p7_of_p2_dvd_oeis_361883 {p a b x : ℕ}
    (h : a ≡ b [MOD p ^ 7]) (hx : p ^ 2 ∣ x) :
    let R := ZMod (p ^ 9)
    ((x : ℕ) : R) * ((a : ℕ) : R) = ((x : ℕ) : R) * ((b : ℕ) : R) := by
  intro R
  rcases hx with ⟨y, rfl⟩
  have hp2a : p ^ 2 * a ≡ p ^ 2 * b [MOD p ^ 9] := by
    have h' := h.mul_left' (p ^ 2)
    have hmod : p ^ 2 * p ^ 7 = p ^ 9 := by
      rw [← pow_add]
    simpa [hmod] using h'
  have hz : (((p ^ 2) * a : ℕ) : R) = (((p ^ 2) * b : ℕ) : R) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hp2a
  calc
    ((((p ^ 2) * y : ℕ) : R) * ((a : ℕ) : R)) = ((y : R) * (((p ^ 2) * a : ℕ) : R)) := by
      simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = ((y : R) * (((p ^ 2) * b : ℕ) : R)) := by rw [hz]
    _ = ((((p ^ 2) * y : ℕ) : R) * ((b : ℕ) : R)) := by
      simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Polynomial lift for the r=3 diagonal summand: an extra power on the left-adjacent
coefficient, plus `p`-divisibility of both left-adjacent coefficients, upgrades the two
adjacent congruences of precisions `p^8` and `p^7` to the required `T` congruence modulo
`p^9`. -/
lemma T_poly_modEq_p9_of_adjacent_lift_oeis_361883 {p A1 A0 C1 C0 : ℕ}
    (hA8 : A1 ≡ A0 [MOD p ^ 8]) (hC7 : C1 ≡ C0 [MOD p ^ 7])
    (hA1div : p ∣ A1) (hA0div : p ∣ A0) :
    A1 ^ 2 * (A1 + 2 * C1) ≡ A0 ^ 2 * (A0 + 2 * C0) [MOD p ^ 9] := by
  let R := ZMod (p ^ 9)
  apply (ZMod.natCast_eq_natCast_iff _ _ _).1
  change (((A1 ^ 2 * (A1 + 2 * C1) : ℕ) : R) =
    ((A0 ^ 2 * (A0 + 2 * C0) : ℕ) : R))
  have hAmul : ∀ x : ℕ, p ∣ x → ((x : ℕ) : R) * ((A1 : ℕ) : R) = ((x : ℕ) : R) * ((A0 : ℕ) : R) := by
    intro x hx
    exact zmod_mul_eq_of_modEq_p8_of_p_dvd_oeis_361883 (p := p) (a := A1) (b := A0) (x := x) hA8 hx
  have hCmul : ∀ x : ℕ, p ^ 2 ∣ x → ((x : ℕ) : R) * ((C1 : ℕ) : R) = ((x : ℕ) : R) * ((C0 : ℕ) : R) := by
    intro x hx
    exact zmod_mul_eq_of_modEq_p7_of_p2_dvd_oeis_361883 (p := p) (a := C1) (b := C0) (x := x) hC7 hx
  have hA1sq : ((A1 ^ 2 : ℕ) : R) = ((A0 ^ 2 : ℕ) : R) := by
    have h1 := hAmul A1 hA1div
    have h2 := hAmul A0 hA0div
    calc
      ((A1 ^ 2 : ℕ) : R) = ((A1 : R) * (A1 : R)) := by simp [pow_two]
      _ = ((A1 : R) * (A0 : R)) := h1
      _ = ((A0 : R) * (A1 : R)) := by ring
      _ = ((A0 : R) * (A0 : R)) := h2
      _ = ((A0 ^ 2 : ℕ) : R) := by simp [pow_two]
  have hA0sq_p2 : p ^ 2 ∣ A0 ^ 2 := by
    rcases hA0div with ⟨u, hu⟩
    refine ⟨u ^ 2, ?_⟩
    rw [hu]
    ring
  have hA0sq_p : p ∣ A0 ^ 2 := by
    exact (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hA0sq_p2
  have hcube : ((A1 ^ 2 * A1 : ℕ) : R) = ((A0 ^ 2 * A0 : ℕ) : R) := by
    calc
      ((A1 ^ 2 * A1 : ℕ) : R) = ((A1 ^ 2 : ℕ) : R) * ((A1 : ℕ) : R) := by simp
      _ = ((A0 ^ 2 : ℕ) : R) * ((A1 : ℕ) : R) := by rw [hA1sq]
      _ = ((A0 ^ 2 : ℕ) : R) * ((A0 : ℕ) : R) := hAmul (A0 ^ 2) hA0sq_p
      _ = ((A0 ^ 2 * A0 : ℕ) : R) := by simp
  have hCterm : ((A1 ^ 2 * C1 : ℕ) : R) = ((A0 ^ 2 * C0 : ℕ) : R) := by
    calc
      ((A1 ^ 2 * C1 : ℕ) : R) = ((A1 ^ 2 : ℕ) : R) * ((C1 : ℕ) : R) := by simp
      _ = ((A0 ^ 2 : ℕ) : R) * ((C1 : ℕ) : R) := by rw [hA1sq]
      _ = ((A0 ^ 2 : ℕ) : R) * ((C0 : ℕ) : R) := hCmul (A0 ^ 2) hA0sq_p2
      _ = ((A0 ^ 2 * C0 : ℕ) : R) := by simp
  calc
    ((A1 ^ 2 * (A1 + 2 * C1) : ℕ) : R)
        = ((A1 ^ 2 * A1 : ℕ) : R) + (2 : R) * ((A1 ^ 2 * C1 : ℕ) : R) := by
          simp [Nat.cast_add, Nat.cast_mul, right_distrib, mul_assoc, mul_left_comm, mul_comm]
    _ = ((A0 ^ 2 * A0 : ℕ) : R) + (2 : R) * ((A0 ^ 2 * C0 : ℕ) : R) := by
          rw [hcube, hCterm]
    _ = ((A0 ^ 2 * (A0 + 2 * C0) : ℕ) : R) := by
          simp [Nat.cast_add, Nat.cast_mul, right_distrib, mul_assoc, mul_left_comm, mul_comm]

/-- Conditional summand lift corresponding to `T_poly_modEq_p9_of_adjacent_lift_oeis_361883`. -/
lemma T_diag_nonunit_modEq_r_three_of_adjacent_lift_oeis_361883 {p M j : ℕ}
    (hp0 : 0 < p) (hMpos : 0 < M)
    (hA8 : Nat.choose (M * p + p * j - 1) (M * p - 1) ≡
        Nat.choose (M + j - 1) (M - 1) [MOD p ^ 8])
    (hC7 : Nat.choose (M * p + p * j - 1) (M * p) ≡
        Nat.choose (M + j - 1) M [MOD p ^ 7])
    (hA1div : p ∣ Nat.choose (M * p + p * j - 1) (M * p - 1))
    (hA0div : p ∣ Nat.choose (M + j - 1) (M - 1)) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ 9] := by
  have hMp : 0 < M * p := Nat.mul_pos hMpos hp0
  rw [oeis_361883_T_eq_sq_mul (N := M * p) (k := p * j) hMp]
  rw [oeis_361883_T_eq_sq_mul (N := M) (k := j) hMpos]
  let A1 := Nat.choose (M * p + p * j - 1) (M * p - 1)
  let C1 := Nat.choose (M * p + p * j - 1) (M * p)
  let A0 := Nat.choose (M + j - 1) (M - 1)
  let C0 := Nat.choose (M + j - 1) M
  change A1 ^ 2 * (A1 + 2 * C1) ≡ A0 ^ 2 * (A0 + 2 * C0) [MOD p ^ 9]
  exact T_poly_modEq_p9_of_adjacent_lift_oeis_361883
    (p := p) (A1 := A1) (A0 := A0) (C1 := C1) (C0 := C0)
    (by simpa [A1, A0] using hA8) (by simpa [C1, C0] using hC7)
    (by simpa [A1] using hA1div) (by simpa [A0] using hA0div)

/-- In the exact-valuation-one right-index case, the right-adjacent congruence modulo
`p^7` and the adjacent identities force the left-adjacent congruence one power higher.
This is the cancellation step `(A1-A0)*j=(C1-C0)*M`, using `p^2 ∣ M` and
`v_p(j)=1`. -/
lemma choose_left_modEq_p8_of_right_modEq_p7_exact_p_oeis_361883 {p M j : ℕ} [Fact p.Prime]
    (hMpos : 0 < M) (hMdiv : p ^ 2 ∣ M) (hjdiv : p ∣ j) (hjnot2 : ¬ p ^ 2 ∣ j)
    (hC7 : Nat.choose (M * p + p * j - 1) (M * p) ≡
        Nat.choose (M + j - 1) M [MOD p ^ 7]) :
    Nat.choose (M * p + p * j - 1) (M * p - 1) ≡
        Nat.choose (M + j - 1) (M - 1) [MOD p ^ 8] := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  rcases hjdiv with ⟨d, hd⟩
  have hjnotd : ¬ p ∣ d := by
    intro hpd
    rcases hpd with ⟨e, rfl⟩
    apply hjnot2
    refine ⟨e, ?_⟩
    rw [hd]
    ring
  let A1 := Nat.choose (M * p + p * j - 1) (M * p - 1)
  let C1 := Nat.choose (M * p + p * j - 1) (M * p)
  let A0 := Nat.choose (M + j - 1) (M - 1)
  let C0 := Nat.choose (M + j - 1) M
  have hC7' : C1 ≡ C0 [MOD p ^ 7] := by simpa [C1, C0] using hC7
  have hM9 : p ^ 9 ∣ p ^ 7 * M := by
    rcases hMdiv with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [hu]
    calc
      p ^ 7 * (p ^ 2 * u) = (p ^ 7 * p ^ 2) * u := by ring
      _ = p ^ (7 + 2) * u := by rw [← pow_add]
      _ = p ^ 9 * u := by norm_num
  have hCM9 : C1 * M ≡ C0 * M [MOD p ^ 9] := by
    have h := hC7'.mul_right' M
    exact Nat.ModEq.of_dvd hM9 h
  have hadj1 : C1 * M = A1 * j := by
    have hraw := choose_adjacent_mul_for_oeis_361883 (n := M * p) (k := p * j)
      (Nat.mul_pos hMpos hp0)
    apply Nat.eq_of_mul_eq_mul_left hp0
    calc
      p * (C1 * M) = C1 * (M * p) := by ring
      _ = A1 * (p * j) := by simpa [A1, C1] using hraw
      _ = p * (A1 * j) := by ring
  have hadj0 : C0 * M = A0 * j := by
    simpa [A0, C0] using choose_adjacent_mul_for_oeis_361883 (n := M) (k := j) hMpos
  have hAj9 : A1 * j ≡ A0 * j [MOD p ^ 9] := by
    simpa [hadj1, hadj0] using hCM9
  have hpd9 : p ^ 9 / (p ^ 9).gcd p = p ^ 8 := by
    have hg : (p ^ 9).gcd p = p := Nat.gcd_eq_right (dvd_pow_self p (by norm_num : 9 ≠ 0))
    rw [hg]
    simpa using (Nat.pow_div (x := p) (m := 9) (n := 1) (by norm_num) hp0)
  have hAd_cancel : A1 * d ≡ A0 * d [MOD p ^ 8] := by
    have hpAj : p * (A1 * d) ≡ p * (A0 * d) [MOD p ^ 9] := by
      simpa [hd, mul_assoc, mul_left_comm, mul_comm] using hAj9
    have hcan := Nat.ModEq.cancel_left_div_gcd (m := p ^ 9) (a := A1 * d) (b := A0 * d) (c := p)
      (pow_pos hp0 9) hpAj
    simpa [hpd9] using hcan
  have hgcd : (p ^ 8).gcd d = 1 := by
    exact (Nat.coprime_iff_gcd_eq_one.mp (Nat.Coprime.pow_left 8 ((hp.coprime_iff_not_dvd).2 hjnotd)))
  have hA8' := Nat.ModEq.cancel_right_of_coprime (m := p ^ 8) (a := A1) (b := A0) (c := d) hgcd hAd_cancel
  simpa [A1, A0] using hA8'

/-- The remaining `r=3` non-unit diagonal subcase when the right index has exact
`p`-adic valuation one. -/
lemma T_diag_nonunit_modEq_r_three_of_p_dvd_not_p2_dvd_right_oeis_361883 {p M j : ℕ} [Fact p.Prime]
  (hp5 : 5 ≤ p) (hMpos : 0 < M) (hMdiv : p^2 ∣ M) (hjdiv : p ∣ j) (hjnot2 : ¬ p^2 ∣ j) :
  oeis_361883_T (M*p) (p*j) ≡ oeis_361883_T M j [MOD p^9] := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  have hjpos : 0 < j := by
    by_contra hjnpos
    have hj0 : j = 0 := Nat.eq_zero_of_not_pos hjnpos
    subst j
    exact hjnot2 (dvd_zero (p ^ 2))
  have hU : let R := ZMod (p ^ 7)
      ((unitPartProd_oeis_361883 p (M + j) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p M : ℕ) : R) *
          ((unitPartProd_oeis_361883 p j : ℕ) : R) :=
    unitPartProd_zmod_p7_add_of_p2_dvd_left_p_dvd_right_oeis_361883
      (p := p) (B := M) (C := j) hp hp5 hMdiv hjdiv
  have hC7 : Nat.choose (M * p + p * j - 1) (M * p) ≡
        Nat.choose (M + j - 1) M [MOD p ^ 7] := by
    have h := choose_mul_sub_one_right_modEq_p7_of_unitPartProd_add_oeis_361883
      (p := p) (B := M) (C := j) hp hjpos hU
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using h
  have hA8 : Nat.choose (M * p + p * j - 1) (M * p - 1) ≡
        Nat.choose (M + j - 1) (M - 1) [MOD p ^ 8] :=
    choose_left_modEq_p8_of_right_modEq_p7_exact_p_oeis_361883
      (p := p) (M := M) (j := j) hMpos hMdiv hjdiv hjnot2 hC7
  have hvj : padicValNat p j = 1 := by
    have hjne : j ≠ 0 := hjpos.ne'
    have hle1 : 1 ≤ padicValNat p j := by
      exact (padicValNat_dvd_iff_le (p := p) hjne).1 (by simpa using hjdiv)
    have hnle2 : ¬ 2 ≤ padicValNat p j := by
      intro hle2
      exact hjnot2 ((padicValNat_dvd_iff_le (p := p) hjne).2 hle2)
    omega
  have hA0div : p ∣ Nat.choose (M + j - 1) (M - 1) := by
    have h := choose_adjacent_dvd_of_M_dvd_oeis_361883
      (p := p) (M := M) (j := j) (m := 2) hMpos hjpos hMdiv
    simpa [hvj] using h
  have hpjpos : 0 < p * j := Nat.mul_pos hp0 hjpos
  have hMpdiv3 : p ^ 3 ∣ M * p := by
    rcases hMdiv with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [hu]
    ring
  have hvpj : padicValNat p (p * j) = 2 := by
    have hpjne : p * j ≠ 0 := (Nat.mul_pos hp0 hjpos).ne'
    have hp2dvd : p ^ 2 ∣ p * j := by
      rcases hjdiv with ⟨d, hd⟩
      refine ⟨d, ?_⟩
      rw [hd]
      ring
    have hle2 : 2 ≤ padicValNat p (p * j) :=
      (padicValNat_dvd_iff_le (p := p) hpjne).1 hp2dvd
    have hnle3 : ¬ 3 ≤ padicValNat p (p * j) := by
      intro hle3
      have hp3dvd : p ^ 3 ∣ p * j := (padicValNat_dvd_iff_le (p := p) hpjne).2 hle3
      apply hjnot2
      have hp3eq : p ^ 3 = p * p ^ 2 := by ring
      rw [hp3eq] at hp3dvd
      simpa [Nat.mul_comm] using Nat.dvd_of_mul_dvd_mul_left hp0 hp3dvd
    omega
  have hA1div : p ∣ Nat.choose (M * p + p * j - 1) (M * p - 1) := by
    have h := choose_adjacent_dvd_of_M_dvd_oeis_361883
      (p := p) (M := M * p) (j := p * j) (m := 3)
      (Nat.mul_pos hMpos hp0) hpjpos hMpdiv3
    simpa [hvpj] using h
  have hres := T_diag_nonunit_modEq_r_three_of_adjacent_lift_oeis_361883
    (p := p) (M := M) (j := j) hp0 hMpos hA8 hC7 hA1div hA0div
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hres

/-- Minimal-precision conditional r=3 non-unit diagonal reduction.  The exact `j = 0`
case is discharged.  For `j > 0`, `p^2 ∣ M` and `p ∣ M+j` force `p ∣ j`, the
minimal `p^7` unit-part additivity supplies the two adjacent congruences modulo `p^7`,
and the remaining hypothesis `hlift` is precisely the still-missing polynomial/T-divisibility
step upgrading those adjacent `p^7` congruences to the target `p^9` summand congruence. -/
lemma T_diag_nonunit_modEq_r_three_of_unitPartProd_add_p7_and_adjacent_lift_oeis_361883
    {p M j : ℕ} [Fact p.Prime]
    (_hp5 : 5 ≤ p) (hMpos : 0 < M) (hMdiv : p ^ 2 ∣ M) (hpdiv : p ∣ M + j)
    (hU : let R := ZMod (p ^ 7)
      ((unitPartProd_oeis_361883 p (M + j) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p M : ℕ) : R) *
          ((unitPartProd_oeis_361883 p j : ℕ) : R))
    (hlift :
      Nat.choose (M * p + p * j - 1) (M * p - 1) ≡
          Nat.choose (M + j - 1) (M - 1) [MOD p ^ 7] →
      Nat.choose (M * p + p * j - 1) (M * p) ≡
          Nat.choose (M + j - 1) M [MOD p ^ 7] →
      oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ 9]) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ 9] := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  by_cases hjzero : j = 0
  · subst j
    simpa using T_diag_zero_modEq_oeis_361883 (p := p) (M := M) (r := 3) hMpos hp0
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
    have hpM : p ∣ M := by
      exact (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hMdiv
    have _hjdiv : p ∣ j := by
      simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hpdiv hpM
    refine hlift ?_ ?_
    · have h := choose_mul_sub_one_modEq_p7_of_unitPartProd_add_oeis_361883
        (p := p) (B := M) (C := j) hp hMpos hU
      simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc] using h
    · have h := choose_mul_sub_one_right_modEq_p7_of_unitPartProd_add_oeis_361883
        (p := p) (B := M) (C := j) hp hjpos hU
      simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc] using h

/-- The r=3 non-unit diagonal summand is reduced to the suggested missing p^9
unit-part multiplicativity for the split `M + j`, with `p^2 ∣ M` and `p ∣ j`
forced by `p ∣ M + j`. -/
lemma T_diag_nonunit_modEq_r_three_of_unitPartProd_add_oeis_361883 {p M j : ℕ} [Fact p.Prime]
    (_hp5 : 5 ≤ p) (hMpos : 0 < M) (hMdiv : p ^ 2 ∣ M) (hpdiv : p ∣ M + j)
    (hU : let R := ZMod (p ^ 9)
      ((unitPartProd_oeis_361883 p (M + j) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p M : ℕ) : R) *
          ((unitPartProd_oeis_361883 p j : ℕ) : R)) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ 9] := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  by_cases hjzero : j = 0
  · subst j
    simpa using T_diag_zero_modEq_oeis_361883 (p := p) (M := M) (r := 3) hMpos hp0
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
    have hpM : p ∣ M := by
      exact (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hMdiv
    have hjdiv : p ∣ j := by
      simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hpdiv hpM
    have hdiag := T_diag_mod_pow_of_adjacent_modEq_oeis_361883
      (p := p) (M := M) (r := 3) (j := j) hp0 hMpos
      (by
        have h := choose_mul_sub_one_modEq_p9_of_unitPartProd_add_oeis_361883
          (p := p) (B := M) (C := j) hp hMpos hU
        simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc] using h)
      (by
        have h := choose_mul_sub_one_right_modEq_p9_of_unitPartProd_add_oeis_361883
          (p := p) (B := M) (C := j) hp hjpos hU
        simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc] using h)
    simpa using hdiag


/-- The `r = 3` non-unit diagonal congruence in the subcase where the right index is also
`p^2`-divisible, using the p^9 unit-part multiplicativity proved by grouping into `p^3`
superblocks. -/
lemma T_diag_nonunit_modEq_r_three_of_p2_dvd_right_oeis_361883 {p M j : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hMpos : 0 < M) (hMdiv : p ^ 2 ∣ M) (hpdiv : p ∣ M + j)
    (hjdiv2 : p ^ 2 ∣ j) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ 9] := by
  have hp : p.Prime := Fact.out
  exact T_diag_nonunit_modEq_r_three_of_unitPartProd_add_oeis_361883
    (p := p) (M := M) (j := j) hp5 hMpos hMdiv hpdiv
    (unitPartProd_zmod_p9_add_of_p2_dvd_both_oeis_361883
      (p := p) (B := M) (C := j) hp hp5 hMdiv hjdiv2)


/-- The unconditional `r = 3` non-unit diagonal congruence.  Since `p^2 ∣ M`,
`p ∣ M + j` forces `p ∣ j`; the two proved non-unit subcases then split on
whether `j` is itself `p^2`-divisible. -/
lemma T_diag_nonunit_modEq_r_three_oeis_361883 {p M j : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hMpos : 0 < M) (hMdiv : p ^ 2 ∣ M) (hpdiv : p ∣ M + j) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ 9] := by
  have hpM : p ∣ M := by
    exact (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hMdiv
  have hjdiv : p ∣ j := by
    simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hpdiv hpM
  by_cases hjdiv2 : p ^ 2 ∣ j
  · exact T_diag_nonunit_modEq_r_three_of_p2_dvd_right_oeis_361883
      (p := p) (M := M) (j := j) hp5 hMpos hMdiv hpdiv hjdiv2
  · exact T_diag_nonunit_modEq_r_three_of_p_dvd_not_p2_dvd_right_oeis_361883
      (p := p) (M := M) (j := j) hp5 hMpos hMdiv hjdiv hjdiv2

/-- The unconditional diagonal contribution congruence at level `r = 3`.  Unit
terms are handled by the general unit diagonal theorem; non-unit terms use the
unconditional `r = 3` non-unit diagonal congruence above. -/
lemma diag_sum_modEq_r_three_oeis_361883 {p M : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hMpos : 0 < M) (hMdiv : p ^ 2 ∣ M) :
    (Finset.sum (Finset.range (M + 1)) fun j => oeis_361883_T (M * p) (p * j)) ≡
      a M [MOD p ^ 9] := by
  refine diag_sum_modEq_of_pointwise_oeis_361883 (p := p) (M := M) (r := 3) hMpos ?_
  intro j _hj
  by_cases hunit : ¬ p ∣ M + j
  · exact T_diag_unit_modEq_general_oeis_361883
      (p := p) (M := M) (r := 3) (j := j) hp5 (by norm_num) hMpos (by simpa using hMdiv) hunit
  · exact T_diag_nonunit_modEq_r_three_oeis_361883
      (p := p) (M := M) (j := j) hp5 hMpos hMdiv (not_not.mp hunit)

/-- Diagonal r=3 contribution, with the unit case proved unconditionally and the non-unit
case reduced pointwise to p^9 unit-part multiplicativity for the relevant split. -/
lemma diag_sum_modEq_r_three_of_nonunit_unitPartProd_add_oeis_361883 {p M : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hMpos : 0 < M) (hMdiv : p ^ 2 ∣ M)
    (hU_nonunit : ∀ j, j ∈ Finset.range (M + 1) → p ∣ M + j →
      let R := ZMod (p ^ 9)
      ((unitPartProd_oeis_361883 p (M + j) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p M : ℕ) : R) *
          ((unitPartProd_oeis_361883 p j : ℕ) : R)) :
    (Finset.sum (Finset.range (M + 1)) fun j => oeis_361883_T (M * p) (p * j)) ≡
      a M [MOD p ^ 9] := by
  refine diag_sum_modEq_of_pointwise_oeis_361883 (p := p) (M := M) (r := 3) hMpos ?_
  intro j hj
  by_cases hunit : ¬ p ∣ M + j
  · have h := T_diag_unit_modEq_general_oeis_361883
      (p := p) (M := M) (r := 3) (j := j) hp5 (by norm_num) hMpos (by simpa using hMdiv) hunit
    simpa using h
  · have hpdiv : p ∣ M + j := not_not.mp hunit
    have h := T_diag_nonunit_modEq_r_three_of_unitPartProd_add_oeis_361883
      (p := p) (M := M) (j := j) hp5 hMpos hMdiv hpdiv (hU_nonunit j hj hpdiv)
    simpa using h

/-- A focused r=3 one-step theorem.  The unit diagonal part is discharged by the existing
general theorem; the two remaining hypotheses are exactly the non-unit diagonal p^9
unit-part multiplicativity and the off-diagonal weighted moment modulo `p^3` (expressed as
`p^6` killing the moment in `ZMod (p^9)`). -/
lemma oeis_361883_conjecture_0_r_three_of_nonunit_unitPartProd_add_and_offdiag_moment
    {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n)
    (hUdiag :
      let M := n * p ^ 2
      ∀ j, j ∈ Finset.range (M + 1) → p ∣ M + j →
        let R := ZMod (p ^ 9)
        ((unitPartProd_oeis_361883 p (M + j) : ℕ) : R) =
          ((unitPartProd_oeis_361883 p M : ℕ) : R) *
            ((unitPartProd_oeis_361883 p j : ℕ) : R))
    (hoffmoment :
      let M := n * p ^ 2
      let R := ZMod (p ^ 9)
      ((p ^ 6 : ℕ) : R) *
        (∑ j ∈ Finset.range M,
          let D := Nat.choose (M * p + p * j) (M * p)
          (D : R) ^ 3 *
            (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
              ((p * j + t : R)⁻¹) ^ 2)) = 0) :
    a (n * p ^ 3) ≡ a (n * p ^ 2) [MOD p ^ 9] := by
  haveI : Fact p.Prime := ⟨hp⟩
  let M := n * p ^ 2
  have hp0 : 0 < p := hp.pos
  have hMpos : 0 < M := Nat.mul_pos hn (pow_pos hp0 2)
  have hMdiv : p ^ 2 ∣ M := by
    dsimp [M]
    exact dvd_mul_left (p ^ 2) n
  have hdiag :
      (Finset.sum (Finset.range (M + 1)) fun j => oeis_361883_T (M * p) (p * j)) ≡
        a M [MOD p ^ (3 * 3)] := by
    have h := diag_sum_modEq_r_three_of_nonunit_unitPartProd_add_oeis_361883
      (p := p) (M := M) hp5 hMpos hMdiv (by simpa [M] using hUdiag)
    simpa using h
  have hoff :
      (Finset.sum (Finset.range M) fun j =>
        Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
          oeis_361883_T (M * p) (p * j + t)) ≡ 0 [MOD p ^ (3 * 3)] := by
    refine offdiag_global_modEq_zero_general_of_weighted_zmod_pPow_mul_eq_zero_oeis_361883
      (p := p) (M := M) (r := 3) hp hp5 (by norm_num) hMpos (by simpa using hMdiv) ?_
    dsimp
    simpa [M] using hoffmoment
  have hstep := oeis_361883_step_of_diag_offdiag (p := p) (M := M) (r := 3) hMpos hp0 hdiag hoff
  have hreindex : a (n * p ^ 3) = a (M * p) := by
    dsimp [M]
    ring_nf
  have htarget : a (n * p ^ 2) = a M := by
    dsimp [M]
  rw [hreindex, htarget]
  simpa using hstep


/-- The conjectured supercongruence at the first level `r = 1`. -/
lemma oeis_361883_conjecture_0_r_one {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) :
    a (n * p) ≡ a n [MOD p ^ 3] := by
  have hp0 : 0 < p := hp.pos
  have hdiag := diag_sum_modEq_r_one_oeis_361883 (p := p) (M := n) hp hp5 hn
  have hoff := offdiag_global_modEq_zero_r_one_oeis_361883 (p := p) (M := n) hp hp5 hn
  have hstep := oeis_361883_step_of_diag_offdiag (p := p) (M := n) (r := 1) hn hp0
    (by simpa using hdiag) (by simpa using hoff)
  simpa using hstep


/-- The full one-step congruence at the second level `r = 2`. -/
lemma oeis_361883_conjecture_0_r_two {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) :
    a (n * p ^ 2) ≡ a (n * p) [MOD p ^ 6] := by
  haveI : Fact p.Prime := ⟨hp⟩
  let M := n * p
  have hp0 : 0 < p := hp.pos
  have hMpos : 0 < M := Nat.mul_pos hn hp0
  have hMdiv : p ∣ M := by
    dsimp [M]
    exact dvd_mul_left p n
  have hdiag :
      (Finset.sum (Finset.range (M + 1)) fun j => oeis_361883_T (M * p) (p * j)) ≡
        a M [MOD p ^ (3 * 2)] := by
    refine diag_sum_modEq_of_pointwise_oeis_361883 (p := p) (M := M) (r := 2) hMpos ?_
    intro j hj
    by_cases hunit : ¬ p ∣ M + j
    · exact T_diag_unit_modEq_general_oeis_361883
        (p := p) (M := M) (r := 2) (j := j) hp5 (by norm_num) hMpos (by simpa using hMdiv) hunit
    · exact T_diag_nonunit_modEq_r_two_oeis_361883
        (p := p) (M := M) (j := j) hp5 hMpos hMdiv (by simpa using not_not.mp hunit)
  have hoff :
      (Finset.sum (Finset.range M) fun j =>
        Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
          oeis_361883_T (M * p) (p * j + t)) ≡ 0 [MOD p ^ (3 * 2)] := by
    simpa using offdiag_global_modEq_zero_r_two_oeis_361883
      (p := p) (M := M) hp hp5 hMpos hMdiv
  have hstep := oeis_361883_step_of_diag_offdiag (p := p) (M := M) (r := 2) hMpos hp0 hdiag hoff
  have hreindex : a (n * p ^ 2) = a (M * p) := by
    dsimp [M]
    ring_nf
  have htarget : a (n * p) = a M := by
    dsimp [M]
  rw [hreindex, htarget]
  simpa using hstep


/-- The harmonic correction over the first `b` positive integers, in `ZMod (p^2)`.  This is
`∑_{l=1}^b l⁻¹`, indexed as `i + 1` over `range b`. -/
def hb_p2_oeis_361883 (p b : ℕ) : ZMod (p ^ 2) :=
  ∑ i ∈ Finset.range b, (((i + 1 : ℕ) : ZMod (p ^ 2))⁻¹)

/-- In `ZMod (p^2)`, every square of a multiple of `p` is zero. -/
lemma zmod_p2_p_mul_sq_eq_zero_oeis_361883 {p : ℕ} (x : ZMod (p ^ 2)) :
    ((p : ZMod (p ^ 2)) * x) ^ 2 = 0 := by
  let R := ZMod (p ^ 2)
  have hp2zero : ((p ^ 2 : ℕ) : R) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (p ^ 2) (p ^ 2)).2 (dvd_refl _)
  calc
    (((p : R) * x) ^ 2) = x ^ 2 * ((p ^ 2 : ℕ) : R) := by
      rw [pow_two, Nat.cast_pow]
      ring
    _ = 0 := by rw [hp2zero, mul_zero]

/-- In `ZMod (p^2)`, the product of two multiples of `p` is zero. -/
lemma zmod_p2_p_mul_mul_eq_zero_oeis_361883 {p : ℕ} (x y : ZMod (p ^ 2)) :
    ((p : ZMod (p ^ 2)) * x) * ((p : ZMod (p ^ 2)) * y) = 0 := by
  let R := ZMod (p ^ 2)
  have hp2zero : ((p ^ 2 : ℕ) : R) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (p ^ 2) (p ^ 2)).2 (dvd_refl _)
  calc
    ((p : R) * x) * ((p : R) * y) = x * y * ((p ^ 2 : ℕ) : R) := by
      rw [Nat.cast_pow]
      ring
    _ = 0 := by rw [hp2zero, mul_zero]

/-- Products of first-order `p`-perturbations linearize modulo `p^2`. -/
lemma zmod_p2_prod_one_add_p_mul_eq_one_add_p_sum_oeis_361883 {p : ℕ}
    (s : Finset ℕ) (f : ℕ → ZMod (p ^ 2)) :
    (∏ i ∈ s, (1 + (p : ZMod (p ^ 2)) * f i)) =
      1 + (p : ZMod (p ^ 2)) * (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    have hcross : ((p : ZMod (p ^ 2)) * f a) *
        ((p : ZMod (p ^ 2)) * (∑ i ∈ s, f i)) = 0 :=
      zmod_p2_p_mul_mul_eq_zero_oeis_361883 (p := p) (f a) (∑ i ∈ s, f i)
    calc
      (1 + (p : ZMod (p ^ 2)) * f a) *
          (1 + (p : ZMod (p ^ 2)) * (∑ i ∈ s, f i))
          = 1 + (p : ZMod (p ^ 2)) * f a +
              (p : ZMod (p ^ 2)) * (∑ i ∈ s, f i) +
              ((p : ZMod (p ^ 2)) * f a) *
                ((p : ZMod (p ^ 2)) * (∑ i ∈ s, f i)) := by ring
      _ = 1 + (p : ZMod (p ^ 2)) * (f a + ∑ i ∈ s, f i) := by rw [hcross]; ring

/-- The product of the `b` multiple-of-`p` correction factors is governed by `hb`. -/
lemma zmod_p2_prod_one_add_p_mul_N_inv_eq_hb_oeis_361883 {p N b : ℕ} :
    (∏ i ∈ Finset.range b,
        (1 + (p : ZMod (p ^ 2)) * (N : ZMod (p ^ 2)) *
          (((i + 1 : ℕ) : ZMod (p ^ 2))⁻¹))) =
      1 + (p : ZMod (p ^ 2)) * (N : ZMod (p ^ 2)) * hb_p2_oeis_361883 p b := by
  let R := ZMod (p ^ 2)
  have h := zmod_p2_prod_one_add_p_mul_eq_one_add_p_sum_oeis_361883
    (p := p) (s := Finset.range b)
    (f := fun i => (N : R) * (((i + 1 : ℕ) : R)⁻¹))
  dsimp [hb_p2_oeis_361883] at h ⊢
  calc
    (∏ i ∈ Finset.range b,
        (1 + (p : R) * (N : R) * (((i + 1 : ℕ) : R)⁻¹)))
        = ∏ i ∈ Finset.range b,
            (1 + (p : R) * ((N : R) * (((i + 1 : ℕ) : R)⁻¹))) := by
              apply Finset.prod_congr rfl
              intro i hi
              ring
    _ = 1 + (p : R) * (∑ i ∈ Finset.range b, (N : R) * (((i + 1 : ℕ) : R)⁻¹)) := h
    _ = 1 + (p : R) * (N : R) * (∑ i ∈ Finset.range b, (((i + 1 : ℕ) : R)⁻¹)) := by
          rw [← Finset.mul_sum]
          ring


/-- A natural number not divisible by `p` is a unit modulo `p^2`. -/
lemma zmod_p2_natCast_isUnit_of_not_dvd_oeis_361883 {p x : ℕ} (hp : p.Prime)
    (hnot : ¬ p ∣ x) : IsUnit ((x : ℕ) : ZMod (p ^ 2)) := by
  exact (ZMod.isUnit_iff_coprime _ _).2 (hp.coprime_pow_of_not_dvd hnot)

/-- In the top-increment ratio modulo `p^2`, an increment not divisible by `p` contributes
trivially: the `p^2` shifts in numerator and denominator vanish, and the remaining factor is
`i * i⁻¹`. -/
lemma zmod_p2_nonmultiple_top_increment_ratio_eq_one_oeis_361883 {p N q i : ℕ}
    (hp : p.Prime) (hnot : ¬ p ∣ i) :
    let R := ZMod (p ^ 2)
    (((p ^ 2 * (N + q) + i : ℕ) : R) * (((p ^ 2 * q + i : ℕ) : R)⁻¹)) = 1 := by
  intro R
  have hden : ((p ^ 2 * q + i : ℕ) : R) = ((i : ℕ) : R) := by
    have hp2zero : ((p ^ 2 : ℕ) : R) = 0 :=
      (ZMod.natCast_eq_zero_iff (p ^ 2) (p ^ 2)).2 (dvd_refl _)
    rw [Nat.cast_add, Nat.cast_mul, hp2zero, zero_mul, zero_add]
  have hnum : ((p ^ 2 * (N + q) + i : ℕ) : R) = ((i : ℕ) : R) := by
    have hp2zero : ((p ^ 2 : ℕ) : R) = 0 :=
      (ZMod.natCast_eq_zero_iff (p ^ 2) (p ^ 2)).2 (dvd_refl _)
    rw [Nat.cast_add, Nat.cast_mul, hp2zero, zero_mul, zero_add]
  have hunit : IsUnit ((i : ℕ) : R) :=
    zmod_p2_natCast_isUnit_of_not_dvd_oeis_361883 (p := p) hp hnot
  rcases hunit with ⟨u, hu⟩
  have hmul : ((i : ℕ) : R) * (((i : ℕ) : R)⁻¹) = 1 := by
    rw [← hu, ZMod.inv_coe_unit]
    exact Units.mul_inv u
  rw [hden, hnum, hmul]

/-- A multiple-of-`p` top-increment factor has the expected first-order contribution.  This is
the local factor
`(p*(N+q)+l)/(p*q+l) = 1 + p*N/l` in `ZMod (p^2)`, written with inverses of the
unit representatives. -/
lemma zmod_p2_multiple_top_increment_ratio_eq_one_add_oeis_361883 {p N q l : ℕ}
    (hp : p.Prime) (hnot : ¬ p ∣ l) :
    let R := ZMod (p ^ 2)
    (((p * (N + q) + l : ℕ) : R) * (((p * q + l : ℕ) : R)⁻¹)) =
      1 + (p : R) * (N : R) * (((l : ℕ) : R)⁻¹) := by
  intro R
  have hunit_l : IsUnit ((l : ℕ) : R) :=
    zmod_p2_natCast_isUnit_of_not_dvd_oeis_361883 (p := p) hp hnot
  have hnot_den : ¬ p ∣ p * q + l := by
    intro hdiv
    have hpq : p ∣ p * q := dvd_mul_right p q
    have hl : p ∣ l := by
      simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hdiv hpq
    exact hnot hl
  have hunit_den : IsUnit ((p * q + l : ℕ) : R) :=
    zmod_p2_natCast_isUnit_of_not_dvd_oeis_361883 (p := p) hp hnot_den
  rcases hunit_den with ⟨uden, huden⟩
  rcases hunit_l with ⟨ul, hul⟩
  have hden_mul : ((p * q + l : ℕ) : R) * (((p * q + l : ℕ) : R)⁻¹) = 1 := by
    rw [← huden, ZMod.inv_coe_unit]
    exact Units.mul_inv uden
  have hl_mul : ((l : ℕ) : R) * (((l : ℕ) : R)⁻¹) = 1 := by
    rw [← hul, ZMod.inv_coe_unit]
    exact Units.mul_inv ul
  have hp2zero : ((p ^ 2 : ℕ) : R) = 0 :=
    (ZMod.natCast_eq_zero_iff (p ^ 2) (p ^ 2)).2 (dvd_refl _)
  have hpinv_den_eq_l :
      (p : R) * (((p * q + l : ℕ) : R)⁻¹) = (p : R) * (((l : ℕ) : R)⁻¹) := by
    have h1 : ((p * q + l : ℕ) : R) = (p : R) * (q : R) + (l : R) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
    have hcalc : ((l : R) * (((p * q + l : ℕ) : R)⁻¹)) =
        1 - (p : R) * (q : R) * (((p * q + l : ℕ) : R)⁻¹) := by
      calc
        (l : R) * (((p * q + l : ℕ) : R)⁻¹) =
            (((p * q + l : ℕ) : R) - (p : R) * (q : R)) *
              (((p * q + l : ℕ) : R)⁻¹) := by rw [h1]; ring
        _ = 1 - (p : R) * (q : R) * (((p * q + l : ℕ) : R)⁻¹) := by
              rw [sub_mul, hden_mul]
    calc
      (p : R) * (((p * q + l : ℕ) : R)⁻¹)
          = (p : R) * (1 * (((p * q + l : ℕ) : R)⁻¹)) := by ring
      _ = (p : R) * (((l : R) * (((l : ℕ) : R)⁻¹)) *
            (((p * q + l : ℕ) : R)⁻¹)) := by rw [hl_mul]
      _ = (p : R) * ((((l : R) * (((p * q + l : ℕ) : R)⁻¹)) *
            (((l : ℕ) : R)⁻¹))) := by ring
      _ = (p : R) * (((1 - (p : R) * (q : R) * (((p * q + l : ℕ) : R)⁻¹)) *
            (((l : ℕ) : R)⁻¹))) := by rw [hcalc]
      _ = (p : R) * (((l : ℕ) : R)⁻¹) := by
        have hz : ((p : R) * ((p : R) * (q : R) * (((p * q + l : ℕ) : R)⁻¹) *
            (((l : ℕ) : R)⁻¹))) = 0 := by
          calc
            ((p : R) * ((p : R) * (q : R) * (((p * q + l : ℕ) : R)⁻¹) *
                (((l : ℕ) : R)⁻¹)))
                = ((p ^ 2 : ℕ) : R) * ((q : R) * (((p * q + l : ℕ) : R)⁻¹) *
                    (((l : ℕ) : R)⁻¹)) := by
                  rw [Nat.cast_pow]
                  ring
            _ = 0 := by rw [hp2zero, zero_mul]
        calc
          (p : R) * (((1 - (p : R) * (q : R) * (((p * q + l : ℕ) : R)⁻¹)) *
              (((l : ℕ) : R)⁻¹)))
              = (p : R) * (((l : ℕ) : R)⁻¹) -
                  (p : R) * ((p : R) * (q : R) * (((p * q + l : ℕ) : R)⁻¹) *
                    (((l : ℕ) : R)⁻¹)) := by ring
          _ = (p : R) * (((l : ℕ) : R)⁻¹) := by rw [hz, sub_zero]
  calc
    (((p * (N + q) + l : ℕ) : R) * (((p * q + l : ℕ) : R)⁻¹))
        = (((p * q + l : ℕ) : R) + (p : R) * (N : R)) *
            (((p * q + l : ℕ) : R)⁻¹) := by
          norm_num [Nat.cast_add, Nat.cast_mul]
          ring
    _ = 1 + (p : R) * (N : R) * (((p * q + l : ℕ) : R)⁻¹) := by
          rw [add_mul, hden_mul]
    _ = 1 + (N : R) * ((p : R) * (((p * q + l : ℕ) : R)⁻¹)) := by ring
    _ = 1 + (N : R) * ((p : R) * (((l : ℕ) : R)⁻¹)) := by rw [hpinv_den_eq_l]
    _ = 1 + (p : R) * (N : R) * (((l : ℕ) : R)⁻¹) := by ring

/-- Product form of the multiple-of-`p` part of the top-increment ratio.  Under `b < p`, the
multiples encountered are `p, 2p, ..., bp`, and each contributes `1 + p*N/l`; hence the product
is governed by `hb_p2_oeis_361883`. -/
lemma zmod_p2_prod_multiple_top_increment_ratio_eq_hb_oeis_361883 {p N q b : ℕ}
    (hp : p.Prime) (hb : b < p) :
    let R := ZMod (p ^ 2)
    (∏ i ∈ Finset.range b,
        (((p * (N + q) + (i + 1) : ℕ) : R) *
          (((p * q + (i + 1) : ℕ) : R)⁻¹))) =
      1 + (p : R) * (N : R) * hb_p2_oeis_361883 p b := by
  intro R
  calc
    (∏ i ∈ Finset.range b,
        (((p * (N + q) + (i + 1) : ℕ) : R) *
          (((p * q + (i + 1) : ℕ) : R)⁻¹)))
        = ∏ i ∈ Finset.range b,
            (1 + (p : R) * (N : R) * ((((i + 1 : ℕ) : R))⁻¹)) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hi_lt : i + 1 < p := by
            have hib : i < b := Finset.mem_range.mp hi
            omega
          have hnot : ¬ p ∣ i + 1 := Nat.not_dvd_of_pos_of_lt (by omega) hi_lt
          simpa using zmod_p2_multiple_top_increment_ratio_eq_one_add_oeis_361883
            (p := p) (N := N) (q := q) (l := i + 1) hp hnot
    _ = 1 + (p : R) * (N : R) * hb_p2_oeis_361883 p b :=
          zmod_p2_prod_one_add_p_mul_N_inv_eq_hb_oeis_361883 (p := p) (N := N) (b := b)


/-- One top-increment step for a binomial coefficient in `ZMod m`, when the new
complementary denominator is a unit. -/
lemma zmod_choose_top_succ_ratio_oeis_361883 {m A K : ℕ}
    (hunit : IsUnit (((A + 1 - K : ℕ) : ZMod m))) :
    let R := ZMod m
    ((Nat.choose (A + 1) K : ℕ) : R) =
      ((Nat.choose A K : ℕ) : R) * ((A + 1 : ℕ) : R) *
        (((A + 1 - K : ℕ) : R)⁻¹) := by
  intro R
  have hnat := Nat.choose_mul_succ_eq A K
  have hcast : ((Nat.choose A K : ℕ) : R) * ((A + 1 : ℕ) : R) =
      ((Nat.choose (A + 1) K : ℕ) : R) * ((A + 1 - K : ℕ) : R) := by
    simpa [Nat.cast_mul] using congrArg (fun n : ℕ => (n : R)) hnat
  rcases hunit with ⟨u, hu⟩
  have hden : ((A + 1 - K : ℕ) : R) * (((A + 1 - K : ℕ) : R)⁻¹) = 1 := by
    rw [← hu, ZMod.inv_coe_unit]
    exact Units.mul_inv u
  calc
    ((Nat.choose (A + 1) K : ℕ) : R)
        = ((Nat.choose (A + 1) K : ℕ) : R) *
            (((A + 1 - K : ℕ) : R) * (((A + 1 - K : ℕ) : R)⁻¹)) := by
              rw [hden, mul_one]
    _ = (((Nat.choose (A + 1) K : ℕ) : R) * ((A + 1 - K : ℕ) : R)) *
          (((A + 1 - K : ℕ) : R)⁻¹) := by ring
    _ = (((Nat.choose A K : ℕ) : R) * ((A + 1 : ℕ) : R)) *
          (((A + 1 - K : ℕ) : R)⁻¹) := by rw [← hcast]
    _ = ((Nat.choose A K : ℕ) : R) * ((A + 1 : ℕ) : R) *
          (((A + 1 - K : ℕ) : R)⁻¹) := by ring

/-- Product form for adjoining `L` top increments to a binomial coefficient, in a
`ZMod` ring, provided all complementary denominators are units. -/
lemma zmod_choose_top_add_prod_ratio_oeis_361883 {m A K L : ℕ} (hKA : K ≤ A)
    (hunit : ∀ i ∈ Finset.range L, IsUnit (((A - K + (i + 1) : ℕ) : ZMod m))) :
    let R := ZMod m
    ((Nat.choose (A + L) K : ℕ) : R) =
      ((Nat.choose A K : ℕ) : R) *
        (∏ i ∈ Finset.range L,
          (((A + (i + 1) : ℕ) : R) * (((A - K + (i + 1) : ℕ) : R)⁻¹))) := by
  intro R
  induction L with
  | zero => simp
  | succ L ih =>
      have hunitL : IsUnit (((A + L + 1 - K : ℕ) : R)) := by
        have h0 : IsUnit (((A - K + (L + 1) : ℕ) : R)) := hunit L (by simp)
        have heq : A + L + 1 - K = A - K + (L + 1) := by
          rw [show A + L + 1 = A + (L + 1) by omega, Nat.sub_add_comm hKA]
        convert h0 using 1
        exact congrArg (fun n : ℕ => (n : R)) heq
      have hstep := zmod_choose_top_succ_ratio_oeis_361883 (m := m) (A := A + L) (K := K) hunitL
      have ih' : ((Nat.choose (A + L) K : ℕ) : R) =
          ((Nat.choose A K : ℕ) : R) *
            (∏ i ∈ Finset.range L,
              (((A + (i + 1) : ℕ) : R) * (((A - K + (i + 1) : ℕ) : R)⁻¹))) := by
        apply ih
        intro i hi
        exact hunit i (Finset.mem_range.mpr (by
          have hiL := Finset.mem_range.mp hi
          omega))
      dsimp at hstep
      rw [show A + Nat.succ L = A + L + 1 by omega]
      rw [hstep, ih']
      rw [Finset.prod_range_succ]
      have hnum : A + L + 1 = A + (L + 1) := by omega
      have hden : A + (L + 1) - K = A - K + (L + 1) := by
        rw [Nat.sub_add_comm hKA]
      rw [hnum, hden]
      ring

/-- If the bottom index is divisible by `p^2`, adding a low base-`p` digit to a
`p`-multiple top does not change the binomial coefficient modulo `p^2`. -/
lemma zmod_p2_choose_mul_add_small_eq_choose_mul_oeis_361883 {p A B c : ℕ}
    (hp : p.Prime) (hBA : B ≤ A) (hB : p ∣ B) (hc : c < p) :
    let R := ZMod (p ^ 2)
    ((Nat.choose (p * A + c) (p * B) : ℕ) : R) =
      ((Nat.choose (p * A) (p * B) : ℕ) : R) := by
  intro R
  have hprod := zmod_choose_top_add_prod_ratio_oeis_361883
    (m := p ^ 2) (A := p * A) (K := p * B) (L := c) (by nlinarith)
  have hunit : ∀ i ∈ Finset.range c,
      IsUnit (((p * A - p * B + (i + 1) : ℕ) : R)) := by
    intro i hi
    have hi_lt : i + 1 < p := by
      have := Finset.mem_range.mp hi
      omega
    have hnot : ¬ p ∣ p * (A - B) + (i + 1) := by
      intro hdiv
      have hp_part : p ∣ p * (A - B) := dvd_mul_right p (A - B)
      have hi_dvd : p ∣ i + 1 := by
        simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hdiv hp_part
      exact (Nat.not_dvd_of_pos_of_lt (by omega) hi_lt) hi_dvd
    have heq : p * A - p * B + (i + 1) = p * (A - B) + (i + 1) := by
      rw [Nat.mul_sub_left_distrib]
    simpa [heq] using zmod_p2_natCast_isUnit_of_not_dvd_oeis_361883 (p := p) hp hnot
  specialize hprod hunit
  dsimp at hprod
  rw [hprod]
  have hprod_one :
      (∏ i ∈ Finset.range c,
          (((p * A + (i + 1) : ℕ) : R) *
            (((p * A - p * B + (i + 1) : ℕ) : R)⁻¹))) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hi_lt : i + 1 < p := by
      have := Finset.mem_range.mp hi
      omega
    have hden_unit : IsUnit (((p * A - p * B + (i + 1) : ℕ) : R)) := hunit i hi
    rcases hden_unit with ⟨u, hu⟩
    have hden_mul : ((p * A - p * B + (i + 1) : ℕ) : R) *
        (((p * A - p * B + (i + 1) : ℕ) : R)⁻¹) = 1 := by
      rw [← hu, ZMod.inv_coe_unit]
      exact Units.mul_inv u
    have hpBzero : ((p * B : ℕ) : R) = 0 := by
      rcases hB with ⟨d, rfl⟩
      rw [show p * (p * d) = p ^ 2 * d by ring]
      simp [Nat.cast_mul]
    have hnum_eq_den : ((p * A + (i + 1) : ℕ) : R) =
        ((p * A - p * B + (i + 1) : ℕ) : R) := by
      have hnat : p * A + (i + 1) = (p * A - p * B + (i + 1)) + p * B := by
        have hle : p * B ≤ p * A := Nat.mul_le_mul_left p hBA
        omega
      rw [hnat, Nat.cast_add, hpBzero, add_zero]
    rw [hnum_eq_den, hden_mul]
  rw [hprod_one, mul_one]

/-- Product formula for adding fewer than `p` top increments to
`choose (p*(N+q)) (p*N)` modulo `p^2`. -/
lemma zmod_p2_choose_p_linear_add_prod_oeis_361883 {p N q b : ℕ}
    (hp : p.Prime) (hb : b < p) :
    let R := ZMod (p ^ 2)
    ((Nat.choose (p * (N + q) + b) (p * N) : ℕ) : R) =
      ((Nat.choose (p * (N + q)) (p * N) : ℕ) : R) *
        (∏ i ∈ Finset.range b,
          (((p * (N + q) + (i + 1) : ℕ) : R) *
            (((p * q + (i + 1) : ℕ) : R)⁻¹))) := by
  intro R
  have hprod := zmod_choose_top_add_prod_ratio_oeis_361883
    (m := p ^ 2) (A := p * (N + q)) (K := p * N) (L := b) (by nlinarith)
  have hunit : ∀ i ∈ Finset.range b,
      IsUnit (((p * (N + q) - p * N + (i + 1) : ℕ) : R)) := by
    intro i hi
    have hi_lt : i + 1 < p := by
      have := Finset.mem_range.mp hi
      omega
    have hnot : ¬ p ∣ p * q + (i + 1) := by
      intro hdiv
      have hpq : p ∣ p * q := dvd_mul_right p q
      have hi_dvd : p ∣ i + 1 := by
        simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hdiv hpq
      exact (Nat.not_dvd_of_pos_of_lt (by omega) hi_lt) hi_dvd
    have heq : p * (N + q) - p * N + (i + 1) = p * q + (i + 1) := by
      rw [show p * (N + q) = p * N + p * q by ring, Nat.add_sub_cancel_left]
    simpa [heq] using zmod_p2_natCast_isUnit_of_not_dvd_oeis_361883 (p := p) hp hnot
  specialize hprod hunit
  dsimp at hprod
  rw [hprod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hden : p * (N + q) - p * N + (i + 1) = p * q + (i + 1) := by
    rw [show p * (N + q) = p * N + p * q by ring, Nat.add_sub_cancel_left]
  rw [hden]

/-- The explicit top-increment product identity needed for the `r = 3` off-diagonal
linearization.  The low `p*c` part disappears modulo `p^2`; the `b` multiples of
`p^2` give exactly the displayed factors after one cancellation of `p`. -/
lemma hprod_r_three_offdiag_increment_product_oeis_361883 {p N q b c : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (hb : b < p) (hc : c < p) :
    let R := ZMod (p ^ 2)
    ((Nat.choose (p ^ 3 * N + p ^ 3 * q + p ^ 2 * b + p * c) (p ^ 3 * N) : ℕ) : R) =
      ((Nat.choose (p ^ 3 * (N + q)) (p ^ 3 * N) : ℕ) : R) *
        (∏ i ∈ Finset.range b,
          (((p * (N + q) + (i + 1) : ℕ) : R) *
            (((p * q + (i + 1) : ℕ) : R)⁻¹))) := by
  intro R
  have hp : p.Prime := Fact.out
  let A1 := p ^ 2 * (N + q) + p * b + c
  let B1 := p ^ 2 * N
  have hred1mod : Nat.choose (p * A1) (p * B1) ≡ Nat.choose A1 B1 [MOD p ^ 2] := by
    have hraw := choose_mul_mul_modEq_of_right_dvd_oeis_361883
      (p := p) (A := A1) (B := B1) (s := 2) hp hp5 (by dsimp [B1]; exact dvd_mul_right (p ^ 2) N)
    exact hraw.of_dvd (pow_dvd_pow p (by norm_num : 2 ≤ 2 + 2))
  have hred1 : ((Nat.choose (p ^ 3 * N + p ^ 3 * q + p ^ 2 * b + p * c) (p ^ 3 * N) : ℕ) : R) =
      ((Nat.choose A1 B1 : ℕ) : R) := by
    have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).2 hred1mod
    dsimp [A1, B1] at hcast ⊢
    convert hcast using 1 <;> ring_nf
  have hdropc : ((Nat.choose A1 B1 : ℕ) : R) =
      ((Nat.choose (p * (p * (N + q) + b)) (p * (p * N)) : ℕ) : R) := by
    have h := zmod_p2_choose_mul_add_small_eq_choose_mul_oeis_361883
      (p := p) (A := p * (N + q) + b) (B := p * N) (c := c) hp (by nlinarith)
      (dvd_mul_right p N) hc
    dsimp at h
    dsimp [A1, B1]
    convert h using 1 <;> ring_nf
  have hscalemod : Nat.choose (p * (p * (N + q) + b)) (p * (p * N)) ≡
      Nat.choose (p * (N + q) + b) (p * N) [MOD p ^ 2] := by
    have hraw := choose_mul_mul_modEq_of_right_dvd_oeis_361883
      (p := p) (A := p * (N + q) + b) (B := p * N) (s := 1)
      hp hp5 (by simpa using (dvd_mul_right p N : p ∣ p * N))
    exact hraw.of_dvd (pow_dvd_pow p (by norm_num : 2 ≤ 1 + 2))
  have hscale : ((Nat.choose (p * (p * (N + q) + b)) (p * (p * N)) : ℕ) : R) =
      ((Nat.choose (p * (N + q) + b) (p * N) : ℕ) : R) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hscalemod

  have hprodlin := zmod_p2_choose_p_linear_add_prod_oeis_361883
    (p := p) (N := N) (q := q) (b := b) hp hb
  dsimp at hprodlin
  have hcentralmod : Nat.choose (p * (p ^ 2 * (N + q))) (p * (p ^ 2 * N)) ≡
      Nat.choose (p ^ 2 * (N + q)) (p ^ 2 * N) [MOD p ^ 2] := by
    have hraw := choose_mul_mul_modEq_of_right_dvd_oeis_361883
      (p := p) (A := p ^ 2 * (N + q)) (B := p ^ 2 * N) (s := 2)
      hp hp5 (dvd_mul_right (p ^ 2) N)
    exact hraw.of_dvd (pow_dvd_pow p (by norm_num : 2 ≤ 2 + 2))
  have hcentral_p2 : ((Nat.choose (p ^ 3 * (N + q)) (p ^ 3 * N) : ℕ) : R) =
      ((Nat.choose (p * (p * (N + q))) (p * (p * N)) : ℕ) : R) := by
    have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).2 hcentralmod
    convert hcast using 1 <;> ring_nf
  have hcentralmod2 : Nat.choose (p * (p * (N + q))) (p * (p * N)) ≡
      Nat.choose (p * (N + q)) (p * N) [MOD p ^ 2] := by
    have hraw := choose_mul_mul_modEq_of_right_dvd_oeis_361883
      (p := p) (A := p * (N + q)) (B := p * N) (s := 1)
      hp hp5 (by simpa using (dvd_mul_right p N : p ∣ p * N))
    exact hraw.of_dvd (pow_dvd_pow p (by norm_num : 2 ≤ 1 + 2))
  have hcentral_p1 : ((Nat.choose (p * (p * (N + q))) (p * (p * N)) : ℕ) : R) =
      ((Nat.choose (p * (N + q)) (p * N) : ℕ) : R) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hcentralmod2
  have hcentral : ((Nat.choose (p ^ 3 * (N + q)) (p ^ 3 * N) : ℕ) : R) =
      ((Nat.choose (p * (N + q)) (p * N) : ℕ) : R) := by
    rw [hcentral_p2, hcentral_p1]
  calc
    ((Nat.choose (p ^ 3 * N + p ^ 3 * q + p ^ 2 * b + p * c) (p ^ 3 * N) : ℕ) : R)
        = ((Nat.choose A1 B1 : ℕ) : R) := hred1
    _ = ((Nat.choose (p * (p * (N + q) + b)) (p * (p * N)) : ℕ) : R) := hdropc
    _ = ((Nat.choose (p * (N + q) + b) (p * N) : ℕ) : R) := hscale
    _ = ((Nat.choose (p * (N + q)) (p * N) : ℕ) : R) *
        (∏ i ∈ Finset.range b,
          (((p * (N + q) + (i + 1) : ℕ) : R) *
            (((p * q + (i + 1) : ℕ) : R)⁻¹))) := hprodlin
    _ = ((Nat.choose (p ^ 3 * (N + q)) (p ^ 3 * N) : ℕ) : R) *
        (∏ i ∈ Finset.range b,
          (((p * (N + q) + (i + 1) : ℕ) : R) *
            (((p * q + (i + 1) : ℕ) : R)⁻¹))) := by
          rw [hcentral]

/-- Cubing `1 + p*x` in `ZMod (p^2)` keeps only the linear term. -/
lemma zmod_p2_cube_one_add_p_mul_oeis_361883 {p : ℕ} (x : ZMod (p ^ 2)) :
    (1 + (p : ZMod (p ^ 2)) * x) ^ 3 = 1 + 3 * (p : ZMod (p ^ 2)) * x := by
  let R := ZMod (p ^ 2)
  have hsq : (((p : R) * x) ^ 2) = 0 := zmod_p2_p_mul_sq_eq_zero_oeis_361883 (p := p) x
  have hcube : (((p : R) * x) ^ 3) = 0 := by
    rw [show (((p : R) * x) ^ 3) = ((p : R) * x) ^ 2 * ((p : R) * x) by ring]
    rw [hsq, zero_mul]
  calc
    (1 + (p : R) * x) ^ 3 = 1 + 3 * ((p : R) * x) + 3 * (((p : R) * x) ^ 2) + (((p : R) * x) ^ 3) := by ring
    _ = 1 + 3 * (p : R) * x := by rw [hsq, hcube]; ring

/-- If a binomial factor has the expected first-order form, then its cube has the expansion
needed for the `r = 3` off-diagonal moment. -/
lemma zmod_p2_cube_of_linear_perturbation_oeis_361883 {p : ℕ}
    (C D x : ZMod (p ^ 2))
    (hD : D = C * (1 + (p : ZMod (p ^ 2)) * x)) :
    D ^ 3 = C ^ 3 * (1 + 3 * (p : ZMod (p ^ 2)) * x) := by
  rw [hD, mul_pow]
  rw [zmod_p2_cube_one_add_p_mul_oeis_361883 (p := p) x]

/-- The central part of the `r = 3` off-diagonal binomial factor reduces to the unscaled
coefficient modulo `p^2`. -/
lemma central_binomial_p3_mod_p2_r_three_offdiag_oeis_361883 {p N q : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) :
    ((Nat.choose (p ^ 3 * (N + q)) (p ^ 3 * N) : ℕ) : ZMod (p ^ 2)) =
      ((Nat.choose (N + q) N : ℕ) : ZMod (p ^ 2)) := by
  have hp : p.Prime := Fact.out
  let R := ZMod (p ^ 2)
  have h1mod : Nat.choose (p ^ 3 * (N + q)) (p ^ 3 * N) ≡
      Nat.choose (p ^ 2 * (N + q)) (p ^ 2 * N) [MOD p ^ 2] := by
    have hraw := choose_mul_mul_modEq_of_right_dvd_oeis_361883
      (p := p) (A := p ^ 2 * (N + q)) (B := p ^ 2 * N) (s := 2)
      hp hp5 (dvd_mul_right (p ^ 2) N)
    have hdiv : p ^ 2 ∣ p ^ (2 + 2) := pow_dvd_pow p (by norm_num : 2 ≤ 2 + 2)
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hraw.of_dvd hdiv
  have h2mod : Nat.choose (p ^ 2 * (N + q)) (p ^ 2 * N) ≡
      Nat.choose (p * (N + q)) (p * N) [MOD p ^ 2] := by
    have hraw := choose_mul_mul_modEq_of_right_dvd_oeis_361883
      (p := p) (A := p * (N + q)) (B := p * N) (s := 1)
      hp hp5 (by simp)
    have hdiv : p ^ 2 ∣ p ^ (1 + 2) := pow_dvd_pow p (by norm_num : 2 ≤ 1 + 2)
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hraw.of_dvd hdiv
  have h3mod : Nat.choose (p * (N + q)) (p * N) ≡
      Nat.choose (N + q) N [MOD p ^ 2] := by
    have hraw := choose_mul_mul_modEq_of_right_dvd_oeis_361883
      (p := p) (A := N + q) (B := N) (s := 0) hp hp5 (one_dvd N)
    simpa using hraw
  have h1 : ((Nat.choose (p ^ 3 * (N + q)) (p ^ 3 * N) : ℕ) : R) =
      ((Nat.choose (p ^ 2 * (N + q)) (p ^ 2 * N) : ℕ) : R) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 h1mod
  have h2 : ((Nat.choose (p ^ 2 * (N + q)) (p ^ 2 * N) : ℕ) : R) =
      ((Nat.choose (p * (N + q)) (p * N) : ℕ) : R) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 h2mod
  have h3 : ((Nat.choose (p * (N + q)) (p * N) : ℕ) : R) =
      ((Nat.choose (N + q) N : ℕ) : R) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 h3mod
  rw [h1, h2, h3]

/-- Bridge from the proved top-increment product ratio to the linear hypothesis
used by `D_cube_expansion_r_three_offdiag_conditional_oeis_361883`. -/
lemma D_linear_hypothesis_r_three_offdiag_of_increment_product_oeis_361883 {p N q b c : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (hb : b < p) (hc : c < p) :
    let R := ZMod (p ^ 2)
    ((Nat.choose (p ^ 3 * N + p ^ 3 * q + p ^ 2 * b + p * c) (p ^ 3 * N) : ℕ) : R) =
      ((Nat.choose (N + q) N : ℕ) : R) *
        (1 + (p : R) * (N : R) * hb_p2_oeis_361883 p b) := by
  intro R
  have hp : p.Prime := Fact.out
  have hcentral := central_binomial_p3_mod_p2_r_three_offdiag_oeis_361883
    (p := p) (N := N) (q := q) hp5
  have hprod := hprod_r_three_offdiag_increment_product_oeis_361883
    (p := p) (N := N) (q := q) (b := b) (c := c) hp5 hb hc
  have hmultiple := zmod_p2_prod_multiple_top_increment_ratio_eq_hb_oeis_361883
    (p := p) (N := N) (q := q) (b := b) hp hb
  dsimp at hprod hmultiple
  rw [hprod, hcentral, hmultiple]


/-- Conditional `r = 3` off-diagonal binomial-cube expansion.  The hypothesis is precisely
the still-local product-ratio calculation: after adjoining the extra top `p^2*b + p*c`, the
binomial differs from the central coefficient by the linear harmonic correction. -/
lemma D_cube_expansion_r_three_offdiag_conditional_oeis_361883 {p N q b c : ℕ}
    (hDlin :
      let R := ZMod (p ^ 2)
      ((Nat.choose (p ^ 3 * N + p ^ 3 * q + p ^ 2 * b + p * c) (p ^ 3 * N) : ℕ) : R) =
        ((Nat.choose (N + q) N : ℕ) : R) *
          (1 + (p : R) * (N : R) * hb_p2_oeis_361883 p b)) :
    let R := ZMod (p ^ 2)
    ((Nat.choose (p ^ 3 * N + p ^ 3 * q + p ^ 2 * b + p * c) (p ^ 3 * N) : ℕ) : R) ^ 3 =
      ((Nat.choose (N + q) N : ℕ) : R) ^ 3 *
        (1 + 3 * (p : R) * (N : R) * hb_p2_oeis_361883 p b) := by
  intro R
  let D : R := ((Nat.choose (p ^ 3 * N + p ^ 3 * q + p ^ 2 * b + p * c) (p ^ 3 * N) : ℕ) : R)
  let C : R := ((Nat.choose (N + q) N : ℕ) : R)
  let x : R := (N : R) * hb_p2_oeis_361883 p b
  have hD : D = C * (1 + (p : R) * x) := by
    dsimp [D, C, x]
    simpa [mul_assoc] using hDlin
  have h := zmod_p2_cube_of_linear_perturbation_oeis_361883 (p := p) C D x hD
  dsimp [D, C, x] at h
  simpa [mul_assoc] using h


/-- Unconditional `r = 3` off-diagonal binomial-cube expansion modulo `p^2`, obtained by
combining the proved linear increment formula with the conditional cube expansion. -/
lemma D_cube_expansion_r_three_offdiag_oeis_361883 {p N q b c : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (hb : b < p) (hc : c < p) :
    let R := ZMod (p ^ 2)
    ((Nat.choose (p ^ 3 * N + p ^ 3 * q + p ^ 2 * b + p * c) (p ^ 3 * N) : ℕ) : R) ^ 3 =
      ((Nat.choose (N + q) N : ℕ) : R) ^ 3 *
        (1 + 3 * (p : R) * (N : R) * hb_p2_oeis_361883 p b) := by
  exact D_cube_expansion_r_three_offdiag_conditional_oeis_361883
    (p := p) (N := N) (q := q) (b := b) (c := c)
    (D_linear_hypothesis_r_three_offdiag_of_increment_product_oeis_361883
      (p := p) (N := N) (q := q) (b := b) (c := c) hp5 hb hc)

/-- In `ZMod (p^3)`, a factor vanishing modulo `p^2` times a factor vanishing modulo `p`
is zero. -/
lemma zmod_p3_mul_eq_zero_of_castHom_p2_eq_zero_of_castHom_p_eq_zero_oeis_361883
    {p : ℕ} (hp : p.Prime) (x y : ZMod (p ^ 3))
    (hx : ZMod.castHom (show p ^ 2 ∣ p ^ 3 by exact pow_dvd_pow p (by norm_num : 2 ≤ 3))
        (ZMod (p ^ 2)) x = 0)
    (hy : ZMod.castHom (show p ∣ p ^ 3 by exact dvd_pow_self p (by norm_num : 3 ≠ 0))
        (ZMod p) y = 0) :
    x * y = 0 := by
  haveI : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val y]
  have hxval0 : ((x.val : ℕ) : ZMod (p ^ 2)) = 0 := by
    simpa [ZMod.castHom_apply] using hx
  have hyval0 : ((y.val : ℕ) : ZMod p) = 0 := by
    simpa [ZMod.castHom_apply] using hy
  have hxdiv : p ^ 2 ∣ x.val := (ZMod.natCast_eq_zero_iff x.val (p ^ 2)).1 hxval0
  have hydiv : p ∣ y.val := (ZMod.natCast_eq_zero_iff y.val p).1 hyval0
  rcases hxdiv with ⟨a, ha⟩
  rcases hydiv with ⟨b, hb⟩
  rw [ha, hb, Nat.cast_mul, Nat.cast_mul]
  have hzero : ((p ^ 3 : ℕ) : ZMod (p ^ 3)) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (p ^ 3) (p ^ 3)).2 (dvd_refl _)
  calc
    (((p ^ 2 : ℕ) : ZMod (p ^ 3)) * (a : ZMod (p ^ 3))) *
        (((p : ℕ) : ZMod (p ^ 3)) * (b : ZMod (p ^ 3)))
        = (a : ZMod (p ^ 3)) * (b : ZMod (p ^ 3)) * ((p ^ 3 : ℕ) : ZMod (p ^ 3)) := by
          rw [show ((p ^ 2 : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) ^ 2 by rw [Nat.cast_pow],
            show ((p ^ 3 : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) ^ 3 by rw [Nat.cast_pow]]
          ring
    _ = 0 := by rw [hzero, mul_zero]

/-- If two coefficients in `ZMod (p^3)` agree after reduction modulo `p^2`, then their
products with a `p`-divisible off-diagonal inverse-square block agree. -/
lemma zmod_p3_coeff_mul_offdiag_inner_eq_of_castHom_p2_eq_oeis_361883 {p j : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (A B : ZMod (p ^ 3))
    (hAB : ZMod.castHom (show p ^ 2 ∣ p ^ 3 by exact pow_dvd_pow p (by norm_num : 2 ≤ 3))
        (ZMod (p ^ 2)) A =
      ZMod.castHom (show p ^ 2 ∣ p ^ 3 by exact pow_dvd_pow p (by norm_num : 2 ≤ 3))
        (ZMod (p ^ 2)) B) :
    let H : ZMod (p ^ 3) :=
      ∑ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * j + t : ZMod (p ^ 3))⁻¹) ^ 2
    A * H = B * H := by
  intro H
  have hdiff : ZMod.castHom (show p ^ 2 ∣ p ^ 3 by exact pow_dvd_pow p (by norm_num : 2 ≤ 3))
        (ZMod (p ^ 2)) (A - B) = 0 := by
    rw [map_sub, hAB, sub_self]
  have hH : ZMod.castHom (show p ∣ p ^ 3 by exact dvd_pow_self p (by norm_num : 3 ≠ 0))
        (ZMod p) H = 0 := by
    simpa [H] using offdiag_inner_inv_sq_zmod_p3_castHom_p_eq_zero_oeis_361883
      (p := p) (j := j) hp hp5
  have hprod : (A - B) * H = 0 :=
    zmod_p3_mul_eq_zero_of_castHom_p2_eq_zero_of_castHom_p_eq_zero_oeis_361883
      (p := p) hp (A - B) H hdiff hH
  calc
    A * H = B * H + (A - B) * H := by ring
    _ = B * H := by rw [hprod, add_zero]

/-- The weighted off-diagonal inverse-square moment for `r = 3` vanishes modulo `p^3`. -/
lemma offdiag_weighted_moment_zmod_p3_zero_r_three_oeis_361883 {p M : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hMdiv : p ^ 2 ∣ M) :
    (∑ j ∈ Finset.range M,
      let D := Nat.choose (M * p + p * j) (M * p)
      ((D : ZMod (p ^ 3)) ^ 3) *
        (∑ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * j + t : ZMod (p ^ 3))⁻¹) ^ 2)) = 0 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let R := ZMod (p ^ 3)
  let S := ZMod (p ^ 2)
  let phi := ZMod.castHom (show p ^ 2 ∣ p ^ 3 by exact pow_dvd_pow p (by norm_num : 2 ≤ 3)) S
  rcases hMdiv with ⟨N, hMN⟩
  subst M
  let H : ℕ → R := fun j =>
    ∑ t ∈ (Finset.range p).filter (fun t => 0 < t), ((p * j + t : R)⁻¹) ^ 2
  let C : ℕ → R := fun q => ((Nat.choose (N + q) N : ℕ) : R) ^ 3
  let B : ℕ → R := fun b => ((hb_p2_oeis_361883 p b).val : R)
  let E : ℕ → ℕ → R := fun q b => C q * (1 + 3 * (p : R) * (N : R) * B b)
  have hB_cast (b : ℕ) : phi (B b) = hb_p2_oeis_361883 p b := by
    have hval : (((hb_p2_oeis_361883 p b).val : S) = hb_p2_oeis_361883 p b) :=
      ZMod.natCast_zmod_val (hb_p2_oeis_361883 p b)
    simpa [B, phi, S, ZMod.castHom_apply] using hval
  have hsuper (q : ℕ) : (∑ b ∈ Finset.range p, ∑ c ∈ Finset.range p, H (p * (p * q + b) + c)) = 0 := by
    have h0 := offdiag_inner_inv_sq_zmod_p3_superblock_eq_zero_oeis_361883
      (p := p) (q := q) hp hp5
    dsimp at h0
    let F : ℕ → R := fun a => H (p ^ 2 * q + a)
    have hdecomp : (∑ a ∈ Finset.range (p ^ 2), F a) =
        ∑ b ∈ Finset.range p, ∑ c ∈ Finset.range p, F (p * b + c) := by
      simpa [pow_two] using (sum_range_mul_decomp_oeis_361883 p p F)
    have hleft : (∑ a ∈ Finset.range (p ^ 2), F a) = 0 := by
      simpa [F, H, R, pow_two, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h0
    have hright : (∑ b ∈ Finset.range p, ∑ c ∈ Finset.range p, F (p * b + c)) = 0 := by
      rw [← hdecomp, hleft]
    calc
      (∑ b ∈ Finset.range p, ∑ c ∈ Finset.range p, H (p * (p * q + b) + c))
          = ∑ b ∈ Finset.range p, ∑ c ∈ Finset.range p, F (p * b + c) := by
            apply Finset.sum_congr rfl
            intro b hbmem
            apply Finset.sum_congr rfl
            intro c hcmem
            dsimp [F]
            congr 1
            ring
      _ = 0 := hright
  have hpblock (q b : ℕ) :
      (p : R) * (∑ c ∈ Finset.range p, H (p * (p * q + b) + c)) = 0 := by
    simpa [H, R, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      offdiag_inner_inv_sq_zmod_p3_p_mul_p_block_eq_zero_oeis_361883
        (p := p) (b := p * q + b) hp hp5
  have hEblock (q : ℕ) :
      (∑ b ∈ Finset.range p, ∑ c ∈ Finset.range p, E q b * H (p * (p * q + b) + c)) = 0 := by
    have hsplit :
        (∑ b ∈ Finset.range p, ∑ c ∈ Finset.range p, E q b * H (p * (p * q + b) + c)) =
          C q * (∑ b ∈ Finset.range p, ∑ c ∈ Finset.range p, H (p * (p * q + b) + c)) +
            ∑ b ∈ Finset.range p,
              (C q * (3 * (p : R) * (N : R) * B b)) *
                (∑ c ∈ Finset.range p, H (p * (p * q + b) + c)) := by
      simp only [E]
      rw [Finset.mul_sum]
      simp only [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b hbmem
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c hcmem
      ring
    rw [hsplit, hsuper q, mul_zero, zero_add]
    apply Finset.sum_eq_zero
    intro b hbmem
    calc
      (C q * (3 * (p : R) * (N : R) * B b)) *
          (∑ c ∈ Finset.range p, H (p * (p * q + b) + c))
          = (C q * (3 * (N : R) * B b)) *
              ((p : R) * (∑ c ∈ Finset.range p, H (p * (p * q + b) + c))) := by ring
      _ = 0 := by rw [hpblock q b, mul_zero]
  have hpoint (q b c : ℕ) (hbmem : b ∈ Finset.range p) (hcmem : c ∈ Finset.range p) :
      let D := Nat.choose ((N * p ^ 2) * p + p * (p * (p * q + b) + c)) ((N * p ^ 2) * p)
      ((D : R) ^ 3) * H (p * (p * q + b) + c) = E q b * H (p * (p * q + b) + c) := by
    intro D
    have hb_lt : b < p := Finset.mem_range.mp hbmem
    have hc_lt : c < p := Finset.mem_range.mp hcmem
    let A : R := (D : R) ^ 3
    let E' : R := E q b
    have htop : (N * p ^ 2) * p + p * (p * (p * q + b) + c) =
        p ^ 3 * N + p ^ 3 * q + p ^ 2 * b + p * c := by ring
    have hbot : (N * p ^ 2) * p = p ^ 3 * N := by ring
    have hAB : phi A = phi E' := by
      have hexp := D_cube_expansion_r_three_offdiag_oeis_361883
        (p := p) (N := N) (q := q) (b := b) (c := c) hp5 hb_lt hc_lt
      dsimp at hexp
      dsimp [A, E']
      change phi (((Nat.choose ((N * p ^ 2) * p + p * (p * (p * q + b) + c)) ((N * p ^ 2) * p) : R) ^ 3)) = phi (E q b)
      rw [htop, hbot]
      rw [map_pow]
      calc
        (phi (((Nat.choose (p ^ 3 * N + p ^ 3 * q + p ^ 2 * b + p * c) (p ^ 3 * N) : ℕ) : R))) ^ 3
            = (((Nat.choose (p ^ 3 * N + p ^ 3 * q + p ^ 2 * b + p * c) (p ^ 3 * N) : ℕ) : S) ^ 3) := by
              simp [phi]
        _ = ((Nat.choose (N + q) N : ℕ) : S) ^ 3 *
                (1 + 3 * (p : S) * (N : S) * hb_p2_oeis_361883 p b) := hexp
        _ = phi (E q b) := by
          have hphi3 : phi (3 : R) = (3 : S) := by exact map_ofNat phi 3
          simp [E, C, hB_cast b, hphi3, map_mul, map_add, map_pow]
    exact zmod_p3_coeff_mul_offdiag_inner_eq_of_castHom_p2_eq_oeis_361883
      (p := p) (j := p * (p * q + b) + c) hp hp5 A E' hAB
  change (∑ j ∈ Finset.range (p ^ 2 * N),
      ((Nat.choose ((p ^ 2 * N) * p + p * j) ((p ^ 2 * N) * p) : R) ^ 3) * H j) = 0
  rw [Nat.mul_comm (p ^ 2) N]
  rw [sum_range_mul_decomp_oeis_361883 N (p ^ 2)
    (fun j => ((Nat.choose ((N * p ^ 2) * p + p * j) ((N * p ^ 2) * p) : R) ^ 3) * H j)]
  apply Finset.sum_eq_zero
  intro q hq
  have hinner_decomp :
      (∑ a ∈ Finset.range (p ^ 2),
        ((Nat.choose ((N * p ^ 2) * p + p * (p ^ 2 * q + a)) ((N * p ^ 2) * p) : R) ^ 3) * H (p ^ 2 * q + a)) =
      ∑ b ∈ Finset.range p, ∑ c ∈ Finset.range p,
        ((Nat.choose ((N * p ^ 2) * p + p * (p * (p * q + b) + c)) ((N * p ^ 2) * p) : R) ^ 3) *
          H (p * (p * q + b) + c) := by
    let G : ℕ → R := fun a =>
      ((Nat.choose ((N * p ^ 2) * p + p * (p ^ 2 * q + a)) ((N * p ^ 2) * p) : R) ^ 3) * H (p ^ 2 * q + a)
    have hdec := sum_range_mul_decomp_oeis_361883 p p G
    calc
      (∑ a ∈ Finset.range (p ^ 2),
        ((Nat.choose ((N * p ^ 2) * p + p * (p ^ 2 * q + a)) ((N * p ^ 2) * p) : R) ^ 3) * H (p ^ 2 * q + a))
          = ∑ a ∈ Finset.range (p ^ 2), G a := rfl
      _ = ∑ b ∈ Finset.range p, ∑ c ∈ Finset.range p, G (p * b + c) := by
          simpa [pow_two] using hdec
      _ = ∑ b ∈ Finset.range p, ∑ c ∈ Finset.range p,
        ((Nat.choose ((N * p ^ 2) * p + p * (p * (p * q + b) + c)) ((N * p ^ 2) * p) : R) ^ 3) *
          H (p * (p * q + b) + c) := by
          apply Finset.sum_congr rfl
          intro b hbmem
          apply Finset.sum_congr rfl
          intro c hcmem
          dsimp [G]
          have hidx : p ^ 2 * q + (p * b + c) = p * (p * q + b) + c := by ring
          rw [hidx]
  rw [hinner_decomp]
  calc
    (∑ b ∈ Finset.range p, ∑ c ∈ Finset.range p,
      ((Nat.choose ((N * p ^ 2) * p + p * (p * (p * q + b) + c)) ((N * p ^ 2) * p) : R) ^ 3) *
        H (p * (p * q + b) + c))
        = ∑ b ∈ Finset.range p, ∑ c ∈ Finset.range p, E q b * H (p * (p * q + b) + c) := by
          apply Finset.sum_congr rfl
          intro b hbmem
          apply Finset.sum_congr rfl
          intro c hcmem
          simpa using hpoint q b c hbmem hcmem
    _ = 0 := hEblock q


/-- The full off-diagonal contribution vanishes at the third level `r = 3`. -/
lemma offdiag_global_modEq_zero_r_three_oeis_361883 {p M : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hMpos : 0 < M) (hMdiv : p ^ 2 ∣ M) :
    (Finset.sum (Finset.range M) fun j =>
      Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
        oeis_361883_T (M * p) (p * j + t)) ≡ 0 [MOD p ^ 9] := by
  refine offdiag_global_modEq_zero_r_three_of_weighted_moment_zmod_p3_oeis_361883
    (p := p) (M := M) hp hp5 hMpos hMdiv ?_
  exact offdiag_weighted_moment_zmod_p3_zero_r_three_oeis_361883
    (p := p) (M := M) hp hp5 hMdiv

/-- The full one-step congruence at the third level `r = 3`. -/
lemma oeis_361883_conjecture_0_r_three {p n : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) :
    a (n * p ^ 3) ≡ a (n * p ^ 2) [MOD p ^ 9] := by
  haveI : Fact p.Prime := ⟨hp⟩
  let M := n * p ^ 2
  have hp0 : 0 < p := hp.pos
  have hMpos : 0 < M := Nat.mul_pos hn (pow_pos hp0 2)
  have hMdiv : p ^ 2 ∣ M := by
    dsimp [M]
    exact dvd_mul_left (p ^ 2) n
  have hdiag :
      (Finset.sum (Finset.range (M + 1)) fun j => oeis_361883_T (M * p) (p * j)) ≡
        a M [MOD p ^ (3 * 3)] := by
    have h := diag_sum_modEq_r_three_oeis_361883 (p := p) (M := M) hp5 hMpos hMdiv
    simpa using h
  have hoff :
      (Finset.sum (Finset.range M) fun j =>
        Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
          oeis_361883_T (M * p) (p * j + t)) ≡ 0 [MOD p ^ (3 * 3)] := by
    have h := offdiag_global_modEq_zero_r_three_oeis_361883 (p := p) (M := M) hp hp5 hMpos hMdiv
    simpa using h
  have hstep := oeis_361883_step_of_diag_offdiag (p := p) (M := M) (r := 3) hMpos hp0 hdiag hoff
  have hreindex : a (n * p ^ 3) = a (M * p) := by
    dsimp [M]
    ring_nf
  have htarget : a (n * p ^ 2) = a M := by
    dsimp [M]
  rw [hreindex, htarget]
  simpa using hstep



lemma zmod_pPow_complement_mul_eq_zero_of_castHom_eq_zero_oeis_361883 {p r k : ℕ}
    (hp : p.Prime) (hkr : k ≤ r) (x : ZMod (p ^ r))
    (hx : ZMod.castHom (show p ^ k ∣ p ^ r by exact pow_dvd_pow p hkr) (ZMod (p ^ k)) x = 0) :
    (p ^ (r - k) : ZMod (p ^ r)) * x = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x]
  have hxval0 : ((x.val : ℕ) : ZMod (p ^ k)) = 0 := by
    simpa [ZMod.castHom_apply] using hx
  have hxdiv : p ^ k ∣ x.val := (ZMod.natCast_eq_zero_iff x.val (p ^ k)).1 hxval0
  rcases hxdiv with ⟨y, hy⟩
  rw [hy, Nat.cast_mul]
  rw [← Nat.cast_pow]

  have hzero : ((p ^ r : ℕ) : ZMod (p ^ r)) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (p ^ r) (p ^ r)).2 (dvd_refl _)
  have hexp : r - k + k = r := Nat.sub_add_cancel hkr
  have hpows : ((p ^ (r - k) : ℕ) : ZMod (p ^ r)) * ((p ^ k : ℕ) : ZMod (p ^ r)) =
      ((p ^ r : ℕ) : ZMod (p ^ r)) := by
    rw [← Nat.cast_mul, ← pow_add, hexp]
  change (((p ^ (r - k) : ℕ) : ZMod (p ^ r)) * (((p ^ k : ℕ) : ZMod (p ^ r)) * (y : ZMod (p ^ r)))) = 0

  calc
    (((p ^ (r - k) : ℕ) : ZMod (p ^ r)) * (((p ^ k : ℕ) : ZMod (p ^ r)) * (y : ZMod (p ^ r))))
        = (((p ^ (r - k) : ℕ) : ZMod (p ^ r)) * ((p ^ k : ℕ) : ZMod (p ^ r))) * (y : ZMod (p ^ r)) := by
          ring
    _ = ((p ^ r : ℕ) : ZMod (p ^ r)) * (y : ZMod (p ^ r)) := by rw [hpows]
    _ = 0 := by rw [hzero, zero_mul]

lemma coprime_add_pPow_mul_of_coprime_pPow_oeis_361883 {p k r q x : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hxc : Nat.Coprime x (p ^ k)) :
    Nat.Coprime (p ^ k * q + x) (p ^ r) := by
  have hnotx : ¬ p ∣ x := by
    intro hpx
    have hp_dvd_pk : p ∣ p ^ k := dvd_pow_self p (Nat.ne_of_gt hk)
    have hp_dvd_gcd : p ∣ Nat.gcd x (p ^ k) := Nat.dvd_gcd hpx hp_dvd_pk
    rw [hxc.gcd_eq_one] at hp_dvd_gcd
    exact hp.not_dvd_one hp_dvd_gcd
  have hnot : ¬ p ∣ p ^ k * q + x := by
    intro hdiv
    have hp_dvd_pkq : p ∣ p ^ k * q := by
      have hp_dvd_pk : p ∣ p ^ k := dvd_pow_self p (Nat.ne_of_gt hk)
      exact dvd_mul_of_dvd_left hp_dvd_pk q
    have hpx : p ∣ x := (Nat.dvd_add_iff_right hp_dvd_pkq).2 hdiv
    exact hnotx hpx
  exact hp.coprime_pow_of_not_dvd hnot

lemma zmod_castHom_inv_sq_pPow_shift_oeis_361883 {p r k q x : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hkr : k ≤ r) (hxc : Nat.Coprime x (p ^ k)) :
    let R := ZMod (p ^ r)
    let S := ZMod (p ^ k)
    ZMod.castHom (show p ^ k ∣ p ^ r by exact pow_dvd_pow p hkr) S
      ((((p ^ k * q + x : ℕ) : R)⁻¹) ^ 2) = (((x : S)⁻¹) ^ 2) := by
  intro R S
  let f := ZMod.castHom (show p ^ k ∣ p ^ r by exact pow_dvd_pow p hkr) S
  have hcopR : Nat.Coprime (p ^ k * q + x) (p ^ r) :=
    coprime_add_pPow_mul_of_coprime_pPow_oeis_361883 (p := p) (k := k) (r := r) (q := q) (x := x) hp hk hxc
  let uR : Rˣ := ZMod.unitOfCoprime (p ^ k * q + x) hcopR
  let uS : Sˣ := ZMod.unitOfCoprime x hxc
  have hmapu : Units.map f.toMonoidHom uR = uS := by
    apply Units.ext
    change f ((p ^ k * q + x : ℕ) : R) = (x : S)
    rw [Nat.cast_add, Nat.cast_mul]
    change f (((p ^ k : ℕ) : R) * (q : R) + (x : R)) = (x : S)
    rw [map_add, map_mul]
    have hpk : f (((p ^ k : ℕ) : R)) = 0 := by
      have hpkS : (((p ^ k : ℕ) : S)) = 0 :=
        (ZMod.natCast_eq_zero_iff (p ^ k) (p ^ k)).2 (dvd_refl _)
      rw [ZMod.castHom_apply, ZMod.cast_natCast (show p ^ k ∣ p ^ r by exact pow_dvd_pow p hkr)]
      exact hpkS
    rw [hpk, zero_mul, zero_add]
    simp [f]
  have hmapinv : f ((uR⁻¹ : Rˣ) : R) = ((uS⁻¹ : Sˣ) : S) := by
    calc
      f ((uR⁻¹ : Rˣ) : R) = ((Units.map f.toMonoidHom uR)⁻¹ : Sˣ) := by
        exact (Units.coe_map_inv f.toMonoidHom uR).symm
      _ = ((uS⁻¹ : Sˣ) : S) := by rw [hmapu]
  have hinvR : (((p ^ k * q + x : ℕ) : R)⁻¹) = ((uR⁻¹ : Rˣ) : R) := by
    simpa [uR] using ZMod.inv_coe_unit uR
  have hinvS : ((x : S)⁻¹) = ((uS⁻¹ : Sˣ) : S) := by
    simpa [uS] using ZMod.inv_coe_unit uS
  calc
    f (((((p ^ k * q + x : ℕ) : R)⁻¹) ^ 2)) = (f ((((p ^ k * q + x : ℕ) : R)⁻¹))) ^ 2 := by
      exact map_pow f ((((p ^ k * q + x : ℕ) : R)⁻¹)) 2
    _ = (f ((uR⁻¹ : Rˣ) : R)) ^ 2 := by rw [hinvR]
    _ = (((uS⁻¹ : Sˣ) : S)) ^ 2 := by rw [hmapinv]
    _ = (((x : S)⁻¹) ^ 2) := by rw [hinvS]

lemma unitBlockSq_pPow_complement_kills_oeis_361883 (p r k q : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) (hkr : k ≤ r) :
    let R := ZMod (p ^ r)
    (p ^ (r - k) : R) *
      (∑ x ∈ (Finset.range (p ^ k)).filter (fun x => Nat.Coprime x (p ^ k)),
        ((((p ^ k * q + x : ℕ) : R)⁻¹) ^ 2)) = 0 := by
  intro R
  let S := ZMod (p ^ k)
  let f := ZMod.castHom (show p ^ k ∣ p ^ r by exact pow_dvd_pow p hkr) S
  let U : R := ∑ x ∈ (Finset.range (p ^ k)).filter (fun x => Nat.Coprime x (p ^ k)),
        ((((p ^ k * q + x : ℕ) : R)⁻¹) ^ 2)
  have hmap : f U = 0 := by
    calc
      f U = ∑ x ∈ (Finset.range (p ^ k)).filter (fun x => Nat.Coprime x (p ^ k)),
          (((x : S)⁻¹) ^ 2) := by
            dsimp [U]
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro x hx
            exact zmod_castHom_inv_sq_pPow_shift_oeis_361883
              (p := p) (r := r) (k := k) (q := q) (x := x) hp hk hkr (Finset.mem_filter.mp hx).2
      _ = 0 := by
        simpa [S] using sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p k hp hp5
  simpa [U] using zmod_pPow_complement_mul_eq_zero_of_castHom_eq_zero_oeis_361883
    (p := p) (r := r) (k := k) hp hkr U hmap


lemma zmod_castHom_inv_pPow_shift_oeis_361883 {p r k q x : ℕ}
    (hp : p.Prime) (hk : 0 < k) (hkr : k ≤ r) (hxc : Nat.Coprime x (p ^ k)) :
    let R := ZMod (p ^ r)
    let S := ZMod (p ^ k)
    ZMod.castHom (show p ^ k ∣ p ^ r by exact pow_dvd_pow p hkr) S
      ((((p ^ k * q + x : ℕ) : R)⁻¹)) = (((x : S)⁻¹)) := by
  intro R S
  let f := ZMod.castHom (show p ^ k ∣ p ^ r by exact pow_dvd_pow p hkr) S
  have hcopR : Nat.Coprime (p ^ k * q + x) (p ^ r) :=
    coprime_add_pPow_mul_of_coprime_pPow_oeis_361883 (p := p) (k := k) (r := r) (q := q) (x := x) hp hk hxc
  let uR : Rˣ := ZMod.unitOfCoprime (p ^ k * q + x) hcopR
  let uS : Sˣ := ZMod.unitOfCoprime x hxc
  have hmapu : Units.map f.toMonoidHom uR = uS := by
    apply Units.ext
    change f ((p ^ k * q + x : ℕ) : R) = (x : S)
    rw [Nat.cast_add, Nat.cast_mul]
    change f (((p ^ k : ℕ) : R) * (q : R) + (x : R)) = (x : S)
    rw [map_add, map_mul]
    have hpk : f (((p ^ k : ℕ) : R)) = 0 := by
      have hpkS : (((p ^ k : ℕ) : S)) = 0 :=
        (ZMod.natCast_eq_zero_iff (p ^ k) (p ^ k)).2 (dvd_refl _)
      rw [ZMod.castHom_apply, ZMod.cast_natCast (show p ^ k ∣ p ^ r by exact pow_dvd_pow p hkr)]
      exact hpkS
    rw [hpk, zero_mul, zero_add]
    simp [f]
  have hmapinv : f ((uR⁻¹ : Rˣ) : R) = ((uS⁻¹ : Sˣ) : S) := by
    calc
      f ((uR⁻¹ : Rˣ) : R) = ((Units.map f.toMonoidHom uR)⁻¹ : Sˣ) := by
        exact (Units.coe_map_inv f.toMonoidHom uR).symm
      _ = ((uS⁻¹ : Sˣ) : S) := by rw [hmapu]
  have hinvR : (((p ^ k * q + x : ℕ) : R)⁻¹) = ((uR⁻¹ : Rˣ) : R) := by
    simpa [uR] using ZMod.inv_coe_unit uR
  have hinvS : ((x : S)⁻¹) = ((uS⁻¹ : Sˣ) : S) := by
    simpa [uS] using ZMod.inv_coe_unit uS
  calc
    f ((((p ^ k * q + x : ℕ) : R)⁻¹)) = f ((uR⁻¹ : Rˣ) : R) := by rw [hinvR]
    _ = ((uS⁻¹ : Sˣ) : S) := hmapinv
    _ = ((x : S)⁻¹) := by rw [hinvS]

lemma coprime_pPow_isUnit_zmod_pPow_oeis_361883 {p m r x : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hx : Nat.Coprime x (p ^ m)) :
    IsUnit ((x : ℕ) : ZMod (p ^ r)) := by
  have hxp : Nat.Coprime x p := Nat.Coprime.of_dvd_right
    (dvd_pow_self p (Nat.ne_of_gt hm)) hx
  have hnot : ¬ p ∣ x := (hp.coprime_iff_not_dvd).mp hxp.symm
  exact (ZMod.isUnit_iff_coprime x (p ^ r)).2 (hp.coprime_pow_of_not_dvd hnot)

lemma superblock_pPow_shift_factor_eq_mul_one_add_oeis_361883 {p m b x : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hx : Nat.Coprime x (p ^ m)) :
    (((p ^ m * b + x : ℕ) : ZMod (p ^ (3 * m)))) =
      ((x : ℕ) : ZMod (p ^ (3 * m))) *
        (1 + (((p ^ m * b : ℕ) : ZMod (p ^ (3 * m)))) *
          (((x : ℕ) : ZMod (p ^ (3 * m)))⁻¹)) := by
  let R := ZMod (p ^ (3 * m))
  have hunit : IsUnit ((x : ℕ) : R) :=
    coprime_pPow_isUnit_zmod_pPow_oeis_361883 (p := p) (m := m) (r := 3 * m) hp hm hx
  rcases hunit with ⟨u, hu⟩
  have hmul : ((x : ℕ) : R) * (((x : ℕ) : R)⁻¹) = 1 := by
    rw [← hu, ZMod.inv_coe_unit]
    exact Units.mul_inv u
  change (((p ^ m * b + x : ℕ) : R)) =
      ((x : ℕ) : R) * (1 + (((p ^ m * b : ℕ) : R)) * (((x : ℕ) : R)⁻¹))
  rw [Nat.cast_add]
  calc
    (((p ^ m * b : ℕ) : R) + ((x : ℕ) : R)) =
        ((x : ℕ) : R) + ((p ^ m * b : ℕ) : R) := by ring
    _ = ((x : ℕ) : R) * (1 + (((p ^ m * b : ℕ) : R)) * (((x : ℕ) : R)⁻¹)) := by
      rw [mul_add, mul_one]
      calc
        ((x : ℕ) : R) + ((p ^ m * b : ℕ) : R) =
            ((x : ℕ) : R) + ((p ^ m * b : ℕ) : R) * (((x : ℕ) : R) * (((x : ℕ) : R)⁻¹)) := by
              rw [hmul, mul_one]
        _ = ((x : ℕ) : R) + ((x : ℕ) : R) * (((p ^ m * b : ℕ) : R) * (((x : ℕ) : R)⁻¹)) := by
              ring

lemma unit_superblock_shift_zmod_pow_3m_hS2_oeis_361883 {p m b : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 0 < m) :
  ((((p ^ m * b : ℕ) : ZMod (p ^ (3 * m)))) ^ 2) *
    (∑ x ∈ (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)),
      ∑ y ∈ ((Finset.range (p ^ m)).filter (fun y => Nat.Coprime y (p ^ m))).filter (fun y => y < x),
        (((y : ℕ) : ZMod (p ^ (3 * m)))⁻¹) * (((x : ℕ) : ZMod (p ^ (3 * m)))⁻¹)) = 0 := by
  classical
  let R := ZMod (p ^ (3 * m))
  let S := ZMod (p ^ m)
  let s := (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m))
  let fR : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  let fS : ℕ → S := fun x => (((x : ℕ) : S)⁻¹)
  let E : R := ∑ x ∈ s, ∑ y ∈ s.filter (fun y => y < x), fR y * fR x
  let D : R := ∑ x ∈ s, (fR x) ^ 2
  let A : R := ∑ x ∈ s, fR x
  have hmr : m ≤ 3 * m := by nlinarith [hm]
  let phi := ZMod.castHom (show p ^ m ∣ p ^ (3 * m) by exact pow_dvd_pow p hmr) S
  have hphi_f (x : ℕ) (hxmem : x ∈ s) : phi (fR x) = fS x := by
    have hxc : Nat.Coprime x (p ^ m) := (Finset.mem_filter.mp hxmem).2
    have h := zmod_castHom_inv_pPow_shift_oeis_361883
      (p := p) (r := 3 * m) (k := m) (q := 0) (x := x) hp hm hmr hxc
    simpa [phi, fR, fS, R, S] using h
  have hphi_A : phi A = 0 := by
    calc
      phi A = ∑ x ∈ s, fS x := by
        dsimp [A]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hxmem
        simpa using hphi_f x hxmem
      _ = 0 := by
        dsimp [s, fS, S]
        exact sum_range_coprime_inv_zmod_pow_eq_zero_oeis_361883 p m hp hp5
  have hphi_D : phi D = 0 := by
    calc
      phi D = ∑ x ∈ s, (fS x) ^ 2 := by
        dsimp [D]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hxmem
        rw [map_pow]
        rw [hphi_f x hxmem]
      _ = 0 := by
        dsimp [s, fS, S]
        exact sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p m hp hp5
  have hkill_A_sq : (p ^ (2 * m) : R) * (A ^ 2) = 0 := by
    have hcomp : 3 * m - m = 2 * m := by omega
    rw [← hcomp]
    apply zmod_pPow_complement_mul_eq_zero_of_castHom_eq_zero_oeis_361883 (p := p) (r := 3 * m) (k := m) hp hmr
    rw [map_pow, hphi_A, zero_pow (by norm_num : 2 ≠ 0)]
  have hkill_D : (p ^ (2 * m) : R) * D = 0 := by
    have hcomp : 3 * m - m = 2 * m := by omega
    rw [← hcomp]
    exact zmod_pPow_complement_mul_eq_zero_of_castHom_eq_zero_oeis_361883
      (p := p) (r := 3 * m) (k := m) hp hmr D hphi_D
  have hpair_id : A ^ 2 = D + 2 * E := by
    dsimp [A, D, E, fR, s]
    exact finset_sum_sq_eq_diag_add_two_ordered_pairs_oeis_361883
      ((Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)))
      (fun x => (((x : ℕ) : R)⁻¹))
  have htwo_mul : (2 : R) * ((p ^ (2 * m) : R) * E) = 0 := by
    have hcalc : (p ^ (2 * m) : R) * (A ^ 2) = (p ^ (2 * m) : R) * D + (2 : R) * ((p ^ (2 * m) : R) * E) := by
      rw [hpair_id]
      ring
    have hsub : (p ^ (2 * m) : R) * (A ^ 2) - (p ^ (2 * m) : R) * D = (2 : R) * ((p ^ (2 * m) : R) * E) := by
      rw [hcalc]
      ring
    rw [← hsub, hkill_A_sq, hkill_D]
    ring
  have htwo_unit : IsUnit (2 : R) := by
    apply (ZMod.isUnit_iff_coprime 2 (p ^ (3 * m))).2
    exact coprime_two_pow_prime_oeis_361883 (r := 3 * m) hp hp5
  have hkill_E : (p ^ (2 * m) : R) * E = 0 := by
    rcases htwo_unit with ⟨u, hu⟩
    have h : (u : R) * ((p ^ (2 * m) : R) * E) = 0 := by
      simpa [hu] using htwo_mul
    have h' : ((p ^ (2 * m) : R) * E) * (u : R) = 0 := by
      simpa [mul_comm] using h
    exact (Units.mul_left_eq_zero u).mp h'
  change (((p ^ m * b : ℕ) : R) ^ 2) * E = 0
  calc
    (((p ^ m * b : ℕ) : R) ^ 2) * E = (b ^ 2 : R) * ((p ^ (2 * m) : R) * E) := by
      rw [Nat.cast_mul]
      rw [show (((p ^ m : ℕ) : R)) = (p : R) ^ m by rw [Nat.cast_pow]]
      ring
    _ = 0 := by rw [hkill_E, mul_zero]

lemma unit_superblock_shift_zmod_pow_3m_hS1_oeis_361883 {p m b : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 0 < m) :
  (((p ^ m * b : ℕ) : ZMod (p ^ (3 * m)))) *
    (∑ x ∈ (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m)),
      (((x : ℕ) : ZMod (p ^ (3 * m)))⁻¹)) = 0 := by
  classical
  let R := ZMod (p ^ (3 * m))
  let S := ZMod (p ^ m)
  let s := (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m))
  let c : ℕ → ℕ := fun x => p ^ m - x
  let fR : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  let fS : ℕ → S := fun x => (((x : ℕ) : S)⁻¹)
  let A : R := ∑ x ∈ s, fR x
  let T : R := ∑ x ∈ s, fR x * fR (c x)
  have hmr : m ≤ 3 * m := by nlinarith [hm]
  let phi := ZMod.castHom (show p ^ m ∣ p ^ (3 * m) by exact pow_dvd_pow p hmr) S
  have hs_mem_data {x : ℕ} (hx : x ∈ s) : x < p ^ m ∧ Nat.Coprime x (p ^ m) := by
    have h := Finset.mem_filter.mp hx
    exact ⟨Finset.mem_range.mp h.1, h.2⟩
  have hpm_gt_one : 1 < p ^ m := by
    have hp1 : 1 < p := hp.one_lt
    exact one_lt_pow hm.ne' hp1
  have hpos_of_mem {x : ℕ} (hx : x ∈ s) : 0 < x := by
    have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hx).2
    by_contra hx0
    have hxz : x = 0 := Nat.eq_zero_of_not_pos hx0
    subst hxz
    have hbad : p ^ m = 1 := by simpa [Nat.Coprime] using hxc
    omega
  have hc_mem {x : ℕ} (hx : x ∈ s) : c x ∈ s := by
    have hxlt : x < p ^ m := (hs_mem_data hx).1
    have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hx).2
    have hxpos : 0 < x := hpos_of_mem hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · dsimp [c]
      omega
    · dsimp [c]
      exact (Nat.coprime_self_sub_left (show x ≤ p ^ m by omega)).2 hxc
  have hc_invol {x : ℕ} (hx : x ∈ s) : c (c x) = x := by
    have hxlt : x < p ^ m := (hs_mem_data hx).1
    have hxpos : 0 < x := hpos_of_mem hx
    dsimp [c]
    omega
  have hcast_sum {x : ℕ} (hx : x ∈ s) :
      ((x : R) + ((c x : ℕ) : R)) = ((p ^ m : ℕ) : R) := by
    have hxlt : x < p ^ m := (hs_mem_data hx).1
    have hnat : x + (p ^ m - x) = p ^ m := Nat.add_sub_of_le (show x ≤ p ^ m by omega)
    dsimp [c]
    rw [← Nat.cast_add, hnat]
  have hpair_inv {x : ℕ} (hx : x ∈ s) :
      fR x + fR (c x) = ((p ^ m : ℕ) : R) * fR x * fR (c x) := by
    have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hx).2
    have hcc : Nat.Coprime (c x) (p ^ m) := (hs_mem_data (hc_mem hx)).2
    have hxunit : IsUnit ((x : ℕ) : R) := coprime_pPow_isUnit_zmod_pPow_oeis_361883 (p := p) (m := m) (r := 3 * m) hp hm hxc
    have hcunit : IsUnit (((c x : ℕ) : R)) := coprime_pPow_isUnit_zmod_pPow_oeis_361883 (p := p) (m := m) (r := 3 * m) hp hm hcc
    rcases hxunit with ⟨ux, hux⟩
    rcases hcunit with ⟨uc, huc⟩
    have hxmul : ((x : ℕ) : R) * fR x = 1 := by
      dsimp [fR]
      rw [← hux, ZMod.inv_coe_unit]
      exact Units.mul_inv ux
    have hcmul : (((c x : ℕ) : R)) * fR (c x) = 1 := by
      dsimp [fR]
      rw [← huc, ZMod.inv_coe_unit]
      exact Units.mul_inv uc
    have hmain : (((x : ℕ) : R) + ((c x : ℕ) : R)) * fR x * fR (c x) = fR x + fR (c x) := by
      calc
        (((x : ℕ) : R) + ((c x : ℕ) : R)) * fR x * fR (c x)
            = (((x : ℕ) : R) * fR x) * fR (c x) + (((c x : ℕ) : R) * fR (c x)) * fR x := by ring
        _ = fR x + fR (c x) := by rw [hxmul, hcmul]; ring
    rw [← hmain, hcast_sum hx]
  have hA_comp : A = ∑ x ∈ s, fR (c x) := by
    dsimp [A]
    refine Finset.sum_bij (fun x _ => c x) ?_ ?_ ?_ ?_
    · intro x hx
      exact hc_mem hx
    · intro x hx y hy hxy
      have hxlt : x < p ^ m := (hs_mem_data hx).1
      have hylt : y < p ^ m := (hs_mem_data hy).1
      dsimp [c] at hxy
      omega
    · intro y hy
      refine ⟨c y, hc_mem hy, ?_⟩
      exact hc_invol hy
    · intro x hx
      rw [hc_invol hx]
  have htwoA : (2 : R) * A = ((p ^ m : ℕ) : R) * T := by
    calc
      (2 : R) * A = A + A := by ring
      _ = (∑ x ∈ s, fR x) + A := by rfl
      _ = (∑ x ∈ s, fR x) + (∑ x ∈ s, fR (c x)) := by rw [hA_comp]
      _ = ∑ x ∈ s, (fR x + fR (c x)) := by rw [Finset.sum_add_distrib]
      _ = ∑ x ∈ s, (((p ^ m : ℕ) : R) * fR x * fR (c x)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hpair_inv hx
      _ = ((p ^ m : ℕ) : R) * T := by
        dsimp [T]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
  have hphi_f {x : ℕ} (hxmem : x ∈ s) : phi (fR x) = fS x := by
    have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hxmem).2
    have h := zmod_castHom_inv_pPow_shift_oeis_361883
      (p := p) (r := 3 * m) (k := m) (q := 0) (x := x) hp hm hmr hxc
    simpa [phi, fR, fS, R, S] using h
  have hphi_T : phi T = 0 := by
    calc
      phi T = ∑ x ∈ s, fS x * fS (c x) := by
        dsimp [T]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro x hx
        rw [map_mul, hphi_f hx, hphi_f (hc_mem hx)]
      _ = ∑ x ∈ s, - (fS x) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt : x < p ^ m := (hs_mem_data hx).1
        have hnat : x + (p ^ m - x) = p ^ m := Nat.add_sub_of_le (show x ≤ p ^ m by omega)
        have hsum0 : ((x : ℕ) : S) + ((c x : ℕ) : S) = 0 := by
          dsimp [c]
          rw [← Nat.cast_add, hnat]
          simp [S]
        have hc_eq_neg : ((c x : ℕ) : S) = - ((x : ℕ) : S) := by
          exact eq_neg_of_add_eq_zero_right hsum0
        have hf_neg : fS (c x) = - fS x := by
          dsimp [fS]
          rw [hc_eq_neg]
          have hxc : Nat.Coprime x (p ^ m) := (hs_mem_data hx).2
          have hxunitS : IsUnit ((x : ℕ) : S) := by
            exact (ZMod.isUnit_iff_coprime x (p ^ m)).2 hxc
          rcases hxunitS with ⟨u, hu⟩
          rw [← hu, ZMod.inv_coe_unit]
          change (-(u : S))⁻¹ = -↑(u⁻¹)
          rw [show -(u : S) = ((-u : Sˣ) : S) by rfl]
          rw [ZMod.inv_coe_unit]
          rfl
        rw [hf_neg]
        ring
      _ = - (∑ x ∈ s, (fS x) ^ 2) := by rw [Finset.sum_neg_distrib]
      _ = 0 := by
        dsimp [s, fS, S]
        rw [sum_range_coprime_inv_sq_zmod_pow_eq_zero_oeis_361883 p m hp hp5, neg_zero]
  have hkill_T : (p ^ (2 * m) : R) * T = 0 := by
    have hcomp : 3 * m - m = 2 * m := by omega
    rw [← hcomp]
    exact zmod_pPow_complement_mul_eq_zero_of_castHom_eq_zero_oeis_361883
      (p := p) (r := 3 * m) (k := m) hp hmr T hphi_T
  have htwo_goal : (2 : R) * ((((p ^ m * b : ℕ) : R)) * A) = 0 := by
    calc
      (2 : R) * ((((p ^ m * b : ℕ) : R)) * A)
          = (((p ^ m * b : ℕ) : R)) * ((2 : R) * A) := by ring
      _ = (((p ^ m * b : ℕ) : R)) * (((p ^ m : ℕ) : R) * T) := by rw [htwoA]
      _ = (b : R) * ((p ^ (2 * m) : R) * T) := by
        rw [Nat.cast_mul]
        rw [show (((p ^ m : ℕ) : R)) = (p : R) ^ m by rw [Nat.cast_pow]]
        ring
      _ = 0 := by rw [hkill_T, mul_zero]
  have htwo_unit : IsUnit (2 : R) := by
    apply (ZMod.isUnit_iff_coprime 2 (p ^ (3 * m))).2
    exact coprime_two_pow_prime_oeis_361883 (r := 3 * m) hp hp5
  change (((p ^ m * b : ℕ) : R)) * A = 0
  rcases htwo_unit with ⟨u, hu⟩
  have h : (u : R) * ((((p ^ m * b : ℕ) : R)) * A) = 0 := by
    simpa [hu] using htwo_goal
  have h' : ((((p ^ m * b : ℕ) : R)) * A) * (u : R) = 0 := by
    simpa [mul_comm] using h
  exact (Units.mul_left_eq_zero u).mp h'

lemma unit_superblock_shift_zmod_pow_3m_oeis_361883 {p m b : ℕ}
  (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 0 < m) :
 let R := ZMod (p^(3*m))
 (∏ x ∈ (range (p^m)).filter (fun x=>Nat.Coprime x (p^m)), ((p^m*b+x:ℕ):R)) =
 (∏ x ∈ (range (p^m)).filter (fun x=>Nat.Coprime x (p^m)), ((x:ℕ):R)) := by
  classical
  let R := ZMod (p ^ (3 * m))
  let s := (Finset.range (p ^ m)).filter (fun x => Nat.Coprime x (p ^ m))
  let δ : R := ((p ^ m * b : ℕ) : R)
  let f : ℕ → R := fun x => (((x : ℕ) : R)⁻¹)
  have hδ3 : δ ^ 3 = 0 := by
    rw [← Nat.cast_pow]
    apply (ZMod.natCast_eq_zero_iff ((p ^ m * b) ^ 3) (p ^ (3 * m))).2
    refine ⟨b ^ 3, ?_⟩
    rw [mul_pow]
    rw [← pow_mul]
    have hm3 : m * 3 = 3 * m := by omega
    rw [hm3]
  have hratio : (∏ x ∈ s, (1 + δ * f x)) = (1 : R) := by
    have htrunc := finset_prod_one_add_nilpotent_order3_oeis_361883 (s := s) (δ := δ) (f := f) hδ3
    rw [htrunc]
    dsimp [s, δ, f]
    rw [unit_superblock_shift_zmod_pow_3m_hS1_oeis_361883 (p := p) (m := m) (b := b) hp hp5 hm,
      unit_superblock_shift_zmod_pow_3m_hS2_oeis_361883 (p := p) (m := m) (b := b) hp hp5 hm]
    simp
  intro Rdef
  change (∏ x ∈ s, ((p ^ m * b + x : ℕ) : R)) = (∏ x ∈ s, ((x : ℕ) : R))
  calc
    (∏ x ∈ s, ((p ^ m * b + x : ℕ) : R)) =
        ∏ x ∈ s, (((x : ℕ) : R) * (1 + δ * f x)) := by
          apply Finset.prod_congr rfl
          intro x hx
          have hxc : Nat.Coprime x (p ^ m) := (Finset.mem_filter.mp hx).2
          dsimp [δ, f]
          exact superblock_pPow_shift_factor_eq_mul_one_add_oeis_361883 (p := p) (m := m) (b := b) (x := x) hp hm hxc
    _ = (∏ x ∈ s, ((x : ℕ) : R)) * (∏ x ∈ s, (1 + δ * f x)) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ x ∈ s, ((x : ℕ) : R)) := by
          rw [hratio, mul_one]


/-- If the bottom index is divisible by `p^(e-1)`, adding a low base-`p` digit to a
`p`-multiple top does not change the binomial coefficient modulo `p^e`. -/
lemma zmod_pPow_choose_mul_add_small_eq_choose_mul_oeis_361883 {p e A B c : ℕ}
    (hp : p.Prime) (he : 0 < e) (hBA : B ≤ A) (hB : p ^ (e - 1) ∣ B) (hc : c < p) :
    let R := ZMod (p ^ e)
    ((Nat.choose (p * A + c) (p * B) : ℕ) : R) =
      ((Nat.choose (p * A) (p * B) : ℕ) : R) := by
  intro R
  have hprod := zmod_choose_top_add_prod_ratio_oeis_361883
    (m := p ^ e) (A := p * A) (K := p * B) (L := c) (by nlinarith)
  have hunit : ∀ i ∈ Finset.range c,
      IsUnit (((p * A - p * B + (i + 1) : ℕ) : R)) := by
    intro i hi
    have hi_lt : i + 1 < p := by
      have := Finset.mem_range.mp hi
      omega
    have hnot : ¬ p ∣ p * (A - B) + (i + 1) := by
      intro hdiv
      have hp_part : p ∣ p * (A - B) := dvd_mul_right p (A - B)
      have hi_dvd : p ∣ i + 1 := by
        simpa [Nat.add_sub_cancel_left] using Nat.dvd_sub hdiv hp_part
      exact (Nat.not_dvd_of_pos_of_lt (by omega) hi_lt) hi_dvd
    have heq : p * A - p * B + (i + 1) = p * (A - B) + (i + 1) := by
      rw [Nat.mul_sub_left_distrib]
    have hcop : Nat.Coprime (p * (A - B) + (i + 1)) (p ^ e) := by
      exact hp.coprime_pow_of_not_dvd hnot
    exact (ZMod.isUnit_iff_coprime _ _).2 (by simpa [heq] using hcop)
  specialize hprod hunit
  dsimp at hprod
  rw [hprod]
  have hprod_one :
      (∏ i ∈ Finset.range c,
          (((p * A + (i + 1) : ℕ) : R) *
            (((p * A - p * B + (i + 1) : ℕ) : R)⁻¹))) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    have hden_unit : IsUnit (((p * A - p * B + (i + 1) : ℕ) : R)) := hunit i hi
    rcases hden_unit with ⟨u, hu⟩
    have hden_mul : ((p * A - p * B + (i + 1) : ℕ) : R) *
        (((p * A - p * B + (i + 1) : ℕ) : R)⁻¹) = 1 := by
      rw [← hu, ZMod.inv_coe_unit]
      exact Units.mul_inv u
    have hpBzero : ((p * B : ℕ) : R) = 0 := by
      rcases hB with ⟨d, hd⟩
      subst B
      have hpe : p * (p ^ (e - 1) * d) = p ^ e * d := by
        calc
          p * (p ^ (e - 1) * d) = (p * p ^ (e - 1)) * d := by ring
          _ = p ^ e * d := by
            have hs : p * p ^ (e - 1) = p ^ e := by
              rw [mul_comm, ← pow_succ]
              congr 1
              exact Nat.succ_pred_eq_of_pos he
            rw [hs]
      rw [hpe]
      simp [Nat.cast_mul]
    have hnum_eq_den : ((p * A + (i + 1) : ℕ) : R) =
        ((p * A - p * B + (i + 1) : ℕ) : R) := by
      have hnat : p * A + (i + 1) = (p * A - p * B + (i + 1)) + p * B := by
        have hle : p * B ≤ p * A := Nat.mul_le_mul_left p hBA
        omega
      rw [hnat, Nat.cast_add, hpBzero, add_zero]
    rw [hnum_eq_den, hden_mul]
  rw [hprod_one, mul_one]

/-- A special digit-dropping congruence for the binomial coefficient appearing in the
off-diagonal moment.  If `p^e ∣ N`, the final base-`p` digit of the offset can be
removed modulo `p^e`. -/
lemma zmod_pPow_choose_p_digit_drop_oeis_361883 {p e N q a : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (he : 0 < e) (hN : p ^ e ∣ N) (ha : a < p) :
    let R := ZMod (p ^ e)
    ((Nat.choose (p * (N + (p * q + a))) (p * N) : ℕ) : R) =
      ((Nat.choose (p * (N / p + q)) (p * (N / p)) : ℕ) : R) := by
  intro R
  rcases hN with ⟨d, rfl⟩
  have hpe_split : p ^ e * d = p * (p ^ (e - 1) * d) := by
    calc
      p ^ e * d = (p * p ^ (e - 1)) * d := by
        have hs : p ^ e = p * p ^ (e - 1) := by
          rw [mul_comm, ← pow_succ]
          congr 1
          omega
        rw [hs]
      _ = p * (p ^ (e - 1) * d) := by ring
  have hdiv_eq : (p ^ e * d) / p = p ^ (e - 1) * d := by
    rw [hpe_split]
    exact Nat.mul_div_right (p ^ (e - 1) * d) hp.pos
  let A := p ^ (e - 1) * d + q
  let B := p ^ (e - 1) * d
  have hleft_nat : p * (p ^ e * d + (p * q + a)) = p * (p * A + a) := by
    dsimp [A]
    rw [hpe_split]
    ring
  have hbot_nat : p * (p ^ e * d) = p * (p * B) := by
    dsimp [B]
    rw [hpe_split]
  have hfirst_mod : Nat.choose (p * (p ^ e * d + (p * q + a))) (p * (p ^ e * d)) ≡
      Nat.choose (p ^ e * d + (p * q + a)) (p ^ e * d) [MOD p ^ e] := by
    have hraw := choose_mul_mul_modEq_of_right_dvd_pow_s3_oeis_361883
      (p := p) (A := p ^ e * d + (p * q + a)) (B := p ^ e * d) (s := e) hp hp5 (dvd_mul_right (p ^ e) d)
    exact hraw.of_dvd (pow_dvd_pow p (by omega : e ≤ e + 3))
  have hfirst_eq : ((Nat.choose (p * (p ^ e * d + (p * q + a))) (p * (p ^ e * d)) : ℕ) : R) =
      ((Nat.choose (p ^ e * d + (p * q + a)) (p ^ e * d) : ℕ) : R) := by
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hfirst_mod
  have hmiddle_nat_top : p ^ e * d + (p * q + a) = p * A + a := by
    dsimp [A]
    rw [hpe_split]
    ring
  have hmiddle_nat_bot : p ^ e * d = p * B := by
    dsimp [B]
    rw [hpe_split]
  have hsmall := zmod_pPow_choose_mul_add_small_eq_choose_mul_oeis_361883
    (p := p) (e := e) (A := A) (B := B) (c := a) hp he (by dsimp [A, B]; omega)
    (by dsimp [B]; exact dvd_mul_right (p ^ (e - 1)) d) ha
  dsimp at hsmall
  calc
    ((Nat.choose (p * (p ^ e * d + (p * q + a))) (p * (p ^ e * d)) : ℕ) : R)
        = ((Nat.choose (p ^ e * d + (p * q + a)) (p ^ e * d) : ℕ) : R) := hfirst_eq
    _ = ((Nat.choose (p * A + a) (p * B) : ℕ) : R) := by rw [hmiddle_nat_top, hmiddle_nat_bot]
    _ = ((Nat.choose (p * A) (p * B) : ℕ) : R) := hsmall
    _ = ((Nat.choose (p * ((p ^ e * d) / p + q)) (p * ((p ^ e * d) / p)) : ℕ) : R) := by
      rw [hdiv_eq]



/-- Arbitrary-modulus cancellation of the common unit-part factor in the factorial identities. -/
lemma unitPartProd_cancel_modEq_pow_of_add_congr_oeis_361883 {p e B C X Y : ℕ}
    (hp : p.Prime)
    (hU : let R := ZMod (p ^ e)
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R))
    (hidentity : X * unitPartProd_oeis_361883 p B * unitPartProd_oeis_361883 p C =
      Y * unitPartProd_oeis_361883 p (B + C)) :
    X ≡ Y [MOD p ^ e] := by
  classical
  let R := ZMod (p ^ e)
  let UB : R := (unitPartProd_oeis_361883 p B : ℕ)
  let UC : R := (unitPartProd_oeis_361883 p C : ℕ)
  let V : R := UB * UC
  have hcast := congrArg (fun n : ℕ => (n : R)) hidentity
  have hU' : ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) = V := by
    simpa [R, V, UB, UC] using hU
  have hmain : ((X : ℕ) : R) * V = ((Y : ℕ) : R) * V := by
    simpa [R, V, UB, UC, hU', Nat.cast_mul, mul_assoc] using hcast
  have hV : IsUnit V := by
    dsimp [V, UB, UC]
    exact (unitPartProd_zmod_pow_isUnit_oeis_361883 (p := p) (N := B) (e := e) hp).mul
      (unitPartProd_zmod_pow_isUnit_oeis_361883 (p := p) (N := C) (e := e) hp)
  have hz : ((X : ℕ) : R) = ((Y : ℕ) : R) := hV.mul_right_cancel hmain
  exact (ZMod.natCast_eq_natCast_iff _ _ (p ^ e)).1 hz

lemma choose_mul_sub_one_modEq_of_unitPartProd_add_pow_oeis_361883 {p e B C : ℕ}
    (hp : p.Prime) (hBpos : 0 < B)
    (hU : let R := ZMod (p ^ e)
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R)) :
    Nat.choose (p * (B + C) - 1) (p * B - 1) ≡
      Nat.choose (B + C - 1) (B - 1) [MOD p ^ e] := by
  have hidentity := choose_mul_sub_one_unitPart_identity_oeis_361883
    (p := p) (B := B) (C := C) hp hBpos
  exact unitPartProd_cancel_modEq_pow_of_add_congr_oeis_361883
    (p := p) (e := e) (B := B) (C := C)
    (X := Nat.choose (p * (B + C) - 1) (p * B - 1))
    (Y := Nat.choose (B + C - 1) (B - 1)) hp hU hidentity

lemma choose_mul_sub_one_right_modEq_of_unitPartProd_add_pow_oeis_361883 {p e B C : ℕ}
    (hp : p.Prime) (hCpos : 0 < C)
    (hU : let R := ZMod (p ^ e)
      ((unitPartProd_oeis_361883 p (B + C) : ℕ) : R) =
        ((unitPartProd_oeis_361883 p B : ℕ) : R) *
          ((unitPartProd_oeis_361883 p C : ℕ) : R)) :
    Nat.choose (p * (B + C) - 1) (p * B) ≡ Nat.choose (B + C - 1) B [MOD p ^ e] := by
  have hidentity := choose_mul_sub_one_right_unitPart_identity_oeis_361883
    (p := p) (B := B) (C := C) hp hCpos
  exact unitPartProd_cancel_modEq_pow_of_add_congr_oeis_361883
    (p := p) (e := e) (B := B) (C := C)
    (X := Nat.choose (p * (B + C) - 1) (p * B))
    (Y := Nat.choose (B + C - 1) B) hp hU hidentity


/-- Mixed-precision multiplication in a prime-power `ZMod`: a congruence modulo `p^e`
may be used modulo `p^(e+d)` after multiplying by a factor divisible by `p^d`. -/
lemma zmod_mul_eq_of_modEq_pow_of_pow_dvd_oeis_361883 {p e d a b x : ℕ}
    (h : a ≡ b [MOD p ^ e]) (hx : p ^ d ∣ x) :
    let R := ZMod (p ^ (e + d))
    ((x : ℕ) : R) * ((a : ℕ) : R) = ((x : ℕ) : R) * ((b : ℕ) : R) := by
  intro R
  rcases hx with ⟨y, rfl⟩
  have hpa : p ^ d * a ≡ p ^ d * b [MOD p ^ (e + d)] := by
    have h' := h.mul_left' (p ^ d)
    have hmod : p ^ d * p ^ e = p ^ (e + d) := by
      rw [← pow_add]
      congr 1
      omega
    simpa [hmod] using h'
  have hz : (((p ^ d) * a : ℕ) : R) = (((p ^ d) * b : ℕ) : R) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hpa
  calc
    ((((p ^ d) * y : ℕ) : R) * ((a : ℕ) : R)) =
        ((y : R) * (((p ^ d) * a : ℕ) : R)) := by
      simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = ((y : R) * (((p ^ d) * b : ℕ) : R)) := by rw [hz]
    _ = ((((p ^ d) * y : ℕ) : R) * ((b : ℕ) : R)) := by
      simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]

lemma zmod_mul_eq_of_modEq_pow_of_pow_add_dvd_oeis_361883 {p e d₁ d₂ a b x : ℕ}
    (h : a ≡ b [MOD p ^ e]) (hx : p ^ (d₁ + d₂) ∣ x) :
    let R := ZMod (p ^ (e + d₁ + d₂))
    ((x : ℕ) : R) * ((a : ℕ) : R) = ((x : ℕ) : R) * ((b : ℕ) : R) := by
  intro R
  rcases hx with ⟨y, rfl⟩
  have hpa : p ^ (d₁ + d₂) * a ≡ p ^ (d₁ + d₂) * b [MOD p ^ (e + d₁ + d₂)] := by
    have h' := h.mul_left' (p ^ (d₁ + d₂))
    have hmod : p ^ (d₁ + d₂) * p ^ e = p ^ (e + d₁ + d₂) := by
      rw [← pow_add]
      congr 1
      omega
    simpa [hmod] using h'
  have hz : (((p ^ (d₁ + d₂)) * a : ℕ) : R) = (((p ^ (d₁ + d₂)) * b : ℕ) : R) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hpa
  calc
    ((((p ^ (d₁ + d₂)) * y : ℕ) : R) * ((a : ℕ) : R)) =
        ((y : R) * (((p ^ (d₁ + d₂)) * a : ℕ) : R)) := by
      simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = ((y : R) * (((p ^ (d₁ + d₂)) * b : ℕ) : R)) := by rw [hz]
    _ = ((((p ^ (d₁ + d₂)) * y : ℕ) : R) * ((b : ℕ) : R)) := by
      simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]


/-- Generic polynomial lift for diagonal summands.  If the left adjacent coefficient is known
one `p^d`-block more accurately than the right adjacent coefficient and both left adjacent
coefficients are divisible by `p^d`, then `A^2 (A+2C)` is congruent at the combined precision. -/
lemma T_poly_modEq_of_adjacent_mixed_precision_oeis_361883 {p E d A1 A0 C1 C0 : ℕ}
    (hA : A1 ≡ A0 [MOD p ^ (E + d)]) (hC : C1 ≡ C0 [MOD p ^ E])
    (hA1div : p ^ d ∣ A1) (hA0div : p ^ d ∣ A0) :
    A1 ^ 2 * (A1 + 2 * C1) ≡ A0 ^ 2 * (A0 + 2 * C0) [MOD p ^ (E + d + d)] := by
  let R := ZMod (p ^ (E + d + d))
  apply (ZMod.natCast_eq_natCast_iff _ _ _).1
  change (((A1 ^ 2 * (A1 + 2 * C1) : ℕ) : R) =
    ((A0 ^ 2 * (A0 + 2 * C0) : ℕ) : R))
  have hAmul : ∀ x : ℕ, p ^ d ∣ x → ((x : ℕ) : R) * ((A1 : ℕ) : R) = ((x : ℕ) : R) * ((A0 : ℕ) : R) := by
    intro x hx
    exact zmod_mul_eq_of_modEq_pow_of_pow_dvd_oeis_361883
      (p := p) (e := E + d) (d := d) (a := A1) (b := A0) (x := x) hA hx
  have hCmul : ∀ x : ℕ, p ^ (d + d) ∣ x → ((x : ℕ) : R) * ((C1 : ℕ) : R) = ((x : ℕ) : R) * ((C0 : ℕ) : R) := by
    intro x hx
    exact zmod_mul_eq_of_modEq_pow_of_pow_add_dvd_oeis_361883
      (p := p) (e := E) (d₁ := d) (d₂ := d) (a := C1) (b := C0) (x := x) hC hx
  have hA1sq : ((A1 ^ 2 : ℕ) : R) = ((A0 ^ 2 : ℕ) : R) := by
    have h1 := hAmul A1 hA1div
    have h2 := hAmul A0 hA0div
    calc
      ((A1 ^ 2 : ℕ) : R) = ((A1 : R) * (A1 : R)) := by simp [pow_two]
      _ = ((A1 : R) * (A0 : R)) := h1
      _ = ((A0 : R) * (A1 : R)) := by ring
      _ = ((A0 : R) * (A0 : R)) := h2
      _ = ((A0 ^ 2 : ℕ) : R) := by simp [pow_two]
  have hA0sq_p2d : p ^ (d + d) ∣ A0 ^ 2 := by
    rcases hA0div with ⟨u, hu⟩
    refine ⟨u ^ 2, ?_⟩
    rw [hu]
    rw [mul_pow]
    rw [pow_two]
    rw [← pow_add]
  have hA0sq_pd : p ^ d ∣ A0 ^ 2 := (pow_dvd_pow p (by omega : d ≤ d + d)).trans hA0sq_p2d
  have hcube : ((A1 ^ 2 * A1 : ℕ) : R) = ((A0 ^ 2 * A0 : ℕ) : R) := by
    calc
      ((A1 ^ 2 * A1 : ℕ) : R) = ((A1 ^ 2 : ℕ) : R) * ((A1 : ℕ) : R) := by simp
      _ = ((A0 ^ 2 : ℕ) : R) * ((A1 : ℕ) : R) := by rw [hA1sq]
      _ = ((A0 ^ 2 : ℕ) : R) * ((A0 : ℕ) : R) := hAmul (A0 ^ 2) hA0sq_pd
      _ = ((A0 ^ 2 * A0 : ℕ) : R) := by simp
  have hCterm : ((A1 ^ 2 * C1 : ℕ) : R) = ((A0 ^ 2 * C0 : ℕ) : R) := by
    calc
      ((A1 ^ 2 * C1 : ℕ) : R) = ((A1 ^ 2 : ℕ) : R) * ((C1 : ℕ) : R) := by simp
      _ = ((A0 ^ 2 : ℕ) : R) * ((C1 : ℕ) : R) := by rw [hA1sq]
      _ = ((A0 ^ 2 : ℕ) : R) * ((C0 : ℕ) : R) := hCmul (A0 ^ 2) hA0sq_p2d
      _ = ((A0 ^ 2 * C0 : ℕ) : R) := by simp
  calc
    ((A1 ^ 2 * (A1 + 2 * C1) : ℕ) : R)
        = ((A1 ^ 2 * A1 : ℕ) : R) + (2 : R) * ((A1 ^ 2 * C1 : ℕ) : R) := by
          simp [Nat.cast_add, Nat.cast_mul, right_distrib, mul_assoc, mul_left_comm, mul_comm]
    _ = ((A0 ^ 2 * A0 : ℕ) : R) + (2 : R) * ((A0 ^ 2 * C0 : ℕ) : R) := by
          rw [hcube, hCterm]
    _ = ((A0 ^ 2 * (A0 + 2 * C0) : ℕ) : R) := by
          simp [Nat.cast_add, Nat.cast_mul, right_distrib, mul_assoc, mul_left_comm, mul_comm]

/-- The right-adjacent congruence plus the adjacent identities lift the left-adjacent
congruence by the excess divisibility of `M` over `j`. -/
lemma choose_left_modEq_of_right_modEq_exact_padic_oeis_361883 {p M j s t E d : ℕ} [Fact p.Prime]
    (hMpos : 0 < M) (hMdiv : p ^ s ∣ M) (hts : t ≤ s) (hjeq : j = p ^ t * d)
    (hdcop : Nat.Coprime d p)
    (hC : Nat.choose (M * p + p * j - 1) (M * p) ≡
        Nat.choose (M + j - 1) M [MOD p ^ E]) :
    Nat.choose (M * p + p * j - 1) (M * p - 1) ≡
        Nat.choose (M + j - 1) (M - 1) [MOD p ^ (E + s - t)] := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  let A1 := Nat.choose (M * p + p * j - 1) (M * p - 1)
  let C1 := Nat.choose (M * p + p * j - 1) (M * p)
  let A0 := Nat.choose (M + j - 1) (M - 1)
  let C0 := Nat.choose (M + j - 1) M
  have hC' : C1 ≡ C0 [MOD p ^ E] := by simpa [C1, C0] using hC
  have hpMp : p ^ (s + 1) ∣ M * p := by
    rcases hMdiv with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [hu]
    rw [pow_succ]
    ring
  have hdiv_mod : p ^ (E + s + 1) ∣ p ^ E * (M * p) := by
    rcases hpMp with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    rw [hu]
    calc
      p ^ E * (p ^ (s + 1) * u) = (p ^ E * p ^ (s + 1)) * u := by ring
      _ = p ^ (E + (s + 1)) * u := by rw [← pow_add]
      _ = p ^ (E + s + 1) * u := by rw [show E + (s + 1) = E + s + 1 by omega]
  have hCM : C1 * (M * p) ≡ C0 * (M * p) [MOD p ^ (E + s + 1)] := by
    have h := hC'.mul_right' (M * p)
    exact Nat.ModEq.of_dvd hdiv_mod h
  have hadj1 : C1 * (M * p) = A1 * (p * j) := by
    simpa [A1, C1] using choose_adjacent_mul_for_oeis_361883 (n := M * p) (k := p * j)
      (Nat.mul_pos hMpos hp0)
  have hadj0 : C0 * (M * p) = A0 * (p * j) := by
    have hraw := choose_adjacent_mul_for_oeis_361883 (n := M) (k := j) hMpos
    calc
      C0 * (M * p) = p * (C0 * M) := by ring
      _ = p * (A0 * j) := by rw [show C0 * M = A0 * j by simpa [A0, C0] using hraw]
      _ = A0 * (p * j) := by ring
  have hAj : A1 * (p * j) ≡ A0 * (p * j) [MOD p ^ (E + s + 1)] := by
    simpa [hadj1, hadj0] using hCM
  have hpj : p * j = p ^ (t + 1) * d := by
    rw [hjeq]
    rw [pow_succ]
    ring
  have hpowle : t + 1 ≤ E + s + 1 := by omega
  have hgcdpow : (p ^ (E + s + 1)).gcd (p ^ (t + 1)) = p ^ (t + 1) :=
    Nat.gcd_eq_right (pow_dvd_pow p hpowle)
  have hdivpow : p ^ (E + s + 1) / (p ^ (t + 1)) = p ^ (E + s - t) := by
    have hsplit : E + s + 1 = (t + 1) + (E + s - t) := by omega
    rw [hsplit]
    rw [pow_add]
    rw [Nat.mul_comm]
    exact Nat.mul_div_left _ (pow_pos hp0 (t + 1))
  have hAd_cancel : A1 * d ≡ A0 * d [MOD p ^ (E + s - t)] := by
    have hpAj : p ^ (t + 1) * (A1 * d) ≡ p ^ (t + 1) * (A0 * d) [MOD p ^ (E + s + 1)] := by
      simpa [hpj, mul_assoc, mul_left_comm, mul_comm] using hAj
    have hcan := Nat.ModEq.cancel_left_div_gcd (m := p ^ (E + s + 1))
      (a := A1 * d) (b := A0 * d) (c := p ^ (t + 1)) (pow_pos hp0 (E + s + 1)) hpAj
    simpa [hgcdpow, hdivpow] using hcan
  have hgcd : (p ^ (E + s - t)).gcd d = 1 := by
    rw [Nat.gcd_comm]
    exact Nat.coprime_iff_gcd_eq_one.mp (hdcop.pow_right (E + s - t))
  have hA := Nat.ModEq.cancel_right_of_coprime (m := p ^ (E + s - t))
    (a := A1) (b := A0) (c := d) hgcd hAd_cancel
  simpa [A1, A0] using hA



/-- The inverse-square unit block of length `p^k`, shifted by `p^k*q`, in `ZMod (p^r)`. -/
def unitBlockSqShift_pPow_oeis_361883 (p r k q : ℕ) : ZMod (p ^ r) :=
  ∑ x ∈ (Finset.range (p ^ k)).filter (fun x => Nat.Coprime x (p ^ k)),
    ((((p ^ k * q + x : ℕ) : ZMod (p ^ r))⁻¹) ^ 2)

/-- The staged weighted off-diagonal moment: after dropping `k` base-`p` digits from
`j`, the inverse-square kernel is accumulated in unit blocks of size `p^(k+1)`. -/
def offdiagStageSum_pPow_oeis_361883 (p r k N : ℕ) : ZMod (p ^ r) :=
  ∑ q ∈ Finset.range N,
    ((Nat.choose (p * (N + q)) (p * N) : ℕ) : ZMod (p ^ r)) ^ 3 *
      unitBlockSqShift_pPow_oeis_361883 p r (k + 1) q

lemma unitBlockSqShift_pPow_complement_kills_oeis_361883 (p r k q : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) (hkr : k ≤ r) :
    (p ^ (r - k) : ZMod (p ^ r)) * unitBlockSqShift_pPow_oeis_361883 p r k q = 0 := by
  simpa [unitBlockSqShift_pPow_oeis_361883] using
    unitBlockSq_pPow_complement_kills_oeis_361883 (p := p) (r := r) (k := k) (q := q)
      hp hp5 hk hkr

lemma zmod_pPow_mul_eq_zero_of_castHom_eq_zero_of_pPow_mul_eq_zero_oeis_361883
    {p r e : ℕ} (hp : p.Prime) (he : e ≤ r) (x y : ZMod (p ^ r))
    (hx : ZMod.castHom (show p ^ e ∣ p ^ r by exact pow_dvd_pow p he) (ZMod (p ^ e)) x = 0)
    (hy : (p ^ e : ZMod (p ^ r)) * y = 0) :
    x * y = 0 := by
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  rw [← ZMod.natCast_zmod_val x]
  have hxval0 : ((x.val : ℕ) : ZMod (p ^ e)) = 0 := by
    simpa [ZMod.castHom_apply] using hx
  have hxdiv : p ^ e ∣ x.val := (ZMod.natCast_eq_zero_iff x.val (p ^ e)).1 hxval0
  rcases hxdiv with ⟨a, ha⟩
  rw [ha, Nat.cast_mul]
  change (((p ^ e : ℕ) : ZMod (p ^ r)) * (a : ZMod (p ^ r))) * y = 0
  calc
    (((p ^ e : ℕ) : ZMod (p ^ r)) * (a : ZMod (p ^ r))) * y
        = (a : ZMod (p ^ r)) * (((p ^ e : ℕ) : ZMod (p ^ r)) * y) := by ring
    _ = 0 := by
      have hy' : (((p ^ e : ℕ) : ZMod (p ^ r)) * y) = 0 := by simpa using hy
      rw [hy', mul_zero]

lemma zmod_pPow_coeff_cube_mul_eq_of_castHom_eq_of_pPow_mul_eq_zero_oeis_361883
    {p r e : ℕ} (hp : p.Prime) (he : e ≤ r) (A B H : ZMod (p ^ r))
    (hAB : ZMod.castHom (show p ^ e ∣ p ^ r by exact pow_dvd_pow p he) (ZMod (p ^ e)) A =
      ZMod.castHom (show p ^ e ∣ p ^ r by exact pow_dvd_pow p he) (ZMod (p ^ e)) B)
    (hH : (p ^ e : ZMod (p ^ r)) * H = 0) :
    A ^ 3 * H = B ^ 3 * H := by
  let f := ZMod.castHom (show p ^ e ∣ p ^ r by exact pow_dvd_pow p he) (ZMod (p ^ e))
  have hdiff : f (A ^ 3 - B ^ 3) = 0 := by
    rw [map_sub, map_pow, map_pow, hAB, sub_self]
  have hzero : (A ^ 3 - B ^ 3) * H = 0 :=
    zmod_pPow_mul_eq_zero_of_castHom_eq_zero_of_pPow_mul_eq_zero_oeis_361883
      (p := p) (r := r) (e := e) hp he (A ^ 3 - B ^ 3) H hdiff hH
  calc
    A ^ 3 * H = B ^ 3 * H + (A ^ 3 - B ^ 3) * H := by ring
    _ = B ^ 3 * H := by rw [hzero, add_zero]


lemma coprime_high_digit_add_pPow_iff_oeis_361883 {p K a x : ℕ}
    (hp : p.Prime) (hK : 0 < K) :
    Nat.Coprime (p ^ K * a + x) (p ^ (K + 1)) ↔ Nat.Coprime x (p ^ K) := by
  constructor
  · intro hcop
    have hnot : ¬ p ∣ x := by
      intro hpx
      have hp_high : p ∣ p ^ K * a := by
        exact dvd_mul_of_dvd_left (dvd_pow_self p (Nat.ne_of_gt hK)) a
      have hp_sum : p ∣ p ^ K * a + x := Nat.dvd_add hp_high hpx
      have hp_pow : p ∣ p ^ (K + 1) := dvd_pow_self p (by omega : K + 1 ≠ 0)
      have hp_gcd : p ∣ Nat.gcd (p ^ K * a + x) (p ^ (K + 1)) := Nat.dvd_gcd hp_sum hp_pow
      rw [hcop.gcd_eq_one] at hp_gcd
      exact hp.not_dvd_one hp_gcd
    exact hp.coprime_pow_of_not_dvd hnot
  · intro hcop
    have hnotx : ¬ p ∣ x := by
      intro hpx
      have hp_pow : p ∣ p ^ K := dvd_pow_self p (Nat.ne_of_gt hK)
      have hp_gcd : p ∣ Nat.gcd x (p ^ K) := Nat.dvd_gcd hpx hp_pow
      rw [hcop.gcd_eq_one] at hp_gcd
      exact hp.not_dvd_one hp_gcd
    have hnotsum : ¬ p ∣ p ^ K * a + x := by
      intro hsum
      have hp_high : p ∣ p ^ K * a := by
        exact dvd_mul_of_dvd_left (dvd_pow_self p (Nat.ne_of_gt hK)) a
      have hpx : p ∣ x := (Nat.dvd_add_iff_right hp_high).2 hsum
      exact hnotx hpx
    exact hp.coprime_pow_of_not_dvd hnotsum

lemma unitBlockSqShift_pPow_split_succ_oeis_361883 (p r K q : ℕ)
    (hp : p.Prime) (hK : 0 < K) :
    unitBlockSqShift_pPow_oeis_361883 p r (K + 1) q =
      ∑ a ∈ Finset.range p, unitBlockSqShift_pPow_oeis_361883 p r K (p * q + a) := by
  classical
  let R := ZMod (p ^ r)
  let F : ℕ → R := fun y =>
    if Nat.Coprime y (p ^ (K + 1)) then
      ((((p ^ (K + 1) * q + y : ℕ) : R)⁻¹) ^ 2)
    else 0
  have hleft_filter : unitBlockSqShift_pPow_oeis_361883 p r (K + 1) q =
      ∑ y ∈ Finset.range (p ^ (K + 1)), F y := by
    dsimp [unitBlockSqShift_pPow_oeis_361883, F]
    rw [Finset.sum_filter]
  have hdecomp : (∑ y ∈ Finset.range (p ^ (K + 1)), F y) =
      ∑ a ∈ Finset.range p, ∑ x ∈ Finset.range (p ^ K), F (p ^ K * a + x) := by
    have hpow : p ^ (K + 1) = p * p ^ K := by
      rw [pow_succ', Nat.mul_comm]
    rw [hpow]
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (sum_range_mul_decomp_oeis_361883 p (p ^ K) F)
  have hright : (∑ a ∈ Finset.range p, ∑ x ∈ Finset.range (p ^ K), F (p ^ K * a + x)) =
      ∑ a ∈ Finset.range p, unitBlockSqShift_pPow_oeis_361883 p r K (p * q + a) := by
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [unitBlockSqShift_pPow_oeis_361883, F]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    have hcopiff := coprime_high_digit_add_pPow_iff_oeis_361883 (p := p) (K := K) (a := a) (x := x) hp hK
    by_cases hcx : Nat.Coprime x (p ^ K)
    · have hcy : Nat.Coprime (p ^ K * a + x) (p ^ (K + 1)) := hcopiff.2 hcx
      rw [if_pos hcy, if_pos hcx]
      apply congrArg (fun z : R => z⁻¹ ^ 2)
      ring_nf
    · have hcy : ¬ Nat.Coprime (p ^ K * a + x) (p ^ (K + 1)) := by
        intro hc
        exact hcx (hcopiff.1 hc)
      rw [if_neg hcy, if_neg hcx]
  rw [hleft_filter, hdecomp, hright]


lemma offdiagStageSum_pPow_eq_next_oeis_361883 {p r e k N : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (heq : r = e + 1 + k + 1) (hN : p ^ (e + 1) ∣ N) :
    offdiagStageSum_pPow_oeis_361883 p r k N =
      offdiagStageSum_pPow_oeis_361883 p r (k + 1) (N / p) := by
  classical
  let R := ZMod (p ^ r)
  have hp_pos : 0 < p := hp.pos
  have hp_dvd_N : p ∣ N := by
    rcases hN with ⟨d, hd⟩
    rw [hd]
    simpa [pow_succ', Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      (dvd_mul_right p (p ^ e * d))
  have hN_mul : N / p * p = N := Nat.div_mul_cancel hp_dvd_N
  have hk1_pos : 0 < k + 1 := by omega
  have hk1_le_r : k + 1 ≤ r := by omega
  have hkill (q : ℕ) :
      (p ^ (e + 1) : R) * unitBlockSqShift_pPow_oeis_361883 p r (k + 1) q = 0 := by
    have h := unitBlockSqShift_pPow_complement_kills_oeis_361883
      (p := p) (r := r) (k := k + 1) (q := q) hp hp5 hk1_pos hk1_le_r
    have hexp : r - (k + 1) = e + 1 := by omega
    simpa [R, hexp] using h
  have hpoint (q a : ℕ) (ha : a ∈ Finset.range p) :
      ((Nat.choose (p * (N + (p * q + a))) (p * N) : ℕ) : R) ^ 3 *
          unitBlockSqShift_pPow_oeis_361883 p r (k + 1) (p * q + a) =
        ((Nat.choose (p * (N / p + q)) (p * (N / p)) : ℕ) : R) ^ 3 *
          unitBlockSqShift_pPow_oeis_361883 p r (k + 1) (p * q + a) := by
    have ha_lt : a < p := Finset.mem_range.mp ha
    let S := ZMod (p ^ (e + 1))
    let f := ZMod.castHom (show p ^ (e + 1) ∣ p ^ r by exact pow_dvd_pow p (by omega)) S
    have hdrop := zmod_pPow_choose_p_digit_drop_oeis_361883
      (p := p) (e := e + 1) (N := N) (q := q) (a := a) hp hp5 (by omega) hN ha_lt
    dsimp at hdrop
    have hAB : f (((Nat.choose (p * (N + (p * q + a))) (p * N) : ℕ) : R)) =
        f (((Nat.choose (p * (N / p + q)) (p * (N / p)) : ℕ) : R)) := by
      simpa [f, S, ZMod.castHom_apply] using hdrop
    exact zmod_pPow_coeff_cube_mul_eq_of_castHom_eq_of_pPow_mul_eq_zero_oeis_361883
      (p := p) (r := r) (e := e + 1) hp (by omega)
      (((Nat.choose (p * (N + (p * q + a))) (p * N) : ℕ) : R))
      (((Nat.choose (p * (N / p + q)) (p * (N / p)) : ℕ) : R))
      (unitBlockSqShift_pPow_oeis_361883 p r (k + 1) (p * q + a)) hAB (hkill (p * q + a))
  dsimp [offdiagStageSum_pPow_oeis_361883]
  conv_lhs => rw [← hN_mul]
  rw [sum_range_mul_decomp_oeis_361883 (N / p) p
    (fun j => ((Nat.choose (p * (N / p * p + j)) (p * (N / p * p)) : ℕ) : R) ^ 3 *
      unitBlockSqShift_pPow_oeis_361883 p r (k + 1) j)]
  apply Finset.sum_congr rfl
  intro q hq
  calc
    (∑ a ∈ Finset.range p,
        ((Nat.choose (p * (N / p * p + (p * q + a))) (p * (N / p * p)) : ℕ) : R) ^ 3 *
          unitBlockSqShift_pPow_oeis_361883 p r (k + 1) (p * q + a))
        = ∑ a ∈ Finset.range p,
          ((Nat.choose (p * (N / p + q)) (p * (N / p)) : ℕ) : R) ^ 3 *
            unitBlockSqShift_pPow_oeis_361883 p r (k + 1) (p * q + a) := by
          apply Finset.sum_congr rfl
          intro a ha
          simpa [hN_mul] using hpoint q a ha
    _ = ((Nat.choose (p * (N / p + q)) (p * (N / p)) : ℕ) : R) ^ 3 *
          (∑ a ∈ Finset.range p, unitBlockSqShift_pPow_oeis_361883 p r (k + 1) (p * q + a)) := by
          rw [Finset.mul_sum]
    _ = ((Nat.choose (p * (N / p + q)) (p * (N / p)) : ℕ) : R) ^ 3 *
          unitBlockSqShift_pPow_oeis_361883 p r (k + 1 + 1) q := by
          rw [unitBlockSqShift_pPow_split_succ_oeis_361883 (p := p) (r := r) (K := k + 1) (q := q) hp (by omega)]
    _ = ((Nat.choose (p * (N / p + q)) (p * (N / p)) : ℕ) : R) ^ 3 *
          unitBlockSqShift_pPow_oeis_361883 p r (k + 2) q := by ring_nf

lemma offdiagStageSum_pPow_zero_aux_oeis_361883 {p e k N : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hN : p ^ e ∣ N) :
    offdiagStageSum_pPow_oeis_361883 p (e + k + 1) k N = 0 := by
  induction e generalizing k N with
  | zero =>
      dsimp [offdiagStageSum_pPow_oeis_361883]
      apply Finset.sum_eq_zero
      intro q hq
      have hkill := unitBlockSqShift_pPow_complement_kills_oeis_361883
        (p := p) (r := 0 + k + 1) (k := k + 1) (q := q) hp hp5 (by omega) (by omega)
      have hinner : unitBlockSqShift_pPow_oeis_361883 p (0 + k + 1) (k + 1) q = 0 := by
        simpa using hkill
      rw [hinner, mul_zero]
  | succ e ih =>
      have hnext : offdiagStageSum_pPow_oeis_361883 p (Nat.succ e + k + 1) k N =
          offdiagStageSum_pPow_oeis_361883 p (Nat.succ e + k + 1) (k + 1) (N / p) := by
        exact offdiagStageSum_pPow_eq_next_oeis_361883
          (p := p) (r := Nat.succ e + k + 1) (e := e) (k := k) (N := N) hp hp5 (by omega) hN
      have hp_pos : 0 < p := hp.pos
      have hN' : p ^ e ∣ N / p := by
        rcases hN with ⟨d, hd⟩
        rw [hd]
        have hsplit : p ^ (e + 1) * d = p * (p ^ e * d) := by
          rw [pow_succ']; ring
        rw [hsplit]
        rw [Nat.mul_div_right _ hp_pos]
        exact dvd_mul_right (p ^ e) d
      rw [hnext]
      have hr_eq : Nat.succ e + k + 1 = e + (k + 1) + 1 := by omega
      rw [hr_eq]
      exact ih (k := k + 1) (N := N / p) hN'


lemma unitBlockSqShift_one_eq_offdiag_inner_oeis_361883 (p r j : ℕ) (hp : p.Prime) :
    unitBlockSqShift_pPow_oeis_361883 p r 1 j =
      ∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
        ((((p * j + t : ℕ) : ZMod (p ^ r))⁻¹) ^ 2) := by
  classical
  dsimp [unitBlockSqShift_pPow_oeis_361883]
  have hfilter : (Finset.range (p ^ 1)).filter (fun x => Nat.Coprime x (p ^ 1)) =
      (Finset.range p).filter (fun x => 0 < x) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, pow_one]
    constructor
    · intro hx
      rcases hx with ⟨hxlt, hcop⟩
      refine ⟨hxlt, ?_⟩
      by_contra hx0
      have hx_eq : x = 0 := by omega
      subst x
      have hp_eq_one : p = 1 := by
        simpa using hcop.gcd_eq_one
      exact hp.ne_one hp_eq_one
    · intro hx
      rcases hx with ⟨hxlt, hxpos⟩
      refine ⟨hxlt, ?_⟩
      have hnot : ¬ p ∣ x := Nat.not_dvd_of_pos_of_lt hxpos hxlt
      exact ((hp.coprime_iff_not_dvd).2 hnot).symm
  rw [hfilter]
  simp [pow_one]

/-- All-`r` weighted off-diagonal inverse-square moment modulo `p^r`. -/
lemma offdiag_weighted_moment_zmod_pPow_zero_oeis_361883 {p M r : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r) (_hMpos : 0 < M)
    (hMdiv : p ^ (r - 1) ∣ M) :
    let R := ZMod (p ^ r)
    (∑ j ∈ Finset.range M,
      ((Nat.choose (p * (M + j)) (p * M) : ℕ) : R) ^ 3 *
        (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((((p * j + t : ℕ) : R)⁻¹) ^ 2))) = 0 := by
  dsimp
  have hstage := offdiagStageSum_pPow_zero_aux_oeis_361883
    (p := p) (e := r - 1) (k := 0) (N := M) hp hp5 hMdiv
  have hrpow : r - 1 + 0 + 1 = r := by omega
  rw [← hrpow]
  dsimp [offdiagStageSum_pPow_oeis_361883] at hstage
  rw [← hstage]
  apply Finset.sum_congr rfl
  intro j hj
  rw [unitBlockSqShift_one_eq_offdiag_inner_oeis_361883 (p := p) (r := r - 1 + 0 + 1) (j := j) hp]

/-- Lifting the all-`r` weighted moment through the existing off-diagonal reduction. -/
lemma offdiag_global_modEq_zero_all_r_of_weighted_moment_oeis_361883 {p M r : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 0 < r) (hMpos : 0 < M)
    (hMdiv : p ^ (r - 1) ∣ M) :
    (Finset.sum (Finset.range M) fun j =>
      Finset.sum ((Finset.range p).filter (fun t => 0 < t)) fun t =>
        oeis_361883_T (M * p) (p * j + t)) ≡ 0 [MOD p ^ (3 * r)] := by
  let R := ZMod (p ^ (3 * r))
  let W : R :=
    ∑ j ∈ Finset.range M,
      ((Nat.choose (M * p + p * j) (M * p) : ℕ) : R) ^ 3 *
        (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
          ((((p * j + t : ℕ) : R)⁻¹) ^ 2))
  have hcastW : ZMod.castHom (show p ^ r ∣ p ^ (3 * r) by exact pow_dvd_pow p (by omega)) (ZMod (p ^ r)) W = 0 := by
    let f := ZMod.castHom (show p ^ r ∣ p ^ (3 * r) by exact pow_dvd_pow p (by omega)) (ZMod (p ^ r))
    change f W = 0
    dsimp [W]
    rw [map_sum]
    have hmoment := offdiag_weighted_moment_zmod_pPow_zero_oeis_361883
      (p := p) (M := M) (r := r) hp hp5 hr hMpos hMdiv
    dsimp at hmoment
    calc
      (∑ x ∈ Finset.range M,
          ZMod.castHom (show p ^ r ∣ p ^ (3 * r) by exact pow_dvd_pow p (by omega)) (ZMod (p ^ r))
            (((Nat.choose (M * p + p * x) (M * p) : ℕ) : R) ^ 3 *
              ∑ t ∈ (Finset.range p).filter (fun t => 0 < t), ((((p * x + t : ℕ) : R)⁻¹) ^ 2)))
        = ∑ j ∈ Finset.range M,
          ((Nat.choose (p * (M + j)) (p * M) : ℕ) : ZMod (p ^ r)) ^ 3 *
            (∑ t ∈ (Finset.range p).filter (fun t => 0 < t),
              ((((p * j + t : ℕ) : ZMod (p ^ r))⁻¹) ^ 2)) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [map_mul, map_pow, map_sum]
          congr 1
          · simp
            congr 1
            ring_nf
          · apply Finset.sum_congr rfl
            intro t ht
            have ht0 : 0 < t := (Finset.mem_filter.mp ht).2
            have htp : t < p := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
            have hcop : Nat.Coprime (p * j + t) (p ^ r) := by
              have hnot : ¬ p ∣ p * j + t := by
                intro hdiv
                have hpj : p ∣ p * j := dvd_mul_right p j
                have hpt : p ∣ t := (Nat.dvd_add_iff_right hpj).2 hdiv
                exact (Nat.not_dvd_of_pos_of_lt ht0 htp) hpt
              exact hp.coprime_pow_of_not_dvd hnot
            simpa [f, Nat.cast_add, Nat.cast_mul] using
              zmod_castHom_inv_sq_pPow_shift_oeis_361883
                (p := p) (r := 3 * r) (k := r) (q := 0) (x := p * j + t)
                hp hr (by omega) hcop
      _ = 0 := hmoment
  have hkill : (p ^ (2 * r) : R) * W = 0 := by
    have h := zmod_pPow_complement_mul_eq_zero_of_castHom_eq_zero_oeis_361883
      (p := p) (r := 3 * r) (k := r) hp (by omega) W hcastW
    have hexp : 3 * r - r = 2 * r := by omega
    simpa [R, hexp] using h
  refine offdiag_global_modEq_zero_general_of_weighted_zmod_pPow_mul_eq_zero_oeis_361883
    (p := p) (M := M) (r := r) hp hp5 hr hMpos hMdiv ?_
  simpa [R, W, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hkill




/-- All-level complementary diagonal congruence.  The case `r=1` is the existing base
case; for `r>1`, non-unitness forces `p ∣ j`.  The split unit-part product gives the
right-adjacent congruence, the adjacent identities lift the left-adjacent congruence, and the
mixed-precision polynomial lemma supplies the diagonal summand congruence. -/
lemma T_diag_nonunit_modEq_all_r_oeis_361883 {p M r j : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hr : 0 < r) (hMpos : 0 < M) (hMdiv : p ^ (r - 1) ∣ M)
    (hpdiv : p ∣ M + j) :
    oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ (3 * r)] := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  by_cases hr1 : r = 1
  · exact T_diag_nonunit_modEq_general_of_r_eq_one_oeis_361883
      (p := p) (M := M) (r := r) (j := j) hp5 hr hMpos hMdiv hpdiv hr1
  have hrgt : 1 < r := by omega
  by_cases hj0 : j = 0
  · subst j
    simpa using T_diag_zero_modEq_oeis_361883 (p := p) (M := M) (r := r) hMpos hp0
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  have hjdiv : p ∣ j := dvd_j_of_nonunit_diag_of_r_gt_one_oeis_361883
    (p := p) (M := M) (r := r) (j := j) hrgt hMdiv hpdiv
  let s := r - 1
  let t := padicValNat p j
  have hs_eq : s + 1 = r := by dsimp [s]; omega
  have htpos : 0 < t := by
    have hjne : j ≠ 0 := hj0
    exact one_le_padicValNat_of_dvd (p := p) hjne hjdiv
  by_cases hts : t ≤ s
  · let E := s + 2 * t + 3
    let d := s - t
    have hU : let R := ZMod (p ^ E)
        ((unitPartProd_oeis_361883 p (M + j) : ℕ) : R) =
          ((unitPartProd_oeis_361883 p M : ℕ) : R) *
            ((unitPartProd_oeis_361883 p j : ℕ) : R) := by
      dsimp [E]
      exact unitPartProd_zmod_pow_split_add_of_dvd_le_oeis_361883
        (p := p) (B := M) (C := j) (s := s) (t := t) hp hp5 hMdiv
        (pow_padicValNat_dvd (p := p) (n := j)) hts
    have hC : Nat.choose (M * p + p * j - 1) (M * p) ≡
        Nat.choose (M + j - 1) M [MOD p ^ E] := by
      have h := choose_mul_sub_one_right_modEq_of_unitPartProd_add_pow_oeis_361883
        (p := p) (e := E) (B := M) (C := j) hp hjpos hU
      simpa [E, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc] using h
    have hjpow := pow_padicValNat_dvd (p := p) (n := j)
    rcases hjpow with ⟨q, hq⟩
    have hqcop' : Nat.Coprime q p := by
      by_contra hbad
      have hpq : p ∣ q := by
        by_contra hnp
        exact hbad (((hp.coprime_iff_not_dvd).2 hnp).symm)
      rcases hpq with ⟨u, hu⟩
      have hsucc : p ^ (t + 1) ∣ j := by
        refine ⟨u, ?_⟩
        rw [hq, hu, pow_succ]
        ring
      exact pow_succ_padicValNat_not_dvd (p := p) hj0 hsucc
    have hA : Nat.choose (M * p + p * j - 1) (M * p - 1) ≡
        Nat.choose (M + j - 1) (M - 1) [MOD p ^ (E + d)] := by
      have hleft := choose_left_modEq_of_right_modEq_exact_padic_oeis_361883
        (p := p) (M := M) (j := j) (s := s) (t := t) (E := E) (d := q)
        hMpos hMdiv hts (by exact hq) hqcop' hC
      have hed : E + s - t = E + d := by dsimp [d]; omega
      simpa [hed] using hleft
    have hA0div : p ^ d ∣ Nat.choose (M + j - 1) (M - 1) := by
      exact choose_adjacent_dvd_of_M_dvd_oeis_361883
        (p := p) (M := M) (j := j) (m := s) hMpos hjpos hMdiv
    have hpj_ne : p * j ≠ 0 := mul_ne_zero hp.ne_zero hj0
    have hpj_val : padicValNat p (p * j) = t + 1 := by
      rw [padicValNat.mul hp.ne_zero hj0, padicValNat_self]
      dsimp [t]
      omega
    have hMpdiv : p ^ (s + 1) ∣ M * p := by
      rcases hMdiv with ⟨u, hu⟩
      refine ⟨u, ?_⟩
      rw [hu, pow_succ]
      ring
    have hA1raw := choose_adjacent_dvd_of_M_dvd_oeis_361883
      (p := p) (M := M * p) (j := p * j) (m := s + 1)
      (Nat.mul_pos hMpos hp0) (Nat.mul_pos hp0 hjpos) hMpdiv
    have hA1div : p ^ d ∣ Nat.choose (M * p + p * j - 1) (M * p - 1) := by
      have hpoweq : (s + 1) - padicValNat p (p * j) = d := by
        rw [hpj_val]
        dsimp [d]
        omega
      simpa [hpoweq, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hA1raw
    have hTpoly := T_poly_modEq_of_adjacent_mixed_precision_oeis_361883
      (p := p) (E := E) (d := d)
      (A1 := Nat.choose (M * p + p * j - 1) (M * p - 1))
      (A0 := Nat.choose (M + j - 1) (M - 1))
      (C1 := Nat.choose (M * p + p * j - 1) (M * p))
      (C0 := Nat.choose (M + j - 1) M) hA hC hA1div hA0div
    have hmodexp : E + d + d = 3 * r := by
      dsimp [E, d, s]
      omega
    have hT : oeis_361883_T (M * p) (p * j) ≡ oeis_361883_T M j [MOD p ^ (E + d + d)] := by
      have hMp : 0 < M * p := Nat.mul_pos hMpos hp0
      rw [oeis_361883_T_eq_sq_mul (N := M * p) (k := p * j) hMp]
      rw [oeis_361883_T_eq_sq_mul (N := M) (k := j) hMpos]
      simpa using hTpoly
    simpa [hmodexp] using hT
  · have hst : s ≤ t := le_of_lt (Nat.lt_of_not_ge hts)
    have hj_s : p ^ s ∣ j := by
      exact (padicValNat_dvd_iff_le (p := p) hj0).2 hst
    let E := s + 2 * s + 3
    have hU : let R := ZMod (p ^ E)
        ((unitPartProd_oeis_361883 p (M + j) : ℕ) : R) =
          ((unitPartProd_oeis_361883 p M : ℕ) : R) *
            ((unitPartProd_oeis_361883 p j : ℕ) : R) := by
      dsimp [E]
      exact unitPartProd_zmod_pow_split_add_of_dvd_le_oeis_361883
        (p := p) (B := M) (C := j) (s := s) (t := s) hp hp5 hMdiv hj_s (le_refl s)
    have hA : Nat.choose (M * p + p * j - 1) (M * p - 1) ≡
        Nat.choose (M + j - 1) (M - 1) [MOD p ^ E] := by
      have h := choose_mul_sub_one_modEq_of_unitPartProd_add_pow_oeis_361883
        (p := p) (e := E) (B := M) (C := j) hp hMpos hU
      simpa [E, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc] using h
    have hC : Nat.choose (M * p + p * j - 1) (M * p) ≡
        Nat.choose (M + j - 1) M [MOD p ^ E] := by
      have h := choose_mul_sub_one_right_modEq_of_unitPartProd_add_pow_oeis_361883
        (p := p) (e := E) (B := M) (C := j) hp hjpos hU
      simpa [E, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
        Nat.mul_left_comm, Nat.mul_assoc] using h
    have hdiag := T_diag_mod_pow_of_adjacent_modEq_oeis_361883
      (p := p) (M := M) (r := r) (j := j) hp0 hMpos
      (by
        have hE : E = 3 * r := by dsimp [E, s]; omega
        simpa [hE] using hA)
      (by
        have hE : E = 3 * r := by dsimp [E, s]; omega
        simpa [hE] using hC)
    exact hdiag

/-- All-level diagonal contribution congruence. -/
lemma diag_sum_modEq_all_r_oeis_361883 {p M r : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hr : 0 < r) (hMpos : 0 < M) (hMdiv : p ^ (r - 1) ∣ M) :
    (Finset.sum (Finset.range (M + 1)) fun j => oeis_361883_T (M * p) (p * j)) ≡
      a M [MOD p ^ (3 * r)] := by
  refine diag_sum_modEq_of_pointwise_oeis_361883 (p := p) (M := M) (r := r) hMpos ?_
  intro j hj
  by_cases hpunit : p ∣ M + j
  · exact T_diag_nonunit_modEq_all_r_oeis_361883
      (p := p) (M := M) (r := r) (j := j) hp5 hr hMpos hMdiv hpunit
  · exact T_diag_unit_modEq_general_oeis_361883
      (p := p) (M := M) (r := r) (j := j) hp5 hr hMpos hMdiv hpunit

/--
The central binomial coefficients $u(n) := \binom{2n}{n}$ satisfy the supercongruences
$u(n \cdot p^r) \equiv u(n \cdot p^{r-1}) \pmod{p^{3r}}$ for positive integers $n$ and $r$


and all primes $p \ge 5$. We conjecture that the present sequence $a(n)$ satisfies the same congruences.
-/
theorem oeis_361883_conjecture_0 {p n r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    a (n * p ^ r) ≡ a (n * p ^ (r - 1)) [MOD p ^ (3 * r)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  let M := n * p ^ (r - 1)
  have hMpos : 0 < M := Nat.mul_pos hn (pow_pos hp.pos (r - 1))
  have hMdiv : p ^ (r - 1) ∣ M := by
    dsimp [M]
    simp
  refine oeis_361883_conjecture_0_of_diag_offdiag (p := p) (n := n) (r := r) hp hn hr ?_ ?_
  · exact diag_sum_modEq_all_r_oeis_361883
      (p := p) (M := M) (r := r) hp5 hr hMpos hMdiv
  · simpa [M] using offdiag_global_modEq_zero_all_r_of_weighted_moment_oeis_361883
      (p := p) (M := M) (r := r) hp hp5 hr hMpos hMdiv

