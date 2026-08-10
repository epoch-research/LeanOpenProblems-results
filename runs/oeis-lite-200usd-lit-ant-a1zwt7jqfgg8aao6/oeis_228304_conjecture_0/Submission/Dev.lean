import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)

def c (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)

section
variable {p : ℕ} [Fact p.Prime]

/-- Single-step Lucas in `ZMod p`. -/
lemma choose_zmod (n k : ℕ) :
    ((n.choose k : ZMod p)) = ((n % p).choose (k % p) : ZMod p) * ((n / p).choose (k / p) : ZMod p) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := k) (p := p)
  rw [← ZMod.intCast_eq_intCast_iff] at h
  push_cast at h
  exact_mod_cast h

/-- `p.choose j = 0` in `ZMod p` for `0 < j < p`. -/
lemma choose_p_zmod (hp : p.Prime) {j : ℕ} (hj : 0 < j) (hjp : j < p) :
    (p.choose j : ZMod p) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact hp.dvd_choose_self (by omega) hjp

/-- `(p-1).choose k = (-1)^k` in `ZMod p`. -/
lemma choose_pred (hp : p.Prime) : ∀ k : ℕ, k ≤ p - 1 → ((p - 1).choose k : ZMod p) = (-1) ^ k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ n ih =>
    intro hk
    have hple : n + 1 ≤ p - 1 := hk
    have hp2 : 2 ≤ p := hp.two_le
    -- Pascal: p.choose (n+1) = (p-1).choose n + (p-1).choose (n+1)
    have hpas : (p - 1).choose n + (p - 1).choose (n + 1) = p.choose (n + 1) := by
      conv_rhs => rw [show p = (p - 1) + 1 by omega]
      rw [Nat.choose_succ_succ]
    have h0 : (p.choose (n + 1) : ZMod p) = 0 := by
      apply choose_p_zmod hp (by omega) (by omega)
    have hcast : ((p - 1).choose n : ZMod p) + ((p - 1).choose (n + 1) : ZMod p) = 0 := by
      have := congrArg (Nat.cast : ℕ → ZMod p) hpas
      push_cast at this; rw [this, h0]
    have ihn : ((p - 1).choose n : ZMod p) = (-1) ^ n := ih (by omega)
    have hstep : ((p - 1).choose (n + 1) : ZMod p) = -((p - 1).choose n : ZMod p) := by
      linear_combination hcast
    rw [hstep, ihn]; ring

-- Helper: decompose mod/div.
lemma modw {x q s : ℕ} (hp : 0 < p) (h : x = s + q * p) (hs : s < p) :
    x % p = s ∧ x / p = q := by
  subst h
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  · rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hs, Nat.zero_add]

-- Helper computations for `p ≤ x < 2p`.
lemma mod_lo (hp : p.Prime) {r : ℕ} (hr : r < p) : (p + r) % p = r := by
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt hr]
lemma div_lo (hp : p.Prime) {r : ℕ} (hr : r < p) : (p + r) / p = 1 := by
  rw [Nat.add_comm, Nat.add_div_right _ hp.pos, Nat.div_eq_of_lt hr]

/-- Lucas reduction: `(p+r).choose k₀ = r.choose k₀` for `k₀ ≤ r < p`. -/
lemma choose_add_lo (hp : p.Prime) {r k₀ : ℕ} (hr : r < p) (hk : k₀ ≤ r) :
    (((p + r).choose k₀ : ZMod p)) = (r.choose k₀ : ZMod p) := by
  have hk0 : k₀ < p := lt_of_le_of_lt hk hr
  rw [choose_zmod (p + r) k₀, mod_lo hp hr, div_lo hp hr,
      Nat.mod_eq_of_lt hk0, Nat.div_eq_of_lt hk0, Nat.choose_zero_right]
  simp

/-- Lucas reduction: `(p+r).choose (p+k₀) = r.choose k₀` for `k₀ ≤ r < p`. -/
lemma choose_add_hi (hp : p.Prime) {r k₀ : ℕ} (hr : r < p) (hk : k₀ ≤ r) :
    (((p + r).choose (p + k₀) : ZMod p)) = (r.choose k₀ : ZMod p) := by
  have hk0 : k₀ < p := lt_of_le_of_lt hk hr
  rw [choose_zmod (p + r) (p + k₀), mod_lo hp hr, div_lo hp hr,
      mod_lo hp hk0, div_lo hp hk0, Nat.choose_self]
  simp

/-- `(p+r).choose k = 0` for `r < k < p`. -/
lemma choose_add_mid (hp : p.Prime) {r k : ℕ} (hr : r < p) (hrk : r < k) (hkp : k < p) :
    (((p + r).choose k : ZMod p)) = 0 := by
  rw [choose_zmod (p + r) k, mod_lo hp hr, div_lo hp hr,
      Nat.mod_eq_of_lt hkp, Nat.div_eq_of_lt hkp, Nat.choose_zero_right,
      Nat.choose_eq_zero_of_lt hrk]
  simp

/-- Central binomial vanishing: `(2*m).choose m = 0` for `p ≤ 2*m` and `m < p`. -/
lemma central_vanish (hp : p.Prime) {m : ℕ} (hm : m < p) (h2 : p ≤ 2 * m) :
    (((2 * m).choose m : ZMod p)) = 0 := by
  have hmm : (2 * m) % p = 2 * m - p ∧ (2 * m) / p = 1 :=
    modw hp.pos (by omega) (by omega)
  rw [choose_zmod (2 * m) m, hmm.1, hmm.2, Nat.mod_eq_of_lt hm, Nat.div_eq_of_lt hm,
      Nat.choose_eq_zero_of_lt (by omega : 2 * m - p < m)]
  simp

/-- Central binomial shift: `(2*(p+m)).choose (p+m) = 2 * (2*m).choose m` for `m < p`. -/
lemma central_shift (hp : p.Prime) {m : ℕ} (hm : m < p) :
    (((2 * (p + m)).choose (p + m) : ZMod p)) = 2 * ((2 * m).choose m : ZMod p) := by
  have hpm : (p + m) % p = m ∧ (p + m) / p = 1 := modw hp.pos (by ring) hm
  rcases lt_or_ge (2 * m) p with h | h
  · -- 2m < p
    have hx : (2 * (p + m)) % p = 2 * m ∧ (2 * (p + m)) / p = 2 :=
      modw hp.pos (by ring) h
    rw [choose_zmod (2 * (p + m)) (p + m), hx.1, hx.2, hpm.1, hpm.2,
        show (2 : ℕ).choose 1 = 2 from rfl]
    push_cast; ring
  · -- 2m ≥ p
    have hx : (2 * (p + m)) % p = 2 * m - p ∧ (2 * (p + m)) / p = 3 :=
      modw hp.pos (by omega) (by omega)
    rw [choose_zmod (2 * (p + m)) (p + m), hx.1, hx.2, hpm.1, hpm.2,
        Nat.choose_eq_zero_of_lt (by omega : 2 * m - p < m)]
    rw [central_vanish hp hm h]
    simp

lemma a_cast (n : ℕ) :
    ((a n : ℤ) : ZMod p) = ∑ k ∈ range (n + 1), (-1 : ZMod p) ^ k * ((n.choose k : ZMod p)) ^ 4 := by
  unfold a
  push_cast
  rfl

lemma c_cast (n : ℕ) :
    ((c n : ℤ) : ZMod p) = ∑ k ∈ range (n + 1),
      (-1 : ZMod p) ^ k * ((n.choose k : ZMod p)) ^ 2
        * ((2 * k).choose k : ZMod p) * ((2 * (n - k)).choose (n - k) : ZMod p) := by
  unfold c
  push_cast
  rfl

/-- General pairing-to-zero lemma. -/
lemma pairing_zero (hp : p.Prime) {r : ℕ} (hr : r < p) (f : ℕ → ZMod p)
    (H1 : ∀ k, r < k → k < p → f k = 0)
    (H2 : ∀ k₀, k₀ ≤ r → f k₀ + f (p + k₀) = 0) :
    ∑ k ∈ range (p + r + 1), f k = 0 := by
  apply Finset.sum_involution
    (g := fun a _ => if a ≤ r then p + a else if a < p then a else a - p)
  · -- hg₁ : f a + f (g a) = 0
    intro a ha
    rw [Finset.mem_range] at ha
    by_cases h1 : a ≤ r
    · simp only [h1, if_true]; exact H2 a h1
    · by_cases h2 : a < p
      · simp only [h1, if_false, h2, if_true]
        rw [H1 a (by omega) h2]; ring
      · simp only [h1, if_false, h2, if_false]
        have h3 : a - p ≤ r := by omega
        have key := H2 (a - p) h3
        rw [show p + (a - p) = a by omega] at key
        rw [add_comm]; exact key
  · -- hg₃ : f a ≠ 0 → g a ≠ a
    intro a ha hfa
    rw [Finset.mem_range] at ha
    by_cases h1 : a ≤ r
    · simp only [h1, if_true]; omega
    · by_cases h2 : a < p
      · exact absurd (H1 a (by omega) h2) hfa
      · simp only [h1, if_false, h2, if_false]; omega
  · -- g_mem
    intro a ha
    rw [Finset.mem_range] at ha ⊢
    by_cases h1 : a ≤ r
    · simp only [h1, if_true]; omega
    · by_cases h2 : a < p
      · simp only [h1, if_false, h2, if_true]; omega
      · simp only [h1, if_false, h2, if_false]; omega
  · -- hg₄ : involution
    intro a ha
    rw [Finset.mem_range] at ha
    by_cases h1 : a ≤ r
    · simp only [h1, if_true]
      rw [if_neg (show ¬ p + a ≤ r by omega), if_neg (show ¬ p + a < p by omega)]
      omega
    · by_cases h2 : a < p
      · simp only [h1, h2, if_false, if_true]
      · simp only [h1, if_false, h2, if_false]
        rw [if_pos (show a - p ≤ r by omega)]
        omega

/-- `(-1)^(p+k) = -(-1)^k` in `ZMod p` for odd `p`. -/
lemma neg_one_pow_add (hodd : Odd p) (k : ℕ) :
    (-1 : ZMod p) ^ (p + k) = -((-1 : ZMod p) ^ k) := by
  rw [pow_add, Odd.neg_one_pow hodd]; ring

/-- `a(p+r) ≡ 0` for `r < p`. -/
lemma a_vanish (hp : p.Prime) (hodd : Odd p) {r : ℕ} (hr : r < p) :
    ((a (p + r) : ℤ) : ZMod p) = 0 := by
  rw [a_cast]
  exact pairing_zero hp hr (fun k => (-1 : ZMod p) ^ k * ((p + r).choose k : ZMod p) ^ 4)
    (by intro k hrk hkp; simp only; rw [choose_add_mid hp hr hrk hkp]; ring)
    (by
      intro k₀ hk
      simp only
      rw [choose_add_lo hp hr hk, choose_add_hi hp hr hk, neg_one_pow_add hodd]
      ring)

/-- `a(p-1) ≡ 1`. -/
lemma a_val (hp : p.Prime) (hodd : Odd p) : ((a (p - 1) : ℤ) : ZMod p) = 1 := by
  rw [a_cast]
  have hsum : ∀ k ∈ range (p - 1 + 1),
      (-1 : ZMod p) ^ k * (((p - 1).choose k : ZMod p)) ^ 4 = (-1 : ZMod p) ^ k := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h4 : (((-1 : ZMod p)) ^ k) ^ 4 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [choose_pred hp k (by omega), h4]; ring
  rw [Finset.sum_congr rfl hsum]
  -- ∑_{k=0}^{p-1} (-1)^k = 1
  have hpe : p - 1 + 1 = p := by have := hp.two_le; omega
  rw [hpe, neg_one_geom_sum, if_neg (Nat.not_even_iff_odd.mpr hodd)]

/-- Determinant of an "anti-triangular" Hankel matrix. -/
lemma detHankel {R : Type*} [CommRing R] :
    ∀ (n : ℕ) (s : ℕ → R), (∀ t, n ≤ t → s t = 0) →
      Matrix.det (fun i j : Fin n => s (i.val + j.val))
        = (-1 : R) ^ (n * (n - 1) / 2) * (s (n - 1)) ^ n := by
  intro n
  induction n with
  | zero => intro s hs; simp
  | succ m ih =>
    intro s hs
    rw [Matrix.det_succ_column _ (Fin.last m), Finset.sum_eq_single (0 : Fin (m + 1))]
    · -- main term i = 0
      have hminor : Matrix.submatrix (fun i j : Fin (m + 1) => s (i.val + j.val))
            (Fin.succAbove 0) (Fin.succAbove (Fin.last m))
          = (fun i j : Fin m => s (i.val + j.val + 1)) := by
        funext i j
        simp only [Matrix.submatrix_apply, Fin.succAbove_zero, Fin.succAbove_last,
          Fin.val_succ, Fin.val_castSucc]
        congr 1; omega
      rw [hminor]
      have ih' := ih (fun t => s (t + 1)) (by intro t ht; exact hs (t + 1) (by omega))
      simp only at ih'
      rw [ih']
      simp only [Fin.val_zero, Fin.val_last, Nat.zero_add]
      have hpow : (s (m - 1 + 1)) ^ m = (s m) ^ m := by
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm; simp
        · rw [show m - 1 + 1 = m by omega]
      have hexp : (m + 1) * m / 2 = m + m * (m - 1) / 2 := by
        rcases m with _ | k
        · rfl
        · have e2 : (k + 1 - 1) = k := by omega
          rw [e2]
          have hev : 2 ∣ (k + 1) * k := by
            rw [mul_comm]; exact (Nat.even_mul_succ_self k).two_dvd
          have key : (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) := by ring
          rw [key]
          omega
      rw [hpow, show (m + 1 - 1) = m by omega, hexp, pow_add, pow_succ]
      ring
    · -- terms i ≠ 0 vanish
      intro i _ hi0
      have hi : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      have hz : s (i.val + (Fin.last m).val) = 0 := by
        apply hs; rw [Fin.val_last]; omega
      rw [hz, mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- `c(p+r) ≡ 0` for `r < p`. -/
lemma c_vanish (hp : p.Prime) (hodd : Odd p) {r : ℕ} (hr : r < p) :
    ((c (p + r) : ℤ) : ZMod p) = 0 := by
  rw [c_cast]
  refine pairing_zero hp hr
    (fun k => (-1 : ZMod p) ^ k * ((p + r).choose k : ZMod p) ^ 2
        * ((2 * k).choose k : ZMod p) * ((2 * ((p + r) - k)).choose ((p + r) - k) : ZMod p))
    ?_ ?_
  · intro k hrk hkp
    simp only
    rw [choose_add_mid hp hr hrk hkp]; ring
  · intro k₀ hk
    simp only
    have hk0p : k₀ < p := lt_of_le_of_lt hk hr
    have hsp : r - k₀ < p := by omega
    have hs1 : (p + r) - k₀ = p + (r - k₀) := by omega
    have hs2 : (p + r) - (p + k₀) = r - k₀ := by omega
    rw [hs1, hs2, choose_add_lo hp hr hk, choose_add_hi hp hr hk,
        central_shift hp hsp, central_shift hp hk0p, neg_one_pow_add hodd]
    ring

/-- `c(p-1) ≡ (-1)^((p-1)/2)`. -/
lemma c_val (hp : p.Prime) (hodd : Odd p) :
    ((c (p - 1) : ℤ) : ZMod p) = (-1 : ZMod p) ^ ((p - 1) / 2) := by
  rw [c_cast]
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  set q := (p - 1) / 2 with hq
  -- simplify ((p-1).choose k)^2 = 1
  have hsq : ∀ k ∈ range ((p - 1) + 1),
      (-1 : ZMod p) ^ k * (((p - 1).choose k : ZMod p)) ^ 2 * ((2 * k).choose k : ZMod p)
          * ((2 * ((p - 1) - k)).choose ((p - 1) - k) : ZMod p)
        = (-1 : ZMod p) ^ k * ((2 * k).choose k : ZMod p)
          * ((2 * ((p - 1) - k)).choose ((p - 1) - k) : ZMod p) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hpow : (((-1 : ZMod p)) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [choose_pred hp k (by omega), hpow]; ring
  rw [Finset.sum_congr rfl hsq]
  rw [Finset.sum_eq_single q]
  · -- value at q
    have hqq : (p - 1) - q = q := by omega
    have h2q : 2 * q = p - 1 := by omega
    rw [hqq, h2q, choose_pred hp q (by omega)]
    have hq2 : (((-1 : ZMod p)) ^ q) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    linear_combination ((-1 : ZMod p) ^ q) * hq2
  · -- vanishing of other terms
    intro k hk hkq
    rw [Finset.mem_range] at hk
    rcases lt_or_gt_of_ne hkq with hlt | hgt
    · -- k < q : last central binomial vanishes
      rw [central_vanish hp (show (p - 1) - k < p by omega) (by omega)]
      ring
    · -- k > q : first central binomial vanishes
      rw [central_vanish hp (show k < p by omega) (by omega)]
      ring
  · intro hq0
    exact absurd (Finset.mem_range.mpr (by omega)) hq0

/-- Determinant mod `p` of the Hankel matrix of a sequence `g` that vanishes mod `p` past `p`. -/
lemma hankel_det_modp (hp : p.Prime) (hodd : Odd p) (g : ℕ → ℤ)
    (hvan : ∀ r, r < p → (((g (p + r)) : ℤ) : ZMod p) = 0) :
    ((Matrix.det (fun i j : Fin p => g (i.val + j.val)) : ℤ) : ZMod p)
      = (-1 : ZMod p) ^ ((p - 1) / 2) * (((g (p - 1) : ℤ) : ZMod p)) ^ p := by
  have hp2 := hp.two_le
  set s : ℕ → ZMod p := fun t => if t < p then ((g t : ℤ) : ZMod p) else 0 with hs_def
  have hmatrix : (fun i j : Fin p => ((g (i.val + j.val) : ℤ) : ZMod p))
      = (fun i j : Fin p => s (i.val + j.val)) := by
    funext i j
    by_cases hlt : i.val + j.val < p
    · simp only [hs_def, hlt, if_true]
    · have hr : (i.val + j.val) - p < p := by
        have := i.isLt; have := j.isLt; omega
      have hz : ((g (i.val + j.val) : ℤ) : ZMod p) = 0 := by
        have := hvan ((i.val + j.val) - p) hr
        rwa [show p + ((i.val + j.val) - p) = i.val + j.val by omega] at this
      rw [hz]
      simp only [hs_def, hlt, if_false]
  have hcast : ((Matrix.det (fun i j : Fin p => g (i.val + j.val)) : ℤ) : ZMod p)
      = Matrix.det (fun i j : Fin p => ((g (i.val + j.val) : ℤ) : ZMod p)) := by
    have h := (Int.castRingHom (ZMod p)).map_det (fun i j : Fin p => g (i.val + j.val))
    simpa using h
  rw [hcast, hmatrix,
      detHankel p s (by intro t ht; simp only [hs_def, if_neg (by omega : ¬ t < p)])]
  have hsp : s (p - 1) = ((g (p - 1) : ℤ) : ZMod p) := by
    simp only [hs_def, if_pos (by omega : p - 1 < p)]
  rw [hsp]
  congr 1
  have hdvd : 2 ∣ (p - 1) := by rcases hodd with ⟨k, hk⟩; omega
  rw [Nat.mul_div_assoc p hdvd, pow_mul, Odd.neg_one_pow hodd]

end

open Nat Finset Matrix in
theorem oeis_228304_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    let N := Fin p
    let half_minus_one := (p - 1) / 2
    let A : Matrix N N ℤ := fun i j => a (i.val + j.val)
    let C : Matrix N N ℤ := fun i j => c (i.val + j.val)
    (Matrix.det A ≡ (-1 : ℤ) ^ half_minus_one [ZMOD p]) ∧ (Matrix.det C ≡ 1 [ZMOD p]) := by
  intro N half_minus_one A C
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two h_odd
  show (Matrix.det (fun i j : Fin p => a (i.val + j.val)) ≡ (-1 : ℤ) ^ ((p - 1) / 2) [ZMOD p]) ∧
       (Matrix.det (fun i j : Fin p => c (i.val + j.val)) ≡ 1 [ZMOD p])
  constructor
  · apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    rw [hankel_det_modp hp hodd a (fun r hr => a_vanish hp hodd hr), a_val hp hodd,
        one_pow, mul_one]
    push_cast
    ring
  · apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    rw [hankel_det_modp hp hodd c (fun r hr => c_vanish hp hodd hr), c_val hp hodd]
    push_cast
    rw [show (-1 : ZMod p) ^ ((p - 1) / 2) * ((-1 : ZMod p) ^ ((p - 1) / 2)) ^ p
          = ((-1 : ZMod p) ^ ((p - 1) / 2)) ^ (p + 1) by rw [pow_succ]; ring,
        ← pow_mul, Even.neg_one_pow ((Odd.add_one hodd).mul_left ((p - 1) / 2))]

#print axioms oeis_228304_conjecture_0
