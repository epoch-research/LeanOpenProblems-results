import FormalConjectures.Util.ProblemImports

open Nat Finset Matrix

/--
A228304: The sequence $a(n)$ is defined by the alternating sum of fourth powers of binomial coefficients.
$$a(n) = \sum_{k=0}^n \binom{n}{k}^4 (-1)^k$$
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)

/--
A228304 c(n) sequence:
$$c(n) = \sum_{k=0}^n (-1)^k \binom{n}{k}^2 \binom{2k}{k} \binom{2(n-k)}{n-k}$$
-/
def c (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)

def aa (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k => ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 4)


def cc (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    ((-1 : ℤ) ^ k) * ((choose n k : ℤ) ^ 2) * (choose (2 * k) k : ℤ) * (choose (2 * (n - k)) (n - k) : ℤ)

lemma neg_one_pow_add_odd (k m : ℕ) : (-1 : ℤ) ^ (k + (2*m+1)) = - ((-1 : ℤ)^k) := by
  rw [pow_add]
  norm_num [pow_succ]

lemma aa_odd_zero (n : ℕ) (hn : Odd n) : aa n = 0 := by
  rcases hn with ⟨m, rfl⟩
  dsimp [aa]
  let f : ℕ → ℤ := fun k => ((-1 : ℤ) ^ k) * ((choose (2*m+1) k : ℤ) ^ 4)
  have hreflect : (∑ k ∈ range (2*m+2), f k) = ∑ k ∈ range (2*m+2), f (2*m+2 - 1 - k) := by
    simpa [f] using (Finset.sum_range_reflect f (2*m+2)).symm
  have hterm : ∀ k ∈ range (2*m+2), f (2*m+2 - 1 - k) = - f k := by
    intro k hk
    have hk_le : k ≤ 2*m+1 := by
      rw [mem_range] at hk
      omega
    have hsub : 2*m+2 - 1 - k = 2*m+1 - k := by omega
    dsimp [f]
    -- the reflected index has already simplified to `2*m+1-k`
    have hchoose : choose (2*m+1) (2*m+1 - k) = choose (2*m+1) k := by
      exact Nat.choose_symm hk_le
    rw [hchoose]
    have hpar : (2*m+1 - k) % 2 ≠ k % 2 := by omega
    have hpows : (-1 : ℤ) ^ (2*m+1 - k) = - ((-1 : ℤ)^k) := by
      rw [neg_one_pow_eq_ite, neg_one_pow_eq_ite]
      by_cases hE : Even k
      · have hOsub : Odd (2*m+1 - k) := by
          rw [← Nat.not_even_iff_odd]
          intro hEs
          have : Even ((2*m+1 - k) + k) := hEs.add hE
          rw [Nat.sub_add_cancel hk_le] at this
          exact (Nat.not_even_iff_odd.mpr ⟨m, by omega⟩) this
        have hN : ¬ Even (2*m+1 - k) := Nat.not_even_iff_odd.mpr hOsub
        simp [hE, hN]
      · have hOk : Odd k := Nat.not_even_iff_odd.mp hE
        have hEsub : Even (2*m+1 - k) := by
          rw [← Nat.not_odd_iff_even]
          intro hOs
          have : Even ((2*m+1 - k) + k) := hOs.add_odd hOk
          rw [Nat.sub_add_cancel hk_le] at this
          exact (Nat.not_even_iff_odd.mpr ⟨m, by omega⟩) this
        simp [hE, hEsub]
    rw [hpows]
    ring
  have hneg : (∑ k ∈ range (2*m+2), f k) = - (∑ k ∈ range (2*m+2), f k) := by
    calc
      (∑ k ∈ range (2*m+2), f k)
          = ∑ k ∈ range (2*m+2), f (2*m+2 - 1 - k) := hreflect
      _ = ∑ k ∈ range (2*m+2), - f k := Finset.sum_congr rfl hterm
      _ = - (∑ k ∈ range (2*m+2), f k) := Finset.sum_neg_distrib f
  have hz : (∑ k ∈ range (2*m+2), f k) = 0 := by linarith
  simpa [f] using hz


lemma cc_odd_zero (n : ℕ) (hn : Odd n) : cc n = 0 := by
  rcases hn with ⟨m, rfl⟩
  dsimp [cc]
  let f : ℕ → ℤ := fun k =>
    ((-1 : ℤ) ^ k) * ((choose (2*m+1) k : ℤ) ^ 2) * (choose (2*k) k : ℤ) * (choose (2*((2*m+1)-k)) ((2*m+1)-k) : ℤ)
  have hreflect : (∑ k ∈ range (2*m+2), f k) = ∑ k ∈ range (2*m+2), f (2*m+2 - 1 - k) := by
    simpa [f] using (Finset.sum_range_reflect f (2*m+2)).symm
  have hterm : ∀ k ∈ range (2*m+2), f (2*m+2 - 1 - k) = - f k := by
    intro k hk
    have hk_le : k ≤ 2*m+1 := by rw [mem_range] at hk; omega
    dsimp [f]
    have hidx : 2*m+2 - 1 - k = 2*m+1-k := by omega
    have hchoose : choose (2*m+1) (2*m+1-k) = choose (2*m+1) k := Nat.choose_symm hk_le
    have hsubsub : 2*m+1 - (2*m+1-k) = k := by omega
    have hpows : (-1 : ℤ) ^ (2*m+1-k) = - ((-1 : ℤ)^k) := by
      rw [neg_one_pow_eq_ite, neg_one_pow_eq_ite]
      by_cases hE : Even k
      · have hOsub : Odd (2*m+1-k) := by
          rw [← Nat.not_even_iff_odd]
          intro hEs
          have : Even ((2*m+1-k)+k) := hEs.add hE
          rw [Nat.sub_add_cancel hk_le] at this
          exact (Nat.not_even_iff_odd.mpr ⟨m, by omega⟩) this
        simp [hE, Nat.not_even_iff_odd.mpr hOsub]
      · have hOk : Odd k := Nat.not_even_iff_odd.mp hE
        have hEsub : Even (2*m+1-k) := by
          rw [← Nat.not_odd_iff_even]
          intro hOs
          have : Even ((2*m+1-k)+k) := hOs.add_odd hOk
          rw [Nat.sub_add_cancel hk_le] at this
          exact (Nat.not_even_iff_odd.mpr ⟨m, by omega⟩) this
        simp [hE, hEsub]
    rw [hpows, hchoose, hsubsub]
    ring
  have hneg : (∑ k ∈ range (2*m+2), f k) = - (∑ k ∈ range (2*m+2), f k) := by
    calc
      (∑ k ∈ range (2*m+2), f k) = ∑ k ∈ range (2*m+2), f (2*m+2 - 1 - k) := hreflect
      _ = ∑ k ∈ range (2*m+2), - f k := Finset.sum_congr rfl hterm
      _ = - (∑ k ∈ range (2*m+2), f k) := Finset.sum_neg_distrib f
  have hz : (∑ k ∈ range (2*m+2), f k) = 0 := by linarith
  simpa [f] using hz


lemma choose_p_add_cast (p d k : ℕ) [Fact p.Prime] :
    ((Nat.choose (p + d) k : ℕ) : ZMod p) =
      ((Nat.choose d k : ℕ) : ZMod p) + if p ≤ k then ((Nat.choose d (k - p) : ℕ) : ZMod p) else 0 := by
  let XX : Polynomial (ZMod p) := Polynomial.X
  have hfresh : ((1 + XX) ^ p) = (1 + XX ^ p) := by
    simpa [XX] using (add_pow_char (1 : Polynomial (ZMod p)) (Polynomial.X : Polynomial (ZMod p)) p)
  have hpoly : ((1 + XX) ^ (p+d)) = ((1 + XX^p) * (1 + XX)^d) := by
    rw [pow_add, hfresh]
  have hcoeff := congrArg (fun q : Polynomial (ZMod p) => q.coeff k) hpoly
  dsimp [XX] at hcoeff
  rw [Polynomial.coeff_one_add_X_pow] at hcoeff
  -- simplify RHS coefficient
  rw [add_mul, one_mul] at hcoeff
  rw [Polynomial.coeff_add, Polynomial.coeff_one_add_X_pow] at hcoeff
  by_cases hk : p ≤ k
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hshift : (Polynomial.X ^ p * (1 + Polynomial.X : Polynomial (ZMod p)) ^ d).coeff (p + e) =
        ((Nat.choose d e : ℕ) : ZMod p) := by
      rw [show p + e = e + p by omega]
      rw [Polynomial.coeff_X_pow_mul, Polynomial.coeff_one_add_X_pow]
    rw [hshift] at hcoeff
    simpa [Nat.add_sub_cancel_left] using hcoeff
  · have hklt : k < p := Nat.lt_of_not_ge hk
    have hzero : (Polynomial.X ^ p * (1 + Polynomial.X : Polynomial (ZMod p)) ^ d).coeff k = 0 := by
      rw [Polynomial.coeff_X_pow_mul']
      simp [hk]
    rw [hzero] at hcoeff
    simpa [hk] using hcoeff


lemma a_p_add_odd_cast (p d : ℕ) [Fact p.Prime] (hpodd : Odd p) (hd : Odd d) (hdlt : d < p) :
    ((aa (p+d) : ZMod p) = 0) := by
  dsimp [aa]
  -- cast the integer sum to zmod
  push_cast
  have hsplit := Finset.sum_range_add (fun k => ((-1 : ZMod p) ^ k) * (((choose (p+d) k : ℕ) : ZMod p) ^ 4)) p (d+1)
  change (∑ x ∈ range (p + (d+1)), ((-1 : ZMod p) ^ x) * (((p+d).choose x : ℕ) : ZMod p) ^ 4) = 0
  rw [hsplit]
  -- simplify binomial coefficients in both blocks
  simp_rw [choose_p_add_cast p d]
  -- First sum truncates at `d+1` because `choose d x=0` for `d<x`.
  have hfirst :
      (∑ x ∈ range p, (-1 : ZMod p) ^ x * (↑(d.choose x) + if p ≤ x then ↑(d.choose (x - p)) else 0) ^ 4) =
      (∑ x ∈ range (d+1), (-1 : ZMod p) ^ x * (↑(d.choose x) : ZMod p) ^ 4) := by
    have hif : ∀ x ∈ range p, (if p ≤ x then (↑(d.choose (x - p)) : ZMod p) else 0) = 0 := by
      intro x hx
      rw [mem_range] at hx
      simp [Nat.not_le_of_gt hx]
    calc
      (∑ x ∈ range p, (-1 : ZMod p) ^ x * (↑(d.choose x) + if p ≤ x then ↑(d.choose (x - p)) else 0) ^ 4)
          = ∑ x ∈ range p, (-1 : ZMod p) ^ x * (↑(d.choose x) : ZMod p) ^ 4 := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [hif x hx, add_zero]
      _ = ∑ x ∈ range (d+1), (-1 : ZMod p) ^ x * (↑(d.choose x) : ZMod p) ^ 4 := by
          exact Finset.eventually_constant_sum
            (u := fun x => (-1 : ZMod p) ^ x * (↑(d.choose x) : ZMod p) ^ 4)
            (N := d+1) (n := p)
            (by
              intro n hn
              have hdn : d < n := by omega
              simp [Nat.choose_eq_zero_of_lt hdn])
            (by omega)
  have hsecond :
      (∑ x ∈ range (d + 1),
        (-1 : ZMod p) ^ (p + x) * (↑(d.choose (p + x)) + if p ≤ p + x then ↑(d.choose (p + x - p)) else 0) ^ 4) =
      - (∑ x ∈ range (d+1), (-1 : ZMod p) ^ x * (↑(d.choose x) : ZMod p) ^ 4) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [mem_range] at hx
    have hchoose0 : d.choose (p + x) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hp_le : p ≤ p + x := Nat.le_add_right _ _
    have hsub : p + x - p = x := by omega
    have hpows : (-1 : ZMod p) ^ (p + x) = - ((-1 : ZMod p) ^ x) := by
      rw [pow_add]
      have hpoddpow : (-1 : ZMod p) ^ p = -1 := hpodd.neg_one_pow
      rw [hpoddpow]
      ring
    simp [hchoose0, hp_le, hsub, hpows]
  rw [hfirst, hsecond]
  abel


lemma choose_p_sub_one_cast (p k : ℕ) [Fact p.Prime] (hk : k ≤ p - 1) :
    (((p - 1).choose k : ℕ) : ZMod p) = (-1 : ZMod p) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hkprev : k ≤ p - 1 := by omega
      have ih' := ih hkprev
      have hksucc_lt_p : k + 1 < p := by omega
      have hnonzero : ((k+1 : ℕ) : ZMod p) ≠ 0 := by
        intro hzero
        rw [ZMod.natCast_eq_zero_iff] at hzero
        have hple : p ≤ k+1 := Nat.le_of_dvd (Nat.succ_pos k) hzero
        omega
      have hrec_nat := Nat.choose_succ_right_eq (p-1) k
      have hrec : (((p - 1).choose (k+1) : ℕ) : ZMod p) * ((k+1 : ℕ) : ZMod p) =
          (((p - 1).choose k : ℕ) : ZMod p) * ((p - 1 - k : ℕ) : ZMod p) := by
        have h := congrArg (fun n : ℕ => (n : ZMod p)) hrec_nat
        simpa [Nat.cast_mul] using h
      have hpminus : ((p - 1 - k : ℕ) : ZMod p) = - (((k+1 : ℕ) : ZMod p)) := by
        have hnat : p - 1 - k + (k+1) = p := by omega
        apply add_right_cancel (b := (((k+1 : ℕ) : ZMod p)))
        calc
          ((p - 1 - k : ℕ) : ZMod p) + ((k+1 : ℕ) : ZMod p)
              = ((p - 1 - k + (k+1) : ℕ) : ZMod p) := by exact (Nat.cast_add _ _).symm
          _ = (p : ZMod p) := by rw [hnat]
          _ = - ((k+1 : ℕ) : ZMod p) + ((k+1 : ℕ) : ZMod p) := by simp; ring
      rw [ih', hpminus] at hrec
      have : (((p - 1).choose (k+1) : ℕ) : ZMod p) = (-1 : ZMod p) ^ (k+1) := by
        apply mul_right_cancel₀ hnonzero
        rw [hrec]
        ring
      exact this

lemma central_p_add_cast (p m : ℕ) [Fact p.Prime] (hm : m < p) :
    (((2 * (p + m)).choose (p + m) : ℕ) : ZMod p) =
      (2 : ZMod p) * (((2*m).choose m : ℕ) : ZMod p) := by
  have htop : 2 * (p + m) = p + (p + 2*m) := by omega
  rw [htop]
  rw [choose_p_add_cast p (p + 2*m) (p+m)]
  have hp_le : p ≤ p + m := Nat.le_add_right _ _
  have hsub : p + m - p = m := by omega
  simp only [hp_le, if_true, hsub]
  have hsym : (p + 2*m).choose (p + m) = (p + 2*m).choose m := by
    rw [show p + m = p + 2*m - m by omega]
    rw [Nat.choose_symm (by omega)]
  rw [hsym]
  have hsmall : ¬ p ≤ m := Nat.not_le_of_gt hm
  have hchoose : (((p + 2*m).choose m : ℕ) : ZMod p) = (((2*m).choose m : ℕ) : ZMod p) := by
    have h := choose_p_add_cast p (2*m) m
    simpa [hsmall] using h
  rw [hchoose]
  ring

lemma central_cast_eq_zero_of_half_lt (p m : ℕ) [Fact p.Prime] (hm : m < p) (hhalf : p ≤ 2*m) :
    (((2*m).choose m : ℕ) : ZMod p) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact (Fact.out : Nat.Prime p).dvd_choose hm (by omega) hhalf



lemma c_p_add_odd_cast (p d : ℕ) [Fact p.Prime] (hpodd : Odd p) (hd : Odd d) (hdlt : d < p) :
    ((cc (p+d) : ZMod p) = 0) := by
  dsimp [cc]
  push_cast
  have hsplit := Finset.sum_range_add (fun k =>
    ((-1 : ZMod p) ^ k) * ((((p+d).choose k : ℕ) : ZMod p) ^ 2) * (((2*k).choose k : ℕ) : ZMod p) * (((2*((p+d)-k)).choose ((p+d)-k) : ℕ) : ZMod p)) p (d+1)
  change (∑ x ∈ range (p + (d+1)),
    (-1 : ZMod p) ^ x * (↑((p+d).choose x) : ZMod p) ^ 2 * (↑((2*x).choose x) : ZMod p) * (↑((2*((p+d)-x)).choose ((p+d)-x)) : ZMod p)) = 0
  rw [hsplit]
  simp_rw [choose_p_add_cast p d]
  have hfirst :
      (∑ x ∈ range p,
        (-1 : ZMod p) ^ x * (↑(d.choose x) + if p ≤ x then ↑(d.choose (x - p)) else 0) ^ 2 * (↑((2*x).choose x) : ZMod p) * (↑((2*((p+d)-x)).choose ((p+d)-x)) : ZMod p)) =
      (∑ x ∈ range (d+1),
        (-1 : ZMod p) ^ x * (↑(d.choose x) : ZMod p) ^ 2 * (↑((2*x).choose x) : ZMod p) * ((2 : ZMod p) * (↑((2*(d-x)).choose (d-x)) : ZMod p))) := by
    calc
      (∑ x ∈ range p,
        (-1 : ZMod p) ^ x * (↑(d.choose x) + if p ≤ x then ↑(d.choose (x - p)) else 0) ^ 2 * (↑((2*x).choose x) : ZMod p) * (↑((2*((p+d)-x)).choose ((p+d)-x)) : ZMod p))
      = ∑ x ∈ range (d+1),
        (-1 : ZMod p) ^ x * (↑(d.choose x) : ZMod p) ^ 2 * (↑((2*x).choose x) : ZMod p) * (↑((2*((p+d)-x)).choose ((p+d)-x)) : ZMod p) := by
          have hif : ∀ x ∈ range p, (if p ≤ x then (↑(d.choose (x - p)) : ZMod p) else 0) = 0 := by
            intro x hx
            rw [mem_range] at hx
            simp [Nat.not_le_of_gt hx]
          calc
            (∑ x ∈ range p,
              (-1 : ZMod p) ^ x * (↑(d.choose x) + if p ≤ x then ↑(d.choose (x - p)) else 0) ^ 2 * (↑((2*x).choose x) : ZMod p) * (↑((2*((p+d)-x)).choose ((p+d)-x)) : ZMod p))
              = ∑ x ∈ range p,
                (-1 : ZMod p) ^ x * (↑(d.choose x) : ZMod p) ^ 2 * (↑((2*x).choose x) : ZMod p) * (↑((2*((p+d)-x)).choose ((p+d)-x)) : ZMod p) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw [hif x hx, add_zero]
            _ = ∑ x ∈ range (d+1),
                (-1 : ZMod p) ^ x * (↑(d.choose x) : ZMod p) ^ 2 * (↑((2*x).choose x) : ZMod p) * (↑((2*((p+d)-x)).choose ((p+d)-x)) : ZMod p) := by
                  exact Finset.eventually_constant_sum
                    (u := fun x => (-1 : ZMod p) ^ x * (↑(d.choose x) : ZMod p) ^ 2 * (↑((2*x).choose x) : ZMod p) * (↑((2*((p+d)-x)).choose ((p+d)-x)) : ZMod p))
                    (N := d+1) (n := p)
                    (by
                      intro n hn
                      have hdn : d < n := by omega
                      simp [Nat.choose_eq_zero_of_lt hdn])
                    (by omega)
      _ = ∑ x ∈ range (d+1),
        (-1 : ZMod p) ^ x * (↑(d.choose x) : ZMod p) ^ 2 * (↑((2*x).choose x) : ZMod p) * ((2 : ZMod p) * (↑((2*(d-x)).choose (d-x)) : ZMod p)) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [mem_range] at hx
          have hpx : p + d - x = p + (d - x) := by omega
          rw [hpx]
          rw [central_p_add_cast p (d-x) (by omega)]
  have hsecond :
      (∑ x ∈ range (d + 1),
        (-1 : ZMod p) ^ (p + x) * (↑(d.choose (p + x)) + if p ≤ p + x then ↑(d.choose (p + x - p)) else 0) ^ 2 *
          (↑((2*(p+x)).choose (p+x)) : ZMod p) * (↑((2*((p+d)-(p+x))).choose ((p+d)-(p+x))) : ZMod p)) =
      - (∑ x ∈ range (d+1),
        (-1 : ZMod p) ^ x * (↑(d.choose x) : ZMod p) ^ 2 * (↑((2*x).choose x) : ZMod p) * ((2 : ZMod p) * (↑((2*(d-x)).choose (d-x)) : ZMod p))) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [mem_range] at hx
    have hchoose0 : d.choose (p + x) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hp_le : p ≤ p + x := Nat.le_add_right _ _
    have hsub : p + x - p = x := by omega
    have hsub2 : p + d - (p + x) = d - x := by omega
    have hpows : (-1 : ZMod p) ^ (p + x) = - ((-1 : ZMod p) ^ x) := by
      rw [pow_add]
      rw [hpodd.neg_one_pow]
      ring
    rw [central_p_add_cast p x (by omega)]
    simp [hchoose0, hp_le, hsub, hsub2, hpows]
    ring
  -- finish: in the first sum, terms with either central factor above halfway vanish; otherwise the two sums cancel already.
  rw [hfirst, hsecond]
  abel

lemma aa_p_sub_one_cast (p : ℕ) [Fact p.Prime] (hpodd : Odd p) : ((aa (p-1) : ZMod p) = 1) := by
  dsimp [aa]
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  rw [Nat.sub_add_cancel hp_pos]
  push_cast
  calc
    (∑ k ∈ range p, (-1 : ZMod p) ^ k * (↑((p - 1).choose k) : ZMod p) ^ 4)
        = ∑ k ∈ range p, ((-1 : ZMod p) ^ k) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [mem_range] at hk
            have hk' : k ≤ p-1 := by omega
            rw [choose_p_sub_one_cast p k hk']
            rw [show (-1 : ZMod p) ^ k * ((-1 : ZMod p) ^ k) ^ 4 = (-1 : ZMod p) ^ (k * 5) by ring]
            exact neg_one_pow_congr (R := ZMod p) (by
              constructor
              · intro h
                by_contra hkE
                have hok : Odd k := Nat.not_even_iff_odd.mp hkE
                have ho5 : Odd 5 := by norm_num
                exact (Nat.not_even_iff_odd.mpr (hok.mul ho5)) h
              · intro h
                exact h.mul_right 5)
    _ = (∑ k : Fin p, (-1 : ZMod p) ^ k.val) := by
          rw [Fin.sum_univ_eq_sum_range]
    _ = 1 := by
          rw [Fin.sum_neg_one_pow]
          simp [Nat.not_even_iff_odd.mpr hpodd]



lemma cc_p_sub_one_cast (h : ℕ) (p : ℕ) [Fact p.Prime] (hp : p = 2*h+1) :
    ((cc (p-1) : ZMod p) = (-1 : ZMod p) ^ h) := by
  subst hp
  dsimp [cc]
  have hp_pos : 0 < 2*h+1 := by omega
  push_cast
  let mid : ℕ := h
  have hmidmem : mid ∈ range (2*h+1) := by simp [mid]; omega
  rw [Finset.sum_eq_single mid]
  · simp [mid]
    have hchoose := choose_p_sub_one_cast (2*h+1) h (by omega)
    have hch : (((2*h).choose h : ℕ) : ZMod (2*h+1)) = (-1 : ZMod (2*h+1)) ^ h := by
      simpa [show 2*h+1-1 = 2*h by omega] using hchoose
    have hsubh : 2*h - h = h := by omega
    rw [hsubh, hch]
    rw [show (-1 : ZMod (2*h+1)) ^ h * ((-1 : ZMod (2*h+1)) ^ h) ^ 2 * ((-1 : ZMod (2*h+1)) ^ h) * ((-1 : ZMod (2*h+1)) ^ h) = (-1 : ZMod (2*h+1)) ^ (h * 5) by ring]
    exact neg_one_pow_congr (R := ZMod (2*h+1)) (by
      constructor
      · intro hh
        by_contra hE
        have hoh : Odd h := Nat.not_even_iff_odd.mp hE
        have ho5 : Odd 5 := by norm_num
        exact (Nat.not_even_iff_odd.mpr (hoh.mul ho5)) hh
      · intro hh
        exact hh.mul_right 5)
  · intro k hk hne
    rw [mem_range] at hk
    by_cases hklt : k < h
    · have mlt : 2*h - k < 2*h+1 := by omega
      have hhalf : 2*h+1 ≤ 2*(2*h - k) := by omega
      have hz := central_cast_eq_zero_of_half_lt (2*h+1) (2*h-k) mlt hhalf
      have hsub : 2*h - k = (2*h+1) - 1 - k := by omega
      simp [hsub.symm, hz]
    · have hkgt : h < k := by omega
      have hhalf : 2*h+1 ≤ 2*k := by omega
      have hz := central_cast_eq_zero_of_half_lt (2*h+1) k hk hhalf
      simp [hz]
  · intro hnot
    exact (hnot hmidmem).elim


lemma sign_revPerm_odd (h : ℕ) :
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (2*h+1))) : ℤ) : ℤ) = (-1 : ℤ) ^ h := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  simp only [Fin.revPerm_apply]
  simp only [Fin.rev_lt_rev]
  have hinner : ∀ x : Fin (2*h+1),
      (∏ i ∈ Ioi x, ((if i < x then 1 else -1 : ℤˣ) : ℤ)) = (-1 : ℤ) ^ (Ioi x).card := by
    intro x
    calc
      (∏ i ∈ Ioi x, ((if i < x then 1 else -1 : ℤˣ) : ℤ))
          = ∏ i ∈ Ioi x, (-1 : ℤ) := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [mem_Ioi] at hi
              simp [not_lt_of_gt hi]
      _ = (-1 : ℤ) ^ (Ioi x).card := by simp
  push_cast
  simp_rw [hinner]
  rw [Finset.prod_pow_eq_pow_sum]
  apply neg_one_pow_congr (R := ℤ)
  have hsum : (∑ x : Fin (2*h+1), (Ioi x).card) = h * (2*h+1) := by
    simp only [Fin.card_Ioi]
    change (∑ x : Fin (2*h+1), (2*h - x.val)) = h * (2*h+1)
    rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => 2*h - x)]
    rw [show (∑ x ∈ range (2*h+1), (2*h - x)) = (∑ x ∈ range (2*h+1), x) by
      simpa using (Finset.sum_range_reflect (fun x => x) (2*h+1))]
    rw [Finset.sum_range_id]
    rw [show (2*h+1 - 1) = 2*h by omega]
    rw [show 2*h = h*2 by omega]
    rw [show (h*2 + 1) * (h * 2) = ((h*2 + 1) * h) * 2 by ring]
    rw [Nat.mul_div_left ((h*2 + 1) * h) (by decide : 0 < 2)]
    ring
  rw [hsum]
  constructor
  · intro he
    by_cases hh : Even h
    · exact hh
    · have hoh : Odd h := Nat.not_even_iff_odd.mp hh
      have hon : Odd (2*h+1) := ⟨h, by omega⟩
      have : Odd (h * (2*h+1)) := hoh.mul hon
      exact (Nat.not_even_iff_odd.mpr this he).elim
  · intro hh
    exact hh.mul_right (2*h+1)

lemma det_hankel_high (h : ℕ) (s : ℕ → ZMod (2*h+1)) (v : ZMod (2*h+1))
    (hzero : ∀ n, 2*h+1 ≤ n → n < 2*(2*h+1) - 1 → s n = 0)
    (hdiag : s (2*h) = v) :
    (Matrix.det (fun i j : Fin (2*h+1) => s (i.val + j.val))) = (-1 : ZMod (2*h+1)) ^ h * v ^ (2*h+1) := by
  let M : Matrix (Fin (2*h+1)) (Fin (2*h+1)) (ZMod (2*h+1)) := fun i j => s (i.val + j.val)
  have hperm := Matrix.det_permute' (Fin.revPerm : Equiv.Perm (Fin (2*h+1))) M
  have htri : (M.submatrix id (Fin.revPerm : Equiv.Perm (Fin (2*h+1)))).BlockTriangular id := by
    intro i j hij
    dsimp [M]
    have hjlt : j.val < i.val := hij
    have hsumn : 2*h+1 ≤ i.val + (Fin.rev j).val := by
      simp [Fin.rev]
      omega
    have hlt : i.val + (Fin.rev j).val < 2*(2*h+1) - 1 := by
      have hi := i.isLt; have hj := (Fin.rev j).isLt
      omega
    exact hzero _ hsumn hlt
  have hdettri : (M.submatrix id (Fin.revPerm : Equiv.Perm (Fin (2*h+1)))).det = v ^ (2*h+1) := by
    rw [Matrix.det_of_upperTriangular htri]
    trans ∏ _i : Fin (2*h+1), v
    · apply Finset.prod_congr rfl
      intro i hi
      dsimp [M]
      have hsum : i.val + (2*h+1 - (i.val + 1)) = 2*h := by
        simpa [Fin.rev] using (Fin.add_rev_cast i)
      rw [hsum, hdiag]
    · simp
  have hsign : (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (2*h+1))) : ℤ) : ZMod (2*h+1))) = (-1 : ZMod (2*h+1)) ^ h := by
    calc
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (2*h+1))) : ℤ) : ZMod (2*h+1)))
          = ((((-1 : ℤ) ^ h) : ℤ) : ZMod (2*h+1)) := congrArg (fun z : ℤ => (z : ZMod (2*h+1))) (sign_revPerm_odd h)
      _ = (-1 : ZMod (2*h+1)) ^ h := by simp
  have hrel : (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (2*h+1))) : ℤ) : ZMod (2*h+1))) * Matrix.det M = v ^ (2*h+1) := by
    simpa [M] using hperm.symm.trans hdettri
  calc
    Matrix.det (fun i j : Fin (2*h+1) => s (i.val + j.val)) = Matrix.det M := rfl
    _ = (-1 : ZMod (2*h+1)) ^ h * v ^ (2*h+1) := by
      rw [← hrel, hsign]
      rw [← mul_assoc]
      have hsquare : (-1 : ZMod (2*h+1)) ^ h * (-1 : ZMod (2*h+1)) ^ h = 1 := by
        rw [← pow_add]
        have : Even (h + h) := ⟨h, by omega⟩
        simpa using (this.neg_one_pow (α := ZMod (2*h+1)))
      rw [hsquare, one_mul]

theorem test_main (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    let N := Fin p
    let half_minus_one := (p - 1) / 2
    let A : Matrix N N ℤ := fun i j => aa (i.val + j.val)
    let C : Matrix N N ℤ := fun i j => cc (i.val + j.val)
    (Matrix.det A ≡ (-1 : ℤ) ^ half_minus_one [ZMOD p]) ∧ (Matrix.det C ≡ 1 [ZMOD p]) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two h_odd
  rcases hpodd with ⟨h, hp_eq⟩
  subst hp_eq
  simp only
  constructor
  · rw [← ZMod.intCast_eq_intCast_iff]
    change (Int.castRingHom (ZMod (2*h+1))) (Matrix.det (fun i j : Fin (2*h+1) => (aa (i.val + j.val) : ℤ))) = ((((-1 : ℤ) ^ (((2*h+1)-1)/2)) : ℤ) : ZMod (2*h+1))
    rw [RingHom.map_det]
    change Matrix.det (fun i j : Fin (2*h+1) => ((aa (i.val+j.val) : ℤ) : ZMod (2*h+1))) = _
    have hdet := det_hankel_high h (fun n => ((aa n : ℤ) : ZMod (2*h+1))) 1 ?_ ?_
    · rw [hdet]
      simp [show ((2*h+1)-1)/2 = h by omega]
    · intro n hn hnlt
      by_cases hono : Odd n
      · simp [aa_odd_zero n hono]
      · have hdodd : Odd (n - (2*h+1)) := by
          rcases (Nat.not_odd_iff_even.mp hono) with ⟨r, hr⟩
          use r - h - 1
          omega
        have hdlt : n - (2*h+1) < 2*h+1 := by omega
        have hnadd : n = (2*h+1) + (n - (2*h+1)) := by omega
        rw [hnadd]
        exact a_p_add_odd_cast (2*h+1) (n-(2*h+1)) ⟨h, by omega⟩ hdodd hdlt
    · simpa [show 2*h+1-1=2*h by omega] using aa_p_sub_one_cast (2*h+1) ⟨h, by omega⟩
  · rw [← ZMod.intCast_eq_intCast_iff]
    change (Int.castRingHom (ZMod (2*h+1))) (Matrix.det (fun i j : Fin (2*h+1) => (cc (i.val + j.val) : ℤ))) = (1 : ZMod (2*h+1))
    rw [RingHom.map_det]
    change Matrix.det (fun i j : Fin (2*h+1) => ((cc (i.val+j.val) : ℤ) : ZMod (2*h+1))) = _
    have hdet := det_hankel_high h (fun n => ((cc n : ℤ) : ZMod (2*h+1))) ((-1 : ZMod (2*h+1))^h) ?_ ?_
    · rw [hdet]
      have hpoddpow : ((-1 : ZMod (2*h+1)) ^ h) ^ (2*h+1) = (-1 : ZMod (2*h+1)) ^ h := by
        rw [← pow_mul]
        apply neg_one_pow_congr (R := ZMod (2*h+1))
        constructor
        · intro he
          by_cases hh : Even h
          · exact hh
          · have hoh : Odd h := Nat.not_even_iff_odd.mp hh
            have hon : Odd (2*h+1) := ⟨h, by omega⟩
            exact (Nat.not_even_iff_odd.mpr (hoh.mul hon) he).elim
        · intro hh; exact hh.mul_right (2*h+1)
      rw [hpoddpow]
      rw [← pow_add]
      have : Even (h+h) := ⟨h, by omega⟩
      simpa using (this.neg_one_pow (α := ZMod (2*h+1)))
    · intro n hn hnlt
      by_cases hono : Odd n
      · simp [cc_odd_zero n hono]
      · have hdodd : Odd (n - (2*h+1)) := by
          rcases (Nat.not_odd_iff_even.mp hono) with ⟨r, hr⟩
          use r - h - 1
          omega
        have hdlt : n - (2*h+1) < 2*h+1 := by omega
        have hnadd : n = (2*h+1) + (n - (2*h+1)) := by omega
        rw [hnadd]
        exact c_p_add_odd_cast (2*h+1) (n-(2*h+1)) ⟨h, by omega⟩ hdodd hdlt
    · simpa [show 2*h+1-1=2*h by omega] using cc_p_sub_one_cast h (2*h+1) rfl


/--
A228304 Conjecture: Let p be any odd prime, and let A(p) be the p X p determinant with (i,j)-entry equal to a(i+j) for all i,j = 0,...,p-1. Then A(p) == (-1)^{(p-1)/2} (mod p). Similarly, if c(n) = sum_{k=0}^n (-1)^k*C(n,k)^2*C(2k,k)*C(2(n-k),n-k) and C(p) is the p X p determinant with (i,j)-entry equal to c(i+j) for all i,j = 0,...,p-1, then we have C(p) == 1 (mod p).
-/
theorem oeis_228304_conjecture_0 (p : ℕ) (hp : Nat.Prime p) (h_odd : p ≠ 2) :
    let N := Fin p
    let half_minus_one := (p - 1) / 2
    -- A(p) is the p x p matrix with entries a(i+j)
    let A : Matrix N N ℤ := fun i j => a (i.val + j.val)
    -- C(p) is the p x p matrix with entries c(i+j)
    let C : Matrix N N ℤ := fun i j => c (i.val + j.val)
    (Matrix.det A ≡ (-1 : ℤ) ^ half_minus_one [ZMOD p]) ∧ (Matrix.det C ≡ 1 [ZMOD p]) := by
  change
    let N := Fin p
    let half_minus_one := (p - 1) / 2
    let A : Matrix N N ℤ := fun i j => aa (i.val + j.val)
    let C : Matrix N N ℤ := fun i j => cc (i.val + j.val)
    (Matrix.det A ≡ (-1 : ℤ) ^ half_minus_one [ZMOD p]) ∧ (Matrix.det C ≡ 1 [ZMOD p])
  exact test_main p hp h_odd
