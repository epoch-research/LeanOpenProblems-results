import FormalConjectures.Util.ProblemImports

open Matrix Nat Int

/--
A226163: Determinant of the $(p_n-1)/2$-by-$(p_n-1)/2$ matrix with $(i,j)$-entry being the Legendre symbol
$$\left(\frac{i^2 - \left(\frac{p_n-1}{2}\right)! \cdot j}{p_n}\right)$$
where $p_n$ is the $n$-th prime.
The sequence is naturally indexed starting from $n=2$.
-/
noncomputable def A226163 (n : ℕ) : ℤ :=
  if h : n < 2 then 0 else

  -- p is the n-th prime, p_n. Mathlib's nth Nat.Prime is 0-indexed, so we use (n-1).
  -- Since n >= 2, p >= 3 is an an odd prime.
  let p : ℕ := Nat.nth Nat.Prime (n - 1)

  -- Matrix dimension m = (p-1)/2.
  let m : ℕ := (p - 1) / 2

  -- The constant C = ((p-1)/2)! as an integer.
  let C : ℤ := m.factorial.cast

  -- The matrix M has entries in ℤ.
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    -- 1-based indices i' and j' for the formula: 1 <= i', j' <= m.
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast

    -- Argument for the Legendre symbol: i'^2 - C * j'
    let arg : ℤ := i' * i' - C * j'

    -- jacobiSym is the Legendre symbol since p is prime.
    jacobiSym arg p

  M.det

/- Auxiliary facts -/

namespace OEIS226163

open Polynomial

lemma nth_prime_ne_two {n : ℕ} (hn : 2 ≤ n) :
    Nat.nth Nat.Prime (n - 1) ≠ 2 := by
  have hle := add_two_le_nth_prime (n - 1)
  have : 3 ≤ Nat.nth Nat.Prime (n - 1) := by
    have : n - 1 + 2 = n + 1 := by omega
    omega
  omega

lemma nth_prime_odd {n : ℕ} (hn : 2 ≤ n) :
    Odd (Nat.nth Nat.Prime (n - 1)) :=
  (prime_nth_prime (n - 1)).odd_of_ne_two (nth_prime_ne_two hn)

lemma two_mul_half_pred {p : ℕ} (hp : Odd p) : 2 * ((p - 1) / 2) = p - 1 := by
  obtain ⟨k, hk⟩ := hp
  have : p - 1 = 2 * k := by omega
  rw [this, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

lemma p_div_two_eq {p : ℕ} (hp : Odd p) : p / 2 = (p - 1) / 2 := by
  obtain ⟨k, rfl⟩ := hp
  simp [Nat.add_div, Nat.mul_div_right]

lemma m_lt_p {p : ℕ} [Fact p.Prime] : (p - 1) / 2 < p := by
  have hppos : 0 < p := (Fact.out : p.Prime).pos
  have : (p - 1) / 2 ≤ p - 1 := Nat.div_le_self _ _
  omega

lemma one_add_val_lt_p {p : ℕ} [Fact p.Prime] (i : Fin ((p - 1) / 2)) :
    i.val + 1 < p := by
  have := i.isLt
  have := m_lt_p (p := p)
  omega

lemma one_add_val_ne_zero {p : ℕ} [Fact p.Prime] (i : Fin ((p - 1) / 2)) :
    ((i.val + 1 : ℕ) : ZMod p) ≠ 0 := by
  intro h
  have hlt := one_add_val_lt_p (p := p) i
  have : p ∣ i.val + 1 := (ZMod.natCast_eq_zero_iff _ _).1 h
  have hpos : 0 < i.val + 1 := Nat.succ_pos _
  have : p ≤ i.val + 1 := Nat.le_of_dvd hpos this
  omega

lemma factorial_half_sq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (((p - 1) / 2)! : ZMod p) ^ 2 = (-1) ^ (((p - 1) / 2) + 1) := by
  set m := (p - 1) / 2
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hW : ((p - 1)! : ZMod p) = -1 := ZMod.wilsons_lemma p
  have hm_le : m ≤ p - 1 := Nat.div_le_self _ _
  have hsub : p - 1 - m = m := by
    have := two_mul_half_pred hp_odd
    omega
  have hfac : (p - 1)! = m ! * (p - 1).descFactorial m := by
    have := Nat.factorial_mul_descFactorial hm_le
    rw [hsub] at this
    rw [← this, mul_comm]
  have hm_le' : m ≤ p := (m_lt_p (p := p)).le
  have hdesc : ((p - 1).descFactorial m : ZMod p) = (-1) ^ m * (m ! : ZMod p) :=
    ZMod.cast_descFactorial hm_le'
  have hprod : ((p - 1)! : ZMod p) =
      (m ! : ZMod p) * ((-1) ^ m * (m ! : ZMod p)) := by
    rw [hfac, Nat.cast_mul, hdesc]
  have h1 : (m ! : ZMod p) ^ 2 * (-1) ^ m = -1 := by
    calc
      (m ! : ZMod p) ^ 2 * (-1) ^ m
          = ((m ! : ZMod p) * (m ! : ZMod p)) * (-1) ^ m := by ring
      _ = (m ! : ZMod p) * ((-1) ^ m * (m ! : ZMod p)) := by ring
      _ = ((p - 1)! : ZMod p) := hprod.symm
      _ = -1 := hW
  have hneg : ((-1 : ZMod p) ^ m) * ((-1 : ZMod p) ^ m) = 1 := by
    rw [← pow_add, ← two_mul]
    simp
  calc
    (m ! : ZMod p) ^ 2
        = (m ! : ZMod p) ^ 2 * 1 := by ring
    _ = (m ! : ZMod p) ^ 2 * (((-1 : ZMod p) ^ m) * ((-1 : ZMod p) ^ m)) := by
        rw [hneg]
    _ = ((m ! : ZMod p) ^ 2 * ((-1 : ZMod p) ^ m)) * ((-1 : ZMod p) ^ m) := by ring
    _ = (-1) * ((-1 : ZMod p) ^ m) := by rw [h1]
    _ = (-1) ^ (m + 1) := by
        rw [pow_succ, mul_comm]

lemma factorial_half_sq_of_one_mod_four {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    (((p - 1) / 2)! : ZMod p) ^ 2 = -1 := by
  have hp2 : p ≠ 2 := by intro h; subst h; simp at hp
  have hmain := factorial_half_sq (p := p) hp2
  have hodd : Odd (((p - 1) / 2) + 1) := by
    have : ((p - 1) / 2 + 1) % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  simpa [Odd.neg_one_pow hodd] using hmain

lemma factorial_half_sq_of_three_mod_four {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    (((p - 1) / 2)! : ZMod p) ^ 2 = 1 := by
  have hp2 : p ≠ 2 := by intro h; subst h; simp at hp
  have hmain := factorial_half_sq (p := p) hp2
  have heven : Even (((p - 1) / 2) + 1) := by
    have : ((p - 1) / 2 + 1) % 2 = 0 := by omega
    exact Nat.even_iff.2 this
  simpa [Even.neg_one_pow heven] using hmain

noncomputable def evalMatrix (p : ℕ) : Matrix (Fin ((p - 1) / 2)) (Fin ((p - 1) / 2)) ℤ :=
  fun i j =>
    let i' : ℤ := (i.val + 1 : ℕ)
    let j' : ℤ := (j.val + 1 : ℕ)
    let C : ℤ := (((p - 1) / 2)! : ℤ)
    jacobiSym (i' * i' - C * j') p

lemma A226163_eq {n : ℕ} (hn : 2 ≤ n) :
    A226163 n = (evalMatrix (Nat.nth Nat.Prime (n - 1))).det := by
  unfold A226163 evalMatrix
  have : ¬ n < 2 := not_lt.mpr hn
  simp [this]

lemma jacobiSym_eq_legendre {p : ℕ} [Fact p.Prime] (a : ℤ) :
    jacobiSym a p = legendreSym p a :=
  (jacobiSym.legendreSym.to_jacobiSym p a).symm

lemma evalMatrix_apply {p : ℕ} [Fact p.Prime] (i j : Fin ((p - 1) / 2)) :
    evalMatrix p i j =
      legendreSym p
        (((i.val + 1 : ℕ) : ℤ) * ((i.val + 1 : ℕ) : ℤ) -
          ((((p - 1) / 2)! : ℤ) * ((j.val + 1 : ℕ) : ℤ))) := by
  simp [evalMatrix, jacobiSym_eq_legendre]

lemma odd_p {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : Odd p :=
  (Fact.out : p.Prime).odd_of_ne_two hp2

lemma evalMatrix_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (i j : Fin ((p - 1) / 2)) :
    ((evalMatrix p i j : ℤ) : ZMod p) =
      ((((i.val + 1 : ℕ) : ZMod p) ^ 2 -
          ((((p - 1) / 2)! : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))) ^ ((p - 1) / 2)) := by
  rw [evalMatrix_apply, legendreSym.eq_pow]
  have hdiv : p / 2 = (p - 1) / 2 := p_div_two_eq (odd_p hp2)
  simp [hdiv, pow_two]

def powMatrix (p : ℕ) [Fact p.Prime] :
    Matrix (Fin ((p - 1) / 2)) (Fin ((p - 1) / 2)) (ZMod p) :=
  fun i j =>
    ((((i.val + 1 : ℕ) : ZMod p) ^ 2 -
        ((((p - 1) / 2)! : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))) ^ ((p - 1) / 2))

lemma evalMatrix_map_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (evalMatrix p).map (Int.cast : ℤ → ZMod p) = powMatrix p := by
  ext i j
  simpa [powMatrix, Matrix.map_apply] using evalMatrix_zmod (p := p) hp2 i j

lemma vandermonde_nodes_injective {p : ℕ} [Fact p.Prime] :
    Function.Injective (fun i : Fin ((p - 1) / 2) => ((i.val + 1 : ℕ) : ZMod p)) := by
  intro i j h
  have hi := one_add_val_lt_p (p := p) i
  have hj := one_add_val_lt_p (p := p) j
  have hi' : ((i.val + 1 : ℕ) : ZMod p).val = i.val + 1 := ZMod.val_natCast_of_lt hi
  have hj' : ((j.val + 1 : ℕ) : ZMod p).val = j.val + 1 := ZMod.val_natCast_of_lt hj
  have : i.val + 1 = j.val + 1 := by
    rw [← hi', ← hj']
    exact congrArg ZMod.val h
  exact Fin.ext (by omega)

lemma moments_zero_imp_eq_zero {p : ℕ} [Fact p.Prime]
    (v : Fin ((p - 1) / 2) → ZMod p)
    (h : ∀ k : Fin ((p - 1) / 2),
      ∑ j : Fin ((p - 1) / 2), v j * ((j.val + 1 : ℕ) : ZMod p) ^ (k.val : ℕ) = 0) :
    v = 0 := by
  let nodes : Fin ((p - 1) / 2) → ZMod p := fun i => (i.val + 1 : ℕ)
  have hinj : Function.Injective nodes := vandermonde_nodes_injective (p := p)
  exact eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj (fun i => by
    simpa [nodes] using h i)

lemma C_ne_zero {p : ℕ} [Fact p.Prime] :
    (((p - 1) / 2)! : ZMod p) ≠ 0 := by
  have hp : p.Prime := Fact.out
  intro h
  have : p ∣ ((p - 1) / 2)! := (ZMod.natCast_eq_zero_iff _ _).1 h
  have : p ≤ (p - 1) / 2 := (hp.dvd_factorial).1 this
  have := m_lt_p (p := p)
  omega

/- Forward-difference binomial identities. -/

lemma sum_signed_choose_pow {R : Type*} [CommRing R] (m k : ℕ) :
    ∑ t ∈ Finset.range (m + 1),
      ((-1 : R) ^ (m - t) * (m.choose t : R)) * (t : R) ^ k =
    ((fwdDiff (1 : R))^[m] (fun r : R => r ^ k)) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp [nsmul_eq_mul, zsmul_eq_mul]

lemma sum_signed_choose_pow_of_lt {R : Type*} [CommRing R] {m k : ℕ} (h : k < m) :
    ∑ t ∈ Finset.range (m + 1),
      ((-1 : R) ^ (m - t) * (m.choose t : R)) * (t : R) ^ k = 0 := by
  rw [sum_signed_choose_pow, fwdDiff_iter_pow_eq_zero_of_lt h]
  simp

lemma sum_signed_choose_pow_eq_factorial {R : Type*} [CommRing R] (m : ℕ) :
    ∑ t ∈ Finset.range (m + 1),
      ((-1 : R) ^ (m - t) * (m.choose t : R)) * (t : R) ^ m = (m ! : R) := by
  rw [sum_signed_choose_pow, fwdDiff_iter_eq_factorial]
  simp

lemma sum_signed_choose_eq_zero {R : Type*} [CommRing R] {m : ℕ} (hm : 0 < m) :
    ∑ t ∈ Finset.range (m + 1), ((-1 : R) ^ (m - t) * (m.choose t : R)) = 0 := by
  have := sum_signed_choose_pow_of_lt (R := R) (k := 0) (m := m) hm
  simpa using this

lemma m_pos {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : 0 < (p - 1) / 2 := by
  have hp_odd := odd_p hp2
  have h2 := two_mul_half_pred hp_odd
  have hppos : 2 < p := (Fact.out : p.Prime).two_le.lt_of_ne' hp2
  omega

lemma sq_nodes_injective {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Function.Injective (fun i : Fin ((p - 1) / 2) =>
      ((i.val + 1 : ℕ) : ZMod p) ^ 2) := by
  intro i j h
  set a := ((i.val + 1 : ℕ) : ZMod p)
  set b := ((j.val + 1 : ℕ) : ZMod p)
  have : a = b ∨ a = -b := sq_eq_sq_iff_eq_or_eq_neg.1 h
  rcases this with h | h
  · exact vandermonde_nodes_injective (p := p) h
  · have hab : a + b = 0 := by
      rw [h, neg_add_cancel]
    have hsum : i.val + 1 + (j.val + 1) < p := by
      have hm := two_mul_half_pred (odd_p hp2)
      have := i.isLt
      have := j.isLt
      omega
    have hcast : ((i.val + 1 + (j.val + 1) : ℕ) : ZMod p) = a + b := by
      simp [a, b]
    have hz : ((i.val + 1 + (j.val + 1) : ℕ) : ZMod p) = 0 := by
      rw [hcast, hab]
    have : p ∣ i.val + 1 + (j.val + 1) := (ZMod.natCast_eq_zero_iff _ _).1 hz
    have hpos : 0 < i.val + 1 + (j.val + 1) := by omega
    have : p ≤ i.val + 1 + (j.val + 1) := Nat.le_of_dvd hpos this
    omega

lemma sq_pow_eq_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (i : Fin ((p - 1) / 2)) :
    (((i.val + 1 : ℕ) : ZMod p) ^ 2) ^ ((p - 1) / 2) = 1 := by
  have ha : ((i.val + 1 : ℕ) : ZMod p) ≠ 0 := one_add_val_ne_zero i
  have hfermat : ((i.val + 1 : ℕ) : ZMod p) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one ha
  have h2 := two_mul_half_pred (odd_p hp2)
  calc
    (((i.val + 1 : ℕ) : ZMod p) ^ 2) ^ ((p - 1) / 2)
        = ((i.val + 1 : ℕ) : ZMod p) ^ (2 * ((p - 1) / 2)) := by rw [pow_mul]
    _ = ((i.val + 1 : ℕ) : ZMod p) ^ (p - 1) := by rw [h2]
    _ = 1 := hfermat

/-- The interpolating polynomial `∑ⱼ vⱼ (X - C·(j+1))^m`. -/
noncomputable def kernelPoly {p : ℕ} [Fact p.Prime]
    (v : Fin ((p - 1) / 2) → ZMod p) : Polynomial (ZMod p) :=
  ∑ j : Fin ((p - 1) / 2),
    C (v j) * (X - C ((((p - 1) / 2)! : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))) ^ ((p - 1) / 2)

lemma kernelPoly_eval {p : ℕ} [Fact p.Prime]
    (v : Fin ((p - 1) / 2) → ZMod p) (i : Fin ((p - 1) / 2)) :
    (kernelPoly v).eval (((i.val + 1 : ℕ) : ZMod p) ^ 2) =
      (powMatrix p *ᵥ v) i := by
  simp only [kernelPoly, powMatrix, mulVec, dotProduct, eval_finset_sum, eval_mul, eval_C,
    eval_pow, eval_sub, eval_X]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma kernelPoly_natDegree_le {p : ℕ} [Fact p.Prime]
    (v : Fin ((p - 1) / 2) → ZMod p) :
    (kernelPoly v).natDegree ≤ (p - 1) / 2 := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  have hle := natDegree_pow_le_of_le ((p - 1) / 2)
    (natDegree_X_sub_C
      ((((p - 1) / 2)! : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))).le
  simpa using hle

lemma evalMatrix_det_eq_zero_imp_pow {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (h : (evalMatrix p).det = 0) : (powMatrix p).det = 0 := by
  have hmap := (Int.castRingHom (ZMod p)).map_det (evalMatrix p)
  -- `↑(det) = det (mapMatrix)`
  have h0 : ((Int.castRingHom (ZMod p)).mapMatrix (evalMatrix p)).det = 0 := by
    rw [← hmap, h, map_zero]
  have hmeq : (Int.castRingHom (ZMod p)).mapMatrix (evalMatrix p) =
      (evalMatrix p).map (Int.cast : ℤ → ZMod p) := rfl
  rw [hmeq, evalMatrix_map_zmod hp2] at h0
  exact h0

lemma powMatrix_det_eq_zero_iff {p : ℕ} [Fact p.Prime] :
    (powMatrix p).det = 0 ↔ ∃ v : Fin ((p - 1) / 2) → ZMod p, v ≠ 0 ∧ powMatrix p *ᵥ v = 0 :=
  (Matrix.exists_mulVec_eq_zero_iff).symm

/-- Signed binomial vector `vᵢ = (-1)^{m-(i+1)} binom(m, i+1)`. -/
def binomVec (p : ℕ) : Fin ((p - 1) / 2) → ZMod p :=
  fun i =>
    (-1 : ZMod p) ^ (((p - 1) / 2) - (i.val + 1)) *
      (((p - 1) / 2).choose (i.val + 1) : ZMod p)


lemma binomVec_last {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    binomVec p ⟨(p - 1) / 2 - 1, by have := m_pos hp2; omega⟩ = 1 := by
  have hm : 0 < (p - 1) / 2 := m_pos hp2
  simp [binomVec]
  have : (p - 1) / 2 - 1 + 1 = (p - 1) / 2 := by omega
  simp [this]

lemma binomVec_moment {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    ∑ i : Fin ((p - 1) / 2),
      binomVec p i * ((i.val + 1 : ℕ) : ZMod p) ^ k =
    ∑ t ∈ Finset.range (((p - 1) / 2) + 1),
      ((-1 : ZMod p) ^ (((p - 1) / 2) - t) *
        (((p - 1) / 2).choose t : ZMod p)) * (t : ZMod p) ^ k := by
  set m := (p - 1) / 2
  let g : ℕ → ZMod p := fun t =>
    ((-1 : ZMod p) ^ (m - t) * (m.choose t : ZMod p)) * (t : ZMod p) ^ k
  have hRHS : ∑ t ∈ Finset.range (m + 1), g t = ∑ t ∈ Finset.range m, g (t + 1) := by
    rw [Finset.sum_range_succ']
    have : g 0 = 0 := by simp [g, zero_pow hk.ne']
    simp [this]
  have hLHS :
      ∑ i : Fin m, binomVec p i * ((i.val + 1 : ℕ) : ZMod p) ^ k =
        ∑ t ∈ Finset.range m, g (t + 1) := by
    trans ∑ i : Fin m, g (i.val + 1)
    · refine Fintype.sum_congr _ _ fun i => ?_
      simp [binomVec, g, m]
    · exact (Finset.sum_range (fun t => g (t + 1))).symm
  simp [g] at hLHS hRHS ⊢
  rw [hLHS, hRHS]

lemma binomVec_moment_of_lt {p : ℕ} [Fact p.Prime] {k : ℕ}
    (hk : 0 < k) (hkm : k < (p - 1) / 2) :
    ∑ i : Fin ((p - 1) / 2),
      binomVec p i * ((i.val + 1 : ℕ) : ZMod p) ^ k = 0 := by
  rw [binomVec_moment hk, sum_signed_choose_pow_of_lt hkm]

lemma binomVec_moment_eq_factorial {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∑ i : Fin ((p - 1) / 2),
      binomVec p i * ((i.val + 1 : ℕ) : ZMod p) ^ ((p - 1) / 2) =
      (((p - 1) / 2)! : ZMod p) := by
  have hm : 0 < (p - 1) / 2 := m_pos hp2
  rw [binomVec_moment hm, sum_signed_choose_pow_eq_factorial]

lemma binomVec_sum {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∑ i : Fin ((p - 1) / 2), binomVec p i =
      (-1 : ZMod p) ^ (((p - 1) / 2) + 1) := by
  have hm : 0 < (p - 1) / 2 := m_pos hp2
  set m := (p - 1) / 2
  let g : ℕ → ZMod p := fun t => (-1 : ZMod p) ^ (m - t) * (m.choose t : ZMod p)
  have hsum : ∑ t ∈ Finset.range (m + 1), g t = 0 :=
    sum_signed_choose_eq_zero (R := ZMod p) hm
  have hsplit : ∑ t ∈ Finset.range (m + 1), g t = g 0 + ∑ t ∈ Finset.range m, g (t + 1) := by
    rw [Finset.sum_range_succ']
    abel
  have hg0 : g 0 = (-1 : ZMod p) ^ m := by simp [g]
  have hLHS : ∑ i : Fin m, binomVec p i = ∑ t ∈ Finset.range m, g (t + 1) := by
    trans ∑ i : Fin m, g (i.val + 1)
    · refine Fintype.sum_congr _ _ fun i => ?_
      simp [binomVec, g, m]
    · exact (Finset.sum_range (fun t => g (t + 1))).symm
  have : (-1 : ZMod p) ^ m + ∑ i : Fin m, binomVec p i = 0 := by
    rw [← hg0, hLHS, ← hsplit, hsum]
  have : ∑ i : Fin m, binomVec p i = -((-1 : ZMod p) ^ m) := by
    linear_combination this
  calc
    ∑ i : Fin m, binomVec p i = -((-1 : ZMod p) ^ m) := this
    _ = (-1 : ZMod p) ^ (m + 1) := by
        rw [pow_succ, mul_comm, ← neg_eq_neg_one_mul]

lemma choose_cast_ne_zero {p : ℕ} [Fact p.Prime] {n k : ℕ}
    (hn : n < p) (hk : k ≤ n) : (n.choose k : ZMod p) ≠ 0 := by
  intro h
  have hp : p.Prime := Fact.out
  have hdiv0 : p ∣ n.choose k := (ZMod.natCast_eq_zero_iff _ _).1 h
  have hfac : n.choose k * (k ! * (n - k)!) = n ! := by
    simpa [mul_assoc] using Nat.choose_mul_factorial_mul_factorial hk
  have : p ∣ n ! := by
    rw [← hfac]
    exact dvd_mul_of_dvd_left hdiv0 _
  have : p ≤ n := (hp.dvd_factorial).1 this
  omega

lemma kernelPoly_coeff {p : ℕ} [Fact p.Prime]
    (v : Fin ((p - 1) / 2) → ZMod p) (k : ℕ) :
    (kernelPoly v).coeff k =
      ∑ j : Fin ((p - 1) / 2),
        v j * ((((p - 1) / 2).choose k : ZMod p) *
          ((-((((p - 1) / 2)! : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))) ^
            (((p - 1) / 2) - k))) := by
  unfold kernelPoly
  rw [finset_sum_coeff]
  refine Fintype.sum_congr _ _ fun j => ?_
  rw [coeff_C_mul]
  have hrew :
      (X - C ((((p - 1) / 2)! : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))) ^ ((p - 1) / 2) =
        (X + C (-((((p - 1) / 2)! : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)))) ^
          ((p - 1) / 2) := by
    simp [sub_eq_add_neg]
  rw [hrew, coeff_X_add_C_pow]
  ring

lemma kernelPoly_coeff_degree {p : ℕ} [Fact p.Prime]
    (v : Fin ((p - 1) / 2) → ZMod p) :
    (kernelPoly v).coeff ((p - 1) / 2) = ∑ j : Fin ((p - 1) / 2), v j := by
  rw [kernelPoly_coeff]
  refine Fintype.sum_congr _ _ fun j => ?_
  simp [Nat.choose_self]

lemma kernelPoly_eq_C_mul_X_pow_sub_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (v : Fin ((p - 1) / 2) → ZMod p) (hv : powMatrix p *ᵥ v = 0) :
    ∃ c : ZMod p, kernelPoly v = C c * (X ^ ((p - 1) / 2) - 1) := by
  let m : ℕ := (p - 1) / 2
  let P : (ZMod p)[X] := kernelPoly v
  let Q : (ZMod p)[X] := X ^ m - 1
  let c : ZMod p := P.coeff m
  refine ⟨c, ?_⟩
  let D : (ZMod p)[X] := P - C c * Q
  have hm : 0 < m := m_pos hp2
  have hPdeg : P.natDegree ≤ m := kernelPoly_natDegree_le v
  have hQ_m : Q.coeff m = 1 := by
    dsimp [Q]
    simp [coeff_X_pow, coeff_sub, coeff_one, hm.ne']
  have hD_high : ∀ n, m ≤ n → D.coeff n = 0 := by
    intro n hn
    dsimp [D]
    rw [coeff_sub, coeff_C_mul]
    rcases eq_or_lt_of_le hn with rfl | hlt
    · simp [c, hQ_m]
    · have hPn : P.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (hPdeg.trans_lt hlt)
      have hQn : Q.coeff n = 0 := by
        dsimp [Q]
        have hn0 : n ≠ 0 := by omega
        simp [coeff_X_pow, coeff_sub, coeff_one, Nat.ne_of_gt hlt, hn0]
      simp [hPn, hQn]
  have hDeval : ∀ i : Fin ((p - 1) / 2),
      D.eval (((i.val + 1 : ℕ) : ZMod p) ^ 2) = 0 := by
    intro i
    have hP0 : P.eval (((i.val + 1 : ℕ) : ZMod p) ^ 2) = 0 := by
      dsimp [P]
      rw [kernelPoly_eval v i]
      exact congrFun hv i
    have hQ0 : Q.eval (((i.val + 1 : ℕ) : ZMod p) ^ 2) = 0 := by
      dsimp [Q]
      rw [eval_sub, eval_pow, eval_X, eval_one, sq_pow_eq_one hp2 i]
      simp
    dsimp [D]
    rw [eval_sub, eval_mul, eval_C, hP0, hQ0]
    ring
  by_cases hD0 : D = 0
  · have : P = C c * Q := sub_eq_zero.mp hD0
    simpa [P, Q, m] using this
  · have hdeg : D.natDegree < m := by
      have : D.natDegree ≤ m - 1 :=
        (natDegree_le_iff_coeff_eq_zero).2 fun N hN => hD_high N (by omega)
      omega
    have : D = 0 :=
      eq_zero_of_natDegree_lt_card_of_eval_eq_zero D
        (sq_nodes_injective hp2) hDeval (by
          simpa [Fintype.card_fin] using hdeg)
    contradiction

lemma moment_zero_of_kernel {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (v : Fin ((p - 1) / 2) → ZMod p) {c : ZMod p}
    (hc : kernelPoly v = C c * (X ^ ((p - 1) / 2) - 1)) :
    ∑ j : Fin ((p - 1) / 2), v j = c := by
  have hm : 0 < (p - 1) / 2 := m_pos hp2
  have h : (kernelPoly v).coeff ((p - 1) / 2) = (C c * (X ^ ((p - 1) / 2) - 1)).coeff ((p - 1) / 2) :=
    congrArg (fun q : (ZMod p)[X] => q.coeff ((p - 1) / 2)) hc
  rw [kernelPoly_coeff_degree] at h
  have hrhs : (C c * (X ^ ((p - 1) / 2) - 1)).coeff ((p - 1) / 2) = c := by
    simp [coeff_C_mul, coeff_X_pow, coeff_sub, coeff_one, hm.ne']
  exact h.trans hrhs

lemma middle_moments_of_kernel {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (v : Fin ((p - 1) / 2) → ZMod p) {c : ZMod p}
    (hc : kernelPoly v = C c * (X ^ ((p - 1) / 2) - 1))
    {s : ℕ} (hs0 : 0 < s) (hs : s < (p - 1) / 2) :
    ∑ j : Fin ((p - 1) / 2), v j * ((j.val + 1 : ℕ) : ZMod p) ^ s = 0 := by
  have hm : 0 < (p - 1) / 2 := m_pos hp2
  let m : ℕ := (p - 1) / 2
  have hr0 : m - s ≠ 0 := by omega
  have hrm : m - s ≠ m := by omega
  have hms : m - (m - s) = s := by omega
  have hcoeff : (kernelPoly v).coeff (m - s) =
      (C c * (X ^ m - 1)).coeff (m - s) :=
    congrArg (fun q : (ZMod p)[X] => q.coeff (m - s)) hc
  have hrhs : (C c * (X ^ m - 1)).coeff (m - s) = 0 := by
    simp [coeff_C_mul, coeff_X_pow, coeff_sub, coeff_one, hrm, hr0]
  have hch : (m.choose (m - s) : ZMod p) ≠ 0 :=
    choose_cast_ne_zero (by have := m_lt_p (p := p); omega) (Nat.sub_le _ _)
  have hlhs :
      (kernelPoly v).coeff (m - s) =
        (m.choose (m - s) : ZMod p) *
          ∑ j : Fin ((p - 1) / 2),
            v j * ((-((((p - 1) / 2)! : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))) ^ s) := by
    rw [kernelPoly_coeff]
    have hpow : (p - 1) / 2 - (m - s) = s := by simp [m]; omega
    simp only [hpow]
    rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun j => ?_
    ring
  have hsumneg :
      ∑ j : Fin ((p - 1) / 2),
        v j * ((-((((p - 1) / 2)! : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))) ^ s) = 0 := by
    have : (m.choose (m - s) : ZMod p) *
        ∑ j : Fin ((p - 1) / 2),
          v j * ((-((((p - 1) / 2)! : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))) ^ s) = 0 := by
      rw [← hlhs, hcoeff, hrhs]
    exact (mul_eq_zero.mp this).resolve_left hch
  have hfactor :
      ∑ j : Fin ((p - 1) / 2),
        v j * ((-((((p - 1) / 2)! : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))) ^ s) =
      ((-1 : ZMod p) ^ s * ((((p - 1) / 2)! : ZMod p) ^ s)) *
        ∑ j : Fin ((p - 1) / 2), v j * ((j.val + 1 : ℕ) : ZMod p) ^ s := by
    rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun j => ?_
    have hnegpow : ∀ (a : ZMod p), (-a) ^ s = (-1 : ZMod p) ^ s * a ^ s := by
      intro a
      rw [← neg_one_mul a, mul_pow]
    rw [hnegpow]
    ring
  rw [hfactor] at hsumneg
  have hunit : ((-1 : ZMod p) ^ s * ((((p - 1) / 2)! : ZMod p) ^ s)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (pow_ne_zero _ C_ne_zero)
  exact (mul_eq_zero.mp hsumneg).resolve_left hunit

lemma last_moment_of_kernel {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (v : Fin ((p - 1) / 2) → ZMod p) {c : ZMod p}
    (hc : kernelPoly v = C c * (X ^ ((p - 1) / 2) - 1)) :
    ((-1 : ZMod p) ^ ((p - 1) / 2) *
      ((((p - 1) / 2)! : ZMod p) ^ ((p - 1) / 2) *
        ∑ j : Fin ((p - 1) / 2),
          v j * ((j.val + 1 : ℕ) : ZMod p) ^ ((p - 1) / 2))) = -c := by
  have hm : 0 < (p - 1) / 2 := m_pos hp2
  let m : ℕ := (p - 1) / 2
  have hcoeff : (kernelPoly v).coeff 0 = (C c * (X ^ m - 1)).coeff 0 :=
    congrArg (fun q : (ZMod p)[X] => q.coeff 0) hc
  have hrhs : (C c * (X ^ m - 1)).coeff 0 = -c := by
    have hm0 : ¬ (0 = m) := by
      intro h; exact hm.ne' (by simp [m] at h; exact h.symm)
    simp [coeff_C_mul, coeff_X_pow, coeff_sub, coeff_one, hm0]
  have hlhs : (kernelPoly v).coeff 0 =
      ∑ j : Fin ((p - 1) / 2),
        v j * ((-((((p - 1) / 2)! : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))) ^ m) := by
    rw [kernelPoly_coeff]
    simp [m]
  have hsum : ∑ j : Fin ((p - 1) / 2),
      v j * ((-((((p - 1) / 2)! : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))) ^ m) = -c := by
    rw [← hlhs, hcoeff, hrhs]
  have hfactor :
      ∑ j : Fin ((p - 1) / 2),
        v j * ((-((((p - 1) / 2)! : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))) ^ m) =
      ((-1 : ZMod p) ^ m * ((((p - 1) / 2)! : ZMod p) ^ m)) *
        ∑ j : Fin ((p - 1) / 2), v j * ((j.val + 1 : ℕ) : ZMod p) ^ m := by
    rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun j => ?_
    have hnegpow : ∀ (a : ZMod p), (-a) ^ m = (-1 : ZMod p) ^ m * a ^ m := by
      intro a
      rw [← neg_one_mul a, mul_pow]
    rw [hnegpow]
    ring
  rw [hfactor] at hsum
  simpa [m, mul_assoc] using hsum

lemma evalMatrix_det_ne_zero_of_one_mod_four {p : ℕ} [Fact p.Prime]
    (hp : p % 4 = 1) : (evalMatrix p).det ≠ 0 := by
  have hp2 : p ≠ 2 := by intro h; subst h; simp at hp
  intro hdet
  have hpow : (powMatrix p).det = 0 := evalMatrix_det_eq_zero_imp_pow hp2 hdet
  obtain ⟨v, hv0, hv⟩ := (powMatrix_det_eq_zero_iff (p := p)).1 hpow
  obtain ⟨c, hc⟩ := kernelPoly_eq_C_mul_X_pow_sub_one hp2 v hv
  have hsum := moment_zero_of_kernel hp2 v hc
  have hmid : ∀ s : ℕ, 0 < s → s < (p - 1) / 2 →
      ∑ j : Fin ((p - 1) / 2), v j * ((j.val + 1 : ℕ) : ZMod p) ^ s = 0 :=
    fun s hs0 hs => middle_moments_of_kernel hp2 v hc hs0 hs
  have hlast := last_moment_of_kernel hp2 v hc
  rcases eq_or_ne c 0 with hc0 | hc0
  · have hmoments : ∀ k : Fin ((p - 1) / 2),
        ∑ j : Fin ((p - 1) / 2), v j * ((j.val + 1 : ℕ) : ZMod p) ^ (k.val : ℕ) = 0 := by
      intro k
      by_cases hk0 : k.val = 0
      · simpa [hk0, hc0] using hsum
      · exact hmid k.val (Nat.pos_of_ne_zero hk0) k.isLt
    exact hv0 (moments_zero_imp_eq_zero v hmoments)
  · let lam : ZMod p := c * (-1 : ZMod p) ^ (((p - 1) / 2) + 1)
    have hbsum := binomVec_sum hp2
    have hsign2 : ((-1 : ZMod p) ^ (((p - 1) / 2) + 1)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm]
      exact Even.neg_one_pow (even_two_mul _)
    have hlam : lam * ∑ i : Fin ((p - 1) / 2), binomVec p i = c := by
      rw [hbsum]
      calc
        lam * ((-1 : ZMod p) ^ (((p - 1) / 2) + 1))
            = c * ((-1 : ZMod p) ^ (((p - 1) / 2) + 1)) *
                ((-1 : ZMod p) ^ (((p - 1) / 2) + 1)) := by
              simp [lam, mul_assoc]
        _ = c * ((-1 : ZMod p) ^ (((p - 1) / 2) + 1)) ^ 2 := by ring
        _ = c * 1 := by rw [hsign2]
        _ = c := by simp
    let w : Fin ((p - 1) / 2) → ZMod p := fun j => v j - lam * binomVec p j
    have hw_all : ∀ k : Fin ((p - 1) / 2),
        ∑ j : Fin ((p - 1) / 2), w j * ((j.val + 1 : ℕ) : ZMod p) ^ (k.val : ℕ) = 0 := by
      intro k
      have hsplit :
          ∑ j : Fin ((p - 1) / 2), w j * ((j.val + 1 : ℕ) : ZMod p) ^ (k.val : ℕ) =
            ∑ j : Fin ((p - 1) / 2), v j * ((j.val + 1 : ℕ) : ZMod p) ^ (k.val : ℕ) -
              lam * ∑ j : Fin ((p - 1) / 2),
                binomVec p j * ((j.val + 1 : ℕ) : ZMod p) ^ (k.val : ℕ) := by
        simp only [w, sub_mul, Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]
      rw [hsplit]
      by_cases hk0 : k.val = 0
      · have hv0m : ∑ j : Fin ((p - 1) / 2),
            v j * ((j.val + 1 : ℕ) : ZMod p) ^ (k.val : ℕ) = c := by
          simpa [hk0] using hsum
        have hb0m : ∑ j : Fin ((p - 1) / 2),
            binomVec p j * ((j.val + 1 : ℕ) : ZMod p) ^ (k.val : ℕ) =
              ∑ j : Fin ((p - 1) / 2), binomVec p j := by
          simp [hk0]
        rw [hv0m, hb0m, hlam, sub_self]
      · have hvmid := hmid k.val (Nat.pos_of_ne_zero hk0) k.isLt
        have hbmid := binomVec_moment_of_lt (p := p) (Nat.pos_of_ne_zero hk0) k.isLt
        rw [hvmid, hbmid, mul_zero, sub_zero]
    have hw0 : w = 0 := moments_zero_imp_eq_zero w hw_all
    have hvlam : v = fun j => lam * binomVec p j := by
      funext j
      have : w j = 0 := congrFun hw0 j
      exact eq_of_sub_eq_zero this
    have hlam0 : lam ≠ 0 := by
      intro h0
      apply hv0
      funext j
      simp [hvlam, h0]
    have hbmom := binomVec_moment_eq_factorial hp2
    have hvlast :
        ∑ j : Fin ((p - 1) / 2),
          v j * ((j.val + 1 : ℕ) : ZMod p) ^ ((p - 1) / 2) =
        lam * (((p - 1) / 2)! : ZMod p) := by
      simp only [hvlam, mul_assoc, ← Finset.mul_sum]
      rw [hbmom]
    have hconstr :
        ((-1 : ZMod p) ^ ((p - 1) / 2) *
          ((((p - 1) / 2)! : ZMod p) ^ ((p - 1) / 2) *
            (lam * (((p - 1) / 2)! : ZMod p)))) = -c := by
      convert hlast
      exact hvlast.symm
    have hc_expr : c = lam * (-1 : ZMod p) ^ (((p - 1) / 2) + 1) := by
      simp only [lam]
      rw [mul_assoc, ← pow_two, hsign2, mul_one]
    have hpow_eq : ((((p - 1) / 2)! : ZMod p) ^ (((p - 1) / 2) + 1)) = 1 := by
      have hneg : (-1 : ZMod p) ^ ((p - 1) / 2) ≠ 0 :=
        pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
      have hR : -c = (-1 : ZMod p) ^ ((p - 1) / 2) * lam := by
        rw [hc_expr, pow_succ]
        ring
      have hL :
          ((-1 : ZMod p) ^ ((p - 1) / 2) *
            ((((p - 1) / 2)! : ZMod p) ^ (((p - 1) / 2) + 1) * lam)) = -c := by
        convert hconstr using 1
        rw [pow_succ]
        ring
      have : ((-1 : ZMod p) ^ ((p - 1) / 2) *
            ((((p - 1) / 2)! : ZMod p) ^ (((p - 1) / 2) + 1) * lam)) =
          (-1 : ZMod p) ^ ((p - 1) / 2) * lam := by
        rw [hL, hR]
      have : ((((p - 1) / 2)! : ZMod p) ^ (((p - 1) / 2) + 1) * lam - lam) *
          ((-1 : ZMod p) ^ ((p - 1) / 2)) = 0 := by
        linear_combination this
      have : ((((p - 1) / 2)! : ZMod p) ^ (((p - 1) / 2) + 1) * lam - lam) = 0 :=
        (mul_eq_zero.mp this).resolve_right hneg
      have : (((((p - 1) / 2)! : ZMod p) ^ (((p - 1) / 2) + 1)) - 1) * lam = 0 := by
        linear_combination this
      exact eq_of_sub_eq_zero ((mul_eq_zero.mp this).resolve_right hlam0)
    have hsq := factorial_half_sq_of_one_mod_four (p := p) hp
    have : (-1 : ZMod p) ^ (((p - 1) / 2) + 1) = 1 := by
      calc
        (-1 : ZMod p) ^ (((p - 1) / 2) + 1)
            = ((((p - 1) / 2)! : ZMod p) ^ 2) ^ (((p - 1) / 2) + 1) := by rw [hsq]
        _ = ((((p - 1) / 2)! : ZMod p) ^ (2 * (((p - 1) / 2) + 1))) := by rw [← pow_mul]
        _ = (((((p - 1) / 2)! : ZMod p) ^ (((p - 1) / 2) + 1)) ^ 2) := by
              rw [mul_comm, pow_mul]
        _ = (1 : ZMod p) ^ 2 := by rw [hpow_eq]
        _ = 1 := by simp
    have hodd : Odd (((p - 1) / 2) + 1) := by
      have : (((p - 1) / 2) + 1) % 2 = 1 := by omega
      exact Nat.odd_iff.2 this
    have hneg1 : (-1 : ZMod p) = 1 := by simpa [Odd.neg_one_pow hodd] using this
    have h2 : (2 : ZMod p) = 0 := by
      have : (1 : ZMod p) + 1 = 0 := add_eq_zero_iff_eq_neg.mpr (by simpa using hneg1.symm)
      rw [← Nat.cast_one, ← Nat.cast_add] at this
      exact this
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h2
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) this
    have : 2 < p := (Fact.out : p.Prime).two_le.lt_of_ne' hp2
    omega

lemma odd_prime_mod_four {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (odd_p hp2)
  omega

lemma m_odd_of_three_mod_four {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    Odd ((p - 1) / 2) := by
  have : ((p - 1) / 2) % 2 = 1 := by omega
  exact Nat.odd_iff.2 this

lemma factorial_half_eq_neg_one_or_one {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    (((p - 1) / 2)! : ZMod p) = 1 ∨ (((p - 1) / 2)! : ZMod p) = -1 := by
  have hsq := factorial_half_sq_of_three_mod_four (p := p) hp
  have h : ((((p - 1) / 2)! : ZMod p) - 1) *
      ((((p - 1) / 2)! : ZMod p) + 1) = 0 := by
    have : ((((p - 1) / 2)! : ZMod p) ^ 2 - 1) = 0 := by
      simpa [sub_eq_zero] using hsq
    linear_combination this
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (eq_of_sub_eq_zero h)
  · exact Or.inr (eq_neg_iff_add_eq_zero.2 h)


/-- The sign `ε ≡ ((p-1)/2)! (mod p)`, equal to `±1` when `p ≡ 3 (mod 4)`. -/
noncomputable def epsInt (p : ℕ) [Fact p.Prime] : ℤ :=
  if (((p - 1) / 2)! : ZMod p) = 1 then 1 else -1

lemma two_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h
  have : p ≤ 2 := Nat.le_of_dvd (by norm_num) this
  have : 2 < p := (Fact.out : p.Prime).two_le.lt_of_ne' hp2
  omega

lemma ringChar_zmod_ne_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n p]
  exact hp2

lemma four_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (4 : ZMod p) ≠ 0 := by
  have h2 := two_ne_zero_zmod hp2
  have : (4 : ZMod p) = (2 : ZMod p) * 2 := by norm_num
  rw [this]
  exact mul_ne_zero h2 h2

lemma epsInt_spec {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    (epsInt p : ZMod p) = (((p - 1) / 2)! : ZMod p) := by
  unfold epsInt
  rcases factorial_half_eq_neg_one_or_one hp with h | h
  · simp [h]
  · split_ifs with h1
    · have hneg : (1 : ZMod p) = -1 := h1.symm.trans h
      have hp2 : p ≠ 2 := by intro hp'; subst hp'; simp at hp
      have h2 : (2 : ZMod p) = 0 := by
        have : (1 : ZMod p) + 1 = 0 := add_eq_zero_iff_eq_neg.mpr hneg
        rw [← Nat.cast_one, ← Nat.cast_add] at this
        exact this
      exact (two_ne_zero_zmod hp2 h2).elim
    · simpa using h.symm

lemma epsInt_eq_one_or_neg_one {p : ℕ} [Fact p.Prime] :
    epsInt p = 1 ∨ epsInt p = -1 := by
  unfold epsInt
  split_ifs <;> simp

lemma epsInt_mul_self {p : ℕ} [Fact p.Prime] : epsInt p * epsInt p = 1 := by
  rcases epsInt_eq_one_or_neg_one (p := p) with h | h <;> simp [h]

lemma epsInt_zmod_ne_zero {p : ℕ} [Fact p.Prime] : (epsInt p : ZMod p) ≠ 0 := by
  rcases epsInt_eq_one_or_neg_one (p := p) with h | h <;> simp [h]

lemma epsInt_zmod_sq {p : ℕ} [Fact p.Prime] : (epsInt p : ZMod p) ^ 2 = 1 := by
  have := epsInt_mul_self (p := p)
  simpa [pow_two] using congrArg (fun z : ℤ => (z : ZMod p)) this

lemma jacobi_neg_one_of_three_mod_four {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    jacobiSym (-1) p = -1 := by
  have hodd : Odd p := by
    have : p % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  rw [jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_three_mod_four hp]

lemma jacobiSym_eq_quadraticChar {p : ℕ} [Fact p.Prime] (a : ℤ) :
    jacobiSym a p = quadraticChar (ZMod p) (a : ZMod p) := by
  rw [jacobiSym_eq_legendre, legendreSym]

lemma quadraticChar_neg_one_three {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    quadraticChar (ZMod p) (-1) = -1 := by
  simpa [jacobiSym_eq_quadraticChar] using jacobi_neg_one_of_three_mod_four hp

/-- The partner matrix with entries `χ(i² + ε j)`. -/
noncomputable def partnerMatrix (p : ℕ) [Fact p.Prime] :
    Matrix (Fin ((p - 1) / 2)) (Fin ((p - 1) / 2)) ℤ :=
  fun i j =>
    jacobiSym
      (((i.val + 1 : ℕ) : ℤ) * ((i.val + 1 : ℕ) : ℤ) +
        epsInt p * ((j.val + 1 : ℕ) : ℤ)) p

lemma evalMatrix_eq_eps {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (i j : Fin ((p - 1) / 2)) :
    evalMatrix p i j =
      jacobiSym
        (((i.val + 1 : ℕ) : ℤ) * ((i.val + 1 : ℕ) : ℤ) -
          epsInt p * ((j.val + 1 : ℕ) : ℤ)) p := by
  apply jacobiSym.mod_left'
  rw [← ZMod.intCast_eq_intCast_iff']
  have hC : ((((p - 1) / 2)! : ℤ) : ZMod p) = (epsInt p : ZMod p) := by
    simpa using (epsInt_spec hp).symm
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, hC]

/-- Nodes `1, …, m` inside `ZMod p`. -/
def posNodes (p : ℕ) [Fact p.Prime] : Fin ((p - 1) / 2) → ZMod p :=
  fun j => ((j.val + 1 : ℕ) : ZMod p)

lemma posNodes_injective {p : ℕ} [Fact p.Prime] :
    Function.Injective (posNodes p) :=
  vandermonde_nodes_injective (p := p)

lemma posNodes_ne_zero {p : ℕ} [Fact p.Prime] (j : Fin ((p - 1) / 2)) :
    posNodes p j ≠ 0 :=
  one_add_val_ne_zero j

lemma posNodes_add_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (i j : Fin ((p - 1) / 2)) :
    posNodes p i + posNodes p j ≠ 0 := by
  intro hab
  have hsum : i.val + 1 + (j.val + 1) < p := by
    have hm := two_mul_half_pred (odd_p hp2)
    have := i.isLt
    have := j.isLt
    omega
  have hcast : ((i.val + 1 + (j.val + 1) : ℕ) : ZMod p) =
      posNodes p i + posNodes p j := by
    simp [posNodes]
  have hz : ((i.val + 1 + (j.val + 1) : ℕ) : ZMod p) = 0 := by
    rw [hcast, hab]
  have : p ∣ i.val + 1 + (j.val + 1) := (ZMod.natCast_eq_zero_iff _ _).1 hz
  have hpos : 0 < i.val + 1 + (j.val + 1) := by omega
  have : p ≤ i.val + 1 + (j.val + 1) := Nat.le_of_dvd hpos this
  omega

lemma posNodes_ne_neg {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (i j : Fin ((p - 1) / 2)) :
    posNodes p i ≠ -posNodes p j := by
  intro h
  exact posNodes_add_ne_zero hp2 i j (by rw [h, neg_add_cancel])

/- Quadratic character sums -/

lemma quadraticChar_sum_sq {p : ℕ} [Fact p.Prime] (_hp2 : p ≠ 2) :
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 2) = (p : ℤ) - 1 := by
  have h1 : ∀ x ∈ Finset.univ.erase (0 : ZMod p),
      quadraticChar (ZMod p) (x ^ 2) = 1 := by
    intro x hx
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
    exact quadraticChar_sq_one' hx0
  have htot := Finset.sum_erase_add (Finset.univ : Finset (ZMod p))
    (fun x => quadraticChar (ZMod p) (x ^ 2)) (Finset.mem_univ (0 : ZMod p))
  have hzero : quadraticChar (ZMod p) ((0 : ZMod p) ^ 2) = 0 := by simp
  calc
    ∑ x, quadraticChar (ZMod p) (x ^ 2)
        = ∑ x ∈ Finset.univ.erase (0 : ZMod p), quadraticChar (ZMod p) (x ^ 2) +
            quadraticChar (ZMod p) (0 ^ 2) := htot.symm
    _ = ∑ x ∈ Finset.univ.erase (0 : ZMod p), quadraticChar (ZMod p) (x ^ 2) := by
          rw [hzero, add_zero]
    _ = ∑ x ∈ Finset.univ.erase (0 : ZMod p), (1 : ℤ) := Finset.sum_congr rfl h1
    _ = ((Finset.univ.erase (0 : ZMod p)).card : ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ((p - 1 : ℕ) : ℤ) := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card p]
    _ = (p : ℤ) - 1 := by
          have : 1 ≤ p := (Fact.out : p.Prime).one_le
          simp [Nat.cast_sub this]

lemma quadraticChar_sum_u_mul_sub_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∑ u : ZMod p, quadraticChar (ZMod p) (u * (u - 1)) = -1 := by
  have hchar := ringChar_zmod_ne_two (p := p) hp2
  have hχ : quadraticChar (ZMod p) ≠ 1 := quadraticChar_ne_one hchar
  have hinv : (quadraticChar (ZMod p))⁻¹ = quadraticChar (ZMod p) :=
    MulChar.IsQuadratic.inv (quadraticChar_isQuadratic (ZMod p))
  have hJ : jacobiSum (quadraticChar (ZMod p)) (quadraticChar (ZMod p)) =
      -quadraticChar (ZMod p) (-1) := by
    nth_rw 2 [← hinv]
    exact jacobiSum_nontrivial_inv hχ
  have hsum :
      ∑ u : ZMod p, quadraticChar (ZMod p) (u * (u - 1)) =
        quadraticChar (ZMod p) (-1) *
          jacobiSum (quadraticChar (ZMod p)) (quadraticChar (ZMod p)) := by
    unfold jacobiSum
    rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun u => ?_
    have : u * (u - 1) = (-1) * (u * (1 - u)) := by ring
    rw [this, map_mul, map_mul]
  rw [hsum, hJ]
  have hsq : quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [mul_neg, hsq]

lemma quadraticChar_sum_y_mul_sub {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {d : ZMod p} (hd : d ≠ 0) :
    ∑ y : ZMod p, quadraticChar (ZMod p) (y * (y - d)) = -1 := by
  have hre :
      ∑ y : ZMod p, quadraticChar (ZMod p) (y * (y - d)) =
        ∑ u : ZMod p, quadraticChar (ZMod p) ((d * u) * (d * u - d)) :=
    (Fintype.sum_equiv (Equiv.mulLeft₀ d hd)
      (fun u => quadraticChar (ZMod p) ((d * u) * (d * u - d)))
      (fun y => quadraticChar (ZMod p) (y * (y - d)))
      (fun _ => rfl)).symm
  have hcongr : ∀ u : ZMod p,
      quadraticChar (ZMod p) ((d * u) * (d * u - d)) =
        quadraticChar (ZMod p) (u * (u - 1)) := by
    intro u
    have : (d * u) * (d * u - d) = d ^ 2 * (u * (u - 1)) := by ring
    rw [this, map_mul, quadraticChar_sq_one' hd, one_mul]
  rw [hre, Fintype.sum_congr _ _ hcongr, quadraticChar_sum_u_mul_sub_one hp2]

lemma quadraticChar_sum_translate {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (d : ZMod p) :
    ∑ y : ZMod p, quadraticChar (ZMod p) (y - d) = 0 := by
  have h := Fintype.sum_equiv (Equiv.addLeft (-d))
    (fun y => quadraticChar (ZMod p) (y - d))
    (fun z => quadraticChar (ZMod p) z)
    (fun y => by simp [sub_eq_add_neg, add_comm])
  exact h.trans (quadraticChar_sum_zero (ringChar_zmod_ne_two hp2))

lemma card_sqrts_quadraticChar {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (y : ZMod p) :
    ((Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)).card : ℤ) =
      quadraticChar (ZMod p) y + 1 := by
  have hn := quadraticChar_card_sqrts (ringChar_zmod_ne_two (p := p) hp2) y
  have hset : {x : ZMod p | x ^ 2 = y}.toFinset =
      Finset.univ.filter (fun x : ZMod p => x ^ 2 = y) := by
    ext x; simp
  simpa [hset] using hn

lemma quadraticChar_sum_sq_sub {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (d : ZMod p) :
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 2 - d) =
      if d = 0 then (p : ℤ) - 1 else -1 := by
  by_cases hd : d = 0
  · subst hd
    simpa using quadraticChar_sum_sq (p := p) hp2
  · have hgroup :
        ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 2 - d) =
          ∑ y : ZMod p,
            ((Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)).card : ℤ) *
              quadraticChar (ZMod p) (y - d) := by
      have hx : ∀ x : ZMod p,
          quadraticChar (ZMod p) (x ^ 2 - d) =
            ∑ y : ZMod p,
              (if x ^ 2 = y then quadraticChar (ZMod p) (y - d) else 0) := by
        intro x
        rw [Finset.sum_eq_single (x ^ 2)]
        · simp
        · intro y _ hy
          simp [eq_comm, hy]
        · intro h; exact (h (Finset.mem_univ _)).elim
      rw [Fintype.sum_congr _ _ hx, Finset.sum_comm]
      refine Fintype.sum_congr _ _ fun y => ?_
      have hite : ∀ x : ZMod p,
          (if x ^ 2 = y then quadraticChar (ZMod p) (y - d) else 0) =
            (if x ^ 2 = y then (1 : ℤ) else 0) * quadraticChar (ZMod p) (y - d) := by
        intro x; split_ifs <;> simp
      rw [Fintype.sum_congr _ _ hite, ← Finset.sum_mul]
      congr 1
      simp [Finset.sum_boole]
    rw [hgroup]
    have hcard : ∀ y : ZMod p,
        ((Finset.univ.filter (fun x : ZMod p => x ^ 2 = y)).card : ℤ) *
            quadraticChar (ZMod p) (y - d) =
          (quadraticChar (ZMod p) y + 1) * quadraticChar (ZMod p) (y - d) := by
      intro y
      rw [card_sqrts_quadraticChar hp2 y]
    rw [Fintype.sum_congr _ _ hcard]
    have hsplit :
        ∑ y : ZMod p,
            (quadraticChar (ZMod p) y + 1) * quadraticChar (ZMod p) (y - d) =
          ∑ y : ZMod p, quadraticChar (ZMod p) (y * (y - d)) +
            ∑ y : ZMod p, quadraticChar (ZMod p) (y - d) := by
      simp only [add_mul, one_mul, map_mul, Finset.sum_add_distrib]
    rw [hsplit, quadraticChar_sum_y_mul_sub hp2 hd, quadraticChar_sum_translate hp2 d]
    simp [hd]

lemma complete_square_quadratic {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (a b c : ZMod p) (ha : a ≠ 0) (x : ZMod p) :
    a * x ^ 2 + b * x + c =
      a * ((x + b / (2 * a)) ^ 2 - (b ^ 2 - 4 * a * c) / (4 * a ^ 2)) := by
  have h2 := two_ne_zero_zmod hp2
  have ha2 : (2 * a) ≠ 0 := mul_ne_zero h2 ha
  have h4 := four_ne_zero_zmod hp2
  have ha4 : (4 * a ^ 2) ≠ 0 := mul_ne_zero h4 (pow_ne_zero _ ha)
  field_simp [ha, h2, ha2, h4, ha4]
  ring

lemma quadraticChar_sum_quadratic {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (a b c : ZMod p) (ha : a ≠ 0) :
    ∑ x : ZMod p, quadraticChar (ZMod p) (a * x ^ 2 + b * x + c) =
      if b ^ 2 - 4 * a * c = 0 then
        quadraticChar (ZMod p) a * ((p : ℤ) - 1)
      else
        -quadraticChar (ZMod p) a := by
  have h2 := two_ne_zero_zmod hp2
  set Δ := b ^ 2 - 4 * a * c
  have hrewrite := complete_square_quadratic (p := p) hp2 a b c ha
  have htrans :
      ∑ x : ZMod p, quadraticChar (ZMod p)
          (a * ((x + b / (2 * a)) ^ 2 - Δ / (4 * a ^ 2))) =
        ∑ z : ZMod p, quadraticChar (ZMod p)
          (a * (z ^ 2 - Δ / (4 * a ^ 2))) := by
    exact Fintype.sum_equiv (Equiv.addRight (b / (2 * a)))
      (fun x => quadraticChar (ZMod p)
        (a * ((x + b / (2 * a)) ^ 2 - Δ / (4 * a ^ 2))))
      (fun z => quadraticChar (ZMod p) (a * (z ^ 2 - Δ / (4 * a ^ 2))))
      (fun _ => rfl)
  have hsum :
      ∑ x : ZMod p, quadraticChar (ZMod p) (a * x ^ 2 + b * x + c) =
        quadraticChar (ZMod p) a *
          ∑ z : ZMod p, quadraticChar (ZMod p) (z ^ 2 - Δ / (4 * a ^ 2)) := by
    refine Eq.trans (Fintype.sum_congr _ _ fun x => by rw [hrewrite x]) ?_
    rw [htrans]
    have : ∀ z, quadraticChar (ZMod p) (a * (z ^ 2 - Δ / (4 * a ^ 2))) =
        quadraticChar (ZMod p) a * quadraticChar (ZMod p) (z ^ 2 - Δ / (4 * a ^ 2)) := by
      intro z; rw [map_mul]
    rw [Fintype.sum_congr _ _ this, ← Finset.mul_sum]
  rw [hsum, quadraticChar_sum_sq_sub hp2]
  have ha4 : (4 * a ^ 2) ≠ 0 :=
    mul_ne_zero (four_ne_zero_zmod hp2) (pow_ne_zero _ ha)
  have hδ : Δ / (4 * a ^ 2) = 0 ↔ Δ = 0 := by
    constructor
    · intro h
      exact (div_eq_zero_iff.mp h).resolve_right ha4
    · intro h; simp [h]
  by_cases hΔ : Δ = 0
  · simp [Δ, hΔ]
  · have : Δ / (4 * a ^ 2) ≠ 0 := fun h => hΔ (hδ.1 h)
    simp [Δ, hΔ, this]

lemma det_eq_zero_of_transpose_eq_neg {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (A : Matrix n n R) (hA : Aᵀ = -A)
    (hodd : Odd (Fintype.card n)) : A.det = 0 := by
  have : A.det = -A.det := by
    calc
      A.det = Aᵀ.det := (Matrix.det_transpose A).symm
      _ = (-A).det := by rw [hA]
      _ = (-1 : R) ^ Fintype.card n * A.det := Matrix.det_neg A
      _ = (-1 : R) * A.det := by rw [Odd.neg_one_pow hodd]
      _ = -A.det := by simp
  have : (2 : R) * A.det = 0 := by
    linear_combination this
  exact (mul_eq_zero.mp this).resolve_left (by norm_num)

lemma card_fin_m_odd {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    Odd (Fintype.card (Fin ((p - 1) / 2))) := by
  simpa [Fintype.card_fin] using m_odd_of_three_mod_four hp

/- Identifying `I ∪ (-I)` with `F_p^*`. -/

lemma image_posNodes_card {p : ℕ} [Fact p.Prime] :
    (Finset.univ.image (posNodes p)).card = (p - 1) / 2 := by
  rw [Finset.card_image_of_injective _ (posNodes_injective (p := p)),
    Finset.card_univ, Fintype.card_fin]

lemma image_neg_posNodes_card {p : ℕ} [Fact p.Prime] :
    (Finset.univ.image (fun j : Fin ((p - 1) / 2) => -posNodes p j)).card =
      (p - 1) / 2 := by
  have hinj : Function.Injective (fun j : Fin ((p - 1) / 2) => -posNodes p j) := by
    intro i j h
    exact posNodes_injective (neg_injective h)
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

lemma image_posNodes_disjoint_neg {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Disjoint (Finset.univ.image (posNodes p))
      (Finset.univ.image (fun j : Fin ((p - 1) / 2) => -posNodes p j)) := by
  refine Finset.disjoint_iff_ne.2 ?_
  intro x hx y hy
  rcases Finset.mem_image.1 hx with ⟨i, _, rfl⟩
  rcases Finset.mem_image.1 hy with ⟨j, _, rfl⟩
  exact posNodes_ne_neg hp2 i j

lemma zero_nmem_image_posNodes {p : ℕ} [Fact p.Prime] :
    (0 : ZMod p) ∉ Finset.univ.image (posNodes p) := by
  intro h
  rcases Finset.mem_image.1 h with ⟨j, _, hj⟩
  exact posNodes_ne_zero j hj

lemma zero_nmem_image_neg_posNodes {p : ℕ} [Fact p.Prime] :
    (0 : ZMod p) ∉ Finset.univ.image (fun j : Fin ((p - 1) / 2) => -posNodes p j) := by
  intro h
  rcases Finset.mem_image.1 h with ⟨j, _, hj⟩
  exact posNodes_ne_zero j (neg_eq_zero.mp hj)

lemma image_posNodes_union_neg {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Finset.univ.image (posNodes p) ∪
        Finset.univ.image (fun j : Fin ((p - 1) / 2) => -posNodes p j) =
      Finset.univ.erase (0 : ZMod p) := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_union] at hx
    have hx0 : x ≠ 0 := by
      intro h0
      rcases hx with hx | hx
      · exact zero_nmem_image_posNodes (p := p) (h0 ▸ hx)
      · exact zero_nmem_image_neg_posNodes (p := p) (h0 ▸ hx)
    exact Finset.mem_erase.2 ⟨hx0, Finset.mem_univ _⟩
  · have hdisj := image_posNodes_disjoint_neg (p := p) hp2
    have hcard :
        ((Finset.univ.image (posNodes p)) ∪
            (Finset.univ.image (fun j : Fin ((p - 1) / 2) => -posNodes p j))).card =
          p - 1 := by
      rw [Finset.card_union_of_disjoint hdisj, image_posNodes_card,
        image_neg_posNodes_card]
      have := two_mul_half_pred (odd_p hp2)
      omega
    have herase : (Finset.univ.erase (0 : ZMod p)).card = p - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ZMod.card p]
    omega

lemma sum_over_pos_neg {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (f : ZMod p → ℤ) :
    ∑ t : ZMod p, f t =
      f 0 +
        ∑ j : Fin ((p - 1) / 2), f (posNodes p j) +
          ∑ j : Fin ((p - 1) / 2), f (-posNodes p j) := by
  have hI := image_posNodes_union_neg (p := p) hp2
  have hdisj := image_posNodes_disjoint_neg (p := p) hp2
  have hinj : Function.Injective (posNodes p) := posNodes_injective (p := p)
  have hinj' : Function.Injective (fun j : Fin ((p - 1) / 2) => -posNodes p j) := by
    intro i j h; exact posNodes_injective (neg_injective h)
  have htot : ∑ t : ZMod p, f t =
      ∑ t ∈ Finset.univ.erase (0 : ZMod p), f t + f 0 :=
    (Finset.sum_erase_add (Finset.univ : Finset (ZMod p)) f
      (Finset.mem_univ (0 : ZMod p))).symm
  have : ∑ t ∈ Finset.univ.erase (0 : ZMod p), f t =
      ∑ t ∈ Finset.univ.image (posNodes p), f t +
        ∑ t ∈ Finset.univ.image (fun j : Fin ((p - 1) / 2) => -posNodes p j), f t := by
    rw [← hI, Finset.sum_union hdisj]
  rw [htot, this, Finset.sum_image (fun _ _ _ _ h => hinj h),
    Finset.sum_image (fun _ _ _ _ h => hinj' h)]
  abel

/- The product `M Nᵀ` is skew-symmetric. -/

lemma eval_mul_partner_sum {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (i k : Fin ((p - 1) / 2)) :
    ∑ j : Fin ((p - 1) / 2), evalMatrix p i j * partnerMatrix p k j =
      ∑ j : Fin ((p - 1) / 2),
        quadraticChar (ZMod p)
          ((((i.val + 1 : ℕ) : ZMod p) ^ 2 -
              (epsInt p : ZMod p) * posNodes p j) *
            (((k.val + 1 : ℕ) : ZMod p) ^ 2 +
              (epsInt p : ZMod p) * posNodes p j)) := by
  refine Fintype.sum_congr _ _ fun j => ?_
  rw [evalMatrix_eq_eps hp, partnerMatrix, ← jacobiSym.mul_left,
    jacobiSym_eq_quadraticChar]
  congr 1
  simp [posNodes, pow_two]

lemma pair_sum_eq_complete {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (i k : Fin ((p - 1) / 2)) :
    ∑ j : Fin ((p - 1) / 2),
        quadraticChar (ZMod p)
          ((((i.val + 1 : ℕ) : ZMod p) ^ 2 -
              (epsInt p : ZMod p) * posNodes p j) *
            (((k.val + 1 : ℕ) : ZMod p) ^ 2 +
              (epsInt p : ZMod p) * posNodes p j)) +
      ∑ j : Fin ((p - 1) / 2),
        quadraticChar (ZMod p)
          ((((i.val + 1 : ℕ) : ZMod p) ^ 2 -
              (epsInt p : ZMod p) * (-posNodes p j)) *
            (((k.val + 1 : ℕ) : ZMod p) ^ 2 +
              (epsInt p : ZMod p) * (-posNodes p j))) =
      ∑ t : ZMod p,
        quadraticChar (ZMod p)
          ((((i.val + 1 : ℕ) : ZMod p) ^ 2 - (epsInt p : ZMod p) * t) *
            (((k.val + 1 : ℕ) : ZMod p) ^ 2 + (epsInt p : ZMod p) * t)) -
        quadraticChar (ZMod p)
          ((((i.val + 1 : ℕ) : ZMod p) ^ 2) *
            (((k.val + 1 : ℕ) : ZMod p) ^ 2)) := by
  have hp2 : p ≠ 2 := by intro h; subst h; simp at hp
  let f : ZMod p → ℤ := fun t =>
    quadraticChar (ZMod p)
      ((((i.val + 1 : ℕ) : ZMod p) ^ 2 - (epsInt p : ZMod p) * t) *
        (((k.val + 1 : ℕ) : ZMod p) ^ 2 + (epsInt p : ZMod p) * t))
  have hsplit := sum_over_pos_neg (p := p) hp2 f
  have hf0 : f 0 =
      quadraticChar (ZMod p)
        ((((i.val + 1 : ℕ) : ZMod p) ^ 2) *
          (((k.val + 1 : ℕ) : ZMod p) ^ 2)) := by
    simp [f]
  have := hsplit
  simp only [f] at this hf0 ⊢
  linarith

lemma squares_add_ne_zero {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (i k : Fin ((p - 1) / 2)) :
    ((i.val + 1 : ℕ) : ZMod p) ^ 2 + ((k.val + 1 : ℕ) : ZMod p) ^ 2 ≠ 0 := by
  intro h
  have ha0 : ((i.val + 1 : ℕ) : ZMod p) ≠ 0 := one_add_val_ne_zero i
  have hb0 : ((k.val + 1 : ℕ) : ZMod p) ≠ 0 := one_add_val_ne_zero k
  have hab : ((i.val + 1 : ℕ) : ZMod p) ^ 2 =
      -(((k.val + 1 : ℕ) : ZMod p) ^ 2) := eq_neg_iff_add_eq_zero.mpr h
  have hratio :
      ((i.val + 1 : ℕ) : ZMod p) ^ 2 * (((k.val + 1 : ℕ) : ZMod p) ^ 2)⁻¹ = -1 := by
    field_simp [hb0]
    exact hab
  have hsq : IsSquare (-1 : ZMod p) := by
    refine ⟨((i.val + 1 : ℕ) : ZMod p) * (((k.val + 1 : ℕ) : ZMod p))⁻¹, ?_⟩
    have : (((i.val + 1 : ℕ) : ZMod p) * (((k.val + 1 : ℕ) : ZMod p))⁻¹) *
        (((i.val + 1 : ℕ) : ZMod p) * (((k.val + 1 : ℕ) : ZMod p))⁻¹) =
        ((i.val + 1 : ℕ) : ZMod p) ^ 2 * (((k.val + 1 : ℕ) : ZMod p) ^ 2)⁻¹ := by
      field_simp [hb0]
    exact (this.trans hratio).symm
  have : ¬ IsSquare (-1 : ZMod p) := by
    rw [ZMod.exists_sq_eq_neg_one_iff]
    omega
  exact this hsq

lemma complete_char_sum_pair {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (i k : Fin ((p - 1) / 2)) :
    ∑ t : ZMod p,
        quadraticChar (ZMod p)
          ((((i.val + 1 : ℕ) : ZMod p) ^ 2 - (epsInt p : ZMod p) * t) *
            (((k.val + 1 : ℕ) : ZMod p) ^ 2 + (epsInt p : ZMod p) * t)) = 1 := by
  have hp2 : p ≠ 2 := by intro h; subst h; simp at hp
  set a : ZMod p := ((i.val + 1 : ℕ) : ZMod p) ^ 2
  set b : ZMod p := ((k.val + 1 : ℕ) : ZMod p) ^ 2
  set ε : ZMod p := (epsInt p : ZMod p)
  have ha0 : a ≠ 0 := pow_ne_zero _ (one_add_val_ne_zero i)
  have hb0 : b ≠ 0 := pow_ne_zero _ (one_add_val_ne_zero k)
  have hε2 : ε ^ 2 = 1 := epsInt_zmod_sq (p := p)
  have hpoly : ∀ t : ZMod p, (a - ε * t) * (b + ε * t) = -t ^ 2 + ε * (a - b) * t + a * b := by
    intro t
    calc
      (a - ε * t) * (b + ε * t)
          = a * b + a * (ε * t) - (ε * t) * b - (ε * t) * (ε * t) := by ring
      _ = a * b + ε * (a - b) * t - (ε * ε) * t ^ 2 := by ring
      _ = a * b + ε * (a - b) * t - (1 : ZMod p) * t ^ 2 := by
            have : ε * ε = 1 := by simpa [pow_two] using hε2
            rw [this]
      _ = -t ^ 2 + ε * (a - b) * t + a * b := by ring
  have hsum :
      ∑ t : ZMod p, quadraticChar (ZMod p) ((a - ε * t) * (b + ε * t)) =
        ∑ t : ZMod p, quadraticChar (ZMod p) (-t ^ 2 + ε * (a - b) * t + a * b) :=
    Fintype.sum_congr _ _ fun t => by rw [hpoly t]
  have hform : ∀ t : ZMod p,
      -t ^ 2 + ε * (a - b) * t + a * b =
        (-1) * t ^ 2 + (ε * (a - b)) * t + (a * b) := by
    intro t; ring
  have hquad :=
    quadraticChar_sum_quadratic (p := p) hp2 (-1) (ε * (a - b)) (a * b)
      (neg_ne_zero.2 one_ne_zero)
  have hΔ : (ε * (a - b)) ^ 2 - 4 * (-1) * (a * b) ≠ 0 := by
    have : (ε * (a - b)) ^ 2 - 4 * (-1) * (a * b) = (a + b) ^ 2 := by
      have hεε : ε * ε = 1 := by simpa [pow_two] using hε2
      calc
        (ε * (a - b)) ^ 2 - 4 * (-1) * (a * b)
            = (ε * ε) * (a - b) ^ 2 + 4 * (a * b) := by ring
        _ = (1 : ZMod p) * (a - b) ^ 2 + 4 * (a * b) := by rw [hεε]
        _ = (a + b) ^ 2 := by ring
    rw [this]
    exact pow_ne_zero _ (squares_add_ne_zero hp i k)
  have hχneg : quadraticChar (ZMod p) (-1) = -1 := quadraticChar_neg_one_three hp
  have : ∑ t : ZMod p,
      quadraticChar (ZMod p) ((-1) * t ^ 2 + (ε * (a - b)) * t + (a * b)) =
        -quadraticChar (ZMod p) (-1) := by
    rwa [if_neg hΔ] at hquad
  calc
    ∑ t : ZMod p, quadraticChar (ZMod p) ((a - ε * t) * (b + ε * t))
        = ∑ t : ZMod p, quadraticChar (ZMod p) (-t ^ 2 + ε * (a - b) * t + a * b) := hsum
    _ = ∑ t : ZMod p,
          quadraticChar (ZMod p) ((-1) * t ^ 2 + (ε * (a - b)) * t + (a * b)) :=
        Fintype.sum_congr _ _ fun t => by rw [hform t]
    _ = -quadraticChar (ZMod p) (-1) := this
    _ = 1 := by simp [hχneg]

lemma chi_ab_squares {p : ℕ} [Fact p.Prime]
    (i k : Fin ((p - 1) / 2)) :
    quadraticChar (ZMod p)
        ((((i.val + 1 : ℕ) : ZMod p) ^ 2) *
          (((k.val + 1 : ℕ) : ZMod p) ^ 2)) = 1 := by
  rw [map_mul, quadraticChar_sq_one' (one_add_val_ne_zero i),
    quadraticChar_sq_one' (one_add_val_ne_zero k), mul_one]

lemma eval_mul_partner_transpose_is_skew {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    ((evalMatrix p) * (partnerMatrix p)ᵀ)ᵀ =
      -((evalMatrix p) * (partnerMatrix p)ᵀ) := by
  ext i k
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.mul_apply]
  change
      ∑ j : Fin ((p - 1) / 2), evalMatrix p k j * partnerMatrix p i j =
      -∑ j : Fin ((p - 1) / 2), evalMatrix p i j * partnerMatrix p k j
  suffices
      (∑ j : Fin ((p - 1) / 2), evalMatrix p i j * partnerMatrix p k j) +
      (∑ j : Fin ((p - 1) / 2), evalMatrix p k j * partnerMatrix p i j) = 0 by
    linarith
  have hL := eval_mul_partner_sum hp i k
  have hR := eval_mul_partner_sum hp k i
  have hR' :
      ∑ j : Fin ((p - 1) / 2), evalMatrix p k j * partnerMatrix p i j =
        ∑ j : Fin ((p - 1) / 2),
          quadraticChar (ZMod p)
            ((((i.val + 1 : ℕ) : ZMod p) ^ 2 -
                (epsInt p : ZMod p) * (-posNodes p j)) *
              (((k.val + 1 : ℕ) : ZMod p) ^ 2 +
                (epsInt p : ZMod p) * (-posNodes p j))) := by
    refine hR.trans ?_
    refine Fintype.sum_congr _ _ fun j => ?_
    congr 1
    ring
  rw [hL, hR', pair_sum_eq_complete hp i k, complete_char_sum_pair hp i k,
    chi_ab_squares]
  norm_num

/- The partner matrix is invertible. -/

noncomputable def partnerPoly {p : ℕ} [Fact p.Prime]
    (v : Fin ((p - 1) / 2) → ZMod p) : Polynomial (ZMod p) :=
  ∑ j : Fin ((p - 1) / 2),
    C (v j) * (X + C ((epsInt p : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))) ^
      ((p - 1) / 2)

lemma partnerPoly_eval {p : ℕ} [Fact p.Prime]
    (v : Fin ((p - 1) / 2) → ZMod p) (i : Fin ((p - 1) / 2)) :
    (partnerPoly v).eval (((i.val + 1 : ℕ) : ZMod p) ^ 2) =
      ((fun i j : Fin ((p - 1) / 2) =>
        ((((i.val + 1 : ℕ) : ZMod p) ^ 2 +
          (epsInt p : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)) ^
            ((p - 1) / 2))) *ᵥ v) i := by
  simp only [partnerPoly, mulVec, dotProduct, eval_finset_sum, eval_mul, eval_C,
    eval_pow, eval_add, eval_X]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma partnerPoly_natDegree_le {p : ℕ} [Fact p.Prime]
    (v : Fin ((p - 1) / 2) → ZMod p) :
    (partnerPoly v).natDegree ≤ (p - 1) / 2 := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  have hle := natDegree_pow_le_of_le ((p - 1) / 2)
    (natDegree_X_add_C
      ((epsInt p : ZMod p) * ((j.val + 1 : ℕ) : ZMod p))).le
  simpa using hle

lemma partnerPoly_eq_C_mul {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (v : Fin ((p - 1) / 2) → ZMod p)
    (hv : (fun i j : Fin ((p - 1) / 2) =>
        ((((i.val + 1 : ℕ) : ZMod p) ^ 2 +
          (epsInt p : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)) ^
            ((p - 1) / 2))) *ᵥ v = 0) :
    ∃ c : ZMod p, partnerPoly v = C c * (X ^ ((p - 1) / 2) - 1) := by
  let P : (ZMod p)[X] := partnerPoly v
  let Q : (ZMod p)[X] := X ^ ((p - 1) / 2) - 1
  let c : ZMod p := P.coeff ((p - 1) / 2)
  refine ⟨c, ?_⟩
  let D : (ZMod p)[X] := P - C c * Q
  have hm : 0 < (p - 1) / 2 := m_pos hp2
  have hPdeg : P.natDegree ≤ (p - 1) / 2 := partnerPoly_natDegree_le v
  have hQ_m : Q.coeff ((p - 1) / 2) = 1 := by
    dsimp [Q]
    simp [coeff_X_pow, coeff_sub, coeff_one, hm.ne']
  have hD_high : ∀ n, (p - 1) / 2 ≤ n → D.coeff n = 0 := by
    intro n hn
    dsimp [D]
    rw [coeff_sub, coeff_C_mul]
    rcases eq_or_lt_of_le hn with rfl | hlt
    · simp [c, hQ_m]
    · have hPn : P.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (hPdeg.trans_lt hlt)
      have hQn : Q.coeff n = 0 := by
        dsimp [Q]
        have hn0 : n ≠ 0 := by omega
        simp [coeff_X_pow, coeff_sub, coeff_one, Nat.ne_of_gt hlt, hn0]
      simp [hPn, hQn]
  have hDeval : ∀ i : Fin ((p - 1) / 2),
      D.eval (((i.val + 1 : ℕ) : ZMod p) ^ 2) = 0 := by
    intro i
    have hP0 : P.eval (((i.val + 1 : ℕ) : ZMod p) ^ 2) = 0 := by
      dsimp [P]
      rw [partnerPoly_eval v i]
      exact congrFun hv i
    have hQ0 : Q.eval (((i.val + 1 : ℕ) : ZMod p) ^ 2) = 0 := by
      dsimp [Q]
      rw [eval_sub, eval_pow, eval_X, eval_one, sq_pow_eq_one hp2 i]
      simp
    dsimp [D]
    rw [eval_sub, eval_mul, eval_C, hP0, hQ0]
    ring
  by_cases hD0 : D = 0
  · have : P = C c * Q := sub_eq_zero.mp hD0
    simpa [P, Q] using this
  · have hdeg : D.natDegree < (p - 1) / 2 := by
      have : D.natDegree ≤ (p - 1) / 2 - 1 :=
        (natDegree_le_iff_coeff_eq_zero).2 fun N hN => hD_high N (by omega)
      omega
    have : D = 0 :=
      eq_zero_of_natDegree_lt_card_of_eval_eq_zero D
        (sq_nodes_injective hp2) hDeval (by
          simpa [Fintype.card_fin] using hdeg)
    contradiction

lemma partnerPoly_coeff {p : ℕ} [Fact p.Prime]
    (v : Fin ((p - 1) / 2) → ZMod p) (k : ℕ) :
    (partnerPoly v).coeff k =
      ∑ j : Fin ((p - 1) / 2),
        v j * ((((p - 1) / 2).choose k : ZMod p) *
          (((epsInt p : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)) ^
            (((p - 1) / 2) - k))) := by
  unfold partnerPoly
  rw [finset_sum_coeff]
  refine Fintype.sum_congr _ _ fun j => ?_
  rw [coeff_C_mul, coeff_X_add_C_pow]
  ring

lemma partner_moment_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (v : Fin ((p - 1) / 2) → ZMod p) {c : ZMod p}
    (hc : partnerPoly v = C c * (X ^ ((p - 1) / 2) - 1)) :
    ∑ j : Fin ((p - 1) / 2), v j = c := by
  have hm : 0 < (p - 1) / 2 := m_pos hp2
  have h : (partnerPoly v).coeff ((p - 1) / 2) =
      (C c * (X ^ ((p - 1) / 2) - 1)).coeff ((p - 1) / 2) :=
    congrArg (fun q : (ZMod p)[X] => q.coeff ((p - 1) / 2)) hc
  have hlhs : (partnerPoly v).coeff ((p - 1) / 2) =
      ∑ j : Fin ((p - 1) / 2), v j := by
    rw [partnerPoly_coeff]
    refine Fintype.sum_congr _ _ fun j => ?_
    simp [Nat.choose_self]
  have hrhs : (C c * (X ^ ((p - 1) / 2) - 1)).coeff ((p - 1) / 2) = c := by
    simp [coeff_C_mul, coeff_X_pow, coeff_sub, coeff_one, hm.ne']
  exact hlhs.symm.trans (h.trans hrhs)

lemma partner_middle_moments {p : ℕ} [Fact p.Prime] (_hp2 : p ≠ 2)
    (v : Fin ((p - 1) / 2) → ZMod p) {c : ZMod p}
    (hc : partnerPoly v = C c * (X ^ ((p - 1) / 2) - 1))
    {s : ℕ} (hs0 : 0 < s) (hs : s < (p - 1) / 2) :
    ∑ j : Fin ((p - 1) / 2), v j * ((j.val + 1 : ℕ) : ZMod p) ^ s = 0 := by
  have hr0 : (p - 1) / 2 - s ≠ 0 := by omega
  have hrm : (p - 1) / 2 - s ≠ (p - 1) / 2 := by omega
  have hcoeff : (partnerPoly v).coeff ((p - 1) / 2 - s) =
      (C c * (X ^ ((p - 1) / 2) - 1)).coeff ((p - 1) / 2 - s) :=
    congrArg (fun q : (ZMod p)[X] => q.coeff ((p - 1) / 2 - s)) hc
  have hrhs : (C c * (X ^ ((p - 1) / 2) - 1)).coeff ((p - 1) / 2 - s) = 0 := by
    simp [coeff_C_mul, coeff_X_pow, coeff_sub, coeff_one, hrm, hr0]
  have hch : (((p - 1) / 2).choose ((p - 1) / 2 - s) : ZMod p) ≠ 0 :=
    choose_cast_ne_zero (by have := m_lt_p (p := p); omega) (Nat.sub_le _ _)
  have hpow : (p - 1) / 2 - ((p - 1) / 2 - s) = s := by omega
  have hlhs :
      (partnerPoly v).coeff ((p - 1) / 2 - s) =
        (((p - 1) / 2).choose ((p - 1) / 2 - s) : ZMod p) *
          ((epsInt p : ZMod p) ^ s) *
          ∑ j : Fin ((p - 1) / 2),
            v j * ((j.val + 1 : ℕ) : ZMod p) ^ s := by
    rw [partnerPoly_coeff]
    simp only [hpow]
    conv_rhs => rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun j => ?_
    rw [mul_pow]
    ring
  have hεs : (epsInt p : ZMod p) ^ s ≠ 0 := pow_ne_zero _ (epsInt_zmod_ne_zero (p := p))
  have : (((p - 1) / 2).choose ((p - 1) / 2 - s) : ZMod p) *
      ((epsInt p : ZMod p) ^ s) *
      ∑ j : Fin ((p - 1) / 2),
        v j * ((j.val + 1 : ℕ) : ZMod p) ^ s = 0 := by
    rw [← hlhs, hcoeff, hrhs]
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact (hch h).elim
    · exact (hεs h).elim
  · exact h

lemma partner_last_moment {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (v : Fin ((p - 1) / 2) → ZMod p) {c : ZMod p}
    (hc : partnerPoly v = C c * (X ^ ((p - 1) / 2) - 1)) :
    (epsInt p : ZMod p) ^ ((p - 1) / 2) *
      ∑ j : Fin ((p - 1) / 2),
        v j * ((j.val + 1 : ℕ) : ZMod p) ^ ((p - 1) / 2) = -c := by
  have hm : 0 < (p - 1) / 2 := m_pos hp2
  have hcoeff : (partnerPoly v).coeff 0 =
      (C c * (X ^ ((p - 1) / 2) - 1)).coeff 0 :=
    congrArg (fun q : (ZMod p)[X] => q.coeff 0) hc
  have hrhs : (C c * (X ^ ((p - 1) / 2) - 1)).coeff 0 = -c := by
    have hm0 : ¬ (0 = (p - 1) / 2) := fun h => hm.ne' h.symm
    simp [coeff_X_pow, coeff_sub, coeff_one, hm0]
  have hlhs : (partnerPoly v).coeff 0 =
      ∑ j : Fin ((p - 1) / 2),
        v j * (((epsInt p : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)) ^
          ((p - 1) / 2)) := by
    rw [partnerPoly_coeff]
    simp
  have hfactor :
      ∑ j : Fin ((p - 1) / 2),
          v j * (((epsInt p : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)) ^
            ((p - 1) / 2)) =
        (epsInt p : ZMod p) ^ ((p - 1) / 2) *
          ∑ j : Fin ((p - 1) / 2),
            v j * ((j.val + 1 : ℕ) : ZMod p) ^ ((p - 1) / 2) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_congr _ _ fun j => ?_
    rw [mul_pow]
    ring
  rw [← hfactor, ← hlhs, hcoeff, hrhs]

lemma partnerPow_mulVec_eq_zero_imp {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    (v : Fin ((p - 1) / 2) → ZMod p)
    (hv : (fun i j : Fin ((p - 1) / 2) =>
        ((((i.val + 1 : ℕ) : ZMod p) ^ 2 +
          (epsInt p : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)) ^
            ((p - 1) / 2))) *ᵥ v = 0) :
    v = 0 := by
  have hp2 : p ≠ 2 := by intro h; subst h; simp at hp
  have hodd : Odd ((p - 1) / 2) := m_odd_of_three_mod_four hp
  obtain ⟨c, hc⟩ := partnerPoly_eq_C_mul hp2 v hv
  have hsum := partner_moment_zero hp2 v hc
  have hmid : ∀ s : ℕ, 0 < s → s < (p - 1) / 2 →
      ∑ j : Fin ((p - 1) / 2), v j * ((j.val + 1 : ℕ) : ZMod p) ^ s = 0 :=
    fun s hs0 hs => partner_middle_moments hp2 v hc hs0 hs
  have hlast := partner_last_moment hp2 v hc
  have hbsum := binomVec_sum hp2
  have hsign : (-1 : ZMod p) ^ (((p - 1) / 2) + 1) = 1 := by
    have : Even (((p - 1) / 2) + 1) := by
      have : (((p - 1) / 2) + 1) % 2 = 0 := by omega
      exact Nat.even_iff.2 this
    simpa using Even.neg_one_pow this
  have hbsum1 : ∑ i : Fin ((p - 1) / 2), binomVec p i = 1 := by
    simpa [hsign] using hbsum
  let w : Fin ((p - 1) / 2) → ZMod p := fun j => v j - c * binomVec p j
  have hw : ∀ k : Fin ((p - 1) / 2),
      ∑ j : Fin ((p - 1) / 2),
        w j * ((j.val + 1 : ℕ) : ZMod p) ^ (k.val : ℕ) = 0 := by
    intro k
    have hsplit :
        ∑ j : Fin ((p - 1) / 2),
          w j * ((j.val + 1 : ℕ) : ZMod p) ^ (k.val : ℕ) =
        ∑ j : Fin ((p - 1) / 2),
          v j * ((j.val + 1 : ℕ) : ZMod p) ^ (k.val : ℕ) -
        c * ∑ j : Fin ((p - 1) / 2),
          binomVec p j * ((j.val + 1 : ℕ) : ZMod p) ^ (k.val : ℕ) := by
      simp only [w, sub_mul, Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]
    rw [hsplit]
    by_cases hk0 : k.val = 0
    · have hv0 : ∑ j : Fin ((p - 1) / 2),
          v j * ((j.val + 1 : ℕ) : ZMod p) ^ (k.val : ℕ) = c := by
        simpa [hk0] using hsum
      have hb0 : ∑ j : Fin ((p - 1) / 2),
          binomVec p j * ((j.val + 1 : ℕ) : ZMod p) ^ (k.val : ℕ) = 1 := by
        simpa [hk0] using hbsum1
      rw [hv0, hb0]; ring
    · have hv := hmid k.val (Nat.pos_of_ne_zero hk0) k.isLt
      have hb := binomVec_moment_of_lt (p := p) (Nat.pos_of_ne_zero hk0) k.isLt
      rw [hv, hb, mul_zero, sub_zero]
  have hw0 : w = 0 := moments_zero_imp_eq_zero w hw
  have hvlam : v = fun j => c * binomVec p j := by
    funext j
    have : w j = 0 := congrFun hw0 j
    exact eq_of_sub_eq_zero this
  have hμlast :
      ∑ j : Fin ((p - 1) / 2),
        v j * ((j.val + 1 : ℕ) : ZMod p) ^ ((p - 1) / 2) =
      c * (((p - 1) / 2)! : ZMod p) := by
    simp only [hvlam, mul_assoc, ← Finset.mul_sum]
    rw [binomVec_moment_eq_factorial hp2]
  have hεm : (epsInt p : ZMod p) ^ ((p - 1) / 2) = (epsInt p : ZMod p) := by
    have : (p - 1) / 2 = 2 * (((p - 1) / 2) / 2) + 1 := by
      have := hodd
      omega
    rw [this, pow_succ, pow_mul, epsInt_zmod_sq (p := p), one_pow, one_mul]
  have hεC : (epsInt p : ZMod p) * (((p - 1) / 2)! : ZMod p) = 1 := by
    rw [epsInt_spec hp]
    simpa [pow_two] using factorial_half_sq_of_three_mod_four (p := p) hp
  have : (epsInt p : ZMod p) * (c * (((p - 1) / 2)! : ZMod p)) = -c := by
    rw [← hμlast, ← hεm, hlast]
  have : c * ((epsInt p : ZMod p) * (((p - 1) / 2)! : ZMod p) + 1) = 0 := by
    linear_combination this
  rw [hεC, one_add_one_eq_two] at this
  have hc0 : c = 0 := (mul_eq_zero.mp this).resolve_right (two_ne_zero_zmod hp2)
  funext j
  simp [hvlam, hc0]

lemma partnerMatrix_map_zmod {p : ℕ} [Fact p.Prime] (_hp : p % 4 = 3)
    (hp2 : p ≠ 2) :
    (partnerMatrix p).map (Int.cast : ℤ → ZMod p) =
      fun i j =>
        ((((i.val + 1 : ℕ) : ZMod p) ^ 2 +
          (epsInt p : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)) ^
            ((p - 1) / 2)) := by
  ext i j
  have := jacobiSym_eq_legendre (p := p)
    (((i.val + 1 : ℕ) : ℤ) * ((i.val + 1 : ℕ) : ℤ) +
      epsInt p * ((j.val + 1 : ℕ) : ℤ))
  simp only [partnerMatrix, Matrix.map_apply]
  rw [this, legendreSym.eq_pow]
  have hdiv : p / 2 = (p - 1) / 2 := p_div_two_eq (odd_p hp2)
  simp [hdiv, pow_two]

lemma partnerMatrix_det_ne_zero {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    (partnerMatrix p).det ≠ 0 := by
  have hp2 : p ≠ 2 := by intro h; subst h; simp at hp
  intro hdet
  have hmap := (Int.castRingHom (ZMod p)).map_det (partnerMatrix p)
  have h0 : ((Int.castRingHom (ZMod p)).mapMatrix (partnerMatrix p)).det = 0 := by
    rw [← hmap, hdet, map_zero]
  have hmeq : (Int.castRingHom (ZMod p)).mapMatrix (partnerMatrix p) =
      (partnerMatrix p).map (Int.cast : ℤ → ZMod p) := rfl
  rw [hmeq, partnerMatrix_map_zmod hp hp2] at h0
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff
      (M := (fun (i j : Fin ((p - 1) / 2)) =>
        ((((i.val + 1 : ℕ) : ZMod p) ^ 2 +
          (epsInt p : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)) ^
            ((p - 1) / 2))))).mpr h0
  exact hv0 (partnerPow_mulVec_eq_zero_imp hp v hv)

lemma evalMatrix_det_eq_zero_of_three_mod_four {p : ℕ} [Fact p.Prime]
    (hp : p % 4 = 3) : (evalMatrix p).det = 0 := by
  have hN := partnerMatrix_det_ne_zero hp
  have hskew := eval_mul_partner_transpose_is_skew hp
  have hodd := card_fin_m_odd hp
  have hprod :
      ((evalMatrix p) * (partnerMatrix p)ᵀ).det = 0 :=
    det_eq_zero_of_transpose_eq_neg _ hskew hodd
  have : (evalMatrix p).det * (partnerMatrix p).det = 0 := by
    simpa [Matrix.det_mul, Matrix.det_transpose] using hprod
  exact (mul_eq_zero.mp this).resolve_right hN


end OEIS226163

/--
Conjecture: a(n) = 0 if and only if p_n ≡ 3 (mod 4).
-/
theorem oeis_226163_conjecture_0 (n : ℕ) (h_n : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  rw [OEIS226163.A226163_eq h_n]
  set p := Nat.nth Nat.Prime (n - 1)
  haveI : Fact p.Prime := ⟨prime_nth_prime (n - 1)⟩
  have hp2 : p ≠ 2 := OEIS226163.nth_prime_ne_two h_n
  rcases OEIS226163.odd_prime_mod_four hp2 with h1 | h3
  · constructor
    · intro hdet
      exact (OEIS226163.evalMatrix_det_ne_zero_of_one_mod_four h1 hdet).elim
    · intro h
      omega
  · constructor
    · intro _; exact h3
    · intro _
      exact OEIS226163.evalMatrix_det_eq_zero_of_three_mod_four h3
