import FormalConjectures.Util.ProblemImports
open Nat Finset

-- reuse absorbZ, binomCore, binomIdE from Dev (copy minimal)
lemma absorbZ (n k : ℕ) :
    ((n.choose (k+1) : ℤ)) * ((k:ℤ)+1) = (n.choose k : ℤ) * ((n:ℤ) - (k:ℤ)) := by
  by_cases h : k ≤ n
  · have hnat : n.choose (k+1) * (k+1) = n.choose k * (n - k) := by rw [Nat.choose_succ_right_eq]
    have := congrArg (Nat.cast : ℕ → ℤ) hnat
    push_cast [Nat.cast_sub h] at this; linarith [this]
  · have h1 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : n.choose (k+1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h1, h2]

lemma binomCore (m k : ℕ) :
    ((m+2:ℤ)^2) * ((m+2).choose (k+2)) - (3*(m+2:ℤ)^2 - 3*(m+2) + 1) * ((m+1).choose (k+2))
      + 2*(m+1:ℤ)^2 * (m.choose (k+2))
    = ((k:ℤ)+2)^2 * ((m+1).choose (k+1)) - ((k:ℤ)+3)^2 * ((m+1).choose (k+3)) := by
  have p1 : (m+2).choose (k+2) = m.choose k + 2 * m.choose (k+1) + m.choose (k+2) := by
    rw [Nat.choose_succ_succ (m+1) (k+1), Nat.choose_succ_succ m k, Nat.choose_succ_succ m (k+1)]; ring
  have p2 : (m+1).choose (k+2) = m.choose (k+1) + m.choose (k+2) := Nat.choose_succ_succ m (k+1)
  have p3 : (m+1).choose (k+1) = m.choose k + m.choose (k+1) := Nat.choose_succ_succ m k
  have p4 : (m+1).choose (k+3) = m.choose (k+2) + m.choose (k+3) := Nat.choose_succ_succ m (k+2)
  have A1 := absorbZ m k
  have A2 := absorbZ m (k+1)
  have A3 := absorbZ m (k+2)
  push_cast [p1, p2, p3, p4] at *
  linear_combination (- ((m:ℤ)+k+4)) * A1 + ((m:ℤ)+1) * A2 + ((k:ℤ)+3) * A3

lemma binomIdE (N j : ℕ) :
    ((N+2:ℤ)^2) * ((N+2).choose (2*j)) - (3*(N+2:ℤ)^2 - 3*(N+2) + 1) * ((N+1).choose (2*j))
      + 2*(N+1:ℤ)^2 * (N.choose (2*j))
    = (2*j:ℤ)^2 * ((N+1).choose (2*j-1)) - ((2*j:ℤ)+1)^2 * ((N+1).choose (2*j+1)) := by
  match j with
  | 0 =>
    simp only [Nat.mul_zero, Nat.zero_sub, zero_add, Nat.choose_zero_right, Nat.choose_one_right]
    push_cast; ring
  | (jj+1) =>
    have e2 : 2*(jj+1)-1 = (2*jj)+1 := by omega
    have e3 : 2*(jj+1)+1 = (2*jj)+3 := by omega
    have e1 : 2*(jj+1) = (2*jj)+2 := by ring
    rw [e2, e3, e1]
    have := binomCore N (2*jj)
    push_cast at this ⊢
    linear_combination this

-- central binomial relation
lemma centralBinomRel (j : ℕ) :
    ((j:ℤ)+1) * ((2*j+2).choose (j+1)) = 2*(2*(j:ℤ)+1) * ((2*j).choose j) := by
  have h := Nat.succ_mul_centralBinom_succ j
  simp only [Nat.centralBinom] at h
  have e : 2*(j+1) = 2*j+2 := by ring
  rw [e] at h
  have := congrArg (Nat.cast : ℕ → ℤ) h
  push_cast at this
  linarith [this]

noncomputable def Tz (n j : ℕ) : ℤ :=
  (n.choose (2*j) : ℤ) * (8:ℤ)^(n-2*j) * (4:ℤ)^j * ((2*j).choose j : ℤ)^2

noncomputable def Gz (n j : ℕ) : ℤ :=
  -(4:ℤ)*(j:ℤ)^2 * ((n-1).choose (2*j-1) : ℤ) * (8:ℤ)^(n-2*j) * (4:ℤ)^j * ((2*j).choose j : ℤ)^2

-- squared central binomial relation
lemma centralBinomSq (j : ℕ) :
    ((j:ℤ)+1)^2 * ((2*j+2).choose (j+1) : ℤ)^2 = 4*(2*(j:ℤ)+1)^2 * ((2*j).choose j : ℤ)^2 := by
  have h := centralBinomRel j
  linear_combination (((j:ℤ)+1)*((2*j+2).choose (j+1):ℤ) + 2*(2*(j:ℤ)+1)*((2*j).choose j:ℤ)) * h

-- interior pointwise identity
lemma pointwise_interior (N j : ℕ) (hj : 2*j ≤ N) :
    ((N+2:ℤ)^2) * Tz (N+2) j - 8*(3*(N+2:ℤ)^2-3*(N+2)+1)*Tz (N+1) j
      + 128*((N+1:ℤ))^2*Tz N j = Gz (N+2) (j+1) - Gz (N+2) j := by
  have b := binomIdE N j
  have hsq := centralBinomSq j
  simp only [Tz, Gz]
  have pw1 : (N+2)-2*j = (N-2*j)+2 := by omega
  have pw2 : (N+1)-2*j = (N-2*j)+1 := by omega
  have pw3 : (N+2)-2*(j+1) = N-2*j := by omega
  have i1 : (N+2)-1 = N+1 := by omega
  have i2 : 2*(j+1)-1 = 2*j+1 := by omega
  have i3 : 2*(j+1) = 2*j+2 := by ring
  rw [pw3, i2, i1, pw1, pw2, i3]
  simp only [pow_add, pow_succ, pow_one]
  push_cast
  linear_combination (64*(8:ℤ)^(N-2*j)*(4:ℤ)^j*((2*j).choose j:ℤ)^2) * b
     + (16*(8:ℤ)^(N-2*j)*(4:ℤ)^j*((N+1).choose (2*j+1):ℤ)) * hsq

lemma pointwise (N j : ℕ) :
    ((N+2:ℤ)^2) * Tz (N+2) j - 8*(3*(N+2:ℤ)^2-3*(N+2)+1)*Tz (N+1) j
      + 128*((N+1:ℤ))^2*Tz N j = Gz (N+2) (j+1) - Gz (N+2) j := by
  by_cases h : 2*j ≤ N
  · exact pointwise_interior N j h
  · by_cases hA : 2*j = N+1
    · -- 2j = N+1
      have e1 : (N+2).choose (2*j) = N+2 := by
        rw [show 2*j = N+1 by omega]; exact Nat.choose_succ_self_right (N+1)
      have e2 : (N+1).choose (2*j) = 1 := by rw [show 2*j = N+1 by omega]; exact Nat.choose_self _
      have e3 : N.choose (2*j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have e4 : (N+2-1).choose (2*j-1) = N+1 := by
        rw [show N+2-1 = N+1 by omega, show 2*j-1 = N by omega]; exact Nat.choose_succ_self_right N
      have e5 : (N+2-1).choose (2*(j+1)-1) = 0 := by
        rw [show N+2-1=N+1 by omega]; exact Nat.choose_eq_zero_of_lt (by omega)
      have ex1 : (N+2)-2*j = 1 := by omega
      have ex2 : (N+1)-2*j = 0 := by omega
      have ex3 : (N+2)-2*(j+1) = 0 := by omega
      simp only [Tz, Gz, e1, e2, e3, e4, e5, ex1, ex2, ex3, pow_zero, pow_one]
      have hz2' : (N+1:ℤ)^2 = 4*(j:ℤ)^2 := by
        have : (N+1:ℤ) = 2*(j:ℤ) := by exact_mod_cast (by omega : N+1 = 2*j)
        rw [this]; ring
      have hz3 : (N+2:ℤ)^3 - 3*(N+2)^2 + 3*(N+2) - 1 = (N+1)^3 := by ring
      push_cast
      linear_combination ((8:ℤ)*(4:ℤ)^j*((2*j).choose j:ℤ)^2)*hz3 + ((8:ℤ)*(4:ℤ)^j*((2*j).choose j:ℤ)^2*((N:ℤ)+1))*hz2'
    · by_cases hB : 2*j = N+2
      · -- 2j = N+2
        have e1 : (N+2).choose (2*j) = 1 := by rw [show 2*j = N+2 by omega]; exact Nat.choose_self _
        have e2 : (N+1).choose (2*j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have e3 : N.choose (2*j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have e4 : (N+2-1).choose (2*j-1) = 1 := by
          rw [show N+2-1 = N+1 by omega, show 2*j-1 = N+1 by omega]; exact Nat.choose_self _
        have e5 : (N+2-1).choose (2*(j+1)-1) = 0 := by
          rw [show N+2-1=N+1 by omega]; exact Nat.choose_eq_zero_of_lt (by omega)
        have ex1 : (N+2)-2*j = 0 := by omega
        have ex3 : (N+2)-2*(j+1) = 0 := by omega
        simp only [Tz, Gz, e1, e2, e3, e4, e5, ex1, ex3, pow_zero]
        have hz2 : (N+2:ℤ)^2 = 4*(j:ℤ)^2 := by
          have : (N+2:ℤ) = 2*(j:ℤ) := by exact_mod_cast (by omega : N+2 = 2*j)
          rw [this]; ring
        push_cast
        linear_combination ((4:ℤ)^j*((2*j).choose j:ℤ)^2) * hz2
      · -- 2j ≥ N+3
        have c1 : (N+2).choose (2*j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have c2 : (N+1).choose (2*j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have c3 : N.choose (2*j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have c4 : (N+1).choose (2*j-1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have c5 : (N+1).choose (2*(j+1)-1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [Tz, Gz, c1, c2, c3, c4, c5]

def natT (n j : ℕ) : ℕ := n.choose (2*j) * 8^(n-2*j) * 4^j * ((2*j).choose j)^2
lemma Tz_eq (n j : ℕ) : Tz n j = (natT n j : ℤ) := by
  simp only [Tz, natT]; push_cast; ring
def natF (n : ℕ) : ℕ := ∑ j ∈ range (n+1), natT n j

lemma sum_pointwise (N : ℕ) :
    ∑ j ∈ range (N+3), (((N+2:ℤ)^2)*Tz (N+2) j - 8*(3*(N+2:ℤ)^2-3*(N+2)+1)*Tz (N+1) j
      + 128*((N+1:ℤ))^2*Tz N j) = 0 := by
  rw [Finset.sum_congr rfl (fun j _ => pointwise N j)]
  rw [Finset.sum_range_sub (fun j => Gz (N+2) j)]
  have g0 : Gz (N+2) 0 = 0 := by simp [Gz]
  have gN : Gz (N+2) (N+3) = 0 := by
    have hc : (N+1).choose (2*(N+3)-1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [Gz, hc]
  rw [g0, gN]; ring

-- convert range(N+3) sums to natF
lemma sumTz_eq_natF (n : ℕ) : ∑ j ∈ range (n+1), Tz n j = (natF n : ℤ) := by
  simp only [natF, Tz_eq]; push_cast; rfl

lemma sumTz_big (n M : ℕ) (hM : n+1 ≤ M) : ∑ j ∈ range M, Tz n j = (natF n : ℤ) := by
  rw [← sumTz_eq_natF]
  have hsub : range (n+1) ⊆ range M := by
    intro x hx; simp only [Finset.mem_range] at *; omega
  refine (Finset.sum_subset hsub ?_).symm
  intro j hj hj'
  simp only [Finset.mem_range] at hj hj'
  have : n < 2*j := by omega
  simp [Tz, Nat.choose_eq_zero_of_lt this]

lemma Frec (N : ℕ) :
    ((N+2:ℤ)^2)*(natF (N+2)) - 8*(3*(N+2:ℤ)^2-3*(N+2)+1)*(natF (N+1))
      + 128*((N+1:ℤ))^2*(natF N) = 0 := by
  have h := sum_pointwise N
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum] at h
  rw [sumTz_big (N+2) (N+3) (by omega), sumTz_big (N+1) (N+3) (by omega),
      sumTz_big N (N+3) (by omega)] at h
  linarith [h]

def aa : ℕ → ℕ
| 0 => 1
| 1 => 8
| n + 2 =>
  let n' := n + 2
  let an_minus_1 := aa (n + 1)
  let an_minus_2 := aa n
  let term1_factor := 8 * (3 * n'^2 - 3 * n' + 1)
  let term2_factor := 128 * (n' - 1)^2
  (term1_factor * an_minus_1 - term2_factor * an_minus_2) / (n'^2)

lemma natFrec_nat (N : ℕ) :
    (N+2)^2 * natF (N+2) = 8*(3*(N+2)^2-3*(N+2)+1)*natF (N+1) - 128*(N+1)^2*natF N := by
  have hle : 3*(N+2) ≤ 3*(N+2)^2 := by nlinarith
  have h := Frec N
  have hbig : 128*(N+1)^2*natF N ≤ 8*(3*(N+2)^2-3*(N+2)+1)*natF (N+1) := by
    have hz : ((128*(N+1)^2*natF N : ℕ):ℤ) ≤ ((8*(3*(N+2)^2-3*(N+2)+1)*natF (N+1):ℕ):ℤ) := by
      push_cast [Nat.cast_sub hle]
      nlinarith [h, Int.natCast_nonneg (natF (N+2)), sq_nonneg ((N:ℤ)+2)]
    exact_mod_cast hz
  zify [hbig, hle]
  push_cast at h ⊢
  linarith [h]

lemma aa_eq_natF : ∀ n, aa n = natF n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | (N+2) =>
      have ih1 : aa (N+1) = natF (N+1) := ih (N+1) (by omega)
      have ih0 : aa N = natF N := ih N (by omega)
      have hdef : aa (N+2)
          = (8*(3*(N+2)^2-3*(N+2)+1)*aa (N+1) - 128*((N+2)-1)^2*aa N)/((N+2)^2) := rfl
      rw [hdef, ih1, ih0, show (N+2)-1 = N+1 by omega, ← natFrec_nat N]
      rw [Nat.mul_div_cancel_left _ (by positivity)]
