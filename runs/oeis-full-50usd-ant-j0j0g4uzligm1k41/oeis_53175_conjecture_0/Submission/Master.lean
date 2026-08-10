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

-- ===== Centered moments and moment expansion =====
open scoped BigOperators

noncomputable def cmom (p : ℕ) : ℤ := if Even p then (4:ℤ)^(p/2) * ((p.choose (p/2) : ℤ))^2 else 0

lemma sum_even_reindex (h : ℕ → ℤ) (N : ℕ) :
    ∑ p ∈ range N, (if Even p then h (p/2) else 0) = ∑ j ∈ range ((N+1)/2), h j := by
  induction N with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd M with he | ho
    · -- M even, M = k+k
      obtain ⟨k, rfl⟩ := he
      have hev : Even (k+k) := ⟨k, rfl⟩
      simp only [hev, if_true]
      rw [show (k+k+1)/2 = k by omega, show (k+k+1+1)/2 = k+1 by omega,
          show (k+k)/2 = k by omega, Finset.sum_range_succ]
    · -- M odd, M = 2k+1
      obtain ⟨k, rfl⟩ := ho
      have hod : ¬ Even (2*k+1) := by rw [Nat.not_even_iff_odd]; exact ⟨k, rfl⟩
      simp only [hod, if_false]
      rw [show (2*k+1+1)/2 = k+1 by omega, show (2*k+1+1+1)/2 = k+1 by omega]
      simp

lemma moment_expand (r : ℕ) :
    (aa r : ℤ) = ∑ p ∈ range (r+1), ((r.choose p : ℤ)) * (8:ℤ)^(r-p) * cmom p := by
  rw [aa_eq_natF, ← sumTz_eq_natF]
  -- rewrite RHS terms
  have hf : ∀ p ∈ range (r+1), ((r.choose p : ℤ)) * (8:ℤ)^(r-p) * cmom p
      = (if Even p then (Tz r (p/2)) else 0) := by
    intro p _
    unfold cmom Tz
    by_cases hp : Even p
    · obtain ⟨k, rfl⟩ := hp
      have hev : Even (k+k) := ⟨k, rfl⟩
      simp only [hev, if_true]
      rw [show (k+k)/2 = k by omega]; push_cast; ring
    · simp [hp]
  rw [Finset.sum_congr rfl hf, sum_even_reindex (fun j => Tz r j) (r+1)]
  -- now ∑ j ∈ range ((r+2)/2), Tz r j  =  ∑ j ∈ range (r+1), Tz r j
  symm
  apply Finset.sum_subset
  · intro x hx; simp only [Finset.mem_range] at *; omega
  · intro j _ hj
    simp only [Finset.mem_range] at hj
    have : r < 2*j := by omega
    simp [Tz, Nat.choose_eq_zero_of_lt this]

-- ===== Matrix congruence P = L C Lᵀ =====
open Matrix

def PP (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℤ := Matrix.of fun i j => (aa (i.val + j.val) : ℤ)

def Lmat (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℤ :=
  Matrix.of fun i l => (i.val.choose l.val : ℤ) * (8:ℤ)^(i.val - l.val)

noncomputable def Cmat (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℤ :=
  Matrix.of fun l m => cmom (l.val + m.val)

-- termwise 8-power identity
lemma term_eq (i j l m : ℕ) :
    ((i.choose l : ℤ) * (j.choose m : ℤ)) * (8:ℤ)^(i+j-(l+m)) * cmom (l+m)
    = ((i.choose l : ℤ) * (8:ℤ)^(i-l)) * cmom (l+m) * ((j.choose m : ℤ) * (8:ℤ)^(j-m)) := by
  by_cases hl : l ≤ i
  · by_cases hm : m ≤ j
    · have : i+j-(l+m) = (i-l)+(j-m) := by omega
      rw [this, pow_add]; ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : j < m)]; push_cast; ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : i < l)]; push_cast; ring

-- box (support) form of the moment expansion
lemma boxKEY (i j n : ℕ) (hi : i ≤ n) (hj : j ≤ n) :
    (aa (i+j) : ℤ)
    = ∑ l ∈ range (n+1), ∑ m ∈ range (n+1),
        ((i.choose l : ℤ) * (8:ℤ)^(i-l)) * cmom (l+m) * ((j.choose m : ℤ) * (8:ℤ)^(j-m)) := by
  -- Start from moment_expand and expand with Vandermonde
  rw [moment_expand (i+j)]
  -- LHS: ∑ s ∈ range (i+j+1), C(i+j,s) 8^{i+j-s} cmom s
  have vdm : ∀ s, ((i+j).choose s : ℤ)
      = ∑ x ∈ Finset.antidiagonal s, (i.choose x.1 : ℤ) * (j.choose x.2 : ℤ) := by
    intro s
    rw [Nat.add_choose_eq]
    push_cast
    rfl
  have step1 : ∑ s ∈ range (i+j+1), ((i+j).choose s : ℤ) * (8:ℤ)^(i+j-s) * cmom s
      = ∑ s ∈ range (i+j+1), ∑ x ∈ Finset.antidiagonal s,
          ((i.choose x.1 : ℤ) * (j.choose x.2 : ℤ)) * (8:ℤ)^(i+j-s) * cmom s := by
    apply Finset.sum_congr rfl
    intro s _
    rw [vdm s, Finset.sum_mul, Finset.sum_mul]
  rw [step1]
  -- convert to term_eq form (using s = x.1 + x.2 on antidiagonal)
  have step2 : ∀ s ∈ range (i+j+1), ∑ x ∈ Finset.antidiagonal s,
          ((i.choose x.1 : ℤ) * (j.choose x.2 : ℤ)) * (8:ℤ)^(i+j-s) * cmom s
      = ∑ x ∈ Finset.antidiagonal s,
          ((i.choose x.1 : ℤ) * (8:ℤ)^(i - x.1)) * cmom (x.1+x.2)
            * ((j.choose x.2 : ℤ) * (8:ℤ)^(j - x.2)) := by
    intro s _
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_antidiagonal] at hx
    subst hx
    exact term_eq i j x.1 x.2
  rw [Finset.sum_congr rfl step2]
  -- Now flatten ∑_s ∑_{antidiag s} to a sum over pairs, then to box
  -- antidiagonal → range(s+1)
  have step3 : ∀ s ∈ range (i+j+1), ∑ x ∈ Finset.antidiagonal s,
          ((i.choose x.1 : ℤ) * (8:ℤ)^(i - x.1)) * cmom (x.1+x.2)
            * ((j.choose x.2 : ℤ) * (8:ℤ)^(j - x.2))
      = ∑ k ∈ range (s+1), ((i.choose k : ℤ) * (8:ℤ)^(i - k)) * cmom (k+(s-k))
            * ((j.choose (s-k) : ℤ) * (8:ℤ)^(j - (s-k))) := by
    intro s _
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_congr rfl step3]
  -- diag flip
  rw [Finset.sum_range_diag_flip (i+j+1)
      (fun a b => ((i.choose a : ℤ) * (8:ℤ)^(i - a)) * cmom (a+b)
            * ((j.choose b : ℤ) * (8:ℤ)^(j - b)))]
  -- Now LHS = ∑ l ∈ range(i+j+1), ∑ k ∈ range(i+j+1-l), F l k.
  -- inner: range(i+j+1-l) → range(j+1)
  have innerEq : ∀ l ∈ range (i+j+1),
      (∑ k ∈ range (i+j+1-l), ((i.choose l : ℤ) * (8:ℤ)^(i-l)) * cmom (l+k)
          * ((j.choose k : ℤ) * (8:ℤ)^(j-k)))
      = ∑ m ∈ range (j+1), ((i.choose l : ℤ) * (8:ℤ)^(i-l)) * cmom (l+m)
          * ((j.choose m : ℤ) * (8:ℤ)^(j-m)) := by
    intro l _
    by_cases hl : l ≤ i
    · refine (Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at *; omega) ?_).symm
      intro k _ hk
      simp only [Finset.mem_range] at hk
      rw [Nat.choose_eq_zero_of_lt (by omega : j < k)]; push_cast; ring
    · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · intro m _; rw [Nat.choose_eq_zero_of_lt (by omega : i < l)]; push_cast; ring
      · intro k _; rw [Nat.choose_eq_zero_of_lt (by omega : i < l)]; push_cast; ring
  rw [Finset.sum_congr rfl innerEq]
  -- outer: range(i+j+1) → range(i+1)
  have outerEq :
      (∑ l ∈ range (i+j+1), ∑ m ∈ range (j+1), ((i.choose l : ℤ) * (8:ℤ)^(i-l)) * cmom (l+m)
          * ((j.choose m : ℤ) * (8:ℤ)^(j-m)))
      = ∑ l ∈ range (i+1), ∑ m ∈ range (j+1), ((i.choose l : ℤ) * (8:ℤ)^(i-l)) * cmom (l+m)
          * ((j.choose m : ℤ) * (8:ℤ)^(j-m)) := by
    refine (Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at *; omega) ?_).symm
    intro l _ hl
    simp only [Finset.mem_range] at hl
    apply Finset.sum_eq_zero
    intro m _; rw [Nat.choose_eq_zero_of_lt (by omega : i < l)]; push_cast; ring
  rw [outerEq]
  -- RHS box: range(n+1) → range(i+1), range(j+1)
  symm
  -- inner shrink range(n+1) → range(j+1)
  have boxInner : ∀ l ∈ range (n+1),
      (∑ m ∈ range (n+1), ((i.choose l : ℤ) * (8:ℤ)^(i-l)) * cmom (l+m)
          * ((j.choose m : ℤ) * (8:ℤ)^(j-m)))
      = ∑ m ∈ range (j+1), ((i.choose l : ℤ) * (8:ℤ)^(i-l)) * cmom (l+m)
          * ((j.choose m : ℤ) * (8:ℤ)^(j-m)) := by
    intro l _
    refine (Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at *; omega) ?_).symm
    intro m _ hm
    simp only [Finset.mem_range] at hm
    rw [Nat.choose_eq_zero_of_lt (by omega : j < m)]; push_cast; ring
  rw [Finset.sum_congr rfl boxInner]
  -- outer shrink range(n+1) → range(i+1)
  refine (Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at *; omega) ?_).symm
  intro l _ hl
  simp only [Finset.mem_range] at hl
  apply Finset.sum_eq_zero
  intro m _; rw [Nat.choose_eq_zero_of_lt (by omega : i < l)]; push_cast; ring

lemma finrange2 (n : ℕ) (g : ℕ → ℕ → ℤ) :
    (∑ m : Fin (n+1), ∑ l : Fin (n+1), g l.val m.val)
    = ∑ l ∈ range (n+1), ∑ m ∈ range (n+1), g l m := by
  rw [Fin.sum_univ_eq_sum_range (fun mm => ∑ l : Fin (n+1), g l.val mm) (n+1)]
  rw [Finset.sum_congr rfl (fun m _ => Fin.sum_univ_eq_sum_range (fun ll => g ll m) (n+1))]
  rw [Finset.sum_comm]

lemma P_eq (n : ℕ) : PP n = Lmat n * Cmat n * (Lmat n)ᵀ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Lmat, Cmat, Matrix.of_apply, PP,
    Finset.sum_mul]
  rw [boxKEY i.val j.val n (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt)]
  rw [← finrange2 n (fun l m => ((i.val.choose l : ℤ) * (8:ℤ)^(i.val-l)) * cmom (l+m)
        * ((j.val.choose m : ℤ) * (8:ℤ)^(j.val-m)))]

lemma Lmat_lowerTri (n : ℕ) : (Lmat n).BlockTriangular OrderDual.toDual := by
  intro i j h
  have h' : i < j := OrderDual.toDual_lt_toDual.mp h
  simp only [Lmat, Matrix.of_apply]
  rw [Nat.choose_eq_zero_of_lt (Fin.lt_iff_val_lt_val.mp h')]
  simp

lemma Lmat_det (n : ℕ) : (Lmat n).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (Lmat_lowerTri n)]
  apply Finset.prod_eq_one
  intro i _
  simp [Lmat, Nat.choose_self]

lemma detPP (n : ℕ) : (PP n).det = (Cmat n).det := by
  rw [P_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Lmat_det]
  ring

-- ===== Central-binomial Hankel LDLᵀ identity =====
lemma choose_symm_shift (i j : ℕ) (h : j ≤ i) :
    (2*i).choose (i-j) = (2*i).choose (i+j) := by
  rw [← Nat.choose_symm (by omega : i+j ≤ 2*i)]; congr 1; omega

lemma vander_range (i k : ℕ) :
    (2*i+2*k).choose (i+k) = ∑ a ∈ range (i+k+1), (2*i).choose a * (2*k).choose (i+k-a) := by
  rw [Nat.add_choose_eq (2*i) (2*k) (i+k), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

lemma ldlKEY (i k : ℕ) :
    ((2*(i+k)).choose (i+k) : ℤ)
    = ∑ j ∈ range (i+k+1), (if j = 0 then (1:ℤ) else 2)
        * (if j ≤ i then ((2*i).choose (i-j):ℤ) else 0)
        * (if j ≤ k then ((2*k).choose (k-j):ℤ) else 0) := by
  set g : ℕ → ℤ := fun a => (if a+1 ≤ i then ((2*i).choose (i-(a+1)):ℤ) else 0)
        * (if a+1 ≤ k then ((2*k).choose (k-(a+1)):ℤ) else 0) with hg
  -- vander over ℤ
  have hv : ((2*(i+k)).choose (i+k) : ℤ)
      = ∑ a ∈ range (i+k+1), ((2*i).choose a : ℤ) * ((2*k).choose (i+k-a) : ℤ) := by
    have := vander_range i k
    rw [show 2*i+2*k = 2*(i+k) by ring] at this
    rw [this]; push_cast; rfl
  rw [hv]
  -- split at i+1 (only LHS occurrence)
  nth_rewrite 1 [show i+k+1 = (i+1)+k by omega]
  rw [Finset.sum_range_add]
  -- first block reflect a ↦ i-a
  rw [show (∑ a ∈ range (i+1), ((2*i).choose a : ℤ) * ((2*k).choose (i+k-a) : ℤ))
      = ∑ a ∈ range (i+1), ((2*i).choose (i-a) : ℤ) * ((2*k).choose (k+a) : ℤ) from ?_]
  · -- peel a=0 from first
    rw [Finset.sum_range_succ' (fun a => ((2*i).choose (i-a) : ℤ) * ((2*k).choose (k+a) : ℤ)) i]
    -- RHS: peel j=0
    rw [Finset.sum_range_succ' (fun j => (if j = 0 then (1:ℤ) else 2)
        * (if j ≤ i then ((2*i).choose (i-j):ℤ) else 0)
        * (if j ≤ k then ((2*k).choose (k-j):ℤ) else 0)) (i+k)]
    -- both constant terms are C(2i,i)C(2k,k)
    have hA' : (∑ a ∈ range i, ((2*i).choose (i-(a+1)) : ℤ) * ((2*k).choose (k+(a+1)) : ℤ))
        = ∑ a ∈ range (i+k), g a := by
      have e1 : (∑ a ∈ range i, ((2*i).choose (i-(a+1)) : ℤ) * ((2*k).choose (k+(a+1)) : ℤ))
          = ∑ a ∈ range i, g a := by
        apply Finset.sum_congr rfl; intro a ha; simp only [Finset.mem_range] at ha
        rw [hg]; simp only []; rw [if_pos (by omega : a+1 ≤ i)]
        by_cases h2 : a+1 ≤ k
        · rw [if_pos h2, choose_symm_shift k (a+1) h2]
        · rw [if_neg h2, Nat.choose_eq_zero_of_lt (by omega : 2*k < k+(a+1))]; ring
      rw [e1]
      apply Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at *; omega)
      intro a _ ha; simp only [Finset.mem_range] at ha
      rw [hg]; simp only []; rw [if_neg (by omega : ¬ (a+1 ≤ i))]; ring
    have hB : (∑ a ∈ range k, ((2*i).choose (i+1+a) : ℤ) * ((2*k).choose (i+k-(i+1+a)) : ℤ))
        = ∑ a ∈ range (i+k), g a := by
      have e1 : (∑ a ∈ range k, ((2*i).choose (i+1+a) : ℤ) * ((2*k).choose (i+k-(i+1+a)) : ℤ))
          = ∑ a ∈ range k, g a := by
        apply Finset.sum_congr rfl; intro a ha; simp only [Finset.mem_range] at ha
        rw [hg]; simp only []
        rw [if_pos (by omega : a+1 ≤ k), show i+k-(i+1+a) = k-(a+1) by omega]
        by_cases h1 : a+1 ≤ i
        · rw [if_pos h1, show i+1+a = i+(a+1) by omega, ← choose_symm_shift i (a+1) h1]
        · rw [if_neg h1, Nat.choose_eq_zero_of_lt (by omega : 2*i < i+1+a)]; ring
      rw [e1]
      apply Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at *; omega)
      intro a _ ha; simp only [Finset.mem_range] at ha
      rw [hg]; simp only []; rw [if_neg (by omega : ¬ (a+1 ≤ k))]; ring
    rw [hA', hB]
    -- constant terms
    have hc0 : (if (0:ℕ) = 0 then (1:ℤ) else 2)
        * (if (0:ℕ) ≤ i then ((2*i).choose (i-0):ℤ) else 0)
        * (if (0:ℕ) ≤ k then ((2*k).choose (k-0):ℤ) else 0)
        = ((2*i).choose (i-0) : ℤ) * ((2*k).choose (k+0) : ℤ) := by
      simp
    -- the RHS sum body for j+1 has factor 2
    have hbody : ∀ j, (if j+1 = 0 then (1:ℤ) else 2)
        * (if j+1 ≤ i then ((2*i).choose (i-(j+1)):ℤ) else 0)
        * (if j+1 ≤ k then ((2*k).choose (k-(j+1)):ℤ) else 0) = 2 * g j := by
      intro j; rw [hg]; simp only []; rw [if_neg (by omega : ¬ (j+1=0))]; ring
    rw [Finset.sum_congr rfl (fun j _ => hbody j), ← Finset.mul_sum, hc0]
    ring
  · -- prove the reflection
    rw [← Finset.sum_range_reflect (fun a => ((2*i).choose a : ℤ) * ((2*k).choose (i+k-a) : ℤ)) (i+1)]
    apply Finset.sum_congr rfl
    intro a ha; simp only [Finset.mem_range] at ha
    rw [show (i+1)-1-a = i-a by omega, show i+k-(i-a) = k+a by omega]

-- ===== Positive definiteness of central-binomial (squared) Hankel =====
open scoped Kronecker

noncomputable def Lm (s : ℕ) : Matrix (Fin s) (Fin s) ℝ :=
  Matrix.of fun i j => if (j:ℕ) ≤ (i:ℕ) then ((2*i.val).choose (i.val-j.val) : ℝ) else 0

noncomputable def Dm (s : ℕ) : Matrix (Fin s) (Fin s) ℝ :=
  Matrix.diagonal fun j => if (j:ℕ) = 0 then (1:ℝ) else 2

noncomputable def Hm (s : ℕ) : Matrix (Fin s) (Fin s) ℝ :=
  Matrix.of fun i k => ((2*(i.val+k.val)).choose (i.val+k.val) : ℝ)

lemma Lm_lower (s : ℕ) : (Lm s).BlockTriangular OrderDual.toDual := by
  intro i j h
  have h' : i < j := OrderDual.toDual_lt_toDual.mp h
  simp only [Lm, Matrix.of_apply]
  rw [if_neg (by have := Fin.lt_iff_val_lt_val.mp h'; omega)]

lemma Lm_det (s : ℕ) : (Lm s).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (Lm_lower s)]
  apply Finset.prod_eq_one
  intro i _; simp [Lm, Nat.choose_self]

lemma Lm_unit (s : ℕ) : IsUnit (Lm s) := by
  rw [Matrix.isUnit_iff_isUnit_det, Lm_det]; exact isUnit_one

lemma Hm_ldl (s : ℕ) : Hm s = Lm s * Dm s * (Lm s)ᵀ := by
  ext i k
  rw [Matrix.mul_apply]
  simp only [Dm, Matrix.mul_diagonal, Matrix.transpose_apply, Hm, Lm, Matrix.of_apply]
  set f : ℕ → ℝ := fun x => (if x ≤ i.val then ((2*i.val).choose (i.val-x):ℝ) else 0)
      * (if x = 0 then (1:ℝ) else 2) * (if x ≤ k.val then ((2*k.val).choose (k.val-x):ℝ) else 0)
      with hf
  rw [Fin.sum_univ_eq_sum_range f s]
  -- ldlKEY over ℝ
  have hR : ((2*(i.val+k.val)).choose (i.val+k.val) : ℝ) = ∑ j ∈ range (i.val+k.val+1), f j := by
    have := ldlKEY i.val k.val
    have h2 : ((2*(i.val+k.val)).choose (i.val+k.val) : ℝ)
        = ∑ j ∈ range (i.val+k.val+1), (if j = 0 then (1:ℝ) else 2)
          * (if j ≤ i.val then ((2*i.val).choose (i.val-j):ℝ) else 0)
          * (if j ≤ k.val then ((2*k.val).choose (k.val-j):ℝ) else 0) := by
      rw [show ((2*(i.val+k.val)).choose (i.val+k.val) : ℝ)
          = (((2*(i.val+k.val)).choose (i.val+k.val) : ℤ) : ℝ) by push_cast; ring, this]
      push_cast
      apply Finset.sum_congr rfl; intro j _
      by_cases h0 : j = 0 <;> by_cases hi : j ≤ i.val <;> by_cases hk : j ≤ k.val <;>
        simp [h0, hi, hk]
    rw [h2]; apply Finset.sum_congr rfl; intro j _; simp only [hf]; ring
  rw [hR]
  -- both range sums equal (f = 0 outside range(min+1))
  have hz : ∀ x, ¬ x < min i.val k.val + 1 → f x = 0 := by
    intro x hx; simp only [hf]
    rcases Nat.lt_or_ge i.val k.val with h | h
    · rw [if_neg (by omega : ¬ x ≤ i.val)]; ring
    · rw [if_neg (by omega : ¬ x ≤ k.val)]; ring
  rw [← Finset.sum_subset (show range (min i.val k.val+1) ⊆ range s by
        intro x hx; simp only [Finset.mem_range] at *; omega)
      (fun x _ hx => hz x (by simpa using hx)),
     ← Finset.sum_subset (show range (min i.val k.val+1) ⊆ range (i.val+k.val+1) by
        intro x hx; simp only [Finset.mem_range] at *; omega)
      (fun x _ hx => hz x (by simpa using hx))]

lemma Hm_posDef (s : ℕ) : (Hm s).PosDef := by
  have hstar : star ((Lm s)ᵀ) = Lm s := by
    ext a b; simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [Hm_ldl, show Lm s * Dm s * (Lm s)ᵀ = star ((Lm s)ᵀ) * Dm s * (Lm s)ᵀ by rw [hstar]]
  rw [(Matrix.isUnit_iff_isUnit_det _).mpr (by rw [Matrix.det_transpose, Lm_det]; exact isUnit_one)
        |>.posDef_star_left_conjugate_iff]
  rw [Dm, Matrix.posDef_diagonal_iff]
  intro j; by_cases h : (j:ℕ) = 0 <;> simp [h]

-- injective submatrix of PosDef is PosDef
lemma posDef_submatrix {N M : Type*} [Fintype N] [Fintype M] [DecidableEq N] [DecidableEq M]
    {A : Matrix N N ℝ} (hA : A.PosDef) {e : M → N} (he : Function.Injective e) :
    (A.submatrix e e).PosDef := by
  set P : Matrix N M ℝ := (fun n m => if n = e m then 1 else 0) with hP
  have hPinj : Function.Injective P.mulVec := by
    intro x y hxy
    funext m
    have h := congrFun hxy (e m)
    simp only [Matrix.mulVec, dotProduct, hP] at h
    rw [Finset.sum_eq_single m, Finset.sum_eq_single m] at h
    · simpa using h
    · intro b _ hb; rw [if_neg (fun hc => hb (he hc).symm), zero_mul]
    · intro hh; exact absurd (Finset.mem_univ m) hh
    · intro b _ hb; rw [if_neg (fun hc => hb (he hc).symm), zero_mul]
    · intro hh; exact absurd (Finset.mem_univ m) hh
  have hEq : A.submatrix e e = Pᴴ * A * P := by
    ext m m'
    rw [Matrix.submatrix_apply, Matrix.mul_apply]
    rw [Finset.sum_eq_single (e m')]
    · rw [Matrix.mul_apply]
      rw [show P (e m') m' = 1 by simp [hP], mul_one]
      rw [Finset.sum_eq_single (e m)]
      · simp [Matrix.conjTranspose_apply, hP]
      · intro b _ hb
        simp only [Matrix.conjTranspose_apply, hP, star_trivial]
        rw [if_neg hb, zero_mul]
      · intro hh; exact absurd (Finset.mem_univ _) hh
    · intro b _ hb
      simp only [hP]; rw [if_neg hb, mul_zero]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  rw [hEq]
  exact hA.conjTranspose_mul_mul_same hPinj

noncomputable def Gmat (s : ℕ) : Matrix (Fin s) (Fin s) ℝ :=
  (Hm s ⊗ₖ Hm s).submatrix (fun i => (i,i)) (fun i => (i,i))

lemma Gmat_apply (s : ℕ) (i k : Fin s) :
    Gmat s i k = ((2*(i.val+k.val)).choose (i.val+k.val) : ℝ)^2 := by
  simp only [Gmat, Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Hm, Matrix.of_apply]
  ring

lemma Gmat_posDef (s : ℕ) : (Gmat s).PosDef :=
  posDef_submatrix ((Hm_posDef s).kronecker (Hm_posDef s))
    (fun a b h => (Prod.ext_iff.mp h).1)

lemma Gmat_det_pos (s : ℕ) : 0 < (Gmat s).det := (Gmat_posDef s).det_pos

-- ===== Shifted central-binomial Hankel (odd block) =====
lemma choose_symm_shift' (i j : ℕ) (h : j ≤ i) :
    (2*i+1).choose (i-j) = (2*i+1).choose (i+1+j) := by
  rw [← Nat.choose_symm (by omega : i+1+j ≤ 2*i+1)]; congr 1; omega

lemma ldlKEY' (i k : ℕ) :
    ((2*(i+k)+2).choose (i+k+1) : ℤ)
    = ∑ j ∈ range (i+k+1), 2 * (if j ≤ i then ((2*i+1).choose (i-j):ℤ) else 0)
        * (if j ≤ k then ((2*k+1).choose (k-j):ℤ) else 0) := by
  set g : ℕ → ℤ := fun a => (if a ≤ i then ((2*i+1).choose (i-a):ℤ) else 0)
      * (if a ≤ k then ((2*k+1).choose (k-a):ℤ) else 0) with hg
  have hv : ((2*(i+k)+2).choose (i+k+1):ℤ)
      = ∑ a ∈ range (i+k+1+1), ((2*i+1).choose a:ℤ)*((2*k+1).choose (i+k+1-a):ℤ) := by
    have := Nat.add_choose_eq (2*i+1) (2*k+1) (i+k+1)
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
    rw [show (2*i+1)+(2*k+1) = 2*(i+k)+2 by ring] at this
    rw [this]; push_cast; rfl
  rw [hv]
  nth_rewrite 1 [show i+k+1+1 = (i+1)+(k+1) by omega]
  rw [Finset.sum_range_add]
  rw [show (∑ a ∈ range (i+1), ((2*i+1).choose a:ℤ)*((2*k+1).choose (i+k+1-a):ℤ))
      = ∑ a ∈ range (i+1), ((2*i+1).choose (i-a):ℤ)*((2*k+1).choose (k+1+a):ℤ) from ?_]
  · have hA : (∑ a ∈ range (i+1), ((2*i+1).choose (i-a):ℤ)*((2*k+1).choose (k+1+a):ℤ))
        = ∑ a ∈ range (i+k+1), g a := by
      have e1 : (∑ a ∈ range (i+1), ((2*i+1).choose (i-a):ℤ)*((2*k+1).choose (k+1+a):ℤ))
          = ∑ a ∈ range (i+1), g a := by
        apply Finset.sum_congr rfl; intro a ha; simp only [Finset.mem_range] at ha
        rw [hg]; simp only []; rw [if_pos (by omega : a ≤ i)]
        by_cases h2 : a ≤ k
        · rw [if_pos h2, choose_symm_shift' k a h2]
        · rw [if_neg h2, Nat.choose_eq_zero_of_lt (by omega : 2*k+1 < k+1+a)]; ring
      rw [e1]
      apply Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at *; omega)
      intro a _ ha; simp only [Finset.mem_range] at ha
      rw [hg]; simp only []; rw [if_neg (by omega : ¬ (a ≤ i))]; ring
    have hB : (∑ a ∈ range (k+1), ((2*i+1).choose (i+1+a):ℤ)*((2*k+1).choose (i+k+1-(i+1+a)):ℤ))
        = ∑ a ∈ range (i+k+1), g a := by
      have e1 : (∑ a ∈ range (k+1), ((2*i+1).choose (i+1+a):ℤ)*((2*k+1).choose (i+k+1-(i+1+a)):ℤ))
          = ∑ a ∈ range (k+1), g a := by
        apply Finset.sum_congr rfl; intro a ha; simp only [Finset.mem_range] at ha
        rw [hg]; simp only []
        rw [if_pos (by omega : a ≤ k), show i+k+1-(i+1+a) = k-a by omega]
        by_cases h1 : a ≤ i
        · rw [if_pos h1, ← choose_symm_shift' i a h1]
        · rw [if_neg h1, Nat.choose_eq_zero_of_lt (by omega : 2*i+1 < i+1+a)]; ring
      rw [e1]
      apply Finset.sum_subset (by intro x hx; simp only [Finset.mem_range] at *; omega)
      intro a _ ha; simp only [Finset.mem_range] at ha
      rw [hg]; simp only []; rw [if_neg (by omega : ¬ (a ≤ k))]; ring
    rw [hA, hB]
    have hbody : ∀ j, 2 * (if j ≤ i then ((2*i+1).choose (i-j):ℤ) else 0)
        * (if j ≤ k then ((2*k+1).choose (k-j):ℤ) else 0) = 2 * g j := by
      intro j; rw [hg]; ring
    rw [Finset.sum_congr rfl (fun j _ => hbody j), ← Finset.mul_sum]; ring
  · rw [← Finset.sum_range_reflect (fun a => ((2*i+1).choose a:ℤ)*((2*k+1).choose (i+k+1-a):ℤ)) (i+1)]
    apply Finset.sum_congr rfl; intro a ha; simp only [Finset.mem_range] at ha
    rw [show (i+1)-1-a = i-a by omega, show i+k+1-(i-a) = k+1+a by omega]

noncomputable def Lm' (t : ℕ) : Matrix (Fin t) (Fin t) ℝ :=
  Matrix.of fun i j => if (j:ℕ) ≤ (i:ℕ) then ((2*i.val+1).choose (i.val-j.val) : ℝ) else 0
noncomputable def Dm' (t : ℕ) : Matrix (Fin t) (Fin t) ℝ := Matrix.diagonal fun _ => (2:ℝ)
noncomputable def Hm' (t : ℕ) : Matrix (Fin t) (Fin t) ℝ :=
  Matrix.of fun i k => ((2*(i.val+k.val)+2).choose (i.val+k.val+1) : ℝ)

lemma Lm'_lower (t : ℕ) : (Lm' t).BlockTriangular OrderDual.toDual := by
  intro i j h
  have h' : i < j := OrderDual.toDual_lt_toDual.mp h
  simp only [Lm', Matrix.of_apply]
  rw [if_neg (by have := Fin.lt_iff_val_lt_val.mp h'; omega)]

lemma Lm'_det (t : ℕ) : (Lm' t).det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ (Lm'_lower t)]
  apply Finset.prod_eq_one; intro i _; simp [Lm', Nat.choose_self]

lemma Hm'_ldl (t : ℕ) : Hm' t = Lm' t * Dm' t * (Lm' t)ᵀ := by
  ext i k
  rw [Matrix.mul_apply]
  simp only [Dm', Matrix.mul_diagonal, Matrix.transpose_apply, Hm', Lm', Matrix.of_apply]
  set f : ℕ → ℝ := fun x => (if x ≤ i.val then ((2*i.val+1).choose (i.val-x):ℝ) else 0)
      * 2 * (if x ≤ k.val then ((2*k.val+1).choose (k.val-x):ℝ) else 0) with hf
  rw [Fin.sum_univ_eq_sum_range f t]
  have hR : ((2*(i.val+k.val)+2).choose (i.val+k.val+1) : ℝ) = ∑ j ∈ range (i.val+k.val+1), f j := by
    have h2 : ((2*(i.val+k.val)+2).choose (i.val+k.val+1) : ℝ)
        = ∑ j ∈ range (i.val+k.val+1), 2 * (if j ≤ i.val then ((2*i.val+1).choose (i.val-j):ℝ) else 0)
          * (if j ≤ k.val then ((2*k.val+1).choose (k.val-j):ℝ) else 0) := by
      rw [show ((2*(i.val+k.val)+2).choose (i.val+k.val+1) : ℝ)
          = (((2*(i.val+k.val)+2).choose (i.val+k.val+1) : ℤ) : ℝ) by push_cast; ring, ldlKEY']
      push_cast
      apply Finset.sum_congr rfl; intro j _
      by_cases hi : j ≤ i.val <;> by_cases hk : j ≤ k.val <;> simp [hi, hk]
    rw [h2]; apply Finset.sum_congr rfl; intro j _; rw [hf]; ring
  rw [hR]
  have hz : ∀ x, ¬ x < min i.val k.val + 1 → f x = 0 := by
    intro x hx; simp only [hf]
    rcases Nat.lt_or_ge i.val k.val with h | h
    · rw [if_neg (by omega : ¬ x ≤ i.val)]; ring
    · rw [if_neg (by omega : ¬ x ≤ k.val)]; ring
  rw [← Finset.sum_subset (show range (min i.val k.val+1) ⊆ range t by
        intro x hx; simp only [Finset.mem_range] at *; omega) (fun x _ hx => hz x (by simpa using hx)),
     ← Finset.sum_subset (show range (min i.val k.val+1) ⊆ range (i.val+k.val+1) by
        intro x hx; simp only [Finset.mem_range] at *; omega) (fun x _ hx => hz x (by simpa using hx))]

lemma Hm'_posDef (t : ℕ) : (Hm' t).PosDef := by
  have hstar : star ((Lm' t)ᵀ) = Lm' t := by
    ext a b; simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [Hm'_ldl, show Lm' t * Dm' t * (Lm' t)ᵀ = star ((Lm' t)ᵀ) * Dm' t * (Lm' t)ᵀ by rw [hstar]]
  rw [(Matrix.isUnit_iff_isUnit_det _).mpr (by rw [Matrix.det_transpose, Lm'_det]; exact isUnit_one)
        |>.posDef_star_left_conjugate_iff]
  rw [Dm', Matrix.posDef_diagonal_iff]; intro j; norm_num

noncomputable def Gmat' (t : ℕ) : Matrix (Fin t) (Fin t) ℝ :=
  (Hm' t ⊗ₖ Hm' t).submatrix (fun i => (i,i)) (fun i => (i,i))

lemma Gmat'_apply (t : ℕ) (i k : Fin t) :
    Gmat' t i k = ((2*(i.val+k.val)+2).choose (i.val+k.val+1) : ℝ)^2 := by
  simp only [Gmat', Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Hm', Matrix.of_apply]; ring

lemma Gmat'_det_pos (t : ℕ) : 0 < (Gmat' t).det :=
  (posDef_submatrix ((Hm'_posDef t).kronecker (Hm'_posDef t))
    (fun a b h => (Prod.ext_iff.mp h).1)).det_pos

-- ===== Parity block decomposition of det Cmat =====
lemma Cmat_blockTri (n : ℕ) : (Cmat n).BlockTriangular (fun i => i.val % 2) := by
  intro i j h
  dsimp only at h
  simp only [Cmat, Matrix.of_apply, cmom]
  have hne : ¬ Even (i.val + j.val) := by
    rw [Nat.not_even_iff]; omega
  rw [if_neg hne]

-- even reindex equiv
private lemma e0aux1 (n p : ℕ) (h : p < n/2+1) : 2*p < n+1 := by omega
private lemma e0aux2 (n x : ℕ) (h : x < n+1) : x/2 < n/2+1 := by omega
private lemma emod2 (p : ℕ) : (2*p) % 2 = 0 := by omega
private lemma e1aux1 (n q : ℕ) (h : q < (n+1)/2) : 2*q+1 < n+1 := by omega
private lemma e1aux2 (n x : ℕ) (h : x < n+1) (h2 : x%2=1) : x/2 < (n+1)/2 := by omega
private lemma omod2 (q : ℕ) : (2*q+1) % 2 = 1 := by omega

def e0 (n : ℕ) : Fin (n/2+1) ≃ {i : Fin (n+1) // i.val % 2 = 0} where
  toFun p := ⟨⟨2*p.val, e0aux1 n p.val p.isLt⟩, emod2 p.val⟩
  invFun i := ⟨i.val.val/2, e0aux2 n i.val.val i.val.isLt⟩
  left_inv p := by apply Fin.ext; show 2*p.val/2 = p.val; omega
  right_inv i := by
    apply Subtype.ext; apply Fin.ext; show 2*(i.val.val/2) = i.val.val
    have h2 := i.property; omega
  
def e1 (n : ℕ) : Fin ((n+1)/2) ≃ {i : Fin (n+1) // i.val % 2 = 1} where
  toFun q := ⟨⟨2*q.val+1, e1aux1 n q.val q.isLt⟩, omod2 q.val⟩
  invFun i := ⟨i.val.val/2, e1aux2 n i.val.val i.val.isLt i.property⟩
  left_inv q := by apply Fin.ext; show (2*q.val+1)/2 = q.val; omega
  right_inv i := by
    apply Subtype.ext; apply Fin.ext; show 2*(i.val.val/2)+1 = i.val.val
    have h2 := i.property; omega

-- even block determinant positive
lemma even_block_pos (n : ℕ) :
    0 < ((Cmat n).toSquareBlock (fun i => i.val % 2) 0).det := by
  rw [← Matrix.det_submatrix_equiv_self (e0 n)]
  set E : Matrix (Fin (n/2+1)) (Fin (n/2+1)) ℤ :=
    ((Cmat n).toSquareBlock (fun i => i.val % 2) 0).submatrix (e0 n) (e0 n) with hE
  have hEval : ∀ p q, E p q = cmom (2*p.val + 2*q.val) := by
    intro p q
    simp only [hE, Matrix.submatrix_apply, Matrix.toSquareBlock_def, Cmat, Matrix.of_apply, e0,
      Equiv.coe_fn_mk, Fin.val_mk]
  -- cast to ℝ, show = D_E Gmat D_E
  have hpos : 0 < ((E.det : ℤ) : ℝ) := by
    rw [show ((E.det:ℤ):ℝ) = (Int.castRingHom ℝ) E.det from rfl, (Int.castRingHom ℝ).map_det,
      RingHom.mapMatrix_apply]
    set d : Fin (n/2+1) → ℝ := fun p => (4:ℝ)^p.val with hd
    have hmap : E.map (Int.castRingHom ℝ)
        = Matrix.diagonal d * Gmat (n/2+1) * Matrix.diagonal d := by
      ext p q
      rw [Matrix.map_apply, hEval, Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Gmat_apply, show 2*p.val+2*q.val = 2*(p.val+q.val) by ring, cmom,
        if_pos ⟨p.val+q.val, by ring⟩, Int.coe_castRingHom]
      push_cast
      rw [show (2*(p.val+q.val))/2 = p.val+q.val by omega, hd,
        show (4:ℝ)^(p.val+q.val) = (4:ℝ)^p.val*(4:ℝ)^q.val from pow_add 4 p.val q.val]
      ring
    rw [hmap, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hp : (0:ℝ) < ∏ p : Fin (n/2+1), d p := Finset.prod_pos (fun i _ => by rw [hd]; positivity)
    have := Gmat_det_pos (n/2+1)
    exact mul_pos (mul_pos hp this) hp
  have : 0 < (E.det : ℝ) := by exact_mod_cast hpos
  exact_mod_cast this

-- odd block determinant positive
lemma odd_block_pos (n : ℕ) :
    0 < ((Cmat n).toSquareBlock (fun i => i.val % 2) 1).det := by
  rw [← Matrix.det_submatrix_equiv_self (e1 n)]
  set O : Matrix (Fin ((n+1)/2)) (Fin ((n+1)/2)) ℤ :=
    ((Cmat n).toSquareBlock (fun i => i.val % 2) 1).submatrix (e1 n) (e1 n) with hO
  have hOval : ∀ p q, O p q = cmom (2*p.val+1 + (2*q.val+1)) := by
    intro p q
    simp only [hO, Matrix.submatrix_apply, Matrix.toSquareBlock_def, Cmat, Matrix.of_apply, e1,
      Equiv.coe_fn_mk, Fin.val_mk]
  have hpos : 0 < ((O.det : ℤ) : ℝ) := by
    rw [show ((O.det:ℤ):ℝ) = (Int.castRingHom ℝ) O.det from rfl, (Int.castRingHom ℝ).map_det,
      RingHom.mapMatrix_apply]
    set d : Fin ((n+1)/2) → ℝ := fun p => 2*(4:ℝ)^p.val with hd
    have hmap : O.map (Int.castRingHom ℝ)
        = Matrix.diagonal d * Gmat' ((n+1)/2) * Matrix.diagonal d := by
      ext p q
      rw [Matrix.map_apply, hOval, Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Gmat'_apply, show 2*p.val+1+(2*q.val+1) = 2*(p.val+q.val+1) by ring, cmom,
        if_pos ⟨p.val+q.val+1, by ring⟩, Int.coe_castRingHom]
      push_cast
      rw [show (2*(p.val+q.val+1))/2 = p.val+q.val+1 by omega,
        show 2*(p.val+q.val+1) = 2*(p.val+q.val)+2 by ring, hd]
      ring
    rw [hmap, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    have hp : (0:ℝ) < ∏ p : Fin ((n+1)/2), d p := Finset.prod_pos (fun i _ => by rw [hd]; positivity)
    have := Gmat'_det_pos ((n+1)/2)
    exact mul_pos (mul_pos hp this) hp
  have : 0 < (O.det : ℝ) := by exact_mod_cast hpos
  exact_mod_cast this

lemma detCmat_pos (n : ℕ) : 0 < (Cmat n).det := by
  rw [(Cmat_blockTri n).det]
  apply Finset.prod_pos
  intro a ha
  simp only [Finset.mem_image] at ha
  obtain ⟨j, _, rfl⟩ := ha
  rcases (by omega : j.val % 2 = 0 ∨ j.val % 2 = 1) with h | h
  · rw [h]; exact even_block_pos n
  · rw [h]; exact odd_block_pos n

lemma detPP_pos (n : ℕ) : 0 < (PP n).det := by
  rw [detPP]; exact detCmat_pos n

-- ===== centralBinom 2-adic =====
open Nat
noncomputable def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

lemma sum_digits_two_mul (m : ℕ) : (Nat.digits 2 (2*m)).sum = (Nat.digits 2 m).sum := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp
  · rw [Nat.digits_def' (by norm_num : 2 ≤ 2) (by omega)]
    simp [Nat.mul_div_cancel_left, Nat.mul_mod_right]

lemma padicVal_centralBinom (m : ℕ) : padicValNat 2 ((2*m).choose m) = s2 m := by
  haveI h : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have H := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := m) (n := 2*m) (by omega)
  rw [show 2*m - m = m by omega, sum_digits_two_mul] at H
  simp only [s2]
  omega

-- ===== matching lemmas =====

def IsMatch (r e : ℕ) (f : ℕ → ℕ) : Prop :=
  Set.BijOn f (Set.Icc 1 r) (Set.Icc 1 r) ∧ (∀ x, 1 ≤ x → x ≤ r → ∃ k, x + f x = 2^k + e)

-- top forcing: for x ≥ 2^(K-1)+e, f x = 2^K + e - x
lemma top_force (r e K : ℕ) (he : e ≤ 1) (hK : 1 ≤ K) (hK1 : r < 2^K + e) (hK2 : 2^K + e ≤ 2*r)
    (f : ℕ → ℕ) (hf : IsMatch r e f)
    (x : ℕ) (hx1 : 2^(K-1) + e ≤ x) (hx2 : x ≤ r) : f x = 2^K + e - x := by
  have hx0 : 1 ≤ x := by have h1 : 1 ≤ 2^(K-1) := Nat.one_le_two_pow; omega
  obtain ⟨hbij, hp⟩ := hf
  have hmem : f x ∈ Set.Icc 1 r := hbij.mapsTo ⟨hx0, hx2⟩
  obtain ⟨k, hk⟩ := hp x hx0 hx2
  have hf1 : 1 ≤ f x := hmem.1
  have hf2 : f x ≤ r := hmem.2
  have hhalf : 2*2^(K-1) = 2^K := by
    have : 2^K = 2^(K-1+1) := by congr 1; omega
    rw [this, pow_succ]; ring
  have hlow : K ≤ k := by
    by_contra h; push_neg at h
    have : 2^k ≤ 2^(K-1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hhigh : k ≤ K := by
    by_contra h; push_neg at h
    have h3 : 2^(K+1) ≤ 2^k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2^(K+1) = 2*2^K := by rw [pow_succ]; ring
    omega
  have : k = K := le_antisymm hhigh hlow
  subst this; omega

lemma inv_match (r e : ℕ) (f : ℕ → ℕ) (hf : IsMatch r e f) :
    IsMatch r e (Function.invFunOn f (Set.Icc 1 r)) := by
  obtain ⟨hbij, hp⟩ := hf
  set S := Set.Icc 1 r
  set g := Function.invFunOn f S with hg
  have hinv : Set.InvOn g f S S := hbij.invOn_invFunOn
  have hfmaps : Set.MapsTo f S S := hbij.mapsTo
  have hgmaps : Set.MapsTo g S S := fun y hy => Function.invFunOn_mem (hbij.surjOn hy)
  have hgb : Set.BijOn g S S := hinv.symm.bijOn hgmaps hfmaps
  refine ⟨hgb, ?_⟩
  intro y hy1 hy2
  have hyS : y ∈ S := ⟨hy1, hy2⟩
  have hgyS : g y ∈ S := hgb.mapsTo hyS
  have hfg : f (g y) = y := hinv.2 hyS
  obtain ⟨k, hk⟩ := hp (g y) hgyS.1 hgyS.2
  exact ⟨k, by rw [hfg] at hk; omega⟩

-- block forcing on [2^K + e - r, r]
lemma block_force (r e K : ℕ) (he : e ≤ 1) (hK : 1 ≤ K) (hK1 : r < 2^K + e) (hK2 : 2^K + e ≤ 2*r)
    (f : ℕ → ℕ) (hf : IsMatch r e f)
    (x : ℕ) (hx1 : 2^K + e - r ≤ x) (hx2 : x ≤ r) : f x = 2^K + e - x := by
  have hhalf : 2*2^(K-1) = 2^K := by
    have : 2^K = 2^(K-1+1) := by congr 1; omega
    rw [this, pow_succ]; ring
  by_cases hc : 2^(K-1) + e ≤ x
  · exact top_force r e K he hK hK1 hK2 f hf x hc hx2
  · push_neg at hc
    set g := Function.invFunOn f (Set.Icc 1 r) with hg
    have hgm := inv_match r e f hf
    obtain ⟨hbij, hp⟩ := hf
    have hinv : Set.InvOn g f (Set.Icc 1 r) (Set.Icc 1 r) := hbij.invOn_invFunOn
    set y := 2^K + e - x with hy
    have hy1 : 2^(K-1) + e ≤ y := by omega
    have hy2 : y ≤ r := by omega
    have hgy : g y = 2^K + e - y := top_force r e K he hK hK1 hK2 g hgm y hy1 hy2
    have hxeq : 2^K + e - y = x := by omega
    rw [hxeq] at hgy
    have hyS : y ∈ Set.Icc 1 r := ⟨by omega, hy2⟩
    have hfg : f (g y) = y := hinv.2 hyS
    rw [hgy] at hfg
    rw [hfg, hy]

lemma lower_match (r e K : ℕ) (he : e ≤ 1) (hK : 1 ≤ K) (hK1 : r < 2^K + e) (hK2 : 2^K + e ≤ 2*r)
    (f : ℕ → ℕ) (hf : IsMatch r e f) : IsMatch (2^K + e - r - 1) e f := by
  set r' := 2^K + e - r - 1 with hr'def
  have hr'r : r' < r := by omega
  have hbf := block_force r e K he hK hK1 hK2 f hf
  obtain ⟨hbij, hp⟩ := hf
  have hnotblock : ∀ x, 1 ≤ x → x ≤ r' → f x ≤ r' := by
    intro x hx1 hx2
    by_contra h; push_neg at h
    have hfxr : f x ≤ r := (hbij.mapsTo ⟨hx1, le_trans hx2 hr'r.le⟩).2
    have hfx1 : 1 ≤ f x := (hbij.mapsTo ⟨hx1, le_trans hx2 hr'r.le⟩).1
    set w := 2^K + e - f x with hw
    have hw1 : 2^K + e - r ≤ w := by omega
    have hw2 : w ≤ r := by omega
    have hfw : f w = 2^K + e - w := hbf w hw1 hw2
    have hcalc : 2^K + e - w = f x := by omega
    rw [hcalc] at hfw
    have hwS : w ∈ Set.Icc 1 r := ⟨by omega, hw2⟩
    have hxS : x ∈ Set.Icc 1 r := ⟨hx1, le_trans hx2 hr'r.le⟩
    have := hbij.injOn hwS hxS hfw
    omega
  refine ⟨⟨fun x hx => ⟨(hbij.mapsTo ⟨hx.1, le_trans hx.2 hr'r.le⟩).1, hnotblock x hx.1 hx.2⟩,
      fun a ha b hb => hbij.injOn ⟨ha.1, le_trans ha.2 hr'r.le⟩ ⟨hb.1, le_trans hb.2 hr'r.le⟩, ?_⟩,
    fun x hx1 hx2 => hp x hx1 (le_trans hx2 hr'r.le)⟩
  intro y hy
  rw [Set.mem_Icc] at hy
  have hyIcc : y ∈ Set.Icc 1 r := ⟨hy.1, le_trans hy.2 hr'r.le⟩
  obtain ⟨x, hxS, hfx⟩ := hbij.surjOn hyIcc
  refine ⟨x, ⟨hxS.1, ?_⟩, hfx⟩
  by_contra h; push_neg at h
  have hbfx := hbf x (by omega) hxS.2
  rw [hfx] at hbfx
  have hyr' : y ≤ r' := hy.2
  have hxr : x ≤ r := hxS.2
  omega

-- unique power of 2 in range [r+1-e, 2r-e]
lemma pow_uniq (r e a b : ℕ) (he : e ≤ 1) (ha1 : r < 2^a + e) (ha2 : 2^a + e ≤ 2*r)
    (hb1 : r < 2^b + e) (hb2 : 2^b + e ≤ 2*r) : a = b := by
  rcases le_total a b with h | h
  · have h1 : 2^(a+1) = 2*2^a := by rw [pow_succ]; ring
    have hlt : 2^b < 2^(a+1) := by omega
    have : b < a+1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  · have h1 : 2^(b+1) = 2*2^b := by rw [pow_succ]; ring
    have hlt : 2^a < 2^(b+1) := by omega
    have : a < b+1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega

lemma pow_ex (r e : ℕ) (he : e ≤ 1) (hr : 2 ≤ r) :
    ∃ K, 1 ≤ K ∧ r < 2^K + e ∧ 2^K + e ≤ 2*r := by
  rcases Nat.eq_zero_or_pos e with he0 | hepos
  · subst he0
    refine ⟨Nat.log 2 r + 1, by omega, ?_, ?_⟩
    · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) r; omega
    · have := Nat.pow_log_le_self 2 (by omega : r ≠ 0); rw [pow_succ]; omega
  · have he1 : e = 1 := by omega
    subst he1
    refine ⟨Nat.clog 2 r, Nat.clog_pos (by norm_num) (by omega), ?_, ?_⟩
    · have := Nat.le_pow_clog (by norm_num : 1 < 2) r; omega
    · have hc : 1 ≤ Nat.clog 2 r := Nat.clog_pos (by norm_num) (by omega)
      set A := 2^(Nat.clog 2 r) with hA
      set B := 2^(Nat.clog 2 r - 1) with hB
      have h1 : B < r := by rw [hB]; exact Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (show 1 < r by omega)
      have h2 : A = 2*B := by rw [hA, hB, ← pow_succ']; congr 1; omega
      omega

lemma match_unique (e : ℕ) (he : e ≤ 1) : ∀ r, ∀ f g, IsMatch r e f → IsMatch r e g →
    ∀ x, 1 ≤ x → x ≤ r → f x = g x := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro f g hf hg x hx1 hx2
    have hr1 : 1 ≤ r := le_trans hx1 hx2
    rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · have hr : r = 1 := by omega
      subst hr
      obtain ⟨hbf, _⟩ := hf; obtain ⟨hbg, _⟩ := hg
      have hfx : f 1 ∈ Set.Icc 1 1 := hbf.mapsTo ⟨le_refl _, le_refl _⟩
      have hgx : g 1 ∈ Set.Icc 1 1 := hbg.mapsTo ⟨le_refl _, le_refl _⟩
      have hx : x = 1 := by omega
      subst hx
      have h1 : f 1 = 1 := by have := hfx.2; have := hfx.1; omega
      rw [h1]; have := hgx.2; have := hgx.1; omega
    · obtain ⟨hbf, hpf⟩ := hf
      obtain ⟨kf, hkf⟩ := hpf r (by omega) (le_refl r)
      have hfr : f r ∈ Set.Icc 1 r := hbf.mapsTo ⟨by omega, le_refl r⟩
      set K := kf with hKdef
      have hK1 : r < 2^K + e := by have := hfr.1; omega
      have hK2 : 2^K + e ≤ 2*r := by have := hfr.2; omega
      have hK : 1 ≤ K := by
        rcases Nat.eq_zero_or_pos K with h | h
        · exfalso; rw [h] at hK1 hK2; simp only [pow_zero] at hK1 hK2; omega
        · exact h
      by_cases hb : 2^K + e - r ≤ x
      · rw [block_force r e K he hK hK1 hK2 f ⟨hbf,hpf⟩ x hb hx2,
            block_force r e K he hK hK1 hK2 g hg x hb hx2]
      · push_neg at hb
        have hfl := lower_match r e K he hK hK1 hK2 f ⟨hbf,hpf⟩
        have hgl := lower_match r e K he hK hK1 hK2 g hg
        have hr' : 2^K + e - r - 1 < r := by omega
        exact ih (2^K + e - r - 1) hr' f g hfl hgl x hx1 (by omega)

lemma match_exists (e : ℕ) (he : e ≤ 1) : ∀ r, ∃ f, IsMatch r e f := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · rcases Nat.lt_or_ge r 1 with hr0 | hr1
      · have : r = 0 := by omega
        subst this
        have hemp : Set.Icc 1 0 = (∅ : Set ℕ) := Set.Icc_eq_empty (by omega)
        exact ⟨fun _ => 0, by rw [hemp]; exact Set.bijOn_empty _, fun x hx1 hx2 => by omega⟩
      · have hr : r = 1 := by omega
        subst hr
        refine ⟨fun _ => 1, ⟨fun x _ => Set.mem_Icc.mpr ⟨le_refl 1, le_refl 1⟩,
          fun a ha b hb _ => by rw [Set.mem_Icc] at ha hb; omega,
          fun y hy => ⟨1, Set.mem_Icc.mpr ⟨le_refl 1, le_refl 1⟩,
            by rw [Set.mem_Icc] at hy; show (1:ℕ) = y; omega⟩⟩, ?_⟩
        intro x hx1 hx2
        have hx : x = 1 := by omega
        subst hx
        refine ⟨1 - e, ?_⟩
        interval_cases e <;> rfl
    · obtain ⟨K, hK, hK1, hK2⟩ := pow_ex r e he hr2
      set r' := 2^K + e - r - 1 with hr'def
      have hr'r : r' < r := by omega
      obtain ⟨h, hh⟩ := ih r' hr'r
      obtain ⟨hhbij, hhp⟩ := hh
      refine ⟨fun x => if 2^K + e - r ≤ x ∧ x ≤ r then 2^K + e - x else h x, ?_, ?_⟩
      · constructor
        · intro x hx
          rw [Set.mem_Icc] at hx ⊢; dsimp only
          by_cases hb : 2^K + e - r ≤ x ∧ x ≤ r
          · rw [if_pos hb]; omega
          · rw [if_neg hb]
            have := hhbij.mapsTo ⟨hx.1, (by omega : x ≤ r')⟩
            rw [Set.mem_Icc] at this; omega
        · refine ⟨?_, ?_⟩
          · intro a ha b hb hab
            rw [Set.mem_Icc] at ha hb; dsimp only at hab
            by_cases hba : 2^K + e - r ≤ a ∧ a ≤ r <;> by_cases hbb : 2^K + e - r ≤ b ∧ b ≤ r
            · rw [if_pos hba, if_pos hbb] at hab; omega
            · exfalso; rw [if_pos hba, if_neg hbb] at hab
              have := hhbij.mapsTo ⟨hb.1, (by omega : b ≤ r')⟩; rw [Set.mem_Icc] at this; omega
            · exfalso; rw [if_neg hba, if_pos hbb] at hab
              have := hhbij.mapsTo ⟨ha.1, (by omega : a ≤ r')⟩; rw [Set.mem_Icc] at this; omega
            · rw [if_neg hba, if_neg hbb] at hab
              exact hhbij.injOn ⟨ha.1, by omega⟩ ⟨hb.1, by omega⟩ hab
          · intro y hy
            rw [Set.mem_Icc] at hy
            by_cases hyb : 2^K + e - r ≤ y
            · refine ⟨2^K + e - y, by rw [Set.mem_Icc]; omega, ?_⟩
              dsimp only; rw [if_pos ⟨by omega, by omega⟩]; omega
            · have hyIcc : y ∈ Set.Icc 1 r' := Set.mem_Icc.mpr ⟨hy.1, by omega⟩
              obtain ⟨x, hxmem, hfx⟩ := hhbij.surjOn hyIcc
              rw [Set.mem_Icc] at hxmem
              refine ⟨x, Set.mem_Icc.mpr ⟨hxmem.1, by omega⟩, ?_⟩
              dsimp only; rw [if_neg (by omega : ¬(2^K + e - r ≤ x ∧ x ≤ r))]; exact hfx
      · intro x hx1 hx2
        dsimp only
        by_cases hb : 2^K + e - r ≤ x ∧ x ≤ r
        · rw [if_pos hb]; exact ⟨K, by omega⟩
        · rw [if_neg hb]; exact hhp x hx1 (by omega)

lemma centralBinom_factor (m : ℕ) : ∃ u : ℤ, Odd u ∧ ((2*m).choose m : ℤ) = 2^(s2 m) * u := by
  have hv : padicValNat 2 ((2*m).choose m) = s2 m := padicVal_centralBinom m
  set C := (2*m).choose m with hC
  have hdvd : 2^(s2 m) ∣ C := hv ▸ pow_padicValNat_dvd
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨(q:ℤ), ?_, by rw [hq]; push_cast; ring⟩
  rw [Int.odd_coe_nat, Nat.odd_iff]
  by_contra h
  replace h : q % 2 = 0 := by omega
  have h2 : 2^(s2 m + 1) ∣ C := by
    rw [hq]; obtain ⟨k, hk⟩ := (Nat.even_iff.mpr h); exact ⟨k, by rw [hk]; ring⟩
  exact (hv ▸ pow_succ_padicValNat_not_dvd (n := C) (p := 2) (by have := Nat.choose_pos (n:=2*m) (k:=m) (by omega); omega)) h2

lemma odd_sum_of_unique {I : Type*} [Fintype I] [DecidableEq I] (c : I → ℤ) (m : ℕ) (i0 : I)
    (hmain : ∃ u : ℤ, Odd u ∧ c i0 = 2^m * u)
    (hrest : ∀ i, i ≠ i0 → (2^(m+1) : ℤ) ∣ c i) :
    ∃ u : ℤ, Odd u ∧ (∑ i, c i) = 2^m * u := by
  obtain ⟨u0, hu0, hc0⟩ := hmain
  have hsplit : (∑ i, c i) = c i0 + ∑ i ∈ Finset.univ.erase i0, c i :=
    (Finset.add_sum_erase _ c (Finset.mem_univ i0)).symm
  have hdvd : (2^(m+1) : ℤ) ∣ ∑ i ∈ Finset.univ.erase i0, c i :=
    Finset.dvd_sum (fun i hi => hrest i (Finset.ne_of_mem_erase hi))
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨u0 + 2*k, ?_, ?_⟩
  · rcases hu0 with ⟨t, ht⟩; exact ⟨t + k, by rw [ht]; ring⟩
  · rw [hsplit, hc0, hk]; ring

lemma s2_two_mul (m : ℕ) : s2 (2*m) = s2 m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp [s2]
  · simp only [s2, Nat.digits_def' (by norm_num : 2 ≤ 2) (by omega : 0 < 2*m)]
    simp [Nat.mul_div_cancel_left, Nat.mul_mod_right]

lemma s2_pow2 (k : ℕ) : s2 (2^k) = 1 := by
  induction k with
  | zero => simp [s2]
  | succ n ih => rw [pow_succ, mul_comm, s2_two_mul]; exact ih

lemma s2_pos (m : ℕ) (h : 1 ≤ m) : 1 ≤ s2 m := by
  have hne : Nat.digits 2 m ≠ [] := by rw [Nat.digits_ne_nil_iff_ne_zero]; omega
  have hlast : (Nat.digits 2 m).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 2 (by omega)
  have hle := List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.getLast_mem hne)
  simp only [s2]; omega

lemma s2_eq_one_of (m : ℕ) (h : s2 m = 1) : ∃ k, m = 2^k := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hm : m ≠ 0 := by rintro rfl; simp [s2] at h
    have hd : s2 m = m % 2 + s2 (m / 2) := by
      simp only [s2, Nat.digits_def' (by norm_num : 2 ≤ 2) (by omega : 0 < m)]; simp
    rcases Nat.lt_or_ge (m % 2) 1 with hb | hb
    · have hb0 : m % 2 = 0 := by omega
      have : s2 (m/2) = 1 := by omega
      obtain ⟨j, hj⟩ := ih (m/2) (by omega) this
      exact ⟨j+1, by rw [pow_succ, mul_comm, ← hj]; omega⟩
    · have hb1 : m % 2 = 1 := by omega
      have hs0 : s2 (m/2) = 0 := by omega
      have hz : m / 2 = 0 := by
        by_contra hc
        have hne : Nat.digits 2 (m/2) ≠ [] := by rw [Nat.digits_ne_nil_iff_ne_zero]; omega
        have hlast : (Nat.digits 2 (m/2)).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 2 hc
        have hle := List.single_le_sum (fun x _ => Nat.zero_le x) _ (List.getLast_mem hne)
        simp only [s2] at hs0; omega
      exact ⟨0, by rw [pow_zero]; omega⟩

lemma g_lower (s d : ℕ) (σ : Equiv.Perm (Fin s)) :
    s - 1 ≤ ∑ i : Fin s, s2 ((σ i).val + i.val + d) := by
  have hterm : ∀ i : Fin s, (if (σ i).val + i.val + d = 0 then 0 else 1) ≤ s2 ((σ i).val + i.val + d) := by
    intro i; by_cases h : (σ i).val + i.val + d = 0
    · simp [h]
    · rw [if_neg h]; exact s2_pos _ (by omega)
  have h1 : (∑ i : Fin s, (if (σ i).val + i.val + d = 0 then 0 else 1)) ≤ ∑ i, s2 ((σ i).val + i.val + d) :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have hcard : (Finset.univ.filter (fun i : Fin s => (σ i).val + i.val + d = 0)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact Fin.ext (by omega)
  have hsplit : (∑ i : Fin s, (if (σ i).val+i.val+d = 0 then (0:ℕ) else 1))
      + (Finset.univ.filter (fun i:Fin s => (σ i).val+i.val+d=0)).card = s := by
    have hpt : ∀ i:Fin s, (if (σ i).val+i.val+d=0 then (0:ℕ) else 1)
        + (if (σ i).val+i.val+d=0 then 1 else 0) = 1 := by intro i; split_ifs <;> rfl
    rw [Finset.card_filter, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun i _ => hpt i)]
    simp
  omega

lemma cmom_even_factor (m : ℕ) : ∃ u : ℤ, Odd u ∧ cmom (2*m) = 2^(2*m + 2*s2 m) * u := by
  obtain ⟨u, hu, hcu⟩ := centralBinom_factor m
  refine ⟨u^2, hu.pow, ?_⟩
  rw [cmom, if_pos ⟨m, by ring⟩, show (2*m)/2 = m by omega, hcu, mul_pow, ← pow_mul,
      show (4:ℤ) = 2^2 by norm_num, ← pow_mul, ← mul_assoc, ← pow_add,
      show 2*m + s2 m*2 = 2*m + 2*s2 m by ring]

lemma prod_val (s d : ℕ) (σ : Equiv.Perm (Fin s)) :
    ∃ u : ℤ, Odd u ∧ (∏ i : Fin s, cmom (2*((σ i).val + i.val + d)))
      = 2^(∑ i : Fin s, (2*((σ i).val + i.val + d) + 2*s2 ((σ i).val + i.val + d))) * u := by
  have h : ∀ i : Fin s, ∃ u : ℤ, Odd u ∧
      cmom (2*((σ i).val + i.val + d)) = 2^(2*((σ i).val+i.val+d) + 2*s2 ((σ i).val+i.val+d)) * u :=
    fun i => cmom_even_factor _
  choose u hu heq using h
  refine ⟨∏ i, u i, ?_, ?_⟩
  · exact Finset.prod_induction _ Odd (fun a b => Odd.mul) odd_one (fun i _ => hu i)
  · rw [Finset.prod_congr rfl (fun i _ => heq i), Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]
