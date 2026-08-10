import FormalConjectures.Util.ProblemImports

open Polynomial Nat Finset

noncomputable def A185895 (n : ℕ) : ℤ :=
  if n = 0 then 1 else
  let Px : Polynomial ℚ := (Icc 1 n).prod (fun k : ℕ =>
    (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)
  let coeff_n : ℚ := Polynomial.coeff Px n
  let a_n_q : ℚ := coeff_n * n.factorial.cast
  a_n_q.floor

-- Step 1: expand the product coefficient as a subset sum.
-- ∏_{k∈Icc 1 n} (1 - C(1/k!) X^k) = ∑_{t ⊆ Icc 1 n} ∏_{k∈t} (-(C(1/k!) X^k))

example (n : ℕ) :
    ((Icc 1 n).prod (fun k : ℕ =>
      (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k))
    = ∑ t ∈ (Icc 1 n).powerset, ∏ k ∈ t, (-(C ((1:ℚ)/k.factorial.cast) * X ^ k)) := by
  have : ∀ k : ℕ, (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k
      = (-(C ((1:ℚ)/k.factorial.cast) * X ^ k)) + 1 := by intro k; ring
  simp_rw [this]
  rw [Finset.prod_add]
  simp

-- Each term is a monomial: ∏_{k∈t}(-(C(1/k!)X^k)) = C((-1)^|t| ∏1/k!) X^{∑t}
example (t : Finset ℕ) :
    ∏ k ∈ t, (-(C ((1:ℚ)/k.factorial.cast) * X ^ k))
    = C ((-1)^t.card * ∏ k ∈ t, ((1:ℚ)/k.factorial.cast)) * X ^ (∑ k ∈ t, k) := by
  rw [Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [map_mul, map_pow, map_neg, map_one, map_prod]
  ring

noncomputable def Sterm (t : Finset ℕ) : ℤ := (-1)^t.card * (Nat.multinomial t id : ℤ)

noncomputable def S (n : ℕ) : ℤ :=
  ∑ t ∈ (Icc 1 n).powerset.filter (fun t => ∑ k ∈ t, k = n), Sterm t

-- multinomial as rational: n! * ∏ 1/k! = multinomial, when ∑ t = n
lemma multinom_rat (t : Finset ℕ) (n : ℕ) (h : ∑ k ∈ t, k = n) :
    (n.factorial : ℚ) * ∏ k ∈ t, ((1:ℚ)/k.factorial.cast) = (Nat.multinomial t id : ℚ) := by
  have hspec := Nat.multinomial_spec t id
  simp only [id] at hspec ⊢
  rw [h] at hspec
  have hprod : (0:ℚ) < ∏ k ∈ t, (k.factorial : ℚ) := by
    apply Finset.prod_pos; intro k _; exact_mod_cast Nat.factorial_pos k
  rw [Finset.prod_div_distrib, Finset.prod_const_one]
  field_simp
  rw [← hspec]
  push_cast
  ring

-- coeff n of Px as a subset sum
lemma coeff_expand (n : ℕ) :
    Polynomial.coeff ((Icc 1 n).prod (fun k : ℕ =>
      (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)) n
    = ∑ t ∈ (Icc 1 n).powerset,
        ((-1)^t.card * ∏ k ∈ t, ((1:ℚ)/k.factorial.cast)) * (if n = ∑ k ∈ t, k then 1 else 0) := by
  have h1 : ((Icc 1 n).prod (fun k : ℕ =>
      (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k))
    = ∑ t ∈ (Icc 1 n).powerset, ∏ k ∈ t, (-(C ((1:ℚ)/k.factorial.cast) * X ^ k)) := by
    have : ∀ k : ℕ, (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k
        = (-(C ((1:ℚ)/k.factorial.cast) * X ^ k)) + 1 := by intro k; ring
    simp_rw [this]; rw [Finset.prod_add]; simp
  rw [h1, Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro t ht
  have h2 : ∏ k ∈ t, (-(C ((1:ℚ)/k.factorial.cast) * X ^ k))
    = C ((-1)^t.card * ∏ k ∈ t, ((1:ℚ)/k.factorial.cast)) * X ^ (∑ k ∈ t, k) := by
    rw [Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    simp only [map_mul, map_pow, map_neg, map_one, map_prod]; ring
  rw [h2, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

-- coeff_n * n! equals S n (as rationals)
lemma coeffn_mul_fact (n : ℕ) :
    (Polynomial.coeff ((Icc 1 n).prod (fun k : ℕ =>
      (1 : Polynomial ℚ) - C ((1 : ℚ) / k.factorial.cast) * X ^ k)) n) * n.factorial
    = (S n : ℚ) := by
  rw [coeff_expand, Finset.sum_mul]
  have hS : (S n : ℚ)
      = ∑ t ∈ (Icc 1 n).powerset, (if n = ∑ k ∈ t, k then (Sterm t : ℚ) else 0) := by
    rw [S]
    push_cast
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases h : ∑ k ∈ t, k = n
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun hh => h hh.symm)]
  rw [hS]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases h : n = ∑ k ∈ t, k
  · simp only [if_pos h]
    have := multinom_rat t n h.symm
    rw [Sterm]
    push_cast
    rw [← this]
    ring
  · simp only [if_neg h]; ring

-- M_r(n): number-weighted count of r-block distinct-size set partitions of [n]
noncomputable def Mr (r n : ℕ) : ℤ :=
  ∑ t ∈ (Icc 1 n).powerset.filter (fun t => t.card = r ∧ ∑ k ∈ t, k = n),
    (Nat.multinomial t id : ℤ)

-- S n = ∑_{r=0}^{n} (-1)^r M_r(n)
lemma S_eq_sum_Mr (n : ℕ) : S n = ∑ r ∈ range (n+1), (-1)^r * Mr r n := by
  rw [S]
  -- group the filtered sum by cardinality
  have hmaps : ∀ t ∈ (Icc 1 n).powerset.filter (fun t => ∑ k ∈ t, k = n),
      t.card ∈ range (n+1) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht
    rw [Finset.mem_range]
    have : t.card ≤ (Icc 1 n).card := Finset.card_le_card ht.1
    simp [Nat.card_Icc] at this ⊢
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (f := Sterm)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Mr, Finset.mul_sum, Finset.filter_filter]
  apply Finset.sum_congr
  · apply Finset.filter_congr; intro t _; rw [and_comm]
  · intro t ht
    simp only [Finset.mem_filter] at ht
    rw [Sterm, ht.2.1]

/-- Triangular number T_r = r(r+1)/2. -/
def tri (r : ℕ) : ℕ := r * (r + 1) / 2

lemma two_tri (r : ℕ) : 2 * tri r = r * (r + 1) := by
  rw [tri, Nat.mul_div_cancel']
  exact (Nat.even_mul_succ_self r).two_dvd

lemma tri_succ (r : ℕ) : tri (r + 1) = tri r + (r + 1) := by
  have h1 := two_tri (r+1)
  have h2 := two_tri r
  have h3 : (r+1)*(r+1+1) = r*(r+1) + 2*(r+1) := by ring
  omega

lemma tri_ge (r : ℕ) : r ≤ tri r := by
  have := two_tri r
  nlinarith [this]

lemma tri_mono {a b : ℕ} (h : a ≤ b) : tri a ≤ tri b := by
  have h1 := two_tri a
  have h2 := two_tri b
  nlinarith [h1, h2, h]

/-- m n = largest r with T_r ≤ n. -/
def mm (n : ℕ) : ℕ := Nat.findGreatest (fun r => tri r ≤ n) n

lemma mm_spec (n : ℕ) : tri (mm n) ≤ n :=
  Nat.findGreatest_spec (P := fun r => tri r ≤ n) (m := 0) (Nat.zero_le n) (by simp [tri])

lemma mm_max (n : ℕ) : n < tri (mm n + 1) := by
  by_cases hle : mm n + 1 ≤ n
  · have := Nat.findGreatest_is_greatest (P := fun r => tri r ≤ n) (n := n)
      (k := mm n + 1) (by simp [mm]) hle
    omega
  · have : n < mm n + 1 := by omega
    calc n < mm n + 1 := this
      _ ≤ tri (mm n + 1) := tri_ge _

-- m is between consecutive: for n ≥ 1, mm n = mm (n-1) or mm(n-1)+1
lemma mm_mono {a b : ℕ} (h : a ≤ b) : mm a ≤ mm b := by
  apply Nat.le_findGreatest
  · exact le_trans (Nat.findGreatest_le a) h
  · exact le_trans (mm_spec a) h

def is_triangular (n : ℕ) : Prop := ∃ k : ℕ, n = k * (k + 1) / 2

lemma is_tri_iff (n : ℕ) : is_triangular n ↔ ∃ k, tri k = n :=
  ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

lemma mm_le_succ (p : ℕ) : mm (p + 1) ≤ mm p + 1 := by
  by_contra h
  push_neg at h  -- mm p + 1 < mm (p+1)
  have hmono : mm p + 2 ≤ mm (p + 1) := by omega
  have h1 : tri (mm p + 2) ≤ tri (mm (p + 1)) := tri_mono hmono
  have h2 : tri (mm (p + 1)) ≤ p + 1 := mm_spec (p + 1)
  have h3 : p < tri (mm p + 1) := mm_max p
  have h4 : tri (mm p + 2) = tri (mm p + 1) + (mm p + 2) := tri_succ (mm p + 1)
  omega

lemma mm_step_iff (p : ℕ) : mm (p + 1) = mm p + 1 ↔ is_triangular (p + 1) := by
  rw [is_tri_iff]
  constructor
  · intro h
    refine ⟨mm p + 1, ?_⟩
    have h1 : tri (mm (p + 1)) ≤ p + 1 := mm_spec (p + 1)
    have h2 : p < tri (mm p + 1) := mm_max p
    rw [h] at h1
    omega
  · rintro ⟨k, hk⟩
    have hkle : k ≤ p + 1 := by rw [← hk]; exact tri_ge k
    have hk1 : k ≤ mm (p + 1) := Nat.le_findGreatest hkle (by rw [hk])
    have hk2 : mm p < k := by
      by_contra hc
      push_neg at hc
      have : tri k ≤ tri (mm p) := tri_mono hc
      have := mm_spec p
      omega
    have hle := mm_le_succ p
    omega

-- The bridge: A185895 n = S n
lemma bridge (n : ℕ) : A185895 n = S n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have h1 : A185895 0 = 1 := by simp [A185895]
    have h2 : S 0 = 1 := by
      rw [S, show (Finset.Icc 1 0) = (∅ : Finset ℕ) from rfl, Finset.powerset_empty]
      rw [Finset.filter_singleton, if_pos (by simp)]
      simp [Sterm, Nat.multinomial]
    rw [h1, h2]
  · rw [A185895, if_neg (by omega)]
    simp only
    rw [coeffn_mul_fact n]
    exact Rat.floor_intCast _

-- THE HARD CORE (to be proven via monotonicity of M_r):
lemma key_sign (n : ℕ) : 0 < (-1)^(mm n) * S n := by sorry

-- Final assembly
lemma final_S (n : ℕ) (hn : 0 < n) : S n * S (n - 1) < 0 ↔ is_triangular n := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hu := key_sign (p + 1)
  have hv := key_sign p
  have hstep := mm_step_iff p
  have hlo : mm p ≤ mm (p + 1) := mm_mono (by omega)
  have hhi : mm (p + 1) ≤ mm p + 1 := mm_le_succ p
  have hprod : 0 < ((-1 : ℤ) ^ (mm (p + 1)) * S (p + 1)) * ((-1) ^ (mm p) * S p) :=
    mul_pos hu hv
  have hkey : ((-1 : ℤ) ^ (mm (p + 1)) * S (p + 1)) * ((-1) ^ (mm p) * S p)
      = (-1) ^ (mm (p + 1) + mm p) * (S (p + 1) * S p) := by rw [pow_add]; ring
  rw [hkey] at hprod
  rcases (show mm (p + 1) = mm p ∨ mm (p + 1) = mm p + 1 by omega) with he | he
  · -- even exponent: product > 0, not triangular
    have hev : Even (mm (p + 1) + mm p) := ⟨mm p, by omega⟩
    rw [hev.neg_one_pow, one_mul] at hprod
    constructor
    · intro hlt; exfalso; linarith
    · intro htri; exfalso; have := hstep.mpr htri; omega
  · -- odd exponent: product < 0, triangular
    have hod : Odd (mm (p + 1) + mm p) := ⟨mm p, by omega⟩
    rw [hod.neg_one_pow] at hprod
    constructor
    · intro _; exact hstep.mp he
    · intro _; linarith

theorem oeis_185895_conjecture_1 :
  ∀ (n : ℕ), 0 < n →
    ((A185895 n) * (A185895 (n - 1)) < 0 ↔ is_triangular n) := by
  intro n hn
  rw [bridge n, bridge (n - 1)]
  exact final_S n hn
