import FormalConjectures.Util.ProblemImports

open Nat

/--
A323557: G.f.: $\sum_{n\ge 0} x^n \cdot \frac{(1 + x^n)^n}{(1 + x^{n+1})^{n+1}}$.
The $m$-th term $a(m)$ is the coefficient of $x^m$, which is explicitly given by the sum:
$$ a(m) = \sum_{n=0}^m \sum_{k=0}^n \binom{n}{k} (-1)^j \binom{n+j}{j},$$
where $j = \frac{m - n(k+1)}{n+1}$, and the term is zero unless $j$ is a natural number.
-/
def a (m : ℕ) : ℤ :=
  Finset.sum (Finset.range (m + 1)) fun n =>
    Finset.sum (Finset.range (n + 1)) fun k =>
      let exp_x_num := n * (k + 1)
      if exp_x_num ≤ m then
        let remainder := m - exp_x_num
        if (n + 1) ∣ remainder then
          let j : ℕ := remainder / (n + 1)
          let c₁ : ℤ := (n.choose k)
          let c₂ : ℤ := (choose (n + j) j)
          let sign : ℤ := if Even j then 1 else -1
          sign * c₁ * c₂
        else
          0
      else
        0


/-! ## Parity of binomial coefficients (Kummer for p = 2) -/

private lemma land_eq_zero_iff (a b : ℕ) :
    a &&& b = 0 ↔ ¬(a % 2 = 1 ∧ b % 2 = 1) ∧ (a / 2 &&& b / 2 = 0) := by
  have hmod : (a &&& b) % 2 = 1 ↔ (a % 2 = 1 ∧ b % 2 = 1) := by
    have h := Nat.testBit_and a b 0
    simp only [Nat.testBit_zero] at h
    simpa [Bool.and_eq_true] using h
  have hdiv : (a &&& b) / 2 = a / 2 &&& b / 2 := Nat.and_div_two
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← hmod]; omega
    · rw [← hdiv]; omega
  · rintro ⟨h1, h2⟩
    have e1 : (a &&& b) % 2 ≠ 1 := fun hc => h1 (hmod.mp hc)
    have e2 : (a &&& b) / 2 = 0 := by rw [hdiv]; exact h2
    omega

/-- For all `a b`, `Odd ((a+b).choose a) ↔ a &&& b = 0` (Kummer's theorem at `p = 2`). -/
theorem odd_choose_iff (a b : ℕ) : Odd ((a + b).choose a) ↔ a &&& b = 0 := by
  have main : ∀ N : ℕ, ∀ a b : ℕ, a + b = N →
      (Odd ((a + b).choose a) ↔ a &&& b = 0) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro a b hab
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hab
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha; subst hb; simp
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have luc : ((a + b).choose a) % 2 =
          (((a + b) % 2).choose (a % 2) * ((a + b) / 2).choose (a / 2)) % 2 :=
        Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2)
      rw [Nat.odd_iff, land_eq_zero_iff]
      have iha' := ih (a / 2 + b / 2) (by omega) (a / 2) (b / 2) rfl
      rw [Nat.odd_iff] at iha'
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
        rcases Nat.mod_two_eq_zero_or_one b with hb | hb
      · have h2 : (a + b) / 2 = a / 2 + b / 2 := by omega
        simp only [ha, hb, h2, Nat.choose_zero_right, Nat.choose_self, one_mul,
          Nat.add_mod, Nat.zero_mod] at luc
        rw [luc, iha']; simp [ha, hb]
      · have h2 : (a + b) / 2 = a / 2 + b / 2 := by omega
        have h1 : (a + b) % 2 = 1 := by omega
        rw [h1, h2, ha] at luc
        simp only [Nat.choose_zero_right, one_mul] at luc
        rw [luc, iha']; simp [ha, hb]
      · have h2 : (a + b) / 2 = a / 2 + b / 2 := by omega
        have h1 : (a + b) % 2 = 1 := by omega
        rw [h1, h2, ha] at luc
        simp only [Nat.choose_self, one_mul] at luc
        rw [luc, iha']; simp [ha, hb]
      · have h1 : (a + b) % 2 = 0 := by omega
        rw [h1, ha] at luc
        norm_num at luc
        constructor
        · intro hc; rw [luc] at hc; simp at hc
        · rintro ⟨hcon, -⟩; exact absurd ⟨ha, hb⟩ hcon
  exact main (a + b) a b rfl

/-! ## Disjoint-union bitwise lemmas -/

private theorem lor_add_land (a b : ℕ) : (a ||| b) + (a &&& b) = a + b := by
  have main : ∀ N a b : ℕ, a + b = N → (a ||| b) + (a &&& b) = a + b := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro a b hab
      rcases Nat.eq_zero_or_pos N with hN | hN
      · have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst ha; subst hb; simp
      have hor1 : (a ||| b) % 2 = 1 ↔ (a % 2 = 1 ∨ b % 2 = 1) := by
        have h := Nat.testBit_or a b 0
        simp only [Nat.testBit_zero] at h
        simpa [Bool.or_eq_true] using h
      have hand1 : (a &&& b) % 2 = 1 ↔ (a % 2 = 1 ∧ b % 2 = 1) := by
        have h := Nat.testBit_and a b 0
        simp only [Nat.testBit_zero] at h
        simpa [Bool.and_eq_true] using h
      have hdor : (a ||| b) / 2 = a / 2 ||| b / 2 := Nat.or_div_two
      have hdand : (a &&& b) / 2 = a / 2 &&& b / 2 := Nat.and_div_two
      have ihr := ih (a/2 + b/2) (by omega) (a/2) (b/2) rfl
      have hor2 := Nat.mod_two_eq_zero_or_one (a ||| b)
      have hand2 := Nat.mod_two_eq_zero_or_one (a &&& b)
      omega
  exact main (a + b) a b rfl

private theorem add_eq_or {a b : ℕ} (h : a &&& b = 0) : a + b = a ||| b := by
  have := lor_add_land a b; omega

private theorem lor_eq_zero {a b : ℕ} (h : a ||| b = 0) : a = 0 ∧ b = 0 := by
  have h1 : a ≤ a ||| b := Nat.left_le_or
  have h2 : b ≤ b ||| a := Nat.left_le_or
  rw [Nat.or_comm b a] at h2
  omega

/-- The key bitwise facts powering the involution. -/
private theorem bit_facts (n k J : ℕ) (hk : k ≤ n)
    (ck : k &&& (n - k) = 0) (cj : J &&& n = 0) :
    k &&& J = 0 ∧ (n - k) &&& (k + J) = 0 ∧ (n - k) &&& n = (n - k) := by
  set p := n - k with hp
  have hkp : k + p = n := by omega
  have hn : n = k ||| p := by rw [← add_eq_or ck, hkp]
  have hJor : (J &&& k) ||| (J &&& p) = 0 := by
    rw [← Nat.and_or_distrib_left, ← hn]; exact cj
  obtain ⟨hJk, hJp⟩ := lor_eq_zero hJor
  have hkJ : k &&& J = 0 := by rw [Nat.and_comm]; exact hJk
  have hpk : p &&& k = 0 := by rw [Nat.and_comm]; exact ck
  have hpJ : p &&& J = 0 := by rw [Nat.and_comm]; exact hJp
  refine ⟨hkJ, ?_, ?_⟩
  · rw [add_eq_or hkJ, Nat.and_or_distrib_left, hpk, hpJ]; simp
  · rw [hn, Nat.and_or_distrib_left, hpk, Nat.and_self]; simp

/-! ## The sequence and its parity -/

theorem natCastZMod2 (x : ℕ) : (x : ZMod 2) = if Odd x then 1 else 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  rcases Nat.even_or_odd x with he | ho
  · rw [if_neg (by simpa [Nat.not_odd_iff_even] using he)]
    obtain ⟨t, rfl⟩ := he; push_cast; rw [← two_mul, h2, zero_mul]
  · rw [if_pos ho]
    obtain ⟨t, rfl⟩ := ho; push_cast; rw [h2]; ring


def jj (m n k : ℕ) : ℕ := (m - n * (k + 1)) / (n + 1)
def P (m n k : ℕ) : Prop :=
  n * (k + 1) ≤ m ∧ (n + 1) ∣ (m - n * (k + 1)) ∧
    Odd (n.choose k) ∧ Odd ((n + jj m n k).choose (jj m n k))

instance decP (m n k : ℕ) : Decidable (P m n k) := by unfold P; infer_instance

theorem term_cast (m n k : ℕ) :
    (((if n * (k + 1) ≤ m then
        if (n + 1) ∣ (m - n * (k + 1)) then
          (if Even ((m - n * (k + 1)) / (n + 1)) then (1:ℤ) else -1)
            * (↑(n.choose k))
            * (↑((n + (m - n * (k + 1)) / (n + 1)).choose ((m - n * (k + 1)) / (n + 1))))
        else 0
      else 0) : ℤ) : ZMod 2) = if P m n k then 1 else 0 := by
  by_cases h1 : n * (k + 1) ≤ m
  · by_cases h2 : (n + 1) ∣ (m - n * (k + 1))
    · rw [if_pos h1, if_pos h2]
      push_cast
      rw [show (if Even ((m - n * (k + 1)) / (n + 1)) then (1:ZMod 2) else -1) = 1 from by
            split_ifs <;> decide, one_mul,
          natCastZMod2 (n.choose k),
          natCastZMod2 ((n + (m - n*(k+1))/(n+1)).choose ((m-n*(k+1))/(n+1)))]
      simp only [P, jj, h1, h2, true_and]
      split_ifs <;> simp_all
    · rw [if_pos h1, if_neg h2]; simp [P, h2]
  · rw [if_neg h1]; simp [P, h1]

/-- `(a m : ZMod 2)` as a sum of indicators over a product. -/
theorem a_cast (m : ℕ) :
    (a m : ZMod 2) = ∑ p ∈ (Finset.range (m+1)) ×ˢ (Finset.range (m+1)),
      (if P m p.1 p.2 then (1:ZMod 2) else 0) := by
  have step1 : (a m : ZMod 2) = ∑ n ∈ Finset.range (m+1), ∑ k ∈ Finset.range (n+1),
      (if P m n k then (1:ZMod 2) else 0) := by
    rw [show ((a m : ℤ) : ZMod 2) = (Int.castRingHom (ZMod 2)) (a m) from rfl, a, map_sum]
    apply Finset.sum_congr rfl; intro n _
    rw [map_sum]
    apply Finset.sum_congr rfl; intro k _
    exact term_cast m n k
  rw [step1]
  have step2 : ∀ n ∈ Finset.range (m+1),
      ∑ k ∈ Finset.range (n+1), (if P m n k then (1:ZMod 2) else 0)
    = ∑ k ∈ Finset.range (m+1), (if P m n k then (1:ZMod 2) else 0) := by
    intro n hn
    simp only [Finset.mem_range] at hn
    have hsub : Finset.range (n+1) ⊆ Finset.range (m+1) := by
      intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    apply Finset.sum_subset hsub
    intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [if_neg]
    intro hP
    have := hP.2.2.1
    rw [Nat.odd_iff] at this
    have hz : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    omega
  rw [Finset.sum_congr rfl step2, ← Finset.sum_product']

/-- Extract arithmetic and bitwise facts from a "good" pair. -/
private lemma good_bits (m n k : ℕ) (hP : P m n k) :
    k ≤ n ∧ m = n * (k + 1) + (n + 1) * (jj m n k) ∧
      (k &&& jj m n k = 0) ∧ ((n - k) &&& (k + jj m n k) = 0) ∧ ((n - k) &&& n = n - k)
      ∧ (jj m n k &&& n = 0) := by
  obtain ⟨h1, h2, hok, hoj⟩ := hP
  set j := jj m n k with hjdef
  have hk : k ≤ n := by
    by_contra hc; push_neg at hc
    rw [Nat.odd_iff, Nat.choose_eq_zero_of_lt hc] at hok; simp at hok
  have hjmul : (n + 1) * j = m - n * (k + 1) := by
    rw [hjdef, jj, mul_comm]; exact Nat.div_mul_cancel h2
  have hm : m = n * (k + 1) + (n + 1) * j := by omega
  have ck : k &&& (n - k) = 0 :=
    (odd_choose_iff k (n - k)).mp (by rw [show k + (n - k) = n from by omega]; exact hok)
  have cj : j &&& n = 0 :=
    (odd_choose_iff j n).mp (by rw [show j + n = n + j from by omega]; exact hoj)
  obtain ⟨b1, b2, b3⟩ := bit_facts n k j hk ck cj
  exact ⟨hk, hm, b1, b2, b3, cj⟩

private lemma fixed_pronic (m n k : ℕ) (hP : P m n k) (hfix : k + jj m n k = n) :
    m = n * (n + 1) := by
  obtain ⟨hk, hm, b1, b2, b3, cj⟩ := good_bits m n k hP
  set j := jj m n k with hjdef
  have hjn : j = n - k := by omega
  have e : j &&& n = j := by rw [hjn]; exact b3
  have hj0 : j = 0 := by omega
  have hkn : k = n := by omega
  rw [hm, hj0, hkn]; ring

/-- The involution on pairs. -/
def gg (m : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if P m p.1 p.2 then (p.2 + jj m p.1 p.2, p.2) else p

/-- The involution maps a good pair to a good pair, and recovers the original. -/
private lemma image_P (m n k : ℕ) (hP : P m n k) :
    P m (k + jj m n k) k ∧ jj m (k + jj m n k) k = n - k ∧ k + jj m n k ≤ m := by
  obtain ⟨hk, hm, b1, b2, b3, cj⟩ := good_bits m n k hP
  set j := jj m n k with hjdef
  obtain ⟨d, hd⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  have hdk : n - k = d := by omega
  rw [hdk] at b2 b3
  rw [hd] at hm
  have hm' : m = (k + j) * (k + 1) + (k + j + 1) * d := by rw [hm]; ring
  have hXeq : m - (k + j) * (k + 1) = (k + j + 1) * d := by omega
  have hjj' : jj m (k + j) k = d := by
    rw [jj, hXeq]; exact Nat.mul_div_right d (by omega)
  have hP' : P m (k + j) k := by
    refine ⟨by omega, ⟨d, by omega⟩, (odd_choose_iff k j).mpr b1, ?_⟩
    rw [hjj', show k + j + d = d + (k + j) from by omega]
    exact (odd_choose_iff d (k + j)).mpr b2
  refine ⟨hP', hjj'.trans hdk.symm, ?_⟩
  have hle : k + j ≤ (k + j) * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- oeis_323557_conjecture_0: Odd terms occur only at positions n*(n+1) for n >= 0 (conjecture; verified for initial 32600 terms). -/
theorem oeis_323557_conjecture_0 (m : ℕ) : Odd (a m) → ∃ n : ℕ, m = n * (n + 1) := by
  intro hodd
  by_contra hcon
  push_neg at hcon
  have hzero : (a m : ZMod 2) = 0 := by
    rw [a_cast]
    refine Finset.sum_involution (fun p _ => gg m p) ?_ ?_ ?_ ?_
    · -- hg₁
      intro p hp
      by_cases hP : P m p.1 p.2
      · have himg := image_P m p.1 p.2 hP
        simp only [gg, if_pos hP]
        rw [if_pos himg.1]
        decide
      · simp [gg, if_neg hP]
    · -- hg₃
      intro p hp hfne
      have hP : P m p.1 p.2 := by
        by_contra h; rw [if_neg h] at hfne; exact hfne rfl
      simp only [gg, if_pos hP]
      intro heq
      have hcoord : p.2 + jj m p.1 p.2 = p.1 := (Prod.ext_iff.mp heq).1
      exact hcon p.1 (fixed_pronic m p.1 p.2 hP hcoord)
    · -- g_mem
      intro p hp
      by_cases hP : P m p.1 p.2
      · have himg := image_P m p.1 p.2 hP
        obtain ⟨hk, _, _, _, _, _⟩ := good_bits m p.1 p.2 hP
        simp only [gg, if_pos hP, Finset.mem_product, Finset.mem_range]
        refine ⟨by omega, by omega⟩
      · simp only [gg, if_neg hP]; exact hp
    · -- hg₄
      intro p hp
      by_cases hP : P m p.1 p.2
      · have himg := image_P m p.1 p.2 hP
        obtain ⟨hk, _, _, _, _, _⟩ := good_bits m p.1 p.2 hP
        simp only [gg, if_pos hP, if_pos himg.1]
        have h21 : p.2 + jj m (p.2 + jj m p.1 p.2) p.2 = p.1 := by
          rw [himg.2.1]; omega
        rw [h21]
      · simp only [gg, if_neg hP]
  have hdvd : (2:ℤ) ∣ a m := (ZMod.intCast_zmod_eq_zero_iff_dvd (a m) 2).mp hzero
  have heven : Even (a m) := (even_iff_two_dvd).mpr hdvd
  exact (Int.not_even_iff_odd.mpr hodd) heven
