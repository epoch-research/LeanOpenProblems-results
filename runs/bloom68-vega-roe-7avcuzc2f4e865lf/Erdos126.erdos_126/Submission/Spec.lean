import FormalConjecturesUtil

/-!
# Erdős Problem 126

*Reference:* [erdosproblems.com/126](https://www.erdosproblems.com/126)
-/

open Filter

namespace Erdos126

def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop := ∀ n,
    IsGreatest
      { m | ∀ (A : Finset ℕ), A.card = n →
        m ≤ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card}
      (f n)

end Erdos126

/- Checked auxiliary lemmas for the prime-support bound. -/

section

/-
# A prime-color baseline for Erdős problem 126

The positive elements of a finite set of natural numbers have distinct binary
codes indexed by the prime divisors of the product of their pair sums.  For an
odd prime, the bit records which half contains the leading nonzero residue;
for the prime two, it records which half contains the odd part modulo four.

Consequently, the cardinality is at most `2 ^ k + 1`, where `k` is the number
of distinct prime divisors of the ordered off-diagonal pair-sum product.  The
extra one allows the vertex zero.  This is only an exponential baseline, not
the stronger asymptotic bound asked for in the conjecture.
-/

namespace Erdos126PrimeCode

/-- The bit determined by the leading unit at `p`.  At two the modulus is four. -/
def primeColor (p a : ℕ) : Bool :=
  if p = 2 then decide (2 * (ordCompl[p] a % 4) < 4)
  else decide (2 * (ordCompl[p] a % p) < p)

/-- Opposite nonzero residues, neither at the midpoint, lie in different halves. -/
lemma half_colors_ne {m x y : ℕ} (hx : ¬ m ∣ x)
    (hmid : 2 * (x % m) ≠ m) (hxy : m ∣ x + y) :
    decide (2 * (x % m) < m) ≠ decide (2 * (y % m) < m) := by
  have hsum : x % m + y % m = m := by
    have h := Nat.add_mod_add_of_le_add_mod
      (Nat.le_mod_add_mod_of_dvd_add_of_not_dvd hxy hx)
    rw [Nat.mod_eq_zero_of_dvd hxy, zero_add] at h
    exact h.symm
  intro h
  have hiff := decide_eq_decide.mp h
  by_cases hxlt : 2 * (x % m) < m
  · have hylt := hiff.mp hxlt
    omega
  · have hynlt : ¬ 2 * (y % m) < m := fun hy => hxlt (hiff.mpr hy)
    omega

/-- If the sum has higher `p`-valuation than one summand, both summands have
exactly the same `p`-valuation. -/
lemma factorization_eq_of_lt_sum {p a b : ℕ} (hp : p.Prime)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.factorization p < (a + b).factorization p) :
    a.factorization p = b.factorization p := by
  have hsum0 : a + b ≠ 0 := by omega
  have hs : p ^ (a.factorization p + 1) ∣ a + b :=
    (hp.pow_dvd_iff_le_factorization hsum0).mpr h
  have ha0 : p ^ a.factorization p ∣ a := Nat.ordProj_dvd a p
  have hb0 : p ^ a.factorization p ∣ b :=
    (Nat.dvd_add_iff_right ha0).mpr
      ((pow_dvd_pow p (by omega : a.factorization p ≤ a.factorization p + 1)).trans hs)
  have hle : a.factorization p ≤ b.factorization p :=
    (hp.pow_dvd_iff_le_factorization hb).mp hb0
  have hnle : ¬ a.factorization p + 1 ≤ b.factorization p := by
    intro hle'
    have hb1 : p ^ (a.factorization p + 1) ∣ b :=
      (hp.pow_dvd_iff_le_factorization hb).mpr hle'
    have ha1 : p ^ (a.factorization p + 1) ∣ a :=
      (Nat.dvd_add_iff_left hb1).mpr hs
    have := (hp.pow_dvd_iff_le_factorization ha).mp ha1
    omega
  omega

/-- Cancel the common maximal prime power in a sum. -/
lemma pow_dvd_unit_sum {p a b k : ℕ} (hp : p.Prime)
    (hab : a.factorization p = b.factorization p)
    (h : p ^ (a.factorization p + k) ∣ a + b) :
    p ^ k ∣ ordCompl[p] a + ordCompl[p] b := by
  have hsum : a + b = p ^ a.factorization p * (ordCompl[p] a + ordCompl[p] b) := by
    calc
      a + b = p ^ a.factorization p * ordCompl[p] a +
          p ^ b.factorization p * ordCompl[p] b := by
        rw [Nat.ordProj_mul_ordCompl_eq_self, Nat.ordProj_mul_ordCompl_eq_self]
      _ = p ^ a.factorization p * (ordCompl[p] a + ordCompl[p] b) := by
        rw [← hab, mul_add]
  apply Nat.dvd_of_mul_dvd_mul_left (Nat.pow_pos hp.pos)
  rw [← pow_add, ← hsum]
  exact h

/-- Equal bits prevent the valuation of a sum from exceeding that of `2 * a`.
The allowance of one extra factor of two is precisely why its bit uses modulus
four instead of modulus two. -/
lemma factorization_sum_le_of_color_eq {p a b : ℕ} (hp : p.Prime)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : primeColor p a = primeColor p b) :
    (a + b).factorization p ≤ (2 * a).factorization p := by
  by_contra hle
  have hlt : (2 * a).factorization p < (a + b).factorization p := by omega
  have hfa : (2 * a).factorization p = (2 : ℕ).factorization p + a.factorization p := by
    rw [Nat.factorization_mul (by decide) ha, Finsupp.add_apply]
  have hva : a.factorization p < (a + b).factorization p := by omega
  have hab := factorization_eq_of_lt_sum hp ha hb hva
  have hsum0 : a + b ≠ 0 := by omega
  by_cases hp2 : p = 2
  · subst p
    have htwo : (2 : ℕ).factorization 2 = 1 := Nat.prime_two.factorization_self
    have hd : 2 ^ (a.factorization 2 + 2) ∣ a + b :=
      (Nat.prime_two.pow_dvd_iff_le_factorization hsum0).mpr (by omega)
    have h4 : 4 ∣ ordCompl[2] a + ordCompl[2] b := by
      simpa using pow_dvd_unit_sum Nat.prime_two hab hd
    have hn2 : ¬ 2 ∣ ordCompl[2] a := Nat.not_dvd_ordCompl Nat.prime_two ha
    have hn4 : ¬ 4 ∣ ordCompl[2] a := fun h => hn2 ((by decide : 2 ∣ 4).trans h)
    have hmid : 2 * (ordCompl[2] a % 4) ≠ 4 := by
      have hmod2 : ordCompl[2] a % 2 ≠ 0 := fun h => hn2 (Nat.dvd_of_mod_eq_zero h)
      have hmod4 := Nat.mod_mod_of_dvd (ordCompl[2] a) (by decide : 2 ∣ 4)
      omega
    exact half_colors_ne hn4 hmid h4 (by simpa [primeColor] using hc)
  · have hd : p ^ (a.factorization p + 1) ∣ a + b :=
      (hp.pow_dvd_iff_le_factorization hsum0).mpr hva
    have hunit : p ∣ ordCompl[p] a + ordCompl[p] b := by
      simpa using pow_dvd_unit_sum hp hab hd
    have hmid : 2 * (ordCompl[p] a % p) ≠ p := by
      have hodd := hp.mod_two_eq_one_iff_ne_two.mpr hp2
      omega
    exact half_colors_ne (Nat.not_dvd_ordCompl hp ha) hmid hunit
      (by simpa [primeColor, hp2] using hc)

/-- Agreement at every prime dividing the sum forces the sum to divide `2 * a`. -/
lemma sum_dvd_twice_of_colors_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : ∀ p : ℕ, p.Prime → p ∣ a + b → primeColor p a = primeColor p b) :
    a + b ∣ 2 * a := by
  apply (Nat.factorization_prime_le_iff_dvd (by omega) (by omega)).mp
  intro p hp
  by_cases hd : p ∣ a + b
  · exact factorization_sum_le_of_color_eq hp ha hb (hc p hp hd)
  · rw [Nat.factorization_eq_zero_of_not_dvd hd]
    exact Nat.zero_le _

/-- Two positive vertices agreeing at all prime divisors of their sum are equal. -/
lemma eq_of_colors_eq {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : ∀ p : ℕ, p.Prime → p ∣ a + b → primeColor p a = primeColor p b) :
    a = b := by
  have h₁ := Nat.le_of_dvd (by omega : 0 < 2 * a)
    (sum_dvd_twice_of_colors_eq ha hb hc)
  have h₂ := Nat.le_of_dvd (by omega : 0 < 2 * b)
    (sum_dvd_twice_of_colors_eq hb ha (fun p hp hd =>
      (hc p hp (by simpa [Nat.add_comm] using hd)).symm))
  omega

/-- The product over ordered pairs of distinct vertices, as in the conjecture. -/
def sumProduct (A : Finset ℕ) : ℕ :=
  ∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)

lemma sumProduct_ne_zero (A : Finset ℕ) : sumProduct A ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  rintro ⟨a, b⟩ hab
  have hne := (Finset.mem_offDiag.mp hab).2.2
  dsimp
  omega

/-- Each prime divisor of a pair sum occurs among the indexing primes. -/
lemma prime_mem_sumProduct {A : Finset ℕ} {a b p : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (hp : p.Prime) (hd : p ∣ a + b) :
    p ∈ (sumProduct A).primeFactors := by
  apply hp.mem_primeFactors _ (sumProduct_ne_zero A)
  exact hd.trans (Finset.dvd_prod_of_mem (fun q : ℕ × ℕ => q.1 + q.2)
    (show (a, b) ∈ A.offDiag from Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩))

/-- The binary code of a vertex, with coordinates indexed by a finite prime set. -/
def code (S : Finset ℕ) (a : ℕ) : S → Bool :=
  fun p => primeColor p a

/-- On the positive vertices, the code using the primes of the pair-sum product
is injective. -/
theorem code_injective (A : Finset ℕ) :
    Function.Injective (fun a : A.erase 0 => code (sumProduct A).primeFactors a) := by
  intro a b hcode
  apply Subtype.ext
  by_contra hne
  apply hne
  have ha := Finset.mem_erase.mp a.property
  have hb := Finset.mem_erase.mp b.property
  apply eq_of_colors_eq ha.1 hb.1
  intro p hp hd
  have hpS := prime_mem_sumProduct ha.2 hb.2 hne hp hd
  exact congrFun hcode ⟨p, hpS⟩

/-- The positive vertices fit into the space of binary codes. -/
theorem card_erase_zero_le (A : Finset ℕ) :
    (A.erase 0).card ≤ 2 ^ (sumProduct A).primeFactors.card := by
  have h := Fintype.card_le_of_injective
    (fun a : A.erase 0 => code (sumProduct A).primeFactors a) (code_injective A)
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using h

/-- Certified exponential baseline for the ordered pair-sum prime count.
This does not assert the superlogarithmic bound of Erdős problem 126. -/
theorem card_le_two_pow_primeFactors_card_add_one (A : Finset ℕ) :
    A.card ≤ 2 ^ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card + 1 := by
  have h := card_erase_zero_le A
  change (A.erase 0).card ≤ 2 ^ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card at h
  by_cases hzero : 0 ∈ A
  · have hcard := Finset.card_erase_add_one hzero
    omega
  · rw [Finset.erase_eq_of_notMem hzero] at h
    omega

end Erdos126PrimeCode

end

section

/-
# A signed laminar-family cardinal bound

Scalar quadratic forms, a two-copy Hall matching, and the two budgets for the
signed-family kernel occurring in the `n ≤ 3 r²` bound.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos126Kernel

/-- The scalar quadratic form of a finite real kernel. -/
def qform {V : Type*} [Fintype V] (M : V → V → ℝ) (z : V → ℝ) : ℝ :=
  ∑ i, ∑ j, z i * z j * M i j

/-- Conditional negative semidefiniteness on vectors whose coordinates sum to zero. -/
def CND {V : Type*} [Fintype V] (M : V → V → ℝ) : Prop :=
  ∀ z : V → ℝ, (∑ i, z i) = 0 → qform M z ≤ 0

/-- The weighted co-membership kernel of a finite family of supports. -/
def familyKernel {V : Type*} [Fintype V] {J : Type*}
    (F : Finset J) (U : J → Finset V) (w : J → ℝ) (i j : V) : ℝ := by
  classical
  exact ∑ t ∈ F, if i ∈ U t ∧ j ∈ U t then w t else 0

/-- The contribution from pairs of opposite signs. -/
def crossKernel {V P : Type*} [Fintype P]
    (M : P → V → V → ℝ) (σ : P → V → Bool) (i j : V) : ℝ :=
  ∑ p, if σ p i = σ p j then 0 else M p i j

/-- The contribution from pairs of equal signs. -/
def sameKernel {V P : Type*} [Fintype P]
    (M : P → V → V → ℝ) (σ : P → V → Bool) (i j : V) : ℝ :=
  ∑ p, if σ p i = σ p j then M p i j else 0

set_option maxHeartbeats 0

section Matching

variable {V : Type*} [Fintype V]

/-- A laminar family of sets, each containing its index and at least two points,
has distinct representatives in two copies of the punctured sets. -/
theorem laminar_two_copy_matching (A : V → Finset V)
    (hself : ∀ i, i ∈ A i) (hsize : ∀ i, 2 ≤ (A i).card)
    (hlam : ∀ i j, Disjoint (A i) (A j) ∨ A i ⊆ A j ∨ A j ⊆ A i) :
    ∃ H : V → V × Bool, Function.Injective H ∧
      ∀ i, (H i).1 ≠ i ∧ (H i).1 ∈ A i := by
  classical
  have hne (i : V) : ((A i).erase i).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (hself i)]
    have := hsize i
    omega
  choose g hg using hne
  have hall (s : Finset V) :
      s.card ≤ (s.biUnion (fun i => (A i).erase i ×ˢ (univ : Finset Bool))).card := by
    let N := s.biUnion (fun i => (A i).erase i)
    let B := s \ N
    have hB (i : V) (hi : i ∈ B) : i ∈ s ∧ i ∉ N := mem_sdiff.mp hi
    have hdisj (i j : V) (hi : i ∈ B) (hj : j ∈ B) (hne : i ≠ j) :
        Disjoint (A i) (A j) := by
      rcases hlam i j with hd | hij | hji
      · exact hd
      · exfalso
        apply (hB i hi).2
        exact mem_biUnion.mpr ⟨j, (hB j hj).1, mem_erase.mpr ⟨hne, hij (hself i)⟩⟩
      · exfalso
        apply (hB j hj).2
        exact mem_biUnion.mpr ⟨i, (hB i hi).1, mem_erase.mpr ⟨hne.symm, hji (hself j)⟩⟩
    have hBN : B.card ≤ N.card := by
      apply Finset.card_le_card_of_injOn g
      · intro i hi
        exact mem_biUnion.mpr ⟨i, (hB i hi).1, hg i⟩
      · intro i hi j hj hij
        by_contra hne
        have hd := Finset.disjoint_left.mp (hdisj i j hi hj hne)
        exact hd (mem_of_mem_erase (hg i)) (hij ▸ mem_of_mem_erase (hg j))
    have hs : s.card ≤ 2 * N.card := by
      have hcard := Finset.card_sdiff_add_card_inter s N
      have hinter : (s ∩ N).card ≤ N.card := card_le_card inter_subset_right
      dsimp [B] at hBN
      omega
    have hprod : s.biUnion (fun i => (A i).erase i ×ˢ (univ : Finset Bool)) =
        N ×ˢ (univ : Finset Bool) := by
      ext x
      simp [N]
    rw [hprod, card_product]
    simpa [Nat.mul_comm] using hs
  obtain ⟨H, hH, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (fun i => (A i).erase i ×ˢ (univ : Finset Bool))).mp hall
  exact ⟨H, hH, fun i => mem_erase.mp (mem_product.mp (hmem i)).1⟩

/-- A smallest support through a point lies in every support through that point.
If no support contains the point, the whole vertex set is used. -/
theorem exists_minimal_support {J : Type*} (F : Finset J) (U : J → Finset V)
    (hn : 2 ≤ Fintype.card V)
    (hsize : ∀ t ∈ F, 2 ≤ (U t).card)
    (hlam : ∀ t ∈ F, ∀ u ∈ F,
      Disjoint (U t) (U u) ∨ U t ⊆ U u ∨ U u ⊆ U t) (i : V) :
    ∃ A : Finset V, i ∈ A ∧ 2 ≤ A.card ∧
      (A = univ ∨ ∃ t ∈ F, A = U t) ∧
      ∀ t ∈ F, i ∈ U t → A ⊆ U t := by
  classical
  let G := F.filter (fun t => i ∈ U t)
  by_cases hG : G.Nonempty
  · obtain ⟨t, ht, hmin⟩ := G.exists_min_image (fun t => (U t).card) hG
    have htF : t ∈ F := (mem_filter.mp ht).1
    have hit : i ∈ U t := (mem_filter.mp ht).2
    refine ⟨U t, hit, hsize t htF, Or.inr ⟨t, htF, rfl⟩, ?_⟩
    intro u hu hiu
    rcases hlam t htF u hu with hd | htu | hut
    · exact False.elim (Finset.disjoint_left.mp hd hit hiu)
    · exact htu
    · have hcard := hmin u (mem_filter.mpr ⟨hu, hiu⟩)
      exact le_of_eq (Finset.eq_of_subset_of_card_le hut hcard).symm
  · refine ⟨univ, mem_univ i, by simpa using hn, Or.inl rfl, ?_⟩
    intro t ht hit
    exact False.elim (hG ⟨t, mem_filter.mpr ⟨ht, hit⟩⟩)

/-- Laminar weighted kernels have a two-copy matching along which each diagonal
entry is preserved. No finiteness assumption on the label type is required. -/
theorem familyKernel_matching {J : Type*} (F : Finset J)
    (U : J → Finset V) (w : J → ℝ) (hn : 2 ≤ Fintype.card V)
    (hsize : ∀ t ∈ F, 2 ≤ (U t).card)
    (hlam : ∀ t ∈ F, ∀ u ∈ F,
      Disjoint (U t) (U u) ∨ U t ⊆ U u ∨ U u ⊆ U t) :
    ∃ H : V → V × Bool, Function.Injective H ∧
      ∀ i, (H i).1 ≠ i ∧
        familyKernel F U w i (H i).1 = familyKernel F U w i i := by
  classical
  choose A hself hcard horigin hsub using
    (exists_minimal_support F U hn hsize hlam)
  have hAlam (i j : V) : Disjoint (A i) (A j) ∨ A i ⊆ A j ∨ A j ⊆ A i := by
    rcases horigin i with hi | ⟨t, ht, hi⟩
    · exact Or.inr (Or.inr (hi ▸ subset_univ _))
    rcases horigin j with hj | ⟨u, hu, hj⟩
    · exact Or.inr (Or.inl (hj ▸ subset_univ _))
    rw [hi, hj]
    exact hlam t ht u hu
  obtain ⟨H, hH, hmem⟩ := laminar_two_copy_matching A hself hcard hAlam
  refine ⟨H, hH, fun i => ⟨(hmem i).1, ?_⟩⟩
  unfold familyKernel
  apply sum_congr rfl
  intro t ht
  by_cases hit : i ∈ U t
  · have hjt := hsub i t ht hit (hmem i).2
    simp [hit, hjt]
  · simp [hit]

end Matching

section Geometry

variable {V : Type*} [Fintype V]

/-- A coordinate unit vector, with no decidable-equality assumption in the API. -/
def unitVector (i k : V) : ℝ := by
  classical
  exact if k = i then 1 else 0

@[simp] theorem sum_unitVector (i : V) : (∑ k, unitVector i k) = 1 := by
  classical
  simp [unitVector]

@[simp] theorem sum_unitVector_mul (i : V) (f : V → ℝ) :
    (∑ k, unitVector i k * f k) = f i := by
  classical
  simp [unitVector, ite_mul]

@[simp] theorem qform_unitVector (C : V → V → ℝ) (i : V) :
    qform C (unitVector i) = C i i := by
  classical
  simp [qform, unitVector, ite_mul, mul_ite]

theorem qform_unitVector_add (C : V → V → ℝ) (i j : V) :
    qform C (fun k => unitVector i k + unitVector j k) =
      C i i + C i j + C j i + C j j := by
  classical
  simp [qform, unitVector, add_mul, mul_add, ite_mul, mul_ite, sum_add_distrib]
  ring

/-- Expanding an affine test vector using symmetry, entirely in scalar sums. -/
theorem qform_affine (C : V → V → ℝ) (hsymm : ∀ i j, C i j = C j i)
    (x : V → ℝ) (a b : ℝ) :
    qform C (fun i => a * x i - b) =
      a ^ 2 * qform C x - 2 * a * b * (∑ i, x i * ∑ j, C i j) +
        b ^ 2 * (∑ i, ∑ j, C i j) := by
  have hcol : (∑ i, ∑ j, x j * C i j) = ∑ i, x i * ∑ j, C i j := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [hsymm i j]
  unfold qform
  calc
    (∑ i, ∑ j, (a * x i - b) * (a * x j - b) * C i j) =
        ∑ i, ∑ j, (a ^ 2 * (x i * x j * C i j) -
          a * b * (x i * C i j) - a * b * (x j * C i j) + b ^ 2 * C i j) := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
      rw [hcol]
      ring

/-- The elementary CND geometry estimates from the one-point and two-point tests. -/
theorem cnd_geometry (C : V → V → ℝ) (hcnd : CND C)
    (hsymm : ∀ i j, C i j = C j i) (hdiag : ∀ i, C i i = 0) :
    ∃ h : V → ℝ, (∀ i, 0 ≤ h i) ∧
      (∀ i j, (Fintype.card V : ℝ) ^ 2 * C i j ≤ h i + h j) ∧
      (∑ i, h i) = (Fintype.card V : ℝ) * (∑ i, ∑ j, C i j) := by
  let n : ℝ := Fintype.card V
  let S := ∑ i, ∑ j, C i j
  let h := fun i => 2 * n * (∑ j, C i j) - S
  refine ⟨h, ?_, ?_, ?_⟩
  · intro i
    have hz : (∑ k, (n * unitVector i k - 1)) = 0 := by
      simp [sum_sub_distrib, ← mul_sum, n]
    have ht := hcnd _ hz
    rw [qform_affine C hsymm, qform_unitVector, hdiag, sum_unitVector_mul] at ht
    dsimp [h, S]
    nlinarith
  · intro i j
    have hz : (∑ k, (n * (unitVector i k + unitVector j k) - 2)) = 0 := by
      simp [sum_sub_distrib, ← mul_sum, sum_add_distrib, n]
      ring
    have ht := hcnd _ hz
    have hrow : (∑ k, (unitVector i k + unitVector j k) * (∑ l, C k l)) =
        (∑ l, C i l) + (∑ l, C j l) := by
      simp [add_mul, sum_add_distrib]
    rw [qform_affine C hsymm, qform_unitVector_add, hdiag, hdiag, hrow,
      hsymm j i] at ht
    change n ^ 2 * C i j ≤ (2 * n * (∑ k, C i k) - S) +
      (2 * n * (∑ k, C j k) - S)
    dsimp [S]
    nlinarith
  · dsimp [h]
    simp only [sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
    dsimp [n, S]
    ring

/-- An injection into two copies charges each nonnegative weight at most twice. -/
theorem sum_fst_le_two_sum (h : V → ℝ) (h0 : ∀ i, 0 ≤ h i)
    (H : V → V × Bool) (hH : Function.Injective H) :
    (∑ i, h (H i).1) ≤ 2 * ∑ i, h i := by
  classical
  calc
    (∑ i, h (H i).1) = ∑ x ∈ univ.image H, h x.1 :=
      (sum_image (s := univ) (f := fun x : V × Bool => h x.1)
        (fun i _ j _ hij => hH hij)).symm
    _ ≤ ∑ x : V × Bool, h x.1 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun x _ _ => h0 x.1)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [← mul_sum, ← two_mul]

/-- The second budget for a diagonal dominated along a two-copy matching. -/
theorem cnd_matching_budget (C : V → V → ℝ) (hcnd : CND C)
    (hsymm : ∀ i j, C i j = C j i) (hdiag : ∀ i, C i i = 0)
    (hn : 0 < Fintype.card V) (D : V → ℝ)
    (H : V → V × Bool) (hH : Function.Injective H)
    (hD : ∀ i, D i ≤ C i (H i).1) :
    (Fintype.card V : ℝ) * (∑ i, D i) ≤ 3 * (∑ i, ∑ j, C i j) := by
  obtain ⟨h, h0, hpairs, hsum⟩ := cnd_geometry C hcnd hsymm hdiag
  have hbound : (Fintype.card V : ℝ) ^ 2 * (∑ i, D i) ≤ 3 * ∑ i, h i := by
    calc
      _ = ∑ i, (Fintype.card V : ℝ) ^ 2 * D i := mul_sum _ _ _
      _ ≤ ∑ i, (h i + h (H i).1) := by
        apply sum_le_sum
        intro i _
        exact (mul_le_mul_of_nonneg_left (hD i) (sq_nonneg _)).trans (hpairs i (H i).1)
      _ = (∑ i, h i) + (∑ i, h (H i).1) := sum_add_distrib
      _ ≤ 3 * ∑ i, h i := by
        have := sum_fst_le_two_sum h h0 H hH
        linarith
  rw [hsum] at hbound
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  apply le_of_mul_le_mul_left (a := (Fintype.card V : ℝ)) _ hnR
  nlinarith [hbound]

end Geometry

section SignedKernels

variable {V : Type*} [Fintype V]

@[simp] theorem qform_one (M : V → V → ℝ) :
    qform M (fun _ => 1) = ∑ i, ∑ j, M i j := by
  simp [qform]

/-- Quadratic forms commute with a finite sum of kernels. -/
theorem qform_sum {J : Type*} (F : Finset J) (M : J → V → V → ℝ) (z : V → ℝ) :
    qform (fun i j => ∑ t ∈ F, M t i j) z = ∑ t ∈ F, qform (M t) z := by
  unfold qform
  simp only [mul_sum]
  calc
    (∑ i, ∑ j, ∑ t ∈ F, z i * z j * M t i j) =
        ∑ i, ∑ t ∈ F, ∑ j, z i * z j * M t i j := by
      apply sum_congr rfl
      intro i _
      exact sum_comm
    _ = _ := sum_comm

/-- A weighted family kernel is a sum of rank-one Gram kernels. -/
theorem qform_familyKernel {J : Type*} (F : Finset J) (U : J → Finset V)
    (w : J → ℝ) (z : V → ℝ) :
    qform (familyKernel F U w) z = ∑ t ∈ F, w t * (∑ i ∈ U t, z i) ^ 2 := by
  classical
  unfold familyKernel
  rw [qform_sum]
  apply sum_congr rfl
  intro t _
  calc
    qform (fun i j => if i ∈ U t ∧ j ∈ U t then w t else 0) z =
        ∑ i, ∑ j, (if i ∈ U t then z i else 0) *
          (if j ∈ U t then z j else 0) * w t := by
      unfold qform
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      by_cases hi : i ∈ U t <;> by_cases hj : j ∈ U t <;> simp [hi, hj]
    _ = w t * (∑ i ∈ U t, z i) ^ 2 := by
      simp only [← sum_mul, ← mul_sum, sum_ite_mem, univ_inter]
      ring

theorem familyKernel_nonneg {J : Type*} (F : Finset J) (U : J → Finset V)
    (w : J → ℝ) (hw : ∀ t ∈ F, 0 ≤ w t) (i j : V) :
    0 ≤ familyKernel F U w i j := by
  classical
  unfold familyKernel
  apply sum_nonneg
  intro t ht
  split_ifs
  · exact hw t ht
  · exact le_rfl

theorem familyKernel_symm {J : Type*} (F : Finset J) (U : J → Finset V)
    (w : J → ℝ) (i j : V) :
    familyKernel F U w i j = familyKernel F U w j i := by
  classical
  simp only [familyKernel, and_comm]

theorem familyKernel_psd {J : Type*} (F : Finset J) (U : J → Finset V)
    (w : J → ℝ) (hw : ∀ t ∈ F, 0 ≤ w t) (z : V → ℝ) :
    0 ≤ qform (familyKernel F U w) z := by
  rw [qform_familyKernel]
  exact sum_nonneg (fun t ht => mul_nonneg (hw t ht) (sq_nonneg _))

/-- The real sign associated with a Boolean. -/
def boolSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem boolSign_mul_self (b : Bool) : boolSign b * boolSign b = 1 := by
  cases b <;> norm_num [boolSign]

theorem boolSign_cases (b : Bool) : boolSign b = 1 ∨ boolSign b = -1 := by
  cases b <;> simp [boolSign]

theorem boolSign_mul (a b : Bool) :
    boolSign a * boolSign b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> norm_num [boolSign]

/-- Twisting a kernel by signs is the same as twisting its test vector. -/
theorem qform_twist (M : V → V → ℝ) (s z : V → ℝ) :
    qform (fun i j => s i * s j * M i j) z = qform M (fun i => s i * z i) := by
  unfold qform
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

variable {P : Type*} [Fintype P]

/-- The sum of the signed Gram kernels. -/
def signedKernel (M : P → V → V → ℝ) (σ : P → V → Bool) (i j : V) : ℝ :=
  ∑ p, boolSign (σ p i) * boolSign (σ p j) * M p i j

section VertexIndependent

omit [Fintype V]

@[simp] theorem signedKernel_diag (M : P → V → V → ℝ) (σ : P → V → Bool) (i : V) :
    signedKernel M σ i i = ∑ p, M p i i := by
  simp [signedKernel]

theorem signedKernel_eq (M : P → V → V → ℝ) (σ : P → V → Bool) (i j : V) :
    signedKernel M σ i j = sameKernel M σ i j - crossKernel M σ i j := by
  unfold signedKernel sameKernel crossKernel
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  rw [boolSign_mul]
  by_cases h : σ p i = σ p j <;> simp [h]

theorem kernel_mass_split (M : P → V → V → ℝ) (σ : P → V → Bool) (i j : V) :
    (∑ p, M p i j) = 2 * crossKernel M σ i j + signedKernel M σ i j := by
  unfold crossKernel signedKernel
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [boolSign_mul]
  by_cases h : σ p i = σ p j <;> simp [h]
  ring

theorem crossKernel_nonneg (M : P → V → V → ℝ) (σ : P → V → Bool)
    (hM : ∀ p i j, 0 ≤ M p i j) (i j : V) : 0 ≤ crossKernel M σ i j := by
  unfold crossKernel
  apply sum_nonneg
  intro p _
  split_ifs
  · exact le_rfl
  · exact hM p i j

theorem sameKernel_nonneg (M : P → V → V → ℝ) (σ : P → V → Bool)
    (hM : ∀ p i j, 0 ≤ M p i j) (i j : V) : 0 ≤ sameKernel M σ i j := by
  unfold sameKernel
  apply sum_nonneg
  intro p _
  split_ifs
  · exact hM p i j
  · exact le_rfl

@[simp] theorem crossKernel_diag (M : P → V → V → ℝ) (σ : P → V → Bool) (i : V) :
    crossKernel M σ i i = 0 := by
  simp [crossKernel]

theorem crossKernel_symm (M : P → V → V → ℝ) (σ : P → V → Bool)
    (hM : ∀ p i j, M p i j = M p j i) (i j : V) :
    crossKernel M σ i j = crossKernel M σ j i := by
  unfold crossKernel
  apply sum_congr rfl
  intro p _
  rw [hM p i j]
  by_cases h : σ p i = σ p j
  · simp only [h, if_true]
  · simp only [if_neg h, if_neg (Ne.symm h)]

/-- Every off-diagonal family entry is bounded by the cross kernel, using the
strict separation for pairs whose signs agree. -/
theorem kernel_le_cross_offdiag (M : P → V → V → ℝ) (σ : P → V → Bool)
    (hM : ∀ p i j, 0 ≤ M p i j)
    (hstrict : ∀ i j, i ≠ j → sameKernel M σ i j < crossKernel M σ i j)
    (p : P) (i j : V) (hij : i ≠ j) : M p i j ≤ crossKernel M σ i j := by
  by_cases h : σ p i = σ p j
  · have hs : M p i j ≤ sameKernel M σ i j := by
      have hs := single_le_sum (s := univ)
        (f := fun q => if σ q i = σ q j then M q i j else 0)
        (fun q _ => by dsimp only; split_ifs; exact hM q i j; exact le_rfl) (mem_univ p)
      simpa only [if_pos h] using hs
    exact hs.trans (hstrict i j hij).le
  · have hs := single_le_sum (s := univ)
      (f := fun q => if σ q i = σ q j then 0 else M q i j)
      (fun q _ => by dsimp only; split_ifs; exact le_rfl; exact hM q i j) (mem_univ p)
    simpa only [if_neg h] using hs

end VertexIndependent

/-- Strict separation and at least two vertices make the total cross mass positive. -/
theorem crossKernel_total_pos (M : P → V → V → ℝ) (σ : P → V → Bool)
    (hM : ∀ p i j, 0 ≤ M p i j) (hn : 2 ≤ Fintype.card V)
    (hstrict : ∀ i j, i ≠ j → sameKernel M σ i j < crossKernel M σ i j) :
    0 < ∑ i, ∑ j, crossKernel M σ i j := by
  obtain ⟨i, j, hij⟩ := Fintype.one_lt_card_iff.mp (show 1 < Fintype.card V by omega)
  have hpos : 0 < crossKernel M σ i j :=
    (sameKernel_nonneg M σ hM i j).trans_lt (hstrict i j hij)
  apply sum_pos' (fun k _ => sum_nonneg (fun l _ => crossKernel_nonneg M σ hM k l))
  exact ⟨i, mem_univ i, sum_pos' (fun l _ => crossKernel_nonneg M σ hM i l)
    ⟨j, mem_univ j, hpos⟩⟩

end SignedKernels

section Budgets

variable {V : Type*} [Fintype V]

/-- For a kernel with nonpositive off-diagonal entries, every sign vector costs
at most twice the trace, minus the all-ones quadratic form. -/
theorem qform_sign_bound (Q : V → V → ℝ)
    (hneg : ∀ i j, i ≠ j → Q i j ≤ 0) (s : V → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    qform Q s + qform Q (fun _ => 1) ≤ 2 * ∑ i, Q i i := by
  classical
  calc
    _ = ∑ i, ∑ j, (s i * s j + 1) * Q i j := by
      simp only [qform, add_mul, one_mul, sum_add_distrib]
    _ ≤ ∑ i, ∑ j, if i = j then 2 * Q i i else 0 := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      by_cases hij : i = j
      · subst j
        rcases hs i with hi | hi <;> norm_num [hi]
      · rw [if_neg hij]
        have hn : 0 ≤ s i * s j + 1 := by
          rcases hs i with hi | hi <;> rcases hs j with hj | hj <;> norm_num [hi, hj]
        exact mul_nonpos_of_nonneg_of_nonpos hn (hneg i j hij)
    _ = _ := by simp [← mul_sum]

variable {P : Type*} [Fintype P]

/-- The signed-Gram budget `S ≤ r T`. -/
theorem signed_budget (M : P → V → V → ℝ) (σ : P → V → Bool)
    (hpsd : ∀ p z, 0 ≤ qform (M p) z)
    (hstrict : ∀ i j, i ≠ j → sameKernel M σ i j < crossKernel M σ i j) :
    (∑ i, ∑ j, crossKernel M σ i j) ≤
      (Fintype.card P : ℝ) * (∑ p, ∑ i, M p i i) := by
  let Qp := fun p i j => boolSign (σ p i) * boolSign (σ p j) * M p i j
  let Q := signedKernel M σ
  let T := ∑ p, ∑ i, M p i i
  let S := ∑ i, ∑ j, crossKernel M σ i j
  let mass := fun p => ∑ i, ∑ j, M p i j
  let r : ℝ := Fintype.card P
  have hQp (p : P) (z : V → ℝ) : 0 ≤ qform (Qp p) z := by
    dsimp [Qp]
    rw [qform_twist]
    exact hpsd p _
  have hQsum (z : V → ℝ) : qform Q z = ∑ p, qform (Qp p) z := by
    exact qform_sum univ Qp z
  have hQ (z : V → ℝ) : 0 ≤ qform Q z := by
    rw [hQsum]
    exact sum_nonneg (fun p _ => hQp p z)
  have htrace : (∑ i, Q i i) = T := by
    dsimp [Q, T]
    simp only [signedKernel_diag]
    exact sum_comm
  have hneg (i j : V) (hij : i ≠ j) : Q i j ≤ 0 := by
    dsimp [Q]
    rw [signedKernel_eq]
    linarith [hstrict i j hij]
  have hmass (p : P) : mass p ≤ 2 * T := by
    let sp := fun i => boolSign (σ p i)
    have heval : qform (Qp p) sp = mass p := by
      dsimp [Qp, sp]
      rw [qform_twist]
      simp only [boolSign_mul_self, qform_one]
      rfl
    have hle : qform (Qp p) sp ≤ qform Q sp := by
      rw [hQsum]
      exact single_le_sum (fun q _ => hQp q sp) (mem_univ p)
    have hb := qform_sign_bound Q hneg sp (fun i => boolSign_cases (σ p i))
    rw [htrace] at hb
    have hb0 := hQ (fun _ => 1)
    linarith
  have hmass_total : (∑ p, mass p) ≤ 2 * r * T := by
    calc
      _ ≤ ∑ _p : P, 2 * T := sum_le_sum (fun p _ => hmass p)
      _ = _ := by simp [r]; ring
  have hsplit : (∑ p, mass p) = 2 * S + qform Q (fun _ => 1) := by
    calc
      (∑ p, mass p) = ∑ i, ∑ j, ∑ p, M p i j := by
        dsimp [mass]
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        exact sum_comm
      _ = 2 * S + ∑ i, ∑ j, Q i j := by
        simp_rw [kernel_mass_split M σ]
        simp only [sum_add_distrib, ← mul_sum]
        rfl
      _ = _ := by rw [qform_one]
  have hb0 := hQ (fun _ => 1)
  change S ≤ r * T
  linarith

end Budgets

/-- **Signed laminar-family cardinal bound.**

The labels `J` need not form a finite type, and different labels may have equal
supports. For each `p`, the weights are nonnegative, every support has at least
two vertices, and the supports are laminar. Conditional negative definiteness
of the cross kernel and strict off-diagonal separation imply `|V| ≤ 3 |P|²`.
-/
theorem signed_family_card_bound
    {V P J : Type*} [Fintype V] [Fintype P]
    (F : P → Finset J) (U : P → J → Finset V) (w : P → J → ℝ)
    (σ : P → V → Bool)
    (hn : 2 ≤ Fintype.card V)
    (hw : ∀ p t, t ∈ F p → 0 ≤ w p t)
    (hsize : ∀ p t, t ∈ F p → 2 ≤ (U p t).card)
    (hlam : ∀ p t, t ∈ F p → ∀ u, u ∈ F p →
      Disjoint (U p t) (U p u) ∨ U p t ⊆ U p u ∨ U p u ⊆ U p t)
    (hcnd : CND (crossKernel (fun p => familyKernel (F p) (U p) (w p)) σ))
    (hstrict : ∀ i j, i ≠ j →
      sameKernel (fun p => familyKernel (F p) (U p) (w p)) σ i j <
        crossKernel (fun p => familyKernel (F p) (U p) (w p)) σ i j) :
    (Fintype.card V : ℝ) ≤ 3 * (Fintype.card P : ℝ) ^ 2 := by
  let M := fun p => familyKernel (F p) (U p) (w p)
  let C := crossKernel M σ
  let S := ∑ i, ∑ j, C i j
  let T := ∑ p, ∑ i, M p i i
  let n : ℝ := Fintype.card V
  let r : ℝ := Fintype.card P
  have hM0 (p : P) (i j : V) : 0 ≤ M p i j :=
    familyKernel_nonneg (F p) (U p) (w p) (hw p) i j
  have hMpsd (p : P) (z : V → ℝ) : 0 ≤ qform (M p) z :=
    familyKernel_psd (F p) (U p) (w p) (hw p) z
  have hMsymm (p : P) (i j : V) : M p i j = M p j i :=
    familyKernel_symm (F p) (U p) (w p) i j
  have hCsymm : ∀ i j, C i j = C j i := crossKernel_symm M σ hMsymm
  have hCdiag : ∀ i, C i i = 0 := crossKernel_diag M σ
  have hnpos : 0 < Fintype.card V := by omega
  have hnR : 0 < n := by
    dsimp [n]
    exact_mod_cast hnpos
  have hrR : 0 ≤ r := Nat.cast_nonneg _
  have hS : 0 < S := crossKernel_total_pos M σ hM0 hn hstrict
  have hfirst : S ≤ r * T := signed_budget M σ hMpsd hstrict
  have hsecondp (p : P) : n * (∑ i, M p i i) ≤ 3 * S := by
    obtain ⟨H, hH, hmatch⟩ :=
      familyKernel_matching (F p) (U p) (w p) hn (hsize p) (hlam p)
    apply cnd_matching_budget C hcnd hCsymm hCdiag hnpos (fun i => M p i i) H hH
    intro i
    calc
      M p i i = M p i (H i).1 := (hmatch i).2.symm
      _ ≤ C i (H i).1 :=
        kernel_le_cross_offdiag M σ hM0 hstrict p i (H i).1 (hmatch i).1.symm
  have hsecond : n * T ≤ 3 * r * S := by
    calc
      _ = ∑ p, n * (∑ i, M p i i) := mul_sum _ _ _
      _ ≤ ∑ _p : P, 3 * S := sum_le_sum (fun p _ => hsecondp p)
      _ = _ := by simp [r]; ring
  have hfinal : n * S ≤ (3 * r ^ 2) * S := by
    calc
      n * S ≤ n * (r * T) := mul_le_mul_of_nonneg_left hfirst hnR.le
      _ = r * (n * T) := by ring
      _ ≤ r * (3 * r * S) := mul_le_mul_of_nonneg_left hsecond hrR
      _ = (3 * r ^ 2) * S := by ring
  exact le_of_mul_le_mul_right hfinal hS

end Erdos126Kernel

end

end

section

/-
# Mixed negation-orbits of a finite vertex set

The mixed orbits form a disjoint family. A Boolean labeling which separates
non-self-opposite residues is constant on each side of every mixed orbit.
This gives the cross-entry identity and same-side entry bound. The residual
self-opposite kernel is positive semidefinite, by a finite-image sum of squares.
Additive homomorphisms enlarge orbits and give one-way laminarity of the families.
No finiteness assumption on the residue groups is used.
-/

namespace Erdos126Orbit

open scoped BigOperators
open Finset

noncomputable section

variable {V G : Type*} [Fintype V] [AddCommGroup G] [DecidableEq G]

/-- The vertices whose values agree up to sign with the value at `i`. -/
def orbit (v : V → G) (i : V) : Finset V :=
  univ.filter (fun j => v j = v i ∨ v j = -v i)

/-- A support contains both sides of a non-self-opposite residue pair. -/
def mixed (v : V → G) (U : Finset V) : Prop :=
  ∃ i ∈ U, ∃ j ∈ U, v i = -v j ∧ v i ≠ -v i

/-- The distinct mixed negation-orbits. -/
def family (v : V → G) : Finset (Finset V) := by
  classical
  exact (univ.image (orbit v)).filter (mixed v)

section Orbits

variable (v : V → G)

@[simp] theorem mem_orbit {i j : V} :
    i ∈ orbit v j ↔ v i = v j ∨ v i = -v j := by
  simp [orbit]

@[simp] theorem self_mem_orbit (i : V) : i ∈ orbit v i :=
  (mem_orbit v).2 (Or.inl rfl)

theorem mem_orbit_symm {i j : V} (h : i ∈ orbit v j) : j ∈ orbit v i := by
  rcases (mem_orbit v).1 h with h | h
  · exact (mem_orbit v).2 (Or.inl h.symm)
  · apply (mem_orbit v).2
    right
    simpa only [neg_neg] using congrArg Neg.neg h.symm

/-- Any member can be used as the representative of an orbit. -/
theorem orbit_eq_of_mem {i j : V} (h : i ∈ orbit v j) :
    orbit v i = orbit v j := by
  ext k
  simp only [mem_orbit]
  rcases (mem_orbit v).1 h with h | h
  · rw [h]
  · rw [h, neg_neg]
    exact or_comm

theorem orbit_eq_of_common_mem {i j k : V}
    (hi : k ∈ orbit v i) (hj : k ∈ orbit v j) : orbit v i = orbit v j :=
  (orbit_eq_of_mem v hi).symm.trans (orbit_eq_of_mem v hj)

theorem orbit_eq_iff {i j : V} :
    orbit v i = orbit v j ↔ v i = v j ∨ v i = -v j := by
  constructor
  · intro h
    apply (mem_orbit v).1
    rw [← h]
    exact self_mem_orbit v i
  · intro h
    exact orbit_eq_of_mem v ((mem_orbit v).2 h)

theorem orbit_disjoint_or_eq (i j : V) :
    Disjoint (orbit v i) (orbit v j) ∨ orbit v i = orbit v j := by
  classical
  by_cases h : Disjoint (orbit v i) (orbit v j)
  · exact Or.inl h
  · obtain ⟨k, hi, hj⟩ := Finset.not_disjoint_iff.1 h
    exact Or.inr (orbit_eq_of_common_mem v hi hj)

/-- Being non-self-opposite is constant on an orbit. -/
theorem nonself_of_mem_orbit {i j : V} (hi : i ∈ orbit v j)
    (hj : v j ≠ -v j) : v i ≠ -v i := by
  rcases (mem_orbit v).1 hi with h | h
  · simpa only [h] using hj
  · rw [h, neg_neg]
    exact Ne.symm hj

end Orbits

section Families

variable (v : V → G)

@[simp] theorem mem_family {U : Finset V} :
    U ∈ family v ↔ (∃ i, orbit v i = U) ∧ mixed v U := by
  classical
  simp only [family, mem_filter, mem_image, mem_univ, true_and]

theorem mixed_of_mem_family {U : Finset V} (hU : U ∈ family v) : mixed v U :=
  ((mem_family v).1 hU).2

theorem exists_orbit_of_mem_family {U : Finset V} (hU : U ∈ family v) :
    ∃ i, orbit v i = U :=
  ((mem_family v).1 hU).1

/-- A family member is exactly the orbit of any of its vertices. -/
theorem eq_orbit_of_mem_family {U : Finset V} {i : V}
    (hU : U ∈ family v) (hi : i ∈ U) : U = orbit v i := by
  obtain ⟨k, rfl⟩ := exists_orbit_of_mem_family v hU
  exact (orbit_eq_of_mem v hi).symm

theorem value_eq_or_neg_of_mem_family {U : Finset V} {i j : V}
    (hU : U ∈ family v) (hi : i ∈ U) (hj : j ∈ U) :
    v i = v j ∨ v i = -v j := by
  rw [eq_orbit_of_mem_family v hU hj] at hi
  exact (mem_orbit v).1 hi

theorem card_two_le_of_mem_family {U : Finset V} (hU : U ∈ family v) :
    2 ≤ U.card := by
  obtain ⟨i, hi, j, hj, hij, hni⟩ := mixed_of_mem_family v hU
  apply Finset.one_lt_card.2
  refine ⟨i, hi, j, hj, ?_⟩
  intro h
  subst j
  exact hni hij

theorem nonself_of_mem_family {U : Finset V} {i : V}
    (hU : U ∈ family v) (hi : i ∈ U) : v i ≠ -v i := by
  obtain ⟨a, ha, b, hb, hab, hna⟩ := mixed_of_mem_family v hU
  rw [eq_orbit_of_mem_family v hU ha] at hi
  exact nonself_of_mem_orbit v hi hna

/-- Every vertex in a mixed orbit has an opposite-valued witness in that orbit. -/
theorem exists_opposite_of_mem_family {U : Finset V} {i : V}
    (hU : U ∈ family v) (hi : i ∈ U) : ∃ j ∈ U, v i = -v j := by
  obtain ⟨a, ha, b, hb, hab, hna⟩ := mixed_of_mem_family v hU
  rcases value_eq_or_neg_of_mem_family v hU hi ha with h | h
  · exact ⟨b, hb, h.trans hab⟩
  · exact ⟨a, ha, h⟩

theorem family_disjoint_or_eq {U W : Finset V}
    (hU : U ∈ family v) (hW : W ∈ family v) : Disjoint U W ∨ U = W := by
  obtain ⟨i, rfl⟩ := exists_orbit_of_mem_family v hU
  obtain ⟨j, rfl⟩ := exists_orbit_of_mem_family v hW
  exact orbit_disjoint_or_eq v i j

/-- An opposite-valued non-self-opposite pair generates a member of the family. -/
theorem orbit_mem_family_of_opposite {i j : V}
    (hij : v i = -v j) (hni : v i ≠ -v i) : orbit v i ∈ family v := by
  apply (mem_family v).2
  refine ⟨⟨i, rfl⟩, i, self_mem_orbit v i, j, ?_, hij, hni⟩
  exact mem_orbit_symm v ((mem_orbit v).2 (Or.inr hij))

theorem orbit_mem_family_iff (i : V) :
    orbit v i ∈ family v ↔ v i ≠ -v i ∧ ∃ j, v i = -v j := by
  constructor
  · intro hi
    obtain ⟨j, hj, hij⟩ := exists_opposite_of_mem_family v hi (self_mem_orbit v i)
    exact ⟨nonself_of_mem_family v hi (self_mem_orbit v i), j, hij⟩
  · rintro ⟨hni, j, hij⟩
    exact orbit_mem_family_of_opposite v hij hni

end Families

section Signs

/-- In a two-element type, two elements different from a third one agree. -/
theorem bool_eq_of_ne_common {a b c : Bool} (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

variable (v : V → G) (σ : V → Bool)
    (hσ : ∀ i j, v i = -v j → v i ≠ -v i → σ i ≠ σ j)

include hσ

/-- An opposite witness forces equal values in a mixed orbit to have equal signs. -/
theorem sign_eq_of_value_eq {U : Finset V} {i j : V}
    (hU : U ∈ family v) (hi : i ∈ U) (hj : j ∈ U) (hij : v i = v j) :
    σ i = σ j := by
  obtain ⟨k, hk, hik⟩ := exists_opposite_of_mem_family v hU hi
  exact bool_eq_of_ne_common
    (hσ i k hik (nonself_of_mem_family v hU hi))
    (hσ j k (hij.symm.trans hik) (nonself_of_mem_family v hU hj))

theorem sign_ne_iff {U : Finset V} {i j : V}
    (hU : U ∈ family v) (hi : i ∈ U) (hj : j ∈ U) :
    σ i ≠ σ j ↔ v i = -v j := by
  constructor
  · intro hne
    rcases value_eq_or_neg_of_mem_family v hU hi hj with h | h
    · exact False.elim (hne (sign_eq_of_value_eq v σ hσ hU hi hj h))
    · exact h
  · intro hij
    exact hσ i j hij (nonself_of_mem_family v hU hi)

theorem sign_eq_iff {U : Finset V} {i j : V}
    (hU : U ∈ family v) (hi : i ∈ U) (hj : j ∈ U) :
    σ i = σ j ↔ v i = v j := by
  constructor
  · intro heq
    rcases value_eq_or_neg_of_mem_family v hU hi hj with h | h
    · exact h
    · exact False.elim (hσ i j h (nonself_of_mem_family v hU hi) heq)
  · exact sign_eq_of_value_eq v σ hσ hU hi hj

end Signs

section Entries

open scoped Classical

variable (v : V → G)

/-- Co-membership counts the unique mixed orbit, when that orbit exists. -/
theorem sum_members_eq (i j : V) :
    (∑ U ∈ family v, if i ∈ U ∧ j ∈ U then (1 : ℝ) else 0) =
      if orbit v i ∈ family v ∧ j ∈ orbit v i then 1 else 0 := by
  classical
  by_cases hi : orbit v i ∈ family v
  · rw [Finset.sum_eq_single (orbit v i)]
    · simp [hi]
    · intro U hU hne
      by_cases hiU : i ∈ U
      · exact False.elim (hne (eq_orbit_of_mem_family v hU hiU))
      · simp [hiU]
    · intro hnot
      exact False.elim (hnot hi)
  · rw [if_neg (fun h => hi h.1)]
    apply Finset.sum_eq_zero
    intro U hU
    have hiU : i ∉ U := by
      intro hit
      apply hi
      simpa only [← eq_orbit_of_mem_family v hU hit] using hU
    simp [hiU]

theorem sum_members_le_one (i j : V) :
    (∑ U ∈ family v, if i ∈ U ∧ j ∈ U then (1 : ℝ) else 0) ≤ 1 := by
  rw [sum_members_eq]
  split_ifs <;> norm_num

variable (σ : V → Bool)
    (hσ : ∀ i j, v i = -v j → v i ≠ -v i → σ i ≠ σ j)

include hσ

/-- Opposite-sign entries recover precisely the non-self-opposite pairs. -/
theorem sum_cross_entries (i j : V) :
    (∑ U ∈ family v, if i ∈ U ∧ j ∈ U ∧ σ i ≠ σ j then (1 : ℝ) else 0) =
      if v i = -v j ∧ v i ≠ -v i then 1 else 0 := by
  classical
  by_cases h : v i = -v j ∧ v i ≠ -v i
  · have hiF := orbit_mem_family_of_opposite v h.1 h.2
    have hj : j ∈ orbit v i := mem_orbit_symm v ((mem_orbit v).2 (Or.inr h.1))
    have hs := hσ i j h.1 h.2
    calc
      (∑ U ∈ family v, if i ∈ U ∧ j ∈ U ∧ σ i ≠ σ j then (1 : ℝ) else 0) =
          ∑ U ∈ family v, if i ∈ U ∧ j ∈ U then (1 : ℝ) else 0 := by
            simp [hs]
      _ = 1 := by rw [sum_members_eq]; simp [hiF, hj]
      _ = if v i = -v j ∧ v i ≠ -v i then 1 else 0 := (if_pos h).symm
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro U hU
    apply if_neg
    rintro ⟨hi, hj, hne⟩
    exact h ⟨(sign_ne_iff v σ hσ hU hi hj).1 hne, nonself_of_mem_family v hU hi⟩

/-- Equal-sign entries are bounded by the non-self-opposite equal-value kernel. -/
theorem sum_same_entries_le (i j : V) :
    (∑ U ∈ family v, if i ∈ U ∧ j ∈ U ∧ σ i = σ j then (1 : ℝ) else 0) ≤
      if v i = v j ∧ v i ≠ -v i then 1 else 0 := by
  classical
  by_cases h : v i = v j ∧ v i ≠ -v i
  · rw [if_pos h]
    calc
      (∑ U ∈ family v, if i ∈ U ∧ j ∈ U ∧ σ i = σ j then (1 : ℝ) else 0) ≤
          ∑ U ∈ family v, if i ∈ U ∧ j ∈ U then (1 : ℝ) else 0 := by
            apply Finset.sum_le_sum
            intro U hU
            by_cases hi : i ∈ U <;> by_cases hj : j ∈ U <;>
              by_cases hs : σ i = σ j <;> simp [hi, hj, hs]
      _ ≤ 1 := sum_members_le_one v i j
  · rw [if_neg h]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro U hU
    apply if_neg
    rintro ⟨hi, hj, heq⟩
    exact h ⟨(sign_eq_iff v σ hσ hU hi hj).1 heq, nonself_of_mem_family v hU hi⟩

end Entries

section PositiveSemidefinite

variable {A : Type*} [DecidableEq A]

/-- An equality kernel restricted to any collection of values is a sum of squares.
Only the finite image of the value map is used; the value type need not be finite. -/
theorem equality_kernel_eq_sum_sq (w : V → A) (p : A → Prop) [DecidablePred p]
    (z : V → ℝ) :
    (∑ i, ∑ j, z i * z j * (if w i = w j ∧ p (w i) then (1 : ℝ) else 0)) =
      ∑ a ∈ (univ.image w).filter p,
        (∑ i ∈ univ.filter (fun i => w i = a), z i) ^ 2 := by
  classical
  calc
    (∑ i, ∑ j, z i * z j * (if w i = w j ∧ p (w i) then (1 : ℝ) else 0)) =
        ∑ a ∈ univ.image w, ∑ i ∈ univ.filter (fun i => w i = a),
          ∑ j, z i * z j * (if w i = w j ∧ p (w i) then (1 : ℝ) else 0) :=
      (Finset.sum_fiberwise_of_maps_to
        (fun i _ => Finset.mem_image_of_mem w (Finset.mem_univ i)) _).symm
    _ = ∑ a ∈ univ.image w,
        if p a then (∑ i ∈ univ.filter (fun i => w i = a), z i) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hp : p a
      · rw [if_pos hp, pow_two, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hwi : w i = a := (Finset.mem_filter.1 hi).2
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hwj : w j = a
        · simp [hwi, hwj, hp]
        · simp [hwi, hp, hwj, Ne.symm hwj]
      · rw [if_neg hp]
        apply Finset.sum_eq_zero
        intro i hi
        have hwi : w i = a := (Finset.mem_filter.1 hi).2
        simp [hwi, hp]
    _ = ∑ a ∈ (univ.image w).filter p,
        (∑ i ∈ univ.filter (fun i => w i = a), z i) ^ 2 :=
      (Finset.sum_filter _ _).symm

theorem equality_kernel_nonneg (w : V → A) (p : A → Prop) [DecidablePred p]
    (z : V → ℝ) :
    0 ≤ ∑ i, ∑ j, z i * z j * (if w i = w j ∧ p (w i) then (1 : ℝ) else 0) := by
  rw [equality_kernel_eq_sum_sq]
  exact Finset.sum_nonneg (fun a _ => sq_nonneg _)

/-- The baseline kernel groups into squares over self-opposite residue classes. -/
theorem baseline_eq_sum_sq (v : V → G) (z : V → ℝ) :
    (∑ i, ∑ j, z i * z j * (if v i = v j ∧ v i = -v i then (1 : ℝ) else 0)) =
      ∑ a ∈ (univ.image v).filter (fun a => a = -a),
        (∑ i ∈ univ.filter (fun i => v i = a), z i) ^ 2 :=
  equality_kernel_eq_sum_sq v (fun a => a = -a) z

/-- Positive semidefiniteness of the self-opposite baseline kernel. -/
theorem baseline_psd (v : V → G) (z : V → ℝ) :
    0 ≤ ∑ i, ∑ j, z i * z j * (if v i = v j ∧ v i = -v i then (1 : ℝ) else 0) :=
  equality_kernel_nonneg v (fun a => a = -a) z

end PositiveSemidefinite

section Maps

variable {H : Type*} [AddCommGroup H] [DecidableEq H]
    (v : V → G) (f : G →+ H)

/-- Mapping the residues by an additive homomorphism can only enlarge an orbit. -/
theorem orbit_subset_map (i : V) :
    orbit v i ⊆ orbit (fun x => f (v x)) i := by
  intro j hj
  rcases (mem_orbit v).1 hj with h | h
  · exact (mem_orbit (fun x => f (v x))).2 (Or.inl (congrArg f h))
  · apply (mem_orbit (fun x => f (v x))).2
    right
    simpa only [map_neg] using congrArg f h

/-- Intersecting mixed orbits at two mapped levels are nested in the map direction. -/
theorem family_map_subset_of_common_mem {U W : Finset V} {i : V}
    (hU : U ∈ family v) (hW : W ∈ family (fun x => f (v x)))
    (hiU : i ∈ U) (hiW : i ∈ W) : U ⊆ W := by
  rw [eq_orbit_of_mem_family v hU hiU,
    eq_orbit_of_mem_family (fun x => f (v x)) hW hiW]
  exact orbit_subset_map v f i

theorem family_map_disjoint_or_subset {U W : Finset V}
    (hU : U ∈ family v) (hW : W ∈ family (fun x => f (v x))) :
    Disjoint U W ∨ U ⊆ W := by
  classical
  by_cases hd : Disjoint U W
  · exact Or.inl hd
  · obtain ⟨i, hiU, hiW⟩ := Finset.not_disjoint_iff.1 hd
    exact Or.inr (family_map_subset_of_common_mem v f hU hW hiU hiW)

end Maps

end

end Erdos126Orbit

end

section

/-
# Conditional negative definiteness of the additive logarithm kernel

The proof uses the power series for `-log (1 - x)`, after the change of
variables `x = (a - 1) / (a + 1)`. No distinctness assumption is needed.
-/

namespace Erdos126Log

/-- The change of variables from positive reals to the open interval `(-1, 1)`. -/
noncomputable def mobius (a : ℝ) : ℝ := (a - 1) / (a + 1)

lemma abs_mobius_lt_one {a : ℝ} (ha : 0 < a) : |mobius a| < 1 := by
  have hden : 0 < a + 1 := by linarith
  rw [mobius, abs_lt]
  constructor
  · apply (lt_div_iff₀ hden).2
    linarith
  · apply (div_lt_iff₀ hden).2
    linarith

lemma log_add_mobius {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a + b) = Real.log (a + 1) + Real.log (b + 1) - Real.log 2 +
      Real.log (1 - mobius a * mobius b) := by
  have ha1 : a + 1 ≠ 0 := ne_of_gt (by linarith)
  have hb1 : b + 1 ≠ 0 := ne_of_gt (by linarith)
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hid : 1 - mobius a * mobius b = (2 * (a + b)) / ((a + 1) * (b + 1)) := by
    unfold mobius
    field_simp [ha1, hb1]
    ring
  rw [hid, Real.log_div (mul_ne_zero htwo hab) (mul_ne_zero ha1 hb1),
    Real.log_mul htwo hab, Real.log_mul ha1 hb1]
  ring

/-- Each coefficient of the summed logarithm power series is a nonnegative square. -/
lemma log_one_sub_mul_nonpos {ι : Type*} [Fintype ι] (x c : ι → ℝ)
    (hx : ∀ i, |x i| < 1) :
    (∑ i, ∑ j, c i * c j * Real.log (1 - x i * x j)) ≤ 0 := by
  classical
  have hprod (i j : ι) : |x i * x j| < 1 := by
    rw [abs_mul]
    calc
      |x i| * |x j| ≤ 1 * |x j| :=
        mul_le_mul_of_nonneg_right (hx i).le (abs_nonneg _)
      _ < 1 := by simpa only [one_mul] using hx j
  have hs : HasSum
      (fun n : ℕ => ∑ i, ∑ j,
        c i * c j * ((x i * x j) ^ (n + 1) / ((n : ℝ) + 1)))
      (∑ i, ∑ j, c i * c j * (-Real.log (1 - x i * x j))) := by
    exact hasSum_sum (fun i _ => hasSum_sum (fun j _ =>
      (Real.hasSum_pow_div_log_of_abs_lt_one (hprod i j)).mul_left (c i * c j)))
  have hterm (n : ℕ) :
      (∑ i, ∑ j, c i * c j * ((x i * x j) ^ (n + 1) / ((n : ℝ) + 1))) =
        (∑ i, c i * x i ^ (n + 1)) ^ 2 / ((n : ℝ) + 1) := by
    rw [pow_two, Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_pow]
    ring
  have hnonneg : 0 ≤ ∑ i, ∑ j, c i * c j * (-Real.log (1 - x i * x j)) :=
    hs.nonneg (fun n => by
      rw [hterm]
      exact div_nonneg (sq_nonneg _) (Nat.cast_add_one_pos n).le)
  simpa only [mul_neg, Finset.sum_neg_distrib, neg_nonneg] using hnonneg

/-- Zero-sum coefficients annihilate kernels which separate into a row and a column term. -/
lemma sum_separable_eq_zero {ι : Type*} [Fintype ι] (c u v : ι → ℝ)
    (hc : ∑ i, c i = 0) :
    (∑ i, ∑ j, c i * c j * (u i + v j)) = 0 := by
  classical
  calc
    (∑ i, ∑ j, c i * c j * (u i + v j)) =
        (∑ i, c i * u i) * (∑ j, c j) + (∑ i, c i) * (∑ j, c j * v j) := by
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    _ = 0 := by rw [hc]; ring

/-- The additive logarithm kernel is conditionally negative definite on positive reals. -/
lemma log_add_cnd {ι : Type*} [Fintype ι] (a c : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hc : ∑ i, c i = 0) :
    (∑ i, ∑ j, c i * c j * Real.log (a i + a j)) ≤ 0 := by
  classical
  have hnonpos := log_one_sub_mul_nonpos (fun i => mobius (a i)) c
    (fun i => abs_mobius_lt_one (ha i))
  have hcancel :
      (∑ i, ∑ j, c i * c j *
        (Real.log (a i + 1) + (Real.log (a j + 1) - Real.log 2))) = 0 :=
    sum_separable_eq_zero c (fun i => Real.log (a i + 1))
      (fun j => Real.log (a j + 1) - Real.log 2) hc
  calc
    (∑ i, ∑ j, c i * c j * Real.log (a i + a j)) =
        (∑ i, ∑ j, c i * c j *
          (Real.log (a i + 1) + (Real.log (a j + 1) - Real.log 2))) +
        (∑ i, ∑ j, c i * c j * Real.log (1 - mobius (a i) * mobius (a j))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [log_add_mobius (ha i) (ha j)]
      ring
    _ ≤ 0 := by rw [hcancel, zero_add]; exact hnonpos

end Erdos126Log

end

section

/-
# Truncated prime-power counts and logarithmic factorization sums

These lemmas are independent of the other submission modules.
-/

namespace Erdos126PrimeLog

open scoped BigOperators

noncomputable section

/-- The number of positive powers of `p` with exponent at most `K` that divide `m`. -/
def countPowers (p K m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, if p ^ (k + 1) ∣ m then (1 : ℝ) else 0

theorem countPowers_nonneg (p K m : ℕ) : 0 ≤ countPowers p K m := by
  unfold countPowers
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> norm_num

/-- Truncating the count of prime powers truncates the factorization exponent. -/
theorem countPowers_eq_min (p K m : ℕ) (hp : p.Prime) (hm : m ≠ 0) :
    countPowers p K m = ((min K (m.factorization p) : ℕ) : ℝ) := by
  have hfilter : (Finset.range K).filter (fun k => k < m.factorization p) =
      Finset.range (min K (m.factorization p)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  simp only [countPowers, hp.pow_dvd_iff_le_factorization hm, Nat.add_one_le_iff,
    Finset.sum_boole]
  rw [hfilter, Finset.card_range]

theorem countPowers_le_factorization (p K m : ℕ) (hp : p.Prime) (hm : m ≠ 0) :
    countPowers p K m ≤ (m.factorization p : ℝ) := by
  rw [countPowers_eq_min p K m hp hm]
  exact_mod_cast (min_le_right K (m.factorization p))

theorem countPowers_eq_factorization (p K m : ℕ) (hp : p.Prime) (hm : m ≠ 0)
    (hK : m.factorization p ≤ K) :
    countPowers p K m = (m.factorization p : ℝ) := by
  rw [countPowers_eq_min p K m hp hm, min_eq_right hK]

/-- A finite set containing all prime factors gives the full logarithmic sum.
No primality assumption on the other elements of `S` is needed. -/
theorem sum_log_factorization_eq (S : Finset ℕ) (m : ℕ)
    (hsupp : m.primeFactors ⊆ S) :
    (∑ p ∈ S, Real.log (p : ℝ) * (m.factorization p : ℝ)) = Real.log (m : ℝ) := by
  calc
    (∑ p ∈ S, Real.log (p : ℝ) * (m.factorization p : ℝ)) =
        ∑ p ∈ m.primeFactors, Real.log (p : ℝ) * (m.factorization p : ℝ) := by
      symm
      apply Finset.sum_subset hsupp
      intro p _ hp
      have hz : m.factorization p = 0 :=
        Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using hp)
      simp only [hz, Nat.cast_zero, mul_zero]
    _ = Real.log (m : ℝ) := by
      simpa only [Finsupp.sum, Nat.support_factorization, mul_comm] using
        (Real.log_nat_eq_sum_factorization m).symm

/-- Any finite subsum of the logarithmic factorization sum is at most `log m`. -/
theorem sum_log_factorization_le (S : Finset ℕ) (m : ℕ) :
    (∑ p ∈ S, Real.log (p : ℝ) * (m.factorization p : ℝ)) ≤ Real.log (m : ℝ) := by
  calc
    (∑ p ∈ S, Real.log (p : ℝ) * (m.factorization p : ℝ)) ≤
        ∑ p ∈ S ∪ m.primeFactors, Real.log (p : ℝ) * (m.factorization p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro p _ _
      exact mul_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg _)
    _ = Real.log (m : ℝ) :=
      sum_log_factorization_eq (S ∪ m.primeFactors) m Finset.subset_union_right

theorem sum_log_count_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (K m : ℕ) (hm : m ≠ 0) :
    (∑ p ∈ S, Real.log (p : ℝ) * countPowers p K m) ≤ Real.log (m : ℝ) := by
  calc
    (∑ p ∈ S, Real.log (p : ℝ) * countPowers p K m) ≤
        ∑ p ∈ S, Real.log (p : ℝ) * (m.factorization p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left
        (countPowers_le_factorization p K m (hS p hp) hm) (Real.log_natCast_nonneg p)
    _ ≤ Real.log (m : ℝ) := sum_log_factorization_le S m

theorem sum_log_count_eq (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (K m : ℕ) (hm : m ≠ 0) (hsupp : m.primeFactors ⊆ S)
    (hK : ∀ p ∈ S, m.factorization p ≤ K) :
    (∑ p ∈ S, Real.log (p : ℝ) * countPowers p K m) = Real.log (m : ℝ) := by
  calc
    (∑ p ∈ S, Real.log (p : ℝ) * countPowers p K m) =
        ∑ p ∈ S, Real.log (p : ℝ) * (m.factorization p : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [countPowers_eq_factorization p K m (hS p hp) hm (hK p hp)]
    _ = Real.log (m : ℝ) := sum_log_factorization_eq S m hsupp

/-- A finite family has a uniform factorization cutoff for its pairwise sums on `S`. -/
theorem exists_factorization_cutoff {V : Type*} [Fintype V] (a : V → ℕ) (S : Finset ℕ) :
    ∃ K : ℕ, ∀ p ∈ S, ∀ i j : V, (a i + a j).factorization p ≤ K := by
  classical
  refine ⟨S.sup (fun p => Finset.univ.sup (fun i : V =>
    Finset.univ.sup (fun j : V => (a i + a j).factorization p))), ?_⟩
  intro p hp i j
  exact Finset.le_sup_of_le hp <|
    Finset.le_sup_of_le (Finset.mem_univ i) <|
      Finset.le_sup (f := fun j : V => (a i + a j).factorization p) (Finset.mem_univ j)

end

end Erdos126PrimeLog

end

section

/-
# Signed families at direct prime-power residue levels

At level `k`, the values are the original natural numbers modulo `p ^ (k + 1)`.
The mixed negation-orbits are tagged by their levels, so equal supports at
several levels remain distinct nodes. Their supports form a laminar family,
and every node has at least two vertices. The signs are the existing
`Erdos126PrimeCode.primeColor p (a i)`; no valuation normalization is used in
constructing the residues or the nodes.
-/

namespace Erdos126PrimeFamily

open scoped BigOperators
open Finset

noncomputable section

variable {V : Type*}

/-- The direct residue at level `k`, without removing any prime powers. -/
def residue (a : V → ℕ) (p k : ℕ) (i : V) : ZMod (p ^ (k + 1)) :=
  (a i : ZMod (p ^ (k + 1)))

/-- Negation of direct residues is equivalent to divisibility of their sum. -/
theorem residue_eq_neg_iff_dvd (a : V → ℕ) (p k : ℕ) (i j : V) :
    residue a p k i = -residue a p k j ↔ p ^ (k + 1) ∣ a i + a j := by
  simpa only [residue, Nat.cast_add, add_eq_zero_iff_eq_neg] using
    (ZMod.natCast_eq_zero_iff (a i + a j) (p ^ (k + 1)))

/-- A direct residue is self-opposite exactly when the modulus divides twice it. -/
theorem residue_eq_self_neg_iff_dvd_twice (a : V → ℕ) (p k : ℕ) (i : V) :
    residue a p k i = -residue a p k i ↔ p ^ (k + 1) ∣ 2 * a i := by
  simpa only [two_mul] using residue_eq_neg_iff_dvd a p k i i

/-- Reduction from a higher direct-residue level to a lower one. -/
@[simp] theorem castHom_residue (a : V → ℕ) (p : ℕ) {k l : ℕ} (h : k ≤ l)
    (i : V) :
    ZMod.castHom (pow_dvd_pow p (Nat.add_le_add_right h 1))
        (ZMod (p ^ (k + 1))) (residue a p l i) = residue a p k i := by
  exact map_natCast _ (a i)

/-- At every level, the prime colors separate opposite, non-self-opposite
residues. The existing prime-color bound includes the prime two. -/
theorem color_separation (a : V → ℕ) (p : ℕ) (hp : p.Prime)
    (ha : ∀ i, a i ≠ 0) (k : ℕ) :
    ∀ i j, residue a p k i = -residue a p k j →
      residue a p k i ≠ -residue a p k i →
      Erdos126PrimeCode.primeColor p (a i) ≠ Erdos126PrimeCode.primeColor p (a j) := by
  intro i j hij hni hc
  have hsum : p ^ (k + 1) ∣ a i + a j :=
    (residue_eq_neg_iff_dvd a p k i j).mp hij
  have htwice : ¬ p ^ (k + 1) ∣ 2 * a i :=
    fun h => hni ((residue_eq_self_neg_iff_dvd_twice a p k i).mpr h)
  have hsum0 : a i + a j ≠ 0 := by
    have := ha i
    omega
  have htwice0 : 2 * a i ≠ 0 := mul_ne_zero (by decide) (ha i)
  have hle := Erdos126PrimeCode.factorization_sum_le_of_color_eq hp (ha i) (ha j) hc
  exact htwice ((hp.pow_dvd_iff_le_factorization htwice0).mpr
    (((hp.pow_dvd_iff_le_factorization hsum0).mp hsum).trans hle))

variable [Fintype V]

/-- Mixed negation-orbits, with the level retained as part of each node. -/
def nodes (a : V → ℕ) (p K : ℕ) : Finset (Σ _ : ℕ, Finset V) :=
  (range K).sigma (fun k => Erdos126Orbit.family (residue a p k))

/-- The local weighted co-membership kernel, with constant weight `log p`. -/
def kernel (a : V → ℕ) (p K : ℕ) : V → V → ℝ :=
  Erdos126Kernel.familyKernel (nodes a p K) (fun t => t.2) (fun _ => Real.log p)

@[simp] theorem mem_nodes (a : V → ℕ) (p K : ℕ) {t : Σ _ : ℕ, Finset V} :
    t ∈ nodes a p K ↔ t.1 < K ∧ t.2 ∈ Erdos126Orbit.family (residue a p t.1) := by
  simp only [nodes, Finset.mem_sigma, Finset.mem_range]

/-- Every node contains at least two vertices. -/
theorem nodes_card_two_le (a : V → ℕ) (p K : ℕ) :
    ∀ t ∈ nodes a p K, 2 ≤ t.2.card := by
  intro t ht
  exact Erdos126Orbit.card_two_le_of_mem_family (residue a p t.1)
    ((mem_nodes a p K).mp ht).2

/-- At a fixed level, supports are disjoint or equal. -/
theorem family_disjoint_or_eq (a : V → ℕ) (p k : ℕ) {U W : Finset V}
    (hU : U ∈ Erdos126Orbit.family (residue a p k))
    (hW : W ∈ Erdos126Orbit.family (residue a p k)) : Disjoint U W ∨ U = W :=
  Erdos126Orbit.family_disjoint_or_eq (residue a p k) hU hW

/-- When `k ≤ l`, a support at level `l` is disjoint from, or contained in,
a support at level `k`. -/
theorem family_disjoint_or_subset (a : V → ℕ) (p : ℕ) {k l : ℕ} (h : k ≤ l)
    {U W : Finset V}
    (hU : U ∈ Erdos126Orbit.family (residue a p l))
    (hW : W ∈ Erdos126Orbit.family (residue a p k)) : Disjoint U W ∨ U ⊆ W := by
  let f : ZMod (p ^ (l + 1)) →+ ZMod (p ^ (k + 1)) :=
    (ZMod.castHom (pow_dvd_pow p (Nat.add_le_add_right h 1))
      (ZMod (p ^ (k + 1)))).toAddMonoidHom
  have hf : (fun i => f (residue a p l i)) = residue a p k := by
    funext i
    exact castHom_residue a p h i
  apply Erdos126Orbit.family_map_disjoint_or_subset (residue a p l) f hU
  simpa only [hf] using hW

/-- The supports of the level-tagged nodes are laminar. Equal supports at
different levels are allowed. -/
theorem nodes_laminar (a : V → ℕ) (p K : ℕ) :
    ∀ t ∈ nodes a p K, ∀ u ∈ nodes a p K,
      Disjoint t.2 u.2 ∨ t.2 ⊆ u.2 ∨ u.2 ⊆ t.2 := by
  intro t ht u hu
  have htF := ((mem_nodes a p K).mp ht).2
  have huF := ((mem_nodes a p K).mp hu).2
  rcases le_total t.1 u.1 with h | h
  · rcases family_disjoint_or_subset a p h huF htF with hd | hs
    · exact Or.inl hd.symm
    · exact Or.inr (Or.inr hs)
  · rcases family_disjoint_or_subset a p h htF huF with hd | hs
    · exact Or.inl hd
    · exact Or.inr (Or.inl hs)

section Entries

open scoped Classical

/-- Expanding the level tags gives the finite sum of the level kernels. -/
theorem kernel_eq_sum (a : V → ℕ) (p K : ℕ) (i j : V) :
    kernel a p K i j =
      ∑ k ∈ range K, ∑ U ∈ Erdos126Orbit.family (residue a p k),
        if i ∈ U ∧ j ∈ U then Real.log p else 0 := by
  unfold kernel Erdos126Kernel.familyKernel nodes
  exact (Finset.sum_sigma' (range K)
    (fun k => Erdos126Orbit.family (residue a p k))
    (fun _ U => if i ∈ U ∧ j ∈ U then Real.log p else 0)).symm

/-- Equivalently, `log p` multiplies the number of supporting nodes. -/
theorem kernel_eq_log_mul_sum (a : V → ℕ) (p K : ℕ) (i j : V) :
    kernel a p K i j =
      Real.log p * ∑ k ∈ range K, ∑ U ∈ Erdos126Orbit.family (residue a p k),
        if i ∈ U ∧ j ∈ U then (1 : ℝ) else 0 := by
  rw [kernel_eq_sum]
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]

/-- Opposite-color entries recover exactly the opposite, non-self-opposite
residue pairs at the chosen levels. -/
theorem kernel_cross_eq (a : V → ℕ) (p K : ℕ) (hp : p.Prime)
    (ha : ∀ i, a i ≠ 0) (i j : V) :
    (if Erdos126PrimeCode.primeColor p (a i) = Erdos126PrimeCode.primeColor p (a j)
      then 0 else kernel a p K i j) =
      Real.log p * ∑ k ∈ range K,
        if residue a p k i = -residue a p k j ∧
          residue a p k i ≠ -residue a p k i then (1 : ℝ) else 0 := by
  calc
    _ = Real.log p * ∑ k ∈ range K,
        ∑ U ∈ Erdos126Orbit.family (residue a p k),
          if i ∈ U ∧ j ∈ U ∧
            Erdos126PrimeCode.primeColor p (a i) ≠ Erdos126PrimeCode.primeColor p (a j)
            then (1 : ℝ) else 0 := by
      by_cases hc : Erdos126PrimeCode.primeColor p (a i) =
          Erdos126PrimeCode.primeColor p (a j)
      · simp [hc]
      · simpa [hc] using kernel_eq_log_mul_sum a p K i j
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      exact Erdos126Orbit.sum_cross_entries (residue a p k)
        (fun i => Erdos126PrimeCode.primeColor p (a i))
        (color_separation a p hp ha k) i j

/-- Prime logarithms give nonnegative local weights. -/
theorem log_prime_nonneg (p : ℕ) (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
  Real.log_nonneg (by exact_mod_cast hp.one_lt.le)

/-- Equal-color entries are bounded by equal, non-self-opposite residues at
the chosen levels. -/
theorem kernel_same_le (a : V → ℕ) (p K : ℕ) (hp : p.Prime)
    (ha : ∀ i, a i ≠ 0) (i j : V) :
    (if Erdos126PrimeCode.primeColor p (a i) = Erdos126PrimeCode.primeColor p (a j)
      then kernel a p K i j else 0) ≤
      Real.log p * ∑ k ∈ range K,
        if residue a p k i = residue a p k j ∧
          residue a p k i ≠ -residue a p k i then (1 : ℝ) else 0 := by
  calc
    _ = Real.log p * ∑ k ∈ range K,
        ∑ U ∈ Erdos126Orbit.family (residue a p k),
          if i ∈ U ∧ j ∈ U ∧
            Erdos126PrimeCode.primeColor p (a i) = Erdos126PrimeCode.primeColor p (a j)
            then (1 : ℝ) else 0 := by
      by_cases hc : Erdos126PrimeCode.primeColor p (a i) =
          Erdos126PrimeCode.primeColor p (a j)
      · simpa only [if_pos hc, hc, and_true] using kernel_eq_log_mul_sum a p K i j
      · simp [hc]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (log_prime_nonneg p hp)
      apply Finset.sum_le_sum
      intro k hk
      exact Erdos126Orbit.sum_same_entries_le (residue a p k)
        (fun i => Erdos126PrimeCode.primeColor p (a i))
        (color_separation a p hp ha k) i j

end Entries

/-- The local kernel has nonnegative entries. -/
theorem kernel_nonneg (a : V → ℕ) (p K : ℕ) (hp : p.Prime) (i j : V) :
    0 ≤ kernel a p K i j :=
  Erdos126Kernel.familyKernel_nonneg (nodes a p K) (fun t => t.2)
    (fun _ => Real.log p) (fun _ _ => log_prime_nonneg p hp) i j

/-- The local kernel is symmetric. -/
theorem kernel_symm (a : V → ℕ) (p K : ℕ) (i j : V) :
    kernel a p K i j = kernel a p K j i :=
  Erdos126Kernel.familyKernel_symm (nodes a p K) (fun t => t.2)
    (fun _ => Real.log p) i j

/-- Nonnegative node weights make the local family kernel positive semidefinite. -/
theorem kernel_psd (a : V → ℕ) (p K : ℕ) (hp : p.Prime) (z : V → ℝ) :
    0 ≤ Erdos126Kernel.qform (kernel a p K) z :=
  Erdos126Kernel.familyKernel_psd (nodes a p K) (fun t => t.2)
    (fun _ => Real.log p) (fun _ _ => log_prime_nonneg p hp) z

end

end Erdos126PrimeFamily

end

section

/-
# An extremal-function reduction for Erdős problem 126

This file is independent of `Submission.Spec`.  It uses the product over ordered
pairs of distinct elements, exactly as in the conjecture.  It proves positivity
of that product, existence and uniqueness of the extremal function, and attainment
of every extremal value.  The asymptotic arithmetic bound itself is not assumed
as an axiom or proved here: it appears as the hypothesis of the reduction.
-/

open Filter

namespace Erdos126Reduction

/-- The product of the pair sums over the ordered off-diagonal. -/
def sumProduct (A : Finset ℕ) : ℕ :=
  ∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)

/-- The number of distinct prime divisors of the pair-sum product. -/
def P (A : Finset ℕ) : ℕ :=
  (sumProduct A).primeFactors.card

/-- The original greatest-universal-lower-bound specification of `f`. -/
def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop :=
  ∀ n, IsGreatest
    {m | ∀ A : Finset ℕ, A.card = n → m ≤ P A}
    (f n)

/-- Distinct natural numbers have a strictly positive sum, even if one is zero. -/
theorem sum_pos_of_mem_offDiag {A : Finset ℕ} {a b : ℕ}
    (hab : (a, b) ∈ A.offDiag) : 0 < a + b := by
  have hne : a ≠ b := (Finset.mem_offDiag.mp hab).2.2
  omega

/-- In particular the product used in `P` is never zero. -/
theorem sumProduct_pos (A : Finset ℕ) : 0 < sumProduct A := by
  unfold sumProduct
  apply Finset.prod_pos
  rintro ⟨a, b⟩ hab
  exact sum_pos_of_mem_offDiag hab

theorem sumProduct_ne_zero (A : Finset ℕ) : sumProduct A ≠ 0 :=
  ne_of_gt (sumProduct_pos A)

@[simp] theorem P_empty : P ∅ = 0 := by
  simp [P, sumProduct]

@[simp] theorem P_singleton (a : ℕ) : P {a} = 0 := by
  simp [P, sumProduct, Finset.offDiag_singleton]

/-- A canonical extremal function, defined by minimizing the attained values. -/
noncomputable def extremal (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ A : Finset ℕ, A.card = n ∧ P A = m}

/-- The defining set is nonempty (use `Finset.range n`), so its natural-number
infimum is itself attained. -/
theorem extremal_attained (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ P A = extremal n := by
  have hnonempty : {m : ℕ | ∃ A : Finset ℕ, A.card = n ∧ P A = m}.Nonempty :=
    ⟨P (Finset.range n), Finset.range n, Finset.card_range n, rfl⟩
  exact Nat.sInf_mem hnonempty

/-- The canonical extremal value is a lower bound for every set of that size. -/
theorem extremal_le {n : ℕ} {A : Finset ℕ} (hA : A.card = n) :
    extremal n ≤ P A := by
  exact Nat.sInf_le ⟨A, hA, rfl⟩

/-- The attained minimum satisfies the original `IsGreatest` specification. -/
theorem extremal_spec : IsMaximalAddFactorsCard extremal := by
  intro n
  refine ⟨fun A hA => extremal_le hA, ?_⟩
  intro m hm
  obtain ⟨A, hA, hP⟩ := extremal_attained n
  simpa only [hP] using hm A hA

/-- Any two functions satisfying the specification agree everywhere. -/
theorem spec_unique {f g : ℕ → ℕ}
    (hf : IsMaximalAddFactorsCard f) (hg : IsMaximalAddFactorsCard g) : f = g := by
  funext n
  exact (hf n).unique (hg n)

theorem exists_spec : ∃ f : ℕ → ℕ, IsMaximalAddFactorsCard f :=
  ⟨extremal, extremal_spec⟩

theorem existsUnique_spec : ∃! f : ℕ → ℕ, IsMaximalAddFactorsCard f := by
  refine ⟨extremal, extremal_spec, ?_⟩
  intro f hf
  exact spec_unique hf extremal_spec

/-- Attainment for an arbitrary function satisfying the original specification. -/
theorem attained {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f) (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ P A = f n := by
  rw [spec_unique hf extremal_spec]
  exact extremal_attained n

/-- The lower-bound half of the specification, indexed by the actual cardinality. -/
theorem le_P {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f) (A : Finset ℕ) :
    f A.card ≤ P A :=
  (hf A.card).1 A rfl

/-- The logarithmic denominator vanishes at these small sizes, which are excluded
by the thresholds in the asymptotic reduction. -/
theorem spec_zero {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f) : f 0 = 0 := by
  have h := le_P hf ∅
  simpa using h

theorem spec_one {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f) : f 1 = 0 := by
  have h := le_P hf {0}
  simpa using h

/-- The actual universally quantified asymptotic conjecture. -/
def Conjecture : Prop :=
  ∀ f : ℕ → ℕ, IsMaximalAddFactorsCard f →
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop

/-- The uniform arithmetic lower bound sufficient for the conjecture. -/
def UniformBound : Prop :=
  ∀ C : ℝ, ∃ N : ℕ, ∀ A : Finset ℕ, N ≤ A.card →
    C * Real.log (A.card : ℝ) ≤ (P A : ℝ)

/-- An equivalent version that explicitly avoids cardinalities zero and one. -/
def UniformBoundFromTwo : Prop :=
  ∀ C : ℝ, ∃ N : ℕ, 2 ≤ N ∧ ∀ A : Finset ℕ, N ≤ A.card →
    C * Real.log (A.card : ℝ) ≤ (P A : ℝ)

/-- Increasing a threshold to `max N 2` does not change the uniform bound. -/
theorem uniformBound_iff_fromTwo : UniformBound ↔ UniformBoundFromTwo := by
  constructor
  · intro h C
    obtain ⟨N, hN⟩ := h C
    refine ⟨max N 2, le_max_right N 2, ?_⟩
    intro A hA
    exact hN A ((le_max_left N 2).trans hA)
  · intro h C
    obtain ⟨N, _, hN⟩ := h C
    exact ⟨N, hN⟩

/-- Division by `log n` is order-preserving once `n ≥ 2`. -/
theorem log_nat_pos {n : ℕ} (hn : 2 ≤ n) : 0 < Real.log (n : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < n by omega)

/-- The uniform bound applies to an attaining set at each cardinality, so it
forces every specified extremal function to grow faster than `log n`. -/
theorem tendsto_of_uniformBound {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f)
    (h : UniformBound) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro C
  obtain ⟨N, hNtwo, hN⟩ := uniformBound_iff_fromTwo.mp h C
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨A, hcard, hP⟩ := attained hf n
  have hbound := hN A (by simpa only [hcard] using hn)
  rw [hcard, hP] at hbound
  exact (le_div_iff₀ (log_nat_pos (hNtwo.trans hn))).mpr hbound

/-- Conversely, the limit gives a bound for `f(A.card)`, which is a lower bound
for `P A`.  The threshold is explicitly at least two. -/
theorem uniformBoundFromTwo_of_tendsto {f : ℕ → ℕ}
    (hf : IsMaximalAddFactorsCard f)
    (h : Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop) :
    UniformBoundFromTwo := by
  intro C
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp h C
  refine ⟨max N 2, le_max_right N 2, ?_⟩
  intro A hA
  have hlog : 0 < Real.log (A.card : ℝ) :=
    log_nat_pos ((le_max_right N 2).trans hA)
  have hratio := hN A.card ((le_max_left N 2).trans hA)
  have hbound : C * Real.log (A.card : ℝ) ≤ (f A.card : ℝ) :=
    (le_div_iff₀ hlog).mp hratio
  exact hbound.trans (Nat.cast_le.mpr (le_P hf A))

theorem uniformBound_of_tendsto {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f)
    (h : Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop) :
    UniformBound :=
  uniformBound_iff_fromTwo.mpr (uniformBoundFromTwo_of_tendsto hf h)

/-- Equivalence for any function satisfying the greatest-lower-bound specification. -/
theorem tendsto_iff_uniformBound {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop ↔
      UniformBound :=
  ⟨uniformBound_of_tendsto hf, tendsto_of_uniformBound hf⟩

theorem tendsto_iff_uniformBoundFromTwo {f : ℕ → ℕ}
    (hf : IsMaximalAddFactorsCard f) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop ↔
      UniformBoundFromTwo :=
  (tendsto_iff_uniformBound hf).trans uniformBound_iff_fromTwo

/-- Existence of `extremal` makes the entire conjecture equivalent to the uniform
bound, not merely an implication with a possibly vacuous specification. -/
theorem conjecture_iff_uniformBound : Conjecture ↔ UniformBound := by
  constructor
  · intro h
    exact uniformBound_of_tendsto extremal_spec (h extremal extremal_spec)
  · intro h f hf
    exact tendsto_of_uniformBound hf h

/-- The same full equivalence with all thresholds constrained to be at least two. -/
theorem conjecture_iff_uniformBoundFromTwo : Conjecture ↔ UniformBoundFromTwo :=
  conjecture_iff_uniformBound.trans uniformBound_iff_fromTwo

/-- It also suffices to state the limit for the explicitly constructed function. -/
theorem conjecture_iff_extremal_tendsto : Conjecture ↔
    Tendsto (fun n : ℕ => (extremal n : ℝ) / Real.log (n : ℝ)) atTop atTop :=
  conjecture_iff_uniformBound.trans (tendsto_iff_uniformBound extremal_spec).symm

end Erdos126Reduction

end

section

/-
# The quadratic prime-support bound

The prime-power mixed-orbit families split the sum kernel into a cross kernel
and a positive semidefinite self-opposite baseline.  The logarithm of the full
sum kernel is conditionally negative semidefinite.  Comparing sums with positive
absolute differences gives the strict separation required by the signed-family
bound.  Removing zero then yields a uniform quadratic cardinality bound.
-/

open scoped BigOperators
open Finset

namespace Erdos126Arithmetic

noncomputable section

open Erdos126Kernel Erdos126PrimeFamily Erdos126PrimeLog

variable {V : Type*} [Fintype V]

/-- Self-opposite residue classes give the baseline at one prime-power level. -/
def baselineLevel (a : V → ℕ) (p k : ℕ) (i j : V) : ℝ :=
  if residue a p k i = residue a p k j ∧
    residue a p k i = -residue a p k i then 1 else 0

/-- The weighted, truncated baseline at a single prime. -/
def localBaseline (a : V → ℕ) (p K : ℕ) (i j : V) : ℝ :=
  Real.log p * ∑ k ∈ range K, baselineLevel a p k i j

/-- The cross kernel indexed by the chosen primes. -/
def C (a : V → ℕ) (S : Finset ℕ) (K : ℕ) : V → V → ℝ :=
  crossKernel (fun p : S => kernel a p K)
    (fun p i => Erdos126PrimeCode.primeColor p (a i))

/-- The retained same-side kernel. -/
def R (a : V → ℕ) (S : Finset ℕ) (K : ℕ) : V → V → ℝ :=
  sameKernel (fun p : S => kernel a p K)
    (fun p i => Erdos126PrimeCode.primeColor p (a i))

/-- The baseline summed over all chosen primes. -/
def B (a : V → ℕ) (S : Finset ℕ) (K : ℕ) (i j : V) : ℝ :=
  ∑ p : S, localBaseline a p K i j

omit [Fintype V] in
lemma residue_eq_iff_dvd_dist (a : V → ℕ) (p k : ℕ) (i j : V) :
    residue a p k i = residue a p k j ↔ p ^ (k + 1) ∣ Nat.dist (a i) (a j) := by
  by_cases h : a i ≤ a j
  · rw [Nat.dist_eq_sub_of_le h]
    simpa only [Nat.cast_sub h, sub_eq_zero, residue, eq_comm] using
      (ZMod.natCast_eq_zero_iff (a j - a i) (p ^ (k + 1)))
  · have h' : a j ≤ a i := by omega
    rw [Nat.dist_eq_sub_of_le_right h']
    simpa only [Nat.cast_sub h', sub_eq_zero, residue] using
      (ZMod.natCast_eq_zero_iff (a i - a j) (p ^ (k + 1)))

omit [Fintype V] in
lemma cross_add_baselineLevel (a : V → ℕ) (p k : ℕ) (i j : V) :
    (if residue a p k i = -residue a p k j ∧
        residue a p k i ≠ -residue a p k i then (1 : ℝ) else 0) +
      baselineLevel a p k i j =
      if p ^ (k + 1) ∣ a i + a j then 1 else 0 := by
  simp only [← residue_eq_neg_iff_dvd]
  unfold baselineLevel
  by_cases hs : residue a p k i = -residue a p k i
  · have he : residue a p k i = -residue a p k j ↔
        residue a p k i = residue a p k j := by
      constructor
      · intro h
        have h' := congrArg Neg.neg h
        simpa only [neg_neg, ← hs] using h'
      · intro h
        simpa only [← h] using hs
    rw [if_neg (fun h => h.2 hs)]
    have hb : (residue a p k i = residue a p k j ∧
        residue a p k i = -residue a p k i) ↔
        residue a p k i = -residue a p k j :=
      ⟨fun h => he.mpr h.1, fun h => ⟨he.mp h, hs⟩⟩
    simp only [hb, zero_add]
  · have hb : ¬ (residue a p k i = residue a p k j ∧
        residue a p k i = -residue a p k i) := fun h => hs h.2
    rw [if_neg hb]
    simp only [and_iff_left hs, add_zero]

omit [Fintype V] in
lemma same_add_baselineLevel (a : V → ℕ) (p k : ℕ) (i j : V) :
    (if residue a p k i = residue a p k j ∧
        residue a p k i ≠ -residue a p k i then (1 : ℝ) else 0) +
      baselineLevel a p k i j =
      if p ^ (k + 1) ∣ Nat.dist (a i) (a j) then 1 else 0 := by
  simp only [← residue_eq_iff_dvd_dist]
  unfold baselineLevel
  by_cases hs : residue a p k i = -residue a p k i
  · rw [if_neg (fun h => h.2 hs)]
    simp only [and_iff_left hs, zero_add]
  · have hb : ¬ (residue a p k i = residue a p k j ∧
        residue a p k i = -residue a p k i) := fun h => hs h.2
    rw [if_neg hb]
    simp only [and_iff_left hs, add_zero]

lemma local_cross_add_baseline (a : V → ℕ) (p K : ℕ) (hp : p.Prime)
    (ha : ∀ i, a i ≠ 0) (i j : V) :
    (if Erdos126PrimeCode.primeColor p (a i) =
        Erdos126PrimeCode.primeColor p (a j) then 0 else kernel a p K i j) +
      localBaseline a p K i j = Real.log p * countPowers p K (a i + a j) := by
  rw [kernel_cross_eq a p K hp ha]
  unfold localBaseline countPowers
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro k hk
  exact cross_add_baselineLevel a p k i j

lemma local_same_add_baseline_le (a : V → ℕ) (p K : ℕ) (hp : p.Prime)
    (ha : ∀ i, a i ≠ 0) (i j : V) :
    (if Erdos126PrimeCode.primeColor p (a i) =
        Erdos126PrimeCode.primeColor p (a j) then kernel a p K i j else 0) +
      localBaseline a p K i j ≤
      Real.log p * countPowers p K (Nat.dist (a i) (a j)) := by
  calc
    _ ≤ (Real.log p * ∑ k ∈ range K,
        if residue a p k i = residue a p k j ∧
          residue a p k i ≠ -residue a p k i then (1 : ℝ) else 0) +
        localBaseline a p K i j :=
      add_le_add (kernel_same_le a p K hp ha i j) le_rfl
    _ = _ := by
      unfold localBaseline countPowers
      rw [← mul_add, ← sum_add_distrib]
      congr 1
      apply sum_congr rfl
      intro k hk
      exact same_add_baselineLevel a p k i j

lemma qform_smul (c : ℝ) (M : V → V → ℝ) (z : V → ℝ) :
    qform (fun i j => c * M i j) z = c * qform M z := by
  unfold qform
  simp only [mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

lemma localBaseline_psd (a : V → ℕ) (p K : ℕ) (z : V → ℝ) :
    0 ≤ qform (localBaseline a p K) z := by
  unfold localBaseline
  rw [qform_smul, qform_sum]
  apply mul_nonneg (Real.log_natCast_nonneg p)
  apply sum_nonneg
  intro k hk
  exact Erdos126Orbit.baseline_psd (residue a p k) z

lemma B_psd (a : V → ℕ) (S : Finset ℕ) (K : ℕ) (z : V → ℝ) :
    0 ≤ qform (B a S K) z := by
  unfold B
  rw [qform_sum]
  exact sum_nonneg (fun p _ => localBaseline_psd a p K z)

/-- Cross cancellation plus the baseline counts all supported prime powers. -/
lemma C_add_B_eq_sum (a : V → ℕ) (S : Finset ℕ) (K : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ i, a i ≠ 0) (i j : V) :
    C a S K i j + B a S K i j =
      ∑ p ∈ S, Real.log p * countPowers p K (a i + a j) := by
  unfold C B crossKernel
  rw [← sum_add_distrib]
  calc
    _ = ∑ p : S, Real.log (p : ℕ) * countPowers p K (a i + a j) := by
      apply sum_congr rfl
      intro p hp
      exact local_cross_add_baseline a p K (hS p p.property) ha i j
    _ = _ := sum_coe_sort S (fun p : ℕ => Real.log (p : ℝ) * countPowers p K (a i + a j))

lemma C_add_B_eq_log (a : V → ℕ) (S : Finset ℕ) (K : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ i, a i ≠ 0)
    (hsupp : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S)
    (hK : ∀ p ∈ S, ∀ i j, (a i + a j).factorization p ≤ K)
    (i j : V) (hij : i ≠ j) :
    C a S K i j + B a S K i j = Real.log (a i + a j : ℕ) := by
  rw [C_add_B_eq_sum a S K hS ha]
  exact sum_log_count_eq S hS K (a i + a j) (by have := ha i; omega)
    (hsupp i j hij) (fun p hp => hK p hp i j)

omit [Fintype V] in
lemma B_diag_le (a : V → ℕ) (S : Finset ℕ) (K : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ i, a i ≠ 0) (i : V) :
    B a S K i i ≤ Real.log (2 * a i : ℕ) := by
  have heq : B a S K i i =
      ∑ p ∈ S, Real.log p * countPowers p K (2 * a i) := by
    unfold B localBaseline baselineLevel countPowers
    simp only [true_and, residue_eq_self_neg_iff_dvd_twice]
    exact sum_coe_sort S (fun p : ℕ => Real.log (p : ℝ) *
      ∑ k ∈ range K, if p ^ (k + 1) ∣ 2 * a i then (1 : ℝ) else 0)
  rw [heq]
  exact sum_log_count_le S hS K (2 * a i) (mul_ne_zero (by decide) (ha i))

lemma R_add_B_le_log_dist (a : V → ℕ) (S : Finset ℕ) (K : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ i, a i ≠ 0)
    (i j : V) (hij : a i ≠ a j) :
    R a S K i j + B a S K i j ≤ Real.log (Nat.dist (a i) (a j) : ℕ) := by
  unfold R B sameKernel
  rw [← sum_add_distrib]
  calc
    _ ≤ ∑ p : S, Real.log (p : ℕ) * countPowers p K (Nat.dist (a i) (a j)) := by
      apply sum_le_sum
      intro p hp
      exact local_same_add_baseline_le a p K (hS p p.property) ha i j
    _ = ∑ p ∈ S, Real.log p * countPowers p K (Nat.dist (a i) (a j)) :=
      sum_coe_sort S (fun p : ℕ => Real.log (p : ℝ) * countPowers p K (Nat.dist (a i) (a j)))
    _ ≤ _ := sum_log_count_le S hS K _ (Nat.dist_pos_of_ne hij).ne'

/-- Conditional negativity survives subtracting the baseline and the missing
nonnegative diagonal prime contributions. -/
lemma C_cnd (a : V → ℕ) (S : Finset ℕ) (K : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ i, a i ≠ 0)
    (hsupp : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S)
    (hK : ∀ p ∈ S, ∀ i j, (a i + a j).factorization p ≤ K) :
    CND (C a S K) := by
  intro z hz
  have hlog := Erdos126Log.log_add_cnd (fun i => (a i : ℝ)) z
    (fun i => by dsimp; exact_mod_cast Nat.pos_of_ne_zero (ha i)) hz
  have hbase := B_psd a S K z
  have hineq : qform (C a S K) z + qform (B a S K) z ≤
      ∑ i, ∑ j, z i * z j * Real.log ((a i : ℝ) + (a j : ℝ)) := by
    calc
      _ = ∑ i, ∑ j, z i * z j * (C a S K i j + B a S K i j) := by
        simp only [qform, mul_add, sum_add_distrib]
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        apply sum_le_sum
        intro j hj
        by_cases he : i = j
        · subst j
          have hb : B a S K i i ≤ Real.log ((a i : ℝ) + (a i : ℝ)) := by
            simpa only [Nat.cast_mul, Nat.cast_ofNat, two_mul, Nat.cast_add] using B_diag_le a S K hS ha i
          have hc : C a S K i i = 0 := crossKernel_diag _ _ i
          rw [hc, zero_add]
          exact mul_le_mul_of_nonneg_left hb (mul_self_nonneg _)
        · rw [C_add_B_eq_log a S K hS ha hsupp hK i j he]
          simp only [Nat.cast_add, le_refl]
  linarith

/-- A positive pair sum is larger than the absolute difference, even after
retaining only the chosen prime powers of the difference. -/
lemma R_lt_C (a : V → ℕ) (S : Finset ℕ) (K : ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ i, a i ≠ 0)
    (hinj : Function.Injective a)
    (hsupp : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S)
    (hK : ∀ p ∈ S, ∀ i j, (a i + a j).factorization p ≤ K)
    (i j : V) (hij : i ≠ j) : R a S K i j < C a S K i j := by
  have hne : a i ≠ a j := fun h => hij (hinj h)
  have hdpos : 0 < Nat.dist (a i) (a j) := Nat.dist_pos_of_ne hne
  have hdlt : Nat.dist (a i) (a j) < a i + a j := by
    have hi := ha i
    have hj := ha j
    unfold Nat.dist
    omega
  have hlog : Real.log (Nat.dist (a i) (a j) : ℕ) < Real.log (a i + a j : ℕ) :=
    Real.log_lt_log (by exact_mod_cast hdpos) (by exact_mod_cast hdlt)
  have hsame := R_add_B_le_log_dist a S K hS ha i j hne
  have hcross := C_add_B_eq_log a S K hS ha hsupp hK i j hij
  linarith

/-- The quadratic bound for a positive injectively indexed set whose restricted
pair sums are supported on `S`. -/
theorem card_le_three_sq (a : V → ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (ha : ∀ i, a i ≠ 0)
    (hinj : Function.Injective a) (hn : 2 ≤ Fintype.card V)
    (hsupp : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S) :
    Fintype.card V ≤ 3 * S.card ^ 2 := by
  obtain ⟨K, hK⟩ := exists_factorization_cutoff a S
  have h := signed_family_card_bound
    (fun p : S => nodes a p K) (fun _ t => t.2) (fun p _ => Real.log (p : ℕ))
    (fun p i => Erdos126PrimeCode.primeColor p (a i)) hn
    (fun p _ _ => Real.log_natCast_nonneg p)
    (fun p => nodes_card_two_le a p K)
    (fun p => nodes_laminar a p K)
    (C_cnd a S K hS ha hsupp hK)
    (R_lt_C a S K hS ha hinj hsupp hK)
  have h' : (Fintype.card V : ℝ) ≤ 3 * (S.card : ℝ) ^ 2 := by
    simpa only [Fintype.card_coe] using h
  exact_mod_cast h'

/-- The uniform quadratic bound, including the harmless small sets and a
possible vertex zero. -/
theorem quadraticBound (A : Finset ℕ) :
    A.card ≤ 3 * (Erdos126Reduction.P A) ^ 2 + 2 := by
  classical
  let S := (Erdos126Reduction.sumProduct A).primeFactors
  change A.card ≤ 3 * S.card ^ 2 + 2
  have hcard : A.card ≤ (A.erase 0).card + 1 := by
    by_cases hzero : 0 ∈ A
    · exact (card_erase_add_one hzero).ge
    · rw [erase_eq_of_notMem hzero]
      omega
  by_cases hn : 2 ≤ (A.erase 0).card
  · have h : (A.erase 0).card ≤ 3 * S.card ^ 2 := by
      have hc := card_le_three_sq (fun i : A.erase 0 => (i : ℕ)) S
        (fun p hp => Nat.prime_of_mem_primeFactors hp)
        (fun i => (mem_erase.mp i.property).1)
        Subtype.val_injective (by simpa only [Fintype.card_coe] using hn)
        (by
          intro i j hij p hp
          have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Subtype.ext h)
          have hprime := Nat.mem_primeFactors.mp hp
          exact Erdos126PrimeCode.prime_mem_sumProduct
            (mem_of_mem_erase i.property) (mem_of_mem_erase j.property)
            hne hprime.1 hprime.2.1)
      simpa only [Fintype.card_coe] using hc
    omega
  · omega

end

end Erdos126Arithmetic

end

section

/-
# The analytic consequence of a quadratic bound for Erdős problem 126

The arithmetic inequality is an explicit hypothesis.  Since `log n ^ 2 = o(n)`,
it implies the uniform lower bound from `Submission.Reduction`, and hence the
required limit for every function satisfying the original extremal specification.
-/

open Filter
open scoped Topology

namespace Erdos126Limit

open Erdos126Reduction

/-- The quadratic cardinality bound implies the uniform logarithmic lower bound.
Squaring the real constant treats positive and negative constants uniformly. -/
theorem uniformBound_of_quadratic
    (h : ∀ A : Finset ℕ, A.card ≤ 3 * (P A) ^ 2 + 2) : UniformBound := by
  intro C
  have hlim : Tendsto
      (fun n : ℕ => 3 * (C * Real.log (n : ℝ)) ^ 2 / ((n : ℝ) - 2))
      atTop (𝓝 0) := by
    have hlog :=
      ((Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 2 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).const_mul
          (3 * C ^ 2)
    simpa only [Function.comp_def, one_mul, sub_eq_add_neg, mul_zero, mul_pow,
      mul_assoc, mul_div_assoc] using hlog
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const zero_lt_one)
  refine ⟨max N 3, ?_⟩
  intro A hA
  have hlarge : 3 ≤ A.card := (le_max_right N 3).trans hA
  have hdenom : 0 < (A.card : ℝ) - 2 := by
    have hthree : (3 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hlarge
    linarith
  have hsmall : 3 * (C * Real.log (A.card : ℝ)) ^ 2 < (A.card : ℝ) - 2 := by
    have hx := (div_lt_iff₀ hdenom).mp (hN A.card ((le_max_left N 3).trans hA))
    simpa only [one_mul] using hx
  have hquad : (A.card : ℝ) ≤ 3 * (P A : ℝ) ^ 2 + 2 := by
    exact_mod_cast h A
  apply le_of_sq_le_sq _ (Nat.cast_nonneg (P A))
  nlinarith only [hquad, hsmall]

/-- Apply the existing extremal-function reduction to the quadratic bound. -/
theorem tendsto_of_quadratic {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f)
    (h : ∀ A : Finset ℕ, A.card ≤ 3 * (P A) ^ 2 + 2) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop :=
  tendsto_of_uniformBound hf (uniformBound_of_quadratic h)

/-- The quadratic bound suffices for the universally quantified conjecture. -/
theorem conjecture_of_quadratic
    (h : ∀ A : Finset ℕ, A.card ≤ 3 * (P A) ^ 2 + 2) : Conjecture := by
  intro f hf
  exact tendsto_of_quadratic hf h

end Erdos126Limit

end

namespace Erdos126

/--
Let $f(n)$ be maximal such that if $A\subseteq\mathbb{N}$ has $|A| = n$ then
$\prod_{a\neq b\in A}(a + b)$ has at least $f(n)$ distinct prime factors.
Is it true that $\frac{f(n)}{\log n} \to\infty$?
-/
theorem erdos_126 : ∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f →
    Tendsto (fun n => f n / Real.log n) atTop atTop := by
  intro f hf
  exact Erdos126Limit.tendsto_of_quadratic hf Erdos126Arithmetic.quadraticBound

end Erdos126

theorem Erdos126.erdos_126.disproof : ¬ (type_of% @Erdos126.erdos_126) := sorry
