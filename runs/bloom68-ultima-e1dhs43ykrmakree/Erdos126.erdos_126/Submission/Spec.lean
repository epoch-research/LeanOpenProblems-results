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

/-
## Proof architecture

The proof gives the stronger uniform bound
`A.card ≤ 1024 * (s + 1)^8` for positive finite sets, where `s` is the
number of primes dividing their off-diagonal sums.

Prime-power cancellation gives weighted laminar opposition families. Their
signed Gram kernel has strictly negative off-diagonal entries, while the
opposition kernel is conditionally negative semidefinite. A finite energy
estimate, laminar pruning, and an almost-obtuse sign-vector bound give the
polynomial cardinality bound. Removing zero and taking the attained extremal
minimum then yields the stated limit.
-/

/-
Independent checks for Erdős problem 126. These establish only the precise
meaning, existence, uniqueness, and monotonicity of the minimum in the statement,
not the conjectural asymptotic. Neither theorem from Spec.lean is imported.
-/

namespace Independent126

open Filter

-- This is the definition from Spec.lean, copied without importing either conjectural theorem.
def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop := ∀ n,
    IsGreatest
      { m | ∀ (A : Finset ℕ), A.card = n →
        m ≤ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card}
      (f n)

def factorCount (A : Finset ℕ) : ℕ :=
  (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card

theorem offDiag_product_pos (A : Finset ℕ) :
    0 < ∏ ⟨a, b⟩ ∈ A.offDiag, (a + b) := by
  apply Finset.prod_pos
  intro p hp
  have hne := (Finset.mem_offDiag.mp hp).2.2
  rcases p with ⟨a, b⟩
  dsimp at *
  omega

-- In particular the ordered product has exactly the intended union of prime supports.
theorem prime_mem_iff (A : Finset ℕ) (p : ℕ) :
    p ∈ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors ↔
    p.Prime ∧ ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ p ∣ a + b := by
  rw [Nat.mem_primeFactors_of_ne_zero (ne_of_gt (offDiag_product_pos A))]
  constructor
  · rintro ⟨hp, hdiv⟩
    obtain ⟨⟨a, b⟩, hab, hdiv⟩ :=
      (hp.prime.dvd_finset_prod_iff (fun q : ℕ × ℕ => q.1 + q.2)).mp hdiv
    obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
    exact ⟨hp, a, ha, b, hb, hne, hdiv⟩
  · rintro ⟨hp, a, ha, b, hb, hne, hdiv⟩
    exact ⟨hp, (hp.prime.dvd_finset_prod_iff (fun q : ℕ × ℕ => q.1 + q.2)).mpr
      ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hne⟩, hdiv⟩⟩

theorem factorCount_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    factorCount A ≤ factorCount B := by
  apply Finset.card_le_card
  intro p hp
  rw [prime_mem_iff] at hp ⊢
  obtain ⟨hprime, a, ha, b, hb, hne, hdiv⟩ := hp
  exact ⟨hprime, a, hAB ha, b, hAB hb, hne, hdiv⟩


theorem factorCount_attains (n : ℕ) :
    ∃ m, ∃ A : Finset ℕ, A.card = n ∧ factorCount A = m :=
  ⟨factorCount (Finset.range n), Finset.range n, Finset.card_range n, rfl⟩

noncomputable def minimum (n : ℕ) : ℕ := by
  classical
  exact Nat.find (factorCount_attains n)

theorem minimum_is_maximal : IsMaximalAddFactorsCard minimum := by
  classical
  intro n
  constructor
  · intro A hA
    exact Nat.find_min' (factorCount_attains n) ⟨A, hA, rfl⟩
  · intro m hm
    obtain ⟨A, hA, hmin⟩ := Nat.find_spec (factorCount_attains n)
    have hbound := hm A hA
    change m ≤ factorCount A at hbound
    change m ≤ minimum n
    simpa only [minimum, hmin] using hbound

theorem maximal_unique {f g : ℕ → ℕ}
    (hf : IsMaximalAddFactorsCard f) (hg : IsMaximalAddFactorsCard g) : f = g := by
  funext n
  exact le_antisymm ((hg n).2 (hf n).1) ((hf n).2 (hg n).1)

theorem exists_maximal : ∃ f, IsMaximalAddFactorsCard f :=
  ⟨minimum, minimum_is_maximal⟩

theorem maximal_attained {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f) (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ factorCount A = f n := by
  classical
  rw [maximal_unique hf minimum_is_maximal]
  exact Nat.find_spec (factorCount_attains n)

theorem maximal_monotone {f : ℕ → ℕ} (hf : IsMaximalAddFactorsCard f) :
    Monotone f := by
  intro m n hmn
  apply (hf n).2
  intro A hA
  obtain ⟨B, hBA, hB⟩ := Finset.exists_subset_card_eq (hmn.trans_eq hA.symm)
  exact ((hf m).1 B hB).trans (factorCount_mono hBA)

theorem two_unit_equation (a u v : ℕ) (huv : u ≠ v) :
    ((a : ℚ) + v) / ((v : ℚ) - u) -
      ((a : ℚ) + u) / ((v : ℚ) - u) = 1 := by
  have hne : (v : ℚ) - u ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast Ne.symm huv)
  field_simp
  ring

theorem real_division_exact (f : ℕ → ℕ) :
    Tendsto (fun n => f n / Real.log n) atTop atTop ↔
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop := Iff.rfl


end Independent126

/-
# A binary-signature bound for Erdős problem 126

For a finite set of positive natural numbers, the number of elements is at most
`2 ^ S.card`, where `S` is the prime support of the ordered off-diagonal product
of pair sums. The color at an odd prime records the half containing the nonzero
residue of the prime-free part; at two it records the odd part modulo four.

Equal colors at all primes dividing a pair sum force that sum to divide twice
either entry, and hence force the entries to be equal. This is only an
exponential cardinality bound, not the conjectural superlogarithmic bound.
Neither statement from `Submission.Spec` is imported.
-/

namespace Signature126

/-- The exact prime support in the problem, including both orders of each pair. -/
def primeSupport (A : Finset ℕ) : Finset ℕ :=
  (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors

/-- A single bit at each prime. The exceptional bit at two uses modulus four. -/
def primeColor (p a : ℕ) : Bool :=
  if p = 2 then decide (ordCompl[2] a % 4 = 1)
  else decide (ordCompl[p] a % p ≤ p / 2)

private theorem same_half_not_dvd_add {p u v : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hu : ¬p ∣ u) (hv : ¬p ∣ v)
    (hc : decide (u % p ≤ p / 2) = decide (v % p ≤ p / 2)) :
    ¬p ∣ u + v := by
  intro hd
  have hru := Nat.mod_lt u hp.pos
  have hrv := Nat.mod_lt v hp.pos
  have hru0 : u % p ≠ 0 := fun h => hu (Nat.dvd_of_mod_eq_zero h)
  have hrv0 : v % p ≠ 0 := fun h => hv (Nat.dvd_of_mod_eq_zero h)
  have hsum : (u % p + v % p) % p = 0 := by
    rw [← Nat.add_mod]
    exact Nat.mod_eq_zero_of_dvd hd
  have hsum' : u % p + v % p = p := by
    by_cases hlt : u % p + v % p < p
    · rw [Nat.mod_eq_of_lt hlt] at hsum
      omega
    · rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt hlt),
        Nat.mod_eq_of_lt (show u % p + v % p - p < p by omega)] at hsum
      omega
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hiff := decide_eq_decide.mp hc
  omega

private theorem same_mod_four_not_four_dvd_add {u v : ℕ}
    (hu : ¬2 ∣ u) (hv : ¬2 ∣ v)
    (hc : decide (u % 4 = 1) = decide (v % 4 = 1)) :
    ¬4 ∣ u + v := by
  have hu0 : u % 2 ≠ 0 := fun h => hu (Nat.dvd_of_mod_eq_zero h)
  have hv0 : v % 2 ≠ 0 := fun h => hv (Nat.dvd_of_mod_eq_zero h)
  have hiff := decide_eq_decide.mp hc
  intro hd
  have hmod := Nat.mod_eq_zero_of_dvd hd
  omega

/-- Matching colors bound the valuation of the sum of the prime-free parts.
At odd primes it is zero; at two it is at most one. -/
theorem ordCompl_sum_factorization_le {p a b : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hc : primeColor p a = primeColor p b) :
    (ordCompl[p] a + ordCompl[p] b).factorization p ≤ (2 : ℕ).factorization p := by
  have hua := Nat.not_dvd_ordCompl hp ha.ne'
  have hub := Nat.not_dvd_ordCompl hp hb.ne'
  by_cases hp2 : p = 2
  · subst p
    have hc' : decide (ordCompl[2] a % 4 = 1) =
        decide (ordCompl[2] b % 4 = 1) := by
      simpa [primeColor] using hc
    have hnot := same_mod_four_not_four_dvd_add hua hub hc'
    have hnonzero : ordCompl[2] a + ordCompl[2] b ≠ 0 := by
      have := Nat.ordCompl_pos 2 ha.ne'
      omega
    have hle : (ordCompl[2] a + ordCompl[2] b).factorization 2 ≤ 1 := by
      by_contra h
      have hfac : 2 ≤ (ordCompl[2] a + ordCompl[2] b).factorization 2 := by omega
      have hd := (Nat.prime_two.pow_dvd_iff_le_factorization hnonzero).2 hfac
      exact hnot (by simpa using hd)
    simpa only [Nat.prime_two.factorization_self] using hle
  · have hc' : decide (ordCompl[p] a % p ≤ p / 2) =
        decide (ordCompl[p] b % p ≤ p / 2) := by
      simpa [primeColor, hp2] using hc
    have hnot := same_half_not_dvd_add hp hp2 hua hub hc'
    rw [Nat.factorization_eq_zero_of_not_dvd hnot]
    exact Nat.zero_le _

private theorem factorization_add_le_of_lt {p a b : ℕ}
    (hp : p.Prime) (ha : a ≠ 0) (hlt : a.factorization p < b.factorization p) :
    (a + b).factorization p ≤ a.factorization p := by
  have hs : a + b ≠ 0 := by omega
  by_contra h
  have hsdiv : p ^ (a.factorization p + 1) ∣ a + b :=
    (hp.pow_dvd_iff_le_factorization hs).2 (by omega)
  have hbdiv : p ^ (a.factorization p + 1) ∣ b :=
    (pow_dvd_pow p (by omega : a.factorization p + 1 ≤ b.factorization p)).trans
      (Nat.ordProj_dvd b p)
  exact Nat.pow_succ_factorization_not_dvd ha hp
    ((Nat.dvd_add_iff_left hbdiv).mpr hsdiv)

/-- For matching colors, every prime-power contribution to `a + b` occurs in `2*a`. -/
theorem same_color_factorization_add_le {p a b : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hc : primeColor p a = primeColor p b) :
    (a + b).factorization p ≤ (2 * a).factorization p := by
  rw [Nat.factorization_mul (by decide : (2 : ℕ) ≠ 0) ha.ne', Finsupp.add_apply]
  rcases lt_trichotomy (a.factorization p) (b.factorization p) with hlt | heq | hgt
  · have hle := factorization_add_le_of_lt hp ha.ne' hlt
    omega
  · have hsum : a + b = p ^ (a.factorization p) * (ordCompl[p] a + ordCompl[p] b) := by
      calc
        a + b = p ^ (a.factorization p) * ordCompl[p] a +
            p ^ (b.factorization p) * ordCompl[p] b := by
          rw [Nat.ordProj_mul_ordCompl_eq_self, Nat.ordProj_mul_ordCompl_eq_self]
        _ = p ^ (a.factorization p) * (ordCompl[p] a + ordCompl[p] b) := by
          rw [← heq, mul_add]
    have hu : ordCompl[p] a + ordCompl[p] b ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (Nat.ordCompl_pos p ha.ne') (Nat.le_add_right _ _))
    rw [hsum, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hu,
      Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same]
    have hle := ordCompl_sum_factorization_le hp ha hb hc
    omega
  · have hle := factorization_add_le_of_lt hp hb.ne' hgt
    rw [Nat.add_comm b a] at hle
    omega

/-- Matching colors on the prime support of a sum force the sum to divide `2*a`. -/
theorem sum_dvd_two_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : ∀ p ∈ (a + b).primeFactors, primeColor p a = primeColor p b) :
    a + b ∣ 2 * a := by
  apply (Nat.factorization_le_iff_dvd (by omega) (by positivity)).mp
  intro p
  by_cases hm : p ∈ (a + b).primeFactors
  · exact same_color_factorization_add_le (Nat.prime_of_mem_primeFactors hm) ha hb (hc p hm)
  · have hz : (a + b).factorization p = 0 := Finsupp.notMem_support_iff.mp hm
    rw [hz]
    exact Nat.zero_le _

/-- Positive integers with matching colors at every prime dividing their sum are equal. -/
theorem eq_of_prime_colors_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hc : ∀ p ∈ (a + b).primeFactors, primeColor p a = primeColor p b) :
    a = b := by
  have hd₁ := sum_dvd_two_mul ha hb hc
  have hd₂ : b + a ∣ 2 * b := sum_dvd_two_mul hb ha (by
    intro p hp
    exact (hc p (by simpa [Nat.add_comm] using hp)).symm)
  have hle₁ := Nat.le_of_dvd (by positivity : 0 < 2 * a) hd₁
  have hle₂ := Nat.le_of_dvd (by positivity : 0 < 2 * b) hd₂
  omega

/-- The binary signature, indexed by the primes occurring in pair sums of `A`. -/
def signature (A : Finset ℕ) (a : ℕ) : ↥(primeSupport A) → Bool :=
  fun p => primeColor p.1 a

/-- Signatures distinguish the elements of any finite set of positive naturals. -/
theorem signature_injective (A : Finset ℕ) (hpos : ∀ a ∈ A, 0 < a) :
    Function.Injective (fun a : A => signature A a) := by
  intro a b hab
  apply Subtype.ext
  by_contra hne
  apply hne
  apply eq_of_prime_colors_eq (hpos a a.property) (hpos b b.property)
  intro p hp
  have hs : p ∈ primeSupport A := by
    apply (Independent126.prime_mem_iff A p).mpr
    obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact ⟨hprime, a, a.property, b, b.property, hne, hdvd⟩
  exact congrFun hab ⟨p, hs⟩

/-- The positive-natural cardinality bound for the exact ordered product in the problem. -/
theorem card_le_two_pow_primeFactors_of_pos (A : Finset ℕ) (hpos : ∀ a ∈ A, 0 < a) :
    A.card ≤ 2 ^ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card := by
  classical
  have h := Fintype.card_le_of_injective (fun a : A => signature A a)
    (signature_injective A hpos)
  simpa [primeSupport] using h

/-- For arbitrary naturals, deleting zero costs at most one element and cannot
increase the prime support. -/
theorem card_le_two_pow_primeFactors_add_one (A : Finset ℕ) :
    A.card ≤ 2 ^ (∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card + 1 := by
  have hpos : ∀ a ∈ A.erase 0, 0 < a := by
    intro a ha
    exact Nat.pos_of_ne_zero (Finset.mem_erase.mp ha).1
  have hB := card_le_two_pow_primeFactors_of_pos (A.erase 0) hpos
  change (A.erase 0).card ≤ 2 ^ Independent126.factorCount (A.erase 0) at hB
  have hmono := Independent126.factorCount_mono (Finset.erase_subset 0 A)
  have hpow : 2 ^ Independent126.factorCount (A.erase 0) ≤
      2 ^ Independent126.factorCount A :=
    Nat.pow_le_pow_right (by decide) hmono
  have hcard : A.card ≤ (A.erase 0).card + 1 := by
    by_cases hz : 0 ∈ A
    · exact le_of_eq (Finset.card_erase_add_one hz).symm
    · simp [Finset.erase_eq_of_notMem hz]
  change A.card ≤ 2 ^ Independent126.factorCount A + 1
  omega

/-- The attained-minimum corollary for the exact extremal definition copied from
`Spec` in `Independent126`. This does not assert the conjectural asymptotic. -/
theorem maximal_card_bound {f : ℕ → ℕ}
    (hf : Independent126.IsMaximalAddFactorsCard f) (n : ℕ) :
    n ≤ 2 ^ (f n) + 1 := by
  obtain ⟨A, hA, hcost⟩ := Independent126.maximal_attained hf n
  have h := card_le_two_pow_primeFactors_add_one A
  change A.card ≤ 2 ^ Independent126.factorCount A + 1 at h
  simpa only [hA, hcost] using h


end Signature126

open scoped BigOperators

namespace E126

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- A finite weighted laminar family. Repeated supports are combined in the weight. -/
structure LaminarFamily (ι : Type*) [DecidableEq ι] where
  nodes : Finset (Finset ι)
  weight : Finset ι → ℝ
  weight_nonneg : ∀ B ∈ nodes, 0 ≤ weight B
  laminar : ∀ B ∈ nodes, ∀ C ∈ nodes, B ⊆ C ∨ C ⊆ B ∨ Disjoint B C

/-- The real indicator of a finite subset. -/
def ind (B : Finset ι) (i : ι) : ℝ := if i ∈ B then 1 else 0

@[simp] theorem ind_of_mem {B : Finset ι} {i : ι} (h : i ∈ B) : ind B i = 1 := by
  simp [ind, h]

@[simp] theorem ind_of_not_mem {B : Finset ι} {i : ι} (h : i ∉ B) : ind B i = 0 := by
  simp [ind, h]

@[simp] theorem ind_sq (B : Finset ι) (i : ι) : ind B i ^ 2 = ind B i := by
  unfold ind
  split <;> norm_num

theorem ind_nonneg (B : Finset ι) (i : ι) : 0 ≤ ind B i := by
  unfold ind
  split <;> norm_num

namespace LaminarFamily

def kernel (W : LaminarFamily ι) (i j : ι) : ℝ :=
  ∑ B ∈ W.nodes, W.weight B * ind B i * ind B j

theorem kernel_symm (W : LaminarFamily ι) (i j : ι) : W.kernel i j = W.kernel j i := by
  unfold kernel
  apply Finset.sum_congr rfl
  intro B hB
  ring

theorem kernel_nonneg (W : LaminarFamily ι) (i j : ι) : 0 ≤ W.kernel i j := by
  apply Finset.sum_nonneg
  intro B hB
  exact mul_nonneg (mul_nonneg (W.weight_nonneg B hB) (ind_nonneg B i)) (ind_nonneg B j)

end LaminarFamily

/-- One prime's cancellation tree, with a consistent sign on each root. -/
structure OppositionFamily (ι : Type*) [DecidableEq ι] extends LaminarFamily ι where
  sign : ι → Bool
  bichromatic : ∀ B ∈ nodes, ∀ i ∈ B, ∃ j ∈ B, sign j ≠ sign i

namespace OppositionFamily

def unsigned (W : OppositionFamily ι) : ι → ι → ℝ := W.toLaminarFamily.kernel

def signVal (W : OppositionFamily ι) (i : ι) : ℝ := if W.sign i then 1 else -1

def signed (W : OppositionFamily ι) (i j : ι) : ℝ :=
  W.signVal i * W.signVal j * W.unsigned i j

def opposition (W : OppositionFamily ι) (i j : ι) : ℝ :=
  if W.sign i = W.sign j then 0 else W.unsigned i j

def agreement (W : OppositionFamily ι) (i j : ι) : ℝ :=
  if W.sign i = W.sign j then W.unsigned i j else 0

@[simp] theorem signVal_sq (W : OppositionFamily ι) (i : ι) : W.signVal i ^ 2 = 1 := by
  unfold signVal
  split <;> norm_num

theorem signVal_abs (W : OppositionFamily ι) (i : ι) : |W.signVal i| = 1 := by
  unfold signVal
  split <;> norm_num

theorem unsigned_nonneg (W : OppositionFamily ι) (i j : ι) : 0 ≤ W.unsigned i j :=
  W.toLaminarFamily.kernel_nonneg i j

theorem unsigned_symm (W : OppositionFamily ι) (i j : ι) : W.unsigned i j = W.unsigned j i :=
  W.toLaminarFamily.kernel_symm i j

theorem opposition_nonneg (W : OppositionFamily ι) (i j : ι) : 0 ≤ W.opposition i j := by
  unfold opposition
  split
  · exact le_rfl
  · exact W.unsigned_nonneg i j

@[simp] theorem opposition_diag (W : OppositionFamily ι) (i : ι) : W.opposition i i = 0 := by
  simp [opposition]

theorem opposition_symm (W : OppositionFamily ι) (i j : ι) :
    W.opposition i j = W.opposition j i := by
  simp only [opposition, eq_comm (a := W.sign i), W.unsigned_symm i j]

theorem signed_eq (W : OppositionFamily ι) (i j : ι) :
    W.signed i j = W.agreement i j - W.opposition i j := by
  cases hi : W.sign i <;> cases hj : W.sign j <;>
    simp [signed, signVal, agreement, opposition, hi, hj]

theorem unsigned_eq (W : OppositionFamily ι) (i j : ι) :
    W.unsigned i j = W.agreement i j + W.opposition i j := by
  unfold agreement opposition
  split <;> simp

theorem opposition_eq (W : OppositionFamily ι) (i j : ι) :
    W.opposition i j = (W.unsigned i j - W.signed i j) / 2 := by
  rw [W.signed_eq i j, W.unsigned_eq i j]
  ring

end OppositionFamily

variable [Fintype ι]

/-- Quadratic form, written as finite sums to avoid a matrix basis choice. -/
def quad (K : ι → ι → ℝ) (q : ι → ℝ) : ℝ := ∑ i, ∑ j, q i * q j * K i j

def CND (K : ι → ι → ℝ) : Prop := ∀ q : ι → ℝ, (∑ i, q i) = 0 → quad K q ≤ 0

variable {κ : Type*} [Fintype κ]

def totalOpposition (W : κ → OppositionFamily ι) (i j : ι) : ℝ :=
  ∑ p, (W p).opposition i j

def totalSigned (W : κ → OppositionFamily ι) (i j : ι) : ℝ :=
  ∑ p, (W p).signed i j

def totalUnsigned (W : κ → OppositionFamily ι) (i j : ι) : ℝ :=
  ∑ p, (W p).unsigned i j

end
end E126

/-
# Logarithmic kernels for Erdős problem 126

The log-sum kernel on positive reals is conditionally negative semidefinite.
The log-gcd kernel and equality-of-valuations kernel are positive semidefinite.
All statements allow repeated inputs and arbitrary real coefficients.

The analytic proof uses the Möbius transform `(a - 1) / (a + 1)` and the power
series for `-log (1 - x)`. The arithmetic proof uses the nonnegative von Mangoldt
divisor expansion of the logarithm.
-/

namespace E126

open scoped BigOperators

namespace LogKernel

/-- The quadratic form of a rank-one kernel is a square. -/
lemma rank_one_sum {ι : Type*} [Fintype ι] (q v : ι → ℝ) :
    (∑ i, ∑ j, q i * q j * (v i * v j)) = (∑ i, q i * v i) ^ 2 := by
  classical
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Terms depending on only one of the two indices vanish on zero-sum vectors. -/
lemma separated_sum_eq_zero {ι : Type*} [Fintype ι] (q u v : ι → ℝ) (c : ℝ)
    (hq : ∑ i, q i = 0) :
    (∑ i, ∑ j, q i * q j * (u i + v j + c)) = 0 := by
  classical
  have hu : (∑ i, ∑ j, q i * q j * u i) = 0 := by
    calc
      _ = (∑ i, q i * u i) * (∑ j, q j) := by
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hq, mul_zero]
  have hv : (∑ i, ∑ j, q i * q j * v j) = 0 := by
    calc
      _ = (∑ i, q i) * (∑ j, q j * v j) := by
        rw [Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hq, zero_mul]
  have hc : (∑ i, ∑ j, q i * q j * c) = 0 := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, hq, mul_zero, Finset.sum_const_zero,
      zero_mul]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hu, hv, hc]
  ring

lemma abs_mobius_lt_one {a : ℝ} (ha : 0 < a) :
    |(a - 1) / (a + 1)| < 1 := by
  have hp : 0 < a + 1 := by linarith
  rw [abs_lt]
  constructor
  · rw [lt_div_iff₀ hp]
    linarith
  · rw [div_lt_iff₀ hp]
    linarith

lemma abs_mul_lt_one {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) :
    |x * y| < 1 := by
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ 1 * |y| := mul_le_mul_of_nonneg_right hx.le (abs_nonneg y)
    _ < 1 := by simpa using hy

/-- The log-sum kernel differs from a power-series kernel by separated terms. -/
lemma log_add_mobius {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a + b) = Real.log (a + 1) + Real.log (b + 1) - Real.log 2 +
      Real.log (1 - ((a - 1) / (a + 1)) * ((b - 1) / (b + 1))) := by
  have ha1 : a + 1 ≠ 0 := by positivity
  have hb1 : b + 1 ≠ 0 := by positivity
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have heq : 1 - ((a - 1) / (a + 1)) * ((b - 1) / (b + 1)) =
      (2 * (a + b)) / ((a + 1) * (b + 1)) := by
    field_simp
    ring
  rw [heq, Real.log_div (mul_ne_zero (by norm_num) hab) (mul_ne_zero ha1 hb1),
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hab, Real.log_mul ha1 hb1]
  ring

/-- The kernel `-log (1 - rᵢ rⱼ)` is positive semidefinite for `|rᵢ| < 1`. -/
lemma neg_log_one_sub_mul_psd {ι : Type*} [Fintype ι] (r q : ι → ℝ)
    (hr : ∀ i, |r i| < 1) :
    0 ≤ ∑ i, ∑ j, q i * q j * (-Real.log (1 - r i * r j)) := by
  classical
  have hs : HasSum
      (fun n : ℕ => ∑ i, ∑ j,
        q i * q j * ((r i * r j) ^ (n + 1) / ((n : ℝ) + 1)))
      (∑ i, ∑ j, q i * q j * (-Real.log (1 - r i * r j))) := by
    apply hasSum_sum
    intro i hi
    apply hasSum_sum
    intro j hj
    exact (Real.hasSum_pow_div_log_of_abs_lt_one
      (abs_mul_lt_one (hr i) (hr j))).mul_left (q i * q j)
  apply HasSum.nonneg _ hs
  intro n
  have heq : (∑ i, ∑ j,
      q i * q j * ((r i * r j) ^ (n + 1) / ((n : ℝ) + 1))) =
      (∑ i, q i * r i ^ (n + 1)) ^ 2 / ((n : ℝ) + 1) := by
    rw [← rank_one_sum q (fun i => r i ^ (n + 1))]
    simp only [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_pow]
    ring
  rw [heq]
  positivity

end LogKernel

/-- Weak conditional negative definiteness of the log-sum kernel on positive reals.
No injectivity or distinctness hypothesis is required. -/
theorem log_sum_cnd {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (q : ι → ℝ) (hq : ∑ i, q i = 0) :
    (∑ i, ∑ j, q i * q j * Real.log (a i + a j)) ≤ 0 := by
  classical
  let r : ι → ℝ := fun i => (a i - 1) / (a i + 1)
  have hr : ∀ i, |r i| < 1 := fun i => LogKernel.abs_mobius_lt_one (ha i)
  have hn := LogKernel.neg_log_one_sub_mul_psd r q hr
  have hz := LogKernel.separated_sum_eq_zero q
    (fun i => Real.log (a i + 1)) (fun i => Real.log (a i + 1)) (-Real.log 2) hq
  have heq : (∑ i, ∑ j, q i * q j * Real.log (a i + a j)) =
      ∑ i, ∑ j, q i * q j * Real.log (1 - r i * r j) := by
    calc
      _ = (∑ i, ∑ j, q i * q j *
          (Real.log (a i + 1) + Real.log (a j + 1) + -Real.log 2)) +
          ∑ i, ∑ j, q i * q j * Real.log (1 - r i * r j) := by
        simp_rw [LogKernel.log_add_mobius (ha _) (ha _), sub_eq_add_neg,
          mul_add, Finset.sum_add_distrib]
        rfl
      _ = _ := by rw [hz, zero_add]
  rw [heq]
  simpa only [mul_neg, Finset.sum_neg_distrib, neg_nonneg] using hn

/-- The natural-number specialization of `log_sum_cnd`. -/
theorem log_sum_nat_cnd {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (ha : ∀ i, 0 < a i) (q : ι → ℝ) (hq : ∑ i, q i = 0) :
    (∑ i, ∑ j, q i * q j * Real.log ((a i + a j : ℕ) : ℝ)) ≤ 0 := by
  simpa only [Nat.cast_add] using
    log_sum_cnd (fun i => (a i : ℝ)) (fun i => Nat.cast_pos.mpr (ha i)) q hq

namespace LogKernel

/-- A finite weighted feature kernel is a sum of squares. -/
lemma weighted_feature_sum {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (w : κ → ℝ) (v : κ → ι → ℝ) (q : ι → ℝ) :
    (∑ i, ∑ j, q i * q j * (∑ k ∈ s, w k * (v k i * v k j))) =
      ∑ k ∈ s, w k * (∑ i, q i * v k i) ^ 2 := by
  classical
  simp_rw [Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ k ∈ s, q i * q j * (w k * (v k i * v k j))) =
        ∑ i, ∑ k ∈ s, ∑ j, q i * q j * (w k * (v k i * v k j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ k ∈ s, ∑ i, ∑ j, q i * q j * (w k * (v k i * v k j)) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← rank_one_sum q (v k), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

lemma weighted_feature_psd {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (w : κ → ℝ) (v : κ → ι → ℝ) (q : ι → ℝ)
    (hw : ∀ k ∈ s, 0 ≤ w k) :
    0 ≤ ∑ i, ∑ j, q i * q j * (∑ k ∈ s, w k * (v k i * v k j)) := by
  rw [weighted_feature_sum]
  exact Finset.sum_nonneg (fun k hk => mul_nonneg (hw k hk) (sq_nonneg _))

/-- Equality of labels is a sum of indicator rank-one kernels. -/
lemma equality_eq_features {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (v : ι → κ) (i j : ι) :
    (if v i = v j then (1 : ℝ) else 0) =
      ∑ k ∈ Finset.univ.image v,
        (if v i = k then (1 : ℝ) else 0) * (if v j = k then (1 : ℝ) else 0) := by
  classical
  have hi : v i ∈ Finset.univ.image v := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, hi, if_true]
  simp only [eq_comm]

/-- Expand log-gcd into nonnegative divisor features using von Mangoldt's identity. -/
lemma log_gcd_eq_features {a b M : ℕ} (hg : Nat.gcd a b ≠ 0) (hM : M ≠ 0)
    (hdiv : Nat.gcd a b ∣ M) :
    Real.log (Nat.gcd a b : ℝ) =
      ∑ d ∈ M.divisors, ArithmeticFunction.vonMangoldt d *
        ((if d ∣ a then (1 : ℝ) else 0) * (if d ∣ b then (1 : ℝ) else 0)) := by
  rw [← ArithmeticFunction.vonMangoldt_sum]
  apply Finset.sum_subset_zero_on_sdiff (Nat.divisors_subset_of_dvd hM hdiv)
  · intro d hd
    have hnot : ¬d ∣ Nat.gcd a b := by
      intro hdg
      exact (Finset.mem_sdiff.mp hd).2 (Nat.mem_divisors.mpr ⟨hdg, hg⟩)
    by_cases hda : d ∣ a
    · have hdb : ¬d ∣ b := fun hdb => hnot (Nat.dvd_gcd hda hdb)
      simp [hdb]
    · simp [hda]
  · intro d hd
    obtain ⟨hda, hdb⟩ := Nat.dvd_gcd_iff.mp (Nat.dvd_of_mem_divisors hd)
    simp [hda, hdb]

end LogKernel

/-- The equivalence-class matrix of any labeling is positive semidefinite.
The label type need not itself be finite. -/
theorem equivalence_class_psd {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (v : ι → κ) (q : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, q i * q j * (if v i = v j then (1 : ℝ) else 0) := by
  classical
  have h := LogKernel.weighted_feature_psd (Finset.univ.image v) (fun _ => (1 : ℝ))
    (fun k i => if v i = k then (1 : ℝ) else 0) q (by intros; norm_num)
  simpa only [one_mul, ← LogKernel.equality_eq_features v] using h

/-- A nonnegative multiple of an equivalence-class matrix is positive semidefinite. -/
theorem equivalence_class_weighted_psd {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (v : ι → κ) (q : ι → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    0 ≤ ∑ i, ∑ j, q i * q j * (if v i = v j then c else 0) := by
  have heq : (∑ i, ∑ j, q i * q j * (if v i = v j then c else 0)) =
      (∑ i, ∑ j, q i * q j * (if v i = v j then (1 : ℝ) else 0)) * c := by
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  rw [heq]
  exact mul_nonneg (equivalence_class_psd v q) hc

/-- Equality of the exponents of `2` in the natural-number factorizations is PSD. -/
theorem factorization_two_psd {ι : Type*} [Fintype ι] (a : ι → ℕ) (q : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, q i * q j *
      (if (a i).factorization 2 = (a j).factorization 2 then (1 : ℝ) else 0) :=
  equivalence_class_psd (fun i => (a i).factorization 2) q

/-- The same equality-of-valuations PSD statement using `padicValNat`. -/
theorem padicValNat_two_psd {ι : Type*} [Fintype ι] (a : ι → ℕ) (q : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, q i * q j *
      (if padicValNat 2 (a i) = padicValNat 2 (a j) then (1 : ℝ) else 0) :=
  equivalence_class_psd (fun i => padicValNat 2 (a i)) q

/-- Positive semidefiniteness of log-gcd on positive natural numbers. -/
theorem log_gcd_psd {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (ha : ∀ i, 0 < a i) (q : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, q i * q j * Real.log (Nat.gcd (a i) (a j) : ℝ) := by
  classical
  let M : ℕ := ∏ i, a i
  have hM : M ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (ha i).ne')
  have hlog : ∀ i j, Real.log (Nat.gcd (a i) (a j) : ℝ) =
      ∑ d ∈ M.divisors, ArithmeticFunction.vonMangoldt d *
        ((if d ∣ a i then (1 : ℝ) else 0) * (if d ∣ a j then (1 : ℝ) else 0)) := by
    intro i j
    apply LogKernel.log_gcd_eq_features (Nat.gcd_ne_zero_left (ha i).ne') hM
    exact (Nat.gcd_dvd_left (a i) (a j)).trans (Finset.dvd_prod_of_mem a (Finset.mem_univ i))
  simp_rw [hlog]
  exact LogKernel.weighted_feature_psd M.divisors ArithmeticFunction.vonMangoldt
    (fun d i => if d ∣ a i then (1 : ℝ) else 0) q
    (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- The arithmetic logarithmic kernel used for Erdős problem 126. -/
noncomputable def arithmetic_log_kernel (a b : ℕ) : ℝ :=
  Real.log ((a + b : ℕ) : ℝ) - Real.log (Nat.gcd a b : ℝ) -
    (if a.factorization 2 = b.factorization 2 then Real.log 2 else 0)

/-- The arithmetic logarithmic kernel is weakly conditionally negative semidefinite. -/
theorem arithmetic_log_kernel_cnd {ι : Type*} [Fintype ι] (a : ι → ℕ)
    (ha : ∀ i, 0 < a i) (q : ι → ℝ) (hq : ∑ i, q i = 0) :
    (∑ i, ∑ j, q i * q j * arithmetic_log_kernel (a i) (a j)) ≤ 0 := by
  have hs := log_sum_nat_cnd a ha q hq
  have hg := log_gcd_psd a ha q
  have hv := equivalence_class_weighted_psd (fun i => (a i).factorization 2) q
    (Real.log 2) (Real.log_nonneg (by norm_num))
  simp only [arithmetic_log_kernel, mul_sub, Finset.sum_sub_distrib]
  linarith

/-- On positive inputs the arithmetic logarithmic kernel has zero diagonal. -/
@[simp] theorem arithmetic_log_kernel_diag {a : ℕ} (ha : 0 < a) :
    arithmetic_log_kernel a a = 0 := by
  have haR : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
  rw [arithmetic_log_kernel, Nat.gcd_self, if_pos rfl, Nat.cast_add, ← two_mul,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) haR]
  ring

end E126

/-
# Energy and diameter bounds for opposition trees

The local estimates use only laminarity and bichromatic nodes. The global
energy estimate combines the unsigned and signed Gram kernels with CND.
The diameter estimate uses a three-point CND test, not a Euclidean embedding.
-/

open scoped BigOperators

namespace E126

noncomputable section

variable {ι : Type*} [DecidableEq ι]

namespace LaminarFamily

/-- Inclusion of the common-node supports gives an inequality of kernels. -/
theorem kernel_le_of_common_nodes (W : LaminarFamily ι) (a b c d : ι)
    (h : ∀ B ∈ W.nodes, a ∈ B → b ∈ B → c ∈ B ∧ d ∈ B) :
    W.kernel a b ≤ W.kernel c d := by
  apply Finset.sum_le_sum
  intro B hB
  by_cases ha : a ∈ B
  · by_cases hb : b ∈ B
    · obtain ⟨hc, hd⟩ := h B hB ha hb
      simp [ind, ha, hb, hc, hd]
    · simpa [ind, hb] using
        mul_nonneg (mul_nonneg (W.weight_nonneg B hB) (ind_nonneg B c))
          (ind_nonneg B d)
  · simpa [ind, ha] using
      mul_nonneg (mul_nonneg (W.weight_nonneg B hB) (ind_nonneg B c))
        (ind_nonneg B d)

/-- A laminar common-ancestor kernel is an ultrametric similarity. -/
theorem kernel_min_le (W : LaminarFamily ι) (x i j : ι) :
    min (W.kernel x i) (W.kernel x j) ≤ W.kernel i j := by
  by_cases h : ∀ B ∈ W.nodes, x ∈ B → i ∈ B → j ∈ B
  · exact (min_le_left _ _).trans
      (W.kernel_le_of_common_nodes x i i j (fun B hB hx hi => ⟨hi, h B hB hx hi⟩))
  · push_neg at h
    obtain ⟨B, hB, hxB, hiB, hjB⟩ := h
    apply (min_le_right _ _).trans
    apply W.kernel_le_of_common_nodes x j i j
    intro C hC hxC hjC
    rcases W.laminar B hB C hC with hBC | hCB | hd
    · exact ⟨hBC hiB, hjC⟩
    · exact (hjB (hCB hjC)).elim
    · exact (Finset.disjoint_left.mp hd hxB hxC).elim

/-- A smallest node through a point is contained in all nodes through it. -/
theorem exists_smallest_node (W : LaminarFamily ι) (i : ι)
    (h : ∃ B ∈ W.nodes, i ∈ B) :
    ∃ B ∈ W.nodes, i ∈ B ∧ ∀ C ∈ W.nodes, i ∈ C → B ⊆ C := by
  let S := W.nodes.filter (fun B => i ∈ B)
  have hS : S.Nonempty := by
    obtain ⟨B, hB, hi⟩ := h
    exact ⟨B, Finset.mem_filter.mpr ⟨hB, hi⟩⟩
  obtain ⟨B, hB, hmin⟩ := S.exists_min_image Finset.card hS
  obtain ⟨hBW, hiB⟩ := Finset.mem_filter.mp hB
  refine ⟨B, hBW, hiB, ?_⟩
  intro C hC hiC
  rcases W.laminar B hBW C hC with hBC | hCB | hd
  · exact hBC
  · have hcard : B.card ≤ C.card := hmin C (Finset.mem_filter.mpr ⟨hC, hiC⟩)
    have heq : C = B := Finset.eq_of_subset_of_card_le hCB hcard
    rw [heq]
  · exact (Finset.disjoint_left.mp hd hiB hiC).elim

end LaminarFamily

namespace OppositionFamily

theorem agreement_nonneg (W : OppositionFamily ι) (i j : ι) :
    0 ≤ W.agreement i j := by
  unfold agreement
  split
  · exact W.unsigned_nonneg i j
  · exact le_rfl

/-- The common-neighbor bound, also valid with coincident indices. -/
theorem opposition_min_le_agreement (W : OppositionFamily ι) (x i j : ι) :
    min (W.opposition x i) (W.opposition x j) ≤ W.agreement i j := by
  by_cases hxi : W.sign x = W.sign i
  · calc
      _ ≤ W.opposition x i := min_le_left _ _
      _ = 0 := if_pos hxi
      _ ≤ _ := W.agreement_nonneg i j
  by_cases hxj : W.sign x = W.sign j
  · calc
      _ ≤ W.opposition x j := min_le_right _ _
      _ = 0 := if_pos hxj
      _ ≤ _ := W.agreement_nonneg i j
  have hij : W.sign i = W.sign j := by
    cases hx : W.sign x <;> cases hi : W.sign i <;> cases hj : W.sign j <;>
      simp_all
  simpa only [opposition, agreement, if_neg hxi, if_neg hxj, if_pos hij] using
    W.toLaminarFamily.kernel_min_le x i j

/-- Bichromaticity supplies an opposite vertex realizing the entire diagonal.
If no node contains `i`, both sides are zero and the witness can be `i`. -/
theorem exists_diagonal_witness (W : OppositionFamily ι) (i : ι) :
    ∃ j, W.unsigned i i = W.opposition i j := by
  by_cases h : ∃ B ∈ W.nodes, i ∈ B
  · obtain ⟨B, hB, hiB, hmin⟩ := W.toLaminarFamily.exists_smallest_node i h
    obtain ⟨j, hjB, hji⟩ := W.bichromatic B hB i hiB
    refine ⟨j, ?_⟩
    rw [opposition, if_neg (Ne.symm hji)]
    unfold unsigned LaminarFamily.kernel
    apply Finset.sum_congr rfl
    intro C hC
    by_cases hiC : i ∈ C
    · have hjC : j ∈ C := hmin C hC hiC hjB
      simp [ind, hiC, hjC]
    · simp [ind, hiC]
  · refine ⟨i, ?_⟩
    rw [opposition_diag]
    unfold unsigned LaminarFamily.kernel
    apply Finset.sum_eq_zero
    intro B hB
    have hiB : i ∉ B := fun hi => h ⟨B, hB, hi⟩
    simp [ind, hiB]

/-- In particular, any uniform opposition bound controls the unsigned diagonal. -/
theorem unsigned_diag_le (W : OppositionFamily ι) (L : ℝ)
    (hL : ∀ i j, W.opposition i j ≤ L) (i : ι) :
    W.unsigned i i ≤ L := by
  obtain ⟨j, hj⟩ := W.exists_diagonal_witness i
  rw [hj]
  exact hL i j

end OppositionFamily

variable [Fintype ι]

namespace LaminarFamily

/-- The unsigned kernel is a nonnegative sum of rank-one quadratic forms. -/
theorem kernel_quad_eq (W : LaminarFamily ι) (q : ι → ℝ) :
    quad W.kernel q = ∑ B ∈ W.nodes, W.weight B * (∑ i, q i * ind B i) ^ 2 := by
  simpa only [quad, kernel, mul_assoc] using
    LogKernel.weighted_feature_sum W.nodes W.weight ind q

theorem kernel_psd (W : LaminarFamily ι) (q : ι → ℝ) :
    0 ≤ quad W.kernel q := by
  rw [W.kernel_quad_eq]
  exact Finset.sum_nonneg (fun B hB => mul_nonneg (W.weight_nonneg B hB) (sq_nonneg _))

end LaminarFamily

namespace OppositionFamily

theorem unsigned_psd (W : OppositionFamily ι) (q : ι → ℝ) :
    0 ≤ quad W.unsigned q := W.toLaminarFamily.kernel_psd q

/-- Consistent signs preserve the Gram representation. -/
theorem signed_psd (W : OppositionFamily ι) (q : ι → ℝ) :
    0 ≤ quad W.signed q := by
  calc
    0 ≤ quad W.unsigned (fun i => q i * W.signVal i) := W.unsigned_psd _
    _ = quad W.signed q := by
      unfold quad signed
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

omit [Fintype ι] in
@[simp] theorem signed_diag (W : OppositionFamily ι) (i : ι) :
    W.signed i i = W.unsigned i i := by
  rw [signed, ← pow_two, signVal_sq, one_mul]

end OppositionFamily

omit [DecidableEq ι] in
/-- A PSD matrix with nonpositive off-diagonal entries is bounded by twice its
own diagonal. Symmetry is not needed for this quadratic-form statement. -/
theorem z_matrix_quad_le (K : ι → ι → ℝ)
    (hpsd : ∀ q, 0 ≤ quad K q) (hoff : ∀ i j, i ≠ j → K i j ≤ 0) (q : ι → ℝ) :
    quad K q ≤ 2 * ∑ i, q i ^ 2 * K i i := by
  classical
  have hterm (i j : ι) :
      q i * q j * K i j + |q i| * |q j| * K i j ≤
        if i = j then 2 * (q i ^ 2 * K i i) else 0 := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, ← pow_two, ← pow_two, sq_abs]
      linarith
    · rw [if_neg hij]
      have hab : 0 ≤ q i * q j + |q i| * |q j| := by
        have h := neg_abs_le (q i * q j)
        rw [abs_mul] at h
        linarith
      simpa only [add_mul] using
        mul_nonpos_of_nonneg_of_nonpos hab (hoff i j hij)
  have hsum : quad K q + quad K (fun i => |q i|) ≤ 2 * ∑ i, q i ^ 2 * K i i := by
    calc
      _ = ∑ i, ∑ j, (q i * q j * K i j + |q i| * |q j| * K i j) := by
        simp only [quad, Finset.sum_add_distrib]
      _ ≤ ∑ i, ∑ j, if i = j then 2 * (q i ^ 2 * K i i) else 0 :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
      _ = _ := by simp [Finset.mul_sum]
  have habs := hpsd (fun i => |q i|)
  linarith

omit [DecidableEq ι] in
/-- A three-point test of CND gives the squared-distance triangle bound directly.
The test vector is `e_a + e_b - 2 e_y`; coincident points are allowed. -/
theorem cnd_triangle (K : ι → ι → ℝ) (hCND : CND K)
    (hsym : ∀ i j, K i j = K j i) (hdiag : ∀ i, K i i = 0) (a b y : ι) :
    K a b ≤ 2 * K a y + 2 * K b y := by
  classical
  let q : ι → ℝ := fun i =>
    (if i = a then 1 else 0) + (if i = b then 1 else 0) -
      2 * (if i = y then 1 else 0)
  have htest (f : ι → ℝ) : ∑ i, q i * f i = f a + f b - 2 * f y := by
    simp [q, add_mul, sub_mul, ite_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
  have hq : ∑ i, q i = 0 := by
    have h := htest (fun _ => 1)
    norm_num at h
    exact h
  have heval : quad K q =
      (K a a + K a b - 2 * K a y) + (K b a + K b b - 2 * K b y) -
        2 * (K y a + K y b - 2 * K y y) := by
    calc
      _ = ∑ i, q i * (∑ j, q j * K i j) := by
        simp only [quad, Finset.mul_sum, mul_assoc]
      _ = (∑ j, q j * K a j) + (∑ j, q j * K b j) -
          2 * (∑ j, q j * K y j) := htest _
      _ = _ := by rw [htest, htest, htest]
  have hc := hCND q hq
  rw [heval, hdiag a, hdiag b, hdiag y, hsym b a, hsym y a, hsym y b] at hc
  linarith

variable {κ : Type*} [Fintype κ]

omit [DecidableEq ι] in
/-- Quadratic forms commute with finite sums of kernels. -/
theorem quad_sum (K : κ → ι → ι → ℝ) (q : ι → ℝ) :
    quad (fun i j => ∑ p, K p i j) q = ∑ p, quad (K p) q := by
  classical
  unfold quad
  simp_rw [Finset.mul_sum]
  calc
    (∑ i, ∑ j, ∑ p, q i * q j * K p i j) =
        ∑ i, ∑ p, ∑ j, q i * q j * K p i j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem totalUnsigned_psd (W : κ → OppositionFamily ι) (q : ι → ℝ) :
    0 ≤ quad (totalUnsigned W) q := by
  unfold totalUnsigned
  rw [quad_sum]
  exact Finset.sum_nonneg (fun p _ => (W p).unsigned_psd q)

theorem totalSigned_psd (W : κ → OppositionFamily ι) (q : ι → ℝ) :
    0 ≤ quad (totalSigned W) q := by
  unfold totalSigned
  rw [quad_sum]
  exact Finset.sum_nonneg (fun p _ => (W p).signed_psd q)

omit [Fintype ι] in
theorem opposition_le_totalOpposition (W : κ → OppositionFamily ι) (p : κ) (i j : ι) :
    (W p).opposition i j ≤ totalOpposition W i j :=
  Finset.single_le_sum (fun k _ => (W k).opposition_nonneg i j) (Finset.mem_univ p)

omit [Fintype ι] in
theorem totalOpposition_nonneg (W : κ → OppositionFamily ι) (i j : ι) :
    0 ≤ totalOpposition W i j :=
  Finset.sum_nonneg (fun p _ => (W p).opposition_nonneg i j)

omit [Fintype ι] in
@[simp] theorem totalOpposition_diag (W : κ → OppositionFamily ι) (i : ι) :
    totalOpposition W i i = 0 := by
  simp [totalOpposition]

omit [Fintype ι] in
theorem totalOpposition_symm (W : κ → OppositionFamily ι) (i j : ι) :
    totalOpposition W i j = totalOpposition W j i := by
  unfold totalOpposition
  exact Finset.sum_congr rfl (fun p _ => (W p).opposition_symm i j)

omit [Fintype ι] in
theorem totalOpposition_eq (W : κ → OppositionFamily ι) (i j : ι) :
    totalOpposition W i j = (totalUnsigned W i j - totalSigned W i j) / 2 := by
  unfold totalOpposition totalUnsigned totalSigned
  simp_rw [OppositionFamily.opposition_eq]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]

theorem quad_totalOpposition (W : κ → OppositionFamily ι) (q : ι → ℝ) :
    quad (totalOpposition W) q =
      (quad (totalUnsigned W) q - quad (totalSigned W) q) / 2 := by
  unfold quad
  simp_rw [totalOpposition_eq, ← mul_div_assoc, ← Finset.sum_div, mul_sub,
    Finset.sum_sub_distrib]

omit [Fintype ι] in
@[simp] theorem totalSigned_diag (W : κ → OppositionFamily ι) (i : ι) :
    totalSigned W i i = totalUnsigned W i i := by
  simp [totalSigned, totalUnsigned]

omit [Fintype ι] in
theorem totalUnsigned_diag_le (W : κ → OppositionFamily ι) (L : ℝ)
    (hL : ∀ i j, totalOpposition W i j ≤ L) (i : ι) :
    totalUnsigned W i i ≤ (Fintype.card κ : ℝ) * L := by
  calc
    _ ≤ ∑ _p : κ, L := by
      apply Finset.sum_le_sum
      intro p hp
      exact (W p).unsigned_diag_le L
        (fun a b => (opposition_le_totalOpposition W p a b).trans (hL a b)) i
    _ = _ := by simp

theorem quad_unsigned_le_totalUnsigned (W : κ → OppositionFamily ι) (p : κ) (q : ι → ℝ) :
    quad (W p).unsigned q ≤ quad (totalUnsigned W) q := by
  unfold totalUnsigned
  rw [quad_sum]
  exact Finset.single_le_sum (fun k _ => (W k).unsigned_psd q) (Finset.mem_univ p)

/-- The energy estimate only needs the weak Z-matrix hypothesis. No positivity
hypothesis on `L` is required beyond its being a uniform opposition bound. -/
theorem unsigned_energy_bound_of_nonpos (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j ≤ 0)
    (hCND : CND (totalOpposition W)) (L : ℝ)
    (hL : ∀ i j, totalOpposition W i j ≤ L) (p : κ) (q : ι → ℝ)
    (hq : ∑ i, q i = 0) :
    quad (W p).unsigned q ≤
      2 * (Fintype.card κ : ℝ) * L * (∑ i, q i ^ 2) := by
  have hUV : quad (totalUnsigned W) q ≤ quad (totalSigned W) q := by
    have hc := hCND q hq
    rw [quad_totalOpposition] at hc
    linarith
  calc
    _ ≤ quad (totalUnsigned W) q := quad_unsigned_le_totalUnsigned W p q
    _ ≤ quad (totalSigned W) q := hUV
    _ ≤ 2 * ∑ i, q i ^ 2 * totalSigned W i i :=
      z_matrix_quad_le (totalSigned W) (totalSigned_psd W) hV q
    _ ≤ 2 * ∑ i, q i ^ 2 * ((Fintype.card κ : ℝ) * L) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro i hi
      rw [totalSigned_diag]
      exact mul_le_mul_of_nonneg_left (totalUnsigned_diag_le W L hL i) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The unsigned energy estimate under the strict off-diagonal LCM hypothesis. -/
theorem unsigned_energy_bound (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j < 0)
    (hCND : CND (totalOpposition W)) (L : ℝ)
    (hL : ∀ i j, totalOpposition W i j ≤ L) (p : κ) (q : ι → ℝ)
    (hq : ∑ i, q i = 0) :
    quad (W p).unsigned q ≤
      2 * (Fintype.card κ : ℝ) * L * (∑ i, q i ^ 2) :=
  unsigned_energy_bound_of_nonpos W (fun i j hij => (hV i j hij).le) hCND L hL p q hq

omit [Fintype ι] in
/-- A negative total signed entry strictly dominates every individual agreement
entry by the total opposition entry. -/
theorem agreement_lt_totalOpposition (W : κ → OppositionFamily ι) (p : κ) (i j : ι)
    (hV : totalSigned W i j < 0) :
    (W p).agreement i j < totalOpposition W i j := by
  have hsum : (∑ k, (W k).agreement i j) < totalOpposition W i j := by
    unfold totalSigned at hV
    simp_rw [OppositionFamily.signed_eq, Finset.sum_sub_distrib] at hV
    exact sub_neg.mp hV
  exact (Finset.single_le_sum (fun k _ => (W k).agreement_nonneg i j)
    (Finset.mem_univ p)).trans_lt hsum

omit [Fintype ι] in
/-- For a fixed point and family, a set of opposition diameter at most `δ`
contains at most one point whose opposition to the fixed point exceeds `δ`. -/
theorem large_opposition_card_le_one (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j < 0) (T : Finset ι) (δ : ℝ)
    (hT : ∀ i ∈ T, ∀ j ∈ T, totalOpposition W i j ≤ δ) (x : ι) (p : κ) :
    (T.filter (fun y => δ < (W p).opposition x y)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨hiT, hi⟩ := Finset.mem_filter.mp hi
  obtain ⟨hjT, hj⟩ := Finset.mem_filter.mp hj
  by_contra hij
  have hmin : δ < min ((W p).opposition x i) ((W p).opposition x j) := lt_min hi hj
  have hlocal := (W p).opposition_min_le_agreement x i j
  have hglobal := agreement_lt_totalOpposition W p i j (hV i j hij)
  have hbound := hT i hiT j hjT
  linarith

omit [Fintype ι] in
/-- Avoiding the at most `2 * card κ` exceptional points gives a point good
simultaneously for the two prescribed points in every family. -/
theorem exists_good_intermediate (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j < 0) (T : Finset ι) (δ : ℝ)
    (hT : ∀ i ∈ T, ∀ j ∈ T, totalOpposition W i j ≤ δ)
    (hcard : 2 * Fintype.card κ < T.card) (a b : ι) :
    ∃ y ∈ T, (∀ p, (W p).opposition a y ≤ δ) ∧
      (∀ p, (W p).opposition b y ≤ δ) := by
  classical
  let bad (x : ι) : Finset ι :=
    Finset.univ.biUnion (fun p : κ => T.filter (fun y => δ < (W p).opposition x y))
  have hbad (x : ι) : (bad x).card ≤ Fintype.card κ := by
    calc
      _ ≤ ∑ p : κ, (T.filter (fun y => δ < (W p).opposition x y)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _p : κ, 1 := Finset.sum_le_sum
        (fun p _ => large_opposition_card_le_one W hV T δ hT x p)
      _ = _ := by simp
  have hbadab : (bad a ∪ bad b).card ≤ 2 * Fintype.card κ := by
    have hu := Finset.card_union_le (bad a) (bad b)
    have ha := hbad a
    have hb := hbad b
    omega
  obtain ⟨y, hyT, hybad⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (hbadab.trans_lt hcard)
  have hgood (x : ι) (hx : y ∉ bad x) (p : κ) : (W p).opposition x y ≤ δ := by
    by_contra h
    apply hx
    exact Finset.mem_biUnion.mpr
      ⟨p, Finset.mem_univ p, Finset.mem_filter.mpr ⟨hyT, lt_of_not_ge h⟩⟩
  refine ⟨y, hyT, hgood a ?_, hgood b ?_⟩
  · exact fun h => hybad (Finset.mem_union_left _ h)
  · exact fun h => hybad (Finset.mem_union_right _ h)

/-- A small diameter on more than `2 * card κ` points controls the global
opposition diameter. This proof uses only exceptional-point counting and the
three-point CND test. A separate nonnegativity assumption on `δ` is unnecessary. -/
theorem totalOpposition_diameter_bound (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j < 0)
    (hCND : CND (totalOpposition W)) (T : Finset ι) (δ : ℝ)
    (hT : ∀ i ∈ T, ∀ j ∈ T, totalOpposition W i j ≤ δ)
    (hcard : 2 * Fintype.card κ < T.card) (a b : ι) :
    totalOpposition W a b ≤ 4 * (Fintype.card κ : ℝ) * δ := by
  obtain ⟨y, _hyT, hay, hby⟩ := exists_good_intermediate W hV T δ hT hcard a b
  have hsum (x : ι) (hx : ∀ p, (W p).opposition x y ≤ δ) :
      totalOpposition W x y ≤ (Fintype.card κ : ℝ) * δ := by
    calc
      _ ≤ ∑ _p : κ, δ := Finset.sum_le_sum (fun p _ => hx p)
      _ = _ := by simp
  have ha := hsum a hay
  have hb := hsum b hby
  have htri := cnd_triangle (totalOpposition W) hCND
    (totalOpposition_symm W) (totalOpposition_diag W) a b y
  linarith

/-- Version convenient for bounds obtained only on distinct pairs in `T`. -/
theorem totalOpposition_diameter_bound_of_offDiag (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j < 0)
    (hCND : CND (totalOpposition W)) (T : Finset ι) (δ : ℝ) (hδ : 0 ≤ δ)
    (hT : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → totalOpposition W i j ≤ δ)
    (hcard : 2 * Fintype.card κ < T.card) (a b : ι) :
    totalOpposition W a b ≤ 4 * (Fintype.card κ : ℝ) * δ := by
  apply totalOpposition_diameter_bound W hV hCND T δ _ hcard a b
  intro i hi j hj
  by_cases hij : i = j
  · subst j
    simpa using hδ
  · exact hT i hi j hj hij

end
end E126

/-
# Finite laminar pruning for Erdős problem 126

A zero-sum energy bound for a nonnegative laminar kernel gives a constant
baseline outside a small exceptional set, up to an error of `2 * M / t`.
The symmetric bad sets consist of pairs in nodes of cardinality less than `t`.
All estimates concern the unsigned kernel.
-/

open scoped BigOperators

namespace E126

noncomputable section

variable {ι : Type*} [DecidableEq ι]

namespace Pruning126

/-- Nodes through a common point are ordered by their cardinalities. -/
lemma subset_of_common_point (W : LaminarFamily ι) {B C : Finset ι}
    (hB : B ∈ W.nodes) (hC : C ∈ W.nodes) {i : ι}
    (hiB : i ∈ B) (hiC : i ∈ C) (hcard : B.card ≤ C.card) : B ⊆ C := by
  rcases W.laminar B hB C hC with hBC | hCB | hd
  · exact hBC
  · have heq : C = B := Finset.eq_of_subset_of_card_le hCB hcard
    rw [heq]
  · exact (Finset.disjoint_left.mp hd hiB hiC).elim

variable [Fintype ι]

/-- The bad relation includes every pair in a small node, including its diagonal. -/
def smallNeighbours (W : LaminarFamily ι) (t : ℕ) (i : ι) : Finset ι :=
  Finset.univ.filter (fun j => ∃ B ∈ W.nodes, B.card < t ∧ i ∈ B ∧ j ∈ B)

@[simp] lemma mem_smallNeighbours (W : LaminarFamily ι) (t : ℕ) (i j : ι) :
    j ∈ smallNeighbours W t i ↔ ∃ B ∈ W.nodes, B.card < t ∧ i ∈ B ∧ j ∈ B := by
  simp [smallNeighbours]

lemma smallNeighbours_symm (W : LaminarFamily ι) (t : ℕ) (i j : ι) :
    j ∈ smallNeighbours W t i ↔ i ∈ smallNeighbours W t j := by
  simp only [mem_smallNeighbours]
  constructor <;> rintro ⟨B, hB, hcard, hi, hj⟩
  · exact ⟨B, hB, hcard, hj, hi⟩
  · exact ⟨B, hB, hcard, hj, hi⟩

/-- All small nodes through a point lie in the largest such node. -/
lemma smallNeighbours_card_le (W : LaminarFamily ι) (t : ℕ) (i : ι) :
    (smallNeighbours W t i).card ≤ t := by
  let S := W.nodes.filter (fun B => B.card < t ∧ i ∈ B)
  by_cases hS : S.Nonempty
  · obtain ⟨B, hB, hmax⟩ := S.exists_max_image Finset.card hS
    obtain ⟨hBW, hBt, hiB⟩ := Finset.mem_filter.mp hB
    have hsub : smallNeighbours W t i ⊆ B := by
      intro j hj
      obtain ⟨C, hCW, hCt, hiC, hjC⟩ := (mem_smallNeighbours W t i j).mp hj
      have hCS : C ∈ S := Finset.mem_filter.mpr ⟨hCW, hCt, hiC⟩
      exact subset_of_common_point W hCW hBW hiC hiB (hmax C hCS) hjC
    exact (Finset.card_le_card hsub).trans hBt.le
  · have hempty : smallNeighbours W t i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨B, hBW, hBt, hiB, _⟩ := (mem_smallNeighbours W t i j).mp hj
      exact hS ⟨B, Finset.mem_filter.mpr ⟨hBW, hBt, hiB⟩⟩
    simp [hempty]

lemma sum_ind (B : Finset ι) : (∑ i, ind B i) = (B.card : ℝ) := by
  simp [ind]

/-- A normalized difference of indicators on two disjoint supports. -/
def contrast (C D : Finset ι) (i : ι) : ℝ :=
  ind C i / (C.card : ℝ) - ind D i / (D.card : ℝ)

lemma contrast_sum_zero {C D : Finset ι} (hC : 0 < C.card) (hD : 0 < D.card) :
    (∑ i, contrast C D i) = 0 := by
  have hc : (C.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hC.ne'
  have hd : (D.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  simp only [contrast, Finset.sum_sub_distrib, ← Finset.sum_div, sum_ind,
    div_self hc, div_self hd, sub_self]

lemma contrast_norm_sq {C D : Finset ι} (hC : 0 < C.card) (hD : 0 < D.card)
    (hCD : Disjoint C D) :
    (∑ i, contrast C D i ^ 2) = 1 / (C.card : ℝ) + 1 / (D.card : ℝ) := by
  have hc : (C.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hC.ne'
  have hd : (D.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  have hpoint : ∀ i, contrast C D i ^ 2 =
      ind C i / (C.card : ℝ) ^ 2 + ind D i / (D.card : ℝ) ^ 2 := by
    intro i
    by_cases hiC : i ∈ C
    · have hiD : i ∉ D := fun hiD => Finset.disjoint_left.mp hCD hiC hiD
      simp [contrast, ind, hiC, hiD]
    · by_cases hiD : i ∈ D <;> simp [contrast, ind, hiC, hiD]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, sum_ind, sum_ind]
  field_simp

/-- Every node separating the positive support from the negative support has dot product one. -/
lemma contrast_dot_one {C D A : Finset ι} (hC : 0 < C.card)
    (hCA : C ⊆ A) (hDA : Disjoint D A) :
    (∑ i, contrast C D i * ind A i) = 1 := by
  have hc : (C.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hC.ne'
  have hpoint : ∀ i, contrast C D i * ind A i = ind C i / (C.card : ℝ) := by
    intro i
    by_cases hiA : i ∈ A
    · have hiD : i ∉ D := fun hiD => Finset.disjoint_left.mp hDA hiD hiA
      simp [contrast, ind, hiA, hiD]
    · have hiC : i ∉ C := fun hiC => hiA (hCA hiC)
      simp [contrast, ind, hiA, hiC]
  simp_rw [hpoint]
  rw [← Finset.sum_div, sum_ind, div_self hc]

/-- The energy expansion uses every original node, not just a selected chain. -/
lemma kernel_sum_squares (W : LaminarFamily ι) (q : ι → ℝ) :
    quad W.kernel q = ∑ B ∈ W.nodes, W.weight B * (∑ i, q i * ind B i) ^ 2 := by
  simpa only [quad, LaminarFamily.kernel, mul_assoc] using
    LogKernel.weighted_feature_sum W.nodes W.weight ind q

/-- The weights of a chain between `C` and `D` are bounded by a zero-sum test.
Only the two support cardinalities and the interval containments are needed. -/
lemma chain_weight_le (W : LaminarFamily ι) {M : ℝ} (hM : 0 ≤ M)
    (henergy : ∀ q : ι → ℝ, (∑ i, q i) = 0 →
      quad W.kernel q ≤ M * ∑ i, q i ^ 2)
    {t : ℕ} (ht : 0 < t) {C D : Finset ι} {S : Finset (Finset ι)}
    (hS : S ⊆ W.nodes) (hCD : C ⊆ D) (hCt : t ≤ C.card) (hDt : t ≤ Dᶜ.card)
    (hchain : ∀ A ∈ S, C ⊆ A ∧ A ⊆ D) :
    (∑ A ∈ S, W.weight A) ≤ 2 * M / (t : ℝ) := by
  have hC : 0 < C.card := ht.trans_le hCt
  have hD : 0 < Dᶜ.card := ht.trans_le hDt
  have hdis : Disjoint C Dᶜ := by
    apply Finset.disjoint_left.mpr
    intro i hiC hiD
    exact (Finset.mem_compl.mp hiD) (hCD hiC)
  let q := contrast C Dᶜ
  have hzero : (∑ i, q i) = 0 := contrast_sum_zero hC hD
  have htR : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have hnorm : (∑ i, q i ^ 2) ≤ 2 / (t : ℝ) := by
    rw [show (∑ i, q i ^ 2) = 1 / (C.card : ℝ) + 1 / (Dᶜ.card : ℝ) from
      contrast_norm_sq hC hD hdis]
    calc
      _ ≤ 1 / (t : ℝ) + 1 / (t : ℝ) := add_le_add
        (one_div_le_one_div_of_le htR (Nat.cast_le.mpr hCt))
        (one_div_le_one_div_of_le htR (Nat.cast_le.mpr hDt))
      _ = _ := by ring
  have hdot : ∀ A ∈ S, (∑ i, q i * ind A i) = 1 := by
    intro A hA
    obtain ⟨hCA, hAD⟩ := hchain A hA
    apply contrast_dot_one hC hCA
    apply Finset.disjoint_left.mpr
    intro i hiD hiA
    exact (Finset.mem_compl.mp hiD) (hAD hiA)
  calc
    (∑ A ∈ S, W.weight A) = ∑ A ∈ S, W.weight A * (∑ i, q i * ind A i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [hdot A hA]
      ring
    _ ≤ ∑ A ∈ W.nodes, W.weight A * (∑ i, q i * ind A i) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hS
        (fun A hA _ => mul_nonneg (W.weight_nonneg A hA) (sq_nonneg _))
    _ = quad W.kernel q := (kernel_sum_squares W q).symm
    _ ≤ M * ∑ i, q i ^ 2 := henergy q hzero
    _ ≤ M * (2 / (t : ℝ)) := mul_le_mul_of_nonneg_left hnorm hM
    _ = 2 * M / (t : ℝ) := by ring

/-- The common nodes left after removing all almost-full nodes. -/
def residualNodes (W : LaminarFamily ι) (t : ℕ) (i j : ι) : Finset (Finset ι) :=
  W.nodes.filter (fun B => B.card ≤ Fintype.card ι - t ∧ i ∈ B ∧ j ∈ B)

/-- A nonbad pair has small residual common depth. The extremal common nodes
supply the two supports for the normalized contrast. -/
lemma residual_weight_le (W : LaminarFamily ι) {M : ℝ} (hM : 0 ≤ M)
    (henergy : ∀ q : ι → ℝ, (∑ i, q i) = 0 →
      quad W.kernel q ≤ M * ∑ i, q i ^ 2)
    {t : ℕ} (ht : 0 < t) (hnt : t ≤ Fintype.card ι) (i j : ι)
    (hbad : j ∉ smallNeighbours W t i) :
    (∑ B ∈ residualNodes W t i j, W.weight B) ≤ 2 * M / (t : ℝ) := by
  let S := residualNodes W t i j
  change (∑ B ∈ S, W.weight B) ≤ 2 * M / (t : ℝ)
  by_cases hS : S.Nonempty
  · obtain ⟨C, hCS, hmin⟩ := S.exists_min_image Finset.card hS
    obtain ⟨D, hDS, hmax⟩ := S.exists_max_image Finset.card hS
    obtain ⟨hCW, _, hiC, hjC⟩ := Finset.mem_filter.mp hCS
    obtain ⟨hDW, hDt, hiD, _⟩ := Finset.mem_filter.mp hDS
    have hCt : t ≤ C.card := by
      by_contra hc
      apply hbad
      exact (mem_smallNeighbours W t i j).mpr ⟨C, hCW, by omega, hiC, hjC⟩
    have hDcompl : t ≤ Dᶜ.card := by
      rw [Finset.card_compl]
      omega
    have hCD : C ⊆ D := subset_of_common_point W hCW hDW hiC hiD (hmin D hDS)
    apply chain_weight_le W hM henergy ht
      (show S ⊆ W.nodes from Finset.filter_subset _ _) hCD hCt hDcompl
    intro A hAS
    obtain ⟨hAW, _, hiA, _⟩ := Finset.mem_filter.mp hAS
    exact ⟨subset_of_common_point W hCW hAW hiC hiA (hmin A hAS),
      subset_of_common_point W hAW hDW hiA hiD (hmax A hAS)⟩
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hempty, Finset.sum_empty]
    exact div_nonneg (mul_nonneg (by norm_num) hM) (Nat.cast_nonneg t)

/-- The common contribution of all nodes of size greater than `n - t`. -/
def baseline (W : LaminarFamily ι) (t : ℕ) : ℝ :=
  ∑ B ∈ W.nodes.filter (fun B => Fintype.card ι - t < B.card), W.weight B

lemma baseline_nonneg (W : LaminarFamily ι) (t : ℕ) : 0 ≤ baseline W t := by
  apply Finset.sum_nonneg
  intro B hB
  exact W.weight_nonneg B (Finset.mem_filter.mp hB).1

/-- Almost-full nodes form a chain. The complement of its smallest member
has cardinality less than `t` and is the only exceptional set needed. -/
lemma exists_exceptional (W : LaminarFamily ι) {t : ℕ} (ht : 0 < t)
    (hnt : 2 * t < Fintype.card ι) :
    ∃ Z : Finset ι, Z.card < t ∧
      ∀ B ∈ W.nodes, Fintype.card ι - t < B.card → ∀ i, i ∉ Z → i ∈ B := by
  let S := W.nodes.filter (fun B => Fintype.card ι - t < B.card)
  by_cases hS : S.Nonempty
  · obtain ⟨B, hBS, hmin⟩ := S.exists_min_image Finset.card hS
    obtain ⟨hBW, hBt⟩ := Finset.mem_filter.mp hBS
    refine ⟨Bᶜ, ?_, ?_⟩
    · rw [Finset.card_compl]
      omega
    · intro A hAW hAt i hi
      have hiB : i ∈ B := by simpa only [Finset.mem_compl, not_not] using hi
      have hAS : A ∈ S := Finset.mem_filter.mpr ⟨hAW, hAt⟩
      have hsub : B ⊆ A := by
        rcases W.laminar B hBW A hAW with hBA | hAB | hd
        · exact hBA
        · have heq : A = B := Finset.eq_of_subset_of_card_le hAB (hmin A hAS)
          rw [heq]
        · have hunion := Finset.card_le_univ (B ∪ A)
          rw [Finset.card_union_of_disjoint hd] at hunion
          omega
      exact hsub hiB
  · refine ⟨∅, by simpa using ht, ?_⟩
    intro B hBW hBt i _
    exact (hS ⟨B, Finset.mem_filter.mpr ⟨hBW, hBt⟩⟩).elim

/-- Outside the exceptional set the almost-full nodes contribute exactly the baseline. -/
lemma kernel_eq_baseline_add (W : LaminarFamily ι) (t : ℕ) (i j : ι)
    (hlarge : ∀ B ∈ W.nodes, Fintype.card ι - t < B.card → i ∈ B ∧ j ∈ B) :
    W.kernel i j = baseline W t + ∑ B ∈ residualNodes W t i j, W.weight B := by
  unfold LaminarFamily.kernel baseline residualNodes
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hBt : Fintype.card ι - t < B.card
  · obtain ⟨hiB, hjB⟩ := hlarge B hB hBt
    have hBt' : ¬B.card ≤ Fintype.card ι - t := by omega
    simp [hBt, hBt', ind, hiB, hjB]
  · have hBt' : B.card ≤ Fintype.card ι - t := by omega
    by_cases hiB : i ∈ B <;> by_cases hjB : j ∈ B <;>
      simp [hBt, hBt', ind, hiB, hjB]

end Pruning126

variable [Fintype ι]

/-- Finite laminar pruning from a zero-sum energy bound.

The bad relation is symmetric and includes every pair sharing a node smaller
than `t`. After deleting at most `t` points, all other off-diagonal entries
lie in the interval `[β, β + 2 * M / t]`, with a nonnegative common baseline.
No assertion about signed kernels is used or needed. -/
theorem LaminarFamily.pruning (W : LaminarFamily ι) {M : ℝ} (hM : 0 ≤ M)
    (henergy : ∀ q : ι → ℝ, (∑ i, q i) = 0 →
      quad W.kernel q ≤ M * ∑ i, q i ^ 2)
    (t : ℕ) (ht : 2 ≤ t) (hnt : 2 * t < Fintype.card ι) :
    ∃ (Z : Finset ι) (β : ℝ) (bad : ι → Finset ι),
      Z.card ≤ t ∧ 0 ≤ β ∧ (∀ i, (bad i).card ≤ t) ∧
      (∀ i j, j ∈ bad i ↔ i ∈ bad j) ∧
      ∀ i j, i ≠ j → i ∉ Z → j ∉ Z → j ∉ bad i →
        β ≤ W.kernel i j ∧ W.kernel i j ≤ β + 2 * M / (t : ℝ) := by
  have htpos : 0 < t := by omega
  obtain ⟨Z, hZ, hlarge⟩ := Pruning126.exists_exceptional W htpos hnt
  refine ⟨Z, Pruning126.baseline W t, Pruning126.smallNeighbours W t,
    hZ.le, Pruning126.baseline_nonneg W t, Pruning126.smallNeighbours_card_le W t,
    Pruning126.smallNeighbours_symm W t, ?_⟩
  intro i j _hij hi hj hbad
  have heq := Pruning126.kernel_eq_baseline_add W t i j
    (fun B hB hBt => ⟨hlarge B hB hBt i hi, hlarge B hB hBt j hj⟩)
  rw [heq]
  constructor
  · apply le_add_of_nonneg_right
    apply Finset.sum_nonneg
    intro B hB
    exact W.weight_nonneg B (Finset.mem_filter.mp hB).1
  · exact add_le_add le_rfl
      (Pruning126.residual_weight_le W hM henergy htpos (by omega) i j hbad)

end
end E126

/-
# An elementary bound for weighted sign Gram kernels

For nonnegative weights of positive total mass, signs with square one, and
`2 * card κ * G i j ≤ ∑ p, β p` off the diagonal, the number of vertices is at
most `4 * card κ`. The proof uses finite sums, Cauchy–Schwarz for the weights,
and the polynomial `(x + B) * (2 * s * x - B)`. No matrix rank, spectral theorem,
or Euclidean embedding is used.
-/

open scoped BigOperators NNReal

namespace E126.Spherical126

noncomputable section

variable {ι κ : Type*} [Fintype κ]

/-- The weighted sign Gram kernel; arbitrary real features are allowed here. -/
def gram (β : κ → ℝ) (σ : κ → ι → ℝ) (i j : ι) : ℝ :=
  ∑ p, β p * σ p i * σ p j

/-- Square-one signs make the diagonal equal to the total weight. -/
theorem gram_diag (β : κ → ℝ) (σ : κ → ι → ℝ)
    (hσ : ∀ p i, σ p i ^ 2 = 1) (i : ι) :
    gram β σ i i = ∑ p, β p := by
  simp only [gram, mul_assoc, ← pow_two, hσ, mul_one]

/-- Every entry is at least minus the total weight. -/
theorem neg_sum_le_gram (β : κ → ℝ) (σ : κ → ι → ℝ)
    (hβ : ∀ p, 0 ≤ β p) (hσ : ∀ p i, σ p i ^ 2 = 1) (i j : ι) :
    -(∑ p, β p) ≤ gram β σ i j := by
  calc
    -(∑ p, β p) = ∑ p, β p * (-1) := by simp
    _ ≤ gram β σ i j := by
      apply Finset.sum_le_sum
      intro p hp
      have hprod : -1 ≤ σ p i * σ p j := by
        nlinarith [sq_nonneg (σ p i + σ p j), hσ p i, hσ p j]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod (hβ p)

variable [Fintype ι]

/-- The sum of a weighted Gram kernel is a weighted sum of squares. -/
theorem sum_gram_eq (β : κ → ℝ) (σ : κ → ι → ℝ) :
    (∑ i, ∑ j, gram β σ i j) = ∑ p, β p * (∑ i, σ p i) ^ 2 := by
  classical
  unfold gram
  calc
    (∑ i, ∑ j, ∑ p, β p * σ p i * σ p j) =
        ∑ i, ∑ p, ∑ j, β p * σ p i * σ p j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ p, ∑ i, ∑ j, β p * σ p i * σ p j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [pow_two, Finset.sum_mul_sum]
      simp only [Finset.mul_sum, mul_assoc]

/-- Nonnegative weights imply a nonnegative sum of Gram entries. -/
theorem sum_gram_nonneg (β : κ → ℝ) (σ : κ → ι → ℝ)
    (hβ : ∀ p, 0 ≤ β p) : 0 ≤ ∑ i, ∑ j, gram β σ i j := by
  rw [sum_gram_eq]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hβ p) (sq_nonneg _)

/-- Expanding the square interchanges the vertex and feature Gram kernels. -/
theorem sum_sq_gram_eq (β : κ → ℝ) (σ : κ → ι → ℝ) :
    (∑ i, ∑ j, gram β σ i j ^ 2) =
      ∑ p, ∑ q, β p * β q * (∑ i, σ p i * σ q i) ^ 2 := by
  classical
  have hsq (i j : ι) : gram β σ i j ^ 2 =
      gram (fun pq : κ × κ => β pq.1 * β pq.2)
        (fun pq i => σ pq.1 i * σ pq.2 i) i j := by
    simp only [gram, pow_two, Finset.sum_mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    ring
  simp_rw [hsq]
  rw [sum_gram_eq]
  simp only [Fintype.sum_prod_type]

/-- Keeping only equal-feature terms gives the elementary trace lower bound. -/
theorem card_sq_mul_sum_sq_le_sum_sq_gram (β : κ → ℝ) (σ : κ → ι → ℝ)
    (hβ : ∀ p, 0 ≤ β p) (hσ : ∀ p i, σ p i ^ 2 = 1) :
    (Fintype.card ι : ℝ) ^ 2 * (∑ p, β p ^ 2) ≤
      ∑ i, ∑ j, gram β σ i j ^ 2 := by
  classical
  have hinner (p : κ) : (∑ i, σ p i * σ p i) = (Fintype.card ι : ℝ) := by
    simp only [← pow_two, hσ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
  rw [sum_sq_gram_eq]
  calc
    (Fintype.card ι : ℝ) ^ 2 * (∑ p, β p ^ 2) =
        ∑ p, β p * β p * (∑ i, σ p i * σ p i) ^ 2 := by
      simp_rw [hinner, ← pow_two, ← Finset.sum_mul]
      ring
    _ ≤ ∑ p, ∑ q, β p * β q * (∑ i, σ p i * σ q i) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      exact Finset.single_le_sum
        (fun q _ => mul_nonneg (mul_nonneg (hβ p) (hβ q))
          (sq_nonneg (∑ i, σ p i * σ q i)))
        (Finset.mem_univ p)

/-- Finite Cauchy–Schwarz converts the sum of squared weights into total mass.
This is the usual Gram trace/rank inequality, with denominators cleared. -/
theorem trace_sq_le (β : κ → ℝ) (σ : κ → ι → ℝ)
    (hβ : ∀ p, 0 ≤ β p) (hσ : ∀ p i, σ p i ^ 2 = 1) :
    (Fintype.card ι : ℝ) ^ 2 * (∑ p, β p) ^ 2 ≤
      (Fintype.card κ : ℝ) * (∑ i, ∑ j, gram β σ i j ^ 2) := by
  have hCS : (∑ p, β p) ^ 2 ≤ (Fintype.card κ : ℝ) * (∑ p, β p ^ 2) := by
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset κ) (fun _ => (1 : ℝ)) β
  calc
    (Fintype.card ι : ℝ) ^ 2 * (∑ p, β p) ^ 2 ≤
        (Fintype.card ι : ℝ) ^ 2 * ((Fintype.card κ : ℝ) * (∑ p, β p ^ 2)) :=
      mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ = (Fintype.card κ : ℝ) * ((Fintype.card ι : ℝ) ^ 2 * (∑ p, β p ^ 2)) := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (card_sq_mul_sum_sq_le_sum_sq_gram β σ hβ hσ) (Nat.cast_nonneg _)

/-- Almost-obtuse weighted sign vectors have at most four times as many vertices
as features. The off-diagonal hypothesis has no divisions. Positive total mass
already forces the feature type to be nonempty; the vertex type may be empty. -/
theorem card_le_four_mul (β : κ → ℝ) (σ : κ → ι → ℝ)
    (hβ : ∀ p, 0 ≤ β p) (hσ : ∀ p i, σ p i ^ 2 = 1)
    (hB : 0 < ∑ p, β p)
    (hoff : ∀ i j, i ≠ j →
      2 * (Fintype.card κ : ℝ) * gram β σ i j ≤ ∑ p, β p) :
    Fintype.card ι ≤ 4 * Fintype.card κ := by
  classical
  by_cases hι : Fintype.card ι = 0
  · simp [hι]
  let N : ℝ := Fintype.card ι
  let s : ℝ := Fintype.card κ
  let B : ℝ := ∑ p, β p
  let G := gram β σ
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero hι
  have hs : 1 ≤ s := by
    have hc : 1 ≤ Fintype.card κ := by
      by_contra hc
      haveI : IsEmpty κ := Fintype.card_eq_zero_iff.mp (by omega)
      simp at hB
    dsimp [s]
    exact_mod_cast hc
  have hB' : 0 < B := hB
  have hsum : 0 ≤ ∑ i, ∑ j, G i j := sum_gram_nonneg β σ hβ
  have htrace : N ^ 2 * B ^ 2 ≤ s * (∑ i, ∑ j, G i j ^ 2) :=
    trace_sq_le β σ hβ hσ
  have hcoef : 0 ≤ (2 * s - 1) * B * (∑ i, ∑ j, G i j) :=
    mul_nonneg (mul_nonneg (by linarith) hB'.le) hsum
  let f : ℝ → ℝ := fun x => (x + B) * (2 * s * x - B)
  have hupper : (∑ i, ∑ j, f (G i j)) ≤ N * (4 * s * B ^ 2) := by
    calc
      (∑ i, ∑ j, f (G i j)) ≤
          ∑ i : ι, ∑ j : ι, if i = j then 4 * s * B ^ 2 else 0 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        split_ifs with hij
        · subst j
          have hdiag : G i i = B := gram_diag β σ hσ i
          dsimp only [f]
          rw [hdiag]
          nlinarith [sq_nonneg B]
        · have hlow : -B ≤ G i j := neg_sum_le_gram β σ hβ hσ i j
          have hhigh : 2 * s * G i j ≤ B := hoff i j hij
          exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      _ = N * (4 * s * B ^ 2) := by simp [N]
  have hpoly : (∑ i, ∑ j, f (G i j)) =
      2 * s * (∑ i, ∑ j, G i j ^ 2) +
        (2 * s - 1) * B * (∑ i, ∑ j, G i j) - B ^ 2 * N ^ 2 := by
    have hf (i j : ι) : f (G i j) =
        2 * s * G i j ^ 2 + (2 * s - 1) * B * G i j - B ^ 2 := by
      dsimp only [f]
      ring
    simp_rw [hf, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    dsimp only [N]
    ring
  rw [hpoly] at hupper
  have hbound : B ^ 2 * N ^ 2 ≤ B ^ 2 * (4 * s * N) := by
    nlinarith only [htrace, hcoef, hupper]
  have hcancel := le_of_mul_le_mul_left hbound (sq_pos_of_pos hB')
  have hcard : N ≤ 4 * s :=
    le_of_mul_le_mul_right (by simpa only [pow_two] using hcancel) hN
  change (Fintype.card ι : ℝ) ≤ 4 * (Fintype.card κ : ℝ) at hcard
  exact_mod_cast hcard

/-- The same bound with the original divided off-diagonal hypothesis. -/
theorem card_le_four_mul_of_div (β : κ → ℝ) (σ : κ → ι → ℝ)
    (hβ : ∀ p, 0 ≤ β p) (hσ : ∀ p i, σ p i ^ 2 = 1)
    (hB : 0 < ∑ p, β p)
    (hoff : ∀ i j, i ≠ j →
      gram β σ i j ≤ (∑ p, β p) / (2 * (Fintype.card κ : ℝ))) :
    Fintype.card ι ≤ 4 * Fintype.card κ := by
  have hs : 0 < Fintype.card κ := by
    simpa only [Finset.card_univ] using
      Finset.card_pos.mpr (Finset.nonempty_of_sum_ne_zero (ne_of_gt hB))
  have hd : 0 < 2 * (Fintype.card κ : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr hs)
  apply card_le_four_mul β σ hβ hσ hB
  intro i j hij
  simpa only [mul_comm] using (le_div_iff₀ hd).mp (hoff i j hij)

/-- The nonnegative-real weight interface to the denominator-free bound. -/
theorem card_le_four_mul_nnreal (β : κ → ℝ≥0) (σ : κ → ι → ℝ)
    (hσ : ∀ p i, σ p i ^ 2 = 1) (hB : 0 < ∑ p, (β p : ℝ))
    (hoff : ∀ i j, i ≠ j →
      2 * (Fintype.card κ : ℝ) * gram (fun p => (β p : ℝ)) σ i j ≤
        ∑ p, (β p : ℝ)) :
    Fintype.card ι ≤ 4 * Fintype.card κ :=
  card_le_four_mul (fun p => (β p : ℝ)) σ (fun p => (β p).coe_nonneg) hσ hB hoff

/-- Nonnegative-real weights and the divided off-diagonal hypothesis. -/
theorem card_le_four_mul_nnreal_of_div (β : κ → ℝ≥0) (σ : κ → ι → ℝ)
    (hσ : ∀ p i, σ p i ^ 2 = 1) (hB : 0 < ∑ p, (β p : ℝ))
    (hoff : ∀ i j, i ≠ j →
      gram (fun p => (β p : ℝ)) σ i j ≤
        (∑ p, (β p : ℝ)) / (2 * (Fintype.card κ : ℝ))) :
    Fintype.card ι ≤ 4 * Fintype.card κ :=
  card_le_four_mul_of_div (fun p => (β p : ℝ)) σ
    (fun p => (β p).coe_nonneg) hσ hB hoff

/-- Restriction to a finite vertex set, with no finiteness assumption on its
ambient type. Only signs and off-diagonal bounds on that set are needed. -/
theorem card_finset_le_four_mul {α : Type*} (T : Finset α)
    (β : κ → ℝ) (σ : κ → α → ℝ)
    (hβ : ∀ p, 0 ≤ β p) (hσ : ∀ p i, i ∈ T → σ p i ^ 2 = 1)
    (hB : 0 < ∑ p, β p)
    (hoff : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      2 * (Fintype.card κ : ℝ) * gram β σ i j ≤ ∑ p, β p) :
    T.card ≤ 4 * Fintype.card κ := by
  classical
  simpa only [Fintype.card_coe] using
    card_le_four_mul β (fun p (i : T) => σ p i)
      hβ (fun p i => hσ p i i.property) hB
      (fun i j hij => hoff i i.property j j.property (fun h => hij (Subtype.ext h)))

end

end E126.Spherical126

/- A finite packing estimate for symmetric forbidden neighborhoods. -/

namespace E126.Packing126

variable {ι : Type*} [DecidableEq ι]

def Independent (bad : ι → Finset ι) (T : Finset ι) : Prop :=
  ∀ i ∈ T, ∀ j ∈ T, i ≠ j → j ∉ bad i

/-- A maximal independent set and its forbidden neighborhoods cover the ambient set. -/
theorem card_le (Y : Finset ι) (bad : ι → Finset ι)
    (hsymm : ∀ i j, j ∈ bad i ↔ i ∈ bad j)
    (d k : ℕ) (hdegree : ∀ i, (bad i).card ≤ d)
    (hind : ∀ T ⊆ Y, Independent bad T → T.card ≤ k) :
    Y.card ≤ k * (d + 1) := by
  classical
  let S := Y.powerset.filter (Independent bad)
  have hS : S.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    simp [Independent]
  obtain ⟨T, hT, hmax⟩ := S.exists_max_image Finset.card hS
  obtain ⟨hTY, hTi⟩ := Finset.mem_filter.mp hT
  have hTY' : T ⊆ Y := Finset.mem_powerset.mp hTY
  have hcover : Y ⊆ T.biUnion (fun i => insert i (bad i)) := by
    intro y hy
    by_contra hnot
    have hyT : y ∉ T := by
      intro hyT
      exact hnot (Finset.mem_biUnion.mpr ⟨y, hyT, Finset.mem_insert_self _ _⟩)
    have hybad : ∀ i ∈ T, y ∉ bad i := by
      intro i hi hbad
      exact hnot (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_insert_of_mem hbad⟩)
    have hnew : Independent bad (insert y T) := by
      intro i hi j hj hij
      by_cases hiy : i = y
      · subst i
        have hjT : j ∈ T := (Finset.mem_insert.mp hj).resolve_left (Ne.symm hij)
        exact fun h => hybad j hjT ((hsymm y j).mp h)
      · have hiT : i ∈ T := (Finset.mem_insert.mp hi).resolve_left hiy
        by_cases hjy : j = y
        · subst j
          exact hybad i hiT
        · have hjT : j ∈ T := (Finset.mem_insert.mp hj).resolve_left hjy
          exact hTi i hiT j hjT hij
    have hmem : insert y T ∈ S := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr (Finset.insert_subset hy hTY'), hnew⟩
    have hc := hmax (insert y T) hmem
    rw [Finset.card_insert_of_notMem hyT] at hc
    omega
  calc
    Y.card ≤ (T.biUnion (fun i => insert i (bad i))).card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ T, (insert i (bad i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ T, (d + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.card_insert_le i (bad i)).trans (Nat.add_le_add_right (hdegree i) 1)
    _ = T.card * (d + 1) := by simp
    _ ≤ k * (d + 1) := Nat.mul_le_mul_right _ (hind T hTY' hTi)

end E126.Packing126

/- Polynomial capacity of signed laminar families satisfying the two global inequalities. -/

open scoped BigOperators

namespace E126

noncomputable section

variable {ι κ : Type*} [DecidableEq ι] [Fintype ι] [Fintype κ]

namespace Capacity126

/-- On a set where all kernels are approximately flat, the sign vectors form
an almost-obtuse code. The diameter bound supplies the missing baseline mass. -/
theorem flat_independent_bound (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j < 0)
    (hCND : CND (totalOpposition W))
    (a b : ι) (L : ℝ) (hLab : totalOpposition W a b = L) (hL : 0 < L)
    (β : κ → ℝ) (hβ : ∀ p, 0 ≤ β p) (e : ℝ) (he : 0 ≤ e)
    (hsmall : 16 * (Fintype.card κ : ℝ) ^ 2 * e ≤ L)
    (T : Finset ι)
    (hF : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → totalOpposition W i j ≤ (∑ p, β p) + e)
    (hR : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      Spherical126.gram β (fun p => (W p).signVal) i j ≤ e) :
    T.card ≤ 4 * Fintype.card κ := by
  by_cases hc : T.card ≤ 2 * Fintype.card κ
  · omega
  have hc' : 2 * Fintype.card κ < T.card := by omega
  have hB : 0 ≤ ∑ p, β p := Finset.sum_nonneg (fun p _ => hβ p)
  have hd := totalOpposition_diameter_bound_of_offDiag W hV hCND T ((∑ p, β p) + e)
    (add_nonneg hB he) hF hc' a b
  rw [hLab] at hd
  have hsN : 0 < Fintype.card κ := by
    by_contra h
    have hz : Fintype.card κ = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero, zero_mul] at hd
    linarith
  have hs : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast hsN
  have hs0 : (0 : ℝ) < Fintype.card κ := by exact_mod_cast hsN
  have haux : 4 * (Fintype.card κ : ℝ) * e ≤ (∑ p, β p) + e := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * (Fintype.card κ : ℝ) by positivity)).mp
    nlinarith only [hsmall, hd]
  have hse : e ≤ (Fintype.card κ : ℝ) * e := by nlinarith only [mul_le_mul_of_nonneg_right hs he]
  have hBpos : 0 < ∑ p, β p := by
    by_contra h
    have hBn : (∑ p, β p) ≤ 0 := le_of_not_gt h
    have he0 : e = 0 := by nlinarith only [haux, hse, he, hBn]
    have hmul : 4 * (Fintype.card κ : ℝ) * (∑ p, β p) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hBn
    rw [he0, add_zero] at hd
    linarith
  have heB : 2 * (Fintype.card κ : ℝ) * e ≤ ∑ p, β p := by
    nlinarith only [haux, hse, he]
  apply Spherical126.card_finset_le_four_mul T β (fun p => (W p).signVal) hβ
    (fun p i _ => (W p).signVal_sq i) hBpos
  intro i hi j hj hij
  exact (mul_le_mul_of_nonneg_left (hR i hi j hj hij) (by positivity)).trans heB

omit [Fintype ι] in
/-- Approximation of an unsigned entry also approximates its signed entry. -/
theorem signed_approx (W : OppositionFamily ι) (i j : ι) (β r : ℝ)
    (hlo : β ≤ W.unsigned i j) (hhi : W.unsigned i j ≤ β + r) :
    W.signed i j ≤ β * W.signVal i * W.signVal j + r ∧
      β * W.signVal i * W.signVal j ≤ W.signed i j + r := by
  cases hi : W.sign i <;> cases hj : W.sign j <;>
    simp [OppositionFamily.signed, OppositionFamily.signVal, hi, hj] <;> constructor <;> linarith

/-- The numerical budget used in the pruning step. -/
theorem error_budget (s : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    16 * (s : ℝ) ^ 2 * ((s : ℝ) * (2 * (2 * (s : ℝ) * L) /
      ((64 * (s + 1) ^ 4 : ℕ) : ℝ))) ≤ L := by
  have ht : (0 : ℝ) < ((64 * (s + 1) ^ 4 : ℕ) : ℝ) := by positivity
  have hp : (s : ℝ) ^ 4 ≤ ((s : ℝ) + 1) ^ 4 := by gcongr; norm_num
  have hh : 64 * (s : ℝ) ^ 4 * L ≤ ((64 * (s + 1) ^ 4 : ℕ) : ℝ) * L := by
    push_cast
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num)) hL
  calc
    _ = (64 * (s : ℝ) ^ 4 * L) / ((64 * (s + 1) ^ 4 : ℕ) : ℝ) := by ring
    _ ≤ L := (div_le_iff₀ ht).mpr (by nlinarith only [hh])

/-- A generous integer bound, chosen to keep the eventual limit transfer simple. -/
theorem count_budget (s n : ℕ)
    (h : n ≤ s * (64 * (s + 1) ^ 4) +
      (4 * s) * (s * (64 * (s + 1) ^ 4) + 1)) :
    n ≤ 1024 * (s + 1) ^ 8 := by
  have hw : 1 ≤ s + 1 := by omega
  have hp : (s + 1) ^ 6 ≤ (s + 1) ^ 8 := Nat.pow_le_pow_right hw (by decide)
  have hpow : s + 1 ≤ (s + 1) ^ 6 := by
    calc
      s + 1 = (s + 1) ^ 1 := by simp
      _ ≤ (s + 1) ^ 6 := Nat.pow_le_pow_right hw (by decide)
  have hs1 : s ≤ (s + 1) ^ 2 := by nlinarith
  have hs2 : s ^ 2 ≤ (s + 1) ^ 2 := Nat.pow_le_pow_left (by omega) _
  have h1 : s * (64 * (s + 1) ^ 4) ≤ 64 * (s + 1) ^ 6 := by
    calc
      _ ≤ (s + 1) ^ 2 * (64 * (s + 1) ^ 4) := Nat.mul_le_mul_right _ hs1
      _ = _ := by ring
  have h2 : (4 * s) * (s * (64 * (s + 1) ^ 4) + 1) ≤
      256 * (s + 1) ^ 6 + 4 * (s + 1) := by
    calc
      _ = s ^ 2 * (256 * (s + 1) ^ 4) + 4 * s := by ring
      _ ≤ (s + 1) ^ 2 * (256 * (s + 1) ^ 4) + 4 * (s + 1) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hs2) (Nat.mul_le_mul_left _ (by omega))
      _ = _ := by ring
  omega

end Capacity126

/-- Polynomial capacity for all finite opposition-tree families. -/
theorem opposition_capacity (W : κ → OppositionFamily ι)
    (hV : ∀ i j, i ≠ j → totalSigned W i j < 0)
    (hCND : CND (totalOpposition W)) :
    Fintype.card ι ≤ 1024 * (Fintype.card κ + 1) ^ 8 := by
  classical
  let s := Fintype.card κ
  let t := 64 * (s + 1) ^ 4
  have ht : 2 ≤ t := by dsimp [t]; nlinarith [Nat.one_le_pow 4 (s + 1) (by omega)]
  by_cases hn : Fintype.card ι ≤ 2 * t
  · have hw : 1 ≤ s + 1 := by omega
    have hp : (s + 1) ^ 4 ≤ (s + 1) ^ 8 := Nat.pow_le_pow_right hw (by decide)
    dsimp [t] at hn
    change Fintype.card ι ≤ 1024 * (s + 1) ^ 8
    nlinarith
  have hnt : 2 * t < Fintype.card ι := by omega
  have hι : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  letI : Nonempty ι := hι
  obtain ⟨ab, _, hab⟩ := (Finset.univ : Finset (ι × ι)).exists_max_image
    (fun x => totalOpposition W x.1 x.2) Finset.univ_nonempty
  let L := totalOpposition W ab.1 ab.2
  have hmax : ∀ i j, totalOpposition W i j ≤ L := fun i j => hab (i, j) (Finset.mem_univ _)
  have hL : 0 < L := by
    have htwo : 1 < Fintype.card ι := by omega
    obtain ⟨i, j, hij⟩ := Fintype.one_lt_card_iff.mp htwo
    have hU : 0 ≤ totalUnsigned W i j :=
      Finset.sum_nonneg (fun p _ => (W p).unsigned_nonneg i j)
    have heq := totalOpposition_eq W i j
    have hv := hV i j hij
    have hb := hmax i j
    linarith
  let M : ℝ := 2 * (s : ℝ) * L
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpr (p : κ) := (W p).toLaminarFamily.pruning hM
    (fun q hq => unsigned_energy_bound W hV hCND L hmax p q hq) t ht hnt
  choose Z β bad hZ hβ hbad hsym happ using hpr
  let Zall : Finset ι := Finset.univ.biUnion Z
  let badall : ι → Finset ι := fun i => Finset.univ.biUnion (fun p => bad p i)
  let Y : Finset ι := Finset.univ \ Zall
  have hZall : Zall.card ≤ s * t := by
    calc
      _ ≤ ∑ p : κ, (Z p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p : κ, t := Finset.sum_le_sum (fun p _ => hZ p)
      _ = _ := by simp [s]
  have hbadall : ∀ i, (badall i).card ≤ s * t := by
    intro i
    calc
      _ ≤ ∑ p : κ, (bad p i).card := Finset.card_biUnion_le
      _ ≤ ∑ _p : κ, t := Finset.sum_le_sum (fun p _ => hbad p i)
      _ = _ := by simp [s]
  have hsymall : ∀ i j, j ∈ badall i ↔ i ∈ badall j := by
    intro i j
    simp only [badall, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact exists_congr (fun p => hsym p i j)
  let r : ℝ := 2 * M / (t : ℝ)
  let e : ℝ := (s : ℝ) * r
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hsmall : 16 * (Fintype.card κ : ℝ) ^ 2 * e ≤ L :=
    Capacity126.error_budget s L hL.le
  have hind : ∀ T ⊆ Y, Packing126.Independent badall T → T.card ≤ 4 * s := by
    intro T hTY hTi
    have hlocal : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ∀ p,
        β p ≤ (W p).unsigned i j ∧ (W p).unsigned i j ≤ β p + r := by
      intro i hi j hj hij p
      have hiz : i ∉ Zall := (Finset.mem_sdiff.mp (hTY hi)).2
      have hjz : j ∉ Zall := (Finset.mem_sdiff.mp (hTY hj)).2
      have hb : j ∉ badall i := hTi i hi j hj hij
      apply happ p i j hij
      · exact fun h => hiz (Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, h⟩)
      · exact fun h => hjz (Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, h⟩)
      · exact fun h => hb (Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, h⟩)
    apply Capacity126.flat_independent_bound W hV hCND ab.1 ab.2 L rfl hL β hβ e he hsmall T
    · intro i hi j hj hij
      calc
        totalOpposition W i j ≤ ∑ p, (β p + r) := by
          apply Finset.sum_le_sum
          intro p hp
          have hu := (hlocal i hi j hj hij p).2
          have hβr := add_nonneg (hβ p) hr
          unfold OppositionFamily.opposition
          split <;> assumption
        _ = (∑ p, β p) + e := by simp [Finset.sum_add_distrib, e, s]
    · intro i hi j hj hij
      have hsum : Spherical126.gram β (fun p => (W p).signVal) i j ≤
          totalSigned W i j + e := by
        calc
          _ ≤ ∑ p, ((W p).signed i j + r) := by
            apply Finset.sum_le_sum
            intro p hp
            exact (Capacity126.signed_approx (W p) i j (β p) r
              (hlocal i hi j hj hij p).1 (hlocal i hi j hj hij p).2).2
          _ = _ := by simp [Finset.sum_add_distrib, totalSigned, e, s]
      exact hsum.trans (by linarith [hV i j hij])
  have hY : Y.card ≤ (4 * s) * (s * t + 1) :=
    Packing126.card_le Y badall hsymall (s * t) (4 * s) hbadall hind
  have hcard : Fintype.card ι = Y.card + Zall.card := by
    simpa [Y] using (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ Zall)).symm
  apply Capacity126.count_budget s (Fintype.card ι)
  dsimp [t] at hY hZall
  omega

end
end E126

/-
# Finite opposition families from refining partitions

At each level we retain the bichromatic classes of a partition.  Repeated
supports are compressed by adding their weights, not by deleting occurrences.
This module is independent of the arithmetic used to supply the labels.
-/

open scoped BigOperators

namespace E126.ArithmeticCells126

noncomputable section

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

/-- A class of the partition at level `n`. -/
def cell (f : ℕ → ι → κ) (n : ℕ) (i : ι) : Finset ι :=
  Finset.univ.filter (fun j => f n j = f n i)

omit [DecidableEq ι] in
@[simp] theorem mem_cell (f : ℕ → ι → κ) (n : ℕ) (i j : ι) :
    j ∈ cell f n i ↔ f n j = f n i := by
  simp [cell]

omit [DecidableEq ι] in
@[simp] theorem self_mem_cell (f : ℕ → ι → κ) (n : ℕ) (i : ι) :
    i ∈ cell f n i := by simp

omit [DecidableEq ι] in
lemma cell_eq_of_mem {f : ℕ → ι → κ} {n : ℕ} {i j : ι}
    (h : j ∈ cell f n i) : cell f n j = cell f n i := by
  have he := (mem_cell f n i j).mp h
  ext k
  simp [he]

/-- Activity means that both global colors occur. -/
def Active (σ : ι → Bool) (B : Finset ι) : Prop :=
  ∃ i ∈ B, ∃ j ∈ B, σ i ≠ σ j

instance activeDecidable (σ : ι → Bool) (B : Finset ι) : Decidable (Active σ B) := by
  unfold Active
  infer_instance

omit [Fintype ι] [DecidableEq ι] in
lemma active_bichromatic {σ : ι → Bool} {B : Finset ι} (h : Active σ B)
    {i : ι} (_hi : i ∈ B) : ∃ j ∈ B, σ j ≠ σ i := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  by_cases hui : σ u = σ i
  · exact ⟨v, hv, fun hvi => huv (hui.trans hvi.symm)⟩
  · exact ⟨u, hu, hui⟩

/-- Distinct active supports at one level. -/
def cells (σ : ι → Bool) (f : ℕ → ι → κ) (n : ℕ) : Finset (Finset ι) := by
  classical
  exact (Finset.univ.image (cell f n)).filter (Active σ)

lemma mem_cells {σ : ι → Bool} {f : ℕ → ι → κ} {n : ℕ} {B : Finset ι} :
    B ∈ cells σ f n ↔ (∃ i, cell f n i = B) ∧ Active σ B := by
  classical
  simp [cells]

@[simp] lemma cell_mem_cells {σ : ι → Bool} {f : ℕ → ι → κ} {n : ℕ} {i : ι} :
    cell f n i ∈ cells σ f n ↔ Active σ (cell f n i) := by
  rw [mem_cells]
  exact ⟨And.right, fun h => ⟨⟨i, rfl⟩, h⟩⟩

lemma eq_cell_of_mem {σ : ι → Bool} {f : ℕ → ι → κ} {n : ℕ}
    {B : Finset ι} (hB : B ∈ cells σ f n) {i : ι} (hi : i ∈ B) :
    B = cell f n i := by
  obtain ⟨⟨j, rfl⟩, _⟩ := mem_cells.mp hB
  exact (cell_eq_of_mem hi).symm

/-- All active supports up to a finite depth. -/
def allCells (K : ℕ) (σ : ι → Bool) (f : ℕ → ι → κ) : Finset (Finset ι) :=
  (Finset.range K).biUnion (cells σ f)

lemma cells_subset_allCells {K n : ℕ} (hn : n ∈ Finset.range K)
    (σ : ι → Bool) (f : ℕ → ι → κ) : cells σ f n ⊆ allCells K σ f := by
  intro B hB
  exact Finset.mem_biUnion.mpr ⟨n, hn, hB⟩

lemma allCells_laminar (K : ℕ) (σ : ι → Bool) (f : ℕ → ι → κ)
    (hf : ∀ n m, n ≤ m → ∀ i j, f m i = f m j → f n i = f n j) :
    ∀ B ∈ allCells K σ f, ∀ C ∈ allCells K σ f,
      B ⊆ C ∨ C ⊆ B ∨ Disjoint B C := by
  intro B hB C hC
  obtain ⟨n, hn, hB⟩ := Finset.mem_biUnion.mp hB
  obtain ⟨m, hm, hC⟩ := Finset.mem_biUnion.mp hC
  by_cases hd : Disjoint B C
  · exact Or.inr (Or.inr hd)
  · obtain ⟨i, hiB, hiC⟩ := Finset.not_disjoint_iff.mp hd
    rw [eq_cell_of_mem hB hiB, eq_cell_of_mem hC hiC]
    rcases le_total n m with hnm | hmn
    · right; left
      intro j hj
      exact (mem_cell f n i j).mpr (hf n m hnm j i ((mem_cell f m i j).mp hj))
    · left
      intro j hj
      exact (mem_cell f m i j).mpr (hf m n hmn j i ((mem_cell f n i j).mp hj))

/-- The weight includes every level at which the support occurs. -/
def levelWeight (K : ℕ) (σ : ι → Bool) (f : ℕ → ι → κ)
    (w : ℝ) (B : Finset ι) : ℝ :=
  ∑ n ∈ Finset.range K, if B ∈ cells σ f n then w else 0

/-- Compress a finite refining sequence of bichromatic partitions. -/
def build (K : ℕ) (σ : ι → Bool) (f : ℕ → ι → κ)
    (hf : ∀ n m, n ≤ m → ∀ i j, f m i = f m j → f n i = f n j)
    (w : ℝ) (hw : 0 ≤ w) : OppositionFamily ι where
  nodes := allCells K σ f
  weight := levelWeight K σ f w
  weight_nonneg := by
    intro B hB
    apply Finset.sum_nonneg
    intro n hn
    split_ifs <;> positivity
  laminar := allCells_laminar K σ f hf
  sign := σ
  bichromatic := by
    intro B hB i hi
    obtain ⟨n, hn, hB⟩ := Finset.mem_biUnion.mp hB
    exact active_bichromatic (mem_cells.mp hB).2 hi

lemma layer_kernel (σ : ι → Bool) (f : ℕ → ι → κ) (n : ℕ) (w : ℝ) (i j : ι) :
    (∑ B ∈ cells σ f n, w * ind B i * ind B j) =
      if Active σ (cell f n i) ∧ f n i = f n j then w else 0 := by
  classical
  by_cases hA : Active σ (cell f n i)
  · rw [Finset.sum_eq_single_of_mem (cell f n i) (cell_mem_cells.mpr hA)]
    · by_cases hij : f n i = f n j
      · simp [ind, hA, hij]
      · simp [ind, hA, hij, Ne.symm hij]
    · intro B hB hne
      have hi : i ∉ B := fun hi => hne (eq_cell_of_mem hB hi)
      simp [ind, hi]
  · have hz : ∀ B ∈ cells σ f n, w * ind B i * ind B j = 0 := by
      intro B hB
      have hi : i ∉ B := by
        intro hi
        have he := eq_cell_of_mem hB hi
        exact hA (he ▸ (mem_cells.mp hB).2)
      simp [ind, hi]
    rw [Finset.sum_eq_zero hz]
    simp [hA]

lemma unsigned_eq_sum (K : ℕ) (σ : ι → Bool) (f : ℕ → ι → κ)
    (hf : ∀ n m, n ≤ m → ∀ i j, f m i = f m j → f n i = f n j)
    (w : ℝ) (hw : 0 ≤ w) (i j : ι) :
    (build K σ f hf w hw).unsigned i j =
      ∑ n ∈ Finset.range K,
        if Active σ (cell f n i) ∧ f n i = f n j then w else 0 := by
  classical
  change (∑ B ∈ allCells K σ f,
    (∑ n ∈ Finset.range K, if B ∈ cells σ f n then w else 0) * ind B i * ind B j) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← layer_kernel σ f n w i j]
  symm
  apply Finset.sum_subset_zero_on_sdiff (cells_subset_allCells hn σ f)
  · intro B hB
    simp [(Finset.mem_sdiff.mp hB).2]
  · intro B hB
    simp [hB]

/-- Opposite-colored vertices activate their own class, so no activity test remains. -/
lemma opposition_eq_sum (K : ℕ) (σ : ι → Bool) (f : ℕ → ι → κ)
    (hf : ∀ n m, n ≤ m → ∀ i j, f m i = f m j → f n i = f n j)
    (w : ℝ) (hw : 0 ≤ w) (i j : ι) (hij : σ i ≠ σ j) :
    (build K σ f hf w hw).opposition i j =
      ∑ n ∈ Finset.range K, if f n i = f n j then w else 0 := by
  classical
  change (if σ i = σ j then 0 else (build K σ f hf w hw).unsigned i j) = _
  rw [if_neg hij, unsigned_eq_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases he : f n i = f n j
  · have hA : Active σ (cell f n i) :=
      ⟨i, self_mem_cell f n i, j, (mem_cell f n i j).mpr he.symm, hij⟩
    simp [he, hA]
  · simp [he]

/-- Dropping the activity test only increases the same-side kernel. -/
lemma agreement_le_sum (K : ℕ) (σ : ι → Bool) (f : ℕ → ι → κ)
    (hf : ∀ n m, n ≤ m → ∀ i j, f m i = f m j → f n i = f n j)
    (w : ℝ) (hw : 0 ≤ w) (i j : ι) :
    (build K σ f hf w hw).agreement i j ≤
      ∑ n ∈ Finset.range K, if f n i = f n j then w else 0 := by
  classical
  have hle : (build K σ f hf w hw).agreement i j ≤
      (build K σ f hf w hw).unsigned i j := by
    unfold OppositionFamily.agreement
    split_ifs
    · exact le_rfl
    · exact OppositionFamily.unsigned_nonneg _ _ _
  refine hle.trans ?_
  rw [unsigned_eq_sum]
  apply Finset.sum_le_sum
  intro n hn
  split_ifs <;> simp_all

/-- Counting the initial `e` levels of a tower. -/
lemma sum_initial (K e : ℕ) (w : ℝ) (he : e ≤ K) :
    (∑ n ∈ Finset.range K, if n < e then w else 0) = (e : ℝ) * w := by
  rw [← Finset.sum_filter]
  have hset : (Finset.range K).filter (fun n => n < e) = Finset.range e := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset]
  simp

/-- A truncated initial segment has at most `e` weighted levels. -/
lemma sum_initial_le (K e : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    (∑ n ∈ Finset.range K, if n < e then w else 0) ≤ (e : ℝ) * w := by
  rcases le_total e K with h | h
  · exact (sum_initial K e w h).le
  · have heq : (∑ n ∈ Finset.range K, if n < e then w else 0) = (K : ℝ) * w := by
      calc
        _ = ∑ _n ∈ Finset.range K, w := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [if_pos (lt_of_lt_of_le (Finset.mem_range.mp hn) h)]
        _ = _ := by simp
    rw [heq]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) hw

end

end E126.ArithmeticCells126

/-
# Valuation algebra for the integer opposition model

The correction at two is made before constructing the trees.  All difference
valuations below are taken only for distinct positive inputs.  No asymptotic
conjecture, or declaration from `Submission.Spec`, is used.
-/

namespace E126.ArithmeticValuation126

/-- The exceptional first level at two. -/
def epsilon (p : ℕ) : ℕ := if p = 2 then 1 else 0

lemma factorization_two (p : ℕ) : (2 : ℕ).factorization p = epsilon p := by
  simp [Nat.prime_two.factorization, epsilon, Finsupp.single_apply, eq_comm]

/-- The common valuation, with the extra baseline at two when appropriate. -/
def base (p a b : ℕ) : ℕ :=
  min (a.factorization p) (b.factorization p) +
    if a.factorization p = b.factorization p then epsilon p else 0

lemma base_of_eq {p a b : ℕ} (he : a.factorization p = b.factorization p) :
    base p a b = a.factorization p + epsilon p := by
  simp only [base, ← he, min_self, if_true]

/-- The adjusted normalized-sum exponent. -/
def sumExp (p a b : ℕ) : ℕ := (a + b).factorization p - base p a b

/-- The nonnegative absolute difference, without truncated subtraction. -/
def diff (a b : ℕ) : ℕ := ((a : ℤ) - (b : ℤ)).natAbs

/-- The adjusted normalized-difference exponent. -/
def diffExp (p a b : ℕ) : ℕ := (diff a b).factorization p - base p a b

lemma diff_pos {a b : ℕ} (hab : a ≠ b) : 0 < diff a b := by
  apply Int.natAbs_sub_pos_iff.mpr
  exact_mod_cast hab

lemma diff_lt_sum {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : diff a b < a + b := by
  unfold diff
  rcases le_total a b with h | h
  · rw [Int.natAbs_natCast_sub_natCast_of_le h]
    omega
  · rw [Int.natAbs_natCast_sub_natCast_of_ge h]
    omega

lemma diff_mul (k a b : ℕ) : diff (k * a) (k * b) = k * diff a b := by
  simp [diff, Nat.cast_mul, ← mul_sub, Int.natAbs_mul]

lemma gcd_factorization {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (p : ℕ) :
    (Nat.gcd a b).factorization p = min (a.factorization p) (b.factorization p) := by
  rw [Nat.factorization_gcd ha.ne' hb.ne', Finsupp.inf_apply]

lemma base_eq_gcd_add {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (p : ℕ) :
    base p a b = (Nat.gcd a b).factorization p +
      if p = 2 ∧ a.factorization 2 = b.factorization 2 then 1 else 0 := by
  rw [gcd_factorization ha hb]
  by_cases hp : p = 2
  · subst p
    simp [base, epsilon]
  · simp [base, epsilon, hp]

lemma min_le_sum_factorization {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) :
    min (a.factorization p) (b.factorization p) ≤ (a + b).factorization p := by
  apply (hp.pow_dvd_iff_le_factorization (by omega : a + b ≠ 0)).mp
  exact Nat.dvd_add
    ((pow_dvd_pow p (min_le_left _ _)).trans (Nat.ordProj_dvd a p))
    ((pow_dvd_pow p (min_le_right _ _)).trans (Nat.ordProj_dvd b p))

lemma min_le_diff_factorization {p a b : ℕ} (hp : p.Prime) (hab : a ≠ b) :
    min (a.factorization p) (b.factorization p) ≤ (diff a b).factorization p := by
  apply (hp.pow_dvd_iff_le_factorization (diff_pos hab).ne').mp
  apply Int.natCast_dvd.mp
  apply dvd_sub
  · exact Int.natCast_dvd_natCast.mpr
      ((pow_dvd_pow p (min_le_left _ _)).trans (Nat.ordProj_dvd a p))
  · exact Int.natCast_dvd_natCast.mpr
      ((pow_dvd_pow p (min_le_right _ _)).trans (Nat.ordProj_dvd b p))

/-- The strict valuation dichotomy for a sum (the reverse inequality is automatic). -/
lemma factorization_add_le_of_lt {p a b : ℕ}
    (hp : p.Prime) (ha : a ≠ 0) (hlt : a.factorization p < b.factorization p) :
    (a + b).factorization p ≤ a.factorization p := by
  have hs : a + b ≠ 0 := by omega
  by_contra h
  have hsdiv : p ^ (a.factorization p + 1) ∣ a + b :=
    (hp.pow_dvd_iff_le_factorization hs).2 (by omega)
  have hbdiv : p ^ (a.factorization p + 1) ∣ b :=
    (pow_dvd_pow p (by omega : a.factorization p + 1 ≤ b.factorization p)).trans
      (Nat.ordProj_dvd b p)
  exact Nat.pow_succ_factorization_not_dvd ha hp
    ((Nat.dvd_add_iff_left hbdiv).mpr hsdiv)

lemma add_eq_pow_mul_units {p a b : ℕ} (he : a.factorization p = b.factorization p) :
    a + b = p ^ (a.factorization p) * (ordCompl[p] a + ordCompl[p] b) := by
  calc
    a + b = p ^ (a.factorization p) * ordCompl[p] a +
        p ^ (b.factorization p) * ordCompl[p] b := by
      rw [Nat.ordProj_mul_ordCompl_eq_self, Nat.ordProj_mul_ordCompl_eq_self]
    _ = _ := by rw [← he, mul_add]

lemma diff_eq_pow_mul_units {p a b : ℕ} (he : a.factorization p = b.factorization p) :
    diff a b = p ^ (a.factorization p) * diff (ordCompl[p] a) (ordCompl[p] b) := by
  calc
    diff a b = diff (p ^ (a.factorization p) * ordCompl[p] a)
        (p ^ (a.factorization p) * ordCompl[p] b) := by
      rw [Nat.ordProj_mul_ordCompl_eq_self, he, Nat.ordProj_mul_ordCompl_eq_self]
    _ = _ := diff_mul _ _ _

lemma unit_sum_ne_zero {p a b : ℕ} (ha : 0 < a) :
    ordCompl[p] a + ordCompl[p] b ≠ 0 := by
  exact ne_of_gt (Nat.add_pos_left (Nat.ordCompl_pos p ha.ne') _)

lemma unit_diff_ne_zero {p a b : ℕ} (hab : a ≠ b)
    (he : a.factorization p = b.factorization p) :
    diff (ordCompl[p] a) (ordCompl[p] b) ≠ 0 := by
  intro hz
  have h := diff_pos hab
  rw [diff_eq_pow_mul_units he, hz, mul_zero] at h
  omega

lemma sum_factorization_of_eq {p a b : ℕ} (hp : p.Prime) (ha : 0 < a)
    (he : a.factorization p = b.factorization p) :
    (a + b).factorization p = a.factorization p +
      (ordCompl[p] a + ordCompl[p] b).factorization p := by
  conv_lhs => rw [add_eq_pow_mul_units he]
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (unit_sum_ne_zero ha),
    Finsupp.add_apply, Nat.factorization_pow_self hp]

lemma diff_factorization_of_eq {p a b : ℕ} (hp : p.Prime) (hab : a ≠ b)
    (he : a.factorization p = b.factorization p) :
    (diff a b).factorization p = a.factorization p +
      (diff (ordCompl[p] a) (ordCompl[p] b)).factorization p := by
  rw [diff_eq_pow_mul_units he,
    Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (unit_diff_ne_zero hab he),
    Finsupp.add_apply, Nat.factorization_pow_self hp]

lemma two_dvd_add_of_odd {u v : ℕ} (hu : ¬2 ∣ u) (hv : ¬2 ∣ v) : 2 ∣ u + v := by
  have hu' : u % 2 ≠ 0 := fun h => hu (Nat.dvd_of_mod_eq_zero h)
  have hv' : v % 2 ≠ 0 := fun h => hv (Nat.dvd_of_mod_eq_zero h)
  apply Nat.dvd_of_mod_eq_zero
  omega

lemma two_dvd_diff_of_odd {u v : ℕ} (hu : ¬2 ∣ u) (hv : ¬2 ∣ v) : 2 ∣ diff u v := by
  have hu' : u % 2 ≠ 0 := fun h => hu (Nat.dvd_of_mod_eq_zero h)
  have hv' : v % 2 ≠ 0 := fun h => hv (Nat.dvd_of_mod_eq_zero h)
  have hm : (v : ℤ) ≡ (u : ℤ) [ZMOD (2 : ℕ)] := by
    apply Int.natCast_modEq_iff.mpr
    change v % 2 = u % 2
    omega
  exact Int.natCast_dvd.mp hm.dvd

lemma epsilon_le_unit_sum {p a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    epsilon p ≤ (ordCompl[p] a + ordCompl[p] b).factorization p := by
  by_cases hp : p = 2
  · subst p
    change 1 ≤ _
    apply (Nat.prime_two.pow_dvd_iff_le_factorization (unit_sum_ne_zero ha)).mp
    simpa using two_dvd_add_of_odd
      (Nat.not_dvd_ordCompl Nat.prime_two ha.ne') (Nat.not_dvd_ordCompl Nat.prime_two hb.ne')
  · simp [epsilon, hp]

lemma epsilon_le_unit_diff {p a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (he : a.factorization p = b.factorization p) :
    epsilon p ≤ (diff (ordCompl[p] a) (ordCompl[p] b)).factorization p := by
  by_cases hp : p = 2
  · subst p
    change 1 ≤ _
    apply (Nat.prime_two.pow_dvd_iff_le_factorization (unit_diff_ne_zero hab he)).mp
    simpa using two_dvd_diff_of_odd
      (Nat.not_dvd_ordCompl Nat.prime_two ha.ne') (Nat.not_dvd_ordCompl Nat.prime_two hb.ne')
  · simp [epsilon, hp]

lemma base_le_sum {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) :
    base p a b ≤ (a + b).factorization p := by
  by_cases he : a.factorization p = b.factorization p
  · rw [sum_factorization_of_eq hp ha he]
    have h := epsilon_le_unit_sum (p := p) ha hb
    rw [base_of_eq he]
    exact Nat.add_le_add_left h _
  · simpa [base, he] using min_le_sum_factorization hp ha hb

lemma base_le_diff {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    base p a b ≤ (diff a b).factorization p := by
  by_cases he : a.factorization p = b.factorization p
  · rw [diff_factorization_of_eq hp hab he]
    have h := epsilon_le_unit_diff ha hb hab he
    rw [base_of_eq he]
    exact Nat.add_le_add_left h _
  · simpa [base, he] using min_le_diff_factorization hp hab

lemma sumExp_of_ne {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (he : a.factorization p ≠ b.factorization p) : sumExp p a b = 0 := by
  unfold sumExp base
  rw [if_neg he, add_zero]
  apply Nat.sub_eq_zero_of_le
  rcases lt_or_gt_of_ne he with hlt | hgt
  · rw [min_eq_left hlt.le]
    exact factorization_add_le_of_lt hp ha.ne' hlt
  · rw [min_eq_right hgt.le, Nat.add_comm a b]
    exact factorization_add_le_of_lt hp hb.ne' hgt

lemma sumExp_of_eq {p a b : ℕ} (hp : p.Prime) (ha : 0 < a)
    (he : a.factorization p = b.factorization p) :
    sumExp p a b = (ordCompl[p] a + ordCompl[p] b).factorization p - epsilon p := by
  rw [sumExp, sum_factorization_of_eq hp ha he, base_of_eq he, Nat.add_sub_add_left]

lemma diffExp_of_eq {p a b : ℕ} (hp : p.Prime) (hab : a ≠ b)
    (he : a.factorization p = b.factorization p) :
    diffExp p a b = (diff (ordCompl[p] a) (ordCompl[p] b)).factorization p - epsilon p := by
  rw [diffExp, diff_factorization_of_eq hp hab he, base_of_eq he, Nat.add_sub_add_left]

/-- The threshold characterization, with levels numbered from zero. -/
lemma sumExp_threshold {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    n < sumExp p a b ↔ a.factorization p = b.factorization p ∧
      p ^ (n + 1 + epsilon p) ∣ ordCompl[p] a + ordCompl[p] b := by
  by_cases he : a.factorization p = b.factorization p
  · rw [sumExp_of_eq hp ha he, and_iff_right he,
      hp.pow_dvd_iff_le_factorization (unit_sum_ne_zero ha)]
    omega
  · simp [sumExp_of_ne hp ha hb he, he]

lemma same_color_sumExp_zero {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hc : Signature126.primeColor p a = Signature126.primeColor p b) :
    sumExp p a b = 0 := by
  by_cases he : a.factorization p = b.factorization p
  · rw [sumExp_of_eq hp ha he]
    apply Nat.sub_eq_zero_of_le
    rw [← factorization_two]
    exact Signature126.ordCompl_sum_factorization_le hp ha hb hc
  · exact sumExp_of_ne hp ha hb he

/-- Orient units once, using the global color rather than a new sign at each level. -/
def orient (s : Bool) (u : ℕ) : ℤ := if s then (u : ℤ) else -(u : ℤ)

lemma orient_mod_opposite (s t : Bool) (u v m : ℕ) (hst : s ≠ t) :
    orient s u % (m : ℤ) = orient t v % (m : ℤ) ↔ m ∣ u + v := by
  change Int.ModEq (m : ℤ) (orient s u) (orient t v) ↔ _
  rw [Int.modEq_iff_dvd]
  cases s <;> cases t
  · exact (hst rfl).elim
  · simp only [orient, Bool.false_eq_true, if_false, if_true]
    rw [show (v : ℤ) - -(u : ℤ) = ((u + v : ℕ) : ℤ) by push_cast; ring]
    exact Int.natCast_dvd_natCast
  · simp only [orient, Bool.false_eq_true, if_false, if_true]
    rw [show -(v : ℤ) - (u : ℤ) = -((u + v : ℕ) : ℤ) by push_cast; ring, dvd_neg]
    exact Int.natCast_dvd_natCast
  · exact (hst rfl).elim

lemma orient_mod_same (s : Bool) (u v m : ℕ) :
    orient s u % (m : ℤ) = orient s v % (m : ℤ) ↔ m ∣ diff u v := by
  change Int.ModEq (m : ℤ) (orient s u) (orient s v) ↔ _
  rw [Int.modEq_iff_dvd]
  cases s
  · simp only [orient, Bool.false_eq_true, if_false]
    rw [show -(v : ℤ) - -(u : ℤ) = (u : ℤ) - (v : ℤ) by ring]
    exact Int.natCast_dvd
  · simp only [orient, if_true]
    rw [show (v : ℤ) - (u : ℤ) = -((u : ℤ) - (v : ℤ)) by ring, dvd_neg]
    exact Int.natCast_dvd

/-- A signed unit residue together with its valuation tag. -/
def label (p n a : ℕ) : ℕ × ℤ :=
  (a.factorization p,
    orient (Signature126.primeColor p a) (ordCompl[p] a) % (p ^ (n + 1 + epsilon p) : ℕ))

lemma label_refines (p : ℕ) {n m : ℕ} (hnm : n ≤ m) {a b : ℕ}
    (he : label p m a = label p m b) : label p n a = label p n b := by
  obtain ⟨hv, hu⟩ := Prod.mk.inj he
  apply Prod.ext hv
  apply Int.ModEq.of_dvd _ hu
  exact Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (by omega))

lemma label_eq_opposite {p a b : ℕ} (hp : p.Prime) (ha : 0 < a) (hb : 0 < b)
    (hc : Signature126.primeColor p a ≠ Signature126.primeColor p b) (n : ℕ) :
    label p n a = label p n b ↔ n < sumExp p a b := by
  rw [sumExp_threshold hp ha hb]
  simp only [label, Prod.mk.injEq]
  rw [orient_mod_opposite _ _ _ _ _ hc]

/-- Same-color members of a level have the corresponding adjusted difference valuation. -/
lemma label_eq_same_bound {p a b : ℕ} (hp : p.Prime) (hab : a ≠ b)
    (hc : Signature126.primeColor p a = Signature126.primeColor p b) (n : ℕ)
    (he : label p n a = label p n b) : n < diffExp p a b := by
  obtain ⟨hv, hu⟩ := Prod.mk.inj he
  rw [diffExp_of_eq hp hab hv]
  have hd : p ^ (n + 1 + epsilon p) ∣ diff (ordCompl[p] a) (ordCompl[p] b) := by
    apply (orient_mod_same (Signature126.primeColor p a) _ _ _).mp
    simpa only [hc] using hu
  have ht := (hp.pow_dvd_iff_le_factorization (unit_diff_ne_zero hab hv)).mp hd
  omega

end E126.ArithmeticValuation126

/-
# One prime's finite integer opposition family

The level labels contain a valuation tag and a globally oriented unit residue.
At two the first modulus is four.  The construction retains only bichromatic
classes, and `ArithmeticCells126.build` combines all repeated supports.
-/

open scoped BigOperators

namespace E126.ArithmeticPrime126

open ArithmeticValuation126

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The maximum off-diagonal sum valuation, with maximum of the empty set zero. -/
def maxDepth (a : ι → ℕ) (p : ℕ) : ℕ :=
  (Finset.univ : Finset ι).offDiag.sup (fun ij => (a ij.1 + a ij.2).factorization p)

lemma sumExp_le_maxDepth (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (p : ℕ) (hp : p.Prime) (i j : ι) :
    sumExp p (a i) (a j) ≤ maxDepth a p := by
  by_cases hij : i = j
  · subst j
    rw [same_color_sumExp_zero hp (ha i) (ha i) rfl]
    exact Nat.zero_le _
  · have hmem : (i, j) ∈ (Finset.univ : Finset ι).offDiag :=
      Finset.mem_offDiag.mpr ⟨Finset.mem_univ i, Finset.mem_univ j, hij⟩
    exact (Nat.sub_le _ _).trans (Finset.le_sup (f := fun ij : ι × ι =>
      (a ij.1 + a ij.2).factorization p) hmem)

lemma log_prime_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) :=
  Real.log_nonneg (by exact_mod_cast hp.one_le)

/-- The explicit prime family. It is defined even without positivity assumptions
on the inputs; those assumptions enter its arithmetic kernel theorem. -/
def family (a : ι → ℕ) (p : ℕ) (hp : p.Prime) : OppositionFamily ι :=
  ArithmeticCells126.build (maxDepth a p)
    (fun i => Signature126.primeColor p (a i))
    (fun n i => label p n (a i))
    (fun _ _ h _ _ he => label_refines p h he)
    (Real.log (p : ℝ)) (log_prime_nonneg hp)

@[simp] lemma family_sign (a : ι → ℕ) (p : ℕ) (hp : p.Prime) (i : ι) :
    (family a p hp).sign i = Signature126.primeColor p (a i) := rfl

/-- Exact opposite-side kernel, with the adjusted exponent at two. -/
theorem opposition_eq (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (p : ℕ) (hp : p.Prime) (i j : ι) :
    (family a p hp).opposition i j =
      (sumExp p (a i) (a j) : ℝ) * Real.log (p : ℝ) := by
  classical
  by_cases hc : Signature126.primeColor p (a i) = Signature126.primeColor p (a j)
  · rw [same_color_sumExp_zero hp (ha i) (ha j) hc]
    simp [OppositionFamily.opposition, hc]
  · unfold family
    rw [ArithmeticCells126.opposition_eq_sum _ _ _ _ _ _ i j hc]
    simp_rw [label_eq_opposite hp (ha i) (ha j) hc]
    exact ArithmeticCells126.sum_initial _ _ _ (sumExp_le_maxDepth a ha p hp i j)

/-- Every retained same-side level is accounted for by the adjusted difference
valuation. This upper bound suffices without an explicit common-neighbor maximum. -/
theorem agreement_le (a : ι → ℕ) (p : ℕ) (hp : p.Prime) (i j : ι)
    (hij : a i ≠ a j) :
    (family a p hp).agreement i j ≤
      (diffExp p (a i) (a j) : ℝ) * Real.log (p : ℝ) := by
  classical
  have hw := log_prime_nonneg hp
  by_cases hc : Signature126.primeColor p (a i) = Signature126.primeColor p (a j)
  · calc
      (family a p hp).agreement i j ≤
          ∑ n ∈ Finset.range (maxDepth a p),
            if label p n (a i) = label p n (a j) then Real.log (p : ℝ) else 0 :=
        ArithmeticCells126.agreement_le_sum _ _ _ _ _ _ i j
      _ ≤ ∑ n ∈ Finset.range (maxDepth a p),
          if n < diffExp p (a i) (a j) then Real.log (p : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases he : label p n (a i) = label p n (a j)
        · rw [if_pos he, if_pos (label_eq_same_bound hp hij hc n he)]
        · rw [if_neg he]
          split_ifs
          · exact hw
          · exact le_rfl
      _ ≤ (diffExp p (a i) (a j) : ℝ) * Real.log (p : ℝ) :=
        ArithmeticCells126.sum_initial_le _ _ _ hw
  · have hz : (family a p hp).agreement i j = 0 := by
      simp [OppositionFamily.agreement, hc]
    rw [hz]
    exact mul_nonneg (Nat.cast_nonneg _) hw

/-- After subtracting opposition, the common normalization and the two-adic
baseline cancel. This form is convenient for summing over the prime support. -/
theorem signed_le (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (p : ℕ) (hp : p.Prime) (i j : ι) (hij : a i ≠ a j) :
    (family a p hp).signed i j ≤
      ((diff (a i) (a j)).factorization p : ℝ) * Real.log (p : ℝ) -
      ((a i + a j).factorization p : ℝ) * Real.log (p : ℝ) := by
  rw [OppositionFamily.signed_eq, opposition_eq a ha p hp i j]
  calc
    _ ≤ (diffExp p (a i) (a j) : ℝ) * Real.log (p : ℝ) -
        (sumExp p (a i) (a j) : ℝ) * Real.log (p : ℝ) :=
      sub_le_sub_right (agreement_le a p hp i j hij) _
    _ = _ := by
      rw [diffExp, sumExp, Nat.cast_sub (base_le_diff hp (ha i) (ha j) hij),
        Nat.cast_sub (base_le_sum hp (ha i) (ha j))]
      ring

end

end E126.ArithmeticPrime126

/-
# The positive-integer arithmetic model for Erdős problem 126

For distinct positive integers indexed by any finite type, and any prime set
containing the support of all off-diagonal sums, this module constructs one
finite laminar opposition family per prime. Its total opposition is exactly
`E126.arithmetic_log_kernel`, including the diagonal, and its total signed
kernel is strictly negative off the diagonal.

The construction uses globally oriented unit residues. Bichromatic cells are
retained and repeated supports have their weights added. At two, the first
modulus is four and all exponents use the adjusted baseline from the outset.
No declaration from `Submission.Spec` is imported.
-/

open scoped BigOperators

namespace E126

namespace ArithmeticModel126

open ArithmeticValuation126

lemma log_eq_sum_factorization (n : ℕ) (S : Finset ℕ) (hS : n.primeFactors ⊆ S) :
    Real.log (n : ℝ) = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization]
  exact Finsupp.sum_of_support_subset _ hS _ (by intros; simp)

/-- A partial prime-factorization sum is bounded by the full logarithm. -/
lemma sum_factorization_le_log (n : ℕ) (S : Finset ℕ) :
    (∑ p ∈ S, (n.factorization p : ℝ) * Real.log (p : ℝ)) ≤ Real.log (n : ℝ) := by
  calc
    _ ≤ ∑ p ∈ S ∪ n.primeFactors, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro p hp hnot
      exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
    _ = _ := (log_eq_sum_factorization n _ Finset.subset_union_right).symm

lemma two_mem_of_equal_valuations {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (S : Finset ℕ) (hS : (a + b).primeFactors ⊆ S)
    (he : a.factorization 2 = b.factorization 2) : 2 ∈ S := by
  apply hS
  apply Nat.mem_primeFactors.mpr
  have hs : a + b ≠ 0 := by omega
  refine ⟨Nat.prime_two, ?_, hs⟩
  apply (Nat.prime_two.dvd_iff_one_le_factorization hs).mpr
  have h := base_le_sum Nat.prime_two ha hb
  rw [base_of_eq he] at h
  simp only [epsilon, if_true] at h
  omega

/-- The common baseline sums to log-gcd plus the required equality-of-2-valuations term. -/
lemma sum_base_log {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (S : Finset ℕ) (hS : (a + b).primeFactors ⊆ S) :
    (∑ p ∈ S, (base p a b : ℝ) * Real.log (p : ℝ)) =
      Real.log (Nat.gcd a b : ℝ) +
        if a.factorization 2 = b.factorization 2 then Real.log 2 else 0 := by
  have hgS : (Nat.gcd a b).primeFactors ⊆ S :=
    (Nat.primeFactors_mono
      (Nat.dvd_add (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b)) (by omega)).trans hS
  have heach : ∀ p, (base p a b : ℝ) * Real.log (p : ℝ) =
      ((Nat.gcd a b).factorization p : ℝ) * Real.log (p : ℝ) +
        if p = 2 ∧ a.factorization 2 = b.factorization 2 then Real.log (p : ℝ) else 0 := by
    intro p
    rw [base_eq_gcd_add ha hb, Nat.cast_add, add_mul]
    split_ifs <;> simp
  simp_rw [heach, Finset.sum_add_distrib]
  rw [← log_eq_sum_factorization _ S hgS]
  congr 1
  by_cases he : a.factorization 2 = b.factorization 2
  · have htwo := two_mem_of_equal_valuations ha hb S hS he
    simp [he, htwo]
  · simp [he]

/-- Exact logarithmic sum of all adjusted prime exponents. -/
lemma sum_sumExp_log {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) (hS : (a + b).primeFactors ⊆ S) :
    (∑ p ∈ S, (sumExp p a b : ℝ) * Real.log (p : ℝ)) = arithmetic_log_kernel a b := by
  calc
    _ = (∑ p ∈ S, ((a + b).factorization p : ℝ) * Real.log (p : ℝ)) -
        ∑ p ∈ S, (base p a b : ℝ) * Real.log (p : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [sumExp, Nat.cast_sub (base_le_sum (hprime p hp) ha hb), sub_mul]
    _ = arithmetic_log_kernel a b := by
      rw [← log_eq_sum_factorization _ S hS, sum_base_log ha hb S hS]
      unfold arithmetic_log_kernel
      ring

end ArithmeticModel126

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual finite integer model, indexed by the prescribed prime support.
Its definition needs no injectivity or positivity hypotheses. -/
def arithmeticModel (a : ι → ℕ) (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime) :
    S → OppositionFamily ι :=
  fun p => ArithmeticPrime126.family a p.1 (hprime p.1 p.2)

/-- Full matrix identity, including the diagonal and empty/singleton index types. -/
theorem arithmeticModel_opposition (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hsupport : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S) (i j : ι) :
    totalOpposition (arithmeticModel a S hprime) i j = arithmetic_log_kernel (a i) (a j) := by
  classical
  by_cases hij : i = j
  · subst j
    simp [totalOpposition, arithmetic_log_kernel_diag (ha i)]
  · unfold totalOpposition arithmeticModel
    simp_rw [ArithmeticPrime126.opposition_eq a ha]
    rw [← Finset.sum_subtype S (fun _ => Iff.rfl)
      (fun p => (ArithmeticValuation126.sumExp p (a i) (a j) : ℝ) * Real.log (p : ℝ))]
    exact ArithmeticModel126.sum_sumExp_log (ha i) (ha j) S hprime (hsupport i j hij)

/-- A stronger quantitative form of off-diagonal negativity. Both the gcd
normalization and the extra baseline at two cancel in the signed difference. -/
theorem arithmeticModel_signed_le (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hinj : Function.Injective a) (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hsupport : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S)
    (i j : ι) (hij : i ≠ j) :
    totalSigned (arithmeticModel a S hprime) i j ≤
      Real.log (ArithmeticValuation126.diff (a i) (a j) : ℝ) -
        Real.log ((a i + a j : ℕ) : ℝ) := by
  classical
  have hab : a i ≠ a j := fun h => hij (hinj h)
  calc
    _ ≤ ∑ p : S,
        (((ArithmeticValuation126.diff (a i) (a j)).factorization p.1 : ℝ) * Real.log (p.1 : ℝ) -
        ((a i + a j).factorization p.1 : ℝ) * Real.log (p.1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact ArithmeticPrime126.signed_le a ha p.1 (hprime p.1 p.2) i j hab
    _ = (∑ p ∈ S,
        ((ArithmeticValuation126.diff (a i) (a j)).factorization p : ℝ) * Real.log (p : ℝ)) -
        ∑ p ∈ S, ((a i + a j).factorization p : ℝ) * Real.log (p : ℝ) := by
      rw [Finset.sum_sub_distrib]
      congr 1 <;> symm <;> exact Finset.sum_subtype S (fun _ => Iff.rfl) _
    _ ≤ _ := by
      rw [← ArithmeticModel126.log_eq_sum_factorization _ S (hsupport i j hij)]
      exact sub_le_sub_right (ArithmeticModel126.sum_factorization_le_log _ S) _

/-- Strict signed-kernel negativity for distinct positive integer inputs. -/
theorem arithmeticModel_signed_neg (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hinj : Function.Injective a) (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hsupport : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S)
    (i j : ι) (hij : i ≠ j) :
    totalSigned (arithmeticModel a S hprime) i j < 0 := by
  have hab : a i ≠ a j := fun h => hij (hinj h)
  have hlog := Real.log_lt_log
    (Nat.cast_pos.mpr (ArithmeticValuation126.diff_pos hab) :
      (0 : ℝ) < ArithmeticValuation126.diff (a i) (a j))
    (Nat.cast_lt.mpr (ArithmeticValuation126.diff_lt_sum (ha i) (ha j)))
  exact lt_of_le_of_lt (arithmeticModel_signed_le a ha hinj S hprime hsupport i j hij)
    (sub_neg.mpr hlog)

/-- The model inherits the already-proved weak conditional negative definiteness. -/
theorem arithmeticModel_cnd (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hsupport : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S) :
    CND (totalOpposition (arithmeticModel a S hprime)) := by
  intro q hq
  unfold quad
  simp_rw [arithmeticModel_opposition a ha S hprime hsupport]
  exact arithmetic_log_kernel_cnd a ha q hq

/-- Main arithmetic interface for the abstract finite laminar-capacity argument. -/
theorem exists_arithmetic_model (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hinj : Function.Injective a) (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    (hsupport : ∀ i j, i ≠ j → (a i + a j).primeFactors ⊆ S) :
    ∃ W : S → OppositionFamily ι,
      (∀ i j, totalOpposition W i j = arithmetic_log_kernel (a i) (a j)) ∧
      (∀ i j, i ≠ j → totalSigned W i j < 0) := by
  exact ⟨arithmeticModel a S hprime,
    arithmeticModel_opposition a ha S hprime hsupport,
    arithmeticModel_signed_neg a ha hinj S hprime hsupport⟩

end

end E126

/-
# Polynomial bounds and the extremal logarithmic limit for problem 126

The analytic theorem applies to any natural-valued function satisfying the displayed
polynomial bound; no monotonicity hypothesis is needed. The finite-set transfer below
is conditional on a cardinality bound for sets of positive natural numbers.
-/

namespace E126

open Filter Topology

/-- A polynomial upper bound for the argument forces growth faster than its logarithm. -/
theorem polynomial_bound_tendsto (f : ℕ → ℕ)
    (h : ∀ n, n ≤ 1024 * (f n + 1) ^ 8 + 1) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop := by
  have hf : Tendsto f atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_gt_atTop (1024 * (b + 1) ^ 8 + 1)] with n hn
    by_contra hbf
    have hfb : f n ≤ b := by omega
    have hbound : 1024 * (f n + 1) ^ 8 + 1 ≤ 1024 * (b + 1) ^ 8 + 1 := by
      gcongr
    exact (not_lt_of_ge ((h n).trans hbound)) hn
  have hfR : Tendsto (fun n => (f n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hf
  have hfadd : Tendsto (fun n => (f n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hfR
  have hsmall : Tendsto (fun n => Real.log ((f n : ℝ) + 1) / (f n : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_neg_cancel_right] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp hfadd
  have hmajorant : Tendsto
      (fun n => (Real.log 2048 + 8 * Real.log ((f n : ℝ) + 1)) / (f n : ℝ))
      atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using
      (hfR.const_div_atTop (Real.log 2048)).add (hsmall.const_mul 8)
  have hlog : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ≤ Real.log 2048 + 8 * Real.log ((f n : ℝ) + 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hreal : (n : ℝ) ≤ 1024 * ((f n : ℝ) + 1) ^ 8 + 1 := by
      exact_mod_cast h n
    have hp : (1 : ℝ) ≤ ((f n : ℝ) + 1) ^ 8 :=
      one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
    have hupper : (n : ℝ) ≤ 2048 * ((f n : ℝ) + 1) ^ 8 := by
      linarith only [hreal, hp]
    calc
      Real.log (n : ℝ) ≤ Real.log (2048 * ((f n : ℝ) + 1) ^ 8) :=
        Real.log_le_log (by exact_mod_cast hn) hupper
      _ = Real.log 2048 + 8 * Real.log ((f n : ℝ) + 1) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        norm_num
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) / (f n : ℝ) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ), hfR.eventually_gt_atTop 0] with n hn hfn
    exact div_pos (Real.log_pos (by exact_mod_cast hn)) hfn
  have hzero : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (f n : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' (hpos.mono fun _ hn => hn.le) ?_ hmajorant
    filter_upwards [hlog] with n hn
    exact div_le_div_of_nonneg_right hn (Nat.cast_nonneg _)
  have hright : Tendsto (fun n : ℕ => Real.log (n : ℝ) / (f n : ℝ))
      atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hzero, hpos⟩
  simpa only [Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp hright

/-- A bound for positive sets extends to all natural sets with an additive cost of one. -/
theorem card_bound_of_positive_bound
    (hpos : ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) →
      A.card ≤ 1024 * ((∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card + 1) ^ 8)
    (A : Finset ℕ) :
    A.card ≤ 1024 * ((∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card + 1) ^ 8 + 1 := by
  have hB := hpos (A.erase 0) (by
    intro a ha
    exact Nat.pos_of_ne_zero (Finset.mem_erase.mp ha).1)
  change (A.erase 0).card ≤ 1024 * (Independent126.factorCount (A.erase 0) + 1) ^ 8 at hB
  have hmono := Independent126.factorCount_mono (Finset.erase_subset 0 A)
  have hbound : 1024 * (Independent126.factorCount (A.erase 0) + 1) ^ 8 ≤
      1024 * (Independent126.factorCount A + 1) ^ 8 := by
    gcongr
  have hcard : A.card - 1 ≤ (A.erase 0).card := Finset.pred_card_le_card_erase
  change A.card ≤ 1024 * (Independent126.factorCount A + 1) ^ 8 + 1
  omega

/-- An attained extremal minimum inherits the polynomial bound, including the zero correction. -/
theorem maximal_polynomial_bound {f : ℕ → ℕ}
    (hf : Independent126.IsMaximalAddFactorsCard f)
    (hpos : ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) →
      A.card ≤ 1024 * ((∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card + 1) ^ 8) :
    ∀ n, n ≤ 1024 * (f n + 1) ^ 8 + 1 := by
  intro n
  obtain ⟨A, hA, hcost⟩ := Independent126.maximal_attained hf n
  have h := card_bound_of_positive_bound hpos A
  change A.card ≤ 1024 * (Independent126.factorCount A + 1) ^ 8 + 1 at h
  simpa only [hA, hcost] using h

/-- Conditional transfer from the positive-set cardinality bound to the extremal logarithmic limit. -/
theorem maximal_tendsto_of_positive_bound {f : ℕ → ℕ}
    (hf : Independent126.IsMaximalAddFactorsCard f)
    (hpos : ∀ (A : Finset ℕ), (∀ a ∈ A, 0 < a) →
      A.card ≤ 1024 * ((∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card + 1) ^ 8) :
    Tendsto (fun n : ℕ => (f n : ℝ) / Real.log (n : ℝ)) atTop atTop :=
  polynomial_bound_tendsto f (maximal_polynomial_bound hf hpos)


end E126

/- The polynomial prime-support bound and the extremal limit. -/

namespace E126

/-- A polynomial upper bound for a positive set in terms of its sum-prime support. -/
theorem positive_card_bound (A : Finset ℕ) (hpos : ∀ a ∈ A, 0 < a) :
    A.card ≤ 1024 * ((∏ ⟨a, b⟩ ∈ A.offDiag, (a + b)).primeFactors.card + 1) ^ 8 := by
  classical
  let S := Signature126.primeSupport A
  have hprime : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hsupp : ∀ i j : A, i ≠ j → (i.val + j.val).primeFactors ⊆ S := by
    intro i j hij p hp
    obtain ⟨hpr, hdvd, _⟩ := Nat.mem_primeFactors.mp hp
    exact (Independent126.prime_mem_iff A p).mpr
      ⟨hpr, i, i.property, j, j.property, (fun h => hij (Subtype.ext h)), hdvd⟩
  have ha : ∀ i : A, 0 < (i : ℕ) := fun i => hpos i i.property
  have hinj : Function.Injective (fun i : A => (i : ℕ)) := Subtype.val_injective
  have hc := opposition_capacity (arithmeticModel (fun i : A => (i : ℕ)) S hprime)
    (arithmeticModel_signed_neg _ ha hinj S hprime hsupp)
    (arithmeticModel_cnd _ ha S hprime hsupp)
  simpa [S, Signature126.primeSupport] using hc

/-- The original asymptotic assertion, for the independently copied extremal definition. -/
theorem extremal_tendsto {f : ℕ → ℕ} (hf : Independent126.IsMaximalAddFactorsCard f) :
    Filter.Tendsto (fun n => (f n : ℝ) / Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
  maximal_tendsto_of_positive_bound hf positive_card_bound


end E126

namespace Erdos126

/--
Let $f(n)$ be maximal such that if $A\subseteq\mathbb{N}$ has $|A| = n$ then
$\prod_{a\neq b\in A}(a + b)$ has at least $f(n)$ distinct prime factors.
Is it true that $\frac{f(n)}{\log n} \to\infty$?
-/
theorem erdos_126 : ∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f →
    Tendsto (fun n => f n / Real.log n) atTop atTop := by
  intro f hf
  exact E126.extremal_tendsto hf

end Erdos126

theorem Erdos126.erdos_126.disproof : ¬ (type_of% @Erdos126.erdos_126) := sorry
