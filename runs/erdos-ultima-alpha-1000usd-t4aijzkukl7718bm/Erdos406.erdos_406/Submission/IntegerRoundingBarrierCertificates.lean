import Submission.BalancedAffineCertificates

/-! Integer rounding gives a sufficient barrier criterion not requiring
preservation of a positive real margin. No separating witness is supplied;
this module does not settle Erdős 406. -/
namespace Erdos406IntegerRounding
open Erdos406AffineCertificate Erdos406AffinePotential Erdos406BalancedCertificate
  Erdos406Balanced

/-- The slack `p-1` is compatible with preservation of positive INTEGER
scores, even when the corresponding real affine map has a negative fixed point. -/
lemma positive_of_rounding (p q x y : ℤ) (hp : 0 < p) (hq : 0 < q)
    (hstep : p*x-p+1 ≤ q*y) (hx : 0 < x) : 0 < y := by
  have hx' : 1 ≤ x := by omega
  have hh : 1 ≤ p*x-p+1 := by nlinarith
  by_contra hn
  have hm : q*y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq.le (by omega)
  omega

/-- All premises are explicit. In particular, neither an integer score nor
a positive seed satisfying these conditions has been constructed. -/
theorem integer_rounding_criterion (V : ℕ → ℤ) (p q : ℤ) (E : ℕ)
    (hp : 0 < p) (hq : 0 < q)
    (hstep : ∀ n, p*V n-p+1 ≤ q*V (4*n+1))
    (hgood : ∀ n, Nat.digits 3 n ⊆ [0,1] → V n ≤ 0)
    (hseed : 0 < V (orbit 4 1 E)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  apply Erdos406AffineBarrier.affine_threshold_criterion
    (fun n => (V n : ℝ)) 0 E
  · intro n hn
    have hn' : 0 < V n := by exact_mod_cast hn
    have hh := positive_of_rounding p q (V n) (V (4*n+1)) hp hq (hstep n) hn'
    exact_mod_cast hh
  · intro n hn
    exact_mod_cast hgood n hn
  · exact_mod_cast hseed

def intWeightFrom {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℤ) :
    σ → List ℕ → ℤ
  | _, [] => 0
  | s, d::u => w s d + intWeightFrom D w (D.step s d) u

def intPotential {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℤ) (n : ℕ) : ℤ :=
  intWeightFrom D w D.start (digits n)

lemma cast_intWeightFrom {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℤ)
    (s : σ) (u : List ℕ) :
    (intWeightFrom D w s u : ℝ) = weightFrom D (fun s d => (w s d : ℝ)) s u := by
  induction u generalizing s with
  | nil => simp [intWeightFrom,weightFrom]
  | cons d u ih => simp [intWeightFrom,weightFrom,ih]

lemma cast_intPotential {σ : Type*} (D : DFA ℕ σ) (w : σ → ℕ → ℤ) (n : ℕ) :
    (intPotential D w n : ℝ) = potential D (fun s d => (w s d : ℝ)) n :=
  cast_intWeightFrom D w D.start (digits n)

/-- Reuses the kernel-checked balanced carry transducer. The lower carry
weights may be rational; the digit score itself MUST be integral. -/
theorem balanced_integer_rounding_criterion {σ : Type*}
    (C : Lower σ) (U : GoodUpper C.D C.w) (w : σ → ℕ → ℤ)
    (hw : C.w = fun s d => (w s d : ℝ))
    (p q : ℤ) (E : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hlam : (q : ℝ)*C.lam = p)
    (hdelta : (q : ℝ)*C.delta = 1-p)
    (hc : U.c = 0) (hB : U.B = 0)
    (hseed : 0 < intPotential C.D w (orbit 4 1 E)) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0,1]}.Finite := by
  apply integer_rounding_criterion (intPotential C.D w) p q E hp hq ?_ ?_ hseed
  · intro n
    have hh := C.affine_lower n
    rw [hw, ← cast_intPotential, ← cast_intPotential] at hh
    have hqR : (0 : ℝ) ≤ q := by exact_mod_cast hq.le
    have hm := mul_le_mul_of_nonneg_left hh hqR
    rw [mul_add, ← mul_assoc, hlam, hdelta] at hm
    have he : (p : ℝ)*(intPotential C.D w n : ℝ)-(p : ℝ)+1 ≤
        (q : ℝ)*(intPotential C.D w (4*n+1) : ℝ) := by linarith
    exact_mod_cast he
  · intro n hn
    have hh := U.good_bound n hn
    rw [hc,hB,zero_mul,zero_add,hw,← cast_intPotential] at hh
    exact_mod_cast hh

/-- For p≤q the same integer inequality also preserves nonnegative scores. -/
lemma nonnegative_of_rounding (p q x y : ℤ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p ≤ q) (hstep : p*x-p+1 ≤ q*y) (hx : 0 ≤ x) : 0 ≤ y := by
  have hh : 0 ≤ p*x := mul_nonneg hp.le hx
  by_contra hn
  have hy : y ≤ -1 := by omega
  have hm := mul_le_mul_of_nonneg_left hy hq.le
  nlinarith

/-- Validates the initial zero-score constraints used by the search. -/
lemma orbit_scores_zero_before (V : ℕ → ℤ) (p q : ℤ) (N : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ q) (hzero : V 0 = 0)
    (hstep : ∀ n, p*V n-p+1 ≤ q*V (4*n+1))
    (hlast : V (orbit 4 1 N) ≤ 0) :
    ∀ t ≤ N, V (orbit 4 1 t) = 0 := by
  have hn : ∀ t, 0 ≤ V (orbit 4 1 t) := by
    intro t
    induction t with
    | zero => simp [hzero]
    | succ t ih =>
      simpa only [orbit_succ] using nonnegative_of_rounding p q _ _ hp hq hpq
        (hstep (orbit 4 1 t)) ih
  intro t ht
  apply le_antisymm ?_ (hn t)
  by_contra h
  have hp' : 0 < V (orbit 4 1 t) := by omega
  have hf : ∀ j, 0 < V (orbit 4 1 (t+j)) := by
    intro j
    induction j with
    | zero => simpa using hp'
    | succ j ih =>
      simpa only [Nat.add_succ,orbit_succ] using positive_of_rounding p q _ _
        hp hq (hstep (orbit 4 1 (t+j))) ih
  have hh := hf (N-t)
  rw [Nat.add_sub_of_le ht] at hh
  omega

/-- In the original affine orbit, the scores at indices zero through four
must vanish under the nonnegative-preserving version of the criterion. -/
lemma search_initial_scores_zero (V : ℕ → ℤ) (p q : ℤ)
    (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ q) (hzero : V 0 = 0)
    (hstep : ∀ n, p*V n-p+1 ≤ q*V (4*n+1))
    (hgood : ∀ n, Nat.digits 3 n ⊆ [0,1] → V n ≤ 0) :
    ∀ t ≤ 4, V (orbit 4 1 t) = 0 := by
  apply orbit_scores_zero_before V p q 4 hp hq hpq hzero hstep
  apply hgood
  decide +kernel

/-- A diagnostic map illustrating that the rounding criterion is genuinely
stronger than requiring a homogeneous real lower bound. It is unrelated to
ternary digits and is not a certificate for the original conjecture. -/
def roundMap (x : ℤ) : ℤ := (2*x+1)/3

lemma roundMap_lower (x : ℤ) : 2*x-1 ≤ 3*roundMap x := by
  unfold roundMap
  omega

lemma roundMap_preserves_positive (x : ℤ) (hx : 0 < x) : 0 < roundMap x := by
  exact positive_of_rounding 2 3 x (roundMap x) (by decide) (by decide)
    (by have hh := roundMap_lower x; omega) hx

lemma roundMap_no_homogeneous_lower :
    ¬ ∃ a : ℝ, ∀ x : ℤ, a*(x : ℝ) ≤ (roundMap x : ℝ) := by
  rintro ⟨a, ha⟩
  have h2 := ha 2
  have hm3 := ha (-3)
  norm_num [roundMap] at h2 hm3
  linarith

#print axioms integer_rounding_criterion
#print axioms balanced_integer_rounding_criterion
#print axioms orbit_scores_zero_before
#print axioms roundMap_no_homogeneous_lower
end Erdos406IntegerRounding
