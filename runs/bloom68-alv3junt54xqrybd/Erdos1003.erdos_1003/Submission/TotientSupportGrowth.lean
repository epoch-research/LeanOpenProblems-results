import Submission.TotientCertificates
import Submission.BoundedTotientSupport

/-!
# Two-sided support-growth barriers for adjacent equal totients

These are necessary conditions, not a proof of infinitude or of finiteness.
No theorem from `Submission.Spec` is imported or used.

If an old certificate has `n = R*x`, `n+1 = S*y`, `F = y*g`,
`G = x*g`, adding disjoint squarefree blocks `A,B` gives
`h = gcd (y*phi(A)) (x*phi(B))`.  Its unit determinant requires
`(n+1)*B*phi(A) = n*A*phi(B) + h`.
The original right support is nonempty, hence `2*y <= n+1`.

The lemmas below prove that simultaneous strict support growth must overshoot
on the left, and that the right block is a minimal Euler-ratio crossing.
In particular, replacing a composite candidate below the repair threshold
by any of its prime factors cannot repair the certificate while keeping the
left block fixed, even if other new right-hand primes are also allowed.
-/

namespace TotientSupportGrowth

/-- The gcd after removing the old common totient factor. -/
def extensionGcd (x y A B : ℕ) : ℕ :=
  Nat.gcd (y * A.totient) (x * B.totient)

/-- Exactly the determinant and positivity data needed for the barriers.
This definition does not assert that any such extension exists. -/
structure NormalizedExtension (n x y A B : ℕ) : Prop where
  left_new : 1 < A
  right_new : 1 < B
  x_pos : 0 < x
  y_pos : 0 < y
  right_quotient_bound : 2 * y ≤ n + 1
  determinant : (n + 1) * B * A.totient =
    n * A * B.totient + extensionGcd x y A B

/-- Algebraic bridge from the full extended certificate determinant.
For disjoint squarefree support blocks, `U=phi(A)` and `V=phi(B)`. -/
theorem normalize_determinant
    {R S F G g x y n A B U V : ℕ}
    (hg : 0 < g) (hF : F = y * g) (hG : G = x * g)
    (hn : n = R * x) (hm : n + 1 = S * y)
    (hdet : S * B * (F * U) = R * A * (G * V) + Nat.gcd (F * U) (G * V)) :
    (n + 1) * B * U = n * A * V + Nat.gcd (y * U) (x * V) := by
  have hgcd : Nat.gcd (F * U) (G * V) = Nat.gcd (y * U) (x * V) * g := by
    calc
      Nat.gcd (F * U) (G * V) = Nat.gcd ((y * U) * g) ((x * V) * g) := by
        rw [hF, hG]
        congr 1 <;> ring
      _ = Nat.gcd (y * U) (x * V) * g := Nat.gcd_mul_right (y * U) g (x * V)
  apply Nat.eq_of_mul_eq_mul_right hg
  calc
    ((n + 1) * B * U) * g = S * B * (F * U) := by rw [hm, hF]; ring
    _ = R * A * (G * V) + Nat.gcd (F * U) (G * V) := hdet
    _ = (n * A * V + Nat.gcd (y * U) (x * V)) * g := by
      rw [hgcd, hn, hG]
      ring

/-- An extended determinant with a nonempty old right support supplies
all the hypotheses of the normalized arithmetic lemmas. -/
theorem normalizedExtension_of_determinant
    {R S F G g x y n A B : ℕ}
    (hg : 0 < g) (hF : F = y * g) (hG : G = x * g)
    (hn : n = R * x) (hm : n + 1 = S * y)
    (hS : 2 ≤ S) (hx : 0 < x) (hy : 0 < y)
    (hA : 1 < A) (hB : 1 < B)
    (hdet : S * B * (F * A.totient) =
      R * A * (G * B.totient) + Nat.gcd (F * A.totient) (G * B.totient)) :
    NormalizedExtension n x y A B := by
  refine ⟨hA, hB, hx, hy, ?_, ?_⟩
  · calc
      2 * y ≤ S * y := Nat.mul_le_mul_right y hS
      _ = n + 1 := hm.symm
  · exact normalize_determinant hg hF hG hn hm hdet

/-- A small positive determinant forces a strict totient-ratio crossing. -/
lemma crossing_of_small_remainder {M m U V B h : ℕ}
    (hh : h < M) (hV : V < B) (heq : m * B * U = M * V + h) :
    m * U < M := by
  by_contra hnot
  have hMU : M ≤ m * U := Nat.le_of_not_gt hnot
  have hcontra : M * B < M * B := by
    calc
      M * B ≤ (m * U) * B := Nat.mul_le_mul_right B hMU
      _ = m * B * U := by ring
      _ = M * V + h := heq
      _ < M * V + M := Nat.add_lt_add_left hh _
      _ = M * (V + 1) := by ring
      _ ≤ M * B := Nat.mul_le_mul_left M (by omega)
  exact (Nat.lt_irrefl _ hcontra)

namespace NormalizedExtension

variable {n x y A B : ℕ} (e : NormalizedExtension n x y A B)
include e

lemma gcd_pos : 0 < extensionGcd x y A B := by
  apply Nat.gcd_pos_of_pos_left
  exact Nat.mul_pos e.y_pos (Nat.totient_pos.mpr (by have := e.left_new; omega))

lemma gcd_le_left : extensionGcd x y A B ≤ y * A.totient := by
  apply Nat.gcd_le_left
  exact Nat.mul_pos e.y_pos (Nat.totient_pos.mpr (by have := e.left_new; omega))

lemma gcd_lt_left_size : extensionGcd x y A B < n * A := by
  have hy : y ≤ n := by
    have := e.y_pos
    have := e.right_quotient_bound
    omega
  calc
    extensionGcd x y A B ≤ y * A.totient := e.gcd_le_left
    _ < y * A := Nat.mul_lt_mul_of_pos_left (Nat.totient_lt A e.left_new) e.y_pos
    _ ≤ n * A := Nat.mul_le_mul_right A hy

/-- The new left Euler ratio must cross strictly below `n/(n+1)`. -/
theorem overshoot : (n + 1) * A.totient < n * A :=
  crossing_of_small_remainder e.gcd_lt_left_size (Nat.totient_lt B e.right_new)
    e.determinant

/-- In fact the gcd available to absorb the new determinant is less
than half the unnormalized new left size. -/
theorem gcd_lt_half : 2 * extensionGcd x y A B < n * A := by
  calc
    2 * extensionGcd x y A B ≤ 2 * (y * A.totient) :=
      Nat.mul_le_mul_left 2 e.gcd_le_left
    _ = (2 * y) * A.totient := by ring
    _ ≤ (n + 1) * A.totient :=
      Nat.mul_le_mul_right A.totient e.right_quotient_bound
    _ < n * A := e.overshoot

/-- Every proper coprime factor of the restoring block remains strictly
above the balancing threshold. For squarefree `B`, this covers every
proper divisor. The full block is below it by the determinant identity. -/
theorem proper_factor_above {C D : ℕ}
    (hC : 0 < C) (hD : 1 < D) (hB : B = C * D) (hcop : Nat.Coprime C D) :
    (n + 1) * C * A.totient < n * A * C.totient := by
  have hphiC : 1 ≤ C.totient := Nat.succ_le_of_lt (Nat.totient_pos.mpr hC)
  have hsmall : extensionGcd x y A B < (n * A) * C.totient :=
    e.gcd_lt_left_size.trans_le (by simpa using Nat.mul_le_mul_left (n * A) hphiC)
  have hdet : ((n + 1) * C) * D * A.totient =
      ((n * A) * C.totient) * D.totient + extensionGcd x y A B := by
    have hphiB : B.totient = C.totient * D.totient := by rw [hB, Nat.totient_mul hcop]
    calc
      ((n + 1) * C) * D * A.totient = (n + 1) * B * A.totient := by rw [hB]; ring
      _ = n * A * B.totient + extensionGcd x y A B := e.determinant
      _ = ((n * A) * C.totient) * D.totient + extensionGcd x y A B := by
        rw [hphiB]
        ring
  have hcross := crossing_of_small_remainder hsmall (Nat.totient_lt D hD) hdet
  simpa [mul_assoc] using hcross

/-- A strict two-sided extension adding only one new left prime must
use a prime no larger than the old smaller argument. -/
theorem single_left_prime_le {p : ℕ} (hp : Nat.Prime p)
    (hA : A = p) : p ≤ n := by
  have ho := e.overshoot
  rw [hA, Nat.totient_prime hp] at ho
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
  nlinarith

end NormalizedExtension

/-- The positive amount by which the new left block overshoots. -/
def overshootDefect (n A : ℕ) : ℕ := n * A - (n + 1) * A.totient

namespace NormalizedExtension

variable {n x y A B : ℕ} (e : NormalizedExtension n x y A B)
include e

lemma defect_pos : 0 < overshootDefect n A := by
  exact Nat.sub_pos_of_lt e.overshoot

lemma defect_add : overshootDefect n A + (n + 1) * A.totient = n * A :=
  Nat.sub_add_cancel e.overshoot.le

private lemma defect_mul (q : ℕ) :
    (n * A) * q = (n + 1) * q * A.totient + overshootDefect n A * q := by
  calc
    (n * A) * q = (overshootDefect n A + (n + 1) * A.totient) * q :=
      congrArg (fun z : ℕ => z * q) e.defect_add.symm
    _ = (n + 1) * q * A.totient + overshootDefect n A * q := by ring

/-- A single restoring prime lies strictly between half the repair
threshold and the whole repair threshold (in division-free form). -/
theorem single_right_prime_interval {q : ℕ} (hq : Nat.Prime q) (hB : B = q) :
    n * A < 2 * (overshootDefect n A * q) ∧
      overshootDefect n A * q < n * A := by
  subst B
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel hq.one_le
  have hdet := e.determinant
  rw [Nat.totient_prime hq] at hdet
  have hrel : overshootDefect n A * q + extensionGcd x y A q = n * A := by
    have hcalc : (n * A) * (q - 1) + n * A =
        (n * A) * (q - 1) + (overshootDefect n A * q + extensionGcd x y A q) := by
      calc
        (n * A) * (q - 1) + n * A = (n * A) * q := by
          calc
            (n * A) * (q - 1) + n * A = (n * A) * (q - 1 + 1) := by ring
            _ = (n * A) * q := by rw [hpred]
        _ = (n + 1) * q * A.totient + overshootDefect n A * q := e.defect_mul q
        _ = (n * A) * (q - 1) + (overshootDefect n A * q + extensionGcd x y A q) := by
          rw [hdet]
          ring
    exact (Nat.add_left_cancel hcalc).symm
  have hh := e.gcd_lt_half
  have hp := e.gcd_pos
  omega

/-- If the restoring block has a proper prime factor `q`, that prime
lies strictly above the whole repair threshold, not below it. -/
theorem proper_right_prime_gt {q C : ℕ} (hq : Nat.Prime q) (hC : 1 < C)
    (hB : B = q * C) (hcop : Nat.Coprime q C) :
    n * A < overshootDefect n A * q := by
  have hproper := e.proper_factor_above hq.pos hC hB hcop
  rw [Nat.totient_prime hq] at hproper
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel hq.one_le
  have hlt : (n * A) * (q - 1) + n * A <
      (n * A) * (q - 1) + overshootDefect n A * q := by
    calc
      (n * A) * (q - 1) + n * A = (n * A) * q := by
        calc
          (n * A) * (q - 1) + n * A = (n * A) * (q - 1 + 1) := by ring
          _ = (n * A) * q := by rw [hpred]
      _ = (n + 1) * q * A.totient + overshootDefect n A * q := e.defect_mul q
      _ < (n * A) * (q - 1) + overshootDefect n A * q :=
        Nat.add_lt_add_right hproper _
  exact (add_lt_add_iff_left _).mp hlt

/-- Every prime in a squarefree restoring block lies above half the
repair threshold; for a composite block the stronger whole-threshold
bound holds by `proper_right_prime_gt`. -/
theorem right_prime_gt_half {q : ℕ} (hBsq : Squarefree B)
    (hq : Nat.Prime q) (hqB : q ∣ B) :
    n * A < 2 * (overshootDefect n A * q) := by
  obtain ⟨C, hBC⟩ := hqB
  by_cases hC : C = 1
  · have hBq : B = q := by simpa [hC] using hBC
    exact (e.single_right_prime_interval hq hBq).1
  · have hCpos : 0 < C := by
      have hb := e.right_new
      rw [hBC] at hb
      nlinarith [hq.pos]
    have hCbig : 1 < C := by omega
    have hcop : Nat.Coprime q C := Nat.coprime_of_squarefree_mul (hBC ▸ hBsq)
    have hfull := e.proper_right_prime_gt hq hCbig hBC hcop
    omega

/-- A precise prime-factor-extraction obstruction. Keep the left block
fixed and take a composite candidate `Q` strictly below the single-prime
repair threshold. None of its prime factors can belong to ANY squarefree
restoring block satisfying the unit determinant, including one with
arbitrarily many other primes. -/
theorem composite_candidate_factor_excluded {Q q : ℕ}
    (hBsq : Squarefree B) (hq : Nat.Prime q) (hQ : ¬ Nat.Prime Q)
    (hQpos : 0 < Q) (hqQ : q ∣ Q)
    (hbelow : overshootDefect n A * Q < n * A) : ¬ q ∣ B := by
  obtain ⟨C, hQC⟩ := hqQ
  have hCpos : 0 < C := by
    rw [hQC] at hQpos
    nlinarith [hq.pos]
  have hCne : C ≠ 1 := by
    intro h
    apply hQ
    have hQq : Q = q := by simpa [h] using hQC
    exact hQq.symm ▸ hq
  have hCtwo : 2 ≤ C := by omega
  have hqbound : 2 * q ≤ Q := by
    calc
      2 * q = q * 2 := Nat.mul_comm _ _
      _ ≤ q * C := Nat.mul_le_mul_left q hCtwo
      _ = Q := hQC.symm
  have hsmall : 2 * (overshootDefect n A * q) < n * A := by
    calc
      2 * (overshootDefect n A * q) = overshootDefect n A * (2 * q) := by ring
      _ ≤ overshootDefect n A * Q := Nat.mul_le_mul_left _ hqbound
      _ < n * A := hbelow
  intro hqB
  exact (Nat.lt_asymm hsmall (e.right_prime_gt_half hBsq hq hqB))

end NormalizedExtension

open scoped BigOperators

lemma prime_product_gt_one {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p)
    (hne : P.Nonempty) : 1 < ∏ p ∈ P, p := by
  have hpos : 0 < ∏ p ∈ P, p := Finset.prod_pos fun p hp => (hP p hp).pos
  obtain ⟨p, hp⟩ := hne
  have hle : p ≤ ∏ p ∈ P, p :=
    Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp)
  have := (hP p hp).two_le
  omega

lemma totient_prime_product {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) :
    (∏ p ∈ P, p).totient = ∏ p ∈ P, (p - 1) := by
  have ht := (TotientCertificates.supported_product_totient P 1 hP (by decide) (by simp)).2
  simpa using ht

/-- Actual adjacent collisions and extended support certificates satisfy the
normalized extension hypotheses. This is a necessity theorem only. -/
theorem normalizedExtension_of_adjacent_support_extension
    {n : ℕ} (ht : n.totient = (n + 1).totient)
    (P Q : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hQ : ∀ q ∈ Q, Nat.Prime q)
    (hPn : Disjoint n.primeFactors P) (hQm : Disjoint (n + 1).primeFactors Q)
    (hPne : P.Nonempty) (hQne : Q.Nonempty)
    (hnew : TotientCertificates.SupportCertificate (n.primeFactors ∪ P)
      ((n + 1).primeFactors ∪ Q)) :
    NormalizedExtension n
      (TotientCertificates.radicalPhi (n + 1) /
        Nat.gcd (TotientCertificates.radicalPhi n) (TotientCertificates.radicalPhi (n + 1)))
      (TotientCertificates.radicalPhi n /
        Nat.gcd (TotientCertificates.radicalPhi n) (TotientCertificates.radicalPhi (n + 1)))
      (∏ p ∈ P, p) (∏ q ∈ Q, q) := by
  let R := TotientCertificates.radical n
  let S := TotientCertificates.radical (n + 1)
  let F := TotientCertificates.radicalPhi n
  let G := TotientCertificates.radicalPhi (n + 1)
  let g := Nat.gcd F G
  let x := G / g
  let y := F / g
  let A := ∏ p ∈ P, p
  let B := ∏ q ∈ Q, q
  change NormalizedExtension n x y A B
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    norm_num at ht
  have hFpos : 0 < F := TotientCertificates.radicalPhi_pos n
  have hGpos : 0 < G := TotientCertificates.radicalPhi_pos (n + 1)
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left G hFpos
  have hgF : g ∣ F := Nat.gcd_dvd_left F G
  have hgG : g ∣ G := Nat.gcd_dvd_right F G
  have hxpos : 0 < x := Nat.div_pos (Nat.le_of_dvd hGpos hgG) hgpos
  have hypos : 0 < y := Nat.div_pos (Nat.le_of_dvd hFpos hgF) hgpos
  have hF : F = y * g := (Nat.div_mul_cancel hgF).symm
  have hG : G = x * g := (Nat.div_mul_cancel hgG).symm
  have hpairs := TotientCertificates.primitive_totient_pair_certificate hnpos
    (by omega : 0 < n + 1) (by simp : Nat.Coprime n (n + 1)) ht
  have hn : n = R * x := hpairs.1
  have hm : n + 1 = S * y := hpairs.2
  have hmne : (n + 1).primeFactors.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hz := Nat.primeFactors_eq_empty.mp hempty
    omega
  have hSbig : 2 ≤ S := by
    have hs := prime_product_gt_one (fun p hp => Nat.prime_of_mem_primeFactors hp) hmne
    change 2 ≤ ∏ p ∈ (n + 1).primeFactors, p
    omega
  have hA : 1 < A := prime_product_gt_one hP hPne
  have hB : 1 < B := prime_product_gt_one hQ hQne
  have hphiA : A.totient = ∏ p ∈ P, (p - 1) := totient_prime_product hP
  have hphiB : B.totient = ∏ q ∈ Q, (q - 1) := totient_prime_product hQ
  have hRnew : (∏ p ∈ n.primeFactors ∪ P, p) = R * A := Finset.prod_union hPn
  have hSnew : (∏ q ∈ (n + 1).primeFactors ∪ Q, q) = S * B := Finset.prod_union hQm
  have hFnew : (∏ p ∈ n.primeFactors ∪ P, (p - 1)) = F * A.totient := by
    rw [Finset.prod_union hPn, hphiA]
    rfl
  have hGnew : (∏ q ∈ (n + 1).primeFactors ∪ Q, (q - 1)) = G * B.totient := by
    rw [Finset.prod_union hQm, hphiB]
    rfl
  have hdetnew := hnew.2.2.2.2
  rw [hRnew, hSnew, hFnew, hGnew] at hdetnew
  exact normalizedExtension_of_determinant hgpos hF hG hn hm hSbig
    hxpos hypos hA hB hdetnew



lemma squarefree_prime_product {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) :
    Squarefree (∏ p ∈ P, p) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have hprime : Nat.Prime p := hP p (Finset.mem_insert_self p P)
    have hrest : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ P, q) := by
      apply hprime.coprime_iff_not_dvd.mpr
      apply hprime.prime.not_dvd_finset_prod
      intro q hq hdvd
      have heq : p = q := (Nat.prime_dvd_prime_iff_eq hprime (hrest q hq)).mp hdvd
      exact hp (heq.symm ▸ hq)
    rw [Finset.prod_insert hp]
    exact Nat.squarefree_mul_iff.mpr ⟨hcop, hprime.prime.squarefree, ih hrest⟩

/-- If all new left primes exceed L, their count must exceed
(L+1)/(n+1). This is a local support-growth bound, not a global
bounded-support finiteness theorem. -/
theorem left_new_support_count {n x y A B L : ℕ}
    (e : NormalizedExtension n x y A B) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hA : A = ∏ p ∈ P, p)
    (hlarge : ∀ p ∈ P, L < p) : L + 1 < (n + 1) * P.card := by
  have hApos : (0 : ℚ) < A := by exact_mod_cast (show 0 < A by have := e.left_new; omega)
  have hmpos : (0 : ℚ) < n + 1 := by positivity
  have hLpos : (0 : ℚ) < L + 1 := by positivity
  have hphi : A.totient = ∏ p ∈ P, (p - 1) := by rw [hA]; exact totient_prime_product hP
  have hratio : EulerProductSupport.eulerRatio P = (A.totient : ℚ) / (A : ℚ) := by
    rw [EulerProductSupport.eulerRatio_eq_prod_div hP, ← hA, ← hphi]
  have ho : (n + 1 : ℚ) * (A.totient : ℚ) < (n : ℚ) * (A : ℚ) := by
    exact_mod_cast e.overshoot
  have hmass : 1 / (n + 1 : ℚ) < 1 - EulerProductSupport.eulerRatio P := by
    rw [hratio]
    apply (div_lt_iff₀ hmpos).mpr
    apply (mul_lt_mul_iff_left₀ hApos).mp
    field_simp
    nlinarith [ho]
  have htail := BoundedTotientSupport.eulerRatio_tail_bound (A := ∅) L hP
    (Finset.empty_subset P) (by simpa using hlarge)
  simp only [EulerProductSupport.eulerRatio_empty] at htail
  have hbound : 1 - EulerProductSupport.eulerRatio P ≤ (P.card : ℚ) / (L + 1 : ℚ) :=
    (le_abs_self _).trans htail
  have hstrict : 1 / (n + 1 : ℚ) < (P.card : ℚ) / (L + 1 : ℚ) := hmass.trans_le hbound
  have hcross := (div_lt_div_iff₀ hmpos hLpos).mp hstrict
  simp only [one_mul] at hcross
  have hnat : L + 1 < P.card * (n + 1) := by exact_mod_cast hcross
  simpa [Nat.mul_comm] using hnat


end TotientSupportGrowth
