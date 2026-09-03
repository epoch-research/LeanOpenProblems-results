import Submission.SingleAffineCertificates
import Submission.GeneralResidueObstruction

/-! Every prefix cylinder meets both a hypothetical eventual affine invariant
and its complement. These are necessary conditions, not an invariant witness
or a proof of Erdős 406. -/
namespace Erdos406Work
open Erdos406AffineCertificate Erdos406SingleAffine

lemma affine_iterate_identity (t n : ℕ) :
    3 * (fun x : ℕ => 4 * x + 1)^[t] n + 1 = 4 ^ t * (3 * n + 1) := by
  induction t with
  | zero => simp
  | succ t ih => rw [Function.iterate_succ_apply', pow_succ]; nlinarith

lemma affine_invariant_iterate (P : ℕ → Prop)
    (hclosed : ∀ n, P n → P (4 * n + 1)) {n : ℕ} (hn : P n) (t : ℕ) :
    P ((fun x : ℕ => 4 * x + 1)^[t] n) := by
  induction t with
  | zero => simpa using hn
  | succ t ih => rw [Function.iterate_succ_apply']; exact hclosed _ ih

lemma affine_invariant_orbit_tail (P : ℕ → Prop) (E : ℕ)
    (hclosed : ∀ n, P n → P (4 * n + 1)) (hseed : P (orbit 4 1 E)) (j : ℕ) :
    P (orbit 4 1 (E + j)) := by
  induction j with
  | zero => simpa using hseed
  | succ j ih => rw [← Nat.add_assoc, orbit_succ]; exact hclosed _ ih

lemma divided_prefix_three {n A L : ℕ} (h : n / 3 ^ L = 3 * A) :
    (n / 3) / 3 ^ L = A := by
  have he : (n / 3) / 3 ^ L = (n / 3 ^ L) / 3 := by
    simp only [Nat.div_div_eq_div_mul]
    rw [Nat.mul_comm 3 (3 ^ L)]
  rw [he, h]
  omega

/-- Arbitrarily late affine orbit values have any prescribed leading block. -/
lemma affine_orbit_in_prefix (A E M : ℕ) (hA : 0 < A) :
    ∃ j L : ℕ, M ≤ j ∧ orbit 4 1 (E + j) / 3 ^ L = A := by
  obtain ⟨j, L, hj, hlead⟩ := leading_prefix_in_four_progression (3 * A) E 1 M
    (by positivity) (by decide)
  simp only [one_mul] at hlead
  have hid := single_orbit_identity (E + j)
  have hdiv : 4 ^ (E + j) / 3 = orbit 4 1 (E + j) := by omega
  refine ⟨j, L, hj, ?_⟩
  rw [← hdiv]
  exact divided_prefix_three hlead

/-- Every positive prefix also contains arbitrarily large integers that
 eventually enter the good set under x↦4x+1. No pure-power assertion is made. -/
lemma affine_good_predecessor_in_prefix (A M : ℕ) (hA : 0 < A) :
    ∃ t n L : ℕ, 0 < t ∧ M < n ∧ n / 3 ^ L = A ∧
      Nat.digits 3 ((fun x : ℕ => 4 * x + 1)^[t] n) ⊆ [0, 1] := by
  obtain ⟨t, N, L, ht, hN, hlead, hgood, hmod⟩ :=
    arbitrary_prefix_can_disappear_full_mod (3 * A) 1 3 0 (3 * M + 2)
      (by positivity) (by decide) (by decide)
  simp only [one_mul] at hgood
  have hrem : N % 3 = 1 := by simpa [Nat.ModEq] using hmod
  let n := N / 3
  have hNid : N = 3 * n + 1 := by dsimp [n]; omega
  have hid := affine_iterate_identity t n
  have hquot : (4 ^ t * N) / 3 = (fun x : ℕ => 4 * x + 1)^[t] n := by
    rw [hNid]
    omega
  refine ⟨t, n, L, ht, ?_, divided_prefix_three hlead, ?_⟩
  · dsimp [n]; omega
  · have hh := good_div_three hgood
    rwa [hquot] at hh

/-- Any forward-invariant set rejecting all good integers is co-dense in
 positive prefix cylinders, even without a seed premise. -/
theorem affine_invariant_rejected_prefix (P : ℕ → Prop)
    (hclosed : ∀ n, P n → P (4 * n + 1))
    (hsafe : ∀ n, Nat.digits 3 n ⊆ [0, 1] → ¬ P n) (A M : ℕ) (hA : 0 < A) :
    ∃ n L : ℕ, M < n ∧ n / 3 ^ L = A ∧ ¬ P n := by
  obtain ⟨t, n, L, ht, hn, hlead, hg⟩ := affine_good_predecessor_in_prefix A M hA
  refine ⟨n, L, hn, hlead, fun hp => ?_⟩
  exact hsafe _ hg (affine_invariant_iterate P hclosed hp t)

/-- A seed in the eventual orbit makes the invariant dense in the same
 cylinders. Thus no homogeneous accepting or rejecting suffix cylinder can
 be part of a valid DFA invariant. -/
theorem affine_invariant_prefix_two_sided (P : ℕ → Prop) (E : ℕ)
    (hclosed : ∀ n, P n → P (4 * n + 1)) (hseed : P (orbit 4 1 E))
    (hsafe : ∀ n, Nat.digits 3 n ⊆ [0, 1] → ¬ P n) (A : ℕ) (hA : 0 < A) :
    (∃ n L : ℕ, n / 3 ^ L = A ∧ P n) ∧
      (∃ n L : ℕ, n / 3 ^ L = A ∧ ¬ P n) := by
  constructor
  · obtain ⟨j, L, hj, hlead⟩ := affine_orbit_in_prefix A E 0 hA
    exact ⟨_, L, hlead, affine_invariant_orbit_tail P E hclosed hseed j⟩
  · obtain ⟨n, L, hn, hlead, hnot⟩ := affine_invariant_rejected_prefix P hclosed hsafe A 0 hA
    exact ⟨n, L, hlead, hnot⟩

lemma msd_evalNat_of_prefix {σ : Type*} (D : DFA ℕ σ) {n A L : ℕ}
    (h : n / 3 ^ L = A) :
    Erdos406MSDCertificate.evalNat D n = D.evalFrom
      (Erdos406MSDCertificate.evalNat D A) ((Nat.digits 3 n).take L).reverse := by
  have hdrop := congrArg (Nat.digits 3) h
  rw [digits_div_three_pow] at hdrop
  have he : Nat.digits 3 n = (Nat.digits 3 n).take L ++ Nat.digits 3 A := by
    rw [← hdrop]
    exact (List.take_append_drop L (Nat.digits 3 n)).symm
  have hre : (Nat.digits 3 n).reverse =
      (Nat.digits 3 A).reverse ++ ((Nat.digits 3 n).take L).reverse := by
    conv_lhs => rw [he]
    rw [List.reverse_append]
  unfold Erdos406MSDCertificate.evalNat
  rw [hre, DFA.eval, DFA.evalFrom_of_append]

/-- In particular, every canonical positive-prefix state of a hypothetical
 DFA invariant must have both an accepting and a rejecting continuation. -/
theorem affine_dfa_prefix_continuations {σ : Type*} (D : DFA ℕ σ) (E : ℕ)
    (hclosed : ∀ n, Erdos406MSDCertificate.evalNat D n ∈ D.accept →
      Erdos406MSDCertificate.evalNat D (4 * n + 1) ∈ D.accept)
    (hseed : Erdos406MSDCertificate.evalNat D (orbit 4 1 E) ∈ D.accept)
    (hsafe : ∀ n, Nat.digits 3 n ⊆ [0, 1] →
      Erdos406MSDCertificate.evalNat D n ∉ D.accept) (A : ℕ) (hA : 0 < A) :
    (∃ w : List ℕ, D.evalFrom (Erdos406MSDCertificate.evalNat D A) w ∈ D.accept) ∧
      (∃ w : List ℕ, D.evalFrom (Erdos406MSDCertificate.evalNat D A) w ∉ D.accept) := by
  obtain ⟨⟨n, L, hn, hp⟩, ⟨m, K, hm, hnot⟩⟩ := affine_invariant_prefix_two_sided
    (fun n => Erdos406MSDCertificate.evalNat D n ∈ D.accept) E hclosed hseed hsafe A hA
  constructor
  · exact ⟨_, (msd_evalNat_of_prefix D hn) ▸ hp⟩
  · exact ⟨_, (msd_evalNat_of_prefix D hm) ▸ hnot⟩

#print axioms affine_dfa_prefix_continuations
#print axioms affine_good_predecessor_in_prefix
#print axioms affine_invariant_prefix_two_sided
end Erdos406Work
