import Submission.PrefixInvariantNecessity
import Submission.PurePowerCubeBoundary

/-! Necessary two-sided suffix density for affine invariant certificates.
No sufficient invariant is asserted. -/
namespace Erdos406Work
open Erdos406AffineCertificate Erdos406SingleAffine

lemma affine_modulus_cancel {r n v : ℕ}
    (h : Nat.ModEq (3 ^ (r + 1)) (3 * n + 1) (3 * v + 1)) :
    Nat.ModEq (3 ^ r) n v := by
  have hh := Nat.ModEq.add_right_cancel' 1 h
  rw [pow_succ'] at hh
  exact Nat.ModEq.mul_left_cancel' (by decide : 3 ≠ 0) hh

/-- The affine orbit visits every ternary residue class arbitrarily late. -/
lemma affine_orbit_in_residue (r v E : ℕ) :
    ∃ k : ℕ, E ≤ k ∧ Nat.ModEq (3 ^ r) (orbit 4 1 k) v := by
  obtain ⟨e, he, hres⟩ := unit_power_residue r (3 * v + 1) (by omega)
  let k := e + 3 ^ r * E
  have hp : 1 ≤ 3 ^ r := Nat.one_le_pow _ _ (by decide)
  have hlate : E ≤ k := by dsimp [k]; nlinarith
  have ht : Nat.ModEq (3 ^ (r + 1)) (4 ^ (3 ^ r * E)) 1 :=
    (four_pow_mod_eq_one_iff r _).mpr (dvd_mul_right _ _)
  have hm : Nat.ModEq (3 ^ (r + 1)) (4 ^ k) (3 * v + 1) := by
    dsimp [k]
    simpa only [← pow_add, mul_one] using hres.mul ht
  rw [← single_orbit_identity k] at hm
  exact ⟨k, hlate, affine_modulus_cancel hm⟩

/-- Arbitrarily large members of every ternary residue class eventually
 reach a good integer. These need not be in the orbit from zero. -/
lemma affine_good_predecessor_in_residue (r v M : ℕ) :
    ∃ t n : ℕ, 0 < t ∧ M < n ∧ Nat.ModEq (3 ^ r) n v ∧
      Nat.digits 3 ((fun x : ℕ => 4 * x + 1)^[t] n) ⊆ [0, 1] := by
  obtain ⟨e, he, hres⟩ := unit_power_residue r (3 * v + 1) (by omega)
  obtain ⟨t, N, L, ht, hN, hlead, hgood, hmod⟩ :=
    arbitrary_prefix_can_disappear_full_mod 3 1 (3 ^ (r + 1)) e (3 * M + 2)
      (by decide) (by decide) (by positivity)
  simp only [one_mul] at hmod hgood
  have hm := hmod.trans hres
  have hrem : N % 3 = 1 := by
    have hh := hm.of_dvd (dvd_pow_self 3 (by omega : r + 1 ≠ 0))
    simpa [Nat.ModEq] using hh
  let n := N / 3
  have hNid : N = 3 * n + 1 := by dsimp [n]; omega
  have hid := affine_iterate_identity t n
  have hquot : (4 ^ t * N) / 3 = (fun x : ℕ => 4 * x + 1)^[t] n := by
    rw [hNid]
    omega
  refine ⟨t, n, ht, ?_, ?_, ?_⟩
  · dsimp [n]; omega
  · rw [hNid] at hm
    exact affine_modulus_cancel hm
  · have hh := good_div_three hgood
    rwa [hquot] at hh

/-- Every fixed ternary suffix must occur in both the accepted and rejected
 language of a valid eventual affine invariant. -/
theorem affine_invariant_residue_two_sided (P : ℕ → Prop) (E : ℕ)
    (hclosed : ∀ n, P n → P (4 * n + 1)) (hseed : P (orbit 4 1 E))
    (hsafe : ∀ n, Nat.digits 3 n ⊆ [0, 1] → ¬ P n) (r v : ℕ) :
    (∃ n, Nat.ModEq (3 ^ r) n v ∧ P n) ∧
      (∃ n, Nat.ModEq (3 ^ r) n v ∧ ¬ P n) := by
  constructor
  · obtain ⟨k, hk, hmod⟩ := affine_orbit_in_residue r v E
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact ⟨_, hmod, affine_invariant_orbit_tail P E hclosed hseed j⟩
  · obtain ⟨t, n, ht, hn, hmod, hgood⟩ := affine_good_predecessor_in_residue r v 0
    refine ⟨n, hmod, fun hp => ?_⟩
    exact hsafe _ hgood (affine_invariant_iterate P hclosed hp t)

lemma eval_msd_value {σ : Type*} (D : DFA ℕ σ) (hpad : D.step D.start 0 = D.start)
    (w : List ℕ) (hw : ∀ d ∈ w, d < 3) :
    D.eval w = Erdos406MSDCertificate.evalNat D (Nat.ofDigits 3 w.reverse) := by
  induction w using List.reverseRecOn with
  | nil => simp [Erdos406MSDCertificate.evalNat]
  | append_singleton w d ih =>
    have hd : d < 3 := hw d (by simp)
    have ht : ∀ a ∈ w, a < 3 := fun a ha => hw a (by simp [ha])
    rw [DFA.eval_append_singleton, ih ht]
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append, Nat.ofDigits_cons]
    by_cases hn : d + 3 * Nat.ofDigits 3 w.reverse = 0
    · have hd0 : d = 0 := by omega
      have hv0 : Nat.ofDigits 3 w.reverse = 0 := by omega
      simp [hd0, hv0, Erdos406MSDCertificate.evalNat_zero, hpad]
    · rw [Erdos406MSDCertificate.evalNat_pos D (by omega : 0 < d + 3 * Nat.ofDigits 3 w.reverse)]
      have hdiv : (d + 3 * Nat.ofDigits 3 w.reverse) / 3 = Nat.ofDigits 3 w.reverse := by omega
      have hmod : (d + 3 * Nat.ofDigits 3 w.reverse) % 3 = d := by omega
      rw [hdiv, hmod]

lemma msd_evalNat_of_suffix {σ : Type*} (D : DFA ℕ σ) (hpad : D.step D.start 0 = D.start)
    (w : List ℕ) (hw : ∀ d ∈ w, d < 3) (n : ℕ)
    (hmod : Nat.ModEq (3 ^ w.length) n (Nat.ofDigits 3 w.reverse)) :
    Erdos406MSDCertificate.evalNat D n =
      D.evalFrom (Erdos406MSDCertificate.evalNat D (n / 3 ^ w.length)) w := by
  have hv : Nat.ofDigits 3 w.reverse < 3 ^ w.length := by
    simpa using Nat.ofDigits_lt_base_pow_length (by decide : 1 < 3)
      (fun d hd => hw d (List.mem_reverse.mp hd))
  change n % 3 ^ w.length = Nat.ofDigits 3 w.reverse % 3 ^ w.length at hmod
  rw [Nat.mod_eq_of_lt hv] at hmod
  let u := (Nat.digits 3 (n / 3 ^ w.length)).reverse
  have hu : ∀ d ∈ u ++ w, d < 3 := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact Nat.digits_lt_base (by decide) (List.mem_reverse.mp hd)
    · exact hw d hd
  have hval : Nat.ofDigits 3 (u ++ w).reverse = n := by
    dsimp [u]
    rw [List.reverse_append, List.reverse_reverse, Nat.ofDigits_append,
      List.length_reverse, Nat.ofDigits_digits]
    rw [← hmod]
    exact Nat.mod_add_div n (3 ^ w.length)
  have hh := eval_msd_value D hpad (u ++ w) hu
  rw [hval, DFA.eval, DFA.evalFrom_of_append] at hh
  exact hh.symm

/-- No valid ternary suffix can map every state into the accepting set, or
 every state into its complement, for a valid eventual affine invariant. -/
theorem affine_dfa_suffix_images {σ : Type*} (D : DFA ℕ σ)
    (hpad : D.step D.start 0 = D.start) (E : ℕ)
    (hclosed : ∀ n, Erdos406MSDCertificate.evalNat D n ∈ D.accept →
      Erdos406MSDCertificate.evalNat D (4 * n + 1) ∈ D.accept)
    (hseed : Erdos406MSDCertificate.evalNat D (orbit 4 1 E) ∈ D.accept)
    (hsafe : ∀ n, Nat.digits 3 n ⊆ [0, 1] →
      Erdos406MSDCertificate.evalNat D n ∉ D.accept)
    (w : List ℕ) (hw : ∀ d ∈ w, d < 3) :
    (∃ s, D.evalFrom s w ∈ D.accept) ∧ (∃ s, D.evalFrom s w ∉ D.accept) := by
  obtain ⟨⟨n, hn, hp⟩, ⟨m, hm, hnot⟩⟩ := affine_invariant_residue_two_sided
    (fun n => Erdos406MSDCertificate.evalNat D n ∈ D.accept) E hclosed hseed hsafe
    w.length (Nat.ofDigits 3 w.reverse)
  constructor
  · exact ⟨_, (msd_evalNat_of_suffix D hpad w hw n hn) ▸ hp⟩
  · exact ⟨_, (msd_evalNat_of_suffix D hpad w hw m hm) ▸ hnot⟩

theorem affine_dfa_no_reset_word {σ : Type*} (D : DFA ℕ σ)
    (hpad : D.step D.start 0 = D.start) (E : ℕ)
    (hclosed : ∀ n, Erdos406MSDCertificate.evalNat D n ∈ D.accept →
      Erdos406MSDCertificate.evalNat D (4 * n + 1) ∈ D.accept)
    (hseed : Erdos406MSDCertificate.evalNat D (orbit 4 1 E) ∈ D.accept)
    (hsafe : ∀ n, Nat.digits 3 n ⊆ [0, 1] →
      Erdos406MSDCertificate.evalNat D n ∉ D.accept)
    (w : List ℕ) (hw : ∀ d ∈ w, d < 3) :
    ¬ ∃ q, ∀ s, D.evalFrom s w = q := by
  obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := affine_dfa_suffix_images D hpad E hclosed hseed hsafe w hw
  rintro ⟨q, hq⟩
  rw [hq s] at hs
  rw [hq t] at ht
  exact ht hs

#print axioms affine_dfa_suffix_images
#print axioms affine_dfa_no_reset_word
#print axioms affine_orbit_in_residue
#print axioms affine_good_predecessor_in_residue
#print axioms affine_invariant_residue_two_sided
end Erdos406Work
