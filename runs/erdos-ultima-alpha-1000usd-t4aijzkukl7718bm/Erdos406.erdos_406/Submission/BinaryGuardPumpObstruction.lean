import Submission.BinaryAncestorFamilies

/-! A positive binary pumping loop returns modulo every power of three.
Consequently a loop of closure failures through one good input cannot be
repaired by a fixed ternary-tail guard and an increased cutoff.
This is only an obstruction to such a certificate, not to Erdős 406. -/
namespace Erdos406BinaryGuardPump
open Erdos406BinaryAncestors Erdos406BinaryCertificate

lemma binaryLoop_mod_period (seed L b r : ℕ) :
    ∃ p : ℕ, 0 < p ∧ ∀ t : ℕ,
      binaryLoop seed L b (p * t) % 3 ^ r = seed % 3 ^ r := by
  let q := 3 ^ r
  letI : NeZero q := ⟨by dsimp [q]; positivity⟩
  let f : ZMod q → ZMod q := fun x => (2 ^ L : ℕ) * x + b
  have hu : IsUnit ((2 ^ L : ℕ) : ZMod q) :=
    (ZMod.isUnit_iff_coprime _ _).mpr
      (((by decide : Nat.Coprime 2 3).pow_left L).pow_right r)
  have hinj : Function.Injective f := by
    intro x y hxy
    exact hu.mul_right_injective (add_right_cancel hxy)
  have hcast (t : ℕ) : ((binaryLoop seed L b t : ℕ) : ZMod q) = f^[t] (seed : ZMod q) := by
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [binaryLoop, Nat.cast_add, Nat.cast_mul, ih, Function.iterate_succ_apply']
  obtain ⟨p, hp, hper⟩ := Function.mem_periodicPts.mp (hinj.mem_periodicPts (seed : ZMod q))
  refine ⟨p, hp, fun t => ?_⟩
  have hh : ((binaryLoop seed L b (p * t) : ℕ) : ZMod q) = seed := by
    rw [hcast]
    exact (hper.mul_const t).eq
  exact (ZMod.natCast_eq_natCast_iff' _ _ q).mp hh

lemma binaryLoop_linear_growth (seed L b t : ℕ) (hseed : 0 < seed) (hL : 0 < L) :
    seed + t ≤ binaryLoop seed L b t := by
  have hpow : 2 ≤ 2 ^ L := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 1 ≤ L)
    simpa using hh
  induction t with
  | zero => rfl
  | succ t ih =>
    have hh := Nat.mul_le_mul_right (binaryLoop seed L b t) hpow
    rw [binaryLoop]
    omega

/-- A fixed affine binary loop with positive prefix and one whole-good baseline
has arbitrarily large points in every fixed good ternary-tail cylinder. The
pumped points are not asserted to be whole-good or powers of two. -/
theorem loop_hits_all_fixed_good_guards (seed L b u v : ℕ)
    (hseed : 0 < seed) (hL : 0 < L)
    (hgood : Nat.digits 3 (2 ^ u * seed + v) ⊆ [0, 1])
    (P : ℕ → Prop) (hP : ∀ t : ℕ, P (2 ^ u * binaryLoop seed L b t + v))
    (r M : ℕ) :
    ∃ n : ℕ, M ≤ n ∧ Nat.digits 3 (n % 3 ^ r) ⊆ [0, 1] ∧ P n := by
  obtain ⟨p, hp, hper⟩ := binaryLoop_mod_period seed L b r
  let t := p * (M + 1)
  let n := 2 ^ u * binaryLoop seed L b t + v
  refine ⟨n, ?_, ?_, hP t⟩
  · have hgrow := binaryLoop_linear_growth seed L b t hseed hL
    have ht : M + 1 ≤ t := by
      dsimp [t]
      have hh := Nat.mul_le_mul_right (M + 1) (show 1 ≤ p by omega)
      simpa using hh
    have hpow : 1 ≤ 2 ^ u := Nat.one_le_pow _ _ (by decide)
    have hm : binaryLoop seed L b t ≤ 2 ^ u * binaryLoop seed L b t := by
      simpa using Nat.mul_le_mul_right (binaryLoop seed L b t) hpow
    dsimp [n]
    omega
  · have hm : Nat.ModEq (3 ^ r) (binaryLoop seed L b t) seed := hper (M + 1)
    have hh := (hm.mul_left (2 ^ u)).add_right v
    have hg := good_mod hgood r
    change n % 3 ^ r = (2 ^ u * seed + v) % 3 ^ r at hh
    simpa only [hh] using hg

/-- In particular, a family of actual arithmetic closure failures with such a
loop defeats every finite-tail guard and every proposed larger cutoff. -/
theorem no_guarded_closure_repair (A : ℕ → Prop) (c seed L b u v : ℕ)
    (hseed : 0 < seed) (hL : 0 < L)
    (hgood : Nat.digits 3 (2 ^ u * seed + v) ⊆ [0, 1])
    (hfail : ∀ t : ℕ,
      A (2 ^ u * binaryLoop seed L b t + v) ∧
      ¬ A (3 * (2 ^ u * binaryLoop seed L b t + v) + c)) :
    ¬ ∃ r M : ℕ, ∀ n : ℕ, M ≤ n → Nat.digits 3 (n % 3 ^ r) ⊆ [0, 1] →
      A n → A (3 * n + c) := by
  rintro ⟨r, M, hclosed⟩
  obtain ⟨n, hn, hg, ha, hna⟩ := loop_hits_all_fixed_good_guards seed L b u v
    hseed hL hgood (fun n => A n ∧ ¬ A (3 * n + c)) hfail r M
  exact hna (hclosed n hn hg ha)

#print axioms binaryLoop_mod_period
#print axioms binaryLoop_linear_growth
#print axioms loop_hits_all_fixed_good_guards
#print axioms no_guarded_closure_repair
end Erdos406BinaryGuardPump
