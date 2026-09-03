import Submission.GroupedAffineCertificates

/-! An exact one-orbit reformulation of Erdős406. The initial ternary digit
one is removed from each power4^m, leaving the orbit z'=4z+1 from zero.
No finiteness assertion or certificate witness is supplied. -/

namespace Erdos406SingleAffine
open Erdos406AffineCertificate Erdos406MSDCertificate

lemma single_orbit_identity (t : ℕ) : 3 * orbit 4 1 t + 1 = 4 ^ t := by
  induction t with
  | zero => simp
  | succ t ih => rw [orbit_succ, pow_succ]; nlinarith

lemma single_orbit_good_iff (t : ℕ) :
    Nat.digits 3 (orbit 4 1 t) ⊆ [0, 1] ↔ Nat.digits 3 (4 ^ t) ⊆ [0, 1] := by
  have he := single_orbit_identity t
  constructor
  · intro hd
    rw [← he]
    exact good_three_mul_add hd (by simp)
  · intro hd
    have hh := good_div_three hd
    have hquot : 4 ^ t / 3 = orbit 4 1 t := by omega
    simpa only [hquot] using hh

/-- This is an equivalence only; it does not establish either side. -/
theorem single_affine_iff :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite ↔
    {n : ℕ | (∃ t, n = orbit 4 1 t) ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite := by
  constructor
  · intro h
    refine (h.image (fun n => n / 3)).subset ?_
    rintro n ⟨⟨t, rfl⟩, hd⟩
    refine ⟨4 ^ t, ⟨four_power_isPowerOfTwo _, (single_orbit_good_iff t).mp hd⟩, ?_⟩
    dsimp only
    have he := single_orbit_identity t
    omega
  · intro h
    refine (h.image (fun n => 3 * n + 1)).subset ?_
    rintro n ⟨⟨k, rfl⟩, hd⟩
    obtain ⟨m, hm⟩ := even_exponent hd
    have he : 2 ^ k = 4 ^ m := by
      rw [show k = 2 * m by omega, pow_mul]
      rfl
    rw [he] at hd ⊢
    exact ⟨orbit 4 1 m, ⟨⟨m, rfl⟩, (single_orbit_good_iff m).mpr hd⟩,
      single_orbit_identity m⟩

/-- A single grouped affine certificate for q=4,c=1 would now suffice,
without the pair of q=64 classes. The required finite set is not supplied. -/
theorem single_affine_criterion
    (h : {n : ℕ | (∃ t, n = orbit 4 1 t) ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite) :
    {n : ℕ | n.isPowerOfTwo ∧ Nat.digits 3 n ⊆ [0, 1]}.Finite :=
  single_affine_iff.mpr h

#print axioms single_affine_iff
#print axioms single_affine_criterion
end Erdos406SingleAffine
