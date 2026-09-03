import Submission.FiniteSieveReduction

/-! Fixed-cutoff and fixed-seed facts do not supply the missing uniform sieve cutoff. -/
namespace Erdos952Investigation
namespace SieveQuantifiers
open FiniteSieveReduction

set_option maxHeartbeats 0

/-- Every fixed finite sieve admits an infinite ray when its step bound may
be chosen after the cutoff. -/
theorem every_cutoff_has_some_ray (N : ℕ) : ∃ C : ℤ, HasSieveRay C N := by
  let P : ℕ := N.factorial
  have hP : 0 < P := Nat.factorial_pos _
  let x : ℕ → GaussianInt := fun n => ⟨1 + (P : ℤ) * (n : ℤ), 0⟩
  refine ⟨(P : ℤ)^2 + 1, x, ?_, ?_, ?_⟩
  · intro i j hij
    have he := congrArg Zsqrtd.re hij
    change 1 + (P : ℤ) * (i : ℤ) = 1 + (P : ℤ) * (j : ℤ) at he
    have hP0 : (P : ℤ) ≠ 0 := by exact_mod_cast hP.ne'
    exact Int.natCast_inj.mp (mul_left_cancel₀ hP0 (add_left_cancel he))
  · intro n p hpN hp hdiv
    letI : Fact p.Prime := ⟨hp⟩
    have hpP : p ∣ P := Nat.dvd_factorial hp.pos hpN
    have hPzero : (P : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff P p).mpr hpP
    have hnorm : ((x n).norm : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (x n).norm p).mpr hdiv
    have hnormone : ((x n).norm : ZMod p) = 1 := by
      simp [x, gaussian_norm_sq, hPzero]
    exact one_ne_zero (hnormone.symm.trans hnorm)
  · intro n
    have he : x (n + 1) - x n = (P : GaussianInt) := by
      apply Zsqrtd.ext
      · simp [x]
        ring
      · simp [x]
    rw [he]
    simp [gaussian_norm_sq]

lemma allowed_small_norm {N : ℕ} (hN : 2 ≤ N) {z : GaussianInt}
    (hz : Allowed N z) (hbound : z.norm ≤ (N : ℤ)) : z.norm = 1 := by
  have hn : 0 ≤ z.norm := GaussianInt.norm_nonneg z
  have hnorm0 : z.norm ≠ 0 := by
    intro he
    apply hz 2 hN (by decide)
    simp [he]
  have hnpos : 0 < z.norm.natAbs := Int.natAbs_pos.mpr hnorm0
  have hcast : (z.norm.natAbs : ℤ) = z.norm := Int.natAbs_of_nonneg hn
  by_contra he
  have hneone : z.norm.natAbs ≠ 1 := by intro ht; rw [ht] at hcast; exact he hcast.symm
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hneone
  have hpn : p ≤ N := by
    have hple : (p : ℤ) ≤ z.norm.natAbs := by exact_mod_cast Nat.le_of_dvd hnpos hpd
    rw [hcast] at hple
    exact_mod_cast hple.trans hbound
  exact hz p hpn hp (Int.natCast_dvd.mpr hpd)

lemma norm_le_twice_norm_sub_add (z w : GaussianInt) :
    w.norm ≤ 2 * (w - z).norm + 2 * z.norm := by
  simp only [gaussian_norm_sq, Zsqrtd.re_sub, Zsqrtd.im_sub]
  nlinarith [sq_nonneg (w.re - 2 * z.re), sq_nonneg (w.im - 2 * z.im)]

/-- A cutoff can trap each fixed seed for every step bound. The cutoff here
depends on the seed; this is not the uniform statement needed for a disproof. -/
theorem every_fixed_seed_eventually_trapped (C : ℤ) (z : GaussianInt) :
    ∃ N : ℕ, {w | (sieveGraph C N).Reachable z w}.Finite := by
  let N : ℕ := z.norm.natAbs + 2 * C.natAbs + 3
  have hN2 : 2 ≤ N := by dsimp [N]; omega
  have hNform : (N : ℤ) = z.norm + 2 * |C| + 3 := by
    simp [N, abs_of_nonneg (GaussianInt.norm_nonneg z)]
  have hNz : z.norm ≤ (N : ℤ) := by
    have := abs_nonneg C
    omega
  have hNC : 2 * C + 2 ≤ (N : ℤ) := by
    have := le_abs_self C
    have := GaussianInt.norm_nonneg z
    omega
  let S : Set GaussianInt := {w | w.norm ≤ 1} ∪ {z}
  have hS : S.Finite := (norm_sublevel_finite 1).union (Set.finite_singleton z)
  have hzS : z ∈ S := Or.inr rfl
  have hclosed : ∀ u ∈ S, ∀ w, (sieveGraph C N).Adj u w → w ∈ S := by
    intro u hu w huw
    have hun : u.norm ≤ (N : ℤ) := by
      rcases hu with hu | hu
      · have hNcast : (2 : ℤ) ≤ N := by exact_mod_cast hN2
        exact hu.trans (by omega)
      · rw [Set.mem_singleton_iff.mp hu]
        exact hNz
    have huone := allowed_small_norm hN2 huw.1 hun
    have hstep := huw.2.2.2
    have hnorm := norm_le_twice_norm_sub_add u w
    have hwn : w.norm ≤ (N : ℤ) := by omega
    exact Or.inl (le_of_eq (allowed_small_norm hN2 huw.2.1 hwn))
  refine ⟨N, hS.subset ?_⟩
  have hwalk : ∀ {a b : GaussianInt}, (sieveGraph C N).Walk a b → a ∈ S → b ∈ S := by
    intro a b p
    induction p with
    | nil => exact id
    | cons hab p ih => exact fun ha => ih (hclosed _ ha _ hab)
  intro w hw
  exact hw.elim fun p => hwalk p hzS

#print axioms every_cutoff_has_some_ray
#print axioms every_fixed_seed_eventually_trapped

end SieveQuantifiers
end Erdos952Investigation
