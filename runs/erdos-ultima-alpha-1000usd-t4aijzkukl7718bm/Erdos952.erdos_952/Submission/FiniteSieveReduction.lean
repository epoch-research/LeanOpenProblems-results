import Submission.AdmissibleRay

/-! An exact finite-sieve characterization of the admissible-ray obstruction. -/
namespace Erdos952Investigation
namespace FiniteSieveReduction

open AdmissibleRay
set_option maxHeartbeats 0

/-- A normalized ray with an independently chosen avoiding translate at each prime. -/
def HasAdmissibleRay (C : ℤ) : Prop :=
  ∃ y : ℕ → GaussianInt, y 0 = 0 ∧ Function.Injective y ∧
    (∀ n, (y (n + 1) - y n).norm < C) ∧
    ∀ p : ℕ, p.Prime → ∃ a b : ZMod p, ∀ n, Good p a b (y n)

/-- The usual sieve, not an arbitrarily translated set of residue conditions. -/
def Allowed (N : ℕ) (z : GaussianInt) : Prop :=
  ∀ p ≤ N, p.Prime → ¬ (p : ℤ) ∣ z.norm

def HasSieveRay (C : ℤ) (N : ℕ) : Prop :=
  ∃ x : ℕ → GaussianInt, Function.Injective x ∧
    (∀ n, Allowed N (x n)) ∧ ∀ n, (x (n + 1) - x n).norm < C

lemma prime_crt (N : ℕ) (r : ∀ p : ℕ, p.Prime → ZMod p) :
    ∃ a : ℕ, ∀ p ≤ N, ∀ hp : p.Prime, (a : ZMod p) = r p hp := by
  classical
  let S := (Finset.range (N + 1)).filter Nat.Prime
  let s : ℕ → ℕ := fun p => if hp : p.Prime then (r p hp).val else 0
  have hmem {p : ℕ} (hp : p ∈ S) : p ≤ N ∧ p.Prime := by
    simpa only [S, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] using hp
  have hcop : (S : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hmem hp).2 (hmem hq).2).mpr hpq
  let a := Nat.chineseRemainderOfFinset s id S (fun p hp => (hmem hp).2.ne_zero) hcop
  refine ⟨a.val, ?_⟩
  intro p hpN hp
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hpS : p ∈ S := by simp [S, hp, hpN]
  have he : (a.val : ZMod p) = (s p : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (a.property p hpS)
  simpa [s, hp, ZMod.natCast_val, ZMod.cast_id] using he

lemma admissible_implies_finite_sieve_rays {C : ℤ} (h : HasAdmissibleRay C) :
    ∀ N, HasSieveRay C N := by
  classical
  rintro N
  rcases h with ⟨y, _, hy, hs, hg⟩
  choose a b hab using hg
  obtain ⟨A, hA⟩ := prime_crt N a
  obtain ⟨B, hB⟩ := prime_crt N b
  let z : GaussianInt := ⟨A, B⟩
  refine ⟨fun n => z + y n, ?_, ?_, ?_⟩
  · intro i j hij
    exact hy (add_left_cancel hij)
  · intro n p hpN hp
    have hgood : Good p (A : ZMod p) (B : ZMod p) (y n) := by
      rw [hA p hpN hp, hB p hpN hp]
      exact hab p hp n
    intro hdiv
    have he := (ZMod.intCast_zmod_eq_zero_iff_dvd (z + y n).norm p).mpr hdiv
    apply hgood
    simpa [gaussian_norm_sq, z] using he
  · intro n
    simpa only [add_sub_add_left_eq_sub] using hs n

lemma good_of_sieve {p : ℕ} {z w : GaussianInt} (h : ¬ (p : ℤ) ∣ z.norm) :
    Good p (w.re : ZMod p) (w.im : ZMod p) (z - w) := by
  intro hzero
  apply h
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd z.norm p).mp
  simpa [Good, gaussian_norm_sq] using hzero

lemma sieve_ray_gives_prefix {C : ℤ} {N : ℕ} (h : HasSieveRay C N) :
    Nonempty (AdmissibleRay.Prefix C N) := by
  rcases h with ⟨x, hx, hA, hs⟩
  let f : Fin (N + 1) → GaussianInt := fun i => x i.val - x 0
  have hf0 : f 0 = 0 := by simp [f]
  have hfi : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply hx
    simpa [f] using hij
  have hstep (i : Fin N) : (latticeGraph C).Adj (f i.castSucc) (f i.succ) := by
    refine ⟨fun he => ?_, ?_⟩
    · have := congrArg Fin.val (hfi he)
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
    · simpa only [f, Fin.val_castSucc, Fin.val_succ, sub_sub_sub_cancel_right] using hs i.val
  refine ⟨⟨⟨f, hf0, hfi, hstep⟩, ?_⟩⟩
  intro p hpN hp
  exact ⟨(x 0).re, (x 0).im, fun i => good_of_sieve (hA i.val p hpN hp)⟩

theorem admissible_ray_iff_finite_sieve_rays (C : ℤ) :
    HasAdmissibleRay C ↔ ∀ N, HasSieveRay C N := by
  refine ⟨admissible_implies_finite_sieve_rays, ?_⟩
  intro h
  exact AdmissibleRay.ray_of_prefixes C (fun N => sieve_ray_gives_prefix (h N))

def sieveGraph (C : ℤ) (N : ℕ) : SimpleGraph GaussianInt where
  Adj z w := Allowed N z ∧ Allowed N w ∧ z ≠ w ∧ (w - z).norm < C
  symm := by
    intro z w h
    exact ⟨h.2.1, h.1, h.2.2.1.symm, by rw [norm_sub_comm]; exact h.2.2.2⟩
  loopless := by intro z h; exact h.2.2.1 rfl

lemma sieveGraph_finite_neighbors (C : ℤ) (N : ℕ) (z : GaussianInt) :
    ((sieveGraph C N).neighborSet z).Finite := by
  have hinj : Function.Injective (fun w : GaussianInt => w - z) := by
    intro w v h
    simpa using h
  apply ((norm_sublevel_finite C).preimage (f := fun w => w - z) hinj.injOn).subset
  intro w hw
  exact le_of_lt hw.2.2.2

noncomputable instance (C : ℤ) (N : ℕ) : (sieveGraph C N).LocallyFinite :=
  fun z => (sieveGraph_finite_neighbors C N z).fintype

lemma sieve_ray_iff_infinite_component (C : ℤ) (N : ℕ) :
    HasSieveRay C N ↔ ∃ z, {w | (sieveGraph C N).Reachable z w}.Infinite := by
  constructor
  · rintro ⟨x, hx, hA, hs⟩
    refine ⟨x 0, (RayReduction.ray_iff_infinite_component (sieveGraph C N) (x 0)).mp ?_⟩
    refine ⟨x, rfl, hx, fun n => ⟨hA n, hA (n + 1), ?_, hs n⟩⟩
    intro he
    have := hx he
    omega
  · rintro ⟨z, hz⟩
    obtain ⟨x, _, hx, hs⟩ :=
      (RayReduction.ray_iff_infinite_component (sieveGraph C N) z).mpr hz
    exact ⟨x, hx, fun n => (hs n).1, fun n => (hs n).2.2.2⟩

/-- Compactness supplies a finite cutoff, but only after admissible rays have
been ruled out for the chosen step bound. -/
theorem no_admissible_ray_iff_finite_sieve_components (C : ℤ) :
    (¬ HasAdmissibleRay C) ↔
      ∃ N : ℕ, ∀ z : GaussianInt, {w | (sieveGraph C N).Reachable z w}.Finite := by
  rw [admissible_ray_iff_finite_sieve_rays]
  simp only [not_forall, sieve_ray_iff_infinite_component, not_exists, Set.not_infinite]

/-- A uniform finite-sieve obstruction is sufficient for the full negation of
the Gaussian moat conjecture. No such obstruction is assumed elsewhere. -/
theorem universal_sieve_obstruction_implies_disproof
    (hbarrier : ∀ C : ℤ, ∃ N : ℕ, ∀ z : GaussianInt,
      {w | (sieveGraph C N).Reachable z w}.Finite) :
    ¬ ∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n + 1) - x n).norm < C := by
  rintro ⟨x, C, hx, h⟩
  have hadmissible : HasAdmissibleRay C := prime_walk_yields_admissible_ray x C hx h
  exact (no_admissible_ray_iff_finite_sieve_components C).mpr (hbarrier C) hadmissible

#print axioms no_admissible_ray_iff_finite_sieve_components
#print axioms universal_sieve_obstruction_implies_disproof

#print axioms admissible_ray_iff_finite_sieve_rays

end FiniteSieveReduction
end Erdos952Investigation
