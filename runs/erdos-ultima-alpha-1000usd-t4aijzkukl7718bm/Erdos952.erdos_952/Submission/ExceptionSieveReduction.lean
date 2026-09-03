import Submission.FiniteCertificates
import Submission.SieveQuantifiers
import Submission.PeriodicSieveComponents

/-! An exact sieve reduction retaining the small Gaussian primes. Unlike the
ordinary sieve, these approximating graphs never delete genuine primes.
The needed cutoff may depend on the seed; its existence is not asserted. -/
namespace Erdos952Investigation
namespace ExceptionSieveReduction
open FiniteSieveReduction SieveQuantifiers PeriodicSieveComponents
set_option maxHeartbeats 0

/-- Exact primality in the norm ball of squared radius N, and the ordinary
finite sieve outside that ball. The equivalent disjunction is convenient. -/
def Candidate (N : ℕ) (z : GaussianInt) : Prop :=
  Prime z ∨ (N : ℤ)^2 < z.norm ∧ Allowed N z

lemma prime_candidate {N : ℕ} {z : GaussianInt} (hz : Prime z) : Candidate N z :=
  Or.inl hz

lemma candidate_iff_prime_of_norm_le {N : ℕ} {z : GaussianInt}
    (hz : z.norm ≤ (N : ℤ)^2) : Candidate N z ↔ Prime z := by
  constructor
  · rintro (hp | ⟨hlarge,_⟩)
    · exact hp
    · omega
  · exact prime_candidate

lemma prime_allowed_of_large {N : ℕ} {z : GaussianInt}
    (hz : Prime z) (hlarge : (N : ℤ)^2 < z.norm) : Allowed N z := by
  intro p hpN hp hdiv
  have hsmall := prime_norm_divisor_bound hz hp hdiv
  have hple : (p : ℤ) ≤ N := by exact_mod_cast hpN
  have hp0 : (0 : ℤ) ≤ p := Int.natCast_nonneg p
  nlinarith

lemma candidate_iff_allowed_of_large {N : ℕ} {z : GaussianInt}
    (hlarge : (N : ℤ)^2 < z.norm) : Candidate N z ↔ Allowed N z := by
  refine ⟨?_,fun h => Or.inr ⟨hlarge,h⟩⟩
  rintro (hp | ⟨_,ha⟩)
  · exact prime_allowed_of_large hp hlarge
  · exact ha

lemma candidate_antitone {M N : ℕ} (hMN : M ≤ N) {z : GaussianInt}
    (hz : Candidate N z) : Candidate M z := by
  rcases hz with hp | ⟨hlarge,ha⟩
  · exact prime_candidate hp
  · refine Or.inr ⟨?_,fun p hpM hp => ha p (hpM.trans hMN) hp⟩
    have hMN' : (M : ℤ) ≤ N := by exact_mod_cast hMN
    have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
    nlinarith

lemma candidate_all_iff_prime (z : GaussianInt) :
    (∀ N : ℕ, Candidate N z) ↔ Prime z := by
  refine ⟨?_,fun hp _ => prime_candidate hp⟩
  intro h
  apply (candidate_iff_prime_of_norm_le (N := z.norm.natAbs+1) ?_).mp (h _)
  have hn := GaussianInt.norm_nonneg z
  have hc : (z.norm.natAbs : ℤ) = z.norm := Int.natAbs_of_nonneg hn
  push_cast
  rw [abs_of_nonneg hn]
  nlinarith

/-- At each fixed cutoff only finitely many vertices differ from the usual
periodic sieve. Those exceptions retain the genuine small primes. -/
theorem candidate_diff_finite (N : ℕ) :
    {z : GaussianInt | ¬ (Candidate N z ↔ Allowed N z)}.Finite := by
  apply (norm_sublevel_finite ((N : ℤ)^2)).subset
  intro z hz
  change z.norm ≤ (N : ℤ)^2
  by_contra! hlarge
  exact hz (candidate_iff_allowed_of_large hlarge)

lemma candidate_add_period_outside {N : ℕ} {z d : GaussianInt}
    (hz : Candidate N z) (hzlarge : (N : ℤ)^2 < z.norm)
    (hdlarge : (N : ℤ)^2 < (z+d).norm) (hd : IsPeriod N d) :
    Candidate N (z+d) :=
  (candidate_iff_allowed_of_large hdlarge).mpr
    (allowed_add_period ((candidate_iff_allowed_of_large hzlarge).mp hz) hd)

def candidateGraph (C : ℤ) (N : ℕ) : SimpleGraph GaussianInt where
  Adj z w := Candidate N z ∧ Candidate N w ∧ z ≠ w ∧ (w-z).norm < C
  symm := by
    intro z w h
    exact ⟨h.2.1,h.1,h.2.2.1.symm,by rw [norm_sub_comm]; exact h.2.2.2⟩
  loopless := by intro z h; exact h.2.2.1 rfl

lemma primeGraph_le (C : ℤ) (N : ℕ) : primeGraph C ≤ candidateGraph C N := by
  intro z w h
  exact ⟨prime_candidate h.1,prime_candidate h.2.1,h.2.2⟩

lemma candidateGraph_antitone (C : ℤ) {M N : ℕ} (hMN : M ≤ N) :
    candidateGraph C N ≤ candidateGraph C M := by
  intro z w h
  exact ⟨candidate_antitone hMN h.1,candidate_antitone hMN h.2.1,h.2.2⟩

lemma candidateGraph_finite_neighbors (C : ℤ) (N : ℕ) (z : GaussianInt) :
    ((candidateGraph C N).neighborSet z).Finite := by
  apply ((norm_sublevel_finite C).preimage (f := fun w : GaussianInt => w-z)
    sub_left_injective.injOn).subset
  intro w hw
  exact hw.2.2.2.le

noncomputable instance (C : ℤ) (N : ℕ) : (candidateGraph C N).LocallyFinite :=
  fun z => (candidateGraph_finite_neighbors C N z).fintype

/-- Every actual finite prime barrier is already a barrier for a sufficiently
large exception-retaining cutoff. The same finite set can be used. -/
theorem cutoff_of_finite_prime_barrier (C : ℤ) (S : Finset GaussianInt)
    (hS : ∀ z ∈ S, ∀ w, (primeGraph C).Adj z w → w ∈ S) :
    ∃ N : ℕ, ∀ z ∈ S, ∀ w, (candidateGraph C N).Adj z w → w ∈ S := by
  obtain ⟨B,hB⟩ := (S.finite_toSet.image (fun z : GaussianInt => z.norm)).bddAbove
  let N : ℕ := 2*C.natAbs+2*B.natAbs+2
  have hN : (N : ℤ) = 2*|C|+2*|B|+2 := by simp [N]
  have hBN : B ≤ (N : ℤ) := by
    have := le_abs_self B
    have := abs_nonneg B
    have := abs_nonneg C
    omega
  have hCBN : 2*C+2*B ≤ (N : ℤ) := by
    have := le_abs_self B
    have := le_abs_self C
    omega
  have hNsq : (N : ℤ) ≤ (N : ℤ)^2 := Int.le_self_sq _
  refine ⟨N,?_⟩
  intro z hz w hw
  have hzB : z.norm ≤ B := hB ⟨z,hz,rfl⟩
  have hzN : z.norm ≤ (N : ℤ)^2 := hzB.trans (hBN.trans hNsq)
  have hwN : w.norm ≤ (N : ℤ)^2 := by
    have hh := norm_le_twice_norm_sub_add z w
    have hs := hw.2.2.2
    omega
  apply hS z hz w
  exact ⟨(candidate_iff_prime_of_norm_le hzN).mp hw.1,
    (candidate_iff_prime_of_norm_le hwN).mp hw.2.1,hw.2.2⟩

/-- Exact cutoff criterion for any fixed seed and step bound. It does not
require every component of the cutoff graph to be finite. -/
theorem component_finite_iff_cutoff (C : ℤ) (z : GaussianInt) :
    {w | (primeGraph C).Reachable z w}.Finite ↔
      ∃ N : ℕ, {w | (candidateGraph C N).Reachable z w}.Finite := by
  classical
  constructor
  · intro hf
    let S := hf.toFinset
    have hz : z ∈ S := by simp [S]
    have hS : ∀ u ∈ S, ∀ w, (primeGraph C).Adj u w → w ∈ S := by
      intro u hu w huw
      have hu' : (primeGraph C).Reachable z u := by simpa [S] using hu
      simpa [S] using hu'.trans huw.reachable
    obtain ⟨N,hN⟩ := cutoff_of_finite_prime_barrier C S hS
    refine ⟨N,S.finite_toSet.subset ?_⟩
    have hwalk : ∀ {a b : GaussianInt}, (candidateGraph C N).Walk a b →
        a ∈ S → b ∈ S := by
      intro a b p
      induction p with
      | nil => exact id
      | cons hab p ih => exact fun ha => ih (hN _ ha _ hab)
    intro w hw
    exact hw.elim fun p => hwalk p hz
  · rintro ⟨N,hN⟩
    exact hN.subset (fun w hw => hw.mono (primeGraph_le C N))

theorem component_infinite_iff_all_cutoffs (C : ℤ) (z : GaussianInt) :
    {w | (primeGraph C).Reachable z w}.Infinite ↔
      ∀ N : ℕ, {w | (candidateGraph C N).Reachable z w}.Infinite := by
  simpa only [Set.Infinite,not_exists] using not_congr (component_finite_iff_cutoff C z)

/-- This all-bounds cutoff condition is equivalent to the precise negation of
the original conjecture, unlike uniform trapping by the unmodified sieve. -/
theorem negation_iff_seed_cutoffs :
    (¬ ∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) ↔
    ∀ C : ℤ, ∃ N : ℕ,
      {w | (candidateGraph C N).Reachable (3 : GaussianInt) w}.Finite := by
  rw [gaussian_moat_fixed_seed_equivalence]
  simp only [not_exists,Set.not_infinite]
  exact forall_congr' (fun C => component_finite_iff_cutoff C 3)

theorem conjecture_iff_seed_cutoffs :
    (∃ (x : ℕ → GaussianInt) (C : ℤ), Function.Injective x ∧
      ∀ n, Prime (x n) ∧ (x (n+1)-x n).norm < C) ↔
    ∃ C : ℤ, ∀ N : ℕ,
      {w | (candidateGraph C N).Reachable (3 : GaussianInt) w}.Infinite := by
  rw [gaussian_moat_fixed_seed_equivalence]
  exact exists_congr (fun C => component_infinite_iff_all_cutoffs C 3)

#print axioms candidate_diff_finite
#print axioms component_finite_iff_cutoff
#print axioms negation_iff_seed_cutoffs
#print axioms conjecture_iff_seed_cutoffs

end ExceptionSieveReduction
end Erdos952Investigation
