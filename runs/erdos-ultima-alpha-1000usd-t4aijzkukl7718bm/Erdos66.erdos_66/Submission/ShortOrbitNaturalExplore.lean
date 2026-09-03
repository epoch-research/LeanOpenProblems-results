import Submission.ShortOrbitCarryExplore

/-! Both carry terms for a deterministic phased antitone-row construction.
The result is conditional on one orbit discrepancy bound and does not
assert changing-modulus compatibility. -/
namespace Erdos66ShortOrbitNatural
open Erdos66OriginRepair Erdos66AntitonePairIntervals Erdos66ShortOrbitCarry
  Erdos66IntegerBlock Erdos66TranslatedPrefixPalette
open AdditiveCombinatorics
open scoped Classical
set_option maxHeartbeats 1800000

variable (M : ℕ) [NeZero M]

lemma phased_pairCount (C D : ℕ → Finset (ZMod M)) (b : ZMod M)
    (q k : ℕ) (hk : k ≤ q) (t : ZMod M) :
    pairCount (phasedRows M C b k) (phasedRows M D b (q-k)) t =
      pairCount (C k) (D (q-k)) (t-b*q) := by
  change Erdos66OuterCarryProfile.cyclicCount M (shift M (C k) (b*(k : ZMod M)))
    (shift M (D (q-k)) (b*(q-k : ℕ))) t = _
  rw [shift_cyclicCount]
  have he : t-b*k-b*(q-k : ℕ) = t-b*q := by rw [Nat.cast_sub hk]; ring
  rw [he]
  rfl

lemma upper_short_orbit_error (C D : ℕ → Finset (ZMod M))
    (hC : Antitone C) (hD : Antitone D) (b : ZMod M) (q t : ℕ) (E : ℝ)
    (hE : 0 ≤ E) (hOrbit : IntervalBound M b (q+1) t E) :
    |(∑ k ∈ Finset.range (q+1),
        (upper M (phasedRows M C b k) (phasedRows M D b (q-k)) t : ℝ)) -
      (1-((t+1 : ℕ) : ℝ)/M) *
        (∑ k ∈ Finset.range (q+1),
          (pairCount (C k) (D (q-k)) ((t : ZMod M)-b*q) : ℝ))| ≤
      E*((pairCount (C 0) (D (q/2)) ((t : ZMod M)-b*q) : ℝ) +
        pairCount (C (q/2)) (D 0) ((t : ZMod M)-b*q)) := by
  have hl := lower_short_orbit_error M C D hC hD b q t E hE hOrbit
  have he : (∑ k ∈ Finset.range (q+1),
        (upper M (phasedRows M C b k) (phasedRows M D b (q-k)) t : ℝ)) +
      (∑ k ∈ Finset.range (q+1),
        (lower M (phasedRows M C b k) (phasedRows M D b (q-k)) t : ℝ)) =
      ∑ k ∈ Finset.range (q+1),
        (pairCount (C k) (D (q-k)) ((t : ZMod M)-b*q) : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hh := lower_add_upper M (phasedRows M C b k) (phasedRows M D b (q-k)) t
    change _ = pairCount _ _ (t : ZMod M) at hh
    rw [phased_pairCount M C D b q k (by simpa using Finset.mem_range.mp hk)] at hh
    exact_mod_cast (show upper M (phasedRows M C b k) (phasedRows M D b (q-k)) t +
      lower M (phasedRows M C b k) (phasedRows M D b (q-k)) t = _ by omega)
  rw [abs_le] at hl ⊢
  constructor <;> nlinarith

omit [NeZero M] in
lemma intervalBound_mono (b : ZMod M) (Q R t : ℕ) (E : ℝ) (hRQ : R ≤ Q)
    (h : IntervalBound M b Q t E) : IntervalBound M b R t E := by
  intro a l u hlu hu
  exact h a l u hlu (hu.trans hRQ)

noncomputable def phaseMass (C : ℕ → Finset (ZMod M)) (b : ZMod M)
    (q t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (q+1), (pairCount (C k) (C (q-k)) ((t : ZMod M)-b*q) : ℝ)

noncomputable def halfMass (C : ℕ → Finset (ZMod M)) (b : ZMod M)
    (q t : ℕ) : ℝ := pairCount (C 0) (C (q/2)) ((t : ZMod M)-b*q)

/-- One deterministic phase b works at every target for which its stated
short-orbit discrepancy bound holds. No phase is selected separately for n. -/
theorem natural_short_orbit_error (C : ℕ → Finset (ZMod M)) (hC : Antitone C)
    (b : ZMod M) (q t : ℕ) (hq : 0 < q) (ht : t < M) (E : ℝ) (hE : 0 ≤ E)
    (hOrbit : IntervalBound M b (q+1) t E) :
    |(sumRep (blockSet M (phasedRows M C b)) (q*M+t) : ℝ) -
      (((t+1 : ℕ) : ℝ)/M * phaseMass M C b q t +
        (1-((t+1 : ℕ) : ℝ)/M) * phaseMass M C b (q-1) t)| ≤
      2*E*(halfMass M C b q t + halfMass M C b (q-1) t) := by
  have hl := lower_short_orbit_error M C C hC hC b q t E hE hOrbit
  have hu := upper_short_orbit_error M C C hC hC b (q-1) t E hE
    (intervalBound_mono M b (q+1) ((q-1)+1) t E (by omega) hOrbit)
  simp only [pairCount_comm (C (q/2)) (C 0)] at hl
  simp only [pairCount_comm (C ((q-1)/2)) (C 0)] at hu
  have hdup (x : ℝ) : E*(x+x)=2*E*x := by ring
  simp_rw [hdup] at hl hu
  rw [block_formula M (phasedRows M C b) q t ht]
  push_cast
  have hqe : q-1+1=q := by omega
  change |(∑ k ∈ Finset.range (q+1),
      (lower M (phasedRows M C b k) (phasedRows M C b (q-k)) t : ℝ)) -
      (((t+1 : ℕ) : ℝ)/M)*phaseMass M C b q t| ≤ 2*E*halfMass M C b q t at hl
  change |(∑ k ∈ Finset.range (q-1+1),
      (upper M (phasedRows M C b k) (phasedRows M C b ((q-1)-k)) t : ℝ)) -
      (1-((t+1 : ℕ) : ℝ)/M)*phaseMass M C b (q-1) t| ≤
        2*E*halfMass M C b (q-1) t at hu
  simp only [hqe,show ∀ k : ℕ, q-1-k=q-k-1 by omega] at hu
  have hh := abs_add_le
    ((∑ k ∈ Finset.range (q+1),
      (lower M (phasedRows M C b k) (phasedRows M C b (q-k)) t : ℝ)) -
      (((t+1 : ℕ) : ℝ)/M)*phaseMass M C b q t)
    ((∑ k ∈ Finset.range q,
      (upper M (phasedRows M C b k) (phasedRows M C b (q-k-1)) t : ℝ)) -
      (1-((t+1 : ℕ) : ℝ)/M)*phaseMass M C b (q-1) t)
  have hid : ∀ x y u v : ℝ, x+y-(u+v)=(x-u)+(y-v) := by intros; ring
  rw [hid]
  push_cast at hl hu hh
  nlinarith

end Erdos66ShortOrbitNatural
