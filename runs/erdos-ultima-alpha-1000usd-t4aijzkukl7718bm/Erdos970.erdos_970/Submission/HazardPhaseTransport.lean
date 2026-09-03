import Submission.GapHazardExample
import Submission.SoftEndpointLocal
import Submission.CompetingCoverVariance

/-! Transport the six-prime finite hazard example into the normalized phase
space used by the Laplace lemmas. The interval is reflected so the old left
endpoint becomes the next right endpoint. This is not a target disproof. -/
namespace Erdos970.GapAverages.HazardExample
open Finset

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def reflectedRaw (w : FullPhase) (p : ℕ) : ℕ :=
  if p = 3 ∨ p = 7 ∨ p = 11 then w.1.val+9
  else if p = 101 then 9+101-(w.2 0).val
  else if p = 103 then 9+103-(w.2 1).val
  else 9+107-(w.2 2).val

def reflectedPhase (w : FullPhase) : Phase primes :=
  fun p => ⟨reflectedRaw w p.val % p.val,
    Nat.mod_lt _ (primes_prime p.val p.property).pos⟩

lemma reflection_injective (p b c : ℕ) (hb : b < p) (hc : c < p)
    (he : (9+p-b)%p = (9+p-c)%p) : b = c := by
  have hh : 9+p-b ≡ 9+p-c [MOD p] := he
  have ha := hh.add_right b
  have hb' : (9+p-b)+b = 9+p := by omega
  rw [hb'] at ha
  have hc' : (9+p-c)+c = 9+p := by omega
  have ha' : (9+p-c)+c ≡ (9+p-c)+b [MOD p] := by simpa only [hc'] using ha
  exact ((Nat.ModEq.add_left_cancel' (9+p-c) ha').eq_of_lt_of_lt hc hb).symm

lemma core_residues_injective : ∀ a b : Fin 231,
    (a.val+9)%3 = (b.val+9)%3 → (a.val+9)%7 = (b.val+9)%7 →
    (a.val+9)%11 = (b.val+9)%11 → a = b := by
  decide +kernel

lemma reflectedPhase_injective : Function.Injective reflectedPhase := by
  intro w v he
  have h3 := congrArg (fun r : Phase primes => (r ⟨3, by decide⟩).val) he
  have h7 := congrArg (fun r : Phase primes => (r ⟨7, by decide⟩).val) he
  have h11 := congrArg (fun r : Phase primes => (r ⟨11, by decide⟩).val) he
  have h101 := congrArg (fun r : Phase primes => (r ⟨101, by decide⟩).val) he
  have h103 := congrArg (fun r : Phase primes => (r ⟨103, by decide⟩).val) he
  have h107 := congrArg (fun r : Phase primes => (r ⟨107, by decide⟩).val) he
  norm_num [reflectedPhase, reflectedRaw] at h3 h7 h11 h101 h103 h107
  apply Prod.ext
  · exact core_residues_injective w.1 v.1 h3 h7 h11
  · funext j
    apply Fin.ext
    fin_cases j
    · exact reflection_injective 101 _ _ (w.2 0).isLt (v.2 0).isLt h101
    · exact reflection_injective 103 _ _ (w.2 1).isLt (v.2 1).isLt h103
    · exact reflection_injective 107 _ _ (w.2 2).isLt (v.2 2).isLt h107

lemma normalized_phase_card : Fintype.card (Phase primes) = 257130951 := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [prod_coe_sort primes (fun p : ℕ => p)]
  norm_num [primes]

noncomputable def reflectedPhaseEquiv : FullPhase ≃ Phase primes :=
  Equiv.ofBijective reflectedPhase ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨reflectedPhase_injective, full_phase_card.trans normalized_phase_card.symm⟩)

lemma reflectedPhaseEquiv_apply (w : FullPhase) :
    reflectedPhaseEquiv w = reflectedPhase w := rfl

lemma reflected_tail_hit (p b x : ℕ) (hp : 9 < p) (hb : b < p) (hx : x ≤ 9) :
    x%p = (9+p-b)%p ↔ 9-x = b := by
  constructor
  · intro he
    have hh : x ≡ 9+p-b [MOD p] := he
    have ha := hh.add_right b
    have he' : (9+p-b)+b = 9+p := by omega
    rw [he'] at ha
    have hh9 : 9+p ≡ 9 [MOD p] := by simp [Nat.ModEq]
    have ha9 := ha.trans hh9
    have hn : 9 = x+(9-x) := by omega
    rw [hn] at ha9
    have hc := Nat.ModEq.add_left_cancel' x ha9
    exact (hc.eq_of_lt_of_lt hb (by omega)).symm
  · intro he
    have he' : 9+p-b = p+x := by omega
    simp [he']

lemma coprime_231_iff (a : ℕ) :
    a.Coprime 231 ↔ ¬3 ∣ a ∧ ¬7 ∣ a ∧ ¬11 ∣ a := by
  have he : 231 = 3*(7*11) := by decide
  rw [he, Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_right]
  have h3 : a.Coprime 3 ↔ ¬3 ∣ a :=
    Nat.coprime_comm.trans (by decide : Nat.Prime 3).coprime_iff_not_dvd
  have h7 : a.Coprime 7 ↔ ¬7 ∣ a :=
    Nat.coprime_comm.trans (by decide : Nat.Prime 7).coprime_iff_not_dvd
  have h11 : a.Coprime 11 ↔ ¬11 ∣ a :=
    Nat.coprime_comm.trans (by decide : Nat.Prime 11).coprime_iff_not_dvd
  rw [h3, h7, h11]

def Good (w : FullPhase) (y : ℕ) : Prop :=
  (w.1.val+y).Coprime 231 ∧ ∀ j : Fin 3, y ≠ (w.2 j).val

instance (w : FullPhase) (y : ℕ) : Decidable (Good w y) := by
  unfold Good; infer_instance

lemma point_reflection (w : FullPhase) (x : ℕ) (hx : x ≤ 9) :
    point primes x (reflectedPhase w) = if Good w (9-x) then 1 else 0 := by
  rw [CoverFibers.point_eq_avoidance_indicator]
  have hc (p : ℕ) : x%p = (w.1.val+9)%p ↔ p ∣ w.1.val+(9-x) := by
    have hh := Nat.modEq_iff_dvd' (show x ≤ w.1.val+9 by omega) (n := p)
    have he : w.1.val+9-x = w.1.val+(9-x) := by omega
    simpa only [Nat.ModEq, he] using hh
  have ht (j : Fin 3) : x%(tailPrime j) =
      (9+tailPrime j-(w.2 j).val)%(tailPrime j) ↔ 9-x = (w.2 j).val :=
    reflected_tail_hit _ _ _ (by have := tailPrime_gt j; omega) (w.2 j).isLt hx
  have hzero := ht 0
  have hone := ht 1
  have htwo := ht 2
  change x%101 = (9+101-(w.2 0).val)%101 ↔ 9-x = (w.2 0).val at hzero
  change x%103 = (9+103-(w.2 1).val)%103 ↔ 9-x = (w.2 1).val at hone
  change x%107 = (9+107-(w.2 2).val)%107 ↔ 9-x = (w.2 2).val at htwo
  norm_num only [Nat.reduceAdd] at hzero hone htwo
  have he : (∀ p : primes, x%p.val ≠ ((reflectedPhase w) p).val) ↔ Good w (9-x) := by
    simp only [Subtype.forall, reflectedPhase]
    simp [primes, reflectedRaw, Good, coprime_231_iff, hc, hzero, hone, htwo,
      Fin.forall_fin_succ, and_assoc]
  simp only [he]

lemma good_zero (w : FullPhase) : Good w 0 ↔ Endpoint w := by
  simp [Good, Endpoint, ne_comm]

lemma covers_iff_no_good (w : FullPhase) :
    Covers w ↔ ∀ i < 9, ¬Good w (i+1) := by
  classical
  simp only [Covers, oldPositions, mem_filter, mem_range, Good]
  constructor
  · intro h i hi hg
    obtain ⟨j, hj⟩ := h i ⟨hi, by simpa only [Nat.add_assoc] using hg.1⟩
    exact hg.2 j hj
  · intro h i hi
    have hn := h i hi.1
    have hc : (w.1.val+(i+1)).Coprime 231 := by simpa only [Nat.add_assoc] using hi.2
    by_contra hno
    push_neg at hno
    exact hn ⟨hc, hno⟩

lemma reflected_count (w : FullPhase) :
    intervalCount primes 9 (reflectedPhase w) =
      ∑ i ∈ range 9, if Good w (i+1) then (1 : ℝ) else 0 := by
  rw [intervalCount, ← sum_range_reflect (fun x => point primes x (reflectedPhase w)) 9]
  apply sum_congr rfl
  intro i hi
  have him := mem_range.mp hi
  rw [point_reflection w _ (by omega)]
  have he : 9-(9-1-i) = i+1 := by omega
  rw [he]

lemma reflected_count_zero (w : FullPhase) :
    intervalCount primes 9 (reflectedPhase w) = 0 ↔ Covers w := by
  rw [reflected_count, sum_boole, Nat.cast_eq_zero, card_eq_zero,
    filter_eq_empty_iff, covers_iff_no_good]
  simp only [mem_range]

lemma reflected_endpoint (w : FullPhase) :
    point primes 9 (reflectedPhase w) = if Endpoint w then 1 else 0 := by
  rw [point_reflection w 9 le_rfl]
  simp only [Nat.sub_self, good_zero]

#print axioms reflectedPhaseEquiv
#print axioms reflected_count_zero
#print axioms reflected_endpoint
end Erdos970.GapAverages.HazardExample
