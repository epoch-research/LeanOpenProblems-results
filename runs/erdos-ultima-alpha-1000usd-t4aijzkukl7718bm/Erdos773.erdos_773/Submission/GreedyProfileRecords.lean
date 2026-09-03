import Submission.GreedyTrackedMoments
import Submission.GreedyUniformHorizon

/-!
Concrete profile observables and their initialization in a regular
four-uniform hypergraph. Stored clocks are retained in every crossing event.
-/
namespace Erdos773.GreedyProfileRecords
open Finset GreedyHypergraphState GreedyTrackedState GreedyTrackedMoments
open GreedyTrajectoryCalculus GreedyScaledTrajectory GreedyEnvelopeCalculus
set_option maxHeartbeats 2500000
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]

structure Parameters where
  V : ℝ
  d : ℝ
  rho : ℝ
  K : ℝ

def time (p : Parameters) (n : ℕ) : ℝ := n*(p.d/p.V)
def profile (p : Parameters) (j : Fin 3) (t : ℝ) : ℝ := ![F2 p.d t,F3 p.d t,F4 p.d t] j
def envelope (p : Parameters) (j : Fin 3) (t : ℝ) : ℝ :=
  ![E2 p.d p.rho p.K t,E3 p.d p.rho p.K t,E4 p.d p.rho p.K t] j

def center (p : Parameters) (j : Fin 3) (n : ℕ) : ℝ := profile p j (time p n)
def width (p : Parameters) (j : Fin 3) (n : ℕ) : ℝ := envelope p j (time p n)
def sign (lower : Bool) : ℝ := if lower then -1 else 1
def signedProfile (p : Parameters) (j : Fin 3) (lower : Bool) (n : ℕ) : ℝ :=
  center p j n+sign lower*width p j n

@[simp] lemma time_zero (p : Parameters) : time p 0 = 0 := by simp [time]
lemma time_step (p : Parameters) (n : ℕ) : time p (n+1) = time p n+p.d/p.V := by
  simp only [time,Nat.cast_add,Nat.cast_one]
  ring
lemma time_nonneg {p : Parameters} (hd : 0 ≤ p.d) (hV : 0 ≤ p.V) (n : ℕ) : 0 ≤ time p n := by
  dsimp [time]
  positivity
lemma time_mono {p : Parameters} (hd : 0 ≤ p.d) (hV : 0 ≤ p.V) {n m : ℕ} (hnm : n ≤ m) :
    time p n ≤ time p m := by
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnm) (div_nonneg hd hV)

@[simp] lemma sign_abs (lower : Bool) : |sign lower| = 1 := by cases lower <;> norm_num [sign]
@[simp] lemma sign_sq (lower : Bool) : (sign lower)^2 = 1 := by cases lower <;> norm_num [sign]

lemma profile_nonneg {p : Parameters} (hd : 0 ≤ p.d) {t : ℝ} (ht : 0 ≤ t) (j : Fin 3) :
    0 ≤ profile p j t := by
  have hq := q_pos t
  fin_cases j <;> dsimp [profile,F2,F3,F4,a2,a3,a4] <;> positivity

lemma envelope_nonneg {p : Parameters} (hd : 0 ≤ p.d) (hρ : 0 ≤ p.rho) (j : Fin 3) (t : ℝ) :
    0 ≤ envelope p j t := by
  have h0 := growth_pos p.K 0 t
  have h1 := growth_pos p.K 1 t
  have h2 := growth_pos p.K 2 t
  fin_cases j <;> dsimp [envelope,E2,E3,E4] <;> positivity

lemma width_pos {p : Parameters} (hd : 0 < p.d) (hρ : 0 < p.rho) (j : Fin 3) (n : ℕ) :
    0 < width p j n := by
  have h0 := growth_pos p.K 0 (time p n)
  have h1 := growth_pos p.K 1 (time p n)
  have h2 := growth_pos p.K 2 (time p n)
  fin_cases j <;> dsimp [width,envelope,E2,E3,E4] <;> positivity

lemma available_empty {H : Finset (Finset α)} (hH : ∀ e ∈ H, 2 ≤ e.card) :
    available H ∅ = univ := by
  apply eq_univ_of_forall
  intro u
  apply mem_available.mpr
  refine ⟨by simp,?_⟩
  intro e he hesub
  have hc := card_le_card hesub
  simp only [insert_empty_eq,card_singleton] at hc
  have hh := hH e he
  omega

lemma initial_incident {H : Finset (Finset α)} {r : ℕ} (hr : 2 ≤ r)
    (hH : ∀ e ∈ H, e.card = r) (u : α) : incident H ∅ r u = H.filter (fun e => u ∈ e) := by
  have hA := available_empty (fun e he => by rw [hH e he]; exact hr)
  ext e
  simp only [mem_incident,sdiff_empty,hA,subset_univ,mem_filter,true_and]
  constructor
  · rintro ⟨he,hcard,hu⟩
    exact ⟨he,hu⟩
  · rintro ⟨he,hu⟩
    exact ⟨he,hH e he,hu⟩

lemma initial_incident_other {H : Finset (Finset α)} {r j : ℕ}
    (hH : ∀ e ∈ H, e.card = r) (hj : j ≠ r) (u : α) : incident H ∅ j u = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hs,hcard,hu⟩ := mem_incident.mp he
  simp only [sdiff_empty,hH e he] at hcard
  exact hj hcard.symm

/-- All initial recorded degrees equal the proposed centers, with no
    approximation. The original regular degree is exactly d^3. -/
theorem initial_center {H : Finset (Finset α)} (hH : ∀ e ∈ H, e.card = 4)
    (p : Parameters) (hD : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = p.d^3)
    (T : ℕ) (j : Fin 3) (u : α) : degree (initial H T) j u = center p j 0 := by
  have h2 := initial_incident_other hH (by omega : 2 ≠ 4) u
  have h3 := initial_incident_other hH (by omega : 3 ≠ 4) u
  have h4 := initial_incident (by omega : 2 ≤ 4) hH u
  have hd := hD u
  fin_cases j <;> simp [degree,initial,boundedDegree,center,profile,time,F2,F3,F4,
    a2,a3,a4,q,h2,h3,h4,HypergraphDegreeTrim.degree] at *
  exact hd

/-- Both signed errors start at minus their positive initial width. -/
theorem initial_signed_error {H : Finset (Finset α)} (hH : ∀ e ∈ H, e.card = 4)
    (p : Parameters) (hD : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = p.d^3)
    (T : ℕ) (j : Fin 3) (u : α) (lower : Bool) :
    sign lower*error (signedProfile p j lower) (initial H T) j u = -width p j 0 := by
  have hc := initial_center hH p hD T j u
  have he : error (signedProfile p j lower) (initial H T) j u =
      center p j 0-(center p j 0+sign lower*width p j 0) := by
    change degree (initial H T) j u-_ = _
    rw [hc]
    rfl
  rw [he]
  cases lower <;> simp [sign]

/-- The actual crossing event of the centered signed recorded error. -/
def crossing (p : Parameters) (H : Finset (Finset α)) (T : ℕ)
    (j : Fin 3) (u : α) (lower : Bool) (_n : ℕ) (s : Tracked H T) : Prop :=
  width p j 0 ≤ sign lower*(error (signedProfile p j lower) s j u-
    error (signedProfile p j lower) (initial H T) j u)

lemma crossing_iff {H : Finset (Finset α)} (hH : ∀ e ∈ H, e.card = 4)
    (p : Parameters) (hD : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = p.d^3)
    (T : ℕ) (j : Fin 3) (u : α) (lower : Bool) (n : ℕ) (s : Tracked H T) :
    crossing p H T j u lower n s ↔
      width p j (s.clock u).val ≤ sign lower*(degree s j u-center p j (s.clock u).val) := by
  have hi := initial_signed_error hH p hD T j u lower
  unfold crossing
  rw [mul_sub,hi]
  unfold error signedProfile
  cases lower <;> simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul]
    <;> constructor <;> intro h <;> linarith only [h]

/-- Avoiding the two signed events gives a strict tube at the stored clock,
    including at vertices whose records have frozen. -/
theorem tube_of_no_crossing {H : Finset (Finset α)} (hH : ∀ e ∈ H, e.card = 4)
    (p : Parameters) (hD : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = p.d^3)
    (T : ℕ) (j : Fin 3) (u : α) (n : ℕ) (s : Tracked H T)
    (hg : ∀ lower : Bool, ¬crossing p H T j u lower n s) :
    |degree s j u-center p j (s.clock u).val| < width p j (s.clock u).val := by
  have hupper := hg false
  have hlower := hg true
  rw [crossing_iff hH p hD T j u false n s] at hupper
  rw [crossing_iff hH p hD T j u true n s] at hlower
  simp only [sign,Bool.false_eq_true,if_false,if_true,one_mul,neg_one_mul,not_le] at hupper hlower
  apply abs_lt.mpr
  constructor <;> linarith only [hupper,hlower]

/-- The stored-clock tube is a current-time actual-degree bound on each
    running available vertex when Ready. -/
theorem live_tube {H : Finset (Finset α)} (hH : ∀ e ∈ H, e.card = 4)
    (p : Parameters) (hD : ∀ u : α, (HypergraphDegreeTrim.degree H u:ℝ) = p.d^3)
    {L T n : ℕ} {s : Tracked H T} (hs : Valid H L n s) (hrun : s.running = true)
    (hr : StoppedGreedyMoments.Ready H L s.chosen) (j : Fin 3) (u : α)
    (hu : u ∈ available H s.chosen) (hg : ∀ lower : Bool, ¬crossing p H T j u lower n s) :
    |((incident H s.chosen (j.val+2) u).card:ℝ)-center p j n| ≤ width p j n := by
  have hh := (tube_of_no_crossing hH p hD T j u n s hg).le
  unfold degree at hh
  rw [hs.1 hrun u hu j,hs.2.2 hrun hr u hu] at hh
  exact hh

#print axioms available_empty
#print axioms initial_center
#print axioms initial_signed_error
#print axioms crossing_iff
#print axioms tube_of_no_crossing
#print axioms live_tube
end
end Erdos773.GreedyProfileRecords
