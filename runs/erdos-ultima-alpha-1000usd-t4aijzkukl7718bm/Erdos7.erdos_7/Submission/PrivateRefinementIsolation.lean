import Submission.PrivateReplacement
import Submission.ExchangePrivateTransfer

/-!
# Private refinements and isolated coarse residues

A finer modulus containing all private points permits a safe exchange when
that modulus is already used. In a label-minimal cover, its old coarse residue
must contain no other higher class: otherwise that whole class is absorbed
and can be deleted. These are necessary conditions, not a solution of Erdos 7.
-/

namespace Erdos7PrivateRefinementIsolation
open Erdos7PrivateReplacement
open Erdos7CompanionExchange (Hit)
open Erdos7ExchangePrivateTransfer (LabelMinimal private_of_label_minimal)
open scoped BigOperators

variable {I : Type*}

/-- Move the old upper class into the lower label and the protected private
points into the upper label. The covered union cannot decrease. This proof
also retains points originally covered by both changed classes. -/
theorem swap_private_union [DecidableEq I] (m : I → ℕ) (a : I → ℤ)
    (i j : I) (hji : j ≠ i) (hdiv : m i ∣ m j) (b : ℤ)
    (hp : ∀ x, Private m a i x → (m j : ℤ) ∣ x-b) :
    ∀ x : ℤ, (∃ k, (m k : ℤ) ∣ x-a k) →
      ∃ k, (m k : ℤ) ∣ x-Function.update (Function.update a i (a j)) j b k := by
  classical
  intro x hx
  by_cases hu : (m j : ℤ) ∣ x-a j
  · refine ⟨i, ?_⟩
    simpa [Ne.symm hji] using (Int.natCast_dvd_natCast.mpr hdiv).trans hu
  · by_cases ho : ∃ k, k ≠ i ∧ k ≠ j ∧ (m k : ℤ) ∣ x-a k
    · obtain ⟨k,hki,hkj,hk⟩ := ho
      exact ⟨k,by simpa [hki,hkj] using hk⟩
    · have hi : (m i : ℤ) ∣ x-a i := by
        obtain ⟨k,hk⟩ := hx
        by_cases hki : k=i
        · simpa only [hki] using hk
        · by_cases hkj : k=j
          · exact False.elim (hu (by simpa only [hkj] using hk))
          · exact False.elim (ho ⟨k,hki,hkj,hk⟩)
      have hpriv : Private m a i x := by
        refine ⟨hi,?_⟩
        intro k hki hk
        by_cases hkj : k=j
        · exact hu (by simpa only [hkj] using hk)
        · exact ho ⟨k,hki,hkj,hk⟩
      exact ⟨j,by simpa using hp x hpriv⟩

/-- A safe refinement into an already used larger modulus forces that upper
label to be isolated among ALL higher labels in its coarse residue. -/
theorem refinement_forces_isolation [DecidableEq I]
    (m : I → ℕ) (a : I → ℤ) (hminimal : LabelMinimal m)
    (hcover : ∀ x : ℤ, ∃ k, (m k : ℤ) ∣ x-a k)
    (i j : I) (hji : j ≠ i) (hdiv : m i ∣ m j) (b : ℤ)
    (hp : ∀ x, Private m a i x → (m j : ℤ) ∣ x-b) :
    ∀ k, k ≠ i → k ≠ j → m i ∣ m k → ¬ (m i : ℤ) ∣ a k-a j := by
  intro k hki hkj hd hk
  let c := Function.update (Function.update a i (a j)) j b
  have hc : ∀ x : ℤ, ∃ l, Hit (m l) (c l) x := by
    intro x
    exact swap_private_union m a i j hji hdiv b hp x (hcover x)
  obtain ⟨x,hx,hother⟩ := private_of_label_minimal m hminimal c hc k
  have hxk : (m k : ℤ) ∣ x-a k := by simpa [Hit,c,hki,hkj] using hx
  have hxi : (m i : ℤ) ∣ x-a j := by
    simpa only [sub_add_sub_cancel] using
      dvd_add ((Int.natCast_dvd_natCast.mpr hd).trans hxk) hk
  apply hother i (Ne.symm hki)
  simpa [Hit,c,Ne.symm hji] using hxi

/-- A coarse collision gives an escape from every proposed fine residue.
This conclusion genuinely uses full coverage and label minimality. -/
theorem private_escape_of_coarse_collision [DecidableEq I]
    (m : I → ℕ) (a : I → ℤ) (hminimal : LabelMinimal m)
    (hcover : ∀ x : ℤ, ∃ l, (m l : ℤ) ∣ x-a l)
    (i j k : I) (hji : j ≠ i) (hki : k ≠ i) (hkj : k ≠ j)
    (hj : m i ∣ m j) (hk : m i ∣ m k)
    (halign : (m i : ℤ) ∣ a k-a j) (b : ℤ) :
    ∃ x : ℤ, Private m a i x ∧ ¬ (m j : ℤ) ∣ x-b := by
  classical
  by_contra h
  have hp : ∀ x, Private m a i x → (m j : ℤ) ∣ x-b := by
    intro x hx
    by_contra hn
    exact h ⟨x,hx,hn⟩
  exact refinement_forces_isolation m a hminimal hcover i j hji hj b hp
    k hki hkj hk halign

/-- The available refinement labels have distinct coarse residues, all
avoiding the original lower residue. Hence there are at most `m i - 1` of
them. The bound does not claim that any such label must exist. -/
theorem refinement_targets_card [DecidableEq I]
    (m : I → ℕ) (a : I → ℤ) (hminimal : LabelMinimal m)
    (hcover : ∀ x : ℤ, ∃ l, (m l : ℤ) ∣ x-a l)
    (i : I) (hmi : 0 < m i) (S : Finset I)
    (hS : ∀ j ∈ S, j ≠ i ∧ m i ∣ m j ∧
      ∃ b : ℤ, ∀ x, Private m a i x → (m j : ℤ) ∣ x-b) :
    S.card ≤ m i-1 := by
  classical
  letI : NeZero (m i) := ⟨Nat.ne_of_gt hmi⟩
  let f (j : I) : ZMod (m i) := (a j : ZMod (m i))
  have havoid (j : I) (hj : j ∈ S) : f j ≠ f i := by
    intro heq
    have hd : (m i : ℤ) ∣ a j-a i :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub (a i) (a j) (m i)).mp heq.symm
    obtain ⟨x,hx,ho⟩ := private_of_label_minimal m hminimal a hcover j
    apply ho i (Ne.symm (hS j hj).1)
    simpa only [Hit,sub_add_sub_cancel] using
      dvd_add ((Int.natCast_dvd_natCast.mpr (hS j hj).2.1).trans hx) hd
  have hinj : Set.InjOn f (S : Set I) := by
    intro j hj k hk heq
    by_contra hne
    obtain ⟨b,hb⟩ := (hS j hj).2.2
    have hiso := refinement_forces_isolation m a hminimal hcover i j
      (hS j hj).1 (hS j hj).2.1 b hb
    apply hiso k (hS k hk).1 (Ne.symm hne) (hS k hk).2.1
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub (a j) (a k) (m i)).mp heq
  have hh := Finset.card_le_card_of_injOn (t := Finset.univ.erase (f i)) f
    (fun j hj => by simpa using havoid j hj) hinj
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card] using hh

/-- Total modulus size is bounded at a fixed nonzero common period. -/
lemma sum_moduli_le [Fintype I] (N : ℕ) (hN : N ≠ 0)
    (m : I → ℕ) (hm : ∀ i, m i ∣ N) :
    (∑ i, m i) ≤ Fintype.card I * N := by
  calc
    (∑ i, m i) ≤ ∑ _i : I, N :=
      Finset.sum_le_sum fun i _ => Nat.le_of_dvd (Nat.pos_of_ne_zero hN) (hm i)
    _ = Fintype.card I * N := by simp

/-- At fixed period and class count a covering assignment with maximum total
modulus exists. Residues need not be bounded explicitly: the integer objective
is bounded, so minimization of its deficit suffices. -/
theorem exists_maximum_sum_cover [Fintype I]
    (N : ℕ) (hN : N ≠ 0) (m : I → ℕ) (a : I → ℤ)
    (hc : OddCover N m a) :
    ∃ (n : I → ℕ) (c : I → ℤ), OddCover N n c ∧
      (∑ i, m i) ≤ ∑ i, n i ∧
      ∀ (l : I → ℕ) (b : I → ℤ), OddCover N l b →
        (∑ i, l i) ≤ ∑ i, n i := by
  classical
  let B := Fintype.card I * N
  let P (s : ℕ) := ∃ (n : I → ℕ) (c : I → ℤ),
    OddCover N n c ∧ B-(∑ i, n i)=s
  have hex : ∃ s, P s := ⟨B-(∑ i, m i),m,a,hc,rfl⟩
  obtain ⟨n,c,hn,hs⟩ := Nat.find_spec hex
  have hmax (l : I → ℕ) (b : I → ℤ) (hl : OddCover N l b) :
      (∑ i, l i) ≤ ∑ i, n i := by
    have hh := Nat.find_min' hex (show P (B-(∑ i, l i)) from ⟨l,b,hl,rfl⟩)
    have hnB : (∑ i, n i) ≤ B := sum_moduli_le N hN n (fun i => (hn.2.1 i).2.2)
    have hlB : (∑ i, l i) ≤ B := sum_moduli_le N hN l (fun i => (hl.2.1 i).2.2)
    omega
  exact ⟨n,c,hn,hmax m a hc,hmax⟩

/-- Updating one label to a larger unused modulus increases the objective. -/
lemma sum_update_gt [Fintype I] [DecidableEq I] (m : I → ℕ)
    (i : I) (d : ℕ) (hd : m i < d) :
    (∑ j, m j) < ∑ j, Function.update m i d j := by
  have hh := sum_update_lt (Function.update m i d) i (m i) (by simpa using hd)
  simpa only [Function.update_idem, Function.update_eq_self] using hh

/-- In maximum-sum normal form, every missing larger odd divisor has a private
escape from every residue. This is the reverse-objective counterpart to the
previous minimum-sum private replacement condition. -/
theorem private_escape_of_maximum_sum [Fintype I]
    (N : ℕ) (m : I → ℕ) (a : I → ℤ) (hc : OddCover N m a)
    (hmax : ∀ (n : I → ℕ) (c : I → ℤ), OddCover N n c →
      (∑ j, n j) ≤ ∑ j, m j)
    (i : I) (d : ℕ) (hd : 1 < d ∧ Odd d ∧ d ∣ N)
    (hlt : m i < d) (hmissing : ∀ j, m j ≠ d) (b : ℤ) :
    ∃ x, Private m a i x ∧ ¬ (d : ℤ) ∣ x-b := by
  classical
  by_contra h
  have hp : ∀ x, Private m a i x → (d : ℤ) ∣ x-b := by
    intro x hx
    by_contra hn
    exact h ⟨x,hx,hn⟩
  have hnew := replace_private_cover N m a hc i d b hd hmissing hp
  have hle := hmax _ _ hnew
  have hlt' := sum_update_gt m i d hlt
  omega

/-- Consequently every strict private refinement is an existing label in
maximum-sum normal form. This alone does not give a contradiction. -/
theorem private_refinement_label_exists [Fintype I]
    (N : ℕ) (m : I → ℕ) (a : I → ℤ) (hc : OddCover N m a)
    (hmax : ∀ (n : I → ℕ) (c : I → ℤ), OddCover N n c →
      (∑ j, n j) ≤ ∑ j, m j)
    (i : I) (d : ℕ) (hd : 1 < d ∧ Odd d ∧ d ∣ N) (hlt : m i < d)
    (b : ℤ) (hp : ∀ x, Private m a i x → (d : ℤ) ∣ x-b) :
    ∃ j, m j = d := by
  classical
  by_contra hn
  have hm : ∀ j, m j ≠ d := by simpa only [not_exists] using hn
  obtain ⟨x,hx,hno⟩ := private_escape_of_maximum_sum N m a hc hmax i d hd hlt hm b
  exact hno (hp x hx)

section Control

abbrev controlM := Erdos7CompanionExchange.moduli
abbrev controlA := Erdos7CompanionExchange.residues

/-- The 3-class in the five-class EVEN control has its private points exactly
in residue3 modulo12 (only the needed containment is stated here). -/
lemma control_private_three (x : ℤ) (hx : Private controlM controlA 1 x) :
    (12 : ℤ) ∣ x-3 := by
  have h3 := hx.1
  have h2 := hx.2 0 (by decide)
  have h4 := hx.2 2 (by decide)
  change (3 : ℤ) ∣ x-0 at h3
  change ¬ (2 : ℤ) ∣ x-0 at h2
  change ¬ (4 : ℤ) ∣ x-1 at h4
  omega

def controlTargets : Finset (Fin 5) := {3,4}

lemma control_targets : ∀ j ∈ controlTargets,
    j ≠ (1 : Fin 5) ∧ controlM 1 ∣ controlM j ∧
      ∃ b : ℤ, ∀ x, Private controlM controlA 1 x → (controlM j : ℤ) ∣ x-b := by
  intro j hj
  simp only [controlTargets,Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · exact ⟨by decide,by decide,3,fun x hx =>
      (show (6 : ℤ) ∣ 12 by norm_num).trans (control_private_three x hx)⟩
  · exact ⟨by decide,by decide,3,control_private_three⟩

/-- Both possible non-original coarse residues supply refinement targets.
Thus the general bound is sharp even at an odd lower modulus. The ambient
cover has even moduli and is not a counterexample to the original conjecture. -/
lemma control_card_bound_sharp : controlTargets.card = controlM 1-1 ∧
    controlTargets.card ≤ controlM 1-1 := by
  refine ⟨by decide,?_⟩
  exact refinement_targets_card controlM controlA
    Erdos7ExchangePrivateTransfer.control_label_minimal
    Erdos7CompanionExchange.control_cover 1 (by decide) controlTargets control_targets

/-- Exchange 0 mod3 and 1 mod6 for 1 mod3 and 3 mod6. -/
def controlThreeSixA : Fin 5 → ℤ := ![0,1,1,3,11]

lemma control_three_six_update :
    Function.update (Function.update controlA 1 (controlA 3)) 3 3 =
      controlThreeSixA := by
  decide +kernel

/-- A genuine safe exchange with ODD lower modulus. It keeps the same five
modulus labels and covers every integer, not just a sampled interval. -/
theorem control_three_six_cover : ∀ x : ℤ, ∃ k,
    (controlM k : ℤ) ∣ x-controlThreeSixA k := by
  intro x
  have hp : ∀ y, Private controlM controlA 1 y → (controlM 3 : ℤ) ∣ y-3 := by
    intro y hy
    exact (show (6 : ℤ) ∣ 12 by norm_num).trans (control_private_three y hy)
  have hh := swap_private_union controlM controlA 1 3 (by decide) (by decide) 3
    hp x (Erdos7CompanionExchange.control_cover x)
  rwa [control_three_six_update] at hh

/-- Unlike the earlier 4,12 control, this safe exchange is not a common
translation, already on its two changed labels. Its upper modulus6 is EVEN. -/
theorem control_three_six_not_translation :
    ¬ ∃ c : ℤ, (3 : ℤ) ∣ c-1 ∧ (6 : ℤ) ∣ 1+c-3 := by
  simpa using Erdos7ExchangePrivateTransfer.odd_exchange_not_translation
    3 (by decide) 2 1 0 1 (by norm_num)

/-- The nontranslation control is nevertheless a common reflection. This
records a limitation of the example rather than hiding that extra symmetry. -/
lemma control_three_six_is_reflection : ∀ i : Fin 5,
    (controlM i : ℤ) ∣ (10-controlA i)-controlThreeSixA i := by
  decide +kernel

end Control

#print axioms swap_private_union
#print axioms refinement_forces_isolation
#print axioms private_escape_of_coarse_collision
#print axioms refinement_targets_card
#print axioms exists_maximum_sum_cover
#print axioms private_escape_of_maximum_sum
#print axioms private_refinement_label_exists
#print axioms control_card_bound_sharp
#print axioms control_three_six_cover
#print axioms control_three_six_not_translation
#print axioms control_three_six_is_reflection

end Erdos7PrivateRefinementIsolation
