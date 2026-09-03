import Submission.EssentialCoverProbability

/-!
Exact fibers of the interval-cover event under insertion of one modulus.
The concentration term in the final identity is not bounded here by an
unproved tail estimate; these identities do not settle Erdős 970.
-/
namespace Erdos970.CoverFibers
open Finset
open Erdos970.GapAverages

/-- Residues whose class contains every member of `U`. -/
def completingResidues (U : Finset ℕ) (p : ℕ) : Finset (Fin p) :=
  univ.filter (fun a => ∀ x ∈ U, x % p = a.val)

/-- A nonempty set occupying just one residue class. -/
def Concentrated (U : Finset ℕ) (p : ℕ) : Prop :=
  U.Nonempty ∧ ∀ x ∈ U, ∀ y ∈ U, x % p = y % p

instance (U : Finset ℕ) (p : ℕ) : Decidable (Concentrated U p) :=
  inferInstanceAs (Decidable (U.Nonempty ∧ ∀ x ∈ U, ∀ y ∈ U, x % p = y % p))

lemma completingResidues_empty (p : ℕ) : completingResidues ∅ p = univ := by
  simp [completingResidues]

lemma completingResidues_singleton (U : Finset ℕ) (p : ℕ) (hp : 0 < p)
    (h : Concentrated U p) {x : ℕ} (hx : x ∈ U) :
    completingResidues U p = {⟨x % p, Nat.mod_lt _ hp⟩} := by
  ext a
  simp only [completingResidues, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro ha
    apply Fin.ext
    exact (ha x hx).symm
  · rintro rfl y hy
    exact h.2 y hy x hx

lemma completingResidues_eq_empty (U : Finset ℕ) (p : ℕ)
    (hU : U.Nonempty) (h : ¬Concentrated U p) : completingResidues U p = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hh := (mem_filter.mp ha).2
  exact h ⟨hU, fun x hx y hy => (hh x hx).trans (hh y hy).symm⟩

/-- Every fiber has size zero, one, or the whole modulus. -/
theorem completingResidues_card (U : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    (completingResidues U p).card =
      if U = ∅ then p else if Concentrated U p then 1 else 0 := by
  by_cases hU : U = ∅
  · simp [hU, completingResidues_empty]
  · have hne := nonempty_iff_ne_empty.mpr hU
    by_cases h : Concentrated U p
    · obtain ⟨x, hx⟩ := hne
      rw [completingResidues_singleton U p hp h hx]
      simp [hU, h]
    · rw [completingResidues_eq_empty U p hne h]
      simp [hU, h]

/-- Pointwise exact probability, including the already-covered case. -/
theorem completingResidues_mean (U : Finset ℕ) (p : ℕ) (hp : 0 < p) :
    (∑ a : Fin p, if ∀ x ∈ U, x % p = a.val then (1 : ℝ) else 0) / p =
      (if U = ∅ then 1 else 0) + (if Concentrated U p then 1 else 0) / p := by
  have hc : (∑ a : Fin p, if ∀ x ∈ U, x % p = a.val then (1 : ℝ) else 0) =
      ((completingResidues U p).card : ℝ) := by rw [sum_boole]; rfl
  rw [hc, completingResidues_card U p hp]
  by_cases hU : U = ∅
  · simp [hU, Concentrated, ne_of_gt hp]
  · simp only [hU, if_false]
    split_ifs <;> norm_num

/-- The old survivors, before the extra residue is chosen. -/
noncomputable def phaseSurvivors (P : Finset ℕ) (m : ℕ) (r : Phase P) : Finset ℕ :=
  (range m).filter (fun x => ∀ q : P, x % q.val ≠ (r q).val)

lemma phaseSurvivors_empty_iff (P : Finset ℕ) (m : ℕ) (r : Phase P) :
    phaseSurvivors P m r = ∅ ↔ intervalCount P m r = 0 := by
  classical
  rw [eq_empty_iff_forall_notMem]
  simp only [phaseSurvivors, mem_filter, mem_range, not_and, not_forall, not_not]
  constructor
  · exact count_zero_of_cover P m r
  · exact cover_of_count_zero P m r

/-- Insert one coordinate, retaining the old normalized residues. -/
def extendPhase (P : Finset ℕ) (p : ℕ) (r : Phase P) (a : Fin p) : Phase (insert p P) :=
  fun q => if h : q.val = p then h.symm ▸ a
    else r ⟨q.val, (mem_insert.mp q.property).resolve_left h⟩

lemma extendPhase_new (P : Finset ℕ) (p : ℕ) (r : Phase P) (a : Fin p) :
    extendPhase P p r a ⟨p, mem_insert_self _ _⟩ = a := by
  simp [extendPhase]

lemma extendPhase_old (P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (r : Phase P) (a : Fin p) (q : P) :
    extendPhase P p r a ⟨q.val, mem_insert_of_mem q.property⟩ = r q := by
  have hqp : q.val ≠ p := by rintro he; exact hp (he ▸ q.property)
  simp [extendPhase, hqp]

/-- Covering after insertion is exactly containment of the old survivors in
one selected residue class. -/
theorem inserted_cover_iff (P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (m : ℕ) (r : Phase P) (a : Fin p) :
    intervalCount (insert p P) m (extendPhase P p r a) = 0 ↔
      ∀ x ∈ phaseSurvivors P m r, x % p = a.val := by
  classical
  constructor
  · intro hc x hx
    obtain ⟨hxm, hxo⟩ := mem_filter.mp hx
    obtain ⟨q, hq⟩ := cover_of_count_zero (insert p P) m _ hc x (mem_range.mp hxm)
    by_cases hqp : q.val = p
    · have he : q = ⟨p, mem_insert_self _ _⟩ := Subtype.ext hqp
      cases he
      simpa only [extendPhase_new] using hq
    · have hqP := (mem_insert.mp q.property).resolve_left hqp
      have he : extendPhase P p r a q = r ⟨q.val, hqP⟩ := by simp [extendPhase, hqp]
      rw [he] at hq
      exact (hxo ⟨q.val, hqP⟩ hq).elim
  · intro hc
    apply count_zero_of_cover
    intro x hx
    by_cases hs : x ∈ phaseSurvivors P m r
    · exact ⟨⟨p, mem_insert_self _ _⟩, by simpa only [extendPhase_new] using hc x hs⟩
    · have ho : ∃ q : P, x % q.val = (r q).val := by
        simpa only [phaseSurvivors, mem_filter, mem_range, hx, true_and, not_forall,
          not_not] using hs
      obtain ⟨q, hq⟩ := ho
      exact ⟨⟨q.val, mem_insert_of_mem q.property⟩, by
        simpa only [extendPhase_old P p hp] using hq⟩

/-- The normalized fiber average for the genuine prime-avoidance process. -/
theorem inserted_cover_fiber_mean (P : Finset ℕ) (p : ℕ) (hp0 : 0 < p)
    (hp : p ∉ P) (m : ℕ) (r : Phase P) :
    (∑ a : Fin p, if intervalCount (insert p P) m (extendPhase P p r a) = 0
      then (1 : ℝ) else 0) / p =
      (if intervalCount P m r = 0 then 1 else 0) +
        (if Concentrated (phaseSurvivors P m r) p then 1 else 0) / p := by
  classical
  simp_rw [inserted_cover_iff P p hp]
  rw [completingResidues_mean _ p hp0]
  simp only [phaseSurvivors_empty_iff]

/-- A genuine bijection of normalized phase spaces. -/
def insertPhaseEquiv (P : Finset ℕ) (p : ℕ) (hp : p ∉ P) :
    (Phase P × Fin p) ≃ Phase (insert p P) where
  toFun v := extendPhase P p v.1 v.2
  invFun r := (fun q => r ⟨q.val, mem_insert_of_mem q.property⟩,
    r ⟨p, mem_insert_self _ _⟩)
  left_inv v := by
    rcases v with ⟨r, a⟩
    apply Prod.ext
    · funext q
      exact extendPhase_old P p hp r a q
    · exact extendPhase_new P p r a
  right_inv r := by
    funext q
    by_cases hq : q.val = p
    · have he : q = ⟨p, mem_insert_self _ _⟩ := Subtype.ext hq
      cases he
      simp [extendPhase_new]
    · simp [extendPhase, hq]

lemma phaseMean_insert (P : Finset ℕ) (p : ℕ) (hp : p ∉ P)
    (f : Phase (insert p P) → ℝ) :
    phaseMean (insert p P) f =
      phaseMean P (fun r => (∑ a : Fin p, f (extendPhase P p r a)) / p) := by
  have hs : (∑ v : Phase P × Fin p, f (extendPhase P p v.1 v.2)) =
      ∑ r : Phase (insert p P), f r := by
    apply Fintype.sum_equiv (insertPhaseEquiv P p hp)
    intro v
    rfl
  have hd : (∏ q : ↥(insert p P), (q.val : ℝ)) =
      (p : ℝ) * (∏ q : P, (q.val : ℝ)) := by
    calc
      _ = ∏ q ∈ insert p P, (q : ℝ) := prod_attach _ _
      _ = (p : ℝ) * (∏ q ∈ P, (q : ℝ)) := prod_insert hp
      _ = _ := congrArg ((p : ℝ) * ·) (prod_attach P (fun q => (q : ℝ))).symm
  unfold phaseMean
  rw [hd, ← hs, Fintype.sum_prod_type, ← sum_div]
  ring

/-- The probability that the old survivor set is nonempty and lies in one
class modulo the new prime. -/
noncomputable def concentratedFraction (P : Finset ℕ) (p m : ℕ) : ℝ :=
  phaseMean P (fun r => if Concentrated (phaseSurvivors P m r) p then 1 else 0)

/-- Exact insertion identity. No concentration estimate is implicit here. -/
theorem coveredFraction_insert (P : Finset ℕ) (p : ℕ) (hp0 : 0 < p)
    (hp : p ∉ P) (m : ℕ) :
    coveredFraction (insert p P) m =
      coveredFraction P m + concentratedFraction P p m / p := by
  classical
  rw [coveredFraction, phaseMean_insert P p hp]
  simp_rw [inserted_cover_fiber_mean P p hp0 hp]
  rw [phaseMean_add]
  unfold coveredFraction concentratedFraction phaseMean
  rw [← sum_div]
  ring

lemma concentratedFraction_nonneg (P : Finset ℕ) (p m : ℕ) :
    0 ≤ concentratedFraction P p m := by
  apply div_nonneg
  · exact sum_nonneg (fun r _ => by split_ifs <;> norm_num)
  · positivity

lemma concentratedFraction_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime) (p m : ℕ) :
    concentratedFraction P p m ≤ 1 - coveredFraction P m := by
  classical
  have he : (1 : ℝ) - coveredFraction P m =
      phaseMean P (fun r => 1 - if intervalCount P m r = 0 then 1 else 0) := by
    rw [phaseMean_sub, phaseMean_const P hP]
    rfl
  rw [he]
  apply phaseMean_mono
  intro r
  by_cases hc : Concentrated (phaseSurvivors P m r) p
  · have hn : intervalCount P m r ≠ 0 := by
      intro hz
      exact hc.1.ne_empty ((phaseSurvivors_empty_iff P m r).mpr hz)
    simp [hc, hn]
  · simp only [hc, if_false]
    split_ifs <;> norm_num

/-- A simple consequence of the identity; this weak estimate alone gives
no quadratic worst-case bound. -/
theorem coveredFraction_insert_le (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime)
    (p : ℕ) (hp0 : 0 < p) (hp : p ∉ P) (m : ℕ) :
    coveredFraction (insert p P) m ≤
      coveredFraction P m + (1 - coveredFraction P m) / p := by
  rw [coveredFraction_insert P p hp0 hp]
  exact add_le_add le_rfl (div_le_div_of_nonneg_right
    (concentratedFraction_le P hP p m) (Nat.cast_nonneg p))

#print axioms completingResidues_card
#print axioms inserted_cover_iff
#print axioms inserted_cover_fiber_mean
#print axioms coveredFraction_insert
#print axioms coveredFraction_insert_le
end Erdos970.CoverFibers
