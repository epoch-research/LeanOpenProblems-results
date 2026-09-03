import Submission.DoubledPetersenCircuits

/-!
An even, fractionally realizable Petersen edge-demand vector which is not
an integer sum of ordinary (binary) cycle vectors. This is an obstruction
to an independent floor-rounding repair, NOT to Erdős 184.
-/
open scoped BigOperators
namespace Erdos184.PetersenDemandHole
open DoubledPetersenCertificate
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

abbrev E := Fin 15
abbrev I := Fin 57

def matching : Finset E := {2,4,6,8,9}
def demand (e : E) : ℕ := if e ∈ matching then 2 else 1
def col (i : I) (e : E) : ℕ := digit (asType i) e
def length (i : I) : ℕ := ∑ e, col i e
def matched (i : I) : ℕ := ∑ e ∈ matching, col i e
def alternating : Finset I := {14,23,36,40,48}

lemma demand_even : EvenVector demand := by unfold EvenVector; decide
lemma demand_total : ∑ e, demand e = 20 := by decide
lemma demand_matched : ∑ e ∈ matching, demand e = 10 := by decide
lemma matching_bound (i : I) : 2 * matched i ≤ length i := by revert i; decide
lemma equality_length (i : I) : length i = 2 * matched i → length i = 8 := by
  revert i; decide
lemma alternating_cover (e : E) : ∑ i ∈ alternating, col i e = 2 * demand e := by
  revert e; decide
lemma alternating_card : alternating.card = 5 := by decide

lemma fractional_cover (e : E) :
    ∑ i ∈ alternating, (1 / 2 : ℚ) * (col i e : ℚ) = demand e := by
  rw [← Finset.mul_sum]
  have hh := alternating_cover e
  have hr : (∑ i ∈ alternating, (col i e : ℚ)) = 2 * (demand e : ℚ) := by
    exact_mod_cast hh
  rw [hr]
  ring

/-- No choice of natural multiplicities of ANY of the 57 ordinary Petersen
cycles realizes the even demand vector, despite its exact fractional cover. -/
lemma no_integral_cover (k : I → ℕ) :
    ¬ (∀ e : E, ∑ i, k i * col i e = demand e) := by
  intro hk
  have ht : ∑ i, k i * length i = 20 := by
    simp_rw [length, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hk]
    exact demand_total
  have hm : ∑ i, k i * matched i = 10 := by
    simp_rw [matched, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [hk]
    exact demand_matched
  have heq : (∑ i, k i * (2 * matched i)) = ∑ i, k i * length i := by
    have hh : (∑ i, k i * (2 * matched i)) = 2 * ∑ i, k i * matched i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hh,hm,ht]
  have hp : ∀ i, k i * (2 * matched i) ≤ k i * length i :=
    fun i => Nat.mul_le_mul_left _ (matching_bound i)
  have hi : ∀ i, k i * (2 * matched i) = k i * length i := by
    have hh := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset I)) => hp i)).mp heq
    exact fun i => hh i (Finset.mem_univ _)
  have hs : ∀ i, k i * length i = k i * 8 := by
    intro i
    by_cases hz : k i = 0
    · simp [hz]
    · have hl : length i = 2 * matched i := by
        exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hz) (hi i)).symm
      rw [equality_length i hl]
  simp_rw [hs] at ht
  rw [← Finset.sum_mul] at ht
  omega

/-- The statement without any choice of a cycle-type index. Binary minimal
even vectors are precisely the ordinary Petersen cycle vectors. -/
lemma binary_minimal_is_col (m : Multiplicity) (hm : MinimalEven m)
    (hb : ∀ e, m e < 2) : ∃ i : I, m = col i := by
  obtain ⟨j,hj⟩ := minimalEven_is_type m hm
  by_cases h : j.val < 57
  · exact ⟨⟨j.val,h⟩,hj⟩
  · have hv : 57 ≤ j.val := by omega
    let e : E := ⟨j.val - 57,by omega⟩
    have he : asDigon e = j := by apply Fin.ext; simp only [asDigon,e]; omega
    have hh := hb e
    rw [hj,← he,← digon_digit] at hh
    simp [digon] at hh

lemma no_binary_circuit_partition (D : List Multiplicity)
    (hD : ∀ m ∈ D, MinimalEven m ∧ ∀ e, m e < 2) :
    ¬ (∀ e : E, (D.map (fun m => m e)).sum = demand e) := by
  have hex : ∀ L : List Multiplicity,
      (∀ m ∈ L, MinimalEven m ∧ ∀ e, m e < 2) →
      ∃ F : List I, F.map col = L := by
    intro L
    induction L with
    | nil => intro _; exact ⟨[],rfl⟩
    | cons m L ih =>
      intro hL
      obtain ⟨i,hi⟩ := binary_minimal_is_col m (hL m (by simp)).1 (hL m (by simp)).2
      obtain ⟨F,hF⟩ := ih (fun x hx => hL x (by simp [hx]))
      exact ⟨i::F,by simp [List.map_cons,hF,← hi]⟩
  obtain ⟨F,hF⟩ := hex D hD
  intro he
  apply no_integral_cover (fun i => F.count i)
  intro e
  have hh := he e
  rw [← hF,List.map_map] at hh
  have hs : ∑ i, F.count i * col i e = (F.map (fun i => col i e)).sum := by
    clear hF hh
    induction F with
    | nil => simp
    | cons i F ih =>
      simp only [List.count_cons,List.map_cons,List.sum_cons]
      simp_rw [Nat.add_mul]
      rw [Finset.sum_add_distrib,ih]
      simp [add_comm]
  exact hs.trans hh

/-- Even binary vectors need not be connected for this obstruction. The six
possible two-factor vectors have strict matching slack. -/
lemma binary_even_properties (m : Multiplicity) (he : EvenVector m)
    (hb : ∀ e, m e < 2) (hn : NonzeroVector m) :
    2 * (∑ e ∈ matching, m e) ≤ ∑ e, m e ∧
      ((∑ e, m e) = 2 * (∑ e ∈ matching, m e) → (∑ e, m e) = 8) := by
  obtain ⟨z,hz,hbit⟩ := binary_encode m hb
  have hze : EvenMask z := by intro v; simpa only [maskDegree,hbit] using he v
  rcases evenMask_classification z hz hze with hzero | ⟨i,hi⟩ | ⟨i,hi⟩
  · obtain ⟨e,he⟩ := hn
    have hh := hbit e
    simp [hzero,bit] at hh
    exact (he hh.symm).elim
  · have hm : m = col i := funext fun e =>
      (hbit e).symm.trans (hi ▸ cycleMask_digits i e)
    subst m
    exact ⟨matching_bound i,equality_length i⟩
  · have hm : m = bit (twoFactorMask i) := funext fun e =>
      (hbit e).symm.trans (congrArg (fun z => bit z e) hi)
    have hcheck : ∀ j : Fin 6, 2 * (∑ e ∈ matching, bit (twoFactorMask j) e) <
        ∑ e : E, bit (twoFactorMask j) e := by decide
    have hstrict := hcheck i
    rw [hm]
    exact ⟨hstrict.le,fun hh => ((ne_of_lt hstrict) hh.symm).elim⟩

lemma no_binary_even_cover {J : Type*} [Fintype J] (m : J → Multiplicity)
    (he : ∀ j, EvenVector (m j)) (hb : ∀ j e, m j e < 2)
    (hn : ∀ j, NonzeroVector (m j)) :
    ¬ (∀ e : E, ∑ j, m j e = demand e) := by
  intro hc
  have ht : (∑ j, ∑ e : E, m j e) = 20 := by
    rw [Finset.sum_comm]
    simp_rw [hc]
    exact demand_total
  have hm : (∑ j, 2 * (∑ e ∈ matching, m j e)) = 20 := by
    rw [← Finset.mul_sum,Finset.sum_comm]
    simp_rw [hc]
    rw [demand_matched]
    decide
  have hp (j : J) := binary_even_properties (m j) (he j) (hb j) (hn j)
  have heq : (∑ j, 2 * (∑ e ∈ matching, m j e)) = ∑ j, ∑ e : E, m j e := by omega
  have hlocal := (Finset.sum_eq_sum_iff_of_le
    (fun j (_ : j ∈ (Finset.univ : Finset J)) => (hp j).1)).mp heq
  have hlen (j : J) : (∑ e : E, m j e) = 8 :=
    (hp j).2 (hlocal j (Finset.mem_univ _)).symm
  simp_rw [hlen] at ht
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at ht
  omega

end Erdos184.PetersenDemandHole
