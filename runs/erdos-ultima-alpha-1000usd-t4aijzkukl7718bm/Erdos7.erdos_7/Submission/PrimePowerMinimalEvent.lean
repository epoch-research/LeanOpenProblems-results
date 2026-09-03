import Submission.TwoValueCore
import Submission.PrimePowerCoreSignature

/-! Exact minimal-core events for thin prime-power sections. This connects
Boolean minimality with the deepest-constraint signature; it does not bound
the union of all signatures of a covering system. -/
namespace Erdos7PrimePowerMinimalEvent
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

section Boolean
variable {I J : Type*} [DecidableEq I]

/-- Minimality includes a private Boolean point for each selected clause. -/
def BooleanMinimal (S : J → Finset I) (b : J → I → Fin 2) (s : Finset J) : Prop :=
  (∀ x : I → Fin 2, ∃ j ∈ s, ∀ i ∈ S j, x i = b j i) ∧
  ∀ j ∈ s, ∃ x : I → Fin 2, ∀ k ∈ s,
    (∀ i ∈ S k, x i = b k i) ↔ k = j

/-- The actual sections, evaluated on a pair of selected values per coordinate. -/
def SectionMinimal (A : I → Type*) (S : J → Finset I)
    (B : J → (i : I) → Set (A i)) (s : Finset J)
    (z : (i : I) → Fin 2 → A i) : Prop :=
  (∀ x : I → Fin 2, ∃ j ∈ s, ∀ i ∈ S j, z i (x i) ∈ B j i) ∧
  ∀ j ∈ s, ∃ x : I → Fin 2, ∀ k ∈ s,
    (∀ i ∈ S k, z i (x i) ∈ B k i) ↔ k = j

/-- When membership forces the prescribed Boolean label, the exact event is
Boolean minimality together with activity of every local section. -/
theorem minimal_iff_boolean_and_activity (A : I → Type*) (S : J → Finset I)
    (B : J → (i : I) → Set (A i)) (s : Finset J) (b : J → I → Fin 2)
    (z : (i : I) → Fin 2 → A i)
    (halign : ∀ j ∈ s, ∀ i ∈ S j, ∀ r : Fin 2, z i r ∈ B j i → r = b j i) :
    SectionMinimal A S B s z ↔ BooleanMinimal S b s ∧
      ∀ j ∈ s, ∀ i ∈ S j, z i (b j i) ∈ B j i := by
  have hmatch (hact : ∀ j ∈ s, ∀ i ∈ S j, z i (b j i) ∈ B j i)
      (j : J) (hj : j ∈ s) (x : I → Fin 2) :
      (∀ i ∈ S j, z i (x i) ∈ B j i) ↔ ∀ i ∈ S j, x i = b j i := by
    constructor
    · exact fun h i hi => halign j hj i hi (x i) (h i hi)
    · intro h i hi
      rw [h i hi]
      exact hact j hj i hi
  constructor
  · intro h
    have hact : ∀ j ∈ s, ∀ i ∈ S j, z i (b j i) ∈ B j i := by
      intro j hj i hi
      obtain ⟨x, hx⟩ := h.2 j hj
      have hm := ((hx j hj).mpr rfl) i hi
      rwa [halign j hj i hi (x i) hm] at hm
    refine ⟨⟨?_, ?_⟩, hact⟩
    · intro x
      obtain ⟨j, hj, hm⟩ := h.1 x
      exact ⟨j, hj, (hmatch hact j hj x).mp hm⟩
    · intro j hj
      obtain ⟨x, hx⟩ := h.2 j hj
      exact ⟨x, fun k hk => (hmatch hact k hk x).symm.trans (hx k hk)⟩
  · rintro ⟨h, hact⟩
    constructor
    · intro x
      obtain ⟨j, hj, hm⟩ := h.1 x
      exact ⟨j, hj, (hmatch hact j hj x).mpr hm⟩
    · intro j hj
      obtain ⟨x, hx⟩ := h.2 j hj
      exact ⟨x, fun k hk => (hmatch hact k hk x).trans (hx k hk)⟩

/-- Thinness allows the Boolean model to be extracted from private points.
No unsupported independence assertion is involved. -/
theorem exists_boolean_model (A : I → Type*) (S : J → Finset I)
    (B : J → (i : I) → Set (A i)) (s : Finset J)
    (z : (i : I) → Fin 2 → A i)
    (h : SectionMinimal A S B s z)
    (hthin : ∀ j ∈ s, ∀ i ∈ S j, ∀ r t : Fin 2,
      z i r ∈ B j i → z i t ∈ B j i → r = t) :
    ∃ b : J → I → Fin 2, BooleanMinimal S b s ∧
      (∀ j ∈ s, ∀ i ∈ S j, z i (b j i) ∈ B j i) ∧
      ∀ j ∈ s, ∀ i ∈ S j, ∀ r : Fin 2, z i r ∈ B j i → r = b j i := by
  classical
  have hp (j : J) (hj : j ∈ s) : ∃ x : I → Fin 2, ∀ i ∈ S j, z i (x i) ∈ B j i := by
    obtain ⟨x, hx⟩ := h.2 j hj
    exact ⟨x, (hx j hj).mpr rfl⟩
  let b (j : J) : I → Fin 2 := if hj : j ∈ s then (hp j hj).choose else fun _ => 0
  have hact (j : J) (hj : j ∈ s) : ∀ i ∈ S j, z i (b j i) ∈ B j i := by
    simpa only [b, dif_pos hj] using (hp j hj).choose_spec
  have halign : ∀ j ∈ s, ∀ i ∈ S j, ∀ r : Fin 2, z i r ∈ B j i → r = b j i := by
    intro j hj i hi r hr
    exact hthin j hj i hi r (b j i) hr (hact j hj i hi)
  exact ⟨b, ((minimal_iff_boolean_and_activity A S B s b z halign).mp h).1,
    hact, halign⟩

/-- Every used coordinate of a minimal Boolean cover has both labels. -/
theorem both_labels (S : J → Finset I) (b : J → I → Fin 2) (s : Finset J)
    (h : BooleanMinimal S b s) (i : I) (hi : i ∈ s.biUnion S) (r : Fin 2) :
    ∃ j ∈ s, i ∈ S j ∧ b j i = r := by
  classical
  have hc : ∀ x : I → Fin 2, ∃ j : s, ∀ i ∈ S j.val, x i = b j.val i := by
    intro x
    obtain ⟨j, hj, hx⟩ := h.1 x
    exact ⟨⟨j, hj⟩, hx⟩
  have hp : ∀ j : s, ∃ x : I → Fin 2, ∀ k : s, k ≠ j →
      ¬ ∀ i ∈ S k.val, x i = b k.val i := by
    intro j
    obtain ⟨x, hx⟩ := h.2 j.val j.property
    refine ⟨x, fun k hkj hm => ?_⟩
    exact hkj (Subtype.ext ((hx k.val k.property).mp hm))
  obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨k, hik, hkr⟩ := Erdos7TwoValueCore.irredundant_all_values
    (fun _ : I => Fin 2) (fun j : s => S j.val) (fun j : s => b j.val)
    hc hp i ⟨⟨j, hj⟩, hij⟩ r
  exact ⟨k.val, k.property, hik, hkr⟩
end Boolean

section Arithmetic
variable {I J : Type*} [DecidableEq I] [DecidableEq J]

/-- Different first-digit branches distinguish the Boolean labels of a
positive-exponent cylinder. Primality is not needed for this implication. -/
lemma power_alignment (p e : ℕ) (he : 0 < e) (a : ℤ)
    (root z : Fin 2 → ℤ) (b : Fin 2)
    (hsep : ∀ r t, (p : ℤ) ∣ root r - root t → r = t)
    (hz : ∀ r, (p : ℤ) ∣ z r - root r)
    (ha : (p : ℤ) ∣ a - root b)
    (r : Fin 2) (hr : ((p ^ e : ℕ) : ℤ) ∣ z r - a) : r = b := by
  have hpd : (p : ℤ) ∣ ((p ^ e : ℕ) : ℤ) := by
    exact_mod_cast dvd_pow_self p he.ne'
  apply hsep
  convert dvd_add (dvd_sub (hpd.trans hr) (hz r)) ha using 1
  ring

/-- The clauses using one particular coordinate. -/
def localClauses (S : J → Finset I) (s : Finset J) (i : I) : Finset J :=
  s.filter (fun j => i ∈ S j)

/-- Compatible deepest constraints are exactly all the local constraints.
The representatives are required only at used coordinates. -/
theorem activity_iff_signature (p : I → ℕ) (S : J → Finset I)
    (e : J → I → ℕ) (a : J → I → ℤ) (s : Finset J) (b : J → I → Fin 2)
    (k : I → Fin 2 → J)
    (hk : ∀ i ∈ s.biUnion S, ∀ r,
      k i r ∈ s ∧ i ∈ S (k i r) ∧ b (k i r) i = r)
    (hmax : ∀ j ∈ s, ∀ i ∈ S j, e j i ≤ e (k i (b j i)) i)
    (z : I → Fin 2 → ℤ) :
    (∀ j ∈ s, ∀ i ∈ S j, ((p i ^ e j i : ℕ) : ℤ) ∣ z i (b j i) - a j i) ↔
      ∀ i ∈ s.biUnion S,
        Erdos7PrimePowerCoreSignature.Compatible (p i) (localClauses S s i)
          (fun j => b j i) (fun j => e j i) (fun j => a j i) (k i) ∧
        ∀ r, ((p i ^ e (k i r) i : ℕ) : ℤ) ∣ z i r - a (k i r) i := by
  have hlocal (i : I) (hi : i ∈ s.biUnion S) :=
    Erdos7PrimePowerCoreSignature.constraints_iff_deepest (p i) (localClauses S s i)
      (fun j => b j i) (fun j => e j i) (fun j => a j i) (k i)
      (by
        intro r
        have hr := hk i hi r
        exact ⟨Finset.mem_filter.mpr ⟨hr.1, hr.2.1⟩, hr.2.2⟩)
      (by
        intro j hj
        obtain ⟨hjs, hji⟩ := Finset.mem_filter.mp hj
        exact hmax j hjs i hji) (z i)
  constructor
  · intro h i hi
    apply (hlocal i hi).mp
    intro j hj
    obtain ⟨hjs, hji⟩ := Finset.mem_filter.mp hj
    exact h j hjs i hji
  · intro h j hj i hi
    have hiu : i ∈ s.biUnion S := Finset.mem_biUnion.mpr ⟨j, hj, hi⟩
    exact (hlocal i hiu).mpr (h i hiu) j (Finset.mem_filter.mpr ⟨hj, hi⟩)

/-- Exact signature description of the actual minimal-cover event, with the
root orientation fixed in advance. The Boolean cover and private-point
condition remains on the right: compatibility alone is not coverage. -/
theorem minimal_event_iff_signature (p : I → ℕ) (S : J → Finset I)
    (e : J → I → ℕ) (he : ∀ j i, i ∈ S j → 0 < e j i)
    (a : J → I → ℤ) (s : Finset J) (b : J → I → Fin 2)
    (root z : I → Fin 2 → ℤ)
    (hsep : ∀ i r t, (p i : ℤ) ∣ root i r - root i t → r = t)
    (hz : ∀ i r, (p i : ℤ) ∣ z i r - root i r)
    (ha : ∀ j ∈ s, ∀ i ∈ S j, (p i : ℤ) ∣ a j i - root i (b j i))
    (k : I → Fin 2 → J)
    (hk : ∀ i ∈ s.biUnion S, ∀ r,
      k i r ∈ s ∧ i ∈ S (k i r) ∧ b (k i r) i = r)
    (hmax : ∀ j ∈ s, ∀ i ∈ S j, e j i ≤ e (k i (b j i)) i) :
    SectionMinimal (fun _ : I => ℤ) S
      (fun j i => {x | ((p i ^ e j i : ℕ) : ℤ) ∣ x - a j i}) s z ↔
      BooleanMinimal S b s ∧
      ∀ i ∈ s.biUnion S,
        Erdos7PrimePowerCoreSignature.Compatible (p i) (localClauses S s i)
          (fun j => b j i) (fun j => e j i) (fun j => a j i) (k i) ∧
        ∀ r, ((p i ^ e (k i r) i : ℕ) : ℤ) ∣ z i r - a (k i r) i := by
  rw [minimal_iff_boolean_and_activity (fun _ : I => ℤ) S _ s b z
    (fun j hj i hi r hr => power_alignment (p i) (e j i) (he j i hi) (a j i)
      (root i) (z i) (b j i) (hsep i) (hz i) (ha j hj i hi) r hr)]
  exact and_congr_right (fun _ => activity_iff_signature p S e a s b k hk hmax z)

/-- Deepest representatives are available for every used coordinate of a
minimal Boolean cover. This does not assume that all ambient coordinates
are used, or that the clause supports are distinct. -/
theorem exists_deepest_representatives (S : J → Finset I) (e : J → I → ℕ)
    (s : Finset J) (b : J → I → Fin 2) (h : BooleanMinimal S b s) :
    ∀ i ∈ s.biUnion S, ∃ k : Fin 2 → J,
      (∀ r, k r ∈ s ∧ i ∈ S (k r) ∧ b (k r) i = r) ∧
      ∀ j ∈ s, i ∈ S j → e j i ≤ e (k (b j i)) i := by
  intro i hi
  obtain ⟨k, hk, hmax⟩ := Erdos7PrimePowerCoreSignature.exists_deepest_pair
    (localClauses S s i) (fun j => b j i) (fun j => e j i)
    (by
      intro r
      obtain ⟨j, hj, hij, hjr⟩ := both_labels S b s h i hi r
      exact ⟨j, Finset.mem_filter.mpr ⟨hj, hij⟩, hjr⟩)
  refine ⟨k, ?_, ?_⟩
  · intro r
    have hr := hk r
    exact ⟨(Finset.mem_filter.mp hr.1).1, (Finset.mem_filter.mp hr.1).2, hr.2⟩
  · intro j hj hij
    exact hmax j (Finset.mem_filter.mpr ⟨hj, hij⟩)
/-- A positive-exponent congruence fixes its first digit. -/
lemma first_digit_of_power {p e : ℕ} {x a : ℤ} (he : 0 < e)
    (h : ((p ^ e : ℕ) : ℤ) ∣ x - a) : (x : ZMod p) = (a : ZMod p) := by
  have hd : (p : ℤ) ∣ ((p ^ e : ℕ) : ℤ) := by
    exact_mod_cast dvd_pow_self p he.ne'
  exact ((ZMod.intCast_eq_intCast_iff_dvd_sub a x p).mpr (hd.trans h)).symm

/-- A minimal prime-power event determines its pair of first digits at every
used coordinate. This pair is read from the clause residues, not guessed
independently for each constraint. -/
theorem first_digit_pair_forced (p : I → ℕ) (S : J → Finset I)
    (e : J → I → ℕ) (he : ∀ j i, i ∈ S j → 0 < e j i)
    (a : J → I → ℤ) (s : Finset J) (z : I → Fin 2 → ℤ)
    (hz : ∀ i, Function.Injective (fun r => (z i r : ZMod (p i))))
    (h : SectionMinimal (fun _ : I => ℤ) S
      (fun j i => {x | ((p i ^ e j i : ℕ) : ℤ) ∣ x - a j i}) s z) :
    ∀ i ∈ s.biUnion S,
      (localClauses S s i).image (fun j => (a j i : ZMod (p i))) =
        Finset.univ.image (fun r => (z i r : ZMod (p i))) := by
  classical
  obtain ⟨b, hb, hact, _⟩ := exists_boolean_model (fun _ : I => ℤ) S _ s z h
    (by
      intro j hj i hi r t hr ht
      apply hz i
      exact (first_digit_of_power (he j i hi) hr).trans
        (first_digit_of_power (he j i hi) ht).symm)
  intro i hi
  ext v
  constructor
  · intro hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hjs, hji⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_image.mpr ⟨b j i, Finset.mem_univ _,
      first_digit_of_power (he j i hji) (hact j hjs i hji)⟩
  · intro hv
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j, hj, hij, hjr⟩ := both_labels S b s hb i hi r
    refine Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hij⟩, ?_⟩
    have hh := first_digit_of_power (he j i hij) (hact j hj i hij)
    simpa only [hjr] using hh.symm

theorem first_digit_card_two (p : I → ℕ) (S : J → Finset I)
    (e : J → I → ℕ) (he : ∀ j i, i ∈ S j → 0 < e j i)
    (a : J → I → ℤ) (s : Finset J) (z : I → Fin 2 → ℤ)
    (hz : ∀ i, Function.Injective (fun r => (z i r : ZMod (p i))))
    (h : SectionMinimal (fun _ : I => ℤ) S
      (fun j i => {x | ((p i ^ e j i : ℕ) : ℤ) ∣ x - a j i}) s z) :
    ∀ i ∈ s.biUnion S,
      ((localClauses S s i).image (fun j => (a j i : ZMod (p i)))).card = 2 := by
  intro i hi
  rw [first_digit_pair_forced p S e he a s z hz h i hi,
    Finset.card_image_of_injective _ (hz i)]
  decide

/-- Every actual minimal event on different first-digit branches supplies a
Boolean model and compatible deepest representatives. The signature
conditions cover every used coordinate and include actual deepest hits. -/
theorem exists_signature_of_minimal_event (p : I → ℕ) (S : J → Finset I)
    (e : J → I → ℕ) (he : ∀ j i, i ∈ S j → 0 < e j i)
    (a : J → I → ℤ) (s : Finset J) (z : I → Fin 2 → ℤ)
    (hz : ∀ i, Function.Injective (fun r => (z i r : ZMod (p i))))
    (h : SectionMinimal (fun _ : I => ℤ) S
      (fun j i => {x | ((p i ^ e j i : ℕ) : ℤ) ∣ x - a j i}) s z) :
    ∃ (b : J → I → Fin 2) (k : I → Fin 2 → J),
      BooleanMinimal S b s ∧
      (∀ i ∈ s.biUnion S, ∀ r,
        k i r ∈ s ∧ i ∈ S (k i r) ∧ b (k i r) i = r) ∧
      (∀ j ∈ s, ∀ i ∈ S j, e j i ≤ e (k i (b j i)) i) ∧
      ∀ i ∈ s.biUnion S,
        Erdos7PrimePowerCoreSignature.Compatible (p i) (localClauses S s i)
          (fun j => b j i) (fun j => e j i) (fun j => a j i) (k i) ∧
        ∀ r, ((p i ^ e (k i r) i : ℕ) : ℤ) ∣ z i r - a (k i r) i := by
  classical
  obtain ⟨b, hb, hact, _⟩ := exists_boolean_model (fun _ : I => ℤ) S _ s z h
    (by
      intro j hj i hi r t hr ht
      apply hz i
      exact (first_digit_of_power (he j i hi) hr).trans
        (first_digit_of_power (he j i hi) ht).symm)
  have hrep := exists_deepest_representatives S e s b hb
  obtain ⟨j₀, _, _⟩ := hb.1 (fun _ => 0)
  let k (i : I) : Fin 2 → J :=
    if hi : i ∈ s.biUnion S then (hrep i hi).choose else fun _ => j₀
  have hk : ∀ i ∈ s.biUnion S, ∀ r,
      k i r ∈ s ∧ i ∈ S (k i r) ∧ b (k i r) i = r := by
    intro i hi
    simpa only [k, dif_pos hi] using (hrep i hi).choose_spec.1
  have hmax : ∀ j ∈ s, ∀ i ∈ S j, e j i ≤ e (k i (b j i)) i := by
    intro j hj i hi
    have hiu : i ∈ s.biUnion S := Finset.mem_biUnion.mpr ⟨j, hj, hi⟩
    simpa only [k, dif_pos hiu] using (hrep i hiu).choose_spec.2 j hj hi
  exact ⟨b, k, hb, hk, hmax,
    (activity_iff_signature p S e a s b k hk hmax z).mp hact⟩

end Arithmetic

#print axioms minimal_iff_boolean_and_activity
#print axioms exists_boolean_model
#print axioms minimal_event_iff_signature
#print axioms exists_deepest_representatives
#print axioms first_digit_pair_forced
#print axioms first_digit_card_two
#print axioms exists_signature_of_minimal_event
end Erdos7PrimePowerMinimalEvent
