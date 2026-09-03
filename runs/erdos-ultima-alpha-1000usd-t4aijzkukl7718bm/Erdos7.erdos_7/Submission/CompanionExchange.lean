import FormalConjecturesUtil

/-!
# Exact loss under a companion exchange

A lower class modulo `d` and a disjoint class modulo `p*d` can exchange their
coarse residues. The exchange retains the old upper class. Its losses are
exactly the lower class's private points outside the chosen new upper class.
This criterion does not guarantee a safe exchange, even for a full cover.
-/

namespace Erdos7CompanionExchange
open scoped BigOperators

section Abstract
variable {X : Type*}

/-- `O` is the unchanged union, `L,U` are the old classes, and `A,B` are the
new lower and upper classes. The new lower class contains old `U` and
is disjoint from old `L`. These two inclusions alone give the loss formula. -/
theorem lost_iff (O L U A B : X → Prop)
    (hu : ∀ x, U x → A x)
    (hdis : ∀ x, L x → ¬ A x) (x : X) :
    ((O x ∨ L x ∨ U x) ∧ ¬ (O x ∨ A x ∨ B x)) ↔
      L x ∧ ¬ O x ∧ ¬ B x := by
  constructor
  · rintro ⟨h, hn⟩
    have hO : ¬ O x := fun hx => hn (Or.inl hx)
    have hA : ¬ A x := fun hx => hn (Or.inr (Or.inl hx))
    have hB : ¬ B x := fun hx => hn (Or.inr (Or.inr hx))
    rcases h with h | h | h
    · exact False.elim (hO h)
    · exact ⟨h, hO, hB⟩
    · exact False.elim (hA (hu x h))
  · rintro ⟨hL, hO, hB⟩
    refine ⟨Or.inr (Or.inl hL), ?_⟩
    rintro (h | h | h)
    · exact hO h
    · exact hdis x hL h
    · exact hB h

/-- Conversely, new hits can only come from the enlarged lower class when
the replacement upper class lies in the old lower class. -/
theorem gained_iff (O L U A B : X → Prop) (hb : ∀ x, B x → L x) (x : X) :
    ((O x ∨ A x ∨ B x) ∧ ¬ (O x ∨ L x ∨ U x)) ↔
      A x ∧ ¬ (O x ∨ L x ∨ U x) := by
  constructor
  · rintro ⟨h, hn⟩
    rcases h with h | h | h
    · exact False.elim (hn (Or.inl h))
    · exact ⟨h, hn⟩
    · exact False.elim (hn (Or.inr (Or.inl (hb x h))))
  · rintro ⟨h, hn⟩
    exact ⟨Or.inr (Or.inl h), hn⟩

/-- No old hit can be lost precisely when the new upper class contains all
private points of the old lower class. -/
theorem union_preserved_iff (O L U A B : X → Prop)
    (hu : ∀ x, U x → A x)
    (hdis : ∀ x, L x → ¬ A x) :
    (∀ x, (O x ∨ L x ∨ U x) → O x ∨ A x ∨ B x) ↔
      (∀ x, L x → ¬ O x → B x) := by
  constructor
  · intro h x hL hO
    rcases h x (Or.inr (Or.inl hL)) with h | h | h
    · exact False.elim (hO h)
    · exact False.elim (hdis x hL h)
    · exact h
  · intro h x hx
    rcases hx with hO | hL | hU
    · exact Or.inl hO
    · by_cases hO : O x
      · exact Or.inl hO
      · exact Or.inr (Or.inr (h x hL hO))
    · exact Or.inr (Or.inl (hu x hU))

/-- The exact criterion specializes to genuine full covers. -/
theorem cover_iff (O L U A B : X → Prop)
    (hu : ∀ x, U x → A x)
    (hdis : ∀ x, L x → ¬ A x)
    (hcover : ∀ x, O x ∨ L x ∨ U x) :
    (∀ x, O x ∨ A x ∨ B x) ↔ (∀ x, L x → ¬ O x → B x) := by
  rw [← union_preserved_iff O L U A B hu hdis]
  exact ⟨fun h x _ => h x, fun h x => h x (hcover x)⟩

/-- Two private points which no new upper class can contain together obstruct
every exchange from that family of candidates. -/
theorem all_exchanges_lose {T : Type*} (O L U A : X → Prop) (B : T → X → Prop)
    (hu : ∀ x, U x → A x)
    (hdis : ∀ x, L x → ¬ A x) (x y : X)
    (hx : L x ∧ ¬ O x) (hy : L y ∧ ¬ O y)
    (hsep : ∀ t, ¬ (B t x ∧ B t y)) :
    ∀ t, ∃ z, (O z ∨ L z ∨ U z) ∧ ¬ (O z ∨ A z ∨ B t z) := by
  classical
  intro t
  by_cases htx : B t x
  · refine ⟨y, (lost_iff O L U A (B t) hu hdis y).mpr ?_⟩
    exact ⟨hy.1, hy.2, fun hty => hsep t ⟨htx, hty⟩⟩
  · exact ⟨x, (lost_iff O L U A (B t) hu hdis x).mpr
      ⟨hx.1, hx.2, htx⟩⟩

/-- Across all parts of a finite partition, each point is omitted exactly one
less than the number of parts. This is an exact identity, not a bound on the
least loss of any candidate. -/
theorem total_omitted {T : Type*} [Fintype T] [DecidableEq T]
    [DecidableEq X] (S : Finset X) (f : X → T) :
    (∑ t : T, (S.filter (fun x => f x ≠ t)).card) =
      (Fintype.card T-1)*S.card := by
  classical
  have hf : (∑ t : T, (S.filter (fun x => f x = t)).card) = S.card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter S (Finset.univ : Finset T) f
  have hc (t : T) : (S.filter (fun x => f x ≠ t)).card +
      (S.filter (fun x => f x = t)).card = S.card := by
    simpa using Finset.card_filter_add_card_filter_not (s := S) (fun x => f x ≠ t)
  have hs : (∑ t : T, (S.filter (fun x => f x ≠ t)).card) + S.card =
      Fintype.card T*S.card := by
    conv_lhs => rw [← hf]
    rw [← Finset.sum_add_distrib]
    simp_rw [hc]
    simp
  rw [Nat.mul_sub_right_distrib, one_mul]
  omega

end Abstract

section Arithmetic

/-- Arithmetic congruence classes, with integer modulus. -/
def Hit (d a x : ℤ) : Prop := d ∣ x-a

instance (d a : ℤ) : DecidablePred (Hit d a) :=
  fun x => inferInstanceAs (Decidable (d ∣ x-a))

lemma coarse_of_fine (d p a x : ℤ) (h : Hit (p*d) a x) : Hit d a x := by
  exact (dvd_mul_left d p).trans h

lemma shifted_upper_subset (d p b t x : ℤ) (h : Hit (p*d) (b+t*d) x) :
    Hit d b x := by
  have hh := coarse_of_fine d p (b+t*d) x h
  have hd : d ∣ t*d := dvd_mul_left d t
  have he : x-b = (x-(b+t*d)) + t*d := by ring
  rw [Hit, he]
  exact dvd_add hh hd

lemma incompatible_coarse (d a b : ℤ) (hne : ¬ d ∣ a-b) :
    ∀ x, Hit d b x → ¬ Hit d a x := by
  intro x hb ha
  apply hne
  have h := dvd_sub hb ha
  convert h using 1; ring

/-- Exact integer-point loss formula for swapping a lower class and its
prime-multiple companion. No primality is needed for this formula. -/
theorem arithmetic_lost_iff (O : ℤ → Prop) (d p a b t x : ℤ)
    (hne : ¬ d ∣ a-b) :
    ((O x ∨ Hit d b x ∨ Hit (p*d) a x) ∧
      ¬ (O x ∨ Hit d a x ∨ Hit (p*d) (b+t*d) x)) ↔
      Hit d b x ∧ ¬ O x ∧ ¬ Hit (p*d) (b+t*d) x := by
  exact lost_iff O (Hit d b) (Hit (p*d) a) (Hit d a)
    (Hit (p*d) (b+t*d)) (coarse_of_fine d p a)
    (incompatible_coarse d a b hne) x

/-- A covering-preserving arithmetic exchange is equivalent to all private
points of the lower class having the selected finer residue. -/
theorem arithmetic_cover_iff (O : ℤ → Prop) (d p a b t : ℤ)
    (hne : ¬ d ∣ a-b)
    (hcover : ∀ x, O x ∨ Hit d b x ∨ Hit (p*d) a x) :
    (∀ x, O x ∨ Hit d a x ∨ Hit (p*d) (b+t*d) x) ↔
      (∀ x, Hit d b x → ¬ O x → Hit (p*d) (b+t*d) x) := by
  exact cover_iff O (Hit d b) (Hit (p*d) a) (Hit d a)
    (Hit (p*d) (b+t*d)) (coarse_of_fine d p a)
    (incompatible_coarse d a b hne) hcover

/-- Two private points with distinct residues modulo the upper modulus rule
out every possible companion exchange, not just one selected phase. -/
theorem arithmetic_all_exchanges_lose (O : ℤ → Prop) (d p a b x y : ℤ)
    (hne : ¬ d ∣ a-b) (hx : Hit d b x ∧ ¬ O x) (hy : Hit d b y ∧ ¬ O y)
    (hxy : ¬ (p*d) ∣ x-y) :
    ∀ t : ℤ, ∃ z : ℤ, (O z ∨ Hit d b z ∨ Hit (p*d) a z) ∧
      ¬ (O z ∨ Hit d a z ∨ Hit (p*d) (b+t*d) z) := by
  apply all_exchanges_lose O (Hit d b) (Hit (p*d) a) (Hit d a)
    (fun t => Hit (p*d) (b+t*d)) (coarse_of_fine d p a)
    (incompatible_coarse d a b hne) x y hx hy
  intro t h
  apply hxy
  have hd := dvd_sub h.1 h.2
  convert hd using 1; ring

lemma fine_iff_digit_eq (p : ℕ) [NeZero p] (d b x : ℤ) (hd : d ≠ 0)
    (hx : Hit d b x) (t : ZMod p) :
    Hit ((p : ℤ)*d) (b+(t.val : ℤ)*d) x ↔ (((x-b)/d : ℤ) : ZMod p) = t := by
  have he : x-(b+(t.val : ℤ)*d) = d*((x-b)/d-(t.val : ℤ)) := by
    rw [mul_sub, Int.mul_ediv_cancel' hx]
    ring
  rw [Hit, he, mul_comm (p : ℤ) d, Int.mul_dvd_mul_iff_left hd]
  have hh := ZMod.intCast_eq_intCast_iff_dvd_sub (t.val : ℤ) ((x-b)/d) p
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at hh
  exact hh.symm.trans eq_comm

/-- For any finite set of private lower points, the total number lost over all
`p` exchanges equals `(p-1)` times the number of those points. -/
theorem arithmetic_total_private_loss (O : ℤ → Prop) [DecidablePred O]
    (p : ℕ) [NeZero p]
    (d a b : ℤ) (hd : d ≠ 0) (hne : ¬ d ∣ a-b) (S : Finset ℤ)
    (hS : ∀ x ∈ S, Hit d b x ∧ ¬ O x) :
    (∑ t : ZMod p, (S.filter (fun x =>
      (O x ∨ Hit d b x ∨ Hit ((p : ℤ)*d) a x) ∧
      ¬ (O x ∨ Hit d a x ∨ Hit ((p : ℤ)*d) (b+(t.val : ℤ)*d) x))).card) =
      (p-1)*S.card := by
  classical
  have hf (t : ZMod p) : (S.filter (fun x =>
      (O x ∨ Hit d b x ∨ Hit ((p : ℤ)*d) a x) ∧
      ¬ (O x ∨ Hit d a x ∨ Hit ((p : ℤ)*d) (b+(t.val : ℤ)*d) x))) =
      S.filter (fun x => (((x-b)/d : ℤ) : ZMod p) ≠ t) := by
    apply Finset.filter_congr
    intro x hx
    rw [arithmetic_lost_iff O d p a b t.val x hne]
    simp only [(hS x hx).1, (hS x hx).2, true_and, not_false_eq_true,
      fine_iff_digit_eq p d b x hd (hS x hx).1 t]
  simp_rw [hf]
  simpa only [ZMod.card] using total_omitted S (fun x => (((x-b)/d : ℤ) : ZMod p))

end Arithmetic

section EvenControl

/-- This is a genuine strict cover, but it is NOT odd. -/
def moduli : Fin 5 → ℕ := ![2,3,4,6,12]
def residues : Fin 5 → ℤ := ![0,0,1,1,11]
def witnesses : Fin 5 → ℤ := ![2,3,5,7,11]

theorem control_data : Function.Injective moduli ∧
    (∀ i, 1 < moduli i ∧ moduli i ∣ 12) ∧
    (∀ i j, ((moduli j : ℕ) : ℤ) ∣ witnesses i-residues j ↔ i=j) := by
  decide +kernel

lemma control_finite_cover : ∀ r : Fin 12,
    ∃ i, (moduli i : ℤ) ∣ (r.val : ℤ)-residues i := by
  decide +kernel

theorem control_cover : ∀ x : ℤ, ∃ i, (moduli i : ℤ) ∣ x-residues i := by
  intro x
  let r : Fin 12 := ⟨(x % 12).toNat, by omega⟩
  obtain ⟨i, hi⟩ := control_finite_cover r
  have hr : (r.val : ℤ) = x % 12 := by
    dsimp [r]
    exact Int.toNat_of_nonneg (by omega)
  rw [hr] at hi
  have hm : (moduli i : ℤ) ∣ 12 := by exact_mod_cast (control_data.2.1 i).2
  have h12 : (12 : ℤ) ∣ x-x%12 := Int.dvd_self_sub_emod
  have h := dvd_add (hm.trans h12) hi
  refine ⟨i, ?_⟩
  convert h using 1; ring

/-- Unchanged classes while exchanging the classes modulo 2 and 4. -/
def other (x : ℤ) : Prop := Hit 3 0 x ∨ Hit 6 1 x ∨ Hit 12 11 x

lemma other_context_cover (x : ℤ) : other x ∨ Hit 2 0 x ∨ Hit 4 1 x := by
  obtain ⟨i, hi⟩ := control_cover x
  fin_cases i
  · exact Or.inr (Or.inl hi)
  · exact Or.inl (Or.inl hi)
  · exact Or.inr (Or.inr hi)
  · exact Or.inl (Or.inr (Or.inl hi))
  · exact Or.inl (Or.inr (Or.inr hi))

lemma two_four_private : (Hit 2 0 2 ∧ ¬ other 2) ∧ (Hit 2 0 4 ∧ ¬ other 4) := by
  unfold other Hit
  decide +kernel

/-- Every exchange of this fixed pair loses a point despite full coverage,
distinctness, and a private point for every class. This is not an odd cover. -/
theorem every_two_four_exchange_loses : ∀ t : ℤ, ∃ x : ℤ,
    (other x ∨ Hit 2 0 x ∨ Hit 4 1 x) ∧
      ¬ (other x ∨ Hit 2 1 x ∨ Hit 4 (t*2) x) := by
  apply all_exchanges_lose other (Hit 2 0) (Hit 4 1) (Hit 2 1)
    (fun t => Hit 4 (t*2))
  · exact coarse_of_fine 2 2 1
  · exact incompatible_coarse 2 1 0 (by norm_num)
  · exact two_four_private.1
  · exact two_four_private.2
  · intro t h
    have hd := dvd_sub h.1 h.2
    have h4 : (4 : ℤ) ∣ -2 := by convert hd using 1; ring
    norm_num at h4

/-- The same genuine cover also obstructs every exchange of the classes
modulo 2 and 6. Here the companion multiplier itself is the odd prime 3. -/
def otherSix (x : ℤ) : Prop := Hit 3 0 x ∨ Hit 4 1 x ∨ Hit 12 11 x

lemma other_six_context_cover (x : ℤ) : otherSix x ∨ Hit 2 0 x ∨ Hit 6 1 x := by
  obtain ⟨i, hi⟩ := control_cover x
  fin_cases i
  · exact Or.inr (Or.inl hi)
  · exact Or.inl (Or.inl hi)
  · exact Or.inl (Or.inr (Or.inl hi))
  · exact Or.inr (Or.inr hi)
  · exact Or.inl (Or.inr (Or.inr hi))

theorem every_two_six_exchange_loses : ∀ t : ℤ, ∃ x : ℤ,
    (otherSix x ∨ Hit 2 0 x ∨ Hit 6 1 x) ∧
      ¬ (otherSix x ∨ Hit 2 1 x ∨ Hit 6 (t*2) x) := by
  have hx : Hit 2 0 2 ∧ ¬ otherSix 2 := by unfold otherSix Hit; decide +kernel
  have hy : Hit 2 0 4 ∧ ¬ otherSix 4 := by unfold otherSix Hit; decide +kernel
  simpa using arithmetic_all_exchanges_lose otherSix 2 3 1 0 2 4
    (by norm_num) hx hy (by norm_num)

theorem no_two_six_exchange_cover (t : ℤ) :
    ¬ (∀ x : ℤ, otherSix x ∨ Hit 2 1 x ∨ Hit 6 (t*2) x) := by
  intro h
  obtain ⟨x, _, hx⟩ := every_two_six_exchange_loses t
  exact hx (h x)

end EvenControl

#print axioms arithmetic_lost_iff
#print axioms arithmetic_cover_iff
#print axioms arithmetic_all_exchanges_lose
#print axioms total_omitted
#print axioms arithmetic_total_private_loss
#print axioms control_data
#print axioms control_cover
#print axioms every_two_four_exchange_loses
#print axioms every_two_six_exchange_loses
#print axioms no_two_six_exchange_cover

end Erdos7CompanionExchange
