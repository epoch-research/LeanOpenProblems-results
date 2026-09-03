import FormalConjecturesUtil

/-! A finite limitation of top-digit intersection descent. This file gives a
partial odd family, NOT a covering system and NOT a settlement of Erdős 7. -/
namespace Erdos7TopFiberIntersectionExample
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000

/-- The elementary simultaneous-fiber identity. A genuine cover of every
fiber gives the intersection cover, not merely the union of top families. -/
theorem all_fibers_iff {X R : Type*} [Nonempty R] (L : Set X) (B : R → Set X) :
    (∀ r, L ∪ B r = Set.univ) ↔ L ∪ (⋂ r, B r) = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ L
    · exact Or.inl hx
    · exact Or.inr (Set.mem_iInter.mpr (fun r =>
        (show x ∈ L ∪ B r by rw [h r]; trivial).resolve_left hx))
  · intro h r
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ L ∪ (⋂ r, B r) := by rw [h]; trivial
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Set.mem_iInter.mp hx r)

def modulus : Fin 7 → ℕ := ![3,5,7,15,21,35,105]
def residueN : Fin 7 → ℕ := ![0,0,0,1,8,23,22]
def residue (i : Fin 7) : ℤ := residueN i
def privatePoint : Fin 7 → ℤ := ![3,5,7,1,8,23,22]

lemma arithmetic_data :
    Function.Injective modulus ∧
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ modulus i ∣ 105) ∧
    (∀ i j, (modulus j : ℤ) ∣ privatePoint i-residue j ↔ j=i) ∧
    (∀ i, ¬ (modulus i : ℤ) ∣ 2-residue i) := by
  decide +kernel

lemma comparable_separation : ∀ i j : Fin 7, i ≠ j → modulus i ∣ modulus j →
    ¬ (modulus i : ℤ) ∣ residue j-residue i := by
  decide +kernel

lemma divisor_data : ∀ i : Fin 7, ∀ d : ↥(modulus i).divisors,
    1 < d.val → ∃ j, modulus j=d.val := by
  decide +kernel

theorem divisor_closed (i : Fin 7) (d : ℕ) (hd : d ∣ modulus i) (h1 : 1 < d) :
    ∃ j, modulus j=d := by
  have hp : 0 < modulus i := lt_trans (by omega : 0 < 1) (arithmetic_data.2.1 i).1
  exact divisor_data i ⟨d,Nat.mem_divisors.mpr ⟨hd,hp.ne'⟩⟩ h1

theorem not_cover : ¬ ∀ x : ℤ, ∃ i, (modulus i : ℤ) ∣ x-residue i := by
  intro h
  obtain ⟨i,hi⟩ := h 2
  exact arithmetic_data.2.2.2 i hi

/-- Congruence classes in the quotient period 35, using canonical residues. -/
def coset (m a : ℕ) : Finset (Fin 35) :=
  Finset.univ.filter (fun x => x.val % m = a % m)

def lower : Finset (Fin 35) := Finset.univ.filter (fun x =>
  ∃ i : Fin 7, ¬ 3 ∣ modulus i ∧ x.val % modulus i = residueN i % modulus i)

def upper (r : Fin 3) : Finset (Fin 35) := Finset.univ.filter (fun x =>
  ∃ i : Fin 7, 3 ∣ modulus i ∧ residueN i % 3 = r.val ∧
    x.val % (modulus i / 3) = residueN i % (modulus i / 3))

def joint : Finset (Fin 35) := lower ∪ Finset.univ.filter (fun x => ∀ r, x ∈ upper r)

/-- The unique lift modulo 105 with the given residues modulo 35 and 3. -/
def lift (r : Fin 3) (x : Fin 35) : ℕ :=
  x.val + 35 * ((2*(r.val+3-x.val%3))%3)

lemma lift_data : ∀ r : Fin 3, ∀ x : Fin 35,
    lift r x < 105 ∧ lift r x % 35 = x.val ∧ lift r x % 3 = r.val ∧
    ((∃ i : Fin 7, lift r x % modulus i = residueN i % modulus i) ↔
      x ∈ lower ∨ x ∈ upper r) := by
  decide +kernel

/-- The reduced union records exactly the base points whose ENTIRE fiber was
covered. Thus a genuine original cover would imply a cover by the joint family. -/
theorem mem_joint_iff (x : Fin 35) : x ∈ joint ↔
    ∀ r : Fin 3, ∃ i : Fin 7, lift r x % modulus i = residueN i % modulus i := by
  simp only [joint, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro (hL | hB) r
    · exact (lift_data r x).2.2.2.mpr (Or.inl hL)
    · exact (lift_data r x).2.2.2.mpr (Or.inr (hB r))
  · intro h
    by_cases hx : x ∈ lower
    · exact Or.inl hx
    · exact Or.inr (fun r => ((lift_data r x).2.2.2.mp (h r)).resolve_left hx)

/-- Two different top-color intersections have the SAME modulus 35, and both
are outside the lower union. The existing lower modulus 35 supplies a third
residue class at that modulus. -/
lemma joint_data :
    lower = coset 5 0 ∪ coset 7 0 ∪ coset 35 23 ∧
    (Finset.univ.filter (fun x : Fin 35 => ∀ r, x ∈ upper r)) = {1,22} ∧
    joint = lower ∪ coset 35 1 ∪ coset 35 22 ∧
    1 ∉ lower ∧ 22 ∉ lower ∧ joint.card = 14 := by
  decide +kernel

lemma coset_card_data : ∀ a : Fin 35,
    (coset 5 a.val).card = 7 ∧ (coset 7 a.val).card = 5 ∧
    (coset 35 a.val).card = 1 := by
  decide +kernel

/-- Even allowing arbitrary new residues, one class for EACH available
nontrivial divisor modulus cannot contain this reduced union: 14 > 7+5+1. -/
theorem no_three_cosets (a b c : Fin 35) :
    ¬ joint ⊆ coset 5 a.val ∪ coset 7 b.val ∪ coset 35 c.val := by
  intro h
  have hcard := Finset.card_le_card h
  have h1 := Finset.card_union_le (coset 5 a.val) (coset 7 b.val)
  have h2 := Finset.card_union_le (coset 5 a.val ∪ coset 7 b.val) (coset 35 c.val)
  have ha := (coset_card_data a).1
  have hb := (coset_card_data b).2.1
  have hc := (coset_card_data c).2.2
  have hj := joint_data.2.2.2.2.2
  omega

lemma divisor35_data : ∀ d : ↥(35 : ℕ).divisors,
    1 < d.val → d.val = 5 ∨ d.val = 7 ∨ d.val = 35 := by
  decide +kernel

/-- This also rules out pruning followed by arbitrary distinct nontrivial
modulus assignments inside the smaller period, not just retaining every
intersection as an independently labelled class. -/
theorem no_strict_divisor_family {I : Type*} (m : I → ℕ) (a : I → Fin 35)
    (hinj : Function.Injective m) (hdiv : ∀ i, m i ∣ 35) (h1 : ∀ i, 1 < m i) :
    ¬ ∀ x ∈ joint, ∃ i, x ∈ coset (m i) (a i).val := by
  classical
  let b : ℕ → Fin 35 := Function.extend m a (fun _ => 0)
  have hb (i : I) : b (m i) = a i := hinj.extend_apply a (fun _ => 0) i
  intro h
  apply no_three_cosets (b 5) (b 7) (b 35)
  intro x hx
  obtain ⟨i,hi⟩ := h x hx
  have hi' : x ∈ coset (m i) (b (m i)).val := by rw [hb]; exact hi
  have hd := divisor35_data ⟨m i,Nat.mem_divisors.mpr ⟨hdiv i,by decide⟩⟩ (h1 i)
  change m i = 5 ∨ m i = 7 ∨ m i = 35 at hd
  simp only [Finset.mem_union]
  rcases hd with hd | hd | hd
  · exact Or.inl (Or.inl (by simpa only [hd] using hi'))
  · exact Or.inl (Or.inr (by simpa only [hd] using hi'))
  · exact Or.inr (by simpa only [hd] using hi')

def normalize (a : ℤ) : Fin 35 := ⟨(a : ZMod 35).val, ZMod.val_lt _⟩

lemma normalized_hit (m : ℕ) (hm : m ∣ 35) (x : Fin 35) (a : ℤ)
    (h : (m : ℤ) ∣ (x.val : ℤ)-a) : x ∈ coset m (normalize a).val := by
  have hb : (35 : ℤ) ∣ a-((normalize a).val : ℤ) := by
    apply Int.modEq_iff_dvd.mp
    change ((a : ZMod 35).val : ℤ) % 35 = a % 35
    rw [ZMod.val_intCast]
    simp
  have hm' : (m : ℤ) ∣ (35 : ℤ) := by exact_mod_cast hm
  have hh : (m : ℤ) ∣ (x.val : ℤ)-((normalize a).val : ℤ) := by
    convert dvd_add h (hm'.trans hb) using 1
    ring
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Nat.modEq_iff_dvd.mpr hh).symm⟩

/-- Fully arithmetic version, with unrestricted integer residues. -/
theorem no_strict_arithmetic_preservation {I : Type*} (m : I → ℕ) (a : I → ℤ)
    (hinj : Function.Injective m) (hdiv : ∀ i, m i ∣ 35) (h1 : ∀ i, 1 < m i) :
    ¬ ∀ x ∈ joint, ∃ i, (m i : ℤ) ∣ (x.val : ℤ)-a i := by
  intro h
  apply no_strict_divisor_family m (fun i => normalize (a i)) hinj hdiv h1
  intro x hx
  obtain ⟨i,hi⟩ := h x hx
  exact ⟨i,normalized_hit (m i) (hdiv i) x (a i) hi⟩

#print axioms all_fibers_iff
#print axioms arithmetic_data
#print axioms divisor_closed
#print axioms not_cover
#print axioms mem_joint_iff
#print axioms joint_data
#print axioms no_three_cosets
#print axioms no_strict_divisor_family
#print axioms no_strict_arithmetic_preservation
end Erdos7TopFiberIntersectionExample
