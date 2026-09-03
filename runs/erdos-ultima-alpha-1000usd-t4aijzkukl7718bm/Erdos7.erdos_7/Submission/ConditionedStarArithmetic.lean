import Submission.ConditionedStarPolynomial

/-!
Divisor-closed arithmetic realization of the conditioned star.
The family has private points and a hole; it is NOT a covering system.
-/
namespace Erdos7ConditionedStarArithmetic
open scoped BigOperators
open Erdos7ConditionedStarPolynomial
set_option maxHeartbeats 2000000

abbrev Index (s : Finset Nat.Primes) := Fin 3 ⊕ (Fin 4 × s)
def baseDiv : Fin 4 → ℕ := ![1,3,5,15]
def baseRes : Fin 4 → ℕ := ![0,1,1,2]
def primeRes : Fin 4 → ℕ := ![0,2,3,1]
def smallMod : Fin 3 → ℕ := ![3,5,15]
def smallRes : Fin 3 → ℕ := ![0,0,1]

lemma base_properties (j : Fin 4) : 0 < baseDiv j ∧ baseDiv j ≤ 15 ∧
    baseDiv j ∣ 15 ∧ Odd (baseDiv j) := by fin_cases j <;> decide
lemma small_properties (j : Fin 3) : 1 < smallMod j ∧ smallMod j ≤ 15 ∧
    smallMod j ∣ 15 ∧ Odd (smallMod j) := by fin_cases j <;> decide
lemma base_injective : Function.Injective baseDiv := by decide +kernel
lemma small_injective : Function.Injective smallMod := by decide +kernel

def modulus (s : Finset Nat.Primes) : Index s → ℕ
  | Sum.inl j => smallMod j
  | Sum.inr (j,p) => baseDiv j * (p.val : ℕ)

lemma coprime_fifteen (p : Nat.Primes) (hp : 15 < (p : ℕ)) :
    Nat.Coprime 15 (p : ℕ) := by
  apply Nat.Coprime.symm
  apply p.property.coprime_iff_not_dvd.mpr
  intro h
  have := Nat.le_of_dvd (by decide : 0 < (15 : ℕ)) h
  omega

def residue (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ)) : Index s → ℕ
  | Sum.inl j => smallRes j
  | Sum.inr (j,p) => (Nat.chineseRemainder (coprime_fifteen p.val (hs p.val p.property))
      (baseRes j) (primeRes j)).val

lemma modulus_injective (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ)) :
    Function.Injective (modulus s) := by
  intro i k h
  cases i with
  | inl i =>
      cases k with
      | inl k => exact congrArg Sum.inl (small_injective h)
      | inr k =>
          rcases k with ⟨j,p⟩
          have hp := hs p.val p.property
          have hb := base_properties j
          have hi := small_properties i
          change smallMod i = baseDiv j * (p.val : ℕ) at h
          have hle : (p.val : ℕ) ≤ baseDiv j * (p.val : ℕ) := Nat.le_mul_of_pos_left _ hb.1
          omega
  | inr i =>
      rcases i with ⟨j,p⟩
      cases k with
      | inl k =>
          have hp := hs p.val p.property
          have hb := base_properties j
          have hi := small_properties k
          change baseDiv j * (p.val : ℕ) = smallMod k at h
          have hle : (p.val : ℕ) ≤ baseDiv j * (p.val : ℕ) := Nat.le_mul_of_pos_left _ hb.1
          omega
      | inr k =>
          rcases k with ⟨l,q⟩
          change baseDiv j * (p.val : ℕ) = baseDiv l * (q.val : ℕ) at h
          have hd : (p.val : ℕ) ∣ baseDiv l * (q.val : ℕ) := h ▸ dvd_mul_left _ _
          have he : p=q := by
            rcases p.val.property.dvd_mul.mp hd with hd | hd
            · have hle := Nat.le_of_dvd (base_properties l).1 hd
              have hp := hs p.val p.property
              have hb := (base_properties l).2.1
              omega
            · exact Subtype.ext (Subtype.ext ((Nat.dvd_prime q.val.property).mp hd |>.resolve_left p.val.property.ne_one))
          subst q
          have hj : j=l := base_injective (Nat.mul_right_cancel p.val.property.pos h)
          subst l
          rfl

lemma odd_nontrivial (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ))
    (i : Index s) : Odd (modulus s i) ∧ 1 < modulus s i := by
  cases i with
  | inl j => exact ⟨(small_properties j).2.2.2, (small_properties j).1⟩
  | inr jp =>
      rcases jp with ⟨j,p⟩
      have hp := hs p.val p.property
      have ho := p.val.property.odd_of_ne_two (by omega : (p.val : ℕ) ≠ 2)
      refine ⟨(base_properties j).2.2.2.mul ho, ?_⟩
      have hle := Nat.le_mul_of_pos_left (p.val : ℕ) (base_properties j).1
      change 1 < baseDiv j * (p.val : ℕ)
      omega

lemma modulus_prime_iff (s : Finset Nat.Primes) (i : Index s) :
    (modulus s i).Prime ↔ i=Sum.inl 0 ∨ i=Sum.inl 1 ∨ ∃ p : s, i=Sum.inr (0,p) := by
  cases i with
  | inl j => fin_cases j <;> norm_num [modulus, smallMod] <;> simp
  | inr jp =>
      rcases jp with ⟨j,p⟩
      fin_cases j <;> simp [modulus, baseDiv, Nat.prime_mul_iff,
        p.val.property, p.val.property.ne_one]

lemma divisor15_cases {d : ℕ} (hd : d ∣ 15) : d=1 ∨ d=3 ∨ d=5 ∨ d=15 := by
  have hle := Nat.le_of_dvd (by decide : 0 < (15 : ℕ)) hd
  interval_cases d <;> omega

lemma base_divisor_index {d : ℕ} (hd : d ∣ 15) : ∃ j, baseDiv j=d := by
  rcases divisor15_cases hd with rfl | rfl | rfl | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩

lemma small_divisor_index {d : ℕ} (hd : d ∣ 15) (hgt : 1 < d) : ∃ j, smallMod j=d := by
  rcases divisor15_cases hd with h | rfl | rfl | rfl
  · omega
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩

lemma divisor_closed (s : Finset Nat.Primes) (i : Index s) (d : ℕ)
    (hd : 1 < d) (hdiv : d ∣ modulus s i) : ∃ j, modulus s j=d := by
  cases i with
  | inl j =>
      obtain ⟨k,hk⟩ := small_divisor_index (hdiv.trans (small_properties j).2.2.1) hd
      exact ⟨Sum.inl k,hk⟩
  | inr jp =>
      rcases jp with ⟨j,p⟩
      change d ∣ baseDiv j * (p.val : ℕ) at hdiv
      by_cases hp : (p.val : ℕ) ∣ d
      · obtain ⟨a,rfl⟩ := hp
        have ha : a ∣ baseDiv j := by
          rw [Nat.mul_comm (baseDiv j)] at hdiv
          exact (Nat.mul_dvd_mul_iff_left p.val.property.pos).mp hdiv
        obtain ⟨k,hk⟩ := base_divisor_index (ha.trans (base_properties j).2.2.1)
        refine ⟨Sum.inr (k,p), ?_⟩
        change baseDiv k * (p.val : ℕ) = (p.val : ℕ)*a
        rw [hk, Nat.mul_comm]
      · have hc : Nat.Coprime d (p.val : ℕ) := (p.val.property.coprime_iff_not_dvd.mpr hp).symm
        have ha := hc.dvd_of_dvd_mul_right hdiv
        obtain ⟨k,hk⟩ := small_divisor_index (ha.trans (base_properties j).2.2.1) hd
        exact ⟨Sum.inl k,hk⟩

lemma exists_coordinates (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ))
    (c₃ c₅ : ℕ) (b : Nat.Primes → ℕ) :
    ∃ x : ℕ, Nat.ModEq 3 x c₃ ∧ Nat.ModEq 5 x c₅ ∧
      ∀ p ∈ s, Nat.ModEq (p : ℕ) x (b p) := by
  classical
  let five : Nat.Primes := ⟨5, by decide⟩
  have ht : ∀ p ∈ insert five s, 3 < (p : ℕ) := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · decide
    · have := hs p hp; omega
  obtain ⟨x,h₃,hx⟩ := Erdos7StaticShearerBarrier.exists_coordinates (insert five s) ht c₃
    (fun p => if p=five then c₅ else b p)
  refine ⟨x,h₃,?_,?_⟩
  · simpa using hx five (Finset.mem_insert_self _ _)
  · intro p hp
    have hn : p ≠ five := by
      intro h; have hh := hs p hp; rw [h] at hh; change 15 < 5 at hh; omega
    simpa [hn] using hx p (Finset.mem_insert_of_mem hp)

lemma modEq_source {n x c r : ℕ} (hc : Nat.ModEq n x c) :
    Nat.ModEq n x r ↔ Nat.ModEq n c r :=
  ⟨fun h => hc.symm.trans h, fun h => hc.trans h⟩
lemma modEq_target {n x c r : ℕ} (hr : Nat.ModEq n r c) :
    Nat.ModEq n x r ↔ Nat.ModEq n x c :=
  ⟨fun h => h.trans hr, fun h => h.trans hr.symm⟩

def coordinateHit (s : Finset Nat.Primes) (i : Index s) (c₃ c₅ : ℕ)
    (b : Nat.Primes → ℕ) : Prop :=
  match i with
  | Sum.inl j => (![Nat.ModEq 3 c₃ 0, Nat.ModEq 5 c₅ 0,
      Nat.ModEq 3 c₃ 1 ∧ Nat.ModEq 5 c₅ 1] : Fin 3 → Prop) j
  | Sum.inr (j,p) => (![Nat.ModEq (p.val : ℕ) (b p.val) 0,
      Nat.ModEq 3 c₃ 1 ∧ Nat.ModEq (p.val : ℕ) (b p.val) 2,
      Nat.ModEq 5 c₅ 1 ∧ Nat.ModEq (p.val : ℕ) (b p.val) 3,
      Nat.ModEq 3 c₃ 2 ∧ Nat.ModEq 5 c₅ 2 ∧ Nat.ModEq (p.val : ℕ) (b p.val) 1] : Fin 4 → Prop) j

lemma membership_coordinates (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ))
    (x c₃ c₅ : ℕ) (b : Nat.Primes → ℕ) (h₃ : Nat.ModEq 3 x c₃)
    (h₅ : Nat.ModEq 5 x c₅) (hb : ∀ p ∈ s, Nat.ModEq (p : ℕ) x (b p)) (i : Index s) :
    Nat.ModEq (modulus s i) x (residue s hs i) ↔ coordinateHit s i c₃ c₅ b := by
  have h15 (r : ℕ) : Nat.ModEq 15 x r ↔ Nat.ModEq 3 c₃ r ∧ Nat.ModEq 5 c₅ r := by
    rw [show 15=3*5 from rfl, ← Nat.modEq_and_modEq_iff_modEq_mul (by decide : Nat.Coprime 3 5)]
    exact and_congr (modEq_source h₃) (modEq_source h₅)
  cases i with
  | inl j =>
      fin_cases j
      · exact modEq_source h₃
      · exact modEq_source h₅
      · exact h15 1
  | inr jp =>
      rcases jp with ⟨j,p⟩
      have hc := coprime_fifteen p.val (hs p.val p.property)
      have hr := (Nat.chineseRemainder hc (baseRes j) (primeRes j)).property
      change Nat.ModEq (baseDiv j*(p.val : ℕ)) x _ ↔ _
      rw [← Nat.modEq_and_modEq_iff_modEq_mul (hc.of_dvd_left (base_properties j).2.2.1)]
      dsimp only [residue]
      rw [modEq_target (hr.1.of_dvd (base_properties j).2.2.1), modEq_target hr.2,
        modEq_source (hb p.val p.property)]
      fin_cases j
      · simp [baseDiv, baseRes, primeRes, coordinateHit, Nat.ModEq, Nat.mod_one]
      · exact and_congr (modEq_source h₃) Iff.rfl
      · exact and_congr (modEq_source h₅) Iff.rfl
      · exact (and_congr (h15 2) Iff.rfl).trans and_assoc

lemma nat_private (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ))
    (i : Index s) : ∃ x : ℕ, ∀ j, Nat.ModEq (modulus s j) x (residue s hs j) ↔ i=j := by
  classical
  cases i with
  | inl i =>
      let c₃ := (![0,2,1] : Fin 3 → ℕ) i
      let c₅ := (![3,0,1] : Fin 3 → ℕ) i
      obtain ⟨x,h₃,h₅,hp⟩ := exists_coordinates s hs c₃ c₅ (fun _ => 4)
      refine ⟨x, ?_⟩
      intro j
      rw [membership_coordinates s hs x c₃ c₅ (fun _ => 4) h₃ h₅ hp j]
      cases j with
      | inl j => fin_cases i <;> fin_cases j <;> simp [coordinateHit, c₃, c₅, Nat.ModEq]
      | inr jp =>
          rcases jp with ⟨j,p⟩
          have h0 : 0 < (p.val : ℕ) := by have := hs p.val p.property; omega
          have h1 : 1 < (p.val : ℕ) := p.val.property.one_lt
          have h2 : 2 < (p.val : ℕ) := by have := hs p.val p.property; omega
          have h3 : 3 < (p.val : ℕ) := by have := hs p.val p.property; omega
          have h4 : 4 < (p.val : ℕ) := by have := hs p.val p.property; omega
          fin_cases i <;> fin_cases j <;>
            simp [coordinateHit, c₃, c₅, Nat.ModEq, Nat.mod_eq_of_lt h0,
              Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]
  | inr ip =>
      rcases ip with ⟨i,p⟩
      let c₃ := (![2,1,2,2] : Fin 4 → ℕ) i
      let c₅ := (![3,2,1,2] : Fin 4 → ℕ) i
      let b : Nat.Primes → ℕ := fun q => if q=p.val then primeRes i else 4
      obtain ⟨x,h₃,h₅,hp⟩ := exists_coordinates s hs c₃ c₅ b
      refine ⟨x, ?_⟩
      intro j
      rw [membership_coordinates s hs x c₃ c₅ b h₃ h₅ hp j]
      cases j with
      | inl j => fin_cases i <;> fin_cases j <;> simp [coordinateHit, c₃, c₅, Nat.ModEq]
      | inr jq =>
          rcases jq with ⟨j,q⟩
          have h0 : 0 < (q.val : ℕ) := by have := hs q.val q.property; omega
          have h1 : 1 < (q.val : ℕ) := q.val.property.one_lt
          have h2 : 2 < (q.val : ℕ) := by have := hs q.val q.property; omega
          have h3 : 3 < (q.val : ℕ) := by have := hs q.val q.property; omega
          have h4 : 4 < (q.val : ℕ) := by have := hs q.val q.property; omega
          by_cases he : p=q
          · subst q
            fin_cases i <;> fin_cases j <;>
              simp [coordinateHit, c₃, c₅, b, primeRes, Nat.ModEq, Nat.mod_eq_of_lt h0,
                Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3]
          · have hv : q.val ≠ p.val := fun h => he (Subtype.ext h.symm)
            fin_cases i <;> fin_cases j <;>
              simp [coordinateHit, c₃, c₅, b, hv, he, primeRes, Nat.ModEq, Nat.mod_eq_of_lt h0,
                Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]

lemma private_points (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ)) :
    ∀ i : Index s, ∃ x : ℤ, ∀ j,
      (modulus s j : ℤ) ∣ x-(residue s hs j : ℤ) ↔ i=j := by
  intro i
  obtain ⟨x,hx⟩ := nat_private s hs i
  refine ⟨(x : ℤ), ?_⟩
  intro j
  rw [dvd_sub_comm, ← Nat.modEq_iff_dvd]
  exact hx j

lemma exists_uncovered (s : Finset Nat.Primes) (hs : ∀ p ∈ s, 15 < (p : ℕ)) :
    ∃ z : ℤ, ∀ i : Index s, ¬ (modulus s i : ℤ) ∣ z-(residue s hs i : ℤ) := by
  obtain ⟨x,h₃,h₅,hp⟩ := exists_coordinates s hs 2 3 (fun _ => 4)
  refine ⟨(x : ℤ), ?_⟩
  intro i
  rw [dvd_sub_comm, ← Nat.modEq_iff_dvd,
    membership_coordinates s hs x 2 3 (fun _ => 4) h₃ h₅ hp i]
  cases i with
  | inl j => fin_cases j <;> simp [coordinateHit, Nat.ModEq]
  | inr jp =>
      rcases jp with ⟨j,p⟩
      have h4 : 4 < (p.val : ℕ) := by have := hs p.val p.property; omega
      fin_cases j <;> simp [coordinateHit, Nat.ModEq, Nat.mod_eq_of_lt h4]

#print axioms private_points
#print axioms exists_uncovered
#print axioms modulus_injective
#print axioms divisor_closed
#print axioms membership_coordinates
end Erdos7ConditionedStarArithmetic
