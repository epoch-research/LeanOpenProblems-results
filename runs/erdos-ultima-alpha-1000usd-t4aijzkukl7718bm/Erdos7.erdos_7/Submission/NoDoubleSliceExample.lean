import FormalConjecturesUtil

/-! A partial arithmetic family blocking a proposed multiplicity-two ternary
restriction. It has distinct odd divisor-closed moduli and private points,
but an explicit hole. It is NOT a covering system or a disproof of Erdős7. -/
namespace Erdos7NoDoubleSliceExample
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

def modulus : Fin 17 → ℕ := ![3,9,5,15,45,7,21,63,11,33,99,13,39,117,17,51,153]
def residue : Fin 17 → ℤ := ![0,1,20,11,2,49,22,58,77,23,68,52,79,106,17,35,53]
def privatePoint : Fin 17 → ℤ :=
  ![255258,170173,697700,238241,544547,243103,133708,24313,456368,
    247523,38678,719953,366523,13093,520523,205208,655658]
def prime : Fin 5 → ℕ := ![5,7,11,13,17]
def branch : Fin 5 → ℕ := ![2,4,5,7,8]
def phase : Fin 5 → Fin 3 → ℤ :=
  ![![2,1,0],![5,2,6],![8,2,7],![5,8,11],![1,3,5]]
def index (j : Fin 5) (e : Fin 3) : Fin 17 := ⟨2+3*j.val+e.val,by omega⟩

theorem arithmetic_data :
    Function.Injective modulus ∧
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ modulus i ∣ 765765) ∧
    (∀ i j, (modulus j : ℤ) ∣ privatePoint i-residue j ↔ j=i) ∧
    (∀ i, ¬ (modulus i : ℤ) ∣ 85088-residue i) := by
  decide +kernel

lemma bounded_divisor_data :
    ∀ i : Fin 17, ∀ d : Fin 154, 1 < d.val → d.val ∣ modulus i →
      ∃ j, modulus j=d.val := by
  decide +kernel

theorem divisor_closed (i : Fin 17) (d : ℕ) (hd : d ∣ modulus i) (h1 : 1<d) :
    ∃ j, modulus j=d := by
  have hm : ∀ i : Fin 17, modulus i < 154 := by decide +kernel
  have hmi := hm i
  have hp : 0 < modulus i := lt_trans (by omega : 0<1) (arithmetic_data.2.1 i).1
  have hle := Nat.le_of_dvd hp hd
  exact bounded_divisor_data i ⟨d,by omega⟩ h1 hd

lemma slice_data :
    (∀ j, (prime j).Prime ∧ Nat.Coprime (prime j) 9) ∧
    (∀ j e, modulus (index j e) = 3^e.val*prime j) ∧
    (∀ j e, residue (index j e) = branch j+9*phase j e) ∧
    (∀ j, Function.Injective (index j)) ∧
    (∀ j e f, e ≠ f → ¬ (prime j : ℤ) ∣ phase j e-phase j f) ∧
    (∀ r : Fin 9, r.val%3 ≠ 0 → r.val ≠ 1 → ∃ j, branch j=r.val) := by
  decide +kernel

/-- The restriction is an equality of actual arithmetic classes in the
parameter x, not just a count of projected labels. -/
theorem restricted_class (j : Fin 5) (e : Fin 3) (x : ℤ) :
    (modulus (index j e) : ℤ) ∣ 9*x+branch j-residue (index j e) ↔
      (prime j : ℤ) ∣ x-phase j e := by
  rw [slice_data.2.1 j e,slice_data.2.2.1 j e]
  have he : (3^e.val : ℕ) ∣ 9 := by revert e; decide +kernel
  have hez : ((3^e.val : ℕ):ℤ) ∣ 9 := by exact_mod_cast he
  have hc : IsCoprime (prime j : ℤ) 9 := (slice_data.1 j).2.isCoprime
  have hEq : 9*x+(branch j : ℤ)-((branch j : ℤ)+9*phase j e) = 9*(x-phase j e) := by ring
  rw [hEq,Nat.cast_mul]
  constructor
  · intro h
    exact hc.dvd_of_dvd_mul_left ((dvd_mul_left (prime j : ℤ) ((3^e.val : ℕ):ℤ)).trans h)
  · intro h
    obtain ⟨b,hb⟩ := hez
    obtain ⟨c,hc⟩ := h
    rw [hb,hc]
    exact ⟨b*c,by ring⟩

/-- Every residue modulo9 avoiding the two pure classes retains THREE
pairwise different classes with the same nontrivial reduced modulus. -/
theorem every_good_slice_has_triple (r : Fin 9) (h3 : r.val%3 ≠ 0) (h9 : r.val ≠ 1) :
    ∃ j : Fin 5,
      Function.Injective (index j) ∧
      (∀ e f : Fin 3, e ≠ f → ¬ (prime j : ℤ) ∣ phase j e-phase j f) ∧
      (∀ e : Fin 3, ∀ x : ℤ,
        (modulus (index j e) : ℤ) ∣ 9*x+r.val-residue (index j e) ↔
          (prime j : ℤ) ∣ x-phase j e) := by
  obtain ⟨j,hj⟩ := slice_data.2.2.2.2.2 r h3 h9
  refine ⟨j,slice_data.2.2.2.1 j,slice_data.2.2.2.2.1 j,?_⟩
  intro e x
  rw [←hj]
  exact restricted_class j e x

/-- The two hypotheses above exactly mean that the ternary slice avoids
both original pure-power classes. -/
lemma avoids_pure_iff (r : Fin 9) :
    (¬ (3 : ℤ) ∣ r.val) ∧ (¬ (9 : ℤ) ∣ (r.val : ℤ)-1) ↔
      r.val%3 ≠ 0 ∧ r.val ≠ 1 := by
  revert r
  decide +kernel

#print axioms arithmetic_data
#print axioms divisor_closed
#print axioms every_good_slice_has_triple
end Erdos7NoDoubleSliceExample
