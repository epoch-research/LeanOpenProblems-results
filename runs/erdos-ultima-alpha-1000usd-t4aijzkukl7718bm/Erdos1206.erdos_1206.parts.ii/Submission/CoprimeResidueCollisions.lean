import FormalConjecturesUtil

/-!
Pairwise-coprime cubic collisions simultaneously satisfying any prescribed
congruence to 1 and any prescribed narrow multiplicative band.
This is an arithmetic local result, not a density recurrence theorem.
-/

namespace Erdos1206.CoprimeResidueCollisions
set_option maxHeartbeats 1000000

/-- A cubic family with an additional parameter controlling the relative width. -/
def A (k q : ℕ) : ℕ :=
  (k^3+26*k^2+232*k+657)*q^3+(3*k^2+52*k+232)*q^2+(3*k+26)*q+1
def B (k q : ℕ) : ℕ :=
  (k^3+29*k^2+307*k+1128)*q^3+(3*k^2+58*k+307)*q^2+(3*k+29)*q+1
def C (k q : ℕ) : ℕ :=
  (k^3+31*k^2+347*k+1412)*q^3+(3*k^2+62*k+347)*q^2+(3*k+31)*q+1
def D (k q : ℕ) : ℕ :=
  (k^3+34*k^2+392*k+1583)*q^3+(3*k^2+68*k+392)*q^2+(3*k+34)*q+1

lemma identity (k q : ℕ) : (A k q)^3+(D k q)^3=(B k q)^3+(C k q)^3 := by
  dsimp [A,B,C,D]
  ring

private lemma cubic_coprime (a b c q : ℕ) :
    Nat.Coprime (a*q^3+b*q^2+c*q+1) q := by
  have he : a*q^3+b*q^2+c*q+1=q*(a*q^2+b*q+c)+1 := by ring
  rw [he, Nat.coprime_mul_left_add_left]
  exact Nat.coprime_one_left q

private lemma cubic_mod {m q : ℕ} (hq : m ∣ q) (a b c : ℕ) :
    Nat.ModEq m (a*q^3+b*q^2+c*q+1) 1 := by
  have he : a*q^3+b*q^2+c*q+1=q*(a*q^2+b*q+c)+1 := by ring
  rw [he]
  simp [Nat.ModEq, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hq]

private lemma coprime_of_bezout {a b q r : ℕ} {u v : ℤ}
    (haq : Nat.Coprime a q) (hrq : r ∣ q)
    (hbez : u*(a : ℤ)+v*(b : ℤ)=(r : ℤ)*(q : ℤ)^5) :
    Nat.Coprime a b := by
  apply Nat.coprime_of_dvd
  intro p hp hpa hpb
  have hpr : (p : ℤ) ∣ (r : ℤ)*(q : ℤ)^5 := by
    rw [← hbez]
    exact dvd_add (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hpa) u)
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hpb) v)
  have hpr' : p ∣ r*q^5 := by exact_mod_cast hpr
  have hpq : p ∣ q := (hp.dvd_mul.mp hpr').elim (fun h => h.trans hrq)
    (fun h => hp.dvd_of_dvd_pow h)
  exact hp.not_dvd_one (by simpa [haq.gcd_eq_one] using Nat.dvd_gcd hpa hpq)

/-- The six Bézout certificates have constants dividing 132300. -/
lemma pairwise_coprime {k q : ℕ} (hq : 132300 ∣ q) :
    Nat.Coprime (A k q) (B k q) ∧ Nat.Coprime (A k q) (C k q) ∧
    Nat.Coprime (A k q) (D k q) ∧ Nat.Coprime (B k q) (C k q) ∧
    Nat.Coprime (B k q) (D k q) ∧ Nat.Coprime (C k q) (D k q) := by
  let t : ℤ := ((k : ℤ)+10)*q+1
  have ha : Nat.Coprime (A k q) q := cubic_coprime _ _ _ _
  have hb : Nat.Coprime (B k q) q := cubic_coprime _ _ _ _
  have hc : Nat.Coprime (C k q) q := cubic_coprime _ _ _ _
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · apply coprime_of_bezout ha ((by norm_num : 1050 ∣ 132300).trans hq)
      (u := -t^2+t*q-20*(q : ℤ)^2) (v := t^2-4*t*q+5*(q : ℤ)^2)
    dsimp [A,B,t]
    ring
  · apply coprime_of_bezout ha ((by norm_num : 2940 ∣ 132300).trans hq)
      (u := -t^2+6*t*q-20*(q : ℤ)^2) (v := t^2-11*t*q+40*(q : ℤ)^2)
    dsimp [A,C,t]
    ring
  · apply coprime_of_bezout ha ((by norm_num : 1890 ∣ 132300).trans hq)
      (u := 4*t^2+16*t*q-15*(q : ℤ)^2) (v := -4*t^2+16*t*q+15*(q : ℤ)^2)
    dsimp [A,D,t]
    ring
  · apply coprime_of_bezout hb ((by norm_num : 1260 ∣ 132300).trans hq)
      (u := t^2+t*q-15*(q : ℤ)^2) (v := -t^2+t*q+15*(q : ℤ)^2)
    dsimp [B,C,t]
    ring
  · apply coprime_of_bezout hb ((by norm_num : 2940 ∣ 132300).trans hq)
      (u := -t^2-11*t*q-40*(q : ℤ)^2) (v := t^2+6*t*q+20*(q : ℤ)^2)
    dsimp [B,D,t]
    ring
  · apply coprime_of_bezout hc ((by norm_num : 1050 ∣ 132300).trans hq)
      (u := -t^2-4*t*q-5*(q : ℤ)^2) (v := t^2+t*q+20*(q : ℤ)^2)
    dsimp [C,D,t]
    ring

lemma ordered {k q : ℕ} (hq : 0 < q) :
    q < A k q ∧ A k q < B k q ∧ B k q < C k q ∧ C k q < D k q := by
  dsimp [A,B,C,D]
  constructor
  · ring_nf
    omega
  constructor
  · ring_nf
    omega
  constructor <;> (ring_nf; omega)

lemma narrow (L q : ℕ) : L*D (20*(L+1)) q < (L+1)*A (20*(L+1)) q := by
  dsimp [A,D]
  ring_nf
  omega

/-- Finite congruence restrictions do not prevent narrow, pairwise-coprime
collisions, even arbitrarily far out. This is not recurrence in an arbitrary
dense subset of the progression. -/
theorem coprime_narrow_collision_mod_one (m L N : ℕ) (hm : 0 < m) :
    ∃ a b c d : ℕ, N < a ∧ a < b ∧ b < c ∧ c < d ∧
      a^3+d^3=b^3+c^3 ∧ L*d < (L+1)*a ∧
      Nat.ModEq m a 1 ∧ Nat.ModEq m b 1 ∧ Nat.ModEq m c 1 ∧ Nat.ModEq m d 1 ∧
      Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime a d ∧
      Nat.Coprime b c ∧ Nat.Coprime b d ∧ Nat.Coprime c d := by
  let q := 132300*m*(N+1)
  let k := 20*(L+1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hNq : N ≤ q := by dsimp [q]; nlinarith
  have hqm : m ∣ q := by dsimp [q]; exact dvd_mul_of_dvd_left (dvd_mul_left m 132300) _
  have hqR : 132300 ∣ q := by dsimp [q]; exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  obtain ⟨ha,hab,hbc,hcd⟩ := ordered (k := k) hq
  refine ⟨A k q,B k q,C k q,D k q,hNq.trans_lt ha,hab,hbc,hcd,identity k q,
    narrow L q,?_,?_,?_,?_,pairwise_coprime hqR⟩
  all_goals exact cubic_mod hqm _ _ _

#print axioms identity
#print axioms pairwise_coprime
#print axioms coprime_narrow_collision_mod_one

end Erdos1206.CoprimeResidueCollisions
