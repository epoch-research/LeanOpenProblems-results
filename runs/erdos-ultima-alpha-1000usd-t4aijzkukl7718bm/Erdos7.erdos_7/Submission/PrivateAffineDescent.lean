import Submission.ArithmeticReduction

/-!
Affine restrictions based at a private point have no active unit modulus,
provided the line leaves that point's class. Distinctness still needs a separate
hypothesis. The finite control below is a partial family, not an odd cover.
-/
namespace Erdos7PrivateAffineDescent
open Erdos7Reduction
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The period induced by the substitution `z = x + d*t`. -/
def reduced (m d : ℕ) : ℕ := m / m.gcd d

def Active {I : Type*} (m : I → ℕ) (a : I → ℤ) (x : ℤ) (d : ℕ) (i : I) : Prop :=
  ∃ t : ℤ, (m i : ℤ) ∣ x + (d : ℤ)*t - a i

lemma reduced_mul_iff (m d : ℕ) (hm : 0 < m) (z : ℤ) :
    (m : ℤ) ∣ (d : ℤ)*z ↔ (reduced m d : ℤ) ∣ z := by
  let g := m.gcd d
  have hg : 0 < g := Nat.gcd_pos_of_pos_left d hm
  have hgm : g ∣ m := Nat.gcd_dvd_left m d
  have hgd : g ∣ d := Nat.gcd_dvd_right m d
  have hm' : (m : ℤ) = (g : ℤ)*(m/g : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hgm).symm
  have hd' : (d : ℤ) = (g : ℤ)*(d/g : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel' hgd).symm
  have hc : IsCoprime (m/g : ℤ) (d/g : ℤ) :=
    (Nat.coprime_div_gcd_div_gcd hg).isCoprime
  change (m : ℤ) ∣ (d : ℤ)*z ↔ ((m/g : ℕ) : ℤ) ∣ z
  rw [hm',hd',mul_assoc,Int.mul_dvd_mul_iff_left (by exact_mod_cast hg.ne')]
  exact ⟨hc.dvd_of_dvd_mul_left, fun h => dvd_mul_of_dvd_right h _⟩

lemma fiber_iff (m d : ℕ) (hm : 0 < m) (a x b : ℤ)
    (hb : (m : ℤ) ∣ x+(d : ℤ)*b-a) (t : ℤ) :
    (m : ℤ) ∣ x+(d : ℤ)*t-a ↔ (reduced m d : ℤ) ∣ t-b := by
  rw [← reduced_mul_iff m d hm]
  constructor
  · intro ht
    convert dvd_sub ht hb using 1 <;> ring
  · intro ht
    convert dvd_add ht hb using 1 <;> ring

lemma reduced_eq_one_iff (m d : ℕ) (hm : 0 < m) :
    reduced m d = 1 ↔ m ∣ d := by
  unfold reduced
  rw [Nat.div_eq_iff_eq_mul_left (Nat.gcd_pos_of_pos_left d hm) (Nat.gcd_dvd_left m d),
    one_mul,eq_comm,Nat.gcd_eq_left_iff_dvd]

/-- A unit pullback would contain both endpoints, and hence would be the
private point's class. Leaving that class rules it out. -/
theorem active_nonunit {I : Type*} (m : I → ℕ) (a : I → ℤ) (x : ℤ) (d : ℕ)
    (i : I) (hx : ∀ j, (m j : ℤ) ∣ x-a j ↔ j=i)
    (hy : ¬ (m i : ℤ) ∣ x+(d : ℤ)-a i)
    (j : I) (hm : 0 < m j) (hj : Active m a x d j) : reduced (m j) d ≠ 1 := by
  intro he
  have hd : (m j : ℤ) ∣ (d : ℤ) := Int.natCast_dvd_natCast.mpr
    ((reduced_eq_one_iff (m j) d hm).mp he)
  obtain ⟨t,ht⟩ := hj
  have hbase : (m j : ℤ) ∣ x-a j := by
    convert dvd_sub ht (dvd_mul_of_dvd_left hd t) using 1 <;> ring
  have hji := (hx j).mp hbase
  subst j
  apply hy
  convert dvd_add hbase hd using 1 <;> ring

lemma reduced_pos (m d : ℕ) (hm : 0 < m) : 0 < reduced m d :=
  Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m d))
    (Nat.gcd_pos_of_pos_left d hm)

lemma reduced_dvd (m d : ℕ) : reduced m d ∣ m :=
  Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m d)

lemma reduced_period (m N d : ℕ) (hm : 0 < m) (hmN : m ∣ N) :
    reduced m d ∣ reduced N d := by
  have hN : N ∣ d * reduced N d := by
    have hd := Nat.gcd_dvd_right N d
    have hn := Nat.gcd_dvd_left N d
    obtain ⟨k,hk⟩ := hd
    refine ⟨k,?_⟩
    calc
      d * reduced N d = (N.gcd d * k) * (N / N.gcd d) :=
        congrArg (fun z => z * reduced N d) hk
      _ = (N.gcd d * (N / N.gcd d)) * k := by ring
      _ = N * k := by rw [Nat.mul_div_cancel' hn]
  have h := (reduced_mul_iff m d hm (reduced N d)).mp
    (by exact_mod_cast hmN.trans hN)
  exact Int.natCast_dvd_natCast.mp h

/-- A collision-free private-point restriction gives an actual smaller odd
strict arithmetic cover. Oddness and minimality are not hidden in the lemma. -/
theorem cover_of_private_line {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hm : ∀ i, 1 < m i ∧ Odd (m i))
    (hc : ∀ z : ℤ, ∃ i, (m i : ℤ) ∣ z-a i)
    (N d : ℕ) (hN : 0 < N) (hmN : ∀ i, m i ∣ N) (x : ℤ) (i : I)
    (hx : ∀ j, (m j : ℤ) ∣ x-a j ↔ j=i)
    (hy : ¬ (m i : ℤ) ∣ x+(d : ℤ)-a i)
    (hinj : ∀ j k, Active m a x d j → Active m a x d k →
      reduced (m j) d = reduced (m k) d → j=k) :
    HasOddArithmeticCover (reduced N d) (Fintype.card I) := by
  classical
  let J := {j : I // Active m a x d j}
  let n (j : J) := reduced (m j.val) d
  let b (j : J) : ℤ := Classical.choose j.property
  have hb (j : J) : (m j.val : ℤ) ∣ x+(d : ℤ)*b j-a j.val :=
    Classical.choose_spec j.property
  refine ⟨reduced_pos N d hN,J,inferInstance,n,b,?_,?_,?_,?_,
    Fintype.card_subtype_le _⟩
  · intro j k he
    apply Subtype.ext
    exact hinj j.val k.val j.property k.property he
  · intro j
    have hp := reduced_pos (m j.val) d (by have := (hm j.val).1; omega)
    have hne := active_nonunit m a x d i hx hy j.val
      (by have := (hm j.val).1; omega) j.property
    exact ⟨by dsimp [n]; omega,(hm j.val).2.of_dvd_nat (reduced_dvd _ _)⟩
  · intro t
    obtain ⟨j,hj⟩ := hc (x+(d : ℤ)*t)
    let k : J := ⟨j,t,hj⟩
    exact ⟨k,(fiber_iff (m j) d (by have := (hm j).1; omega)
      (a j) x (b k) (hb k) t).mp hj⟩
  · intro j
    exact reduced_period _ _ _ (by have := (hm j.val).1; omega) (hmN j.val)

/-- There is no unit exception in this private-point collision criterion. -/
theorem private_line_collision {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hm : ∀ i, 1 < m i ∧ Odd (m i))
    (hc : ∀ z : ℤ, ∃ i, (m i : ℤ) ∣ z-a i)
    (N d : ℕ) (hN : 0 < N) (hmN : ∀ i, m i ∣ N) (x : ℤ) (i : I)
    (hx : ∀ j, (m j : ℤ) ∣ x-a j ↔ j=i)
    (hy : ¬ (m i : ℤ) ∣ x+(d : ℤ)-a i)
    (hno : ¬ HasOddArithmeticCover (reduced N d) (Fintype.card I)) :
    ∃ j k, j ≠ k ∧ Active m a x d j ∧ Active m a x d k ∧
      reduced (m j) d = reduced (m k) d := by
  by_contra! h
  apply hno
  apply cover_of_private_line m a hm hc N d hN hmN x i hx hy
  intro j k hj hk he
  by_contra hne
  exact h j k hne hj hk he

section Control

/-- A divisor-closed strict PARTIAL family of common odd period315. -/
def modulus : Fin 10 → ℕ := ![3,5,9,15,45,7,21,35,63,105]
def residue : Fin 10 → ℤ := ![1,1,6,12,39,0,8,8,36,15]
def point : Fin 10 → ℤ := ![22,246,204,57,309,0,29,183,99,120]
def phase : Fin 10 → ℤ := ![0,0,2,8,44,0,1,1,5,2]

lemma arithmetic_data : Function.Injective modulus ∧
    (∀ i, 1 < modulus i ∧ Odd (modulus i) ∧ modulus i ∣ 315) ∧
    (∀ i j, (modulus j : ℤ) ∣ point i-residue j ↔ j=i) ∧
    (∀ i, ¬ (modulus i : ℤ) ∣ 2-residue i) := by
  decide +kernel

lemma divisor_data : ∀ i : Fin 10, ∀ d : ↥(modulus i).divisors,
    1 < d.val → ∃ j, modulus j=d.val := by decide +kernel

theorem divisor_closed (i : Fin 10) (d : ℕ) (hd : d ∣ modulus i) (h1 : 1 < d) :
    ∃ j, modulus j=d :=
  divisor_data i ⟨d,Nat.mem_divisors.mpr ⟨hd,by have := (arithmetic_data.2.1 i).1; omega⟩⟩ h1

lemma phase_hit : ∀ i : Fin 10, i ≠ 5 →
    (modulus i : ℤ) ∣ 1+7*phase i-residue i := by decide +kernel

lemma phase_cover : ∀ t : Fin 45, ∃ i : Fin 10,
    i ≠ 5 ∧ (reduced (modulus i) 7 : ℤ) ∣ (t.val : ℤ)-phase i := by
  decide +kernel

lemma effective_data :
    (∀ i : Fin 10, i ≠ 5 → 1 < reduced (modulus i) 7 ∧
      Odd (reduced (modulus i) 7) ∧ reduced (modulus i) 7 ∣ 45) ∧
    (∀ i j k : Fin 10, i ≠ 5 → j ≠ 5 → k ≠ 5 →
      reduced (modulus i) 7 = reduced (modulus j) 7 →
      reduced (modulus j) 7 = reduced (modulus k) 7 → i=j ∨ i=k ∨ j=k) ∧
    reduced (modulus 0) 7 = reduced (modulus 6) 7 := by
  decide +kernel

lemma inactive_five : ¬ Active modulus residue 1 7 (5 : Fin 10) := by
  rintro ⟨t,ht⟩
  change (7 : ℤ) ∣ 1+7*t-0 at ht
  simp only [sub_zero] at ht
  have hh : (7 : ℤ) ∣ 1 := by
    convert dvd_sub ht (dvd_mul_right (7 : ℤ) t) using 1 <;> ring
  norm_num at hh

lemma active_iff (i : Fin 10) : Active modulus residue 1 7 i ↔ i ≠ 5 := by
  constructor
  · intro hi he
    subst i
    exact inactive_five hi
  · intro hi
    exact ⟨phase i,by simpa using phase_hit i hi⟩

/-- The whole affine line is covered. The original integer family is not. -/
theorem line_covered : ∀ t : ℤ, ∃ i : Fin 10,
    (modulus i : ℤ) ∣ 1+7*t-residue i := by
  intro t
  let r : Fin 45 := ⟨(t % 45).toNat,by
    have h0 := Int.emod_nonneg t (by norm_num : (45 : ℤ) ≠ 0)
    have h1 := Int.emod_lt_of_pos t (by norm_num : (0 : ℤ) < 45)
    omega⟩
  obtain ⟨i,hi,hr⟩ := phase_cover r
  have her : (r.val : ℤ) = t % 45 := by
    dsimp [r]
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  rw [her] at hr
  have hdiff : (45 : ℤ) ∣ t-t % 45 := by
    refine ⟨t/45,?_⟩
    linarith [Int.emod_add_ediv t 45]
  have hdiv : (reduced (modulus i) 7 : ℤ) ∣ t-phase i := by
    have hh : (reduced (modulus i) 7 : ℤ) ∣ t-t % 45 :=
      (Int.natCast_dvd_natCast.mpr (effective_data.1 i hi).2.2).trans hdiff
    convert dvd_add hh hr using 1 <;> ring
  refine ⟨i,?_⟩
  exact (fiber_iff (modulus i) 7 (by have := (arithmetic_data.2.1 i).1; omega)
    (residue i) 1 (phase i) (by simpa using phase_hit i hi) t).mpr hdiv

lemma private_endpoints :
    (∀ j : Fin 10, (modulus j : ℤ) ∣ 22-residue j ↔ j=0) ∧
    (∀ j : Fin 10, (modulus j : ℤ) ∣ 29-residue j ↔ j=6) := by
  decide +kernel

lemma shifted_line_covered : ∀ t : ℤ, ∃ i : Fin 10,
    (modulus i : ℤ) ∣ 22+7*t-residue i := by
  intro t
  obtain ⟨i,hi⟩ := line_covered (t+3)
  exact ⟨i,by convert hi using 1 <;> ring⟩

theorem control_not_cover : ¬ ∀ z : ℤ, ∃ i : Fin 10,
    (modulus i : ℤ) ∣ z-residue i := by
  intro hc
  obtain ⟨i,hi⟩ := hc 2
  exact arithmetic_data.2.2.2 i hi

end Control
#print axioms reduced_mul_iff
#print axioms active_nonunit
#print axioms cover_of_private_line
#print axioms private_line_collision
#print axioms arithmetic_data
#print axioms divisor_closed
#print axioms line_covered
#print axioms effective_data
#print axioms private_endpoints
#print axioms control_not_cover
end Erdos7PrivateAffineDescent
