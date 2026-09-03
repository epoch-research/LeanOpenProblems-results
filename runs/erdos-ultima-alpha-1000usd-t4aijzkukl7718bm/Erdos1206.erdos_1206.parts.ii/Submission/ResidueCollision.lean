import Submission.SummableDivisorCover

/-!
Explicit cubic collisions in every positive-tail residue class. In particular,
no finite set of forbidden divisors omitting 1 can cover all cubic collisions.
This does not exclude nonperiodic positive-density cube-Sidon root sets, and
it does not exclude infinite summable divisor covers.
-/

namespace Erdos1206.ResidueCollision

def a (m : ℕ) : ℕ := m*(6*m^2+15*m+7)+1
def b (m : ℕ) : ℕ := m*(27*m^2+24*m+8)+1
def c (m : ℕ) : ℕ := m*(45*m^2+36*m+10)+1
def d (m : ℕ) : ℕ := m*(48*m^2+39*m+11)+1

lemma identity (m : ℕ) : a m ^ 3 + d m ^ 3 = b m ^ 3 + c m ^ 3 := by
  dsimp [a,b,c,d]
  ring

lemma ordered {m : ℕ} (hm : 0 < m) :
    0 < a m ∧ a m < b m ∧ b m < c m ∧ c m < d m := by
  dsimp [a,b,c,d]
  refine ⟨by positivity, ?_, ?_, ?_⟩
  all_goals nlinarith [sq_nonneg m]

lemma residue (m : ℕ) :
    a m % m = 1 % m ∧ b m % m = 1 % m ∧
      c m % m = 1 % m ∧ d m % m = 1 % m := by
  simp [a,b,c,d,Nat.add_mod]

lemma residue_of_dvd {q m : ℕ} (hq : q ∣ m) :
    a m % q = 1 % q ∧ b m % q = 1 % q ∧
      c m % q = 1 % q ∧ d m % q = 1 % q := by
  have hm := Nat.mod_eq_zero_of_dvd hq
  simp [a,b,c,d,Nat.add_mod,Nat.mul_mod,hm]

/-- Every residue class, arbitrarily far out, contains a strict positive
cubic collision. The four roots are not an arithmetic progression. -/
theorem collision_in_residue_tail (q r N : ℕ) (hq : 0 < q) :
    ∃ x y z w : ℕ, N < x ∧ x < y ∧ y < z ∧ z < w ∧
      x % q = r % q ∧ y % q = r % q ∧ z % q = r % q ∧ w % q = r % q ∧
      x^3+w^3=y^3+z^3 := by
  let m := q*(N+1)
  let k := r+q
  have hm : 0 < m := Nat.mul_pos hq (by omega)
  have hk : 0 < k := by dsimp [k]; omega
  obtain ⟨ha,hab,hbc,hcd⟩ := ordered hm
  obtain ⟨hra,hrb,hrc,hrd⟩ := residue_of_dvd (dvd_mul_right q (N+1))
  have hres (v : ℕ) (hv : v % q = 1 % q) : (k*v) % q = r % q := by
    rw [Nat.mul_mod,hv,← Nat.mul_mod,mul_one]
    simp [k]
  refine ⟨k*a m,k*b m,k*c m,k*d m,?_,
    Nat.mul_lt_mul_of_pos_left hab hk, Nat.mul_lt_mul_of_pos_left hbc hk,
    Nat.mul_lt_mul_of_pos_left hcd hk,
    hres _ hra,hres _ hrb,hres _ hrc,hres _ hrd,?_⟩
  · have hNm : N < m := by dsimp [m]; nlinarith
    have hma : m ≤ a m := by dsimp [a]; nlinarith [sq_nonneg m]
    exact hNm.trans_le (hma.trans (Nat.le_mul_of_pos_left _ hk))
  · simpa only [mul_pow,← mul_add] using congrArg (fun n : ℕ => k^3*n) (identity m)

/-- A cube-Sidon root set cannot contain an entire tail of any residue class. -/
theorem no_residue_tail {S : Set ℕ}
    (hS : IsSidon ((fun n : ℕ => n^3) '' S))
    (q r N : ℕ) (hq : 0 < q) :
    ¬ (∀ n : ℕ, N < n → n % q = r % q → n ∈ S) := by
  intro h
  obtain ⟨x,y,z,w,hNx,hxy,hyz,hzw,hx,hy,hz,hw,he⟩ :=
    collision_in_residue_tail q r N hq
  have hh := hS
    _ ⟨x,h x hNx hx,rfl⟩ _ ⟨y,h y (by omega) hy,rfl⟩
    _ ⟨w,h w (by omega) hw,rfl⟩ _ ⟨z,h z (by omega) hz,rfl⟩ he
  have hxy3 := Nat.pow_lt_pow_left hxy (by decide : 3 ≠ 0)
  have hxz3 := Nat.pow_lt_pow_left (hxy.trans hyz) (by decide : 3 ≠ 0)
  rcases hh with ⟨hh,_⟩ | ⟨hh,_⟩
  · exact (Nat.ne_of_lt hxy3) hh
  · exact (Nat.ne_of_lt hxz3) hh

/-- Eventual periodicity cannot supply an infinite cube-Sidon root set. -/
theorem finite_of_eventually_periodic {S : Set ℕ}
    (hS : IsSidon ((fun n : ℕ => n^3) '' S)) {q N : ℕ} (hq : 0 < q)
    (hp : ∀ n ≥ N, n ∈ S ↔ n+q ∈ S) : S.Finite := by
  have hsub : S ⊆ Set.Iio N := by
    intro m hm
    by_contra h
    have hNm : N ≤ m := by simpa using h
    have hmem (k : ℕ) : m+q*k ∈ S := by
      induction k with
      | zero => simpa using hm
      | succ k ih =>
        have hh := (hp (m+q*k) (by omega)).mp ih
        simpa only [Nat.mul_succ, Nat.add_assoc] using hh
    apply no_residue_tail hS q m m hq
    intro n hn he
    obtain ⟨k,rfl⟩ := (Nat.modEq_iff_exists_eq_add (show m ≤ n by omega)).mp
      (show Nat.ModEq q m n from he.symm)
    exact hmem k
  exact (Set.finite_Iio N).subset hsub

theorem lowerDensity_zero_of_eventually_periodic {S : Set ℕ}
    (hS : IsSidon ((fun n : ℕ => n^3) '' S)) {q N : ℕ} (hq : 0 < q)
    (hp : ∀ n ≥ N, n ∈ S ↔ n+q ∈ S) : S.lowerDensity = 0 :=
  (Nat.hasDensity_zero_of_finite (finite_of_eventually_periodic hS hq hp)).liminf_eq

/-- Finite divisor covers excluding 1 are impossible. The finite-prefix
covers used in compactness reductions may, of course, grow with the cutoff. -/
theorem no_finite_divisor_cover {B : Set ℕ} (hB : B.Finite) (h1 : 1 ∉ B) :
    ¬ IsCubeDivisorCover B := by
  classical
  intro hc
  let F := hB.toFinset.filter (fun n => 0 < n)
  let m := ∏ n ∈ F, n
  have hm : 0 < m := Finset.prod_pos fun n hn => (Finset.mem_filter.mp hn).2
  obtain ⟨ha,hab,hbc,hcd⟩ := ordered hm
  obtain ⟨p,hp,hpd⟩ := hc (a m) (d m) (b m) (c m)
    ha (ha.trans (hab.trans (hbc.trans hcd))) (ha.trans hab) (ha.trans (hab.trans hbc))
    (identity m) (Nat.ne_of_lt hab) (Nat.ne_of_lt (hab.trans hbc))
  have hp0 : 0 < p := by
    rcases hpd with h | h | h | h
    all_goals
      apply Nat.pos_of_ne_zero
      intro hz
      subst p
      simp only [zero_dvd_iff] at h
      omega
  have hpne : p ≠ 1 := fun he => h1 (he ▸ hp)
  have hp1 : 1 < p := by omega
  have hpF : p ∈ F := Finset.mem_filter.mpr ⟨hB.mem_toFinset.mpr hp,hp0⟩
  have hpm : p ∣ m := Finset.dvd_prod_of_mem (fun n => n) hpF
  obtain ⟨hpa,hpb,hpc,hpd'⟩ := residue_of_dvd hpm
  have hone : 1 % p = 1 := Nat.mod_eq_of_lt hp1
  rcases hpd with h | h | h | h
  all_goals have hh := Nat.mod_eq_zero_of_dvd h; omega

#print axioms collision_in_residue_tail
#print axioms no_residue_tail
#print axioms no_finite_divisor_cover
#print axioms finite_of_eventually_periodic
#print axioms lowerDensity_zero_of_eventually_periodic

end Erdos1206.ResidueCollision
