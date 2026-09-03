import Submission.GapRatioResidues

/-! Local restrictions on reduced gaps. These do not settle Erdős 1206. -/
namespace Erdos1206.UnitGapCongruences

private def Q {R : Type*} [CommSemiring R] (a h : R) : R :=
  (a+h)^2+(a+h)*a+a^2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma four_certificate : ∀ a c g u v : ZMod 4,
    a^2=1 → (a+g*u)^2=1 → c^2=1 → (c+g*v)^2=1 →
    u*Q a (g*u)=v*Q c (g*v) → u=v := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 2048 in
private lemma three_certificate : ∀ a c g u v : ZMod 3,
    a≠0 → a+g*u≠0 → c≠0 → c+g*v≠0 → g≠0 →
    u*Q a (g*u)=v*Q c (g*v) → u=v := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma nine_certificate : ∀ a g u : ZMod 9,
    a^6=1 → g^3=0 → Q a (g*u)=3 := by
  decide +kernel

private lemma odd_square_four {n : ℕ} (hn : Odd n) : (n : ZMod 4)^2=1 := by
  have h : n%4=1 ∨ n%4=3 := by
    rw [Nat.odd_iff] at hn
    omega
  have he : (n : ZMod 4)=(n%4 : ℕ) := (ZMod.natCast_mod n 4).symm
  rw [he]
  rcases h with h | h <;> rw [h] <;> decide

private lemma unit_sixth_nine {n : ℕ} (hn : ¬3∣n) : (n : ZMod 9)^6=1 := by
  have hh : n%3≠0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hn
  have h : n%9=1 ∨ n%9=2 ∨ n%9=4 ∨ n%9=5 ∨ n%9=7 ∨ n%9=8 := by omega
  have he : (n : ZMod 9)=(n%9 : ℕ) := (ZMod.natCast_mod n 9).symm
  rw [he]
  rcases h with h | h | h | h | h | h <;> rw [h] <;> decide

private lemma divisible_cube_nine {n : ℕ} (hn : 3∣n) : (n : ZMod 9)^3=0 := by
  obtain ⟨k,rfl⟩ := hn
  have hz : (3 : ZMod 9)^3=0 := by decide
  simp only [Nat.cast_mul,Nat.cast_ofNat,mul_pow,hz,zero_mul]

/-- For four odd roots, canceling any common positive gap factor leaves
congruent gap numerators modulo four. Coprimality of the numerators is not needed. -/
theorem odd_gap_mod_four {a c g u v : ℕ} (hg : 0<g)
    (ha : Odd a) (hb : Odd (a+g*u)) (hc : Odd c) (hd : Odd (c+g*v))
    (he : (a+g*u)^3+c^3=a^3+(c+g*v)^3) : Nat.ModEq 4 u v := by
  have h := cube_collision_cancel_common_gap hg he
  have hZ : (u : ZMod 4)*Q (a : ZMod 4) ((g : ZMod 4)*u)=(v : ZMod 4)*Q (c : ZMod 4) ((g : ZMod 4)*v) := by
    dsimp [Q]
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ZMod 4)) h
  apply (ZMod.natCast_eq_natCast_iff u v 4).mp
  apply four_certificate _ _ _ _ _ (odd_square_four ha) _ (odd_square_four hc) _ hZ
  · simpa only [Nat.cast_add,Nat.cast_mul] using odd_square_four hb
  · simpa only [Nat.cast_add,Nat.cast_mul] using odd_square_four hd

/-- For four roots prime to three, the canceled gap numerators are congruent
modulo three. The case where the gap factor is divisible by three requires
working modulo nine before canceling. -/
theorem unit_gap_mod_three {a c g u v : ℕ} (hg : 0<g)
    (ha : ¬3∣a) (hb : ¬3∣a+g*u) (hc : ¬3∣c) (hd : ¬3∣c+g*v)
    (he : (a+g*u)^3+c^3=a^3+(c+g*v)^3) : Nat.ModEq 3 u v := by
  have h := cube_collision_cancel_common_gap hg he
  by_cases hg3 : 3∣g
  · have hZ : (u : ZMod 9)*Q (a : ZMod 9) ((g : ZMod 9)*u)=(v : ZMod 9)*Q (c : ZMod 9) ((g : ZMod 9)*v) := by
      dsimp [Q]
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ => (n : ZMod 9)) h
    rw [nine_certificate _ _ _ (unit_sixth_nine ha) (divisible_cube_nine hg3),
      nine_certificate _ _ _ (unit_sixth_nine hc) (divisible_cube_nine hg3)] at hZ
    have hmod : Nat.ModEq 9 (u*3) (v*3) :=
      (ZMod.natCast_eq_natCast_iff (u*3) (v*3) 9).mp (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hZ)
    simpa using Nat.ModEq.cancel_right_div_gcd (by norm_num : 0<9) hmod
  · have hZ : (u : ZMod 3)*Q (a : ZMod 3) ((g : ZMod 3)*u)=(v : ZMod 3)*Q (c : ZMod 3) ((g : ZMod 3)*v) := by
      dsimp [Q]
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow] using
        congrArg (fun n : ℕ => (n : ZMod 3)) h
    have hunit (n : ℕ) (hn : ¬3∣n) : (n : ZMod 3)≠0 :=
      (ZMod.natCast_eq_zero_iff n 3).not.mpr hn
    apply (ZMod.natCast_eq_natCast_iff u v 3).mp
    apply three_certificate _ _ _ _ _ (hunit a ha) _ (hunit c hc) _ (hunit g hg3) hZ
    · simpa only [Nat.cast_add,Nat.cast_mul] using hunit (a+g*u) hb
    · simpa only [Nat.cast_add,Nat.cast_mul] using hunit (c+g*v) hd

/-- On the source prime to six, every reduced gap difference is divisible
by twelve, irrespective of the size of the common gap factor. -/
theorem coprime_six_gap_mod_twelve {a c g u v : ℕ} (hg : 0<g)
    (ha : Nat.Coprime a 6) (hb : Nat.Coprime (a+g*u) 6)
    (hc : Nat.Coprime c 6) (hd : Nat.Coprime (c+g*v) 6)
    (he : (a+g*u)^3+c^3=a^3+(c+g*v)^3) : Nat.ModEq 12 u v := by
  have hodd (n : ℕ) (hn : Nat.Coprime n 6) : Odd n := by
    have hh : ¬2∣n := by
      intro h
      have : 2∣Nat.gcd n 6 := Nat.dvd_gcd h (by norm_num)
      rw [hn.gcd_eq_one] at this
      norm_num at this
    rw [Nat.odd_iff]
    rw [Nat.dvd_iff_mod_eq_zero] at hh
    omega
  have hunit (n : ℕ) (hn : Nat.Coprime n 6) : ¬3∣n := by
    intro h
    have : 3∣Nat.gcd n 6 := Nat.dvd_gcd h (by norm_num)
    rw [hn.gcd_eq_one] at this
    norm_num at this
  have h4 := odd_gap_mod_four hg (hodd _ ha) (hodd _ hb) (hodd _ hc) (hodd _ hd) he
  have h3 := unit_gap_mod_three hg (hunit _ ha) (hunit _ hb) (hunit _ hc) (hunit _ hd) he
  exact (Nat.modEq_and_modEq_iff_modEq_mul (by norm_num : Nat.Coprime 3 4)).mp ⟨h3,h4⟩

#print axioms odd_gap_mod_four
#print axioms unit_gap_mod_three
#print axioms coprime_six_gap_mod_twelve
end Erdos1206.UnitGapCongruences
