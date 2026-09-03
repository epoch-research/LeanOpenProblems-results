import Submission.CubicBaseLocus

/-!
Exact common divisibility by prime powers away from 2 and 3 for primitive
parameters in the cubic parametrization. No density conclusion is asserted.
-/

namespace Erdos1206.CubicBaseLocus

private lemma unit_of_nonzero_mod {p : ℕ} (hp : p.Prime) (k : ℕ) (n : ℤ)
    (hn : (n : ZMod p) ≠ 0) : IsUnit (n : ZMod (p^k)) := by
  apply (ZMod.coe_int_isUnit_iff_isCoprime n (p^k)).mpr
  have hnot : ¬ (p : ℤ) ∣ n := (ZMod.intCast_zmod_eq_zero_iff_dvd n p).not.mp hn
  have hc : IsCoprime (p : ℤ) n :=
    (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hnot
  simpa only [Nat.cast_pow] using (hc.pow_left (m := k))

private lemma locus_suffices {R : Type*} [CommRing R] {a b t : R}
    (h : (t=0 ∧ Q a b=0) ∨ (b=0 ∧ t^2+3*a^2=0) ∨
      (b=2*a ∧ t^2+3*a^2=0)) :
    A a b t=0 ∧ B a b t=0 ∧ C a b t=0 ∧ D a b t=0 := by
  rcases h with ⟨ht,hq⟩ | ⟨hb,hn⟩ | ⟨hb,hn⟩
  · simp [A,B,C,D,ht,hq]
  · subst b
    obtain ⟨ha,hb,hc,hd⟩ := zero_b_factorization a t
    simp [ha,hb,hc,hd,hn]
  · subst b
    obtain ⟨ha,hb,hc,hd⟩ := double_a_factorization a t
    simp [ha,hb,hc,hd,hn]

/-- The three base loci already describe cancellation modulo every prime
power, as long as the parameter vector is primitive at that prime. -/
theorem common_prime_power_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {a b t : ℤ}
    (hprimitive : ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ t)) (k : ℕ) :
    ((p : ℤ)^k ∣ A a b t ∧ (p : ℤ)^k ∣ B a b t ∧
      (p : ℤ)^k ∣ C a b t ∧ (p : ℤ)^k ∣ D a b t) ↔
    (((p : ℤ)^k ∣ t ∧ (p : ℤ)^k ∣ Q a b) ∨
      ((p : ℤ)^k ∣ b ∧ (p : ℤ)^k ∣ t^2+3*a^2) ∨
      ((p : ℤ)^k ∣ 2*a-b ∧ (p : ℤ)^k ∣ t^2+3*a^2)) := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 2 p).not.mpr
    exact fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd)
  have h3 : (3 : ZMod p) ≠ 0 := by
    apply (ZMod.natCast_eq_zero_iff 3 p).not.mpr
    exact fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd)
  have hu2 : IsUnit (2 : ZMod (p^k)) := by
    simpa using unit_of_nonzero_mod hp k 2 (by simpa using h2)
  have hu3 : IsUnit (3 : ZMod (p^k)) := by
    simpa using unit_of_nonzero_mod hp k 3 (by simpa using h3)
  have hu6 : IsUnit (6 : ZMod (p^k)) := by
    convert hu2.mul hu3 using 1 <;> norm_num
  have cast_zero (n : ℤ) : (n : ZMod (p^k))=0 ↔ (p : ℤ)^k ∣ n := by
    simpa only [Nat.cast_pow] using ZMod.intCast_zmod_eq_zero_iff_dvd n (p^k)
  have hpr : ¬ ((a : ZMod p)=0 ∧ (b : ZMod p)=0 ∧ (t : ZMod p)=0) := by
    rintro ⟨ha,hb,ht⟩
    exact hprimitive ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha,
      (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb,
      (ZMod.intCast_zmod_eq_zero_iff_dvd t p).mp ht⟩
  constructor
  · rintro ⟨ha,hb,hc,hd⟩
    by_cases hk : k=0
    · simp [hk]
    have hpk : (p : ℤ) ∣ (p : ℤ)^k := dvd_pow_self _ hk
    have hF : A (a : ZMod p) b t=0 ∧ B (a : ZMod p) b t=0 ∧
        C (a : ZMod p) b t=0 ∧ D (a : ZMod p) b t=0 := by
      constructor
      · simpa [A,Q] using (ZMod.intCast_zmod_eq_zero_iff_dvd (A a b t) p).mpr (hpk.trans ha)
      constructor
      · simpa [B,Q] using (ZMod.intCast_zmod_eq_zero_iff_dvd (B a b t) p).mpr (hpk.trans hb)
      constructor
      · simpa [C,Q] using (ZMod.intCast_zmod_eq_zero_iff_dvd (C a b t) p).mpr (hpk.trans hc)
      · simpa [D,Q] using (ZMod.intCast_zmod_eq_zero_iff_dvd (D a b t) p).mpr (hpk.trans hd)
    have hA : A (a : ZMod (p^k)) b t=0 := by simpa [A,Q] using (cast_zero _).mpr ha
    have hB : B (a : ZMod (p^k)) b t=0 := by simpa [B,Q] using (cast_zero _).mpr hb
    have hC : C (a : ZMod (p^k)) b t=0 := by simpa [C,Q] using (cast_zero _).mpr hc
    have hD : D (a : ZMod (p^k)) b t=0 := by simpa [D,Q] using (cast_zero _).mpr hd
    have hs : (2 : ZMod (p^k))*(t : ZMod (p^k))*((t : ZMod (p^k))^2+3*(a : ZMod (p^k))^2)=0 := by
      rw [← sum_outer,hA,hD]; simp
    have hg : (6 : ZMod (p^k))*(b : ZMod (p^k))*(t : ZMod (p^k))*(2*(a : ZMod (p^k))-(b : ZMod (p^k)))=0 := by
      rw [← pair_sum_difference,hA,hB,hC,hD]; simp
    rcases (common_zero_iff h2 h3 (a : ZMod p) b t).mp hF with
      ⟨ht,hq⟩ | ⟨hb0,hn⟩ | ⟨hb0,hn⟩
    · have ha0 : (a : ZMod p) ≠ 0 := by
        intro ha0
        have hb0 : (b : ZMod p)=0 := by
          dsimp [Q] at hq
          simp only [ha0,zero_pow (by decide : 2 ≠ 0),zero_mul,sub_zero,zero_add] at hq
          exact eq_zero_of_pow_eq_zero hq
        exact hpr ⟨ha0,hb0,ht⟩
      have hN : ((t^2+3*a^2 : ℤ) : ZMod p) ≠ 0 := by
        simpa [ht] using mul_ne_zero h3 (pow_ne_zero 2 ha0)
      have huN := unit_of_nonzero_mod hp k (t^2+3*a^2) hN
      have huN' : IsUnit ((t : ZMod (p^k))^2+3*(a : ZMod (p^k))^2) := by simpa using huN
      have htK : (t : ZMod (p^k))=0 := hu2.mul_right_eq_zero.mp (huN'.mul_left_eq_zero.mp hs)
      have hBQ : (3 : ZMod (p^k))*(a : ZMod (p^k))*Q (a : ZMod (p^k)) b=0 := by
        simpa [B,htK] using hB
      have hQK : Q (a : ZMod (p^k)) b=0 :=
        (hu3.mul (unit_of_nonzero_mod hp k a ha0)).mul_right_eq_zero.mp hBQ
      exact Or.inl ⟨(cast_zero t).mp htK,(cast_zero (Q a b)).mp (by simpa [Q] using hQK)⟩
    · have ht0 : (t : ZMod p) ≠ 0 := by
        intro ht0
        have ha0 : (a : ZMod p)=0 := by
          rw [ht0,zero_pow (by decide : 2 ≠ 0),zero_add] at hn
          exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hn).resolve_left h3)
        exact hpr ⟨ha0,hb0,ht0⟩
      have ha0 : (a : ZMod p) ≠ 0 := by
        intro ha0
        have : (t : ZMod p)^2=0 := by simpa [ha0] using hn
        exact ht0 (eq_zero_of_pow_eq_zero this)
      have huT := unit_of_nonzero_mod hp k t ht0
      have hNK : (t : ZMod (p^k))^2+3*(a : ZMod (p^k))^2=0 :=
        (hu2.mul huT).mul_right_eq_zero.mp hs
      have hnon : ((2*a-b : ℤ) : ZMod p) ≠ 0 := by
        simpa [hb0] using mul_ne_zero h2 ha0
      have huL := unit_of_nonzero_mod hp k (2*a-b) hnon
      have huL' : IsUnit (2*(a : ZMod (p^k))-(b : ZMod (p^k))) := by simpa using huL
      have hbK : (b : ZMod (p^k))=0 :=
        hu6.mul_right_eq_zero.mp (huT.mul_left_eq_zero.mp (huL'.mul_left_eq_zero.mp hg))
      exact Or.inr (Or.inl ⟨(cast_zero b).mp hbK,
        (cast_zero (t^2+3*a^2)).mp (by simpa using hNK)⟩)
    · have ht0 : (t : ZMod p) ≠ 0 := by
        intro ht0
        have ha0 : (a : ZMod p)=0 := by
          rw [ht0,zero_pow (by decide : 2 ≠ 0),zero_add] at hn
          exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hn).resolve_left h3)
        exact hpr ⟨ha0,by simpa [ha0] using hb0,ht0⟩
      have ha0 : (a : ZMod p) ≠ 0 := by
        intro ha0
        have : (t : ZMod p)^2=0 := by simpa [ha0] using hn
        exact ht0 (eq_zero_of_pow_eq_zero this)
      have hbn : (b : ZMod p) ≠ 0 := by rw [hb0]; exact mul_ne_zero h2 ha0
      have huT := unit_of_nonzero_mod hp k t ht0
      have hNK : (t : ZMod (p^k))^2+3*(a : ZMod (p^k))^2=0 :=
        (hu2.mul huT).mul_right_eq_zero.mp hs
      have hLK : 2*(a : ZMod (p^k))-(b : ZMod (p^k))=0 :=
        ((hu6.mul (unit_of_nonzero_mod hp k b hbn)).mul huT).mul_right_eq_zero.mp hg
      exact Or.inr (Or.inr ⟨(cast_zero (2*a-b)).mp (by simpa using hLK),
        (cast_zero (t^2+3*a^2)).mp (by simpa using hNK)⟩)
  · intro h
    have hK : ((t : ZMod (p^k))=0 ∧ Q (a : ZMod (p^k)) b=0) ∨
        ((b : ZMod (p^k))=0 ∧ (t : ZMod (p^k))^2+3*(a : ZMod (p^k))^2=0) ∨
        ((b : ZMod (p^k))=2*(a : ZMod (p^k)) ∧ (t : ZMod (p^k))^2+3*(a : ZMod (p^k))^2=0) := by
      rcases h with ⟨ht,hq⟩ | ⟨hb,hn⟩ | ⟨hb,hn⟩
      · exact Or.inl ⟨(cast_zero t).mpr ht,by simpa [Q] using (cast_zero (Q a b)).mpr hq⟩
      · exact Or.inr (Or.inl ⟨(cast_zero b).mpr hb,by simpa using (cast_zero (t^2+3*a^2)).mpr hn⟩)
      · have hz : 2*(a : ZMod (p^k))-(b : ZMod (p^k))=0 := by
          simpa using (cast_zero (2*a-b)).mpr hb
        exact Or.inr (Or.inr ⟨(sub_eq_zero.mp hz).symm,by simpa using (cast_zero (t^2+3*a^2)).mpr hn⟩)
    obtain ⟨ha,hb,hc,hd⟩ := locus_suffices hK
    exact ⟨(cast_zero (A a b t)).mp (by simpa [A,Q] using ha),
      (cast_zero (B a b t)).mp (by simpa [B,Q] using hb),
      (cast_zero (C a b t)).mp (by simpa [C,Q] using hc),
      (cast_zero (D a b t)).mp (by simpa [D,Q] using hd)⟩

#print axioms common_prime_power_iff

end Erdos1206.CubicBaseLocus
