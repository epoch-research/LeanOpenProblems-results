import Submission.ThreePrimeLocalRoots

/-! A finite dimension-three sieve for two signed prime-neighbor incidences.
The congruence restrictions on the common prime are kept in the estimate. -/
namespace Erdos371.FiniteSieve
open Finset

lemma signed_neighbor_coprime (a k p q : ℕ) (e : ℤ) (he : e.natAbs=1)
    (h : (k : ℤ)*p+e=(a : ℤ)*q) : a.Coprime k := by
  have ha : ((a.gcd k : ℕ) : ℤ) ∣ (a : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left a k)
  have hk : ((a.gcd k : ℕ) : ℤ) ∣ (k : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right a k)
  have hd : ((a.gcd k : ℕ) : ℤ) ∣ e := by
    convert dvd_sub (dvd_mul_of_dvd_left ha (q : ℤ)) (dvd_mul_of_dvd_left hk (p : ℤ)) using 1
    linarith
  have hh : a.gcd k ∣ 1 := by simpa only [he] using Int.natCast_dvd.mp hd
  exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp hh)

lemma signed_neighbor_modEq (a k p q p₀ q₀ : ℕ) (e : ℤ) (he : e.natAbs=1)
    (h : (k : ℤ)*p+e=(a : ℤ)*q) (h₀ : (k : ℤ)*p₀+e=(a : ℤ)*q₀) :
    Nat.ModEq a p p₀ := by
  have hmul : Nat.ModEq a (k*p) (k*p₀) := by
    apply Nat.modEq_iff_dvd.mpr
    refine ⟨(q₀ : ℤ)-q,?_⟩
    push_cast
    nlinarith
  exact hmul.cancel_left_of_coprime (signed_neighbor_coprime a k p q e he h)

noncomputable def threePrimePatternSet (T k l a b z : ℕ) (e d : ℤ) : Finset ℕ := by
  classical
  exact (range T).filter fun p => p.Prime ∧ z<p ∧ ∃ q r : ℕ,
    q.Prime ∧ r.Prime ∧ z<q ∧ z<r ∧
      (k : ℤ)*p+e=(a : ℤ)*q ∧ (l : ℤ)*p+d=(b : ℤ)*r

lemma mem_threePrimePatternSet (T k l a b z p : ℕ) (e d : ℤ) :
    p ∈ threePrimePatternSet T k l a b z e d ↔
      p<T ∧ p.Prime ∧ z<p ∧ ∃ q r : ℕ,
        q.Prime ∧ r.Prime ∧ z<q ∧ z<r ∧
          (k : ℤ)*p+e=(a : ℤ)*q ∧ (l : ℤ)*p+d=(b : ℤ)*r := by
  classical
  simp only [threePrimePatternSet,mem_filter,mem_range]

/-- All prime solutions of two signed incidence equations lie in one
residue class modulo lcm(a,b), when the set is nonempty. -/
lemma threePrimePatternSet_progression (T k l a b z : ℕ) (e d : ℤ)
    (ha : 0<a) (hb : 0<b) (he : e.natAbs=1) (hd : d.natAbs=1)
    (h : (threePrimePatternSet T k l a b z e d).Nonempty) :
    ∃ v<a.lcm b, ∀ p ∈ threePrimePatternSet T k l a b z e d, p%(a.lcm b)=v := by
  obtain ⟨p₀,hp₀⟩ := h
  obtain ⟨_,_,_,q₀,r₀,_,_,_,_,he₀,hd₀⟩ := (mem_threePrimePatternSet T k l a b z p₀ e d).mp hp₀
  refine ⟨p₀%(a.lcm b),Nat.mod_lt _ (Nat.lcm_pos ha hb),?_⟩
  intro p hp
  obtain ⟨_,_,_,q,r,_,_,_,_,hep,hdp⟩ := (mem_threePrimePatternSet T k l a b z p e d).mp hp
  exact Nat.mod_lcm (signed_neighbor_modEq a k p q p₀ q₀ e he hep he₀)
    (signed_neighbor_modEq b l p r p₀ r₀ d hd hdp hd₀)

lemma prime_not_dvd_larger_prime (s p z : ℕ) (hs : s.Prime) (hp : p.Prime)
    (hsz : s ≤ z) (hzp : z<p) : ¬s ∣ p := by
  intro hd
  rcases (Nat.dvd_prime hp).mp hd with h | h
  · exact hs.ne_one h
  · omega

/-- The off-diagonal determinant is bounded uniformly by the two slopes. -/
lemma signed_neighbor_determinant_bound (k l X : ℕ) (e d : ℤ)
    (hk : k ≤ X) (hl : l ≤ X) (he : e.natAbs=1) (hd : d.natAbs=1) :
    ((l : ℤ)*e-k*d).natAbs ≤ 2*X := by
  have h := Int.natAbs_sub_le ((l : ℤ)*e) ((k : ℤ)*d)
  simp only [Int.natAbs_mul,Int.natAbs_natCast,he,hd,mul_one] at h
  omega

/-- For bounded cofactors and slopes, the main term has a cubic logarithmic
saving and the exact progression factor 1/lcm(a,b). No asymptotic prime
pattern formula or signed cancellation is used. -/
theorem threePrimePatternSet_sieve_bound (T k l a b X z : ℕ) (e d : ℤ)
    (hk : k ∈ Icc 1 X) (hl : l ∈ Icc 1 X)
    (ha : a ∈ Icc 1 X) (hb : b ∈ Icc 1 X)
    (hz : 1 ≤ z) (he : e.natAbs=1) (hd : d.natAbs=1)
    (hdet : (l : ℤ)*e-k*d ≠ 0) :
    ((threePrimePatternSet T k l a b z e d).card : ℝ) ≤
      2*Real.exp 3*Real.exp (3*primeHarmonic (3+2*X^2))*T/
        ((a.lcm b : ℕ)*(Real.log (z+1 : ℝ))^3)+
      2*((a.lcm b : ℕ) : ℝ)^8*(z+1 : ℝ)^96 := by
  classical
  obtain ⟨hk0,hkX⟩ := mem_Icc.mp hk
  obtain ⟨hl0,hlX⟩ := mem_Icc.mp hl
  obtain ⟨ha0,haX⟩ := mem_Icc.mp ha
  obtain ⟨hb0,hbX⟩ := mem_Icc.mp hb
  by_cases hnon : (threePrimePatternSet T k l a b z e d).Nonempty
  · obtain ⟨v,hv,hprogress⟩ := threePrimePatternSet_progression T k l a b z e d
      (by omega) (by omega) he hd hnon
    let D := 3+2*X^2
    let S := upperSievingPrimes D z
    have hD : 3 ≤ D := by dsimp [D]; omega
    have hX : X ≤ D := by dsimp [D]; nlinarith
    have hM : a.lcm b ≤ D := by
      have hh := Nat.lcm_le_mul (by omega : 0<a) (by omega : 0<b)
      dsimp [D]
      nlinarith [Nat.mul_le_mul haX hbX]
    have hS (s : ℕ) (hs : s ∈ S) : s.Prime ∧ D<s ∧ s≤z :=
      (mem_upperSievingPrimes D z s).mp hs
    have hroots (s : ℕ) (hs : s ∈ S) : (threePrimeResidues s k l e d).card=3 := by
      have hsk : ¬s ∣ k := by
        intro hh
        have := Nat.le_of_dvd (by omega : 0<k) hh
        have := (hS s hs).2.1
        omega
      have hsl : ¬s ∣ l := by
        intro hh
        have := Nat.le_of_dvd (by omega : 0<l) hh
        have := (hS s hs).2.1
        omega
      apply threePrimeResidues_card s k l e d (hS s hs).1 hsk hsl he hd hdet
      have hh := signed_neighbor_determinant_bound k l X e d hkX hlX he hd
      have hh' := (hS s hs).2.1
      dsimp [D] at hh'
      nlinarith
    have hsub : threePrimePatternSet T k l a b z e d ⊆
        (range T).filter (fun p => p%(a.lcm b)=v ∧ ∀ s ∈ S, p%s ∉ threePrimeResidues s k l e d) := by
      intro p hp
      have hprog := hprogress p hp
      obtain ⟨hpT,hpp,hpz,q,r,hq,hr,hqz,hrz,heq,her⟩ :=
        (mem_threePrimePatternSet T k l a b z p e d).mp hp
      refine mem_filter.mpr ⟨mem_range.mpr hpT,hprog,?_⟩
      intro s hs hh
      have hs' := hS s hs
      rw [mod_mem_threePrimeResidues s k l p e d hs'.1.pos] at hh
      rcases hh with hh | hh | hh
      · exact prime_not_dvd_larger_prime s p z hs'.1 hpp hs'.2.2 hpz hh
      · rw [heq] at hh
        have hmul : s ∣ a*q := by exact_mod_cast hh
        rcases hs'.1.dvd_mul.mp hmul with hsa | hsq
        · have := Nat.le_of_dvd (by omega : 0<a) hsa
          omega
        · exact prime_not_dvd_larger_prime s q z hs'.1 hq hs'.2.2 hqz hsq
      · rw [her] at hh
        have hmul : s ∣ b*r := by exact_mod_cast hh
        rcases hs'.1.dvd_mul.mp hmul with hsb | hsr
        · have := Nat.le_of_dvd (by omega : 0<b) hsb
          omega
        · exact prime_not_dvd_larger_prime s r z hs'.1 hr hs'.2.2 hrz hsr
    have hbound := threeResidue_progression_sieve_bound D z (a.lcm b) v T hD hz
      (Nat.lcm_pos (by omega) (by omega)) hM hv (fun s => threePrimeResidues s k l e d)
      (fun s hs => threePrimeResidues_subset s k l e d (hS s hs).1.pos) hroots
    exact ((Nat.cast_le (α := ℝ)).mpr (card_le_card hsub)).trans hbound
  · rw [not_nonempty_iff_eq_empty.mp hnon,card_empty,Nat.cast_zero]
    have hlog : 0 ≤ Real.log (z+1 : ℝ) := Real.log_nonneg (by norm_cast; omega)
    positivity

#print axioms threePrimePatternSet_progression
#print axioms threePrimePatternSet_sieve_bound
end Erdos371.FiniteSieve
