import Submission.RoughSquarefreeConicSetup

/-! A fixed affine parameter lattice supplies many simultaneously squarefree
rough conic collisions. This is not a Sidon root-set construction. -/
namespace Erdos1206.RoughSquarefreeConicSieve
open Finset Filter RoughSquarefreeConicSetup QuadraticSquarefreeSieve
open scoped Classical Topology

variable (D : Data)

lemma seed_coprime (i : Fin 4) : Nat.Coprime (D.F i 0 1) D.q := by
  have ha : IsCoprime (D.an i:ℤ) (D.q:ℤ) := by
    rw [D.cast_an]
    exact RoughConicIntegralCoefficients.a_coprime D.q D.modulus_m D.modulus_L i
  have hm : IsCoprime (D.m:ℤ) (D.q:ℤ) := by
    obtain ⟨z,hz⟩ := D.modulus_m
    refine ⟨1,-18*z,?_⟩
    linear_combination hz
  have hd : IsCoprime (D.dn i:ℤ) (D.q:ℤ) := by
    fin_cases i
    · refine ⟨1,0,?_⟩; norm_num [Data.dn]
    · refine ⟨1,0,?_⟩; norm_num [Data.dn]
    · simpa [Data.dn] using hm
    · simpa [Data.dn] using hm
  have hprod := Nat.isCoprime_iff_coprime.mp (show IsCoprime ((D.dn i*D.an i:ℕ):ℤ) (D.q:ℤ) by
    simpa only [Nat.cast_mul] using hd.mul_left ha)
  simpa [Data.F,Data.A,quad] using hprod

lemma seed_not_dvd {p : ℕ} (hp : p.Prime) (hpq : p ∣ D.q) (i : Fin 4) :
    ¬ p ∣ D.F i 0 1 := by
  intro hf
  have hh := Nat.dvd_gcd hf hpq
  rw [(seed_coprime D i).gcd_eq_one] at hh
  exact hp.not_dvd_one hh

lemma exists_local_witnesses : ∃ T U : ℕ → ℕ,
    (∀ p, p.Prime → p ∣ D.q → T p=0 ∧ U p=1) ∧
    ∀ p, p.Prime → ∀ i, ¬ p^2 ∣ D.F i (T p) (U p) := by
  have hex : ∀ p : ℕ, ∃ t u : ℕ,
      (p.Prime → p ∣ D.q → t=0 ∧ u=1) ∧
      (p.Prime → ∀ i, ¬ p^2 ∣ D.F i t u) := by
    intro p
    by_cases hp : p.Prime
    swap
    · exact ⟨0,1,fun h => (hp h).elim,fun h => (hp h).elim⟩
    by_cases hpq : p ∣ D.q
    · refine ⟨0,1,fun _ _ => ⟨rfl,rfl⟩,fun _ i hd => ?_⟩
      exact seed_not_dvd D hp hpq i ((dvd_pow_self p (by decide : 2 ≠ 0)).trans hd)
    · have hp8 : 2*4 < p := by
        by_contra hn
        have hple : p ≤ 8 := by omega
        have hp210 : p ∣ 210 := by
          interval_cases p <;> norm_num at hp <;> norm_num
        exact hpq (hp210.trans D.multiple210)
      obtain ⟨t,u,htu⟩ := QuadraticLocalAdmissibility.large_prime_locally_squarefree
        hp hp8 D.dn D.an D.bn D.cn D.dn_squarefree
        (fun i => QuadraticLocalAdmissibility.primitive_coefficients_mod_prime hp (D.primitive i))
      refine ⟨t,u,fun _ h => (hpq h).elim,fun _ i => ?_⟩
      simpa only [Data.F,Data.A,Data.B,Data.C,QuadraticLocalAdmissibility.quad_scale] using htu i
  choose T U hTU using hex
  exact ⟨T,U,fun p hp hq => (hTU p).1 hp hq,fun p hp => (hTU p).2 hp⟩

/-- A positive proportion of parameter pairs in one affine lattice gives
squarefree roots. Every pair in that lattice gives roots coprime to q. -/
theorem exists_sieved_progression : ∃ M v w : ℕ, 0 < M ∧ 0 < v ∧ 0 < w ∧
    (∀ i t u, Nat.Coprime (D.F i (M*t+v) (M*u+w)) D.q) ∧
    ∀ᶠ N : ℕ in atTop, (N:ℝ)^2/2 ≤
      (((range N) ×ˢ (range N)).filter (fun x =>
        ∀ i, Squarefree (D.F i (M*x.1+v) (M*x.2+w)))).card := by
  obtain ⟨T,U,hres0,hloc⟩ := exists_local_witnesses D
  let K := 48+D.q+(∑ i : Fin 4,
    (D.A i+(discriminant (D.A i) (D.B i) (D.C i)).natAbs))+1
  let S := ∑ i : Fin 4, (D.A i+D.B i+D.C i)
  have hK : 12*4 ≤ K := by dsimp [K]; omega
  have hqK : D.q ≤ K := by dsimp [K]; omega
  have hAK (i : Fin 4) : D.A i+(discriminant (D.A i) (D.B i) (D.C i)).natAbs ≤ K := by
    have hh := single_le_sum (f := fun j : Fin 4 =>
      D.A j+(discriminant (D.A j) (D.B j) (D.C j)).natAbs)
      (fun _ _ => Nat.zero_le _) (mem_univ i)
    dsimp only at hh
    dsimp [K]
    omega
  have ha (i : Fin 4) : 0 < D.A i ∧ D.A i ≤ K := ⟨D.A_pos i,by have := hAK i; omega⟩
  have hd (i : Fin 4) : discriminant (D.A i) (D.B i) (D.C i) ≠ 0 ∧
      (discriminant (D.A i) (D.B i) (D.C i)).natAbs ≤ K :=
    ⟨D.full_discriminant_ne i,by have := hAK i; omega⟩
  have hS (i : Fin 4) : D.A i+D.B i+D.C i ≤ S :=
    single_le_sum (f := fun j => D.A j+D.B j+D.C j) (fun _ _ => Nat.zero_le _) (mem_univ i)
  obtain ⟨v,w,hv,hw,hres,hgood⟩ := PrescribedQuadraticSieve.prescribed_progression_sieve
    (by decide : 0 < 4) D.A D.B D.C K S hK ha hd hS T U (fun p hp _ => hloc p hp)
  refine ⟨sieveModulus K,v,w,sieveModulus_pos K,hv,hw,?_,hgood⟩
  intro i t u
  apply Nat.coprime_of_dvd
  intro p hp hpf hpq
  have hpK : p ≤ K := (Nat.le_of_dvd D.q_pos hpq).trans hqK
  obtain ⟨ht,hu⟩ := hres p hp hpK t u
  have hmod := AffineQuadraticSquarefreeSieve.quad_modEq (D.A i) (D.B i) (D.C i) ht hu
  have hd' := (hmod.dvd_iff (dvd_pow_self p (by decide : 2 ≠ 0))).mp hpf
  obtain ⟨hT,hU⟩ := hres0 p hp hpq
  rw [hT,hU] at hd'
  exact seed_not_dvd D hp hpq i hd'

#print axioms seed_coprime
#print axioms exists_local_witnesses
#print axioms exists_sieved_progression
end Erdos1206.RoughSquarefreeConicSieve
