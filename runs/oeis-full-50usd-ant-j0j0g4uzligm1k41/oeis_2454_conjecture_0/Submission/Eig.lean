import FormalConjectures.Util.ProblemImports

open Nat
open Matrix Complex
open scoped BigOperators

namespace Eig

/-- The eigenvalues: `lam p = ∑_{r ≠ 0} ζ^{p r} / (ζ^r - 1)`. -/
noncomputable def lam (ζ : ℂ) (N : ℕ) [NeZero N] (p : Fin N) : ℂ :=
  ∑ r : Fin N, (if r = 0 then 0 else ζ ^ ((p : ℕ) * (r : ℕ)) / (ζ ^ (r : ℕ) - 1))

theorem pow_sub_one_ne (ζ : ℂ) (N : ℕ) [NeZero N] (hζ : IsPrimitiveRoot ζ N) (r : Fin N)
    (hr : r ≠ 0) : ζ ^ (r : ℕ) - 1 ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  have hd : (N : ℕ) ∣ (r : ℕ) := (hζ.pow_eq_one_iff_dvd _).mp h
  have hpos : 0 < (r : ℕ) := Nat.pos_of_ne_zero (fun h0 => hr (Fin.ext (by simpa using h0)))
  exact absurd ((Nat.le_of_dvd hpos hd).trans_lt r.isLt) (lt_irrefl _)

/-- Telescoping: `lam ζ N q - lam ζ N p = ∑_{r≠0} ζ^{p r}` when q = p+1. -/
theorem lam_succ_sub (ζ : ℂ) (N : ℕ) [NeZero N] (hζ : IsPrimitiveRoot ζ N)
    (p q : Fin N) (hq : (q : ℕ) = (p : ℕ) + 1) :
    lam ζ N q - lam ζ N p = ∑ r : Fin N, (if r = 0 then 0 else ζ ^ ((p : ℕ) * (r : ℕ))) := by
  simp only [lam, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hr : r = 0
  · simp [hr]
  · have hrne := pow_sub_one_ne ζ N hζ r hr
    rw [if_neg hr, if_neg hr, if_neg hr, hq]
    field_simp
    ring

end Eig

namespace Eig

/-- Character sum over `Fin N`. -/
theorem char_sum (ζ : ℂ) (N : ℕ) (hζ : IsPrimitiveRoot ζ N) (k : ℕ) :
    ∑ j : Fin N, ζ ^ (k * (j : ℕ)) = if N ∣ k then (N : ℂ) else 0 := by
  have hne : ∀ i : Fin N, ζ ^ (k * (i:ℕ)) = (ζ ^ k) ^ (i:ℕ) := fun i => by rw [← pow_mul]
  simp_rw [hne]
  rw [Fin.sum_univ_eq_sum_range (fun i => (ζ ^ k) ^ i)]
  by_cases hdvd : N ∣ k
  · have : ζ ^ k = 1 := by
      obtain ⟨t, rfl⟩ := hdvd; rw [pow_mul, hζ.pow_eq_one, one_pow]
    simp [this, hdvd]
  · have hk1 : ζ ^ k ≠ 1 := by rw [ne_eq, hζ.pow_eq_one_iff_dvd]; exact hdvd
    rw [geom_sum_eq hk1]
    have : (ζ ^ k) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [this]; simp [hdvd]

/-- `∑_{r : Fin N} ζ^{p r} = 0` when `p ≠ 0` (p in `1..N-1`). -/
theorem sum_pow_eq_zero (ζ : ℂ) (N : ℕ) [NeZero N] (hζ : IsPrimitiveRoot ζ N) (p : Fin N)
    (hp : p ≠ 0) : ∑ r : Fin N, ζ ^ ((p : ℕ) * (r : ℕ)) = 0 := by
  rw [char_sum ζ N hζ (p : ℕ)]
  have hpos : 0 < (p : ℕ) := Nat.pos_of_ne_zero (fun h0 => hp (Fin.ext (by simpa using h0)))
  have hnd : ¬ N ∣ (p : ℕ) := fun hd => absurd ((Nat.le_of_dvd hpos hd).trans_lt p.isLt) (lt_irrefl _)
  simp [hnd]

end Eig

namespace Eig

/-- The total of all eigenvalues is `0`. -/
theorem sum_lam_eq_zero (ζ : ℂ) (N : ℕ) [NeZero N] (hζ : IsPrimitiveRoot ζ N) :
    ∑ p : Fin N, lam ζ N p = 0 := by
  simp only [lam]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hr : r = 0
  · simp [hr]
  · have hrne := pow_sub_one_ne ζ N hζ r hr
    have : ∀ p : Fin N, (if r = 0 then (0:ℂ) else ζ ^ ((p:ℕ)*(r:ℕ)) / (ζ ^ (r:ℕ) - 1))
        = (ζ ^ ((r:ℕ)*(p:ℕ))) / (ζ ^ (r:ℕ) - 1) := by
      intro p; rw [if_neg hr, mul_comm (p:ℕ) (r:ℕ)]
    simp_rw [this, ← Finset.sum_div]
    rw [sum_pow_eq_zero ζ N hζ r hr, zero_div]

end Eig

namespace Eig

/-- The telescoping difference value. -/
theorem Tval (ζ : ℂ) (N : ℕ) [NeZero N] (hζ : IsPrimitiveRoot ζ N) (p : Fin N) :
    ∑ r : Fin N, (if r = 0 then (0:ℂ) else ζ ^ ((p:ℕ) * (r:ℕ)))
      = (if N ∣ (p:ℕ) then (N:ℂ) else 0) - 1 := by
  have key : ∀ r : Fin N, (if r = 0 then (0:ℂ) else ζ ^ ((p:ℕ) * (r:ℕ)))
      = ζ ^ ((p:ℕ) * (r:ℕ)) - (if r = 0 then (1:ℂ) else 0) := by
    intro r
    by_cases hr : r = 0
    · subst hr; simp
    · simp [hr]
  simp_rw [key]
  rw [Finset.sum_sub_distrib, char_sum ζ N hζ (p:ℕ)]
  congr 1
  rw [Finset.sum_ite_eq' Finset.univ (0:Fin N) (fun _ => (1:ℂ))]
  simp

/-- Closed form for `p ≥ 1`: `lam p = lam 0 + N - p`. -/
theorem lam_closed (ζ : ℂ) (N : ℕ) [NeZero N] (hζ : IsPrimitiveRoot ζ N) :
    ∀ k : ℕ, (hk : k + 1 < N) →
      lam ζ N ⟨k+1, hk⟩ = lam ζ N 0 + (N:ℂ) - (k+1) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have hsub := lam_succ_sub ζ N hζ 0 ⟨0+1, hk⟩ (by simp)
    rw [Tval ζ N hζ 0] at hsub
    simp only [Fin.val_zero, Nat.dvd_zero, if_true] at hsub
    push_cast
    linear_combination hsub
  | succ k ih =>
    intro hk
    have hk1 : k + 1 < N := Nat.lt_of_succ_lt hk
    have hsub := lam_succ_sub ζ N hζ ⟨k+1, hk1⟩ ⟨k+1+1, hk⟩ (by simp)
    rw [Tval ζ N hζ ⟨k+1, hk1⟩] at hsub
    have hnd : ¬ (N:ℕ) ∣ (k+1) := by
      intro hd
      exact absurd (Nat.le_of_dvd (Nat.succ_pos k) hd) (Nat.not_le.mpr hk1)
    simp only [hnd, if_false, zero_sub] at hsub
    have hih := ih hk1
    have hstep : lam ζ N ⟨k+1+1, hk⟩ = lam ζ N ⟨k+1, hk1⟩ - 1 := by linear_combination hsub
    rw [hstep, hih]; push_cast; ring

end Eig

namespace Eig

/-- The base eigenvalue: `2 · lam 0 = -(N-1)`. -/
theorem two_lam_zero (ζ : ℂ) (N : ℕ) [NeZero N] (hζ : IsPrimitiveRoot ζ N) :
    (2 : ℂ) * lam ζ N 0 = -((N:ℂ) - 1) := by
  have uni : ∀ p : Fin N, lam ζ N p
      = lam ζ N 0 + (N:ℂ) - ((p:ℕ):ℂ) - (if (p:ℕ) = 0 then (N:ℂ) else 0) := by
    intro p
    by_cases hp : (p:ℕ) = 0
    · have hp0 : p = 0 := Fin.ext (by simpa using hp)
      subst hp0; simp
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hp
      have hkN : k + 1 < N := by have hpl := p.isLt; omega
      have hpe : lam ζ N p = lam ζ N ⟨k+1, hkN⟩ := by congr 1; exact Fin.ext hk
      rw [hpe, lam_closed ζ N hζ k hkN, hk]
      simp only [Nat.succ_ne_zero, if_false, sub_zero]
      push_cast; ring
  have hs := sum_lam_eq_zero ζ N hζ
  rw [Finset.sum_congr rfl (fun p _ => uni p)] at hs
  have hcard : (Finset.univ : Finset (Fin N)).card = N := by simp
  have e1 : ∑ _p : Fin N, lam ζ N 0 = (N:ℂ) * lam ζ N 0 := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have e2 : ∑ _p : Fin N, (N:ℂ) = (N:ℂ) * (N:ℂ) := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have e3 : ∑ p : Fin N, (if (p:ℕ) = 0 then (N:ℂ) else 0) = (N:ℂ) := by
    rw [Finset.sum_eq_single (0:Fin N)
      (fun b _ hb => by rw [if_neg]; exact fun h => hb (Fin.ext (by simpa using h)))
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  have e4 : (∑ p : Fin N, ((p:ℕ):ℂ)) * 2 = (N:ℂ) * ((N:ℂ) - 1) := by
    have hnat : (∑ p : Fin N, (p:ℕ)) * 2 = N * (N - 1) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => i)]
      exact Finset.sum_range_id_mul_two N
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have hc := congrArg (Nat.cast : ℕ → ℂ) hnat
      push_cast [Nat.cast_sub h] at hc
      linear_combination hc
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      e1, e2, e3] at hs
  have hN0 : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- hs : (N*lam0 + N*N) - (∑ p) - N = 0
  have e4' : ∑ p : Fin N, ((p:ℕ):ℂ) = (N:ℂ) * ((N:ℂ) - 1) / 2 := by
    field_simp; linear_combination e4
  rw [e4'] at hs
  have key : (N:ℂ) * ((2:ℂ) * lam ζ N 0 + ((N:ℂ) - 1)) = 0 := by
    linear_combination 2 * hs
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hN0
  · linear_combination h

end Eig

namespace Eig

/-- Explicit base value: `lam 0 = -m` for `N = 2m+1`. -/
theorem lam_zero_val (ζ : ℂ) (m : ℕ) (hζ : IsPrimitiveRoot ζ (2*m+1)) :
    haveI : NeZero (2*m+1) := ⟨by omega⟩
    lam ζ (2*m+1) 0 = -(m:ℂ) := by
  haveI : NeZero (2*m+1) := ⟨by omega⟩
  have h := two_lam_zero ζ (2*m+1) hζ
  push_cast at h
  linear_combination h / 2

/-- Explicit value: `lam ⟨k+1⟩ = m - k` for `N = 2m+1`. -/
theorem lam_succ_val (ζ : ℂ) (m : ℕ) (hζ : IsPrimitiveRoot ζ (2*m+1))
    (k : ℕ) (hk : k + 1 < 2*m+1) :
    haveI : NeZero (2*m+1) := ⟨by omega⟩
    lam ζ (2*m+1) ⟨k+1, hk⟩ = (m:ℂ) - (k:ℂ) := by
  haveI : NeZero (2*m+1) := ⟨by omega⟩
  rw [lam_closed ζ (2*m+1) hζ k hk, lam_zero_val ζ m hζ]
  push_cast; ring

end Eig

namespace Eig

/-- Factorial as a complex product over `Ico 1 (m+1)`. -/
theorem prod_Ico_factorial (m : ℕ) :
    ∏ i ∈ Finset.Ico 1 (m+1), ((m:ℂ) + 1 - (i:ℂ)) = (m.factorial : ℂ) := by
  rw [Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel]
  have hconv : ∀ i ∈ Finset.range m, ((m:ℂ)+1-((1+i:ℕ):ℂ)) = (((m - i : ℕ)):ℂ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.cast_sub (le_of_lt hi)]; push_cast; ring
  rw [Finset.prod_congr rfl hconv, ← Nat.cast_prod]
  congr 1
  rw [← Finset.prod_range_add_one_eq_factorial m, ← Finset.prod_range_reflect (fun i => i+1) m]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  omega

end Eig
