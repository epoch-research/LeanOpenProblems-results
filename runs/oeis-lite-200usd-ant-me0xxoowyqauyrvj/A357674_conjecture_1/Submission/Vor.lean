import Mathlib

open Nat Finset BigOperators

namespace Voronoi

variable {R : Type*} [CommRing R]

/-- In a commutative ring, if `x^2 = 0` then `(x+y)^m = y^m + m*x*y^(m-1)`. -/
theorem add_pow_sq_zero (x y : R) (hx : x^2 = 0) (m : ℕ) :
    (x + y)^m = y^m + (m : R) * x * y^(m-1) := by
  induction m with
  | zero => simp
  | succ d hd =>
    rw [pow_succ, hd]
    cases d with
    | zero => simp; ring
    | succ e =>
      simp only [Nat.add_sub_cancel]
      have hye : y^(e+1) = y^e * y := by rw [pow_succ]
      have : (y^(e+1) + (↑(e+1) * x * y^e)) * (x + y)
          = y^(e+1)*x + y^(e+1)*y + (↑(e+1)*x*y^e)*x + (↑(e+1)*x*y^e)*y := by ring
      rw [this]
      have hx2 : (↑(e+1)*x*y^e)*x = (e+1 : R) * (x^2) * y^e := by push_cast; ring
      rw [hx2, hx]
      push_cast
      rw [pow_succ y (e+1)]
      ring

/-- For prime `p > 2`, the map `k ↦ k*2 % p` is injective on `Ico 1 p`. -/
theorem mul2_injOn (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    Set.InjOn (fun k => k * 2 % p) (Finset.Ico 1 p : Finset ℕ) := by
  intro a ha b hb hab
  simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
  simp only at hab
  -- a*2 ≡ b*2 mod p, p prime, p∤2 ⟹ a ≡ b mod p ⟹ a = b
  have hpa : a % p = a := Nat.mod_eq_of_lt ha.2
  have hpb : b % p = b := Nat.mod_eq_of_lt hb.2
  have hmod : a * 2 ≡ b * 2 [MOD p] := hab
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
  have := Nat.ModEq.cancel_right_of_coprime hcop hmod
  unfold Nat.ModEq at this
  rw [hpa, hpb] at this
  exact this

theorem mul2_mapsto (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (k : ℕ) (hk : k ∈ Finset.Ico 1 p) :
    k * 2 % p ∈ Finset.Ico 1 p := by
  simp only [Finset.mem_Ico] at hk ⊢
  refine ⟨?_, Nat.mod_lt _ hp.pos⟩
  rcases Nat.eq_zero_or_pos (k * 2 % p) with h | h
  · exfalso
    have h := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
    · exact absurd (Nat.le_of_dvd (by omega) h1) (by omega)
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h1; omega
  · omega

/-- The image of `Ico 1 p` under `k ↦ k*2 % p` is `Ico 1 p`. -/
theorem mul2_image (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    (Finset.Ico 1 p).image (fun k => k * 2 % p) = Finset.Ico 1 p := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact mul2_mapsto p hp hp2 k hk
  · rw [Finset.card_image_of_injOn (mul2_injOn p hp hp2)]

/-- Reindexing a sum over `Ico 1 p` by `k ↦ k*2 % p`. -/
theorem sum_mul2_reindex (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (g : ℕ → R) :
    ∑ k ∈ Finset.Ico 1 p, g (k * 2 % p) = ∑ k ∈ Finset.Ico 1 p, g k := by
  have h := Finset.sum_image (s := Finset.Ico 1 p) (f := g) (g := fun k => k * 2 % p)
    (fun a ha b hb => mul2_injOn p hp hp2 ha hb)
  rw [mul2_image p hp hp2] at h
  exact h.symm

/-- The power-sum form of Voronoi's congruence (with `a = 2`), in `ZMod (p^2)`. -/
theorem voronoi (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (m : ℕ) :
    ((2 : ZMod (p^2))^m - 1) * (∑ k ∈ Finset.Ico 1 p, (k : ZMod (p^2))^m)
      = (m : ZMod (p^2)) * (p : ZMod (p^2)) *
          (∑ k ∈ Finset.Ico 1 p,
            ((k * 2 / p : ℕ) : ZMod (p^2)) * ((k * 2 % p : ℕ) : ZMod (p^2))^(m-1)) := by
  set Rr := ZMod (p^2)
  have hpr2 : (p : Rr)^2 = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  -- per-term identity
  have hterm : ∀ k ∈ Finset.Ico 1 p,
      (k : Rr)^m * (2:Rr)^m
        = ((k*2%p : ℕ) : Rr)^m
          + (m : Rr) * ((p:Rr) * ((k*2/p : ℕ):Rr)) * ((k*2%p : ℕ):Rr)^(m-1) := by
    intro k _
    have hcast : (k : Rr) * 2 = (p:Rr) * ((k*2/p:ℕ):Rr) + ((k*2%p:ℕ):Rr) := by
      have hnat : k * 2 = p * (k*2/p) + (k*2%p) := (Nat.div_add_mod (k*2) p).symm
      have := congrArg (fun n => ((n:ℕ):Rr)) hnat
      push_cast at this
      linear_combination this
    have hx2 : ((p:Rr) * ((k*2/p:ℕ):Rr))^2 = 0 := by
      rw [mul_pow, hpr2]; ring
    have := add_pow_sq_zero ((p:Rr) * ((k*2/p:ℕ):Rr)) ((k*2%p:ℕ):Rr) hx2 m
    calc (k : Rr)^m * (2:Rr)^m = ((k:Rr)*2)^m := by rw [mul_pow]
      _ = ((p:Rr) * ((k*2/p:ℕ):Rr) + ((k*2%p:ℕ):Rr))^m := by rw [hcast]
      _ = _ := this
  -- sum the per-term identity
  have hsum := Finset.sum_congr rfl hterm
  rw [Finset.sum_add_distrib] at hsum
  -- left side: 2^m * S
  rw [← Finset.sum_mul] at hsum
  -- reindex the r_k^m sum
  have hreindex : ∑ k ∈ Finset.Ico 1 p, ((k*2%p:ℕ):Rr)^m
      = ∑ k ∈ Finset.Ico 1 p, (k:Rr)^m :=
    sum_mul2_reindex p hp hp2 (fun j => ((j:ℕ):Rr)^m)
  rw [hreindex] at hsum
  -- factor out m * p from last sum
  have hfac : ∑ k ∈ Finset.Ico 1 p,
        (m : Rr) * ((p:Rr) * ((k*2/p:ℕ):Rr)) * ((k*2%p:ℕ):Rr)^(m-1)
      = (m:Rr) * (p:Rr) * ∑ k ∈ Finset.Ico 1 p,
          ((k*2/p:ℕ):Rr) * ((k*2%p:ℕ):Rr)^(m-1) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
  rw [hfac] at hsum
  -- now hsum : (∑ k^m) * 2^m = (∑ k^m) + m*p*V
  set S := ∑ k ∈ Finset.Ico 1 p, (k:Rr)^m
  set V := ∑ k ∈ Finset.Ico 1 p, ((k*2/p:ℕ):Rr) * ((k*2%p:ℕ):Rr)^(m-1)
  linear_combination hsum

