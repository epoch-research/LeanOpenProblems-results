import FormalConjectures.Util.ProblemImports
open Nat

theorem pcancel (p : ℕ) [hp : Fact p.Prime] {b c : ℤ} {m : ℕ} (hb : ¬ (p:ℤ) ∣ b)
    (h : (p:ℤ)^m ∣ b * c) : (p:ℤ)^m ∣ c := by
  have hpp : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hcop : IsCoprime ((p:ℤ)^m) b := (hpp.coprime_iff_not_dvd.mpr hb).pow_left
  exact hcop.dvd_of_dvd_mul_left h

theorem extract3 (p : ℕ) [hp : Fact p.Prime] {c : ℤ} {m : ℕ}
    (h : (p:ℤ)^m ∣ 3 * c) : (p:ℤ)^(m-1) ∣ c := by
  rcases eq_or_ne p 3 with h3 | h3
  · subst h3
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · obtain ⟨k, hk⟩ := h
      refine ⟨k, ?_⟩
      have hpow : ((3:ℕ):ℤ)^m = 3 * ((3:ℕ):ℤ)^(m-1) := by
        rw [show m = (m-1)+1 by omega, pow_succ]; push_cast; ring
      rw [hpow] at hk
      have h3ne : (3:ℤ) ≠ 0 := by norm_num
      apply mul_left_cancel₀ h3ne; push_cast at hk ⊢; linarith [hk]
  · have hnd : ¬ (p:ℤ) ∣ 3 := by
      have hn : ¬ p ∣ 3 := by
        intro hd; rcases (Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp hd; exact h3 rfl
      intro hd; exact hn (by exact_mod_cast hd)
    exact dvd_trans (pow_dvd_pow _ (Nat.sub_le m 1)) (pcancel p hnd h)

theorem pmul (p : ℕ) {a b : ℕ} {x y : ℤ} (hx : (p:ℤ)^a ∣ x) (hy : (p:ℤ)^b ∣ y) :
    (p:ℤ)^(a+b) ∣ x * y := by rw [pow_add]; exact mul_dvd_mul hx hy

theorem dvdK {p : ℕ} {a K : ℕ} {x : ℤ} (hx : (p:ℤ)^a ∣ x) (h : K ≤ a) : (p:ℤ)^K ∣ x :=
  dvd_trans (pow_dvd_pow _ h) hx

theorem assembly (p : ℕ) [hp : Fact p.Prime] (r : ℕ) (hr : 2 ≤ r)
    (A a0 B b0 : ℤ) (hb0 : ¬ (p:ℤ) ∣ b0)
    (H1 : (p:ℤ)^3 ∣ (a0 - 3)) (H2 : (p:ℤ)^3 ∣ 3*(b0 - 2))
    (Fα : (p:ℤ)^(3*r) ∣ (A - a0)) (Fβ : (p:ℤ)^(3*r) ∣ 3*(B - b0))
    (F3 : (p:ℤ)^(3*r+3) ∣ (A*b0^3 - a0*B^3)) :
    (p:ℤ)^(3*r+3) ∣ ((a0^2 - 27*b0) - (A^2 - 27*B)) := by
  set K := 3*r+3 with hK
  set α := A - a0 with hα
  set β := B - b0 with hβ
  have hβ1 : (p:ℤ)^(3*r-1) ∣ β := extract3 p Fβ
  -- powers of α, β
  have hα2 : (p:ℤ)^K ∣ α^2 := by
    rw [pow_two]; exact dvdK (pmul p Fα Fα) (by rw [hK]; omega)
  have hβ2 : (p:ℤ)^K ∣ β^2 := by
    rw [pow_two]; exact dvdK (pmul p hβ1 hβ1) (by rw [hK]; omega)
  have hβ3 : (p:ℤ)^K ∣ β^3 := by
    have h1 : (p:ℤ)^((3*r-1)+(3*r-1)+(3*r-1)) ∣ β^3 := by
      have e : β^3 = β*β*β := by ring
      rw [e, pow_add, pow_add]; exact mul_dvd_mul (mul_dvd_mul hβ1 hβ1) hβ1
    exact dvdK h1 (by rw [hK]; omega)
  have hb02 : ¬ (p:ℤ) ∣ b0^2 := by
    intro hd; exact hb0 ((Nat.prime_iff_prime_int.mp hp.out).dvd_of_dvd_pow hd)
  -- HP : p^K ∣ α*b0^3 - 3*a0*b0^2*β
  have HP : (p:ℤ)^K ∣ (α*b0^3 - 3*a0*b0^2*β) := by
    have key : α*b0^3 - 3*a0*b0^2*β = (A*b0^3 - a0*B^3) + 3*a0*b0*β^2 + a0*β^3 := by
      rw [hα, hβ]; ring
    rw [key]
    exact dvd_add (dvd_add F3 (Dvd.dvd.mul_left hβ2 _)) (Dvd.dvd.mul_left hβ3 _)
  -- HQ : p^K ∣ α*b0 - 3*a0*β
  have HQ : (p:ℤ)^K ∣ (α*b0 - 3*a0*β) := by
    apply pcancel p hb02
    have : b0^2 * (α*b0 - 3*a0*β) = α*b0^3 - 3*a0*b0^2*β := by ring
    rw [this]; exact HP
  -- HR : p^K ∣ α*b0 - 9*β
  have HR : (p:ℤ)^K ∣ (α*b0 - 9*β) := by
    have t : (p:ℤ)^K ∣ (3*a0*β - 9*β) := by
      have e : 3*a0*β - 9*β = (a0 - 3)*(3*β) := by ring
      rw [e, hK, show 3*r+3 = 3+3*r by ring]; exact pmul p H1 Fβ
    have := dvd_add HQ t
    have e2 : (α*b0 - 3*a0*β) + (3*a0*β - 9*β) = α*b0 - 9*β := by ring
    rwa [e2] at this
  -- 2a0α - 6α, 3αb0 - 6α
  have T3ab : (p:ℤ)^K ∣ (3*α*b0 - 6*α) := by
    have e : 3*α*b0 - 6*α = α*(3*(b0-2)) := by ring
    rw [e, hK]; exact pmul p Fα H2
  have T2aa : (p:ℤ)^K ∣ (2*a0*α - 6*α) := by
    have e : 2*a0*α - 6*α = α*(2*(a0-3)) := by ring
    rw [e]
    have h2 : (p:ℤ)^3 ∣ 2*(a0-3) := Dvd.dvd.mul_left H1 2
    rw [hK]; exact pmul p Fα h2
  -- HS : p^K ∣ 6*α - 27*β
  have HS : (p:ℤ)^K ∣ (6*α - 27*β) := by
    have h3 : (p:ℤ)^K ∣ (3*α*b0 - 27*β) := by
      have e : 3*α*b0 - 27*β = 3*(α*b0 - 9*β) := by ring
      rw [e]; exact Dvd.dvd.mul_left HR 3
    have := dvd_sub h3 T3ab
    have e2 : (3*α*b0 - 27*β) - (3*α*b0 - 6*α) = 6*α - 27*β := by ring
    rwa [e2] at this
  -- final
  have main : (p:ℤ)^K ∣ (27*β - 2*a0*α) := by
    have := dvd_add HS T2aa
    have e : (6*α - 27*β) + (2*a0*α - 6*α) = -(27*β - 2*a0*α) := by ring
    rw [e] at this
    exact (dvd_neg).mp this
  have goaleq : ((a0^2 - 27*b0) - (A^2 - 27*B)) = (27*β - 2*a0*α) - α^2 := by
    rw [hα, hβ]; ring
  rw [goaleq]; exact dvd_sub main hα2
