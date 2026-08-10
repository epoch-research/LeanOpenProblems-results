import FormalConjectures.Util.ProblemImports

open Nat MvPolynomial BigOperators

abbrev Vars := Fin 3
local notation "P" => MvPolynomial Vars ℤ

def is_var0 (p : P) : Prop :=
  ∀ m ∈ p.support, m 1 = 0 ∧ m 2 = 0

def is_var12 (p : P) : Prop :=
  ∀ m ∈ p.support, m 0 = 0

noncomputable def xyz_pow_n (n : ℕ) : Finsupp Vars ℕ :=
  Finsupp.ofSupportFinite (fun _ : Vars => n) (Set.toFinite _)

theorem coeff_mul_disjoint {p q : P} (hp : is_var0 p) (hq : is_var12 q) (n : ℕ) :
  coeff (xyz_pow_n n) (p * q) = coeff (Finsupp.single 0 n) p * coeff (Finsupp.single 1 n + Finsupp.single 2 n) q := by
  rw [coeff_mul]
  have h_sum : Finsupp.single 0 n + (Finsupp.single 1 n + Finsupp.single 2 n) = xyz_pow_n n := by
    ext i
    fin_cases i <;> simp [xyz_pow_n, Finsupp.ofSupportFinite_coe]
  have h_uniq : ∀ x ∈ Finset.antidiagonal (xyz_pow_n n), coeff x.1 p * coeff x.2 q ≠ 0 → x = (Finsupp.single 0 n, Finsupp.single 1 n + Finsupp.single 2 n) := by
    rintro ⟨x1, x2⟩ h_mem h_ne
    rw [Finset.mem_antidiagonal] at h_mem
    have h_ne1 : coeff x1 p ≠ 0 := fun h => h_ne (by simp [h])
    have h_ne2 : coeff x2 q ≠ 0 := fun h => h_ne (by simp [h])
    have h1 : x1 ∈ p.support := mem_support_iff.mpr h_ne1
    have h2 : x2 ∈ q.support := mem_support_iff.mpr h_ne2
    have hp1 := hp x1 h1
    have hq1 := hq x2 h2
    have hx1 : x1 = Finsupp.single 0 n := by
      ext i
      fin_cases i
      · have h_eq := congr_arg (fun f : Vars →₀ ℕ => f 0) h_mem
        simp [xyz_pow_n, Finsupp.ofSupportFinite_coe, Finsupp.coe_add] at *
        have h_x2_0 : x2 0 = 0 := hq1
        rw [h_x2_0] at h_eq
        omega
      · simp [hp1.1]
      · simp [hp1.2]
    have hx2 : x2 = Finsupp.single 1 n + Finsupp.single 2 n := by
      ext i
      fin_cases i
      · simp [hq1, Finsupp.coe_add]
      · have h_eq := congr_arg (fun f : Vars →₀ ℕ => f 1) h_mem
        simp [xyz_pow_n, Finsupp.ofSupportFinite_coe, Finsupp.coe_add] at *
        rw [hx1] at h_eq
        simp at h_eq
        omega
      · have h_eq := congr_arg (fun f : Vars →₀ ℕ => f 2) h_mem
        simp [xyz_pow_n, Finsupp.ofSupportFinite_coe, Finsupp.coe_add] at *
        rw [hx1] at h_eq
        simp at h_eq
        omega
    rw [hx1, hx2]
  have hi0 : (Finsupp.single 0 n, Finsupp.single 1 n + Finsupp.single 2 n) ∈ Finset.antidiagonal (xyz_pow_n n) := by
    rw [Finset.mem_antidiagonal]
    exact h_sum
  rw [Finset.sum_eq_single (Finsupp.single 0 n, Finsupp.single 1 n + Finsupp.single 2 n)]
  · rintro x h_mem h_ne
    by_contra h_ne_zero
    have h_eq : x = (Finsupp.single 0 n, Finsupp.single 1 n + Finsupp.single 2 n) := h_uniq x h_mem h_ne_zero
    exact h_ne h_eq
  · intro h_not_mem
    exact False.elim (h_not_mem hi0)

