import FormalConjectures.Util.ProblemImports

open Nat BigOperators

/--
A303639: Number of ways to write $n$ as $a^2 + b^2 + \binom{2c+1}{c} + \binom{2d+1}{d}$,
where $a,b,c,d$ are nonnegative integers with $a \le b$ and $c \le d$.
-/
def a (n : ℕ) : ℕ :=
  -- Helper for the binomial coefficient term: B(k) = binomial(2*k+1, k)
  let B (k : ℕ) : ℕ := (2 * k + 1).choose k

  -- The maximum value for $a, b$ is $\lfloor \sqrt{n} \rfloor$.
  -- We can use `Finset.range (n + 1)` as an upper bound for convenience,
  -- but the definition provided uses `n.sqrt + 1`, which is tighter.
  let R_sq := Finset.range (n.sqrt + 1)
  -- The maximum value for $c, d$ is safely bounded by $n$.
  let R_binom := Finset.range (n + 1)

  R_sq.sum fun a =>
    R_sq.sum fun b =>
      R_binom.sum fun c =>
        R_binom.sum fun d =>
          if a ≤ b ∧ c ≤ d ∧ a ^ 2 + b ^ 2 + B c + B d = n then 1 else 0

/-!
The conjecture `a n > 0` for all `n > 1` (Zhi-Wei Sun) is FALSE.
The smallest counterexample is `n = 800322180`, which has no representation
of the form `a^2 + b^2 + C(2c+1,c) + C(2d+1,d)`.
Below we prove `a 800322180 = 0` and hence the negation of the conjecture.
-/

namespace A303639Disproof

/-- If a prime `p ≡ 3 (mod 4)` divides `x^2 + y^2`, then `p` divides both `x` and `y`. -/
theorem core {p x y : ℕ} (hp : p.Prime) (h3 : p % 4 = 3)
    (hdvd : p ∣ x ^ 2 + y ^ 2) : p ∣ x ∧ p ∣ y := by
  haveI : Fact p.Prime := ⟨hp⟩
  have key0 : (x : ZMod p) ^ 2 + (y : ZMod p) ^ 2 = 0 := by
    have h2 : ((x ^ 2 + y ^ 2 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    push_cast at h2; exact h2
  have hy : (y : ZMod p) = 0 := by
    by_contra hy0
    have hyu : (y : ZMod p) * (y : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ hy0
    have hsq : IsSquare (-1 : ZMod p) := by
      refine ⟨(x : ZMod p) * (y : ZMod p)⁻¹, ?_⟩
      have hx2 : (x : ZMod p) ^ 2 = -(y : ZMod p) ^ 2 := by linear_combination key0
      have hyy : (y : ZMod p) ^ 2 * ((y : ZMod p)⁻¹) ^ 2 = 1 := by rw [← mul_pow, hyu, one_pow]
      have hmul : (x : ZMod p) * (y : ZMod p)⁻¹ * ((x : ZMod p) * (y : ZMod p)⁻¹)
          = (x : ZMod p) ^ 2 * ((y : ZMod p)⁻¹) ^ 2 := by ring
      rw [hmul, hx2, neg_mul, hyy]
    exact (ZMod.exists_sq_eq_neg_one_iff (p := p)).1 hsq h3
  have hyd : p ∣ y := (ZMod.natCast_eq_zero_iff y p).1 hy
  have hx : (x : ZMod p) = 0 := by
    have hx2 : (x : ZMod p) ^ 2 = 0 := by rw [hy] at key0; simpa using key0
    exact pow_eq_zero_iff (by norm_num) |>.1 hx2
  have hxd : p ∣ x := (ZMod.natCast_eq_zero_iff x p).1 hx
  exact ⟨hxd, hyd⟩

/-- If `p ≡ 3 (mod 4)` is prime and `p ∤ m`, then `p^(2k+1) * m` is not a sum of two squares. -/
theorem keylem (p : ℕ) (hp : p.Prime) (h3 : p % 4 = 3) :
    ∀ (k m : ℕ), ¬ p ∣ m → ∀ (x y : ℕ), x ^ 2 + y ^ 2 = p ^ (2 * k + 1) * m → False := by
  intro k
  induction k with
  | zero =>
    intro m hm x y h
    have hpm : x ^ 2 + y ^ 2 = p * m := by simpa using h
    have hdvd : p ∣ x ^ 2 + y ^ 2 := by rw [hpm]; exact ⟨m, rfl⟩
    obtain ⟨hx, hy⟩ := core hp h3 hdvd
    obtain ⟨x', rfl⟩ := hx; obtain ⟨y', rfl⟩ := hy
    apply hm
    have heq : p * m = p * (p * (x' ^ 2 + y' ^ 2)) := by rw [← hpm]; ring
    exact ⟨_, Nat.eq_of_mul_eq_mul_left hp.pos heq⟩
  | succ k ih =>
    intro m hm x y h
    have hdvd : p ∣ x ^ 2 + y ^ 2 := by
      rw [h]; exact (dvd_pow_self p (by norm_num)).mul_right m
    obtain ⟨hx, hy⟩ := core hp h3 hdvd
    obtain ⟨x', rfl⟩ := hx; obtain ⟨y', rfl⟩ := hy
    apply ih m hm x' y'
    have hpow : p ^ (2 * (k + 1) + 1) = p ^ 2 * p ^ (2 * k + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow] at h
    have heq : p ^ 2 * (x' ^ 2 + y' ^ 2) = p ^ 2 * (p ^ (2 * k + 1) * m) := by
      have hexp : p ^ 2 * (x' ^ 2 + y' ^ 2) = (p * x') ^ 2 + (p * y') ^ 2 := by ring
      rw [hexp, h]; ring
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) heq

/-- Specialized form: if `r = p^(2k+1) * m` with `p ≡ 3 (mod 4)` prime and `p ∤ m`,
then no `x, y` satisfy `x^2 + y^2 = r`. -/
theorem notSS (r p k m : ℕ) (hp : p.Prime) (h3 : p % 4 = 3)
    (hr : r = p ^ (2 * k + 1) * m) (hm : ¬ p ∣ m) (x y : ℕ) (hxy : x ^ 2 + y ^ 2 = r) : False :=
  keylem p hp h3 k m hm x y (by rw [hxy, hr])

/-- `800322180` cannot be written as `x^2 + y^2 + C(2c+1,c) + C(2d+1,d)`. -/
theorem mainlem : ∀ x y c d : ℕ,
    x ^ 2 + y ^ 2 + (2 * c + 1).choose c + (2 * d + 1).choose d ≠ 800322180 := by
  intro x y c d h
  have hstep : ∀ k, (2*k+1).choose k ≤ (2*(k+1)+1).choose (k+1) := by
    intro k
    have h1 : (2*k+2).choose (k+1) ≤ (2*(k+1)+1).choose (k+1) :=
      Nat.choose_le_choose (k+1) (by omega)
    have h2 : (2*k+2).choose (k+1) = (2*k+1).choose k + (2*k+1).choose (k+1) := by
      rw [show 2*k+2 = (2*k+1)+1 by ring]; exact Nat.choose_succ_succ' (2*k+1) k
    have h3 : (2*k+1).choose (k+1) = (2*k+1).choose k := by
      have hs := Nat.choose_symm (n := 2*k+1) (k := k) (by omega)
      rwa [show (2*k+1) - k = k+1 by omega] at hs
    omega
  have hmono : Monotone (fun k => (2*k+1).choose k) := monotone_nat_of_le_succ hstep
  have hc : c ≤ 15 := by
    by_contra hcon; push_neg at hcon
    have h16c := hmono (show (16:ℕ) ≤ c by omega); simp only [] at h16c
    have hbig : (2*16+1).choose 16 = 1166803110 := by decide
    omega
  have hd : d ≤ 15 := by
    by_contra hcon; push_neg at hcon
    have h16d := hmono (show (16:ℕ) ≤ d by omega); simp only [] at h16d
    have hbig : (2*16+1).choose 16 = 1166803110 := by decide
    omega
  interval_cases c <;> interval_cases d
  · exact notSS 800322178 647 0 1236974 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 800322176 163 0 4909952 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 800322169 67 0 11945107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 800322144 3 0 266774048 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 800322053 23 0 34796611 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 800321717 467 0 1713751 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 800320463 223 0 3588881 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 800315744 991 0 807584 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 800297869 7 0 114328267 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 800229801 3 0 266743267 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 799969463 23 0 34781281 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 798970101 3 0 266323367 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 795121879 887 0 896417 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 780263879 26905651 0 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 722763419 7 0 103251917 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 499781984 1999 0 250016 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*0+1).choose 0 = 1 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 800322176 163 0 4909952 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 800322174 3 1 29641562 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 800322167 643 0 1244669 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 800322142 19 0 42122218 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 800322051 3 0 266774017 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 800321715 3 3 365945 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 800320461 3 0 266773487 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 800315742 3 0 266771914 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 800297867 78607 0 10181 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 800229799 27594131 0 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 799969461 3 0 266656487 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 798970099 31 0 25773229 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 795121877 11 0 72283807 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 780263877 3 0 260087959 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 722763417 3 0 240921139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 499781982 3 0 166593994 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*1+1).choose 1 = 3 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 800322169 67 0 11945107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 800322167 643 0 1244669 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 800322160 11 0 72756560 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 800322135 3 0 266774045 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 800322044 200080511 0 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 800321708 23 0 34796596 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 800320454 284003 0 2818 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 800315735 4326031 0 185 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 800297860 19 0 42120940 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 800229792 3 0 266743264 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 799969454 399984727 0 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 798970092 3 0 266323364 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 795121870 79512187 0 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 780263870 127 0 6143810 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 722763410 2819 0 256390 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 499781975 7 0 71397425 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*2+1).choose 2 = 10 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 800322144 3 0 266774048 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 800322142 19 0 42122218 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 800322135 3 0 266774045 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 800322110 7 0 114331730 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 800322019 7 0 114331717 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 800321683 7 0 114331669 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 800320429 43 0 18612103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 800315710 5843 0 136970 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 800297835 3 0 266765945 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 800229767 7923067 0 101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 799969429 7 0 114281347 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 798970067 7 0 114138581 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 795121845 3 0 265040615 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 780263845 23 0 33924515 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 722763385 23 0 31424495 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 499781950 23 0 21729650 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*3+1).choose 3 = 35 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 800322053 23 0 34796611 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 800322051 3 0 266774017 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 800322044 200080511 0 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 800322019 7 0 114331717 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 800321928 3 0 266773976 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 800321592 3 0 266773864 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 800320338 719 0 1113102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 800315619 3 0 266771873 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 800297744 563 0 1421488 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 800229676 200057419 0 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 799969338 7 0 114281334 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 798969976 7 0 114138568 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 795121754 7 0 113588822 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 780263754 3 0 260087918 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 722763294 3 0 240921098 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 499781859 3 0 166593953 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*4+1).choose 4 = 126 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 800321717 467 0 1713751 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 800321715 3 3 365945 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 800321708 23 0 34796596 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 800321683 7 0 114331669 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 800321592 3 0 266773864 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 800321256 7 0 114331608 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 800320002 3 0 266773334 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 800315283 3 0 266771761 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 800297408 12504647 0 64 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 800229340 23 0 34792580 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 799969002 3 0 266656334 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 798969640 7 0 114138520 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 795121418 7 0 113588774 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 780263418 3 0 260087806 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 722762958 3 0 240920986 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 499781523 3 0 166593841 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*5+1).choose 5 = 462 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 800320463 223 0 3588881 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 800320461 3 0 266773487 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 800320454 284003 0 2818 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 800320429 43 0 18612103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 800320338 719 0 1113102 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 800320002 3 0 266773334 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 800318748 3 0 266772916 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 800314029 19 0 42121791 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 800296154 7 0 114328022 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 800228086 7 0 114318298 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 799967748 3 0 266655916 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 798968386 139 0 5747974 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 795120164 227 0 3502732 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 780262164 11 0 70932924 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 722761704 7 0 103251672 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 499780269 67 0 7459407 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*6+1).choose 6 = 1716 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 800315744 991 0 807584 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 800315742 3 0 266771914 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 800315735 4326031 0 185 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 800315710 5843 0 136970 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 800315619 3 0 266771873 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 800315283 3 0 266771761 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 800314029 19 0 42121791 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 800309310 3 0 266769770 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 800291435 199 0 4021565 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 800223367 31 0 25813657 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 799963029 31 0 25805259 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 798963667 3331 0 239857 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 795115445 139 0 5720255 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 780257445 3 0 260085815 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 722756985 3 0 240918995 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 499775550 3 0 166591850 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*7+1).choose 7 = 6435 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 800297869 7 0 114328267 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 800297867 78607 0 10181 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 800297860 19 0 42120940 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 800297835 3 0 266765945 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 800297744 563 0 1421488 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 800297408 12504647 0 64 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 800296154 7 0 114328022 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 800291435 199 0 4021565 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 800273560 689891 0 1160 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 800205492 3 0 266735164 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 799945154 223 0 3587198 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 798945792 3 0 266315264 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 795097570 59 0 13476230 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 780239570 11 0 70930870 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 722739110 7591 0 95210 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 499757675 19990307 0 25 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*8+1).choose 8 = 24310 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 800229801 3 0 266743267 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 800229799 27594131 0 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 800229792 3 0 266743264 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 800229767 7923067 0 101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 800229676 200057419 0 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 800229340 23 0 34792580 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 800228086 7 0 114318298 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 800223367 31 0 25813657 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 800205492 3 0 266735164 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 800137424 19 0 42112496 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 799877086 887 0 901778 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 798877724 19 0 42046196 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 795029502 3 0 265009834 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 780171502 11 0 70924682 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 722671042 19 0 38035318 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 499689607 19 0 26299453 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*9+1).choose 9 = 92378 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 799969463 23 0 34781281 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 799969461 3 0 266656487 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 799969454 399984727 0 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 799969429 7 0 114281347 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 799969338 7 0 114281334 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 799969002 3 0 266656334 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 799967748 3 0 266655916 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 799963029 31 0 25805259 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 799945154 223 0 3587198 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 799877086 887 0 901778 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 799616748 3 0 266538916 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 798617386 19 0 42032494 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 794769164 7 0 113538452 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 779911164 19 0 41047956 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 722410704 19 0 38021616 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 499429269 19 0 26285751 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*10+1).choose 10 = 352716 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 798970101 3 0 266323367 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 798970099 31 0 25773229 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 798970092 3 0 266323364 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 798970067 7 0 114138581 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 798969976 7 0 114138568 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 798969640 7 0 114138520 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 798968386 139 0 5747974 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 798963667 3331 0 239857 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 798945792 3 0 266315264 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 798877724 19 0 42046196 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 798617386 19 0 42032494 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 797618024 7 0 113945432 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 793769802 3 0 264589934 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 778911802 19 0 40995358 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 721411342 19 0 37969018 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 498429907 19 0 26233153 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*11+1).choose 11 = 1352078 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 795121879 887 0 896417 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 795121877 11 0 72283807 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 795121870 79512187 0 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 795121845 3 0 265040615 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 795121754 7 0 113588822 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 795121418 7 0 113588774 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 795120164 227 0 3502732 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 795115445 139 0 5720255 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 795097570 59 0 13476230 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 795029502 3 0 265009834 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 794769164 7 0 113538452 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 793769802 3 0 264589934 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 789921580 7 0 112845940 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 775063580 19 0 40792820 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 717563120 19 0 37766480 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 494581685 19 0 26030615 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*12+1).choose 12 = 5200300 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 780263879 26905651 0 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 780263877 3 0 260087959 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 780263870 127 0 6143810 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 780263845 23 0 33924515 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 780263754 3 0 260087918 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 780263418 3 0 260087806 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 780262164 11 0 70932924 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 780257445 3 0 260085815 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 780239570 11 0 70930870 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 780171502 11 0 70924682 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 779911164 19 0 41047956 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 778911802 19 0 40995358 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 775063580 19 0 40792820 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 760205580 3 0 253401860 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 702705120 3 0 234235040 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 479723685 3 0 159907895 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*13+1).choose 13 = 20058300 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 722763419 7 0 103251917 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 722763417 3 0 240921139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 722763410 2819 0 256390 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 722763385 23 0 31424495 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 722763294 3 0 240921098 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 722762958 3 0 240920986 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 722761704 7 0 103251672 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 722756985 3 0 240918995 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 722739110 7591 0 95210 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 722671042 19 0 38035318 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 722410704 19 0 38021616 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 721411342 19 0 37969018 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 717563120 19 0 37766480 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 702705120 3 0 234235040 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 645204660 3 0 215068220 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 422223225 3 0 140741075 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*14+1).choose 14 = 77558760 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
  · exact notSS 499781984 1999 0 250016 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*0+1).choose 0 = 1 := (by decide); omega)
  · exact notSS 499781982 3 0 166593994 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*1+1).choose 1 = 3 := (by decide); omega)
  · exact notSS 499781975 7 0 71397425 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*2+1).choose 2 = 10 := (by decide); omega)
  · exact notSS 499781950 23 0 21729650 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*3+1).choose 3 = 35 := (by decide); omega)
  · exact notSS 499781859 3 0 166593953 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*4+1).choose 4 = 126 := (by decide); omega)
  · exact notSS 499781523 3 0 166593841 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*5+1).choose 5 = 462 := (by decide); omega)
  · exact notSS 499780269 67 0 7459407 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*6+1).choose 6 = 1716 := (by decide); omega)
  · exact notSS 499775550 3 0 166591850 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*7+1).choose 7 = 6435 := (by decide); omega)
  · exact notSS 499757675 19990307 0 25 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*8+1).choose 8 = 24310 := (by decide); omega)
  · exact notSS 499689607 19 0 26299453 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*9+1).choose 9 = 92378 := (by decide); omega)
  · exact notSS 499429269 19 0 26285751 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*10+1).choose 10 = 352716 := (by decide); omega)
  · exact notSS 498429907 19 0 26233153 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*11+1).choose 11 = 1352078 := (by decide); omega)
  · exact notSS 494581685 19 0 26030615 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*12+1).choose 12 = 5200300 := (by decide); omega)
  · exact notSS 479723685 3 0 159907895 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*13+1).choose 13 = 20058300 := (by decide); omega)
  · exact notSS 422223225 3 0 140741075 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*14+1).choose 14 = 77558760 := (by decide); omega)
  · exact notSS 199241790 3 0 66413930 (by norm_num) (by norm_num) (by norm_num) (by norm_num) x y (by have e1 : (2*15+1).choose 15 = 300540195 := (by decide); have e2 : (2*15+1).choose 15 = 300540195 := (by decide); omega)
end A303639Disproof

/-- `a 800322180 = 0`: the counterexample has no representation. -/
theorem a_eq_zero : a 800322180 = 0 := by
  unfold a
  refine Finset.sum_eq_zero (fun x _ => ?_)
  refine Finset.sum_eq_zero (fun y _ => ?_)
  refine Finset.sum_eq_zero (fun c _ => ?_)
  refine Finset.sum_eq_zero (fun d _ => ?_)
  rw [if_neg]
  rintro ⟨-, -, heq⟩
  exact A303639Disproof.mainlem x y c d heq

/-- Disproof of the conjecture A303639: it is **not** the case that `a n > 0` for all `n > 1`,
since `a 800322180 = 0`. -/
theorem oeis_a303639_conjecture.disproof : ¬ (∀ (n : ℕ), n > 1 → a n > 0) := by
  intro H
  have hpos := H 800322180 (by norm_num)
  rw [a_eq_zero] at hpos
  exact Nat.lt_irrefl 0 hpos
