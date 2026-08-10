import FormalConjectures.Util.ProblemImports

open Matrix Nat Int

namespace A226163Dev

/-! ## Development file for the A226163 determinant conjecture.

We develop the proof in pieces here, then assemble into `Spec.lean`.

Key facts established mathematically (numerically verified):
* `det M = 0 ⟺ p ≡ 3 mod 4` where `M[i,j] = legendreSym p (i'^2 - C j')`, `C = m!`, `m=(p-1)/2`.
* Easy direction (`p ≡ 1 ⟹ det ≠ 0`): elementary, via `det M ≡ det[(i²-Cj)^m] mod p`,
  the columns `k=0,m` of the Cauchy–Binet factor coincide (since QR are roots of `X^m-1`),
  leaving a 2-term factor `(nonzero)·F` with `F = 1 + (-1)^m C^{1-m}`, and `C² ≡ (-1)^{m+1}` (Wilson).
* Hard direction (`p ≡ 3 ⟹ det = 0`): spectral cancellation; the key analytic lemma
  (R-realness) is an elementary roots-of-unity identity (no Gauss sum sign needed).
-/

-- Warmup: Wilson-type fact `((p-1)/2)!^2 ≡ (-1)^{(p+1)/2} (mod p)`.
-- In ZMod p: with `m = (p-1)/2`, `(m!)^2 = (-1)^{m+1}`.

/-- `(p-1)! = (-1)^m (m!)^2` in `ZMod p`, where `m = (p-1)/2`. -/
theorem factorial_pred_eq (p : ℕ) [hp : Fact p.Prime] (hodd : Odd p) :
    ((p-1).factorial : ZMod p) = (-1)^((p-1)/2) * ((((p-1)/2).factorial : ZMod p))^2 := by
  set m := (p-1)/2 with hm
  obtain ⟨k, hk⟩ := hodd
  have hp2m : p = 2*m+1 := by simp only [hm]; omega
  have hcast : ((p-1).factorial : ZMod p) = ∏ i ∈ Finset.Ico 1 p, (i : ZMod p) := by
    rw [← Finset.prod_Ico_id_eq_factorial, Nat.cast_prod]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    congr 1; omega
  -- split Ico 1 p = Ico 1 (m+1) ∪ Ico (m+1) p
  have hsplit : ∏ i ∈ Finset.Ico 1 p, (i : ZMod p)
      = (∏ i ∈ Finset.Ico 1 (m+1), (i : ZMod p)) * (∏ i ∈ Finset.Ico (m+1) p, (i : ZMod p)) := by
    rw [← Finset.prod_union]
    · congr 1
      rw [Finset.Ico_union_Ico_eq_Ico] <;> omega
    · apply Finset.Ico_disjoint_Ico_consecutive
  -- first product = m!
  have hfst : ∏ i ∈ Finset.Ico 1 (m+1), (i : ZMod p) = (m.factorial : ZMod p) := by
    rw [← Finset.prod_Ico_id_eq_factorial, Nat.cast_prod]
  -- second product = (-1)^m * m!  via i ↦ p - i
  have hsnd : ∏ i ∈ Finset.Ico (m+1) p, (i : ZMod p) = (-1)^m * (m.factorial : ZMod p) := by
    have hcard : (Finset.Ico (m+1) p).card = m := by rw [Nat.card_Ico]; omega
    -- rewrite each factor (i : ZMod p) = -((p - i : ℕ) : ZMod p)
    have h1 : ∏ i ∈ Finset.Ico (m+1) p, (i : ZMod p)
        = ∏ i ∈ Finset.Ico (m+1) p, (-(((p - i : ℕ) : ZMod p))) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [Finset.mem_Ico] at hi
      have hcast : ((p - i : ℕ) : ZMod p) = (p : ZMod p) - (i : ZMod p) := by
        rw [Nat.cast_sub (by omega)]
      rw [hcast]; simp [ZMod.natCast_self]
    rw [h1]
    -- pull out the (-1)'s
    rw [show (fun i => -(((p - i : ℕ) : ZMod p))) = (fun i => (-1 : ZMod p) * (((p - i : ℕ) : ZMod p))) from by
      funext i; ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
    congr 1
    -- reindex i ↦ p - i  to turn Ico (m+1) p into Ico 1 (m+1)
    rw [← hfst]
    apply Finset.prod_nbij' (fun i => p - i) (fun k => p - k)
    · intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
    · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
    · intro i hi; simp only [Finset.mem_Ico] at hi; omega
    · intro k hk; simp only [Finset.mem_Ico] at hk; omega
    · intro i hi; rfl
  rw [hcast, hsplit, hfst, hsnd]
  ring

theorem wilson_half (p : ℕ) [hp : Fact p.Prime] (hodd : Odd p) :
    ((((p-1)/2).factorial : ZMod p))^2 = (-1)^(((p-1)/2)+1) := by
  have hw : ((p-1).factorial : ZMod p) = -1 := by
    exact_mod_cast ZMod.wilsons_lemma p
  have he := factorial_pred_eq p hodd
  set m := (p-1)/2 with hm
  rw [hw] at he
  -- -1 = (-1)^m * (m!)^2  ⟹  (m!)^2 = (-1)^{m+1}
  have hsq : ((((p-1)/2).factorial : ZMod p))^2 = (-1)^(m+1) := by
    have : (-1 : ZMod p)^m * ((((p-1)/2).factorial : ZMod p))^2 = -1 := he.symm
    have hu : ((-1 : ZMod p)^m) * (-1)^m = 1 := by
      rw [← pow_add]; simp [← two_mul, pow_mul]
    calc ((((p-1)/2).factorial : ZMod p))^2
        = (1 : ZMod p) * ((((p-1)/2).factorial : ZMod p))^2 := by ring
      _ = ((-1:ZMod p)^m * (-1)^m) * ((((p-1)/2).factorial : ZMod p))^2 := by rw [hu]
      _ = (-1)^m * ((-1)^m * ((((p-1)/2).factorial : ZMod p))^2) := by ring
      _ = (-1)^m * (-1) := by rw [this]
      _ = (-1)^(m+1) := by rw [pow_succ]
  rw [hsq, hm]

/-- `m! ≠ 0` in `ZMod p` when `m < p`. -/
theorem factorial_ne_zero (p m : ℕ) [Fact p.Prime] (hmp : m < p) :
    ((m.factorial : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  intro hdvd
  have : p ≤ m := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp hdvd
  omega

/-- `p ∤ choose m k` as a nonzero element of `ZMod p`, when `m < p` and `k ≤ m`. -/
theorem choose_ne_zero (p m k : ℕ) [Fact p.Prime] (hmp : m < p) (hk : k ≤ m) :
    ((m.choose k : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  intro hdvd
  have hfac : p ∣ m.factorial := by
    rw [← Nat.choose_mul_factorial_mul_factorial hk]
    exact (hdvd.mul_right _).mul_right _
  have : p ≤ m := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).mp hfac
  omega

/-- Easy direction: if `p ≡ 1 (mod 4)` then the determinant is nonzero. -/
theorem easy_direction (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1)
    (m : ℕ) (hm : m = (p-1)/2)
    (Mtx : Matrix (Fin m) (Fin m) ℤ)
    (hM : Mtx = fun i j => jacobiSym
      (((i.val+1 : ℕ) : ℤ) * ((i.val+1 : ℕ) : ℤ)
        - ((m.factorial : ℕ) : ℤ) * ((j.val+1 : ℕ) : ℤ)) p) :
    Mtx.det ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · -- p odd; p%4=1 and p prime ⟹ p ≥ 5
      have := hp.two_le; omega
  have hmpos : 0 < m := by omega
  have hmp : m < p := by omega
  have hmeven : m % 2 = 0 := by omega
  -- basic ZMod facts
  set c : ZMod p := ((m.factorial : ℕ) : ZMod p) with hc
  set x : Fin m → ZMod p := fun i => ((i.val + 1 : ℕ) : ZMod p) ^ 2 with hx
  set y : Fin m → ZMod p := fun j => ((j.val + 1 : ℕ) : ZMod p) with hy
  have hcne : c ≠ 0 := factorial_ne_zero p m hmp
  -- the base values are nonzero
  have hbase_ne : ∀ i : Fin m, ((i.val + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro i
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    have := i.isLt
    omega
  -- x i ^ m = 1
  have hxm : ∀ i : Fin m, x i ^ m = 1 := by
    intro i
    show (((i.val + 1 : ℕ) : ZMod p) ^ 2) ^ m = 1
    rw [← pow_mul, show 2 * m = p - 1 from by omega]
    exact ZMod.pow_card_sub_one_eq_one (hbase_ne i)
  -- the matrix over ZMod p
  set Mbar : Matrix (Fin m) (Fin m) (ZMod p) := fun i j => (x i - c * y j) ^ m with hMbar
  -- Step 1: cast of det
  have hcast : ((Mtx.det : ℤ) : ZMod p) = Mbar.det := by
    have hmap : Mtx.map (Int.castRingHom (ZMod p)) = Mbar := by
      ext i j
      rw [Matrix.map_apply, hM]
      simp only
      rw [eq_intCast, ← jacobiSym.legendreSym.to_jacobiSym p, legendreSym.eq_pow]
      show ((_ : ℤ) : ZMod p) ^ (p/2) = (x i - c * y j) ^ m
      congr 1
      · simp only [hx, hy, hc]; push_cast; ring
      · omega
    calc ((Mtx.det : ℤ) : ZMod p)
        = (Int.castRingHom (ZMod p)) Mtx.det := by rw [eq_intCast]
      _ = (Mtx.map (Int.castRingHom (ZMod p))).det := RingHom.map_det _ _
      _ = Mbar.det := by rw [hmap]
  -- Step 2: Mbar = vandermonde x * G  (define G)
  set G : Matrix (Fin m) (Fin m) (ZMod p) :=
    fun l j => (↑(m.choose l.val) : ZMod p) * (-(c * y j)) ^ (m - l.val)
      + (if l.val = 0 then 1 else 0) with hG
  have hfactor : Mbar = (Matrix.vandermonde x) * G := by
    ext i j
    show (x i - c * y j) ^ m = ((Matrix.vandermonde x) * G) i j
    rw [Matrix.mul_apply]
    simp only [Matrix.vandermonde_apply]
    -- expand each summand
    have e1 : ∀ l : Fin m, x i ^ l.val * G l j
        = x i ^ l.val * ((↑(m.choose l.val) : ZMod p) * (-(c * y j)) ^ (m - l.val))
          + x i ^ l.val * (if l.val = 0 then (1 : ZMod p) else 0) := by
      intro l; simp only [hG]; ring
    rw [Finset.sum_congr rfl (fun l _ => e1 l), Finset.sum_add_distrib]
    -- second sum = 1
    have e2 : (∑ l : Fin m, x i ^ l.val * (if l.val = 0 then (1 : ZMod p) else 0)) = 1 := by
      rw [Finset.sum_eq_single (⟨0, hmpos⟩ : Fin m)]
      · simp
      · intro l _ hl
        have : l.val ≠ 0 := by
          intro hc0; apply hl; exact Fin.ext hc0
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    -- first sum = (x i - c y j)^m - 1
    have e3 : (∑ l : Fin m, x i ^ l.val
          * ((↑(m.choose l.val) : ZMod p) * (-(c * y j)) ^ (m - l.val)))
        = (x i - c * y j) ^ m - 1 := by
      have hap : (x i - c * y j) ^ m
          = ∑ k ∈ Finset.range (m+1), x i ^ k * (-(c * y j)) ^ (m - k) * ↑(m.choose k) := by
        rw [show x i - c * y j = x i + -(c * y j) from by ring]
        exact add_pow (x i) (-(c * y j)) m
      rw [Finset.sum_range_succ] at hap
      have hlast : x i ^ m * (-(c * y j)) ^ (m - m) * (↑(m.choose m) : ZMod p) = 1 := by
        rw [Nat.sub_self, Nat.choose_self]; simp [hxm i]
      rw [hlast] at hap
      rw [Fin.sum_univ_eq_sum_range
        (fun k => x i ^ k * ((↑(m.choose k) : ZMod p) * (-(c * y j)) ^ (m - k))) m]
      have hcomm : (∑ k ∈ Finset.range m,
            x i ^ k * ((↑(m.choose k) : ZMod p) * (-(c * y j)) ^ (m - k)))
          = ∑ k ∈ Finset.range m, x i ^ k * (-(c * y j)) ^ (m - k) * ↑(m.choose k) := by
        apply Finset.sum_congr rfl; intro k _; ring
      rw [hcomm, hap]; ring
    rw [e2, e3]; ring
  -- Step 3
  have hdetfac : Mbar.det = (Matrix.vandermonde x).det * G.det := by
    rw [hfactor, Matrix.det_mul]
  -- Step 4: det vandermonde ≠ 0
  have hxinj : Function.Injective x := by
    intro i j hij
    have h : ((i.val+1:ℕ):ZMod p) * ((i.val+1:ℕ):ZMod p)
        = ((j.val+1:ℕ):ZMod p) * ((j.val+1:ℕ):ZMod p) := by
      have h2 : x i = x j := hij
      simp only [hx, pow_two] at h2
      exact h2
    rw [mul_self_eq_mul_self_iff] at h
    have hi := i.isLt; have hj := j.isLt
    rcases h with h | h
    · apply Fin.ext
      have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
      have ha : i.val + 1 < p := by omega
      have hb : j.val + 1 < p := by omega
      have hmm : (i.val+1) % p = (j.val+1) % p := hmod
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmm
      omega
    · exfalso
      have h0 : ((i.val+1:ℕ):ZMod p) + ((j.val+1:ℕ):ZMod p) = 0 := by rw [h]; ring
      rw [← Nat.cast_add, CharP.cast_eq_zero_iff (ZMod p) p] at h0
      have := Nat.le_of_dvd (by omega) h0
      omega
  have hdetV : (Matrix.vandermonde x).det ≠ 0 := by
    rw [Ne, Matrix.det_vandermonde_eq_zero_iff]
    rintro ⟨i, j, hij, hne⟩
    exact hne (hxinj hij)
  -- Step 5: det G ≠ 0
  have hdetG : G.det ≠ 0 := by
    have hodd : Odd p := by rw [Nat.odd_iff]; omega
    -- y injective and vandermonde y nonzero
    have hyinj : Function.Injective y := by
      intro a b hab
      have h : ((a.val+1:ℕ):ZMod p) = ((b.val+1:ℕ):ZMod p) := hab
      have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
      have ha : a.val + 1 < p := by have := a.isLt; omega
      have hb : b.val + 1 < p := by have := b.isLt; omega
      have hmm : (a.val+1) % p = (b.val+1) % p := hmod
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmm
      exact Fin.ext (by omega)
    have hW : (Matrix.vandermonde y).det ≠ 0 := by
      rw [Ne, Matrix.det_vandermonde_eq_zero_iff]
      rintro ⟨a, b, hab, hne⟩; exact hne (hyinj hab)
    -- ∏ y = c
    have hprody : (∏ j : Fin m, y j) = c := by
      rw [hc]
      simp only [hy]
      rw [← Nat.cast_prod, Fin.prod_univ_eq_prod_range (fun k => k+1) m,
        Finset.prod_range_add_one_eq_factorial]
    -- the row-scaling vector d
    set d : Fin m → ZMod p :=
      fun l => (↑(m.choose l.val) : ZMod p) * (-1) ^ (m - l.val) * c ^ (m - l.val) with hd
    have hd_ne : ∀ l : Fin m, d l ≠ 0 := by
      intro l
      simp only [hd]
      apply mul_ne_zero
      apply mul_ne_zero
      · exact choose_ne_zero p m l.val hmp (by have := l.isLt; omega)
      · exact pow_ne_zero _ (by norm_num)
      · exact pow_ne_zero _ hcne
    have hG1eq : ∀ (l j : Fin m),
        (↑(m.choose l.val) : ZMod p) * (-(c * y j)) ^ (m - l.val) = d l * y j ^ (m - l.val) := by
      intro l j
      simp only [hd]
      rw [neg_pow, mul_pow]; ring
    set Vt : Matrix (Fin m) (Fin m) (ZMod p) := (Matrix.vandermonde y)ᵀ with hVt
    set Apure : Matrix (Fin m) (Fin m) (ZMod p) := fun l j => d l * y j ^ (m - l.val) with hAp
    set pt0 : Fin m := ⟨0, hmpos⟩ with hpt0
    -- the negation permutation ρ on Fin m
    set ρf : Fin m → Fin m := fun l => ⟨if l.val = 0 then 0 else m - l.val,
      by have hl := l.isLt; split <;> omega⟩ with hρf
    have hρval : ∀ l : Fin m, (ρf l).val = if l.val = 0 then 0 else m - l.val := fun l => rfl
    have hρinv : Function.Involutive ρf := by
      intro l
      apply Fin.ext
      rw [hρval, hρval]
      have hl := l.isLt
      by_cases h : l.val = 0
      · simp [h]
      · have h2 : ¬ (m - l.val = 0) := by omega
        simp only [h, if_false, h2]; omega
    set ρ : Equiv.Perm (Fin m) := Function.Involutive.toPerm ρf hρinv with hρ
    -- factorization of Apure
    have hApure_eq : Apure = Matrix.diagonal d * (Vt.submatrix Fin.revPerm id) * Matrix.diagonal y := by
      ext l j
      have hl := l.isLt
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      show d l * y j ^ (m - l.val) = d l * (Vt.submatrix Fin.revPerm id) l j * y j
      simp only [hVt, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
        id_eq, Fin.revPerm_apply, Fin.val_rev]
      rw [show m - l.val = (m - (l.val + 1)) + 1 from by omega, pow_succ]; ring
    have hdetApure : Apure.det
        = (∏ l, d l) * (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m)) : ZMod p) * (Matrix.vandermonde y).det
          * (∏ j, y j) := by
      rw [hApure_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
        Matrix.det_permute, hVt, Matrix.det_transpose]
      ring
    -- factorization of Aones (= Apure with row pt0 replaced by ones)
    set ones : Fin m → ZMod p := fun _ => 1 with hones
    set Aones : Matrix (Fin m) (Fin m) (ZMod p) := Matrix.updateRow Apure pt0 ones with hAones
    set d'' : Fin m → ZMod p := fun l => if l.val = 0 then 1 else d l with hd''
    have hAones_eq : Aones = Matrix.diagonal d'' * (Vt.submatrix ρ id) := by
      ext l j
      rw [Matrix.diagonal_mul, hAones, Matrix.updateRow_apply]
      simp only [hVt, hd'', Matrix.submatrix_apply, Matrix.transpose_apply,
        Matrix.vandermonde_apply, id_eq]
      have hρlv : (ρ l).val = if l.val = 0 then 0 else m - l.val := hρval l
      rw [hρlv]
      by_cases h : l.val = 0
      · have hlp : l = pt0 := Fin.ext (by rw [hpt0]; exact h)
        rw [if_pos hlp]
        simp [hones, h]
      · have hne : l ≠ pt0 := by intro hh; apply h; rw [hh, hpt0]
        simp only [if_neg h, if_neg hne]
        rw [hAp]
    have hdetAones : Aones.det
        = (∏ l, d'' l) * (Equiv.Perm.sign ρ : ZMod p) * (Matrix.vandermonde y).det := by
      rw [hAones_eq, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permute, hVt,
        Matrix.det_transpose]
      ring
    -- split det G
    have hGeq : G = Matrix.updateRow Apure pt0 (Apure pt0 + ones) := by
      ext l j
      rw [Matrix.updateRow_apply]
      by_cases h : l = pt0
      · simp only [h, if_pos]
        rw [hG]
        simp only [Pi.add_apply, hones, hAp]
        have : (pt0 : Fin m).val = 0 := by rw [hpt0]
        rw [this]; rw [← hG1eq pt0 j]
        simp [this]
      · rw [if_neg h, hG]
        have hlv : l.val ≠ 0 := by
          intro hh; apply h; exact Fin.ext (by rw [hpt0]; exact hh)
        simp only [hlv, if_false, add_zero]
        rw [hG1eq l j, hAp]
    have hGsplit : G.det = Apure.det + Aones.det := by
      rw [hGeq, det_updateRow_add]
      congr 1
      · congr 1
        ext a b
        rw [Matrix.updateRow_apply]
        by_cases h : a = pt0 <;> simp [h]
    -- now assemble
    rw [hGsplit, hdetApure, hdetAones]
    set s1 : ZMod p := (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m)) : ZMod p) with hs1
    set s2 : ZMod p := (Equiv.Perm.sign ρ : ZMod p) with hs2
    have hs1sq : s1 ^ 2 = 1 := by
      rw [hs1]; rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m))) with h | h <;>
        rw [h] <;> simp
    have hs2sq : s2 ^ 2 = 1 := by
      rw [hs2]; rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h <;>
        rw [h] <;> simp
    -- P := ∏ over complement of pt0
    have hsplitprod : (∏ l, d l) = d pt0 * (∏ l ∈ ({pt0} : Finset (Fin m))ᶜ, d l) :=
      Fintype.prod_eq_mul_prod_compl pt0 d
    set P : ZMod p := (∏ l ∈ ({pt0} : Finset (Fin m))ᶜ, d l) with hP
    have hPne : P ≠ 0 := by
      rw [hP, Finset.prod_ne_zero_iff]
      intro l _; exact hd_ne l
    -- ∏ d'' = P
    have hd''prod : (∏ l, d'' l) = P := by
      rw [hP, Fintype.prod_eq_mul_prod_compl pt0 d'']
      have hd''0 : d'' pt0 = 1 := by rw [hd'']; simp [hpt0]
      rw [hd''0, one_mul]
      apply Finset.prod_congr rfl
      intro l hl
      rw [hd'']
      have : l.val ≠ 0 := by
        intro hh
        rw [Finset.mem_compl, Finset.mem_singleton] at hl
        exact hl (Fin.ext (by rw [hpt0]; exact hh))
      simp [this]
    -- d pt0 = (-1)^m * c^m
    have hdpt0 : d pt0 = (-1)^m * c^m := by
      rw [hd]; simp only [hpt0]; simp
    rw [hsplitprod, hd''prod, hdpt0, hprody]
    -- goal: (-1)^m c^m * P * s1 * W * c + P * s2 * W ≠ 0
    -- rewrite W as (vandermonde y).det
    have hkey : ((-1)^m * c^m) * P * s1 * (Matrix.vandermonde y).det * c
        + P * s2 * (Matrix.vandermonde y).det
        = (Matrix.vandermonde y).det * P * (s1 * (-1)^m * c^(m+1) + s2) := by
      ring
    rw [hkey]
    apply mul_ne_zero
    apply mul_ne_zero hW hPne
    -- bracket ≠ 0
    intro hb
    have heq : s1 * (-1)^m * c^(m+1) = -s2 := eq_neg_of_add_eq_zero_left hb
    have h1 : (s1 * (-1)^m * c^(m+1))^2 = 1 := by rw [heq, neg_sq]; exact hs2sq
    have h2 : (s1 * (-1)^m * c^(m+1))^2 = c^(2*(m+1)) := by
      rw [mul_pow, mul_pow, hs1sq,
        show ((-1:ZMod p)^m)^2 = 1 from by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
        one_mul, one_mul, ← pow_mul]
      ring_nf
    rw [h2] at h1
    have hwil : c ^ 2 = (-1)^(m+1) := by
      have hw := wilson_half p hodd
      rw [← hm] at hw
      rw [← hc] at hw
      exact hw
    have hc2 : c^(2*(m+1)) = -1 := by
      rw [pow_mul, hwil, ← pow_mul]
      apply Odd.neg_one_pow
      have hom1 : Odd (m+1) := Nat.odd_iff.mpr (by omega)
      exact hom1.mul hom1
    rw [hc2] at h1
    -- h1 : (-1 : ZMod p) = 1
    have h2ne : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
      intro hdvd; have := Nat.le_of_dvd (by norm_num) hdvd; omega
    apply h2ne
    have htwo : (1 : ZMod p) + 1 = 0 := by linear_combination -h1
    push_cast
    linear_combination htwo
  -- conclude
  have hMbar_ne : Mbar.det ≠ 0 := by rw [hdetfac]; exact mul_ne_zero hdetV hdetG
  intro hzero
  have hz : ((Mtx.det : ℤ) : ZMod p) = 0 := by rw [hzero]; simp
  rw [hcast] at hz
  exact hMbar_ne hz

/-- Cauchy–Binet "function form": for `A : m × N` and `B : N × m`,
    `det (A * B) = ∑_{f : Fin m → Fin N} (∏ i, A i (f i)) * det (B ∘ f)`. -/
theorem cauchy_binet_f {m N : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin m) (Fin N) R) (B : Matrix (Fin N) (Fin m) R) :
    (A * B).det = ∑ f : Fin m → Fin N, (∏ i, A i (f i)) * (B.submatrix f id).det := by
  conv_lhs => rw [Matrix.det_apply]
  simp only [Matrix.mul_apply]
  -- ∑ σ, sign σ • ∏ i, (∑ k, A (σ i) k * B k i)
  conv_lhs =>
    ext σ
    rw [Finset.prod_univ_sum]
  -- now ∑ σ, sign σ • ∑ f, ∏ i, A (σ i) (f i) * B (f i) i
  rw [Finset.sum_comm']
  sorry

end A226163Dev
