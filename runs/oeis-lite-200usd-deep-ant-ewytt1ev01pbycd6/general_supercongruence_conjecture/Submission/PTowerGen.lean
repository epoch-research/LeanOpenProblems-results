import Submission.PTower

/-!
# Generalizing lemmas towards the general-`t` Jacobsthal–Kazandzidis tower

This file collects **fully proven** (sorry-free) generalizations of the
machinery in `Submission.PTower`, aimed at the general-`t` tower congruence

  `p ^ (3*(t+1)) ∣ P A - P B · P (A-B)`   when `p^t ∣ A, B`, `B < A`, `p ≥ 5`.

The single-level (`t = 1`) case `PTower.P_dvd_p6` is already proven there.

The lemmas here generalize two of the core ingredients:

* **General Fermat / Wolstenholme harmonic bound.**  For every `j ≥ 1` with
  `(p-1) ∤ j`, the inverse-`j`-th-power sum vanishes mod `p`, hence
  `1 ≤ v_p (Hs p j)`.  (This generalizes `PTower.one_le_val_H2` and
  `PTower.one_le_val_H3`, which are the special cases `j = 2, 3`.)

* **Generalized power-sum-difference divisibility.**  If `p^s ∣ B` and `p ∣ C`
  and `2 ≤ i ≤ p-1`, then `p^(s+1) ∣ D_i` where
  `D_i = ∑_{k<C} ((B+k)^i - k^i)`.  (This generalizes `PTower.D_dvd`, the case
  `s = 1`, `exponent = 2`.)
-/

open Finset

namespace PTowerGen

open PTower

variable {p : ℕ}

/-! ## General Fermat power-sum vanishing and harmonic bound -/

/-- **General Fermat power-sum vanishing.**  In the finite field `ZMod p`, the
sum `∑_{x} x^i` vanishes whenever `(p-1) ∤ i`.  (When `(p-1) ∣ i` and `i ≠ 0`
the sum is `-1` instead; here we only need the vanishing case.) -/
theorem sum_pow_univ_zero_of_not_dvd (p i : ℕ) [Fact p.Prime]
    (hnd : ¬ (p - 1) ∣ i) : ∑ x : ZMod p, x ^ i = (0 : ZMod p) := by
  classical
  have hi : i ≠ 0 := by rintro rfl; exact hnd (dvd_zero _)
  -- the units of `ZMod p` sit inside `ZMod p` as `ZMod p \ {0}`
  let φ : (ZMod p)ˣ ↪ ZMod p := ⟨fun x => (x : ZMod p), Units.val_injective⟩
  have hmap : (Finset.univ.map φ) = (Finset.univ \ {0} : Finset (ZMod p)) := by
    ext x
    simpa only [Finset.mem_map, Finset.mem_univ, Function.Embedding.coeFn_mk, true_and,
      Finset.mem_sdiff, Finset.mem_singleton, φ] using isUnit_iff_ne_zero
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  -- `q - 1 = p - 1` where `q = card (ZMod p)`
  have hnd' : ¬ (Fintype.card (ZMod p) - 1) ∣ i := by rw [hcard]; exact hnd
  calc
    ∑ x : ZMod p, x ^ i
        = ∑ x ∈ (Finset.univ \ {(0 : ZMod p)}), x ^ i := by
          rw [← Finset.sum_sdiff (Finset.subset_univ ({0} : Finset (ZMod p))),
            Finset.sum_singleton, zero_pow hi, add_zero]
      _ = ∑ x : (ZMod p)ˣ, ((x : ZMod p) ^ i) := by
          rw [← hmap, Finset.sum_map]; rfl
      _ = 0 := by
          rw [FiniteField.sum_pow_units (ZMod p) i, if_neg hnd']

/-- The inverse-`j`-th-power sum over `1, …, p-1` vanishes mod `p` whenever
`(p-1) ∤ j`. -/
theorem sum_inv_pow_zmod_zero (p j : ℕ) [Fact p.Prime] (hnd : ¬ (p - 1) ∣ j) :
    ∑ k ∈ Finset.Icc 1 (p - 1), ((k : ZMod p)⁻¹) ^ j = 0 := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have hj : j ≠ 0 := by rintro rfl; exact hnd (dvd_zero _)
  have hcard : ∑ x : ZMod p, x ^ j = 0 := sum_pow_univ_zero_of_not_dvd p j hnd
  have hinv : ∑ x : ZMod p, (x⁻¹) ^ j = 0 := by
    rw [← hcard]
    exact Equiv.sum_comp
      (Equiv.mk (fun x => x⁻¹) (fun x => x⁻¹) (fun x => inv_inv x) (fun x => inv_inv x))
      (fun y => y ^ j)
  rw [Wolst.sumIcc_eq_sumUniv p (fun x => (x⁻¹) ^ j) (by simp [hj])]
  exact hinv

/-- **General harmonic bound.**  For every `j ≥ 1` with `(p-1) ∤ j`,
`1 ≤ v_p (Hs p j)`.  Generalizes `PTower.one_le_val_H2` (`j = 2`) and
`PTower.one_le_val_H3` (`j = 3`). -/
theorem one_le_val_Hs (p j : ℕ) [Fact p.Prime] (hnd : ¬ (p - 1) ∣ j) :
    (1 : ℤ) ≤ padicValRat p (Hs p j) := by
  have h := le_padicValRat_Hs p j 1 (by rw [pow_one]; exact sum_inv_pow_zmod_zero p j hnd)
  exact_mod_cast h

/-- Packaged as a `vge`. -/
theorem vge_Hs_one (p j : ℕ) [Fact p.Prime] (hnd : ¬ (p - 1) ∣ j) :
    vge p 1 (Hs p j) := Or.inr (one_le_val_Hs p j hnd)

/-! ## Generalized power-sum-difference divisibility

We generalize `PTower.D_dvd`: if `p^s ∣ B` (with `s ≥ 1`) and `p ∣ C`, and
`2 ≤ i ≤ p-1`, then `p^(s+1) ∣ D_i` where
`D_i = ∑_{k<C} ((B+k)^i - k^i)`.  The mechanism is the same as `D_dvd`: modulo
`p^(s+1)` we have `B^2 ≡ 0` (because `2s ≥ s+1`), so the binomial expansion
collapses to `i·B·∑_{k<C} k^(i-1)`, and the inner block power-sum contributes an
extra factor of `p`. -/
theorem D_dvd_gen (p s B C i : ℕ) [Fact p.Prime] (hs : 1 ≤ s)
    (hpB : p ^ s ∣ B) (hpC : p ∣ C) (hi2 : 2 ≤ i) (hip : i ≤ p - 1) :
    ((p : ℤ) ^ (s + 1)) ∣ ∑ k ∈ range C, (((B + k : ℕ) : ℤ) ^ i - (k : ℤ) ^ i) := by
  have hp := (Fact.out : p.Prime)
  haveI : NeZero (p ^ (s + 1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  rw [show ((p : ℤ) ^ (s + 1)) = ((p ^ (s + 1) : ℕ) : ℤ) from by push_cast; ring,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  obtain ⟨b', rfl⟩ := hpB
  obtain ⟨c', rfl⟩ := hpC
  -- `B^2 = 0` in `ZMod (p^(s+1))` since `2s ≥ s+1`.
  have key : (p ^ s * b') ^ 2 = p ^ (s + 1) * (p ^ (s - 1) * b' ^ 2) := by
    have h1 : (p ^ s * b') ^ 2 = p ^ s * p ^ s * b' ^ 2 := by ring
    have h2 : p ^ s * p ^ s = p ^ (s + 1) * p ^ (s - 1) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [h1, h2]; ring
  have hBsq : ((p ^ s * b' : ℕ) : ZMod (p ^ (s + 1))) ^ 2 = 0 := by
    have hz : (p : ZMod (p ^ (s + 1))) ^ (s + 1) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [← Nat.cast_pow, key, Nat.cast_mul, Nat.cast_pow, hz, zero_mul]
  -- write `i = j+1`, `j = i-1 ≥ 1`, `j ≤ p-2`.
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hterm : ∀ k : ℕ,
      ((((p ^ s * b' : ℕ) : ZMod (p ^ (s + 1))) + ((k : ℕ) : ZMod (p ^ (s + 1)))) ^ (j + 1)
          - ((k : ℕ) : ZMod (p ^ (s + 1))) ^ (j + 1))
        = ((j + 1 : ℕ) : ZMod (p ^ (s + 1)))
            * (((p ^ s * b' : ℕ) : ZMod (p ^ (s + 1)))
                * ((k : ℕ) : ZMod (p ^ (s + 1))) ^ j) := by
    intro k
    rw [nilp_binom _ _ hBsq j]; ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, ← Finset.mul_sum]
  -- inner block sum `∑_{k<p*c'} k^j` divisible by `p`.
  set Sm : ℕ := ∑ k ∈ range (p * c'), k ^ j with hSmdef
  have hpSm : p ∣ Sm := by
    have := block_psum p j c' (by omega)
    rw [← ZMod.natCast_eq_zero_iff, hSmdef, Nat.cast_sum]
    simpa using this
  obtain ⟨M, hM⟩ := hpSm
  have hcast : (∑ k ∈ range (p * c'), ((k : ℕ) : ZMod (p ^ (s + 1))) ^ j)
      = ((Sm : ℕ) : ZMod (p ^ (s + 1))) := by
    rw [hSmdef, Nat.cast_sum]; push_cast; rfl
  rw [hcast, hM]
  push_cast
  have hp1 : (p : ZMod (p ^ (s + 1))) ^ (s + 1) = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  linear_combination (((j : ZMod (p ^ (s + 1))) + 1) * (b' : ZMod (p ^ (s + 1)))
    * (M : ZMod (p ^ (s + 1)))) * hp1

/-- `vge` form of `D_dvd_gen`: `v_p(D_i) ≥ s+1` when `p^s ∣ B`, `p ∣ C`,
`2 ≤ i ≤ p-1`.  Generalizes `PTower.vge_DD`. -/
theorem vge_DD_gen (p s B C i : ℕ) [Fact p.Prime] (hs : 1 ≤ s)
    (hpB : p ^ s ∣ B) (hpC : p ∣ C) (hi2 : 2 ≤ i) (hip : i ≤ p - 1) :
    vge p (s + 1) (DD B C i) := by
  have hcast : DD B C i
      = (((∑ k ∈ range C, (((B + k : ℕ) : ℤ) ^ i - (k : ℤ) ^ i)) : ℤ) : ℚ) := by
    rw [DD, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro k _; push_cast; ring
  rw [hcast]
  have := vge_of_int_dvd (D_dvd_gen p s B C i hs hpB hpC hi2 hip)
  simpa using this

/-! ## Generalized block power-sum divisibility

This is the "extra factor" mechanism of point (1) of the general-`t` plan: the
block power-sum over `p^s` complete residue systems is divisible by `p^s`.  It
generalizes `PTower.block_psum` (the case `s = 1`).  We prove `p^s ∣ ∑_{k<p^s·c} k^m`
for `1 ≤ m ≤ p-2` (which forces `(p-1) ∤ m`, the non-degenerate Fermat range). -/

/-- Split a sum over `range (L*M)` into `M` blocks of length `L`. -/
theorem sum_range_block {R : Type*} [AddCommMonoid R] (L M : ℕ) (f : ℕ → R) :
    ∑ k ∈ range (L * M), f k = ∑ a ∈ range M, ∑ j ∈ range L, f (a * L + j) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    ring

/-- **Core block power-sum divisibility** (complete residue system, `c = 1`):
`p^s ∣ ∑_{k<p^s} k^(m'+1)` for `m'+1 ≤ p-2`. -/
theorem blk (p m' : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hmp : m' + 1 ≤ p - 2) (s : ℕ) :
    (p ^ s : ℤ) ∣ ∑ k ∈ range (p ^ s), (k : ℤ) ^ (m' + 1) := by
  have hp := (Fact.out : p.Prime)
  induction s with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · -- `s = 1`: reduce to `block_psum`.
      subst hn0
      haveI : NeZero p := ⟨hp.pos.ne'⟩
      rw [pow_one, pow_one,
        show ((p : ℤ)) = ((p : ℕ) : ℤ) from rfl,
        ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      have hz := block_psum p (m' + 1) 1 hmp
      rw [mul_one] at hz
      simpa using hz
    · -- `n ≥ 1`: binomial collapse plus the induction hypothesis.
      haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero _ hp.pos.ne'⟩
      -- convert IH to a `ℕ` divisibility
      set SN : ℕ := ∑ j ∈ range (p ^ n), j ^ (m' + 1) with hSN
      have ihnat : p ^ n ∣ SN := by
        have hcast : ((SN : ℕ) : ℤ) = ∑ j ∈ range (p ^ n), (j : ℤ) ^ (m' + 1) := by
          rw [hSN]; push_cast; rfl
        have hdvd : ((p ^ n : ℕ) : ℤ) ∣ ((SN : ℕ) : ℤ) := by
          rw [hcast]; exact_mod_cast ih
        exact_mod_cast hdvd
      -- `p` divides the Gauss sum `∑_{a<p} a`
      have hpa : p ∣ ∑ a ∈ range p, a := by
        have h := Finset.sum_range_id_mul_two p
        have hd : p ∣ (∑ a ∈ range p, a) * 2 := by rw [h]; exact Dvd.intro _ rfl
        have hcop : Nat.Coprime p 2 :=
          (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
        exact hcop.dvd_of_dvd_mul_right hd
      -- convert goal to `ZMod (p^(n+1))`
      rw [show ((p : ℤ) ^ (n + 1)) = ((p ^ (n + 1) : ℕ) : ℤ) from by push_cast; ring,
        ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      -- shorthand facts in `ZMod (p^(n+1))`
      have hpn1 : (p : ZMod (p ^ (n + 1))) ^ (n + 1) = 0 := by
        rw [← Nat.cast_pow]; exact ZMod.natCast_self _
      have hX2 : (p : ZMod (p ^ (n + 1))) ^ n * (p : ZMod (p ^ (n + 1))) ^ n = 0 := by
        have hsplit : (p : ZMod (p ^ (n + 1))) ^ n * (p : ZMod (p ^ (n + 1))) ^ n
            = (p : ZMod (p ^ (n + 1))) ^ (n + 1) * (p : ZMod (p ^ (n + 1))) ^ (n - 1) := by
          rw [← pow_add, ← pow_add]; congr 1; omega
        rw [hsplit, hpn1, zero_mul]
      -- expand each block element
      have hterm : ∀ a j : ℕ,
          ((a * p ^ n + j : ℕ) : ZMod (p ^ (n + 1))) ^ (m' + 1)
            = ((j : ℕ) : ZMod (p ^ (n + 1))) ^ (m' + 1)
              + ((m' + 1 : ℕ) : ZMod (p ^ (n + 1)))
                * (((a : ZMod (p ^ (n + 1))) * (p : ZMod (p ^ (n + 1))) ^ n)
                    * ((j : ℕ) : ZMod (p ^ (n + 1))) ^ m') := by
        intro a j
        have hcast : ((a * p ^ n + j : ℕ) : ZMod (p ^ (n + 1)))
            = (a : ZMod (p ^ (n + 1))) * (p : ZMod (p ^ (n + 1))) ^ n
              + ((j : ℕ) : ZMod (p ^ (n + 1))) := by push_cast; ring
        have hx2 : ((a : ZMod (p ^ (n + 1))) * (p : ZMod (p ^ (n + 1))) ^ n) ^ 2 = 0 := by
          have hrw : ((a : ZMod (p ^ (n + 1))) * (p : ZMod (p ^ (n + 1))) ^ n) ^ 2
              = (a : ZMod (p ^ (n + 1))) ^ 2
                * ((p : ZMod (p ^ (n + 1))) ^ n * (p : ZMod (p ^ (n + 1))) ^ n) := by ring
          rw [hrw, hX2, mul_zero]
        rw [hcast, nilp_binom _ _ hx2 m']
      -- reindex into `p` blocks of `p^n`
      rw [show p ^ (n + 1) = p ^ n * p from by rw [pow_succ], sum_range_block]
      -- rewrite each inner block
      have hrw : ∀ a ∈ range p,
          (∑ j ∈ range (p ^ n), ((a * p ^ n + j : ℕ) : ZMod (p ^ (n + 1))) ^ (m' + 1))
            = (∑ j ∈ range (p ^ n), ((j : ℕ) : ZMod (p ^ (n + 1))) ^ (m' + 1))
              + ((m' + 1 : ℕ) : ZMod (p ^ (n + 1)))
                  * ((a : ZMod (p ^ (n + 1))) * (p : ZMod (p ^ (n + 1))) ^ n)
                  * (∑ j ∈ range (p ^ n), ((j : ℕ) : ZMod (p ^ (n + 1))) ^ m') := by
        intro a _
        rw [Finset.sum_congr rfl (fun j _ => hterm a j), Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _; ring
      rw [Finset.sum_congr rfl hrw, Finset.sum_add_distrib]
      -- first block-sum vanishes (uses IH)
      have hpart1 :
          (∑ a ∈ range p, ∑ j ∈ range (p ^ n), ((j : ℕ) : ZMod (p ^ (n + 1))) ^ (m' + 1)) = 0 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        obtain ⟨W, hW⟩ := ihnat
        have hS1 : (∑ j ∈ range (p ^ n), ((j : ℕ) : ZMod (p ^ (n + 1))) ^ (m' + 1))
            = (p : ZMod (p ^ (n + 1))) ^ n * (W : ZMod (p ^ (n + 1))) := by
          have hcast : (∑ j ∈ range (p ^ n), ((j : ℕ) : ZMod (p ^ (n + 1))) ^ (m' + 1))
              = ((SN : ℕ) : ZMod (p ^ (n + 1))) := by rw [hSN]; push_cast; rfl
          rw [hcast, hW]; push_cast; ring
        rw [hS1,
          show (p : ZMod (p ^ (n + 1))) * ((p : ZMod (p ^ (n + 1))) ^ n * (W : ZMod (p ^ (n + 1))))
            = (p : ZMod (p ^ (n + 1))) ^ (n + 1) * (W : ZMod (p ^ (n + 1))) from by ring,
          hpn1, zero_mul]
      -- second block-sum vanishes (uses `p ∣ ∑ a`)
      have hpart2 :
          (∑ a ∈ range p, ((m' + 1 : ℕ) : ZMod (p ^ (n + 1)))
              * ((a : ZMod (p ^ (n + 1))) * (p : ZMod (p ^ (n + 1))) ^ n)
              * (∑ j ∈ range (p ^ n), ((j : ℕ) : ZMod (p ^ (n + 1))) ^ m')) = 0 := by
        have hfac : ∀ a : ℕ,
            ((m' + 1 : ℕ) : ZMod (p ^ (n + 1)))
                * ((a : ZMod (p ^ (n + 1))) * (p : ZMod (p ^ (n + 1))) ^ n)
                * (∑ j ∈ range (p ^ n), ((j : ℕ) : ZMod (p ^ (n + 1))) ^ m')
              = (((m' + 1 : ℕ) : ZMod (p ^ (n + 1))) * (p : ZMod (p ^ (n + 1))) ^ n
                  * (∑ j ∈ range (p ^ n), ((j : ℕ) : ZMod (p ^ (n + 1))) ^ m'))
                * (a : ZMod (p ^ (n + 1))) := fun a => by ring
        rw [Finset.sum_congr rfl (fun a _ => hfac a), ← Finset.mul_sum]
        obtain ⟨V, hV⟩ := hpa
        have hSA : (∑ a ∈ range p, (a : ZMod (p ^ (n + 1)))) = (p : ZMod (p ^ (n + 1))) * (V : ZMod (p ^ (n + 1))) := by
          have h1 : (∑ a ∈ range p, (a : ZMod (p ^ (n + 1)))) = ((∑ a ∈ range p, a : ℕ) : ZMod (p ^ (n + 1))) := by
            push_cast; rfl
          rw [h1, hV]; push_cast; ring
        rw [hSA,
          show (((m' + 1 : ℕ) : ZMod (p ^ (n + 1))) * (p : ZMod (p ^ (n + 1))) ^ n
                * (∑ j ∈ range (p ^ n), ((j : ℕ) : ZMod (p ^ (n + 1))) ^ m'))
              * ((p : ZMod (p ^ (n + 1))) * (V : ZMod (p ^ (n + 1))))
            = ((m' + 1 : ℕ) : ZMod (p ^ (n + 1)))
                * (∑ j ∈ range (p ^ n), ((j : ℕ) : ZMod (p ^ (n + 1))) ^ m')
                * (V : ZMod (p ^ (n + 1))) * (p : ZMod (p ^ (n + 1))) ^ (n + 1) from by ring,
          hpn1, mul_zero]
      rw [hpart1, hpart2, add_zero]

/-- **Generalized block power-sum divisibility.**  For `1 ≤ m'+1 ≤ p-2`,
`p^s ∣ ∑_{k<p^s·c} k^(m'+1)`.  Generalizes `PTower.block_psum` (`s = 1`). -/
theorem block_psum_gen (p s c m' : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hmp : m' + 1 ≤ p - 2) :
    (p ^ s : ℤ) ∣ ∑ k ∈ range (p ^ s * c), (k : ℤ) ^ (m' + 1) := by
  rw [sum_range_block]
  apply Finset.dvd_sum
  intro a _
  have hbase : (p ^ s : ℤ) ∣ ∑ j ∈ range (p ^ s), (j : ℤ) ^ (m' + 1) := blk p m' hp5 hmp s
  have hdiff : (p ^ s : ℤ) ∣
      ∑ j ∈ range (p ^ s), (((a * p ^ s + j : ℕ) : ℤ) ^ (m' + 1) - (j : ℤ) ^ (m' + 1)) := by
    apply Finset.dvd_sum
    intro j _
    have h1 : (p ^ s : ℤ) ∣ ((a * p ^ s + j : ℕ) : ℤ) - (j : ℤ) := by
      have he : ((a * p ^ s + j : ℕ) : ℤ) - (j : ℤ) = (a : ℤ) * (p ^ s : ℤ) := by
        push_cast; ring
      rw [he]; exact dvd_mul_left _ _
    exact dvd_trans h1 (sub_dvd_pow_sub_pow _ _ _)
  have hsplit : (∑ j ∈ range (p ^ s), ((a * p ^ s + j : ℕ) : ℤ) ^ (m' + 1))
      = (∑ j ∈ range (p ^ s), (((a * p ^ s + j : ℕ) : ℤ) ^ (m' + 1) - (j : ℤ) ^ (m' + 1)))
        + ∑ j ∈ range (p ^ s), (j : ℤ) ^ (m' + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _; ring
  rw [hsplit]
  exact dvd_add hdiff hbase

/-! ## Symmetric power-sum-difference divisibility

Combining the binomial expansion with `block_psum_gen`, we obtain the *symmetric*
bound `v_p(D_i) ≥ v_p(B) + v_p(C)` for **all** `1 ≤ i ≤ p-1`, with no constraint
relating `v_p(B)` and `v_p(C)`.  This is the sharp form of point (1) of the
general-`t` plan and strictly strengthens both `PTower.D_dvd` and `D_dvd_gen`. -/
theorem D_dvd_sym (p s s' B C i : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hpB : p ^ s ∣ B) (hpC : p ^ s' ∣ C) (_hi1 : 1 ≤ i) (hip : i ≤ p - 1) :
    ((p : ℤ) ^ (s + s')) ∣ ∑ k ∈ range C, (((B + k : ℕ) : ℤ) ^ i - (k : ℤ) ^ i) := by
  obtain ⟨c', rfl⟩ := hpC
  -- binomial expansion of each summand
  have hexp : ∀ k : ℕ, (((B + k : ℕ) : ℤ) ^ i - (k : ℤ) ^ i)
      = ∑ l ∈ Finset.Ico 1 (i + 1), (B : ℤ) ^ l * (k : ℤ) ^ (i - l) * (i.choose l : ℤ) := by
    intro k
    rw [show (((B + k : ℕ) : ℤ)) = (B : ℤ) + (k : ℤ) from by push_cast; ring, add_pow,
      Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos i),
      show ((B : ℤ) ^ 0 * (k : ℤ) ^ (i - 0) * (i.choose 0 : ℤ)) = (k : ℤ) ^ i from by
        rw [pow_zero, Nat.sub_zero, Nat.choose_zero_right]; push_cast; ring]
    ring
  -- swap the order of summation and factor
  have hD : (∑ k ∈ range (p ^ s' * c'), (((B + k : ℕ) : ℤ) ^ i - (k : ℤ) ^ i))
      = ∑ l ∈ Finset.Ico 1 (i + 1), ((B : ℤ) ^ l * (i.choose l : ℤ)
          * ∑ k ∈ range (p ^ s' * c'), (k : ℤ) ^ (i - l)) := by
    rw [Finset.sum_congr rfl (fun k _ => hexp k), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [hD]
  apply Finset.dvd_sum
  intro l hl
  rw [Finset.mem_Ico] at hl
  -- `p^s ∣ B^l` since `l ≥ 1`
  have hBl : (p : ℤ) ^ s ∣ (B : ℤ) ^ l := by
    obtain ⟨b', rfl⟩ := hpB
    have hcast : ((p ^ s * b' : ℕ) : ℤ) ^ l = (p : ℤ) ^ (s * l) * (b' : ℤ) ^ l := by
      push_cast; rw [mul_pow, ← pow_mul]
    rw [hcast]
    exact Dvd.dvd.mul_right (pow_dvd_pow (p : ℤ) (by nlinarith [hl.1])) _
  -- `p^s' ∣ ∑_{k<C} k^(i-l)` by `block_psum_gen` (or trivially when `i-l = 0`)
  have hCsum : (p : ℤ) ^ s' ∣ ∑ k ∈ range (p ^ s' * c'), (k : ℤ) ^ (i - l) := by
    rcases Nat.eq_zero_or_pos (i - l) with h0 | h1
    · rw [h0]
      simp only [pow_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact ⟨(c' : ℤ), by push_cast; ring⟩
    · obtain ⟨m', hm'⟩ : ∃ m', i - l = m' + 1 := ⟨i - l - 1, by omega⟩
      rw [hm']
      exact block_psum_gen p s' c' m' hp5 (by omega)
  rw [pow_add]
  exact mul_dvd_mul (Dvd.dvd.mul_right hBl _) hCsum

/-- `vge` form of `D_dvd_sym`: `v_p(D_i) ≥ v_p(B)+v_p(C)` for `1 ≤ i ≤ p-1`. -/
theorem vge_DD_sym (p s s' B C i : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hpB : p ^ s ∣ B) (hpC : p ^ s' ∣ C) (hi1 : 1 ≤ i) (hip : i ≤ p - 1) :
    vge p (s + s' : ℕ) (DD B C i) := by
  have hcast : DD B C i
      = (((∑ k ∈ range C, (((B + k : ℕ) : ℤ) ^ i - (k : ℤ) ^ i)) : ℤ) : ℚ) := by
    rw [DD, Int.cast_sum]
    apply Finset.sum_congr rfl
    intro k _; push_cast; ring
  rw [hcast]
  have := vge_of_int_dvd (D_dvd_sym p s s' B C i hp5 hpB hpC hi1 hip)
  simpa using this

/-! ## Odd Wolstenholme bound `v_p(H_j) ≥ 2` for odd `j`

This is the "pairing" ingredient (point (i) of the general-`t` roadmap), carried
out entirely inside `ZMod (p^2)`.  Pairing the residue `r` with `p - r` and using
`(p-r)⁻¹ = -r⁻¹ - p·r⁻²` (valid because `p² = 0` in `ZMod (p²)`) gives, for **odd**
`j`,
  `r⁻ʲ + (p-r)⁻ʲ = -j·p·r⁻⁽ʲ⁺¹⁾`  in `ZMod (p²)`.
Summing and using the `mod p` vanishing of `∑ r⁻⁽ʲ⁺¹⁾` (when `(p-1) ∤ (j+1)`)
shows `∑ r⁻ʲ = 0` in `ZMod (p²)`, hence `v_p(H_j) ≥ 2`.  This strictly generalizes
`PTower.two_le_val_H1` (the case `j = 1`). -/

/-- Uniqueness of inverse in `ZMod n` for a unit. -/
theorem zmod_inv_eq {n : ℕ} {a b : ZMod n} (ha : IsUnit a) (h : a * b = 1) : a⁻¹ = b := by
  calc a⁻¹ = a⁻¹ * 1 := by rw [mul_one]
    _ = a⁻¹ * (a * b) := by rw [h]
    _ = (a⁻¹ * a) * b := by ring
    _ = 1 * b := by rw [ZMod.inv_mul_of_unit a ha]
    _ = b := by rw [one_mul]

/-- Inverse of `p - r` in `ZMod (p²)`: `(p-r)⁻¹ = -r⁻¹ - p·(r⁻¹)²`. -/
theorem inv_p_sub_r (p r : ℕ) [Fact p.Prime] (hr1 : 1 ≤ r) (hrp : r ≤ p - 1) :
    (((p - r : ℕ) : ZMod (p^2)))⁻¹
      = -((r : ZMod (p^2))⁻¹) - (p : ZMod (p^2)) * ((r : ZMod (p^2))⁻¹)^2 := by
  have hp := (Fact.out : p.Prime)
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  have hrunit : IsUnit ((r : ℕ) : ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]
    have hnd : ¬ p ∣ r := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    exact Nat.Coprime.pow_right 2 ((hp.coprime_iff_not_dvd.mpr hnd).symm)
  set ri : ZMod (p^2) := ((r : ℕ) : ZMod (p^2))⁻¹ with hri
  have hrri : ((r : ℕ) : ZMod (p^2)) * ri = 1 := ZMod.mul_inv_of_unit _ hrunit
  have hle : r ≤ p := by omega
  have hcast : (((p - r : ℕ)) : ZMod (p^2)) = (p : ZMod (p^2)) - (r : ZMod (p^2)) := by
    rw [Nat.cast_sub hle]
  have hp2 : (p : ZMod (p^2))^2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  have hprunit : IsUnit (((p - r : ℕ)) : ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]
    have hnd : ¬ p ∣ (p - r) := fun h => by
      have := Nat.le_of_dvd (by omega) h; omega
    exact Nat.Coprime.pow_right 2 ((hp.coprime_iff_not_dvd.mpr hnd).symm)
  rw [hcast]
  apply zmod_inv_eq
  · rwa [hcast] at hprunit
  · have expand : ((p : ZMod (p^2)) - (r : ZMod (p^2))) * (-ri - (p : ZMod (p^2)) * ri^2)
        = -( (p : ZMod (p^2))^2) * ri^2 + (((r:ℕ):ZMod (p^2)) * ri)
          + (p:ZMod (p^2)) * (((r:ℕ):ZMod (p^2)) * ri) * ri - (p : ZMod (p^2)) * ri := by ring
    rw [expand, hp2, hrri]
    ring

/-- Per-term pairing identity in `ZMod (p²)` for odd `j`. -/
theorem pair_term (p r j : ℕ) [Fact p.Prime] (hr1 : 1 ≤ r) (hrp : r ≤ p - 1) (hodd : Odd j) :
    ((r : ZMod (p^2))⁻¹)^j + (((p - r : ℕ) : ZMod (p^2)))⁻¹ ^ j
      = -((j : ZMod (p^2))) * (p : ZMod (p^2)) * ((r : ZMod (p^2))⁻¹)^(j+1) := by
  have hp := (Fact.out : p.Prime)
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  set ri : ZMod (p^2) := ((r : ℕ) : ZMod (p^2))⁻¹ with hri
  have hp2 : (p : ZMod (p^2))^2 = 0 := by rw [← Nat.cast_pow, ZMod.natCast_self]
  rw [inv_p_sub_r p r hr1 hrp]
  have hj1 : 1 ≤ j := hodd.pos
  obtain ⟨m, hm⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hfac : (-ri - (p : ZMod (p^2)) * ri^2) = (-ri) * (1 + (p : ZMod (p^2)) * ri) := by ring
  rw [hfac, mul_pow]
  have hx2 : ((p : ZMod (p^2)) * ri)^2 = 0 := by
    have : ((p : ZMod (p^2)) * ri)^2 = (p : ZMod (p^2))^2 * ri^2 := by ring
    rw [this, hp2, zero_mul]
  have hbin : (1 + (p : ZMod (p^2)) * ri)^j = 1 + (j : ZMod (p^2)) * ((p : ZMod (p^2)) * ri) := by
    rw [hm, add_comm 1 ((p : ZMod (p^2)) * ri), nilp_binom _ _ hx2 m]
    push_cast; ring
  rw [hbin]
  have hodd2 : (-ri)^j = -(ri^j) := hodd.neg_pow ri
  rw [hodd2]
  ring

/-- **Odd Wolstenholme, `ZMod (p²)` form.**  For odd `j` with `(p-1) ∤ (j+1)`,
`∑_{r=1}^{p-1} (r⁻¹)^j = 0` in `ZMod (p²)`. -/
theorem sum_inv_pow_zmod_sq_odd_zero (p j : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hodd : Odd j) (hnd1 : ¬ (p - 1) ∣ (j + 1)) :
    ∑ r ∈ Icc 1 (p - 1), ((r : ZMod (p^2))⁻¹) ^ j = 0 := by
  classical
  have hp := (Fact.out : p.Prime)
  haveI : NeZero (p^2) := ⟨pow_ne_zero 2 hp.pos.ne'⟩
  set s := Icc 1 (p - 1) with hs
  set S := ∑ r ∈ s, ((r : ZMod (p^2))⁻¹) ^ j with hSdef
  have hreidx : S = ∑ r ∈ s, (((p - r : ℕ) : ZMod (p^2)))⁻¹ ^ j := by
    rw [hSdef]
    refine Finset.sum_nbij' (i := fun r => p - r) (j := fun r => p - r) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [hs, mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [hs, mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [hs, mem_Icc] at ha; show p - (p - a) = a; omega
    · intro a ha; simp only [hs, mem_Icc] at ha; show p - (p - a) = a; omega
    · intro a ha; simp only [hs, mem_Icc] at ha
      have hpa : p - (p - a) = a := by omega
      show ((a : ZMod (p^2))⁻¹) ^ j = (((p - (p - a) : ℕ) : ZMod (p^2)))⁻¹ ^ j
      rw [hpa]
  set T := ∑ r ∈ s, ((r : ZMod (p^2))⁻¹) ^ (j + 1) with hTdef
  have h2S : (2 : ZMod (p^2)) * S = -((j : ZMod (p^2))) * (p : ZMod (p^2)) * T := by
    have : (2 : ZMod (p^2)) * S = S + ∑ r ∈ s, (((p - r : ℕ) : ZMod (p^2)))⁻¹ ^ j := by
      rw [← hreidx]; ring
    rw [this, hSdef, ← Finset.sum_add_distrib]
    rw [show (∑ r ∈ s, (((r : ZMod (p^2))⁻¹) ^ j + (((p - r : ℕ) : ZMod (p^2)))⁻¹ ^ j))
        = ∑ r ∈ s, (-((j : ZMod (p^2))) * (p : ZMod (p^2)) * ((r : ZMod (p^2))⁻¹)^(j+1)) from ?_]
    · rw [hTdef, ← Finset.mul_sum, Finset.mul_sum]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [hs, mem_Icc] at hr
      exact pair_term p r j hr.1 hr.2 hodd
  set u : ℕ := (p - 1).factorial with hu
  have hrdvd : ∀ r ∈ s, r ∣ u := by
    intro r hr; rw [hs, mem_Icc] at hr; exact Nat.dvd_factorial (by omega) (by omega)
  have hunit : ∀ r ∈ s, IsUnit ((r : ℕ) : ZMod (p^2)) := by
    intro r hr; rw [ZMod.isUnit_iff_coprime]; rw [hs, mem_Icc] at hr
    have hnd : ¬ p ∣ r := fun h => by have := Nat.le_of_dvd (by omega) h; omega
    exact Nat.Coprime.pow_right 2 ((hp.coprime_iff_not_dvd.mpr hnd).symm)
  have huunit : IsUnit ((u : ℕ) : ZMod (p^2)) := by
    rw [ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.pow_right 2 ?_
    rw [hu]; exact (hp.coprime_iff_not_dvd.mpr (by
      rw [Nat.Prime.dvd_factorial hp]; omega)).symm
  have hscale : ∀ r ∈ s, ((u : ℕ) : ZMod (p^2)) * ((r : ZMod (p^2))⁻¹) = (((u / r : ℕ)) : ZMod (p^2)) := by
    intro r hr
    have hmul : (u / r : ℕ) * r = u := Nat.div_mul_cancel (hrdvd r hr)
    have hbb : ((r : ℕ) : ZMod (p^2)) * ((r : ℕ) : ZMod (p^2))⁻¹ = 1 := ZMod.mul_inv_of_unit _ (hunit r hr)
    calc ((u : ℕ) : ZMod (p^2)) * ((r : ZMod (p^2))⁻¹)
        = (((u / r : ℕ) : ZMod (p^2)) * ((r : ℕ) : ZMod (p^2))) * ((r : ZMod (p^2))⁻¹) := by
            rw [← Nat.cast_mul, hmul]
      _ = ((u / r : ℕ) : ZMod (p^2)) * (((r : ℕ) : ZMod (p^2)) * ((r : ZMod (p^2))⁻¹)) := by ring
      _ = ((u / r : ℕ) : ZMod (p^2)) := by rw [hbb, mul_one]
  set W : ℕ := ∑ r ∈ s, (u / r) ^ (j + 1) with hW
  have huT : ((u : ℕ) : ZMod (p^2))^(j+1) * T = ((W : ℕ) : ZMod (p^2)) := by
    rw [hTdef, Finset.mul_sum, hW, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← mul_pow, hscale r hr, Nat.cast_pow]
  have hpW : p ∣ W := by
    rw [← ZMod.natCast_eq_zero_iff]
    rw [hW, Nat.cast_sum]
    have hz : (∑ r ∈ s, (((u / r : ℕ)) : ZMod p) ^ (j+1)) = 0 := by
      have hrw : (∑ r ∈ s, (((u / r : ℕ)) : ZMod p) ^ (j+1))
          = ((u : ℕ) : ZMod p)^(j+1) * ∑ r ∈ s, (((r : ℕ) : ZMod p)⁻¹) ^ (j+1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        have hunitp : IsUnit ((r : ℕ) : ZMod p) := by
          rw [ZMod.isUnit_iff_coprime]; rw [hs, mem_Icc] at hr
          exact (hp.coprime_iff_not_dvd.mpr (fun h => by have := Nat.le_of_dvd (by omega) h; omega)).symm
        have hmul : (u / r : ℕ) * r = u := Nat.div_mul_cancel (hrdvd r hr)
        have hbb : ((r : ℕ) : ZMod p) * ((r : ℕ) : ZMod p)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hunitp
        rw [← mul_pow]
        congr 1
        calc (((u / r : ℕ)) : ZMod p)
            = (((u / r : ℕ) : ZMod p) * ((r : ℕ) : ZMod p)) * ((r : ℕ) : ZMod p)⁻¹ := by
                rw [mul_assoc, hbb, mul_one]
          _ = ((u : ℕ) : ZMod p) * ((r : ℕ) : ZMod p)⁻¹ := by rw [← Nat.cast_mul, hmul]
      rw [hrw]
      have hthis := sum_inv_pow_zmod_zero p (j+1) hnd1
      rw [hs, hthis, mul_zero]
    simp only [Nat.cast_pow]
    exact hz
  have hpWzero : (p : ZMod (p^2)) * ((W : ℕ) : ZMod (p^2)) = 0 := by
    obtain ⟨W', hW'⟩ := hpW
    have : (p : ZMod (p^2)) * ((W : ℕ) : ZMod (p^2))
        = (p : ZMod (p^2))^2 * ((W' : ℕ) : ZMod (p^2)) := by
      rw [hW']; push_cast; ring
    rw [this, show (p : ZMod (p^2))^2 = 0 from by rw [← Nat.cast_pow, ZMod.natCast_self], zero_mul]
  have hkey : ((u : ℕ) : ZMod (p^2))^(j+1) * ((2 : ZMod (p^2)) * S) = 0 := by
    rw [h2S]
    calc ((u : ℕ) : ZMod (p^2))^(j+1) * (-((j : ZMod (p^2))) * (p : ZMod (p^2)) * T)
        = -((j : ZMod (p^2))) * ((p : ZMod (p^2)) * (((u : ℕ) : ZMod (p^2))^(j+1) * T)) := by ring
      _ = -((j : ZMod (p^2))) * ((p : ZMod (p^2)) * ((W : ℕ) : ZMod (p^2))) := by rw [huT]
      _ = 0 := by rw [hpWzero, mul_zero]
  have hu2 : IsUnit (((u : ℕ) : ZMod (p^2))^(j+1) * (2 : ZMod (p^2))) := by
    refine (huunit.pow (j+1)).mul ?_
    rw [show (2 : ZMod (p^2)) = ((2 : ℕ) : ZMod (p^2)) from by push_cast; ring,
      ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.pow_right 2 ?_
    exact (hp.coprime_iff_not_dvd.mpr (by
      intro h; have := Nat.le_of_dvd (by norm_num) h; omega)).symm
  have hfin : (((u : ℕ) : ZMod (p^2))^(j+1) * (2 : ZMod (p^2))) * S = 0 := by
    rw [show (((u : ℕ) : ZMod (p^2))^(j+1) * (2 : ZMod (p^2))) * S
        = ((u : ℕ) : ZMod (p^2))^(j+1) * ((2 : ZMod (p^2)) * S) from by ring]
    exact hkey
  exact (hu2.mul_right_eq_zero).mp hfin

/-- **Odd Wolstenholme bound.**  For odd `j` with `(p-1) ∤ (j+1)`, `v_p(H_j) ≥ 2`.
Strictly generalizes `PTower.two_le_val_H1` (the case `j = 1`). -/
theorem two_le_val_Hs_odd (p j : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hodd : Odd j) (hnd1 : ¬ (p - 1) ∣ (j + 1)) :
    (2 : ℤ) ≤ padicValRat p (Hs p j) := by
  have h := le_padicValRat_Hs p j 2 (sum_inv_pow_zmod_sq_odd_zero p j hp5 hodd hnd1)
  exact_mod_cast h

/-- Packaged as a `vge`. -/
theorem vge_Hs_two_odd (p j : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hodd : Odd j) (hnd1 : ¬ (p - 1) ∣ (j + 1)) :
    vge p 2 (Hs p j) := Or.inr (two_le_val_Hs_odd p j hp5 hodd hnd1)

/-! ## Towards the general tower crux `crux_gen`

The target is

  `vge p (3*t + 3) (∑ k ∈ Finset.range C, (Fp p (B+k) - Fp p k))`

for `p^t ∣ B, C, A` with `A = B + C`.

The **uniform coefficient bound** below is the key sharpening over the `t = 1`
proof: every coefficient `p^i · e_i` of the crux identity has valuation `≥ 3`
(not just `≥ i`).  Indeed `p·e_1 = p·H_1` has valuation `1 + 2 = 3`
(Wolstenholme), `p²·e_2` has valuation `2 + 1 = 3`, and for `i ≥ 3` the factor
`p^i` already gives `≥ 3`. -/

/-- **Uniform coefficient valuation.**  For `1 ≤ i`, the crux coefficient
`p^i · e_i` has `p`-adic valuation `≥ 3`. -/
theorem vge_pe_three (p i : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hi1 : 1 ≤ i) :
    vge p 3 ((p : ℚ) ^ i * ei p i) := by
  rcases (by omega : i = 1 ∨ i = 2 ∨ 3 ≤ i) with h | h | h
  · subst h
    have hv := vge_mul (vge_ppow (p := p) 1) (Or.inr (two_le_val_H1 p hp5) : vge p 2 (Hs p 1))
    rw [ei_one]
    have : ((1 : ℕ) : ℤ) + 2 = 3 := by norm_num
    rw [this] at hv
    exact hv
  · subst h
    have hv := vge_mul (vge_ppow (p := p) 2) (vge_e2 p hp5)
    have : ((2 : ℕ) : ℤ) + 1 = 3 := by norm_num
    rw [this] at hv
    exact hv
  · have hv := vge_mul (vge_ppow (p := p) i) (vge_ei_zero p i)
    have hle : (3 : ℤ) ≤ ((i : ℕ) : ℤ) + 0 := by
      have : (3 : ℤ) ≤ (i : ℤ) := by exact_mod_cast h
      omega
    exact vge_mono hle hv

/-- **Reduction to a single antidifference.**  With `A = B + C`, the crux sum
equals the "second difference" `R A - R B - R C` of the antidifference
`R n = ∑_{k<n} (Fp p k - 1)`.  This elementary `Finset` identity is the entry
point for the odd-polynomial argument: `R` is an *odd* polynomial in `n` all of
whose coefficients have `v_p ≥ 3`, so only odd powers `n^(2j+1)` survive and
`(B+C)^(2j+1) - B^(2j+1) - C^(2j+1)` is divisible by `A·B·C`. -/
theorem crux_gen_reduction (p B C A : ℕ) (hA : A = B + C) :
    (∑ k ∈ Finset.range C, (Fp p (B + k) - Fp p k))
      = (∑ k ∈ Finset.range A, (Fp p k - 1))
          - (∑ k ∈ Finset.range B, (Fp p k - 1))
          - (∑ k ∈ Finset.range C, (Fp p k - 1)) := by
  subst hA
  rw [Finset.sum_range_add (fun k => Fp p k - 1) B C]
  have hcombine :
      (∑ k ∈ Finset.range C, (Fp p (B + k) - 1))
        - (∑ k ∈ Finset.range C, (Fp p k - 1))
        = ∑ k ∈ Finset.range C, (Fp p (B + k) - Fp p k) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [← hcombine]; ring

/-- **Elementary power-difference divisibility.**  If `p^t ∣ B` and `p^t ∣ C`
then `p^(t*d) ∣ (B+C)^d - B^d - C^d` (each summand is individually divisible by
`p^(t*d)`).  Combined with the coefficient bound `v_p(coeff) ≥ 3`, odd powers
`d = 2j+1 ≥ 3` contribute valuation `≥ 3 + 3t`, which is the mechanism reaching
`3*t + 3`. -/
theorem pow_dvd_power_combo (p t d B C : ℕ) (hB : p ^ t ∣ B) (hC : p ^ t ∣ C) :
    (p : ℤ) ^ (t * d) ∣ (((B + C : ℕ) : ℤ) ^ d - (B : ℤ) ^ d - (C : ℤ) ^ d) := by
  have hpow : ∀ x : ℕ, p ^ t ∣ x → (p : ℤ) ^ (t * d) ∣ (x : ℤ) ^ d := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    refine ⟨(y : ℤ) ^ d, ?_⟩
    push_cast
    rw [mul_pow, ← pow_mul]
  have hBC : p ^ t ∣ (B + C) := Nat.dvd_add hB hC
  exact dvd_sub (dvd_sub (hpow _ hBC) (hpow _ hB)) (hpow _ hC)

/-- **Value bound for the antidifference.**  Every value `R m = ∑_{k<m}(Fp p k - 1)`
has `p`-adic valuation `≥ 3`, since each summand `Fp p k - 1` does
(`Fp_sub_one_vge3`).  This is the value-level input for the coefficient bound. -/
theorem vge_R_value (p m : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    vge p 3 (∑ k ∈ Finset.range m, (Fp p k - 1)) := by
  apply vge_sum
  intro k _
  exact Fp_sub_one_vge3 p k hp5


/-! ## Faulhaber antidifference polynomial and the tower crux `crux_gen` -/

theorem vge_bernoulli (p : ℕ) [Fact p.Prime] (hp2 : 2 ≤ p) :
    ∀ m, m ≤ p - 2 → vge p 0 (bernoulli m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; rw [bernoulli_zero]; exact vge_one p
    · have h := sum_bernoulli (m + 1)
      rw [if_neg (by omega), Finset.sum_range_succ, Nat.choose_succ_self_right] at h
      have hrec : ((m + 1 : ℕ) : ℚ) * bernoulli m
          = -(∑ k ∈ range m, (Nat.choose (m + 1) k : ℚ) * bernoulli k) := by
        linear_combination h
      have hsum : vge p 0 (∑ k ∈ range m, (Nat.choose (m + 1) k : ℚ) * bernoulli k) := by
        apply vge_sum
        intro k hk
        rw [Finset.mem_range] at hk
        have hck : vge p 0 ((Nat.choose (m + 1) k : ℚ)) := by
          rw [show ((Nat.choose (m + 1) k : ℚ)) = (((Nat.choose (m + 1) k : ℤ)) : ℚ) from by push_cast; ring]
          exact vge_int0 _
        have hbk : vge p 0 (bernoulli k) := ih k hk (by omega)
        have := vge_mul hck hbk
        simpa using this
      have hneg : vge p 0 (-(∑ k ∈ range m, (Nat.choose (m + 1) k : ℚ) * bernoulli k)) := by
        have := vge_sub (vge_zero p 0) hsum
        simpa using this
      rw [← hrec] at hneg
      refine vge_cancel_unit (c := ((m + 1 : ℕ) : ℚ)) (by exact_mod_cast Nat.succ_ne_zero m) ?_ hneg
      apply padicValRat_nat_eq_zero
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega

open Polynomial

/-- Faulhaber antidifference polynomial: `Sp i` evaluates to `∑_{k<n} k^i`. -/
noncomputable def Sp (i : ℕ) : ℚ[X] :=
  Polynomial.C ((i : ℚ) + 1)⁻¹ * (Polynomial.bernoulli (i + 1) - Polynomial.C (_root_.bernoulli (i + 1)))

theorem Sp_eval (i n : ℕ) : (Sp i).eval (n : ℚ) = ∑ k ∈ range n, (k : ℚ) ^ i := by
  have hne : ((i : ℚ) + 1) ≠ 0 := by positivity
  have key := sum_range_pow_eq_bernoulli_sub n i
  rw [Sp, eval_mul, eval_C, eval_sub, eval_C, ← key]
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem Fp_sub_one_eq (p k : ℕ) (hp1 : 1 ≤ p) :
    Fp p k - 1 = ∑ i ∈ Icc 1 (p - 1), (p : ℚ) ^ i * ei p i * (k : ℚ) ^ i := by
  rw [F_expand p k hp1, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (show 0 < p by omega)]
  have hf0 : ((p : ℚ) * (k : ℚ)) ^ 0 * ei p 0 = 1 := by rw [pow_zero, one_mul, ei_zero]
  rw [hf0, show (1 : ℚ) + (∑ i ∈ Ico 1 p, ((p : ℚ) * (k : ℚ)) ^ i * ei p i) - 1
        = ∑ i ∈ Ico 1 p, ((p : ℚ) * (k : ℚ)) ^ i * ei p i from by ring]
  have hset : Finset.Ico 1 p = Finset.Icc 1 (p - 1) := by
    ext j; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  rw [hset]
  apply Finset.sum_congr rfl
  intro i _; rw [mul_pow]; ring

noncomputable def Rp (p : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.Icc 1 (p - 1), Polynomial.C ((p : ℚ) ^ i * ei p i) * Sp i

theorem Rp_eval (p n : ℕ) [Fact p.Prime] : (Rp p).eval (n : ℚ) = ∑ k ∈ range n, (Fp p k - 1) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have step : (Rp p).eval (n : ℚ)
      = ∑ k ∈ range n, ∑ i ∈ Icc 1 (p - 1), (p : ℚ) ^ i * ei p i * (k : ℚ) ^ i := by
    rw [Rp, eval_finset_sum]
    rw [Finset.sum_congr rfl (fun i _ => by rw [eval_mul, eval_C, Sp_eval i n, Finset.mul_sum])]
    rw [Finset.sum_comm]
  rw [step]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fp_sub_one_eq p k hp1]

theorem Rp_eval_zero (p : ℕ) [Fact p.Prime] : (Rp p).eval 0 = 0 := by
  have := Rp_eval p 0
  simpa using this

/-- General (rational-argument) expansion of the block product. -/
theorem F_expand_gen (p : ℕ) (y : ℚ) (hp : 1 ≤ p) :
    (∏ r ∈ Icc 1 (p - 1), (1 + ((p : ℚ) * y) * (r : ℚ)⁻¹))
      = ∑ i ∈ range p, ((p : ℚ) * y) ^ i * ei p i := by
  have hcard : (Icc 1 (p - 1)).card + 1 = p := by rw [Nat.card_Icc]; omega
  rw [Finset.prod_one_add, Finset.sum_powerset, hcard]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [ei, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  have hTcard : T.card = j := (mem_powersetCard.mp hT).2
  rw [Finset.prod_mul_distrib, Finset.prod_const, hTcard]

/-- Product reflection: `Block(-1-x) = Block(x)`. -/
theorem prod_refl (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (x : ℚ) :
    (∏ r ∈ Icc 1 (p - 1), (1 + ((p : ℚ) * (-1 - x)) * (r : ℚ)⁻¹))
      = ∏ r ∈ Icc 1 (p - 1), (1 + ((p : ℚ) * x) * (r : ℚ)⁻¹) := by
  have hp := (Fact.out : p.Prime)
  -- nonzeroness of casts on the index set
  have hrpos : ∀ r ∈ Icc 1 (p - 1), (0 : ℚ) < (r : ℚ) := by
    intro r hr; rw [mem_Icc] at hr; exact_mod_cast (by omega : 0 < r)
  have hprne : ∀ r ∈ Icc 1 (p - 1), ((p : ℚ) - (r : ℚ)) ≠ 0 := by
    intro r hr; rw [mem_Icc] at hr
    have : (r : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : r < p)
    linarith
  -- Step 1: reindex r ↦ p - r on the LHS
  have step1 : (∏ r ∈ Icc 1 (p - 1), (1 + ((p : ℚ) * (-1 - x)) * (r : ℚ)⁻¹))
      = ∏ r ∈ Icc 1 (p - 1), (1 + ((p : ℚ) * (-1 - x)) * (((p - r : ℕ) : ℚ))⁻¹) := by
    refine Finset.prod_nbij' (i := fun r => p - r) (j := fun r => p - r) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [mem_Icc] at ha ⊢; omega
    · intro a ha; simp only [mem_Icc] at ha; show p - (p - a) = a; omega
    · intro a ha; simp only [mem_Icc] at ha; show p - (p - a) = a; omega
    · intro a ha; simp only [mem_Icc] at ha; rw [show p - (p - a) = a from by omega]
  rw [step1]
  -- Step 2: termwise L(p-r) = K r * R r
  have step2 : (∏ r ∈ Icc 1 (p - 1), (1 + ((p : ℚ) * (-1 - x)) * (((p - r : ℕ) : ℚ))⁻¹))
      = ∏ r ∈ Icc 1 (p - 1),
          ((-( (r : ℚ) / ((p : ℚ) - (r : ℚ)))) * (1 + ((p : ℚ) * x) * (r : ℚ)⁻¹)) := by
    apply Finset.prod_congr rfl
    intro r hr
    rw [mem_Icc] at hr
    have hrle : r ≤ p := by omega
    have hr0 : (r : ℚ) ≠ 0 := by
      have : (0 : ℚ) < (r : ℚ) := by exact_mod_cast (by omega : 0 < r); 
      linarith
    have hpr0 : ((p : ℚ) - (r : ℚ)) ≠ 0 := hprne r (by rw [mem_Icc]; omega)
    rw [Nat.cast_sub hrle]
    field_simp
    ring
  rw [step2, Finset.prod_mul_distrib]
  -- Step 3: ∏ K r = 1
  have step3 : (∏ r ∈ Icc 1 (p - 1), (-( (r : ℚ) / ((p : ℚ) - (r : ℚ))))) = 1 := by
    have hcard : (Icc 1 (p - 1)).card = p - 1 := by rw [Nat.card_Icc]; omega
    have hnum : (∏ r ∈ Icc 1 (p - 1), ((p : ℚ) - (r : ℚ)))
        = ∏ r ∈ Icc 1 (p - 1), (r : ℚ) := by
      refine Finset.prod_nbij' (i := fun r => p - r) (j := fun r => p - r) ?_ ?_ ?_ ?_ ?_
      · intro a ha; simp only [mem_Icc] at ha ⊢; omega
      · intro a ha; simp only [mem_Icc] at ha ⊢; omega
      · intro a ha; simp only [mem_Icc] at ha; show p - (p - a) = a; omega
      · intro a ha; simp only [mem_Icc] at ha; show p - (p - a) = a; omega
      · intro a ha; simp only [mem_Icc] at ha
        have : a ≤ p := by omega
        rw [Nat.cast_sub this]
    have hprodpos : (∏ r ∈ Icc 1 (p - 1), (r : ℚ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro r hr; exact ne_of_gt (hrpos r hr)
    have hodd : Odd p := hp.odd_of_ne_two (by omega)
    have heven : Even (p - 1) := by rcases hodd with ⟨j, hj⟩; exact ⟨j, by omega⟩
    calc (∏ r ∈ Icc 1 (p - 1), (-( (r : ℚ) / ((p : ℚ) - (r : ℚ)))))
        = (∏ r ∈ Icc 1 (p - 1), (-1 : ℚ))
            * ∏ r ∈ Icc 1 (p - 1), ((r : ℚ) / ((p : ℚ) - (r : ℚ))) := by
          rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro r _; ring
      _ = (-1 : ℚ) ^ (p - 1)
            * ((∏ r ∈ Icc 1 (p - 1), (r : ℚ)) / (∏ r ∈ Icc 1 (p - 1), ((p : ℚ) - (r : ℚ)))) := by
          rw [Finset.prod_const, hcard, Finset.prod_div_distrib]
      _ = (-1 : ℚ) ^ (p - 1) * 1 := by rw [hnum, div_self hprodpos]
      _ = 1 := by rw [mul_one, heven.neg_one_pow]
  rw [step3, one_mul]

/-- The `Fp`-expansion polynomial `g(X) = ∑_{i=1}^{p-1} (p^i e_i) X^i`. -/
noncomputable def gp (p : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.Icc 1 (p - 1), Polynomial.C ((p : ℚ) ^ i * ei p i) * X ^ i

theorem gp_eval (p : ℕ) (x : ℚ) :
    (gp p).eval x = ∑ i ∈ Icc 1 (p - 1), (p : ℚ) ^ i * ei p i * x ^ i := by
  rw [gp, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro i _; rw [eval_mul, eval_C, eval_pow, eval_X]

theorem one_add_gp_eval (p : ℕ) (x : ℚ) (hp1 : 1 ≤ p) :
    1 + (gp p).eval x = ∏ r ∈ Icc 1 (p - 1), (1 + ((p : ℚ) * x) * (r : ℚ)⁻¹) := by
  rw [gp_eval, F_expand_gen p x hp1, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (show 0 < p by omega)]
  have hset : Finset.Ico 1 p = Finset.Icc 1 (p - 1) := by
    ext j; simp only [mem_Ico, mem_Icc]; omega
  rw [hset, pow_zero, one_mul, ei_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _; rw [mul_pow]; ring

theorem gp_eval_refl (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (x : ℚ) :
    (gp p).eval (-1 - x) = (gp p).eval x := by
  have hp1 : 1 ≤ p := by omega
  have h1 := one_add_gp_eval p (-1 - x) hp1
  have h2 := one_add_gp_eval p x hp1
  have hr := prod_refl p hp5 x
  have : 1 + (gp p).eval (-1 - x) = 1 + (gp p).eval x := by rw [h1, hr, ← h2]
  linarith

theorem gp_reflect (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : (gp p).comp (-1 - X) = gp p := by
  apply eq_of_infinite_eval_eq
  have huniv : {x : ℚ | eval x ((gp p).comp (-1 - X)) = eval x (gp p)} = Set.univ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, eval_comp]
    have hev : eval x (-1 - X : ℚ[X]) = -1 - x := by simp
    rw [hev, gp_eval_refl p hp5 x]
  rw [huniv]; exact Set.infinite_univ

theorem Rp_diff (p : ℕ) [Fact p.Prime] : (Rp p).comp (X + 1) - Rp p = gp p := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  apply eq_of_infinite_eval_eq
  have hsub : Set.range (fun n : ℕ => (n : ℚ))
      ⊆ {x : ℚ | eval x ((Rp p).comp (X + 1) - Rp p) = eval x (gp p)} := by
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_setOf_eq, eval_sub, eval_comp]
    have hev : eval (n : ℚ) (X + 1 : ℚ[X]) = (n : ℚ) + 1 := by simp
    rw [hev]
    have e1 : eval ((n : ℚ) + 1) (Rp p) = ∑ k ∈ range (n + 1), (Fp p k - 1) := by
      rw [show ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) from by push_cast; ring, Rp_eval]
    have e2 : eval (n : ℚ) (Rp p) = ∑ k ∈ range n, (Fp p k - 1) := Rp_eval p n
    have e3 : eval (n : ℚ) (gp p) = Fp p n - 1 := by
      rw [gp_eval, ← Fp_sub_one_eq p n hp1]
    rw [e1, e2, e3, Finset.sum_range_succ]; ring
  exact (Set.infinite_range_of_injective (fun a b hh => by exact_mod_cast hh)).mono hsub

theorem poly_const_of_shift (P : ℚ[X]) (h : P.comp (X + 1) = P) (h0 : P.eval 0 = 0) : P = 0 := by
  apply eq_of_infinite_eval_eq
  have hall : ∀ n : ℕ, P.eval (n : ℚ) = 0 := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ m ih =>
      have hstep : P.eval ((m : ℚ) + 1) = P.eval (m : ℚ) := by
        have hc := congr_arg (eval (m : ℚ)) h
        rwa [eval_comp, show eval (m : ℚ) (X + 1 : ℚ[X]) = (m : ℚ) + 1 from by simp] at hc
      rw [show ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 from by push_cast; ring, hstep, ih]
  have hsub : Set.range (fun n : ℕ => (n : ℚ)) ⊆ {x : ℚ | eval x P = eval x 0} := by
    rintro _ ⟨n, rfl⟩; simp only [Set.mem_setOf_eq, eval_zero]; exact hall n
  exact (Set.infinite_range_of_injective (fun a b hh => by exact_mod_cast hh)).mono hsub

theorem antidiff_odd (Q h : ℚ[X]) (hdiff : Q.comp (X + 1) - Q = h) (h0 : Q.eval 0 = 0)
    (hrefl : h.comp (-1 - X) = h) : Q.comp (-X) = -Q := by
  have hQcomp : Q.comp (-X) - Q.comp (-1 - X) = h := by
    have hc := congr_arg (fun r : ℚ[X] => r.comp (-1 - X)) hdiff
    simp only [sub_comp] at hc
    rw [comp_assoc] at hc
    have hxc : (X + 1 : ℚ[X]).comp (-1 - X) = -X := by
      rw [add_comp, X_comp, one_comp]; ring
    rw [hxc, hrefl] at hc
    exact hc
  have hP : (Q + Q.comp (-X)) = 0 := by
    apply poly_const_of_shift
    · rw [add_comp, comp_assoc]
      have hxc2 : (-X : ℚ[X]).comp (X + 1) = -1 - X := by
        rw [neg_comp, X_comp]; ring
      rw [hxc2]
      have hd : Q.comp (X + 1) = Q + h := by linear_combination hdiff
      rw [hd]
      linear_combination -hQcomp
    · simp only [eval_add, eval_comp, eval_neg, eval_X, neg_zero, h0, add_zero]
  linear_combination hP

theorem Rp_odd (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : (Rp p).comp (-X) = -(Rp p) :=
  antidiff_odd (Rp p) (gp p) (Rp_diff p) (Rp_eval_zero p) (gp_reflect p hp5)

theorem Rp_coeff_two (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) : (Rp p).coeff 2 = 0 := by
  have hodd := Rp_odd p hp5
  have hX : (-X : ℚ[X]) = Polynomial.C (-1) * X := by rw [C_neg, C_1, neg_one_mul]
  have h1 : ((Rp p).comp (-X)).coeff 2 = (Rp p).coeff 2 := by
    rw [hX, comp_C_mul_X_coeff]; ring
  rw [hodd, coeff_neg] at h1
  linarith [h1]

theorem vge_Rp_coeff (p d : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hd : 2 ≤ d) :
    vge p 3 ((Rp p).coeff d) := by
  have hcoeff : (Rp p).coeff d
      = ∑ i ∈ Icc 1 (p - 1), ((p : ℚ) ^ i * ei p i) * (Sp i).coeff d := by
    rw [Rp, finset_sum_coeff]
    apply Finset.sum_congr rfl
    intro i _; rw [coeff_C_mul]
  rw [hcoeff]
  apply vge_sum
  intro i hi
  rw [mem_Icc] at hi
  have hSc : (Sp i).coeff d
      = ((i : ℚ) + 1)⁻¹ * (Polynomial.bernoulli (i + 1)).coeff d := by
    rw [Sp, coeff_C_mul, coeff_sub, coeff_C, if_neg (by omega : ¬ (d = 0)), sub_zero]
  rw [coeff_bernoulli] at hSc
  by_cases hdi : d ≤ i + 1
  · rw [if_pos hdi] at hSc
    rw [hSc]
    -- factor valuations
    have vbern : vge p 0 (bernoulli (i + 1 - d)) :=
      vge_bernoulli p (by omega) (i + 1 - d) (by omega)
    have vchoose : vge p 0 (((i + 1).choose d : ℚ)) := by
      rw [show (((i + 1).choose d : ℚ)) = ((((i + 1).choose d : ℕ) : ℤ) : ℚ) from by push_cast; ring]
      exact vge_int0 _
    have vinner0 : vge p 0 (_root_.bernoulli (i + 1 - d) * ((i + 1).choose d : ℚ)) := by
      have := vge_mul vbern vchoose; simpa using this
    by_cases hile : i ≤ p - 2
    · have vpe : vge p 3 ((p : ℚ) ^ i * ei p i) := vge_pe_three p i hp5 hi.1
      have vinv : vge p 0 (((i : ℚ) + 1)⁻¹) := by
        refine Or.inr ?_
        have hc0 : ((i : ℚ) + 1) ≠ 0 := by positivity
        have hcv : padicValRat p ((i : ℚ) + 1) = 0 := by
          rw [show ((i : ℚ) + 1) = ((i + 1 : ℕ) : ℚ) from by push_cast; ring]
          exact padicValRat_nat_eq_zero (fun h => by have := Nat.le_of_dvd (by omega) h; omega)
        rw [show (((i : ℚ) + 1))⁻¹ = 1 / ((i : ℚ) + 1) from by rw [one_div],
          padicValRat.div one_ne_zero hc0, hcv]
        simp
      have vmid := vge_mul vinv vinner0
      have := vge_mul vpe vmid
      exact vge_mono (by norm_num) this
    · have hie : i = p - 1 := by omega
      have vpe : vge p (i : ℤ) ((p : ℚ) ^ i * ei p i) := by
        have := vge_mul (vge_ppow (p := p) i) (vge_ei_zero p i); rwa [add_zero] at this
      have vinv2 : vge p (-1 : ℤ) (((i : ℚ) + 1)⁻¹) := by
        refine Or.inr ?_
        have hc0 : ((i : ℚ) + 1) ≠ 0 := by positivity
        have hcv : padicValRat p ((i : ℚ) + 1) = 1 := by
          have hip : ((i : ℚ) + 1) = (p : ℚ) := by
            rw [hie, Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; ring
          rw [hip, padicValRat.of_nat, padicValNat.self (Fact.out : p.Prime).one_lt, Nat.cast_one]
        rw [show (((i : ℚ) + 1))⁻¹ = 1 / ((i : ℚ) + 1) from by rw [one_div],
          padicValRat.div one_ne_zero hc0, hcv]
        simp
      have vmid := vge_mul vinv2 vinner0
      have hfin := vge_mul vpe vmid
      refine vge_mono ?_ hfin
      have h4 : 4 ≤ i := by omega
      have hc4 : (4 : ℤ) ≤ (i : ℤ) := by exact_mod_cast h4
      omega
  · rw [if_neg hdi, mul_zero] at hSc
    rw [hSc, mul_zero]
    exact vge_zero p 3

theorem crux_gen (p t B C A : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hA : A = B + C) (hpB : p ^ t ∣ B) (hpC : p ^ t ∣ C) (hpA : p ^ t ∣ A) :
    vge p (3 * t + 3) (∑ k ∈ range C, (Fp p (B + k) - Fp p k)) := by
  rw [crux_gen_reduction p B C A hA, ← Rp_eval p A, ← Rp_eval p B, ← Rp_eval p C]
  have key : (Rp p).eval (A : ℚ) - (Rp p).eval (B : ℚ) - (Rp p).eval (C : ℚ)
      = ∑ d ∈ range ((Rp p).natDegree + 1),
          (Rp p).coeff d * ((A : ℚ) ^ d - (B : ℚ) ^ d - (C : ℚ) ^ d) := by
    rw [Polynomial.eval_eq_sum_range (A : ℚ), Polynomial.eval_eq_sum_range (B : ℚ),
      Polynomial.eval_eq_sum_range (C : ℚ), ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _; ring
  rw [key]
  apply vge_sum
  intro d _
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ 3 ≤ d) with h0 | h1 | h2 | h3
  · -- d = 0 : coeff 0 = 0
    subst h0
    have : (Rp p).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]; exact Rp_eval_zero p
    rw [this, zero_mul]; exact vge_zero _ _
  · -- d = 1 : A - B - C = 0
    subst h1
    have hz : (A : ℚ) ^ 1 - (B : ℚ) ^ 1 - (C : ℚ) ^ 1 = 0 := by
      have : (A : ℚ) = (B : ℚ) + (C : ℚ) := by rw [hA]; push_cast; ring
      rw [this]; ring
    rw [hz, mul_zero]; exact vge_zero _ _
  · -- d = 2 : coeff 2 = 0
    subst h2
    rw [Rp_coeff_two p hp5, zero_mul]; exact vge_zero _ _
  · -- d ≥ 3
    have hcoeffv : vge p 3 ((Rp p).coeff d) := vge_Rp_coeff p d hp5 (by omega)
    have hcombo := pow_dvd_power_combo p t d B C hpB hpC
    have hAeq : ((B + C : ℕ) : ℤ) = (A : ℤ) := by rw [hA]
    rw [hAeq] at hcombo
    have hv : vge p ((t * d : ℕ) : ℤ)
        (((A : ℤ) ^ d - (B : ℤ) ^ d - (C : ℤ) ^ d : ℤ) : ℚ) := vge_of_int_dvd hcombo
    have hcast : (((A : ℤ) ^ d - (B : ℤ) ^ d - (C : ℤ) ^ d : ℤ) : ℚ)
        = (A : ℚ) ^ d - (B : ℚ) ^ d - (C : ℚ) ^ d := by push_cast; ring
    rw [hcast] at hv
    have hle : (3 * (t : ℤ)) ≤ ((t * d : ℕ) : ℤ) := by
      have hn : 3 * t ≤ t * d := by
        calc 3 * t = t * 3 := by ring
          _ ≤ t * d := by exact Nat.mul_le_mul_left t (by omega)
      exact_mod_cast hn
    have hprod := vge_mul hcoeffv (vge_mono hle hv)
    rw [show (3 : ℤ) + 3 * (t : ℤ) = 3 * (t : ℤ) + 3 from by ring] at hprod
    exact hprod


/-! ## Reduction of `P_tower_dvd` to the product-difference bound

The following are **fully proven (sorry-free)** ingredients toward the general
tower congruence

  `p ^ (3*(t+1)) ∣ P A - P B · P (A-B)`   when `p^t ∣ A, B`, `B < A`, `p ≥ 5`.

`crux_gen` above already proves the *linear* (single-index) difference bound
`vge p (3t+3) (∑_{k<C}(Fp(B+k) - Fp k))`.  The remaining step is the
**product** difference
`vge p (3t+3) (∏_{k<C} Fp(B+k) - ∏_{k<C} Fp k)`, from which `P_tower_dvd`
follows by the factorisation `P_eq`.  We provide here:

* `int_dvd_of_vge_gen` — the general `vge → ℤ`-divisibility converter (the
  `PTower.int_dvd_of_vge` is hard-coded to exponent `6`);
* `P_tower_reduce` — reduces `P_tower_dvd` to the product-difference `vge`;
* `prod_diff_high` — the "high subset" contribution (subsets of size `≥ t+1`)
  to the powerset expansion of the product difference already has `vge (3t+3)`
  directly, isolating the genuine remaining work to subsets of size `1 … t`. -/

/-- **General `vge → ℤ`-divisibility.**  From `vge p k (N:ℚ)` conclude
`p^k ∣ N` for an integer `N`.  Generalizes `PTower.int_dvd_of_vge` (exponent 6). -/
theorem int_dvd_of_vge_gen {p : ℕ} [Fact p.Prime] {k : ℕ} {N : ℤ}
    (h : vge p (k : ℤ) ((N : ℚ))) : (p : ℤ) ^ k ∣ N := by
  rcases h with h0 | h1
  · have : N = 0 := by exact_mod_cast h0
    rw [this]; exact dvd_zero _
  · by_cases hN : N = 0
    · rw [hN]; exact dvd_zero _
    have hNn : N.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hN
    rw [show ((N : ℚ)) = ((N : ℤ) : ℚ) from rfl, padicValRat.of_int] at h1
    have h2 : (k : ℤ) ≤ (padicValNat p N.natAbs : ℤ) := h1
    have h3 : k ≤ padicValNat p N.natAbs := by exact_mod_cast h2
    have hpk : p ^ k ∣ N.natAbs := (padicValNat_dvd_iff_le hNn).mpr h3
    have hthis : (p : ℤ) ^ k ∣ (N.natAbs : ℤ) := by exact_mod_cast hpk
    exact Int.dvd_natAbs.mp hthis

/-- **Reduction to the product difference.**  If the product difference
`∏_{k<A-B} Fp(B+k) - ∏_{k<A-B} Fp k` has `vge p (3t+3)`, then
`p^(3*(t+1)) ∣ P A - P B · P (A-B)`.  This is the analogue of
`PTower.P_dvd_p6` for general `t`, deferring only the product-difference bound. -/
theorem P_tower_reduce (p t A B : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hBA : B < A)
    (hv : vge p (3 * t + 3)
      ((∏ k ∈ range (A - B), Fp p (B + k)) - (∏ k ∈ range (A - B), Fp p k))) :
    (p : ℤ) ^ (3 * (t + 1)) ∣
      ((JacobRef.P p A : ℤ) - (JacobRef.P p B : ℤ) * (JacobRef.P p (A - B) : ℤ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set C := A - B with hC
  have hBC : B + C = A := by omega
  have hp0 : 0 < p := hp.pos
  have hNQ : (((JacobRef.P p A : ℤ) - (JacobRef.P p B : ℤ) * (JacobRef.P p C : ℤ) : ℤ) : ℚ)
      = (uu p) ^ A * (∏ j ∈ range B, Fp p j)
          * ((∏ k ∈ range C, Fp p (B + k)) - (∏ k ∈ range C, Fp p k)) := by
    push_cast
    rw [P_eq p A hp0, P_eq p B hp0, P_eq p C hp0, show A = B + C from hBC.symm,
      Finset.prod_range_add, pow_add]
    ring
  apply int_dvd_of_vge_gen (k := 3 * (t + 1))
  rw [hNQ]
  have v1 : vge p 0 ((uu p) ^ A) := vge_pow_zero (vge_uu p) A
  have v2 : vge p 0 (∏ j ∈ range B, Fp p j) := by
    have := vge_prod (range B) (fun j => Fp p j) 0 (fun j _ => vge_Fp p j hp5)
    rwa [zero_mul] at this
  have key := vge_mul (vge_mul v1 v2) hv
  have he : ((3 * (t + 1) : ℕ) : ℤ) = 0 + 0 + (3 * (t : ℤ) + 3) := by push_cast; ring
  rw [he]
  exact key

/-- **High-subset contribution.**  In the powerset expansion of the product
difference, every subset `T ⊆ range C` with `|T| ≥ t+1` contributes a term
`∏_{k∈T}(Fp(B+k)-1) - ∏_{k∈T}(Fp k -1)` with `vge p (3t+3)` (each factor has
`vge 3`, so a `≥ t+1`-fold product has `vge ≥ 3(t+1) = 3t+3`).  Thus the only
genuinely remaining work for the full product difference is the low-subset part
(subsets of size `1 … t`), which requires the power-sum/Newton cancellation. -/
theorem prod_diff_high (p t B C : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    vge p (3 * t + 3)
      (∑ T ∈ (range C).powerset.filter (fun T => t + 1 ≤ T.card),
        ((∏ k ∈ T, (Fp p (B + k) - 1)) - (∏ k ∈ T, (Fp p k - 1)))) := by
  apply vge_sum
  intro T hT
  rw [mem_filter, Finset.mem_powerset] at hT
  obtain ⟨_, hcard⟩ := hT
  have va : vge p (3 * T.card) (∏ k ∈ T, (Fp p (B + k) - 1)) :=
    vge_prod T _ 3 (fun k _ => Fp_sub_one_vge3 p (B + k) hp5)
  have vb : vge p (3 * T.card) (∏ k ∈ T, (Fp p k - 1)) :=
    vge_prod T _ 3 (fun k _ => Fp_sub_one_vge3 p k hp5)
  have h3 : (3 * (t : ℤ) + 3) ≤ 3 * (T.card : ℤ) := by
    have : ((t : ℤ) + 1) ≤ (T.card : ℤ) := by exact_mod_cast hcard
    linarith
  exact vge_sub (vge_mono h3 va) (vge_mono h3 vb)

/-! ## Generic Faulhaber antidifference and the power-sum machinery (Step A infrastructure)

The following develop the tools needed for `crux_gen_pow`, the power-sum analogue
of `crux_gen`.  For a polynomial `h`, we build its Faulhaber antidifference
`RpP h` (the unique polynomial with `(RpP h)(n+1) - (RpP h)(n) = h(n)` and
`(RpP h)(0) = 0`), and record:

* `RpP_diff`, `RpP_eval`, `RpP_eval_zero` — the defining properties;
* `RpP_gp_pow_odd` — for `h = (gp p)^l` (which is reflection-symmetric), the
  antidifference is an *odd* polynomial, hence its even-degree coefficients vanish
  (`RpP_gp_pow_coeff_even`);
* `vge_gp_coeff` / `vge_gp_pow_coeff` — every coefficient of `(gp p)^l` has
  `v_p ≥ 3l` (the coefficient-convolution bound: `gp` has all coefficients
  `v_p ≥ 3`, and an `l`-fold product convolves these).

These are the sorry-free ingredients toward `crux_gen_pow`. -/

/-- The Faulhaber polynomial `Sp d` is an antidifference of `X^d`. -/
theorem Sp_diff (d : ℕ) : (Sp d).comp (X + 1) - Sp d = X ^ d := by
  apply eq_of_infinite_eval_eq
  have hsub : Set.range (fun n : ℕ => (n : ℚ))
      ⊆ {x : ℚ | eval x ((Sp d).comp (X + 1) - Sp d) = eval x (X ^ d)} := by
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_setOf_eq, eval_sub, eval_comp, eval_pow, eval_X]
    have hev : eval (n : ℚ) (X + 1 : ℚ[X]) = (n : ℚ) + 1 := by simp
    rw [hev, show ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) from by push_cast; ring,
        Sp_eval d (n + 1), Sp_eval d n, Finset.sum_range_succ]
    ring
  exact (Set.infinite_range_of_injective (fun a b hh => by exact_mod_cast hh)).mono hsub

/-- **Generic Faulhaber antidifference** of a polynomial `h`. -/
noncomputable def RpP (h : ℚ[X]) : ℚ[X] :=
  ∑ d ∈ range (h.natDegree + 1), Polynomial.C (h.coeff d) * Sp d

/-- `RpP h` evaluates to the partial sums `∑_{k<n} h(k)`. -/
theorem RpP_eval (h : ℚ[X]) (n : ℕ) :
    (RpP h).eval (n : ℚ) = ∑ k ∈ range n, h.eval (k : ℚ) := by
  rw [RpP, eval_finset_sum]
  rw [Finset.sum_congr rfl
    (fun d _ => by rw [eval_mul, eval_C, Sp_eval d n, Finset.mul_sum])]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [eval_eq_sum_range]

theorem RpP_eval_zero (h : ℚ[X]) : (RpP h).eval 0 = 0 := by
  have := RpP_eval h 0; simpa using this

/-- The defining antidifference property: `(RpP h)(X+1) - (RpP h) = h`. -/
theorem RpP_diff (h : ℚ[X]) : (RpP h).comp (X + 1) - RpP h = h := by
  apply eq_of_infinite_eval_eq
  have hsub : Set.range (fun n : ℕ => (n : ℚ))
      ⊆ {x : ℚ | eval x ((RpP h).comp (X + 1) - RpP h) = eval x h} := by
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_setOf_eq, eval_sub, eval_comp]
    have hev : eval (n : ℚ) (X + 1 : ℚ[X]) = (n : ℚ) + 1 := by simp
    rw [hev, show ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) from by push_cast; ring,
        RpP_eval h (n + 1), RpP_eval h n, Finset.sum_range_succ]
    ring
  exact (Set.infinite_range_of_injective (fun a b hh => by exact_mod_cast hh)).mono hsub

/-- Every coefficient of `gp p` has `v_p ≥ 3`. -/
theorem vge_gp_coeff (p i : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    vge p 3 ((gp p).coeff i) := by
  rw [gp, finset_sum_coeff]
  apply vge_sum
  intro j hj
  rw [coeff_C_mul, coeff_X_pow]
  by_cases hij : i = j
  · rw [if_pos hij, mul_one]
    rw [mem_Icc] at hj
    exact vge_pe_three p j hp5 hj.1
  · rw [if_neg hij, mul_zero]; exact vge_zero p 3

/-- **Coefficient-convolution bound.**  Every coefficient of `(gp p)^l` has
`v_p ≥ 3l`. -/
theorem vge_gp_pow_coeff (p l d : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    vge p ((3 * l : ℕ) : ℤ) (((gp p) ^ l).coeff d) := by
  induction l generalizing d with
  | zero =>
    simp only [pow_zero, Nat.mul_zero, Nat.cast_zero, coeff_one]
    by_cases hd : d = 0
    · rw [if_pos hd]; exact vge_one p
    · rw [if_neg hd]; exact vge_zero p 0
  | succ l ih =>
    rw [pow_succ, Polynomial.coeff_mul]
    apply vge_sum
    intro x _
    have h1 := ih x.1
    have h2 := vge_gp_coeff p x.2 hp5
    have hm := vge_mul h1 h2
    rw [show ((3 * l : ℕ) : ℤ) + 3 = ((3 * (l + 1) : ℕ) : ℤ) from by push_cast; ring] at hm
    exact hm

/-- `(gp p)^l` is reflection-symmetric: `((gp p)^l).comp(-1-X) = (gp p)^l`. -/
theorem gp_pow_reflect (p l : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ((gp p) ^ l).comp (-1 - X) = (gp p) ^ l := by
  rw [pow_comp, gp_reflect p hp5]

/-- The antidifference of `(gp p)^l` is an odd polynomial. -/
theorem RpP_gp_pow_odd (p l : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    (RpP (gp p ^ l)).comp (-X) = -(RpP (gp p ^ l)) :=
  antidiff_odd (RpP (gp p ^ l)) (gp p ^ l) (RpP_diff _) (RpP_eval_zero _)
    (gp_pow_reflect p l hp5)

/-- Consequently, all even-degree coefficients of the antidifference vanish. -/
theorem RpP_gp_pow_coeff_even (p l d : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hd : Even d) :
    (RpP (gp p ^ l)).coeff d = 0 := by
  have hodd := RpP_gp_pow_odd p l hp5
  have hX : (-X : ℚ[X]) = Polynomial.C (-1) * X := by rw [C_neg, C_1, neg_one_mul]
  have h1 : ((RpP (gp p ^ l)).comp (-X)).coeff d = (RpP (gp p ^ l)).coeff d := by
    rw [hX, comp_C_mul_X_coeff, hd.neg_one_pow, mul_one]
  rw [hodd, coeff_neg] at h1
  linarith [h1]

/-- `gp p` evaluated at a natural equals `Fp p k - 1`. -/
theorem gp_eval_nat (p k : ℕ) [Fact p.Prime] : (gp p).eval (k : ℚ) = Fp p k - 1 := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [gp_eval, ← Fp_sub_one_eq p k hp1]

/-- The antidifference of `(gp p)^l` evaluates to the power-sum
`∑_{k<n} (Fp p k - 1)^l`.  This is the value-level bridge for `crux_gen_pow`. -/
theorem RpP_gp_pow_eval (p l n : ℕ) [Fact p.Prime] :
    (RpP (gp p ^ l)).eval (n : ℚ) = ∑ k ∈ range n, (Fp p k - 1) ^ l := by
  rw [RpP_eval]
  apply Finset.sum_congr rfl
  intro k _
  rw [eval_pow, gp_eval_nat]

/-- Every value of the antidifference `RpP (gp p ^ l)` has `v_p ≥ 3l`
(each summand `(Fp p k - 1)^l` does). -/
theorem vge_RpP_gp_pow_eval (p l n : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    vge p (3 * (l : ℤ)) ((RpP (gp p ^ l)).eval (n : ℚ)) := by
  rw [RpP_gp_pow_eval]
  apply vge_sum
  intro k _
  have h := vge_prod (range l) (fun _ => Fp p k - 1) 3 (fun _ _ => Fp_sub_one_vge3 p k hp5)
  rw [Finset.prod_const, Finset.card_range] at h
  exact h

/-- **Power-sum difference reduction.**  With `A = B + C`, the power-sum
difference `∑_{k<C}((Fp(B+k)-1)^l - (Fp k -1)^l)` equals the second difference
`RpP(gp^l)(A) - RpP(gp^l)(B) - RpP(gp^l)(C)`.  This is the entry point for
`crux_gen_pow` (the odd-polynomial / antidifference argument, analogous to
`crux_gen_reduction`), reducing the power-sum difference to a single
antidifference polynomial. -/
theorem crux_gen_pow_reduction (p l B C A : ℕ) [Fact p.Prime] (hA : A = B + C) :
    (∑ k ∈ range C, ((Fp p (B + k) - 1) ^ l - (Fp p k - 1) ^ l))
      = (RpP (gp p ^ l)).eval (A : ℚ)
          - (RpP (gp p ^ l)).eval (B : ℚ)
          - (RpP (gp p ^ l)).eval (C : ℚ) := by
  rw [RpP_gp_pow_eval, RpP_gp_pow_eval, RpP_gp_pow_eval, hA]
  rw [Finset.sum_range_add (fun k => (Fp p k - 1) ^ l) B C]
  have hcombine :
      (∑ k ∈ range C, (Fp p (B + k) - 1) ^ l)
        - (∑ k ∈ range C, (Fp p k - 1) ^ l)
        = ∑ k ∈ range C, ((Fp p (B + k) - 1) ^ l - (Fp p k - 1) ^ l) := by
    rw [← Finset.sum_sub_distrib]
  rw [← hcombine]; ring

end PTowerGen
