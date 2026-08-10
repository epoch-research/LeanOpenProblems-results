import FormalConjectures.Util.ProblemImports

open Rat Finset

set_option maxRecDepth 60000

/--
A064169: Numerator - denominator in n-th harmonic number, $1 + 1/2 + 1/3 + \dots + 1/n$.
-/
def A064169 (n : ℕ) : ℕ :=
  let hn := harmonic n
  -- The difference in ℤ is non-negative for n ≥ 1. Int.natAbs ensures the output is ℕ.
  Int.natAbs (hn.num - hn.den)

namespace Wolf

def M : ℕ := 16843^3

def hden : ℕ → ℕ
| 0 => 1
| (k+1) => hden k * (k+1)
def hnum : ℕ → ℕ
| 0 => 0
| (k+1) => hnum k * (k+1) + hden k

lemma hden_pos : ∀ k, 0 < hden k
| 0 => by norm_num [hden]
| (k+1) => by rw [hden]; exact Nat.mul_pos (hden_pos k) (by omega)

lemma hden_eq_fact : ∀ k, hden k = k.factorial
| 0 => rfl
| (k+1) => by rw [hden, hden_eq_fact k, Nat.factorial_succ]; ring

lemma harmonic_eq : ∀ k, harmonic k = (hnum k : ℚ) / (hden k : ℚ)
| 0 => by simp [hnum, hden]
| (k+1) => by
    rw [harmonic_succ, harmonic_eq k, hnum, hden]
    have hd : (hden k : ℚ) ≠ 0 := by exact_mod_cast (hden_pos k).ne'
    push_cast
    field_simp

def hmod : ℕ → ℕ × ℕ
| 0 => (0 % M, 1 % M)
| (k+1) => let s := hmod k; ((s.1 * (k+1) + s.2) % M, (s.2 * (k+1)) % M)

lemma modstep (a b c : ℕ) : (a % M * c + b % M) % M = (a * c + b) % M := by
  conv_lhs => rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod]
  conv_rhs => rw [Nat.add_mod, Nat.mul_mod]

lemma modstep2 (b c : ℕ) : (b % M * c) % M = (b * c) % M := by
  conv_lhs => rw [Nat.mul_mod, Nat.mod_mod]
  conv_rhs => rw [Nat.mul_mod]

lemma hmod_eq : ∀ k, hmod k = (hnum k % M, hden k % M)
| 0 => by simp [hmod, hnum, hden]
| (k+1) => by
    rw [hmod, hmod_eq k, hnum, hden]
    dsimp only
    rw [modstep, modstep2]

end Wolf

namespace Wolf
def stepM (s : ℕ × ℕ) (k : ℕ) : ℕ × ℕ := ((s.1 * (k+1) + s.2) % M, (s.2 * (k+1)) % M)

def runM : ℕ → ℕ → (ℕ × ℕ) → (ℕ × ℕ)
| _, 0, s => s
| start, (c+1), s => runM (start+1) c (stepM s start)

lemma hmod_succ (k : ℕ) : hmod (k+1) = stepM (hmod k) k := rfl

lemma runM_add (start c1 c2 : ℕ) (s : ℕ × ℕ) :
    runM start (c1 + c2) s = runM (start + c1) c2 (runM start c1 s) := by
  induction c1 generalizing start s with
  | zero => simp [runM]
  | succ c ih =>
    have h1 : (c+1)+c2 = (c + c2) + 1 := by ring
    have e1 : runM start ((c+c2)+1) s = runM (start+1) (c+c2) (stepM s start) := rfl
    have e2 : runM start (c+1) s = runM (start+1) c (stepM s start) := rfl
    have hi : (start+1)+c = start+(c+1) := by omega
    rw [h1, e1, ih (start+1) (stepM s start), e2, hi]

lemma hmod_run (a b : ℕ) : hmod (a + b) = runM a b (hmod a) := by
  induction b generalizing a with
  | zero => simp [runM]
  | succ c ih =>
    have : a + (c + 1) = (a + 1) + c := by ring
    rw [this, ih (a+1), hmod_succ]
    rfl

lemma hmod_zero_eq : hmod 0 = (0, 1) := by decide

end Wolf

namespace Wolf
private lemma blk0 : runM 0 1000 (0, 1) = (961265879628, 71580900028) := by decide
private lemma blk1 : runM 1000 1000 (961265879628, 71580900028) = (1609396178925, 3373823158438) := by decide
private lemma blk2 : runM 2000 1000 (1609396178925, 3373823158438) = (1501906704902, 1569991477269) := by decide
private lemma blk3 : runM 3000 1000 (1501906704902, 1569991477269) = (3078611723367, 1283805993399) := by decide
private lemma blk4 : runM 4000 1000 (3078611723367, 1283805993399) = (2259530626677, 3734409306131) := by decide
private lemma blk5 : runM 5000 1000 (2259530626677, 3734409306131) = (996986960467, 3017244285036) := by decide
private lemma blk6 : runM 6000 1000 (996986960467, 3017244285036) = (4771298385358, 2739579307819) := by decide
private lemma blk7 : runM 7000 1000 (4771298385358, 2739579307819) = (1589042690885, 4321725229520) := by decide
private lemma blk8 : runM 8000 1000 (1589042690885, 4321725229520) = (1120599203647, 2932838436044) := by decide
private lemma blk9 : runM 9000 1000 (1120599203647, 2932838436044) = (1149863760960, 24738711124) := by decide
private lemma blk10 : runM 10000 1000 (1149863760960, 24738711124) = (4486732163848, 746528446077) := by decide
private lemma blk11 : runM 11000 1000 (4486732163848, 746528446077) = (1678226025178, 4174539266167) := by decide
private lemma blk12 : runM 12000 1000 (1678226025178, 4174539266167) = (1307789376565, 2033328893880) := by decide
private lemma blk13 : runM 13000 1000 (1307789376565, 2033328893880) = (258122591637, 3750319829543) := by decide
private lemma blk14 : runM 14000 1000 (258122591637, 3750319829543) = (2069264610289, 2441835054091) := by decide
private lemma blk15 : runM 15000 1000 (2069264610289, 2441835054091) = (391552328214, 211702801271) := by decide
private lemma blk16 : runM 16000 842 (391552328214, 211702801271) = (0, 169067457020) := by decide

lemma HInv (k : ℕ) : hnum k ≡ (hmod k).1 [MOD M] := by
  rw [hmod_eq k]
  simp [Nat.ModEq]

lemma M_dvd_hnum : M ∣ hnum 16842 := by
  have e1 : runM 0 1000 (0,1) = (961265879628, 71580900028) := blk0
  have e2 : runM 0 2000 (0,1) = (1609396178925, 3373823158438) := by
    have hs : (2000:ℕ) = 1000 + 1000 := by norm_num
    rw [hs, runM_add, e1, Nat.zero_add]; exact blk1
  have e3 : runM 0 3000 (0,1) = (1501906704902, 1569991477269) := by
    have hs : (3000:ℕ) = 2000 + 1000 := by norm_num
    rw [hs, runM_add, e2, Nat.zero_add]; exact blk2
  have e4 : runM 0 4000 (0,1) = (3078611723367, 1283805993399) := by
    have hs : (4000:ℕ) = 3000 + 1000 := by norm_num
    rw [hs, runM_add, e3, Nat.zero_add]; exact blk3
  have e5 : runM 0 5000 (0,1) = (2259530626677, 3734409306131) := by
    have hs : (5000:ℕ) = 4000 + 1000 := by norm_num
    rw [hs, runM_add, e4, Nat.zero_add]; exact blk4
  have e6 : runM 0 6000 (0,1) = (996986960467, 3017244285036) := by
    have hs : (6000:ℕ) = 5000 + 1000 := by norm_num
    rw [hs, runM_add, e5, Nat.zero_add]; exact blk5
  have e7 : runM 0 7000 (0,1) = (4771298385358, 2739579307819) := by
    have hs : (7000:ℕ) = 6000 + 1000 := by norm_num
    rw [hs, runM_add, e6, Nat.zero_add]; exact blk6
  have e8 : runM 0 8000 (0,1) = (1589042690885, 4321725229520) := by
    have hs : (8000:ℕ) = 7000 + 1000 := by norm_num
    rw [hs, runM_add, e7, Nat.zero_add]; exact blk7
  have e9 : runM 0 9000 (0,1) = (1120599203647, 2932838436044) := by
    have hs : (9000:ℕ) = 8000 + 1000 := by norm_num
    rw [hs, runM_add, e8, Nat.zero_add]; exact blk8
  have e10 : runM 0 10000 (0,1) = (1149863760960, 24738711124) := by
    have hs : (10000:ℕ) = 9000 + 1000 := by norm_num
    rw [hs, runM_add, e9, Nat.zero_add]; exact blk9
  have e11 : runM 0 11000 (0,1) = (4486732163848, 746528446077) := by
    have hs : (11000:ℕ) = 10000 + 1000 := by norm_num
    rw [hs, runM_add, e10, Nat.zero_add]; exact blk10
  have e12 : runM 0 12000 (0,1) = (1678226025178, 4174539266167) := by
    have hs : (12000:ℕ) = 11000 + 1000 := by norm_num
    rw [hs, runM_add, e11, Nat.zero_add]; exact blk11
  have e13 : runM 0 13000 (0,1) = (1307789376565, 2033328893880) := by
    have hs : (13000:ℕ) = 12000 + 1000 := by norm_num
    rw [hs, runM_add, e12, Nat.zero_add]; exact blk12
  have e14 : runM 0 14000 (0,1) = (258122591637, 3750319829543) := by
    have hs : (14000:ℕ) = 13000 + 1000 := by norm_num
    rw [hs, runM_add, e13, Nat.zero_add]; exact blk13
  have e15 : runM 0 15000 (0,1) = (2069264610289, 2441835054091) := by
    have hs : (15000:ℕ) = 14000 + 1000 := by norm_num
    rw [hs, runM_add, e14, Nat.zero_add]; exact blk14
  have e16 : runM 0 16000 (0,1) = (391552328214, 211702801271) := by
    have hs : (16000:ℕ) = 15000 + 1000 := by norm_num
    rw [hs, runM_add, e15, Nat.zero_add]; exact blk15
  have e17 : runM 0 16842 (0,1) = (0, 169067457020) := by
    have hs : (16842:ℕ) = 16000 + 842 := by norm_num
    rw [hs, runM_add, e16, Nat.zero_add]; exact blk16
  have hrun : hmod 16842 = (0, 169067457020) := by
    have h := hmod_run 0 16842
    rw [Nat.zero_add] at h
    rw [h, hmod_zero_eq]; exact e17
  have hI := HInv 16842
  have h1 : (hmod 16842).1 = 0 := by rw [hrun]
  rw [h1] at hI
  exact (Nat.modEq_zero_iff_dvd).mp hI

end Wolf


namespace Wolf

lemma p16843_prime : Nat.Prime 16843 := by norm_num

instance : Fact (Nat.Prime 16843) := ⟨p16843_prime⟩

lemma hnum_16842_ne : hnum 16842 ≠ 0 := by
  have hpos := harmonic_pos (n := 16842) (by norm_num)
  rw [harmonic_eq 16842] at hpos
  intro h
  rw [h, Nat.cast_zero, zero_div] at hpos
  exact lt_irrefl _ hpos

lemma val_harmonic_16842 : (3 : ℤ) ≤ padicValRat 16843 (harmonic 16842) := by
  rw [harmonic_eq 16842]
  have hn0 : (hnum 16842 : ℚ) ≠ 0 := by exact_mod_cast hnum_16842_ne
  have hd0 : (hden 16842 : ℚ) ≠ 0 := by
    have := (hden_pos 16842).ne'
    exact_mod_cast this
  have hvnum : 3 ≤ padicValNat 16843 (hnum 16842) := by
    rw [← padicValNat_dvd_iff_le hnum_16842_ne]
    exact M_dvd_hnum
  have hvden : padicValNat 16843 (hden 16842) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    rw [hden_eq_fact]
    intro h
    have := (Nat.Prime.dvd_factorial p16843_prime).mp h
    omega
  have e1 : padicValRat 16843 (hnum 16842 : ℚ) = (padicValNat 16843 (hnum 16842) : ℤ) :=
    padicValRat.of_nat
  have e2 : padicValRat 16843 (hden 16842 : ℚ) = (padicValNat 16843 (hden 16842) : ℤ) :=
    padicValRat.of_nat
  rw [padicValRat.div hn0 hd0, e1, e2, hvden]
  push_cast
  omega

end Wolf

namespace SW
lemma padicValRat_sum_ge {ι : Type*} {s : Finset ι} {f : ι → ℚ} {c : ℤ}
    (hne : s.Nonempty) (hpos : ∀ i ∈ s, 0 < f i)
    (hval : ∀ i ∈ s, c ≤ padicValRat 16843 (f i)) :
    c ≤ padicValRat 16843 (∑ i ∈ s, f i) := by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hval a (by simp)
  | cons a t ha ht ih =>
    rw [Finset.sum_cons]
    have hsum_pos : 0 < ∑ i ∈ t, f i :=
      Finset.sum_pos (fun i hi => hpos i (by simp [hi])) ht
    have h1 : c ≤ padicValRat 16843 (f a) := hval a (by simp)
    have h2 : c ≤ padicValRat 16843 (∑ i ∈ t, f i) :=
      ih (fun i hi => hpos i (by simp [hi])) (fun i hi => hval i (by simp [hi]))
    have hne0 : f a + ∑ i ∈ t, f i ≠ 0 :=
      ne_of_gt (add_pos (hpos a (by simp)) hsum_pos)
    calc c ≤ min (padicValRat 16843 (f a)) (padicValRat 16843 (∑ i ∈ t, f i)) := le_min h1 h2
      _ ≤ _ := padicValRat.min_le_padicValRat_add hne0

lemma harmonic_sum_Icc (n : ℕ) : harmonic n = ∑ k ∈ Icc 1 n, (k:ℚ)⁻¹ := by
  induction n with
  | zero => simp [harmonic]
  | succ m ih =>
    rw [harmonic_succ, ih, Finset.sum_Icc_succ_top (by omega)]

lemma Vsum_eq :
    ∑ k ∈ (Icc (1:ℕ) (16843^2 - 2)).filter (fun k => 16843 ∣ k), (k:ℚ)⁻¹
      = harmonic 16842 / 16843 := by
  have hset : (Icc (1:ℕ) (16843^2 - 2)).filter (fun k => 16843 ∣ k)
       = (Icc (1:ℕ) 16842).image (fun j => 16843 * j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, j, rfl⟩
      exact ⟨j, ⟨by omega, by omega⟩, rfl⟩
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      refine ⟨⟨by omega, ?_⟩, ⟨j, rfl⟩⟩
      calc 16843 * j ≤ 16843 * 16842 := by gcongr
        _ ≤ 16843^2 - 2 := by norm_num
  rw [hset, Finset.sum_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left (by norm_num) h)]
  have hterm : ∀ j : ℕ, ((16843*j : ℕ):ℚ)⁻¹ = (16843:ℚ)⁻¹ * (j:ℚ)⁻¹ := by
    intro j; push_cast; rw [mul_inv]
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← harmonic_sum_Icc, div_eq_mul_inv, mul_comm]


lemma val_Vsum :
    (2:ℤ) ≤ padicValRat 16843
      (∑ k ∈ (Icc (1:ℕ) (16843^2 - 2)).filter (fun k => 16843 ∣ k), (k:ℚ)⁻¹) := by
  rw [Vsum_eq]
  have hh : harmonic 16842 ≠ 0 := (harmonic_pos (by norm_num)).ne'
  have h16 : (16843:ℚ) = ((16843:ℕ):ℚ) := by norm_num
  rw [h16, padicValRat.div hh (by exact_mod_cast (by norm_num : (16843:ℕ) ≠ 0)),
      padicValRat.self (by norm_num)]
  have := Wolf.val_harmonic_16842
  omega

lemma val_B :
    (2:ℤ) ≤ padicValRat 16843
      (∑ k ∈ (Icc (1:ℕ) (16843^2 - 1)).filter (fun k => ¬ 16843 ∣ k), (k:ℚ)⁻¹) := by
  set W := (Icc (1:ℕ) (16843^2 - 1)).filter (fun k => ¬ 16843 ∣ k) with hW
  have memW : ∀ k, k ∈ W ↔ (1 ≤ k ∧ k ≤ 16843^2 - 1 ∧ ¬ 16843 ∣ k) := by
    intro k; rw [hW]; simp only [Finset.mem_filter, Finset.mem_Icc]; tauto
  have hσmem : ∀ k ∈ W, 16843^2 - k ∈ W := by
    intro k hk; rw [memW] at hk ⊢
    obtain ⟨h1, h2, h3⟩ := hk
    refine ⟨by omega, by omega, ?_⟩
    intro hd
    apply h3
    have hpp : (16843:ℕ) ∣ 16843^2 := ⟨16843, by ring⟩
    have := Nat.dvd_sub hpp hd
    rwa [show 16843^2 - (16843^2 - k) = k from by omega] at this
  have hreidx : ∑ k ∈ W, ((16843^2 - k : ℕ):ℚ)⁻¹ = ∑ k ∈ W, (k:ℚ)⁻¹ := by
    apply Finset.sum_nbij' (fun k => 16843^2 - k) (fun k => 16843^2 - k) hσmem hσmem
    · intro a ha; rw [memW] at ha; omega
    · intro a ha; rw [memW] at ha; omega
    · intro a _; rfl
  have h2B : (2:ℚ) * (∑ k ∈ W, (k:ℚ)⁻¹)
      = ∑ k ∈ W, ((k:ℚ)⁻¹ + ((16843^2 - k:ℕ):ℚ)⁻¹) := by
    rw [Finset.sum_add_distrib, hreidx]; ring
  have hpair : ∀ k ∈ W, (2:ℤ) ≤ padicValRat 16843 ((k:ℚ)⁻¹ + ((16843^2 - k:ℕ):ℚ)⁻¹) := by
    intro k hk
    rw [memW] at hk; obtain ⟨h1, h2, h3⟩ := hk
    have hle : k ≤ 16843^2 := by omega
    have hk0 : (k:ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have hklt : k < 16843^2 := by omega
    have hcard : ((16843^2:ℕ):ℚ) - (k:ℚ) ≠ 0 := by
      have : (k:ℚ) < ((16843^2:ℕ):ℚ) := by exact_mod_cast hklt
      intro hcon; rw [sub_eq_zero] at hcon; linarith
    have hnpk : ¬ (16843:ℕ) ∣ (16843^2 - k) := by
      intro hd
      apply h3
      have hpp : (16843:ℕ) ∣ 16843^2 := ⟨16843, by ring⟩
      have := Nat.dvd_sub hpp hd
      rwa [show 16843^2 - (16843^2 - k) = k from by omega] at this
    have hterm : (k:ℚ)⁻¹ + ((16843^2 - k:ℕ):ℚ)⁻¹
        = ((16843^2:ℕ):ℚ) / ((k * (16843^2 - k):ℕ):ℚ) := by
      rw [Nat.cast_mul, Nat.cast_sub hle]
      field_simp
      ring
    rw [hterm]
    have hnum0 : ((16843^2:ℕ):ℚ) ≠ 0 := by exact_mod_cast (by positivity : (16843^2:ℕ) ≠ 0)
    have hden0 : ((k * (16843^2 - k):ℕ):ℚ) ≠ 0 := by
      have : k * (16843^2 - k) ≠ 0 := by
        apply Nat.mul_ne_zero (by omega)
        omega
      exact_mod_cast this
    rw [padicValRat.div hnum0 hden0, padicValRat.of_nat, padicValRat.of_nat]
    have hv1 : padicValNat 16843 (16843^2) = 2 := padicValNat.prime_pow 2
    have hv2 : padicValNat 16843 (k * (16843^2 - k)) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      rcases (Nat.Prime.dvd_mul (by norm_num)).mp hd with h | h
      · exact h3 h
      · exact hnpk h
    rw [hv1, hv2]; norm_num
  have hne : W.Nonempty := by
    rw [hW]; refine ⟨1, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
  have hpos : ∀ k ∈ W, (0:ℚ) < (k:ℚ)⁻¹ := by
    intro k hk; rw [memW] at hk
    have : (0:ℚ) < (k:ℚ) := by exact_mod_cast (by omega : 0 < k)
    positivity
  -- val of sum of pair terms ≥ 2
  have hsum : (2:ℤ) ≤ padicValRat 16843 (∑ k ∈ W, ((k:ℚ)⁻¹ + ((16843^2 - k:ℕ):ℚ)⁻¹)) := by
    apply padicValRat_sum_ge hne
    · intro k hk
      have hk0 : (0:ℚ) < (k:ℚ)⁻¹ := hpos k hk
      have hm0 : (0:ℚ) < ((16843^2 - k:ℕ):ℚ)⁻¹ := by
        rw [memW] at hk
        have : (0:ℚ) < ((16843^2 - k:ℕ):ℚ) := by
          have : 0 < 16843^2 - k := by omega
          exact_mod_cast this
        positivity
      linarith
    · exact hpair
  rw [← h2B] at hsum
  have h20 : (2:ℚ) ≠ 0 := by norm_num
  have hB0 : (∑ k ∈ W, (k:ℚ)⁻¹) ≠ 0 := by
    apply ne_of_gt
    apply Finset.sum_pos hpos hne
  rw [padicValRat.mul h20 hB0] at hsum
  have : padicValRat 16843 (2:ℚ) = 0 := by
    rw [show (2:ℚ) = ((2:ℕ):ℚ) by norm_num, padicValRat.of_nat]
    norm_num [padicValNat.eq_zero_of_not_dvd]
  rw [this] at hsum
  omega

lemma B_eq_U :
    ∑ k ∈ (Icc (1:ℕ) (16843^2 - 1)).filter (fun k => ¬ 16843 ∣ k), (k:ℚ)⁻¹
    = (∑ k ∈ (Icc (1:ℕ) (16843^2 - 2)).filter (fun k => ¬ 16843 ∣ k), (k:ℚ)⁻¹)
      + ((16843^2 - 1 : ℕ):ℚ)⁻¹ := by
  have hset : (Icc (1:ℕ) (16843^2 - 1)).filter (fun k => ¬ 16843 ∣ k)
       = insert (16843^2 - 1) ((Icc (1:ℕ) (16843^2 - 2)).filter (fun k => ¬ 16843 ∣ k)) := by
    ext k
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, hk2⟩, hnd⟩
      by_cases hh : k = 16843^2 - 1
      · left; exact hh
      · right; exact ⟨⟨hk1, by omega⟩, hnd⟩
    · rintro (rfl | ⟨⟨hk1, hk2⟩, hnd⟩)
      · refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
        intro hd
        have hpp : (16843:ℕ) ∣ 16843^2 := ⟨16843, by ring⟩
        have := Nat.dvd_sub hpp hd
        rw [show 16843^2 - (16843^2 - 1) = 1 from by norm_num] at this
        exact absurd this (by norm_num)
      · exact ⟨⟨hk1, by omega⟩, hnd⟩
  have hnotin : (16843^2 - 1) ∉ (Icc (1:ℕ) (16843^2 - 2)).filter (fun k => ¬ 16843 ∣ k) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rintro ⟨⟨_, hle⟩, _⟩; omega
  rw [hset, Finset.sum_insert hnotin, add_comm]

lemma val_Usum_sub_1 :
    (2:ℤ) ≤ padicValRat 16843
      ((∑ k ∈ (Icc (1:ℕ) (16843^2 - 2)).filter (fun k => ¬ 16843 ∣ k), (k:ℚ)⁻¹) - 1) := by
  set U := (Icc (1:ℕ) (16843^2 - 2)).filter (fun k => ¬ 16843 ∣ k) with hU
  have h12sub : ({1, 2} : Finset ℕ) ⊆ U := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [hU]; simp only [Finset.mem_filter, Finset.mem_Icc]
    rcases hx with rfl | rfl
    · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
    · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
  have hge : (3/2 : ℚ) ≤ ∑ k ∈ U, (k:ℚ)⁻¹ := by
    have hp : ∑ k ∈ ({1,2}:Finset ℕ), (k:ℚ)⁻¹ ≤ ∑ k ∈ U, (k:ℚ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg h12sub (fun i _ _ => by positivity)
    have hpair2 : ∑ k ∈ ({1,2}:Finset ℕ), (k:ℚ)⁻¹ = 3/2 := by
      rw [Finset.sum_pair (by norm_num)]; norm_num
    linarith [hp, hpair2.le, hpair2.symm.le]
  -- val of (p^2-1)⁻¹ + 1
  have hnum0 : ((16843^2:ℕ):ℚ) ≠ 0 := by exact_mod_cast (by positivity : (16843^2:ℕ) ≠ 0)
  have hne1 : ((16843^2-1:ℕ):ℚ) ≠ 0 := by
    have : (0:ℚ) < ((16843^2-1:ℕ):ℚ) := by exact_mod_cast (by norm_num : 0 < 16843^2-1)
    exact this.ne'
  have hY : padicValRat 16843 (((16843^2-1:ℕ):ℚ)⁻¹ + 1) = 2 := by
    have hcast : ((16843^2-1:ℕ):ℚ) + 1 = ((16843^2:ℕ):ℚ) := by
      rw [Nat.cast_sub (by norm_num)]; push_cast; ring
    have hEq : ((16843^2-1:ℕ):ℚ)⁻¹ + 1 = ((16843^2:ℕ):ℚ) / ((16843^2-1:ℕ):ℚ) := by
      field_simp
      linarith [hcast]
    rw [hEq, padicValRat.div hnum0 hne1, padicValRat.of_nat, padicValRat.of_nat]
    have hv1 : padicValNat 16843 (16843^2) = 2 := padicValNat.prime_pow 2
    have hv2 : padicValNat 16843 (16843^2 - 1) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      have hpp : (16843:ℕ) ∣ 16843^2 := ⟨16843, by ring⟩
      have := Nat.dvd_sub hpp hd
      rw [show 16843^2 - (16843^2 - 1) = 1 from by norm_num] at this
      exact absurd this (by norm_num)
    rw [hv1, hv2]; norm_num
  have hrw : (∑ k ∈ U, (k:ℚ)⁻¹) - 1
      = (∑ k ∈ (Icc (1:ℕ) (16843^2 - 1)).filter (fun k => ¬ 16843 ∣ k), (k:ℚ)⁻¹)
        - (((16843^2-1:ℕ):ℚ)⁻¹ + 1) := by
    rw [B_eq_U]; ring
  rw [hrw, sub_eq_add_neg]
  have hne0 : (∑ k ∈ (Icc (1:ℕ) (16843^2 - 1)).filter (fun k => ¬ 16843 ∣ k), (k:ℚ)⁻¹)
      + -(((16843^2-1:ℕ):ℚ)⁻¹ + 1) ≠ 0 := by
    rw [← sub_eq_add_neg, ← hrw]
    have : (0:ℚ) < (∑ k ∈ U, (k:ℚ)⁻¹) - 1 := by linarith [hge]
    exact this.ne'
  refine le_trans ?_ (padicValRat.min_le_padicValRat_add hne0)
  apply le_min
  · exact val_B
  · rw [padicValRat.neg]; exact hY.symm.le

lemma split_q :
    harmonic (16843^2 - 2)
    = (∑ k ∈ (Icc (1:ℕ) (16843^2 - 2)).filter (fun k => ¬ 16843 ∣ k), (k:ℚ)⁻¹)
      + (∑ k ∈ (Icc (1:ℕ) (16843^2 - 2)).filter (fun k => 16843 ∣ k), (k:ℚ)⁻¹) := by
  rw [harmonic_sum_Icc,
    ← Finset.sum_filter_add_sum_filter_not (Icc (1:ℕ) (16843^2 - 2)) (fun k => 16843 ∣ k)]
  ring

lemma val_q_sub_1 : (2:ℤ) ≤ padicValRat 16843 (harmonic (16843^2 - 2) - 1) := by
  rw [split_q]
  set A := ∑ k ∈ (Icc (1:ℕ) (16843^2 - 2)).filter (fun k => ¬ 16843 ∣ k), (k:ℚ)⁻¹ with hA
  set C := ∑ k ∈ (Icc (1:ℕ) (16843^2 - 2)).filter (fun k => 16843 ∣ k), (k:ℚ)⁻¹ with hC
  have hrw : (A + C) - 1 = (A - 1) + C := by ring
  rw [hrw]
  have hA1 : (1:ℚ) < A := by
    have h12sub : ({1, 2} : Finset ℕ)
        ⊆ (Icc (1:ℕ) (16843^2 - 2)).filter (fun k => ¬ 16843 ∣ k) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_Icc]
      rcases hx with rfl | rfl
      · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
      · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩
    have hp : ∑ k ∈ ({1,2}:Finset ℕ), (k:ℚ)⁻¹ ≤ A :=
      Finset.sum_le_sum_of_subset_of_nonneg h12sub (fun i _ _ => inv_nonneg.mpr (Nat.cast_nonneg i))
    have hpair2 : ∑ k ∈ ({1,2}:Finset ℕ), (k:ℚ)⁻¹ = 3/2 := by
      rw [Finset.sum_pair (by norm_num)]; norm_num
    linarith [hp, hpair2.le, hpair2.symm.le]
  have hCpos : (0:ℚ) < C := by
    rw [hC]
    apply Finset.sum_pos
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_Icc] at hi
      have hi0 : (0:ℚ) < (i:ℚ) := by exact_mod_cast (by omega : 0 < i)
      exact inv_pos.mpr hi0
    · refine ⟨16843, ?_⟩
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by norm_num, by norm_num⟩, ⟨1, by ring⟩⟩
  have hne0 : (A - 1) + C ≠ 0 := by
    have : (0:ℚ) < (A - 1) + C := by linarith
    exact this.ne'
  refine le_trans ?_ (padicValRat.min_le_padicValRat_add hne0)
  apply le_min
  · exact val_Usum_sub_1
  · exact val_Vsum

lemma final_dvd :
    ((16843:ℕ):ℤ)^2 ∣ ((harmonic (16843^2 - 2)).num - (harmonic (16843^2 - 2)).den) := by
  set q := harmonic (16843^2 - 2) with hq
  set z : ℤ := q.num - q.den with hz
  have hqd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hnd : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hqd).mp (Rat.num_div_den q)
  have hcast : (z:ℚ) = (q - 1) * (q.den : ℚ) := by
    rw [hz]; push_cast; rw [hnd]; ring
  have hval : (2:ℤ) ≤ padicValRat 16843 (q - 1) := val_q_sub_1
  have hq1ne : q - 1 ≠ 0 := by
    intro h; rw [h] at hval; simp at hval
  have hvalz : (2:ℤ) ≤ padicValRat 16843 (z:ℚ) := by
    rw [hcast, padicValRat.mul hq1ne hqd]
    have hden_val : (0:ℤ) ≤ padicValRat 16843 (q.den : ℚ) := by
      rw [padicValRat.of_nat]; exact_mod_cast Nat.zero_le _
    linarith [hval, hden_val]
  have hvi : (2:ℤ) ≤ padicValInt 16843 z := by rw [← padicValRat.of_int]; exact hvalz
  have hdvd : ((16843:ℕ):ℤ)^2 ∣ z :=
    (padicValInt_dvd_iff (p := 16843) 2 z).mpr (Or.inr (by exact_mod_cast hvi))
  exact hdvd
end SW

theorem oeis_64169_conjecture_0.disproof :
    ¬ ∀ (n : ℕ), n > 2 → ((n ∣ A064169 (n - 2)) ↔ n.Prime) := by
  intro h
  have hn : (16843^2 : ℕ) > 2 := by norm_num
  have hiff := h (16843^2) hn
  have hcast : ((16843^2:ℕ):ℤ) = ((16843:ℕ):ℤ)^2 := by push_cast
  have hL : (16843^2 : ℕ) ∣ A064169 (16843^2 - 2) := by
    have hd : ((16843^2:ℕ):ℤ) ∣ ((harmonic (16843^2 - 2)).num - (harmonic (16843^2 - 2)).den) := by
      rw [hcast]; exact SW.final_dvd
    simp only [A064169]
    rw [show (16843^2:ℕ) = (((16843^2:ℕ):ℤ)).natAbs from (Int.natAbs_natCast _).symm,
        Int.natAbs_dvd_natAbs]
    exact hd
  have hP := hiff.mp hL
  have hnp : ¬ Nat.Prime (16843^2) := by
    intro hp
    rcases hp.eq_one_or_self_of_dvd 16843 ⟨16843, by ring⟩ with h1 | h1
    · norm_num at h1
    · norm_num at h1
  exact hnp hP
