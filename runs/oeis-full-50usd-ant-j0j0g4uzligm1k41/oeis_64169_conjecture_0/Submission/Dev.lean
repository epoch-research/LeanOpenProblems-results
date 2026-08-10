import FormalConjectures.Util.ProblemImports

set_option maxRecDepth 60000

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
