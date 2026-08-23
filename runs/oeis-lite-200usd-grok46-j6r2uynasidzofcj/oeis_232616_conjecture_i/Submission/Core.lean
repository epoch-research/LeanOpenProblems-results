import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Finset ZMod Nat Set Classical

abbrev n0 : ℕ := 550172

def binPowMod : ℕ → ℕ → ℕ
  | 0, _ => 1
  | d + 1, k =>
      let r := binPowMod d (k / 2)
      let r2 := (r * r) % n0
      if k % 2 = 0 then r2 else (r2 * 2) % n0

lemma binPowMod_spec : ∀ (d k : ℕ), k < 2 ^ d → binPowMod d k = 2 ^ k % n0
  | 0, k, hk => by
      have hk0 : k = 0 := by
        change k < 1 at hk
        omega
      subst hk0
      rfl
  | d + 1, k, hk => by
      have hhalf : k / 2 < 2 ^ d := by
        rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2)]
        calc
          k < 2 ^ (d + 1) := hk
          _ = 2 ^ d * 2 := by rw [pow_succ]
      have ih : binPowMod d (k / 2) = 2 ^ (k / 2) % n0 :=
        binPowMod_spec d (k / 2) hhalf
      have hmul :
          (binPowMod d (k / 2) * binPowMod d (k / 2)) % n0 = 2 ^ (2 * (k / 2)) % n0 := by
        rw [ih, ← Nat.mul_mod, ← pow_add, two_mul]
      by_cases hpar : k % 2 = 0
      · have hke : 2 * (k / 2) = k := by
          rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hpar)]
        change (if k % 2 = 0 then
            (binPowMod d (k / 2) * binPowMod d (k / 2)) % n0
          else
            (((binPowMod d (k / 2) * binPowMod d (k / 2)) % n0) * 2) % n0) = 2 ^ k % n0
        rw [if_pos hpar, hmul, hke]
      · have ho : k % 2 = 1 := (Nat.mod_two_eq_zero_or_one k).resolve_left hpar
        have hko : 2 * (k / 2) + 1 = k := by
          have := Nat.div_add_mod k 2
          omega
        change (if k % 2 = 0 then
            (binPowMod d (k / 2) * binPowMod d (k / 2)) % n0
          else
            (((binPowMod d (k / 2) * binPowMod d (k / 2)) % n0) * 2) % n0) = 2 ^ k % n0
        rw [if_neg hpar, hmul]
        have : (2 ^ (2 * (k / 2)) % n0 * 2) % n0 = 2 ^ (2 * (k / 2) + 1) % n0 := by
          rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ]
        rw [this, hko]

lemma two_pow_ge : ∀ k : ℕ, k ≤ 2 ^ k
  | 0 => by simp
  | 1 => by simp
  | k + 2 => by
      have ih := two_pow_ge (k + 1)
      have hmul : k + 2 ≤ 2 * (k + 1) := by omega
      have hpow : 2 * (k + 1) ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left 2 ih
      have heq : 2 * 2 ^ (k + 1) = 2 ^ (k + 2) := by
        rw [← pow_succ']
      exact hmul.trans (hpow.trans heq.le)

lemma pow_mod_eq_add_iff (k r : ℕ) (hge : k ≤ 2 ^ k) (hr : r < n0) :
    2 ^ k % n0 = (r + k) % n0 ↔ (2 ^ k - k) % n0 = r := by
  have hI : 2 ^ k % n0 = (r + k) % n0 ↔ (2 ^ k : ℤ) ≡ ((r + k : ℕ) : ℤ) [ZMOD n0] := by
    constructor
    · intro h
      refine (Int.natCast_modEq_iff).2 ?_
      exact h
    · intro h
      exact (Int.natCast_modEq_iff).1 h
  have hsub : (2 ^ k : ℤ) ≡ ((r + k : ℕ) : ℤ) [ZMOD n0] ↔
      ((2 ^ k : ℤ) - (k : ℤ)) ≡ (r : ℤ) [ZMOD n0] := by
    constructor
    · intro h
      have h' : (2 ^ k : ℤ) ≡ (r : ℤ) + (k : ℤ) [ZMOD n0] := by
        simpa using h
      exact Int.ModEq.add_right_cancel' (k : ℤ) (by simpa [sub_add_cancel] using h')
    · intro h
      have := Int.ModEq.add_right (k : ℤ) h
      simpa [sub_add_cancel] using this
  have hcast : (2 ^ k : ℤ) - (k : ℤ) = ((2 ^ k - k : ℕ) : ℤ) := (Nat.cast_sub hge).symm
  have hJ : ((2 ^ k : ℤ) - (k : ℤ)) ≡ (r : ℤ) [ZMOD n0] ↔ (2 ^ k - k) ≡ r [MOD n0] := by
    rw [hcast]
    exact Int.natCast_modEq_iff
  have hK : (2 ^ k - k) ≡ r [MOD n0] ↔ (2 ^ k - k) % n0 = r % n0 := Iff.rfl
  rw [hI, hsub, hJ, hK, Nat.mod_eq_of_lt hr]

lemma binPowMod_hit_iff (k r : ℕ) (hk : k < 2 ^ 25) (hr : r < n0) :
    binPowMod 25 k = (r + k) % n0 ↔
      ((2 ^ k - k : ℕ) : ZMod n0) = (r : ZMod n0) := by
  have hspec : binPowMod 25 k = 2 ^ k % n0 := binPowMod_spec 25 k hk
  have hge : k ≤ 2 ^ k := two_pow_ge k
  rw [hspec, ZMod.natCast_eq_natCast_iff', pow_mod_eq_add_iff k r hge hr,
      Nat.mod_eq_of_lt hr]

theorem test_bin : binPowMod 25 17135927 = (63945 + 17135927) % n0 := by
  rfl

abbrev missR : ℕ := 63945
abbrev cover0 : ℕ := 17135927
abbrev bound0 : ℕ := 16331504
abbrev lastPrime0 : ℕ := 8165753
abbrev period0 : ℕ := 80200

/--
The predicate that $\{2^k - k: k = 1,\dots,m\}$ contains a complete system of residues modulo $n$.
This is equivalent to the image of $k \mapsto 2^k - k \pmod n$ for $k \in \{1, \dots, m\}$ being the entire $\mathbb{Z}_n$.
-/
def A232616_prop (n m : ℕ) [NeZero n] : Prop :=
  (univ : Finset (ZMod n)) = (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod n)

/--
A232616: Least positive integer $m$ such that $\{2^k - k: k = 1,\dots,m\}$
contains a complete system of residues modulo $n$.
-/
noncomputable def A232616 (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    have hn : NeZero n := NeZero.mk h
    let S : Set ℕ := { m : ℕ | A232616_prop n m }
    sInf S

lemma A232616_prop_iff (n m : ℕ) [NeZero n] :
    A232616_prop n m ↔
      ∀ r : ZMod n, ∃ k ∈ Finset.Icc 1 m, ((2 ^ k - k : ℕ) : ZMod n) = r := by
  unfold A232616_prop
  constructor
  · intro h r
    have hr : r ∈ (univ : Finset (ZMod n)) := Finset.mem_univ r
    rw [h] at hr
    exact Finset.mem_image.mp hr
  · intro h
    ext r
    constructor
    · intro
      exact Finset.mem_image.mpr (h r)
    · intro
      exact Finset.mem_univ r

lemma A232616_eq_sInf (n : ℕ) [NeZero n] :
    A232616 n = sInf { m : ℕ | A232616_prop n m } := by
  simp [A232616, NeZero.ne n]

lemma not_prop_of_missing {n m r : ℕ} [NeZero n]
    (hmiss : ∀ k ∈ Finset.Icc 1 m, ((2 ^ k - k : ℕ) : ZMod n) ≠ (r : ZMod n)) :
    ¬ A232616_prop n m := by
  intro h
  rw [A232616_prop_iff] at h
  obtain ⟨k, hk, heq⟩ := h (r : ZMod n)
  exact hmiss k hk heq

lemma prop_of_all_hit {n m : ℕ} [NeZero n]
    (h : ∀ r : ZMod n, ∃ k ∈ Finset.Icc 1 m, ((2 ^ k - k : ℕ) : ZMod n) = r) :
    A232616_prop n m :=
  (A232616_prop_iff n m).2 h

lemma two_pow_25_big : cover0 < 2 ^ 25 := by decide
lemma two_pow_25_bound : bound0 - 1 < 2 ^ 25 := by decide
lemma missR_lt : missR < n0 := by decide
lemma n0_pos : n0 ≠ 0 := by decide
instance : NeZero n0 := ⟨n0_pos⟩

lemma mem_Icc_1 (k m : ℕ) : k ∈ Finset.Icc 1 m ↔ 1 ≤ k ∧ k ≤ m :=
  Finset.mem_Icc

lemma two_pow_200_mod : 2 ^ 200 % 401 = 1 := by rfl

lemma dvd_401_n0 : 401 ∣ n0 := by decide

lemma missR_mod_401 : missR % 401 = 186 := by rfl

lemma two_pow_mod_401 (k : ℕ) : 2 ^ k % 401 = 2 ^ (k % 200) % 401 := by
  have hpow : 2 ^ k = 2 ^ (200 * (k / 200) + k % 200) := by
    rw [Nat.div_add_mod k 200]
  rw [hpow, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, two_pow_200_mod]
  simp

lemma pow_mod_eq_add_mod401 (k : ℕ) (hge : k ≤ 2 ^ k) :
    2 ^ k % 401 = (186 + k) % 401 ↔ (2 ^ k - k) % 401 = 186 := by
  have hr : 186 < 401 := by decide
  have hI : 2 ^ k % 401 = (186 + k) % 401 ↔ (2 ^ k : ℤ) ≡ ((186 + k : ℕ) : ℤ) [ZMOD 401] := by
    constructor
    · intro h; exact (Int.natCast_modEq_iff).2 h
    · intro h; exact (Int.natCast_modEq_iff).1 h
  have hsub : (2 ^ k : ℤ) ≡ ((186 + k : ℕ) : ℤ) [ZMOD 401] ↔
      ((2 ^ k : ℤ) - (k : ℤ)) ≡ (186 : ℤ) [ZMOD 401] := by
    constructor
    · intro h
      have h' : (2 ^ k : ℤ) ≡ (186 : ℤ) + (k : ℤ) [ZMOD 401] := by simpa using h
      exact Int.ModEq.add_right_cancel' (k : ℤ) (by simpa [sub_add_cancel] using h')
    · intro h
      have := Int.ModEq.add_right (k : ℤ) h
      simpa [sub_add_cancel] using this
  have hcast : (2 ^ k : ℤ) - (k : ℤ) = ((2 ^ k - k : ℕ) : ℤ) := (Nat.cast_sub hge).symm
  have hJ : ((2 ^ k : ℤ) - (k : ℤ)) ≡ (186 : ℤ) [ZMOD 401] ↔ (2 ^ k - k) ≡ 186 [MOD 401] := by
    rw [hcast]; exact Int.natCast_modEq_iff
  have hK : (2 ^ k - k) ≡ 186 [MOD 401] ↔ (2 ^ k - k) % 401 = 186 % 401 := Iff.rfl
  rw [hI, hsub, hJ, hK, Nat.mod_eq_of_lt hr]

lemma hit_imp_mod401 (k : ℕ)
    (h : ((2 ^ k - k : ℕ) : ZMod n0) = (missR : ZMod n0)) :
    2 ^ k % 401 = (186 + k) % 401 := by
  have hge : k ≤ 2 ^ k := two_pow_ge k
  have hmod : (2 ^ k - k) % n0 = missR % n0 :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
  have hmiss : (2 ^ k - k) % n0 = missR := by
    rwa [Nat.mod_eq_of_lt missR_lt] at hmod
  have h401 : (2 ^ k - k) ≡ missR [MOD 401] :=
    Nat.ModEq.of_dvd dvd_401_n0 (by
      change (2 ^ k - k) % n0 = missR % n0
      rw [hmiss, Nat.mod_eq_of_lt missR_lt])
  have : (2 ^ k - k) % 401 = 186 := by
    have := h401
    change (2 ^ k - k) % 401 = missR % 401 at this
    rwa [missR_mod_401] at this
  exact (pow_mod_eq_add_mod401 k hge).2 this

def baseOf (i : ℕ) : ℕ :=
  200 * ((((2 ^ i % 401 + 616 - i) % 401) * 399) % 401) + i

lemma baseOf_lt {i : ℕ} (hi : i < 200) : baseOf i < period0 := by
  unfold baseOf period0
  have : (((2 ^ i % 401 + 616 - i) % 401) * 399) % 401 ≤ 400 :=
    Nat.lt_succ_iff.mp (Nat.mod_lt _ (by decide))
  have : 200 * ((((2 ^ i % 401 + 616 - i) % 401) * 399) % 401) + i ≤ 200 * 400 + i :=
    Nat.add_le_add_right (Nat.mul_le_mul_left 200 this) _
  omega

lemma inv200 : (200 * 399) % 401 = 1 := by rfl

lemma class_of_pow_mod {k : ℕ}
    (h : 2 ^ k % 401 = (186 + k) % 401) :
    k % period0 = baseOf (k % 200) := by
  set i := k % 200
  set q := k / 200
  have hsplit : k = 200 * q + i := by
    simpa [i, q] using (Nat.div_add_mod k 200).symm
  have hi : i < 200 := Nat.mod_lt k (by decide : 0 < 200)
  have h2i : 2 ^ k % 401 = 2 ^ i % 401 := by
    simpa [i] using two_pow_mod_401 k
  have hcong : 2 ^ i % 401 = (186 + 200 * q + i) % 401 := by
    have : 186 + 200 * q + i = 186 + (200 * q + i) := by ring
    rw [this, ← hsplit, ← h, h2i]
  have hge : i ≤ 2 ^ i % 401 + 616 := by
    have : 616 ≤ 2 ^ i % 401 + 616 := Nat.le_add_left _ _
    omega
  -- Integers: 2^i%401 + 616 - i ≡ 200 q [ZMOD 401]
  have hInt : ((2 ^ i % 401 + 616 - i : ℕ) : ℤ) % 401 = (200 * q : ℤ) % 401 := by
    have hcast : ((2 ^ i % 401 + 616 - i : ℕ) : ℤ) =
        (2 ^ i % 401 : ℤ) + 616 - (i : ℤ) := by
      rw [Nat.cast_sub hge, Nat.cast_add]; norm_cast
    rw [hcast]
    have hA : (2 ^ i % 401 : ℤ) % 401 = (186 + 200 * q + i : ℤ) % 401 := by
      simpa [Int.natCast_emod, Nat.cast_add, Nat.cast_mul] using
        congrArg (fun x : ℕ => (x : ℤ)) hcong
    have : ((2 ^ i % 401 : ℤ) + 616 - i) % 401 =
        ((186 + 200 * q + i : ℤ) + 616 - i) % 401 := by
      have h616 : ((2 ^ i % 401 : ℤ) + (616 - i)) % 401 =
          ((186 + 200 * q + i : ℤ) + (616 - i)) % 401 := by
        rw [Int.add_emod, Int.add_emod (186 + 200 * q + i), hA]
      convert h616 using 2 <;> ring
    have hrhs : ((186 + 200 * q + i : ℤ) + 616 - i) = 200 * q + 802 := by ring
    rw [this, hrhs, Int.add_emod]
    have h802 : (802 : ℤ) % 401 = 0 := by decide
    simp [h802]
  have hmul : (((2 ^ i % 401 + 616 - i : ℕ) * 399 : ℕ) : ℤ) % 401 = (q : ℤ) % 401 := by
    have h1 : (((2 ^ i % 401 + 616 - i : ℕ) : ℤ) * 399) % 401 =
        ((200 * q : ℤ) * 399) % 401 := by
      rw [Int.mul_emod, Int.mul_emod (200 * q : ℤ), hInt]
    have h2 : ((200 * q : ℤ) * 399) % 401 = (q : ℤ) % 401 := by
      have hinv : (200 * 399 : ℤ) % 401 = 1 := by decide
      have : (200 * q * 399 : ℤ) = (200 * 399) * q := by ring
      rw [this, Int.mul_emod, hinv, Int.one_mul, Int.emod_emod]
    simpa [Nat.cast_mul] using h1.trans h2
  have hqmod : ((2 ^ i % 401 + 616 - i) * 399) % 401 = q % 401 := by
    have hL : ((q : ℕ) : ℤ) % 401 = ((q % 401 : ℕ) : ℤ) := Int.natCast_emod _ _
    have hR : ((((2 ^ i % 401 + 616 - i) * 399 : ℕ) : ℤ) % 401) =
        (((((2 ^ i % 401 + 616 - i) * 399) % 401) : ℕ) : ℤ) := Int.natCast_emod _ _
    have : (((((2 ^ i % 401 + 616 - i) * 399) % 401) : ℕ) : ℤ) = ((q % 401 : ℕ) : ℤ) := by
      rw [← hL, ← hR, hmul]
    exact_mod_cast this
  have hqmod' : q % 401 =
      (((2 ^ i % 401 + 616 - i) % 401) * 399) % 401 := by
    rw [← hqmod, Nat.mul_mod, Nat.mod_eq_of_lt (by decide : 399 < 401)]
  have hqsplit : q = 401 * (q / 401) + q % 401 := (Nat.div_add_mod q 401).symm
  have hkexp : k = 200 * (q % 401) + i + period0 * (q / 401) := by
    have hq' : 200 * q + i = 200 * (401 * (q / 401) + q % 401) + i := by
      rw [← hqsplit]
    rw [hsplit, hq']
    ring
  have hbase : 200 * (q % 401) + i = baseOf i := by
    unfold baseOf
    rw [hqmod']
  have hsumlt : 200 * (q % 401) + i < period0 := by
    rw [hbase]; exact baseOf_lt hi
  have hmodk : k % period0 = 200 * (q % 401) + i := by
    rw [hkexp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsumlt]
  rw [hmodk, hbase]

lemma hit_structure (k : ℕ)
    (h : ((2 ^ k - k : ℕ) : ZMod n0) = (missR : ZMod n0)) :
    k = baseOf (k % 200) + period0 * (k / period0) := by
  have hmod := class_of_pow_mod (hit_imp_mod401 k h)
  have := Nat.div_add_mod k period0
  omega

lemma div_period_le {k : ℕ} (hk : k ≤ bound0 - 1) : k / period0 ≤ 203 := by
  have : k < 204 * period0 := by
    have : bound0 - 1 < 204 * period0 := by decide
    omega
  exact (Nat.div_lt_iff_lt_mul (by decide : 0 < period0)).2 this |> Nat.le_of_lt_succ

-- Placeholder: every candidate misses missR
lemma all_cands_miss :
  ∀ i < 200, ∀ t ≤ 203,
    bound0 ≤ baseOf i + period0 * t ∨
      binPowMod 25 (baseOf i + period0 * t) ≠ (missR + (baseOf i + period0 * t)) % n0 := by
  sorry

lemma k_lt_two_pow_25_of_le_bound {k : ℕ} (hk : k ≤ bound0 - 1) : k < 2 ^ 25 := by
  have : bound0 - 1 < 2 ^ 25 := two_pow_25_bound
  omega

lemma not_hit_below {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ bound0 - 1) :
    ((2 ^ k - k : ℕ) : ZMod n0) ≠ (missR : ZMod n0) := by
  intro hhit
  have hstr := hit_structure k hhit
  have ht : k / period0 ≤ 203 := div_period_le h2
  have hi : k % 200 < 200 := Nat.mod_lt _ (by decide)
  have hmiss := all_cands_miss (k % 200) hi (k / period0) ht
  have hkexpr : baseOf (k % 200) + period0 * (k / period0) = k := hstr.symm
  rw [hkexpr] at hmiss
  rcases hmiss with hge | hne
  · omega
  · have hk25 : k < 2 ^ 25 := k_lt_two_pow_25_of_le_bound h2
    have := (binPowMod_hit_iff k missR hk25 missR_lt).mpr hhit
    exact hne this

lemma not_prop_below {m : ℕ} (hm : m < bound0) :
    ¬ A232616_prop n0 m := by
  refine not_prop_of_missing (r := missR) ?_
  intro k hk
  rw [mem_Icc_1] at hk
  have : k ≤ bound0 - 1 := by omega
  exact not_hit_below hk.1 this

-- Placeholder: every residue is hit by cover0
lemma all_residues_hit :
  ∀ r < n0, ∃ k, 1 ≤ k ∧ k ≤ cover0 ∧ binPowMod 25 k = (r + k) % n0 := by
  sorry

lemma prop_at_cover : A232616_prop n0 cover0 := by
  apply prop_of_all_hit
  intro r
  let rnat := r.val
  have hrlt : rnat < n0 := ZMod.val_lt r
  obtain ⟨k, hk1, hk2, heq⟩ := all_residues_hit rnat hrlt
  have hk25 : k < 2 ^ 25 := by
    have : cover0 < 2 ^ 25 := two_pow_25_big
    omega
  have hrnat : (rnat : ZMod n0) = r := ZMod.natCast_zmod_val r
  refine ⟨k, ?_, ?_⟩
  · exact (mem_Icc_1 k cover0).2 ⟨hk1, hk2⟩
  · have := (binPowMod_hit_iff k rnat hk25 hrlt).mp heq
    simpa [hrnat] using this

lemma S_nonempty : ({ m : ℕ | A232616_prop n0 m } : Set ℕ).Nonempty :=
  ⟨cover0, prop_at_cover⟩

lemma A232616_ge_bound : bound0 ≤ A232616 n0 := by
  rw [A232616_eq_sInf]
  refine le_csInf S_nonempty ?_
  intro m hm
  by_contra hlt
  exact not_prop_below (lt_of_not_ge hlt) hm

lemma count_ge_finset (s : Finset ℕ) (N : ℕ)
    (hP : ∀ p ∈ s, Nat.Prime p) (hlt : ∀ p ∈ s, p < N) :
    N.count Nat.Prime ≥ s.card := by
  have hsub : s ⊆ (Finset.range N).filter Nat.Prime := by
    intro x hx
    simp [Finset.mem_filter, Finset.mem_range]
    exact ⟨hlt x hx, hP x hx⟩
  have : s.card ≤ ((Finset.range N).filter Nat.Prime).card := Finset.card_le_card hsub
  simpa [Nat.count_eq_card_filter_range] using this

lemma disjoint_of_lt_sets (s t : Finset ℕ)
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) : Disjoint s t := by
  refine Finset.disjoint_left.2 ?_
  intro x hxs hxt
  exact (lt_irrefl x) (h x hxs x hxt)

-- Placeholder prime batches
lemma prime_count_bound : 550172 ≤ Nat.count Nat.Prime 8165754 := by
  sorry

lemma nth_prime_le : Nat.nth Nat.Prime 550171 ≤ lastPrime0 := by
  have hlt : 550171 < Nat.count Nat.Prime 8165754 := by
    have := prime_count_bound
    omega
  have hnth := Nat.nth_lt_of_lt_count hlt
  unfold lastPrime0
  omega

lemma bound_le_conj : 2 * (Nat.nth Nat.Prime (n0 - 1) - 1) ≤ bound0 := by
  have hnth : Nat.nth Nat.Prime 550171 ≤ lastPrime0 := nth_prime_le
  have : n0 - 1 = 550171 := by decide
  rw [this]
  have h1 : Nat.nth Nat.Prime 550171 - 1 ≤ lastPrime0 - 1 :=
    Nat.sub_le_sub_right hnth 1
  have : 2 * (Nat.nth Nat.Prime 550171 - 1) ≤ 2 * (lastPrime0 - 1) :=
    Nat.mul_le_mul_left 2 h1
  have heq : 2 * (lastPrime0 - 1) = bound0 := by decide
  rwa [heq] at this

lemma not_lt_at_n0 : ¬ A232616 n0 < 2 * (Nat.nth Nat.Prime (n0 - 1) - 1) := by
  have h1 := A232616_ge_bound
  have h2 := bound_le_conj
  omega

theorem oeis_232616_conjecture_i.disproof :
    ¬ (∀ (n : ℕ), 0 < n → A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1)) := by
  intro h
  exact not_lt_at_n0 (h n0 (by decide))
