import FormalConjectures.Util.ProblemImports

open Finset ZMod Nat Set Classical

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
    -- Since n is non-zero, the NeZero n instance is available for ZMod n operations.
    have hn : NeZero n := NeZero.mk h

    -- The set $S$ of all $m$ which satisfy the complete residue system condition.
    -- The set $S$ is non-empty based on the external theorem $a(n) \le n^2$.
    let S : Set ℕ := { m : ℕ | A232616_prop n m }

    -- The least element of a non-empty set of natural numbers is its infimum, sInf.
    sInf S

/- # Disproof

We show that the conjecture fails at `n = 550172`:
`A232616 550172 = 17135927 ≥ 2 * (Nat.nth Nat.Prime 550171 - 1)`.
-/

set_option exponentiation.threshold 300
set_option maxRecDepth 40000

namespace A232616D

def av1 (r w : ℕ) : Bool :=
  let diff := (w + 550172 - (63945 + r)) % 550172
  decide (diff % 196 ≠ 0) || decide (17135927 ≤ r + 29400 * ((diff / 196 * 131) % 2807))

def avLoop : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | f+1, r, w => av1 r w && avLoop f (r+1) (2*w % 550172)

lemma avLoop_sound : ∀ f r w, avLoop f r w = true → w = 2^r % 550172 →
    ∀ i, i < f → av1 (r+i) (2^(r+i) % 550172) = true := by
  intro f
  induction f with
  | zero => intro r w _ _ i hi; omega
  | succ f ih =>
    intro r w h hw i hi
    rw [avLoop, Bool.and_eq_true] at h
    rcases i with _ | i
    · rw [Nat.add_zero, ← hw]; exact h.1
    · have h2 : 2 * w % 550172 = 2^(r+1) % 550172 := by
        rw [hw]
        calc 2 * (2^r % 550172) % 550172
            = (2 % 550172) * (2^r % 550172) % 550172 := by norm_num
          _ = 2 * 2^r % 550172 := (Nat.mul_mod 2 (2^r) 550172).symm
          _ = 2^(r+1) % 550172 := by rw [pow_succ, mul_comm]
      have h3 := ih (r+1) (2*w % 550172) h.2 h2 i (by omega)
      have h4 : r + 1 + i = r + (i+1) := by omega
      rwa [h4] at h3

lemma avLoop_sound' (f r0 w : ℕ) (hloop : avLoop f r0 w = true) (hw : w = 2^r0 % 550172) :
    ∀ r, r0 ≤ r → r < r0 + f → av1 r (2^r % 550172) = true := by
  intro r hr1 hr2
  have h := avLoop_sound f r0 w hloop hw (r - r0) (by omega)
  have hr : r0 + (r - r0) = r := by omega
  rwa [hr] at h

lemma avChunk0 : avLoop 1000 2 4 = true := by decide +kernel
lemma avW0 : (4 : Nat) = 2^2 % 550172 := by decide +kernel
lemma avChunk1 : avLoop 1000 1002 534136 = true := by decide +kernel
lemma avW1 : (534136 : Nat) = 2^1002 % 550172 := by decide +kernel
lemma avChunk2 : avLoop 1000 2002 468372 = true := by decide +kernel
lemma avW2 : (468372 : Nat) = 2^2002 % 550172 := by decide +kernel
lemma avChunk3 : avLoop 1000 3002 33688 = true := by decide +kernel
lemma avW3 : (33688 : Nat) = 2^3002 % 550172 := by decide +kernel
lemma avChunk4 : avLoop 1000 4002 287120 = true := by decide +kernel
lemma avW4 : (287120 : Nat) = 2^4002 % 550172 := by decide +kernel
lemma avChunk5 : avLoop 1000 5002 445916 = true := by decide +kernel
lemma avW5 : (445916 : Nat) = 2^5002 % 550172 := by decide +kernel
lemma avChunk6 : avLoop 1000 6002 381756 = true := by decide +kernel
lemma avW6 : (381756 : Nat) = 2^6002 % 550172 := by decide +kernel
lemma avChunk7 : avLoop 1000 7002 118700 = true := by decide +kernel
lemma avW7 : (118700 : Nat) = 2^7002 % 550172 := by decide +kernel
lemma avChunk8 : avLoop 1000 8002 30480 = true := by decide +kernel
lemma avW8 : (30480 : Nat) = 2^8002 % 550172 := by decide +kernel
lemma avChunk9 : avLoop 1000 9002 494036 = true := by decide +kernel
lemma avW9 : (494036 : Nat) = 2^9002 % 550172 := by decide +kernel
lemma avChunk10 : avLoop 1000 10002 28876 = true := by decide +kernel
lemma avW10 : (28876 : Nat) = 2^10002 % 550172 := by decide +kernel
lemma avChunk11 : avLoop 1000 11002 322408 = true := by decide +kernel
lemma avW11 : (322408 : Nat) = 2^11002 % 550172 := by decide +kernel
lemma avChunk12 : avLoop 1000 12002 370528 = true := by decide +kernel
lemma avW12 : (370528 : Nat) = 2^12002 % 550172 := by decide +kernel
lemma avChunk13 : avLoop 1000 13002 17648 = true := by decide +kernel
lemma avW13 : (17648 : Nat) = 2^13002 % 550172 := by decide +kernel
lemma avChunk14 : avLoop 1000 14002 221356 = true := by decide +kernel
lemma avW14 : (221356 : Nat) = 2^14002 % 550172 := by decide +kernel
lemma avChunk15 : avLoop 1000 15002 11232 = true := by decide +kernel
lemma avW15 : (11232 : Nat) = 2^15002 % 550172 := by decide +kernel
lemma avChunk16 : avLoop 1000 16002 85016 = true := by decide +kernel
lemma avW16 : (85016 : Nat) = 2^16002 % 550172 := by decide +kernel
lemma avChunk17 : avLoop 1000 17002 277496 = true := by decide +kernel
lemma avW17 : (277496 : Nat) = 2^17002 % 550172 := by decide +kernel
lemma avChunk18 : avLoop 1000 18002 516492 = true := by decide +kernel
lemma avW18 : (516492 : Nat) = 2^18002 % 550172 := by decide +kernel
lemma avChunk19 : avLoop 1000 19002 230980 = true := by decide +kernel
lemma avW19 : (230980 : Nat) = 2^19002 % 550172 := by decide +kernel
lemma avChunk20 : avLoop 1000 20002 490828 = true := by decide +kernel
lemma avW20 : (490828 : Nat) = 2^20002 % 550172 := by decide +kernel
lemma avChunk21 : avLoop 1000 21002 235792 = true := by decide +kernel
lemma avW21 : (235792 : Nat) = 2^21002 % 550172 := by decide +kernel
lemma avChunk22 : avLoop 1000 22002 455540 = true := by decide +kernel
lemma avW22 : (455540 : Nat) = 2^22002 % 550172 := by decide +kernel
lemma avChunk23 : avLoop 1000 23002 311180 = true := by decide +kernel
lemma avW23 : (311180 : Nat) = 2^23002 % 550172 := by decide +kernel
lemma avChunk24 : avLoop 1000 24002 269476 = true := by decide +kernel
lemma avW24 : (269476 : Nat) = 2^24002 % 550172 := by decide +kernel
lemma avChunk25 : avLoop 1000 25002 208524 = true := by decide +kernel
lemma avW25 : (208524 : Nat) = 2^25002 % 550172 := by decide +kernel
lemma avChunk26 : avLoop 1000 26002 288724 = true := by decide +kernel
lemma avW26 : (288724 : Nat) = 2^26002 % 550172 := by decide +kernel
lemma avChunk27 : avLoop 1000 27002 67372 = true := by decide +kernel
lemma avW27 : (67372 : Nat) = 2^27002 % 550172 := by decide +kernel
lemma avChunk28 : avLoop 1000 28002 40104 = true := by decide +kernel
lemma avW28 : (40104 : Nat) = 2^28002 % 550172 := by decide +kernel
lemma avChunk29 : avLoop 400 29002 423460 = true := by decide +kernel
lemma avW29 : (423460 : Nat) = 2^29002 % 550172 := by decide +kernel

/-- Every r in [2, 29402) passes the avoidance check. -/
lemma avAll : ∀ r, 2 ≤ r → r < 29402 → av1 r (2^r % 550172) = true := by
  intro r h2 h29402
  by_cases hc0 : r < 1002
  · exact avLoop_sound' 1000 2 4 avChunk0 avW0 r (by omega) (by omega)
  by_cases hc1 : r < 2002
  · exact avLoop_sound' 1000 1002 534136 avChunk1 avW1 r (by omega) (by omega)
  by_cases hc2 : r < 3002
  · exact avLoop_sound' 1000 2002 468372 avChunk2 avW2 r (by omega) (by omega)
  by_cases hc3 : r < 4002
  · exact avLoop_sound' 1000 3002 33688 avChunk3 avW3 r (by omega) (by omega)
  by_cases hc4 : r < 5002
  · exact avLoop_sound' 1000 4002 287120 avChunk4 avW4 r (by omega) (by omega)
  by_cases hc5 : r < 6002
  · exact avLoop_sound' 1000 5002 445916 avChunk5 avW5 r (by omega) (by omega)
  by_cases hc6 : r < 7002
  · exact avLoop_sound' 1000 6002 381756 avChunk6 avW6 r (by omega) (by omega)
  by_cases hc7 : r < 8002
  · exact avLoop_sound' 1000 7002 118700 avChunk7 avW7 r (by omega) (by omega)
  by_cases hc8 : r < 9002
  · exact avLoop_sound' 1000 8002 30480 avChunk8 avW8 r (by omega) (by omega)
  by_cases hc9 : r < 10002
  · exact avLoop_sound' 1000 9002 494036 avChunk9 avW9 r (by omega) (by omega)
  by_cases hc10 : r < 11002
  · exact avLoop_sound' 1000 10002 28876 avChunk10 avW10 r (by omega) (by omega)
  by_cases hc11 : r < 12002
  · exact avLoop_sound' 1000 11002 322408 avChunk11 avW11 r (by omega) (by omega)
  by_cases hc12 : r < 13002
  · exact avLoop_sound' 1000 12002 370528 avChunk12 avW12 r (by omega) (by omega)
  by_cases hc13 : r < 14002
  · exact avLoop_sound' 1000 13002 17648 avChunk13 avW13 r (by omega) (by omega)
  by_cases hc14 : r < 15002
  · exact avLoop_sound' 1000 14002 221356 avChunk14 avW14 r (by omega) (by omega)
  by_cases hc15 : r < 16002
  · exact avLoop_sound' 1000 15002 11232 avChunk15 avW15 r (by omega) (by omega)
  by_cases hc16 : r < 17002
  · exact avLoop_sound' 1000 16002 85016 avChunk16 avW16 r (by omega) (by omega)
  by_cases hc17 : r < 18002
  · exact avLoop_sound' 1000 17002 277496 avChunk17 avW17 r (by omega) (by omega)
  by_cases hc18 : r < 19002
  · exact avLoop_sound' 1000 18002 516492 avChunk18 avW18 r (by omega) (by omega)
  by_cases hc19 : r < 20002
  · exact avLoop_sound' 1000 19002 230980 avChunk19 avW19 r (by omega) (by omega)
  by_cases hc20 : r < 21002
  · exact avLoop_sound' 1000 20002 490828 avChunk20 avW20 r (by omega) (by omega)
  by_cases hc21 : r < 22002
  · exact avLoop_sound' 1000 21002 235792 avChunk21 avW21 r (by omega) (by omega)
  by_cases hc22 : r < 23002
  · exact avLoop_sound' 1000 22002 455540 avChunk22 avW22 r (by omega) (by omega)
  by_cases hc23 : r < 24002
  · exact avLoop_sound' 1000 23002 311180 avChunk23 avW23 r (by omega) (by omega)
  by_cases hc24 : r < 25002
  · exact avLoop_sound' 1000 24002 269476 avChunk24 avW24 r (by omega) (by omega)
  by_cases hc25 : r < 26002
  · exact avLoop_sound' 1000 25002 208524 avChunk25 avW25 r (by omega) (by omega)
  by_cases hc26 : r < 27002
  · exact avLoop_sound' 1000 26002 288724 avChunk26 avW26 r (by omega) (by omega)
  by_cases hc27 : r < 28002
  · exact avLoop_sound' 1000 27002 67372 avChunk27 avW27 r (by omega) (by omega)
  by_cases hc28 : r < 29002
  · exact avLoop_sound' 1000 28002 40104 avChunk28 avW28 r (by omega) (by omega)
  by_cases hc29 : r < 29402
  · exact avLoop_sound' 400 29002 423460 avChunk29 avW29 r (by omega) (by omega)
  omega

/- Arithmetic core -/

lemma pow_base : (2:ℕ)^29402 ≡ 4 [MOD 550172] := by
  show 2^29402 % 550172 = 4 % 550172
  decide +kernel

lemma pow_period_step {a : ℕ} (ha : 2 ≤ a) : 2^(a + 29400) ≡ 2^a [MOD 550172] := by
  have h2 : a = (a - 2) + 2 := by omega
  calc (2:ℕ)^(a + 29400) = 2^(a-2) * 2^29402 := by rw [← pow_add]; congr 1; omega
    _ ≡ 2^(a-2) * 4 [MOD 550172] := Nat.ModEq.mul_left _ pow_base
    _ = 2^((a-2) + 2) := by rw [pow_add]; norm_num
    _ = 2^a := by rw [← h2]

lemma pow_period (a : ℕ) (t : ℕ) (ha : 2 ≤ a) : 2^(a + 29400 * t) ≡ 2^a [MOD 550172] := by
  induction t with
  | zero => simpa using Nat.ModEq.refl (2^a)
  | succ t ih =>
    have he : a + 29400 * (t+1) = (a + 29400*t) + 29400 := by ring
    rw [he]
    exact (pow_period_step (by omega)).trans ih

/-- The canonical "gap" value. -/
def diffOf (r v : ℕ) : ℕ := (2^r % 550172 + 550172 - (v + r) % 550172) % 550172

lemma diff_cong (r v : ℕ) : (diffOf r v : ℤ) ≡ 2^r - ((v:ℤ) + r) [ZMOD 550172] := by
  have hw : 2^r % 550172 < 550172 := Nat.mod_lt _ (by norm_num)
  have hu : (v + r) % 550172 < 550172 := Nat.mod_lt _ (by norm_num)
  have hle : (v + r) % 550172 ≤ 2^r % 550172 + 550172 := by omega
  have step1 : (diffOf r v : ℤ) ≡ ((2^r % 550172 + 550172 - (v + r) % 550172 : ℕ) : ℤ) [ZMOD 550172] := by
    exact_mod_cast Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)
  have step2 : ((2^r % 550172 + 550172 - (v + r) % 550172 : ℕ) : ℤ)
      = ((2^r % 550172 : ℕ) : ℤ) + 550172 - ((v + r) % 550172 : ℕ) := by
    push_cast [Nat.cast_sub hle]
    ring
  have hw2 : ((2^r % 550172 : ℕ) : ℤ) ≡ 2^r [ZMOD 550172] := by
    exact_mod_cast Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)
  have hu2 : (((v + r) % 550172 : ℕ) : ℤ) ≡ (v:ℤ) + r [ZMOD 550172] := by
    exact_mod_cast Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)
  have hn0 : (550172 : ℤ) ≡ 0 [ZMOD 550172] := Dvd.dvd.modEq_zero_int dvd_rfl
  calc (diffOf r v : ℤ)
      ≡ ((2^r % 550172 : ℕ) : ℤ) + 550172 - ((v + r) % 550172 : ℕ) [ZMOD 550172] := by
        rw [← step2]; exact step1
    _ ≡ 2^r + 0 - ((v:ℤ) + r) [ZMOD 550172] := ((hw2.add hn0).sub hu2)
    _ = 2^r - ((v:ℤ) + r) := by ring

/-- If `2^r ≡ v + r + 29400 t (mod 550172)` then `196 ∣ diffOf r v` and
    the canonical minimal solution `τ` satisfies `τ ≤ t`. -/
lemma solve_forced {r v t : ℕ} (hcong : 2^r ≡ v + r + 29400*t [MOD 550172]) :
    196 ∣ diffOf r v ∧ (diffOf r v / 196 * 131) % 2807 ≤ t := by
  have hz0 : ((2^r : ℕ) : ℤ) ≡ ((v + r + 29400*t : ℕ) : ℤ) [ZMOD 550172] :=
    Int.natCast_modEq_iff.mpr hcong
  have hz : (2:ℤ)^r ≡ (v:ℤ) + r + 29400*t [ZMOD 550172] := by
    push_cast at hz0; exact hz0
  have h1 : (diffOf r v : ℤ) ≡ 29400 * t [ZMOD 550172] := by
    calc (diffOf r v : ℤ) ≡ 2^r - ((v:ℤ) + r) [ZMOD 550172] := diff_cong r v
      _ ≡ ((v:ℤ) + r + 29400*t) - ((v:ℤ) + r) [ZMOD 550172] := hz.sub_right _
      _ = 29400 * t := by ring
  -- divisibility by 196
  have h3 : (diffOf r v : ℤ) ≡ 0 [ZMOD 196] :=
    (h1.of_dvd (by norm_num)).trans (Dvd.dvd.modEq_zero_int ⟨150*t, by ring⟩)
  have hdvd : (196:ℕ) ∣ diffOf r v := by
    have := Int.modEq_zero_iff_dvd.mp h3
    exact_mod_cast this
  refine ⟨hdvd, ?_⟩
  obtain ⟨D, hD⟩ := hdvd
  have hDdiv : diffOf r v / 196 = D := by omega
  rw [hDdiv]
  -- reduce the congruence mod 2807 after cancelling 196
  have h4 : (550172:ℤ) ∣ (29400*(t:ℤ) - 196*D) := by
    have hdd := Int.ModEq.dvd h1
    have hcast : (diffOf r v : ℤ) = 196 * D := by exact_mod_cast hD
    rw [hcast] at hdd
    exact hdd
  have h5 : (2807:ℤ) ∣ (150*(t:ℤ) - D) := by
    rcases h4 with ⟨z, hz4⟩
    refine ⟨z, ?_⟩
    have h6 : (196:ℤ) * (150*(t:ℤ) - D) = 196 * (2807 * z) := by linarith
    have := mul_left_cancel₀ (by norm_num : (196:ℤ) ≠ 0) h6
    linarith
  have h7 : (150*(t:ℤ)) ≡ (D:ℤ) [ZMOD 2807] := by
    rw [Int.modEq_iff_dvd, ← neg_sub (150*(t:ℤ)) (D:ℤ)]
    exact dvd_neg.mpr h5
  have h8 : (19650*(t:ℤ)) ≡ 131*(D:ℤ) [ZMOD 2807] := by
    have := h7.mul_left 131
    have e1 : (131:ℤ) * (150*(t:ℤ)) = 19650*(t:ℤ) := by ring
    rwa [e1] at this
  have h9 : (t:ℤ) ≡ 19650*(t:ℤ) [ZMOD 2807] := (Int.modEq_iff_dvd.mpr ⟨-7*(t:ℤ), by ring⟩).symm
  have h10 : (t:ℤ) ≡ 131*(D:ℤ) [ZMOD 2807] := h9.trans h8
  have h11 : ((D*131 % 2807 : ℕ):ℤ) ≡ (t:ℤ) [ZMOD 2807] := by
    have hc : ((D*131 % 2807 : ℕ):ℤ) ≡ ((D*131:ℕ):ℤ) [ZMOD 2807] :=
      Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)
    have e2 : ((D*131:ℕ):ℤ) = 131*(D:ℤ) := by push_cast; ring
    rw [e2] at hc
    exact hc.trans h10.symm
  have h12 := Int.ModEq.dvd h11
  obtain ⟨z, hz12⟩ := h12
  have hτlt : D*131 % 2807 < 2807 := Nat.mod_lt _ (by norm_num)
  omega

/-- Construction direction: if `196 ∣ diffOf r v` then the canonical τ solves the congruence. -/
lemma solve_exists {r v : ℕ} (hdvd : 196 ∣ diffOf r v) :
    2^r ≡ v + r + 29400 * ((diffOf r v / 196 * 131) % 2807) [MOD 550172] := by
  obtain ⟨D, hD⟩ := hdvd
  have hDdiv : diffOf r v / 196 = D := by omega
  rw [hDdiv]
  have h1 : ((D * 131 % 2807 : ℕ):ℤ) ≡ 131*(D:ℤ) [ZMOD 2807] := by
    have hc : ((D*131 % 2807 : ℕ):ℤ) ≡ ((D*131:ℕ):ℤ) [ZMOD 2807] :=
      Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)
    have e2 : ((D*131:ℕ):ℤ) = 131*(D:ℤ) := by push_cast; ring
    rwa [e2] at hc
  have h2 : 150*((D * 131 % 2807 : ℕ):ℤ) ≡ 150*(131*(D:ℤ)) [ZMOD 2807] := h1.mul_left 150
  have h3 : 150*(131*(D:ℤ)) ≡ (D:ℤ) [ZMOD 2807] :=
    (Int.modEq_iff_dvd.mpr ⟨-7*(D:ℤ), by ring⟩)
  have h4 : 150*((D * 131 % 2807 : ℕ):ℤ) ≡ (D:ℤ) [ZMOD 2807] := h2.trans h3
  have h5 : 196*(150*((D * 131 % 2807 : ℕ):ℤ)) ≡ 196*(D:ℤ) [ZMOD 196*2807] := h4.mul_left'
  have h6 : 29400*((D * 131 % 2807 : ℕ):ℤ) ≡ (diffOf r v : ℤ) [ZMOD 550172] := by
    have hcast : (diffOf r v : ℤ) = 196 * D := by exact_mod_cast hD
    have e3 : (196:ℤ)*(150*((D * 131 % 2807 : ℕ):ℤ)) = 29400*((D * 131 % 2807 : ℕ):ℤ) := by ring
    have e4 : (196:ℤ)*2807 = 550172 := by norm_num
    rw [e3, e4, ← hcast] at h5
    exact h5
  -- combine with diff_cong
  have h7 : ((v + r + 29400 * (D * 131 % 2807) : ℕ) : ℤ) ≡ (2:ℤ)^r [ZMOD 550172] := by
    have e5 : ((v + r + 29400 * (D * 131 % 2807) : ℕ) : ℤ)
        = ((v:ℤ) + r) + 29400*((D * 131 % 2807 : ℕ):ℤ) := by push_cast; ring
    rw [e5]
    calc ((v:ℤ) + r) + 29400*((D * 131 % 2807 : ℕ):ℤ)
        ≡ ((v:ℤ) + r) + (diffOf r v : ℤ) [ZMOD 550172] := (h6.add_left _)
      _ ≡ ((v:ℤ) + r) + (2^r - ((v:ℤ) + r)) [ZMOD 550172] := ((diff_cong r v).add_left _)
      _ = 2^r := by ring
  have h8 : ((2^r : ℕ):ℤ) ≡ ((v + r + 29400 * (D * 131 % 2807) : ℕ) : ℤ) [ZMOD 550172] := by
    push_cast
    exact h7.symm
  exact Int.natCast_modEq_iff.mp h8

/-- The avoidance theorem: x* = 63945 is not hit before k = 17135927. -/
theorem avoid {k : ℕ} (hk1 : 1 ≤ k) (hkB : k < 17135927)
    (hcong : 2^k ≡ 63945 + k [MOD 550172]) : False := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1' : k = 1 := by omega
    subst hk1'
    exact absurd hcong (by decide)
  · have hk : k = (2 + (k-2) % 29400) + 29400 * ((k-2) / 29400) := by omega
    set r := 2 + (k-2) % 29400 with hrdef
    set t := (k-2) / 29400 with htdef
    have hr2 : 2 ≤ r := by omega
    have hrlt : r < 29402 := by
      have := Nat.mod_lt (k-2) (show 0 < 29400 by norm_num)
      omega
    have hp : 2^k ≡ 2^r [MOD 550172] := by
      conv_lhs => rw [hk]
      exact pow_period r t hr2
    have hcong2 : 2^r ≡ 63945 + r + 29400*t [MOD 550172] := by
      have h := hp.symm.trans hcong
      rwa [hk, ← Nat.add_assoc] at h
    obtain ⟨hdvd, hτ⟩ := solve_forced hcong2
    have hAv := avAll r hr2 hrlt
    simp only [av1, Bool.or_eq_true, decide_eq_true_eq] at hAv
    have hdiff : (2^r % 550172 + 550172 - (63945 + r)) % 550172 = diffOf r 63945 := by
      rw [diffOf, Nat.mod_eq_of_lt (show 63945 + r < 550172 by omega)]
    rcases hAv with h | h
    · rw [hdiff] at h
      obtain ⟨D, hD⟩ := hdvd
      omega
    · rw [hdiff] at h
      have hmul := Nat.mul_le_mul_left 29400 hτ
      omega


/- Coverage -/

def Rtab : List ℕ := [36, 143, 2, 349, 308, 3, 26, 225, 332, 191, 50, 81, 4, 31, 58, 85, 48, 139, 98, 193, 220, 15, 122, 237, 328, 287, 146, 5, 204, 311, 170, 29, 60, 171, 10, 37, 64, 27, 118, 77, 172, 199, 226, 101, 216, 307, 266, 125, 72, 183, 290, 149, 8, 39, 150, 173, 16, 43, 6, 97, 56, 151, 178, 205, 80, 195, 286, 245, 104, 51, 162, 269, 128, 475, 18, 129, 152, 11, 22, 49, 76, 35, 130, 157, 184, 59, 174, 265, 224, 83, 30, 141, 248, 107, 454, 413, 108, 131, 330, 437, 28, 55, 14, 109, 136, 163, 38, 153, 244, 203, 62, 9, 120, 227, 86, 433, 392, 87, 110, 309, 416, 7, 34, 61, 88, 115, 142, 17, 132, 223, 182, 41, 304, 99, 206, 65, 412, 371, 66, 89, 288, 395, 254, 13, 40, 67, 94, 121, 148, 111, 202, 161, 20, 283, 78, 185, 44, 391, 350, 45, 68, 267, 374, 233, 12, 19, 46, 73, 100, 127, 90, 181, 140, 235, 262, 57, 164, 23, 370, 329, 24, 47, 246, 353, 212, 71, 102, 25, 52, 79, 106, 69, 160, 119, 214, 241]

def cov1 (c r : ℕ) : Bool :=
  decide (2 ≤ r) && decide (r < 476) && decide ((2^r % 550172 + 550172 - r) % 196 = c)

lemma covCheck : ((List.range 196).all fun c => cov1 c (Rtab.getD c 0)) = true := by
  decide +kernel

lemma covAll (c : ℕ) (hc : c < 196) : cov1 c (Rtab.getD c 0) = true := by
  have h := covCheck
  rw [List.all_eq_true] at h
  exact h c (List.mem_range.mpr hc)

/-- Coverage: every residue v mod 550172 is hit by some k ≤ 82526801. -/
theorem cover (v : ℕ) (hv : v < 550172) :
    ∃ k, 1 ≤ k ∧ k ≤ 82526801 ∧ 2^k ≡ v + k [MOD 550172] := by
  have hcov := covAll (v % 196) (Nat.mod_lt _ (by norm_num))
  set r := Rtab.getD (v % 196) 0 with hrdef
  simp only [cov1, Bool.and_eq_true, decide_eq_true_eq] at hcov
  obtain ⟨⟨hr2, hr476⟩, hclass⟩ := hcov
  -- 196 ∣ diffOf r v  (pure ℕ congruence chase mod 196)
  have hdvd : 196 ∣ diffOf r v := by
    -- E := 2^r % 550172 + 550172 - r  satisfies E % 196 = v % 196 and E + r = 2^r % 550172 + 550172
    have hE : (2^r % 550172 + 550172 - r) + r = 2^r % 550172 + 550172 := by omega
    -- 2^r ≡ v % 196 + r [MOD 196]
    have h1 : 2^r % 550172 + 550172 ≡ v % 196 + r [MOD 196] := by
      calc 2^r % 550172 + 550172
          = ((2^r % 550172 + 550172 - r) + r) := hE.symm
        _ ≡ (v % 196) + r [MOD 196] := by
            have hx : (2^r % 550172 + 550172 - r) ≡ (2^r % 550172 + 550172 - r) % 196 [MOD 196] :=
              (Nat.mod_modEq _ 196).symm
            rw [hclass] at hx
            exact Nat.ModEq.add_right r hx
    have h2 : 2^r ≡ 2^r % 550172 + 550172 [MOD 196] := by
      have ha : 2^r ≡ 2^r % 550172 [MOD 196] :=
        (Nat.ModEq.of_dvd (by norm_num) (Nat.mod_modEq (2^r) 550172)).symm
      have hb : 2^r % 550172 + 0 ≡ 2^r % 550172 + 550172 [MOD 196] :=
        Nat.ModEq.add_left _ (by decide)
      simpa using ha.trans hb
    have h3 : 2^r ≡ v % 196 + r [MOD 196] := h2.trans h1
    -- diffOf + ((v+r) % 550172) = 2^r % 550172 + 550172 - correction... work via ModEq:
    -- diffOf r v ≡ (2^r % 550172 + 550172) - ((v+r) % 550172)... avoid sub: add and cancel.
    have hu : (v + r) % 550172 ≤ 2^r % 550172 + 550172 := by
      have := Nat.mod_lt (v + r) (show 0 < 550172 by norm_num)
      omega
    have hE2 : (2^r % 550172 + 550172 - (v + r) % 550172) + (v + r) % 550172
        = 2^r % 550172 + 550172 := by omega
    have h4 : diffOf r v + (v + r) % 550172 ≡ 2^r % 550172 + 550172 [MOD 196] := by
      calc diffOf r v + (v + r) % 550172
          ≡ (2^r % 550172 + 550172 - (v + r) % 550172) + (v + r) % 550172 [MOD 196] := by
            exact Nat.ModEq.add_right _ (Nat.ModEq.of_dvd (by norm_num) (Nat.mod_modEq _ 550172))
        _ = 2^r % 550172 + 550172 := hE2
    have h5 : (v + r) % 550172 ≡ v + r [MOD 196] :=
      Nat.ModEq.of_dvd (by norm_num) (Nat.mod_modEq _ 550172)
    have h6 : diffOf r v + (v + r) ≡ 0 + (v + r) [MOD 196] := by
      have hva : v ≡ v % 196 [MOD 196] := (Nat.mod_modEq v 196).symm
      calc diffOf r v + (v + r)
          ≡ diffOf r v + (v + r) % 550172 [MOD 196] := Nat.ModEq.add_left _ h5.symm
        _ ≡ 2^r % 550172 + 550172 [MOD 196] := h4
        _ ≡ v % 196 + r [MOD 196] := h1
        _ ≡ 0 + (v + r) [MOD 196] := by
            have : v % 196 + r ≡ v + r [MOD 196] := Nat.ModEq.add_right r hva.symm
            simpa using this
    have h7 : diffOf r v ≡ 0 [MOD 196] := Nat.ModEq.add_right_cancel' _ h6
    exact (Nat.modEq_zero_iff_dvd).mp h7
  -- construct k
  have hcong := solve_exists hdvd
  set τ := (diffOf r v / 196 * 131) % 2807 with hτdef
  have hτlt : τ < 2807 := Nat.mod_lt _ (by norm_num)
  refine ⟨r + 29400 * τ, by omega, by nlinarith, ?_⟩
  have hp : 2^(r + 29400 * τ) ≡ 2^r [MOD 550172] := pow_period r τ hr2
  calc 2^(r + 29400 * τ) ≡ 2^r [MOD 550172] := hp
    _ ≡ v + r + 29400 * τ [MOD 550172] := hcong
    _ = v + (r + 29400 * τ) := by ring

/- # Verified prime-counting sieve
Goal: `550171 < Nat.count Nat.Prime 8567965` -/

set_option exponentiation.threshold 300
set_option maxRecDepth 40000

namespace Sieve

/- ## The bit pattern `pat p m = Σ_{j<m} 2^(p*j)` -/

def pat (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | m+1 => 1 + 2^p * pat p m

lemma pat_mul_add_one {p : ℕ} (hp : 1 ≤ p) (m : ℕ) : (2^p - 1) * pat p m + 1 = 2^(p*m) := by
  induction m with
  | zero => simp [pat]
  | succ m ih =>
    have h2p : 1 ≤ 2^p := Nat.one_le_two_pow
    calc (2^p - 1) * pat p (m+1) + 1
        = (2^p - 1) * (1 + 2^p * pat p m) + 1 := by rw [pat]
      _ = (2^p - 1) + 2^p * ((2^p - 1) * pat p m + 1) - 2^p + 1 := by
          rw [Nat.mul_add]; ring_nf; omega
      _ = (2^p - 1) + 2^p * 2^(p*m) - 2^p + 1 := by rw [ih]
      _ = 2^p * 2^(p*m) - 1 + 1 := by
          have h1 : 1 ≤ 2^p * 2^(p*m) := Nat.one_le_iff_ne_zero.mpr (by positivity)
          omega
      _ = 2^(p*(m+1)) := by
          have he : p + p*m = p*(m+1) := by ring
          rw [← pow_add, he]
          have h1 : 1 ≤ 2^(p*(m+1)) := Nat.one_le_two_pow
          omega

lemma pat_lt {p : ℕ} (hp : 1 ≤ p) (m : ℕ) : pat p m < 2^(p*m) := by
  have h := pat_mul_add_one hp m
  have h2p : 2 ≤ 2^p := by
    calc 2 = 2^1 := (pow_one 2).symm
    _ ≤ 2^p := Nat.pow_le_pow_right (by norm_num) hp
  have hle : pat p m ≤ (2^p - 1) * pat p m :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- kernel-fast form of `pat` -/
def patF (p m : ℕ) : ℕ := (2^(p*m) - 1) / (2^p - 1)

lemma patF_eq {p : ℕ} (hp : 1 ≤ p) (m : ℕ) : patF p m = pat p m := by
  have h := pat_mul_add_one hp m
  have h2p : 2 ≤ 2^p := by
    calc 2 = 2^1 := (pow_one 2).symm
    _ ≤ 2^p := Nat.pow_le_pow_right (by norm_num) hp
  have hd : 2^(p*m) - 1 = (2^p - 1) * pat p m := by omega
  rw [patF, hd]
  exact Nat.mul_div_cancel_left _ (by omega)

/- ## Digit sums -/

/-- Sum of base-`2^s` digits of `n` (junk value `0` if `s = 0`). -/
def dsum (s : ℕ) (n : ℕ) : ℕ :=
  if hn : n = 0 then 0
  else if hs : s = 0 then 0
  else n % 2^s + dsum s (n / 2^s)
  decreasing_by
    exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (Nat.one_lt_two_pow hs)

lemma dsum_zero (s : ℕ) : dsum s 0 = 0 := by rw [dsum]; simp

lemma dsum_step {s : ℕ} (hs : s ≠ 0) (n : ℕ) : dsum s n = n % 2^s + dsum s (n / 2^s) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [dsum_zero]
  · rw [dsum]; simp [hn, hs]

lemma dsum_of_lt {s : ℕ} (hs : s ≠ 0) {n : ℕ} (h : n < 2^s) : dsum s n = n := by
  rw [dsum_step hs, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, dsum_zero, Nat.add_zero]

/- ## bitwise helpers -/

lemma land_mod_two_pow (a b t : ℕ) : (a &&& b) % 2^t = (a % 2^t) &&& (b % 2^t) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_land]
  by_cases h : i < t <;> simp [h]

lemma land_div_two_pow (a b t : ℕ) : (a &&& b) / 2^t = (a / 2^t) &&& (b / 2^t) := by
  simpa only [Nat.shiftRight_eq_div_pow] using (Nat.shiftRight_and_distrib (a := a) (b := b) (i := t))

lemma add_split {B a b : ℕ} (hB : 0 < B) (h : a % B + b % B < B) :
    (a + b) % B = a % B + b % B ∧ (a + b) / B = a / B + b / B := by
  have ha := Nat.div_add_mod a B
  have hb := Nat.div_add_mod b B
  have hab : a + b = (a % B + b % B) + B * (a / B + b / B) := by ring_nf; omega
  constructor
  · rw [hab, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
  · rw [hab, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt h, Nat.zero_add]

/- ## The doubling round -/

lemma round_eq {s : ℕ} (hs : 1 ≤ s) : ∀ m n, n < 2^(2*s*m) →
    dsum (2*s) ((n &&& ((2^s - 1) * pat (2*s) m)) + ((n / 2^s) &&& ((2^s - 1) * pat (2*s) m)))
      = dsum s n := by
  intro m
  induction m with
  | zero =>
    intro n hn
    have : n = 0 := by simpa using hn
    subst this
    simp [pat, dsum_zero]
  | succ m ih =>
    intro n hn
    set B := 2^(2*s) with hBdef
    have hBpos : 0 < B := by positivity
    set M := (2^s - 1) * pat (2*s) (m+1) with hMdef
    set M' := (2^s - 1) * pat (2*s) m with hM'def
    have hs2 : (1:ℕ) ≤ 2^s := Nat.one_le_two_pow
    have hslt : 2^s < B := by
      rw [hBdef]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    -- structure of M
    have hMstruct : M = (2^s - 1) + B * M' := by
      rw [hMdef, hM'def, pat, hBdef]; ring
    have hMmod : M % B = 2^s - 1 := by
      rw [hMstruct, Nat.mul_comm B M', Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have hMdiv : M / B = M' := by
      rw [hMstruct, Nat.mul_comm B M', Nat.add_mul_div_right _ _ hBpos, Nat.div_eq_of_lt (by omega),
        Nat.zero_add]
    -- the two masked summands
    set A1 := n &&& M with hA1
    set A2 := (n / 2^s) &&& M with hA2
    have hdvd_s_2s : (2^s : ℕ) ∣ B := by
      rw [hBdef]; exact pow_dvd_pow 2 (by omega)
    have hA1mod : A1 % B = n % 2^s := by
      rw [hA1, land_mod_two_pow, hMmod, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_mod_of_dvd _ hdvd_s_2s]
    have hA2mod : A2 % B = (n / 2^s) % 2^s := by
      rw [hA2, land_mod_two_pow, hMmod, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_mod_of_dvd _ hdvd_s_2s]
    have hA1div : A1 / B = (n / B) &&& M' := by
      rw [hA1, land_div_two_pow, hMdiv]
    have hA2div : A2 / B = ((n / B) / 2^s) &&& M' := by
      rw [hA2, land_div_two_pow, hMdiv, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
        mul_comm (2^s) B]
    -- smallness
    have hnm : n % 2^s < 2^s := Nat.mod_lt _ (by positivity)
    have hnm2 : (n / 2^s) % 2^s < 2^s := Nat.mod_lt _ (by positivity)
    have hsmall : A1 % B + A2 % B < B := by
      rw [hA1mod, hA2mod, hBdef]
      have h2 : 2^s + 2^s ≤ 2^(2*s) := by
        have : 2^(s+1) ≤ 2^(2*s) := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at this
        omega
      omega
    obtain ⟨hsplitmod, hsplitdiv⟩ := add_split hBpos hsmall
    -- recursion
    have hnB : n / B < 2^(2*s*m) := by
      rw [Nat.div_lt_iff_lt_mul hBpos, hBdef, ← pow_add]
      calc n < 2^(2*s*(m+1)) := hn
        _ = 2^(2*s*m + 2*s) := by ring_nf
    have hihn := ih (n / B) hnB
    have h2s0 : (2*s) ≠ 0 := by omega
    have hs0 : s ≠ 0 := by omega
    calc dsum (2*s) (A1 + A2)
        = (A1 + A2) % B + dsum (2*s) ((A1 + A2) / B) := by
          rw [dsum_step h2s0]
      _ = (n % 2^s + (n / 2^s) % 2^s) + dsum (2*s) (((n/B) &&& M') + (((n/B)/2^s) &&& M')) := by
          rw [hsplitmod, hsplitdiv, hA1mod, hA2mod, hA1div, hA2div]
      _ = (n % 2^s + (n / 2^s) % 2^s) + dsum s (n / B) := by rw [hihn]
      _ = dsum s n := by
          have hdd : n / 2^s / 2^s = n / B := by
            rw [Nat.div_div_eq_div_mul, ← pow_add, hBdef, two_mul]
          rw [dsum_step hs0 n, dsum_step hs0 (n / 2^s), hdd]
          omega

/- ## Sieve data -/

def X : ℕ := 8567965

def tdLoop : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | f+1, n, j => if j*j > n then true else (n % j != 0) && tdLoop f n (j+2)

def isP (n : ℕ) : Bool := decide (2 ≤ n) && (n == 2 || (n % 2 == 1 && tdLoop 30 n 3))

def Plist : List ℕ := (List.range 2928).filter isP

def mp (p : ℕ) : ℕ := (X-1)/p - 1

def maskOf (p : ℕ) : ℕ := patF p (mp p) <<< (2*p)

def CC : ℕ := Plist.foldr (fun p acc => maskOf p ||| acc) 0

def rmask (j : ℕ) : ℕ := (2^(2^j) - 1) * patF (2^(j+1)) (2^(23-j))

def rnd (j n : ℕ) : ℕ := (n &&& rmask j) + ((n / 2^(2^j)) &&& rmask j)

def iterRounds : ℕ → ℕ → ℕ
  | 0, n => n
  | j+1, n => rnd j (iterRounds j n)

/- ## Round correctness -/

lemma rmask_eq (j : ℕ) : rmask j = (2^(2^j) - 1) * pat (2*2^j) (2^(23-j)) := by
  rw [rmask, patF_eq Nat.one_le_two_pow, pow_succ, mul_comm (2^j) 2]

lemma sq_helper {a : ℕ} (h : 1 ≤ a) : (a+1)*(a-1) = a*a - 1 := by
  rcases Nat.exists_eq_add_of_le h with ⟨b, rfl⟩
  have h1 : 1 + b - 1 = b := by omega
  rw [h1]
  have h2 : (1+b)*(1+b) = (1+b+1)*b + 1 := by ring
  omega

lemma round_correct {j : ℕ} (hj : j < 24) {n : ℕ} (hn : n < 2^(2^24)) :
    dsum (2^(j+1)) (rnd j n) = dsum (2^j) n ∧ rnd j n < 2^(2^24) := by
  set s := 2^j with hsdef
  have hs : 1 ≤ s := Nat.one_le_two_pow
  have hexp : 2*s*2^(23-j) = 2^24 := by
    have h1 : (2:ℕ)^(1 + j + (23 - j)) = 2*2^j*2^(23-j) := by
      rw [pow_add, pow_add, pow_one]
    have h2 : 1 + j + (23 - j) = 24 := by omega
    rw [h2] at h1
    rw [hsdef, ← h1]
  have hn' : n < 2^(2*s*2^(23-j)) := by rw [hexp]; exact hn
  have hre := round_eq hs (2^(23-j)) n hn'
  have hrmask : rmask j = (2^s - 1) * pat (2*s) (2^(23-j)) := rmask_eq j
  have h2s : 2^(j+1) = 2*s := by rw [hsdef, pow_succ, mul_comm]
  constructor
  · rw [h2s, rnd, hrmask]
    exact hre
  · -- bound
    have hpm := pat_mul_add_one (p := 2*s) (by omega) (2^(23-j))
    rw [hexp] at hpm
    have hsq : (2^s + 1) * (2^s - 1) = 2^(2*s) - 1 := by
      have := sq_helper (a := 2^s) Nat.one_le_two_pow
      rw [this, ← pow_add, two_mul]
    have hb : (2^s + 1) * rmask j = 2^(2^24) - 1 := by
      rw [hrmask, ← mul_assoc, hsq]
      omega
    have hle1 : rnd j n ≤ 2 * rmask j := by
      have a1 : n &&& rmask j ≤ rmask j := Nat.and_le_right
      have a2 : (n / 2^(2^j)) &&& rmask j ≤ rmask j := Nat.and_le_right
      rw [rnd]; omega
    have hle2 : 2 * rmask j ≤ (2^s + 1) * rmask j := by
      apply Nat.mul_le_mul _ le_rfl
      have : (2:ℕ) ≤ 2^s := by
        calc (2:ℕ) = 2^1 := (pow_one 2).symm
        _ ≤ 2^s := Nat.pow_le_pow_right (by norm_num) hs
      omega
    have hpos : (1:ℕ) ≤ 2^(2^24) := Nat.one_le_two_pow
    omega

lemma iter_correct {n : ℕ} (hn : n < 2^(2^24)) :
    ∀ j, j ≤ 24 → dsum (2^j) (iterRounds j n) = dsum 1 n ∧ iterRounds j n < 2^(2^24) := by
  intro j
  induction j with
  | zero => intro _; exact ⟨by rw [pow_zero, iterRounds], by rw [iterRounds]; exact hn⟩
  | succ j ih =>
    intro hj
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨h3, h4⟩ := round_correct (show j < 24 by omega) h2
    refine ⟨?_, ?_⟩
    · rw [iterRounds, h3, h1]
    · rw [iterRounds]; exact h4

/- ## dsum 1 counts bits -/

lemma dsum1_card : ∀ L n, n < 2^L → dsum 1 n = ((Finset.range L).filter (fun i => n.testBit i)).card := by
  intro L
  induction L with
  | zero =>
    intro n hn
    have : n = 0 := by simpa using hn
    subst this
    simp [dsum_zero]
  | succ L ih =>
    intro n hn
    have hn2 : n / 2 < 2^L := by
      have h1 : (2:ℕ)^(L+1) = 2^L * 2 := pow_succ 2 L
      omega
    have h1 : dsum 1 n = n % 2 + dsum 1 (n/2) := by
      rw [dsum_step one_ne_zero n, pow_one]
    rw [h1, ih (n/2) hn2, Finset.card_filter, Finset.card_filter, Finset.sum_range_succ']
    simp only [Nat.testBit_add_one, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega

/- ## bits of pat / masks -/

lemma pat_testBit_true {p : ℕ} (hp : 1 ≤ p) : ∀ m j, j < m → (pat p m).testBit (p*j) = true := by
  intro m
  induction m with
  | zero => intro j hj; omega
  | succ m ih =>
    intro j hj
    have hb : (1:ℕ) < 2^p := Nat.one_lt_two_pow (by omega)
    have hpat : pat p (m+1) = 2^p * pat p m + 1 := by rw [pat]; ring
    rw [hpat, Nat.testBit_two_pow_mul_add _ hb]
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [if_pos (by omega : p*0 < p)]
      have h0 : p*0 = 0 := Nat.mul_zero p
      rw [h0]
      decide
    · have hple : p ≤ p*j := by
        calc p = p*1 := (Nat.mul_one p).symm
        _ ≤ p*j := Nat.mul_le_mul le_rfl hjpos
      rw [if_neg (by omega)]
      have hsub : p*j - p = p*(j-1) := by
        have h2 : p*(j-1) + p*1 = p*j := by
          rw [← Nat.mul_add]
          congr 1
          omega
        omega
      rw [hsub]
      exact ih (j-1) (by omega)

lemma maskOf_testBit {p k : ℕ} (hp : 1 ≤ p) (h2 : 2 ≤ k) (hk : k ≤ (X-1)/p) :
    (maskOf p).testBit (p*k) = true := by
  rw [maskOf, patF_eq hp, Nat.testBit_shiftLeft]
  have hge : 2*p ≤ p*k := by
    have := Nat.mul_le_mul (le_refl p) h2
    omega
  have hsub : p*k - 2*p = p*(k-2) := by
    have h1 : p*(k-2) + p*2 = p*k := by
      rw [← Nat.mul_add]
      congr 1
      omega
    omega
  rw [hsub]
  have hlt : k - 2 < mp p := by
    have hmp : mp p = (X-1)/p - 1 := rfl
    omega
  rw [pat_testBit_true hp (mp p) (k-2) hlt]
  simp [hge]

lemma maskOf_lt {p : ℕ} (hp : 1 ≤ p) (hp' : p ≤ 2927) : maskOf p < 2^(2^24) := by
  rw [maskOf, patF_eq hp, Nat.shiftLeft_eq]
  have h1 : pat p (mp p) < 2^(p * mp p) := pat_lt hp _
  have h2 : pat p (mp p) * 2^(2*p) < 2^(p * mp p) * 2^(2*p) :=
    Nat.mul_lt_mul_of_lt_of_le h1 le_rfl (by positivity)
  have h3 : (2:ℕ)^(p * mp p) * 2^(2*p) = 2^(p * mp p + 2*p) := (pow_add 2 _ _).symm
  have h4 : p * mp p + 2*p ≤ 2^24 := by
    have h24 : (2:ℕ)^24 = 16777216 := by norm_num
    have hkey : p * mp p ≤ 8567964 := by
      calc p * mp p ≤ p * ((X-1)/p) := Nat.mul_le_mul le_rfl (Nat.sub_le _ _)
      _ = (X-1)/p * p := Nat.mul_comm _ _
      _ ≤ X - 1 := Nat.div_mul_le_self _ _
      _ = 8567964 := rfl
    omega
  have h5 : (2:ℕ)^(p * mp p + 2*p) ≤ 2^(2^24) := Nat.pow_le_pow_right (by norm_num) h4
  omega

lemma foldr_testBit {i : ℕ} : ∀ (l : List ℕ), ∀ p ∈ l, (maskOf p).testBit i = true →
    (l.foldr (fun q acc => maskOf q ||| acc) 0).testBit i = true := by
  intro l
  induction l with
  | nil => simp
  | cons q t ih =>
    intro p hp h
    simp only [List.foldr_cons, Nat.testBit_or]
    rcases List.mem_cons.mp hp with rfl | hp'
    · rw [h]; simp
    · rw [ih p hp' h]; simp

lemma foldr_lt : ∀ (l : List ℕ), (∀ p ∈ l, maskOf p < 2^(2^24)) →
    (l.foldr (fun q acc => maskOf q ||| acc) 0) < 2^(2^24) := by
  intro l
  induction l with
  | nil => intro _; positivity
  | cons q t ih =>
    intro h
    simp only [List.foldr_cons]
    exact Nat.or_lt_two_pow (h q (List.mem_cons_self)) (ih (fun p hp => h p (List.mem_cons_of_mem q hp)))

lemma Plist_mem_bounds {p : ℕ} (hp : p ∈ Plist) : 2 ≤ p ∧ p < 2928 := by
  rw [Plist, List.mem_filter] at hp
  obtain ⟨h1, h2⟩ := hp
  rw [isP, Bool.and_eq_true] at h2
  exact ⟨of_decide_eq_true h2.1, List.mem_range.mp h1⟩

lemma CC_lt : CC < 2^(2^24) := by
  rw [CC]
  apply foldr_lt
  intro p hp
  obtain ⟨h1, h2⟩ := Plist_mem_bounds hp
  exact maskOf_lt (by omega) (by omega)

/- ## Plist completeness -/

lemma tdLoop_complete (n : ℕ) : ∀ (f j : ℕ), (∀ i, j ≤ i → i*i ≤ n → n % i ≠ 0) →
    tdLoop f n j = true := by
  intro f
  induction f with
  | zero => intro j _; rfl
  | succ f ih =>
    intro j h
    rw [tdLoop]
    by_cases hc : j*j > n
    · simp [hc]
    · rw [if_neg hc]
      have h1 : n % j ≠ 0 := h j le_rfl (by omega)
      have h2 : tdLoop f n (j+2) = true := ih (j+2) (fun i hi h' => h i (by omega) h')
      simp [h1, h2]

lemma mem_Plist {p : ℕ} (hp : Nat.Prime p) (h : p < 2928) : p ∈ Plist := by
  rw [Plist, List.mem_filter]
  refine ⟨List.mem_range.mpr h, ?_⟩
  rw [isP]
  have h2 : 2 ≤ p := hp.two_le
  rcases hp.eq_two_or_odd' with rfl | hodd
  · decide
  · have hmod : p % 2 = 1 := Nat.odd_iff.mp hodd
    have htd : tdLoop 30 p 3 = true := by
      apply tdLoop_complete p 30 3
      intro i hi hii hdvd
      rcases (Nat.Prime.eq_one_or_self_of_dvd hp i (Nat.dvd_of_mod_eq_zero hdvd)) with rfl | rfl
      · omega
      · nlinarith
    simp [h2, hmod, htd]

/- ## Composite numbers are marked -/

lemma composite_marked {i : ℕ} (h2 : 2 ≤ i) (hX : i < X) (hnp : ¬ i.Prime) :
    CC.testBit i = true := by
  set p := i.minFac with hpdef
  have hpp : p.Prime := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ i := Nat.minFac_dvd i
  have hsq : p^2 ≤ i := Nat.minFac_sq_le_self (by omega) hnp
  have hXval : X = 8567965 := rfl
  have hplt : p < 2928 := by
    by_contra hcon
    push_neg at hcon
    have : 2928*2928 ≤ p*p := Nat.mul_le_mul hcon hcon
    have hpp2 : p^2 = p*p := sq p
    omega
  set k := i / p with hkdef
  have hik : i = p * k := (Nat.mul_div_cancel' hpdvd).symm
  have hppos : 1 ≤ p := hpp.one_le
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k
      · omega
      · rw [Nat.mul_one] at hik
        exact absurd (hik ▸ hpp) hnp
    · exact hk
  have hkle : k ≤ (X-1)/p := by
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    have : k * p = p * k := Nat.mul_comm _ _
    omega
  rw [CC]
  apply foldr_testBit Plist p (mem_Plist hpp hplt)
  rw [hik]
  exact maskOf_testBit hppos hk2 hkle

/- ## Counting -/

lemma dsum1_CC_eq : dsum 1 CC = iterRounds 24 CC := by
  obtain ⟨h1, h2⟩ := iter_correct CC_lt 24 le_rfl
  rw [← h1, dsum_of_lt (Nat.two_pow_pos 24).ne' h2]

lemma iter_val : iterRounds 24 CC = 7992566 := by decide +kernel

lemma count_bound : 550171 < Nat.count Nat.Prime 8567965 := by
  have hd : dsum 1 CC = 7992566 := by rw [dsum1_CC_eq, iter_val]
  have hXpow : X < 2^24 := by norm_num [X]
  set F : Finset ℕ := (Finset.range X).filter (fun i => CC.testBit i) with hF
  set T : Finset ℕ := (Finset.range X).filter (fun i => 2 ≤ i ∧ CC.testBit i = false) with hT
  have hFcard : F.card ≤ 7992566 := by
    have hsub : F ⊆ (Finset.range (2^24)).filter (fun i => CC.testBit i) :=
      Finset.filter_subset_filter _ (Finset.range_subset_range.mpr hXpow.le)
    calc F.card ≤ ((Finset.range (2^24)).filter (fun i => CC.testBit i)).card :=
          Finset.card_le_card hsub
    _ = dsum 1 CC := (dsum1_card (2^24) CC CC_lt).symm
    _ = 7992566 := hd
  have hTsub : T ⊆ (Finset.range X).filter Nat.Prime := by
    intro i hi
    rw [hT, Finset.mem_filter] at hi
    obtain ⟨hir, hi2, hib⟩ := hi
    rw [Finset.mem_filter]
    refine ⟨hir, ?_⟩
    by_contra hnp
    have hmark := composite_marked hi2 (Finset.mem_range.mp hir) hnp
    rw [hmark] at hib
    exact absurd hib (by simp)
  have hTeq : T = (Finset.Ico 2 X) \ F := by
    ext i
    rw [hT, hF, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ico,
      Finset.mem_range]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h2, h1⟩, fun hc => by rw [h3] at hc; simp at hc⟩
    · rintro ⟨⟨h2, h1⟩, h3⟩
      refine ⟨h1, h2, ?_⟩
      cases hb : CC.testBit i
      · rfl
      · exact absurd ⟨h1, hb⟩ h3
  have hsd := Finset.le_card_sdiff F (Finset.Ico 2 X)
  have hIco : (Finset.Ico 2 X).card = X - 2 := Nat.card_Ico 2 X
  have hTcard : 575397 ≤ T.card := by
    rw [hTeq]
    have hXv : X = 8567965 := rfl
    omega
  rw [Nat.count_eq_card_filter_range]
  have h55 : (550171:ℕ) < 575397 := by norm_num
  refine lt_of_lt_of_le h55 (le_trans hTcard (Finset.card_le_card ?_))
  intro i hi
  have hm := hTsub hi
  rw [Finset.mem_filter] at hm
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (Finset.mem_range.mp hm.1), hm.2⟩

end Sieve

instance : NeZero (550172 : ℕ) := ⟨by norm_num⟩


lemma cast_val_bridge (k : ℕ) (x : ZMod 550172) :
    ((2^k - k : ℕ) : ZMod 550172) = x ↔ 2^k ≡ x.val + k [MOD 550172] := by
  have h2k : k ≤ 2^k := (Nat.lt_two_pow_self).le
  constructor
  · intro h
    have hval : ((2^k - k : ℕ) : ZMod 550172) = ((x.val : ℕ) : ZMod 550172) := by
      rw [h, ZMod.natCast_val, ZMod.cast_id]
    have h1 := (ZMod.natCast_eq_natCast_iff _ _ _).mp hval
    have h2 := h1.add_right k
    rwa [Nat.sub_add_cancel h2k] at h2
  · intro h
    have h1 : (2^k - k) + k ≡ x.val + k [MOD 550172] := by rwa [Nat.sub_add_cancel h2k]
    have h2 := Nat.ModEq.add_right_cancel' k h1
    have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
    rwa [ZMod.natCast_val, ZMod.cast_id] at h3

lemma prop_iff (m : ℕ) : A232616_prop 550172 m ↔
    ∀ x : ZMod 550172, ∃ k, 1 ≤ k ∧ k ≤ m ∧ 2^k ≡ x.val + k [MOD 550172] := by
  constructor
  · intro h x
    have hx : x ∈ (Finset.Icc 1 m).image fun k ↦ (Nat.cast (2 ^ k - k) : ZMod 550172) := by
      rw [← h]; exact Finset.mem_univ x
    obtain ⟨k, hk, hfk⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_Icc] at hk
    exact ⟨k, hk.1, hk.2, (cast_val_bridge k x).mp hfk⟩
  · intro h
    refine (Finset.eq_univ_iff_forall.mpr ?_).symm
    intro x
    obtain ⟨k, hk1, hkm, hcong⟩ := h x
    exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk1, hkm⟩, (cast_val_bridge k x).mpr hcong⟩

lemma mem_S : A232616_prop 550172 82526801 := by
  rw [prop_iff]
  intro x
  exact cover x.val x.val_lt

lemma S_lb : ∀ m, A232616_prop 550172 m → 17135927 ≤ m := by
  intro m hm
  obtain ⟨k, hk1, hkm, hcong⟩ := (prop_iff m).mp hm (63945 : ZMod 550172)
  have hval : (63945 : ZMod 550172).val = 63945 := by
    rw [ZMod.val_ofNat]
  rw [hval] at hcong
  by_contra hlt
  exact avoid hk1 (by omega) hcong

lemma A232616_eq : A232616 550172 = sInf {m | A232616_prop 550172 m} := by
  rw [A232616, dif_neg (by norm_num : (550172:ℕ) ≠ 0)]

theorem A232616_lb : 17135927 ≤ A232616 550172 := by
  rw [A232616_eq]
  have hne : {m | A232616_prop 550172 m}.Nonempty := ⟨82526801, mem_S⟩
  exact S_lb _ (Nat.sInf_mem hne)

theorem final : ¬ (∀ (n : ℕ), 0 < n → A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1)) := by
  intro h
  have h1 := h 550172 (by norm_num)
  have h2 : Nat.nth Nat.Prime 550171 < 8567965 := Nat.nth_lt_of_lt_count Sieve.count_bound
  have h3 : (550172 - 1 : ℕ) = 550171 := by norm_num
  rw [h3] at h1
  have h4 := A232616_lb
  omega

end A232616D

theorem oeis_232616_conjecture_i.disproof :
    ¬ ∀ (n : ℕ) (hn : 0 < n), A232616 n < 2 * (Nat.nth Nat.Prime (n - 1) - 1) :=
  A232616D.final
