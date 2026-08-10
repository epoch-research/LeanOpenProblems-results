import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Finset ZMod Nat Set Classical

def scan (k p fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel+1 =>
    let p' := (p * 2) % 550172
    let r := (p' + 550172 - (k % 550172)) % 550172
    (r != 13573) && scan (k+1) p' fuel

def advance (p fuel : Nat) : Nat :=
  match fuel with
  | 0 => p
  | fuel+1 => advance ((p * 2) % 550172) fuel

lemma two_pow_ge (k : Nat) : k ≤ 2^k := le_of_lt k.lt_two_pow_self

lemma step_modEq (k p : Nat) (hp : p ≡ 2^(k-1) [MOD 550172]) (hk0 : 1 ≤ k) :
    (p * 2) % 550172 ≡ 2^k [MOD 550172] := by
  have hk' : k = (k - 1) + 1 := by omega
  have hmul : p * 2 ≡ 2^(k-1) * 2 [MOD 550172] := hp.mul_right 2
  rw [hk', pow_succ]
  exact (Nat.mod_modEq _ _).trans hmul

lemma advance_sound (k p fuel : Nat) (hk0 : 1 ≤ k) (hp : p ≡ 2^(k-1) [MOD 550172]) :
    advance p fuel ≡ 2^(k + fuel - 1) [MOD 550172] := by
  induction fuel generalizing k p with
  | zero => simpa using hp
  | succ fuel ih =>
    simp [advance]
    have hp' := step_modEq k p hp hk0
    have hih := ih (k+1) ((p*2)%550172) (by omega) (by
      have hk1 : (k + 1) - 1 = k := by omega
      rwa [hk1])
    have harg : (k + 1) + fuel - 1 = k + fuel := by omega
    simpa [harg] using hih

lemma residue_modEq (k p : Nat) (hp : p ≡ 2^(k-1) [MOD 550172]) (hk : 1 ≤ k) :
    ((p * 2) % 550172 + 550172 - (k % 550172)) % 550172 = (2^k - k) % 550172 := by
  have hp2 := step_modEq k p hp hk
  let q := (p * 2) % 550172
  have hq : q ≡ 2^k [MOD 550172] := by simpa [q] using hp2
  have hqN : q + 550172 ≡ 2^k [MOD 550172] := by
    have h0 : q + 550172 ≡ q [MOD 550172] := by simp [Nat.ModEq]
    exact h0.trans hq
  have hkmod : k % 550172 ≡ k [MOD 550172] := Nat.mod_modEq k 550172
  have hsub : q + 550172 - k % 550172 ≡ 2^k - k [MOD 550172] := by
    apply Nat.ModEq.sub
    · have hkm : k % 550172 ≤ 550172 := (Nat.mod_lt _ (by norm_num : 0 < 550172)).le
      omega
    · exact two_pow_ge k
    · exact hqN
    · exact hkmod
  apply Nat.ModEq.eq_of_lt_of_lt
  · exact (Nat.mod_modEq _ _).trans (hsub.trans (Nat.mod_modEq _ _).symm)
  · exact Nat.mod_lt _ (by norm_num)
  · exact Nat.mod_lt _ (by norm_num)

lemma cast_ne_of_residue_ne (k p : Nat) (hp : p ≡ 2^(k-1) [MOD 550172]) (hk : 1 ≤ k)
    (hne : ((p * 2) % 550172 + 550172 - (k % 550172)) % 550172 ≠ 13573) :
    (Nat.cast (2^k - k) : ZMod 550172) ≠ (13573 : ZMod 550172) := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast] at hv
  have h135 : ZMod.val (13573 : ZMod 550172) = 13573 := ZMod.val_natCast_of_lt (by norm_num)
  rw [h135] at hv
  have heq := residue_modEq k p hp hk
  omega

lemma scan_sound (k p fuel : Nat) (hk0 : 1 ≤ k) (hp : p ≡ 2^(k-1) [MOD 550172]) (hscan : scan k p fuel = true) :
    ∀ j, k ≤ j → j < k + fuel →
      (Nat.cast (2^j - j) : ZMod 550172) ≠ (13573 : ZMod 550172) := by
  induction fuel generalizing k p with
  | zero => intro j hj hj2; omega
  | succ fuel ih =>
    intro j hj hj2
    simp only [scan] at hscan
    let p' := (p * 2) % 550172
    let r := (p' + 550172 - (k % 550172)) % 550172
    have hboth : (r != 13573) = true ∧ scan (k+1) p' fuel = true := by simpa [p', r] using hscan
    have hrne : r ≠ 13573 := bne_iff_ne.mp hboth.1
    by_cases hkj : j = k
    · subst j
      exact cast_ne_of_residue_ne k p hp hk0 (by simpa [p', r] using hrne)
    · have hjnext : k + 1 ≤ j := by omega
      have hp' : p' ≡ 2^((k+1)-1) [MOD 550172] := by
        have hk1 : (k + 1) - 1 = k := by omega
        rw [hk1]
        exact step_modEq k p hp hk0
      exact ih (k+1) p' (by omega) hp' hboth.2 j hjnext (by omega)
lemma scan_chunk_0 : scan 1 1 10000 = true := by decide
lemma adv_chunk_0 : advance 1 10000 = 419848 := by decide
lemma scan_chunk_1 : scan 10001 419848 10000 = true := by decide
lemma adv_chunk_1 : advance 419848 10000 = 535336 := by decide
lemma scan_chunk_2 : scan 20001 535336 5000 = true := by decide
lemma adv_chunk_2 : advance 535336 5000 = 464760 := by decide
lemma hp0 : (1 : Nat) ≡ 2^(1-1) [MOD 550172] := by norm_num [Nat.ModEq]
lemma hp1 : 419848 ≡ 2^(10001-1) [MOD 550172] := by
  have h := advance_sound 1 1 10000 (by norm_num) hp0
  rw [adv_chunk_0] at h
  simpa using h
lemma hp2 : 535336 ≡ 2^(20001-1) [MOD 550172] := by
  have h := advance_sound 10001 419848 10000 (by norm_num) hp1
  rw [adv_chunk_1] at h
  simpa using h
theorem missing_all_proto (j : Nat) (hj1 : 1 ≤ j) (hjB : j < 25001) :
    (Nat.cast (2^j - j) : ZMod 550172) ≠ (13573 : ZMod 550172) := by
  let d := (j - 1) / 10000
  have hd : d = (j - 1) / 10000 := rfl
  have hdle : d ≤ 2 := by
    rw [hd]
    omega
  interval_cases d
  · exact scan_sound 1 1 10000 (by norm_num) hp0 scan_chunk_0 j (by omega) (by omega)
  · exact scan_sound 10001 419848 10000 (by norm_num) hp1 scan_chunk_1 j (by omega) (by omega)
  · exact scan_sound 20001 535336 5000 (by norm_num) hp2 scan_chunk_2 j (by omega) (by omega)
