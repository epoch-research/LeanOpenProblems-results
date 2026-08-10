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
      exact ih (k+1) p' (by omega) hp' hboth.2 j hjnext (by omega)opaque scan_chunk_0 : scan 1 1 2000 = true := by decide
opaque adv_chunk_0 : advance 1 2000 = 254636 := by decide
opaque scan_chunk_1 : scan 2001 254636 2000 = true := by decide
opaque adv_chunk_1 : advance 254636 2000 = 71780 := by decide
opaque scan_chunk_2 : scan 4001 71780 2000 = true := by decide
opaque adv_chunk_2 : advance 71780 2000 = 508068 := by decide
opaque scan_chunk_3 : scan 6001 508068 2000 = true := by decide
opaque adv_chunk_3 : advance 508068 2000 = 7620 := by decide
opaque scan_chunk_4 : scan 8001 7620 2000 = true := by decide
opaque adv_chunk_4 : advance 7620 2000 = 419848 := by decide
opaque scan_chunk_5 : scan 10001 419848 2000 = true := by decide
opaque adv_chunk_5 : advance 419848 2000 = 92632 := by decide
opaque scan_chunk_6 : scan 12001 92632 2000 = true := by decide
opaque adv_chunk_6 : advance 92632 2000 = 467968 := by decide
opaque scan_chunk_7 : scan 14001 467968 2000 = true := by decide
opaque adv_chunk_7 : advance 467968 2000 = 296340 := by decide
opaque scan_chunk_8 : scan 16001 296340 2000 = true := by decide
opaque adv_chunk_8 : advance 296340 2000 = 541752 := by decide
opaque scan_chunk_9 : scan 18001 541752 2000 = true := by decide
opaque adv_chunk_9 : advance 541752 2000 = 535336 := by decide
opaque scan_chunk_10 : scan 20001 535336 2000 = true := by decide
opaque adv_chunk_10 : advance 535336 2000 = 251428 := by decide
opaque scan_chunk_11 : scan 22001 251428 2000 = true := by decide
opaque adv_chunk_11 : advance 251428 2000 = 204912 := by decide
opaque scan_chunk_12 : scan 24001 204912 2000 = true := by decide
opaque adv_chunk_12 : advance 204912 2000 = 209724 := by decide
opaque scan_chunk_13 : scan 26001 209724 2000 = true := by decide
opaque adv_chunk_13 : advance 209724 2000 = 285112 := by decide
opaque scan_chunk_14 : scan 28001 285112 2000 = true := by decide
opaque adv_chunk_14 : advance 285112 2000 = 182456 := by decide
opaque scan_chunk_15 : scan 30001 182456 2000 = true := by decide
opaque adv_chunk_15 : advance 182456 2000 = 41304 := by decide
opaque scan_chunk_16 : scan 32001 41304 2000 = true := by decide
opaque adv_chunk_16 : advance 41304 2000 = 397392 := by decide
opaque scan_chunk_17 : scan 34001 397392 2000 = true := by decide
opaque adv_chunk_17 : advance 397392 2000 = 474384 := by decide
opaque scan_chunk_18 : scan 36001 474384 2000 = true := by decide
opaque adv_chunk_18 : advance 474384 2000 = 30076 := by decide
opaque scan_chunk_19 : scan 38001 30076 2000 = true := by decide
opaque adv_chunk_19 : advance 30076 2000 = 38096 := by decide
opaque scan_chunk_20 : scan 40001 38096 2000 = true := by decide
opaque adv_chunk_20 : advance 38096 2000 = 530524 := by decide
opaque scan_chunk_21 : scan 42001 530524 2000 = true := by decide
opaque adv_chunk_21 : advance 530524 2000 = 176040 := by decide
opaque scan_chunk_22 : scan 44001 176040 2000 = true := by decide
opaque adv_chunk_22 : advance 176040 2000 = 307568 := by decide
opaque scan_chunk_23 : scan 46001 307568 2000 = true := by decide
opaque adv_chunk_23 : advance 307568 2000 = 350876 := by decide
opaque scan_chunk_24 : scan 48001 350876 2000 = true := by decide
opaque adv_chunk_24 : advance 350876 2000 = 479196 := by decide
opaque scan_chunk_25 : scan 50001 479196 2000 = true := by decide
opaque adv_chunk_25 : advance 479196 2000 = 105464 := by decide
opaque scan_chunk_26 : scan 52001 105464 2000 = true := by decide
opaque adv_chunk_26 : advance 105464 2000 = 485612 := by decide
opaque scan_chunk_27 : scan 54001 485612 2000 = true := by decide
opaque adv_chunk_27 : advance 485612 2000 = 389372 := by decide
opaque scan_chunk_28 : scan 56001 389372 2000 = true := by decide
opaque adv_chunk_28 : advance 389372 2000 = 532128 := by decide
opaque scan_chunk_29 : scan 58001 532128 2000 = true := by decide
opaque adv_chunk_29 : advance 532128 2000 = 384560 := by decide
opaque scan_chunk_30 : scan 60001 384560 2000 = true := by decide
opaque adv_chunk_30 : advance 384560 2000 = 456740 := by decide
opaque scan_chunk_31 : scan 62001 456740 2000 = true := by decide
opaque adv_chunk_31 : advance 456740 2000 = 487216 := by decide
opaque scan_chunk_32 : scan 64001 487216 2000 = true := by decide
opaque adv_chunk_32 : advance 487216 2000 = 47720 := by decide
opaque scan_chunk_33 : scan 66001 47720 2000 = true := by decide
opaque adv_chunk_33 : advance 47720 2000 = 131128 := by decide
opaque scan_chunk_34 : scan 68001 131128 2000 = true := by decide
opaque adv_chunk_34 : advance 131128 2000 = 520900 := by decide
opaque scan_chunk_35 : scan 70001 520900 2000 = true := by decide
opaque adv_chunk_35 : advance 520900 2000 = 25264 := by decide
opaque scan_chunk_36 : scan 72001 25264 2000 = true := by decide
opaque adv_chunk_36 : advance 25264 2000 = 512880 := by decide
opaque scan_chunk_37 : scan 74001 512880 2000 = true := by decide
opaque adv_chunk_37 : advance 512880 2000 = 83008 := by decide
opaque scan_chunk_38 : scan 76001 83008 2000 = true := by decide
opaque adv_chunk_38 : advance 83008 2000 = 317192 := by decide
opaque scan_chunk_39 : scan 78001 317192 2000 = true := by decide
opaque adv_chunk_39 : advance 317192 2000 = 501652 := by decide
opaque scan_chunk_40 : scan 80001 501652 2000 = true := by decide
opaque adv_chunk_40 : advance 501652 2000 = 273884 := by decide
opaque scan_chunk_41 : scan 82001 273884 2000 = true := by decide
opaque adv_chunk_41 : advance 273884 2000 = 373332 := by decide
opaque scan_chunk_42 : scan 84001 373332 2000 = true := by decide
opaque adv_chunk_42 : advance 373332 2000 = 97444 := by decide
opaque scan_chunk_43 : scan 86001 97444 2000 = true := by decide
opaque adv_chunk_43 : advance 97444 2000 = 543356 := by decide
opaque scan_chunk_44 : scan 88001 543356 2000 = true := by decide
opaque adv_chunk_44 : advance 543356 2000 = 193684 := by decide
opaque scan_chunk_45 : scan 90001 193684 2000 = true := by decide
opaque adv_chunk_45 : advance 193684 2000 = 400600 := by decide
opaque scan_chunk_46 : scan 92001 400600 2000 = true := by decide
opaque adv_chunk_46 : advance 400600 2000 = 341252 := by decide
opaque scan_chunk_47 : scan 94001 341252 2000 = true := by decide
opaque adv_chunk_47 : advance 341252 2000 = 328420 := by decide
opaque scan_chunk_48 : scan 96001 328420 2000 = true := by decide
opaque adv_chunk_48 : advance 328420 2000 = 310776 := by decide
opaque scan_chunk_49 : scan 98001 310776 2000 = true := by decide
opaque adv_chunk_49 : advance 310776 2000 = 217744 := by decide
opaque scan_chunk_50 : scan 100001 217744 2000 = true := by decide
opaque adv_chunk_50 : advance 217744 2000 = 227368 := by decide
opaque scan_chunk_51 : scan 102001 227368 2000 = true := by decide
opaque adv_chunk_51 : advance 227368 2000 = 378144 := by decide
opaque scan_chunk_52 : scan 104001 378144 2000 = true := by decide
opaque adv_chunk_52 : advance 378144 2000 = 172832 := by decide
opaque scan_chunk_53 : scan 106001 172832 2000 = true := by decide
opaque adv_chunk_53 : advance 172832 2000 = 440700 := by decide
opaque scan_chunk_54 : scan 108001 440700 2000 = true := by decide
opaque adv_chunk_54 : advance 440700 2000 = 52532 := by decide
opaque scan_chunk_55 : scan 110001 52532 2000 = true := by decide
opaque adv_chunk_55 : advance 52532 2000 = 206516 := by decide
opaque scan_chunk_56 : scan 112001 206516 2000 = true := by decide
opaque adv_chunk_56 : advance 206516 2000 = 418244 := by decide
opaque scan_chunk_57 : scan 114001 418244 2000 = true := by decide
opaque adv_chunk_57 : advance 418244 2000 = 434284 := by decide
opaque scan_chunk_58 : scan 116001 434284 2000 = true := by decide
opaque adv_chunk_58 : advance 434284 2000 = 318796 := by decide
opaque scan_chunk_59 : scan 118001 318796 2000 = true := by decide
opaque adv_chunk_59 : advance 318796 2000 = 160000 := by decide
opaque scan_chunk_60 : scan 120001 160000 2000 = true := by decide
opaque adv_chunk_60 : advance 160000 2000 = 423056 := by decide
opaque scan_chunk_61 : scan 122001 423056 2000 = true := by decide
opaque adv_chunk_61 : advance 423056 2000 = 509672 := by decide
opaque scan_chunk_62 : scan 124001 509672 2000 = true := by decide
opaque adv_chunk_62 : advance 509672 2000 = 216140 := by decide
opaque scan_chunk_63 : scan 126001 216140 2000 = true := by decide
opaque adv_chunk_63 : advance 216140 2000 = 18848 := by decide
opaque scan_chunk_64 : scan 128001 18848 2000 = true := by decide
opaque adv_chunk_64 : advance 18848 2000 = 228972 := by decide
opaque scan_chunk_65 : scan 130001 228972 2000 = true := by decide
opaque adv_chunk_65 : advance 228972 2000 = 36492 := by decide
opaque scan_chunk_66 : scan 132001 36492 2000 = true := by decide
opaque adv_chunk_66 : advance 36492 2000 = 322004 := by decide
opaque scan_chunk_67 : scan 134001 322004 2000 = true := by decide
opaque adv_chunk_67 : advance 322004 2000 = 26868 := by decide
opaque scan_chunk_68 : scan 136001 26868 2000 = true := by decide
opaque adv_chunk_68 : advance 26868 2000 = 171228 := by decide
opaque scan_chunk_69 : scan 138001 171228 2000 = true := by decide
opaque adv_chunk_69 : advance 171228 2000 = 232180 := by decide
opaque scan_chunk_70 : scan 140001 232180 2000 = true := by decide
opaque adv_chunk_70 : advance 232180 2000 = 453532 := by decide
opaque scan_chunk_71 : scan 142001 453532 2000 = true := by decide
opaque adv_chunk_71 : advance 453532 2000 = 70176 := by decide
opaque scan_chunk_72 : scan 144001 70176 2000 = true := by decide
opaque adv_chunk_72 : advance 70176 2000 = 299548 := by decide
opaque scan_chunk_73 : scan 146001 299548 2000 = true := by decide
opaque adv_chunk_73 : advance 299548 2000 = 408620 := by decide
opaque scan_chunk_74 : scan 148001 408620 2000 = true := by decide
opaque adv_chunk_74 : advance 408620 2000 = 283508 := by decide
opaque scan_chunk_75 : scan 150001 283508 2000 = true := by decide
opaque adv_chunk_75 : advance 283508 2000 = 524108 := by decide
opaque scan_chunk_76 : scan 152001 524108 2000 = true := by decide
opaque adv_chunk_76 : advance 524108 2000 = 442304 := by decide
opaque scan_chunk_77 : scan 154001 442304 2000 = true := by decide
opaque adv_chunk_77 : advance 442304 2000 = 261052 := by decide
opaque scan_chunk_78 : scan 156001 261052 2000 = true := by decide
opaque adv_chunk_78 : advance 261052 2000 = 355688 := by decide
opaque scan_chunk_79 : scan 158001 355688 2000 = true := by decide
opaque adv_chunk_79 : advance 355688 2000 = 4412 := by decide
opaque scan_chunk_80 : scan 160001 4412 2000 = true := by decide
opaque adv_chunk_80 : advance 4412 2000 = 2808 := by decide
opaque scan_chunk_81 : scan 162001 2808 2000 = true := by decide
opaque adv_chunk_81 : advance 2808 2000 = 344460 := by decide
opaque scan_chunk_82 : scan 164001 344460 2000 = true := by decide
opaque adv_chunk_82 : advance 344460 2000 = 195288 := by decide
opaque scan_chunk_83 : scan 166001 195288 2000 = true := by decide
opaque adv_chunk_83 : advance 195288 2000 = 58948 := by decide
opaque scan_chunk_84 : scan 168001 58948 2000 = true := by decide
opaque adv_chunk_84 : advance 58948 2000 = 490424 := by decide
opaque scan_chunk_85 : scan 170001 490424 2000 = true := by decide
opaque adv_chunk_85 : advance 490424 2000 = 464760 := by decide
opaque scan_chunk_86 : scan 172001 464760 2000 = true := by decide
opaque adv_chunk_86 : advance 464760 2000 = 429472 := by decide
opaque scan_chunk_87 : scan 174001 429472 2000 = true := by decide
opaque adv_chunk_87 : advance 429472 2000 = 243408 := by decide
opaque scan_chunk_88 : scan 176001 243408 2000 = true := by decide
opaque adv_chunk_88 : advance 243408 2000 = 262656 := by decide
opaque scan_chunk_89 : scan 178001 262656 2000 = true := by decide
opaque adv_chunk_89 : advance 262656 2000 = 14036 := by decide
opaque scan_chunk_90 : scan 180001 14036 2000 = true := by decide
opaque adv_chunk_90 : advance 14036 2000 = 153584 := by decide
opaque scan_chunk_91 : scan 182001 153584 2000 = true := by decide
opaque adv_chunk_91 : advance 153584 2000 = 139148 := by decide
opaque scan_chunk_92 : scan 184001 139148 2000 = true := by decide
opaque adv_chunk_92 : advance 139148 2000 = 463156 := by decide
opaque scan_chunk_93 : scan 186001 463156 2000 = true := by decide
opaque adv_chunk_93 : advance 463156 2000 = 220952 := by decide
opaque scan_chunk_94 : scan 188001 220952 2000 = true := by decide
opaque adv_chunk_94 : advance 220952 2000 = 94236 := by decide
opaque scan_chunk_95 : scan 190001 94236 2000 = true := by decide
opaque adv_chunk_95 : advance 94236 2000 = 126316 := by decide
opaque scan_chunk_96 : scan 192001 126316 2000 = true := by decide
opaque adv_chunk_96 : advance 126316 2000 = 445512 := by decide
opaque scan_chunk_97 : scan 194001 445512 2000 = true := by decide
opaque adv_chunk_97 : advance 445512 2000 = 127920 := by decide
opaque scan_chunk_98 : scan 196001 127920 2000 = true := by decide
opaque adv_chunk_98 : advance 127920 2000 = 103860 := by decide
opaque scan_chunk_99 : scan 198001 103860 2000 = true := by decide
opaque adv_chunk_99 : advance 103860 2000 = 277092 := by decide
opaque scan_chunk_100 : scan 200001 277092 2000 = true := by decide
opaque adv_chunk_100 : advance 277092 2000 = 240200 := by decide
opaque scan_chunk_101 : scan 202001 240200 2000 = true := by decide
opaque adv_chunk_101 : advance 240200 2000 = 395788 := by decide
opaque scan_chunk_102 : scan 204001 395788 2000 = true := by decide
opaque adv_chunk_102 : advance 395788 2000 = 265864 := by decide
opaque scan_chunk_103 : scan 206001 265864 2000 = true := by decide
opaque adv_chunk_103 : advance 265864 2000 = 431076 := by decide
opaque scan_chunk_104 : scan 208001 431076 2000 = true := by decide
opaque adv_chunk_104 : advance 431076 2000 = 451928 := by decide
opaque scan_chunk_105 : scan 210001 451928 2000 = true := by decide
opaque adv_chunk_105 : advance 451928 2000 = 411828 := by decide
opaque scan_chunk_106 : scan 212001 411828 2000 = true := by decide
opaque adv_chunk_106 : advance 411828 2000 = 150376 := by decide
opaque scan_chunk_107 : scan 214001 150376 2000 = true := by decide
opaque adv_chunk_107 : advance 150376 2000 = 272280 := by decide
opaque scan_chunk_108 : scan 216001 272280 2000 = true := by decide
opaque adv_chunk_108 : advance 272280 2000 = 164812 := by decide
opaque scan_chunk_109 : scan 218001 164812 2000 = true := by decide
opaque adv_chunk_109 : advance 164812 2000 = 498444 := by decide
opaque scan_chunk_110 : scan 220001 498444 2000 = true := by decide
opaque adv_chunk_110 : advance 498444 2000 = 407016 := by decide
opaque scan_chunk_111 : scan 222001 407016 2000 = true := by decide
opaque adv_chunk_111 : advance 407016 2000 = 74988 := by decide
opaque scan_chunk_112 : scan 224001 74988 2000 = true := by decide
opaque adv_chunk_112 : advance 74988 2000 = 374936 := by decide
opaque scan_chunk_113 : scan 226001 374936 2000 = true := by decide
opaque adv_chunk_113 : advance 374936 2000 = 305964 := by decide
opaque scan_chunk_114 : scan 228001 305964 2000 = true := by decide
opaque adv_chunk_114 : advance 305964 2000 = 142356 := by decide
opaque scan_chunk_115 : scan 230001 142356 2000 = true := by decide
opaque adv_chunk_115 : advance 142356 2000 = 330024 := by decide
opaque scan_chunk_116 : scan 232001 330024 2000 = true := by decide
opaque adv_chunk_116 : advance 330024 2000 = 519296 := by decide
opaque scan_chunk_117 : scan 234001 519296 2000 = true := by decide
opaque adv_chunk_117 : advance 519296 2000 = 366916 := by decide
opaque scan_chunk_118 : scan 236001 366916 2000 = true := by decide
opaque adv_chunk_118 : advance 366916 2000 = 363708 := by decide
opaque scan_chunk_119 : scan 238001 363708 2000 = true := by decide
opaque adv_chunk_119 : advance 363708 2000 = 496840 := by decide
opaque scan_chunk_120 : scan 240001 496840 2000 = true := by decide
opaque adv_chunk_120 : advance 496840 2000 = 198496 := by decide
opaque scan_chunk_121 : scan 242001 198496 2000 = true := by decide
opaque adv_chunk_121 : advance 198496 2000 = 475988 := by decide
opaque scan_chunk_122 : scan 244001 475988 2000 = true := by decide
opaque adv_chunk_122 : advance 475988 2000 = 238596 := by decide
opaque scan_chunk_123 : scan 246001 238596 2000 = true := by decide
opaque adv_chunk_123 : advance 238596 2000 = 187268 := by decide
opaque scan_chunk_124 : scan 248001 187268 2000 = true := by decide
opaque adv_chunk_124 : advance 187268 2000 = 116692 := by decide
opaque scan_chunk_125 : scan 250001 116692 2000 = true := by decide
opaque adv_chunk_125 : advance 116692 2000 = 294736 := by decide
opaque scan_chunk_126 : scan 252001 294736 2000 = true := by decide
opaque adv_chunk_126 : advance 294736 2000 = 333232 := by decide
opaque scan_chunk_127 : scan 254001 333232 2000 = true := by decide
opaque adv_chunk_127 : advance 333232 2000 = 386164 := by decide
opaque scan_chunk_128 : scan 256001 386164 2000 = true := by decide
opaque adv_chunk_128 : advance 386164 2000 = 115088 := by decide
opaque scan_chunk_129 : scan 258001 115088 2000 = true := by decide
opaque adv_chunk_129 : advance 115088 2000 = 86216 := by decide
opaque scan_chunk_130 : scan 260001 86216 2000 = true := by decide
opaque adv_chunk_130 : advance 86216 2000 = 184060 := by decide
opaque scan_chunk_131 : scan 262001 184060 2000 = true := by decide
opaque adv_chunk_131 : advance 184060 2000 = 249824 := by decide
opaque scan_chunk_132 : scan 264001 249824 2000 = true := by decide
opaque adv_chunk_132 : advance 249824 2000 = 546564 := by decide
opaque scan_chunk_133 : scan 266001 546564 2000 = true := by decide
opaque adv_chunk_133 : advance 546564 2000 = 60552 := by decide
opaque scan_chunk_134 : scan 268001 60552 2000 = true := by decide
opaque adv_chunk_134 : advance 60552 2000 = 148772 := by decide
opaque scan_chunk_135 : scan 270001 148772 2000 = true := by decide
opaque adv_chunk_135 : advance 148772 2000 = 63760 := by decide
opaque scan_chunk_136 : scan 272001 63760 2000 = true := by decide
opaque adv_chunk_136 : advance 63760 2000 = 15640 := by decide
opaque scan_chunk_137 : scan 274001 15640 2000 = true := by decide
opaque adv_chunk_137 : advance 15640 2000 = 362104 := by decide
opaque scan_chunk_138 : scan 276001 362104 2000 = true := by decide
opaque adv_chunk_138 : advance 362104 2000 = 288320 := by decide
opaque scan_chunk_139 : scan 278001 288320 2000 = true := by decide
opaque adv_chunk_139 : advance 288320 2000 = 49324 := by decide
opaque scan_chunk_140 : scan 280001 49324 2000 = true := by decide
opaque adv_chunk_140 : advance 49324 2000 = 339648 := by decide
opaque scan_chunk_141 : scan 282001 339648 2000 = true := by decide
opaque adv_chunk_141 : advance 339648 2000 = 119900 := by decide
opaque scan_chunk_142 : scan 284001 119900 2000 = true := by decide
opaque adv_chunk_142 : advance 119900 2000 = 161604 := by decide
opaque scan_chunk_143 : scan 286001 161604 2000 = true := by decide
opaque adv_chunk_143 : advance 161604 2000 = 81404 := by decide
opaque scan_chunk_144 : scan 288001 81404 2000 = true := by decide
opaque adv_chunk_144 : advance 81404 2000 = 108672 := by decide
opaque scan_chunk_145 : scan 290001 108672 2000 = true := by decide
opaque adv_chunk_145 : advance 108672 2000 = 352480 := by decide
opaque scan_chunk_146 : scan 292001 352480 2000 = true := by decide
opaque adv_chunk_146 : advance 352480 2000 = 137544 := by decide
opaque scan_chunk_147 : scan 294001 137544 2000 = true := by decide
opaque adv_chunk_147 : advance 137544 2000 = 254636 := by decide
opaque scan_chunk_148 : scan 296001 254636 2000 = true := by decide
opaque adv_chunk_148 : advance 254636 2000 = 71780 := by decide
opaque scan_chunk_149 : scan 298001 71780 2000 = true := by decide
opaque adv_chunk_149 : advance 71780 2000 = 508068 := by decide
opaque scan_chunk_150 : scan 300001 508068 2000 = true := by decide
opaque adv_chunk_150 : advance 508068 2000 = 7620 := by decide
opaque scan_chunk_151 : scan 302001 7620 2000 = true := by decide
opaque adv_chunk_151 : advance 7620 2000 = 419848 := by decide
opaque scan_chunk_152 : scan 304001 419848 2000 = true := by decide
opaque adv_chunk_152 : advance 419848 2000 = 92632 := by decide
opaque scan_chunk_153 : scan 306001 92632 2000 = true := by decide
opaque adv_chunk_153 : advance 92632 2000 = 467968 := by decide
opaque scan_chunk_154 : scan 308001 467968 2000 = true := by decide
opaque adv_chunk_154 : advance 467968 2000 = 296340 := by decide
opaque scan_chunk_155 : scan 310001 296340 2000 = true := by decide
opaque adv_chunk_155 : advance 296340 2000 = 541752 := by decide
opaque scan_chunk_156 : scan 312001 541752 2000 = true := by decide
opaque adv_chunk_156 : advance 541752 2000 = 535336 := by decide
opaque scan_chunk_157 : scan 314001 535336 2000 = true := by decide
opaque adv_chunk_157 : advance 535336 2000 = 251428 := by decide
opaque scan_chunk_158 : scan 316001 251428 2000 = true := by decide
opaque adv_chunk_158 : advance 251428 2000 = 204912 := by decide
opaque scan_chunk_159 : scan 318001 204912 2000 = true := by decide
opaque adv_chunk_159 : advance 204912 2000 = 209724 := by decide
opaque scan_chunk_160 : scan 320001 209724 2000 = true := by decide
opaque adv_chunk_160 : advance 209724 2000 = 285112 := by decide
opaque scan_chunk_161 : scan 322001 285112 2000 = true := by decide
opaque adv_chunk_161 : advance 285112 2000 = 182456 := by decide
opaque scan_chunk_162 : scan 324001 182456 2000 = true := by decide
opaque adv_chunk_162 : advance 182456 2000 = 41304 := by decide
opaque scan_chunk_163 : scan 326001 41304 2000 = true := by decide
opaque adv_chunk_163 : advance 41304 2000 = 397392 := by decide
opaque scan_chunk_164 : scan 328001 397392 2000 = true := by decide
opaque adv_chunk_164 : advance 397392 2000 = 474384 := by decide
opaque scan_chunk_165 : scan 330001 474384 2000 = true := by decide
opaque adv_chunk_165 : advance 474384 2000 = 30076 := by decide
opaque scan_chunk_166 : scan 332001 30076 2000 = true := by decide
opaque adv_chunk_166 : advance 30076 2000 = 38096 := by decide
opaque scan_chunk_167 : scan 334001 38096 2000 = true := by decide
opaque adv_chunk_167 : advance 38096 2000 = 530524 := by decide
opaque scan_chunk_168 : scan 336001 530524 2000 = true := by decide
opaque adv_chunk_168 : advance 530524 2000 = 176040 := by decide
opaque scan_chunk_169 : scan 338001 176040 2000 = true := by decide
opaque adv_chunk_169 : advance 176040 2000 = 307568 := by decide
opaque scan_chunk_170 : scan 340001 307568 2000 = true := by decide
opaque adv_chunk_170 : advance 307568 2000 = 350876 := by decide
opaque scan_chunk_171 : scan 342001 350876 2000 = true := by decide
opaque adv_chunk_171 : advance 350876 2000 = 479196 := by decide
opaque scan_chunk_172 : scan 344001 479196 2000 = true := by decide
opaque adv_chunk_172 : advance 479196 2000 = 105464 := by decide
opaque scan_chunk_173 : scan 346001 105464 2000 = true := by decide
opaque adv_chunk_173 : advance 105464 2000 = 485612 := by decide
opaque scan_chunk_174 : scan 348001 485612 2000 = true := by decide
opaque adv_chunk_174 : advance 485612 2000 = 389372 := by decide
opaque scan_chunk_175 : scan 350001 389372 2000 = true := by decide
opaque adv_chunk_175 : advance 389372 2000 = 532128 := by decide
opaque scan_chunk_176 : scan 352001 532128 2000 = true := by decide
opaque adv_chunk_176 : advance 532128 2000 = 384560 := by decide
opaque scan_chunk_177 : scan 354001 384560 2000 = true := by decide
opaque adv_chunk_177 : advance 384560 2000 = 456740 := by decide
opaque scan_chunk_178 : scan 356001 456740 2000 = true := by decide
opaque adv_chunk_178 : advance 456740 2000 = 487216 := by decide
opaque scan_chunk_179 : scan 358001 487216 2000 = true := by decide
opaque adv_chunk_179 : advance 487216 2000 = 47720 := by decide
opaque scan_chunk_180 : scan 360001 47720 2000 = true := by decide
opaque adv_chunk_180 : advance 47720 2000 = 131128 := by decide
opaque scan_chunk_181 : scan 362001 131128 2000 = true := by decide
opaque adv_chunk_181 : advance 131128 2000 = 520900 := by decide
opaque scan_chunk_182 : scan 364001 520900 2000 = true := by decide
opaque adv_chunk_182 : advance 520900 2000 = 25264 := by decide
opaque scan_chunk_183 : scan 366001 25264 2000 = true := by decide
opaque adv_chunk_183 : advance 25264 2000 = 512880 := by decide
opaque scan_chunk_184 : scan 368001 512880 2000 = true := by decide
opaque adv_chunk_184 : advance 512880 2000 = 83008 := by decide
opaque scan_chunk_185 : scan 370001 83008 2000 = true := by decide
opaque adv_chunk_185 : advance 83008 2000 = 317192 := by decide
opaque scan_chunk_186 : scan 372001 317192 2000 = true := by decide
opaque adv_chunk_186 : advance 317192 2000 = 501652 := by decide
opaque scan_chunk_187 : scan 374001 501652 2000 = true := by decide
opaque adv_chunk_187 : advance 501652 2000 = 273884 := by decide
opaque scan_chunk_188 : scan 376001 273884 2000 = true := by decide
opaque adv_chunk_188 : advance 273884 2000 = 373332 := by decide
opaque scan_chunk_189 : scan 378001 373332 2000 = true := by decide
opaque adv_chunk_189 : advance 373332 2000 = 97444 := by decide
opaque scan_chunk_190 : scan 380001 97444 2000 = true := by decide
opaque adv_chunk_190 : advance 97444 2000 = 543356 := by decide
opaque scan_chunk_191 : scan 382001 543356 2000 = true := by decide
opaque adv_chunk_191 : advance 543356 2000 = 193684 := by decide
opaque scan_chunk_192 : scan 384001 193684 2000 = true := by decide
opaque adv_chunk_192 : advance 193684 2000 = 400600 := by decide
opaque scan_chunk_193 : scan 386001 400600 2000 = true := by decide
opaque adv_chunk_193 : advance 400600 2000 = 341252 := by decide
opaque scan_chunk_194 : scan 388001 341252 2000 = true := by decide
opaque adv_chunk_194 : advance 341252 2000 = 328420 := by decide
opaque scan_chunk_195 : scan 390001 328420 2000 = true := by decide
opaque adv_chunk_195 : advance 328420 2000 = 310776 := by decide
opaque scan_chunk_196 : scan 392001 310776 2000 = true := by decide
opaque adv_chunk_196 : advance 310776 2000 = 217744 := by decide
opaque scan_chunk_197 : scan 394001 217744 2000 = true := by decide
opaque adv_chunk_197 : advance 217744 2000 = 227368 := by decide
opaque scan_chunk_198 : scan 396001 227368 2000 = true := by decide
opaque adv_chunk_198 : advance 227368 2000 = 378144 := by decide
opaque scan_chunk_199 : scan 398001 378144 2000 = true := by decide
opaque adv_chunk_199 : advance 378144 2000 = 172832 := by decide
opaque hp_chunk_0 : (1 : Nat) ≡ 2^(1-1) [MOD 550172] := by norm_num [Nat.ModEq]
opaque hp_chunk_1 : 254636 ≡ 2^(2001-1) [MOD 550172] := by
  have h := advance_sound 1 1 2000 (by norm_num) hp_chunk_0
  rw [adv_chunk_0] at h
  have he : 1 + 2000 - 1 = 2001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_2 : 71780 ≡ 2^(4001-1) [MOD 550172] := by
  have h := advance_sound 2001 254636 2000 (by norm_num) hp_chunk_1
  rw [adv_chunk_1] at h
  have he : 2001 + 2000 - 1 = 4001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_3 : 508068 ≡ 2^(6001-1) [MOD 550172] := by
  have h := advance_sound 4001 71780 2000 (by norm_num) hp_chunk_2
  rw [adv_chunk_2] at h
  have he : 4001 + 2000 - 1 = 6001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_4 : 7620 ≡ 2^(8001-1) [MOD 550172] := by
  have h := advance_sound 6001 508068 2000 (by norm_num) hp_chunk_3
  rw [adv_chunk_3] at h
  have he : 6001 + 2000 - 1 = 8001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_5 : 419848 ≡ 2^(10001-1) [MOD 550172] := by
  have h := advance_sound 8001 7620 2000 (by norm_num) hp_chunk_4
  rw [adv_chunk_4] at h
  have he : 8001 + 2000 - 1 = 10001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_6 : 92632 ≡ 2^(12001-1) [MOD 550172] := by
  have h := advance_sound 10001 419848 2000 (by norm_num) hp_chunk_5
  rw [adv_chunk_5] at h
  have he : 10001 + 2000 - 1 = 12001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_7 : 467968 ≡ 2^(14001-1) [MOD 550172] := by
  have h := advance_sound 12001 92632 2000 (by norm_num) hp_chunk_6
  rw [adv_chunk_6] at h
  have he : 12001 + 2000 - 1 = 14001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_8 : 296340 ≡ 2^(16001-1) [MOD 550172] := by
  have h := advance_sound 14001 467968 2000 (by norm_num) hp_chunk_7
  rw [adv_chunk_7] at h
  have he : 14001 + 2000 - 1 = 16001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_9 : 541752 ≡ 2^(18001-1) [MOD 550172] := by
  have h := advance_sound 16001 296340 2000 (by norm_num) hp_chunk_8
  rw [adv_chunk_8] at h
  have he : 16001 + 2000 - 1 = 18001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_10 : 535336 ≡ 2^(20001-1) [MOD 550172] := by
  have h := advance_sound 18001 541752 2000 (by norm_num) hp_chunk_9
  rw [adv_chunk_9] at h
  have he : 18001 + 2000 - 1 = 20001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_11 : 251428 ≡ 2^(22001-1) [MOD 550172] := by
  have h := advance_sound 20001 535336 2000 (by norm_num) hp_chunk_10
  rw [adv_chunk_10] at h
  have he : 20001 + 2000 - 1 = 22001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_12 : 204912 ≡ 2^(24001-1) [MOD 550172] := by
  have h := advance_sound 22001 251428 2000 (by norm_num) hp_chunk_11
  rw [adv_chunk_11] at h
  have he : 22001 + 2000 - 1 = 24001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_13 : 209724 ≡ 2^(26001-1) [MOD 550172] := by
  have h := advance_sound 24001 204912 2000 (by norm_num) hp_chunk_12
  rw [adv_chunk_12] at h
  have he : 24001 + 2000 - 1 = 26001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_14 : 285112 ≡ 2^(28001-1) [MOD 550172] := by
  have h := advance_sound 26001 209724 2000 (by norm_num) hp_chunk_13
  rw [adv_chunk_13] at h
  have he : 26001 + 2000 - 1 = 28001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_15 : 182456 ≡ 2^(30001-1) [MOD 550172] := by
  have h := advance_sound 28001 285112 2000 (by norm_num) hp_chunk_14
  rw [adv_chunk_14] at h
  have he : 28001 + 2000 - 1 = 30001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_16 : 41304 ≡ 2^(32001-1) [MOD 550172] := by
  have h := advance_sound 30001 182456 2000 (by norm_num) hp_chunk_15
  rw [adv_chunk_15] at h
  have he : 30001 + 2000 - 1 = 32001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_17 : 397392 ≡ 2^(34001-1) [MOD 550172] := by
  have h := advance_sound 32001 41304 2000 (by norm_num) hp_chunk_16
  rw [adv_chunk_16] at h
  have he : 32001 + 2000 - 1 = 34001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_18 : 474384 ≡ 2^(36001-1) [MOD 550172] := by
  have h := advance_sound 34001 397392 2000 (by norm_num) hp_chunk_17
  rw [adv_chunk_17] at h
  have he : 34001 + 2000 - 1 = 36001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_19 : 30076 ≡ 2^(38001-1) [MOD 550172] := by
  have h := advance_sound 36001 474384 2000 (by norm_num) hp_chunk_18
  rw [adv_chunk_18] at h
  have he : 36001 + 2000 - 1 = 38001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_20 : 38096 ≡ 2^(40001-1) [MOD 550172] := by
  have h := advance_sound 38001 30076 2000 (by norm_num) hp_chunk_19
  rw [adv_chunk_19] at h
  have he : 38001 + 2000 - 1 = 40001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_21 : 530524 ≡ 2^(42001-1) [MOD 550172] := by
  have h := advance_sound 40001 38096 2000 (by norm_num) hp_chunk_20
  rw [adv_chunk_20] at h
  have he : 40001 + 2000 - 1 = 42001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_22 : 176040 ≡ 2^(44001-1) [MOD 550172] := by
  have h := advance_sound 42001 530524 2000 (by norm_num) hp_chunk_21
  rw [adv_chunk_21] at h
  have he : 42001 + 2000 - 1 = 44001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_23 : 307568 ≡ 2^(46001-1) [MOD 550172] := by
  have h := advance_sound 44001 176040 2000 (by norm_num) hp_chunk_22
  rw [adv_chunk_22] at h
  have he : 44001 + 2000 - 1 = 46001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_24 : 350876 ≡ 2^(48001-1) [MOD 550172] := by
  have h := advance_sound 46001 307568 2000 (by norm_num) hp_chunk_23
  rw [adv_chunk_23] at h
  have he : 46001 + 2000 - 1 = 48001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_25 : 479196 ≡ 2^(50001-1) [MOD 550172] := by
  have h := advance_sound 48001 350876 2000 (by norm_num) hp_chunk_24
  rw [adv_chunk_24] at h
  have he : 48001 + 2000 - 1 = 50001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_26 : 105464 ≡ 2^(52001-1) [MOD 550172] := by
  have h := advance_sound 50001 479196 2000 (by norm_num) hp_chunk_25
  rw [adv_chunk_25] at h
  have he : 50001 + 2000 - 1 = 52001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_27 : 485612 ≡ 2^(54001-1) [MOD 550172] := by
  have h := advance_sound 52001 105464 2000 (by norm_num) hp_chunk_26
  rw [adv_chunk_26] at h
  have he : 52001 + 2000 - 1 = 54001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_28 : 389372 ≡ 2^(56001-1) [MOD 550172] := by
  have h := advance_sound 54001 485612 2000 (by norm_num) hp_chunk_27
  rw [adv_chunk_27] at h
  have he : 54001 + 2000 - 1 = 56001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_29 : 532128 ≡ 2^(58001-1) [MOD 550172] := by
  have h := advance_sound 56001 389372 2000 (by norm_num) hp_chunk_28
  rw [adv_chunk_28] at h
  have he : 56001 + 2000 - 1 = 58001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_30 : 384560 ≡ 2^(60001-1) [MOD 550172] := by
  have h := advance_sound 58001 532128 2000 (by norm_num) hp_chunk_29
  rw [adv_chunk_29] at h
  have he : 58001 + 2000 - 1 = 60001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_31 : 456740 ≡ 2^(62001-1) [MOD 550172] := by
  have h := advance_sound 60001 384560 2000 (by norm_num) hp_chunk_30
  rw [adv_chunk_30] at h
  have he : 60001 + 2000 - 1 = 62001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_32 : 487216 ≡ 2^(64001-1) [MOD 550172] := by
  have h := advance_sound 62001 456740 2000 (by norm_num) hp_chunk_31
  rw [adv_chunk_31] at h
  have he : 62001 + 2000 - 1 = 64001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_33 : 47720 ≡ 2^(66001-1) [MOD 550172] := by
  have h := advance_sound 64001 487216 2000 (by norm_num) hp_chunk_32
  rw [adv_chunk_32] at h
  have he : 64001 + 2000 - 1 = 66001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_34 : 131128 ≡ 2^(68001-1) [MOD 550172] := by
  have h := advance_sound 66001 47720 2000 (by norm_num) hp_chunk_33
  rw [adv_chunk_33] at h
  have he : 66001 + 2000 - 1 = 68001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_35 : 520900 ≡ 2^(70001-1) [MOD 550172] := by
  have h := advance_sound 68001 131128 2000 (by norm_num) hp_chunk_34
  rw [adv_chunk_34] at h
  have he : 68001 + 2000 - 1 = 70001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_36 : 25264 ≡ 2^(72001-1) [MOD 550172] := by
  have h := advance_sound 70001 520900 2000 (by norm_num) hp_chunk_35
  rw [adv_chunk_35] at h
  have he : 70001 + 2000 - 1 = 72001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_37 : 512880 ≡ 2^(74001-1) [MOD 550172] := by
  have h := advance_sound 72001 25264 2000 (by norm_num) hp_chunk_36
  rw [adv_chunk_36] at h
  have he : 72001 + 2000 - 1 = 74001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_38 : 83008 ≡ 2^(76001-1) [MOD 550172] := by
  have h := advance_sound 74001 512880 2000 (by norm_num) hp_chunk_37
  rw [adv_chunk_37] at h
  have he : 74001 + 2000 - 1 = 76001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_39 : 317192 ≡ 2^(78001-1) [MOD 550172] := by
  have h := advance_sound 76001 83008 2000 (by norm_num) hp_chunk_38
  rw [adv_chunk_38] at h
  have he : 76001 + 2000 - 1 = 78001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_40 : 501652 ≡ 2^(80001-1) [MOD 550172] := by
  have h := advance_sound 78001 317192 2000 (by norm_num) hp_chunk_39
  rw [adv_chunk_39] at h
  have he : 78001 + 2000 - 1 = 80001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_41 : 273884 ≡ 2^(82001-1) [MOD 550172] := by
  have h := advance_sound 80001 501652 2000 (by norm_num) hp_chunk_40
  rw [adv_chunk_40] at h
  have he : 80001 + 2000 - 1 = 82001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_42 : 373332 ≡ 2^(84001-1) [MOD 550172] := by
  have h := advance_sound 82001 273884 2000 (by norm_num) hp_chunk_41
  rw [adv_chunk_41] at h
  have he : 82001 + 2000 - 1 = 84001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_43 : 97444 ≡ 2^(86001-1) [MOD 550172] := by
  have h := advance_sound 84001 373332 2000 (by norm_num) hp_chunk_42
  rw [adv_chunk_42] at h
  have he : 84001 + 2000 - 1 = 86001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_44 : 543356 ≡ 2^(88001-1) [MOD 550172] := by
  have h := advance_sound 86001 97444 2000 (by norm_num) hp_chunk_43
  rw [adv_chunk_43] at h
  have he : 86001 + 2000 - 1 = 88001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_45 : 193684 ≡ 2^(90001-1) [MOD 550172] := by
  have h := advance_sound 88001 543356 2000 (by norm_num) hp_chunk_44
  rw [adv_chunk_44] at h
  have he : 88001 + 2000 - 1 = 90001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_46 : 400600 ≡ 2^(92001-1) [MOD 550172] := by
  have h := advance_sound 90001 193684 2000 (by norm_num) hp_chunk_45
  rw [adv_chunk_45] at h
  have he : 90001 + 2000 - 1 = 92001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_47 : 341252 ≡ 2^(94001-1) [MOD 550172] := by
  have h := advance_sound 92001 400600 2000 (by norm_num) hp_chunk_46
  rw [adv_chunk_46] at h
  have he : 92001 + 2000 - 1 = 94001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_48 : 328420 ≡ 2^(96001-1) [MOD 550172] := by
  have h := advance_sound 94001 341252 2000 (by norm_num) hp_chunk_47
  rw [adv_chunk_47] at h
  have he : 94001 + 2000 - 1 = 96001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_49 : 310776 ≡ 2^(98001-1) [MOD 550172] := by
  have h := advance_sound 96001 328420 2000 (by norm_num) hp_chunk_48
  rw [adv_chunk_48] at h
  have he : 96001 + 2000 - 1 = 98001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_50 : 217744 ≡ 2^(100001-1) [MOD 550172] := by
  have h := advance_sound 98001 310776 2000 (by norm_num) hp_chunk_49
  rw [adv_chunk_49] at h
  have he : 98001 + 2000 - 1 = 100001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_51 : 227368 ≡ 2^(102001-1) [MOD 550172] := by
  have h := advance_sound 100001 217744 2000 (by norm_num) hp_chunk_50
  rw [adv_chunk_50] at h
  have he : 100001 + 2000 - 1 = 102001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_52 : 378144 ≡ 2^(104001-1) [MOD 550172] := by
  have h := advance_sound 102001 227368 2000 (by norm_num) hp_chunk_51
  rw [adv_chunk_51] at h
  have he : 102001 + 2000 - 1 = 104001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_53 : 172832 ≡ 2^(106001-1) [MOD 550172] := by
  have h := advance_sound 104001 378144 2000 (by norm_num) hp_chunk_52
  rw [adv_chunk_52] at h
  have he : 104001 + 2000 - 1 = 106001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_54 : 440700 ≡ 2^(108001-1) [MOD 550172] := by
  have h := advance_sound 106001 172832 2000 (by norm_num) hp_chunk_53
  rw [adv_chunk_53] at h
  have he : 106001 + 2000 - 1 = 108001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_55 : 52532 ≡ 2^(110001-1) [MOD 550172] := by
  have h := advance_sound 108001 440700 2000 (by norm_num) hp_chunk_54
  rw [adv_chunk_54] at h
  have he : 108001 + 2000 - 1 = 110001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_56 : 206516 ≡ 2^(112001-1) [MOD 550172] := by
  have h := advance_sound 110001 52532 2000 (by norm_num) hp_chunk_55
  rw [adv_chunk_55] at h
  have he : 110001 + 2000 - 1 = 112001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_57 : 418244 ≡ 2^(114001-1) [MOD 550172] := by
  have h := advance_sound 112001 206516 2000 (by norm_num) hp_chunk_56
  rw [adv_chunk_56] at h
  have he : 112001 + 2000 - 1 = 114001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_58 : 434284 ≡ 2^(116001-1) [MOD 550172] := by
  have h := advance_sound 114001 418244 2000 (by norm_num) hp_chunk_57
  rw [adv_chunk_57] at h
  have he : 114001 + 2000 - 1 = 116001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_59 : 318796 ≡ 2^(118001-1) [MOD 550172] := by
  have h := advance_sound 116001 434284 2000 (by norm_num) hp_chunk_58
  rw [adv_chunk_58] at h
  have he : 116001 + 2000 - 1 = 118001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_60 : 160000 ≡ 2^(120001-1) [MOD 550172] := by
  have h := advance_sound 118001 318796 2000 (by norm_num) hp_chunk_59
  rw [adv_chunk_59] at h
  have he : 118001 + 2000 - 1 = 120001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_61 : 423056 ≡ 2^(122001-1) [MOD 550172] := by
  have h := advance_sound 120001 160000 2000 (by norm_num) hp_chunk_60
  rw [adv_chunk_60] at h
  have he : 120001 + 2000 - 1 = 122001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_62 : 509672 ≡ 2^(124001-1) [MOD 550172] := by
  have h := advance_sound 122001 423056 2000 (by norm_num) hp_chunk_61
  rw [adv_chunk_61] at h
  have he : 122001 + 2000 - 1 = 124001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_63 : 216140 ≡ 2^(126001-1) [MOD 550172] := by
  have h := advance_sound 124001 509672 2000 (by norm_num) hp_chunk_62
  rw [adv_chunk_62] at h
  have he : 124001 + 2000 - 1 = 126001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_64 : 18848 ≡ 2^(128001-1) [MOD 550172] := by
  have h := advance_sound 126001 216140 2000 (by norm_num) hp_chunk_63
  rw [adv_chunk_63] at h
  have he : 126001 + 2000 - 1 = 128001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_65 : 228972 ≡ 2^(130001-1) [MOD 550172] := by
  have h := advance_sound 128001 18848 2000 (by norm_num) hp_chunk_64
  rw [adv_chunk_64] at h
  have he : 128001 + 2000 - 1 = 130001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_66 : 36492 ≡ 2^(132001-1) [MOD 550172] := by
  have h := advance_sound 130001 228972 2000 (by norm_num) hp_chunk_65
  rw [adv_chunk_65] at h
  have he : 130001 + 2000 - 1 = 132001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_67 : 322004 ≡ 2^(134001-1) [MOD 550172] := by
  have h := advance_sound 132001 36492 2000 (by norm_num) hp_chunk_66
  rw [adv_chunk_66] at h
  have he : 132001 + 2000 - 1 = 134001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_68 : 26868 ≡ 2^(136001-1) [MOD 550172] := by
  have h := advance_sound 134001 322004 2000 (by norm_num) hp_chunk_67
  rw [adv_chunk_67] at h
  have he : 134001 + 2000 - 1 = 136001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_69 : 171228 ≡ 2^(138001-1) [MOD 550172] := by
  have h := advance_sound 136001 26868 2000 (by norm_num) hp_chunk_68
  rw [adv_chunk_68] at h
  have he : 136001 + 2000 - 1 = 138001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_70 : 232180 ≡ 2^(140001-1) [MOD 550172] := by
  have h := advance_sound 138001 171228 2000 (by norm_num) hp_chunk_69
  rw [adv_chunk_69] at h
  have he : 138001 + 2000 - 1 = 140001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_71 : 453532 ≡ 2^(142001-1) [MOD 550172] := by
  have h := advance_sound 140001 232180 2000 (by norm_num) hp_chunk_70
  rw [adv_chunk_70] at h
  have he : 140001 + 2000 - 1 = 142001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_72 : 70176 ≡ 2^(144001-1) [MOD 550172] := by
  have h := advance_sound 142001 453532 2000 (by norm_num) hp_chunk_71
  rw [adv_chunk_71] at h
  have he : 142001 + 2000 - 1 = 144001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_73 : 299548 ≡ 2^(146001-1) [MOD 550172] := by
  have h := advance_sound 144001 70176 2000 (by norm_num) hp_chunk_72
  rw [adv_chunk_72] at h
  have he : 144001 + 2000 - 1 = 146001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_74 : 408620 ≡ 2^(148001-1) [MOD 550172] := by
  have h := advance_sound 146001 299548 2000 (by norm_num) hp_chunk_73
  rw [adv_chunk_73] at h
  have he : 146001 + 2000 - 1 = 148001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_75 : 283508 ≡ 2^(150001-1) [MOD 550172] := by
  have h := advance_sound 148001 408620 2000 (by norm_num) hp_chunk_74
  rw [adv_chunk_74] at h
  have he : 148001 + 2000 - 1 = 150001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_76 : 524108 ≡ 2^(152001-1) [MOD 550172] := by
  have h := advance_sound 150001 283508 2000 (by norm_num) hp_chunk_75
  rw [adv_chunk_75] at h
  have he : 150001 + 2000 - 1 = 152001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_77 : 442304 ≡ 2^(154001-1) [MOD 550172] := by
  have h := advance_sound 152001 524108 2000 (by norm_num) hp_chunk_76
  rw [adv_chunk_76] at h
  have he : 152001 + 2000 - 1 = 154001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_78 : 261052 ≡ 2^(156001-1) [MOD 550172] := by
  have h := advance_sound 154001 442304 2000 (by norm_num) hp_chunk_77
  rw [adv_chunk_77] at h
  have he : 154001 + 2000 - 1 = 156001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_79 : 355688 ≡ 2^(158001-1) [MOD 550172] := by
  have h := advance_sound 156001 261052 2000 (by norm_num) hp_chunk_78
  rw [adv_chunk_78] at h
  have he : 156001 + 2000 - 1 = 158001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_80 : 4412 ≡ 2^(160001-1) [MOD 550172] := by
  have h := advance_sound 158001 355688 2000 (by norm_num) hp_chunk_79
  rw [adv_chunk_79] at h
  have he : 158001 + 2000 - 1 = 160001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_81 : 2808 ≡ 2^(162001-1) [MOD 550172] := by
  have h := advance_sound 160001 4412 2000 (by norm_num) hp_chunk_80
  rw [adv_chunk_80] at h
  have he : 160001 + 2000 - 1 = 162001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_82 : 344460 ≡ 2^(164001-1) [MOD 550172] := by
  have h := advance_sound 162001 2808 2000 (by norm_num) hp_chunk_81
  rw [adv_chunk_81] at h
  have he : 162001 + 2000 - 1 = 164001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_83 : 195288 ≡ 2^(166001-1) [MOD 550172] := by
  have h := advance_sound 164001 344460 2000 (by norm_num) hp_chunk_82
  rw [adv_chunk_82] at h
  have he : 164001 + 2000 - 1 = 166001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_84 : 58948 ≡ 2^(168001-1) [MOD 550172] := by
  have h := advance_sound 166001 195288 2000 (by norm_num) hp_chunk_83
  rw [adv_chunk_83] at h
  have he : 166001 + 2000 - 1 = 168001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_85 : 490424 ≡ 2^(170001-1) [MOD 550172] := by
  have h := advance_sound 168001 58948 2000 (by norm_num) hp_chunk_84
  rw [adv_chunk_84] at h
  have he : 168001 + 2000 - 1 = 170001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_86 : 464760 ≡ 2^(172001-1) [MOD 550172] := by
  have h := advance_sound 170001 490424 2000 (by norm_num) hp_chunk_85
  rw [adv_chunk_85] at h
  have he : 170001 + 2000 - 1 = 172001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_87 : 429472 ≡ 2^(174001-1) [MOD 550172] := by
  have h := advance_sound 172001 464760 2000 (by norm_num) hp_chunk_86
  rw [adv_chunk_86] at h
  have he : 172001 + 2000 - 1 = 174001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_88 : 243408 ≡ 2^(176001-1) [MOD 550172] := by
  have h := advance_sound 174001 429472 2000 (by norm_num) hp_chunk_87
  rw [adv_chunk_87] at h
  have he : 174001 + 2000 - 1 = 176001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_89 : 262656 ≡ 2^(178001-1) [MOD 550172] := by
  have h := advance_sound 176001 243408 2000 (by norm_num) hp_chunk_88
  rw [adv_chunk_88] at h
  have he : 176001 + 2000 - 1 = 178001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_90 : 14036 ≡ 2^(180001-1) [MOD 550172] := by
  have h := advance_sound 178001 262656 2000 (by norm_num) hp_chunk_89
  rw [adv_chunk_89] at h
  have he : 178001 + 2000 - 1 = 180001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_91 : 153584 ≡ 2^(182001-1) [MOD 550172] := by
  have h := advance_sound 180001 14036 2000 (by norm_num) hp_chunk_90
  rw [adv_chunk_90] at h
  have he : 180001 + 2000 - 1 = 182001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_92 : 139148 ≡ 2^(184001-1) [MOD 550172] := by
  have h := advance_sound 182001 153584 2000 (by norm_num) hp_chunk_91
  rw [adv_chunk_91] at h
  have he : 182001 + 2000 - 1 = 184001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_93 : 463156 ≡ 2^(186001-1) [MOD 550172] := by
  have h := advance_sound 184001 139148 2000 (by norm_num) hp_chunk_92
  rw [adv_chunk_92] at h
  have he : 184001 + 2000 - 1 = 186001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_94 : 220952 ≡ 2^(188001-1) [MOD 550172] := by
  have h := advance_sound 186001 463156 2000 (by norm_num) hp_chunk_93
  rw [adv_chunk_93] at h
  have he : 186001 + 2000 - 1 = 188001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_95 : 94236 ≡ 2^(190001-1) [MOD 550172] := by
  have h := advance_sound 188001 220952 2000 (by norm_num) hp_chunk_94
  rw [adv_chunk_94] at h
  have he : 188001 + 2000 - 1 = 190001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_96 : 126316 ≡ 2^(192001-1) [MOD 550172] := by
  have h := advance_sound 190001 94236 2000 (by norm_num) hp_chunk_95
  rw [adv_chunk_95] at h
  have he : 190001 + 2000 - 1 = 192001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_97 : 445512 ≡ 2^(194001-1) [MOD 550172] := by
  have h := advance_sound 192001 126316 2000 (by norm_num) hp_chunk_96
  rw [adv_chunk_96] at h
  have he : 192001 + 2000 - 1 = 194001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_98 : 127920 ≡ 2^(196001-1) [MOD 550172] := by
  have h := advance_sound 194001 445512 2000 (by norm_num) hp_chunk_97
  rw [adv_chunk_97] at h
  have he : 194001 + 2000 - 1 = 196001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_99 : 103860 ≡ 2^(198001-1) [MOD 550172] := by
  have h := advance_sound 196001 127920 2000 (by norm_num) hp_chunk_98
  rw [adv_chunk_98] at h
  have he : 196001 + 2000 - 1 = 198001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_100 : 277092 ≡ 2^(200001-1) [MOD 550172] := by
  have h := advance_sound 198001 103860 2000 (by norm_num) hp_chunk_99
  rw [adv_chunk_99] at h
  have he : 198001 + 2000 - 1 = 200001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_101 : 240200 ≡ 2^(202001-1) [MOD 550172] := by
  have h := advance_sound 200001 277092 2000 (by norm_num) hp_chunk_100
  rw [adv_chunk_100] at h
  have he : 200001 + 2000 - 1 = 202001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_102 : 395788 ≡ 2^(204001-1) [MOD 550172] := by
  have h := advance_sound 202001 240200 2000 (by norm_num) hp_chunk_101
  rw [adv_chunk_101] at h
  have he : 202001 + 2000 - 1 = 204001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_103 : 265864 ≡ 2^(206001-1) [MOD 550172] := by
  have h := advance_sound 204001 395788 2000 (by norm_num) hp_chunk_102
  rw [adv_chunk_102] at h
  have he : 204001 + 2000 - 1 = 206001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_104 : 431076 ≡ 2^(208001-1) [MOD 550172] := by
  have h := advance_sound 206001 265864 2000 (by norm_num) hp_chunk_103
  rw [adv_chunk_103] at h
  have he : 206001 + 2000 - 1 = 208001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_105 : 451928 ≡ 2^(210001-1) [MOD 550172] := by
  have h := advance_sound 208001 431076 2000 (by norm_num) hp_chunk_104
  rw [adv_chunk_104] at h
  have he : 208001 + 2000 - 1 = 210001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_106 : 411828 ≡ 2^(212001-1) [MOD 550172] := by
  have h := advance_sound 210001 451928 2000 (by norm_num) hp_chunk_105
  rw [adv_chunk_105] at h
  have he : 210001 + 2000 - 1 = 212001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_107 : 150376 ≡ 2^(214001-1) [MOD 550172] := by
  have h := advance_sound 212001 411828 2000 (by norm_num) hp_chunk_106
  rw [adv_chunk_106] at h
  have he : 212001 + 2000 - 1 = 214001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_108 : 272280 ≡ 2^(216001-1) [MOD 550172] := by
  have h := advance_sound 214001 150376 2000 (by norm_num) hp_chunk_107
  rw [adv_chunk_107] at h
  have he : 214001 + 2000 - 1 = 216001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_109 : 164812 ≡ 2^(218001-1) [MOD 550172] := by
  have h := advance_sound 216001 272280 2000 (by norm_num) hp_chunk_108
  rw [adv_chunk_108] at h
  have he : 216001 + 2000 - 1 = 218001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_110 : 498444 ≡ 2^(220001-1) [MOD 550172] := by
  have h := advance_sound 218001 164812 2000 (by norm_num) hp_chunk_109
  rw [adv_chunk_109] at h
  have he : 218001 + 2000 - 1 = 220001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_111 : 407016 ≡ 2^(222001-1) [MOD 550172] := by
  have h := advance_sound 220001 498444 2000 (by norm_num) hp_chunk_110
  rw [adv_chunk_110] at h
  have he : 220001 + 2000 - 1 = 222001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_112 : 74988 ≡ 2^(224001-1) [MOD 550172] := by
  have h := advance_sound 222001 407016 2000 (by norm_num) hp_chunk_111
  rw [adv_chunk_111] at h
  have he : 222001 + 2000 - 1 = 224001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_113 : 374936 ≡ 2^(226001-1) [MOD 550172] := by
  have h := advance_sound 224001 74988 2000 (by norm_num) hp_chunk_112
  rw [adv_chunk_112] at h
  have he : 224001 + 2000 - 1 = 226001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_114 : 305964 ≡ 2^(228001-1) [MOD 550172] := by
  have h := advance_sound 226001 374936 2000 (by norm_num) hp_chunk_113
  rw [adv_chunk_113] at h
  have he : 226001 + 2000 - 1 = 228001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_115 : 142356 ≡ 2^(230001-1) [MOD 550172] := by
  have h := advance_sound 228001 305964 2000 (by norm_num) hp_chunk_114
  rw [adv_chunk_114] at h
  have he : 228001 + 2000 - 1 = 230001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_116 : 330024 ≡ 2^(232001-1) [MOD 550172] := by
  have h := advance_sound 230001 142356 2000 (by norm_num) hp_chunk_115
  rw [adv_chunk_115] at h
  have he : 230001 + 2000 - 1 = 232001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_117 : 519296 ≡ 2^(234001-1) [MOD 550172] := by
  have h := advance_sound 232001 330024 2000 (by norm_num) hp_chunk_116
  rw [adv_chunk_116] at h
  have he : 232001 + 2000 - 1 = 234001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_118 : 366916 ≡ 2^(236001-1) [MOD 550172] := by
  have h := advance_sound 234001 519296 2000 (by norm_num) hp_chunk_117
  rw [adv_chunk_117] at h
  have he : 234001 + 2000 - 1 = 236001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_119 : 363708 ≡ 2^(238001-1) [MOD 550172] := by
  have h := advance_sound 236001 366916 2000 (by norm_num) hp_chunk_118
  rw [adv_chunk_118] at h
  have he : 236001 + 2000 - 1 = 238001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_120 : 496840 ≡ 2^(240001-1) [MOD 550172] := by
  have h := advance_sound 238001 363708 2000 (by norm_num) hp_chunk_119
  rw [adv_chunk_119] at h
  have he : 238001 + 2000 - 1 = 240001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_121 : 198496 ≡ 2^(242001-1) [MOD 550172] := by
  have h := advance_sound 240001 496840 2000 (by norm_num) hp_chunk_120
  rw [adv_chunk_120] at h
  have he : 240001 + 2000 - 1 = 242001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_122 : 475988 ≡ 2^(244001-1) [MOD 550172] := by
  have h := advance_sound 242001 198496 2000 (by norm_num) hp_chunk_121
  rw [adv_chunk_121] at h
  have he : 242001 + 2000 - 1 = 244001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_123 : 238596 ≡ 2^(246001-1) [MOD 550172] := by
  have h := advance_sound 244001 475988 2000 (by norm_num) hp_chunk_122
  rw [adv_chunk_122] at h
  have he : 244001 + 2000 - 1 = 246001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_124 : 187268 ≡ 2^(248001-1) [MOD 550172] := by
  have h := advance_sound 246001 238596 2000 (by norm_num) hp_chunk_123
  rw [adv_chunk_123] at h
  have he : 246001 + 2000 - 1 = 248001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_125 : 116692 ≡ 2^(250001-1) [MOD 550172] := by
  have h := advance_sound 248001 187268 2000 (by norm_num) hp_chunk_124
  rw [adv_chunk_124] at h
  have he : 248001 + 2000 - 1 = 250001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_126 : 294736 ≡ 2^(252001-1) [MOD 550172] := by
  have h := advance_sound 250001 116692 2000 (by norm_num) hp_chunk_125
  rw [adv_chunk_125] at h
  have he : 250001 + 2000 - 1 = 252001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_127 : 333232 ≡ 2^(254001-1) [MOD 550172] := by
  have h := advance_sound 252001 294736 2000 (by norm_num) hp_chunk_126
  rw [adv_chunk_126] at h
  have he : 252001 + 2000 - 1 = 254001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_128 : 386164 ≡ 2^(256001-1) [MOD 550172] := by
  have h := advance_sound 254001 333232 2000 (by norm_num) hp_chunk_127
  rw [adv_chunk_127] at h
  have he : 254001 + 2000 - 1 = 256001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_129 : 115088 ≡ 2^(258001-1) [MOD 550172] := by
  have h := advance_sound 256001 386164 2000 (by norm_num) hp_chunk_128
  rw [adv_chunk_128] at h
  have he : 256001 + 2000 - 1 = 258001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_130 : 86216 ≡ 2^(260001-1) [MOD 550172] := by
  have h := advance_sound 258001 115088 2000 (by norm_num) hp_chunk_129
  rw [adv_chunk_129] at h
  have he : 258001 + 2000 - 1 = 260001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_131 : 184060 ≡ 2^(262001-1) [MOD 550172] := by
  have h := advance_sound 260001 86216 2000 (by norm_num) hp_chunk_130
  rw [adv_chunk_130] at h
  have he : 260001 + 2000 - 1 = 262001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_132 : 249824 ≡ 2^(264001-1) [MOD 550172] := by
  have h := advance_sound 262001 184060 2000 (by norm_num) hp_chunk_131
  rw [adv_chunk_131] at h
  have he : 262001 + 2000 - 1 = 264001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_133 : 546564 ≡ 2^(266001-1) [MOD 550172] := by
  have h := advance_sound 264001 249824 2000 (by norm_num) hp_chunk_132
  rw [adv_chunk_132] at h
  have he : 264001 + 2000 - 1 = 266001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_134 : 60552 ≡ 2^(268001-1) [MOD 550172] := by
  have h := advance_sound 266001 546564 2000 (by norm_num) hp_chunk_133
  rw [adv_chunk_133] at h
  have he : 266001 + 2000 - 1 = 268001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_135 : 148772 ≡ 2^(270001-1) [MOD 550172] := by
  have h := advance_sound 268001 60552 2000 (by norm_num) hp_chunk_134
  rw [adv_chunk_134] at h
  have he : 268001 + 2000 - 1 = 270001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_136 : 63760 ≡ 2^(272001-1) [MOD 550172] := by
  have h := advance_sound 270001 148772 2000 (by norm_num) hp_chunk_135
  rw [adv_chunk_135] at h
  have he : 270001 + 2000 - 1 = 272001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_137 : 15640 ≡ 2^(274001-1) [MOD 550172] := by
  have h := advance_sound 272001 63760 2000 (by norm_num) hp_chunk_136
  rw [adv_chunk_136] at h
  have he : 272001 + 2000 - 1 = 274001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_138 : 362104 ≡ 2^(276001-1) [MOD 550172] := by
  have h := advance_sound 274001 15640 2000 (by norm_num) hp_chunk_137
  rw [adv_chunk_137] at h
  have he : 274001 + 2000 - 1 = 276001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_139 : 288320 ≡ 2^(278001-1) [MOD 550172] := by
  have h := advance_sound 276001 362104 2000 (by norm_num) hp_chunk_138
  rw [adv_chunk_138] at h
  have he : 276001 + 2000 - 1 = 278001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_140 : 49324 ≡ 2^(280001-1) [MOD 550172] := by
  have h := advance_sound 278001 288320 2000 (by norm_num) hp_chunk_139
  rw [adv_chunk_139] at h
  have he : 278001 + 2000 - 1 = 280001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_141 : 339648 ≡ 2^(282001-1) [MOD 550172] := by
  have h := advance_sound 280001 49324 2000 (by norm_num) hp_chunk_140
  rw [adv_chunk_140] at h
  have he : 280001 + 2000 - 1 = 282001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_142 : 119900 ≡ 2^(284001-1) [MOD 550172] := by
  have h := advance_sound 282001 339648 2000 (by norm_num) hp_chunk_141
  rw [adv_chunk_141] at h
  have he : 282001 + 2000 - 1 = 284001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_143 : 161604 ≡ 2^(286001-1) [MOD 550172] := by
  have h := advance_sound 284001 119900 2000 (by norm_num) hp_chunk_142
  rw [adv_chunk_142] at h
  have he : 284001 + 2000 - 1 = 286001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_144 : 81404 ≡ 2^(288001-1) [MOD 550172] := by
  have h := advance_sound 286001 161604 2000 (by norm_num) hp_chunk_143
  rw [adv_chunk_143] at h
  have he : 286001 + 2000 - 1 = 288001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_145 : 108672 ≡ 2^(290001-1) [MOD 550172] := by
  have h := advance_sound 288001 81404 2000 (by norm_num) hp_chunk_144
  rw [adv_chunk_144] at h
  have he : 288001 + 2000 - 1 = 290001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_146 : 352480 ≡ 2^(292001-1) [MOD 550172] := by
  have h := advance_sound 290001 108672 2000 (by norm_num) hp_chunk_145
  rw [adv_chunk_145] at h
  have he : 290001 + 2000 - 1 = 292001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_147 : 137544 ≡ 2^(294001-1) [MOD 550172] := by
  have h := advance_sound 292001 352480 2000 (by norm_num) hp_chunk_146
  rw [adv_chunk_146] at h
  have he : 292001 + 2000 - 1 = 294001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_148 : 254636 ≡ 2^(296001-1) [MOD 550172] := by
  have h := advance_sound 294001 137544 2000 (by norm_num) hp_chunk_147
  rw [adv_chunk_147] at h
  have he : 294001 + 2000 - 1 = 296001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_149 : 71780 ≡ 2^(298001-1) [MOD 550172] := by
  have h := advance_sound 296001 254636 2000 (by norm_num) hp_chunk_148
  rw [adv_chunk_148] at h
  have he : 296001 + 2000 - 1 = 298001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_150 : 508068 ≡ 2^(300001-1) [MOD 550172] := by
  have h := advance_sound 298001 71780 2000 (by norm_num) hp_chunk_149
  rw [adv_chunk_149] at h
  have he : 298001 + 2000 - 1 = 300001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_151 : 7620 ≡ 2^(302001-1) [MOD 550172] := by
  have h := advance_sound 300001 508068 2000 (by norm_num) hp_chunk_150
  rw [adv_chunk_150] at h
  have he : 300001 + 2000 - 1 = 302001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_152 : 419848 ≡ 2^(304001-1) [MOD 550172] := by
  have h := advance_sound 302001 7620 2000 (by norm_num) hp_chunk_151
  rw [adv_chunk_151] at h
  have he : 302001 + 2000 - 1 = 304001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_153 : 92632 ≡ 2^(306001-1) [MOD 550172] := by
  have h := advance_sound 304001 419848 2000 (by norm_num) hp_chunk_152
  rw [adv_chunk_152] at h
  have he : 304001 + 2000 - 1 = 306001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_154 : 467968 ≡ 2^(308001-1) [MOD 550172] := by
  have h := advance_sound 306001 92632 2000 (by norm_num) hp_chunk_153
  rw [adv_chunk_153] at h
  have he : 306001 + 2000 - 1 = 308001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_155 : 296340 ≡ 2^(310001-1) [MOD 550172] := by
  have h := advance_sound 308001 467968 2000 (by norm_num) hp_chunk_154
  rw [adv_chunk_154] at h
  have he : 308001 + 2000 - 1 = 310001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_156 : 541752 ≡ 2^(312001-1) [MOD 550172] := by
  have h := advance_sound 310001 296340 2000 (by norm_num) hp_chunk_155
  rw [adv_chunk_155] at h
  have he : 310001 + 2000 - 1 = 312001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_157 : 535336 ≡ 2^(314001-1) [MOD 550172] := by
  have h := advance_sound 312001 541752 2000 (by norm_num) hp_chunk_156
  rw [adv_chunk_156] at h
  have he : 312001 + 2000 - 1 = 314001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_158 : 251428 ≡ 2^(316001-1) [MOD 550172] := by
  have h := advance_sound 314001 535336 2000 (by norm_num) hp_chunk_157
  rw [adv_chunk_157] at h
  have he : 314001 + 2000 - 1 = 316001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_159 : 204912 ≡ 2^(318001-1) [MOD 550172] := by
  have h := advance_sound 316001 251428 2000 (by norm_num) hp_chunk_158
  rw [adv_chunk_158] at h
  have he : 316001 + 2000 - 1 = 318001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_160 : 209724 ≡ 2^(320001-1) [MOD 550172] := by
  have h := advance_sound 318001 204912 2000 (by norm_num) hp_chunk_159
  rw [adv_chunk_159] at h
  have he : 318001 + 2000 - 1 = 320001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_161 : 285112 ≡ 2^(322001-1) [MOD 550172] := by
  have h := advance_sound 320001 209724 2000 (by norm_num) hp_chunk_160
  rw [adv_chunk_160] at h
  have he : 320001 + 2000 - 1 = 322001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_162 : 182456 ≡ 2^(324001-1) [MOD 550172] := by
  have h := advance_sound 322001 285112 2000 (by norm_num) hp_chunk_161
  rw [adv_chunk_161] at h
  have he : 322001 + 2000 - 1 = 324001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_163 : 41304 ≡ 2^(326001-1) [MOD 550172] := by
  have h := advance_sound 324001 182456 2000 (by norm_num) hp_chunk_162
  rw [adv_chunk_162] at h
  have he : 324001 + 2000 - 1 = 326001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_164 : 397392 ≡ 2^(328001-1) [MOD 550172] := by
  have h := advance_sound 326001 41304 2000 (by norm_num) hp_chunk_163
  rw [adv_chunk_163] at h
  have he : 326001 + 2000 - 1 = 328001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_165 : 474384 ≡ 2^(330001-1) [MOD 550172] := by
  have h := advance_sound 328001 397392 2000 (by norm_num) hp_chunk_164
  rw [adv_chunk_164] at h
  have he : 328001 + 2000 - 1 = 330001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_166 : 30076 ≡ 2^(332001-1) [MOD 550172] := by
  have h := advance_sound 330001 474384 2000 (by norm_num) hp_chunk_165
  rw [adv_chunk_165] at h
  have he : 330001 + 2000 - 1 = 332001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_167 : 38096 ≡ 2^(334001-1) [MOD 550172] := by
  have h := advance_sound 332001 30076 2000 (by norm_num) hp_chunk_166
  rw [adv_chunk_166] at h
  have he : 332001 + 2000 - 1 = 334001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_168 : 530524 ≡ 2^(336001-1) [MOD 550172] := by
  have h := advance_sound 334001 38096 2000 (by norm_num) hp_chunk_167
  rw [adv_chunk_167] at h
  have he : 334001 + 2000 - 1 = 336001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_169 : 176040 ≡ 2^(338001-1) [MOD 550172] := by
  have h := advance_sound 336001 530524 2000 (by norm_num) hp_chunk_168
  rw [adv_chunk_168] at h
  have he : 336001 + 2000 - 1 = 338001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_170 : 307568 ≡ 2^(340001-1) [MOD 550172] := by
  have h := advance_sound 338001 176040 2000 (by norm_num) hp_chunk_169
  rw [adv_chunk_169] at h
  have he : 338001 + 2000 - 1 = 340001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_171 : 350876 ≡ 2^(342001-1) [MOD 550172] := by
  have h := advance_sound 340001 307568 2000 (by norm_num) hp_chunk_170
  rw [adv_chunk_170] at h
  have he : 340001 + 2000 - 1 = 342001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_172 : 479196 ≡ 2^(344001-1) [MOD 550172] := by
  have h := advance_sound 342001 350876 2000 (by norm_num) hp_chunk_171
  rw [adv_chunk_171] at h
  have he : 342001 + 2000 - 1 = 344001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_173 : 105464 ≡ 2^(346001-1) [MOD 550172] := by
  have h := advance_sound 344001 479196 2000 (by norm_num) hp_chunk_172
  rw [adv_chunk_172] at h
  have he : 344001 + 2000 - 1 = 346001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_174 : 485612 ≡ 2^(348001-1) [MOD 550172] := by
  have h := advance_sound 346001 105464 2000 (by norm_num) hp_chunk_173
  rw [adv_chunk_173] at h
  have he : 346001 + 2000 - 1 = 348001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_175 : 389372 ≡ 2^(350001-1) [MOD 550172] := by
  have h := advance_sound 348001 485612 2000 (by norm_num) hp_chunk_174
  rw [adv_chunk_174] at h
  have he : 348001 + 2000 - 1 = 350001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_176 : 532128 ≡ 2^(352001-1) [MOD 550172] := by
  have h := advance_sound 350001 389372 2000 (by norm_num) hp_chunk_175
  rw [adv_chunk_175] at h
  have he : 350001 + 2000 - 1 = 352001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_177 : 384560 ≡ 2^(354001-1) [MOD 550172] := by
  have h := advance_sound 352001 532128 2000 (by norm_num) hp_chunk_176
  rw [adv_chunk_176] at h
  have he : 352001 + 2000 - 1 = 354001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_178 : 456740 ≡ 2^(356001-1) [MOD 550172] := by
  have h := advance_sound 354001 384560 2000 (by norm_num) hp_chunk_177
  rw [adv_chunk_177] at h
  have he : 354001 + 2000 - 1 = 356001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_179 : 487216 ≡ 2^(358001-1) [MOD 550172] := by
  have h := advance_sound 356001 456740 2000 (by norm_num) hp_chunk_178
  rw [adv_chunk_178] at h
  have he : 356001 + 2000 - 1 = 358001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_180 : 47720 ≡ 2^(360001-1) [MOD 550172] := by
  have h := advance_sound 358001 487216 2000 (by norm_num) hp_chunk_179
  rw [adv_chunk_179] at h
  have he : 358001 + 2000 - 1 = 360001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_181 : 131128 ≡ 2^(362001-1) [MOD 550172] := by
  have h := advance_sound 360001 47720 2000 (by norm_num) hp_chunk_180
  rw [adv_chunk_180] at h
  have he : 360001 + 2000 - 1 = 362001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_182 : 520900 ≡ 2^(364001-1) [MOD 550172] := by
  have h := advance_sound 362001 131128 2000 (by norm_num) hp_chunk_181
  rw [adv_chunk_181] at h
  have he : 362001 + 2000 - 1 = 364001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_183 : 25264 ≡ 2^(366001-1) [MOD 550172] := by
  have h := advance_sound 364001 520900 2000 (by norm_num) hp_chunk_182
  rw [adv_chunk_182] at h
  have he : 364001 + 2000 - 1 = 366001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_184 : 512880 ≡ 2^(368001-1) [MOD 550172] := by
  have h := advance_sound 366001 25264 2000 (by norm_num) hp_chunk_183
  rw [adv_chunk_183] at h
  have he : 366001 + 2000 - 1 = 368001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_185 : 83008 ≡ 2^(370001-1) [MOD 550172] := by
  have h := advance_sound 368001 512880 2000 (by norm_num) hp_chunk_184
  rw [adv_chunk_184] at h
  have he : 368001 + 2000 - 1 = 370001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_186 : 317192 ≡ 2^(372001-1) [MOD 550172] := by
  have h := advance_sound 370001 83008 2000 (by norm_num) hp_chunk_185
  rw [adv_chunk_185] at h
  have he : 370001 + 2000 - 1 = 372001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_187 : 501652 ≡ 2^(374001-1) [MOD 550172] := by
  have h := advance_sound 372001 317192 2000 (by norm_num) hp_chunk_186
  rw [adv_chunk_186] at h
  have he : 372001 + 2000 - 1 = 374001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_188 : 273884 ≡ 2^(376001-1) [MOD 550172] := by
  have h := advance_sound 374001 501652 2000 (by norm_num) hp_chunk_187
  rw [adv_chunk_187] at h
  have he : 374001 + 2000 - 1 = 376001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_189 : 373332 ≡ 2^(378001-1) [MOD 550172] := by
  have h := advance_sound 376001 273884 2000 (by norm_num) hp_chunk_188
  rw [adv_chunk_188] at h
  have he : 376001 + 2000 - 1 = 378001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_190 : 97444 ≡ 2^(380001-1) [MOD 550172] := by
  have h := advance_sound 378001 373332 2000 (by norm_num) hp_chunk_189
  rw [adv_chunk_189] at h
  have he : 378001 + 2000 - 1 = 380001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_191 : 543356 ≡ 2^(382001-1) [MOD 550172] := by
  have h := advance_sound 380001 97444 2000 (by norm_num) hp_chunk_190
  rw [adv_chunk_190] at h
  have he : 380001 + 2000 - 1 = 382001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_192 : 193684 ≡ 2^(384001-1) [MOD 550172] := by
  have h := advance_sound 382001 543356 2000 (by norm_num) hp_chunk_191
  rw [adv_chunk_191] at h
  have he : 382001 + 2000 - 1 = 384001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_193 : 400600 ≡ 2^(386001-1) [MOD 550172] := by
  have h := advance_sound 384001 193684 2000 (by norm_num) hp_chunk_192
  rw [adv_chunk_192] at h
  have he : 384001 + 2000 - 1 = 386001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_194 : 341252 ≡ 2^(388001-1) [MOD 550172] := by
  have h := advance_sound 386001 400600 2000 (by norm_num) hp_chunk_193
  rw [adv_chunk_193] at h
  have he : 386001 + 2000 - 1 = 388001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_195 : 328420 ≡ 2^(390001-1) [MOD 550172] := by
  have h := advance_sound 388001 341252 2000 (by norm_num) hp_chunk_194
  rw [adv_chunk_194] at h
  have he : 388001 + 2000 - 1 = 390001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_196 : 310776 ≡ 2^(392001-1) [MOD 550172] := by
  have h := advance_sound 390001 328420 2000 (by norm_num) hp_chunk_195
  rw [adv_chunk_195] at h
  have he : 390001 + 2000 - 1 = 392001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_197 : 217744 ≡ 2^(394001-1) [MOD 550172] := by
  have h := advance_sound 392001 310776 2000 (by norm_num) hp_chunk_196
  rw [adv_chunk_196] at h
  have he : 392001 + 2000 - 1 = 394001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_198 : 227368 ≡ 2^(396001-1) [MOD 550172] := by
  have h := advance_sound 394001 217744 2000 (by norm_num) hp_chunk_197
  rw [adv_chunk_197] at h
  have he : 394001 + 2000 - 1 = 396001 - 1 := by norm_num
  rwa [he] at h
opaque hp_chunk_199 : 378144 ≡ 2^(398001-1) [MOD 550172] := by
  have h := advance_sound 396001 227368 2000 (by norm_num) hp_chunk_198
  rw [adv_chunk_198] at h
  have he : 396001 + 2000 - 1 = 398001 - 1 := by norm_num
  rwa [he] at h
