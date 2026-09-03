import FormalConjecturesUtil

/-! A finite periodic sieve certificate for squared Gaussian steps of size two. -/

namespace Erdos952Investigation

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def sieveNorm (u v : ℤ) : ℤ := (1 + u + v)^2 + (u - v)^2

def sieveAllowed (u v : Fin 195) : Prop :=
  sieveNorm u.val v.val % 3 ≠ 0 ∧
  sieveNorm u.val v.val % 5 ≠ 0 ∧
  sieveNorm u.val v.val % 13 ≠ 0

instance (u v : Fin 195) : Decidable (sieveAllowed u v) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def correctionBits : ℕ → ℕ
  | 188 => 21454937572122444017016858380104328570662347710570444800
  | 189 => 6129982163463555433433388108601236734474956488734412800
  | 190 => 6129982163463555433433393184155397804534083575143731200
  | 191 => 21454937589338619310285113912845543242575661104036329472
  | 192 => 183899464938316712844339267446119218398308481530937216768
  | 193 => 116661790128445654987965041169961849085063268091075631360
  | 194 => 27715453750929707627951001544017439248060547367219465179825
  | _ => 0

def sieveLift (u v : Fin 195) : ℤ :=
  u.val - if (correctionBits u.val).testBit v.val then 195 else 0

private lemma sieve_certificate_row_0 : ∀ v : Fin 195,
    sieveAllowed 0 v → sieveAllowed (0 + 1) v →
    sieveLift (0 + 1) v = sieveLift 0 v + 1 ∧
      sieveLift v (0 + 1) = sieveLift v 0 := by
  decide +kernel

private lemma sieve_certificate_row_1 : ∀ v : Fin 195,
    sieveAllowed 1 v → sieveAllowed (1 + 1) v →
    sieveLift (1 + 1) v = sieveLift 1 v + 1 ∧
      sieveLift v (1 + 1) = sieveLift v 1 := by
  decide +kernel

private lemma sieve_certificate_row_2 : ∀ v : Fin 195,
    sieveAllowed 2 v → sieveAllowed (2 + 1) v →
    sieveLift (2 + 1) v = sieveLift 2 v + 1 ∧
      sieveLift v (2 + 1) = sieveLift v 2 := by
  decide +kernel

private lemma sieve_certificate_row_3 : ∀ v : Fin 195,
    sieveAllowed 3 v → sieveAllowed (3 + 1) v →
    sieveLift (3 + 1) v = sieveLift 3 v + 1 ∧
      sieveLift v (3 + 1) = sieveLift v 3 := by
  decide +kernel

private lemma sieve_certificate_row_4 : ∀ v : Fin 195,
    sieveAllowed 4 v → sieveAllowed (4 + 1) v →
    sieveLift (4 + 1) v = sieveLift 4 v + 1 ∧
      sieveLift v (4 + 1) = sieveLift v 4 := by
  decide +kernel

private lemma sieve_certificate_row_5 : ∀ v : Fin 195,
    sieveAllowed 5 v → sieveAllowed (5 + 1) v →
    sieveLift (5 + 1) v = sieveLift 5 v + 1 ∧
      sieveLift v (5 + 1) = sieveLift v 5 := by
  decide +kernel

private lemma sieve_certificate_row_6 : ∀ v : Fin 195,
    sieveAllowed 6 v → sieveAllowed (6 + 1) v →
    sieveLift (6 + 1) v = sieveLift 6 v + 1 ∧
      sieveLift v (6 + 1) = sieveLift v 6 := by
  decide +kernel

private lemma sieve_certificate_row_7 : ∀ v : Fin 195,
    sieveAllowed 7 v → sieveAllowed (7 + 1) v →
    sieveLift (7 + 1) v = sieveLift 7 v + 1 ∧
      sieveLift v (7 + 1) = sieveLift v 7 := by
  decide +kernel

private lemma sieve_certificate_row_8 : ∀ v : Fin 195,
    sieveAllowed 8 v → sieveAllowed (8 + 1) v →
    sieveLift (8 + 1) v = sieveLift 8 v + 1 ∧
      sieveLift v (8 + 1) = sieveLift v 8 := by
  decide +kernel

private lemma sieve_certificate_row_9 : ∀ v : Fin 195,
    sieveAllowed 9 v → sieveAllowed (9 + 1) v →
    sieveLift (9 + 1) v = sieveLift 9 v + 1 ∧
      sieveLift v (9 + 1) = sieveLift v 9 := by
  decide +kernel

private lemma sieve_certificate_row_10 : ∀ v : Fin 195,
    sieveAllowed 10 v → sieveAllowed (10 + 1) v →
    sieveLift (10 + 1) v = sieveLift 10 v + 1 ∧
      sieveLift v (10 + 1) = sieveLift v 10 := by
  decide +kernel

private lemma sieve_certificate_row_11 : ∀ v : Fin 195,
    sieveAllowed 11 v → sieveAllowed (11 + 1) v →
    sieveLift (11 + 1) v = sieveLift 11 v + 1 ∧
      sieveLift v (11 + 1) = sieveLift v 11 := by
  decide +kernel

private lemma sieve_certificate_row_12 : ∀ v : Fin 195,
    sieveAllowed 12 v → sieveAllowed (12 + 1) v →
    sieveLift (12 + 1) v = sieveLift 12 v + 1 ∧
      sieveLift v (12 + 1) = sieveLift v 12 := by
  decide +kernel

private lemma sieve_certificate_row_13 : ∀ v : Fin 195,
    sieveAllowed 13 v → sieveAllowed (13 + 1) v →
    sieveLift (13 + 1) v = sieveLift 13 v + 1 ∧
      sieveLift v (13 + 1) = sieveLift v 13 := by
  decide +kernel

private lemma sieve_certificate_row_14 : ∀ v : Fin 195,
    sieveAllowed 14 v → sieveAllowed (14 + 1) v →
    sieveLift (14 + 1) v = sieveLift 14 v + 1 ∧
      sieveLift v (14 + 1) = sieveLift v 14 := by
  decide +kernel

private lemma sieve_certificate_row_15 : ∀ v : Fin 195,
    sieveAllowed 15 v → sieveAllowed (15 + 1) v →
    sieveLift (15 + 1) v = sieveLift 15 v + 1 ∧
      sieveLift v (15 + 1) = sieveLift v 15 := by
  decide +kernel

private lemma sieve_certificate_row_16 : ∀ v : Fin 195,
    sieveAllowed 16 v → sieveAllowed (16 + 1) v →
    sieveLift (16 + 1) v = sieveLift 16 v + 1 ∧
      sieveLift v (16 + 1) = sieveLift v 16 := by
  decide +kernel

private lemma sieve_certificate_row_17 : ∀ v : Fin 195,
    sieveAllowed 17 v → sieveAllowed (17 + 1) v →
    sieveLift (17 + 1) v = sieveLift 17 v + 1 ∧
      sieveLift v (17 + 1) = sieveLift v 17 := by
  decide +kernel

private lemma sieve_certificate_row_18 : ∀ v : Fin 195,
    sieveAllowed 18 v → sieveAllowed (18 + 1) v →
    sieveLift (18 + 1) v = sieveLift 18 v + 1 ∧
      sieveLift v (18 + 1) = sieveLift v 18 := by
  decide +kernel

private lemma sieve_certificate_row_19 : ∀ v : Fin 195,
    sieveAllowed 19 v → sieveAllowed (19 + 1) v →
    sieveLift (19 + 1) v = sieveLift 19 v + 1 ∧
      sieveLift v (19 + 1) = sieveLift v 19 := by
  decide +kernel

private lemma sieve_certificate_row_20 : ∀ v : Fin 195,
    sieveAllowed 20 v → sieveAllowed (20 + 1) v →
    sieveLift (20 + 1) v = sieveLift 20 v + 1 ∧
      sieveLift v (20 + 1) = sieveLift v 20 := by
  decide +kernel

private lemma sieve_certificate_row_21 : ∀ v : Fin 195,
    sieveAllowed 21 v → sieveAllowed (21 + 1) v →
    sieveLift (21 + 1) v = sieveLift 21 v + 1 ∧
      sieveLift v (21 + 1) = sieveLift v 21 := by
  decide +kernel

private lemma sieve_certificate_row_22 : ∀ v : Fin 195,
    sieveAllowed 22 v → sieveAllowed (22 + 1) v →
    sieveLift (22 + 1) v = sieveLift 22 v + 1 ∧
      sieveLift v (22 + 1) = sieveLift v 22 := by
  decide +kernel

private lemma sieve_certificate_row_23 : ∀ v : Fin 195,
    sieveAllowed 23 v → sieveAllowed (23 + 1) v →
    sieveLift (23 + 1) v = sieveLift 23 v + 1 ∧
      sieveLift v (23 + 1) = sieveLift v 23 := by
  decide +kernel

private lemma sieve_certificate_row_24 : ∀ v : Fin 195,
    sieveAllowed 24 v → sieveAllowed (24 + 1) v →
    sieveLift (24 + 1) v = sieveLift 24 v + 1 ∧
      sieveLift v (24 + 1) = sieveLift v 24 := by
  decide +kernel

private lemma sieve_certificate_row_25 : ∀ v : Fin 195,
    sieveAllowed 25 v → sieveAllowed (25 + 1) v →
    sieveLift (25 + 1) v = sieveLift 25 v + 1 ∧
      sieveLift v (25 + 1) = sieveLift v 25 := by
  decide +kernel

private lemma sieve_certificate_row_26 : ∀ v : Fin 195,
    sieveAllowed 26 v → sieveAllowed (26 + 1) v →
    sieveLift (26 + 1) v = sieveLift 26 v + 1 ∧
      sieveLift v (26 + 1) = sieveLift v 26 := by
  decide +kernel

private lemma sieve_certificate_row_27 : ∀ v : Fin 195,
    sieveAllowed 27 v → sieveAllowed (27 + 1) v →
    sieveLift (27 + 1) v = sieveLift 27 v + 1 ∧
      sieveLift v (27 + 1) = sieveLift v 27 := by
  decide +kernel

private lemma sieve_certificate_row_28 : ∀ v : Fin 195,
    sieveAllowed 28 v → sieveAllowed (28 + 1) v →
    sieveLift (28 + 1) v = sieveLift 28 v + 1 ∧
      sieveLift v (28 + 1) = sieveLift v 28 := by
  decide +kernel

private lemma sieve_certificate_row_29 : ∀ v : Fin 195,
    sieveAllowed 29 v → sieveAllowed (29 + 1) v →
    sieveLift (29 + 1) v = sieveLift 29 v + 1 ∧
      sieveLift v (29 + 1) = sieveLift v 29 := by
  decide +kernel

private lemma sieve_certificate_row_30 : ∀ v : Fin 195,
    sieveAllowed 30 v → sieveAllowed (30 + 1) v →
    sieveLift (30 + 1) v = sieveLift 30 v + 1 ∧
      sieveLift v (30 + 1) = sieveLift v 30 := by
  decide +kernel

private lemma sieve_certificate_row_31 : ∀ v : Fin 195,
    sieveAllowed 31 v → sieveAllowed (31 + 1) v →
    sieveLift (31 + 1) v = sieveLift 31 v + 1 ∧
      sieveLift v (31 + 1) = sieveLift v 31 := by
  decide +kernel

private lemma sieve_certificate_row_32 : ∀ v : Fin 195,
    sieveAllowed 32 v → sieveAllowed (32 + 1) v →
    sieveLift (32 + 1) v = sieveLift 32 v + 1 ∧
      sieveLift v (32 + 1) = sieveLift v 32 := by
  decide +kernel

private lemma sieve_certificate_row_33 : ∀ v : Fin 195,
    sieveAllowed 33 v → sieveAllowed (33 + 1) v →
    sieveLift (33 + 1) v = sieveLift 33 v + 1 ∧
      sieveLift v (33 + 1) = sieveLift v 33 := by
  decide +kernel

private lemma sieve_certificate_row_34 : ∀ v : Fin 195,
    sieveAllowed 34 v → sieveAllowed (34 + 1) v →
    sieveLift (34 + 1) v = sieveLift 34 v + 1 ∧
      sieveLift v (34 + 1) = sieveLift v 34 := by
  decide +kernel

private lemma sieve_certificate_row_35 : ∀ v : Fin 195,
    sieveAllowed 35 v → sieveAllowed (35 + 1) v →
    sieveLift (35 + 1) v = sieveLift 35 v + 1 ∧
      sieveLift v (35 + 1) = sieveLift v 35 := by
  decide +kernel

private lemma sieve_certificate_row_36 : ∀ v : Fin 195,
    sieveAllowed 36 v → sieveAllowed (36 + 1) v →
    sieveLift (36 + 1) v = sieveLift 36 v + 1 ∧
      sieveLift v (36 + 1) = sieveLift v 36 := by
  decide +kernel

private lemma sieve_certificate_row_37 : ∀ v : Fin 195,
    sieveAllowed 37 v → sieveAllowed (37 + 1) v →
    sieveLift (37 + 1) v = sieveLift 37 v + 1 ∧
      sieveLift v (37 + 1) = sieveLift v 37 := by
  decide +kernel

private lemma sieve_certificate_row_38 : ∀ v : Fin 195,
    sieveAllowed 38 v → sieveAllowed (38 + 1) v →
    sieveLift (38 + 1) v = sieveLift 38 v + 1 ∧
      sieveLift v (38 + 1) = sieveLift v 38 := by
  decide +kernel

private lemma sieve_certificate_row_39 : ∀ v : Fin 195,
    sieveAllowed 39 v → sieveAllowed (39 + 1) v →
    sieveLift (39 + 1) v = sieveLift 39 v + 1 ∧
      sieveLift v (39 + 1) = sieveLift v 39 := by
  decide +kernel

private lemma sieve_certificate_row_40 : ∀ v : Fin 195,
    sieveAllowed 40 v → sieveAllowed (40 + 1) v →
    sieveLift (40 + 1) v = sieveLift 40 v + 1 ∧
      sieveLift v (40 + 1) = sieveLift v 40 := by
  decide +kernel

private lemma sieve_certificate_row_41 : ∀ v : Fin 195,
    sieveAllowed 41 v → sieveAllowed (41 + 1) v →
    sieveLift (41 + 1) v = sieveLift 41 v + 1 ∧
      sieveLift v (41 + 1) = sieveLift v 41 := by
  decide +kernel

private lemma sieve_certificate_row_42 : ∀ v : Fin 195,
    sieveAllowed 42 v → sieveAllowed (42 + 1) v →
    sieveLift (42 + 1) v = sieveLift 42 v + 1 ∧
      sieveLift v (42 + 1) = sieveLift v 42 := by
  decide +kernel

private lemma sieve_certificate_row_43 : ∀ v : Fin 195,
    sieveAllowed 43 v → sieveAllowed (43 + 1) v →
    sieveLift (43 + 1) v = sieveLift 43 v + 1 ∧
      sieveLift v (43 + 1) = sieveLift v 43 := by
  decide +kernel

private lemma sieve_certificate_row_44 : ∀ v : Fin 195,
    sieveAllowed 44 v → sieveAllowed (44 + 1) v →
    sieveLift (44 + 1) v = sieveLift 44 v + 1 ∧
      sieveLift v (44 + 1) = sieveLift v 44 := by
  decide +kernel

private lemma sieve_certificate_row_45 : ∀ v : Fin 195,
    sieveAllowed 45 v → sieveAllowed (45 + 1) v →
    sieveLift (45 + 1) v = sieveLift 45 v + 1 ∧
      sieveLift v (45 + 1) = sieveLift v 45 := by
  decide +kernel

private lemma sieve_certificate_row_46 : ∀ v : Fin 195,
    sieveAllowed 46 v → sieveAllowed (46 + 1) v →
    sieveLift (46 + 1) v = sieveLift 46 v + 1 ∧
      sieveLift v (46 + 1) = sieveLift v 46 := by
  decide +kernel

private lemma sieve_certificate_row_47 : ∀ v : Fin 195,
    sieveAllowed 47 v → sieveAllowed (47 + 1) v →
    sieveLift (47 + 1) v = sieveLift 47 v + 1 ∧
      sieveLift v (47 + 1) = sieveLift v 47 := by
  decide +kernel

private lemma sieve_certificate_row_48 : ∀ v : Fin 195,
    sieveAllowed 48 v → sieveAllowed (48 + 1) v →
    sieveLift (48 + 1) v = sieveLift 48 v + 1 ∧
      sieveLift v (48 + 1) = sieveLift v 48 := by
  decide +kernel

private lemma sieve_certificate_row_49 : ∀ v : Fin 195,
    sieveAllowed 49 v → sieveAllowed (49 + 1) v →
    sieveLift (49 + 1) v = sieveLift 49 v + 1 ∧
      sieveLift v (49 + 1) = sieveLift v 49 := by
  decide +kernel

private lemma sieve_certificate_row_50 : ∀ v : Fin 195,
    sieveAllowed 50 v → sieveAllowed (50 + 1) v →
    sieveLift (50 + 1) v = sieveLift 50 v + 1 ∧
      sieveLift v (50 + 1) = sieveLift v 50 := by
  decide +kernel

private lemma sieve_certificate_row_51 : ∀ v : Fin 195,
    sieveAllowed 51 v → sieveAllowed (51 + 1) v →
    sieveLift (51 + 1) v = sieveLift 51 v + 1 ∧
      sieveLift v (51 + 1) = sieveLift v 51 := by
  decide +kernel

private lemma sieve_certificate_row_52 : ∀ v : Fin 195,
    sieveAllowed 52 v → sieveAllowed (52 + 1) v →
    sieveLift (52 + 1) v = sieveLift 52 v + 1 ∧
      sieveLift v (52 + 1) = sieveLift v 52 := by
  decide +kernel

private lemma sieve_certificate_row_53 : ∀ v : Fin 195,
    sieveAllowed 53 v → sieveAllowed (53 + 1) v →
    sieveLift (53 + 1) v = sieveLift 53 v + 1 ∧
      sieveLift v (53 + 1) = sieveLift v 53 := by
  decide +kernel

private lemma sieve_certificate_row_54 : ∀ v : Fin 195,
    sieveAllowed 54 v → sieveAllowed (54 + 1) v →
    sieveLift (54 + 1) v = sieveLift 54 v + 1 ∧
      sieveLift v (54 + 1) = sieveLift v 54 := by
  decide +kernel

private lemma sieve_certificate_row_55 : ∀ v : Fin 195,
    sieveAllowed 55 v → sieveAllowed (55 + 1) v →
    sieveLift (55 + 1) v = sieveLift 55 v + 1 ∧
      sieveLift v (55 + 1) = sieveLift v 55 := by
  decide +kernel

private lemma sieve_certificate_row_56 : ∀ v : Fin 195,
    sieveAllowed 56 v → sieveAllowed (56 + 1) v →
    sieveLift (56 + 1) v = sieveLift 56 v + 1 ∧
      sieveLift v (56 + 1) = sieveLift v 56 := by
  decide +kernel

private lemma sieve_certificate_row_57 : ∀ v : Fin 195,
    sieveAllowed 57 v → sieveAllowed (57 + 1) v →
    sieveLift (57 + 1) v = sieveLift 57 v + 1 ∧
      sieveLift v (57 + 1) = sieveLift v 57 := by
  decide +kernel

private lemma sieve_certificate_row_58 : ∀ v : Fin 195,
    sieveAllowed 58 v → sieveAllowed (58 + 1) v →
    sieveLift (58 + 1) v = sieveLift 58 v + 1 ∧
      sieveLift v (58 + 1) = sieveLift v 58 := by
  decide +kernel

private lemma sieve_certificate_row_59 : ∀ v : Fin 195,
    sieveAllowed 59 v → sieveAllowed (59 + 1) v →
    sieveLift (59 + 1) v = sieveLift 59 v + 1 ∧
      sieveLift v (59 + 1) = sieveLift v 59 := by
  decide +kernel

private lemma sieve_certificate_row_60 : ∀ v : Fin 195,
    sieveAllowed 60 v → sieveAllowed (60 + 1) v →
    sieveLift (60 + 1) v = sieveLift 60 v + 1 ∧
      sieveLift v (60 + 1) = sieveLift v 60 := by
  decide +kernel

private lemma sieve_certificate_row_61 : ∀ v : Fin 195,
    sieveAllowed 61 v → sieveAllowed (61 + 1) v →
    sieveLift (61 + 1) v = sieveLift 61 v + 1 ∧
      sieveLift v (61 + 1) = sieveLift v 61 := by
  decide +kernel

private lemma sieve_certificate_row_62 : ∀ v : Fin 195,
    sieveAllowed 62 v → sieveAllowed (62 + 1) v →
    sieveLift (62 + 1) v = sieveLift 62 v + 1 ∧
      sieveLift v (62 + 1) = sieveLift v 62 := by
  decide +kernel

private lemma sieve_certificate_row_63 : ∀ v : Fin 195,
    sieveAllowed 63 v → sieveAllowed (63 + 1) v →
    sieveLift (63 + 1) v = sieveLift 63 v + 1 ∧
      sieveLift v (63 + 1) = sieveLift v 63 := by
  decide +kernel

private lemma sieve_certificate_row_64 : ∀ v : Fin 195,
    sieveAllowed 64 v → sieveAllowed (64 + 1) v →
    sieveLift (64 + 1) v = sieveLift 64 v + 1 ∧
      sieveLift v (64 + 1) = sieveLift v 64 := by
  decide +kernel

private lemma sieve_certificate_row_65 : ∀ v : Fin 195,
    sieveAllowed 65 v → sieveAllowed (65 + 1) v →
    sieveLift (65 + 1) v = sieveLift 65 v + 1 ∧
      sieveLift v (65 + 1) = sieveLift v 65 := by
  decide +kernel

private lemma sieve_certificate_row_66 : ∀ v : Fin 195,
    sieveAllowed 66 v → sieveAllowed (66 + 1) v →
    sieveLift (66 + 1) v = sieveLift 66 v + 1 ∧
      sieveLift v (66 + 1) = sieveLift v 66 := by
  decide +kernel

private lemma sieve_certificate_row_67 : ∀ v : Fin 195,
    sieveAllowed 67 v → sieveAllowed (67 + 1) v →
    sieveLift (67 + 1) v = sieveLift 67 v + 1 ∧
      sieveLift v (67 + 1) = sieveLift v 67 := by
  decide +kernel

private lemma sieve_certificate_row_68 : ∀ v : Fin 195,
    sieveAllowed 68 v → sieveAllowed (68 + 1) v →
    sieveLift (68 + 1) v = sieveLift 68 v + 1 ∧
      sieveLift v (68 + 1) = sieveLift v 68 := by
  decide +kernel

private lemma sieve_certificate_row_69 : ∀ v : Fin 195,
    sieveAllowed 69 v → sieveAllowed (69 + 1) v →
    sieveLift (69 + 1) v = sieveLift 69 v + 1 ∧
      sieveLift v (69 + 1) = sieveLift v 69 := by
  decide +kernel

private lemma sieve_certificate_row_70 : ∀ v : Fin 195,
    sieveAllowed 70 v → sieveAllowed (70 + 1) v →
    sieveLift (70 + 1) v = sieveLift 70 v + 1 ∧
      sieveLift v (70 + 1) = sieveLift v 70 := by
  decide +kernel

private lemma sieve_certificate_row_71 : ∀ v : Fin 195,
    sieveAllowed 71 v → sieveAllowed (71 + 1) v →
    sieveLift (71 + 1) v = sieveLift 71 v + 1 ∧
      sieveLift v (71 + 1) = sieveLift v 71 := by
  decide +kernel

private lemma sieve_certificate_row_72 : ∀ v : Fin 195,
    sieveAllowed 72 v → sieveAllowed (72 + 1) v →
    sieveLift (72 + 1) v = sieveLift 72 v + 1 ∧
      sieveLift v (72 + 1) = sieveLift v 72 := by
  decide +kernel

private lemma sieve_certificate_row_73 : ∀ v : Fin 195,
    sieveAllowed 73 v → sieveAllowed (73 + 1) v →
    sieveLift (73 + 1) v = sieveLift 73 v + 1 ∧
      sieveLift v (73 + 1) = sieveLift v 73 := by
  decide +kernel

private lemma sieve_certificate_row_74 : ∀ v : Fin 195,
    sieveAllowed 74 v → sieveAllowed (74 + 1) v →
    sieveLift (74 + 1) v = sieveLift 74 v + 1 ∧
      sieveLift v (74 + 1) = sieveLift v 74 := by
  decide +kernel

private lemma sieve_certificate_row_75 : ∀ v : Fin 195,
    sieveAllowed 75 v → sieveAllowed (75 + 1) v →
    sieveLift (75 + 1) v = sieveLift 75 v + 1 ∧
      sieveLift v (75 + 1) = sieveLift v 75 := by
  decide +kernel

private lemma sieve_certificate_row_76 : ∀ v : Fin 195,
    sieveAllowed 76 v → sieveAllowed (76 + 1) v →
    sieveLift (76 + 1) v = sieveLift 76 v + 1 ∧
      sieveLift v (76 + 1) = sieveLift v 76 := by
  decide +kernel

private lemma sieve_certificate_row_77 : ∀ v : Fin 195,
    sieveAllowed 77 v → sieveAllowed (77 + 1) v →
    sieveLift (77 + 1) v = sieveLift 77 v + 1 ∧
      sieveLift v (77 + 1) = sieveLift v 77 := by
  decide +kernel

private lemma sieve_certificate_row_78 : ∀ v : Fin 195,
    sieveAllowed 78 v → sieveAllowed (78 + 1) v →
    sieveLift (78 + 1) v = sieveLift 78 v + 1 ∧
      sieveLift v (78 + 1) = sieveLift v 78 := by
  decide +kernel

private lemma sieve_certificate_row_79 : ∀ v : Fin 195,
    sieveAllowed 79 v → sieveAllowed (79 + 1) v →
    sieveLift (79 + 1) v = sieveLift 79 v + 1 ∧
      sieveLift v (79 + 1) = sieveLift v 79 := by
  decide +kernel

private lemma sieve_certificate_row_80 : ∀ v : Fin 195,
    sieveAllowed 80 v → sieveAllowed (80 + 1) v →
    sieveLift (80 + 1) v = sieveLift 80 v + 1 ∧
      sieveLift v (80 + 1) = sieveLift v 80 := by
  decide +kernel

private lemma sieve_certificate_row_81 : ∀ v : Fin 195,
    sieveAllowed 81 v → sieveAllowed (81 + 1) v →
    sieveLift (81 + 1) v = sieveLift 81 v + 1 ∧
      sieveLift v (81 + 1) = sieveLift v 81 := by
  decide +kernel

private lemma sieve_certificate_row_82 : ∀ v : Fin 195,
    sieveAllowed 82 v → sieveAllowed (82 + 1) v →
    sieveLift (82 + 1) v = sieveLift 82 v + 1 ∧
      sieveLift v (82 + 1) = sieveLift v 82 := by
  decide +kernel

private lemma sieve_certificate_row_83 : ∀ v : Fin 195,
    sieveAllowed 83 v → sieveAllowed (83 + 1) v →
    sieveLift (83 + 1) v = sieveLift 83 v + 1 ∧
      sieveLift v (83 + 1) = sieveLift v 83 := by
  decide +kernel

private lemma sieve_certificate_row_84 : ∀ v : Fin 195,
    sieveAllowed 84 v → sieveAllowed (84 + 1) v →
    sieveLift (84 + 1) v = sieveLift 84 v + 1 ∧
      sieveLift v (84 + 1) = sieveLift v 84 := by
  decide +kernel

private lemma sieve_certificate_row_85 : ∀ v : Fin 195,
    sieveAllowed 85 v → sieveAllowed (85 + 1) v →
    sieveLift (85 + 1) v = sieveLift 85 v + 1 ∧
      sieveLift v (85 + 1) = sieveLift v 85 := by
  decide +kernel

private lemma sieve_certificate_row_86 : ∀ v : Fin 195,
    sieveAllowed 86 v → sieveAllowed (86 + 1) v →
    sieveLift (86 + 1) v = sieveLift 86 v + 1 ∧
      sieveLift v (86 + 1) = sieveLift v 86 := by
  decide +kernel

private lemma sieve_certificate_row_87 : ∀ v : Fin 195,
    sieveAllowed 87 v → sieveAllowed (87 + 1) v →
    sieveLift (87 + 1) v = sieveLift 87 v + 1 ∧
      sieveLift v (87 + 1) = sieveLift v 87 := by
  decide +kernel

private lemma sieve_certificate_row_88 : ∀ v : Fin 195,
    sieveAllowed 88 v → sieveAllowed (88 + 1) v →
    sieveLift (88 + 1) v = sieveLift 88 v + 1 ∧
      sieveLift v (88 + 1) = sieveLift v 88 := by
  decide +kernel

private lemma sieve_certificate_row_89 : ∀ v : Fin 195,
    sieveAllowed 89 v → sieveAllowed (89 + 1) v →
    sieveLift (89 + 1) v = sieveLift 89 v + 1 ∧
      sieveLift v (89 + 1) = sieveLift v 89 := by
  decide +kernel

private lemma sieve_certificate_row_90 : ∀ v : Fin 195,
    sieveAllowed 90 v → sieveAllowed (90 + 1) v →
    sieveLift (90 + 1) v = sieveLift 90 v + 1 ∧
      sieveLift v (90 + 1) = sieveLift v 90 := by
  decide +kernel

private lemma sieve_certificate_row_91 : ∀ v : Fin 195,
    sieveAllowed 91 v → sieveAllowed (91 + 1) v →
    sieveLift (91 + 1) v = sieveLift 91 v + 1 ∧
      sieveLift v (91 + 1) = sieveLift v 91 := by
  decide +kernel

private lemma sieve_certificate_row_92 : ∀ v : Fin 195,
    sieveAllowed 92 v → sieveAllowed (92 + 1) v →
    sieveLift (92 + 1) v = sieveLift 92 v + 1 ∧
      sieveLift v (92 + 1) = sieveLift v 92 := by
  decide +kernel

private lemma sieve_certificate_row_93 : ∀ v : Fin 195,
    sieveAllowed 93 v → sieveAllowed (93 + 1) v →
    sieveLift (93 + 1) v = sieveLift 93 v + 1 ∧
      sieveLift v (93 + 1) = sieveLift v 93 := by
  decide +kernel

private lemma sieve_certificate_row_94 : ∀ v : Fin 195,
    sieveAllowed 94 v → sieveAllowed (94 + 1) v →
    sieveLift (94 + 1) v = sieveLift 94 v + 1 ∧
      sieveLift v (94 + 1) = sieveLift v 94 := by
  decide +kernel

private lemma sieve_certificate_row_95 : ∀ v : Fin 195,
    sieveAllowed 95 v → sieveAllowed (95 + 1) v →
    sieveLift (95 + 1) v = sieveLift 95 v + 1 ∧
      sieveLift v (95 + 1) = sieveLift v 95 := by
  decide +kernel

private lemma sieve_certificate_row_96 : ∀ v : Fin 195,
    sieveAllowed 96 v → sieveAllowed (96 + 1) v →
    sieveLift (96 + 1) v = sieveLift 96 v + 1 ∧
      sieveLift v (96 + 1) = sieveLift v 96 := by
  decide +kernel

private lemma sieve_certificate_row_97 : ∀ v : Fin 195,
    sieveAllowed 97 v → sieveAllowed (97 + 1) v →
    sieveLift (97 + 1) v = sieveLift 97 v + 1 ∧
      sieveLift v (97 + 1) = sieveLift v 97 := by
  decide +kernel

private lemma sieve_certificate_row_98 : ∀ v : Fin 195,
    sieveAllowed 98 v → sieveAllowed (98 + 1) v →
    sieveLift (98 + 1) v = sieveLift 98 v + 1 ∧
      sieveLift v (98 + 1) = sieveLift v 98 := by
  decide +kernel

private lemma sieve_certificate_row_99 : ∀ v : Fin 195,
    sieveAllowed 99 v → sieveAllowed (99 + 1) v →
    sieveLift (99 + 1) v = sieveLift 99 v + 1 ∧
      sieveLift v (99 + 1) = sieveLift v 99 := by
  decide +kernel

private lemma sieve_certificate_row_100 : ∀ v : Fin 195,
    sieveAllowed 100 v → sieveAllowed (100 + 1) v →
    sieveLift (100 + 1) v = sieveLift 100 v + 1 ∧
      sieveLift v (100 + 1) = sieveLift v 100 := by
  decide +kernel

private lemma sieve_certificate_row_101 : ∀ v : Fin 195,
    sieveAllowed 101 v → sieveAllowed (101 + 1) v →
    sieveLift (101 + 1) v = sieveLift 101 v + 1 ∧
      sieveLift v (101 + 1) = sieveLift v 101 := by
  decide +kernel

private lemma sieve_certificate_row_102 : ∀ v : Fin 195,
    sieveAllowed 102 v → sieveAllowed (102 + 1) v →
    sieveLift (102 + 1) v = sieveLift 102 v + 1 ∧
      sieveLift v (102 + 1) = sieveLift v 102 := by
  decide +kernel

private lemma sieve_certificate_row_103 : ∀ v : Fin 195,
    sieveAllowed 103 v → sieveAllowed (103 + 1) v →
    sieveLift (103 + 1) v = sieveLift 103 v + 1 ∧
      sieveLift v (103 + 1) = sieveLift v 103 := by
  decide +kernel

private lemma sieve_certificate_row_104 : ∀ v : Fin 195,
    sieveAllowed 104 v → sieveAllowed (104 + 1) v →
    sieveLift (104 + 1) v = sieveLift 104 v + 1 ∧
      sieveLift v (104 + 1) = sieveLift v 104 := by
  decide +kernel

private lemma sieve_certificate_row_105 : ∀ v : Fin 195,
    sieveAllowed 105 v → sieveAllowed (105 + 1) v →
    sieveLift (105 + 1) v = sieveLift 105 v + 1 ∧
      sieveLift v (105 + 1) = sieveLift v 105 := by
  decide +kernel

private lemma sieve_certificate_row_106 : ∀ v : Fin 195,
    sieveAllowed 106 v → sieveAllowed (106 + 1) v →
    sieveLift (106 + 1) v = sieveLift 106 v + 1 ∧
      sieveLift v (106 + 1) = sieveLift v 106 := by
  decide +kernel

private lemma sieve_certificate_row_107 : ∀ v : Fin 195,
    sieveAllowed 107 v → sieveAllowed (107 + 1) v →
    sieveLift (107 + 1) v = sieveLift 107 v + 1 ∧
      sieveLift v (107 + 1) = sieveLift v 107 := by
  decide +kernel

private lemma sieve_certificate_row_108 : ∀ v : Fin 195,
    sieveAllowed 108 v → sieveAllowed (108 + 1) v →
    sieveLift (108 + 1) v = sieveLift 108 v + 1 ∧
      sieveLift v (108 + 1) = sieveLift v 108 := by
  decide +kernel

private lemma sieve_certificate_row_109 : ∀ v : Fin 195,
    sieveAllowed 109 v → sieveAllowed (109 + 1) v →
    sieveLift (109 + 1) v = sieveLift 109 v + 1 ∧
      sieveLift v (109 + 1) = sieveLift v 109 := by
  decide +kernel

private lemma sieve_certificate_row_110 : ∀ v : Fin 195,
    sieveAllowed 110 v → sieveAllowed (110 + 1) v →
    sieveLift (110 + 1) v = sieveLift 110 v + 1 ∧
      sieveLift v (110 + 1) = sieveLift v 110 := by
  decide +kernel

private lemma sieve_certificate_row_111 : ∀ v : Fin 195,
    sieveAllowed 111 v → sieveAllowed (111 + 1) v →
    sieveLift (111 + 1) v = sieveLift 111 v + 1 ∧
      sieveLift v (111 + 1) = sieveLift v 111 := by
  decide +kernel

private lemma sieve_certificate_row_112 : ∀ v : Fin 195,
    sieveAllowed 112 v → sieveAllowed (112 + 1) v →
    sieveLift (112 + 1) v = sieveLift 112 v + 1 ∧
      sieveLift v (112 + 1) = sieveLift v 112 := by
  decide +kernel

private lemma sieve_certificate_row_113 : ∀ v : Fin 195,
    sieveAllowed 113 v → sieveAllowed (113 + 1) v →
    sieveLift (113 + 1) v = sieveLift 113 v + 1 ∧
      sieveLift v (113 + 1) = sieveLift v 113 := by
  decide +kernel

private lemma sieve_certificate_row_114 : ∀ v : Fin 195,
    sieveAllowed 114 v → sieveAllowed (114 + 1) v →
    sieveLift (114 + 1) v = sieveLift 114 v + 1 ∧
      sieveLift v (114 + 1) = sieveLift v 114 := by
  decide +kernel

private lemma sieve_certificate_row_115 : ∀ v : Fin 195,
    sieveAllowed 115 v → sieveAllowed (115 + 1) v →
    sieveLift (115 + 1) v = sieveLift 115 v + 1 ∧
      sieveLift v (115 + 1) = sieveLift v 115 := by
  decide +kernel

private lemma sieve_certificate_row_116 : ∀ v : Fin 195,
    sieveAllowed 116 v → sieveAllowed (116 + 1) v →
    sieveLift (116 + 1) v = sieveLift 116 v + 1 ∧
      sieveLift v (116 + 1) = sieveLift v 116 := by
  decide +kernel

private lemma sieve_certificate_row_117 : ∀ v : Fin 195,
    sieveAllowed 117 v → sieveAllowed (117 + 1) v →
    sieveLift (117 + 1) v = sieveLift 117 v + 1 ∧
      sieveLift v (117 + 1) = sieveLift v 117 := by
  decide +kernel

private lemma sieve_certificate_row_118 : ∀ v : Fin 195,
    sieveAllowed 118 v → sieveAllowed (118 + 1) v →
    sieveLift (118 + 1) v = sieveLift 118 v + 1 ∧
      sieveLift v (118 + 1) = sieveLift v 118 := by
  decide +kernel

private lemma sieve_certificate_row_119 : ∀ v : Fin 195,
    sieveAllowed 119 v → sieveAllowed (119 + 1) v →
    sieveLift (119 + 1) v = sieveLift 119 v + 1 ∧
      sieveLift v (119 + 1) = sieveLift v 119 := by
  decide +kernel

private lemma sieve_certificate_row_120 : ∀ v : Fin 195,
    sieveAllowed 120 v → sieveAllowed (120 + 1) v →
    sieveLift (120 + 1) v = sieveLift 120 v + 1 ∧
      sieveLift v (120 + 1) = sieveLift v 120 := by
  decide +kernel

private lemma sieve_certificate_row_121 : ∀ v : Fin 195,
    sieveAllowed 121 v → sieveAllowed (121 + 1) v →
    sieveLift (121 + 1) v = sieveLift 121 v + 1 ∧
      sieveLift v (121 + 1) = sieveLift v 121 := by
  decide +kernel

private lemma sieve_certificate_row_122 : ∀ v : Fin 195,
    sieveAllowed 122 v → sieveAllowed (122 + 1) v →
    sieveLift (122 + 1) v = sieveLift 122 v + 1 ∧
      sieveLift v (122 + 1) = sieveLift v 122 := by
  decide +kernel

private lemma sieve_certificate_row_123 : ∀ v : Fin 195,
    sieveAllowed 123 v → sieveAllowed (123 + 1) v →
    sieveLift (123 + 1) v = sieveLift 123 v + 1 ∧
      sieveLift v (123 + 1) = sieveLift v 123 := by
  decide +kernel

private lemma sieve_certificate_row_124 : ∀ v : Fin 195,
    sieveAllowed 124 v → sieveAllowed (124 + 1) v →
    sieveLift (124 + 1) v = sieveLift 124 v + 1 ∧
      sieveLift v (124 + 1) = sieveLift v 124 := by
  decide +kernel

private lemma sieve_certificate_row_125 : ∀ v : Fin 195,
    sieveAllowed 125 v → sieveAllowed (125 + 1) v →
    sieveLift (125 + 1) v = sieveLift 125 v + 1 ∧
      sieveLift v (125 + 1) = sieveLift v 125 := by
  decide +kernel

private lemma sieve_certificate_row_126 : ∀ v : Fin 195,
    sieveAllowed 126 v → sieveAllowed (126 + 1) v →
    sieveLift (126 + 1) v = sieveLift 126 v + 1 ∧
      sieveLift v (126 + 1) = sieveLift v 126 := by
  decide +kernel

private lemma sieve_certificate_row_127 : ∀ v : Fin 195,
    sieveAllowed 127 v → sieveAllowed (127 + 1) v →
    sieveLift (127 + 1) v = sieveLift 127 v + 1 ∧
      sieveLift v (127 + 1) = sieveLift v 127 := by
  decide +kernel

private lemma sieve_certificate_row_128 : ∀ v : Fin 195,
    sieveAllowed 128 v → sieveAllowed (128 + 1) v →
    sieveLift (128 + 1) v = sieveLift 128 v + 1 ∧
      sieveLift v (128 + 1) = sieveLift v 128 := by
  decide +kernel

private lemma sieve_certificate_row_129 : ∀ v : Fin 195,
    sieveAllowed 129 v → sieveAllowed (129 + 1) v →
    sieveLift (129 + 1) v = sieveLift 129 v + 1 ∧
      sieveLift v (129 + 1) = sieveLift v 129 := by
  decide +kernel

private lemma sieve_certificate_row_130 : ∀ v : Fin 195,
    sieveAllowed 130 v → sieveAllowed (130 + 1) v →
    sieveLift (130 + 1) v = sieveLift 130 v + 1 ∧
      sieveLift v (130 + 1) = sieveLift v 130 := by
  decide +kernel

private lemma sieve_certificate_row_131 : ∀ v : Fin 195,
    sieveAllowed 131 v → sieveAllowed (131 + 1) v →
    sieveLift (131 + 1) v = sieveLift 131 v + 1 ∧
      sieveLift v (131 + 1) = sieveLift v 131 := by
  decide +kernel

private lemma sieve_certificate_row_132 : ∀ v : Fin 195,
    sieveAllowed 132 v → sieveAllowed (132 + 1) v →
    sieveLift (132 + 1) v = sieveLift 132 v + 1 ∧
      sieveLift v (132 + 1) = sieveLift v 132 := by
  decide +kernel

private lemma sieve_certificate_row_133 : ∀ v : Fin 195,
    sieveAllowed 133 v → sieveAllowed (133 + 1) v →
    sieveLift (133 + 1) v = sieveLift 133 v + 1 ∧
      sieveLift v (133 + 1) = sieveLift v 133 := by
  decide +kernel

private lemma sieve_certificate_row_134 : ∀ v : Fin 195,
    sieveAllowed 134 v → sieveAllowed (134 + 1) v →
    sieveLift (134 + 1) v = sieveLift 134 v + 1 ∧
      sieveLift v (134 + 1) = sieveLift v 134 := by
  decide +kernel

private lemma sieve_certificate_row_135 : ∀ v : Fin 195,
    sieveAllowed 135 v → sieveAllowed (135 + 1) v →
    sieveLift (135 + 1) v = sieveLift 135 v + 1 ∧
      sieveLift v (135 + 1) = sieveLift v 135 := by
  decide +kernel

private lemma sieve_certificate_row_136 : ∀ v : Fin 195,
    sieveAllowed 136 v → sieveAllowed (136 + 1) v →
    sieveLift (136 + 1) v = sieveLift 136 v + 1 ∧
      sieveLift v (136 + 1) = sieveLift v 136 := by
  decide +kernel

private lemma sieve_certificate_row_137 : ∀ v : Fin 195,
    sieveAllowed 137 v → sieveAllowed (137 + 1) v →
    sieveLift (137 + 1) v = sieveLift 137 v + 1 ∧
      sieveLift v (137 + 1) = sieveLift v 137 := by
  decide +kernel

private lemma sieve_certificate_row_138 : ∀ v : Fin 195,
    sieveAllowed 138 v → sieveAllowed (138 + 1) v →
    sieveLift (138 + 1) v = sieveLift 138 v + 1 ∧
      sieveLift v (138 + 1) = sieveLift v 138 := by
  decide +kernel

private lemma sieve_certificate_row_139 : ∀ v : Fin 195,
    sieveAllowed 139 v → sieveAllowed (139 + 1) v →
    sieveLift (139 + 1) v = sieveLift 139 v + 1 ∧
      sieveLift v (139 + 1) = sieveLift v 139 := by
  decide +kernel

private lemma sieve_certificate_row_140 : ∀ v : Fin 195,
    sieveAllowed 140 v → sieveAllowed (140 + 1) v →
    sieveLift (140 + 1) v = sieveLift 140 v + 1 ∧
      sieveLift v (140 + 1) = sieveLift v 140 := by
  decide +kernel

private lemma sieve_certificate_row_141 : ∀ v : Fin 195,
    sieveAllowed 141 v → sieveAllowed (141 + 1) v →
    sieveLift (141 + 1) v = sieveLift 141 v + 1 ∧
      sieveLift v (141 + 1) = sieveLift v 141 := by
  decide +kernel

private lemma sieve_certificate_row_142 : ∀ v : Fin 195,
    sieveAllowed 142 v → sieveAllowed (142 + 1) v →
    sieveLift (142 + 1) v = sieveLift 142 v + 1 ∧
      sieveLift v (142 + 1) = sieveLift v 142 := by
  decide +kernel

private lemma sieve_certificate_row_143 : ∀ v : Fin 195,
    sieveAllowed 143 v → sieveAllowed (143 + 1) v →
    sieveLift (143 + 1) v = sieveLift 143 v + 1 ∧
      sieveLift v (143 + 1) = sieveLift v 143 := by
  decide +kernel

private lemma sieve_certificate_row_144 : ∀ v : Fin 195,
    sieveAllowed 144 v → sieveAllowed (144 + 1) v →
    sieveLift (144 + 1) v = sieveLift 144 v + 1 ∧
      sieveLift v (144 + 1) = sieveLift v 144 := by
  decide +kernel

private lemma sieve_certificate_row_145 : ∀ v : Fin 195,
    sieveAllowed 145 v → sieveAllowed (145 + 1) v →
    sieveLift (145 + 1) v = sieveLift 145 v + 1 ∧
      sieveLift v (145 + 1) = sieveLift v 145 := by
  decide +kernel

private lemma sieve_certificate_row_146 : ∀ v : Fin 195,
    sieveAllowed 146 v → sieveAllowed (146 + 1) v →
    sieveLift (146 + 1) v = sieveLift 146 v + 1 ∧
      sieveLift v (146 + 1) = sieveLift v 146 := by
  decide +kernel

private lemma sieve_certificate_row_147 : ∀ v : Fin 195,
    sieveAllowed 147 v → sieveAllowed (147 + 1) v →
    sieveLift (147 + 1) v = sieveLift 147 v + 1 ∧
      sieveLift v (147 + 1) = sieveLift v 147 := by
  decide +kernel

private lemma sieve_certificate_row_148 : ∀ v : Fin 195,
    sieveAllowed 148 v → sieveAllowed (148 + 1) v →
    sieveLift (148 + 1) v = sieveLift 148 v + 1 ∧
      sieveLift v (148 + 1) = sieveLift v 148 := by
  decide +kernel

private lemma sieve_certificate_row_149 : ∀ v : Fin 195,
    sieveAllowed 149 v → sieveAllowed (149 + 1) v →
    sieveLift (149 + 1) v = sieveLift 149 v + 1 ∧
      sieveLift v (149 + 1) = sieveLift v 149 := by
  decide +kernel

private lemma sieve_certificate_row_150 : ∀ v : Fin 195,
    sieveAllowed 150 v → sieveAllowed (150 + 1) v →
    sieveLift (150 + 1) v = sieveLift 150 v + 1 ∧
      sieveLift v (150 + 1) = sieveLift v 150 := by
  decide +kernel

private lemma sieve_certificate_row_151 : ∀ v : Fin 195,
    sieveAllowed 151 v → sieveAllowed (151 + 1) v →
    sieveLift (151 + 1) v = sieveLift 151 v + 1 ∧
      sieveLift v (151 + 1) = sieveLift v 151 := by
  decide +kernel

private lemma sieve_certificate_row_152 : ∀ v : Fin 195,
    sieveAllowed 152 v → sieveAllowed (152 + 1) v →
    sieveLift (152 + 1) v = sieveLift 152 v + 1 ∧
      sieveLift v (152 + 1) = sieveLift v 152 := by
  decide +kernel

private lemma sieve_certificate_row_153 : ∀ v : Fin 195,
    sieveAllowed 153 v → sieveAllowed (153 + 1) v →
    sieveLift (153 + 1) v = sieveLift 153 v + 1 ∧
      sieveLift v (153 + 1) = sieveLift v 153 := by
  decide +kernel

private lemma sieve_certificate_row_154 : ∀ v : Fin 195,
    sieveAllowed 154 v → sieveAllowed (154 + 1) v →
    sieveLift (154 + 1) v = sieveLift 154 v + 1 ∧
      sieveLift v (154 + 1) = sieveLift v 154 := by
  decide +kernel

private lemma sieve_certificate_row_155 : ∀ v : Fin 195,
    sieveAllowed 155 v → sieveAllowed (155 + 1) v →
    sieveLift (155 + 1) v = sieveLift 155 v + 1 ∧
      sieveLift v (155 + 1) = sieveLift v 155 := by
  decide +kernel

private lemma sieve_certificate_row_156 : ∀ v : Fin 195,
    sieveAllowed 156 v → sieveAllowed (156 + 1) v →
    sieveLift (156 + 1) v = sieveLift 156 v + 1 ∧
      sieveLift v (156 + 1) = sieveLift v 156 := by
  decide +kernel

private lemma sieve_certificate_row_157 : ∀ v : Fin 195,
    sieveAllowed 157 v → sieveAllowed (157 + 1) v →
    sieveLift (157 + 1) v = sieveLift 157 v + 1 ∧
      sieveLift v (157 + 1) = sieveLift v 157 := by
  decide +kernel

private lemma sieve_certificate_row_158 : ∀ v : Fin 195,
    sieveAllowed 158 v → sieveAllowed (158 + 1) v →
    sieveLift (158 + 1) v = sieveLift 158 v + 1 ∧
      sieveLift v (158 + 1) = sieveLift v 158 := by
  decide +kernel

private lemma sieve_certificate_row_159 : ∀ v : Fin 195,
    sieveAllowed 159 v → sieveAllowed (159 + 1) v →
    sieveLift (159 + 1) v = sieveLift 159 v + 1 ∧
      sieveLift v (159 + 1) = sieveLift v 159 := by
  decide +kernel

private lemma sieve_certificate_row_160 : ∀ v : Fin 195,
    sieveAllowed 160 v → sieveAllowed (160 + 1) v →
    sieveLift (160 + 1) v = sieveLift 160 v + 1 ∧
      sieveLift v (160 + 1) = sieveLift v 160 := by
  decide +kernel

private lemma sieve_certificate_row_161 : ∀ v : Fin 195,
    sieveAllowed 161 v → sieveAllowed (161 + 1) v →
    sieveLift (161 + 1) v = sieveLift 161 v + 1 ∧
      sieveLift v (161 + 1) = sieveLift v 161 := by
  decide +kernel

private lemma sieve_certificate_row_162 : ∀ v : Fin 195,
    sieveAllowed 162 v → sieveAllowed (162 + 1) v →
    sieveLift (162 + 1) v = sieveLift 162 v + 1 ∧
      sieveLift v (162 + 1) = sieveLift v 162 := by
  decide +kernel

private lemma sieve_certificate_row_163 : ∀ v : Fin 195,
    sieveAllowed 163 v → sieveAllowed (163 + 1) v →
    sieveLift (163 + 1) v = sieveLift 163 v + 1 ∧
      sieveLift v (163 + 1) = sieveLift v 163 := by
  decide +kernel

private lemma sieve_certificate_row_164 : ∀ v : Fin 195,
    sieveAllowed 164 v → sieveAllowed (164 + 1) v →
    sieveLift (164 + 1) v = sieveLift 164 v + 1 ∧
      sieveLift v (164 + 1) = sieveLift v 164 := by
  decide +kernel

private lemma sieve_certificate_row_165 : ∀ v : Fin 195,
    sieveAllowed 165 v → sieveAllowed (165 + 1) v →
    sieveLift (165 + 1) v = sieveLift 165 v + 1 ∧
      sieveLift v (165 + 1) = sieveLift v 165 := by
  decide +kernel

private lemma sieve_certificate_row_166 : ∀ v : Fin 195,
    sieveAllowed 166 v → sieveAllowed (166 + 1) v →
    sieveLift (166 + 1) v = sieveLift 166 v + 1 ∧
      sieveLift v (166 + 1) = sieveLift v 166 := by
  decide +kernel

private lemma sieve_certificate_row_167 : ∀ v : Fin 195,
    sieveAllowed 167 v → sieveAllowed (167 + 1) v →
    sieveLift (167 + 1) v = sieveLift 167 v + 1 ∧
      sieveLift v (167 + 1) = sieveLift v 167 := by
  decide +kernel

private lemma sieve_certificate_row_168 : ∀ v : Fin 195,
    sieveAllowed 168 v → sieveAllowed (168 + 1) v →
    sieveLift (168 + 1) v = sieveLift 168 v + 1 ∧
      sieveLift v (168 + 1) = sieveLift v 168 := by
  decide +kernel

private lemma sieve_certificate_row_169 : ∀ v : Fin 195,
    sieveAllowed 169 v → sieveAllowed (169 + 1) v →
    sieveLift (169 + 1) v = sieveLift 169 v + 1 ∧
      sieveLift v (169 + 1) = sieveLift v 169 := by
  decide +kernel

private lemma sieve_certificate_row_170 : ∀ v : Fin 195,
    sieveAllowed 170 v → sieveAllowed (170 + 1) v →
    sieveLift (170 + 1) v = sieveLift 170 v + 1 ∧
      sieveLift v (170 + 1) = sieveLift v 170 := by
  decide +kernel

private lemma sieve_certificate_row_171 : ∀ v : Fin 195,
    sieveAllowed 171 v → sieveAllowed (171 + 1) v →
    sieveLift (171 + 1) v = sieveLift 171 v + 1 ∧
      sieveLift v (171 + 1) = sieveLift v 171 := by
  decide +kernel

private lemma sieve_certificate_row_172 : ∀ v : Fin 195,
    sieveAllowed 172 v → sieveAllowed (172 + 1) v →
    sieveLift (172 + 1) v = sieveLift 172 v + 1 ∧
      sieveLift v (172 + 1) = sieveLift v 172 := by
  decide +kernel

private lemma sieve_certificate_row_173 : ∀ v : Fin 195,
    sieveAllowed 173 v → sieveAllowed (173 + 1) v →
    sieveLift (173 + 1) v = sieveLift 173 v + 1 ∧
      sieveLift v (173 + 1) = sieveLift v 173 := by
  decide +kernel

private lemma sieve_certificate_row_174 : ∀ v : Fin 195,
    sieveAllowed 174 v → sieveAllowed (174 + 1) v →
    sieveLift (174 + 1) v = sieveLift 174 v + 1 ∧
      sieveLift v (174 + 1) = sieveLift v 174 := by
  decide +kernel

private lemma sieve_certificate_row_175 : ∀ v : Fin 195,
    sieveAllowed 175 v → sieveAllowed (175 + 1) v →
    sieveLift (175 + 1) v = sieveLift 175 v + 1 ∧
      sieveLift v (175 + 1) = sieveLift v 175 := by
  decide +kernel

private lemma sieve_certificate_row_176 : ∀ v : Fin 195,
    sieveAllowed 176 v → sieveAllowed (176 + 1) v →
    sieveLift (176 + 1) v = sieveLift 176 v + 1 ∧
      sieveLift v (176 + 1) = sieveLift v 176 := by
  decide +kernel

private lemma sieve_certificate_row_177 : ∀ v : Fin 195,
    sieveAllowed 177 v → sieveAllowed (177 + 1) v →
    sieveLift (177 + 1) v = sieveLift 177 v + 1 ∧
      sieveLift v (177 + 1) = sieveLift v 177 := by
  decide +kernel

private lemma sieve_certificate_row_178 : ∀ v : Fin 195,
    sieveAllowed 178 v → sieveAllowed (178 + 1) v →
    sieveLift (178 + 1) v = sieveLift 178 v + 1 ∧
      sieveLift v (178 + 1) = sieveLift v 178 := by
  decide +kernel

private lemma sieve_certificate_row_179 : ∀ v : Fin 195,
    sieveAllowed 179 v → sieveAllowed (179 + 1) v →
    sieveLift (179 + 1) v = sieveLift 179 v + 1 ∧
      sieveLift v (179 + 1) = sieveLift v 179 := by
  decide +kernel

private lemma sieve_certificate_row_180 : ∀ v : Fin 195,
    sieveAllowed 180 v → sieveAllowed (180 + 1) v →
    sieveLift (180 + 1) v = sieveLift 180 v + 1 ∧
      sieveLift v (180 + 1) = sieveLift v 180 := by
  decide +kernel

private lemma sieve_certificate_row_181 : ∀ v : Fin 195,
    sieveAllowed 181 v → sieveAllowed (181 + 1) v →
    sieveLift (181 + 1) v = sieveLift 181 v + 1 ∧
      sieveLift v (181 + 1) = sieveLift v 181 := by
  decide +kernel

private lemma sieve_certificate_row_182 : ∀ v : Fin 195,
    sieveAllowed 182 v → sieveAllowed (182 + 1) v →
    sieveLift (182 + 1) v = sieveLift 182 v + 1 ∧
      sieveLift v (182 + 1) = sieveLift v 182 := by
  decide +kernel

private lemma sieve_certificate_row_183 : ∀ v : Fin 195,
    sieveAllowed 183 v → sieveAllowed (183 + 1) v →
    sieveLift (183 + 1) v = sieveLift 183 v + 1 ∧
      sieveLift v (183 + 1) = sieveLift v 183 := by
  decide +kernel

private lemma sieve_certificate_row_184 : ∀ v : Fin 195,
    sieveAllowed 184 v → sieveAllowed (184 + 1) v →
    sieveLift (184 + 1) v = sieveLift 184 v + 1 ∧
      sieveLift v (184 + 1) = sieveLift v 184 := by
  decide +kernel

private lemma sieve_certificate_row_185 : ∀ v : Fin 195,
    sieveAllowed 185 v → sieveAllowed (185 + 1) v →
    sieveLift (185 + 1) v = sieveLift 185 v + 1 ∧
      sieveLift v (185 + 1) = sieveLift v 185 := by
  decide +kernel

private lemma sieve_certificate_row_186 : ∀ v : Fin 195,
    sieveAllowed 186 v → sieveAllowed (186 + 1) v →
    sieveLift (186 + 1) v = sieveLift 186 v + 1 ∧
      sieveLift v (186 + 1) = sieveLift v 186 := by
  decide +kernel

private lemma sieve_certificate_row_187 : ∀ v : Fin 195,
    sieveAllowed 187 v → sieveAllowed (187 + 1) v →
    sieveLift (187 + 1) v = sieveLift 187 v + 1 ∧
      sieveLift v (187 + 1) = sieveLift v 187 := by
  decide +kernel

private lemma sieve_certificate_row_188 : ∀ v : Fin 195,
    sieveAllowed 188 v → sieveAllowed (188 + 1) v →
    sieveLift (188 + 1) v = sieveLift 188 v + 1 ∧
      sieveLift v (188 + 1) = sieveLift v 188 := by
  decide +kernel

private lemma sieve_certificate_row_189 : ∀ v : Fin 195,
    sieveAllowed 189 v → sieveAllowed (189 + 1) v →
    sieveLift (189 + 1) v = sieveLift 189 v + 1 ∧
      sieveLift v (189 + 1) = sieveLift v 189 := by
  decide +kernel

private lemma sieve_certificate_row_190 : ∀ v : Fin 195,
    sieveAllowed 190 v → sieveAllowed (190 + 1) v →
    sieveLift (190 + 1) v = sieveLift 190 v + 1 ∧
      sieveLift v (190 + 1) = sieveLift v 190 := by
  decide +kernel

private lemma sieve_certificate_row_191 : ∀ v : Fin 195,
    sieveAllowed 191 v → sieveAllowed (191 + 1) v →
    sieveLift (191 + 1) v = sieveLift 191 v + 1 ∧
      sieveLift v (191 + 1) = sieveLift v 191 := by
  decide +kernel

private lemma sieve_certificate_row_192 : ∀ v : Fin 195,
    sieveAllowed 192 v → sieveAllowed (192 + 1) v →
    sieveLift (192 + 1) v = sieveLift 192 v + 1 ∧
      sieveLift v (192 + 1) = sieveLift v 192 := by
  decide +kernel

private lemma sieve_certificate_row_193 : ∀ v : Fin 195,
    sieveAllowed 193 v → sieveAllowed (193 + 1) v →
    sieveLift (193 + 1) v = sieveLift 193 v + 1 ∧
      sieveLift v (193 + 1) = sieveLift v 193 := by
  decide +kernel

private lemma sieve_certificate_row_194 : ∀ v : Fin 195,
    sieveAllowed 194 v → sieveAllowed (194 + 1) v →
    sieveLift (194 + 1) v = sieveLift 194 v + 1 ∧
      sieveLift v (194 + 1) = sieveLift v 194 := by
  decide +kernel

lemma sieve_certificate : ∀ u v : Fin 195,
    sieveAllowed u v → sieveAllowed (u + 1) v →
    sieveLift (u + 1) v = sieveLift u v + 1 ∧
      sieveLift v (u + 1) = sieveLift v u := by
  intro u
  fin_cases u
  · exact sieve_certificate_row_0
  · exact sieve_certificate_row_1
  · exact sieve_certificate_row_2
  · exact sieve_certificate_row_3
  · exact sieve_certificate_row_4
  · exact sieve_certificate_row_5
  · exact sieve_certificate_row_6
  · exact sieve_certificate_row_7
  · exact sieve_certificate_row_8
  · exact sieve_certificate_row_9
  · exact sieve_certificate_row_10
  · exact sieve_certificate_row_11
  · exact sieve_certificate_row_12
  · exact sieve_certificate_row_13
  · exact sieve_certificate_row_14
  · exact sieve_certificate_row_15
  · exact sieve_certificate_row_16
  · exact sieve_certificate_row_17
  · exact sieve_certificate_row_18
  · exact sieve_certificate_row_19
  · exact sieve_certificate_row_20
  · exact sieve_certificate_row_21
  · exact sieve_certificate_row_22
  · exact sieve_certificate_row_23
  · exact sieve_certificate_row_24
  · exact sieve_certificate_row_25
  · exact sieve_certificate_row_26
  · exact sieve_certificate_row_27
  · exact sieve_certificate_row_28
  · exact sieve_certificate_row_29
  · exact sieve_certificate_row_30
  · exact sieve_certificate_row_31
  · exact sieve_certificate_row_32
  · exact sieve_certificate_row_33
  · exact sieve_certificate_row_34
  · exact sieve_certificate_row_35
  · exact sieve_certificate_row_36
  · exact sieve_certificate_row_37
  · exact sieve_certificate_row_38
  · exact sieve_certificate_row_39
  · exact sieve_certificate_row_40
  · exact sieve_certificate_row_41
  · exact sieve_certificate_row_42
  · exact sieve_certificate_row_43
  · exact sieve_certificate_row_44
  · exact sieve_certificate_row_45
  · exact sieve_certificate_row_46
  · exact sieve_certificate_row_47
  · exact sieve_certificate_row_48
  · exact sieve_certificate_row_49
  · exact sieve_certificate_row_50
  · exact sieve_certificate_row_51
  · exact sieve_certificate_row_52
  · exact sieve_certificate_row_53
  · exact sieve_certificate_row_54
  · exact sieve_certificate_row_55
  · exact sieve_certificate_row_56
  · exact sieve_certificate_row_57
  · exact sieve_certificate_row_58
  · exact sieve_certificate_row_59
  · exact sieve_certificate_row_60
  · exact sieve_certificate_row_61
  · exact sieve_certificate_row_62
  · exact sieve_certificate_row_63
  · exact sieve_certificate_row_64
  · exact sieve_certificate_row_65
  · exact sieve_certificate_row_66
  · exact sieve_certificate_row_67
  · exact sieve_certificate_row_68
  · exact sieve_certificate_row_69
  · exact sieve_certificate_row_70
  · exact sieve_certificate_row_71
  · exact sieve_certificate_row_72
  · exact sieve_certificate_row_73
  · exact sieve_certificate_row_74
  · exact sieve_certificate_row_75
  · exact sieve_certificate_row_76
  · exact sieve_certificate_row_77
  · exact sieve_certificate_row_78
  · exact sieve_certificate_row_79
  · exact sieve_certificate_row_80
  · exact sieve_certificate_row_81
  · exact sieve_certificate_row_82
  · exact sieve_certificate_row_83
  · exact sieve_certificate_row_84
  · exact sieve_certificate_row_85
  · exact sieve_certificate_row_86
  · exact sieve_certificate_row_87
  · exact sieve_certificate_row_88
  · exact sieve_certificate_row_89
  · exact sieve_certificate_row_90
  · exact sieve_certificate_row_91
  · exact sieve_certificate_row_92
  · exact sieve_certificate_row_93
  · exact sieve_certificate_row_94
  · exact sieve_certificate_row_95
  · exact sieve_certificate_row_96
  · exact sieve_certificate_row_97
  · exact sieve_certificate_row_98
  · exact sieve_certificate_row_99
  · exact sieve_certificate_row_100
  · exact sieve_certificate_row_101
  · exact sieve_certificate_row_102
  · exact sieve_certificate_row_103
  · exact sieve_certificate_row_104
  · exact sieve_certificate_row_105
  · exact sieve_certificate_row_106
  · exact sieve_certificate_row_107
  · exact sieve_certificate_row_108
  · exact sieve_certificate_row_109
  · exact sieve_certificate_row_110
  · exact sieve_certificate_row_111
  · exact sieve_certificate_row_112
  · exact sieve_certificate_row_113
  · exact sieve_certificate_row_114
  · exact sieve_certificate_row_115
  · exact sieve_certificate_row_116
  · exact sieve_certificate_row_117
  · exact sieve_certificate_row_118
  · exact sieve_certificate_row_119
  · exact sieve_certificate_row_120
  · exact sieve_certificate_row_121
  · exact sieve_certificate_row_122
  · exact sieve_certificate_row_123
  · exact sieve_certificate_row_124
  · exact sieve_certificate_row_125
  · exact sieve_certificate_row_126
  · exact sieve_certificate_row_127
  · exact sieve_certificate_row_128
  · exact sieve_certificate_row_129
  · exact sieve_certificate_row_130
  · exact sieve_certificate_row_131
  · exact sieve_certificate_row_132
  · exact sieve_certificate_row_133
  · exact sieve_certificate_row_134
  · exact sieve_certificate_row_135
  · exact sieve_certificate_row_136
  · exact sieve_certificate_row_137
  · exact sieve_certificate_row_138
  · exact sieve_certificate_row_139
  · exact sieve_certificate_row_140
  · exact sieve_certificate_row_141
  · exact sieve_certificate_row_142
  · exact sieve_certificate_row_143
  · exact sieve_certificate_row_144
  · exact sieve_certificate_row_145
  · exact sieve_certificate_row_146
  · exact sieve_certificate_row_147
  · exact sieve_certificate_row_148
  · exact sieve_certificate_row_149
  · exact sieve_certificate_row_150
  · exact sieve_certificate_row_151
  · exact sieve_certificate_row_152
  · exact sieve_certificate_row_153
  · exact sieve_certificate_row_154
  · exact sieve_certificate_row_155
  · exact sieve_certificate_row_156
  · exact sieve_certificate_row_157
  · exact sieve_certificate_row_158
  · exact sieve_certificate_row_159
  · exact sieve_certificate_row_160
  · exact sieve_certificate_row_161
  · exact sieve_certificate_row_162
  · exact sieve_certificate_row_163
  · exact sieve_certificate_row_164
  · exact sieve_certificate_row_165
  · exact sieve_certificate_row_166
  · exact sieve_certificate_row_167
  · exact sieve_certificate_row_168
  · exact sieve_certificate_row_169
  · exact sieve_certificate_row_170
  · exact sieve_certificate_row_171
  · exact sieve_certificate_row_172
  · exact sieve_certificate_row_173
  · exact sieve_certificate_row_174
  · exact sieve_certificate_row_175
  · exact sieve_certificate_row_176
  · exact sieve_certificate_row_177
  · exact sieve_certificate_row_178
  · exact sieve_certificate_row_179
  · exact sieve_certificate_row_180
  · exact sieve_certificate_row_181
  · exact sieve_certificate_row_182
  · exact sieve_certificate_row_183
  · exact sieve_certificate_row_184
  · exact sieve_certificate_row_185
  · exact sieve_certificate_row_186
  · exact sieve_certificate_row_187
  · exact sieve_certificate_row_188
  · exact sieve_certificate_row_189
  · exact sieve_certificate_row_190
  · exact sieve_certificate_row_191
  · exact sieve_certificate_row_192
  · exact sieve_certificate_row_193
  · exact sieve_certificate_row_194

#print axioms sieve_certificate

end Erdos952Investigation
