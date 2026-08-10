import FormalConjectures.Util.ProblemImports

open Nat Finset

/--
A091591: Number of pairs of twin primes between $n^2$ and $(n+1)^2$.
This counts the number of primes $p$ such that $p$ and $p+2$ are both prime,
and the entire twin prime pair $(p, p+2)$ lies strictly between $n^2$ and $(n+1)^2$.
That is, $n^2 < p$ and $p+2 < (n+1)^2$.
-/
def a (n : ℕ) : ℕ :=
  let lower_p_start : ℕ := n ^ 2 + 1
  -- The condition $p+2 < (n+1)^2$ is equivalent to $p \le (n+1)^2 - 3$.
  let max_p_value : ℕ := (n + 1) ^ 2 - 3

  -- We count primes $p$ in the closed interval $[n^2 + 1, (n+1)^2 - 3]$.
  Finset.card $ Finset.filter
    (fun p => p.Prime ∧ (p + 2).Prime)
    (Finset.Icc lower_p_start max_p_value)

theorem witness_1 : ∃ p, p.Prime ∧ 1^2 < p ∧ p < (1+1)^2 := ⟨2, by norm_num⟩
theorem witness_2 : ∃ p, p.Prime ∧ 2^2 < p ∧ p < (2+1)^2 := ⟨5, by norm_num⟩
theorem witness_3 : ∃ p, p.Prime ∧ 3^2 < p ∧ p < (3+1)^2 := ⟨11, by norm_num⟩
theorem witness_4 : ∃ p, p.Prime ∧ 4^2 < p ∧ p < (4+1)^2 := ⟨17, by norm_num⟩
theorem witness_5 : ∃ p, p.Prime ∧ 5^2 < p ∧ p < (5+1)^2 := ⟨29, by norm_num⟩
theorem witness_6 : ∃ p, p.Prime ∧ 6^2 < p ∧ p < (6+1)^2 := ⟨37, by norm_num⟩
theorem witness_7 : ∃ p, p.Prime ∧ 7^2 < p ∧ p < (7+1)^2 := ⟨53, by norm_num⟩
theorem witness_8 : ∃ p, p.Prime ∧ 8^2 < p ∧ p < (8+1)^2 := ⟨67, by norm_num⟩
theorem witness_9 : ∃ p, p.Prime ∧ 9^2 < p ∧ p < (9+1)^2 := ⟨83, by norm_num⟩
theorem witness_10 : ∃ p, p.Prime ∧ 10^2 < p ∧ p < (10+1)^2 := ⟨101, by norm_num⟩
theorem witness_11 : ∃ p, p.Prime ∧ 11^2 < p ∧ p < (11+1)^2 := ⟨127, by norm_num⟩
theorem witness_12 : ∃ p, p.Prime ∧ 12^2 < p ∧ p < (12+1)^2 := ⟨149, by norm_num⟩
theorem witness_13 : ∃ p, p.Prime ∧ 13^2 < p ∧ p < (13+1)^2 := ⟨173, by norm_num⟩
theorem witness_14 : ∃ p, p.Prime ∧ 14^2 < p ∧ p < (14+1)^2 := ⟨197, by norm_num⟩
theorem witness_15 : ∃ p, p.Prime ∧ 15^2 < p ∧ p < (15+1)^2 := ⟨227, by norm_num⟩
theorem witness_16 : ∃ p, p.Prime ∧ 16^2 < p ∧ p < (16+1)^2 := ⟨257, by norm_num⟩
theorem witness_17 : ∃ p, p.Prime ∧ 17^2 < p ∧ p < (17+1)^2 := ⟨293, by norm_num⟩
theorem witness_18 : ∃ p, p.Prime ∧ 18^2 < p ∧ p < (18+1)^2 := ⟨331, by norm_num⟩
theorem witness_19 : ∃ p, p.Prime ∧ 19^2 < p ∧ p < (19+1)^2 := ⟨367, by norm_num⟩
theorem witness_20 : ∃ p, p.Prime ∧ 20^2 < p ∧ p < (20+1)^2 := ⟨401, by norm_num⟩
theorem witness_21 : ∃ p, p.Prime ∧ 21^2 < p ∧ p < (21+1)^2 := ⟨443, by norm_num⟩
theorem witness_22 : ∃ p, p.Prime ∧ 22^2 < p ∧ p < (22+1)^2 := ⟨487, by norm_num⟩
theorem witness_23 : ∃ p, p.Prime ∧ 23^2 < p ∧ p < (23+1)^2 := ⟨541, by norm_num⟩
theorem witness_24 : ∃ p, p.Prime ∧ 24^2 < p ∧ p < (24+1)^2 := ⟨577, by norm_num⟩
theorem witness_25 : ∃ p, p.Prime ∧ 25^2 < p ∧ p < (25+1)^2 := ⟨631, by norm_num⟩
theorem witness_26 : ∃ p, p.Prime ∧ 26^2 < p ∧ p < (26+1)^2 := ⟨677, by norm_num⟩
theorem witness_27 : ∃ p, p.Prime ∧ 27^2 < p ∧ p < (27+1)^2 := ⟨733, by norm_num⟩
theorem witness_28 : ∃ p, p.Prime ∧ 28^2 < p ∧ p < (28+1)^2 := ⟨787, by norm_num⟩
theorem witness_29 : ∃ p, p.Prime ∧ 29^2 < p ∧ p < (29+1)^2 := ⟨853, by norm_num⟩
theorem witness_30 : ∃ p, p.Prime ∧ 30^2 < p ∧ p < (30+1)^2 := ⟨907, by norm_num⟩
theorem witness_31 : ∃ p, p.Prime ∧ 31^2 < p ∧ p < (31+1)^2 := ⟨967, by norm_num⟩
theorem witness_32 : ∃ p, p.Prime ∧ 32^2 < p ∧ p < (32+1)^2 := ⟨1031, by norm_num⟩
theorem witness_33 : ∃ p, p.Prime ∧ 33^2 < p ∧ p < (33+1)^2 := ⟨1091, by norm_num⟩
theorem witness_34 : ∃ p, p.Prime ∧ 34^2 < p ∧ p < (34+1)^2 := ⟨1163, by norm_num⟩
theorem witness_35 : ∃ p, p.Prime ∧ 35^2 < p ∧ p < (35+1)^2 := ⟨1229, by norm_num⟩
theorem witness_36 : ∃ p, p.Prime ∧ 36^2 < p ∧ p < (36+1)^2 := ⟨1297, by norm_num⟩
theorem witness_37 : ∃ p, p.Prime ∧ 37^2 < p ∧ p < (37+1)^2 := ⟨1373, by norm_num⟩
theorem witness_38 : ∃ p, p.Prime ∧ 38^2 < p ∧ p < (38+1)^2 := ⟨1447, by norm_num⟩
theorem witness_39 : ∃ p, p.Prime ∧ 39^2 < p ∧ p < (39+1)^2 := ⟨1523, by norm_num⟩
theorem witness_40 : ∃ p, p.Prime ∧ 40^2 < p ∧ p < (40+1)^2 := ⟨1601, by norm_num⟩
theorem witness_41 : ∃ p, p.Prime ∧ 41^2 < p ∧ p < (41+1)^2 := ⟨1693, by norm_num⟩
theorem witness_42 : ∃ p, p.Prime ∧ 42^2 < p ∧ p < (42+1)^2 := ⟨1777, by norm_num⟩
theorem witness_43 : ∃ p, p.Prime ∧ 43^2 < p ∧ p < (43+1)^2 := ⟨1861, by norm_num⟩
theorem witness_44 : ∃ p, p.Prime ∧ 44^2 < p ∧ p < (44+1)^2 := ⟨1949, by norm_num⟩
theorem witness_45 : ∃ p, p.Prime ∧ 45^2 < p ∧ p < (45+1)^2 := ⟨2027, by norm_num⟩
theorem witness_46 : ∃ p, p.Prime ∧ 46^2 < p ∧ p < (46+1)^2 := ⟨2129, by norm_num⟩
theorem witness_47 : ∃ p, p.Prime ∧ 47^2 < p ∧ p < (47+1)^2 := ⟨2213, by norm_num⟩
theorem witness_48 : ∃ p, p.Prime ∧ 48^2 < p ∧ p < (48+1)^2 := ⟨2309, by norm_num⟩
theorem witness_49 : ∃ p, p.Prime ∧ 49^2 < p ∧ p < (49+1)^2 := ⟨2411, by norm_num⟩
theorem witness_50 : ∃ p, p.Prime ∧ 50^2 < p ∧ p < (50+1)^2 := ⟨2503, by norm_num⟩
theorem witness_51 : ∃ p, p.Prime ∧ 51^2 < p ∧ p < (51+1)^2 := ⟨2609, by norm_num⟩
theorem witness_52 : ∃ p, p.Prime ∧ 52^2 < p ∧ p < (52+1)^2 := ⟨2707, by norm_num⟩
theorem witness_53 : ∃ p, p.Prime ∧ 53^2 < p ∧ p < (53+1)^2 := ⟨2819, by norm_num⟩
theorem witness_54 : ∃ p, p.Prime ∧ 54^2 < p ∧ p < (54+1)^2 := ⟨2917, by norm_num⟩
theorem witness_55 : ∃ p, p.Prime ∧ 55^2 < p ∧ p < (55+1)^2 := ⟨3037, by norm_num⟩
theorem witness_56 : ∃ p, p.Prime ∧ 56^2 < p ∧ p < (56+1)^2 := ⟨3137, by norm_num⟩
theorem witness_57 : ∃ p, p.Prime ∧ 57^2 < p ∧ p < (57+1)^2 := ⟨3251, by norm_num⟩
theorem witness_58 : ∃ p, p.Prime ∧ 58^2 < p ∧ p < (58+1)^2 := ⟨3371, by norm_num⟩
theorem witness_59 : ∃ p, p.Prime ∧ 59^2 < p ∧ p < (59+1)^2 := ⟨3491, by norm_num⟩
theorem witness_60 : ∃ p, p.Prime ∧ 60^2 < p ∧ p < (60+1)^2 := ⟨3607, by norm_num⟩
theorem witness_61 : ∃ p, p.Prime ∧ 61^2 < p ∧ p < (61+1)^2 := ⟨3727, by norm_num⟩
theorem witness_62 : ∃ p, p.Prime ∧ 62^2 < p ∧ p < (62+1)^2 := ⟨3847, by norm_num⟩
theorem witness_63 : ∃ p, p.Prime ∧ 63^2 < p ∧ p < (63+1)^2 := ⟨3989, by norm_num⟩
theorem witness_64 : ∃ p, p.Prime ∧ 64^2 < p ∧ p < (64+1)^2 := ⟨4099, by norm_num⟩
theorem witness_65 : ∃ p, p.Prime ∧ 65^2 < p ∧ p < (65+1)^2 := ⟨4229, by norm_num⟩
theorem witness_66 : ∃ p, p.Prime ∧ 66^2 < p ∧ p < (66+1)^2 := ⟨4357, by norm_num⟩
theorem witness_67 : ∃ p, p.Prime ∧ 67^2 < p ∧ p < (67+1)^2 := ⟨4493, by norm_num⟩
theorem witness_68 : ∃ p, p.Prime ∧ 68^2 < p ∧ p < (68+1)^2 := ⟨4637, by norm_num⟩
theorem witness_69 : ∃ p, p.Prime ∧ 69^2 < p ∧ p < (69+1)^2 := ⟨4783, by norm_num⟩
theorem witness_70 : ∃ p, p.Prime ∧ 70^2 < p ∧ p < (70+1)^2 := ⟨4903, by norm_num⟩
theorem witness_71 : ∃ p, p.Prime ∧ 71^2 < p ∧ p < (71+1)^2 := ⟨5051, by norm_num⟩
theorem witness_72 : ∃ p, p.Prime ∧ 72^2 < p ∧ p < (72+1)^2 := ⟨5189, by norm_num⟩
theorem witness_73 : ∃ p, p.Prime ∧ 73^2 < p ∧ p < (73+1)^2 := ⟨5333, by norm_num⟩
theorem witness_74 : ∃ p, p.Prime ∧ 74^2 < p ∧ p < (74+1)^2 := ⟨5477, by norm_num⟩
theorem witness_75 : ∃ p, p.Prime ∧ 75^2 < p ∧ p < (75+1)^2 := ⟨5639, by norm_num⟩
theorem witness_76 : ∃ p, p.Prime ∧ 76^2 < p ∧ p < (76+1)^2 := ⟨5779, by norm_num⟩
theorem witness_77 : ∃ p, p.Prime ∧ 77^2 < p ∧ p < (77+1)^2 := ⟨5939, by norm_num⟩
theorem witness_78 : ∃ p, p.Prime ∧ 78^2 < p ∧ p < (78+1)^2 := ⟨6089, by norm_num⟩
theorem witness_79 : ∃ p, p.Prime ∧ 79^2 < p ∧ p < (79+1)^2 := ⟨6247, by norm_num⟩
theorem witness_80 : ∃ p, p.Prime ∧ 80^2 < p ∧ p < (80+1)^2 := ⟨6421, by norm_num⟩
theorem witness_81 : ∃ p, p.Prime ∧ 81^2 < p ∧ p < (81+1)^2 := ⟨6563, by norm_num⟩
theorem witness_82 : ∃ p, p.Prime ∧ 82^2 < p ∧ p < (82+1)^2 := ⟨6733, by norm_num⟩
theorem witness_83 : ∃ p, p.Prime ∧ 83^2 < p ∧ p < (83+1)^2 := ⟨6899, by norm_num⟩
theorem witness_84 : ∃ p, p.Prime ∧ 84^2 < p ∧ p < (84+1)^2 := ⟨7057, by norm_num⟩
theorem witness_85 : ∃ p, p.Prime ∧ 85^2 < p ∧ p < (85+1)^2 := ⟨7229, by norm_num⟩
theorem witness_86 : ∃ p, p.Prime ∧ 86^2 < p ∧ p < (86+1)^2 := ⟨7411, by norm_num⟩
theorem witness_87 : ∃ p, p.Prime ∧ 87^2 < p ∧ p < (87+1)^2 := ⟨7573, by norm_num⟩
theorem witness_88 : ∃ p, p.Prime ∧ 88^2 < p ∧ p < (88+1)^2 := ⟨7753, by norm_num⟩
theorem witness_89 : ∃ p, p.Prime ∧ 89^2 < p ∧ p < (89+1)^2 := ⟨7927, by norm_num⟩
theorem witness_90 : ∃ p, p.Prime ∧ 90^2 < p ∧ p < (90+1)^2 := ⟨8101, by norm_num⟩
theorem witness_91 : ∃ p, p.Prime ∧ 91^2 < p ∧ p < (91+1)^2 := ⟨8287, by norm_num⟩
theorem witness_92 : ∃ p, p.Prime ∧ 92^2 < p ∧ p < (92+1)^2 := ⟨8467, by norm_num⟩
theorem witness_93 : ∃ p, p.Prime ∧ 93^2 < p ∧ p < (93+1)^2 := ⟨8663, by norm_num⟩
theorem witness_94 : ∃ p, p.Prime ∧ 94^2 < p ∧ p < (94+1)^2 := ⟨8837, by norm_num⟩
theorem witness_95 : ∃ p, p.Prime ∧ 95^2 < p ∧ p < (95+1)^2 := ⟨9029, by norm_num⟩
theorem witness_96 : ∃ p, p.Prime ∧ 96^2 < p ∧ p < (96+1)^2 := ⟨9221, by norm_num⟩
theorem witness_97 : ∃ p, p.Prime ∧ 97^2 < p ∧ p < (97+1)^2 := ⟨9413, by norm_num⟩
theorem witness_98 : ∃ p, p.Prime ∧ 98^2 < p ∧ p < (98+1)^2 := ⟨9613, by norm_num⟩
theorem witness_99 : ∃ p, p.Prime ∧ 99^2 < p ∧ p < (99+1)^2 := ⟨9803, by norm_num⟩
theorem witness_100 : ∃ p, p.Prime ∧ 100^2 < p ∧ p < (100+1)^2 := ⟨10007, by norm_num⟩
theorem witness_101 : ∃ p, p.Prime ∧ 101^2 < p ∧ p < (101+1)^2 := ⟨10211, by norm_num⟩
theorem witness_102 : ∃ p, p.Prime ∧ 102^2 < p ∧ p < (102+1)^2 := ⟨10427, by norm_num⟩
theorem witness_103 : ∃ p, p.Prime ∧ 103^2 < p ∧ p < (103+1)^2 := ⟨10613, by norm_num⟩
theorem witness_104 : ∃ p, p.Prime ∧ 104^2 < p ∧ p < (104+1)^2 := ⟨10831, by norm_num⟩
theorem witness_105 : ∃ p, p.Prime ∧ 105^2 < p ∧ p < (105+1)^2 := ⟨11027, by norm_num⟩
theorem witness_106 : ∃ p, p.Prime ∧ 106^2 < p ∧ p < (106+1)^2 := ⟨11239, by norm_num⟩
theorem witness_107 : ∃ p, p.Prime ∧ 107^2 < p ∧ p < (107+1)^2 := ⟨11467, by norm_num⟩
theorem witness_108 : ∃ p, p.Prime ∧ 108^2 < p ∧ p < (108+1)^2 := ⟨11677, by norm_num⟩
theorem witness_109 : ∃ p, p.Prime ∧ 109^2 < p ∧ p < (109+1)^2 := ⟨11887, by norm_num⟩
theorem witness_110 : ∃ p, p.Prime ∧ 110^2 < p ∧ p < (110+1)^2 := ⟨12101, by norm_num⟩
theorem witness_111 : ∃ p, p.Prime ∧ 111^2 < p ∧ p < (111+1)^2 := ⟨12323, by norm_num⟩
theorem witness_112 : ∃ p, p.Prime ∧ 112^2 < p ∧ p < (112+1)^2 := ⟨12547, by norm_num⟩
theorem witness_113 : ∃ p, p.Prime ∧ 113^2 < p ∧ p < (113+1)^2 := ⟨12781, by norm_num⟩
theorem witness_114 : ∃ p, p.Prime ∧ 114^2 < p ∧ p < (114+1)^2 := ⟨13001, by norm_num⟩
theorem witness_115 : ∃ p, p.Prime ∧ 115^2 < p ∧ p < (115+1)^2 := ⟨13229, by norm_num⟩
theorem witness_116 : ∃ p, p.Prime ∧ 116^2 < p ∧ p < (116+1)^2 := ⟨13457, by norm_num⟩
theorem witness_117 : ∃ p, p.Prime ∧ 117^2 < p ∧ p < (117+1)^2 := ⟨13691, by norm_num⟩
theorem witness_118 : ∃ p, p.Prime ∧ 118^2 < p ∧ p < (118+1)^2 := ⟨13931, by norm_num⟩
theorem witness_119 : ∃ p, p.Prime ∧ 119^2 < p ∧ p < (119+1)^2 := ⟨14173, by norm_num⟩
theorem witness_120 : ∃ p, p.Prime ∧ 120^2 < p ∧ p < (120+1)^2 := ⟨14401, by norm_num⟩
theorem witness_121 : ∃ p, p.Prime ∧ 121^2 < p ∧ p < (121+1)^2 := ⟨14653, by norm_num⟩
theorem witness_122 : ∃ p, p.Prime ∧ 122^2 < p ∧ p < (122+1)^2 := ⟨14887, by norm_num⟩

theorem witness_valid : (n : ℕ) → (h1 : 0 < n) → (h2 : n ≤ 122) → ∃ p, p.Prime ∧ n^2 < p ∧ p < (n+1)^2
| 0, h1, _ => by omega
| 1, _, _ => witness_1
| 2, _, _ => witness_2
| 3, _, _ => witness_3
| 4, _, _ => witness_4
| 5, _, _ => witness_5
| 6, _, _ => witness_6
| 7, _, _ => witness_7
| 8, _, _ => witness_8
| 9, _, _ => witness_9
| 10, _, _ => witness_10
| 11, _, _ => witness_11
| 12, _, _ => witness_12
| 13, _, _ => witness_13
| 14, _, _ => witness_14
| 15, _, _ => witness_15
| 16, _, _ => witness_16
| 17, _, _ => witness_17
| 18, _, _ => witness_18
| 19, _, _ => witness_19
| 20, _, _ => witness_20
| 21, _, _ => witness_21
| 22, _, _ => witness_22
| 23, _, _ => witness_23
| 24, _, _ => witness_24
| 25, _, _ => witness_25
| 26, _, _ => witness_26
| 27, _, _ => witness_27
| 28, _, _ => witness_28
| 29, _, _ => witness_29
| 30, _, _ => witness_30
| 31, _, _ => witness_31
| 32, _, _ => witness_32
| 33, _, _ => witness_33
| 34, _, _ => witness_34
| 35, _, _ => witness_35
| 36, _, _ => witness_36
| 37, _, _ => witness_37
| 38, _, _ => witness_38
| 39, _, _ => witness_39
| 40, _, _ => witness_40
| 41, _, _ => witness_41
| 42, _, _ => witness_42
| 43, _, _ => witness_43
| 44, _, _ => witness_44
| 45, _, _ => witness_45
| 46, _, _ => witness_46
| 47, _, _ => witness_47
| 48, _, _ => witness_48
| 49, _, _ => witness_49
| 50, _, _ => witness_50
| 51, _, _ => witness_51
| 52, _, _ => witness_52
| 53, _, _ => witness_53
| 54, _, _ => witness_54
| 55, _, _ => witness_55
| 56, _, _ => witness_56
| 57, _, _ => witness_57
| 58, _, _ => witness_58
| 59, _, _ => witness_59
| 60, _, _ => witness_60
| 61, _, _ => witness_61
| 62, _, _ => witness_62
| 63, _, _ => witness_63
| 64, _, _ => witness_64
| 65, _, _ => witness_65
| 66, _, _ => witness_66
| 67, _, _ => witness_67
| 68, _, _ => witness_68
| 69, _, _ => witness_69
| 70, _, _ => witness_70
| 71, _, _ => witness_71
| 72, _, _ => witness_72
| 73, _, _ => witness_73
| 74, _, _ => witness_74
| 75, _, _ => witness_75
| 76, _, _ => witness_76
| 77, _, _ => witness_77
| 78, _, _ => witness_78
| 79, _, _ => witness_79
| 80, _, _ => witness_80
| 81, _, _ => witness_81
| 82, _, _ => witness_82
| 83, _, _ => witness_83
| 84, _, _ => witness_84
| 85, _, _ => witness_85
| 86, _, _ => witness_86
| 87, _, _ => witness_87
| 88, _, _ => witness_88
| 89, _, _ => witness_89
| 90, _, _ => witness_90
| 91, _, _ => witness_91
| 92, _, _ => witness_92
| 93, _, _ => witness_93
| 94, _, _ => witness_94
| 95, _, _ => witness_95
| 96, _, _ => witness_96
| 97, _, _ => witness_97
| 98, _, _ => witness_98
| 99, _, _ => witness_99
| 100, _, _ => witness_100
| 101, _, _ => witness_101
| 102, _, _ => witness_102
| 103, _, _ => witness_103
| 104, _, _ => witness_104
| 105, _, _ => witness_105
| 106, _, _ => witness_106
| 107, _, _ => witness_107
| 108, _, _ => witness_108
| 109, _, _ => witness_109
| 110, _, _ => witness_110
| 111, _, _ => witness_111
| 112, _, _ => witness_112
| 113, _, _ => witness_113
| 114, _, _ => witness_114
| 115, _, _ => witness_115
| 116, _, _ => witness_116
| 117, _, _ => witness_117
| 118, _, _ => witness_118
| 119, _, _ => witness_119
| 120, _, _ => witness_120
| 121, _, _ => witness_121
| 122, _, _ => witness_122
| n + 123, _, h2 => by omega

/--
A091591: Proving a(n)>0 for n>122 would also prove Legendre's conjecture that there is a prime between n^2 and (n+1)^2. - _T. D. Noe_, Feb 28 2007
-/
theorem oeis_a091591_conjecture_1 :
  (∀ n : ℕ, n > 122 → a n > 0) → (∀ n : ℕ, n > 0 → ∃ p, p.Prime ∧ n^2 < p ∧ p < (n+1)^2) := by
  intro h_hyp n hn
  by_cases h_large : n > 122
  · -- Case 1: n > 122
    have h_card : 0 < a n := h_hyp n h_large
    have h_nonempty : (Finset.filter (fun p => p.Prime ∧ (p + 2).Prime) (Finset.Icc (n^2 + 1) ((n + 1)^2 - 3))).Nonempty := by
      rwa [a, Finset.card_pos] at h_card
    rcases h_nonempty with ⟨p, hp⟩
    rw [Finset.mem_filter] at hp
    rcases hp with ⟨h_icc, h_prime, _⟩
    rw [Finset.mem_Icc] at h_icc
    rcases h_icc with ⟨h_low, h_high⟩
    use p
    refine ⟨h_prime, ?_, ?_⟩
    · omega
    · omega
  · -- Case 2: n ≤ 122
    have h_le : n ≤ 122 := by omega
    exact witness_valid n hn h_le
