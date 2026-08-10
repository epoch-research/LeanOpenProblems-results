import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000

open Nat Int Rat Finset

/-- The $n$-th harmonic number $\sum_{k=1}^n 1/k$, as a rational number. -/
noncomputable def harmonic_number (n : ℕ) : ℚ :=
  (Finset.range n).sum fun k => (1 : ℚ) / (((k + 1) : ℕ) : ℚ)

/--
A309391: $a(n) = \gcd(n, A064169(n-2))$ for $n > 2$.
$A064169(m)$ is the numerator minus the denominator of the $m$-th harmonic number $H_m$.
The formula used is $a(n) = \gcd(n, |\text{num}(H_{n-2}) - \text{den}(H_{n-2})|)$.
-/
noncomputable def A309391 (n : ℕ) : ℕ :=
  -- The sequence is usually indexed starting from n=3, but we define it for n:ℕ.
  -- For the terms n=0,1,2, we can assign a default value of 0, as they are not part of the sequence.
  -- The OEIS listing starts at index 3.
  if n < 3 then 0 else
  let m : ℕ := n - 2
  let r : ℚ := harmonic_number m
  -- r.num is ℤ, r.den is ℕ. We compute the absolute difference of the numerator and denominator.
  let num_minus_den : ℤ := r.num - (r.den : ℤ)
  Nat.gcd n num_minus_den.natAbs

abbrev M : ℕ := 16843^3
abbrev f (i : ℕ) : ZMod M := (((i+1 : ℕ) : ZMod M)⁻¹)

opaque block_0 : ((Finset.Ico 0 100).sum f : ZMod M) = 2492743516078 := by decide
opaque block_1 : ((Finset.Ico 100 200).sum f : ZMod M) = 1672288710572 := by decide
opaque block_2 : ((Finset.Ico 200 300).sum f : ZMod M) = 172678634977 := by decide
opaque block_3 : ((Finset.Ico 300 400).sum f : ZMod M) = 3174624492187 := by decide
opaque block_4 : ((Finset.Ico 400 500).sum f : ZMod M) = 400331769876 := by decide
opaque block_5 : ((Finset.Ico 500 600).sum f : ZMod M) = 1106575843307 := by decide
opaque block_6 : ((Finset.Ico 600 700).sum f : ZMod M) = 1184119579109 := by decide
opaque block_7 : ((Finset.Ico 700 800).sum f : ZMod M) = 1587832900787 := by decide
opaque block_8 : ((Finset.Ico 800 900).sum f : ZMod M) = 1023049974057 := by decide
opaque block_9 : ((Finset.Ico 900 1000).sum f : ZMod M) = 3132384961908 := by decide
opaque block_10 : ((Finset.Ico 1000 1100).sum f : ZMod M) = 904665549249 := by decide
opaque block_11 : ((Finset.Ico 1100 1200).sum f : ZMod M) = 1301943680003 := by decide
opaque block_12 : ((Finset.Ico 1200 1300).sum f : ZMod M) = 2866487879278 := by decide
opaque block_13 : ((Finset.Ico 1300 1400).sum f : ZMod M) = 3739363286575 := by decide
opaque block_14 : ((Finset.Ico 1400 1500).sum f : ZMod M) = 4435816788513 := by decide
opaque block_15 : ((Finset.Ico 1500 1600).sum f : ZMod M) = 4741305438073 := by decide
opaque block_16 : ((Finset.Ico 1600 1700).sum f : ZMod M) = 378849003726 := by decide
opaque block_17 : ((Finset.Ico 1700 1800).sum f : ZMod M) = 1115987643354 := by decide
opaque block_18 : ((Finset.Ico 1800 1900).sum f : ZMod M) = 4207793004669 := by decide
opaque block_19 : ((Finset.Ico 1900 2000).sum f : ZMod M) = 2760863720158 := by decide
opaque block_20 : ((Finset.Ico 2000 2100).sum f : ZMod M) = 2355927162162 := by decide
opaque block_21 : ((Finset.Ico 2100 2200).sum f : ZMod M) = 429170207141 := by decide
opaque block_22 : ((Finset.Ico 2200 2300).sum f : ZMod M) = 4000950743021 := by decide
opaque block_23 : ((Finset.Ico 2300 2400).sum f : ZMod M) = 1259042469919 := by decide
opaque block_24 : ((Finset.Ico 2400 2500).sum f : ZMod M) = 4571069669204 := by decide
opaque block_25 : ((Finset.Ico 2500 2600).sum f : ZMod M) = 2965403963621 := by decide
opaque block_26 : ((Finset.Ico 2600 2700).sum f : ZMod M) = 4319621200574 := by decide
opaque block_27 : ((Finset.Ico 2700 2800).sum f : ZMod M) = 374721221475 := by decide
opaque block_28 : ((Finset.Ico 2800 2900).sum f : ZMod M) = 4531849162099 := by decide
opaque block_29 : ((Finset.Ico 2900 3000).sum f : ZMod M) = 1414475645660 := by decide
opaque block_30 : ((Finset.Ico 3000 3100).sum f : ZMod M) = 651096737332 := by decide
opaque block_31 : ((Finset.Ico 3100 3200).sum f : ZMod M) = 4580599068900 := by decide
opaque block_32 : ((Finset.Ico 3200 3300).sum f : ZMod M) = 961445878722 := by decide
opaque block_33 : ((Finset.Ico 3300 3400).sum f : ZMod M) = 3488981364933 := by decide
opaque block_34 : ((Finset.Ico 3400 3500).sum f : ZMod M) = 3700991875971 := by decide
opaque block_35 : ((Finset.Ico 3500 3600).sum f : ZMod M) = 4146800484825 := by decide
opaque block_36 : ((Finset.Ico 3600 3700).sum f : ZMod M) = 3384471094820 := by decide
opaque block_37 : ((Finset.Ico 3700 3800).sum f : ZMod M) = 2346798595163 := by decide
opaque block_38 : ((Finset.Ico 3800 3900).sum f : ZMod M) = 2187812916030 := by decide
opaque block_39 : ((Finset.Ico 3900 4000).sum f : ZMod M) = 3936118917988 := by decide
opaque block_40 : ((Finset.Ico 4000 4100).sum f : ZMod M) = 2671119804207 := by decide
opaque block_41 : ((Finset.Ico 4100 4200).sum f : ZMod M) = 2282004572335 := by decide
opaque block_42 : ((Finset.Ico 4200 4300).sum f : ZMod M) = 767876083679 := by decide
opaque block_43 : ((Finset.Ico 4300 4400).sum f : ZMod M) = 4774325782805 := by decide
opaque block_44 : ((Finset.Ico 4400 4500).sum f : ZMod M) = 2092955105483 := by decide
opaque block_45 : ((Finset.Ico 4500 4600).sum f : ZMod M) = 3549976999062 := by decide
opaque block_46 : ((Finset.Ico 4600 4700).sum f : ZMod M) = 2219683074742 := by decide
opaque block_47 : ((Finset.Ico 4700 4800).sum f : ZMod M) = 4751572091402 := by decide
opaque block_48 : ((Finset.Ico 4800 4900).sum f : ZMod M) = 3396693052594 := by decide
opaque block_49 : ((Finset.Ico 4900 5000).sum f : ZMod M) = 2648640477738 := by decide
opaque block_50 : ((Finset.Ico 5000 5100).sum f : ZMod M) = 3210983579758 := by decide
opaque block_51 : ((Finset.Ico 5100 5200).sum f : ZMod M) = 1566521613649 := by decide
opaque block_52 : ((Finset.Ico 5200 5300).sum f : ZMod M) = 2182943365757 := by decide
opaque block_53 : ((Finset.Ico 5300 5400).sum f : ZMod M) = 4105689758263 := by decide
opaque block_54 : ((Finset.Ico 5400 5500).sum f : ZMod M) = 1975025684630 := by decide
opaque block_55 : ((Finset.Ico 5500 5600).sum f : ZMod M) = 3875422326346 := by decide
opaque block_56 : ((Finset.Ico 5600 5700).sum f : ZMod M) = 3233819704976 := by decide
opaque block_57 : ((Finset.Ico 5700 5800).sum f : ZMod M) = 4071110372271 := by decide
opaque block_58 : ((Finset.Ico 5800 5900).sum f : ZMod M) = 1479578301728 := by decide
opaque block_59 : ((Finset.Ico 5900 6000).sum f : ZMod M) = 1588340361533 := by decide
opaque block_60 : ((Finset.Ico 6000 6100).sum f : ZMod M) = 2587547475763 := by decide
opaque block_61 : ((Finset.Ico 6100 6200).sum f : ZMod M) = 2014553460925 := by decide
opaque block_62 : ((Finset.Ico 6200 6300).sum f : ZMod M) = 596354864661 := by decide
opaque block_63 : ((Finset.Ico 6300 6400).sum f : ZMod M) = 1555439143411 := by decide
opaque block_64 : ((Finset.Ico 6400 6500).sum f : ZMod M) = 1063676624762 := by decide
opaque block_65 : ((Finset.Ico 6500 6600).sum f : ZMod M) = 722289195422 := by decide
opaque block_66 : ((Finset.Ico 6600 6700).sum f : ZMod M) = 3317432932852 := by decide
opaque block_67 : ((Finset.Ico 6700 6800).sum f : ZMod M) = 3438345474565 := by decide
opaque block_68 : ((Finset.Ico 6800 6900).sum f : ZMod M) = 491540790525 := by decide
opaque block_69 : ((Finset.Ico 6900 7000).sum f : ZMod M) = 4601837647159 := by decide
opaque block_70 : ((Finset.Ico 7000 7100).sum f : ZMod M) = 3602491007309 := by decide
opaque block_71 : ((Finset.Ico 7100 7200).sum f : ZMod M) = 1771264369479 := by decide
opaque block_72 : ((Finset.Ico 7200 7300).sum f : ZMod M) = 1641076265401 := by decide
opaque block_73 : ((Finset.Ico 7300 7400).sum f : ZMod M) = 3104508488297 := by decide
opaque block_74 : ((Finset.Ico 7400 7500).sum f : ZMod M) = 2914322808164 := by decide
opaque block_75 : ((Finset.Ico 7500 7600).sum f : ZMod M) = 1196190927420 := by decide
opaque block_76 : ((Finset.Ico 7600 7700).sum f : ZMod M) = 2595801871275 := by decide
opaque block_77 : ((Finset.Ico 7700 7800).sum f : ZMod M) = 491506439962 := by decide
opaque block_78 : ((Finset.Ico 7800 7900).sum f : ZMod M) = 1329900318793 := by decide
opaque block_79 : ((Finset.Ico 7900 8000).sum f : ZMod M) = 2238637938098 := by decide
opaque block_80 : ((Finset.Ico 8000 8100).sum f : ZMod M) = 476646240388 := by decide
opaque block_81 : ((Finset.Ico 8100 8200).sum f : ZMod M) = 1224678279069 := by decide
opaque block_82 : ((Finset.Ico 8200 8300).sum f : ZMod M) = 4508770588903 := by decide
opaque block_83 : ((Finset.Ico 8300 8400).sum f : ZMod M) = 773800577209 := by decide
opaque block_84 : ((Finset.Ico 8400 8500).sum f : ZMod M) = 945264302746 := by decide
opaque block_85 : ((Finset.Ico 8500 8600).sum f : ZMod M) = 4356416878945 := by decide
opaque block_86 : ((Finset.Ico 8600 8700).sum f : ZMod M) = 3106781354914 := by decide
opaque block_87 : ((Finset.Ico 8700 8800).sum f : ZMod M) = 2852469874663 := by decide
opaque block_88 : ((Finset.Ico 8800 8900).sum f : ZMod M) = 512505819834 := by decide
opaque block_89 : ((Finset.Ico 8900 9000).sum f : ZMod M) = 1820008051320 := by decide
opaque block_90 : ((Finset.Ico 9000 9100).sum f : ZMod M) = 3574118156400 := by decide
opaque block_91 : ((Finset.Ico 9100 9200).sum f : ZMod M) = 3931827558547 := by decide
opaque block_92 : ((Finset.Ico 9200 9300).sum f : ZMod M) = 2448189672637 := by decide
opaque block_93 : ((Finset.Ico 9300 9400).sum f : ZMod M) = 4044756403599 := by decide
opaque block_94 : ((Finset.Ico 9400 9500).sum f : ZMod M) = 2015281427295 := by decide
opaque block_95 : ((Finset.Ico 9500 9600).sum f : ZMod M) = 1160014837536 := by decide
opaque block_96 : ((Finset.Ico 9600 9700).sum f : ZMod M) = 4405772198857 := by decide
opaque block_97 : ((Finset.Ico 9700 9800).sum f : ZMod M) = 2804276635745 := by decide
opaque block_98 : ((Finset.Ico 9800 9900).sum f : ZMod M) = 4249217201940 := by decide
opaque block_99 : ((Finset.Ico 9900 10000).sum f : ZMod M) = 1152477025752 := by decide
opaque block_100 : ((Finset.Ico 10000 10100).sum f : ZMod M) = 2023157357095 := by decide
opaque block_101 : ((Finset.Ico 10100 10200).sum f : ZMod M) = 4345270218892 := by decide
opaque block_102 : ((Finset.Ico 10200 10300).sum f : ZMod M) = 3582521726903 := by decide
opaque block_103 : ((Finset.Ico 10300 10400).sum f : ZMod M) = 1263302288419 := by decide
opaque block_104 : ((Finset.Ico 10400 10500).sum f : ZMod M) = 791554241292 := by decide
opaque block_105 : ((Finset.Ico 10500 10600).sum f : ZMod M) = 3273871712861 := by decide
opaque block_106 : ((Finset.Ico 10600 10700).sum f : ZMod M) = 3679769331404 := by decide
opaque block_107 : ((Finset.Ico 10700 10800).sum f : ZMod M) = 3948509433872 := by decide
opaque block_108 : ((Finset.Ico 10800 10900).sum f : ZMod M) = 4336295399767 := by decide
opaque block_109 : ((Finset.Ico 10900 11000).sum f : ZMod M) = 2152685205163 := by decide
opaque block_110 : ((Finset.Ico 11000 11100).sum f : ZMod M) = 4113876649232 := by decide
opaque block_111 : ((Finset.Ico 11100 11200).sum f : ZMod M) = 3226241067936 := by decide
opaque block_112 : ((Finset.Ico 11200 11300).sum f : ZMod M) = 316317092524 := by decide
opaque block_113 : ((Finset.Ico 11300 11400).sum f : ZMod M) = 2696916088306 := by decide
opaque block_114 : ((Finset.Ico 11400 11500).sum f : ZMod M) = 4483679938794 := by decide
opaque block_115 : ((Finset.Ico 11500 11600).sum f : ZMod M) = 1592026250194 := by decide
opaque block_116 : ((Finset.Ico 11600 11700).sum f : ZMod M) = 4421611059964 := by decide
opaque block_117 : ((Finset.Ico 11700 11800).sum f : ZMod M) = 1573195190471 := by decide
opaque block_118 : ((Finset.Ico 11800 11900).sum f : ZMod M) = 3097268369114 := by decide
opaque block_119 : ((Finset.Ico 11900 12000).sum f : ZMod M) = 858105112040 := by decide
opaque block_120 : ((Finset.Ico 12000 12100).sum f : ZMod M) = 1967503323339 := by decide
opaque block_121 : ((Finset.Ico 12100 12200).sum f : ZMod M) = 70105671145 := by decide
opaque block_122 : ((Finset.Ico 12200 12300).sum f : ZMod M) = 1828921721572 := by decide
opaque block_123 : ((Finset.Ico 12300 12400).sum f : ZMod M) = 3223779148874 := by decide
opaque block_124 : ((Finset.Ico 12400 12500).sum f : ZMod M) = 2558090942231 := by decide
opaque block_125 : ((Finset.Ico 12500 12600).sum f : ZMod M) = 629550973919 := by decide
opaque block_126 : ((Finset.Ico 12600 12700).sum f : ZMod M) = 2081284562938 := by decide
opaque block_127 : ((Finset.Ico 12700 12800).sum f : ZMod M) = 4204236692438 := by decide
opaque block_128 : ((Finset.Ico 12800 12900).sum f : ZMod M) = 3226412951709 := by decide
opaque block_129 : ((Finset.Ico 12900 13000).sum f : ZMod M) = 3082774132655 := by decide
opaque block_130 : ((Finset.Ico 13000 13100).sum f : ZMod M) = 413733676391 := by decide
opaque block_131 : ((Finset.Ico 13100 13200).sum f : ZMod M) = 793737105373 := by decide
opaque block_132 : ((Finset.Ico 13200 13300).sum f : ZMod M) = 1924624702408 := by decide
opaque block_133 : ((Finset.Ico 13300 13400).sum f : ZMod M) = 126042230639 := by decide
opaque block_134 : ((Finset.Ico 13400 13500).sum f : ZMod M) = 756351150780 := by decide
opaque block_135 : ((Finset.Ico 13500 13600).sum f : ZMod M) = 1592420382990 := by decide
opaque block_136 : ((Finset.Ico 13600 13700).sum f : ZMod M) = 4767231761208 := by decide
opaque block_137 : ((Finset.Ico 13700 13800).sum f : ZMod M) = 1450724547169 := by decide
opaque block_138 : ((Finset.Ico 13800 13900).sum f : ZMod M) = 860984154616 := by decide
opaque block_139 : ((Finset.Ico 13900 14000).sum f : ZMod M) = 4499286128485 := by decide
opaque block_140 : ((Finset.Ico 14000 14100).sum f : ZMod M) = 750677646539 := by decide
opaque block_141 : ((Finset.Ico 14100 14200).sum f : ZMod M) = 4324853179683 := by decide
opaque block_142 : ((Finset.Ico 14200 14300).sum f : ZMod M) = 2234206449284 := by decide
opaque block_143 : ((Finset.Ico 14300 14400).sum f : ZMod M) = 3752696744057 := by decide
opaque block_144 : ((Finset.Ico 14400 14500).sum f : ZMod M) = 69228875468 := by decide
opaque block_145 : ((Finset.Ico 14500 14600).sum f : ZMod M) = 4470303298663 := by decide
opaque block_146 : ((Finset.Ico 14600 14700).sum f : ZMod M) = 1693812016470 := by decide
opaque block_147 : ((Finset.Ico 14700 14800).sum f : ZMod M) = 769030965782 := by decide
opaque block_148 : ((Finset.Ico 14800 14900).sum f : ZMod M) = 1166408414193 := by decide
opaque block_149 : ((Finset.Ico 14900 15000).sum f : ZMod M) = 1228718574404 := by decide
opaque block_150 : ((Finset.Ico 15000 15100).sum f : ZMod M) = 1938960411286 := by decide
opaque block_151 : ((Finset.Ico 15100 15200).sum f : ZMod M) = 1398067593989 := by decide
opaque block_152 : ((Finset.Ico 15200 15300).sum f : ZMod M) = 2012169470528 := by decide
opaque block_153 : ((Finset.Ico 15300 15400).sum f : ZMod M) = 2462779516442 := by decide
opaque block_154 : ((Finset.Ico 15400 15500).sum f : ZMod M) = 2939482891417 := by decide
opaque block_155 : ((Finset.Ico 15500 15600).sum f : ZMod M) = 35286005863 := by decide
opaque block_156 : ((Finset.Ico 15600 15700).sum f : ZMod M) = 975835070465 := by decide
opaque block_157 : ((Finset.Ico 15700 15800).sum f : ZMod M) = 1693314774320 := by decide
opaque block_158 : ((Finset.Ico 15800 15900).sum f : ZMod M) = 998213319685 := by decide
opaque block_159 : ((Finset.Ico 15900 16000).sum f : ZMod M) = 2419289843257 := by decide
opaque block_160 : ((Finset.Ico 16000 16100).sum f : ZMod M) = 3599822339383 := by decide
opaque block_161 : ((Finset.Ico 16100 16200).sum f : ZMod M) = 4224092856692 := by decide
opaque block_162 : ((Finset.Ico 16200 16300).sum f : ZMod M) = 2930980998319 := by decide
opaque block_163 : ((Finset.Ico 16300 16400).sum f : ZMod M) = 3482176622388 := by decide
opaque block_164 : ((Finset.Ico 16400 16500).sum f : ZMod M) = 3882202685396 := by decide
opaque block_165 : ((Finset.Ico 16500 16600).sum f : ZMod M) = 280668986540 := by decide
opaque block_166 : ((Finset.Ico 16600 16700).sum f : ZMod M) = 4035532809555 := by decide
opaque block_167 : ((Finset.Ico 16700 16800).sum f : ZMod M) = 1929128158165 := by decide
opaque block_168 : ((Finset.Ico 16800 16842).sum f : ZMod M) = 2520171261224 := by decide

opaque tail_168 : ((Finset.Ico 16800 16842).sum f : ZMod M) = 2520171261224 := by
  simpa using block_168
opaque tail_167 : ((Finset.Ico 16700 16842).sum f : ZMod M) = 4449299419389 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 16700 ≤ 16800) (by norm_num : 16800 ≤ 16842)]
  rw [block_167, tail_168]
  decide
opaque tail_166 : ((Finset.Ico 16600 16842).sum f : ZMod M) = 3706697999837 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 16600 ≤ 16700) (by norm_num : 16700 ≤ 16842)]
  rw [block_166, tail_167]
  decide
opaque tail_165 : ((Finset.Ico 16500 16842).sum f : ZMod M) = 3987366986377 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 16500 ≤ 16600) (by norm_num : 16600 ≤ 16842)]
  rw [block_165, tail_166]
  decide
opaque tail_164 : ((Finset.Ico 16400 16842).sum f : ZMod M) = 3091435442666 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 16400 ≤ 16500) (by norm_num : 16500 ≤ 16842)]
  rw [block_164, tail_165]
  decide
opaque tail_163 : ((Finset.Ico 16300 16842).sum f : ZMod M) = 1795477835947 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 16300 ≤ 16400) (by norm_num : 16400 ≤ 16842)]
  rw [block_163, tail_164]
  decide
opaque tail_162 : ((Finset.Ico 16200 16842).sum f : ZMod M) = 4726458834266 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 16200 ≤ 16300) (by norm_num : 16300 ≤ 16842)]
  rw [block_162, tail_163]
  decide
opaque tail_161 : ((Finset.Ico 16100 16842).sum f : ZMod M) = 4172417461851 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 16100 ≤ 16200) (by norm_num : 16200 ≤ 16842)]
  rw [block_161, tail_162]
  decide
opaque tail_160 : ((Finset.Ico 16000 16842).sum f : ZMod M) = 2994105572127 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 16000 ≤ 16100) (by norm_num : 16100 ≤ 16842)]
  rw [block_160, tail_161]
  decide
opaque tail_159 : ((Finset.Ico 15900 16842).sum f : ZMod M) = 635261186277 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 15900 ≤ 16000) (by norm_num : 16000 ≤ 16842)]
  rw [block_159, tail_160]
  decide
opaque tail_158 : ((Finset.Ico 15800 16842).sum f : ZMod M) = 1633474505962 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 15800 ≤ 15900) (by norm_num : 15900 ≤ 16842)]
  rw [block_158, tail_159]
  decide
opaque tail_157 : ((Finset.Ico 15700 16842).sum f : ZMod M) = 3326789280282 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 15700 ≤ 15800) (by norm_num : 15800 ≤ 16842)]
  rw [block_157, tail_158]
  decide
opaque tail_156 : ((Finset.Ico 15600 16842).sum f : ZMod M) = 4302624350747 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 15600 ≤ 15700) (by norm_num : 15700 ≤ 16842)]
  rw [block_156, tail_157]
  decide
opaque tail_155 : ((Finset.Ico 15500 16842).sum f : ZMod M) = 4337910356610 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 15500 ≤ 15600) (by norm_num : 15600 ≤ 16842)]
  rw [block_155, tail_156]
  decide
opaque tail_154 : ((Finset.Ico 15400 16842).sum f : ZMod M) = 2499259018920 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 15400 ≤ 15500) (by norm_num : 15500 ≤ 16842)]
  rw [block_154, tail_155]
  decide
opaque tail_153 : ((Finset.Ico 15300 16842).sum f : ZMod M) = 183904306255 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 15300 ≤ 15400) (by norm_num : 15400 ≤ 16842)]
  rw [block_153, tail_154]
  decide
opaque tail_152 : ((Finset.Ico 15200 16842).sum f : ZMod M) = 2196073776783 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 15200 ≤ 15300) (by norm_num : 15300 ≤ 16842)]
  rw [block_152, tail_153]
  decide
opaque tail_151 : ((Finset.Ico 15100 16842).sum f : ZMod M) = 3594141370772 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 15100 ≤ 15200) (by norm_num : 15200 ≤ 16842)]
  rw [block_151, tail_152]
  decide
opaque tail_150 : ((Finset.Ico 15000 16842).sum f : ZMod M) = 754967552951 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 15000 ≤ 15100) (by norm_num : 15100 ≤ 16842)]
  rw [block_150, tail_151]
  decide
opaque tail_149 : ((Finset.Ico 14900 16842).sum f : ZMod M) = 1983686127355 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 14900 ≤ 15000) (by norm_num : 15000 ≤ 16842)]
  rw [block_149, tail_150]
  decide
opaque tail_148 : ((Finset.Ico 14800 16842).sum f : ZMod M) = 3150094541548 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 14800 ≤ 14900) (by norm_num : 14900 ≤ 16842)]
  rw [block_148, tail_149]
  decide
opaque tail_147 : ((Finset.Ico 14700 16842).sum f : ZMod M) = 3919125507330 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 14700 ≤ 14800) (by norm_num : 14800 ≤ 16842)]
  rw [block_147, tail_148]
  decide
opaque tail_146 : ((Finset.Ico 14600 16842).sum f : ZMod M) = 834803294693 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 14600 ≤ 14700) (by norm_num : 14700 ≤ 16842)]
  rw [block_146, tail_147]
  decide
opaque tail_145 : ((Finset.Ico 14500 16842).sum f : ZMod M) = 526972364249 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 14500 ≤ 14600) (by norm_num : 14600 ≤ 16842)]
  rw [block_145, tail_146]
  decide
opaque tail_144 : ((Finset.Ico 14400 16842).sum f : ZMod M) = 596201239717 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 14400 ≤ 14500) (by norm_num : 14500 ≤ 16842)]
  rw [block_144, tail_145]
  decide
opaque tail_143 : ((Finset.Ico 14300 16842).sum f : ZMod M) = 4348897983774 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 14300 ≤ 14400) (by norm_num : 14400 ≤ 16842)]
  rw [block_143, tail_144]
  decide
opaque tail_142 : ((Finset.Ico 14200 16842).sum f : ZMod M) = 1804970203951 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 14200 ≤ 14300) (by norm_num : 14300 ≤ 16842)]
  rw [block_142, tail_143]
  decide
opaque tail_141 : ((Finset.Ico 14100 16842).sum f : ZMod M) = 1351689154527 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 14100 ≤ 14200) (by norm_num : 14200 ≤ 16842)]
  rw [block_141, tail_142]
  decide
opaque tail_140 : ((Finset.Ico 14000 16842).sum f : ZMod M) = 2102366801066 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 14000 ≤ 14100) (by norm_num : 14100 ≤ 16842)]
  rw [block_140, tail_141]
  decide
opaque tail_139 : ((Finset.Ico 13900 16842).sum f : ZMod M) = 1823518700444 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 13900 ≤ 14000) (by norm_num : 14000 ≤ 16842)]
  rw [block_139, tail_140]
  decide
opaque tail_138 : ((Finset.Ico 13800 16842).sum f : ZMod M) = 2684502855060 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 13800 ≤ 13900) (by norm_num : 13900 ≤ 16842)]
  rw [block_138, tail_139]
  decide
opaque tail_137 : ((Finset.Ico 13700 16842).sum f : ZMod M) = 4135227402229 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 13700 ≤ 13800) (by norm_num : 13800 ≤ 16842)]
  rw [block_137, tail_138]
  decide
opaque tail_136 : ((Finset.Ico 13600 16842).sum f : ZMod M) = 4124324934330 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 13600 ≤ 13700) (by norm_num : 13700 ≤ 16842)]
  rw [block_136, tail_137]
  decide
opaque tail_135 : ((Finset.Ico 13500 16842).sum f : ZMod M) = 938611088213 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 13500 ≤ 13600) (by norm_num : 13600 ≤ 16842)]
  rw [block_135, tail_136]
  decide
opaque tail_134 : ((Finset.Ico 13400 16842).sum f : ZMod M) = 1694962238993 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 13400 ≤ 13500) (by norm_num : 13500 ≤ 16842)]
  rw [block_134, tail_135]
  decide
opaque tail_133 : ((Finset.Ico 13300 16842).sum f : ZMod M) = 1821004469632 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 13300 ≤ 13400) (by norm_num : 13400 ≤ 16842)]
  rw [block_133, tail_134]
  decide
opaque tail_132 : ((Finset.Ico 13200 16842).sum f : ZMod M) = 3745629172040 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 13200 ≤ 13300) (by norm_num : 13300 ≤ 16842)]
  rw [block_132, tail_133]
  decide
opaque tail_131 : ((Finset.Ico 13100 16842).sum f : ZMod M) = 4539366277413 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 13100 ≤ 13200) (by norm_num : 13200 ≤ 16842)]
  rw [block_131, tail_132]
  decide
opaque tail_130 : ((Finset.Ico 13000 16842).sum f : ZMod M) = 174965724697 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 13000 ≤ 13100) (by norm_num : 13100 ≤ 16842)]
  rw [block_130, tail_131]
  decide
opaque tail_129 : ((Finset.Ico 12900 16842).sum f : ZMod M) = 3257739857352 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 12900 ≤ 13000) (by norm_num : 13000 ≤ 16842)]
  rw [block_129, tail_130]
  decide
opaque tail_128 : ((Finset.Ico 12800 16842).sum f : ZMod M) = 1706018579954 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 12800 ≤ 12900) (by norm_num : 12900 ≤ 16842)]
  rw [block_128, tail_129]
  decide
opaque tail_127 : ((Finset.Ico 12700 16842).sum f : ZMod M) = 1132121043285 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 12700 ≤ 12800) (by norm_num : 12800 ≤ 16842)]
  rw [block_127, tail_128]
  decide
opaque tail_126 : ((Finset.Ico 12600 16842).sum f : ZMod M) = 3213405606223 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 12600 ≤ 12700) (by norm_num : 12700 ≤ 16842)]
  rw [block_126, tail_127]
  decide
opaque tail_125 : ((Finset.Ico 12500 16842).sum f : ZMod M) = 3842956580142 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 12500 ≤ 12600) (by norm_num : 12600 ≤ 16842)]
  rw [block_125, tail_126]
  decide
opaque tail_124 : ((Finset.Ico 12400 16842).sum f : ZMod M) = 1622913293266 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 12400 ≤ 12500) (by norm_num : 12500 ≤ 16842)]
  rw [block_124, tail_125]
  decide
opaque tail_123 : ((Finset.Ico 12300 16842).sum f : ZMod M) = 68558213033 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 12300 ≤ 12400) (by norm_num : 12400 ≤ 16842)]
  rw [block_123, tail_124]
  decide
opaque tail_122 : ((Finset.Ico 12200 16842).sum f : ZMod M) = 1897479934605 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 12200 ≤ 12300) (by norm_num : 12300 ≤ 16842)]
  rw [block_122, tail_123]
  decide
opaque tail_121 : ((Finset.Ico 12100 16842).sum f : ZMod M) = 1967585605750 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 12100 ≤ 12200) (by norm_num : 12200 ≤ 16842)]
  rw [block_121, tail_122]
  decide
opaque tail_120 : ((Finset.Ico 12000 16842).sum f : ZMod M) = 3935088929089 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 12000 ≤ 12100) (by norm_num : 12100 ≤ 16842)]
  rw [block_120, tail_121]
  decide
opaque tail_119 : ((Finset.Ico 11900 16842).sum f : ZMod M) = 15059812022 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 11900 ≤ 12000) (by norm_num : 12000 ≤ 16842)]
  rw [block_119, tail_120]
  decide
opaque tail_118 : ((Finset.Ico 11800 16842).sum f : ZMod M) = 3112328181136 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 11800 ≤ 11900) (by norm_num : 11900 ≤ 16842)]
  rw [block_118, tail_119]
  decide
opaque tail_117 : ((Finset.Ico 11700 16842).sum f : ZMod M) = 4685523371607 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 11700 ≤ 11800) (by norm_num : 11800 ≤ 16842)]
  rw [block_117, tail_118]
  decide
opaque tail_116 : ((Finset.Ico 11600 16842).sum f : ZMod M) = 4329000202464 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 11600 ≤ 11700) (by norm_num : 11700 ≤ 16842)]
  rw [block_116, tail_117]
  decide
opaque tail_115 : ((Finset.Ico 11500 16842).sum f : ZMod M) = 1142892223551 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 11500 ≤ 11600) (by norm_num : 11600 ≤ 16842)]
  rw [block_115, tail_116]
  decide
opaque tail_114 : ((Finset.Ico 11400 16842).sum f : ZMod M) = 848437933238 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 11400 ≤ 11500) (by norm_num : 11500 ≤ 16842)]
  rw [block_114, tail_115]
  decide
opaque tail_113 : ((Finset.Ico 11300 16842).sum f : ZMod M) = 3545354021544 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 11300 ≤ 11400) (by norm_num : 11400 ≤ 16842)]
  rw [block_113, tail_114]
  decide
opaque tail_112 : ((Finset.Ico 11200 16842).sum f : ZMod M) = 3861671114068 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 11200 ≤ 11300) (by norm_num : 11300 ≤ 16842)]
  rw [block_112, tail_113]
  decide
opaque tail_111 : ((Finset.Ico 11100 16842).sum f : ZMod M) = 2309777952897 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 11100 ≤ 11200) (by norm_num : 11200 ≤ 16842)]
  rw [block_111, tail_112]
  decide
opaque tail_110 : ((Finset.Ico 11000 16842).sum f : ZMod M) = 1645520373022 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 11000 ≤ 11100) (by norm_num : 11100 ≤ 16842)]
  rw [block_110, tail_111]
  decide
opaque tail_109 : ((Finset.Ico 10900 16842).sum f : ZMod M) = 3798205578185 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 10900 ≤ 11000) (by norm_num : 11000 ≤ 16842)]
  rw [block_109, tail_110]
  decide
opaque tail_108 : ((Finset.Ico 10800 16842).sum f : ZMod M) = 3356366748845 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 10800 ≤ 10900) (by norm_num : 10900 ≤ 16842)]
  rw [block_108, tail_109]
  decide
opaque tail_107 : ((Finset.Ico 10700 16842).sum f : ZMod M) = 2526741953610 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 10700 ≤ 10800) (by norm_num : 10800 ≤ 16842)]
  rw [block_107, tail_108]
  decide
opaque tail_106 : ((Finset.Ico 10600 16842).sum f : ZMod M) = 1428377055907 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 10600 ≤ 10700) (by norm_num : 10700 ≤ 16842)]
  rw [block_106, tail_107]
  decide
opaque tail_105 : ((Finset.Ico 10500 16842).sum f : ZMod M) = 4702248768768 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 10500 ≤ 10600) (by norm_num : 10600 ≤ 16842)]
  rw [block_105, tail_106]
  decide
opaque tail_104 : ((Finset.Ico 10400 16842).sum f : ZMod M) = 715668780953 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 10400 ≤ 10500) (by norm_num : 10500 ≤ 16842)]
  rw [block_104, tail_105]
  decide
opaque tail_103 : ((Finset.Ico 10300 16842).sum f : ZMod M) = 1978971069372 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 10300 ≤ 10400) (by norm_num : 10400 ≤ 16842)]
  rw [block_103, tail_104]
  decide
opaque tail_102 : ((Finset.Ico 10200 16842).sum f : ZMod M) = 783358567168 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 10200 ≤ 10300) (by norm_num : 10300 ≤ 16842)]
  rw [block_102, tail_103]
  decide
opaque tail_101 : ((Finset.Ico 10100 16842).sum f : ZMod M) = 350494556953 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 10100 ≤ 10200) (by norm_num : 10200 ≤ 16842)]
  rw [block_101, tail_102]
  decide
opaque tail_100 : ((Finset.Ico 10000 16842).sum f : ZMod M) = 2373651914048 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 10000 ≤ 10100) (by norm_num : 10100 ≤ 16842)]
  rw [block_100, tail_101]
  decide
opaque tail_99 : ((Finset.Ico 9900 16842).sum f : ZMod M) = 3526128939800 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 9900 ≤ 10000) (by norm_num : 10000 ≤ 16842)]
  rw [block_99, tail_100]
  decide
opaque tail_98 : ((Finset.Ico 9800 16842).sum f : ZMod M) = 2997211912633 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 9800 ≤ 9900) (by norm_num : 9900 ≤ 16842)]
  rw [block_98, tail_99]
  decide
opaque tail_97 : ((Finset.Ico 9700 16842).sum f : ZMod M) = 1023354319271 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 9700 ≤ 9800) (by norm_num : 9800 ≤ 16842)]
  rw [block_97, tail_98]
  decide
opaque tail_96 : ((Finset.Ico 9600 16842).sum f : ZMod M) = 650992289021 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 9600 ≤ 9700) (by norm_num : 9700 ≤ 16842)]
  rw [block_96, tail_97]
  decide
opaque tail_95 : ((Finset.Ico 9500 16842).sum f : ZMod M) = 1811007126557 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 9500 ≤ 9600) (by norm_num : 9600 ≤ 16842)]
  rw [block_95, tail_96]
  decide
opaque tail_94 : ((Finset.Ico 9400 16842).sum f : ZMod M) = 3826288553852 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 9400 ≤ 9500) (by norm_num : 9500 ≤ 16842)]
  rw [block_94, tail_95]
  decide
opaque tail_93 : ((Finset.Ico 9300 16842).sum f : ZMod M) = 3092910728344 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 9300 ≤ 9400) (by norm_num : 9400 ≤ 16842)]
  rw [block_93, tail_94]
  decide
opaque tail_92 : ((Finset.Ico 9200 16842).sum f : ZMod M) = 762966171874 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 9200 ≤ 9300) (by norm_num : 9300 ≤ 16842)]
  rw [block_92, tail_93]
  decide
opaque tail_91 : ((Finset.Ico 9100 16842).sum f : ZMod M) = 4694793730421 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 9100 ≤ 9200) (by norm_num : 9200 ≤ 16842)]
  rw [block_91, tail_92]
  decide
opaque tail_90 : ((Finset.Ico 9000 16842).sum f : ZMod M) = 3490777657714 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 9000 ≤ 9100) (by norm_num : 9100 ≤ 16842)]
  rw [block_90, tail_91]
  decide
opaque tail_89 : ((Finset.Ico 8900 16842).sum f : ZMod M) = 532651479927 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 8900 ≤ 9000) (by norm_num : 9000 ≤ 16842)]
  rw [block_89, tail_90]
  decide
opaque tail_88 : ((Finset.Ico 8800 16842).sum f : ZMod M) = 1045157299761 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 8800 ≤ 8900) (by norm_num : 8900 ≤ 16842)]
  rw [block_88, tail_89]
  decide
opaque tail_87 : ((Finset.Ico 8700 16842).sum f : ZMod M) = 3897627174424 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 8700 ≤ 8800) (by norm_num : 8800 ≤ 16842)]
  rw [block_87, tail_88]
  decide
opaque tail_86 : ((Finset.Ico 8600 16842).sum f : ZMod M) = 2226274300231 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 8600 ≤ 8700) (by norm_num : 8700 ≤ 16842)]
  rw [block_86, tail_87]
  decide
opaque tail_85 : ((Finset.Ico 8500 16842).sum f : ZMod M) = 1804556950069 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 8500 ≤ 8600) (by norm_num : 8600 ≤ 16842)]
  rw [block_85, tail_86]
  decide
opaque tail_84 : ((Finset.Ico 8400 16842).sum f : ZMod M) = 2749821252815 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 8400 ≤ 8500) (by norm_num : 8500 ≤ 16842)]
  rw [block_84, tail_85]
  decide
opaque tail_83 : ((Finset.Ico 8300 16842).sum f : ZMod M) = 3523621830024 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 8300 ≤ 8400) (by norm_num : 8400 ≤ 16842)]
  rw [block_83, tail_84]
  decide
opaque tail_82 : ((Finset.Ico 8200 16842).sum f : ZMod M) = 3254258189820 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 8200 ≤ 8300) (by norm_num : 8300 ≤ 16842)]
  rw [block_82, tail_83]
  decide
opaque tail_81 : ((Finset.Ico 8100 16842).sum f : ZMod M) = 4478936468889 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 8100 ≤ 8200) (by norm_num : 8200 ≤ 16842)]
  rw [block_81, tail_82]
  decide
opaque tail_80 : ((Finset.Ico 8000 16842).sum f : ZMod M) = 177448480170 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 8000 ≤ 8100) (by norm_num : 8100 ≤ 16842)]
  rw [block_80, tail_81]
  decide
opaque tail_79 : ((Finset.Ico 7900 16842).sum f : ZMod M) = 2416086418268 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 7900 ≤ 8000) (by norm_num : 8000 ≤ 16842)]
  rw [block_79, tail_80]
  decide
opaque tail_78 : ((Finset.Ico 7800 16842).sum f : ZMod M) = 3745986737061 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 7800 ≤ 7900) (by norm_num : 7900 ≤ 16842)]
  rw [block_78, tail_79]
  decide
opaque tail_77 : ((Finset.Ico 7700 16842).sum f : ZMod M) = 4237493177023 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 7700 ≤ 7800) (by norm_num : 7800 ≤ 16842)]
  rw [block_77, tail_78]
  decide
opaque tail_76 : ((Finset.Ico 7600 16842).sum f : ZMod M) = 2055160819191 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 7600 ≤ 7700) (by norm_num : 7700 ≤ 16842)]
  rw [block_76, tail_77]
  decide
opaque tail_75 : ((Finset.Ico 7500 16842).sum f : ZMod M) = 3251351746611 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 7500 ≤ 7600) (by norm_num : 7600 ≤ 16842)]
  rw [block_75, tail_76]
  decide
opaque tail_74 : ((Finset.Ico 7400 16842).sum f : ZMod M) = 1387540325668 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 7400 ≤ 7500) (by norm_num : 7500 ≤ 16842)]
  rw [block_74, tail_75]
  decide
opaque tail_73 : ((Finset.Ico 7300 16842).sum f : ZMod M) = 4492048813965 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 7300 ≤ 7400) (by norm_num : 7400 ≤ 16842)]
  rw [block_73, tail_74]
  decide
opaque tail_72 : ((Finset.Ico 7200 16842).sum f : ZMod M) = 1354990850259 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 7200 ≤ 7300) (by norm_num : 7300 ≤ 16842)]
  rw [block_72, tail_73]
  decide
opaque tail_71 : ((Finset.Ico 7100 16842).sum f : ZMod M) = 3126255219738 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 7100 ≤ 7200) (by norm_num : 7200 ≤ 16842)]
  rw [block_71, tail_72]
  decide
opaque tail_70 : ((Finset.Ico 7000 16842).sum f : ZMod M) = 1950611997940 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 7000 ≤ 7100) (by norm_num : 7100 ≤ 16842)]
  rw [block_70, tail_71]
  decide
opaque tail_69 : ((Finset.Ico 6900 16842).sum f : ZMod M) = 1774315415992 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 6900 ≤ 7000) (by norm_num : 7000 ≤ 16842)]
  rw [block_69, tail_70]
  decide
opaque tail_68 : ((Finset.Ico 6800 16842).sum f : ZMod M) = 2265856206517 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 6800 ≤ 6900) (by norm_num : 6900 ≤ 16842)]
  rw [block_68, tail_69]
  decide
opaque tail_67 : ((Finset.Ico 6700 16842).sum f : ZMod M) = 926067451975 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 6700 ≤ 6800) (by norm_num : 6800 ≤ 16842)]
  rw [block_67, tail_68]
  decide
opaque tail_66 : ((Finset.Ico 6600 16842).sum f : ZMod M) = 4243500384827 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 6600 ≤ 6700) (by norm_num : 6700 ≤ 16842)]
  rw [block_66, tail_67]
  decide
opaque tail_65 : ((Finset.Ico 6500 16842).sum f : ZMod M) = 187655351142 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 6500 ≤ 6600) (by norm_num : 6600 ≤ 16842)]
  rw [block_65, tail_66]
  decide
opaque tail_64 : ((Finset.Ico 6400 16842).sum f : ZMod M) = 1251331975904 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 6400 ≤ 6500) (by norm_num : 6500 ≤ 16842)]
  rw [block_64, tail_65]
  decide
opaque tail_63 : ((Finset.Ico 6300 16842).sum f : ZMod M) = 2806771119315 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 6300 ≤ 6400) (by norm_num : 6400 ≤ 16842)]
  rw [block_63, tail_64]
  decide
opaque tail_62 : ((Finset.Ico 6200 16842).sum f : ZMod M) = 3403125983976 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 6200 ≤ 6300) (by norm_num : 6300 ≤ 16842)]
  rw [block_62, tail_63]
  decide
opaque tail_61 : ((Finset.Ico 6100 16842).sum f : ZMod M) = 639545215794 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 6100 ≤ 6200) (by norm_num : 6200 ≤ 16842)]
  rw [block_61, tail_62]
  decide
opaque tail_60 : ((Finset.Ico 6000 16842).sum f : ZMod M) = 3227092691557 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 6000 ≤ 6100) (by norm_num : 6100 ≤ 16842)]
  rw [block_60, tail_61]
  decide
opaque tail_59 : ((Finset.Ico 5900 16842).sum f : ZMod M) = 37298823983 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 5900 ≤ 6000) (by norm_num : 6000 ≤ 16842)]
  rw [block_59, tail_60]
  decide
opaque tail_58 : ((Finset.Ico 5800 16842).sum f : ZMod M) = 1516877125711 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 5800 ≤ 5900) (by norm_num : 5900 ≤ 16842)]
  rw [block_58, tail_59]
  decide
opaque tail_57 : ((Finset.Ico 5700 16842).sum f : ZMod M) = 809853268875 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 5700 ≤ 5800) (by norm_num : 5800 ≤ 16842)]
  rw [block_57, tail_58]
  decide
opaque tail_56 : ((Finset.Ico 5600 16842).sum f : ZMod M) = 4043672973851 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 5600 ≤ 5700) (by norm_num : 5700 ≤ 16842)]
  rw [block_56, tail_57]
  decide
opaque tail_55 : ((Finset.Ico 5500 16842).sum f : ZMod M) = 3140961071090 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 5500 ≤ 5600) (by norm_num : 5600 ≤ 16842)]
  rw [block_55, tail_56]
  decide
opaque tail_54 : ((Finset.Ico 5400 16842).sum f : ZMod M) = 337852526613 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 5400 ≤ 5500) (by norm_num : 5500 ≤ 16842)]
  rw [block_54, tail_55]
  decide
opaque tail_53 : ((Finset.Ico 5300 16842).sum f : ZMod M) = 4443542284876 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 5300 ≤ 5400) (by norm_num : 5400 ≤ 16842)]
  rw [block_53, tail_54]
  decide
opaque tail_52 : ((Finset.Ico 5200 16842).sum f : ZMod M) = 1848351421526 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 5200 ≤ 5300) (by norm_num : 5300 ≤ 16842)]
  rw [block_52, tail_53]
  decide
opaque tail_51 : ((Finset.Ico 5100 16842).sum f : ZMod M) = 3414873035175 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 5100 ≤ 5200) (by norm_num : 5200 ≤ 16842)]
  rw [block_51, tail_52]
  decide
opaque tail_50 : ((Finset.Ico 5000 16842).sum f : ZMod M) = 1847722385826 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 5000 ≤ 5100) (by norm_num : 5100 ≤ 16842)]
  rw [block_50, tail_51]
  decide
opaque tail_49 : ((Finset.Ico 4900 16842).sum f : ZMod M) = 4496362863564 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 4900 ≤ 5000) (by norm_num : 5000 ≤ 16842)]
  rw [block_49, tail_50]
  decide
opaque tail_48 : ((Finset.Ico 4800 16842).sum f : ZMod M) = 3114921687051 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 4800 ≤ 4900) (by norm_num : 4900 ≤ 16842)]
  rw [block_48, tail_49]
  decide
opaque tail_47 : ((Finset.Ico 4700 16842).sum f : ZMod M) = 3088359549346 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 4700 ≤ 4800) (by norm_num : 4800 ≤ 16842)]
  rw [block_47, tail_48]
  decide
opaque tail_46 : ((Finset.Ico 4600 16842).sum f : ZMod M) = 529908394981 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 4600 ≤ 4700) (by norm_num : 4700 ≤ 16842)]
  rw [block_46, tail_47]
  decide
opaque tail_45 : ((Finset.Ico 4500 16842).sum f : ZMod M) = 4079885394043 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 4500 ≤ 4600) (by norm_num : 4600 ≤ 16842)]
  rw [block_45, tail_46]
  decide
opaque tail_44 : ((Finset.Ico 4400 16842).sum f : ZMod M) = 1394706270419 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 4400 ≤ 4500) (by norm_num : 4500 ≤ 16842)]
  rw [block_44, tail_45]
  decide
opaque tail_43 : ((Finset.Ico 4300 16842).sum f : ZMod M) = 1390897824117 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 4300 ≤ 4400) (by norm_num : 4400 ≤ 16842)]
  rw [block_43, tail_44]
  decide
opaque tail_42 : ((Finset.Ico 4200 16842).sum f : ZMod M) = 2158773907796 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 4200 ≤ 4300) (by norm_num : 4300 ≤ 16842)]
  rw [block_42, tail_43]
  decide
opaque tail_41 : ((Finset.Ico 4100 16842).sum f : ZMod M) = 4440778480131 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 4100 ≤ 4200) (by norm_num : 4200 ≤ 16842)]
  rw [block_41, tail_42]
  decide
opaque tail_40 : ((Finset.Ico 4000 16842).sum f : ZMod M) = 2333764055231 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 4000 ≤ 4100) (by norm_num : 4100 ≤ 16842)]
  rw [block_40, tail_41]
  decide
opaque tail_39 : ((Finset.Ico 3900 16842).sum f : ZMod M) = 1491748744112 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 3900 ≤ 4000) (by norm_num : 4000 ≤ 16842)]
  rw [block_39, tail_40]
  decide
opaque tail_38 : ((Finset.Ico 3800 16842).sum f : ZMod M) = 3679561660142 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 3800 ≤ 3900) (by norm_num : 3900 ≤ 16842)]
  rw [block_38, tail_39]
  decide
opaque tail_37 : ((Finset.Ico 3700 16842).sum f : ZMod M) = 1248226026198 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 3700 ≤ 3800) (by norm_num : 3800 ≤ 16842)]
  rw [block_37, tail_38]
  decide
opaque tail_36 : ((Finset.Ico 3600 16842).sum f : ZMod M) = 4632697121018 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 3600 ≤ 3700) (by norm_num : 3700 ≤ 16842)]
  rw [block_36, tail_37]
  decide
opaque tail_35 : ((Finset.Ico 3500 16842).sum f : ZMod M) = 4001363376736 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 3500 ≤ 3600) (by norm_num : 3600 ≤ 16842)]
  rw [block_35, tail_36]
  decide
opaque tail_34 : ((Finset.Ico 3400 16842).sum f : ZMod M) = 2924221023600 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 3400 ≤ 3500) (by norm_num : 3500 ≤ 16842)]
  rw [block_34, tail_35]
  decide
opaque tail_33 : ((Finset.Ico 3300 16842).sum f : ZMod M) = 1635068159426 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 3300 ≤ 3400) (by norm_num : 3400 ≤ 16842)]
  rw [block_33, tail_34]
  decide
opaque tail_32 : ((Finset.Ico 3200 16842).sum f : ZMod M) = 2596514038148 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 3200 ≤ 3300) (by norm_num : 3300 ≤ 16842)]
  rw [block_32, tail_33]
  decide
opaque tail_31 : ((Finset.Ico 3100 16842).sum f : ZMod M) = 2398978877941 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 3100 ≤ 3200) (by norm_num : 3200 ≤ 16842)]
  rw [block_31, tail_32]
  decide
opaque tail_30 : ((Finset.Ico 3000 16842).sum f : ZMod M) = 3050075615273 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 3000 ≤ 3100) (by norm_num : 3100 ≤ 16842)]
  rw [block_30, tail_31]
  decide
opaque tail_29 : ((Finset.Ico 2900 16842).sum f : ZMod M) = 4464551260933 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 2900 ≤ 3000) (by norm_num : 3000 ≤ 16842)]
  rw [block_29, tail_30]
  decide
opaque tail_28 : ((Finset.Ico 2800 16842).sum f : ZMod M) = 4218266193925 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 2800 ≤ 2900) (by norm_num : 2900 ≤ 16842)]
  rw [block_28, tail_29]
  decide
opaque tail_27 : ((Finset.Ico 2700 16842).sum f : ZMod M) = 4592987415400 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 2700 ≤ 2800) (by norm_num : 2800 ≤ 16842)]
  rw [block_27, tail_28]
  decide
opaque tail_26 : ((Finset.Ico 2600 16842).sum f : ZMod M) = 4134474386867 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 2600 ≤ 2700) (by norm_num : 2700 ≤ 16842)]
  rw [block_26, tail_27]
  decide
opaque tail_25 : ((Finset.Ico 2500 16842).sum f : ZMod M) = 2321744121381 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 2500 ≤ 2600) (by norm_num : 2600 ≤ 16842)]
  rw [block_25, tail_26]
  decide
opaque tail_24 : ((Finset.Ico 2400 16842).sum f : ZMod M) = 2114679561478 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 2400 ≤ 2500) (by norm_num : 2500 ≤ 16842)]
  rw [block_24, tail_25]
  decide
opaque tail_23 : ((Finset.Ico 2300 16842).sum f : ZMod M) = 3373722031397 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 2300 ≤ 2400) (by norm_num : 2400 ≤ 16842)]
  rw [block_23, tail_24]
  decide
opaque tail_22 : ((Finset.Ico 2200 16842).sum f : ZMod M) = 2596538545311 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 2200 ≤ 2300) (by norm_num : 2300 ≤ 16842)]
  rw [block_22, tail_23]
  decide
opaque tail_21 : ((Finset.Ico 2100 16842).sum f : ZMod M) = 3025708752452 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 2100 ≤ 2200) (by norm_num : 2200 ≤ 16842)]
  rw [block_21, tail_22]
  decide
opaque tail_20 : ((Finset.Ico 2000 16842).sum f : ZMod M) = 603501685507 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 2000 ≤ 2100) (by norm_num : 2100 ≤ 16842)]
  rw [block_20, tail_21]
  decide
opaque tail_19 : ((Finset.Ico 1900 16842).sum f : ZMod M) = 3364365405665 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 1900 ≤ 2000) (by norm_num : 2000 ≤ 16842)]
  rw [block_19, tail_20]
  decide
opaque tail_18 : ((Finset.Ico 1800 16842).sum f : ZMod M) = 2794024181227 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 1800 ≤ 1900) (by norm_num : 1900 ≤ 16842)]
  rw [block_18, tail_19]
  decide
opaque tail_17 : ((Finset.Ico 1700 16842).sum f : ZMod M) = 3910011824581 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 1700 ≤ 1800) (by norm_num : 1800 ≤ 16842)]
  rw [block_17, tail_18]
  decide
opaque tail_16 : ((Finset.Ico 1600 16842).sum f : ZMod M) = 4288860828307 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 1600 ≤ 1700) (by norm_num : 1700 ≤ 16842)]
  rw [block_16, tail_17]
  decide
opaque tail_15 : ((Finset.Ico 1500 16842).sum f : ZMod M) = 4252032037273 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 1500 ≤ 1600) (by norm_num : 1600 ≤ 16842)]
  rw [block_15, tail_16]
  decide
opaque tail_14 : ((Finset.Ico 1400 16842).sum f : ZMod M) = 3909714596679 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 1400 ≤ 1500) (by norm_num : 1500 ≤ 16842)]
  rw [block_14, tail_15]
  decide
opaque tail_13 : ((Finset.Ico 1300 16842).sum f : ZMod M) = 2870943654147 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 1300 ≤ 1400) (by norm_num : 1400 ≤ 16842)]
  rw [block_13, tail_14]
  decide
opaque tail_12 : ((Finset.Ico 1200 16842).sum f : ZMod M) = 959297304318 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 1200 ≤ 1300) (by norm_num : 1300 ≤ 16842)]
  rw [block_12, tail_13]
  decide
opaque tail_11 : ((Finset.Ico 1100 16842).sum f : ZMod M) = 2261240984321 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 1100 ≤ 1200) (by norm_num : 1200 ≤ 16842)]
  rw [block_11, tail_12]
  decide
opaque tail_10 : ((Finset.Ico 1000 16842).sum f : ZMod M) = 3165906533570 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 1000 ≤ 1100) (by norm_num : 1100 ≤ 16842)]
  rw [block_10, tail_11]
  decide
opaque tail_9 : ((Finset.Ico 900 16842).sum f : ZMod M) = 1520157266371 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 900 ≤ 1000) (by norm_num : 1000 ≤ 16842)]
  rw [block_9, tail_10]
  decide
opaque tail_8 : ((Finset.Ico 800 16842).sum f : ZMod M) = 2543207240428 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 800 ≤ 900) (by norm_num : 900 ≤ 16842)]
  rw [block_8, tail_9]
  decide
opaque tail_7 : ((Finset.Ico 700 16842).sum f : ZMod M) = 4131040141215 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 700 ≤ 800) (by norm_num : 800 ≤ 16842)]
  rw [block_7, tail_8]
  decide
opaque tail_6 : ((Finset.Ico 600 16842).sum f : ZMod M) = 537025491217 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 600 ≤ 700) (by norm_num : 700 ≤ 16842)]
  rw [block_6, tail_7]
  decide
opaque tail_5 : ((Finset.Ico 500 16842).sum f : ZMod M) = 1643601334524 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 500 ≤ 600) (by norm_num : 600 ≤ 16842)]
  rw [block_5, tail_6]
  decide
opaque tail_4 : ((Finset.Ico 400 16842).sum f : ZMod M) = 2043933104400 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 400 ≤ 500) (by norm_num : 500 ≤ 16842)]
  rw [block_4, tail_5]
  decide
opaque tail_3 : ((Finset.Ico 300 16842).sum f : ZMod M) = 440423367480 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 300 ≤ 400) (by norm_num : 400 ≤ 16842)]
  rw [block_3, tail_4]
  decide
opaque tail_2 : ((Finset.Ico 200 16842).sum f : ZMod M) = 613102002457 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 200 ≤ 300) (by norm_num : 300 ≤ 16842)]
  rw [block_2, tail_3]
  decide
opaque tail_1 : ((Finset.Ico 100 16842).sum f : ZMod M) = 2285390713029 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 100 ≤ 200) (by norm_num : 200 ≤ 16842)]
  rw [block_1, tail_2]
  decide
opaque tail_0 : ((Finset.Ico 0 16842).sum f : ZMod M) = 0 := by
  rw [← Finset.sum_Ico_consecutive f (by norm_num : 0 ≤ 100) (by norm_num : 100 ≤ 16842)]
  rw [block_0, tail_1]
  decide
opaque hsmall_zmod : ((Finset.range 16842).sum f : ZMod M) = 0 := by
  rw [Finset.range_eq_Ico]
  simpa using tail_0



lemma sum_divInt_const {α : Type*} (s : Finset α) (a : α → ℤ) (D : ℤ) :
    (∑ x ∈ s, (a x /. D)) = ((∑ x ∈ s, a x) /. D) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, ih]
      exact (Rat.add_divInt (a x) (∑ y ∈ s, a y) D).symm


lemma harmonic_eq_factorial_divInt (n : ℕ) :
    harmonic n = ((∑ i ∈ Finset.range n, ((n.factorial / (i+1) : ℕ) : ℤ)) /. (n.factorial : ℤ)) := by
  rw [harmonic]
  trans ∑ i ∈ Finset.range n, (((n.factorial / (i+1) : ℕ) : ℤ) /. (n.factorial : ℤ))
  · apply Finset.sum_congr rfl
    intro i hi
    have hi1 : 0 < i + 1 := Nat.succ_pos i
    have hle : i + 1 ≤ n := by simpa using hi
    have hdvd : i + 1 ∣ n.factorial := Nat.dvd_factorial hi1 hle
    rw [inv_eq_one_div]
    conv_lhs => change (((1 : ℕ) : ℚ) / (((i+1 : ℕ) : ℕ) : ℚ))
    rw [Rat.natCast_div_eq_divInt (1 : ℕ) (i+1)]
    symm
    have hqpos : 0 < n.factorial / (i+1) := by
      exact Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos n) hdvd) hi1
    have hq : ((n.factorial / (i+1) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hqpos.ne'
    rw [show (n.factorial : ℤ) = ((i+1 : ℕ) : ℤ) * ((n.factorial / (i+1) : ℕ) : ℤ) by
      norm_cast
      exact (Nat.mul_div_cancel' hdvd).symm]
    trans Rat.divInt ((1 : ℤ) * ((n.factorial / (i+1) : ℕ) : ℤ))
        (((i+1 : ℕ) : ℤ) * ((n.factorial / (i+1) : ℕ) : ℤ))
    · congr <;> ring
    · rw [Rat.divInt_mul_right hq]
      norm_num
  · exact sum_divInt_const (Finset.range n) (fun i => ((n.factorial / (i+1) : ℕ) : ℤ)) (n.factorial : ℤ)

lemma zmod_cast_div_of_dvd_of_coprime {M D k : ℕ} (hkd : k ∣ D) (hcop : Nat.Coprime k M) :
    (((D / k : ℕ) : ZMod M) = (D : ZMod M) * (((k : ℕ) : ZMod M)⁻¹)) := by
  have hunit : IsUnit ((k : ℕ) : ZMod M) := (ZMod.isUnit_iff_coprime k M).2 hcop
  apply hunit.mul_left_cancel
  calc
    ((k : ZMod M) * ((D / k : ℕ) : ZMod M)) = (D : ZMod M) := by
      rw [← Nat.cast_mul, Nat.mul_comm, Nat.div_mul_cancel hkd]
    _ = (k : ZMod M) * ((D : ZMod M) * ((k : ZMod M)⁻¹)) := by
      symm
      calc
        (k : ZMod M) * ((D : ZMod M) * ((k : ZMod M)⁻¹)) =
            (D : ZMod M) * ((k : ZMod M) * ((k : ZMod M)⁻¹)) := by ring
        _ = (D : ZMod M) := by rw [ZMod.coe_mul_inv_eq_one k hcop, mul_one]

lemma nat_sum_factorial_div_zmod_zero_of_inv_sum_zero {p n M : ℕ}
    (hM : M = p^3) (hp : Nat.Prime p) (hnlt : n < p)
    (hz : ((Finset.range n).sum (fun i => ((((i+1 : ℕ) : ZMod M))⁻¹)) : ZMod M) = 0) :
    (((∑ i ∈ Finset.range n, (n.factorial / (i+1) : ℕ)) : ℕ) : ZMod M) = 0 := by
  rw [Nat.cast_sum]
  trans (∑ i ∈ Finset.range n, ((n.factorial : ℕ) : ZMod M) * ((((i+1 : ℕ) : ZMod M))⁻¹))
  · apply Finset.sum_congr rfl
    intro i hi
    have hi_lt : i < n := by simpa using hi
    have hi1 : 0 < i+1 := Nat.succ_pos i
    have hle : i+1 ≤ n := by omega
    have hdvd : i+1 ∣ n.factorial := Nat.dvd_factorial hi1 hle
    have hcop_p : Nat.Coprime (i+1) p := by
      exact ((hp.coprime_iff_not_dvd).2 (Nat.not_dvd_of_pos_of_lt hi1 (by omega))).symm
    have hcop : Nat.Coprime (i+1) M := by
      rw [hM]
      exact hcop_p.pow_right 3
    exact zmod_cast_div_of_dvd_of_coprime hdvd hcop
  · rw [← Finset.mul_sum, hz, mul_zero]

lemma nat_dvd_of_zmod_cast_zero {M A : ℕ} [NeZero M] (h : ((A : ZMod M) = 0)) : M ∣ A := by
  rw [← ZMod.natCast_eq_zero_iff]
  exact h


namespace Counter

def Good (p : ℕ) (q : ℚ) : Prop :=
  ∃ a b : ℤ, b ≠ 0 ∧ ¬ (p : ℤ) ∣ b ∧ q = (((p : ℤ)^2 * a) /. b)

opaque harmonic_pred_div_good_of_inv_sum_zero {p : ℕ} (hp : Nat.Prime p) (hp2 : 2 < p)
    (hz : ((Finset.range (p-1)).sum (fun i => ((((i+1 : ℕ) : ZMod (p^3)))⁻¹)) : ZMod (p^3)) = 0) :
    Good p (harmonic (p-1) / (p : ℚ)) := by
  let n : ℕ := p-1
  let A : ℕ := ∑ i ∈ Finset.range n, (n.factorial / (i+1) : ℕ)
  let D : ℕ := n.factorial
  have hnlt : n < p := by dsimp [n]; omega
  have hH : harmonic n = ((A : ℤ) /. (D : ℤ)) := by
    rw [harmonic_eq_factorial_divInt n]
    dsimp [A,D]
    rw [Nat.cast_sum]
    congr 1
  have hz' : ((Finset.range n).sum (fun i => ((((i+1 : ℕ) : ZMod (p^3)))⁻¹)) : ZMod (p^3)) = 0 := by
    dsimp [n]
    exact hz
  have hAz : ((A : ZMod (p^3)) = 0) := by
    dsimp [A]
    apply nat_sum_factorial_div_zmod_zero_of_inv_sum_zero (p:=p) (n:=n) (M:=p^3)
    · rfl
    · exact hp
    · exact hnlt
    · exact hz'
  have hAdivNat : p^3 ∣ A := by
    rw [← ZMod.natCast_eq_zero_iff]
    exact hAz
  have hAdiv : ((p : ℤ)^3 ∣ (A : ℤ)) := by exact_mod_cast hAdivNat
  let a : ℤ := (A : ℤ) / ((p : ℤ)^3)
  have hAeq : (A : ℤ) = (p : ℤ)^3 * a := by
    dsimp [a]
    simpa [mul_comm] using (Int.ediv_mul_cancel hAdiv).symm
  have hD0 : (D : ℤ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hpD : ¬ (p : ℤ) ∣ (D : ℤ) := by
    intro hd
    have hdNat : p ∣ D := by exact_mod_cast hd
    have : p ≤ n := (hp.dvd_factorial.mp (by simpa [D] using hdNat))
    omega
  refine ⟨a, (D : ℤ), hD0, hpD, ?_⟩
  rw [← show n = p-1 by rfl]
  rw [hH, hAeq]
  rw [show (p : ℚ) = ((p : ℤ) /. 1) by rw [Rat.divInt_one]; rfl]
  change (((p : ℤ)^3 * a /. (D : ℤ)) / ((p : ℤ) /. 1)) = ((p : ℤ)^2 * a /. (D : ℤ))
  rw [Rat.divInt_div_divInt]
  rw [show ((p : ℤ)^3 * a) * 1 = (((p : ℤ)^2 * a) * (p : ℤ)) by ring]
  rw [Rat.divInt_mul_right (by exact_mod_cast hp.ne_zero)]

end Counter

namespace Counter

lemma hsmall_div_good : Good 16843 (harmonic 16842 / (16843 : ℚ)) := by
  apply harmonic_pred_div_good_of_inv_sum_zero
  · norm_num
  · norm_num
  · exact hsmall_zmod

end Counter



namespace Counter


lemma Good.of_factor {p : ℕ} {a b : ℤ} (hb0 : b ≠ 0) (hpb : ¬ (p : ℤ) ∣ b) :
    Good p (((p : ℤ)^2 * a) /. b) := ⟨a,b,hb0,hpb,rfl⟩

lemma Good.mul_int {p : ℕ} {q : ℚ} (hq : Good p q) (z : ℤ) : Good p (q * z) := by
  rcases hq with ⟨a,b,hb0,hpb,hrep⟩
  refine ⟨a*z,b,hb0,hpb, ?_⟩
  rw [hrep]
  rw [Rat.intCast_eq_divInt z]
  rw [Rat.divInt_mul_divInt]
  rw [show b * 1 = b by ring]
  rw [show (↑p ^ 2 * a) * z = ↑p ^ 2 * (a * z) by ring]

lemma Good.add {p : ℕ} (hp : Nat.Prime p) {q r : ℚ} (hq : Good p q) (hr : Good p r) :
    Good p (q+r) := by
  rcases hq with ⟨a,b,hb0,hpb,hqrep⟩
  rcases hr with ⟨c,d,hd0,hpd,hrrep⟩
  refine ⟨a*d+c*b,b*d,mul_ne_zero hb0 hd0,?_,?_⟩
  · intro h
    have hpz : Prime (p:ℤ) := Nat.prime_iff_prime_int.1 hp
    rcases hpz.dvd_or_dvd h with hb|hd
    · exact hpb hb
    · exact hpd hd
  · rw [hqrep, hrrep, Rat.divInt_add_divInt]
    · congr 1; ring
    · exact hb0
    · exact hd0

lemma Good.neg {p : ℕ} {q : ℚ} (hq : Good p q) : Good p (-q) := by
  rcases hq with ⟨a,b,hb0,hpb,hrep⟩
  refine ⟨-a,b,hb0,hpb,?_⟩
  rw [hrep]
  simp [Rat.neg_divInt, Int.mul_neg]

lemma Good.sub {p : ℕ} (hp : Nat.Prime p) {q r : ℚ} (hq : Good p q) (hr : Good p r) : Good p (q-r) := by
  simpa [sub_eq_add_neg] using Good.add hp hq (Good.neg hr)

lemma nonmult_term_good (p a r : ℕ) (hp : Nat.Prime p) (hr0 : 0 < r) (hrp : r < p) :
    Good p (((1:ℚ)/(a*p+r) - ((1:ℚ)/r - ((a*p:ℕ):ℚ)/(r^2)))) := by
  have hb0 : (((a*p+r) * r^2 : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by omega : a*p+r ≠ 0) (pow_ne_zero 2 hr0.ne'))
  have hpb : ¬ (p : ℤ) ∣ (((a*p+r) * r^2 : ℕ) : ℤ) := by
    intro h
    have hp_nat_dvd : p ∣ (a*p+r) * r^2 := by exact_mod_cast h
    have hnot1 : ¬ p ∣ a*p+r := by
      intro hd
      have : p ∣ r := by
        have hp_dvd_ap : p ∣ a*p := dvd_mul_left p a
        simpa [Nat.add_sub_cancel_left] using (Nat.dvd_sub hd hp_dvd_ap)
      exact Nat.not_dvd_of_pos_of_lt hr0 hrp this
    have hnot2 : ¬ p ∣ r^2 := by
      intro hd
      exact Nat.not_dvd_of_pos_of_lt hr0 hrp (hp.dvd_of_dvd_pow hd)
    exact (hp.dvd_or_dvd hp_nat_dvd).elim hnot1 hnot2
  refine ⟨(a:ℤ)^2, (((a*p+r) * r^2 : ℕ) : ℤ), hb0, hpb, ?_⟩
  rw [Rat.divInt_eq_div]
  field_simp [show ((a*p+r:ℕ):ℚ) ≠ 0 by positivity, show ((r:ℕ):ℚ) ≠ 0 by positivity,
    show (((((a*p+r) * r^2 : ℕ) : ℤ) : ℚ)) ≠ 0 by exact_mod_cast hb0]
  push_cast
  ring_nf

end Counter


lemma multiples_sum_bij (p : ℕ) (hp0 : 0 < p) :
    (∑ j ∈ Finset.range (p-1), ((((p*(j+1)) : ℕ) : ℚ)⁻¹)) =
    (∑ i ∈ (Finset.range (p^2 - 1)).filter (fun i => p ∣ i+1), (((i+1 : ℕ) : ℚ)⁻¹)) := by
  refine Finset.sum_bij (fun j _ => p*(j+1)-1) ?mem ?inj ?surj ?eq
  · intro j hj
    simp only [mem_filter, mem_range]
    constructor
    · have hjlt : j < p-1 := by simpa using hj
      have hj1lt : j+1 < p := by omega
      have hmul : p*(j+1) < p*p := Nat.mul_lt_mul_of_pos_left hj1lt hp0
      have hjpos : 0 < p*(j+1) := Nat.mul_pos hp0 (Nat.succ_pos j)
      have : p*(j+1)-1 < p^2 - 1 := by
        rw [pow_two]
        omega
      exact this
    · have hjpos : 0 < p*(j+1) := Nat.mul_pos hp0 (Nat.succ_pos j)
      have hsucc : p*(j+1)-1 + 1 = p*(j+1) := Nat.sub_add_cancel (by omega)
      rw [hsucc]
      exact dvd_mul_right p (j+1)
  · intro a ha b hb h
    have hpa : 0 < p*(a+1) := Nat.mul_pos hp0 (Nat.succ_pos a)
    have hpb : 0 < p*(b+1) := Nat.mul_pos hp0 (Nat.succ_pos b)
    have heq1 := congrArg (fun x => x + 1) h
    have heq : p*(a+1) = p*(b+1) := by
      dsimp at heq1
      rw [Nat.sub_add_cancel (by omega : 1 ≤ p*(a+1)), Nat.sub_add_cancel (by omega : 1 ≤ p*(b+1))] at heq1
      exact heq1
    exact Nat.succ.inj (Nat.mul_left_cancel hp0 heq)
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    rcases hi with ⟨hiN, hdiv⟩
    rcases hdiv with ⟨k, hk⟩
    refine ⟨k-1, ?_, ?_⟩
    · simp only [mem_range]
      have hikpos : 0 < i+1 := Nat.succ_pos i
      have hkpos : 0 < k := by nlinarith [hp0, hikpos, hk]
      have hplt : p*k < p*p := by
        rw [← hk]
        rw [pow_two] at hiN
        omega
      have hklt : k < p := Nat.lt_of_mul_lt_mul_left hplt
      omega
    · have hikpos : 0 < i+1 := Nat.succ_pos i
      have hkpos : 0 < k := by nlinarith [hp0, hikpos, hk]
      change p * (k - 1 + 1) - 1 = i
      apply Nat.succ.inj
      change (p * (k - 1 + 1) - 1) + 1 = i + 1
      rw [show k - 1 + 1 = k by omega]
      rw [Nat.sub_add_cancel (by nlinarith [hp0, hkpos] : 1 ≤ p * k)]
      exact hk.symm
  · intro j hj
    have hjpos : 0 < p*(j+1) := Nat.mul_pos hp0 (Nat.succ_pos j)
    have hsucc : p*(j+1)-1 + 1 = p*(j+1) := Nat.sub_add_cancel (by omega)
    simp [hsucc]


lemma nonmultiples_sum_bij (p : ℕ) (hp0 : 0 < p) :
    (∑ a ∈ Finset.range p, ∑ r ∈ Finset.range (p-1), (((a*p + (r+1) : ℕ) : ℚ)⁻¹)) =
    (∑ i ∈ (Finset.range (p^2 - 1)).filter (fun i => ¬ p ∣ i+1), (((i+1 : ℕ) : ℚ)⁻¹)) := by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij (fun ar _ => ar.1*p + (ar.2+1) - 1) ?mem ?inj ?surj ?eq
  · intro ar har
    rcases ar with ⟨a,r⟩
    simp only [mem_sigma, mem_range] at har
    rcases har with ⟨ha, hr⟩
    simp only [mem_filter, mem_range]
    constructor
    · have hpos : 0 < a*p + (r+1) := by omega
      have hlt : a*p + (r+1) < p*p := by
        have ha_le : a ≤ p-1 := by omega
        have hr_lt : r+1 < p := by omega
        have h1 : a*p ≤ (p-1)*p := Nat.mul_le_mul_right p ha_le
        nlinarith [h1, hr_lt]
      rw [pow_two]
      omega
    · have hsucc : a*p + (r+1) - 1 + 1 = a*p + (r+1) := Nat.sub_add_cancel (by omega)
      rw [hsucc]
      intro hd
      have hpa : p ∣ a*p := dvd_mul_left p a
      have hpr : p ∣ r+1 := by
        simpa [Nat.add_assoc] using (Nat.dvd_sub hd hpa)
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) hpr
  · intro ar har bs hbs h
    rcases ar with ⟨a,r⟩; rcases bs with ⟨b,s⟩
    simp only [mem_sigma, mem_range] at har hbs
    rcases har with ⟨ha,hr⟩; rcases hbs with ⟨hb,hs⟩
    have hEq1 := congrArg (fun x => x+1) h
    have hEq : a*p + (r+1) = b*p + (s+1) := by
      dsimp at hEq1
      omega
    have hmod : (r+1) % p = (s+1) % p := by
      calc
        (r+1) % p = (a*p + (r+1)) % p := by rw [Nat.mul_add_mod_self_right]
        _ = (b*p + (s+1)) % p := by rw [hEq]
        _ = (s+1) % p := by rw [Nat.mul_add_mod_self_right]
    have hrlt : r+1 < p := by omega
    have hslt : s+1 < p := by omega
    rw [Nat.mod_eq_of_lt hrlt, Nat.mod_eq_of_lt hslt] at hmod
    have hrs : r = s := by omega
    subst s
    have hab : a = b := by
      have : a*p = b*p := by omega
      exact Nat.mul_right_cancel hp0 this
    subst b
    rfl
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    rcases hi with ⟨hiN,hnot⟩
    let k := i+1
    let a := k / p
    let r := k % p - 1
    have hkpos : 0 < k := by dsimp [k]; omega
    have hklt : k < p*p := by dsimp [k]; rw [← pow_two]; omega
    have hmodnz : k % p ≠ 0 := by
      intro hz
      apply hnot
      have : p ∣ k := (Nat.dvd_iff_mod_eq_zero).2 hz
      simpa [k] using this
    have hmodpos : 0 < k % p := Nat.pos_of_ne_zero hmodnz
    refine ⟨⟨a,r⟩, ?_, ?_⟩
    · simp only [mem_sigma, mem_range]
      constructor
      · dsimp [a]
        exact Nat.div_lt_of_lt_mul hklt
      · dsimp [r]
        have hmodlt : k % p < p := Nat.mod_lt k hp0
        omega
    · dsimp [a,r,k]
      have hdecomp : (i+1) / p * p + (i+1) % p = i+1 := by
        rw [Nat.mul_comm, Nat.div_add_mod]
      change (i + 1) / p * p + ((i + 1) % p - 1 + 1) - 1 = i
      rw [show (i+1)%p - 1 + 1 = (i+1)%p by omega]
      apply Nat.succ.inj
      change ((i + 1) / p * p + (i + 1) % p - 1) + 1 = i + 1
      rw [Nat.sub_add_cancel (by nlinarith [hmodpos] : 1 ≤ (i + 1) / p * p + (i + 1) % p)]
      exact hdecomp
  · intro ar har
    rcases ar with ⟨a,r⟩
    simp only [mem_sigma, mem_range] at har
    rcases har with ⟨ha,hr⟩
    have hsucc : a*p + (r+1) - 1 + 1 = a*p + (r+1) := Nat.sub_add_cancel (by omega)
    simp [hsucc]
    ring

lemma harmonic_square_split (p : ℕ) (hp0 : 0 < p) :
    harmonic (p^2 - 1) =
      (∑ j ∈ Finset.range (p-1), ((((p*(j+1)) : ℕ) : ℚ)⁻¹)) +
      (∑ a ∈ Finset.range p, ∑ r ∈ Finset.range (p-1), (((a*p + (r+1) : ℕ) : ℚ)⁻¹)) := by
  rw [harmonic]
  let F : ℕ → ℚ := fun i => (((i+1 : ℕ) : ℚ)⁻¹)
  have hsplit : (∑ i ∈ Finset.range (p^2 - 1), F i) =
      (∑ i ∈ (Finset.range (p^2 - 1)).filter (fun i => p ∣ i+1), F i) +
      (∑ i ∈ (Finset.range (p^2 - 1)).filter (fun i => ¬ p ∣ i+1), F i) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s:=Finset.range (p^2-1)) (p:=fun i => p ∣ i+1) (f:=F)]
  change (∑ i ∈ Finset.range (p^2 - 1), F i) = _
  rw [hsplit]
  rw [← multiples_sum_bij p hp0, ← nonmultiples_sum_bij p hp0]

namespace Counter
lemma Good.zero (p : ℕ) (hp : Nat.Prime p) : Good p 0 := by
  refine ⟨0, 1, by norm_num, ?_, by simp⟩
  exact (Nat.prime_iff_prime_int.1 hp).not_dvd_one



opaque Good.sum {p : ℕ} (hp : Nat.Prime p) {α : Type*} {s : Finset α} {f : α → ℚ}
    (h : ∀ x ∈ s, Good p (f x)) : Good p (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Good.zero p hp
  | insert a s has ih =>
      rw [Finset.sum_insert has]
      exact Good.add hp (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

end Counter


namespace Counter

lemma multiples_part_good_16843 :
    Good 16843 (∑ j ∈ Finset.range 16842, (((16843*(j+1) : ℕ) : ℚ)⁻¹)) := by
  have hEq : (∑ j ∈ Finset.range 16842, (((16843*(j+1) : ℕ) : ℚ)⁻¹)) =
      harmonic 16842 / (16843 : ℚ) := by
    rw [harmonic]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 : ((j+1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hp0 : (16843 : ℚ) ≠ 0 := by norm_num
    rw [div_eq_mul_inv]
    norm_num
  rw [hEq]
  exact hsmall_div_good

end Counter

namespace Counter

opaque nonmultiple_error_good_generic (p : ℕ) (hp : Nat.Prime p) :
    Good p
      (∑ ar ∈ (Finset.range p).sigma (fun _ => Finset.range (p-1)),
        ((((ar.1*p + (ar.2+1) : ℕ) : ℚ)⁻¹) -
          ((((ar.2+1 : ℕ) : ℚ)⁻¹) - (((ar.1*p : ℕ) : ℚ) / (((ar.2+1 : ℕ) : ℚ)^2))))) := by
  apply Good.sum hp
  intro ar har
  rcases ar with ⟨a,r⟩
  rw [Finset.mem_sigma] at har
  rcases har with ⟨ha,hr⟩
  have hrlt : r < p-1 := by simpa using hr
  simpa [one_div, Nat.cast_add, Nat.cast_mul, add_comm, add_left_comm, add_assoc, mul_comm] using
    (nonmult_term_good p a (r+1) hp (by omega) (by omega))

end Counter



namespace Counter

lemma second_baseline_inner_good_generic (p c r : ℕ) (hp : Nat.Prime p) (hpc : p - 1 = 2*c)
    (hrpos : 0 < r) (hrp : r < p) :
    Good p (∑ a ∈ Finset.range p, (((a*p : ℕ) : ℚ) / (((r : ℕ) : ℚ)^2))) := by
  have hden0 : ((r^2 : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (pow_ne_zero 2 hrpos.ne')
  have hpden : ¬ (p : ℤ) ∣ ((r^2 : ℕ) : ℤ) := by
    intro h
    have hnat : p ∣ r^2 := by exact_mod_cast h
    exact Nat.not_dvd_of_pos_of_lt hrpos hrp (hp.dvd_of_dvd_pow hnat)
  convert Good.of_factor (p:=p) (a:=(c:ℤ)) (b:=((r^2 : ℕ) : ℤ)) hden0 hpden using 1
  rw [Rat.divInt_eq_div]
  rw [← Finset.sum_div]
  congr 1
  norm_cast
  rw [← Finset.sum_mul]
  rw [Finset.sum_range_id]
  have hpodd : p * (p - 1) / 2 = p * c := by
    rw [hpc]
    rw [show p * (2 * c) = 2 * (p * c) by ring]
    exact Nat.mul_div_right (p*c) (by norm_num : 0 < 2)
  rw [hpodd]
  ring

opaque second_baseline_good_generic (p c : ℕ) (hp : Nat.Prime p) (hpc : p - 1 = 2*c) :
    Good p (∑ r ∈ Finset.range (p-1), ∑ a ∈ Finset.range p,
      (((a*p : ℕ) : ℚ) / (((r+1 : ℕ) : ℚ)^2))) := by
  apply Good.sum hp
  intro r hr
  have hrlt : r < p-1 := by simpa using hr
  simpa using second_baseline_inner_good_generic p c (r+1) hp hpc (by omega) (by omega)



end Counter

namespace Counter

lemma first_baseline_good_generic (p : ℕ) (hp : Nat.Prime p)
    (hsmall : Good p (harmonic (p-1) / (p : ℚ))) :
    Good p (∑ a ∈ Finset.range p, ∑ r ∈ Finset.range (p-1), (((r+1 : ℕ) : ℚ)⁻¹)) := by
  have hgood : Good p ((harmonic (p-1) / (p : ℚ)) * ((p : ℤ)^2)) := Good.mul_int hsmall ((p : ℤ)^2)
  have hEq : (∑ a ∈ Finset.range p, ∑ r ∈ Finset.range (p-1), (((r+1 : ℕ) : ℚ)⁻¹)) =
      (harmonic (p-1) / (p : ℚ)) * ((p : ℤ)^2) := by
    rw [harmonic]
    rw [Finset.sum_const]
    simp only [Finset.card_range]
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp [hpq]
    push_cast
    ring
  rw [hEq]
  exact hgood

end Counter

namespace Counter

lemma baseline_good_16843 :
    Good 16843 (∑ a ∈ Finset.range 16843, ∑ r ∈ Finset.range 16842,
      (((((r+1 : ℕ) : ℚ)⁻¹) - (((a*16843 : ℕ) : ℚ) / (((r+1 : ℕ) : ℚ)^2))))) := by
  have hp : Nat.Prime 16843 := by norm_num
  have h1 := first_baseline_good_generic 16843 hp hsmall_div_good
  have h2 := second_baseline_good_generic 16843 8421 hp (by norm_num : 16843 - 1 = 2 * 8421)
  have hsub : Good 16843
      ((∑ a ∈ Finset.range 16843, ∑ r ∈ Finset.range 16842, (((r+1 : ℕ) : ℚ)⁻¹)) -
       (∑ a ∈ Finset.range 16843, ∑ r ∈ Finset.range 16842, (((a*16843 : ℕ) : ℚ) / (((r+1 : ℕ) : ℚ)^2)))) := by
    apply Good.sub hp h1
    rw [Finset.sum_comm]
    exact h2
  simpa [Finset.sum_sub_distrib] using hsub

end Counter

namespace Counter

opaque nonmultiple_part_good_generic (p : ℕ) (hp : Nat.Prime p)
    (hbase : Good p (∑ a ∈ Finset.range p, ∑ r ∈ Finset.range (p-1),
      (((((r+1 : ℕ) : ℚ)⁻¹) - (((a*p : ℕ) : ℚ) / (((r+1 : ℕ) : ℚ)^2)))))) :
    Good p (∑ a ∈ Finset.range p, ∑ r ∈ Finset.range (p-1),
      (((a*p + (r+1) : ℕ) : ℚ)⁻¹)) := by
  have herr0 := nonmultiple_error_good_generic p hp
  have herr : Good p
      ((∑ a ∈ Finset.range p, ∑ r ∈ Finset.range (p-1), (((a*p + (r+1) : ℕ) : ℚ)⁻¹)) -
       ((∑ ar ∈ (Finset.range p).sigma (fun _ => Finset.range (p-1)),
          (((ar.2+1 : ℕ) : ℚ)⁻¹)) -
        (∑ ar ∈ (Finset.range p).sigma (fun _ => Finset.range (p-1)),
          (((ar.1*p : ℕ) : ℚ) / (((ar.2+1 : ℕ) : ℚ)^2))))) := by
    simpa [Finset.sum_sigma', Finset.sum_sub_distrib] using herr0
  have hbasep : Good p
      (((p : ℚ) * (∑ r ∈ Finset.range (p-1), (((r+1 : ℕ) : ℚ)⁻¹))) -
        (∑ ar ∈ (Finset.range p).sigma (fun _ => Finset.range (p-1)),
          (((ar.1*p : ℕ) : ℚ) / (((ar.2+1 : ℕ) : ℚ)^2)))) := by
    simpa [Finset.sum_sigma', Finset.sum_sub_distrib] using hbase
  have hfirst :
      (∑ ar ∈ (Finset.range p).sigma (fun _ => Finset.range (p-1)),
          (((ar.2+1 : ℕ) : ℚ)⁻¹)) =
        ((p : ℚ) * (∑ r ∈ Finset.range (p-1), (((r+1 : ℕ) : ℚ)⁻¹))) := by
    rw [Finset.sum_sigma]
    simp [Finset.mul_sum]
  have hbase' : Good p
      ((∑ ar ∈ (Finset.range p).sigma (fun _ => Finset.range (p-1)),
          (((ar.2+1 : ℕ) : ℚ)⁻¹)) -
        (∑ ar ∈ (Finset.range p).sigma (fun _ => Finset.range (p-1)),
          (((ar.1*p : ℕ) : ℚ) / (((ar.2+1 : ℕ) : ℚ)^2)))) := by
    rw [hfirst]
    exact hbasep
  have hadd := Good.add hp herr hbase'
  simpa [sub_add_cancel] using hadd

lemma nonmultiple_part_good_16843 :
    Good 16843 (∑ a ∈ Finset.range 16843, ∑ r ∈ Finset.range 16842,
      (((a*16843 + (r+1) : ℕ) : ℚ)⁻¹)) := by
  have hp : Nat.Prime 16843 := by norm_num
  exact nonmultiple_part_good_generic 16843 hp baseline_good_16843

end Counter







namespace Counter

lemma harmonic_square_good_16843 :
    Good 16843 (harmonic (16843^2 - 1)) := by
  have hp : Nat.Prime 16843 := by norm_num
  rw [harmonic_square_split 16843 (by norm_num)]
  exact Good.add hp multiples_part_good_16843 nonmultiple_part_good_16843

lemma correction_good_16843 :
    Good 16843 (1 + ((((16843^2 - 1 : ℕ) : ℚ)⁻¹))) := by
  have hgood : Good 16843 ((((16843 : ℤ)^2 * 1) /. (((16843^2 - 1 : ℕ) : ℤ)))) := by
    apply Good.of_factor
    · norm_num
    · norm_num
  convert hgood using 1
  norm_num [Rat.divInt_eq_div]

lemma harmonic_square_pred_good_16843 :
    Good 16843 (harmonic (16843^2 - 2) - 1) := by
  have hp : Nat.Prime 16843 := by norm_num
  let T : ℚ := ((((16843^2 - 1 : ℕ) : ℚ)⁻¹))
  have hcorrT : Good 16843 (1 + T) := by
    dsimp [T]
    exact correction_good_16843
  have hsq := harmonic_square_good_16843
  have hsub : Good 16843 (harmonic (16843^2 - 1) - (1 + T)) := Good.sub hp hsq hcorrT
  have hs0 := harmonic_succ (16843^2 - 2)
  have hs : harmonic (16843^2 - 1) = harmonic (16843^2 - 2) + T := by
    dsimp [T]
    have harg : 16843^2 - 2 + 1 = 16843^2 - 1 := by norm_num
    rw [harg] at hs0
    exact hs0
  have heq : harmonic (16843^2 - 1) - (1 + T) = harmonic (16843^2 - 2) - 1 := by
    rw [hs]
    abel
  rwa [heq] at hsub

lemma num_sub_one (q : ℚ) : (q - 1).num = q.num - (q.den : ℤ) := by
  have h := Rat.substr_num_den' q (1:ℚ)
  simpa using h

lemma pow_two_dvd_num_of_rep {p : ℕ} (hp : Nat.Prime p) {q : ℚ} {a b : ℤ}
    (hb0 : b ≠ 0) (hpb : ¬ (p : ℤ) ∣ b)
    (hq : q = ((p : ℤ)^2 * a) /. b) : ((p : ℤ)^2 ∣ q.num) := by
  by_cases hq0 : q = 0
  · simp [hq0]
  obtain ⟨c, hcnum, hcden⟩ := Rat.num_den_mk hb0 hq
  have hpc : ¬ (p : ℤ) ∣ c := by
    intro hdiv
    apply hpb
    rw [hcden]
    exact dvd_mul_of_dvd_left hdiv _
  have hpzprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hdivprod : ((p : ℤ)^2 ∣ c * q.num) := by
    rw [← hcnum]
    exact dvd_mul_right _ _
  exact hpzprime.pow_dvd_of_dvd_mul_left 2 hpc hdivprod

opaque Good.num_dvd {p : ℕ} (hp : Nat.Prime p) {q : ℚ} (hq : Good p q) :
    ((p : ℤ)^2 ∣ q.num) := by
  rcases hq with ⟨a,b,hb0,hpb,hrep⟩
  exact pow_two_dvd_num_of_rep hp hb0 hpb hrep

opaque harmonic_number_eq_harmonic (n : ℕ) : harmonic_number n = harmonic n := by
  simp [harmonic_number, harmonic, div_eq_mul_inv]


opaque harmonic_square_pred_num_dvd_16843 :
    ((16843 : ℤ)^2 ∣ (harmonic (16843^2 - 2) - 1).num) := by
  have hp : Nat.Prime 16843 := by norm_num
  exact Good.num_dvd hp harmonic_square_pred_good_16843

opaque harmonic_number_square_pred_num_dvd_16843 :
    ((16843 : ℤ)^2 ∣ (harmonic_number (16843^2 - 2) - 1).num) := by
  rw [harmonic_number_eq_harmonic (16843^2 - 2)]
  exact harmonic_square_pred_num_dvd_16843


lemma A309391_16843_sq : A309391 (16843^2) = 16843^2 := by
  let q : ℚ := harmonic_number (16843^2 - 2)
  have hnumdvd : ((16843 : ℤ)^2 ∣ (q - 1).num) := by
    dsimp [q]
    exact harmonic_number_square_pred_num_dvd_16843
  have hdiff : ((16843 : ℤ)^2 ∣ q.num - (q.den : ℤ)) := by
    have hnum_eq : (q - 1).num = q.num - (q.den : ℤ) := num_sub_one q
    rwa [hnum_eq] at hnumdvd
  have hnatdvd : 16843^2 ∣ (q.num - (q.den : ℤ)).natAbs := by
    exact_mod_cast (Int.natAbs_dvd_natAbs.mpr hdiff)
  have hgcd : Nat.gcd (16843^2) (q.num - (q.den : ℤ)).natAbs = 16843^2 := by
    rw [Nat.gcd_eq_left_iff_dvd]
    exact hnatdvd
  have hnot : ¬ 16843^2 < 3 := by norm_num
  unfold A309391
  rw [if_neg hnot]
  dsimp only
  exact hgcd

end Counter

theorem A309391_conjecture.disproof :
    ¬ (∀ (n : ℕ) (h_n : n > 2), A309391 n = n → Nat.Prime n) := by
  intro h
  have hA : A309391 (16843^2) = 16843^2 := Counter.A309391_16843_sq
  have hp := h (16843^2) (by norm_num) hA
  have hnp : ¬ Nat.Prime (16843^2) := by norm_num
  exact hnp hp
