import Submission.PrimeProof
import Submission.Diffs.Diff0
import Submission.Diffs.Diff1
import Submission.Diffs.Diff2
import Submission.Diffs.Diff3
import Submission.Diffs.Diff4
import Submission.Diffs.Diff5
import Submission.Diffs.Diff6
import Submission.Diffs.Diff7
import Submission.Diffs.Diff8
import Submission.Diffs.Diff9
import Submission.Diffs.Diff10
import Submission.Diffs.Diff11
import Submission.Diffs.Diff12
import Submission.Diffs.Diff13
import Submission.Diffs.Diff14
import Submission.Diffs.Diff15
import Submission.Diffs.Diff16
import Submission.Diffs.Diff17
import Submission.Diffs.Diff18
import Submission.Diffs.Diff19
import Submission.Diffs.Diff20
import Submission.Diffs.Diff21
import Submission.Diffs.Diff22
import Submission.Diffs.Diff23
import Submission.Diffs.Diff24
import Submission.Diffs.Diff25
import Submission.Diffs.Diff26
import Submission.Diffs.Diff27
import Submission.Diffs.Diff28
import Submission.Diffs.Diff29
import Submission.Diffs.Diff30
import Submission.Diffs.Diff31

lemma pi_0 : my_pi 0 = 0 := rfl

lemma pi_2 : my_pi 2 = 1 :=
  pi_step 2 0 2 0 1 rfl pi_0 diff_0

lemma pi_6 : my_pi 6 = 3 :=
  pi_step 6 2 4 1 2 rfl pi_2 diff_1

lemma pi_12 : my_pi 12 = 5 :=
  pi_step 12 6 6 3 2 rfl pi_6 diff_2

lemma pi_20 : my_pi 20 = 8 :=
  pi_step 20 12 8 5 3 rfl pi_12 diff_3

lemma pi_30 : my_pi 30 = 10 :=
  pi_step 30 20 10 8 2 rfl pi_20 diff_4

lemma pi_42 : my_pi 42 = 13 :=
  pi_step 42 30 12 10 3 rfl pi_30 diff_5

lemma pi_56 : my_pi 56 = 16 :=
  pi_step 56 42 14 13 3 rfl pi_42 diff_6

lemma pi_72 : my_pi 72 = 20 :=
  pi_step 72 56 16 16 4 rfl pi_56 diff_7

lemma pi_90 : my_pi 90 = 24 :=
  pi_step 90 72 18 20 4 rfl pi_72 diff_8

lemma pi_110 : my_pi 110 = 29 :=
  pi_step 110 90 20 24 5 rfl pi_90 diff_9

lemma pi_132 : my_pi 132 = 32 :=
  pi_step 132 110 22 29 3 rfl pi_110 diff_10

lemma pi_156 : my_pi 156 = 36 :=
  pi_step 156 132 24 32 4 rfl pi_132 diff_11

lemma pi_182 : my_pi 182 = 42 :=
  pi_step 182 156 26 36 6 rfl pi_156 diff_12

lemma pi_210 : my_pi 210 = 46 :=
  pi_step 210 182 28 42 4 rfl pi_182 diff_13

lemma pi_240 : my_pi 240 = 52 :=
  pi_step 240 210 30 46 6 rfl pi_210 diff_14

lemma pi_272 : my_pi 272 = 58 :=
  pi_step 272 240 32 52 6 rfl pi_240 diff_15

lemma pi_306 : my_pi 306 = 62 :=
  pi_step 306 272 34 58 4 rfl pi_272 diff_16

lemma pi_342 : my_pi 342 = 68 :=
  pi_step 342 306 36 62 6 rfl pi_306 diff_17

lemma pi_351 : my_pi 351 = 70 :=
  pi_step 351 342 9 68 2 rfl pi_342 diff_18

lemma pi_378 : my_pi 378 = 74 :=
  pi_step 378 351 27 70 4 rfl pi_351 diff_19

lemma pi_380 : my_pi 380 = 75 :=
  pi_step 380 378 2 74 1 rfl pi_378 diff_20

lemma pi_420 : my_pi 420 = 81 :=
  pi_step 420 380 40 75 6 rfl pi_380 diff_21

lemma pi_462 : my_pi 462 = 89 :=
  pi_step 462 420 42 81 8 rfl pi_420 diff_22

lemma pi_506 : my_pi 506 = 96 :=
  pi_step 506 462 44 89 7 rfl pi_462 diff_23

lemma pi_552 : my_pi 552 = 101 :=
  pi_step 552 506 46 96 5 rfl pi_506 diff_24

lemma pi_600 : my_pi 600 = 109 :=
  pi_step 600 552 48 101 8 rfl pi_552 diff_25

lemma pi_650 : my_pi 650 = 118 :=
  pi_step 650 600 50 109 9 rfl pi_600 diff_26

lemma pi_702 : my_pi 702 = 126 :=
  pi_step 702 650 52 118 8 rfl pi_650 diff_27

lemma pi_756 : my_pi 756 = 133 :=
  pi_step 756 702 54 126 7 rfl pi_702 diff_28

lemma pi_812 : my_pi 812 = 141 :=
  pi_step 812 756 56 133 8 rfl pi_756 diff_29

lemma pi_870 : my_pi 870 = 150 :=
  pi_step 870 812 58 141 9 rfl pi_812 diff_30

lemma pi_930 : my_pi 930 = 158 :=
  pi_step 930 870 60 150 8 rfl pi_870 diff_31

lemma pi_992 : my_pi 992 = 167 :=
  pi_step 992 930 62 158 9 rfl pi_930 diff_32

lemma pi_1035 : my_pi 1035 = 174 :=
  pi_step 1035 992 43 167 7 rfl pi_992 diff_33

lemma pi_1056 : my_pi 1056 = 177 :=
  pi_step 1056 1035 21 174 3 rfl pi_1035 diff_34

lemma pi_1081 : my_pi 1081 = 180 :=
  pi_step 1081 1056 25 177 3 rfl pi_1056 diff_35

lemma pi_1122 : my_pi 1122 = 187 :=
  pi_step 1122 1081 41 180 7 rfl pi_1081 diff_36

lemma pi_1190 : my_pi 1190 = 195 :=
  pi_step 1190 1122 68 187 8 rfl pi_1122 diff_37

lemma pi_1260 : my_pi 1260 = 205 :=
  pi_step 1260 1190 70 195 10 rfl pi_1190 diff_38

lemma pi_1332 : my_pi 1332 = 217 :=
  pi_step 1332 1260 72 205 12 rfl pi_1260 diff_39

lemma pi_1406 : my_pi 1406 = 222 :=
  pi_step 1406 1332 74 217 5 rfl pi_1332 diff_40

lemma pi_1482 : my_pi 1482 = 234 :=
  pi_step 1482 1406 76 222 12 rfl pi_1406 diff_41

lemma pi_1560 : my_pi 1560 = 246 :=
  pi_step 1560 1482 78 234 12 rfl pi_1482 diff_42

lemma pi_1640 : my_pi 1640 = 259 :=
  pi_step 1640 1560 80 246 13 rfl pi_1560 diff_43

lemma pi_1722 : my_pi 1722 = 268 :=
  pi_step 1722 1640 82 259 9 rfl pi_1640 diff_44

lemma pi_1806 : my_pi 1806 = 279 :=
  pi_step 1806 1722 84 268 11 rfl pi_1722 diff_45

lemma pi_1892 : my_pi 1892 = 290 :=
  pi_step 1892 1806 86 279 11 rfl pi_1806 diff_46

lemma pi_1953 : my_pi 1953 = 297 :=
  pi_step 1953 1892 61 290 7 rfl pi_1892 diff_47

lemma pi_1980 : my_pi 1980 = 299 :=
  pi_step 1980 1953 27 297 2 rfl pi_1953 diff_48

lemma pi_2016 : my_pi 2016 = 305 :=
  pi_step 2016 1980 36 299 6 rfl pi_1980 diff_49

lemma pi_2070 : my_pi 2070 = 312 :=
  pi_step 2070 2016 54 305 7 rfl pi_2016 diff_50

lemma pi_2162 : my_pi 2162 = 326 :=
  pi_step 2162 2070 92 312 14 rfl pi_2070 diff_51

lemma pi_2256 : my_pi 2256 = 335 :=
  pi_step 2256 2162 94 326 9 rfl pi_2162 diff_52

lemma pi_2352 : my_pi 2352 = 349 :=
  pi_step 2352 2256 96 335 14 rfl pi_2256 diff_53

lemma pi_2450 : my_pi 2450 = 363 :=
  pi_step 2450 2352 98 349 14 rfl pi_2352 diff_54

lemma pi_2550 : my_pi 2550 = 373 :=
  pi_step 2550 2450 100 363 10 rfl pi_2450 diff_55

lemma pi_2652 : my_pi 2652 = 383 :=
  pi_step 2652 2550 102 373 10 rfl pi_2550 diff_56

lemma pi_2756 : my_pi 2756 = 402 :=
  pi_step 2756 2652 104 383 19 rfl pi_2652 diff_57

lemma pi_2850 : my_pi 2850 = 413 :=
  pi_step 2850 2756 94 402 11 rfl pi_2756 diff_58

lemma pi_2862 : my_pi 2862 = 416 :=
  pi_step 2862 2850 12 413 3 rfl pi_2850 diff_59

lemma pi_2926 : my_pi 2926 = 422 :=
  pi_step 2926 2862 64 416 6 rfl pi_2862 diff_60

lemma pi_2970 : my_pi 2970 = 428 :=
  pi_step 2970 2926 44 422 6 rfl pi_2926 diff_61

lemma pi_3080 : my_pi 3080 = 440 :=
  pi_step 3080 2970 110 428 12 rfl pi_2970 diff_62

lemma pi_3192 : my_pi 3192 = 452 :=
  pi_step 3192 3080 112 440 12 rfl pi_3080 diff_63

lemma pi_3306 : my_pi 3306 = 464 :=
  pi_step 3306 3192 114 452 12 rfl pi_3192 diff_64

lemma pi_3422 : my_pi 3422 = 480 :=
  pi_step 3422 3306 116 464 16 rfl pi_3306 diff_65

lemma pi_3540 : my_pi 3540 = 495 :=
  pi_step 3540 3422 118 480 15 rfl pi_3422 diff_66

lemma pi_3660 : my_pi 3660 = 511 :=
  pi_step 3660 3540 120 495 16 rfl pi_3540 diff_67

lemma pi_3782 : my_pi 3782 = 526 :=
  pi_step 3782 3660 122 511 15 rfl pi_3660 diff_68

lemma pi_3828 : my_pi 3828 = 531 :=
  pi_step 3828 3782 46 526 5 rfl pi_3782 diff_69

lemma pi_3906 : my_pi 3906 = 539 :=
  pi_step 3906 3828 78 531 8 rfl pi_3828 diff_70

lemma pi_3916 : my_pi 3916 = 541 :=
  pi_step 3916 3906 10 539 2 rfl pi_3906 diff_71

lemma pi_4032 : my_pi 4032 = 557 :=
  pi_step 4032 3916 116 541 16 rfl pi_3916 diff_72

lemma pi_4160 : my_pi 4160 = 573 :=
  pi_step 4160 4032 128 557 16 rfl pi_4032 diff_73

lemma pi_4290 : my_pi 4290 = 589 :=
  pi_step 4290 4160 130 573 16 rfl pi_4160 diff_74

lemma pi_4422 : my_pi 4422 = 601 :=
  pi_step 4422 4290 132 589 12 rfl pi_4290 diff_75

lemma pi_4556 : my_pi 4556 = 617 :=
  pi_step 4556 4422 134 601 16 rfl pi_4422 diff_76

lemma pi_4692 : my_pi 4692 = 634 :=
  pi_step 4692 4556 136 617 17 rfl pi_4556 diff_77

lemma pi_4753 : my_pi 4753 = 640 :=
  pi_step 4753 4692 61 634 6 rfl pi_4692 diff_78

lemma pi_4830 : my_pi 4830 = 649 :=
  pi_step 4830 4753 77 640 9 rfl pi_4753 diff_79

lemma pi_4851 : my_pi 4851 = 650 :=
  pi_step 4851 4830 21 649 1 rfl pi_4830 diff_80

lemma pi_4970 : my_pi 4970 = 665 :=
  pi_step 4970 4851 119 650 15 rfl pi_4851 diff_81

lemma pi_5112 : my_pi 5112 = 683 :=
  pi_step 5112 4970 142 665 18 rfl pi_4970 diff_82

lemma pi_5256 : my_pi 5256 = 697 :=
  pi_step 5256 5112 144 683 14 rfl pi_5112 diff_83

lemma pi_5402 : my_pi 5402 = 712 :=
  pi_step 5402 5256 146 697 15 rfl pi_5256 diff_84

lemma pi_5550 : my_pi 5550 = 732 :=
  pi_step 5550 5402 148 712 20 rfl pi_5402 diff_85

lemma pi_5700 : my_pi 5700 = 750 :=
  pi_step 5700 5550 150 732 18 rfl pi_5550 diff_86

lemma pi_5778 : my_pi 5778 = 757 :=
  pi_step 5778 5700 78 750 7 rfl pi_5700 diff_87

lemma pi_5852 : my_pi 5852 = 769 :=
  pi_step 5852 5778 74 757 12 rfl pi_5778 diff_88

lemma pi_5886 : my_pi 5886 = 775 :=
  pi_step 5886 5852 34 769 6 rfl pi_5852 diff_89

lemma pi_6006 : my_pi 6006 = 783 :=
  pi_step 6006 5886 120 775 8 rfl pi_5886 diff_90

lemma pi_6162 : my_pi 6162 = 802 :=
  pi_step 6162 6006 156 783 19 rfl pi_6006 diff_91

lemma pi_6320 : my_pi 6320 = 822 :=
  pi_step 6320 6162 158 802 20 rfl pi_6162 diff_92

lemma pi_6480 : my_pi 6480 = 840 :=
  pi_step 6480 6320 160 822 18 rfl pi_6320 diff_93

lemma pi_6642 : my_pi 6642 = 856 :=
  pi_step 6642 6480 162 840 16 rfl pi_6480 diff_94

lemma pi_6806 : my_pi 6806 = 876 :=
  pi_step 6806 6642 164 856 20 rfl pi_6642 diff_95

lemma pi_6903 : my_pi 6903 = 887 :=
  pi_step 6903 6806 97 876 11 rfl pi_6806 diff_96

lemma pi_6972 : my_pi 6972 = 896 :=
  pi_step 6972 6903 69 887 9 rfl pi_6903 diff_97

lemma pi_7021 : my_pi 7021 = 903 :=
  pi_step 7021 6972 49 896 7 rfl pi_6972 diff_98

lemma pi_7140 : my_pi 7140 = 914 :=
  pi_step 7140 7021 119 903 11 rfl pi_7021 diff_99

