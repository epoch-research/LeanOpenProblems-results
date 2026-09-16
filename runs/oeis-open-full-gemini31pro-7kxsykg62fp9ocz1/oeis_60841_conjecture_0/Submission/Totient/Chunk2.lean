import Submission.Totient.Base
open Nat Finset Rat

set_option maxHeartbeats 200000000
set_option maxRecDepth 20000000
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem tot_920 : totient 920 = 352 := by
  have heq : (2^3 * (5 * (23)) : ℕ) = 920 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_23]
  try omega

theorem v3_phi_920 : v3_fast (totient 920) 100 = v3_phi_list.getD 920 0 := by
  rw [tot_920]
  rfl

theorem tot_921 : totient 921 = 612 := by
  have heq : (3 * (307) : ℕ) = 921 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_307 : totient 307 = 307 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_307]
  try omega

theorem v3_phi_921 : v3_fast (totient 921) 100 = v3_phi_list.getD 921 0 := by
  rw [tot_921]
  rfl

theorem tot_922 : totient 922 = 460 := by
  have heq : (2 * (461) : ℕ) = 922 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_461 : totient 461 = 461 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_461]
  try omega

theorem v3_phi_922 : v3_fast (totient 922) 100 = v3_phi_list.getD 922 0 := by
  rw [tot_922]
  rfl

theorem tot_923 : totient 923 = 840 := by
  have heq : (13 * (71) : ℕ) = 923 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_71]
  try omega

theorem v3_phi_923 : v3_fast (totient 923) 100 = v3_phi_list.getD 923 0 := by
  rw [tot_923]
  rfl

theorem tot_924 : totient 924 = 240 := by
  have heq : (2^2 * (3 * (7 * (11))) : ℕ) = 924 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_11]
  try omega

theorem v3_phi_924 : v3_fast (totient 924) 100 = v3_phi_list.getD 924 0 := by
  rw [tot_924]
  rfl

theorem tot_925 : totient 925 = 720 := by
  have heq : (5^2 * (37) : ℕ) = 925 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_37]
  try omega

theorem v3_phi_925 : v3_fast (totient 925) 100 = v3_phi_list.getD 925 0 := by
  rw [tot_925]
  rfl

theorem tot_926 : totient 926 = 462 := by
  have heq : (2 * (463) : ℕ) = 926 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_463 : totient 463 = 463 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_463]
  try omega

theorem v3_phi_926 : v3_fast (totient 926) 100 = v3_phi_list.getD 926 0 := by
  rw [tot_926]
  rfl

theorem tot_927 : totient 927 = 612 := by
  have heq : (3^2 * (103) : ℕ) = 927 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_103]
  try omega

theorem v3_phi_927 : v3_fast (totient 927) 100 = v3_phi_list.getD 927 0 := by
  rw [tot_927]
  rfl

theorem tot_928 : totient 928 = 448 := by
  have heq : (2^5 * (29) : ℕ) = 928 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_29]
  try omega

theorem v3_phi_928 : v3_fast (totient 928) 100 = v3_phi_list.getD 928 0 := by
  rw [tot_928]
  rfl

theorem tot_929 : totient 929 = 928 := by
  have h : totient 929 = 929 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_929 : v3_fast (totient 929) 100 = v3_phi_list.getD 929 0 := by
  rw [tot_929]
  rfl

theorem tot_930 : totient 930 = 240 := by
  have heq : (2 * (3 * (5 * (31))) : ℕ) = 930 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_31]
  try omega

theorem v3_phi_930 : v3_fast (totient 930) 100 = v3_phi_list.getD 930 0 := by
  rw [tot_930]
  rfl

theorem tot_931 : totient 931 = 756 := by
  have heq : (7^2 * (19) : ℕ) = 931 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_19]
  try omega

theorem v3_phi_931 : v3_fast (totient 931) 100 = v3_phi_list.getD 931 0 := by
  rw [tot_931]
  rfl

theorem tot_932 : totient 932 = 464 := by
  have heq : (2^2 * (233) : ℕ) = 932 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_233 : totient 233 = 233 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_233]
  try omega

theorem v3_phi_932 : v3_fast (totient 932) 100 = v3_phi_list.getD 932 0 := by
  rw [tot_932]
  rfl

theorem tot_933 : totient 933 = 620 := by
  have heq : (3 * (311) : ℕ) = 933 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_311 : totient 311 = 311 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_311]
  try omega

theorem v3_phi_933 : v3_fast (totient 933) 100 = v3_phi_list.getD 933 0 := by
  rw [tot_933]
  rfl

theorem tot_934 : totient 934 = 466 := by
  have heq : (2 * (467) : ℕ) = 934 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_467 : totient 467 = 467 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_467]
  try omega

theorem v3_phi_934 : v3_fast (totient 934) 100 = v3_phi_list.getD 934 0 := by
  rw [tot_934]
  rfl

theorem tot_935 : totient 935 = 640 := by
  have heq : (5 * (11 * (17)) : ℕ) = 935 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11, hp_17]
  try omega

theorem v3_phi_935 : v3_fast (totient 935) 100 = v3_phi_list.getD 935 0 := by
  rw [tot_935]
  rfl

theorem tot_936 : totient 936 = 288 := by
  have heq : (2^3 * (3^2 * (13)) : ℕ) = 936 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13]
  try omega

theorem v3_phi_936 : v3_fast (totient 936) 100 = v3_phi_list.getD 936 0 := by
  rw [tot_936]
  rfl

theorem tot_937 : totient 937 = 936 := by
  have h : totient 937 = 937 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_937 : v3_fast (totient 937) 100 = v3_phi_list.getD 937 0 := by
  rw [tot_937]
  rfl

theorem tot_938 : totient 938 = 396 := by
  have heq : (2 * (7 * (67)) : ℕ) = 938 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_67]
  try omega

theorem v3_phi_938 : v3_fast (totient 938) 100 = v3_phi_list.getD 938 0 := by
  rw [tot_938]
  rfl

theorem tot_939 : totient 939 = 624 := by
  have heq : (3 * (313) : ℕ) = 939 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_313 : totient 313 = 313 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_313]
  try omega

theorem v3_phi_939 : v3_fast (totient 939) 100 = v3_phi_list.getD 939 0 := by
  rw [tot_939]
  rfl

theorem tot_940 : totient 940 = 368 := by
  have heq : (2^2 * (5 * (47)) : ℕ) = 940 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_47]
  try omega

theorem v3_phi_940 : v3_fast (totient 940) 100 = v3_phi_list.getD 940 0 := by
  rw [tot_940]
  rfl

theorem tot_941 : totient 941 = 940 := by
  have h : totient 941 = 941 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_941 : v3_fast (totient 941) 100 = v3_phi_list.getD 941 0 := by
  rw [tot_941]
  rfl

theorem tot_942 : totient 942 = 312 := by
  have heq : (2 * (3 * (157)) : ℕ) = 942 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_157]
  try omega

theorem v3_phi_942 : v3_fast (totient 942) 100 = v3_phi_list.getD 942 0 := by
  rw [tot_942]
  rfl

theorem tot_943 : totient 943 = 880 := by
  have heq : (23 * (41) : ℕ) = 943 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_41]
  try omega

theorem v3_phi_943 : v3_fast (totient 943) 100 = v3_phi_list.getD 943 0 := by
  rw [tot_943]
  rfl

theorem tot_944 : totient 944 = 464 := by
  have heq : (2^4 * (59) : ℕ) = 944 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_59]
  try omega

theorem v3_phi_944 : v3_fast (totient 944) 100 = v3_phi_list.getD 944 0 := by
  rw [tot_944]
  rfl

theorem tot_945 : totient 945 = 432 := by
  have heq : (3^3 * (5 * (7)) : ℕ) = 945 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7]
  try omega

theorem v3_phi_945 : v3_fast (totient 945) 100 = v3_phi_list.getD 945 0 := by
  rw [tot_945]
  rfl

theorem tot_946 : totient 946 = 420 := by
  have heq : (2 * (11 * (43)) : ℕ) = 946 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_43]
  try omega

theorem v3_phi_946 : v3_fast (totient 946) 100 = v3_phi_list.getD 946 0 := by
  rw [tot_946]
  rfl

theorem tot_947 : totient 947 = 946 := by
  have h : totient 947 = 947 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_947 : v3_fast (totient 947) 100 = v3_phi_list.getD 947 0 := by
  rw [tot_947]
  rfl

theorem tot_948 : totient 948 = 312 := by
  have heq : (2^2 * (3 * (79)) : ℕ) = 948 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_79]
  try omega

theorem v3_phi_948 : v3_fast (totient 948) 100 = v3_phi_list.getD 948 0 := by
  rw [tot_948]
  rfl

theorem tot_949 : totient 949 = 864 := by
  have heq : (13 * (73) : ℕ) = 949 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_73]
  try omega

theorem v3_phi_949 : v3_fast (totient 949) 100 = v3_phi_list.getD 949 0 := by
  rw [tot_949]
  rfl

theorem tot_950 : totient 950 = 360 := by
  have heq : (2 * (5^2 * (19)) : ℕ) = 950 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_19]
  try omega

theorem v3_phi_950 : v3_fast (totient 950) 100 = v3_phi_list.getD 950 0 := by
  rw [tot_950]
  rfl

theorem tot_951 : totient 951 = 632 := by
  have heq : (3 * (317) : ℕ) = 951 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_317 : totient 317 = 317 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_317]
  try omega

theorem v3_phi_951 : v3_fast (totient 951) 100 = v3_phi_list.getD 951 0 := by
  rw [tot_951]
  rfl

theorem tot_952 : totient 952 = 384 := by
  have heq : (2^3 * (7 * (17)) : ℕ) = 952 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_17]
  try omega

theorem v3_phi_952 : v3_fast (totient 952) 100 = v3_phi_list.getD 952 0 := by
  rw [tot_952]
  rfl

theorem tot_953 : totient 953 = 952 := by
  have h : totient 953 = 953 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_953 : v3_fast (totient 953) 100 = v3_phi_list.getD 953 0 := by
  rw [tot_953]
  rfl

theorem tot_954 : totient 954 = 312 := by
  have heq : (2 * (3^2 * (53)) : ℕ) = 954 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_53]
  try omega

theorem v3_phi_954 : v3_fast (totient 954) 100 = v3_phi_list.getD 954 0 := by
  rw [tot_954]
  rfl

theorem tot_955 : totient 955 = 760 := by
  have heq : (5 * (191) : ℕ) = 955 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_191]
  try omega

theorem v3_phi_955 : v3_fast (totient 955) 100 = v3_phi_list.getD 955 0 := by
  rw [tot_955]
  rfl

theorem tot_956 : totient 956 = 476 := by
  have heq : (2^2 * (239) : ℕ) = 956 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_239 : totient 239 = 239 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_239]
  try omega

theorem v3_phi_956 : v3_fast (totient 956) 100 = v3_phi_list.getD 956 0 := by
  rw [tot_956]
  rfl

theorem tot_957 : totient 957 = 560 := by
  have heq : (3 * (11 * (29)) : ℕ) = 957 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_29]
  try omega

theorem v3_phi_957 : v3_fast (totient 957) 100 = v3_phi_list.getD 957 0 := by
  rw [tot_957]
  rfl

theorem tot_958 : totient 958 = 478 := by
  have heq : (2 * (479) : ℕ) = 958 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_479 : totient 479 = 479 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_479]
  try omega

theorem v3_phi_958 : v3_fast (totient 958) 100 = v3_phi_list.getD 958 0 := by
  rw [tot_958]
  rfl

theorem tot_959 : totient 959 = 816 := by
  have heq : (7 * (137) : ℕ) = 959 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_137]
  try omega

theorem v3_phi_959 : v3_fast (totient 959) 100 = v3_phi_list.getD 959 0 := by
  rw [tot_959]
  rfl

theorem tot_960 : totient 960 = 256 := by
  have heq : (2^6 * (3 * (5)) : ℕ) = 960 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_960 : v3_fast (totient 960) 100 = v3_phi_list.getD 960 0 := by
  rw [tot_960]
  rfl

theorem tot_961 : totient 961 = 930 := by
  have h : totient (31^2) = 31^1 * (31 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (31^2 : ℕ) = 961 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_961 : v3_fast (totient 961) 100 = v3_phi_list.getD 961 0 := by
  rw [tot_961]
  rfl

theorem tot_962 : totient 962 = 432 := by
  have heq : (2 * (13 * (37)) : ℕ) = 962 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_37]
  try omega

theorem v3_phi_962 : v3_fast (totient 962) 100 = v3_phi_list.getD 962 0 := by
  rw [tot_962]
  rfl

theorem tot_963 : totient 963 = 636 := by
  have heq : (3^2 * (107) : ℕ) = 963 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_107]
  try omega

theorem v3_phi_963 : v3_fast (totient 963) 100 = v3_phi_list.getD 963 0 := by
  rw [tot_963]
  rfl

theorem tot_964 : totient 964 = 480 := by
  have heq : (2^2 * (241) : ℕ) = 964 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_241 : totient 241 = 241 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_241]
  try omega

theorem v3_phi_964 : v3_fast (totient 964) 100 = v3_phi_list.getD 964 0 := by
  rw [tot_964]
  rfl

theorem tot_965 : totient 965 = 768 := by
  have heq : (5 * (193) : ℕ) = 965 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_193]
  try omega

theorem v3_phi_965 : v3_fast (totient 965) 100 = v3_phi_list.getD 965 0 := by
  rw [tot_965]
  rfl

theorem tot_966 : totient 966 = 264 := by
  have heq : (2 * (3 * (7 * (23))) : ℕ) = 966 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_23]
  try omega

theorem v3_phi_966 : v3_fast (totient 966) 100 = v3_phi_list.getD 966 0 := by
  rw [tot_966]
  rfl

theorem tot_967 : totient 967 = 966 := by
  have h : totient 967 = 967 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_967 : v3_fast (totient 967) 100 = v3_phi_list.getD 967 0 := by
  rw [tot_967]
  rfl

theorem tot_968 : totient 968 = 440 := by
  have heq : (2^3 * (11^2) : ℕ) = 968 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_11]
  try omega

theorem v3_phi_968 : v3_fast (totient 968) 100 = v3_phi_list.getD 968 0 := by
  rw [tot_968]
  rfl

theorem tot_969 : totient 969 = 576 := by
  have heq : (3 * (17 * (19)) : ℕ) = 969 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17, hp_19]
  try omega

theorem v3_phi_969 : v3_fast (totient 969) 100 = v3_phi_list.getD 969 0 := by
  rw [tot_969]
  rfl

theorem tot_970 : totient 970 = 384 := by
  have heq : (2 * (5 * (97)) : ℕ) = 970 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_97]
  try omega

theorem v3_phi_970 : v3_fast (totient 970) 100 = v3_phi_list.getD 970 0 := by
  rw [tot_970]
  rfl

theorem tot_971 : totient 971 = 970 := by
  have h : totient 971 = 971 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_971 : v3_fast (totient 971) 100 = v3_phi_list.getD 971 0 := by
  rw [tot_971]
  rfl

theorem tot_972 : totient 972 = 324 := by
  have heq : (2^2 * (3^5) : ℕ) = 972 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^5) = 3^4 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_972 : v3_fast (totient 972) 100 = v3_phi_list.getD 972 0 := by
  rw [tot_972]
  rfl

theorem tot_973 : totient 973 = 828 := by
  have heq : (7 * (139) : ℕ) = 973 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_139]
  try omega

theorem v3_phi_973 : v3_fast (totient 973) 100 = v3_phi_list.getD 973 0 := by
  rw [tot_973]
  rfl

theorem tot_974 : totient 974 = 486 := by
  have heq : (2 * (487) : ℕ) = 974 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_487 : totient 487 = 487 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_487]
  try omega

theorem v3_phi_974 : v3_fast (totient 974) 100 = v3_phi_list.getD 974 0 := by
  rw [tot_974]
  rfl

theorem tot_975 : totient 975 = 480 := by
  have heq : (3 * (5^2 * (13)) : ℕ) = 975 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_13]
  try omega

theorem v3_phi_975 : v3_fast (totient 975) 100 = v3_phi_list.getD 975 0 := by
  rw [tot_975]
  rfl

theorem tot_976 : totient 976 = 480 := by
  have heq : (2^4 * (61) : ℕ) = 976 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_61]
  try omega

theorem v3_phi_976 : v3_fast (totient 976) 100 = v3_phi_list.getD 976 0 := by
  rw [tot_976]
  rfl

theorem tot_977 : totient 977 = 976 := by
  have h : totient 977 = 977 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_977 : v3_fast (totient 977) 100 = v3_phi_list.getD 977 0 := by
  rw [tot_977]
  rfl

theorem tot_978 : totient 978 = 324 := by
  have heq : (2 * (3 * (163)) : ℕ) = 978 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_163]
  try omega

theorem v3_phi_978 : v3_fast (totient 978) 100 = v3_phi_list.getD 978 0 := by
  rw [tot_978]
  rfl

theorem tot_979 : totient 979 = 880 := by
  have heq : (11 * (89) : ℕ) = 979 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_89]
  try omega

theorem v3_phi_979 : v3_fast (totient 979) 100 = v3_phi_list.getD 979 0 := by
  rw [tot_979]
  rfl

theorem tot_980 : totient 980 = 336 := by
  have heq : (2^2 * (5 * (7^2)) : ℕ) = 980 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5, hp_7]
  try omega

theorem v3_phi_980 : v3_fast (totient 980) 100 = v3_phi_list.getD 980 0 := by
  rw [tot_980]
  rfl

theorem tot_981 : totient 981 = 648 := by
  have heq : (3^2 * (109) : ℕ) = 981 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_109]
  try omega

theorem v3_phi_981 : v3_fast (totient 981) 100 = v3_phi_list.getD 981 0 := by
  rw [tot_981]
  rfl

theorem tot_982 : totient 982 = 490 := by
  have heq : (2 * (491) : ℕ) = 982 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_491 : totient 491 = 491 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_491]
  try omega

theorem v3_phi_982 : v3_fast (totient 982) 100 = v3_phi_list.getD 982 0 := by
  rw [tot_982]
  rfl

theorem tot_983 : totient 983 = 982 := by
  have h : totient 983 = 983 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_983 : v3_fast (totient 983) 100 = v3_phi_list.getD 983 0 := by
  rw [tot_983]
  rfl

theorem tot_984 : totient 984 = 320 := by
  have heq : (2^3 * (3 * (41)) : ℕ) = 984 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_41]
  try omega

theorem v3_phi_984 : v3_fast (totient 984) 100 = v3_phi_list.getD 984 0 := by
  rw [tot_984]
  rfl

theorem tot_985 : totient 985 = 784 := by
  have heq : (5 * (197) : ℕ) = 985 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_197]
  try omega

theorem v3_phi_985 : v3_fast (totient 985) 100 = v3_phi_list.getD 985 0 := by
  rw [tot_985]
  rfl

theorem tot_986 : totient 986 = 448 := by
  have heq : (2 * (17 * (29)) : ℕ) = 986 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_29]
  try omega

theorem v3_phi_986 : v3_fast (totient 986) 100 = v3_phi_list.getD 986 0 := by
  rw [tot_986]
  rfl

theorem tot_987 : totient 987 = 552 := by
  have heq : (3 * (7 * (47)) : ℕ) = 987 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_47]
  try omega

theorem v3_phi_987 : v3_fast (totient 987) 100 = v3_phi_list.getD 987 0 := by
  rw [tot_987]
  rfl

theorem tot_988 : totient 988 = 432 := by
  have heq : (2^2 * (13 * (19)) : ℕ) = 988 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_19]
  try omega

theorem v3_phi_988 : v3_fast (totient 988) 100 = v3_phi_list.getD 988 0 := by
  rw [tot_988]
  rfl

theorem tot_989 : totient 989 = 924 := by
  have heq : (23 * (43) : ℕ) = 989 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_43]
  try omega

theorem v3_phi_989 : v3_fast (totient 989) 100 = v3_phi_list.getD 989 0 := by
  rw [tot_989]
  rfl

theorem tot_990 : totient 990 = 240 := by
  have heq : (2 * (3^2 * (5 * (11))) : ℕ) = 990 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_11]
  try omega

theorem v3_phi_990 : v3_fast (totient 990) 100 = v3_phi_list.getD 990 0 := by
  rw [tot_990]
  rfl

theorem tot_991 : totient 991 = 990 := by
  have h : totient 991 = 991 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_991 : v3_fast (totient 991) 100 = v3_phi_list.getD 991 0 := by
  rw [tot_991]
  rfl

theorem tot_992 : totient 992 = 480 := by
  have heq : (2^5 * (31) : ℕ) = 992 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_31]
  try omega

theorem v3_phi_992 : v3_fast (totient 992) 100 = v3_phi_list.getD 992 0 := by
  rw [tot_992]
  rfl

theorem tot_993 : totient 993 = 660 := by
  have heq : (3 * (331) : ℕ) = 993 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_331 : totient 331 = 331 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_331]
  try omega

theorem v3_phi_993 : v3_fast (totient 993) 100 = v3_phi_list.getD 993 0 := by
  rw [tot_993]
  rfl

theorem tot_994 : totient 994 = 420 := by
  have heq : (2 * (7 * (71)) : ℕ) = 994 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_71]
  try omega

theorem v3_phi_994 : v3_fast (totient 994) 100 = v3_phi_list.getD 994 0 := by
  rw [tot_994]
  rfl

theorem tot_995 : totient 995 = 792 := by
  have heq : (5 * (199) : ℕ) = 995 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_199]
  try omega

theorem v3_phi_995 : v3_fast (totient 995) 100 = v3_phi_list.getD 995 0 := by
  rw [tot_995]
  rfl

theorem tot_996 : totient 996 = 328 := by
  have heq : (2^2 * (3 * (83)) : ℕ) = 996 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_83]
  try omega

theorem v3_phi_996 : v3_fast (totient 996) 100 = v3_phi_list.getD 996 0 := by
  rw [tot_996]
  rfl

theorem tot_997 : totient 997 = 996 := by
  have h : totient 997 = 997 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_997 : v3_fast (totient 997) 100 = v3_phi_list.getD 997 0 := by
  rw [tot_997]
  rfl

theorem tot_998 : totient 998 = 498 := by
  have heq : (2 * (499) : ℕ) = 998 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_499 : totient 499 = 499 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_499]
  try omega

theorem v3_phi_998 : v3_fast (totient 998) 100 = v3_phi_list.getD 998 0 := by
  rw [tot_998]
  rfl

theorem tot_999 : totient 999 = 648 := by
  have heq : (3^3 * (37) : ℕ) = 999 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_37]
  try omega

theorem v3_phi_999 : v3_fast (totient 999) 100 = v3_phi_list.getD 999 0 := by
  rw [tot_999]
  rfl

theorem tot_1000 : totient 1000 = 400 := by
  have heq : (2^3 * (5^3) : ℕ) = 1000 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_1000 : v3_fast (totient 1000) 100 = v3_phi_list.getD 1000 0 := by
  rw [tot_1000]
  rfl

theorem tot_1001 : totient 1001 = 720 := by
  have heq : (7 * (11 * (13)) : ℕ) = 1001 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_11, hp_13]
  try omega

theorem v3_phi_1001 : v3_fast (totient 1001) 100 = v3_phi_list.getD 1001 0 := by
  rw [tot_1001]
  rfl

theorem tot_1002 : totient 1002 = 332 := by
  have heq : (2 * (3 * (167)) : ℕ) = 1002 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_167]
  try omega

theorem v3_phi_1002 : v3_fast (totient 1002) 100 = v3_phi_list.getD 1002 0 := by
  rw [tot_1002]
  rfl

theorem tot_1003 : totient 1003 = 928 := by
  have heq : (17 * (59) : ℕ) = 1003 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_59]
  try omega

theorem v3_phi_1003 : v3_fast (totient 1003) 100 = v3_phi_list.getD 1003 0 := by
  rw [tot_1003]
  rfl

theorem tot_1004 : totient 1004 = 500 := by
  have heq : (2^2 * (251) : ℕ) = 1004 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_251 : totient 251 = 251 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_251]
  try omega

theorem v3_phi_1004 : v3_fast (totient 1004) 100 = v3_phi_list.getD 1004 0 := by
  rw [tot_1004]
  rfl

theorem tot_1005 : totient 1005 = 528 := by
  have heq : (3 * (5 * (67)) : ℕ) = 1005 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_67]
  try omega

theorem v3_phi_1005 : v3_fast (totient 1005) 100 = v3_phi_list.getD 1005 0 := by
  rw [tot_1005]
  rfl

theorem tot_1006 : totient 1006 = 502 := by
  have heq : (2 * (503) : ℕ) = 1006 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_503 : totient 503 = 503 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_503]
  try omega

theorem v3_phi_1006 : v3_fast (totient 1006) 100 = v3_phi_list.getD 1006 0 := by
  rw [tot_1006]
  rfl

theorem tot_1007 : totient 1007 = 936 := by
  have heq : (19 * (53) : ℕ) = 1007 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_53]
  try omega

theorem v3_phi_1007 : v3_fast (totient 1007) 100 = v3_phi_list.getD 1007 0 := by
  rw [tot_1007]
  rfl

theorem tot_1008 : totient 1008 = 288 := by
  have heq : (2^4 * (3^2 * (7)) : ℕ) = 1008 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_1008 : v3_fast (totient 1008) 100 = v3_phi_list.getD 1008 0 := by
  rw [tot_1008]
  rfl

theorem tot_1009 : totient 1009 = 1008 := by
  have h : totient 1009 = 1009 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1009 : v3_fast (totient 1009) 100 = v3_phi_list.getD 1009 0 := by
  rw [tot_1009]
  rfl

theorem tot_1010 : totient 1010 = 400 := by
  have heq : (2 * (5 * (101)) : ℕ) = 1010 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_101]
  try omega

theorem v3_phi_1010 : v3_fast (totient 1010) 100 = v3_phi_list.getD 1010 0 := by
  rw [tot_1010]
  rfl

theorem tot_1011 : totient 1011 = 672 := by
  have heq : (3 * (337) : ℕ) = 1011 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_337 : totient 337 = 337 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_337]
  try omega

theorem v3_phi_1011 : v3_fast (totient 1011) 100 = v3_phi_list.getD 1011 0 := by
  rw [tot_1011]
  rfl

theorem tot_1012 : totient 1012 = 440 := by
  have heq : (2^2 * (11 * (23)) : ℕ) = 1012 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_23]
  try omega

theorem v3_phi_1012 : v3_fast (totient 1012) 100 = v3_phi_list.getD 1012 0 := by
  rw [tot_1012]
  rfl

theorem tot_1013 : totient 1013 = 1012 := by
  have h : totient 1013 = 1013 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1013 : v3_fast (totient 1013) 100 = v3_phi_list.getD 1013 0 := by
  rw [tot_1013]
  rfl

theorem tot_1014 : totient 1014 = 312 := by
  have heq : (2 * (3 * (13^2)) : ℕ) = 1014 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_13]
  try omega

theorem v3_phi_1014 : v3_fast (totient 1014) 100 = v3_phi_list.getD 1014 0 := by
  rw [tot_1014]
  rfl

theorem tot_1015 : totient 1015 = 672 := by
  have heq : (5 * (7 * (29)) : ℕ) = 1015 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_29]
  try omega

theorem v3_phi_1015 : v3_fast (totient 1015) 100 = v3_phi_list.getD 1015 0 := by
  rw [tot_1015]
  rfl

theorem tot_1016 : totient 1016 = 504 := by
  have heq : (2^3 * (127) : ℕ) = 1016 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_127]
  try omega

theorem v3_phi_1016 : v3_fast (totient 1016) 100 = v3_phi_list.getD 1016 0 := by
  rw [tot_1016]
  rfl

theorem tot_1017 : totient 1017 = 672 := by
  have heq : (3^2 * (113) : ℕ) = 1017 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_113]
  try omega

theorem v3_phi_1017 : v3_fast (totient 1017) 100 = v3_phi_list.getD 1017 0 := by
  rw [tot_1017]
  rfl

theorem tot_1018 : totient 1018 = 508 := by
  have heq : (2 * (509) : ℕ) = 1018 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_509 : totient 509 = 509 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_509]
  try omega

theorem v3_phi_1018 : v3_fast (totient 1018) 100 = v3_phi_list.getD 1018 0 := by
  rw [tot_1018]
  rfl

theorem tot_1019 : totient 1019 = 1018 := by
  have h : totient 1019 = 1019 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1019 : v3_fast (totient 1019) 100 = v3_phi_list.getD 1019 0 := by
  rw [tot_1019]
  rfl

theorem tot_1020 : totient 1020 = 256 := by
  have heq : (2^2 * (3 * (5 * (17))) : ℕ) = 1020 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_17]
  try omega

theorem v3_phi_1020 : v3_fast (totient 1020) 100 = v3_phi_list.getD 1020 0 := by
  rw [tot_1020]
  rfl

theorem tot_1021 : totient 1021 = 1020 := by
  have h : totient 1021 = 1021 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1021 : v3_fast (totient 1021) 100 = v3_phi_list.getD 1021 0 := by
  rw [tot_1021]
  rfl

theorem tot_1022 : totient 1022 = 432 := by
  have heq : (2 * (7 * (73)) : ℕ) = 1022 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_73]
  try omega

theorem v3_phi_1022 : v3_fast (totient 1022) 100 = v3_phi_list.getD 1022 0 := by
  rw [tot_1022]
  rfl

theorem tot_1023 : totient 1023 = 600 := by
  have heq : (3 * (11 * (31)) : ℕ) = 1023 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_31]
  try omega

theorem v3_phi_1023 : v3_fast (totient 1023) 100 = v3_phi_list.getD 1023 0 := by
  rw [tot_1023]
  rfl

theorem tot_1024 : totient 1024 = 512 := by
  have h : totient (2^10) = 2^9 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (2^10 : ℕ) = 1024 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_1024 : v3_fast (totient 1024) 100 = v3_phi_list.getD 1024 0 := by
  rw [tot_1024]
  rfl

theorem tot_1025 : totient 1025 = 800 := by
  have heq : (5^2 * (41) : ℕ) = 1025 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_41]
  try omega

theorem v3_phi_1025 : v3_fast (totient 1025) 100 = v3_phi_list.getD 1025 0 := by
  rw [tot_1025]
  rfl

theorem tot_1026 : totient 1026 = 324 := by
  have heq : (2 * (3^3 * (19)) : ℕ) = 1026 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19]
  try omega

theorem v3_phi_1026 : v3_fast (totient 1026) 100 = v3_phi_list.getD 1026 0 := by
  rw [tot_1026]
  rfl

theorem tot_1027 : totient 1027 = 936 := by
  have heq : (13 * (79) : ℕ) = 1027 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_79]
  try omega

theorem v3_phi_1027 : v3_fast (totient 1027) 100 = v3_phi_list.getD 1027 0 := by
  rw [tot_1027]
  rfl

theorem tot_1028 : totient 1028 = 512 := by
  have heq : (2^2 * (257) : ℕ) = 1028 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_257 : totient 257 = 257 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_257]
  try omega

theorem v3_phi_1028 : v3_fast (totient 1028) 100 = v3_phi_list.getD 1028 0 := by
  rw [tot_1028]
  rfl

theorem tot_1029 : totient 1029 = 588 := by
  have heq : (3 * (7^3) : ℕ) = 1029 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^3) = 7^2 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_7]
  try omega

theorem v3_phi_1029 : v3_fast (totient 1029) 100 = v3_phi_list.getD 1029 0 := by
  rw [tot_1029]
  rfl

theorem tot_1030 : totient 1030 = 408 := by
  have heq : (2 * (5 * (103)) : ℕ) = 1030 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_103]
  try omega

theorem v3_phi_1030 : v3_fast (totient 1030) 100 = v3_phi_list.getD 1030 0 := by
  rw [tot_1030]
  rfl

theorem tot_1031 : totient 1031 = 1030 := by
  have h : totient 1031 = 1031 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1031 : v3_fast (totient 1031) 100 = v3_phi_list.getD 1031 0 := by
  rw [tot_1031]
  rfl

theorem tot_1032 : totient 1032 = 336 := by
  have heq : (2^3 * (3 * (43)) : ℕ) = 1032 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_43]
  try omega

theorem v3_phi_1032 : v3_fast (totient 1032) 100 = v3_phi_list.getD 1032 0 := by
  rw [tot_1032]
  rfl

theorem tot_1033 : totient 1033 = 1032 := by
  have h : totient 1033 = 1033 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1033 : v3_fast (totient 1033) 100 = v3_phi_list.getD 1033 0 := by
  rw [tot_1033]
  rfl

theorem tot_1034 : totient 1034 = 460 := by
  have heq : (2 * (11 * (47)) : ℕ) = 1034 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_47]
  try omega

theorem v3_phi_1034 : v3_fast (totient 1034) 100 = v3_phi_list.getD 1034 0 := by
  rw [tot_1034]
  rfl

theorem tot_1035 : totient 1035 = 528 := by
  have heq : (3^2 * (5 * (23)) : ℕ) = 1035 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_23]
  try omega

theorem v3_phi_1035 : v3_fast (totient 1035) 100 = v3_phi_list.getD 1035 0 := by
  rw [tot_1035]
  rfl

theorem tot_1036 : totient 1036 = 432 := by
  have heq : (2^2 * (7 * (37)) : ℕ) = 1036 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_37]
  try omega

theorem v3_phi_1036 : v3_fast (totient 1036) 100 = v3_phi_list.getD 1036 0 := by
  rw [tot_1036]
  rfl

theorem tot_1037 : totient 1037 = 960 := by
  have heq : (17 * (61) : ℕ) = 1037 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_61]
  try omega

theorem v3_phi_1037 : v3_fast (totient 1037) 100 = v3_phi_list.getD 1037 0 := by
  rw [tot_1037]
  rfl

theorem tot_1038 : totient 1038 = 344 := by
  have heq : (2 * (3 * (173)) : ℕ) = 1038 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_173]
  try omega

theorem v3_phi_1038 : v3_fast (totient 1038) 100 = v3_phi_list.getD 1038 0 := by
  rw [tot_1038]
  rfl

theorem tot_1039 : totient 1039 = 1038 := by
  have h : totient 1039 = 1039 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1039 : v3_fast (totient 1039) 100 = v3_phi_list.getD 1039 0 := by
  rw [tot_1039]
  rfl

theorem tot_1040 : totient 1040 = 384 := by
  have heq : (2^4 * (5 * (13)) : ℕ) = 1040 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_13]
  try omega

theorem v3_phi_1040 : v3_fast (totient 1040) 100 = v3_phi_list.getD 1040 0 := by
  rw [tot_1040]
  rfl

theorem tot_1041 : totient 1041 = 692 := by
  have heq : (3 * (347) : ℕ) = 1041 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_347 : totient 347 = 347 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_347]
  try omega

theorem v3_phi_1041 : v3_fast (totient 1041) 100 = v3_phi_list.getD 1041 0 := by
  rw [tot_1041]
  rfl

theorem tot_1042 : totient 1042 = 520 := by
  have heq : (2 * (521) : ℕ) = 1042 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_521 : totient 521 = 521 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_521]
  try omega

theorem v3_phi_1042 : v3_fast (totient 1042) 100 = v3_phi_list.getD 1042 0 := by
  rw [tot_1042]
  rfl

theorem tot_1043 : totient 1043 = 888 := by
  have heq : (7 * (149) : ℕ) = 1043 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_149]
  try omega

theorem v3_phi_1043 : v3_fast (totient 1043) 100 = v3_phi_list.getD 1043 0 := by
  rw [tot_1043]
  rfl

theorem tot_1044 : totient 1044 = 336 := by
  have heq : (2^2 * (3^2 * (29)) : ℕ) = 1044 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_29]
  try omega

theorem v3_phi_1044 : v3_fast (totient 1044) 100 = v3_phi_list.getD 1044 0 := by
  rw [tot_1044]
  rfl

theorem tot_1045 : totient 1045 = 720 := by
  have heq : (5 * (11 * (19)) : ℕ) = 1045 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11, hp_19]
  try omega

theorem v3_phi_1045 : v3_fast (totient 1045) 100 = v3_phi_list.getD 1045 0 := by
  rw [tot_1045]
  rfl

theorem tot_1046 : totient 1046 = 522 := by
  have heq : (2 * (523) : ℕ) = 1046 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_523 : totient 523 = 523 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_523]
  try omega

theorem v3_phi_1046 : v3_fast (totient 1046) 100 = v3_phi_list.getD 1046 0 := by
  rw [tot_1046]
  rfl

theorem tot_1047 : totient 1047 = 696 := by
  have heq : (3 * (349) : ℕ) = 1047 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_349 : totient 349 = 349 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_349]
  try omega

theorem v3_phi_1047 : v3_fast (totient 1047) 100 = v3_phi_list.getD 1047 0 := by
  rw [tot_1047]
  rfl

theorem tot_1048 : totient 1048 = 520 := by
  have heq : (2^3 * (131) : ℕ) = 1048 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_131]
  try omega

theorem v3_phi_1048 : v3_fast (totient 1048) 100 = v3_phi_list.getD 1048 0 := by
  rw [tot_1048]
  rfl

theorem tot_1049 : totient 1049 = 1048 := by
  have h : totient 1049 = 1049 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1049 : v3_fast (totient 1049) 100 = v3_phi_list.getD 1049 0 := by
  rw [tot_1049]
  rfl

theorem tot_1050 : totient 1050 = 240 := by
  have heq : (2 * (3 * (5^2 * (7))) : ℕ) = 1050 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_7]
  try omega

theorem v3_phi_1050 : v3_fast (totient 1050) 100 = v3_phi_list.getD 1050 0 := by
  rw [tot_1050]
  rfl

theorem tot_1051 : totient 1051 = 1050 := by
  have h : totient 1051 = 1051 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1051 : v3_fast (totient 1051) 100 = v3_phi_list.getD 1051 0 := by
  rw [tot_1051]
  rfl

theorem tot_1052 : totient 1052 = 524 := by
  have heq : (2^2 * (263) : ℕ) = 1052 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_263 : totient 263 = 263 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_263]
  try omega

theorem v3_phi_1052 : v3_fast (totient 1052) 100 = v3_phi_list.getD 1052 0 := by
  rw [tot_1052]
  rfl

theorem tot_1053 : totient 1053 = 648 := by
  have heq : (3^4 * (13) : ℕ) = 1053 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13]
  try omega

theorem v3_phi_1053 : v3_fast (totient 1053) 100 = v3_phi_list.getD 1053 0 := by
  rw [tot_1053]
  rfl

theorem tot_1054 : totient 1054 = 480 := by
  have heq : (2 * (17 * (31)) : ℕ) = 1054 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_31]
  try omega

theorem v3_phi_1054 : v3_fast (totient 1054) 100 = v3_phi_list.getD 1054 0 := by
  rw [tot_1054]
  rfl

theorem tot_1055 : totient 1055 = 840 := by
  have heq : (5 * (211) : ℕ) = 1055 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_211 : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_211]
  try omega

theorem v3_phi_1055 : v3_fast (totient 1055) 100 = v3_phi_list.getD 1055 0 := by
  rw [tot_1055]
  rfl

theorem tot_1056 : totient 1056 = 320 := by
  have heq : (2^5 * (3 * (11)) : ℕ) = 1056 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11]
  try omega

theorem v3_phi_1056 : v3_fast (totient 1056) 100 = v3_phi_list.getD 1056 0 := by
  rw [tot_1056]
  rfl

theorem tot_1057 : totient 1057 = 900 := by
  have heq : (7 * (151) : ℕ) = 1057 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_151]
  try omega

theorem v3_phi_1057 : v3_fast (totient 1057) 100 = v3_phi_list.getD 1057 0 := by
  rw [tot_1057]
  rfl

theorem tot_1058 : totient 1058 = 506 := by
  have heq : (2 * (23^2) : ℕ) = 1058 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_23 : totient (23^2) = 23^1 * (23 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_23]
  try omega

theorem v3_phi_1058 : v3_fast (totient 1058) 100 = v3_phi_list.getD 1058 0 := by
  rw [tot_1058]
  rfl

theorem tot_1059 : totient 1059 = 704 := by
  have heq : (3 * (353) : ℕ) = 1059 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_353 : totient 353 = 353 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_353]
  try omega

theorem v3_phi_1059 : v3_fast (totient 1059) 100 = v3_phi_list.getD 1059 0 := by
  rw [tot_1059]
  rfl

theorem tot_1060 : totient 1060 = 416 := by
  have heq : (2^2 * (5 * (53)) : ℕ) = 1060 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_53]
  try omega

theorem v3_phi_1060 : v3_fast (totient 1060) 100 = v3_phi_list.getD 1060 0 := by
  rw [tot_1060]
  rfl

theorem tot_1061 : totient 1061 = 1060 := by
  have h : totient 1061 = 1061 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1061 : v3_fast (totient 1061) 100 = v3_phi_list.getD 1061 0 := by
  rw [tot_1061]
  rfl

theorem tot_1062 : totient 1062 = 348 := by
  have heq : (2 * (3^2 * (59)) : ℕ) = 1062 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_59]
  try omega

theorem v3_phi_1062 : v3_fast (totient 1062) 100 = v3_phi_list.getD 1062 0 := by
  rw [tot_1062]
  rfl

theorem tot_1063 : totient 1063 = 1062 := by
  have h : totient 1063 = 1063 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1063 : v3_fast (totient 1063) 100 = v3_phi_list.getD 1063 0 := by
  rw [tot_1063]
  rfl

theorem tot_1064 : totient 1064 = 432 := by
  have heq : (2^3 * (7 * (19)) : ℕ) = 1064 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_19]
  try omega

theorem v3_phi_1064 : v3_fast (totient 1064) 100 = v3_phi_list.getD 1064 0 := by
  rw [tot_1064]
  rfl

theorem tot_1065 : totient 1065 = 560 := by
  have heq : (3 * (5 * (71)) : ℕ) = 1065 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_71]
  try omega

theorem v3_phi_1065 : v3_fast (totient 1065) 100 = v3_phi_list.getD 1065 0 := by
  rw [tot_1065]
  rfl

theorem tot_1066 : totient 1066 = 480 := by
  have heq : (2 * (13 * (41)) : ℕ) = 1066 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_41]
  try omega

theorem v3_phi_1066 : v3_fast (totient 1066) 100 = v3_phi_list.getD 1066 0 := by
  rw [tot_1066]
  rfl

theorem tot_1067 : totient 1067 = 960 := by
  have heq : (11 * (97) : ℕ) = 1067 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_97]
  try omega

theorem v3_phi_1067 : v3_fast (totient 1067) 100 = v3_phi_list.getD 1067 0 := by
  rw [tot_1067]
  rfl

theorem tot_1068 : totient 1068 = 352 := by
  have heq : (2^2 * (3 * (89)) : ℕ) = 1068 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_89]
  try omega

theorem v3_phi_1068 : v3_fast (totient 1068) 100 = v3_phi_list.getD 1068 0 := by
  rw [tot_1068]
  rfl

theorem tot_1069 : totient 1069 = 1068 := by
  have h : totient 1069 = 1069 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1069 : v3_fast (totient 1069) 100 = v3_phi_list.getD 1069 0 := by
  rw [tot_1069]
  rfl

theorem tot_1070 : totient 1070 = 424 := by
  have heq : (2 * (5 * (107)) : ℕ) = 1070 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_107]
  try omega

theorem v3_phi_1070 : v3_fast (totient 1070) 100 = v3_phi_list.getD 1070 0 := by
  rw [tot_1070]
  rfl

theorem tot_1071 : totient 1071 = 576 := by
  have heq : (3^2 * (7 * (17)) : ℕ) = 1071 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_17]
  try omega

theorem v3_phi_1071 : v3_fast (totient 1071) 100 = v3_phi_list.getD 1071 0 := by
  rw [tot_1071]
  rfl

theorem tot_1072 : totient 1072 = 528 := by
  have heq : (2^4 * (67) : ℕ) = 1072 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_67]
  try omega

theorem v3_phi_1072 : v3_fast (totient 1072) 100 = v3_phi_list.getD 1072 0 := by
  rw [tot_1072]
  rfl

theorem tot_1073 : totient 1073 = 1008 := by
  have heq : (29 * (37) : ℕ) = 1073 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_37]
  try omega

theorem v3_phi_1073 : v3_fast (totient 1073) 100 = v3_phi_list.getD 1073 0 := by
  rw [tot_1073]
  rfl

theorem tot_1074 : totient 1074 = 356 := by
  have heq : (2 * (3 * (179)) : ℕ) = 1074 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_179]
  try omega

theorem v3_phi_1074 : v3_fast (totient 1074) 100 = v3_phi_list.getD 1074 0 := by
  rw [tot_1074]
  rfl

theorem tot_1075 : totient 1075 = 840 := by
  have heq : (5^2 * (43) : ℕ) = 1075 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_43]
  try omega

theorem v3_phi_1075 : v3_fast (totient 1075) 100 = v3_phi_list.getD 1075 0 := by
  rw [tot_1075]
  rfl

theorem tot_1076 : totient 1076 = 536 := by
  have heq : (2^2 * (269) : ℕ) = 1076 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_269 : totient 269 = 269 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_269]
  try omega

theorem v3_phi_1076 : v3_fast (totient 1076) 100 = v3_phi_list.getD 1076 0 := by
  rw [tot_1076]
  rfl

theorem tot_1077 : totient 1077 = 716 := by
  have heq : (3 * (359) : ℕ) = 1077 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_359 : totient 359 = 359 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_359]
  try omega

theorem v3_phi_1077 : v3_fast (totient 1077) 100 = v3_phi_list.getD 1077 0 := by
  rw [tot_1077]
  rfl

theorem tot_1078 : totient 1078 = 420 := by
  have heq : (2 * (7^2 * (11)) : ℕ) = 1078 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_11]
  try omega

theorem v3_phi_1078 : v3_fast (totient 1078) 100 = v3_phi_list.getD 1078 0 := by
  rw [tot_1078]
  rfl

theorem tot_1079 : totient 1079 = 984 := by
  have heq : (13 * (83) : ℕ) = 1079 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_83]
  try omega

theorem v3_phi_1079 : v3_fast (totient 1079) 100 = v3_phi_list.getD 1079 0 := by
  rw [tot_1079]
  rfl

theorem tot_1080 : totient 1080 = 288 := by
  have heq : (2^3 * (3^3 * (5)) : ℕ) = 1080 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_1080 : v3_fast (totient 1080) 100 = v3_phi_list.getD 1080 0 := by
  rw [tot_1080]
  rfl

theorem tot_1081 : totient 1081 = 1012 := by
  have heq : (23 * (47) : ℕ) = 1081 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_47]
  try omega

theorem v3_phi_1081 : v3_fast (totient 1081) 100 = v3_phi_list.getD 1081 0 := by
  rw [tot_1081]
  rfl

theorem tot_1082 : totient 1082 = 540 := by
  have heq : (2 * (541) : ℕ) = 1082 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_541 : totient 541 = 541 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_541]
  try omega

theorem v3_phi_1082 : v3_fast (totient 1082) 100 = v3_phi_list.getD 1082 0 := by
  rw [tot_1082]
  rfl

theorem tot_1083 : totient 1083 = 684 := by
  have heq : (3 * (19^2) : ℕ) = 1083 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient (19^2) = 19^1 * (19 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_19]
  try omega

theorem v3_phi_1083 : v3_fast (totient 1083) 100 = v3_phi_list.getD 1083 0 := by
  rw [tot_1083]
  rfl

theorem tot_1084 : totient 1084 = 540 := by
  have heq : (2^2 * (271) : ℕ) = 1084 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_271 : totient 271 = 271 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_271]
  try omega

theorem v3_phi_1084 : v3_fast (totient 1084) 100 = v3_phi_list.getD 1084 0 := by
  rw [tot_1084]
  rfl

theorem tot_1085 : totient 1085 = 720 := by
  have heq : (5 * (7 * (31)) : ℕ) = 1085 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_31]
  try omega

theorem v3_phi_1085 : v3_fast (totient 1085) 100 = v3_phi_list.getD 1085 0 := by
  rw [tot_1085]
  rfl

theorem tot_1086 : totient 1086 = 360 := by
  have heq : (2 * (3 * (181)) : ℕ) = 1086 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_181]
  try omega

theorem v3_phi_1086 : v3_fast (totient 1086) 100 = v3_phi_list.getD 1086 0 := by
  rw [tot_1086]
  rfl

theorem tot_1087 : totient 1087 = 1086 := by
  have h : totient 1087 = 1087 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1087 : v3_fast (totient 1087) 100 = v3_phi_list.getD 1087 0 := by
  rw [tot_1087]
  rfl

theorem tot_1088 : totient 1088 = 512 := by
  have heq : (2^6 * (17) : ℕ) = 1088 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17]
  try omega

theorem v3_phi_1088 : v3_fast (totient 1088) 100 = v3_phi_list.getD 1088 0 := by
  rw [tot_1088]
  rfl

theorem tot_1089 : totient 1089 = 660 := by
  have heq : (3^2 * (11^2) : ℕ) = 1089 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_11]
  try omega

theorem v3_phi_1089 : v3_fast (totient 1089) 100 = v3_phi_list.getD 1089 0 := by
  rw [tot_1089]
  rfl

theorem tot_1090 : totient 1090 = 432 := by
  have heq : (2 * (5 * (109)) : ℕ) = 1090 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_109]
  try omega

theorem v3_phi_1090 : v3_fast (totient 1090) 100 = v3_phi_list.getD 1090 0 := by
  rw [tot_1090]
  rfl

theorem tot_1091 : totient 1091 = 1090 := by
  have h : totient 1091 = 1091 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1091 : v3_fast (totient 1091) 100 = v3_phi_list.getD 1091 0 := by
  rw [tot_1091]
  rfl

theorem tot_1092 : totient 1092 = 288 := by
  have heq : (2^2 * (3 * (7 * (13))) : ℕ) = 1092 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_13]
  try omega

theorem v3_phi_1092 : v3_fast (totient 1092) 100 = v3_phi_list.getD 1092 0 := by
  rw [tot_1092]
  rfl

theorem tot_1093 : totient 1093 = 1092 := by
  have h : totient 1093 = 1093 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1093 : v3_fast (totient 1093) 100 = v3_phi_list.getD 1093 0 := by
  rw [tot_1093]
  rfl

theorem tot_1094 : totient 1094 = 546 := by
  have heq : (2 * (547) : ℕ) = 1094 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_547 : totient 547 = 547 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_547]
  try omega

theorem v3_phi_1094 : v3_fast (totient 1094) 100 = v3_phi_list.getD 1094 0 := by
  rw [tot_1094]
  rfl

theorem tot_1095 : totient 1095 = 576 := by
  have heq : (3 * (5 * (73)) : ℕ) = 1095 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_73]
  try omega

theorem v3_phi_1095 : v3_fast (totient 1095) 100 = v3_phi_list.getD 1095 0 := by
  rw [tot_1095]
  rfl

theorem tot_1096 : totient 1096 = 544 := by
  have heq : (2^3 * (137) : ℕ) = 1096 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_137]
  try omega

theorem v3_phi_1096 : v3_fast (totient 1096) 100 = v3_phi_list.getD 1096 0 := by
  rw [tot_1096]
  rfl

theorem tot_1097 : totient 1097 = 1096 := by
  have h : totient 1097 = 1097 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1097 : v3_fast (totient 1097) 100 = v3_phi_list.getD 1097 0 := by
  rw [tot_1097]
  rfl

theorem tot_1098 : totient 1098 = 360 := by
  have heq : (2 * (3^2 * (61)) : ℕ) = 1098 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_61]
  try omega

theorem v3_phi_1098 : v3_fast (totient 1098) 100 = v3_phi_list.getD 1098 0 := by
  rw [tot_1098]
  rfl

theorem tot_1099 : totient 1099 = 936 := by
  have heq : (7 * (157) : ℕ) = 1099 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_157]
  try omega

theorem v3_phi_1099 : v3_fast (totient 1099) 100 = v3_phi_list.getD 1099 0 := by
  rw [tot_1099]
  rfl

theorem tot_1100 : totient 1100 = 400 := by
  have heq : (2^2 * (5^2 * (11)) : ℕ) = 1100 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_11]
  try omega

theorem v3_phi_1100 : v3_fast (totient 1100) 100 = v3_phi_list.getD 1100 0 := by
  rw [tot_1100]
  rfl

theorem tot_1101 : totient 1101 = 732 := by
  have heq : (3 * (367) : ℕ) = 1101 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_367 : totient 367 = 367 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_367]
  try omega

theorem v3_phi_1101 : v3_fast (totient 1101) 100 = v3_phi_list.getD 1101 0 := by
  rw [tot_1101]
  rfl

theorem tot_1102 : totient 1102 = 504 := by
  have heq : (2 * (19 * (29)) : ℕ) = 1102 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_29]
  try omega

theorem v3_phi_1102 : v3_fast (totient 1102) 100 = v3_phi_list.getD 1102 0 := by
  rw [tot_1102]
  rfl

theorem tot_1103 : totient 1103 = 1102 := by
  have h : totient 1103 = 1103 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1103 : v3_fast (totient 1103) 100 = v3_phi_list.getD 1103 0 := by
  rw [tot_1103]
  rfl

theorem tot_1104 : totient 1104 = 352 := by
  have heq : (2^4 * (3 * (23)) : ℕ) = 1104 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23]
  try omega

theorem v3_phi_1104 : v3_fast (totient 1104) 100 = v3_phi_list.getD 1104 0 := by
  rw [tot_1104]
  rfl

theorem tot_1105 : totient 1105 = 768 := by
  have heq : (5 * (13 * (17)) : ℕ) = 1105 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_13, hp_17]
  try omega

theorem v3_phi_1105 : v3_fast (totient 1105) 100 = v3_phi_list.getD 1105 0 := by
  rw [tot_1105]
  rfl

theorem tot_1106 : totient 1106 = 468 := by
  have heq : (2 * (7 * (79)) : ℕ) = 1106 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_79]
  try omega

theorem v3_phi_1106 : v3_fast (totient 1106) 100 = v3_phi_list.getD 1106 0 := by
  rw [tot_1106]
  rfl

theorem tot_1107 : totient 1107 = 720 := by
  have heq : (3^3 * (41) : ℕ) = 1107 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_41]
  try omega

theorem v3_phi_1107 : v3_fast (totient 1107) 100 = v3_phi_list.getD 1107 0 := by
  rw [tot_1107]
  rfl

theorem tot_1108 : totient 1108 = 552 := by
  have heq : (2^2 * (277) : ℕ) = 1108 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_277 : totient 277 = 277 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_277]
  try omega

theorem v3_phi_1108 : v3_fast (totient 1108) 100 = v3_phi_list.getD 1108 0 := by
  rw [tot_1108]
  rfl

theorem tot_1109 : totient 1109 = 1108 := by
  have h : totient 1109 = 1109 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1109 : v3_fast (totient 1109) 100 = v3_phi_list.getD 1109 0 := by
  rw [tot_1109]
  rfl

theorem tot_1110 : totient 1110 = 288 := by
  have heq : (2 * (3 * (5 * (37))) : ℕ) = 1110 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_37]
  try omega

theorem v3_phi_1110 : v3_fast (totient 1110) 100 = v3_phi_list.getD 1110 0 := by
  rw [tot_1110]
  rfl

theorem tot_1111 : totient 1111 = 1000 := by
  have heq : (11 * (101) : ℕ) = 1111 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_101]
  try omega

theorem v3_phi_1111 : v3_fast (totient 1111) 100 = v3_phi_list.getD 1111 0 := by
  rw [tot_1111]
  rfl

theorem tot_1112 : totient 1112 = 552 := by
  have heq : (2^3 * (139) : ℕ) = 1112 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_139]
  try omega

theorem v3_phi_1112 : v3_fast (totient 1112) 100 = v3_phi_list.getD 1112 0 := by
  rw [tot_1112]
  rfl

theorem tot_1113 : totient 1113 = 624 := by
  have heq : (3 * (7 * (53)) : ℕ) = 1113 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_53]
  try omega

theorem v3_phi_1113 : v3_fast (totient 1113) 100 = v3_phi_list.getD 1113 0 := by
  rw [tot_1113]
  rfl

theorem tot_1114 : totient 1114 = 556 := by
  have heq : (2 * (557) : ℕ) = 1114 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_557 : totient 557 = 557 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_557]
  try omega

theorem v3_phi_1114 : v3_fast (totient 1114) 100 = v3_phi_list.getD 1114 0 := by
  rw [tot_1114]
  rfl

theorem tot_1115 : totient 1115 = 888 := by
  have heq : (5 * (223) : ℕ) = 1115 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_223 : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_223]
  try omega

theorem v3_phi_1115 : v3_fast (totient 1115) 100 = v3_phi_list.getD 1115 0 := by
  rw [tot_1115]
  rfl

theorem tot_1116 : totient 1116 = 360 := by
  have heq : (2^2 * (3^2 * (31)) : ℕ) = 1116 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_31]
  try omega

theorem v3_phi_1116 : v3_fast (totient 1116) 100 = v3_phi_list.getD 1116 0 := by
  rw [tot_1116]
  rfl

theorem tot_1117 : totient 1117 = 1116 := by
  have h : totient 1117 = 1117 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1117 : v3_fast (totient 1117) 100 = v3_phi_list.getD 1117 0 := by
  rw [tot_1117]
  rfl

theorem tot_1118 : totient 1118 = 504 := by
  have heq : (2 * (13 * (43)) : ℕ) = 1118 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_43]
  try omega

theorem v3_phi_1118 : v3_fast (totient 1118) 100 = v3_phi_list.getD 1118 0 := by
  rw [tot_1118]
  rfl

theorem tot_1119 : totient 1119 = 744 := by
  have heq : (3 * (373) : ℕ) = 1119 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_373 : totient 373 = 373 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_373]
  try omega

theorem v3_phi_1119 : v3_fast (totient 1119) 100 = v3_phi_list.getD 1119 0 := by
  rw [tot_1119]
  rfl

theorem tot_1120 : totient 1120 = 384 := by
  have heq : (2^5 * (5 * (7)) : ℕ) = 1120 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7]
  try omega

theorem v3_phi_1120 : v3_fast (totient 1120) 100 = v3_phi_list.getD 1120 0 := by
  rw [tot_1120]
  rfl

theorem tot_1121 : totient 1121 = 1044 := by
  have heq : (19 * (59) : ℕ) = 1121 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_59]
  try omega

theorem v3_phi_1121 : v3_fast (totient 1121) 100 = v3_phi_list.getD 1121 0 := by
  rw [tot_1121]
  rfl

theorem tot_1122 : totient 1122 = 320 := by
  have heq : (2 * (3 * (11 * (17))) : ℕ) = 1122 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11, hp_17]
  try omega

theorem v3_phi_1122 : v3_fast (totient 1122) 100 = v3_phi_list.getD 1122 0 := by
  rw [tot_1122]
  rfl

theorem tot_1123 : totient 1123 = 1122 := by
  have h : totient 1123 = 1123 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1123 : v3_fast (totient 1123) 100 = v3_phi_list.getD 1123 0 := by
  rw [tot_1123]
  rfl

theorem tot_1124 : totient 1124 = 560 := by
  have heq : (2^2 * (281) : ℕ) = 1124 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_281 : totient 281 = 281 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_281]
  try omega

theorem v3_phi_1124 : v3_fast (totient 1124) 100 = v3_phi_list.getD 1124 0 := by
  rw [tot_1124]
  rfl

theorem tot_1125 : totient 1125 = 600 := by
  have heq : (3^2 * (5^3) : ℕ) = 1125 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_5]
  try omega

theorem v3_phi_1125 : v3_fast (totient 1125) 100 = v3_phi_list.getD 1125 0 := by
  rw [tot_1125]
  rfl

theorem tot_1126 : totient 1126 = 562 := by
  have heq : (2 * (563) : ℕ) = 1126 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_563 : totient 563 = 563 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_563]
  try omega

theorem v3_phi_1126 : v3_fast (totient 1126) 100 = v3_phi_list.getD 1126 0 := by
  rw [tot_1126]
  rfl

theorem tot_1127 : totient 1127 = 924 := by
  have heq : (7^2 * (23) : ℕ) = 1127 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_23]
  try omega

theorem v3_phi_1127 : v3_fast (totient 1127) 100 = v3_phi_list.getD 1127 0 := by
  rw [tot_1127]
  rfl

theorem tot_1128 : totient 1128 = 368 := by
  have heq : (2^3 * (3 * (47)) : ℕ) = 1128 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_47]
  try omega

theorem v3_phi_1128 : v3_fast (totient 1128) 100 = v3_phi_list.getD 1128 0 := by
  rw [tot_1128]
  rfl

theorem tot_1129 : totient 1129 = 1128 := by
  have h : totient 1129 = 1129 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1129 : v3_fast (totient 1129) 100 = v3_phi_list.getD 1129 0 := by
  rw [tot_1129]
  rfl

theorem tot_1130 : totient 1130 = 448 := by
  have heq : (2 * (5 * (113)) : ℕ) = 1130 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_113]
  try omega

theorem v3_phi_1130 : v3_fast (totient 1130) 100 = v3_phi_list.getD 1130 0 := by
  rw [tot_1130]
  rfl

theorem tot_1131 : totient 1131 = 672 := by
  have heq : (3 * (13 * (29)) : ℕ) = 1131 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_29]
  try omega

theorem v3_phi_1131 : v3_fast (totient 1131) 100 = v3_phi_list.getD 1131 0 := by
  rw [tot_1131]
  rfl

theorem tot_1132 : totient 1132 = 564 := by
  have heq : (2^2 * (283) : ℕ) = 1132 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_283 : totient 283 = 283 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_283]
  try omega

theorem v3_phi_1132 : v3_fast (totient 1132) 100 = v3_phi_list.getD 1132 0 := by
  rw [tot_1132]
  rfl

theorem tot_1133 : totient 1133 = 1020 := by
  have heq : (11 * (103) : ℕ) = 1133 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_103]
  try omega

theorem v3_phi_1133 : v3_fast (totient 1133) 100 = v3_phi_list.getD 1133 0 := by
  rw [tot_1133]
  rfl

theorem tot_1134 : totient 1134 = 324 := by
  have heq : (2 * (3^4 * (7)) : ℕ) = 1134 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_1134 : v3_fast (totient 1134) 100 = v3_phi_list.getD 1134 0 := by
  rw [tot_1134]
  rfl

theorem tot_1135 : totient 1135 = 904 := by
  have heq : (5 * (227) : ℕ) = 1135 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_227 : totient 227 = 227 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_227]
  try omega

theorem v3_phi_1135 : v3_fast (totient 1135) 100 = v3_phi_list.getD 1135 0 := by
  rw [tot_1135]
  rfl

theorem tot_1136 : totient 1136 = 560 := by
  have heq : (2^4 * (71) : ℕ) = 1136 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_71]
  try omega

theorem v3_phi_1136 : v3_fast (totient 1136) 100 = v3_phi_list.getD 1136 0 := by
  rw [tot_1136]
  rfl

theorem tot_1137 : totient 1137 = 756 := by
  have heq : (3 * (379) : ℕ) = 1137 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_379 : totient 379 = 379 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_379]
  try omega

theorem v3_phi_1137 : v3_fast (totient 1137) 100 = v3_phi_list.getD 1137 0 := by
  rw [tot_1137]
  rfl

theorem tot_1138 : totient 1138 = 568 := by
  have heq : (2 * (569) : ℕ) = 1138 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_569 : totient 569 = 569 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_569]
  try omega

theorem v3_phi_1138 : v3_fast (totient 1138) 100 = v3_phi_list.getD 1138 0 := by
  rw [tot_1138]
  rfl

theorem tot_1139 : totient 1139 = 1056 := by
  have heq : (17 * (67) : ℕ) = 1139 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_67]
  try omega

theorem v3_phi_1139 : v3_fast (totient 1139) 100 = v3_phi_list.getD 1139 0 := by
  rw [tot_1139]
  rfl

theorem tot_1140 : totient 1140 = 288 := by
  have heq : (2^2 * (3 * (5 * (19))) : ℕ) = 1140 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_19]
  try omega

theorem v3_phi_1140 : v3_fast (totient 1140) 100 = v3_phi_list.getD 1140 0 := by
  rw [tot_1140]
  rfl

theorem tot_1141 : totient 1141 = 972 := by
  have heq : (7 * (163) : ℕ) = 1141 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_163]
  try omega

theorem v3_phi_1141 : v3_fast (totient 1141) 100 = v3_phi_list.getD 1141 0 := by
  rw [tot_1141]
  rfl

theorem tot_1142 : totient 1142 = 570 := by
  have heq : (2 * (571) : ℕ) = 1142 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_571 : totient 571 = 571 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_571]
  try omega

theorem v3_phi_1142 : v3_fast (totient 1142) 100 = v3_phi_list.getD 1142 0 := by
  rw [tot_1142]
  rfl

theorem tot_1143 : totient 1143 = 756 := by
  have heq : (3^2 * (127) : ℕ) = 1143 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_127]
  try omega

theorem v3_phi_1143 : v3_fast (totient 1143) 100 = v3_phi_list.getD 1143 0 := by
  rw [tot_1143]
  rfl

theorem tot_1144 : totient 1144 = 480 := by
  have heq : (2^3 * (11 * (13)) : ℕ) = 1144 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_13]
  try omega

theorem v3_phi_1144 : v3_fast (totient 1144) 100 = v3_phi_list.getD 1144 0 := by
  rw [tot_1144]
  rfl

theorem tot_1145 : totient 1145 = 912 := by
  have heq : (5 * (229) : ℕ) = 1145 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_229 : totient 229 = 229 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_229]
  try omega

theorem v3_phi_1145 : v3_fast (totient 1145) 100 = v3_phi_list.getD 1145 0 := by
  rw [tot_1145]
  rfl

theorem tot_1146 : totient 1146 = 380 := by
  have heq : (2 * (3 * (191)) : ℕ) = 1146 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_191]
  try omega

theorem v3_phi_1146 : v3_fast (totient 1146) 100 = v3_phi_list.getD 1146 0 := by
  rw [tot_1146]
  rfl

theorem tot_1147 : totient 1147 = 1080 := by
  have heq : (31 * (37) : ℕ) = 1147 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_31, hp_37]
  try omega

theorem v3_phi_1147 : v3_fast (totient 1147) 100 = v3_phi_list.getD 1147 0 := by
  rw [tot_1147]
  rfl

theorem tot_1148 : totient 1148 = 480 := by
  have heq : (2^2 * (7 * (41)) : ℕ) = 1148 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_41]
  try omega

theorem v3_phi_1148 : v3_fast (totient 1148) 100 = v3_phi_list.getD 1148 0 := by
  rw [tot_1148]
  rfl

theorem tot_1149 : totient 1149 = 764 := by
  have heq : (3 * (383) : ℕ) = 1149 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_383 : totient 383 = 383 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_383]
  try omega

theorem v3_phi_1149 : v3_fast (totient 1149) 100 = v3_phi_list.getD 1149 0 := by
  rw [tot_1149]
  rfl

theorem tot_1150 : totient 1150 = 440 := by
  have heq : (2 * (5^2 * (23)) : ℕ) = 1150 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_23]
  try omega

theorem v3_phi_1150 : v3_fast (totient 1150) 100 = v3_phi_list.getD 1150 0 := by
  rw [tot_1150]
  rfl

theorem tot_1151 : totient 1151 = 1150 := by
  have h : totient 1151 = 1151 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1151 : v3_fast (totient 1151) 100 = v3_phi_list.getD 1151 0 := by
  rw [tot_1151]
  rfl

theorem tot_1152 : totient 1152 = 384 := by
  have heq : (2^7 * (3^2) : ℕ) = 1152 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^7) = 2^6 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_1152 : v3_fast (totient 1152) 100 = v3_phi_list.getD 1152 0 := by
  rw [tot_1152]
  rfl

theorem tot_1153 : totient 1153 = 1152 := by
  have h : totient 1153 = 1153 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1153 : v3_fast (totient 1153) 100 = v3_phi_list.getD 1153 0 := by
  rw [tot_1153]
  rfl

theorem tot_1154 : totient 1154 = 576 := by
  have heq : (2 * (577) : ℕ) = 1154 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_577 : totient 577 = 577 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_577]
  try omega

theorem v3_phi_1154 : v3_fast (totient 1154) 100 = v3_phi_list.getD 1154 0 := by
  rw [tot_1154]
  rfl

theorem tot_1155 : totient 1155 = 480 := by
  have heq : (3 * (5 * (7 * (11))) : ℕ) = 1155 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7, hp_11]
  try omega

theorem v3_phi_1155 : v3_fast (totient 1155) 100 = v3_phi_list.getD 1155 0 := by
  rw [tot_1155]
  rfl

theorem tot_1156 : totient 1156 = 544 := by
  have heq : (2^2 * (17^2) : ℕ) = 1156 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient (17^2) = 17^1 * (17 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_17]
  try omega

theorem v3_phi_1156 : v3_fast (totient 1156) 100 = v3_phi_list.getD 1156 0 := by
  rw [tot_1156]
  rfl

theorem tot_1157 : totient 1157 = 1056 := by
  have heq : (13 * (89) : ℕ) = 1157 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_89]
  try omega

theorem v3_phi_1157 : v3_fast (totient 1157) 100 = v3_phi_list.getD 1157 0 := by
  rw [tot_1157]
  rfl

theorem tot_1158 : totient 1158 = 384 := by
  have heq : (2 * (3 * (193)) : ℕ) = 1158 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_193]
  try omega

theorem v3_phi_1158 : v3_fast (totient 1158) 100 = v3_phi_list.getD 1158 0 := by
  rw [tot_1158]
  rfl

theorem tot_1159 : totient 1159 = 1080 := by
  have heq : (19 * (61) : ℕ) = 1159 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_61]
  try omega

theorem v3_phi_1159 : v3_fast (totient 1159) 100 = v3_phi_list.getD 1159 0 := by
  rw [tot_1159]
  rfl

theorem tot_1160 : totient 1160 = 448 := by
  have heq : (2^3 * (5 * (29)) : ℕ) = 1160 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_29]
  try omega

theorem v3_phi_1160 : v3_fast (totient 1160) 100 = v3_phi_list.getD 1160 0 := by
  rw [tot_1160]
  rfl

theorem tot_1161 : totient 1161 = 756 := by
  have heq : (3^3 * (43) : ℕ) = 1161 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_43]
  try omega

theorem v3_phi_1161 : v3_fast (totient 1161) 100 = v3_phi_list.getD 1161 0 := by
  rw [tot_1161]
  rfl

theorem tot_1162 : totient 1162 = 492 := by
  have heq : (2 * (7 * (83)) : ℕ) = 1162 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_83]
  try omega

theorem v3_phi_1162 : v3_fast (totient 1162) 100 = v3_phi_list.getD 1162 0 := by
  rw [tot_1162]
  rfl

theorem tot_1163 : totient 1163 = 1162 := by
  have h : totient 1163 = 1163 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1163 : v3_fast (totient 1163) 100 = v3_phi_list.getD 1163 0 := by
  rw [tot_1163]
  rfl

theorem tot_1164 : totient 1164 = 384 := by
  have heq : (2^2 * (3 * (97)) : ℕ) = 1164 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_97]
  try omega

theorem v3_phi_1164 : v3_fast (totient 1164) 100 = v3_phi_list.getD 1164 0 := by
  rw [tot_1164]
  rfl

theorem tot_1165 : totient 1165 = 928 := by
  have heq : (5 * (233) : ℕ) = 1165 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_233 : totient 233 = 233 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_233]
  try omega

theorem v3_phi_1165 : v3_fast (totient 1165) 100 = v3_phi_list.getD 1165 0 := by
  rw [tot_1165]
  rfl

theorem tot_1166 : totient 1166 = 520 := by
  have heq : (2 * (11 * (53)) : ℕ) = 1166 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_53]
  try omega

theorem v3_phi_1166 : v3_fast (totient 1166) 100 = v3_phi_list.getD 1166 0 := by
  rw [tot_1166]
  rfl

theorem tot_1167 : totient 1167 = 776 := by
  have heq : (3 * (389) : ℕ) = 1167 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_389 : totient 389 = 389 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_389]
  try omega

theorem v3_phi_1167 : v3_fast (totient 1167) 100 = v3_phi_list.getD 1167 0 := by
  rw [tot_1167]
  rfl

theorem tot_1168 : totient 1168 = 576 := by
  have heq : (2^4 * (73) : ℕ) = 1168 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_73]
  try omega

theorem v3_phi_1168 : v3_fast (totient 1168) 100 = v3_phi_list.getD 1168 0 := by
  rw [tot_1168]
  rfl

theorem tot_1169 : totient 1169 = 996 := by
  have heq : (7 * (167) : ℕ) = 1169 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_167]
  try omega

theorem v3_phi_1169 : v3_fast (totient 1169) 100 = v3_phi_list.getD 1169 0 := by
  rw [tot_1169]
  rfl

theorem tot_1170 : totient 1170 = 288 := by
  have heq : (2 * (3^2 * (5 * (13))) : ℕ) = 1170 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_13]
  try omega

theorem v3_phi_1170 : v3_fast (totient 1170) 100 = v3_phi_list.getD 1170 0 := by
  rw [tot_1170]
  rfl

theorem tot_1171 : totient 1171 = 1170 := by
  have h : totient 1171 = 1171 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1171 : v3_fast (totient 1171) 100 = v3_phi_list.getD 1171 0 := by
  rw [tot_1171]
  rfl

theorem tot_1172 : totient 1172 = 584 := by
  have heq : (2^2 * (293) : ℕ) = 1172 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_293 : totient 293 = 293 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_293]
  try omega

theorem v3_phi_1172 : v3_fast (totient 1172) 100 = v3_phi_list.getD 1172 0 := by
  rw [tot_1172]
  rfl

theorem tot_1173 : totient 1173 = 704 := by
  have heq : (3 * (17 * (23)) : ℕ) = 1173 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17, hp_23]
  try omega

theorem v3_phi_1173 : v3_fast (totient 1173) 100 = v3_phi_list.getD 1173 0 := by
  rw [tot_1173]
  rfl

theorem tot_1174 : totient 1174 = 586 := by
  have heq : (2 * (587) : ℕ) = 1174 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_587 : totient 587 = 587 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_587]
  try omega

theorem v3_phi_1174 : v3_fast (totient 1174) 100 = v3_phi_list.getD 1174 0 := by
  rw [tot_1174]
  rfl

theorem tot_1175 : totient 1175 = 920 := by
  have heq : (5^2 * (47) : ℕ) = 1175 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_47]
  try omega

theorem v3_phi_1175 : v3_fast (totient 1175) 100 = v3_phi_list.getD 1175 0 := by
  rw [tot_1175]
  rfl

theorem tot_1176 : totient 1176 = 336 := by
  have heq : (2^3 * (3 * (7^2)) : ℕ) = 1176 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_1176 : v3_fast (totient 1176) 100 = v3_phi_list.getD 1176 0 := by
  rw [tot_1176]
  rfl

theorem tot_1177 : totient 1177 = 1060 := by
  have heq : (11 * (107) : ℕ) = 1177 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_107]
  try omega

theorem v3_phi_1177 : v3_fast (totient 1177) 100 = v3_phi_list.getD 1177 0 := by
  rw [tot_1177]
  rfl

theorem tot_1178 : totient 1178 = 540 := by
  have heq : (2 * (19 * (31)) : ℕ) = 1178 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19, hp_31]
  try omega

theorem v3_phi_1178 : v3_fast (totient 1178) 100 = v3_phi_list.getD 1178 0 := by
  rw [tot_1178]
  rfl

theorem tot_1179 : totient 1179 = 780 := by
  have heq : (3^2 * (131) : ℕ) = 1179 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_131]
  try omega

theorem v3_phi_1179 : v3_fast (totient 1179) 100 = v3_phi_list.getD 1179 0 := by
  rw [tot_1179]
  rfl

theorem tot_1180 : totient 1180 = 464 := by
  have heq : (2^2 * (5 * (59)) : ℕ) = 1180 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_59]
  try omega

theorem v3_phi_1180 : v3_fast (totient 1180) 100 = v3_phi_list.getD 1180 0 := by
  rw [tot_1180]
  rfl

theorem tot_1181 : totient 1181 = 1180 := by
  have h : totient 1181 = 1181 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1181 : v3_fast (totient 1181) 100 = v3_phi_list.getD 1181 0 := by
  rw [tot_1181]
  rfl

theorem tot_1182 : totient 1182 = 392 := by
  have heq : (2 * (3 * (197)) : ℕ) = 1182 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_197]
  try omega

theorem v3_phi_1182 : v3_fast (totient 1182) 100 = v3_phi_list.getD 1182 0 := by
  rw [tot_1182]
  rfl

theorem tot_1183 : totient 1183 = 936 := by
  have heq : (7 * (13^2) : ℕ) = 1183 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_7, hp_13]
  try omega

theorem v3_phi_1183 : v3_fast (totient 1183) 100 = v3_phi_list.getD 1183 0 := by
  rw [tot_1183]
  rfl

theorem tot_1184 : totient 1184 = 576 := by
  have heq : (2^5 * (37) : ℕ) = 1184 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_37]
  try omega

theorem v3_phi_1184 : v3_fast (totient 1184) 100 = v3_phi_list.getD 1184 0 := by
  rw [tot_1184]
  rfl

theorem tot_1185 : totient 1185 = 624 := by
  have heq : (3 * (5 * (79)) : ℕ) = 1185 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_79]
  try omega

theorem v3_phi_1185 : v3_fast (totient 1185) 100 = v3_phi_list.getD 1185 0 := by
  rw [tot_1185]
  rfl

theorem tot_1186 : totient 1186 = 592 := by
  have heq : (2 * (593) : ℕ) = 1186 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_593 : totient 593 = 593 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_593]
  try omega

theorem v3_phi_1186 : v3_fast (totient 1186) 100 = v3_phi_list.getD 1186 0 := by
  rw [tot_1186]
  rfl

theorem tot_1187 : totient 1187 = 1186 := by
  have h : totient 1187 = 1187 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1187 : v3_fast (totient 1187) 100 = v3_phi_list.getD 1187 0 := by
  rw [tot_1187]
  rfl

theorem tot_1188 : totient 1188 = 360 := by
  have heq : (2^2 * (3^3 * (11)) : ℕ) = 1188 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11]
  try omega

theorem v3_phi_1188 : v3_fast (totient 1188) 100 = v3_phi_list.getD 1188 0 := by
  rw [tot_1188]
  rfl

theorem tot_1189 : totient 1189 = 1120 := by
  have heq : (29 * (41) : ℕ) = 1189 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_41]
  try omega

theorem v3_phi_1189 : v3_fast (totient 1189) 100 = v3_phi_list.getD 1189 0 := by
  rw [tot_1189]
  rfl

theorem tot_1190 : totient 1190 = 384 := by
  have heq : (2 * (5 * (7 * (17))) : ℕ) = 1190 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7, hp_17]
  try omega

theorem v3_phi_1190 : v3_fast (totient 1190) 100 = v3_phi_list.getD 1190 0 := by
  rw [tot_1190]
  rfl

theorem tot_1191 : totient 1191 = 792 := by
  have heq : (3 * (397) : ℕ) = 1191 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_397 : totient 397 = 397 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_397]
  try omega

theorem v3_phi_1191 : v3_fast (totient 1191) 100 = v3_phi_list.getD 1191 0 := by
  rw [tot_1191]
  rfl

theorem tot_1192 : totient 1192 = 592 := by
  have heq : (2^3 * (149) : ℕ) = 1192 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_149]
  try omega

theorem v3_phi_1192 : v3_fast (totient 1192) 100 = v3_phi_list.getD 1192 0 := by
  rw [tot_1192]
  rfl

theorem tot_1193 : totient 1193 = 1192 := by
  have h : totient 1193 = 1193 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1193 : v3_fast (totient 1193) 100 = v3_phi_list.getD 1193 0 := by
  rw [tot_1193]
  rfl

theorem tot_1194 : totient 1194 = 396 := by
  have heq : (2 * (3 * (199)) : ℕ) = 1194 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_199 : totient 199 = 199 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_199]
  try omega

theorem v3_phi_1194 : v3_fast (totient 1194) 100 = v3_phi_list.getD 1194 0 := by
  rw [tot_1194]
  rfl

theorem tot_1195 : totient 1195 = 952 := by
  have heq : (5 * (239) : ℕ) = 1195 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_239 : totient 239 = 239 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_239]
  try omega

theorem v3_phi_1195 : v3_fast (totient 1195) 100 = v3_phi_list.getD 1195 0 := by
  rw [tot_1195]
  rfl

theorem tot_1196 : totient 1196 = 528 := by
  have heq : (2^2 * (13 * (23)) : ℕ) = 1196 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_23]
  try omega

theorem v3_phi_1196 : v3_fast (totient 1196) 100 = v3_phi_list.getD 1196 0 := by
  rw [tot_1196]
  rfl

theorem tot_1197 : totient 1197 = 648 := by
  have heq : (3^2 * (7 * (19)) : ℕ) = 1197 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_19]
  try omega

theorem v3_phi_1197 : v3_fast (totient 1197) 100 = v3_phi_list.getD 1197 0 := by
  rw [tot_1197]
  rfl

theorem tot_1198 : totient 1198 = 598 := by
  have heq : (2 * (599) : ℕ) = 1198 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_599 : totient 599 = 599 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_599]
  try omega

theorem v3_phi_1198 : v3_fast (totient 1198) 100 = v3_phi_list.getD 1198 0 := by
  rw [tot_1198]
  rfl

theorem tot_1199 : totient 1199 = 1080 := by
  have heq : (11 * (109) : ℕ) = 1199 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_109]
  try omega

theorem v3_phi_1199 : v3_fast (totient 1199) 100 = v3_phi_list.getD 1199 0 := by
  rw [tot_1199]
  rfl

theorem tot_1200 : totient 1200 = 320 := by
  have heq : (2^4 * (3 * (5^2)) : ℕ) = 1200 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_1200 : v3_fast (totient 1200) 100 = v3_phi_list.getD 1200 0 := by
  rw [tot_1200]
  rfl

theorem tot_1201 : totient 1201 = 1200 := by
  have h : totient 1201 = 1201 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1201 : v3_fast (totient 1201) 100 = v3_phi_list.getD 1201 0 := by
  rw [tot_1201]
  rfl

theorem tot_1202 : totient 1202 = 600 := by
  have heq : (2 * (601) : ℕ) = 1202 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_601 : totient 601 = 601 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_601]
  try omega

theorem v3_phi_1202 : v3_fast (totient 1202) 100 = v3_phi_list.getD 1202 0 := by
  rw [tot_1202]
  rfl

theorem tot_1203 : totient 1203 = 800 := by
  have heq : (3 * (401) : ℕ) = 1203 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_401 : totient 401 = 401 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_401]
  try omega

theorem v3_phi_1203 : v3_fast (totient 1203) 100 = v3_phi_list.getD 1203 0 := by
  rw [tot_1203]
  rfl

theorem tot_1204 : totient 1204 = 504 := by
  have heq : (2^2 * (7 * (43)) : ℕ) = 1204 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_43]
  try omega

theorem v3_phi_1204 : v3_fast (totient 1204) 100 = v3_phi_list.getD 1204 0 := by
  rw [tot_1204]
  rfl

theorem tot_1205 : totient 1205 = 960 := by
  have heq : (5 * (241) : ℕ) = 1205 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_241 : totient 241 = 241 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_241]
  try omega

theorem v3_phi_1205 : v3_fast (totient 1205) 100 = v3_phi_list.getD 1205 0 := by
  rw [tot_1205]
  rfl

theorem tot_1206 : totient 1206 = 396 := by
  have heq : (2 * (3^2 * (67)) : ℕ) = 1206 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_67]
  try omega

theorem v3_phi_1206 : v3_fast (totient 1206) 100 = v3_phi_list.getD 1206 0 := by
  rw [tot_1206]
  rfl

theorem tot_1207 : totient 1207 = 1120 := by
  have heq : (17 * (71) : ℕ) = 1207 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_71]
  try omega

theorem v3_phi_1207 : v3_fast (totient 1207) 100 = v3_phi_list.getD 1207 0 := by
  rw [tot_1207]
  rfl

theorem tot_1208 : totient 1208 = 600 := by
  have heq : (2^3 * (151) : ℕ) = 1208 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_151]
  try omega

theorem v3_phi_1208 : v3_fast (totient 1208) 100 = v3_phi_list.getD 1208 0 := by
  rw [tot_1208]
  rfl

theorem tot_1209 : totient 1209 = 720 := by
  have heq : (3 * (13 * (31)) : ℕ) = 1209 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_13, hp_31]
  try omega

theorem v3_phi_1209 : v3_fast (totient 1209) 100 = v3_phi_list.getD 1209 0 := by
  rw [tot_1209]
  rfl

theorem tot_1210 : totient 1210 = 440 := by
  have heq : (2 * (5 * (11^2)) : ℕ) = 1210 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient (11^2) = 11^1 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5, hp_11]
  try omega

theorem v3_phi_1210 : v3_fast (totient 1210) 100 = v3_phi_list.getD 1210 0 := by
  rw [tot_1210]
  rfl

theorem tot_1211 : totient 1211 = 1032 := by
  have heq : (7 * (173) : ℕ) = 1211 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_173 : totient 173 = 173 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_173]
  try omega

theorem v3_phi_1211 : v3_fast (totient 1211) 100 = v3_phi_list.getD 1211 0 := by
  rw [tot_1211]
  rfl

theorem tot_1212 : totient 1212 = 400 := by
  have heq : (2^2 * (3 * (101)) : ℕ) = 1212 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_101]
  try omega

theorem v3_phi_1212 : v3_fast (totient 1212) 100 = v3_phi_list.getD 1212 0 := by
  rw [tot_1212]
  rfl

theorem tot_1213 : totient 1213 = 1212 := by
  have h : totient 1213 = 1213 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1213 : v3_fast (totient 1213) 100 = v3_phi_list.getD 1213 0 := by
  rw [tot_1213]
  rfl

theorem tot_1214 : totient 1214 = 606 := by
  have heq : (2 * (607) : ℕ) = 1214 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_607 : totient 607 = 607 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_607]
  try omega

theorem v3_phi_1214 : v3_fast (totient 1214) 100 = v3_phi_list.getD 1214 0 := by
  rw [tot_1214]
  rfl

theorem tot_1215 : totient 1215 = 648 := by
  have heq : (3^5 * (5) : ℕ) = 1215 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^5) = 3^4 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5]
  try omega

theorem v3_phi_1215 : v3_fast (totient 1215) 100 = v3_phi_list.getD 1215 0 := by
  rw [tot_1215]
  rfl

theorem tot_1216 : totient 1216 = 576 := by
  have heq : (2^6 * (19) : ℕ) = 1216 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_19]
  try omega

theorem v3_phi_1216 : v3_fast (totient 1216) 100 = v3_phi_list.getD 1216 0 := by
  rw [tot_1216]
  rfl

theorem tot_1217 : totient 1217 = 1216 := by
  have h : totient 1217 = 1217 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1217 : v3_fast (totient 1217) 100 = v3_phi_list.getD 1217 0 := by
  rw [tot_1217]
  rfl

theorem tot_1218 : totient 1218 = 336 := by
  have heq : (2 * (3 * (7 * (29))) : ℕ) = 1218 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_29]
  try omega

theorem v3_phi_1218 : v3_fast (totient 1218) 100 = v3_phi_list.getD 1218 0 := by
  rw [tot_1218]
  rfl

theorem tot_1219 : totient 1219 = 1144 := by
  have heq : (23 * (53) : ℕ) = 1219 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_53]
  try omega

theorem v3_phi_1219 : v3_fast (totient 1219) 100 = v3_phi_list.getD 1219 0 := by
  rw [tot_1219]
  rfl

theorem tot_1220 : totient 1220 = 480 := by
  have heq : (2^2 * (5 * (61)) : ℕ) = 1220 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_61]
  try omega

theorem v3_phi_1220 : v3_fast (totient 1220) 100 = v3_phi_list.getD 1220 0 := by
  rw [tot_1220]
  rfl

theorem tot_1221 : totient 1221 = 720 := by
  have heq : (3 * (11 * (37)) : ℕ) = 1221 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_37]
  try omega

theorem v3_phi_1221 : v3_fast (totient 1221) 100 = v3_phi_list.getD 1221 0 := by
  rw [tot_1221]
  rfl

theorem tot_1222 : totient 1222 = 552 := by
  have heq : (2 * (13 * (47)) : ℕ) = 1222 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_47]
  try omega

theorem v3_phi_1222 : v3_fast (totient 1222) 100 = v3_phi_list.getD 1222 0 := by
  rw [tot_1222]
  rfl

theorem tot_1223 : totient 1223 = 1222 := by
  have h : totient 1223 = 1223 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1223 : v3_fast (totient 1223) 100 = v3_phi_list.getD 1223 0 := by
  rw [tot_1223]
  rfl

theorem tot_1224 : totient 1224 = 384 := by
  have heq : (2^3 * (3^2 * (17)) : ℕ) = 1224 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_17]
  try omega

theorem v3_phi_1224 : v3_fast (totient 1224) 100 = v3_phi_list.getD 1224 0 := by
  rw [tot_1224]
  rfl

theorem tot_1225 : totient 1225 = 840 := by
  have heq : (5^2 * (7^2) : ℕ) = 1225 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_5, hp_7]
  try omega

theorem v3_phi_1225 : v3_fast (totient 1225) 100 = v3_phi_list.getD 1225 0 := by
  rw [tot_1225]
  rfl

theorem tot_1226 : totient 1226 = 612 := by
  have heq : (2 * (613) : ℕ) = 1226 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_613 : totient 613 = 613 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_613]
  try omega

theorem v3_phi_1226 : v3_fast (totient 1226) 100 = v3_phi_list.getD 1226 0 := by
  rw [tot_1226]
  rfl

theorem tot_1227 : totient 1227 = 816 := by
  have heq : (3 * (409) : ℕ) = 1227 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_409 : totient 409 = 409 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_409]
  try omega

theorem v3_phi_1227 : v3_fast (totient 1227) 100 = v3_phi_list.getD 1227 0 := by
  rw [tot_1227]
  rfl

theorem tot_1228 : totient 1228 = 612 := by
  have heq : (2^2 * (307) : ℕ) = 1228 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_307 : totient 307 = 307 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_307]
  try omega

theorem v3_phi_1228 : v3_fast (totient 1228) 100 = v3_phi_list.getD 1228 0 := by
  rw [tot_1228]
  rfl

theorem tot_1229 : totient 1229 = 1228 := by
  have h : totient 1229 = 1229 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1229 : v3_fast (totient 1229) 100 = v3_phi_list.getD 1229 0 := by
  rw [tot_1229]
  rfl

theorem tot_1230 : totient 1230 = 320 := by
  have heq : (2 * (3 * (5 * (41))) : ℕ) = 1230 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_41]
  try omega

theorem v3_phi_1230 : v3_fast (totient 1230) 100 = v3_phi_list.getD 1230 0 := by
  rw [tot_1230]
  rfl

theorem tot_1231 : totient 1231 = 1230 := by
  have h : totient 1231 = 1231 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1231 : v3_fast (totient 1231) 100 = v3_phi_list.getD 1231 0 := by
  rw [tot_1231]
  rfl

theorem tot_1232 : totient 1232 = 480 := by
  have heq : (2^4 * (7 * (11)) : ℕ) = 1232 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_11]
  try omega

theorem v3_phi_1232 : v3_fast (totient 1232) 100 = v3_phi_list.getD 1232 0 := by
  rw [tot_1232]
  rfl

theorem tot_1233 : totient 1233 = 816 := by
  have heq : (3^2 * (137) : ℕ) = 1233 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_137]
  try omega

theorem v3_phi_1233 : v3_fast (totient 1233) 100 = v3_phi_list.getD 1233 0 := by
  rw [tot_1233]
  rfl

theorem tot_1234 : totient 1234 = 616 := by
  have heq : (2 * (617) : ℕ) = 1234 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_617 : totient 617 = 617 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_617]
  try omega

theorem v3_phi_1234 : v3_fast (totient 1234) 100 = v3_phi_list.getD 1234 0 := by
  rw [tot_1234]
  rfl

theorem tot_1235 : totient 1235 = 864 := by
  have heq : (5 * (13 * (19)) : ℕ) = 1235 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_13, hp_19]
  try omega

theorem v3_phi_1235 : v3_fast (totient 1235) 100 = v3_phi_list.getD 1235 0 := by
  rw [tot_1235]
  rfl

theorem tot_1236 : totient 1236 = 408 := by
  have heq : (2^2 * (3 * (103)) : ℕ) = 1236 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_103]
  try omega

theorem v3_phi_1236 : v3_fast (totient 1236) 100 = v3_phi_list.getD 1236 0 := by
  rw [tot_1236]
  rfl

theorem tot_1237 : totient 1237 = 1236 := by
  have h : totient 1237 = 1237 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1237 : v3_fast (totient 1237) 100 = v3_phi_list.getD 1237 0 := by
  rw [tot_1237]
  rfl

theorem tot_1238 : totient 1238 = 618 := by
  have heq : (2 * (619) : ℕ) = 1238 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_619 : totient 619 = 619 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_619]
  try omega

theorem v3_phi_1238 : v3_fast (totient 1238) 100 = v3_phi_list.getD 1238 0 := by
  rw [tot_1238]
  rfl

theorem tot_1239 : totient 1239 = 696 := by
  have heq : (3 * (7 * (59)) : ℕ) = 1239 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_59]
  try omega

theorem v3_phi_1239 : v3_fast (totient 1239) 100 = v3_phi_list.getD 1239 0 := by
  rw [tot_1239]
  rfl

theorem tot_1240 : totient 1240 = 480 := by
  have heq : (2^3 * (5 * (31)) : ℕ) = 1240 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_31]
  try omega

theorem v3_phi_1240 : v3_fast (totient 1240) 100 = v3_phi_list.getD 1240 0 := by
  rw [tot_1240]
  rfl

theorem tot_1241 : totient 1241 = 1152 := by
  have heq : (17 * (73) : ℕ) = 1241 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_73]
  try omega

theorem v3_phi_1241 : v3_fast (totient 1241) 100 = v3_phi_list.getD 1241 0 := by
  rw [tot_1241]
  rfl

theorem tot_1242 : totient 1242 = 396 := by
  have heq : (2 * (3^3 * (23)) : ℕ) = 1242 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_23]
  try omega

theorem v3_phi_1242 : v3_fast (totient 1242) 100 = v3_phi_list.getD 1242 0 := by
  rw [tot_1242]
  rfl

theorem tot_1243 : totient 1243 = 1120 := by
  have heq : (11 * (113) : ℕ) = 1243 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_11, hp_113]
  try omega

theorem v3_phi_1243 : v3_fast (totient 1243) 100 = v3_phi_list.getD 1243 0 := by
  rw [tot_1243]
  rfl

theorem tot_1244 : totient 1244 = 620 := by
  have heq : (2^2 * (311) : ℕ) = 1244 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_311 : totient 311 = 311 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_311]
  try omega

theorem v3_phi_1244 : v3_fast (totient 1244) 100 = v3_phi_list.getD 1244 0 := by
  rw [tot_1244]
  rfl

theorem tot_1245 : totient 1245 = 656 := by
  have heq : (3 * (5 * (83)) : ℕ) = 1245 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_83]
  try omega

theorem v3_phi_1245 : v3_fast (totient 1245) 100 = v3_phi_list.getD 1245 0 := by
  rw [tot_1245]
  rfl

theorem tot_1246 : totient 1246 = 528 := by
  have heq : (2 * (7 * (89)) : ℕ) = 1246 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_89]
  try omega

theorem v3_phi_1246 : v3_fast (totient 1246) 100 = v3_phi_list.getD 1246 0 := by
  rw [tot_1246]
  rfl

theorem tot_1247 : totient 1247 = 1176 := by
  have heq : (29 * (43) : ℕ) = 1247 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_43]
  try omega

theorem v3_phi_1247 : v3_fast (totient 1247) 100 = v3_phi_list.getD 1247 0 := by
  rw [tot_1247]
  rfl

theorem tot_1248 : totient 1248 = 384 := by
  have heq : (2^5 * (3 * (13)) : ℕ) = 1248 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13]
  try omega

theorem v3_phi_1248 : v3_fast (totient 1248) 100 = v3_phi_list.getD 1248 0 := by
  rw [tot_1248]
  rfl

theorem tot_1249 : totient 1249 = 1248 := by
  have h : totient 1249 = 1249 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1249 : v3_fast (totient 1249) 100 = v3_phi_list.getD 1249 0 := by
  rw [tot_1249]
  rfl

theorem tot_1250 : totient 1250 = 500 := by
  have heq : (2 * (5^4) : ℕ) = 1250 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^4) = 5^3 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_1250 : v3_fast (totient 1250) 100 = v3_phi_list.getD 1250 0 := by
  rw [tot_1250]
  rfl

theorem tot_1251 : totient 1251 = 828 := by
  have heq : (3^2 * (139) : ℕ) = 1251 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_139 : totient 139 = 139 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_139]
  try omega

theorem v3_phi_1251 : v3_fast (totient 1251) 100 = v3_phi_list.getD 1251 0 := by
  rw [tot_1251]
  rfl

theorem tot_1252 : totient 1252 = 624 := by
  have heq : (2^2 * (313) : ℕ) = 1252 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_313 : totient 313 = 313 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_313]
  try omega

theorem v3_phi_1252 : v3_fast (totient 1252) 100 = v3_phi_list.getD 1252 0 := by
  rw [tot_1252]
  rfl

theorem tot_1253 : totient 1253 = 1068 := by
  have heq : (7 * (179) : ℕ) = 1253 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_179 : totient 179 = 179 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_179]
  try omega

theorem v3_phi_1253 : v3_fast (totient 1253) 100 = v3_phi_list.getD 1253 0 := by
  rw [tot_1253]
  rfl

theorem tot_1254 : totient 1254 = 360 := by
  have heq : (2 * (3 * (11 * (19))) : ℕ) = 1254 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_11, hp_19]
  try omega

theorem v3_phi_1254 : v3_fast (totient 1254) 100 = v3_phi_list.getD 1254 0 := by
  rw [tot_1254]
  rfl

theorem tot_1255 : totient 1255 = 1000 := by
  have heq : (5 * (251) : ℕ) = 1255 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_251 : totient 251 = 251 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_251]
  try omega

theorem v3_phi_1255 : v3_fast (totient 1255) 100 = v3_phi_list.getD 1255 0 := by
  rw [tot_1255]
  rfl

theorem tot_1256 : totient 1256 = 624 := by
  have heq : (2^3 * (157) : ℕ) = 1256 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_157 : totient 157 = 157 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_157]
  try omega

theorem v3_phi_1256 : v3_fast (totient 1256) 100 = v3_phi_list.getD 1256 0 := by
  rw [tot_1256]
  rfl

theorem tot_1257 : totient 1257 = 836 := by
  have heq : (3 * (419) : ℕ) = 1257 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_419 : totient 419 = 419 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_419]
  try omega

theorem v3_phi_1257 : v3_fast (totient 1257) 100 = v3_phi_list.getD 1257 0 := by
  rw [tot_1257]
  rfl

theorem tot_1258 : totient 1258 = 576 := by
  have heq : (2 * (17 * (37)) : ℕ) = 1258 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_37]
  try omega

theorem v3_phi_1258 : v3_fast (totient 1258) 100 = v3_phi_list.getD 1258 0 := by
  rw [tot_1258]
  rfl

theorem tot_1259 : totient 1259 = 1258 := by
  have h : totient 1259 = 1259 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1259 : v3_fast (totient 1259) 100 = v3_phi_list.getD 1259 0 := by
  rw [tot_1259]
  rfl

theorem tot_1260 : totient 1260 = 288 := by
  have heq : (2^2 * (3^2 * (5 * (7))) : ℕ) = 1260 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_7]
  try omega

theorem v3_phi_1260 : v3_fast (totient 1260) 100 = v3_phi_list.getD 1260 0 := by
  rw [tot_1260]
  rfl

theorem tot_1261 : totient 1261 = 1152 := by
  have heq : (13 * (97) : ℕ) = 1261 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_97]
  try omega

theorem v3_phi_1261 : v3_fast (totient 1261) 100 = v3_phi_list.getD 1261 0 := by
  rw [tot_1261]
  rfl

theorem tot_1262 : totient 1262 = 630 := by
  have heq : (2 * (631) : ℕ) = 1262 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_631 : totient 631 = 631 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_631]
  try omega

theorem v3_phi_1262 : v3_fast (totient 1262) 100 = v3_phi_list.getD 1262 0 := by
  rw [tot_1262]
  rfl

theorem tot_1263 : totient 1263 = 840 := by
  have heq : (3 * (421) : ℕ) = 1263 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_421 : totient 421 = 421 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_421]
  try omega

theorem v3_phi_1263 : v3_fast (totient 1263) 100 = v3_phi_list.getD 1263 0 := by
  rw [tot_1263]
  rfl

theorem tot_1264 : totient 1264 = 624 := by
  have heq : (2^4 * (79) : ℕ) = 1264 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_79]
  try omega

theorem v3_phi_1264 : v3_fast (totient 1264) 100 = v3_phi_list.getD 1264 0 := by
  rw [tot_1264]
  rfl

theorem tot_1265 : totient 1265 = 880 := by
  have heq : (5 * (11 * (23)) : ℕ) = 1265 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11, hp_23]
  try omega

theorem v3_phi_1265 : v3_fast (totient 1265) 100 = v3_phi_list.getD 1265 0 := by
  rw [tot_1265]
  rfl

theorem tot_1266 : totient 1266 = 420 := by
  have heq : (2 * (3 * (211)) : ℕ) = 1266 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_211 : totient 211 = 211 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_211]
  try omega

theorem v3_phi_1266 : v3_fast (totient 1266) 100 = v3_phi_list.getD 1266 0 := by
  rw [tot_1266]
  rfl

theorem tot_1267 : totient 1267 = 1080 := by
  have heq : (7 * (181) : ℕ) = 1267 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_181 : totient 181 = 181 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_181]
  try omega

theorem v3_phi_1267 : v3_fast (totient 1267) 100 = v3_phi_list.getD 1267 0 := by
  rw [tot_1267]
  rfl

theorem tot_1268 : totient 1268 = 632 := by
  have heq : (2^2 * (317) : ℕ) = 1268 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_317 : totient 317 = 317 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_317]
  try omega

theorem v3_phi_1268 : v3_fast (totient 1268) 100 = v3_phi_list.getD 1268 0 := by
  rw [tot_1268]
  rfl

theorem tot_1269 : totient 1269 = 828 := by
  have heq : (3^3 * (47) : ℕ) = 1269 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_47]
  try omega

theorem v3_phi_1269 : v3_fast (totient 1269) 100 = v3_phi_list.getD 1269 0 := by
  rw [tot_1269]
  rfl

theorem tot_1270 : totient 1270 = 504 := by
  have heq : (2 * (5 * (127)) : ℕ) = 1270 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_127 : totient 127 = 127 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_127]
  try omega

theorem v3_phi_1270 : v3_fast (totient 1270) 100 = v3_phi_list.getD 1270 0 := by
  rw [tot_1270]
  rfl

theorem tot_1271 : totient 1271 = 1200 := by
  have heq : (31 * (41) : ℕ) = 1271 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_31, hp_41]
  try omega

theorem v3_phi_1271 : v3_fast (totient 1271) 100 = v3_phi_list.getD 1271 0 := by
  rw [tot_1271]
  rfl

theorem tot_1272 : totient 1272 = 416 := by
  have heq : (2^3 * (3 * (53)) : ℕ) = 1272 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_53]
  try omega

theorem v3_phi_1272 : v3_fast (totient 1272) 100 = v3_phi_list.getD 1272 0 := by
  rw [tot_1272]
  rfl

theorem tot_1273 : totient 1273 = 1188 := by
  have heq : (19 * (67) : ℕ) = 1273 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_67]
  try omega

theorem v3_phi_1273 : v3_fast (totient 1273) 100 = v3_phi_list.getD 1273 0 := by
  rw [tot_1273]
  rfl

theorem tot_1274 : totient 1274 = 504 := by
  have heq : (2 * (7^2 * (13)) : ℕ) = 1274 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_13]
  try omega

theorem v3_phi_1274 : v3_fast (totient 1274) 100 = v3_phi_list.getD 1274 0 := by
  rw [tot_1274]
  rfl

theorem tot_1275 : totient 1275 = 640 := by
  have heq : (3 * (5^2 * (17)) : ℕ) = 1275 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_17]
  try omega

theorem v3_phi_1275 : v3_fast (totient 1275) 100 = v3_phi_list.getD 1275 0 := by
  rw [tot_1275]
  rfl

theorem tot_1276 : totient 1276 = 560 := by
  have heq : (2^2 * (11 * (29)) : ℕ) = 1276 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_29]
  try omega

theorem v3_phi_1276 : v3_fast (totient 1276) 100 = v3_phi_list.getD 1276 0 := by
  rw [tot_1276]
  rfl

theorem tot_1277 : totient 1277 = 1276 := by
  have h : totient 1277 = 1277 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1277 : v3_fast (totient 1277) 100 = v3_phi_list.getD 1277 0 := by
  rw [tot_1277]
  rfl

theorem tot_1278 : totient 1278 = 420 := by
  have heq : (2 * (3^2 * (71)) : ℕ) = 1278 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_71]
  try omega

theorem v3_phi_1278 : v3_fast (totient 1278) 100 = v3_phi_list.getD 1278 0 := by
  rw [tot_1278]
  rfl

theorem tot_1279 : totient 1279 = 1278 := by
  have h : totient 1279 = 1279 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1279 : v3_fast (totient 1279) 100 = v3_phi_list.getD 1279 0 := by
  rw [tot_1279]
  rfl

theorem tot_1280 : totient 1280 = 512 := by
  have heq : (2^8 * (5) : ℕ) = 1280 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^8) = 2^7 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5]
  try omega

theorem v3_phi_1280 : v3_fast (totient 1280) 100 = v3_phi_list.getD 1280 0 := by
  rw [tot_1280]
  rfl

theorem tot_1281 : totient 1281 = 720 := by
  have heq : (3 * (7 * (61)) : ℕ) = 1281 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_7, hp_61]
  try omega

theorem v3_phi_1281 : v3_fast (totient 1281) 100 = v3_phi_list.getD 1281 0 := by
  rw [tot_1281]
  rfl

theorem tot_1282 : totient 1282 = 640 := by
  have heq : (2 * (641) : ℕ) = 1282 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_641 : totient 641 = 641 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_641]
  try omega

theorem v3_phi_1282 : v3_fast (totient 1282) 100 = v3_phi_list.getD 1282 0 := by
  rw [tot_1282]
  rfl

theorem tot_1283 : totient 1283 = 1282 := by
  have h : totient 1283 = 1283 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1283 : v3_fast (totient 1283) 100 = v3_phi_list.getD 1283 0 := by
  rw [tot_1283]
  rfl

theorem tot_1284 : totient 1284 = 424 := by
  have heq : (2^2 * (3 * (107)) : ℕ) = 1284 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_107 : totient 107 = 107 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_107]
  try omega

theorem v3_phi_1284 : v3_fast (totient 1284) 100 = v3_phi_list.getD 1284 0 := by
  rw [tot_1284]
  rfl

theorem tot_1285 : totient 1285 = 1024 := by
  have heq : (5 * (257) : ℕ) = 1285 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_257 : totient 257 = 257 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_257]
  try omega

theorem v3_phi_1285 : v3_fast (totient 1285) 100 = v3_phi_list.getD 1285 0 := by
  rw [tot_1285]
  rfl

theorem tot_1286 : totient 1286 = 642 := by
  have heq : (2 * (643) : ℕ) = 1286 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_643 : totient 643 = 643 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_643]
  try omega

theorem v3_phi_1286 : v3_fast (totient 1286) 100 = v3_phi_list.getD 1286 0 := by
  rw [tot_1286]
  rfl

theorem tot_1287 : totient 1287 = 720 := by
  have heq : (3^2 * (11 * (13)) : ℕ) = 1287 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_13]
  try omega

theorem v3_phi_1287 : v3_fast (totient 1287) 100 = v3_phi_list.getD 1287 0 := by
  rw [tot_1287]
  rfl

theorem tot_1288 : totient 1288 = 528 := by
  have heq : (2^3 * (7 * (23)) : ℕ) = 1288 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_23]
  try omega

theorem v3_phi_1288 : v3_fast (totient 1288) 100 = v3_phi_list.getD 1288 0 := by
  rw [tot_1288]
  rfl

theorem tot_1289 : totient 1289 = 1288 := by
  have h : totient 1289 = 1289 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1289 : v3_fast (totient 1289) 100 = v3_phi_list.getD 1289 0 := by
  rw [tot_1289]
  rfl

theorem tot_1290 : totient 1290 = 336 := by
  have heq : (2 * (3 * (5 * (43))) : ℕ) = 1290 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_43]
  try omega

theorem v3_phi_1290 : v3_fast (totient 1290) 100 = v3_phi_list.getD 1290 0 := by
  rw [tot_1290]
  rfl

theorem tot_1291 : totient 1291 = 1290 := by
  have h : totient 1291 = 1291 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1291 : v3_fast (totient 1291) 100 = v3_phi_list.getD 1291 0 := by
  rw [tot_1291]
  rfl

theorem tot_1292 : totient 1292 = 576 := by
  have heq : (2^2 * (17 * (19)) : ℕ) = 1292 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_17, hp_19]
  try omega

theorem v3_phi_1292 : v3_fast (totient 1292) 100 = v3_phi_list.getD 1292 0 := by
  rw [tot_1292]
  rfl

theorem tot_1293 : totient 1293 = 860 := by
  have heq : (3 * (431) : ℕ) = 1293 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_431 : totient 431 = 431 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_431]
  try omega

theorem v3_phi_1293 : v3_fast (totient 1293) 100 = v3_phi_list.getD 1293 0 := by
  rw [tot_1293]
  rfl

theorem tot_1294 : totient 1294 = 646 := by
  have heq : (2 * (647) : ℕ) = 1294 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_647 : totient 647 = 647 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_647]
  try omega

theorem v3_phi_1294 : v3_fast (totient 1294) 100 = v3_phi_list.getD 1294 0 := by
  rw [tot_1294]
  rfl

theorem tot_1295 : totient 1295 = 864 := by
  have heq : (5 * (7 * (37)) : ℕ) = 1295 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_7, hp_37]
  try omega

theorem v3_phi_1295 : v3_fast (totient 1295) 100 = v3_phi_list.getD 1295 0 := by
  rw [tot_1295]
  rfl

theorem tot_1296 : totient 1296 = 432 := by
  have heq : (2^4 * (3^4) : ℕ) = 1296 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3]
  try omega

theorem v3_phi_1296 : v3_fast (totient 1296) 100 = v3_phi_list.getD 1296 0 := by
  rw [tot_1296]
  rfl

theorem tot_1297 : totient 1297 = 1296 := by
  have h : totient 1297 = 1297 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1297 : v3_fast (totient 1297) 100 = v3_phi_list.getD 1297 0 := by
  rw [tot_1297]
  rfl

theorem tot_1298 : totient 1298 = 580 := by
  have heq : (2 * (11 * (59)) : ℕ) = 1298 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_59]
  try omega

theorem v3_phi_1298 : v3_fast (totient 1298) 100 = v3_phi_list.getD 1298 0 := by
  rw [tot_1298]
  rfl

theorem tot_1299 : totient 1299 = 864 := by
  have heq : (3 * (433) : ℕ) = 1299 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_433 : totient 433 = 433 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_433]
  try omega

theorem v3_phi_1299 : v3_fast (totient 1299) 100 = v3_phi_list.getD 1299 0 := by
  rw [tot_1299]
  rfl

theorem tot_1300 : totient 1300 = 480 := by
  have heq : (2^2 * (5^2 * (13)) : ℕ) = 1300 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_13]
  try omega

theorem v3_phi_1300 : v3_fast (totient 1300) 100 = v3_phi_list.getD 1300 0 := by
  rw [tot_1300]
  rfl

theorem tot_1301 : totient 1301 = 1300 := by
  have h : totient 1301 = 1301 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1301 : v3_fast (totient 1301) 100 = v3_phi_list.getD 1301 0 := by
  rw [tot_1301]
  rfl

theorem tot_1302 : totient 1302 = 360 := by
  have heq : (2 * (3 * (7 * (31))) : ℕ) = 1302 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7, hp_31]
  try omega

theorem v3_phi_1302 : v3_fast (totient 1302) 100 = v3_phi_list.getD 1302 0 := by
  rw [tot_1302]
  rfl

theorem tot_1303 : totient 1303 = 1302 := by
  have h : totient 1303 = 1303 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1303 : v3_fast (totient 1303) 100 = v3_phi_list.getD 1303 0 := by
  rw [tot_1303]
  rfl

theorem tot_1304 : totient 1304 = 648 := by
  have heq : (2^3 * (163) : ℕ) = 1304 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_163 : totient 163 = 163 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_163]
  try omega

theorem v3_phi_1304 : v3_fast (totient 1304) 100 = v3_phi_list.getD 1304 0 := by
  rw [tot_1304]
  rfl

theorem tot_1305 : totient 1305 = 672 := by
  have heq : (3^2 * (5 * (29)) : ℕ) = 1305 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_29]
  try omega

theorem v3_phi_1305 : v3_fast (totient 1305) 100 = v3_phi_list.getD 1305 0 := by
  rw [tot_1305]
  rfl

theorem tot_1306 : totient 1306 = 652 := by
  have heq : (2 * (653) : ℕ) = 1306 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_653 : totient 653 = 653 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_653]
  try omega

theorem v3_phi_1306 : v3_fast (totient 1306) 100 = v3_phi_list.getD 1306 0 := by
  rw [tot_1306]
  rfl

theorem tot_1307 : totient 1307 = 1306 := by
  have h : totient 1307 = 1307 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1307 : v3_fast (totient 1307) 100 = v3_phi_list.getD 1307 0 := by
  rw [tot_1307]
  rfl

theorem tot_1308 : totient 1308 = 432 := by
  have heq : (2^2 * (3 * (109)) : ℕ) = 1308 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_109 : totient 109 = 109 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_109]
  try omega

theorem v3_phi_1308 : v3_fast (totient 1308) 100 = v3_phi_list.getD 1308 0 := by
  rw [tot_1308]
  rfl

theorem tot_1309 : totient 1309 = 960 := by
  have heq : (7 * (11 * (17)) : ℕ) = 1309 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_11, hp_17]
  try omega

theorem v3_phi_1309 : v3_fast (totient 1309) 100 = v3_phi_list.getD 1309 0 := by
  rw [tot_1309]
  rfl

theorem tot_1310 : totient 1310 = 520 := by
  have heq : (2 * (5 * (131)) : ℕ) = 1310 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_131 : totient 131 = 131 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_131]
  try omega

theorem v3_phi_1310 : v3_fast (totient 1310) 100 = v3_phi_list.getD 1310 0 := by
  rw [tot_1310]
  rfl

theorem tot_1311 : totient 1311 = 792 := by
  have heq : (3 * (19 * (23)) : ℕ) = 1311 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_19, hp_23]
  try omega

theorem v3_phi_1311 : v3_fast (totient 1311) 100 = v3_phi_list.getD 1311 0 := by
  rw [tot_1311]
  rfl

theorem tot_1312 : totient 1312 = 640 := by
  have heq : (2^5 * (41) : ℕ) = 1312 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_41]
  try omega

theorem v3_phi_1312 : v3_fast (totient 1312) 100 = v3_phi_list.getD 1312 0 := by
  rw [tot_1312]
  rfl

theorem tot_1313 : totient 1313 = 1200 := by
  have heq : (13 * (101) : ℕ) = 1313 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_101 : totient 101 = 101 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_101]
  try omega

theorem v3_phi_1313 : v3_fast (totient 1313) 100 = v3_phi_list.getD 1313 0 := by
  rw [tot_1313]
  rfl

theorem tot_1314 : totient 1314 = 432 := by
  have heq : (2 * (3^2 * (73)) : ℕ) = 1314 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_73 : totient 73 = 73 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_73]
  try omega

theorem v3_phi_1314 : v3_fast (totient 1314) 100 = v3_phi_list.getD 1314 0 := by
  rw [tot_1314]
  rfl

theorem tot_1315 : totient 1315 = 1048 := by
  have heq : (5 * (263) : ℕ) = 1315 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_263 : totient 263 = 263 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_263]
  try omega

theorem v3_phi_1315 : v3_fast (totient 1315) 100 = v3_phi_list.getD 1315 0 := by
  rw [tot_1315]
  rfl

theorem tot_1316 : totient 1316 = 552 := by
  have heq : (2^2 * (7 * (47)) : ℕ) = 1316 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_47]
  try omega

theorem v3_phi_1316 : v3_fast (totient 1316) 100 = v3_phi_list.getD 1316 0 := by
  rw [tot_1316]
  rfl

theorem tot_1317 : totient 1317 = 876 := by
  have heq : (3 * (439) : ℕ) = 1317 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_439 : totient 439 = 439 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_439]
  try omega

theorem v3_phi_1317 : v3_fast (totient 1317) 100 = v3_phi_list.getD 1317 0 := by
  rw [tot_1317]
  rfl

theorem tot_1318 : totient 1318 = 658 := by
  have heq : (2 * (659) : ℕ) = 1318 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_659 : totient 659 = 659 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_659]
  try omega

theorem v3_phi_1318 : v3_fast (totient 1318) 100 = v3_phi_list.getD 1318 0 := by
  rw [tot_1318]
  rfl

theorem tot_1319 : totient 1319 = 1318 := by
  have h : totient 1319 = 1319 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1319 : v3_fast (totient 1319) 100 = v3_phi_list.getD 1319 0 := by
  rw [tot_1319]
  rfl

theorem tot_1320 : totient 1320 = 320 := by
  have heq : (2^3 * (3 * (5 * (11))) : ℕ) = 1320 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_5, hp_11]
  try omega

theorem v3_phi_1320 : v3_fast (totient 1320) 100 = v3_phi_list.getD 1320 0 := by
  rw [tot_1320]
  rfl

theorem tot_1321 : totient 1321 = 1320 := by
  have h : totient 1321 = 1321 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1321 : v3_fast (totient 1321) 100 = v3_phi_list.getD 1321 0 := by
  rw [tot_1321]
  rfl

theorem tot_1322 : totient 1322 = 660 := by
  have heq : (2 * (661) : ℕ) = 1322 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_661 : totient 661 = 661 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_661]
  try omega

theorem v3_phi_1322 : v3_fast (totient 1322) 100 = v3_phi_list.getD 1322 0 := by
  rw [tot_1322]
  rfl

theorem tot_1323 : totient 1323 = 756 := by
  have heq : (3^3 * (7^2) : ℕ) = 1323 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^2) = 7^1 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_3, hp_7]
  try omega

theorem v3_phi_1323 : v3_fast (totient 1323) 100 = v3_phi_list.getD 1323 0 := by
  rw [tot_1323]
  rfl

theorem tot_1324 : totient 1324 = 660 := by
  have heq : (2^2 * (331) : ℕ) = 1324 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_331 : totient 331 = 331 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_331]
  try omega

theorem v3_phi_1324 : v3_fast (totient 1324) 100 = v3_phi_list.getD 1324 0 := by
  rw [tot_1324]
  rfl

theorem tot_1325 : totient 1325 = 1040 := by
  have heq : (5^2 * (53) : ℕ) = 1325 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_53]
  try omega

theorem v3_phi_1325 : v3_fast (totient 1325) 100 = v3_phi_list.getD 1325 0 := by
  rw [tot_1325]
  rfl

theorem tot_1326 : totient 1326 = 384 := by
  have heq : (2 * (3 * (13 * (17))) : ℕ) = 1326 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_13, hp_17]
  try omega

theorem v3_phi_1326 : v3_fast (totient 1326) 100 = v3_phi_list.getD 1326 0 := by
  rw [tot_1326]
  rfl

theorem tot_1327 : totient 1327 = 1326 := by
  have h : totient 1327 = 1327 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1327 : v3_fast (totient 1327) 100 = v3_phi_list.getD 1327 0 := by
  rw [tot_1327]
  rfl

theorem tot_1328 : totient 1328 = 656 := by
  have heq : (2^4 * (83) : ℕ) = 1328 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_83 : totient 83 = 83 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_83]
  try omega

theorem v3_phi_1328 : v3_fast (totient 1328) 100 = v3_phi_list.getD 1328 0 := by
  rw [tot_1328]
  rfl

theorem tot_1329 : totient 1329 = 884 := by
  have heq : (3 * (443) : ℕ) = 1329 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_443 : totient 443 = 443 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_443]
  try omega

theorem v3_phi_1329 : v3_fast (totient 1329) 100 = v3_phi_list.getD 1329 0 := by
  rw [tot_1329]
  rfl

theorem tot_1330 : totient 1330 = 432 := by
  have heq : (2 * (5 * (7 * (19))) : ℕ) = 1330 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_7, hp_19]
  try omega

theorem v3_phi_1330 : v3_fast (totient 1330) 100 = v3_phi_list.getD 1330 0 := by
  rw [tot_1330]
  rfl

theorem tot_1331 : totient 1331 = 1210 := by
  have h : totient (11^3) = 11^2 * (11 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (11^3 : ℕ) = 1331 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_1331 : v3_fast (totient 1331) 100 = v3_phi_list.getD 1331 0 := by
  rw [tot_1331]
  rfl

theorem tot_1332 : totient 1332 = 432 := by
  have heq : (2^2 * (3^2 * (37)) : ℕ) = 1332 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_37 : totient 37 = 37 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_37]
  try omega

theorem v3_phi_1332 : v3_fast (totient 1332) 100 = v3_phi_list.getD 1332 0 := by
  rw [tot_1332]
  rfl

theorem tot_1333 : totient 1333 = 1260 := by
  have heq : (31 * (43) : ℕ) = 1333 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_31, hp_43]
  try omega

theorem v3_phi_1333 : v3_fast (totient 1333) 100 = v3_phi_list.getD 1333 0 := by
  rw [tot_1333]
  rfl

theorem tot_1334 : totient 1334 = 616 := by
  have heq : (2 * (23 * (29)) : ℕ) = 1334 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_23, hp_29]
  try omega

theorem v3_phi_1334 : v3_fast (totient 1334) 100 = v3_phi_list.getD 1334 0 := by
  rw [tot_1334]
  rfl

theorem tot_1335 : totient 1335 = 704 := by
  have heq : (3 * (5 * (89)) : ℕ) = 1335 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_89 : totient 89 = 89 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_89]
  try omega

theorem v3_phi_1335 : v3_fast (totient 1335) 100 = v3_phi_list.getD 1335 0 := by
  rw [tot_1335]
  rfl

theorem tot_1336 : totient 1336 = 664 := by
  have heq : (2^3 * (167) : ℕ) = 1336 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_167 : totient 167 = 167 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_167]
  try omega

theorem v3_phi_1336 : v3_fast (totient 1336) 100 = v3_phi_list.getD 1336 0 := by
  rw [tot_1336]
  rfl

theorem tot_1337 : totient 1337 = 1140 := by
  have heq : (7 * (191) : ℕ) = 1337 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_191 : totient 191 = 191 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_191]
  try omega

theorem v3_phi_1337 : v3_fast (totient 1337) 100 = v3_phi_list.getD 1337 0 := by
  rw [tot_1337]
  rfl

theorem tot_1338 : totient 1338 = 444 := by
  have heq : (2 * (3 * (223)) : ℕ) = 1338 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_223 : totient 223 = 223 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_223]
  try omega

theorem v3_phi_1338 : v3_fast (totient 1338) 100 = v3_phi_list.getD 1338 0 := by
  rw [tot_1338]
  rfl

theorem tot_1339 : totient 1339 = 1224 := by
  have heq : (13 * (103) : ℕ) = 1339 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_103 : totient 103 = 103 - 1 := totient_prime (by norm_num)
  rw [hp_13, hp_103]
  try omega

theorem v3_phi_1339 : v3_fast (totient 1339) 100 = v3_phi_list.getD 1339 0 := by
  rw [tot_1339]
  rfl

theorem tot_1340 : totient 1340 = 528 := by
  have heq : (2^2 * (5 * (67)) : ℕ) = 1340 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_67 : totient 67 = 67 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_67]
  try omega

theorem v3_phi_1340 : v3_fast (totient 1340) 100 = v3_phi_list.getD 1340 0 := by
  rw [tot_1340]
  rfl

theorem tot_1341 : totient 1341 = 888 := by
  have heq : (3^2 * (149) : ℕ) = 1341 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_149 : totient 149 = 149 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_149]
  try omega

theorem v3_phi_1341 : v3_fast (totient 1341) 100 = v3_phi_list.getD 1341 0 := by
  rw [tot_1341]
  rfl

theorem tot_1342 : totient 1342 = 600 := by
  have heq : (2 * (11 * (61)) : ℕ) = 1342 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_61 : totient 61 = 61 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_61]
  try omega

theorem v3_phi_1342 : v3_fast (totient 1342) 100 = v3_phi_list.getD 1342 0 := by
  rw [tot_1342]
  rfl

theorem tot_1343 : totient 1343 = 1248 := by
  have heq : (17 * (79) : ℕ) = 1343 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  have hp_79 : totient 79 = 79 - 1 := totient_prime (by norm_num)
  rw [hp_17, hp_79]
  try omega

theorem v3_phi_1343 : v3_fast (totient 1343) 100 = v3_phi_list.getD 1343 0 := by
  rw [tot_1343]
  rfl

theorem tot_1344 : totient 1344 = 384 := by
  have heq : (2^6 * (3 * (7)) : ℕ) = 1344 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^6) = 2^5 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_7]
  try omega

theorem v3_phi_1344 : v3_fast (totient 1344) 100 = v3_phi_list.getD 1344 0 := by
  rw [tot_1344]
  rfl

theorem tot_1345 : totient 1345 = 1072 := by
  have heq : (5 * (269) : ℕ) = 1345 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_269 : totient 269 = 269 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_269]
  try omega

theorem v3_phi_1345 : v3_fast (totient 1345) 100 = v3_phi_list.getD 1345 0 := by
  rw [tot_1345]
  rfl

theorem tot_1346 : totient 1346 = 672 := by
  have heq : (2 * (673) : ℕ) = 1346 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_673 : totient 673 = 673 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_673]
  try omega

theorem v3_phi_1346 : v3_fast (totient 1346) 100 = v3_phi_list.getD 1346 0 := by
  rw [tot_1346]
  rfl

theorem tot_1347 : totient 1347 = 896 := by
  have heq : (3 * (449) : ℕ) = 1347 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_449 : totient 449 = 449 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_449]
  try omega

theorem v3_phi_1347 : v3_fast (totient 1347) 100 = v3_phi_list.getD 1347 0 := by
  rw [tot_1347]
  rfl

theorem tot_1348 : totient 1348 = 672 := by
  have heq : (2^2 * (337) : ℕ) = 1348 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_337 : totient 337 = 337 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_337]
  try omega

theorem v3_phi_1348 : v3_fast (totient 1348) 100 = v3_phi_list.getD 1348 0 := by
  rw [tot_1348]
  rfl

theorem tot_1349 : totient 1349 = 1260 := by
  have heq : (19 * (71) : ℕ) = 1349 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  have hp_71 : totient 71 = 71 - 1 := totient_prime (by norm_num)
  rw [hp_19, hp_71]
  try omega

theorem v3_phi_1349 : v3_fast (totient 1349) 100 = v3_phi_list.getD 1349 0 := by
  rw [tot_1349]
  rfl

theorem tot_1350 : totient 1350 = 360 := by
  have heq : (2 * (3^3 * (5^2)) : ℕ) = 1350 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient (3^3) = 3^2 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient (5^2) = 5^1 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_3, hp_5]
  try omega

theorem v3_phi_1350 : v3_fast (totient 1350) 100 = v3_phi_list.getD 1350 0 := by
  rw [tot_1350]
  rfl

theorem tot_1351 : totient 1351 = 1152 := by
  have heq : (7 * (193) : ℕ) = 1351 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_193 : totient 193 = 193 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_193]
  try omega

theorem v3_phi_1351 : v3_fast (totient 1351) 100 = v3_phi_list.getD 1351 0 := by
  rw [tot_1351]
  rfl

theorem tot_1352 : totient 1352 = 624 := by
  have heq : (2^3 * (13^2) : ℕ) = 1352 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_13 : totient (13^2) = 13^1 * (13 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_13]
  try omega

theorem v3_phi_1352 : v3_fast (totient 1352) 100 = v3_phi_list.getD 1352 0 := by
  rw [tot_1352]
  rfl

theorem tot_1353 : totient 1353 = 800 := by
  have heq : (3 * (11 * (41)) : ℕ) = 1353 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_41 : totient 41 = 41 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_11, hp_41]
  try omega

theorem v3_phi_1353 : v3_fast (totient 1353) 100 = v3_phi_list.getD 1353 0 := by
  rw [tot_1353]
  rfl

theorem tot_1354 : totient 1354 = 676 := by
  have heq : (2 * (677) : ℕ) = 1354 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_677 : totient 677 = 677 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_677]
  try omega

theorem v3_phi_1354 : v3_fast (totient 1354) 100 = v3_phi_list.getD 1354 0 := by
  rw [tot_1354]
  rfl

theorem tot_1355 : totient 1355 = 1080 := by
  have heq : (5 * (271) : ℕ) = 1355 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_271 : totient 271 = 271 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_271]
  try omega

theorem v3_phi_1355 : v3_fast (totient 1355) 100 = v3_phi_list.getD 1355 0 := by
  rw [tot_1355]
  rfl

theorem tot_1356 : totient 1356 = 448 := by
  have heq : (2^2 * (3 * (113)) : ℕ) = 1356 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_113 : totient 113 = 113 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_113]
  try omega

theorem v3_phi_1356 : v3_fast (totient 1356) 100 = v3_phi_list.getD 1356 0 := by
  rw [tot_1356]
  rfl

theorem tot_1357 : totient 1357 = 1276 := by
  have heq : (23 * (59) : ℕ) = 1357 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_23 : totient 23 = 23 - 1 := totient_prime (by norm_num)
  have hp_59 : totient 59 = 59 - 1 := totient_prime (by norm_num)
  rw [hp_23, hp_59]
  try omega

theorem v3_phi_1357 : v3_fast (totient 1357) 100 = v3_phi_list.getD 1357 0 := by
  rw [tot_1357]
  rfl

theorem tot_1358 : totient 1358 = 576 := by
  have heq : (2 * (7 * (97)) : ℕ) = 1358 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_97 : totient 97 = 97 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_7, hp_97]
  try omega

theorem v3_phi_1358 : v3_fast (totient 1358) 100 = v3_phi_list.getD 1358 0 := by
  rw [tot_1358]
  rfl

theorem tot_1359 : totient 1359 = 900 := by
  have heq : (3^2 * (151) : ℕ) = 1359 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_151 : totient 151 = 151 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_151]
  try omega

theorem v3_phi_1359 : v3_fast (totient 1359) 100 = v3_phi_list.getD 1359 0 := by
  rw [tot_1359]
  rfl

theorem tot_1360 : totient 1360 = 512 := by
  have heq : (2^4 * (5 * (17)) : ℕ) = 1360 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^4) = 2^3 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_17]
  try omega

theorem v3_phi_1360 : v3_fast (totient 1360) 100 = v3_phi_list.getD 1360 0 := by
  rw [tot_1360]
  rfl

theorem tot_1361 : totient 1361 = 1360 := by
  have h : totient 1361 = 1361 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1361 : v3_fast (totient 1361) 100 = v3_phi_list.getD 1361 0 := by
  rw [tot_1361]
  rfl

theorem tot_1362 : totient 1362 = 452 := by
  have heq : (2 * (3 * (227)) : ℕ) = 1362 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_227 : totient 227 = 227 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_227]
  try omega

theorem v3_phi_1362 : v3_fast (totient 1362) 100 = v3_phi_list.getD 1362 0 := by
  rw [tot_1362]
  rfl

theorem tot_1363 : totient 1363 = 1288 := by
  have heq : (29 * (47) : ℕ) = 1363 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_29 : totient 29 = 29 - 1 := totient_prime (by norm_num)
  have hp_47 : totient 47 = 47 - 1 := totient_prime (by norm_num)
  rw [hp_29, hp_47]
  try omega

theorem v3_phi_1363 : v3_fast (totient 1363) 100 = v3_phi_list.getD 1363 0 := by
  rw [tot_1363]
  rfl

theorem tot_1364 : totient 1364 = 600 := by
  have heq : (2^2 * (11 * (31)) : ℕ) = 1364 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  have hp_31 : totient 31 = 31 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_11, hp_31]
  try omega

theorem v3_phi_1364 : v3_fast (totient 1364) 100 = v3_phi_list.getD 1364 0 := by
  rw [tot_1364]
  rfl

theorem tot_1365 : totient 1365 = 576 := by
  have heq : (3 * (5 * (7 * (13))) : ℕ) = 1365 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_5, hp_7, hp_13]
  try omega

theorem v3_phi_1365 : v3_fast (totient 1365) 100 = v3_phi_list.getD 1365 0 := by
  rw [tot_1365]
  rfl

theorem tot_1366 : totient 1366 = 682 := by
  have heq : (2 * (683) : ℕ) = 1366 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_683 : totient 683 = 683 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_683]
  try omega

theorem v3_phi_1366 : v3_fast (totient 1366) 100 = v3_phi_list.getD 1366 0 := by
  rw [tot_1366]
  rfl

theorem tot_1367 : totient 1367 = 1366 := by
  have h : totient 1367 = 1367 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1367 : v3_fast (totient 1367) 100 = v3_phi_list.getD 1367 0 := by
  rw [tot_1367]
  rfl

theorem tot_1368 : totient 1368 = 432 := by
  have heq : (2^3 * (3^2 * (19)) : ℕ) = 1368 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^3) = 2^2 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_3 : totient (3^2) = 3^1 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_19 : totient 19 = 19 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_19]
  try omega

theorem v3_phi_1368 : v3_fast (totient 1368) 100 = v3_phi_list.getD 1368 0 := by
  rw [tot_1368]
  rfl

theorem tot_1369 : totient 1369 = 1332 := by
  have h : totient (37^2) = 37^1 * (37 - 1) := totient_prime_pow (by norm_num) (by decide)
  have heq : (37^2 : ℕ) = 1369 := by decide
  rw [← heq]
  rw [h]
  try omega

theorem v3_phi_1369 : v3_fast (totient 1369) 100 = v3_phi_list.getD 1369 0 := by
  rw [tot_1369]
  rfl

theorem tot_1370 : totient 1370 = 544 := by
  have heq : (2 * (5 * (137)) : ℕ) = 1370 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_5 : totient 5 = 5 - 1 := totient_prime (by norm_num)
  have hp_137 : totient 137 = 137 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_5, hp_137]
  try omega

theorem v3_phi_1370 : v3_fast (totient 1370) 100 = v3_phi_list.getD 1370 0 := by
  rw [tot_1370]
  rfl

theorem tot_1371 : totient 1371 = 912 := by
  have heq : (3 * (457) : ℕ) = 1371 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_457 : totient 457 = 457 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_457]
  try omega

theorem v3_phi_1371 : v3_fast (totient 1371) 100 = v3_phi_list.getD 1371 0 := by
  rw [tot_1371]
  rfl

theorem tot_1372 : totient 1372 = 588 := by
  have heq : (2^2 * (7^3) : ℕ) = 1372 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^2) = 2^1 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_7 : totient (7^3) = 7^2 * (7 - 1) := totient_prime_pow (by norm_num) (by decide)
  rw [hp_2, hp_7]
  try omega

theorem v3_phi_1372 : v3_fast (totient 1372) 100 = v3_phi_list.getD 1372 0 := by
  rw [tot_1372]
  rfl

theorem tot_1373 : totient 1373 = 1372 := by
  have h : totient 1373 = 1373 - 1 := totient_prime (by norm_num)
  rw [h]
  try omega

theorem v3_phi_1373 : v3_fast (totient 1373) 100 = v3_phi_list.getD 1373 0 := by
  rw [tot_1373]
  rfl

theorem tot_1374 : totient 1374 = 456 := by
  have heq : (2 * (3 * (229)) : ℕ) = 1374 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_3 : totient 3 = 3 - 1 := totient_prime (by norm_num)
  have hp_229 : totient 229 = 229 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_3, hp_229]
  try omega

theorem v3_phi_1374 : v3_fast (totient 1374) 100 = v3_phi_list.getD 1374 0 := by
  rw [tot_1374]
  rfl

theorem tot_1375 : totient 1375 = 1000 := by
  have heq : (5^3 * (11) : ℕ) = 1375 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_5 : totient (5^3) = 5^2 * (5 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_11 : totient 11 = 11 - 1 := totient_prime (by norm_num)
  rw [hp_5, hp_11]
  try omega

theorem v3_phi_1375 : v3_fast (totient 1375) 100 = v3_phi_list.getD 1375 0 := by
  rw [tot_1375]
  rfl

theorem tot_1376 : totient 1376 = 672 := by
  have heq : (2^5 * (43) : ℕ) = 1376 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_2 : totient (2^5) = 2^4 * (2 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_43 : totient 43 = 43 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_43]
  try omega

theorem v3_phi_1376 : v3_fast (totient 1376) 100 = v3_phi_list.getD 1376 0 := by
  rw [tot_1376]
  rfl

theorem tot_1377 : totient 1377 = 864 := by
  have heq : (3^4 * (17) : ℕ) = 1377 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_3 : totient (3^4) = 3^3 * (3 - 1) := totient_prime_pow (by norm_num) (by decide)
  have hp_17 : totient 17 = 17 - 1 := totient_prime (by norm_num)
  rw [hp_3, hp_17]
  try omega

theorem v3_phi_1377 : v3_fast (totient 1377) 100 = v3_phi_list.getD 1377 0 := by
  rw [tot_1377]
  rfl

theorem tot_1378 : totient 1378 = 624 := by
  have heq : (2 * (13 * (53)) : ℕ) = 1378 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  rw [totient_mul (by decide)]
  have hp_2 : totient 2 = 2 - 1 := totient_prime (by norm_num)
  have hp_13 : totient 13 = 13 - 1 := totient_prime (by norm_num)
  have hp_53 : totient 53 = 53 - 1 := totient_prime (by norm_num)
  rw [hp_2, hp_13, hp_53]
  try omega

theorem v3_phi_1378 : v3_fast (totient 1378) 100 = v3_phi_list.getD 1378 0 := by
  rw [tot_1378]
  rfl

theorem tot_1379 : totient 1379 = 1176 := by
  have heq : (7 * (197) : ℕ) = 1379 := by decide
  rw [← heq]
  rw [totient_mul (by decide)]
  have hp_7 : totient 7 = 7 - 1 := totient_prime (by norm_num)
  have hp_197 : totient 197 = 197 - 1 := totient_prime (by norm_num)
  rw [hp_7, hp_197]
  try omega

theorem v3_phi_1379 : v3_fast (totient 1379) 100 = v3_phi_list.getD 1379 0 := by
  rw [tot_1379]
  rfl

theorem v3_phi_eq_list_2 (k : ℕ) (hk1 : 920 ≤ k) (hk2 : k ≤ 1379) : v3_fast k.totient 100 = v3_phi_list.getD k 0 := by
  have heq : k = 920 + (k - 920) := by omega
  revert hk1 hk2
  rw [heq]
  match k - 920 with
  | 0 => intro _ _; exact v3_phi_920
  | 1 => intro _ _; exact v3_phi_921
  | 2 => intro _ _; exact v3_phi_922
  | 3 => intro _ _; exact v3_phi_923
  | 4 => intro _ _; exact v3_phi_924
  | 5 => intro _ _; exact v3_phi_925
  | 6 => intro _ _; exact v3_phi_926
  | 7 => intro _ _; exact v3_phi_927
  | 8 => intro _ _; exact v3_phi_928
  | 9 => intro _ _; exact v3_phi_929
  | 10 => intro _ _; exact v3_phi_930
  | 11 => intro _ _; exact v3_phi_931
  | 12 => intro _ _; exact v3_phi_932
  | 13 => intro _ _; exact v3_phi_933
  | 14 => intro _ _; exact v3_phi_934
  | 15 => intro _ _; exact v3_phi_935
  | 16 => intro _ _; exact v3_phi_936
  | 17 => intro _ _; exact v3_phi_937
  | 18 => intro _ _; exact v3_phi_938
  | 19 => intro _ _; exact v3_phi_939
  | 20 => intro _ _; exact v3_phi_940
  | 21 => intro _ _; exact v3_phi_941
  | 22 => intro _ _; exact v3_phi_942
  | 23 => intro _ _; exact v3_phi_943
  | 24 => intro _ _; exact v3_phi_944
  | 25 => intro _ _; exact v3_phi_945
  | 26 => intro _ _; exact v3_phi_946
  | 27 => intro _ _; exact v3_phi_947
  | 28 => intro _ _; exact v3_phi_948
  | 29 => intro _ _; exact v3_phi_949
  | 30 => intro _ _; exact v3_phi_950
  | 31 => intro _ _; exact v3_phi_951
  | 32 => intro _ _; exact v3_phi_952
  | 33 => intro _ _; exact v3_phi_953
  | 34 => intro _ _; exact v3_phi_954
  | 35 => intro _ _; exact v3_phi_955
  | 36 => intro _ _; exact v3_phi_956
  | 37 => intro _ _; exact v3_phi_957
  | 38 => intro _ _; exact v3_phi_958
  | 39 => intro _ _; exact v3_phi_959
  | 40 => intro _ _; exact v3_phi_960
  | 41 => intro _ _; exact v3_phi_961
  | 42 => intro _ _; exact v3_phi_962
  | 43 => intro _ _; exact v3_phi_963
  | 44 => intro _ _; exact v3_phi_964
  | 45 => intro _ _; exact v3_phi_965
  | 46 => intro _ _; exact v3_phi_966
  | 47 => intro _ _; exact v3_phi_967
  | 48 => intro _ _; exact v3_phi_968
  | 49 => intro _ _; exact v3_phi_969
  | 50 => intro _ _; exact v3_phi_970
  | 51 => intro _ _; exact v3_phi_971
  | 52 => intro _ _; exact v3_phi_972
  | 53 => intro _ _; exact v3_phi_973
  | 54 => intro _ _; exact v3_phi_974
  | 55 => intro _ _; exact v3_phi_975
  | 56 => intro _ _; exact v3_phi_976
  | 57 => intro _ _; exact v3_phi_977
  | 58 => intro _ _; exact v3_phi_978
  | 59 => intro _ _; exact v3_phi_979
  | 60 => intro _ _; exact v3_phi_980
  | 61 => intro _ _; exact v3_phi_981
  | 62 => intro _ _; exact v3_phi_982
  | 63 => intro _ _; exact v3_phi_983
  | 64 => intro _ _; exact v3_phi_984
  | 65 => intro _ _; exact v3_phi_985
  | 66 => intro _ _; exact v3_phi_986
  | 67 => intro _ _; exact v3_phi_987
  | 68 => intro _ _; exact v3_phi_988
  | 69 => intro _ _; exact v3_phi_989
  | 70 => intro _ _; exact v3_phi_990
  | 71 => intro _ _; exact v3_phi_991
  | 72 => intro _ _; exact v3_phi_992
  | 73 => intro _ _; exact v3_phi_993
  | 74 => intro _ _; exact v3_phi_994
  | 75 => intro _ _; exact v3_phi_995
  | 76 => intro _ _; exact v3_phi_996
  | 77 => intro _ _; exact v3_phi_997
  | 78 => intro _ _; exact v3_phi_998
  | 79 => intro _ _; exact v3_phi_999
  | 80 => intro _ _; exact v3_phi_1000
  | 81 => intro _ _; exact v3_phi_1001
  | 82 => intro _ _; exact v3_phi_1002
  | 83 => intro _ _; exact v3_phi_1003
  | 84 => intro _ _; exact v3_phi_1004
  | 85 => intro _ _; exact v3_phi_1005
  | 86 => intro _ _; exact v3_phi_1006
  | 87 => intro _ _; exact v3_phi_1007
  | 88 => intro _ _; exact v3_phi_1008
  | 89 => intro _ _; exact v3_phi_1009
  | 90 => intro _ _; exact v3_phi_1010
  | 91 => intro _ _; exact v3_phi_1011
  | 92 => intro _ _; exact v3_phi_1012
  | 93 => intro _ _; exact v3_phi_1013
  | 94 => intro _ _; exact v3_phi_1014
  | 95 => intro _ _; exact v3_phi_1015
  | 96 => intro _ _; exact v3_phi_1016
  | 97 => intro _ _; exact v3_phi_1017
  | 98 => intro _ _; exact v3_phi_1018
  | 99 => intro _ _; exact v3_phi_1019
  | 100 => intro _ _; exact v3_phi_1020
  | 101 => intro _ _; exact v3_phi_1021
  | 102 => intro _ _; exact v3_phi_1022
  | 103 => intro _ _; exact v3_phi_1023
  | 104 => intro _ _; exact v3_phi_1024
  | 105 => intro _ _; exact v3_phi_1025
  | 106 => intro _ _; exact v3_phi_1026
  | 107 => intro _ _; exact v3_phi_1027
  | 108 => intro _ _; exact v3_phi_1028
  | 109 => intro _ _; exact v3_phi_1029
  | 110 => intro _ _; exact v3_phi_1030
  | 111 => intro _ _; exact v3_phi_1031
  | 112 => intro _ _; exact v3_phi_1032
  | 113 => intro _ _; exact v3_phi_1033
  | 114 => intro _ _; exact v3_phi_1034
  | 115 => intro _ _; exact v3_phi_1035
  | 116 => intro _ _; exact v3_phi_1036
  | 117 => intro _ _; exact v3_phi_1037
  | 118 => intro _ _; exact v3_phi_1038
  | 119 => intro _ _; exact v3_phi_1039
  | 120 => intro _ _; exact v3_phi_1040
  | 121 => intro _ _; exact v3_phi_1041
  | 122 => intro _ _; exact v3_phi_1042
  | 123 => intro _ _; exact v3_phi_1043
  | 124 => intro _ _; exact v3_phi_1044
  | 125 => intro _ _; exact v3_phi_1045
  | 126 => intro _ _; exact v3_phi_1046
  | 127 => intro _ _; exact v3_phi_1047
  | 128 => intro _ _; exact v3_phi_1048
  | 129 => intro _ _; exact v3_phi_1049
  | 130 => intro _ _; exact v3_phi_1050
  | 131 => intro _ _; exact v3_phi_1051
  | 132 => intro _ _; exact v3_phi_1052
  | 133 => intro _ _; exact v3_phi_1053
  | 134 => intro _ _; exact v3_phi_1054
  | 135 => intro _ _; exact v3_phi_1055
  | 136 => intro _ _; exact v3_phi_1056
  | 137 => intro _ _; exact v3_phi_1057
  | 138 => intro _ _; exact v3_phi_1058
  | 139 => intro _ _; exact v3_phi_1059
  | 140 => intro _ _; exact v3_phi_1060
  | 141 => intro _ _; exact v3_phi_1061
  | 142 => intro _ _; exact v3_phi_1062
  | 143 => intro _ _; exact v3_phi_1063
  | 144 => intro _ _; exact v3_phi_1064
  | 145 => intro _ _; exact v3_phi_1065
  | 146 => intro _ _; exact v3_phi_1066
  | 147 => intro _ _; exact v3_phi_1067
  | 148 => intro _ _; exact v3_phi_1068
  | 149 => intro _ _; exact v3_phi_1069
  | 150 => intro _ _; exact v3_phi_1070
  | 151 => intro _ _; exact v3_phi_1071
  | 152 => intro _ _; exact v3_phi_1072
  | 153 => intro _ _; exact v3_phi_1073
  | 154 => intro _ _; exact v3_phi_1074
  | 155 => intro _ _; exact v3_phi_1075
  | 156 => intro _ _; exact v3_phi_1076
  | 157 => intro _ _; exact v3_phi_1077
  | 158 => intro _ _; exact v3_phi_1078
  | 159 => intro _ _; exact v3_phi_1079
  | 160 => intro _ _; exact v3_phi_1080
  | 161 => intro _ _; exact v3_phi_1081
  | 162 => intro _ _; exact v3_phi_1082
  | 163 => intro _ _; exact v3_phi_1083
  | 164 => intro _ _; exact v3_phi_1084
  | 165 => intro _ _; exact v3_phi_1085
  | 166 => intro _ _; exact v3_phi_1086
  | 167 => intro _ _; exact v3_phi_1087
  | 168 => intro _ _; exact v3_phi_1088
  | 169 => intro _ _; exact v3_phi_1089
  | 170 => intro _ _; exact v3_phi_1090
  | 171 => intro _ _; exact v3_phi_1091
  | 172 => intro _ _; exact v3_phi_1092
  | 173 => intro _ _; exact v3_phi_1093
  | 174 => intro _ _; exact v3_phi_1094
  | 175 => intro _ _; exact v3_phi_1095
  | 176 => intro _ _; exact v3_phi_1096
  | 177 => intro _ _; exact v3_phi_1097
  | 178 => intro _ _; exact v3_phi_1098
  | 179 => intro _ _; exact v3_phi_1099
  | 180 => intro _ _; exact v3_phi_1100
  | 181 => intro _ _; exact v3_phi_1101
  | 182 => intro _ _; exact v3_phi_1102
  | 183 => intro _ _; exact v3_phi_1103
  | 184 => intro _ _; exact v3_phi_1104
  | 185 => intro _ _; exact v3_phi_1105
  | 186 => intro _ _; exact v3_phi_1106
  | 187 => intro _ _; exact v3_phi_1107
  | 188 => intro _ _; exact v3_phi_1108
  | 189 => intro _ _; exact v3_phi_1109
  | 190 => intro _ _; exact v3_phi_1110
  | 191 => intro _ _; exact v3_phi_1111
  | 192 => intro _ _; exact v3_phi_1112
  | 193 => intro _ _; exact v3_phi_1113
  | 194 => intro _ _; exact v3_phi_1114
  | 195 => intro _ _; exact v3_phi_1115
  | 196 => intro _ _; exact v3_phi_1116
  | 197 => intro _ _; exact v3_phi_1117
  | 198 => intro _ _; exact v3_phi_1118
  | 199 => intro _ _; exact v3_phi_1119
  | 200 => intro _ _; exact v3_phi_1120
  | 201 => intro _ _; exact v3_phi_1121
  | 202 => intro _ _; exact v3_phi_1122
  | 203 => intro _ _; exact v3_phi_1123
  | 204 => intro _ _; exact v3_phi_1124
  | 205 => intro _ _; exact v3_phi_1125
  | 206 => intro _ _; exact v3_phi_1126
  | 207 => intro _ _; exact v3_phi_1127
  | 208 => intro _ _; exact v3_phi_1128
  | 209 => intro _ _; exact v3_phi_1129
  | 210 => intro _ _; exact v3_phi_1130
  | 211 => intro _ _; exact v3_phi_1131
  | 212 => intro _ _; exact v3_phi_1132
  | 213 => intro _ _; exact v3_phi_1133
  | 214 => intro _ _; exact v3_phi_1134
  | 215 => intro _ _; exact v3_phi_1135
  | 216 => intro _ _; exact v3_phi_1136
  | 217 => intro _ _; exact v3_phi_1137
  | 218 => intro _ _; exact v3_phi_1138
  | 219 => intro _ _; exact v3_phi_1139
  | 220 => intro _ _; exact v3_phi_1140
  | 221 => intro _ _; exact v3_phi_1141
  | 222 => intro _ _; exact v3_phi_1142
  | 223 => intro _ _; exact v3_phi_1143
  | 224 => intro _ _; exact v3_phi_1144
  | 225 => intro _ _; exact v3_phi_1145
  | 226 => intro _ _; exact v3_phi_1146
  | 227 => intro _ _; exact v3_phi_1147
  | 228 => intro _ _; exact v3_phi_1148
  | 229 => intro _ _; exact v3_phi_1149
  | 230 => intro _ _; exact v3_phi_1150
  | 231 => intro _ _; exact v3_phi_1151
  | 232 => intro _ _; exact v3_phi_1152
  | 233 => intro _ _; exact v3_phi_1153
  | 234 => intro _ _; exact v3_phi_1154
  | 235 => intro _ _; exact v3_phi_1155
  | 236 => intro _ _; exact v3_phi_1156
  | 237 => intro _ _; exact v3_phi_1157
  | 238 => intro _ _; exact v3_phi_1158
  | 239 => intro _ _; exact v3_phi_1159
  | 240 => intro _ _; exact v3_phi_1160
  | 241 => intro _ _; exact v3_phi_1161
  | 242 => intro _ _; exact v3_phi_1162
  | 243 => intro _ _; exact v3_phi_1163
  | 244 => intro _ _; exact v3_phi_1164
  | 245 => intro _ _; exact v3_phi_1165
  | 246 => intro _ _; exact v3_phi_1166
  | 247 => intro _ _; exact v3_phi_1167
  | 248 => intro _ _; exact v3_phi_1168
  | 249 => intro _ _; exact v3_phi_1169
  | 250 => intro _ _; exact v3_phi_1170
  | 251 => intro _ _; exact v3_phi_1171
  | 252 => intro _ _; exact v3_phi_1172
  | 253 => intro _ _; exact v3_phi_1173
  | 254 => intro _ _; exact v3_phi_1174
  | 255 => intro _ _; exact v3_phi_1175
  | 256 => intro _ _; exact v3_phi_1176
  | 257 => intro _ _; exact v3_phi_1177
  | 258 => intro _ _; exact v3_phi_1178
  | 259 => intro _ _; exact v3_phi_1179
  | 260 => intro _ _; exact v3_phi_1180
  | 261 => intro _ _; exact v3_phi_1181
  | 262 => intro _ _; exact v3_phi_1182
  | 263 => intro _ _; exact v3_phi_1183
  | 264 => intro _ _; exact v3_phi_1184
  | 265 => intro _ _; exact v3_phi_1185
  | 266 => intro _ _; exact v3_phi_1186
  | 267 => intro _ _; exact v3_phi_1187
  | 268 => intro _ _; exact v3_phi_1188
  | 269 => intro _ _; exact v3_phi_1189
  | 270 => intro _ _; exact v3_phi_1190
  | 271 => intro _ _; exact v3_phi_1191
  | 272 => intro _ _; exact v3_phi_1192
  | 273 => intro _ _; exact v3_phi_1193
  | 274 => intro _ _; exact v3_phi_1194
  | 275 => intro _ _; exact v3_phi_1195
  | 276 => intro _ _; exact v3_phi_1196
  | 277 => intro _ _; exact v3_phi_1197
  | 278 => intro _ _; exact v3_phi_1198
  | 279 => intro _ _; exact v3_phi_1199
  | 280 => intro _ _; exact v3_phi_1200
  | 281 => intro _ _; exact v3_phi_1201
  | 282 => intro _ _; exact v3_phi_1202
  | 283 => intro _ _; exact v3_phi_1203
  | 284 => intro _ _; exact v3_phi_1204
  | 285 => intro _ _; exact v3_phi_1205
  | 286 => intro _ _; exact v3_phi_1206
  | 287 => intro _ _; exact v3_phi_1207
  | 288 => intro _ _; exact v3_phi_1208
  | 289 => intro _ _; exact v3_phi_1209
  | 290 => intro _ _; exact v3_phi_1210
  | 291 => intro _ _; exact v3_phi_1211
  | 292 => intro _ _; exact v3_phi_1212
  | 293 => intro _ _; exact v3_phi_1213
  | 294 => intro _ _; exact v3_phi_1214
  | 295 => intro _ _; exact v3_phi_1215
  | 296 => intro _ _; exact v3_phi_1216
  | 297 => intro _ _; exact v3_phi_1217
  | 298 => intro _ _; exact v3_phi_1218
  | 299 => intro _ _; exact v3_phi_1219
  | 300 => intro _ _; exact v3_phi_1220
  | 301 => intro _ _; exact v3_phi_1221
  | 302 => intro _ _; exact v3_phi_1222
  | 303 => intro _ _; exact v3_phi_1223
  | 304 => intro _ _; exact v3_phi_1224
  | 305 => intro _ _; exact v3_phi_1225
  | 306 => intro _ _; exact v3_phi_1226
  | 307 => intro _ _; exact v3_phi_1227
  | 308 => intro _ _; exact v3_phi_1228
  | 309 => intro _ _; exact v3_phi_1229
  | 310 => intro _ _; exact v3_phi_1230
  | 311 => intro _ _; exact v3_phi_1231
  | 312 => intro _ _; exact v3_phi_1232
  | 313 => intro _ _; exact v3_phi_1233
  | 314 => intro _ _; exact v3_phi_1234
  | 315 => intro _ _; exact v3_phi_1235
  | 316 => intro _ _; exact v3_phi_1236
  | 317 => intro _ _; exact v3_phi_1237
  | 318 => intro _ _; exact v3_phi_1238
  | 319 => intro _ _; exact v3_phi_1239
  | 320 => intro _ _; exact v3_phi_1240
  | 321 => intro _ _; exact v3_phi_1241
  | 322 => intro _ _; exact v3_phi_1242
  | 323 => intro _ _; exact v3_phi_1243
  | 324 => intro _ _; exact v3_phi_1244
  | 325 => intro _ _; exact v3_phi_1245
  | 326 => intro _ _; exact v3_phi_1246
  | 327 => intro _ _; exact v3_phi_1247
  | 328 => intro _ _; exact v3_phi_1248
  | 329 => intro _ _; exact v3_phi_1249
  | 330 => intro _ _; exact v3_phi_1250
  | 331 => intro _ _; exact v3_phi_1251
  | 332 => intro _ _; exact v3_phi_1252
  | 333 => intro _ _; exact v3_phi_1253
  | 334 => intro _ _; exact v3_phi_1254
  | 335 => intro _ _; exact v3_phi_1255
  | 336 => intro _ _; exact v3_phi_1256
  | 337 => intro _ _; exact v3_phi_1257
  | 338 => intro _ _; exact v3_phi_1258
  | 339 => intro _ _; exact v3_phi_1259
  | 340 => intro _ _; exact v3_phi_1260
  | 341 => intro _ _; exact v3_phi_1261
  | 342 => intro _ _; exact v3_phi_1262
  | 343 => intro _ _; exact v3_phi_1263
  | 344 => intro _ _; exact v3_phi_1264
  | 345 => intro _ _; exact v3_phi_1265
  | 346 => intro _ _; exact v3_phi_1266
  | 347 => intro _ _; exact v3_phi_1267
  | 348 => intro _ _; exact v3_phi_1268
  | 349 => intro _ _; exact v3_phi_1269
  | 350 => intro _ _; exact v3_phi_1270
  | 351 => intro _ _; exact v3_phi_1271
  | 352 => intro _ _; exact v3_phi_1272
  | 353 => intro _ _; exact v3_phi_1273
  | 354 => intro _ _; exact v3_phi_1274
  | 355 => intro _ _; exact v3_phi_1275
  | 356 => intro _ _; exact v3_phi_1276
  | 357 => intro _ _; exact v3_phi_1277
  | 358 => intro _ _; exact v3_phi_1278
  | 359 => intro _ _; exact v3_phi_1279
  | 360 => intro _ _; exact v3_phi_1280
  | 361 => intro _ _; exact v3_phi_1281
  | 362 => intro _ _; exact v3_phi_1282
  | 363 => intro _ _; exact v3_phi_1283
  | 364 => intro _ _; exact v3_phi_1284
  | 365 => intro _ _; exact v3_phi_1285
  | 366 => intro _ _; exact v3_phi_1286
  | 367 => intro _ _; exact v3_phi_1287
  | 368 => intro _ _; exact v3_phi_1288
  | 369 => intro _ _; exact v3_phi_1289
  | 370 => intro _ _; exact v3_phi_1290
  | 371 => intro _ _; exact v3_phi_1291
  | 372 => intro _ _; exact v3_phi_1292
  | 373 => intro _ _; exact v3_phi_1293
  | 374 => intro _ _; exact v3_phi_1294
  | 375 => intro _ _; exact v3_phi_1295
  | 376 => intro _ _; exact v3_phi_1296
  | 377 => intro _ _; exact v3_phi_1297
  | 378 => intro _ _; exact v3_phi_1298
  | 379 => intro _ _; exact v3_phi_1299
  | 380 => intro _ _; exact v3_phi_1300
  | 381 => intro _ _; exact v3_phi_1301
  | 382 => intro _ _; exact v3_phi_1302
  | 383 => intro _ _; exact v3_phi_1303
  | 384 => intro _ _; exact v3_phi_1304
  | 385 => intro _ _; exact v3_phi_1305
  | 386 => intro _ _; exact v3_phi_1306
  | 387 => intro _ _; exact v3_phi_1307
  | 388 => intro _ _; exact v3_phi_1308
  | 389 => intro _ _; exact v3_phi_1309
  | 390 => intro _ _; exact v3_phi_1310
  | 391 => intro _ _; exact v3_phi_1311
  | 392 => intro _ _; exact v3_phi_1312
  | 393 => intro _ _; exact v3_phi_1313
  | 394 => intro _ _; exact v3_phi_1314
  | 395 => intro _ _; exact v3_phi_1315
  | 396 => intro _ _; exact v3_phi_1316
  | 397 => intro _ _; exact v3_phi_1317
  | 398 => intro _ _; exact v3_phi_1318
  | 399 => intro _ _; exact v3_phi_1319
  | 400 => intro _ _; exact v3_phi_1320
  | 401 => intro _ _; exact v3_phi_1321
  | 402 => intro _ _; exact v3_phi_1322
  | 403 => intro _ _; exact v3_phi_1323
  | 404 => intro _ _; exact v3_phi_1324
  | 405 => intro _ _; exact v3_phi_1325
  | 406 => intro _ _; exact v3_phi_1326
  | 407 => intro _ _; exact v3_phi_1327
  | 408 => intro _ _; exact v3_phi_1328
  | 409 => intro _ _; exact v3_phi_1329
  | 410 => intro _ _; exact v3_phi_1330
  | 411 => intro _ _; exact v3_phi_1331
  | 412 => intro _ _; exact v3_phi_1332
  | 413 => intro _ _; exact v3_phi_1333
  | 414 => intro _ _; exact v3_phi_1334
  | 415 => intro _ _; exact v3_phi_1335
  | 416 => intro _ _; exact v3_phi_1336
  | 417 => intro _ _; exact v3_phi_1337
  | 418 => intro _ _; exact v3_phi_1338
  | 419 => intro _ _; exact v3_phi_1339
  | 420 => intro _ _; exact v3_phi_1340
  | 421 => intro _ _; exact v3_phi_1341
  | 422 => intro _ _; exact v3_phi_1342
  | 423 => intro _ _; exact v3_phi_1343
  | 424 => intro _ _; exact v3_phi_1344
  | 425 => intro _ _; exact v3_phi_1345
  | 426 => intro _ _; exact v3_phi_1346
  | 427 => intro _ _; exact v3_phi_1347
  | 428 => intro _ _; exact v3_phi_1348
  | 429 => intro _ _; exact v3_phi_1349
  | 430 => intro _ _; exact v3_phi_1350
  | 431 => intro _ _; exact v3_phi_1351
  | 432 => intro _ _; exact v3_phi_1352
  | 433 => intro _ _; exact v3_phi_1353
  | 434 => intro _ _; exact v3_phi_1354
  | 435 => intro _ _; exact v3_phi_1355
  | 436 => intro _ _; exact v3_phi_1356
  | 437 => intro _ _; exact v3_phi_1357
  | 438 => intro _ _; exact v3_phi_1358
  | 439 => intro _ _; exact v3_phi_1359
  | 440 => intro _ _; exact v3_phi_1360
  | 441 => intro _ _; exact v3_phi_1361
  | 442 => intro _ _; exact v3_phi_1362
  | 443 => intro _ _; exact v3_phi_1363
  | 444 => intro _ _; exact v3_phi_1364
  | 445 => intro _ _; exact v3_phi_1365
  | 446 => intro _ _; exact v3_phi_1366
  | 447 => intro _ _; exact v3_phi_1367
  | 448 => intro _ _; exact v3_phi_1368
  | 449 => intro _ _; exact v3_phi_1369
  | 450 => intro _ _; exact v3_phi_1370
  | 451 => intro _ _; exact v3_phi_1371
  | 452 => intro _ _; exact v3_phi_1372
  | 453 => intro _ _; exact v3_phi_1373
  | 454 => intro _ _; exact v3_phi_1374
  | 455 => intro _ _; exact v3_phi_1375
  | 456 => intro _ _; exact v3_phi_1376
  | 457 => intro _ _; exact v3_phi_1377
  | 458 => intro _ _; exact v3_phi_1378
  | 459 => intro _ _; exact v3_phi_1379
  | x + 460 => intro h1 h2; omega

