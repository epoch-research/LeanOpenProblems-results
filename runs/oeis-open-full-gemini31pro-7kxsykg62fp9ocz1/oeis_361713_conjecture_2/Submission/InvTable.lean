import Mathlib
import Submission.InvFiles.Inv_0
import Submission.InvFiles.Inv_1
import Submission.InvFiles.Inv_2
import Submission.InvFiles.Inv_3
import Submission.InvFiles.Inv_4
import Submission.InvFiles.Inv_5
import Submission.InvFiles.Inv_6
import Submission.InvFiles.Inv_7
import Submission.InvFiles.Inv_8
import Submission.InvFiles.Inv_9
import Submission.InvFiles.Inv_10
import Submission.InvFiles.Inv_11
import Submission.InvFiles.Inv_12
import Submission.InvFiles.Inv_13
import Submission.InvFiles.Inv_14
import Submission.InvFiles.Inv_15
import Submission.InvFiles.Inv_16
import Submission.InvFiles.Inv_17
import Submission.InvFiles.Inv_18
import Submission.InvFiles.Inv_19
import Submission.InvFiles.Inv_20
import Submission.InvFiles.Inv_21
import Submission.InvFiles.Inv_22
import Submission.InvFiles.Inv_23
import Submission.InvFiles.Inv_24
import Submission.InvFiles.Inv_25
import Submission.InvFiles.Inv_26
import Submission.InvFiles.Inv_27
import Submission.InvFiles.Inv_28
import Submission.InvFiles.Inv_29
import Submission.InvFiles.Inv_30
import Submission.InvFiles.Inv_31
import Submission.InvFiles.Inv_32
import Submission.InvFiles.Inv_33
import Submission.InvFiles.Inv_34
import Submission.InvFiles.Inv_35
import Submission.InvFiles.Inv_36
import Submission.InvFiles.Inv_37
import Submission.InvFiles.Inv_38
import Submission.InvFiles.Inv_39
import Submission.InvFiles.Inv_40
import Submission.InvFiles.Inv_41
import Submission.InvFiles.Inv_42
import Submission.InvFiles.Inv_43
import Submission.InvFiles.Inv_44
import Submission.InvFiles.Inv_45
import Submission.InvFiles.Inv_46
import Submission.InvFiles.Inv_47
import Submission.InvFiles.Inv_48
import Submission.InvFiles.Inv_49
import Submission.InvFiles.Inv_50
import Submission.InvFiles.Inv_51
import Submission.InvFiles.Inv_52
import Submission.InvFiles.Inv_53
import Submission.InvFiles.Inv_54
import Submission.InvFiles.Inv_55
import Submission.InvFiles.Inv_56
import Submission.InvFiles.Inv_57
import Submission.InvFiles.Inv_58
import Submission.InvFiles.Inv_59
import Submission.InvFiles.Inv_60
import Submission.InvFiles.Inv_61
import Submission.InvFiles.Inv_62
import Submission.InvFiles.Inv_63
import Submission.InvFiles.Inv_64
import Submission.InvFiles.Inv_65
import Submission.InvFiles.Inv_66
import Submission.InvFiles.Inv_67
import Submission.InvFiles.Inv_68
import Submission.InvFiles.Inv_69
import Submission.InvFiles.Inv_70
import Submission.InvFiles.Inv_71
import Submission.InvFiles.Inv_72
import Submission.InvFiles.Inv_73
import Submission.InvFiles.Inv_74
import Submission.InvFiles.Inv_75
import Submission.InvFiles.Inv_76
import Submission.InvFiles.Inv_77
import Submission.InvFiles.Inv_78
import Submission.InvFiles.Inv_79
import Submission.InvFiles.Inv_80
import Submission.InvFiles.Inv_81
import Submission.InvFiles.Inv_82
import Submission.InvFiles.Inv_83
import Submission.InvFiles.Inv_84
import Submission.InvFiles.Inv_85
import Submission.InvFiles.Inv_86
import Submission.InvFiles.Inv_87
import Submission.InvFiles.Inv_88
import Submission.InvFiles.Inv_89
import Submission.InvFiles.Inv_90
import Submission.InvFiles.Inv_91
import Submission.InvFiles.Inv_92
import Submission.InvFiles.Inv_93
import Submission.InvFiles.Inv_94
import Submission.InvFiles.Inv_95
import Submission.InvFiles.Inv_96
import Submission.InvFiles.Inv_97
import Submission.InvFiles.Inv_98

def modinv_table (x : ℕ) : ℕ :=
  if x <= 59733 then
  if x <= 29866 then
  if x <= 15530 then
  if x <= 8362 then
  if x <= 4778 then
  if x <= 2389 then
  if x <= 1194 then
  inv_chunk_0 x
else
  inv_chunk_1 x
else
  if x <= 3583 then
  inv_chunk_2 x
else
  inv_chunk_3 x
else
  if x <= 7167 then
  if x <= 5973 then
  inv_chunk_4 x
else
  inv_chunk_5 x
else
  inv_chunk_6 x
else
  if x <= 11946 then
  if x <= 10751 then
  if x <= 9557 then
  inv_chunk_7 x
else
  inv_chunk_8 x
else
  inv_chunk_9 x
else
  if x <= 14335 then
  if x <= 13141 then
  inv_chunk_10 x
else
  inv_chunk_11 x
else
  inv_chunk_12 x
else
  if x <= 22698 then
  if x <= 19114 then
  if x <= 17919 then
  if x <= 16725 then
  inv_chunk_13 x
else
  inv_chunk_14 x
else
  inv_chunk_15 x
else
  if x <= 21503 then
  if x <= 20309 then
  inv_chunk_16 x
else
  inv_chunk_17 x
else
  inv_chunk_18 x
else
  if x <= 26282 then
  if x <= 25087 then
  if x <= 23893 then
  inv_chunk_19 x
else
  inv_chunk_20 x
else
  inv_chunk_21 x
else
  if x <= 28671 then
  if x <= 27477 then
  inv_chunk_22 x
else
  inv_chunk_23 x
else
  inv_chunk_24 x
else
  if x <= 45397 then
  if x <= 38229 then
  if x <= 34645 then
  if x <= 32255 then
  if x <= 31061 then
  inv_chunk_25 x
else
  inv_chunk_26 x
else
  if x <= 33450 then
  inv_chunk_27 x
else
  inv_chunk_28 x
else
  if x <= 37034 then
  if x <= 35839 then
  inv_chunk_29 x
else
  inv_chunk_30 x
else
  inv_chunk_31 x
else
  if x <= 41813 then
  if x <= 40618 then
  if x <= 39423 then
  inv_chunk_32 x
else
  inv_chunk_33 x
else
  inv_chunk_34 x
else
  if x <= 44202 then
  if x <= 43007 then
  inv_chunk_35 x
else
  inv_chunk_36 x
else
  inv_chunk_37 x
else
  if x <= 52565 then
  if x <= 48981 then
  if x <= 47786 then
  if x <= 46591 then
  inv_chunk_38 x
else
  inv_chunk_39 x
else
  inv_chunk_40 x
else
  if x <= 51370 then
  if x <= 50175 then
  inv_chunk_41 x
else
  inv_chunk_42 x
else
  inv_chunk_43 x
else
  if x <= 56149 then
  if x <= 54954 then
  if x <= 53759 then
  inv_chunk_44 x
else
  inv_chunk_45 x
else
  inv_chunk_46 x
else
  if x <= 58538 then
  if x <= 57343 then
  inv_chunk_47 x
else
  inv_chunk_48 x
else
  inv_chunk_49 x
else
  if x <= 89599 then
  if x <= 75263 then
  if x <= 68095 then
  if x <= 64511 then
  if x <= 62122 then
  if x <= 60927 then
  inv_chunk_50 x
else
  inv_chunk_51 x
else
  if x <= 63317 then
  inv_chunk_52 x
else
  inv_chunk_53 x
else
  if x <= 66901 then
  if x <= 65706 then
  inv_chunk_54 x
else
  inv_chunk_55 x
else
  inv_chunk_56 x
else
  if x <= 71679 then
  if x <= 70485 then
  if x <= 69290 then
  inv_chunk_57 x
else
  inv_chunk_58 x
else
  inv_chunk_59 x
else
  if x <= 74069 then
  if x <= 72874 then
  inv_chunk_60 x
else
  inv_chunk_61 x
else
  inv_chunk_62 x
else
  if x <= 82431 then
  if x <= 78847 then
  if x <= 77653 then
  if x <= 76458 then
  inv_chunk_63 x
else
  inv_chunk_64 x
else
  inv_chunk_65 x
else
  if x <= 81237 then
  if x <= 80042 then
  inv_chunk_66 x
else
  inv_chunk_67 x
else
  inv_chunk_68 x
else
  if x <= 86015 then
  if x <= 84821 then
  if x <= 83626 then
  inv_chunk_69 x
else
  inv_chunk_70 x
else
  inv_chunk_71 x
else
  if x <= 88405 then
  if x <= 87210 then
  inv_chunk_72 x
else
  inv_chunk_73 x
else
  inv_chunk_74 x
else
  if x <= 103935 then
  if x <= 96767 then
  if x <= 93183 then
  if x <= 91989 then
  if x <= 90794 then
  inv_chunk_75 x
else
  inv_chunk_76 x
else
  inv_chunk_77 x
else
  if x <= 95573 then
  if x <= 94378 then
  inv_chunk_78 x
else
  inv_chunk_79 x
else
  inv_chunk_80 x
else
  if x <= 100351 then
  if x <= 99157 then
  if x <= 97962 then
  inv_chunk_81 x
else
  inv_chunk_82 x
else
  inv_chunk_83 x
else
  if x <= 102741 then
  if x <= 101546 then
  inv_chunk_84 x
else
  inv_chunk_85 x
else
  inv_chunk_86 x
else
  if x <= 111103 then
  if x <= 107519 then
  if x <= 106325 then
  if x <= 105130 then
  inv_chunk_87 x
else
  inv_chunk_88 x
else
  inv_chunk_89 x
else
  if x <= 109909 then
  if x <= 108714 then
  inv_chunk_90 x
else
  inv_chunk_91 x
else
  inv_chunk_92 x
else
  if x <= 114687 then
  if x <= 113493 then
  if x <= 112298 then
  inv_chunk_93 x
else
  inv_chunk_94 x
else
  inv_chunk_95 x
else
  if x <= 117077 then
  if x <= 115882 then
  inv_chunk_96 x
else
  inv_chunk_97 x
else
  inv_chunk_98 x
