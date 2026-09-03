import Submission.Sieve729Data
import Submission.Sieve729Masks

/-! Kernel-checked closure identities for a block of barrier rows. -/
namespace Erdos952Investigation.Sieve729
open BitsetBarrier
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

lemma row_checked_1000 :
    (dilate period (rowNeighbors rows 1000) &&& bits 1000) ||| rows 1000 = rows 1000 := by
  decide +kernel

lemma row_checked_1001 :
    (dilate period (rowNeighbors rows 1001) &&& bits 1001) ||| rows 1001 = rows 1001 := by
  decide +kernel

lemma row_checked_1002 :
    (dilate period (rowNeighbors rows 1002) &&& bits 1002) ||| rows 1002 = rows 1002 := by
  decide +kernel

lemma row_checked_1003 :
    (dilate period (rowNeighbors rows 1003) &&& bits 1003) ||| rows 1003 = rows 1003 := by
  decide +kernel

lemma row_checked_1004 :
    (dilate period (rowNeighbors rows 1004) &&& bits 1004) ||| rows 1004 = rows 1004 := by
  decide +kernel

lemma row_checked_1005 :
    (dilate period (rowNeighbors rows 1005) &&& bits 1005) ||| rows 1005 = rows 1005 := by
  decide +kernel

lemma row_checked_1006 :
    (dilate period (rowNeighbors rows 1006) &&& bits 1006) ||| rows 1006 = rows 1006 := by
  decide +kernel

lemma row_checked_1007 :
    (dilate period (rowNeighbors rows 1007) &&& bits 1007) ||| rows 1007 = rows 1007 := by
  decide +kernel

lemma row_checked_1008 :
    (dilate period (rowNeighbors rows 1008) &&& bits 1008) ||| rows 1008 = rows 1008 := by
  decide +kernel

lemma row_checked_1009 :
    (dilate period (rowNeighbors rows 1009) &&& bits 1009) ||| rows 1009 = rows 1009 := by
  decide +kernel

lemma row_checked_1010 :
    (dilate period (rowNeighbors rows 1010) &&& bits 1010) ||| rows 1010 = rows 1010 := by
  decide +kernel

lemma row_checked_1011 :
    (dilate period (rowNeighbors rows 1011) &&& bits 1011) ||| rows 1011 = rows 1011 := by
  decide +kernel

lemma row_checked_1012 :
    (dilate period (rowNeighbors rows 1012) &&& bits 1012) ||| rows 1012 = rows 1012 := by
  decide +kernel

lemma row_checked_1013 :
    (dilate period (rowNeighbors rows 1013) &&& bits 1013) ||| rows 1013 = rows 1013 := by
  decide +kernel

lemma row_checked_1014 :
    (dilate period (rowNeighbors rows 1014) &&& bits 1014) ||| rows 1014 = rows 1014 := by
  decide +kernel

lemma row_checked_1015 :
    (dilate period (rowNeighbors rows 1015) &&& bits 1015) ||| rows 1015 = rows 1015 := by
  decide +kernel

lemma row_checked_1016 :
    (dilate period (rowNeighbors rows 1016) &&& bits 1016) ||| rows 1016 = rows 1016 := by
  decide +kernel

lemma row_checked_1017 :
    (dilate period (rowNeighbors rows 1017) &&& bits 1017) ||| rows 1017 = rows 1017 := by
  decide +kernel

lemma row_checked_1018 :
    (dilate period (rowNeighbors rows 1018) &&& bits 1018) ||| rows 1018 = rows 1018 := by
  decide +kernel

lemma row_checked_1019 :
    (dilate period (rowNeighbors rows 1019) &&& bits 1019) ||| rows 1019 = rows 1019 := by
  decide +kernel

lemma row_checked_1020 :
    (dilate period (rowNeighbors rows 1020) &&& bits 1020) ||| rows 1020 = rows 1020 := by
  decide +kernel

lemma row_checked_1021 :
    (dilate period (rowNeighbors rows 1021) &&& bits 1021) ||| rows 1021 = rows 1021 := by
  decide +kernel

lemma row_checked_1022 :
    (dilate period (rowNeighbors rows 1022) &&& bits 1022) ||| rows 1022 = rows 1022 := by
  decide +kernel

lemma row_checked_1023 :
    (dilate period (rowNeighbors rows 1023) &&& bits 1023) ||| rows 1023 = rows 1023 := by
  decide +kernel

lemma row_checked_1024 :
    (dilate period (rowNeighbors rows 1024) &&& bits 1024) ||| rows 1024 = rows 1024 := by
  decide +kernel

lemma row_checked_1025 :
    (dilate period (rowNeighbors rows 1025) &&& bits 1025) ||| rows 1025 = rows 1025 := by
  decide +kernel

lemma row_checked_1026 :
    (dilate period (rowNeighbors rows 1026) &&& bits 1026) ||| rows 1026 = rows 1026 := by
  decide +kernel

lemma row_checked_1027 :
    (dilate period (rowNeighbors rows 1027) &&& bits 1027) ||| rows 1027 = rows 1027 := by
  decide +kernel

lemma row_checked_1028 :
    (dilate period (rowNeighbors rows 1028) &&& bits 1028) ||| rows 1028 = rows 1028 := by
  decide +kernel

lemma row_checked_1029 :
    (dilate period (rowNeighbors rows 1029) &&& bits 1029) ||| rows 1029 = rows 1029 := by
  decide +kernel

lemma row_checked_1030 :
    (dilate period (rowNeighbors rows 1030) &&& bits 1030) ||| rows 1030 = rows 1030 := by
  decide +kernel

lemma row_checked_1031 :
    (dilate period (rowNeighbors rows 1031) &&& bits 1031) ||| rows 1031 = rows 1031 := by
  decide +kernel

lemma row_checked_1032 :
    (dilate period (rowNeighbors rows 1032) &&& bits 1032) ||| rows 1032 = rows 1032 := by
  decide +kernel

lemma row_checked_1033 :
    (dilate period (rowNeighbors rows 1033) &&& bits 1033) ||| rows 1033 = rows 1033 := by
  decide +kernel

lemma row_checked_1034 :
    (dilate period (rowNeighbors rows 1034) &&& bits 1034) ||| rows 1034 = rows 1034 := by
  decide +kernel

lemma row_checked_1035 :
    (dilate period (rowNeighbors rows 1035) &&& bits 1035) ||| rows 1035 = rows 1035 := by
  decide +kernel

lemma row_checked_1036 :
    (dilate period (rowNeighbors rows 1036) &&& bits 1036) ||| rows 1036 = rows 1036 := by
  decide +kernel

lemma row_checked_1037 :
    (dilate period (rowNeighbors rows 1037) &&& bits 1037) ||| rows 1037 = rows 1037 := by
  decide +kernel

lemma row_checked_1038 :
    (dilate period (rowNeighbors rows 1038) &&& bits 1038) ||| rows 1038 = rows 1038 := by
  decide +kernel

lemma row_checked_1039 :
    (dilate period (rowNeighbors rows 1039) &&& bits 1039) ||| rows 1039 = rows 1039 := by
  decide +kernel

lemma row_checked_1040 :
    (dilate period (rowNeighbors rows 1040) &&& bits 1040) ||| rows 1040 = rows 1040 := by
  decide +kernel

lemma row_checked_1041 :
    (dilate period (rowNeighbors rows 1041) &&& bits 1041) ||| rows 1041 = rows 1041 := by
  decide +kernel

lemma row_checked_1042 :
    (dilate period (rowNeighbors rows 1042) &&& bits 1042) ||| rows 1042 = rows 1042 := by
  decide +kernel

lemma row_checked_1043 :
    (dilate period (rowNeighbors rows 1043) &&& bits 1043) ||| rows 1043 = rows 1043 := by
  decide +kernel

lemma row_checked_1044 :
    (dilate period (rowNeighbors rows 1044) &&& bits 1044) ||| rows 1044 = rows 1044 := by
  decide +kernel

lemma row_checked_1045 :
    (dilate period (rowNeighbors rows 1045) &&& bits 1045) ||| rows 1045 = rows 1045 := by
  decide +kernel

lemma row_checked_1046 :
    (dilate period (rowNeighbors rows 1046) &&& bits 1046) ||| rows 1046 = rows 1046 := by
  decide +kernel

lemma row_checked_1047 :
    (dilate period (rowNeighbors rows 1047) &&& bits 1047) ||| rows 1047 = rows 1047 := by
  decide +kernel

lemma row_checked_1048 :
    (dilate period (rowNeighbors rows 1048) &&& bits 1048) ||| rows 1048 = rows 1048 := by
  decide +kernel

lemma row_checked_1049 :
    (dilate period (rowNeighbors rows 1049) &&& bits 1049) ||| rows 1049 = rows 1049 := by
  decide +kernel

lemma row_checked_1050 :
    (dilate period (rowNeighbors rows 1050) &&& bits 1050) ||| rows 1050 = rows 1050 := by
  decide +kernel

lemma row_checked_1051 :
    (dilate period (rowNeighbors rows 1051) &&& bits 1051) ||| rows 1051 = rows 1051 := by
  decide +kernel

lemma row_checked_1052 :
    (dilate period (rowNeighbors rows 1052) &&& bits 1052) ||| rows 1052 = rows 1052 := by
  decide +kernel

lemma row_checked_1053 :
    (dilate period (rowNeighbors rows 1053) &&& bits 1053) ||| rows 1053 = rows 1053 := by
  decide +kernel

lemma row_checked_1054 :
    (dilate period (rowNeighbors rows 1054) &&& bits 1054) ||| rows 1054 = rows 1054 := by
  decide +kernel

lemma row_checked_1055 :
    (dilate period (rowNeighbors rows 1055) &&& bits 1055) ||| rows 1055 = rows 1055 := by
  decide +kernel

lemma row_checked_1056 :
    (dilate period (rowNeighbors rows 1056) &&& bits 1056) ||| rows 1056 = rows 1056 := by
  decide +kernel

lemma row_checked_1057 :
    (dilate period (rowNeighbors rows 1057) &&& bits 1057) ||| rows 1057 = rows 1057 := by
  decide +kernel

lemma row_checked_1058 :
    (dilate period (rowNeighbors rows 1058) &&& bits 1058) ||| rows 1058 = rows 1058 := by
  decide +kernel

lemma row_checked_1059 :
    (dilate period (rowNeighbors rows 1059) &&& bits 1059) ||| rows 1059 = rows 1059 := by
  decide +kernel

lemma row_checked_1060 :
    (dilate period (rowNeighbors rows 1060) &&& bits 1060) ||| rows 1060 = rows 1060 := by
  decide +kernel

lemma row_checked_1061 :
    (dilate period (rowNeighbors rows 1061) &&& bits 1061) ||| rows 1061 = rows 1061 := by
  decide +kernel

lemma row_checked_1062 :
    (dilate period (rowNeighbors rows 1062) &&& bits 1062) ||| rows 1062 = rows 1062 := by
  decide +kernel

lemma row_checked_1063 :
    (dilate period (rowNeighbors rows 1063) &&& bits 1063) ||| rows 1063 = rows 1063 := by
  decide +kernel

lemma row_checked_1064 :
    (dilate period (rowNeighbors rows 1064) &&& bits 1064) ||| rows 1064 = rows 1064 := by
  decide +kernel

lemma row_checked_1065 :
    (dilate period (rowNeighbors rows 1065) &&& bits 1065) ||| rows 1065 = rows 1065 := by
  decide +kernel

lemma row_checked_1066 :
    (dilate period (rowNeighbors rows 1066) &&& bits 1066) ||| rows 1066 = rows 1066 := by
  decide +kernel

lemma row_checked_1067 :
    (dilate period (rowNeighbors rows 1067) &&& bits 1067) ||| rows 1067 = rows 1067 := by
  decide +kernel

lemma row_checked_1068 :
    (dilate period (rowNeighbors rows 1068) &&& bits 1068) ||| rows 1068 = rows 1068 := by
  decide +kernel

lemma row_checked_1069 :
    (dilate period (rowNeighbors rows 1069) &&& bits 1069) ||| rows 1069 = rows 1069 := by
  decide +kernel

lemma row_checked_1070 :
    (dilate period (rowNeighbors rows 1070) &&& bits 1070) ||| rows 1070 = rows 1070 := by
  decide +kernel

lemma row_checked_1071 :
    (dilate period (rowNeighbors rows 1071) &&& bits 1071) ||| rows 1071 = rows 1071 := by
  decide +kernel

lemma row_checked_1072 :
    (dilate period (rowNeighbors rows 1072) &&& bits 1072) ||| rows 1072 = rows 1072 := by
  decide +kernel

lemma row_checked_1073 :
    (dilate period (rowNeighbors rows 1073) &&& bits 1073) ||| rows 1073 = rows 1073 := by
  decide +kernel

lemma row_checked_1074 :
    (dilate period (rowNeighbors rows 1074) &&& bits 1074) ||| rows 1074 = rows 1074 := by
  decide +kernel

lemma row_checked_1075 :
    (dilate period (rowNeighbors rows 1075) &&& bits 1075) ||| rows 1075 = rows 1075 := by
  decide +kernel

lemma row_checked_1076 :
    (dilate period (rowNeighbors rows 1076) &&& bits 1076) ||| rows 1076 = rows 1076 := by
  decide +kernel

lemma row_checked_1077 :
    (dilate period (rowNeighbors rows 1077) &&& bits 1077) ||| rows 1077 = rows 1077 := by
  decide +kernel

lemma row_checked_1078 :
    (dilate period (rowNeighbors rows 1078) &&& bits 1078) ||| rows 1078 = rows 1078 := by
  decide +kernel

lemma row_checked_1079 :
    (dilate period (rowNeighbors rows 1079) &&& bits 1079) ||| rows 1079 = rows 1079 := by
  decide +kernel

lemma row_checked_1080 :
    (dilate period (rowNeighbors rows 1080) &&& bits 1080) ||| rows 1080 = rows 1080 := by
  decide +kernel

lemma row_checked_1081 :
    (dilate period (rowNeighbors rows 1081) &&& bits 1081) ||| rows 1081 = rows 1081 := by
  decide +kernel

lemma row_checked_1082 :
    (dilate period (rowNeighbors rows 1082) &&& bits 1082) ||| rows 1082 = rows 1082 := by
  decide +kernel

lemma row_checked_1083 :
    (dilate period (rowNeighbors rows 1083) &&& bits 1083) ||| rows 1083 = rows 1083 := by
  decide +kernel

lemma row_checked_1084 :
    (dilate period (rowNeighbors rows 1084) &&& bits 1084) ||| rows 1084 = rows 1084 := by
  decide +kernel

lemma row_checked_1085 :
    (dilate period (rowNeighbors rows 1085) &&& bits 1085) ||| rows 1085 = rows 1085 := by
  decide +kernel

lemma row_checked_1086 :
    (dilate period (rowNeighbors rows 1086) &&& bits 1086) ||| rows 1086 = rows 1086 := by
  decide +kernel

lemma row_checked_1087 :
    (dilate period (rowNeighbors rows 1087) &&& bits 1087) ||| rows 1087 = rows 1087 := by
  decide +kernel

lemma row_checked_1088 :
    (dilate period (rowNeighbors rows 1088) &&& bits 1088) ||| rows 1088 = rows 1088 := by
  decide +kernel

lemma row_checked_1089 :
    (dilate period (rowNeighbors rows 1089) &&& bits 1089) ||| rows 1089 = rows 1089 := by
  decide +kernel

lemma row_checked_1090 :
    (dilate period (rowNeighbors rows 1090) &&& bits 1090) ||| rows 1090 = rows 1090 := by
  decide +kernel

lemma row_checked_1091 :
    (dilate period (rowNeighbors rows 1091) &&& bits 1091) ||| rows 1091 = rows 1091 := by
  decide +kernel

lemma row_checked_1092 :
    (dilate period (rowNeighbors rows 1092) &&& bits 1092) ||| rows 1092 = rows 1092 := by
  decide +kernel

lemma row_checked_1093 :
    (dilate period (rowNeighbors rows 1093) &&& bits 1093) ||| rows 1093 = rows 1093 := by
  decide +kernel

lemma row_checked_1094 :
    (dilate period (rowNeighbors rows 1094) &&& bits 1094) ||| rows 1094 = rows 1094 := by
  decide +kernel

lemma row_checked_1095 :
    (dilate period (rowNeighbors rows 1095) &&& bits 1095) ||| rows 1095 = rows 1095 := by
  decide +kernel

lemma row_checked_1096 :
    (dilate period (rowNeighbors rows 1096) &&& bits 1096) ||| rows 1096 = rows 1096 := by
  decide +kernel

lemma row_checked_1097 :
    (dilate period (rowNeighbors rows 1097) &&& bits 1097) ||| rows 1097 = rows 1097 := by
  decide +kernel

lemma row_checked_1098 :
    (dilate period (rowNeighbors rows 1098) &&& bits 1098) ||| rows 1098 = rows 1098 := by
  decide +kernel

lemma row_checked_1099 :
    (dilate period (rowNeighbors rows 1099) &&& bits 1099) ||| rows 1099 = rows 1099 := by
  decide +kernel

lemma block_checked_10 (i : Fin 100) :
    (dilate period (rowNeighbors rows (1000 + i.val)) &&& bits (1000 + i.val)) |||
      rows (1000 + i.val) = rows (1000 + i.val) := by
  fin_cases i
  · exact row_checked_1000
  · exact row_checked_1001
  · exact row_checked_1002
  · exact row_checked_1003
  · exact row_checked_1004
  · exact row_checked_1005
  · exact row_checked_1006
  · exact row_checked_1007
  · exact row_checked_1008
  · exact row_checked_1009
  · exact row_checked_1010
  · exact row_checked_1011
  · exact row_checked_1012
  · exact row_checked_1013
  · exact row_checked_1014
  · exact row_checked_1015
  · exact row_checked_1016
  · exact row_checked_1017
  · exact row_checked_1018
  · exact row_checked_1019
  · exact row_checked_1020
  · exact row_checked_1021
  · exact row_checked_1022
  · exact row_checked_1023
  · exact row_checked_1024
  · exact row_checked_1025
  · exact row_checked_1026
  · exact row_checked_1027
  · exact row_checked_1028
  · exact row_checked_1029
  · exact row_checked_1030
  · exact row_checked_1031
  · exact row_checked_1032
  · exact row_checked_1033
  · exact row_checked_1034
  · exact row_checked_1035
  · exact row_checked_1036
  · exact row_checked_1037
  · exact row_checked_1038
  · exact row_checked_1039
  · exact row_checked_1040
  · exact row_checked_1041
  · exact row_checked_1042
  · exact row_checked_1043
  · exact row_checked_1044
  · exact row_checked_1045
  · exact row_checked_1046
  · exact row_checked_1047
  · exact row_checked_1048
  · exact row_checked_1049
  · exact row_checked_1050
  · exact row_checked_1051
  · exact row_checked_1052
  · exact row_checked_1053
  · exact row_checked_1054
  · exact row_checked_1055
  · exact row_checked_1056
  · exact row_checked_1057
  · exact row_checked_1058
  · exact row_checked_1059
  · exact row_checked_1060
  · exact row_checked_1061
  · exact row_checked_1062
  · exact row_checked_1063
  · exact row_checked_1064
  · exact row_checked_1065
  · exact row_checked_1066
  · exact row_checked_1067
  · exact row_checked_1068
  · exact row_checked_1069
  · exact row_checked_1070
  · exact row_checked_1071
  · exact row_checked_1072
  · exact row_checked_1073
  · exact row_checked_1074
  · exact row_checked_1075
  · exact row_checked_1076
  · exact row_checked_1077
  · exact row_checked_1078
  · exact row_checked_1079
  · exact row_checked_1080
  · exact row_checked_1081
  · exact row_checked_1082
  · exact row_checked_1083
  · exact row_checked_1084
  · exact row_checked_1085
  · exact row_checked_1086
  · exact row_checked_1087
  · exact row_checked_1088
  · exact row_checked_1089
  · exact row_checked_1090
  · exact row_checked_1091
  · exact row_checked_1092
  · exact row_checked_1093
  · exact row_checked_1094
  · exact row_checked_1095
  · exact row_checked_1096
  · exact row_checked_1097
  · exact row_checked_1098
  · exact row_checked_1099

#print axioms row_checked_1099

end Erdos952Investigation.Sieve729
