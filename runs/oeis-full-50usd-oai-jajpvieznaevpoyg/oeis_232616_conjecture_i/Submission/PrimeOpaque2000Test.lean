import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

opaque prime_block_0 : 303 ≤ Nat.count (fun k => Nat.Prime (0 + k)) 2000 := by
  let L : List Nat := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733,1741,1747,1753,1759,1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877,1879,1889,1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (0 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 303 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_1 : 247 ≤ Nat.count (fun k => Nat.Prime (2000 + k)) 2000 := by
  let L : List Nat := [3,11,17,27,29,39,53,63,69,81,83,87,89,99,111,113,129,131,137,141,143,153,161,179,203,207,213,221,237,239,243,251,267,269,273,281,287,293,297,309,311,333,339,341,347,351,357,371,377,381,383,389,393,399,411,417,423,437,441,447,459,467,473,477,503,521,531,539,543,549,551,557,579,591,593,609,617,621,633,647,657,659,663,671,677,683,687,689,693,699,707,711,713,719,729,731,741,749,753,767,777,789,791,797,801,803,819,833,837,843,851,857,861,879,887,897,903,909,917,927,939,953,957,963,969,971,999,1001,1011,1019,1023,1037,1041,1049,1061,1067,1079,1083,1089,1109,1119,1121,1137,1163,1167,1169,1181,1187,1191,1203,1209,1217,1221,1229,1251,1253,1257,1259,1271,1299,1301,1307,1313,1319,1323,1329,1331,1343,1347,1359,1361,1371,1373,1389,1391,1407,1413,1433,1449,1457,1461,1463,1467,1469,1491,1499,1511,1517,1527,1529,1533,1539,1541,1547,1557,1559,1571,1581,1583,1593,1607,1613,1617,1623,1631,1637,1643,1659,1671,1673,1677,1691,1697,1701,1709,1719,1727,1733,1739,1761,1767,1769,1779,1793,1797,1803,1821,1823,1833,1847,1851,1853,1863,1877,1881,1889,1907,1911,1917,1919,1923,1929,1931,1943,1947,1967,1989]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (2000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 247 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_2 : 233 ≤ Nat.count (fun k => Nat.Prime (4000 + k)) 2000 := by
  let L : List Nat := [1,3,7,13,19,21,27,49,51,57,73,79,91,93,99,111,127,129,133,139,153,157,159,177,201,211,217,219,229,231,241,243,253,259,261,271,273,283,289,297,327,337,339,349,357,363,373,391,397,409,421,423,441,447,451,457,463,481,483,493,507,513,517,519,523,547,549,561,567,583,591,597,603,621,637,639,643,649,651,657,663,673,679,691,703,721,723,729,733,751,759,783,787,789,793,799,801,813,817,831,861,871,877,889,903,909,919,931,933,937,943,951,957,967,969,973,987,993,999,1003,1009,1011,1021,1023,1039,1051,1059,1077,1081,1087,1099,1101,1107,1113,1119,1147,1153,1167,1171,1179,1189,1197,1209,1227,1231,1233,1237,1261,1273,1279,1281,1297,1303,1309,1323,1333,1347,1351,1381,1387,1393,1399,1407,1413,1417,1419,1431,1437,1441,1443,1449,1471,1477,1479,1483,1501,1503,1507,1519,1521,1527,1531,1557,1563,1569,1573,1581,1591,1623,1639,1641,1647,1651,1653,1657,1659,1669,1683,1689,1693,1701,1711,1717,1737,1741,1743,1749,1779,1783,1791,1801,1807,1813,1821,1827,1839,1843,1849,1851,1857,1861,1867,1869,1879,1881,1897,1903,1923,1927,1939,1953,1981,1987]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (4000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 233 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_3 : 224 ≤ Nat.count (fun k => Nat.Prime (6000 + k)) 2000 := by
  let L : List Nat := [7,11,29,37,43,47,53,67,73,79,89,91,101,113,121,131,133,143,151,163,173,197,199,203,211,217,221,229,247,257,263,269,271,277,287,299,301,311,317,323,329,337,343,353,359,361,367,373,379,389,397,421,427,449,451,469,473,481,491,521,529,547,551,553,563,569,571,577,581,599,607,619,637,653,659,661,673,679,689,691,701,703,709,719,733,737,761,763,779,781,791,793,803,823,827,829,833,841,857,863,869,871,883,899,907,911,917,947,949,959,961,967,971,977,983,991,997,1001,1013,1019,1027,1039,1043,1057,1069,1079,1103,1109,1121,1127,1129,1151,1159,1177,1187,1193,1207,1211,1213,1219,1229,1237,1243,1247,1253,1283,1297,1307,1309,1321,1331,1333,1349,1351,1369,1393,1411,1417,1433,1451,1457,1459,1477,1481,1487,1489,1499,1507,1517,1523,1529,1537,1541,1547,1549,1559,1561,1573,1577,1583,1589,1591,1603,1607,1621,1639,1643,1649,1669,1673,1681,1687,1691,1699,1703,1717,1723,1727,1741,1753,1757,1759,1789,1793,1817,1823,1829,1841,1853,1867,1873,1877,1879,1883,1901,1907,1919,1927,1933,1937,1949,1951,1963,1993]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (6000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 224 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_4 : 222 ≤ Nat.count (fun k => Nat.Prime (8000 + k)) 2000 := by
  let L : List Nat := [9,11,17,39,53,59,69,81,87,89,93,101,111,117,123,147,161,167,171,179,191,209,219,221,231,233,237,243,263,269,273,287,291,293,297,311,317,329,353,363,369,377,387,389,419,423,429,431,443,447,461,467,501,513,521,527,537,539,543,563,573,581,597,599,609,623,627,629,641,647,663,669,677,681,689,693,699,707,713,719,731,737,741,747,753,761,779,783,803,807,819,821,831,837,839,849,861,863,867,887,893,923,929,933,941,951,963,969,971,999,1001,1007,1011,1013,1029,1041,1043,1049,1059,1067,1091,1103,1109,1127,1133,1137,1151,1157,1161,1173,1181,1187,1199,1203,1209,1221,1227,1239,1241,1257,1277,1281,1283,1293,1311,1319,1323,1337,1341,1343,1349,1371,1377,1391,1397,1403,1413,1419,1421,1431,1433,1437,1439,1461,1463,1467,1473,1479,1491,1497,1511,1521,1533,1539,1547,1551,1587,1601,1613,1619,1623,1629,1631,1643,1649,1661,1677,1679,1689,1697,1719,1721,1733,1739,1743,1749,1767,1769,1781,1787,1791,1803,1811,1817,1829,1833,1839,1851,1857,1859,1871,1883,1887,1901,1907,1923,1929,1931,1941,1949,1967,1973]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (8000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 222 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_5 : 209 ≤ Nat.count (fun k => Nat.Prime (10000 + k)) 2000 := by
  let L : List Nat := [7,9,37,39,61,67,69,79,91,93,99,103,111,133,139,141,151,159,163,169,177,181,193,211,223,243,247,253,259,267,271,273,289,301,303,313,321,331,333,337,343,357,369,391,399,427,429,433,453,457,459,463,477,487,499,501,513,529,531,559,567,589,597,601,607,613,627,631,639,651,657,663,667,687,691,709,711,723,729,733,739,753,771,781,789,799,831,837,847,853,859,861,867,883,889,891,903,909,937,939,949,957,973,979,987,993,1003,1027,1047,1057,1059,1069,1071,1083,1087,1093,1113,1117,1119,1131,1149,1159,1161,1171,1173,1177,1197,1213,1239,1243,1251,1257,1261,1273,1279,1287,1299,1311,1317,1321,1329,1351,1353,1369,1383,1393,1399,1411,1423,1437,1443,1447,1467,1471,1483,1489,1491,1497,1503,1519,1527,1549,1551,1579,1587,1593,1597,1617,1621,1633,1657,1677,1681,1689,1699,1701,1717,1719,1731,1743,1777,1779,1783,1789,1801,1807,1813,1821,1827,1831,1833,1839,1863,1867,1887,1897,1903,1909,1923,1927,1933,1939,1941,1953,1959,1969,1971,1981,1987]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (10000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 209 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_6 : 214 ≤ Nat.count (fun k => Nat.Prime (12000 + k)) 2000 := by
  let L : List Nat := [7,11,37,41,43,49,71,73,97,101,107,109,113,119,143,149,157,161,163,197,203,211,227,239,241,251,253,263,269,277,281,289,301,323,329,343,347,373,377,379,391,401,409,413,421,433,437,451,457,473,479,487,491,497,503,511,517,527,539,541,547,553,569,577,583,589,601,611,613,619,637,641,647,653,659,671,689,697,703,713,721,739,743,757,763,781,791,799,809,821,823,829,841,853,889,893,899,907,911,917,919,923,941,953,959,967,973,979,983,1001,1003,1007,1009,1033,1037,1043,1049,1063,1093,1099,1103,1109,1121,1127,1147,1151,1159,1163,1171,1177,1183,1187,1217,1219,1229,1241,1249,1259,1267,1291,1297,1309,1313,1327,1331,1337,1339,1367,1381,1397,1399,1411,1417,1421,1441,1451,1457,1463,1469,1477,1487,1499,1513,1523,1537,1553,1567,1577,1591,1597,1613,1619,1627,1633,1649,1669,1679,1681,1687,1691,1693,1697,1709,1711,1721,1723,1729,1751,1757,1759,1763,1781,1789,1799,1807,1829,1831,1841,1859,1873,1877,1879,1883,1901,1903,1907,1913,1921,1931,1933,1963,1967,1997,1999]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (12000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 214 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_7 : 210 ≤ Nat.count (fun k => Nat.Prime (14000 + k)) 2000 := by
  let L : List Nat := [9,11,29,33,51,57,71,81,83,87,107,143,149,153,159,173,177,197,207,221,243,249,251,281,293,303,321,323,327,341,347,369,387,389,401,407,411,419,423,431,437,447,449,461,479,489,503,519,533,537,543,549,551,557,561,563,591,593,621,627,629,633,639,653,657,669,683,699,713,717,723,731,737,741,747,753,759,767,771,779,783,797,813,821,827,831,843,851,867,869,879,887,891,897,923,929,939,947,951,957,969,983,1013,1017,1031,1053,1061,1073,1077,1083,1091,1101,1107,1121,1131,1137,1139,1149,1161,1173,1187,1193,1199,1217,1227,1233,1241,1259,1263,1269,1271,1277,1287,1289,1299,1307,1313,1319,1329,1331,1349,1359,1361,1373,1377,1383,1391,1401,1413,1427,1439,1443,1451,1461,1467,1473,1493,1497,1511,1527,1541,1551,1559,1569,1581,1583,1601,1607,1619,1629,1641,1643,1647,1649,1661,1667,1671,1679,1683,1727,1731,1733,1737,1739,1749,1761,1767,1773,1787,1791,1797,1803,1809,1817,1823,1859,1877,1881,1887,1889,1901,1907,1913,1919,1923,1937,1959,1971,1973,1991]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (14000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 210 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_8 : 202 ≤ Nat.count (fun k => Nat.Prime (16000 + k)) 2000 := by
  let L : List Nat := [1,7,33,57,61,63,67,69,73,87,91,97,103,111,127,139,141,183,187,189,193,217,223,229,231,249,253,267,273,301,319,333,339,349,361,363,369,381,411,417,421,427,433,447,451,453,477,481,487,493,519,529,547,553,561,567,573,603,607,619,631,633,649,651,657,661,673,691,693,699,703,729,741,747,759,763,787,811,823,829,831,843,871,879,883,889,901,903,921,927,931,937,943,963,979,981,987,993,1011,1021,1027,1029,1033,1041,1047,1053,1077,1093,1099,1107,1117,1123,1137,1159,1167,1183,1189,1191,1203,1207,1209,1231,1239,1257,1291,1293,1299,1317,1321,1327,1333,1341,1351,1359,1377,1383,1387,1389,1393,1401,1417,1419,1431,1443,1449,1467,1471,1477,1483,1489,1491,1497,1509,1519,1539,1551,1569,1573,1579,1581,1597,1599,1609,1623,1627,1657,1659,1669,1681,1683,1707,1713,1729,1737,1747,1749,1761,1783,1789,1791,1807,1827,1837,1839,1851,1863,1881,1891,1903,1909,1911,1921,1923,1929,1939,1957,1959,1971,1977,1981,1987,1989]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (16000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 202 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_9 : 198 ≤ Nat.count (fun k => Nat.Prime (18000 + k)) 2000 := by
  let L : List Nat := [13,41,43,47,49,59,61,77,89,97,119,121,127,131,133,143,149,169,181,191,199,211,217,223,229,233,251,253,257,269,287,289,301,307,311,313,329,341,353,367,371,379,397,401,413,427,433,439,443,451,457,461,481,493,503,517,521,523,539,541,553,583,587,593,617,637,661,671,679,691,701,713,719,731,743,749,757,773,787,793,797,803,839,859,869,899,911,913,917,919,947,959,973,979,1001,1009,1013,1031,1037,1051,1069,1073,1079,1081,1087,1121,1139,1141,1157,1163,1181,1183,1207,1211,1213,1219,1231,1237,1249,1259,1267,1273,1289,1301,1309,1319,1333,1373,1379,1381,1387,1391,1403,1417,1421,1423,1427,1429,1433,1441,1447,1457,1463,1469,1471,1477,1483,1489,1501,1507,1531,1541,1543,1553,1559,1571,1577,1583,1597,1603,1609,1661,1681,1687,1697,1699,1709,1717,1727,1739,1751,1753,1759,1763,1777,1793,1801,1813,1819,1841,1843,1853,1861,1867,1889,1891,1913,1919,1927,1937,1949,1961,1963,1973,1979,1991,1993,1997]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (18000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 198 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_10 : 202 ≤ Nat.count (fun k => Nat.Prime (20000 + k)) 2000 := by
  let L : List Nat := [11,21,23,29,47,51,63,71,89,101,107,113,117,123,129,143,147,149,161,173,177,183,201,219,231,233,249,261,269,287,297,323,327,333,341,347,353,357,359,369,389,393,399,407,411,431,441,443,477,479,483,507,509,521,533,543,549,551,563,593,599,611,627,639,641,663,681,693,707,717,719,731,743,747,749,753,759,771,773,789,807,809,849,857,873,879,887,897,899,903,921,929,939,947,959,963,981,983,1001,1011,1013,1017,1019,1023,1031,1059,1061,1067,1089,1101,1107,1121,1139,1143,1149,1157,1163,1169,1179,1187,1191,1193,1211,1221,1227,1247,1269,1277,1283,1313,1317,1319,1323,1341,1347,1377,1379,1383,1391,1397,1401,1407,1419,1433,1467,1481,1487,1491,1493,1499,1503,1517,1521,1523,1529,1557,1559,1563,1569,1577,1587,1589,1599,1601,1611,1613,1617,1647,1649,1661,1673,1683,1701,1713,1727,1737,1739,1751,1757,1767,1773,1787,1799,1803,1817,1821,1839,1841,1851,1859,1863,1871,1881,1893,1911,1929,1937,1943,1961,1977,1991,1997]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (20000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 202 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_11 : 204 ≤ Nat.count (fun k => Nat.Prime (22000 + k)) 2000 := by
  let L : List Nat := [3,13,27,31,37,39,51,63,67,73,79,91,93,109,111,123,129,133,147,153,157,159,171,189,193,229,247,259,271,273,277,279,283,291,303,307,343,349,367,369,381,391,397,409,433,441,447,453,469,481,483,501,511,531,541,543,549,567,571,573,613,619,621,637,639,643,651,669,679,691,697,699,709,717,721,727,739,741,751,769,777,783,787,807,811,817,853,859,861,871,877,901,907,921,937,943,961,963,973,993,1003,1011,1017,1021,1027,1029,1039,1041,1053,1057,1059,1063,1071,1081,1087,1099,1117,1131,1143,1159,1167,1173,1189,1197,1201,1203,1209,1227,1251,1269,1279,1291,1293,1297,1311,1321,1327,1333,1339,1357,1369,1371,1399,1417,1431,1447,1459,1473,1497,1509,1531,1537,1539,1549,1557,1561,1563,1567,1581,1593,1599,1603,1609,1623,1627,1629,1633,1663,1669,1671,1677,1687,1689,1719,1741,1743,1747,1753,1761,1767,1773,1789,1801,1813,1819,1827,1831,1833,1857,1869,1873,1879,1887,1893,1899,1909,1911,1917,1929,1957,1971,1977,1981,1993]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (22000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 204 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_12 : 192 ≤ Nat.count (fun k => Nat.Prime (24000 + k)) 2000 := by
  let L : List Nat := [1,7,19,23,29,43,49,61,71,77,83,91,97,103,107,109,113,121,133,137,151,169,179,181,197,203,223,229,239,247,251,281,317,329,337,359,371,373,379,391,407,413,419,421,439,443,469,473,481,499,509,517,527,533,547,551,571,593,611,623,631,659,671,677,683,691,697,709,733,749,763,767,781,793,799,809,821,841,847,851,859,877,889,907,917,919,923,943,953,967,971,977,979,989,1013,1031,1033,1037,1057,1073,1087,1097,1111,1117,1121,1127,1147,1153,1163,1169,1171,1183,1189,1219,1229,1237,1243,1247,1253,1261,1301,1303,1307,1309,1321,1339,1343,1349,1357,1367,1373,1391,1409,1411,1423,1439,1447,1453,1457,1463,1469,1471,1523,1537,1541,1561,1577,1579,1583,1589,1601,1603,1609,1621,1633,1639,1643,1657,1667,1673,1679,1693,1703,1717,1733,1741,1747,1759,1763,1771,1793,1799,1801,1819,1841,1847,1849,1867,1873,1889,1903,1913,1919,1931,1933,1939,1943,1951,1969,1981,1997,1999]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (24000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 192 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_13 : 195 ≤ Nat.count (fun k => Nat.Prime (26000 + k)) 2000 := by
  let L : List Nat := [3,17,21,29,41,53,83,99,107,111,113,119,141,153,161,171,177,183,189,203,209,227,237,249,251,261,263,267,293,297,309,317,321,339,347,357,371,387,393,399,407,417,423,431,437,449,459,479,489,497,501,513,539,557,561,573,591,597,627,633,641,647,669,681,683,687,693,699,701,711,713,717,723,729,731,737,759,777,783,801,813,821,833,839,849,861,863,879,881,891,893,903,921,927,947,951,953,959,981,987,993,1011,1017,1031,1043,1059,1061,1067,1073,1077,1091,1103,1107,1109,1127,1143,1179,1191,1197,1211,1239,1241,1253,1259,1271,1277,1281,1283,1299,1329,1337,1361,1367,1397,1407,1409,1427,1431,1437,1449,1457,1479,1481,1487,1509,1527,1529,1539,1541,1551,1581,1583,1611,1617,1631,1647,1653,1673,1689,1691,1697,1701,1733,1737,1739,1743,1749,1751,1763,1767,1773,1779,1791,1793,1799,1803,1809,1817,1823,1827,1847,1851,1883,1893,1901,1917,1919,1941,1943,1947,1953,1961,1967,1983,1997]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (26000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 195 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_14 : 190 ≤ Nat.count (fun k => Nat.Prime (28000 + k)) 2000 := by
  let L : List Nat := [1,19,27,31,51,57,69,81,87,97,99,109,111,123,151,163,181,183,201,211,219,229,277,279,283,289,297,307,309,319,349,351,387,393,403,409,411,429,433,439,447,463,477,493,499,513,517,537,541,547,549,559,571,573,579,591,597,603,607,619,621,627,631,643,649,657,661,663,669,687,697,703,711,723,729,751,753,759,771,789,793,807,813,817,837,843,859,867,871,879,901,909,921,927,933,949,961,979,1009,1017,1021,1023,1027,1033,1059,1063,1077,1101,1123,1129,1131,1137,1147,1153,1167,1173,1179,1191,1201,1207,1209,1221,1231,1243,1251,1269,1287,1297,1303,1311,1327,1333,1339,1347,1363,1383,1387,1389,1399,1401,1411,1423,1429,1437,1443,1453,1473,1483,1501,1527,1531,1537,1567,1569,1573,1581,1587,1599,1611,1629,1633,1641,1663,1669,1671,1683,1717,1723,1741,1753,1759,1761,1789,1803,1819,1833,1837,1851,1863,1867,1873,1879,1881,1917,1921,1927,1947,1959,1983,1989]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (28000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 190 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_15 : 187 ≤ Nat.count (fun k => Nat.Prime (30000 + k)) 2000 := by
  let L : List Nat := [11,13,29,47,59,71,89,91,97,103,109,113,119,133,137,139,161,169,181,187,197,203,211,223,241,253,259,269,271,293,307,313,319,323,341,347,367,389,391,403,427,431,449,467,469,491,493,497,509,517,529,539,553,557,559,577,593,631,637,643,649,661,671,677,689,697,703,707,713,727,757,763,773,781,803,809,817,829,839,841,851,853,859,869,871,881,893,911,931,937,941,949,971,977,983,1013,1019,1033,1039,1051,1063,1069,1079,1081,1091,1121,1123,1139,1147,1151,1153,1159,1177,1181,1183,1189,1193,1219,1223,1231,1237,1247,1249,1253,1259,1267,1271,1277,1307,1319,1321,1327,1333,1337,1357,1379,1387,1391,1393,1397,1469,1477,1481,1489,1511,1513,1517,1531,1541,1543,1547,1567,1573,1583,1601,1607,1627,1643,1649,1657,1663,1667,1687,1699,1721,1723,1727,1729,1741,1751,1769,1771,1793,1799,1817,1847,1849,1859,1873,1883,1891,1907,1957,1963,1973,1981,1991]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (30000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 187 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_16 : 206 ≤ Nat.count (fun k => Nat.Prime (32000 + k)) 2000 := by
  let L : List Nat := [3,9,27,29,51,57,59,63,69,77,83,89,99,117,119,141,143,159,173,183,189,191,203,213,233,237,251,257,261,297,299,303,309,321,323,327,341,353,359,363,369,371,377,381,401,411,413,423,429,441,443,467,479,491,497,503,507,531,533,537,561,563,569,573,579,587,603,609,611,621,633,647,653,687,693,707,713,717,719,749,771,779,783,789,797,801,803,831,833,839,843,869,887,909,911,917,933,939,941,957,969,971,983,987,993,999,1013,1023,1029,1037,1049,1053,1071,1073,1083,1091,1107,1113,1119,1149,1151,1161,1179,1181,1191,1199,1203,1211,1223,1247,1287,1289,1301,1311,1317,1329,1331,1343,1347,1349,1353,1359,1377,1391,1403,1409,1413,1427,1457,1461,1469,1479,1487,1493,1503,1521,1529,1533,1547,1563,1569,1577,1581,1587,1589,1599,1601,1613,1617,1619,1623,1629,1637,1641,1647,1679,1703,1713,1721,1739,1749,1751,1757,1767,1769,1773,1791,1797,1809,1811,1827,1829,1851,1857,1863,1871,1889,1893,1911,1923,1931,1937,1941,1961,1967,1997]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (32000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 206 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_17 : 186 ≤ Nat.count (fun k => Nat.Prime (34000 + k)) 2000 := by
  let L : List Nat := [19,31,33,39,57,61,123,127,129,141,147,157,159,171,183,211,213,217,231,253,259,261,267,273,283,297,301,303,313,319,327,337,351,361,367,369,381,403,421,429,439,457,469,471,483,487,499,501,511,513,519,537,543,549,583,589,591,603,607,613,631,649,651,667,673,679,687,693,703,721,729,739,747,757,759,763,781,807,819,841,843,847,849,871,877,883,897,913,919,939,949,961,963,981,1023,1027,1051,1053,1059,1069,1081,1083,1089,1099,1107,1111,1117,1129,1141,1149,1153,1159,1171,1201,1221,1227,1251,1257,1267,1279,1281,1291,1311,1317,1323,1327,1339,1353,1363,1381,1393,1401,1407,1419,1423,1437,1447,1449,1461,1491,1507,1509,1521,1527,1531,1533,1537,1543,1569,1573,1591,1593,1597,1603,1617,1671,1677,1729,1731,1747,1753,1759,1771,1797,1801,1803,1809,1831,1837,1839,1851,1863,1869,1879,1897,1899,1911,1923,1933,1951,1963,1969,1977,1983,1993,1999]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (34000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 186 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_18 : 193 ≤ Nat.count (fun k => Nat.Prime (36000 + k)) 2000 := by
  let L : List Nat := [7,11,13,17,37,61,67,73,83,97,107,109,131,137,151,161,187,191,209,217,229,241,251,263,269,277,293,299,307,313,319,341,343,353,373,383,389,433,451,457,467,469,473,479,493,497,523,527,529,541,551,559,563,571,583,587,599,607,629,637,643,653,671,677,683,691,697,709,713,721,739,749,761,767,779,781,787,791,793,809,821,833,847,857,871,877,887,899,901,913,919,923,929,931,943,947,973,979,997,1003,1013,1019,1021,1039,1049,1057,1061,1087,1097,1117,1123,1139,1159,1171,1181,1189,1199,1201,1217,1223,1243,1253,1273,1277,1307,1309,1313,1321,1337,1339,1357,1361,1363,1369,1379,1397,1409,1423,1441,1447,1463,1483,1489,1493,1501,1507,1511,1517,1529,1537,1547,1549,1561,1567,1571,1573,1579,1589,1591,1607,1619,1633,1643,1649,1657,1663,1691,1693,1699,1717,1747,1781,1783,1799,1811,1813,1831,1847,1853,1861,1871,1879,1889,1897,1907,1951,1957,1963,1967,1987,1991,1993,1997]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (36000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 193 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_19 : 186 ≤ Nat.count (fun k => Nat.Prime (38000 + k)) 2000 := by
  let L : List Nat := [11,39,47,53,69,83,113,119,149,153,167,177,183,189,197,201,219,231,237,239,261,273,281,287,299,303,317,321,327,329,333,351,371,377,393,431,447,449,453,459,461,501,543,557,561,567,569,593,603,609,611,629,639,651,653,669,671,677,693,699,707,711,713,723,729,737,747,749,767,783,791,803,821,833,839,851,861,867,873,891,903,917,921,923,933,953,959,971,977,993,1019,1023,1041,1043,1047,1079,1089,1097,1103,1107,1113,1119,1133,1139,1157,1161,1163,1181,1191,1199,1209,1217,1227,1229,1233,1239,1241,1251,1293,1301,1313,1317,1323,1341,1343,1359,1367,1371,1373,1383,1397,1409,1419,1439,1443,1451,1461,1499,1503,1509,1511,1521,1541,1551,1563,1569,1581,1607,1619,1623,1631,1659,1667,1671,1679,1703,1709,1719,1727,1733,1749,1761,1769,1779,1791,1799,1821,1827,1829,1839,1841,1847,1857,1863,1869,1877,1883,1887,1901,1929,1937,1953,1971,1979,1983,1989]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (38000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 186 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_20 : 189 ≤ Nat.count (fun k => Nat.Prime (40000 + k)) 2000 := by
  let L : List Nat := [9,13,31,37,39,63,87,93,99,111,123,127,129,151,153,163,169,177,189,193,213,231,237,241,253,277,283,289,343,351,357,361,387,423,427,429,433,459,471,483,487,493,499,507,519,529,531,543,559,577,583,591,597,609,627,637,639,693,697,699,709,739,751,759,763,771,787,801,813,819,823,829,841,847,849,853,867,879,883,897,903,927,933,939,949,961,973,993,1011,1017,1023,1039,1047,1051,1057,1077,1081,1113,1117,1131,1141,1143,1149,1161,1177,1179,1183,1189,1201,1203,1213,1221,1227,1231,1233,1243,1257,1263,1269,1281,1299,1333,1341,1351,1357,1381,1387,1389,1399,1411,1413,1443,1453,1467,1479,1491,1507,1513,1519,1521,1539,1543,1549,1579,1593,1597,1603,1609,1611,1617,1621,1627,1641,1647,1651,1659,1669,1681,1687,1719,1729,1737,1759,1761,1771,1777,1801,1809,1813,1843,1849,1851,1863,1879,1887,1893,1897,1903,1911,1927,1941,1947,1953,1957,1959,1969,1981,1983,1999]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (40000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 189 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_21 : 187 ≤ Nat.count (fun k => Nat.Prime (42000 + k)) 2000 := by
  let L : List Nat := [13,17,19,23,43,61,71,73,83,89,101,131,139,157,169,179,181,187,193,197,209,221,223,227,239,257,281,283,293,299,307,323,331,337,349,359,373,379,391,397,403,407,409,433,437,443,451,457,461,463,467,473,487,491,499,509,533,557,569,571,577,589,611,641,643,649,667,677,683,689,697,701,703,709,719,727,737,743,751,767,773,787,793,797,821,829,839,841,853,859,863,899,901,923,929,937,943,953,961,967,979,989,1003,1013,1019,1037,1049,1051,1063,1067,1093,1103,1117,1133,1151,1159,1177,1189,1201,1207,1223,1237,1261,1271,1283,1291,1313,1319,1321,1331,1391,1397,1399,1403,1411,1427,1441,1451,1457,1481,1487,1499,1517,1541,1543,1573,1577,1579,1591,1597,1607,1609,1613,1627,1633,1649,1651,1661,1669,1691,1711,1717,1721,1753,1759,1777,1781,1783,1787,1789,1793,1801,1853,1867,1889,1891,1913,1933,1943,1951,1961,1963,1969,1973,1987,1991,1997]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (42000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 187 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_22 : 182 ≤ Nat.count (fun k => Nat.Prime (44000 + k)) 2000 := by
  let L : List Nat := [17,21,27,29,41,53,59,71,87,89,101,111,119,123,129,131,159,171,179,189,201,203,207,221,249,257,263,267,269,273,279,281,293,351,357,371,381,383,389,417,449,453,483,491,497,501,507,519,531,533,537,543,549,563,579,587,617,621,623,633,641,647,651,657,683,687,699,701,711,729,741,753,771,773,777,789,797,809,819,839,843,851,867,879,887,893,909,917,927,939,953,959,963,971,983,987,1007,1013,1053,1061,1077,1083,1119,1121,1127,1131,1137,1139,1161,1179,1181,1191,1197,1233,1247,1259,1263,1281,1289,1293,1307,1317,1319,1329,1337,1341,1343,1361,1377,1389,1403,1413,1427,1433,1439,1481,1491,1497,1503,1523,1533,1541,1553,1557,1569,1587,1589,1599,1613,1631,1641,1659,1667,1673,1677,1691,1697,1707,1737,1751,1757,1763,1767,1779,1817,1821,1823,1827,1833,1841,1853,1863,1869,1887,1893,1943,1949,1953,1959,1971,1979,1989]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (44000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 182 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_23 : 185 ≤ Nat.count (fun k => Nat.Prime (46000 + k)) 2000 := by
  let L : List Nat := [21,27,49,51,61,73,91,93,99,103,133,141,147,153,171,181,183,187,199,219,229,237,261,271,273,279,301,307,309,327,337,349,351,381,399,411,439,441,447,451,457,471,477,489,499,507,511,523,549,559,567,573,589,591,601,619,633,639,643,649,663,679,681,687,691,703,723,727,747,751,757,769,771,807,811,817,819,829,831,853,861,867,877,889,901,919,933,957,993,997,1017,1041,1051,1057,1059,1087,1093,1111,1119,1123,1129,1137,1143,1147,1149,1161,1189,1207,1221,1237,1251,1269,1279,1287,1293,1297,1303,1309,1317,1339,1351,1353,1363,1381,1387,1389,1407,1417,1419,1431,1441,1459,1491,1497,1501,1507,1513,1521,1527,1533,1543,1563,1569,1581,1591,1599,1609,1623,1629,1639,1653,1657,1659,1681,1699,1701,1711,1713,1717,1737,1741,1743,1777,1779,1791,1797,1807,1809,1819,1837,1843,1857,1869,1881,1903,1911,1917,1933,1939,1947,1951,1963,1969,1977,1981]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (46000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 185 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_24 : 187 ≤ Nat.count (fun k => Nat.Prime (48000 + k)) 2000 := by
  let L : List Nat := [17,23,29,49,73,79,91,109,119,121,131,157,163,179,187,193,197,221,239,247,259,271,281,299,311,313,337,341,353,371,383,397,407,409,413,437,449,463,473,479,481,487,491,497,523,527,533,539,541,563,571,589,593,611,619,623,647,649,661,673,677,679,731,733,751,757,761,767,779,781,787,799,809,817,821,823,847,857,859,869,871,883,889,907,947,953,973,989,991,1003,1009,1019,1031,1033,1037,1043,1057,1069,1081,1103,1109,1117,1121,1123,1139,1157,1169,1171,1177,1193,1199,1201,1207,1211,1223,1253,1261,1277,1279,1297,1307,1331,1333,1339,1363,1367,1369,1391,1393,1409,1411,1417,1429,1433,1451,1459,1463,1477,1481,1499,1523,1529,1531,1537,1547,1549,1559,1597,1603,1613,1627,1633,1639,1663,1667,1669,1681,1697,1711,1727,1739,1741,1747,1757,1783,1787,1789,1801,1807,1811,1823,1831,1843,1853,1871,1877,1891,1919,1921,1927,1937,1939,1943,1957,1991,1993,1999]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (48000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 187 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_25 : 186 ≤ Nat.count (fun k => Nat.Prime (50000 + k)) 2000 := by
  let L : List Nat := [21,23,33,47,51,53,69,77,87,93,101,111,119,123,129,131,147,153,159,177,207,221,227,231,261,263,273,287,291,311,321,329,333,341,359,363,377,383,387,411,417,423,441,459,461,497,503,513,527,539,543,549,551,581,587,591,593,599,627,647,651,671,683,707,723,741,753,767,773,777,789,821,833,839,849,857,867,873,891,893,909,923,929,951,957,969,971,989,993,1001,1031,1043,1047,1059,1061,1071,1109,1131,1133,1137,1151,1157,1169,1193,1197,1199,1203,1217,1229,1239,1241,1257,1263,1283,1287,1307,1329,1341,1343,1347,1349,1361,1383,1407,1413,1419,1421,1427,1431,1437,1439,1449,1461,1473,1479,1481,1487,1503,1511,1517,1521,1539,1551,1563,1577,1581,1593,1599,1607,1613,1631,1637,1647,1659,1673,1679,1683,1691,1713,1719,1721,1749,1767,1769,1787,1797,1803,1817,1827,1829,1839,1853,1859,1869,1871,1893,1899,1907,1913,1929,1941,1949,1971,1973,1977,1991]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (50000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 186 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_26 : 181 ≤ Nat.count (fun k => Nat.Prime (52000 + k)) 2000 := by
  let L : List Nat := [9,21,27,51,57,67,69,81,103,121,127,147,153,163,177,181,183,189,201,223,237,249,253,259,267,289,291,301,313,321,361,363,369,379,387,391,433,453,457,489,501,511,517,529,541,543,553,561,567,571,579,583,609,627,631,639,667,673,691,697,709,711,721,727,733,747,757,769,783,807,813,817,837,859,861,879,883,889,901,903,919,937,951,957,963,967,973,981,999,1003,1017,1047,1051,1069,1077,1087,1089,1093,1101,1113,1117,1129,1147,1149,1161,1171,1173,1189,1197,1201,1231,1233,1239,1267,1269,1279,1281,1299,1309,1323,1327,1353,1359,1377,1381,1401,1407,1411,1419,1437,1441,1453,1479,1503,1507,1527,1549,1551,1569,1591,1593,1597,1609,1611,1617,1623,1629,1633,1639,1653,1657,1681,1693,1699,1717,1719,1731,1759,1773,1777,1783,1791,1813,1819,1831,1849,1857,1861,1881,1887,1891,1897,1899,1917,1923,1927,1939,1951,1959,1987,1993]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (52000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 181 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_27 : 183 ≤ Nat.count (fun k => Nat.Prime (54000 + k)) 2000 := by
  let L : List Nat := [1,11,13,37,49,59,83,91,101,121,133,139,151,163,167,181,193,217,251,269,277,287,293,311,319,323,331,347,361,367,371,377,401,403,409,413,419,421,437,443,449,469,493,497,499,503,517,521,539,541,547,559,563,577,581,583,601,617,623,629,631,647,667,673,679,709,713,721,727,751,767,773,779,787,799,829,833,851,869,877,881,907,917,919,941,949,959,973,979,983,1001,1009,1021,1049,1051,1057,1061,1073,1079,1103,1109,1117,1127,1147,1163,1171,1201,1207,1213,1217,1219,1229,1243,1249,1259,1291,1313,1331,1333,1337,1339,1343,1351,1373,1381,1399,1411,1439,1441,1457,1469,1487,1501,1511,1529,1541,1547,1579,1589,1603,1609,1619,1621,1631,1633,1639,1661,1663,1667,1673,1681,1691,1697,1711,1717,1721,1733,1763,1787,1793,1799,1807,1813,1817,1819,1823,1829,1837,1843,1849,1871,1889,1897,1901,1903,1921,1927,1931,1933,1949,1967,1987,1997]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (54000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 183 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_28 : 190 ≤ Nat.count (fun k => Nat.Prime (56000 + k)) 2000 := by
  let L : List Nat := [3,9,39,41,53,81,87,93,99,101,113,123,131,149,167,171,179,197,207,209,237,239,249,263,267,269,299,311,333,359,369,377,383,393,401,417,431,437,443,453,467,473,477,479,489,501,503,509,519,527,531,533,543,569,591,597,599,611,629,633,659,663,671,681,687,701,711,713,731,737,747,767,773,779,783,807,809,813,821,827,843,857,873,891,893,897,909,911,921,923,929,941,951,957,963,983,989,993,999,1037,1041,1047,1059,1073,1077,1089,1097,1107,1119,1131,1139,1143,1149,1163,1173,1179,1191,1193,1203,1221,1223,1241,1251,1259,1269,1271,1283,1287,1301,1329,1331,1347,1349,1367,1373,1383,1389,1397,1413,1427,1457,1467,1487,1493,1503,1527,1529,1557,1559,1571,1587,1593,1601,1637,1641,1649,1653,1667,1679,1689,1697,1709,1713,1719,1727,1731,1737,1751,1773,1781,1787,1791,1793,1803,1809,1829,1839,1847,1853,1859,1881,1899,1901,1917,1923,1943,1947,1973,1977,1991]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (56000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 190 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_29 : 184 ≤ Nat.count (fun k => Nat.Prime (58000 + k)) 2000 := by
  let L : List Nat := [13,27,31,43,49,57,61,67,73,99,109,111,129,147,151,153,169,171,189,193,199,207,211,217,229,231,237,243,271,309,313,321,337,363,367,369,379,391,393,403,411,417,427,439,441,451,453,477,481,511,537,543,549,567,573,579,601,603,613,631,657,661,679,687,693,699,711,727,733,741,757,763,771,787,789,831,889,897,901,907,909,913,921,937,943,963,967,979,991,997,1009,1011,1021,1023,1029,1051,1053,1063,1069,1077,1083,1093,1107,1113,1119,1123,1141,1149,1159,1167,1183,1197,1207,1209,1219,1221,1233,1239,1243,1263,1273,1281,1333,1341,1351,1357,1359,1369,1377,1387,1393,1399,1407,1417,1419,1441,1443,1447,1453,1467,1471,1473,1497,1509,1513,1539,1557,1561,1567,1581,1611,1617,1621,1627,1629,1651,1659,1663,1669,1671,1693,1699,1707,1723,1729,1743,1747,1753,1771,1779,1791,1797,1809,1833,1863,1879,1887,1921,1929,1951,1957,1971,1981,1999]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (58000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 184 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_30 : 175 ≤ Nat.count (fun k => Nat.Prime (60000 + k)) 2000 := by
  let L : List Nat := [13,17,29,37,41,77,83,89,91,101,103,107,127,133,139,149,161,167,169,209,217,223,251,257,259,271,289,293,317,331,337,343,353,373,383,397,413,427,443,449,457,493,497,509,521,527,539,589,601,607,611,617,623,631,637,647,649,659,661,679,689,703,719,727,733,737,757,761,763,773,779,793,811,821,859,869,887,889,899,901,913,917,919,923,937,943,953,961,1001,1007,1027,1031,1043,1051,1057,1091,1099,1121,1129,1141,1151,1153,1169,1211,1223,1231,1253,1261,1283,1291,1297,1331,1333,1339,1343,1357,1363,1379,1381,1403,1409,1417,1441,1463,1469,1471,1483,1487,1493,1507,1511,1519,1543,1547,1553,1559,1561,1583,1603,1609,1613,1627,1631,1637,1643,1651,1657,1667,1673,1681,1687,1703,1717,1723,1729,1751,1757,1781,1813,1819,1837,1843,1861,1871,1879,1909,1927,1933,1949,1961,1967,1979,1981,1987,1991]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (60000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 175 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_31 : 181 ≤ Nat.count (fun k => Nat.Prime (62000 + k)) 2000 := by
  let L : List Nat := [3,11,17,39,47,53,57,71,81,99,119,129,131,137,141,143,171,189,191,201,207,213,219,233,273,297,299,303,311,323,327,347,351,383,401,417,423,459,467,473,477,483,497,501,507,533,539,549,563,581,591,597,603,617,627,633,639,653,659,683,687,701,723,731,743,753,761,773,791,801,819,827,851,861,869,873,897,903,921,927,929,939,969,971,981,983,987,989,1029,1031,1059,1067,1073,1079,1097,1103,1113,1127,1131,1149,1179,1197,1199,1211,1241,1247,1277,1281,1299,1311,1313,1317,1331,1337,1347,1353,1361,1367,1377,1389,1391,1397,1409,1419,1421,1439,1443,1463,1467,1473,1487,1493,1499,1521,1527,1533,1541,1559,1577,1587,1589,1599,1601,1607,1611,1617,1629,1647,1649,1659,1667,1671,1689,1691,1697,1703,1709,1719,1727,1737,1743,1761,1773,1781,1793,1799,1803,1809,1823,1839,1841,1853,1857,1863,1901,1907,1913,1929,1949,1977,1997]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (62000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 181 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_32 : 178 ≤ Nat.count (fun k => Nat.Prime (64000 + k)) 2000 := by
  let L : List Nat := [7,13,19,33,37,63,67,81,91,109,123,151,153,157,171,187,189,217,223,231,237,271,279,283,301,303,319,327,333,373,381,399,403,433,439,451,453,483,489,499,513,553,567,577,579,591,601,609,613,621,627,633,661,663,667,679,693,709,717,747,763,781,783,793,811,817,849,853,871,877,879,891,901,919,921,927,937,951,969,997,1003,1011,1027,1029,1033,1053,1063,1071,1089,1099,1101,1111,1119,1123,1129,1141,1147,1167,1171,1173,1179,1183,1203,1213,1239,1257,1267,1269,1287,1293,1309,1323,1327,1353,1357,1371,1381,1393,1407,1413,1419,1423,1437,1447,1449,1479,1497,1519,1521,1537,1539,1543,1551,1557,1563,1579,1581,1587,1599,1609,1617,1629,1633,1647,1651,1657,1677,1687,1699,1701,1707,1713,1717,1719,1729,1731,1761,1777,1789,1809,1827,1831,1837,1839,1843,1851,1867,1881,1899,1921,1927,1929,1951,1957,1963,1981,1983,1993]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (64000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 178 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_33 : 183 ≤ Nat.count (fun k => Nat.Prime (66000 + k)) 2000 := by
  let L : List Nat := [29,37,41,47,67,71,83,89,103,107,109,137,161,169,173,179,191,221,239,271,293,301,337,343,347,359,361,373,377,383,403,413,431,449,457,463,467,491,499,509,523,529,533,541,553,569,571,587,593,601,617,629,643,653,683,697,701,713,721,733,739,749,751,763,791,797,809,821,841,851,853,863,877,883,889,919,923,931,943,947,949,959,973,977,1003,1021,1033,1043,1049,1057,1061,1073,1079,1103,1121,1129,1139,1141,1153,1157,1169,1181,1187,1189,1211,1213,1217,1219,1231,1247,1261,1271,1273,1289,1307,1339,1343,1349,1369,1391,1399,1409,1411,1421,1427,1429,1433,1447,1453,1477,1481,1489,1493,1499,1511,1523,1531,1537,1547,1559,1567,1577,1579,1589,1601,1607,1619,1631,1651,1679,1699,1709,1723,1733,1741,1751,1757,1759,1763,1777,1783,1789,1801,1807,1819,1829,1843,1853,1867,1883,1891,1901,1927,1931,1933,1939,1943,1957,1961,1967,1979,1987,1993]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (66000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 183 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_34 : 161 ≤ Nat.count (fun k => Nat.Prime (68000 + k)) 2000 := by
  let L : List Nat := [23,41,53,59,71,87,99,111,113,141,147,161,171,207,209,213,219,227,239,261,279,281,311,329,351,371,389,399,437,443,447,449,473,477,483,489,491,501,507,521,531,539,543,567,581,597,611,633,639,659,669,683,687,699,711,713,729,737,743,749,767,771,777,791,813,819,821,863,879,881,891,897,899,903,909,917,927,947,963,993,1001,1011,1019,1029,1031,1061,1067,1073,1109,1119,1127,1143,1149,1151,1163,1191,1193,1197,1203,1221,1233,1239,1247,1257,1259,1263,1313,1317,1337,1341,1371,1379,1383,1389,1401,1403,1427,1431,1439,1457,1463,1467,1473,1481,1491,1493,1497,1499,1539,1557,1593,1623,1653,1661,1677,1691,1697,1709,1737,1739,1761,1763,1767,1779,1809,1821,1827,1829,1833,1847,1857,1859,1877,1899,1911,1929,1931,1941,1959,1991,1997]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (68000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 161 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_35 : 193 ≤ Nat.count (fun k => Nat.Prime (70000 + k)) 2000 := by
  let L : List Nat := [1,3,9,19,39,51,61,67,79,99,111,117,121,123,139,141,157,163,177,181,183,199,201,207,223,229,237,241,249,271,289,297,309,313,321,327,351,373,379,381,393,423,429,439,451,457,459,481,487,489,501,507,529,537,549,571,573,583,589,607,619,621,627,639,657,663,667,687,709,717,729,753,769,783,793,823,841,843,849,853,867,877,879,891,901,913,919,921,937,949,951,957,969,979,981,991,997,999,1011,1023,1039,1059,1069,1081,1089,1119,1129,1143,1147,1153,1161,1167,1171,1191,1209,1233,1237,1249,1257,1261,1263,1287,1293,1317,1327,1329,1333,1339,1341,1347,1353,1359,1363,1387,1389,1399,1411,1413,1419,1429,1437,1443,1453,1471,1473,1479,1483,1503,1527,1537,1549,1551,1563,1569,1593,1597,1633,1647,1663,1671,1693,1699,1707,1711,1713,1719,1741,1761,1777,1789,1807,1809,1821,1837,1843,1849,1861,1867,1879,1881,1887,1899,1909,1917,1933,1941,1947,1963,1971,1983,1987,1993,1999]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (70000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 193 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_36 : 173 ≤ Nat.count (fun k => Nat.Prime (72000 + k)) 2000 := by
  let L : List Nat := [19,31,43,47,53,73,77,89,91,101,103,109,139,161,167,169,173,211,221,223,227,229,251,253,269,271,277,287,307,313,337,341,353,367,379,383,421,431,461,467,469,481,493,497,503,533,547,551,559,577,613,617,623,643,647,649,661,671,673,679,689,701,707,719,727,733,739,763,767,797,817,823,859,869,871,883,889,893,901,907,911,923,931,937,949,953,959,973,977,997,1009,1013,1019,1037,1039,1043,1061,1063,1079,1091,1121,1127,1133,1141,1181,1189,1237,1243,1259,1277,1291,1303,1309,1327,1331,1351,1361,1363,1369,1379,1387,1417,1421,1433,1453,1459,1471,1477,1483,1517,1523,1529,1547,1553,1561,1571,1583,1589,1597,1607,1609,1613,1637,1643,1651,1673,1679,1681,1693,1699,1709,1721,1727,1751,1757,1771,1783,1819,1823,1847,1849,1859,1867,1877,1883,1897,1907,1939,1943,1951,1961,1973,1999]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (72000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 173 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_37 : 183 ≤ Nat.count (fun k => Nat.Prime (74000 + k)) 2000 := by
  let L : List Nat := [17,21,27,47,51,71,77,93,99,101,131,143,149,159,161,167,177,189,197,201,203,209,219,231,257,279,287,293,297,311,317,323,353,357,363,377,381,383,411,413,419,441,449,453,471,489,507,509,521,527,531,551,561,567,573,587,597,609,611,623,653,687,699,707,713,717,719,729,731,747,759,761,771,779,797,821,827,831,843,857,861,869,873,887,891,897,903,923,929,933,941,959,1011,1013,1017,1029,1037,1041,1079,1083,1109,1133,1149,1161,1167,1169,1181,1193,1209,1211,1217,1223,1227,1239,1253,1269,1277,1289,1307,1323,1329,1337,1347,1353,1367,1377,1389,1391,1401,1403,1407,1431,1437,1479,1503,1511,1521,1527,1533,1539,1541,1553,1557,1571,1577,1583,1611,1617,1619,1629,1641,1653,1659,1679,1683,1689,1703,1707,1709,1721,1731,1743,1767,1773,1781,1787,1793,1797,1821,1833,1853,1869,1883,1913,1931,1937,1941,1967,1979,1983,1989,1991,1997]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (74000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 183 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_38 : 178 ≤ Nat.count (fun k => Nat.Prime (76000 + k)) 2000 := by
  let L : List Nat := [1,3,31,39,79,81,91,99,103,123,129,147,157,159,163,207,213,231,243,249,253,259,261,283,289,303,333,343,367,369,379,387,403,421,423,441,463,471,481,487,493,507,511,519,537,541,543,561,579,597,603,607,631,649,651,667,673,679,697,717,733,753,757,771,777,781,801,819,829,831,837,847,871,873,883,907,913,919,943,949,961,963,991,1003,1017,1023,1029,1041,1047,1069,1081,1093,1101,1137,1141,1153,1167,1171,1191,1201,1213,1237,1239,1243,1249,1261,1263,1267,1269,1279,1291,1317,1323,1339,1347,1351,1359,1369,1377,1383,1417,1419,1431,1447,1471,1477,1479,1489,1491,1509,1513,1521,1527,1543,1549,1551,1557,1563,1569,1573,1587,1591,1611,1617,1621,1641,1647,1659,1681,1687,1689,1699,1711,1713,1719,1723,1731,1743,1747,1761,1773,1783,1797,1801,1813,1839,1849,1863,1867,1893,1899,1929,1933,1951,1969,1977,1983,1999]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (76000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 178 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_39 : 175 ≤ Nat.count (fun k => Nat.Prime (78000 + k)) 2000 := by
  let L : List Nat := [7,17,31,41,49,59,79,101,121,137,139,157,163,167,173,179,191,193,203,229,233,241,259,277,283,301,307,311,317,341,347,367,401,427,437,439,467,479,487,497,509,511,517,539,541,553,569,571,577,583,593,607,623,643,649,653,691,697,707,713,721,737,779,781,787,791,797,803,809,823,839,853,857,877,887,889,893,901,919,929,941,977,979,989,1031,1039,1043,1063,1087,1103,1111,1133,1139,1147,1151,1153,1159,1181,1187,1193,1201,1229,1231,1241,1259,1273,1279,1283,1301,1309,1319,1333,1337,1349,1357,1367,1379,1393,1397,1399,1411,1423,1427,1433,1451,1481,1493,1531,1537,1549,1559,1561,1579,1589,1601,1609,1613,1621,1627,1631,1633,1657,1669,1687,1691,1693,1697,1699,1757,1769,1777,1801,1811,1813,1817,1823,1829,1841,1843,1847,1861,1867,1873,1889,1901,1903,1907,1939,1943,1967,1973,1979,1987,1997,1999]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (78000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 175 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_40 : 180 ≤ Nat.count (fun k => Nat.Prime (80000 + k)) 2000 := by
  let L : List Nat := [21,39,51,71,77,107,111,141,147,149,153,167,173,177,191,207,209,221,231,233,239,251,263,273,279,287,309,317,329,341,347,363,369,387,407,429,447,449,471,473,489,491,513,527,537,557,567,599,603,611,621,627,629,651,657,669,671,677,681,683,687,701,713,737,747,749,761,777,779,783,789,803,809,819,831,833,849,863,897,909,911,917,923,929,933,953,963,989,1001,1013,1017,1019,1023,1031,1041,1043,1047,1049,1071,1077,1083,1097,1101,1119,1131,1157,1163,1173,1181,1197,1199,1203,1223,1233,1239,1281,1283,1293,1299,1307,1331,1343,1349,1353,1359,1371,1373,1401,1409,1421,1439,1457,1463,1509,1517,1527,1533,1547,1551,1553,1559,1563,1569,1611,1619,1629,1637,1647,1649,1667,1671,1677,1689,1701,1703,1707,1727,1737,1749,1761,1769,1773,1799,1817,1839,1847,1853,1869,1883,1899,1901,1919,1929,1931,1937,1943,1953,1967,1971,1973]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (80000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 180 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_41 : 173 ≤ Nat.count (fun k => Nat.Prime (82000 + k)) 2000 := by
  let L : List Nat := [3,7,9,13,21,31,37,39,51,67,73,129,139,141,153,163,171,183,189,193,207,217,219,223,231,237,241,261,267,279,301,307,339,349,351,361,373,387,393,421,457,463,469,471,483,487,493,499,507,529,531,549,559,561,567,571,591,601,609,613,619,633,651,657,699,721,723,727,729,757,759,763,781,787,793,799,811,813,837,847,883,889,891,903,913,939,963,981,997,1003,1009,1023,1047,1059,1063,1071,1077,1089,1093,1101,1117,1137,1177,1203,1207,1219,1221,1227,1231,1233,1243,1257,1267,1269,1273,1299,1311,1339,1341,1357,1383,1389,1399,1401,1407,1417,1423,1431,1437,1443,1449,1459,1471,1477,1497,1537,1557,1561,1563,1579,1591,1597,1609,1617,1621,1639,1641,1653,1663,1689,1701,1717,1719,1737,1761,1773,1777,1791,1813,1833,1843,1857,1869,1873,1891,1903,1911,1921,1933,1939,1969,1983,1987]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (82000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 173 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_42 : 172 ≤ Nat.count (fun k => Nat.Prime (84000 + k)) 2000 := by
  let L : List Nat := [11,17,47,53,59,61,67,89,121,127,131,137,143,163,179,181,191,199,211,221,223,229,239,247,263,299,307,313,317,319,347,349,377,389,391,401,407,421,431,437,443,449,457,463,467,481,499,503,509,521,523,533,551,559,589,629,631,649,653,659,673,691,697,701,713,719,731,737,751,761,787,793,809,811,827,857,859,869,871,913,919,947,961,967,977,979,991,1009,1021,1027,1037,1049,1061,1081,1087,1091,1093,1103,1109,1121,1133,1147,1159,1193,1199,1201,1213,1223,1229,1237,1243,1247,1259,1297,1303,1313,1331,1333,1361,1363,1369,1381,1411,1427,1429,1439,1447,1451,1453,1469,1487,1513,1517,1523,1531,1549,1571,1577,1597,1601,1607,1619,1621,1627,1639,1643,1661,1667,1669,1691,1703,1711,1717,1733,1751,1781,1793,1817,1819,1829,1831,1837,1843,1847,1853,1889,1903,1909,1931,1933,1991,1999]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (84000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 172 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_43 : 181 ≤ Nat.count (fun k => Nat.Prime (86000 + k)) 2000 := by
  let L : List Nat := [11,17,27,29,69,77,83,111,113,117,131,137,143,161,171,179,183,197,201,209,239,243,249,257,263,269,287,291,293,297,311,323,341,351,353,357,369,371,381,389,399,413,423,441,453,461,467,477,491,501,509,531,533,539,561,573,579,587,599,627,629,677,689,693,711,719,729,743,753,767,771,783,813,837,843,851,857,861,869,923,927,929,939,951,959,969,981,993,1011,1013,1037,1041,1049,1071,1083,1103,1107,1119,1121,1133,1149,1151,1179,1181,1187,1211,1221,1223,1251,1253,1257,1277,1281,1293,1299,1313,1317,1323,1337,1359,1383,1403,1407,1421,1427,1433,1443,1473,1481,1491,1509,1511,1517,1523,1539,1541,1547,1553,1557,1559,1583,1587,1589,1613,1623,1629,1631,1641,1643,1649,1671,1679,1683,1691,1697,1701,1719,1721,1739,1743,1751,1767,1793,1797,1803,1811,1833,1853,1869,1877,1881,1887,1911,1917,1931,1943,1959,1961,1973,1977,1991]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (86000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 181 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_44 : 170 ≤ Nat.count (fun k => Nat.Prime (88000 + k)) 2000 := by
  let L : List Nat := [1,3,7,19,37,69,79,93,117,129,169,177,211,223,237,241,259,261,289,301,321,327,337,339,379,397,411,423,427,463,469,471,493,499,513,523,547,589,591,607,609,643,651,657,661,663,667,681,721,729,741,747,771,789,793,799,801,807,811,813,817,819,843,853,861,867,873,883,897,903,919,937,951,969,993,997,1003,1009,1017,1021,1041,1051,1057,1069,1071,1083,1087,1101,1107,1113,1119,1123,1137,1153,1189,1203,1209,1213,1227,1231,1237,1261,1269,1273,1293,1303,1317,1329,1363,1371,1381,1387,1393,1399,1413,1417,1431,1443,1449,1459,1477,1491,1501,1513,1519,1521,1527,1533,1561,1563,1567,1591,1597,1599,1603,1611,1627,1633,1653,1657,1659,1669,1671,1681,1689,1753,1759,1767,1779,1783,1797,1809,1819,1821,1833,1839,1849,1867,1891,1897,1899,1909,1917,1923,1939,1959,1963,1977,1983,1989]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (88000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 170 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_45 : 174 ≤ Nat.count (fun k => Nat.Prime (90000 + k)) 2000 := by
  let L : List Nat := [1,7,11,17,19,23,31,53,59,67,71,73,89,107,121,127,149,163,173,187,191,197,199,203,217,227,239,247,263,271,281,289,313,353,359,371,373,379,397,401,403,407,437,439,469,473,481,499,511,523,527,529,533,547,583,599,617,619,631,641,647,659,677,679,697,703,709,731,749,787,793,803,821,823,833,841,847,863,887,901,907,911,917,931,947,971,977,989,997,1009,1019,1033,1079,1081,1097,1099,1121,1127,1129,1139,1141,1151,1153,1159,1163,1183,1193,1199,1229,1237,1243,1249,1253,1283,1291,1297,1303,1309,1331,1367,1369,1373,1381,1387,1393,1397,1411,1423,1433,1453,1457,1459,1463,1493,1499,1513,1529,1541,1571,1573,1577,1583,1591,1621,1631,1639,1673,1691,1703,1711,1733,1753,1757,1771,1781,1801,1807,1811,1813,1823,1837,1841,1867,1873,1909,1921,1939,1943,1951,1957,1961,1967,1969,1997]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (90000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 174 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_46 : 183 ≤ Nat.count (fun k => Nat.Prime (92000 + k)) 2000 := by
  let L : List Nat := [3,9,33,41,51,77,83,107,111,119,143,153,173,177,179,189,203,219,221,227,233,237,243,251,269,297,311,317,333,347,353,357,363,369,377,381,383,387,399,401,413,419,431,459,461,467,479,489,503,507,551,557,567,569,581,593,623,627,639,641,647,657,669,671,681,683,693,699,707,717,723,737,753,761,767,779,789,791,801,809,821,831,849,857,861,863,867,893,899,921,927,941,951,957,959,987,993,1001,1047,1053,1059,1077,1083,1089,1097,1103,1113,1131,1133,1139,1151,1169,1179,1187,1199,1229,1239,1241,1251,1253,1257,1263,1281,1283,1287,1307,1319,1323,1329,1337,1371,1377,1383,1407,1419,1427,1463,1479,1481,1487,1491,1493,1497,1503,1523,1529,1553,1557,1559,1563,1581,1601,1607,1629,1637,1683,1701,1703,1719,1739,1761,1763,1787,1809,1811,1827,1851,1871,1887,1889,1893,1901,1911,1913,1923,1937,1941,1949,1967,1971,1979,1983,1997]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (92000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 183 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_47 : 182 ≤ Nat.count (fun k => Nat.Prime (94000 + k)) 2000 := by
  let L : List Nat := [7,9,33,49,57,63,79,99,109,111,117,121,151,153,169,201,207,219,229,253,261,273,291,307,309,321,327,331,343,349,351,379,397,399,421,427,433,439,441,447,463,477,483,513,529,531,541,543,547,559,561,573,583,597,603,613,621,649,651,687,693,709,723,727,747,771,777,781,789,793,811,819,823,837,841,847,849,873,889,903,907,933,949,951,961,993,999,1003,1009,1021,1027,1063,1071,1083,1087,1089,1093,1101,1107,1111,1131,1143,1153,1177,1189,1191,1203,1213,1219,1231,1233,1239,1257,1261,1267,1273,1279,1287,1311,1317,1327,1339,1369,1383,1393,1401,1413,1419,1429,1441,1443,1461,1467,1471,1479,1483,1507,1527,1531,1539,1549,1561,1569,1581,1597,1603,1617,1621,1629,1633,1651,1701,1707,1713,1717,1723,1731,1737,1747,1773,1783,1789,1791,1801,1803,1813,1819,1857,1869,1873,1881,1891,1911,1917,1923,1929,1947,1957,1959,1971,1987,1989]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (94000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 182 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_48 : 166 ≤ Nat.count (fun k => Nat.Prime (96000 + k)) 2000 := by
  let L : List Nat := [1,13,17,43,53,59,79,97,137,149,157,167,179,181,199,211,221,223,233,259,263,269,281,289,293,323,329,331,337,353,377,401,419,431,443,451,457,461,469,479,487,493,497,517,527,553,557,581,587,589,601,643,661,667,671,697,703,731,737,739,749,757,763,769,779,787,797,799,821,823,827,847,851,857,893,907,911,931,953,959,973,979,989,997,1001,1003,1007,1021,1039,1073,1081,1103,1117,1127,1151,1157,1159,1169,1171,1177,1187,1213,1231,1241,1259,1283,1301,1303,1327,1367,1369,1373,1379,1381,1387,1397,1423,1429,1441,1453,1459,1463,1499,1501,1511,1523,1547,1549,1553,1561,1571,1577,1579,1583,1607,1609,1613,1649,1651,1673,1687,1711,1729,1771,1777,1787,1789,1813,1829,1841,1843,1847,1849,1859,1861,1871,1879,1883,1919,1927,1931,1943,1961,1967,1973,1987]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (96000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 166 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
opaque prime_block_49 : 174 ≤ Nat.count (fun k => Nat.Prime (98000 + k)) 2000 := by
  let L : List Nat := [9,11,17,41,47,57,81,101,123,129,143,179,207,213,221,227,251,257,269,297,299,317,321,323,327,347,369,377,387,389,407,411,419,429,443,453,459,467,473,479,491,507,519,533,543,561,563,573,597,621,627,639,641,663,669,689,711,713,717,729,731,737,773,779,801,807,809,837,849,867,869,873,887,893,897,899,909,911,927,929,939,947,953,963,981,993,999,1013,1017,1023,1041,1053,1079,1083,1089,1103,1109,1119,1131,1133,1137,1139,1149,1173,1181,1191,1223,1233,1241,1251,1257,1259,1277,1289,1317,1347,1349,1367,1371,1377,1391,1397,1401,1409,1431,1439,1469,1487,1497,1523,1527,1529,1551,1559,1563,1571,1577,1581,1607,1611,1623,1643,1661,1667,1679,1689,1707,1709,1713,1719,1721,1733,1761,1767,1787,1793,1809,1817,1823,1829,1833,1839,1859,1871,1877,1881,1901,1907,1923,1929,1961,1971,1989,1991]
  have hnodup : L.Nodup := by decide
  have hbound : L.Forall (fun x => x < 2000) := by
    subst L
    repeat constructor <;> norm_num
  have hprime : L.Forall (fun x => Nat.Prime (98000 + x)) := by
    subst L
    repeat constructor <;> norm_num
  rw [Nat.count_eq_card_filter_range]
  have hcard : L.toFinset.card = 174 := by
    rw [List.toFinset_card_of_nodup hnodup]
    subst L
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp hbound) x hxL, (List.forall_iff_forall_mem.mp hprime) x hxL⟩
