import Submission.FiveCertificates1Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows1
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src1600 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1600 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1600_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle1600_1 : CycleData E W := ⟨3,![2,10,11,15,7],![3,4,14,26,16]⟩
def cycle1600_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1600_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1600_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle1600_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1600 : PartitionData E W := ⟨6,![cycle1600_0,cycle1600_1,cycle1600_2,cycle1600_3,cycle1600_4,cycle1600_5]⟩
lemma valid_data1600 : data1600.Valid src1600 dst1600 Finset.univ := by decide +kernel

def src1601 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1601 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1601_0 : CycleData E W := ⟨2,![0,14,11,5],![2,6,26,14]⟩
def cycle1601_1 : CycleData E W := ⟨2,![1,17,16,7],![3,6,38,16]⟩
def cycle1601_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1601_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1601_4 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle1601_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1601 : PartitionData E W := ⟨6,![cycle1601_0,cycle1601_1,cycle1601_2,cycle1601_3,cycle1601_4,cycle1601_5]⟩
lemma valid_data1601 : data1601.Valid src1601 dst1601 Finset.univ := by decide +kernel

def src1602 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1602 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1602_0 : CycleData E W := ⟨3,![0,17,20,11,5],![2,6,38,28,14]⟩
def cycle1602_1 : CycleData E W := ⟨1,![1,14,7],![3,6,16]⟩
def cycle1602_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1602_3 : CycleData E W := ⟨2,![3,21,16,13],![4,8,38,26]⟩
def cycle1602_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1602_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1602 : PartitionData E W := ⟨6,![cycle1602_0,cycle1602_1,cycle1602_2,cycle1602_3,cycle1602_4,cycle1602_5]⟩
lemma valid_data1602 : data1602.Valid src1602 dst1602 Finset.univ := by decide +kernel

def src1603 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1603 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1603_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle1603_1 : CycleData E W := ⟨2,![2,13,15,7],![3,4,26,16]⟩
def cycle1603_2 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle1603_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1603_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle1603_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1603 : PartitionData E W := ⟨6,![cycle1603_0,cycle1603_1,cycle1603_2,cycle1603_3,cycle1603_4,cycle1603_5]⟩
lemma valid_data1603 : data1603.Valid src1603 dst1603 Finset.univ := by decide +kernel

def src1604 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1604 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1604_0 : CycleData E W := ⟨2,![0,17,20,9],![2,6,38,18]⟩
def cycle1604_1 : CycleData E W := ⟨1,![1,14,7],![3,6,16]⟩
def cycle1604_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1604_3 : CycleData E W := ⟨2,![3,21,16,13],![4,8,38,26]⟩
def cycle1604_4 : CycleData E W := ⟨2,![4,18,11,5],![2,8,28,14]⟩
def cycle1604_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1604 : PartitionData E W := ⟨6,![cycle1604_0,cycle1604_1,cycle1604_2,cycle1604_3,cycle1604_4,cycle1604_5]⟩
lemma valid_data1604 : data1604.Valid src1604 dst1604 Finset.univ := by decide +kernel

def src1605 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1605 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1605_0 : CycleData E W := ⟨3,![0,17,12,11,5],![2,6,26,28,14]⟩
def cycle1605_1 : CycleData E W := ⟨1,![1,14,7],![3,6,16]⟩
def cycle1605_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1605_3 : CycleData E W := ⟨2,![3,21,16,13],![4,8,38,26]⟩
def cycle1605_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1605_5 : CycleData E W := ⟨2,![8,19,20,15],![16,18,28,38]⟩
def data1605 : PartitionData E W := ⟨6,![cycle1605_0,cycle1605_1,cycle1605_2,cycle1605_3,cycle1605_4,cycle1605_5]⟩
lemma valid_data1605 : data1605.Valid src1605 dst1605 Finset.univ := by decide +kernel

def src1606 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1606 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1606_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle1606_1 : CycleData E W := ⟨3,![2,13,17,14,7],![3,4,26,6,16]⟩
def cycle1606_2 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle1606_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1606_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1606_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1606 : PartitionData E W := ⟨6,![cycle1606_0,cycle1606_1,cycle1606_2,cycle1606_3,cycle1606_4,cycle1606_5]⟩
lemma valid_data1606 : data1606.Valid src1606 dst1606 Finset.univ := by decide +kernel

def src1607 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1607 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1607_0 : CycleData E W := ⟨3,![0,17,12,11,5],![2,6,26,28,14]⟩
def cycle1607_1 : CycleData E W := ⟨1,![1,14,7],![3,6,16]⟩
def cycle1607_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1607_3 : CycleData E W := ⟨2,![3,21,16,13],![4,8,38,26]⟩
def cycle1607_4 : CycleData E W := ⟨2,![4,18,19,9],![2,8,28,18]⟩
def cycle1607_5 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def data1607 : PartitionData E W := ⟨6,![cycle1607_0,cycle1607_1,cycle1607_2,cycle1607_3,cycle1607_4,cycle1607_5]⟩
lemma valid_data1607 : data1607.Valid src1607 dst1607 Finset.univ := by decide +kernel

def src1608 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1608 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1608_0 : CycleData E W := ⟨9,![4,18,8,16,17,1,2,13,12,11,5],![2,8,18,16,38,6,3,4,26,28,14]⟩
def cycle1608_1 : CycleData E W := ⟨9,![0,14,15,7,6,10,3,21,20,19,9],![2,6,26,16,3,14,4,8,38,28,18]⟩
def data1608 : PartitionData E W := ⟨2,![cycle1608_0,cycle1608_1]⟩
lemma valid_data1608 : data1608.Valid src1608 dst1608 Finset.univ := by decide +kernel

def src1609 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1609 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1609_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle1609_1 : CycleData E W := ⟨2,![2,13,15,7],![3,4,26,16]⟩
def cycle1609_2 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle1609_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1609_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle1609_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1609 : PartitionData E W := ⟨6,![cycle1609_0,cycle1609_1,cycle1609_2,cycle1609_3,cycle1609_4,cycle1609_5]⟩
lemma valid_data1609 : data1609.Valid src1609 dst1609 Finset.univ := by decide +kernel

def src1610 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1610 : E → W := ![6,3,4,8,2,14,3,16,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1610_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1610_1 : CycleData E W := ⟨2,![1,14,15,7],![3,6,26,16]⟩
def cycle1610_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1610_3 : CycleData E W := ⟨2,![3,18,12,13],![4,8,28,26]⟩
def cycle1610_4 : CycleData E W := ⟨2,![5,11,19,9],![2,14,28,18]⟩
def cycle1610_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data1610 : PartitionData E W := ⟨6,![cycle1610_0,cycle1610_1,cycle1610_2,cycle1610_3,cycle1610_4,cycle1610_5]⟩
lemma valid_data1610 : data1610.Valid src1610 dst1610 Finset.univ := by decide +kernel

def src1611 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1611 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1611_0 : CycleData E W := ⟨9,![4,18,8,7,1,17,16,10,13,12,5],![2,8,18,16,3,6,38,26,4,28,14]⟩
def cycle1611_1 : CycleData E W := ⟨9,![0,14,15,11,6,2,3,21,20,19,9],![2,6,16,26,14,3,4,8,38,28,18]⟩
def data1611 : PartitionData E W := ⟨2,![cycle1611_0,cycle1611_1]⟩
lemma valid_data1611 : data1611.Valid src1611 dst1611 Finset.univ := by decide +kernel

def src1612 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1612 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1612_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle1612_1 : CycleData E W := ⟨2,![2,10,15,7],![3,4,26,16]⟩
def cycle1612_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1612_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1612_4 : CycleData E W := ⟨2,![14,8,19,17],![6,16,18,38]⟩
def cycle1612_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1612 : PartitionData E W := ⟨6,![cycle1612_0,cycle1612_1,cycle1612_2,cycle1612_3,cycle1612_4,cycle1612_5]⟩
lemma valid_data1612 : data1612.Valid src1612 dst1612 Finset.univ := by decide +kernel

def src1613 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1613 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1613_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1613_1 : CycleData E W := ⟨1,![1,14,7],![3,6,16]⟩
def cycle1613_2 : CycleData E W := ⟨2,![2,10,11,6],![3,4,26,14]⟩
def cycle1613_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1613_4 : CycleData E W := ⟨2,![5,12,19,9],![2,14,28,18]⟩
def cycle1613_5 : CycleData E W := ⟨2,![8,20,16,15],![16,18,38,26]⟩
def data1613 : PartitionData E W := ⟨6,![cycle1613_0,cycle1613_1,cycle1613_2,cycle1613_3,cycle1613_4,cycle1613_5]⟩
lemma valid_data1613 : data1613.Valid src1613 dst1613 Finset.univ := by decide +kernel

def src1614 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1614 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1614_0 : CycleData E W := ⟨2,![0,17,11,5],![2,6,26,14]⟩
def cycle1614_1 : CycleData E W := ⟨1,![1,14,7],![3,6,16]⟩
def cycle1614_2 : CycleData E W := ⟨2,![2,13,12,6],![3,4,28,14]⟩
def cycle1614_3 : CycleData E W := ⟨2,![3,21,16,10],![4,8,38,26]⟩
def cycle1614_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1614_5 : CycleData E W := ⟨2,![8,19,20,15],![16,18,28,38]⟩
def data1614 : PartitionData E W := ⟨6,![cycle1614_0,cycle1614_1,cycle1614_2,cycle1614_3,cycle1614_4,cycle1614_5]⟩
lemma valid_data1614 : data1614.Valid src1614 dst1614 Finset.univ := by decide +kernel

def src1615 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1615 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1615_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle1615_1 : CycleData E W := ⟨3,![2,10,17,14,7],![3,4,26,6,16]⟩
def cycle1615_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1615_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1615_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1615_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1615 : PartitionData E W := ⟨6,![cycle1615_0,cycle1615_1,cycle1615_2,cycle1615_3,cycle1615_4,cycle1615_5]⟩
lemma valid_data1615 : data1615.Valid src1615 dst1615 Finset.univ := by decide +kernel

def src1616 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1616 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1616_0 : CycleData E W := ⟨2,![0,17,11,5],![2,6,26,14]⟩
def cycle1616_1 : CycleData E W := ⟨1,![1,14,7],![3,6,16]⟩
def cycle1616_2 : CycleData E W := ⟨2,![2,13,12,6],![3,4,28,14]⟩
def cycle1616_3 : CycleData E W := ⟨2,![3,21,16,10],![4,8,38,26]⟩
def cycle1616_4 : CycleData E W := ⟨2,![4,18,19,9],![2,8,28,18]⟩
def cycle1616_5 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def data1616 : PartitionData E W := ⟨6,![cycle1616_0,cycle1616_1,cycle1616_2,cycle1616_3,cycle1616_4,cycle1616_5]⟩
lemma valid_data1616 : data1616.Valid src1616 dst1616 Finset.univ := by decide +kernel

def src1617 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1617 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1617_0 : CycleData E W := ⟨9,![4,3,10,14,17,16,7,6,12,19,9],![2,8,4,26,6,38,16,3,14,28,18]⟩
def cycle1617_1 : CycleData E W := ⟨9,![0,1,2,13,20,21,18,8,15,11,5],![2,6,3,4,28,38,8,18,16,26,14]⟩
def data1617 : PartitionData E W := ⟨2,![cycle1617_0,cycle1617_1]⟩
lemma valid_data1617 : data1617.Valid src1617 dst1617 Finset.univ := by decide +kernel

def src1618 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1618 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1618_0 : CycleData E W := ⟨2,![0,1,6,5],![2,6,3,14]⟩
def cycle1618_1 : CycleData E W := ⟨2,![2,10,15,7],![3,4,26,16]⟩
def cycle1618_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1618_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1618_4 : CycleData E W := ⟨1,![8,19,16],![16,18,38]⟩
def cycle1618_5 : CycleData E W := ⟨3,![14,11,12,20,17],![6,26,14,28,38]⟩
def data1618 : PartitionData E W := ⟨6,![cycle1618_0,cycle1618_1,cycle1618_2,cycle1618_3,cycle1618_4,cycle1618_5]⟩
lemma valid_data1618 : data1618.Valid src1618 dst1618 Finset.univ := by decide +kernel

def src1619 : E → W := ![2,6,3,4,8,2,14,3,16,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1619 : E → W := ![6,3,4,8,2,14,3,16,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1619_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1619_1 : CycleData E W := ⟨2,![1,14,10,2],![3,6,26,4]⟩
def cycle1619_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1619_3 : CycleData E W := ⟨2,![5,12,19,9],![2,14,28,18]⟩
def cycle1619_4 : CycleData E W := ⟨2,![6,11,15,7],![3,14,26,16]⟩
def cycle1619_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data1619 : PartitionData E W := ⟨6,![cycle1619_0,cycle1619_1,cycle1619_2,cycle1619_3,cycle1619_4,cycle1619_5]⟩
lemma valid_data1619 : data1619.Valid src1619 dst1619 Finset.univ := by decide +kernel

def src1620 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1620 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1620_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1620_1 : CycleData E W := ⟨2,![1,14,8,7],![3,6,16,18]⟩
def cycle1620_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1620_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle1620_4 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle1620_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1620 : PartitionData E W := ⟨6,![cycle1620_0,cycle1620_1,cycle1620_2,cycle1620_3,cycle1620_4,cycle1620_5]⟩
lemma valid_data1620 : data1620.Valid src1620 dst1620 Finset.univ := by decide +kernel

def src1621 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1621 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1621_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1621_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle1621_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1621_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1621_4 : CycleData E W := ⟨4,![4,18,8,15,11,5],![2,8,18,16,26,14]⟩
def cycle1621_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1621 : PartitionData E W := ⟨6,![cycle1621_0,cycle1621_1,cycle1621_2,cycle1621_3,cycle1621_4,cycle1621_5]⟩
lemma valid_data1621 : data1621.Valid src1621 dst1621 Finset.univ := by decide +kernel

def src1622 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1622 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1622_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1622_1 : CycleData E W := ⟨2,![1,17,20,7],![3,6,38,18]⟩
def cycle1622_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1622_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1622_4 : CycleData E W := ⟨3,![4,21,16,11,5],![2,8,38,26,14]⟩
def cycle1622_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1622 : PartitionData E W := ⟨6,![cycle1622_0,cycle1622_1,cycle1622_2,cycle1622_3,cycle1622_4,cycle1622_5]⟩
lemma valid_data1622 : data1622.Valid src1622 dst1622 Finset.univ := by decide +kernel

def src1623 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1623 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1623_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1623_1 : CycleData E W := ⟨2,![1,17,11,6],![3,6,26,14]⟩
def cycle1623_2 : CycleData E W := ⟨2,![2,13,19,7],![3,4,28,18]⟩
def cycle1623_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle1623_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle1623_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1623 : PartitionData E W := ⟨6,![cycle1623_0,cycle1623_1,cycle1623_2,cycle1623_3,cycle1623_4,cycle1623_5]⟩
lemma valid_data1623 : data1623.Valid src1623 dst1623 Finset.univ := by decide +kernel

def src1624 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1624 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1624_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1624_1 : CycleData E W := ⟨2,![1,17,11,6],![3,6,26,14]⟩
def cycle1624_2 : CycleData E W := ⟨2,![2,3,18,7],![3,4,8,18]⟩
def cycle1624_3 : CycleData E W := ⟨3,![4,21,13,10,5],![2,8,28,4,14]⟩
def cycle1624_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1624_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1624 : PartitionData E W := ⟨6,![cycle1624_0,cycle1624_1,cycle1624_2,cycle1624_3,cycle1624_4,cycle1624_5]⟩
lemma valid_data1624 : data1624.Valid src1624 dst1624 Finset.univ := by decide +kernel

def src1625 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1625 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1625_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1625_1 : CycleData E W := ⟨2,![1,17,11,6],![3,6,26,14]⟩
def cycle1625_2 : CycleData E W := ⟨2,![2,13,19,7],![3,4,28,18]⟩
def cycle1625_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle1625_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle1625_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1625 : PartitionData E W := ⟨6,![cycle1625_0,cycle1625_1,cycle1625_2,cycle1625_3,cycle1625_4,cycle1625_5]⟩
lemma valid_data1625 : data1625.Valid src1625 dst1625 Finset.univ := by decide +kernel

def src1626 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1626 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1626_0 : CycleData E W := ⟨9,![4,18,8,16,17,14,12,13,2,6,5],![2,8,18,16,38,6,26,28,4,3,14]⟩
def cycle1626_1 : CycleData E W := ⟨9,![0,1,7,19,20,21,3,10,11,15,9],![2,6,3,18,28,38,8,4,14,26,16]⟩
def data1626 : PartitionData E W := ⟨2,![cycle1626_0,cycle1626_1]⟩
lemma valid_data1626 : data1626.Valid src1626 dst1626 Finset.univ := by decide +kernel

def src1627 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1627 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1627_0 : CycleData E W := ⟨2,![0,14,11,5],![2,6,26,14]⟩
def cycle1627_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle1627_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1627_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1627_4 : CycleData E W := ⟨2,![4,18,8,9],![2,8,18,16]⟩
def cycle1627_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data1627 : PartitionData E W := ⟨6,![cycle1627_0,cycle1627_1,cycle1627_2,cycle1627_3,cycle1627_4,cycle1627_5]⟩
lemma valid_data1627 : data1627.Valid src1627 dst1627 Finset.univ := by decide +kernel

def src1628 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1628 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1628_0 : CycleData E W := ⟨2,![0,14,11,5],![2,6,26,14]⟩
def cycle1628_1 : CycleData E W := ⟨2,![1,17,20,7],![3,6,38,18]⟩
def cycle1628_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1628_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1628_4 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle1628_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1628 : PartitionData E W := ⟨6,![cycle1628_0,cycle1628_1,cycle1628_2,cycle1628_3,cycle1628_4,cycle1628_5]⟩
lemma valid_data1628 : data1628.Valid src1628 dst1628 Finset.univ := by decide +kernel

def src1629 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1629 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1629_0 : CycleData E W := ⟨9,![5,11,12,16,17,1,2,3,18,8,9],![2,14,28,26,38,6,3,4,8,18,16]⟩
def cycle1629_1 : CycleData E W := ⟨9,![0,14,15,13,10,6,7,19,20,21,4],![2,6,16,26,4,14,3,18,28,38,8]⟩
def data1629 : PartitionData E W := ⟨2,![cycle1629_0,cycle1629_1]⟩
lemma valid_data1629 : data1629.Valid src1629 dst1629 Finset.univ := by decide +kernel

def src1630 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1630 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1630_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1630_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle1630_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1630_3 : CycleData E W := ⟨3,![3,18,8,15,13],![4,8,18,16,26]⟩
def cycle1630_4 : CycleData E W := ⟨2,![4,21,11,5],![2,8,28,14]⟩
def cycle1630_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1630 : PartitionData E W := ⟨6,![cycle1630_0,cycle1630_1,cycle1630_2,cycle1630_3,cycle1630_4,cycle1630_5]⟩
lemma valid_data1630 : data1630.Valid src1630 dst1630 Finset.univ := by decide +kernel

def src1631 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1631 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1631_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1631_1 : CycleData E W := ⟨2,![1,17,20,7],![3,6,38,18]⟩
def cycle1631_2 : CycleData E W := ⟨1,![2,10,6],![3,4,14]⟩
def cycle1631_3 : CycleData E W := ⟨2,![3,21,16,13],![4,8,38,26]⟩
def cycle1631_4 : CycleData E W := ⟨2,![4,18,11,5],![2,8,28,14]⟩
def cycle1631_5 : CycleData E W := ⟨2,![8,19,12,15],![16,18,28,26]⟩
def data1631 : PartitionData E W := ⟨6,![cycle1631_0,cycle1631_1,cycle1631_2,cycle1631_3,cycle1631_4,cycle1631_5]⟩
lemma valid_data1631 : data1631.Valid src1631 dst1631 Finset.univ := by decide +kernel

def src1632 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1632 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1632_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1632_1 : CycleData E W := ⟨2,![1,17,13,2],![3,6,26,4]⟩
def cycle1632_2 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle1632_3 : CycleData E W := ⟨2,![6,11,19,7],![3,14,28,18]⟩
def cycle1632_4 : CycleData E W := ⟨2,![18,8,15,21],![8,18,16,38]⟩
def cycle1632_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1632 : PartitionData E W := ⟨6,![cycle1632_0,cycle1632_1,cycle1632_2,cycle1632_3,cycle1632_4,cycle1632_5]⟩
lemma valid_data1632 : data1632.Valid src1632 dst1632 Finset.univ := by decide +kernel

def src1633 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1633 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1633_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1633_1 : CycleData E W := ⟨2,![1,17,13,2],![3,6,26,4]⟩
def cycle1633_2 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle1633_3 : CycleData E W := ⟨3,![6,11,21,18,7],![3,14,28,8,18]⟩
def cycle1633_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1633_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1633 : PartitionData E W := ⟨6,![cycle1633_0,cycle1633_1,cycle1633_2,cycle1633_3,cycle1633_4,cycle1633_5]⟩
lemma valid_data1633 : data1633.Valid src1633 dst1633 Finset.univ := by decide +kernel

def src1634 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1634 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1634_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1634_1 : CycleData E W := ⟨2,![1,17,13,2],![3,6,26,4]⟩
def cycle1634_2 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle1634_3 : CycleData E W := ⟨2,![6,11,19,7],![3,14,28,18]⟩
def cycle1634_4 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def cycle1634_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1634 : PartitionData E W := ⟨6,![cycle1634_0,cycle1634_1,cycle1634_2,cycle1634_3,cycle1634_4,cycle1634_5]⟩
lemma valid_data1634 : data1634.Valid src1634 dst1634 Finset.univ := by decide +kernel

def src1635 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1635 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1635_0 : CycleData E W := ⟨9,![0,17,16,15,12,11,10,2,7,18,4],![2,6,38,16,26,28,14,4,3,18,8]⟩
def cycle1635_1 : CycleData E W := ⟨9,![5,6,1,14,13,3,21,20,19,8,9],![2,14,3,6,26,4,8,38,28,18,16]⟩
def data1635 : PartitionData E W := ⟨2,![cycle1635_0,cycle1635_1]⟩
lemma valid_data1635 : data1635.Valid src1635 dst1635 Finset.univ := by decide +kernel

def src1636 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1636 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1636_0 : CycleData E W := ⟨9,![0,17,16,15,12,11,10,2,7,18,4],![2,6,38,16,26,28,14,4,3,18,8]⟩
def cycle1636_1 : CycleData E W := ⟨9,![5,6,1,14,13,3,21,20,19,8,9],![2,14,3,6,26,4,8,28,38,18,16]⟩
def data1636 : PartitionData E W := ⟨2,![cycle1636_0,cycle1636_1]⟩
lemma valid_data1636 : data1636.Valid src1636 dst1636 Finset.univ := by decide +kernel

def src1637 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1637 : E → W := ![6,3,4,8,2,14,3,18,16,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1637_0 : CycleData E W := ⟨9,![0,17,16,8,7,6,10,13,12,18,4],![2,6,38,16,18,3,14,4,26,28,8]⟩
def cycle1637_1 : CycleData E W := ⟨9,![5,11,19,20,21,3,2,1,14,15,9],![2,14,28,18,38,8,4,3,6,26,16]⟩
def data1637 : PartitionData E W := ⟨2,![cycle1637_0,cycle1637_1]⟩
lemma valid_data1637 : data1637.Valid src1637 dst1637 Finset.univ := by decide +kernel

def src1638 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1638 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1638_0 : CycleData E W := ⟨9,![4,18,7,6,12,13,10,16,17,14,9],![2,8,18,3,14,28,4,26,38,6,16]⟩
def cycle1638_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,8,15,11,5],![2,6,3,4,8,38,28,18,16,26,14]⟩
def data1638 : PartitionData E W := ⟨2,![cycle1638_0,cycle1638_1]⟩
lemma valid_data1638 : data1638.Valid src1638 dst1638 Finset.univ := by decide +kernel

def src1639 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1639 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1639_0 : CycleData E W := ⟨9,![4,18,7,6,12,13,10,16,17,14,9],![2,8,18,3,14,28,4,26,38,6,16]⟩
def cycle1639_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,8,15,11,5],![2,6,3,4,8,28,38,18,16,26,14]⟩
def data1639 : PartitionData E W := ⟨2,![cycle1639_0,cycle1639_1]⟩
lemma valid_data1639 : data1639.Valid src1639 dst1639 Finset.univ := by decide +kernel

def src1640 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1640 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1640_0 : CycleData E W := ⟨9,![5,12,18,3,10,16,17,1,7,8,9],![2,14,28,8,4,26,38,6,3,18,16]⟩
def cycle1640_1 : CycleData E W := ⟨9,![0,14,15,11,6,2,13,19,20,21,4],![2,6,16,26,14,3,4,28,18,38,8]⟩
def data1640 : PartitionData E W := ⟨2,![cycle1640_0,cycle1640_1]⟩
lemma valid_data1640 : data1640.Valid src1640 dst1640 Finset.univ := by decide +kernel

def src1641 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1641 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1641_0 : CycleData E W := ⟨9,![0,1,2,13,12,11,16,15,8,18,4],![2,6,3,4,28,14,26,38,16,18,8]⟩
def cycle1641_1 : CycleData E W := ⟨9,![5,6,7,19,20,21,3,10,17,14,9],![2,14,3,18,28,38,8,4,26,6,16]⟩
def data1641 : PartitionData E W := ⟨2,![cycle1641_0,cycle1641_1]⟩
lemma valid_data1641 : data1641.Valid src1641 dst1641 Finset.univ := by decide +kernel

def src1642 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1642 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1642_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1642_1 : CycleData E W := ⟨2,![1,17,10,2],![3,6,26,4]⟩
def cycle1642_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1642_3 : CycleData E W := ⟨3,![4,18,7,6,5],![2,8,18,3,14]⟩
def cycle1642_4 : CycleData E W := ⟨1,![8,19,15],![16,18,38]⟩
def cycle1642_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1642 : PartitionData E W := ⟨6,![cycle1642_0,cycle1642_1,cycle1642_2,cycle1642_3,cycle1642_4,cycle1642_5]⟩
lemma valid_data1642 : data1642.Valid src1642 dst1642 Finset.univ := by decide +kernel

def src1643 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1643 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1643_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1643_1 : CycleData E W := ⟨2,![1,17,10,2],![3,6,26,4]⟩
def cycle1643_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1643_3 : CycleData E W := ⟨3,![4,21,16,11,5],![2,8,38,26,14]⟩
def cycle1643_4 : CycleData E W := ⟨2,![6,12,19,7],![3,14,28,18]⟩
def cycle1643_5 : CycleData E W := ⟨1,![8,20,15],![16,18,38]⟩
def data1643 : PartitionData E W := ⟨6,![cycle1643_0,cycle1643_1,cycle1643_2,cycle1643_3,cycle1643_4,cycle1643_5]⟩
lemma valid_data1643 : data1643.Valid src1643 dst1643 Finset.univ := by decide +kernel

def src1644 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1644 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1644_0 : CycleData E W := ⟨9,![4,18,7,6,12,13,10,14,17,16,9],![2,8,18,3,14,28,4,26,6,38,16]⟩
def cycle1644_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,8,15,11,5],![2,6,3,4,8,38,28,18,16,26,14]⟩
def data1644 : PartitionData E W := ⟨2,![cycle1644_0,cycle1644_1]⟩
lemma valid_data1644 : data1644.Valid src1644 dst1644 Finset.univ := by decide +kernel

def src1645 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1645 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1645_0 : CycleData E W := ⟨9,![4,18,7,6,12,13,10,14,17,16,9],![2,8,18,3,14,28,4,26,6,38,16]⟩
def cycle1645_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,8,15,11,5],![2,6,3,4,8,28,38,18,16,26,14]⟩
def data1645 : PartitionData E W := ⟨2,![cycle1645_0,cycle1645_1]⟩
lemma valid_data1645 : data1645.Valid src1645 dst1645 Finset.univ := by decide +kernel

def src1646 : E → W := ![2,6,3,4,8,2,14,3,18,16,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1646 : E → W := ![6,3,4,8,2,14,3,18,16,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1646_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1646_1 : CycleData E W := ⟨2,![1,14,10,2],![3,6,26,4]⟩
def cycle1646_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1646_3 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle1646_4 : CycleData E W := ⟨2,![6,12,19,7],![3,14,28,18]⟩
def cycle1646_5 : CycleData E W := ⟨1,![8,20,16],![16,18,38]⟩
def data1646 : PartitionData E W := ⟨6,![cycle1646_0,cycle1646_1,cycle1646_2,cycle1646_3,cycle1646_4,cycle1646_5]⟩
lemma valid_data1646 : data1646.Valid src1646 dst1646 Finset.univ := by decide +kernel

def src1647 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1647 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1647_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1647_1 : CycleData E W := ⟨1,![1,14,7],![3,6,16]⟩
def cycle1647_2 : CycleData E W := ⟨3,![5,10,2,8,9],![2,14,4,3,18]⟩
def cycle1647_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle1647_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1647_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1647 : PartitionData E W := ⟨6,![cycle1647_0,cycle1647_1,cycle1647_2,cycle1647_3,cycle1647_4,cycle1647_5]⟩
lemma valid_data1647 : data1647.Valid src1647 dst1647 Finset.univ := by decide +kernel

def src1648 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1648 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1648_0 : CycleData E W := ⟨3,![0,1,2,10,5],![2,6,3,4,14]⟩
def cycle1648_1 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1648_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1648_3 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1648_4 : CycleData E W := ⟨3,![7,14,17,19,8],![3,16,6,38,18]⟩
def cycle1648_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1648 : PartitionData E W := ⟨6,![cycle1648_0,cycle1648_1,cycle1648_2,cycle1648_3,cycle1648_4,cycle1648_5]⟩
lemma valid_data1648 : data1648.Valid src1648 dst1648 Finset.univ := by decide +kernel

def src1649 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1649 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1649_0 : CycleData E W := ⟨2,![0,17,20,9],![2,6,38,18]⟩
def cycle1649_1 : CycleData E W := ⟨1,![1,14,7],![3,6,16]⟩
def cycle1649_2 : CycleData E W := ⟨2,![2,13,19,8],![3,4,28,18]⟩
def cycle1649_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle1649_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1649_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1649 : PartitionData E W := ⟨6,![cycle1649_0,cycle1649_1,cycle1649_2,cycle1649_3,cycle1649_4,cycle1649_5]⟩
lemma valid_data1649 : data1649.Valid src1649 dst1649 Finset.univ := by decide +kernel

def src1650 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1650 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1650_0 : CycleData E W := ⟨2,![0,17,11,5],![2,6,26,14]⟩
def cycle1650_1 : CycleData E W := ⟨1,![1,14,7],![3,6,16]⟩
def cycle1650_2 : CycleData E W := ⟨2,![2,13,19,8],![3,4,28,18]⟩
def cycle1650_3 : CycleData E W := ⟨3,![3,21,15,6,10],![4,8,38,16,14]⟩
def cycle1650_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1650_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1650 : PartitionData E W := ⟨6,![cycle1650_0,cycle1650_1,cycle1650_2,cycle1650_3,cycle1650_4,cycle1650_5]⟩
lemma valid_data1650 : data1650.Valid src1650 dst1650 Finset.univ := by decide +kernel

def src1651 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1651 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1651_0 : CycleData E W := ⟨3,![0,1,2,10,5],![2,6,3,4,14]⟩
def cycle1651_1 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1651_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1651_3 : CycleData E W := ⟨2,![14,6,11,17],![6,16,14,26]⟩
def cycle1651_4 : CycleData E W := ⟨2,![7,15,19,8],![3,16,38,18]⟩
def cycle1651_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1651 : PartitionData E W := ⟨6,![cycle1651_0,cycle1651_1,cycle1651_2,cycle1651_3,cycle1651_4,cycle1651_5]⟩
lemma valid_data1651 : data1651.Valid src1651 dst1651 Finset.univ := by decide +kernel

def src1652 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1652 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1652_0 : CycleData E W := ⟨9,![5,10,3,18,12,16,15,14,1,8,9],![2,14,4,8,28,26,38,16,6,3,18]⟩
def cycle1652_1 : CycleData E W := ⟨9,![0,17,11,6,7,2,13,19,20,21,4],![2,6,26,14,16,3,4,28,18,38,8]⟩
def data1652 : PartitionData E W := ⟨2,![cycle1652_0,cycle1652_1]⟩
lemma valid_data1652 : data1652.Valid src1652 dst1652 Finset.univ := by decide +kernel

def src1653 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1653 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1653_0 : CycleData E W := ⟨9,![4,18,8,2,13,12,14,17,16,6,5],![2,8,18,3,4,28,26,6,38,16,14]⟩
def cycle1653_1 : CycleData E W := ⟨9,![0,1,7,15,11,10,3,21,20,19,9],![2,6,3,16,26,14,4,8,38,28,18]⟩
def data1653 : PartitionData E W := ⟨2,![cycle1653_0,cycle1653_1]⟩
lemma valid_data1653 : data1653.Valid src1653 dst1653 Finset.univ := by decide +kernel

def src1654 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1654 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1654_0 : CycleData E W := ⟨3,![0,1,2,10,5],![2,6,3,4,14]⟩
def cycle1654_1 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1654_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1654_3 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1654_4 : CycleData E W := ⟨2,![7,16,19,8],![3,16,38,18]⟩
def cycle1654_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1654 : PartitionData E W := ⟨6,![cycle1654_0,cycle1654_1,cycle1654_2,cycle1654_3,cycle1654_4,cycle1654_5]⟩
lemma valid_data1654 : data1654.Valid src1654 dst1654 Finset.univ := by decide +kernel

def src1655 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1655 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1655_0 : CycleData E W := ⟨9,![5,6,16,17,14,12,18,3,2,8,9],![2,14,16,38,6,26,28,8,4,3,18]⟩
def cycle1655_1 : CycleData E W := ⟨9,![0,1,7,15,11,10,13,19,20,21,4],![2,6,3,16,26,14,4,28,18,38,8]⟩
def data1655 : PartitionData E W := ⟨2,![cycle1655_0,cycle1655_1]⟩
lemma valid_data1655 : data1655.Valid src1655 dst1655 Finset.univ := by decide +kernel

def src1656 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1656 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1656_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1656_1 : CycleData E W := ⟨1,![1,14,7],![3,6,16]⟩
def cycle1656_2 : CycleData E W := ⟨2,![2,3,18,8],![3,4,8,18]⟩
def cycle1656_3 : CycleData E W := ⟨2,![5,11,19,9],![2,14,28,18]⟩
def cycle1656_4 : CycleData E W := ⟨2,![10,6,15,13],![4,14,16,26]⟩
def cycle1656_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1656 : PartitionData E W := ⟨6,![cycle1656_0,cycle1656_1,cycle1656_2,cycle1656_3,cycle1656_4,cycle1656_5]⟩
lemma valid_data1656 : data1656.Valid src1656 dst1656 Finset.univ := by decide +kernel

def src1657 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1657 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1657_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,14]⟩
def cycle1657_1 : CycleData E W := ⟨2,![1,17,19,8],![3,6,38,18]⟩
def cycle1657_2 : CycleData E W := ⟨2,![2,13,15,7],![3,4,26,16]⟩
def cycle1657_3 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle1657_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1657_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1657 : PartitionData E W := ⟨6,![cycle1657_0,cycle1657_1,cycle1657_2,cycle1657_3,cycle1657_4,cycle1657_5]⟩
lemma valid_data1657 : data1657.Valid src1657 dst1657 Finset.univ := by decide +kernel

def src1658 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1658 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1658_0 : CycleData E W := ⟨9,![0,17,16,13,3,18,11,6,7,8,9],![2,6,38,26,4,8,28,14,16,3,18]⟩
def cycle1658_1 : CycleData E W := ⟨9,![4,21,20,19,12,15,14,1,2,10,5],![2,8,38,18,28,26,16,6,3,4,14]⟩
def data1658 : PartitionData E W := ⟨2,![cycle1658_0,cycle1658_1]⟩
lemma valid_data1658 : data1658.Valid src1658 dst1658 Finset.univ := by decide +kernel

def src1659 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1659 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1659_0 : CycleData E W := ⟨9,![0,1,7,15,16,12,11,10,3,18,9],![2,6,3,16,38,26,28,14,4,8,18]⟩
def cycle1659_1 : CycleData E W := ⟨9,![4,21,20,19,8,2,13,17,14,6,5],![2,8,38,28,18,3,4,26,6,16,14]⟩
def data1659 : PartitionData E W := ⟨2,![cycle1659_0,cycle1659_1]⟩
lemma valid_data1659 : data1659.Valid src1659 dst1659 Finset.univ := by decide +kernel

def src1660 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1660 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1660_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,14]⟩
def cycle1660_1 : CycleData E W := ⟨2,![1,17,13,2],![3,6,26,4]⟩
def cycle1660_2 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle1660_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1660_4 : CycleData E W := ⟨2,![7,15,19,8],![3,16,38,18]⟩
def cycle1660_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1660 : PartitionData E W := ⟨6,![cycle1660_0,cycle1660_1,cycle1660_2,cycle1660_3,cycle1660_4,cycle1660_5]⟩
lemma valid_data1660 : data1660.Valid src1660 dst1660 Finset.univ := by decide +kernel

def src1661 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1661 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1661_0 : CycleData E W := ⟨9,![5,10,3,18,12,16,15,14,1,8,9],![2,14,4,8,28,26,38,16,6,3,18]⟩
def cycle1661_1 : CycleData E W := ⟨9,![0,17,13,2,7,6,11,19,20,21,4],![2,6,26,4,3,16,14,28,18,38,8]⟩
def data1661 : PartitionData E W := ⟨2,![cycle1661_0,cycle1661_1]⟩
lemma valid_data1661 : data1661.Valid src1661 dst1661 Finset.univ := by decide +kernel

def src1662 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1662 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1662_0 : CycleData E W := ⟨9,![5,11,12,15,16,17,1,2,3,18,9],![2,14,28,26,16,38,6,3,4,8,18]⟩
def cycle1662_1 : CycleData E W := ⟨9,![0,14,13,10,6,7,8,19,20,21,4],![2,6,26,4,14,16,3,18,28,38,8]⟩
def data1662 : PartitionData E W := ⟨2,![cycle1662_0,cycle1662_1]⟩
lemma valid_data1662 : data1662.Valid src1662 dst1662 Finset.univ := by decide +kernel

def src1663 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1663 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1663_0 : CycleData E W := ⟨9,![5,11,12,15,16,17,1,2,3,18,9],![2,14,28,26,16,38,6,3,4,8,18]⟩
def cycle1663_1 : CycleData E W := ⟨9,![0,14,13,10,6,7,8,19,20,21,4],![2,6,26,4,14,16,3,18,38,28,8]⟩
def data1663 : PartitionData E W := ⟨2,![cycle1663_0,cycle1663_1]⟩
lemma valid_data1663 : data1663.Valid src1663 dst1663 Finset.univ := by decide +kernel

def src1664 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1664 : E → W := ![6,3,4,8,2,14,16,3,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1664_0 : CycleData E W := ⟨9,![4,18,12,13,10,6,16,17,1,8,9],![2,8,28,26,4,14,16,38,6,3,18]⟩
def cycle1664_1 : CycleData E W := ⟨9,![0,14,15,7,2,3,21,20,19,11,5],![2,6,26,16,3,4,8,38,18,28,14]⟩
def data1664 : PartitionData E W := ⟨2,![cycle1664_0,cycle1664_1]⟩
lemma valid_data1664 : data1664.Valid src1664 dst1664 Finset.univ := by decide +kernel

def src1665 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1665 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1665_0 : CycleData E W := ⟨3,![0,17,20,12,5],![2,6,38,28,14]⟩
def cycle1665_1 : CycleData E W := ⟨1,![1,14,7],![3,6,16]⟩
def cycle1665_2 : CycleData E W := ⟨2,![2,13,19,8],![3,4,28,18]⟩
def cycle1665_3 : CycleData E W := ⟨2,![3,21,16,10],![4,8,38,26]⟩
def cycle1665_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1665_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data1665 : PartitionData E W := ⟨6,![cycle1665_0,cycle1665_1,cycle1665_2,cycle1665_3,cycle1665_4,cycle1665_5]⟩
lemma valid_data1665 : data1665.Valid src1665 dst1665 Finset.univ := by decide +kernel

def src1666 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1666 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1666_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,14]⟩
def cycle1666_1 : CycleData E W := ⟨2,![1,17,19,8],![3,6,38,18]⟩
def cycle1666_2 : CycleData E W := ⟨2,![2,10,15,7],![3,4,26,16]⟩
def cycle1666_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1666_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1666_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1666 : PartitionData E W := ⟨6,![cycle1666_0,cycle1666_1,cycle1666_2,cycle1666_3,cycle1666_4,cycle1666_5]⟩
lemma valid_data1666 : data1666.Valid src1666 dst1666 Finset.univ := by decide +kernel

def src1667 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1667 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1667_0 : CycleData E W := ⟨2,![0,17,20,9],![2,6,38,18]⟩
def cycle1667_1 : CycleData E W := ⟨1,![1,14,7],![3,6,16]⟩
def cycle1667_2 : CycleData E W := ⟨2,![2,13,19,8],![3,4,28,18]⟩
def cycle1667_3 : CycleData E W := ⟨2,![3,21,16,10],![4,8,38,26]⟩
def cycle1667_4 : CycleData E W := ⟨2,![4,18,12,5],![2,8,28,14]⟩
def cycle1667_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def data1667 : PartitionData E W := ⟨6,![cycle1667_0,cycle1667_1,cycle1667_2,cycle1667_3,cycle1667_4,cycle1667_5]⟩
lemma valid_data1667 : data1667.Valid src1667 dst1667 Finset.univ := by decide +kernel

def src1668 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1668 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1668_0 : CycleData E W := ⟨2,![0,17,11,5],![2,6,26,14]⟩
def cycle1668_1 : CycleData E W := ⟨1,![1,14,7],![3,6,16]⟩
def cycle1668_2 : CycleData E W := ⟨2,![2,13,19,8],![3,4,28,18]⟩
def cycle1668_3 : CycleData E W := ⟨2,![3,21,16,10],![4,8,38,26]⟩
def cycle1668_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1668_5 : CycleData E W := ⟨2,![6,15,20,12],![14,16,38,28]⟩
def data1668 : PartitionData E W := ⟨6,![cycle1668_0,cycle1668_1,cycle1668_2,cycle1668_3,cycle1668_4,cycle1668_5]⟩
lemma valid_data1668 : data1668.Valid src1668 dst1668 Finset.univ := by decide +kernel

def src1669 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1669 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1669_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,14]⟩
def cycle1669_1 : CycleData E W := ⟨2,![1,17,10,2],![3,6,26,4]⟩
def cycle1669_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1669_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1669_4 : CycleData E W := ⟨2,![7,15,19,8],![3,16,38,18]⟩
def cycle1669_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1669 : PartitionData E W := ⟨6,![cycle1669_0,cycle1669_1,cycle1669_2,cycle1669_3,cycle1669_4,cycle1669_5]⟩
lemma valid_data1669 : data1669.Valid src1669 dst1669 Finset.univ := by decide +kernel

def src1670 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1670 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1670_0 : CycleData E W := ⟨9,![5,12,18,3,10,16,15,14,1,8,9],![2,14,28,8,4,26,38,16,6,3,18]⟩
def cycle1670_1 : CycleData E W := ⟨9,![0,17,11,6,7,2,13,19,20,21,4],![2,6,26,14,16,3,4,28,18,38,8]⟩
def data1670 : PartitionData E W := ⟨2,![cycle1670_0,cycle1670_1]⟩
lemma valid_data1670 : data1670.Valid src1670 dst1670 Finset.univ := by decide +kernel

def src1671 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1671 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1671_0 : CycleData E W := ⟨9,![4,18,8,1,17,16,15,10,13,12,5],![2,8,18,3,6,38,16,26,4,28,14]⟩
def cycle1671_1 : CycleData E W := ⟨9,![0,14,11,6,7,2,3,21,20,19,9],![2,6,26,14,16,3,4,8,38,28,18]⟩
def data1671 : PartitionData E W := ⟨2,![cycle1671_0,cycle1671_1]⟩
lemma valid_data1671 : data1671.Valid src1671 dst1671 Finset.univ := by decide +kernel

def src1672 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1672 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1672_0 : CycleData E W := ⟨2,![0,14,11,5],![2,6,26,14]⟩
def cycle1672_1 : CycleData E W := ⟨2,![1,17,19,8],![3,6,38,18]⟩
def cycle1672_2 : CycleData E W := ⟨2,![2,10,15,7],![3,4,26,16]⟩
def cycle1672_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1672_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1672_5 : CycleData E W := ⟨2,![6,16,20,12],![14,16,38,28]⟩
def data1672 : PartitionData E W := ⟨6,![cycle1672_0,cycle1672_1,cycle1672_2,cycle1672_3,cycle1672_4,cycle1672_5]⟩
lemma valid_data1672 : data1672.Valid src1672 dst1672 Finset.univ := by decide +kernel

def src1673 : E → W := ![2,6,3,4,8,2,14,16,3,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1673 : E → W := ![6,3,4,8,2,14,16,3,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1673_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1673_1 : CycleData E W := ⟨2,![1,14,10,2],![3,6,26,4]⟩
def cycle1673_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1673_3 : CycleData E W := ⟨2,![5,12,19,9],![2,14,28,18]⟩
def cycle1673_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1673_5 : CycleData E W := ⟨2,![7,16,20,8],![3,16,38,18]⟩
def data1673 : PartitionData E W := ⟨6,![cycle1673_0,cycle1673_1,cycle1673_2,cycle1673_3,cycle1673_4,cycle1673_5]⟩
lemma valid_data1673 : data1673.Valid src1673 dst1673 Finset.univ := by decide +kernel

def src1674 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1674 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1674_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1674_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle1674_2 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle1674_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle1674_4 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle1674_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1674 : PartitionData E W := ⟨6,![cycle1674_0,cycle1674_1,cycle1674_2,cycle1674_3,cycle1674_4,cycle1674_5]⟩
lemma valid_data1674 : data1674.Valid src1674 dst1674 Finset.univ := by decide +kernel

def src1675 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1675 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1675_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1675_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle1675_2 : CycleData E W := ⟨3,![2,10,11,15,8],![3,4,14,26,16]⟩
def cycle1675_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1675_4 : CycleData E W := ⟨2,![4,18,6,5],![2,8,18,14]⟩
def cycle1675_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1675 : PartitionData E W := ⟨6,![cycle1675_0,cycle1675_1,cycle1675_2,cycle1675_3,cycle1675_4,cycle1675_5]⟩
lemma valid_data1675 : data1675.Valid src1675 dst1675 Finset.univ := by decide +kernel

def src1676 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1676 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1676_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1676_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle1676_2 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle1676_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1676_4 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle1676_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data1676 : PartitionData E W := ⟨6,![cycle1676_0,cycle1676_1,cycle1676_2,cycle1676_3,cycle1676_4,cycle1676_5]⟩
lemma valid_data1676 : data1676.Valid src1676 dst1676 Finset.univ := by decide +kernel

def src1677 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1677 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1677_0 : CycleData E W := ⟨2,![0,17,11,5],![2,6,26,14]⟩
def cycle1677_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle1677_2 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle1677_3 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle1677_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle1677_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1677 : PartitionData E W := ⟨6,![cycle1677_0,cycle1677_1,cycle1677_2,cycle1677_3,cycle1677_4,cycle1677_5]⟩
lemma valid_data1677 : data1677.Valid src1677 dst1677 Finset.univ := by decide +kernel

def src1678 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1678 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1678_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1678_1 : CycleData E W := ⟨3,![1,17,11,10,2],![3,6,26,14,4]⟩
def cycle1678_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1678_3 : CycleData E W := ⟨2,![4,18,6,5],![2,8,18,14]⟩
def cycle1678_4 : CycleData E W := ⟨2,![7,19,15,8],![3,18,38,16]⟩
def cycle1678_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1678 : PartitionData E W := ⟨6,![cycle1678_0,cycle1678_1,cycle1678_2,cycle1678_3,cycle1678_4,cycle1678_5]⟩
lemma valid_data1678 : data1678.Valid src1678 dst1678 Finset.univ := by decide +kernel

def src1679 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1679 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1679_0 : CycleData E W := ⟨2,![0,17,11,5],![2,6,26,14]⟩
def cycle1679_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle1679_2 : CycleData E W := ⟨2,![2,10,6,7],![3,4,14,18]⟩
def cycle1679_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1679_4 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle1679_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data1679 : PartitionData E W := ⟨6,![cycle1679_0,cycle1679_1,cycle1679_2,cycle1679_3,cycle1679_4,cycle1679_5]⟩
lemma valid_data1679 : data1679.Valid src1679 dst1679 Finset.univ := by decide +kernel

def src1680 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1680 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1680_0 : CycleData E W := ⟨9,![0,17,16,8,2,13,12,11,6,18,4],![2,6,38,16,3,4,28,26,14,18,8]⟩
def cycle1680_1 : CycleData E W := ⟨9,![5,10,3,21,20,19,7,1,14,15,9],![2,14,4,8,38,28,18,3,6,26,16]⟩
def data1680 : PartitionData E W := ⟨2,![cycle1680_0,cycle1680_1]⟩
lemma valid_data1680 : data1680.Valid src1680 dst1680 Finset.univ := by decide +kernel

def src1681 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1681 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1681_0 : CycleData E W := ⟨9,![0,17,16,8,2,13,12,11,6,18,4],![2,6,38,16,3,4,28,26,14,18,8]⟩
def cycle1681_1 : CycleData E W := ⟨9,![5,10,3,21,20,19,7,1,14,15,9],![2,14,4,8,28,38,18,3,6,26,16]⟩
def data1681 : PartitionData E W := ⟨2,![cycle1681_0,cycle1681_1]⟩
lemma valid_data1681 : data1681.Valid src1681 dst1681 Finset.univ := by decide +kernel

def src1682 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1682 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1682_0 : CycleData E W := ⟨9,![5,6,7,2,3,18,12,14,17,16,9],![2,14,18,3,4,8,28,26,6,38,16]⟩
def cycle1682_1 : CycleData E W := ⟨9,![0,1,8,15,11,10,13,19,20,21,4],![2,6,3,16,26,14,4,28,18,38,8]⟩
def data1682 : PartitionData E W := ⟨2,![cycle1682_0,cycle1682_1]⟩
lemma valid_data1682 : data1682.Valid src1682 dst1682 Finset.univ := by decide +kernel

def src1683 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1683 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1683_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1683_1 : CycleData E W := ⟨3,![1,17,21,18,7],![3,6,38,8,18]⟩
def cycle1683_2 : CycleData E W := ⟨2,![2,13,15,8],![3,4,26,16]⟩
def cycle1683_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle1683_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle1683_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1683 : PartitionData E W := ⟨6,![cycle1683_0,cycle1683_1,cycle1683_2,cycle1683_3,cycle1683_4,cycle1683_5]⟩
lemma valid_data1683 : data1683.Valid src1683 dst1683 Finset.univ := by decide +kernel

def src1684 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1684 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1684_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1684_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle1684_2 : CycleData E W := ⟨2,![2,13,15,8],![3,4,26,16]⟩
def cycle1684_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle1684_4 : CycleData E W := ⟨2,![18,6,11,21],![8,18,14,28]⟩
def cycle1684_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1684 : PartitionData E W := ⟨6,![cycle1684_0,cycle1684_1,cycle1684_2,cycle1684_3,cycle1684_4,cycle1684_5]⟩
lemma valid_data1684 : data1684.Valid src1684 dst1684 Finset.univ := by decide +kernel

def src1685 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1685 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1685_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1685_1 : CycleData E W := ⟨2,![1,17,20,7],![3,6,38,18]⟩
def cycle1685_2 : CycleData E W := ⟨2,![2,13,15,8],![3,4,26,16]⟩
def cycle1685_3 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle1685_4 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle1685_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1685 : PartitionData E W := ⟨6,![cycle1685_0,cycle1685_1,cycle1685_2,cycle1685_3,cycle1685_4,cycle1685_5]⟩
lemma valid_data1685 : data1685.Valid src1685 dst1685 Finset.univ := by decide +kernel

def src1686 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1686 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1686_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1686_1 : CycleData E W := ⟨2,![1,17,13,2],![3,6,26,4]⟩
def cycle1686_2 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle1686_3 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle1686_4 : CycleData E W := ⟨3,![7,18,21,15,8],![3,18,8,38,16]⟩
def cycle1686_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1686 : PartitionData E W := ⟨6,![cycle1686_0,cycle1686_1,cycle1686_2,cycle1686_3,cycle1686_4,cycle1686_5]⟩
lemma valid_data1686 : data1686.Valid src1686 dst1686 Finset.univ := by decide +kernel

def src1687 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1687 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1687_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1687_1 : CycleData E W := ⟨2,![1,17,13,2],![3,6,26,4]⟩
def cycle1687_2 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle1687_3 : CycleData E W := ⟨2,![18,6,11,21],![8,18,14,28]⟩
def cycle1687_4 : CycleData E W := ⟨2,![7,19,15,8],![3,18,38,16]⟩
def cycle1687_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1687 : PartitionData E W := ⟨6,![cycle1687_0,cycle1687_1,cycle1687_2,cycle1687_3,cycle1687_4,cycle1687_5]⟩
lemma valid_data1687 : data1687.Valid src1687 dst1687 Finset.univ := by decide +kernel

def src1688 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1688 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1688_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1688_1 : CycleData E W := ⟨2,![1,17,13,2],![3,6,26,4]⟩
def cycle1688_2 : CycleData E W := ⟨2,![4,3,10,5],![2,8,4,14]⟩
def cycle1688_3 : CycleData E W := ⟨1,![6,19,11],![14,18,28]⟩
def cycle1688_4 : CycleData E W := ⟨2,![7,20,15,8],![3,18,38,16]⟩
def cycle1688_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1688 : PartitionData E W := ⟨6,![cycle1688_0,cycle1688_1,cycle1688_2,cycle1688_3,cycle1688_4,cycle1688_5]⟩
lemma valid_data1688 : data1688.Valid src1688 dst1688 Finset.univ := by decide +kernel

def src1689 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1689 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1689_0 : CycleData E W := ⟨9,![0,17,16,8,2,13,12,11,6,18,4],![2,6,38,16,3,4,26,28,14,18,8]⟩
def cycle1689_1 : CycleData E W := ⟨9,![5,10,3,21,20,19,7,1,14,15,9],![2,14,4,8,38,28,18,3,6,26,16]⟩
def data1689 : PartitionData E W := ⟨2,![cycle1689_0,cycle1689_1]⟩
lemma valid_data1689 : data1689.Valid src1689 dst1689 Finset.univ := by decide +kernel

def src1690 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1690 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1690_0 : CycleData E W := ⟨9,![0,17,16,8,2,13,12,11,6,18,4],![2,6,38,16,3,4,26,28,14,18,8]⟩
def cycle1690_1 : CycleData E W := ⟨9,![5,10,3,21,20,19,7,1,14,15,9],![2,14,4,8,28,38,18,3,6,26,16]⟩
def data1690 : PartitionData E W := ⟨2,![cycle1690_0,cycle1690_1]⟩
lemma valid_data1690 : data1690.Valid src1690 dst1690 Finset.univ := by decide +kernel

def src1691 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1691 : E → W := ![6,3,4,8,2,14,18,3,16,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1691_0 : CycleData E W := ⟨9,![0,17,16,8,7,6,10,13,12,18,4],![2,6,38,16,3,18,14,4,26,28,8]⟩
def cycle1691_1 : CycleData E W := ⟨9,![5,11,19,20,21,3,2,1,14,15,9],![2,14,28,18,38,8,4,3,6,26,16]⟩
def data1691 : PartitionData E W := ⟨2,![cycle1691_0,cycle1691_1]⟩
lemma valid_data1691 : data1691.Valid src1691 dst1691 Finset.univ := by decide +kernel

def src1692 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1692 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1692_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1692_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle1692_2 : CycleData E W := ⟨2,![2,3,18,7],![3,4,8,18]⟩
def cycle1692_3 : CycleData E W := ⟨2,![5,11,15,9],![2,14,26,16]⟩
def cycle1692_4 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def cycle1692_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1692 : PartitionData E W := ⟨6,![cycle1692_0,cycle1692_1,cycle1692_2,cycle1692_3,cycle1692_4,cycle1692_5]⟩
lemma valid_data1692 : data1692.Valid src1692 dst1692 Finset.univ := by decide +kernel

def src1693 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1693 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1693_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1693_1 : CycleData E W := ⟨2,![1,17,19,7],![3,6,38,18]⟩
def cycle1693_2 : CycleData E W := ⟨2,![2,10,15,8],![3,4,26,16]⟩
def cycle1693_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1693_4 : CycleData E W := ⟨2,![4,18,6,5],![2,8,18,14]⟩
def cycle1693_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1693 : PartitionData E W := ⟨6,![cycle1693_0,cycle1693_1,cycle1693_2,cycle1693_3,cycle1693_4,cycle1693_5]⟩
lemma valid_data1693 : data1693.Valid src1693 dst1693 Finset.univ := by decide +kernel

def src1694 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1694 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1694_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1694_1 : CycleData E W := ⟨2,![1,17,20,7],![3,6,38,18]⟩
def cycle1694_2 : CycleData E W := ⟨2,![2,10,15,8],![3,4,26,16]⟩
def cycle1694_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1694_4 : CycleData E W := ⟨3,![4,21,16,11,5],![2,8,38,26,14]⟩
def cycle1694_5 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def data1694 : PartitionData E W := ⟨6,![cycle1694_0,cycle1694_1,cycle1694_2,cycle1694_3,cycle1694_4,cycle1694_5]⟩
lemma valid_data1694 : data1694.Valid src1694 dst1694 Finset.univ := by decide +kernel

def src1695 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1695 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1695_0 : CycleData E W := ⟨2,![0,17,11,5],![2,6,26,14]⟩
def cycle1695_1 : CycleData E W := ⟨1,![1,14,8],![3,6,16]⟩
def cycle1695_2 : CycleData E W := ⟨2,![2,3,18,7],![3,4,8,18]⟩
def cycle1695_3 : CycleData E W := ⟨2,![4,21,15,9],![2,8,38,16]⟩
def cycle1695_4 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def cycle1695_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1695 : PartitionData E W := ⟨6,![cycle1695_0,cycle1695_1,cycle1695_2,cycle1695_3,cycle1695_4,cycle1695_5]⟩
lemma valid_data1695 : data1695.Valid src1695 dst1695 Finset.univ := by decide +kernel

def src1696 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1696 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1696_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1696_1 : CycleData E W := ⟨2,![1,17,10,2],![3,6,26,4]⟩
def cycle1696_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1696_3 : CycleData E W := ⟨2,![4,18,6,5],![2,8,18,14]⟩
def cycle1696_4 : CycleData E W := ⟨2,![7,19,15,8],![3,18,38,16]⟩
def cycle1696_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1696 : PartitionData E W := ⟨6,![cycle1696_0,cycle1696_1,cycle1696_2,cycle1696_3,cycle1696_4,cycle1696_5]⟩
lemma valid_data1696 : data1696.Valid src1696 dst1696 Finset.univ := by decide +kernel

def src1697 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1697 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1697_0 : CycleData E W := ⟨1,![0,14,9],![2,6,16]⟩
def cycle1697_1 : CycleData E W := ⟨2,![1,17,10,2],![3,6,26,4]⟩
def cycle1697_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1697_3 : CycleData E W := ⟨3,![4,21,16,11,5],![2,8,38,26,14]⟩
def cycle1697_4 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def cycle1697_5 : CycleData E W := ⟨2,![7,20,15,8],![3,18,38,16]⟩
def data1697 : PartitionData E W := ⟨6,![cycle1697_0,cycle1697_1,cycle1697_2,cycle1697_3,cycle1697_4,cycle1697_5]⟩
lemma valid_data1697 : data1697.Valid src1697 dst1697 Finset.univ := by decide +kernel

def src1698 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1698 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1698_0 : CycleData E W := ⟨9,![4,18,7,8,16,17,14,10,13,12,5],![2,8,18,3,16,38,6,26,4,28,14]⟩
def cycle1698_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,6,11,15,9],![2,6,3,4,8,38,28,18,14,26,16]⟩
def data1698 : PartitionData E W := ⟨2,![cycle1698_0,cycle1698_1]⟩
lemma valid_data1698 : data1698.Valid src1698 dst1698 Finset.univ := by decide +kernel

def src1699 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1699 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1699_0 : CycleData E W := ⟨9,![4,18,7,8,16,17,14,10,13,12,5],![2,8,18,3,16,38,6,26,4,28,14]⟩
def cycle1699_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,6,11,15,9],![2,6,3,4,8,28,38,18,14,26,16]⟩
def data1699 : PartitionData E W := ⟨2,![cycle1699_0,cycle1699_1]⟩
lemma valid_data1699 : data1699.Valid src1699 dst1699 Finset.univ := by decide +kernel

def src1700 : E → W := ![2,6,3,4,8,2,14,18,3,16,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1700 : E → W := ![6,3,4,8,2,14,18,3,16,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1700_0 : CycleData E W := ⟨2,![0,14,11,5],![2,6,26,14]⟩
def cycle1700_1 : CycleData E W := ⟨2,![1,17,20,7],![3,6,38,18]⟩
def cycle1700_2 : CycleData E W := ⟨2,![2,10,15,8],![3,4,26,16]⟩
def cycle1700_3 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1700_4 : CycleData E W := ⟨2,![4,21,16,9],![2,8,38,16]⟩
def cycle1700_5 : CycleData E W := ⟨1,![6,19,12],![14,18,28]⟩
def data1700 : PartitionData E W := ⟨6,![cycle1700_0,cycle1700_1,cycle1700_2,cycle1700_3,cycle1700_4,cycle1700_5]⟩
lemma valid_data1700 : data1700.Valid src1700 dst1700 Finset.univ := by decide +kernel

def src1701 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1701 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1701_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle1701_1 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1701_2 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle1701_3 : CycleData E W := ⟨3,![4,21,17,14,5],![2,8,38,6,16]⟩
def cycle1701_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1701_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1701 : PartitionData E W := ⟨6,![cycle1701_0,cycle1701_1,cycle1701_2,cycle1701_3,cycle1701_4,cycle1701_5]⟩
lemma valid_data1701 : data1701.Valid src1701 dst1701 Finset.univ := by decide +kernel

def src1702 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1702 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1702_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1702_1 : CycleData E W := ⟨2,![1,17,19,8],![3,6,38,18]⟩
def cycle1702_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1702_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1702_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1702_5 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1702_6 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1702 : PartitionData E W := ⟨7,![cycle1702_0,cycle1702_1,cycle1702_2,cycle1702_3,cycle1702_4,cycle1702_5,cycle1702_6]⟩
lemma valid_data1702 : data1702.Valid src1702 dst1702 Finset.univ := by decide +kernel

def src1703 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1703 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1703_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle1703_1 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1703_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1703_3 : CycleData E W := ⟨3,![4,21,17,14,5],![2,8,38,6,16]⟩
def cycle1703_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1703_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data1703 : PartitionData E W := ⟨6,![cycle1703_0,cycle1703_1,cycle1703_2,cycle1703_3,cycle1703_4,cycle1703_5]⟩
lemma valid_data1703 : data1703.Valid src1703 dst1703 Finset.univ := by decide +kernel

def src1704 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1704 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1704_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle1704_1 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1704_2 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle1704_3 : CycleData E W := ⟨2,![4,21,15,5],![2,8,38,16]⟩
def cycle1704_4 : CycleData E W := ⟨2,![14,6,11,17],![6,16,14,26]⟩
def cycle1704_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1704 : PartitionData E W := ⟨6,![cycle1704_0,cycle1704_1,cycle1704_2,cycle1704_3,cycle1704_4,cycle1704_5]⟩
lemma valid_data1704 : data1704.Valid src1704 dst1704 Finset.univ := by decide +kernel

def src1705 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1705 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1705_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle1705_1 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1705_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1705_3 : CycleData E W := ⟨3,![4,18,19,15,5],![2,8,18,38,16]⟩
def cycle1705_4 : CycleData E W := ⟨2,![14,6,11,17],![6,16,14,26]⟩
def cycle1705_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1705 : PartitionData E W := ⟨6,![cycle1705_0,cycle1705_1,cycle1705_2,cycle1705_3,cycle1705_4,cycle1705_5]⟩
lemma valid_data1705 : data1705.Valid src1705 dst1705 Finset.univ := by decide +kernel

def src1706 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1706 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1706_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle1706_1 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1706_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1706_3 : CycleData E W := ⟨2,![4,21,15,5],![2,8,38,16]⟩
def cycle1706_4 : CycleData E W := ⟨2,![14,6,11,17],![6,16,14,26]⟩
def cycle1706_5 : CycleData E W := ⟨2,![19,12,16,20],![18,28,26,38]⟩
def data1706 : PartitionData E W := ⟨6,![cycle1706_0,cycle1706_1,cycle1706_2,cycle1706_3,cycle1706_4,cycle1706_5]⟩
lemma valid_data1706 : data1706.Valid src1706 dst1706 Finset.univ := by decide +kernel

def src1707 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1707 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1707_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle1707_1 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1707_2 : CycleData E W := ⟨2,![3,18,19,13],![4,8,18,28]⟩
def cycle1707_3 : CycleData E W := ⟨2,![4,21,16,5],![2,8,38,16]⟩
def cycle1707_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1707_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1707 : PartitionData E W := ⟨6,![cycle1707_0,cycle1707_1,cycle1707_2,cycle1707_3,cycle1707_4,cycle1707_5]⟩
lemma valid_data1707 : data1707.Valid src1707 dst1707 Finset.univ := by decide +kernel

def src1708 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1708 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1708_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle1708_1 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1708_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1708_3 : CycleData E W := ⟨3,![4,18,19,16,5],![2,8,18,38,16]⟩
def cycle1708_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1708_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1708 : PartitionData E W := ⟨6,![cycle1708_0,cycle1708_1,cycle1708_2,cycle1708_3,cycle1708_4,cycle1708_5]⟩
lemma valid_data1708 : data1708.Valid src1708 dst1708 Finset.univ := by decide +kernel

def src1709 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1709 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1709_0 : CycleData E W := ⟨2,![0,1,8,9],![2,6,3,18]⟩
def cycle1709_1 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1709_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1709_3 : CycleData E W := ⟨2,![4,21,16,5],![2,8,38,16]⟩
def cycle1709_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1709_5 : CycleData E W := ⟨3,![14,12,19,20,17],![6,26,28,18,38]⟩
def data1709 : PartitionData E W := ⟨6,![cycle1709_0,cycle1709_1,cycle1709_2,cycle1709_3,cycle1709_4,cycle1709_5]⟩
lemma valid_data1709 : data1709.Valid src1709 dst1709 Finset.univ := by decide +kernel

def src1710 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1710 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1710_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1710_1 : CycleData E W := ⟨3,![1,17,20,19,8],![3,6,38,28,18]⟩
def cycle1710_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1710_3 : CycleData E W := ⟨2,![3,21,16,13],![4,8,38,26]⟩
def cycle1710_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1710_5 : CycleData E W := ⟨2,![6,15,12,11],![14,16,26,28]⟩
def data1710 : PartitionData E W := ⟨6,![cycle1710_0,cycle1710_1,cycle1710_2,cycle1710_3,cycle1710_4,cycle1710_5]⟩
lemma valid_data1710 : data1710.Valid src1710 dst1710 Finset.univ := by decide +kernel

def src1711 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1711 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1711_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1711_1 : CycleData E W := ⟨2,![1,17,19,8],![3,6,38,18]⟩
def cycle1711_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1711_3 : CycleData E W := ⟨2,![3,21,12,13],![4,8,28,26]⟩
def cycle1711_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1711_5 : CycleData E W := ⟨3,![6,15,16,20,11],![14,16,26,38,28]⟩
def data1711 : PartitionData E W := ⟨6,![cycle1711_0,cycle1711_1,cycle1711_2,cycle1711_3,cycle1711_4,cycle1711_5]⟩
lemma valid_data1711 : data1711.Valid src1711 dst1711 Finset.univ := by decide +kernel

def src1712 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1712 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1712_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1712_1 : CycleData E W := ⟨2,![1,17,20,8],![3,6,38,18]⟩
def cycle1712_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1712_3 : CycleData E W := ⟨2,![3,21,16,13],![4,8,38,26]⟩
def cycle1712_4 : CycleData E W := ⟨2,![4,18,19,9],![2,8,28,18]⟩
def cycle1712_5 : CycleData E W := ⟨2,![6,15,12,11],![14,16,26,28]⟩
def data1712 : PartitionData E W := ⟨6,![cycle1712_0,cycle1712_1,cycle1712_2,cycle1712_3,cycle1712_4,cycle1712_5]⟩
lemma valid_data1712 : data1712.Valid src1712 dst1712 Finset.univ := by decide +kernel

def src1713 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1713 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1713_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1713_1 : CycleData E W := ⟨2,![1,17,13,2],![3,6,26,4]⟩
def cycle1713_2 : CycleData E W := ⟨3,![3,21,15,6,10],![4,8,38,16,14]⟩
def cycle1713_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1713_4 : CycleData E W := ⟨2,![7,11,19,8],![3,14,28,18]⟩
def cycle1713_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1713 : PartitionData E W := ⟨6,![cycle1713_0,cycle1713_1,cycle1713_2,cycle1713_3,cycle1713_4,cycle1713_5]⟩
lemma valid_data1713 : data1713.Valid src1713 dst1713 Finset.univ := by decide +kernel

def src1714 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1714 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1714_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1714_1 : CycleData E W := ⟨2,![1,17,13,2],![3,6,26,4]⟩
def cycle1714_2 : CycleData E W := ⟨2,![3,21,11,10],![4,8,28,14]⟩
def cycle1714_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1714_4 : CycleData E W := ⟨3,![7,6,15,19,8],![3,14,16,38,18]⟩
def cycle1714_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1714 : PartitionData E W := ⟨6,![cycle1714_0,cycle1714_1,cycle1714_2,cycle1714_3,cycle1714_4,cycle1714_5]⟩
lemma valid_data1714 : data1714.Valid src1714 dst1714 Finset.univ := by decide +kernel

def src1715 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1715 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1715_0 : CycleData E W := ⟨9,![0,14,15,16,13,3,18,11,7,8,9],![2,6,16,38,26,4,8,28,14,3,18]⟩
def cycle1715_1 : CycleData E W := ⟨9,![4,21,20,19,12,17,1,2,10,6,5],![2,8,38,18,28,26,6,3,4,14,16]⟩
def data1715 : PartitionData E W := ⟨2,![cycle1715_0,cycle1715_1]⟩
lemma valid_data1715 : data1715.Valid src1715 dst1715 Finset.univ := by decide +kernel

def src1716 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1716 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1716_0 : CycleData E W := ⟨9,![0,17,16,6,11,12,13,2,8,18,4],![2,6,38,16,14,28,26,4,3,18,8]⟩
def cycle1716_1 : CycleData E W := ⟨9,![5,15,14,1,7,10,3,21,20,19,9],![2,16,26,6,3,14,4,8,38,28,18]⟩
def data1716 : PartitionData E W := ⟨2,![cycle1716_0,cycle1716_1]⟩
lemma valid_data1716 : data1716.Valid src1716 dst1716 Finset.univ := by decide +kernel

def src1717 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1717 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1717_0 : CycleData E W := ⟨2,![0,14,15,5],![2,6,26,16]⟩
def cycle1717_1 : CycleData E W := ⟨2,![1,17,19,8],![3,6,38,18]⟩
def cycle1717_2 : CycleData E W := ⟨1,![2,10,7],![3,4,14]⟩
def cycle1717_3 : CycleData E W := ⟨2,![3,21,12,13],![4,8,28,26]⟩
def cycle1717_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1717_5 : CycleData E W := ⟨2,![6,16,20,11],![14,16,38,28]⟩
def data1717 : PartitionData E W := ⟨6,![cycle1717_0,cycle1717_1,cycle1717_2,cycle1717_3,cycle1717_4,cycle1717_5]⟩
lemma valid_data1717 : data1717.Valid src1717 dst1717 Finset.univ := by decide +kernel

def src1718 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1718 : E → W := ![6,3,4,8,2,16,14,3,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1718_0 : CycleData E W := ⟨9,![4,18,12,14,17,16,6,10,2,8,9],![2,8,28,26,6,38,16,14,4,3,18]⟩
def cycle1718_1 : CycleData E W := ⟨9,![0,1,7,11,19,20,21,3,13,15,5],![2,6,3,14,28,18,38,8,4,26,16]⟩
def data1718 : PartitionData E W := ⟨2,![cycle1718_0,cycle1718_1]⟩
lemma valid_data1718 : data1718.Valid src1718 dst1718 Finset.univ := by decide +kernel

def src1719 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1719 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1719_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1719_1 : CycleData E W := ⟨3,![1,17,16,10,2],![3,6,38,26,4]⟩
def cycle1719_2 : CycleData E W := ⟨2,![3,21,20,13],![4,8,38,28]⟩
def cycle1719_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1719_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1719_5 : CycleData E W := ⟨2,![7,12,19,8],![3,14,28,18]⟩
def data1719 : PartitionData E W := ⟨6,![cycle1719_0,cycle1719_1,cycle1719_2,cycle1719_3,cycle1719_4,cycle1719_5]⟩
lemma valid_data1719 : data1719.Valid src1719 dst1719 Finset.univ := by decide +kernel

def src1720 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1720 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1720_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1720_1 : CycleData E W := ⟨3,![1,17,16,10,2],![3,6,38,26,4]⟩
def cycle1720_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1720_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1720_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1720_5 : CycleData E W := ⟨3,![7,12,20,19,8],![3,14,28,38,18]⟩
def data1720 : PartitionData E W := ⟨6,![cycle1720_0,cycle1720_1,cycle1720_2,cycle1720_3,cycle1720_4,cycle1720_5]⟩
lemma valid_data1720 : data1720.Valid src1720 dst1720 Finset.univ := by decide +kernel

def src1721 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1721 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1721_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1721_1 : CycleData E W := ⟨3,![1,17,16,10,2],![3,6,38,26,4]⟩
def cycle1721_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1721_3 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle1721_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1721_5 : CycleData E W := ⟨2,![7,12,19,8],![3,14,28,18]⟩
def data1721 : PartitionData E W := ⟨6,![cycle1721_0,cycle1721_1,cycle1721_2,cycle1721_3,cycle1721_4,cycle1721_5]⟩
lemma valid_data1721 : data1721.Valid src1721 dst1721 Finset.univ := by decide +kernel

def src1722 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1722 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1722_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1722_1 : CycleData E W := ⟨2,![1,17,10,2],![3,6,26,4]⟩
def cycle1722_2 : CycleData E W := ⟨2,![3,21,20,13],![4,8,38,28]⟩
def cycle1722_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1722_4 : CycleData E W := ⟨2,![6,15,16,11],![14,16,38,26]⟩
def cycle1722_5 : CycleData E W := ⟨2,![7,12,19,8],![3,14,28,18]⟩
def data1722 : PartitionData E W := ⟨6,![cycle1722_0,cycle1722_1,cycle1722_2,cycle1722_3,cycle1722_4,cycle1722_5]⟩
lemma valid_data1722 : data1722.Valid src1722 dst1722 Finset.univ := by decide +kernel

def src1723 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1723 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1723_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1723_1 : CycleData E W := ⟨2,![1,17,10,2],![3,6,26,4]⟩
def cycle1723_2 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1723_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1723_4 : CycleData E W := ⟨2,![6,15,16,11],![14,16,38,26]⟩
def cycle1723_5 : CycleData E W := ⟨3,![7,12,20,19,8],![3,14,28,38,18]⟩
def data1723 : PartitionData E W := ⟨6,![cycle1723_0,cycle1723_1,cycle1723_2,cycle1723_3,cycle1723_4,cycle1723_5]⟩
lemma valid_data1723 : data1723.Valid src1723 dst1723 Finset.univ := by decide +kernel

def src1724 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1724 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1724_0 : CycleData E W := ⟨1,![0,14,5],![2,6,16]⟩
def cycle1724_1 : CycleData E W := ⟨2,![1,17,10,2],![3,6,26,4]⟩
def cycle1724_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1724_3 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle1724_4 : CycleData E W := ⟨2,![6,15,16,11],![14,16,38,26]⟩
def cycle1724_5 : CycleData E W := ⟨2,![7,12,19,8],![3,14,28,18]⟩
def data1724 : PartitionData E W := ⟨6,![cycle1724_0,cycle1724_1,cycle1724_2,cycle1724_3,cycle1724_4,cycle1724_5]⟩
lemma valid_data1724 : data1724.Valid src1724 dst1724 Finset.univ := by decide +kernel

def src1725 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1725 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1725_0 : CycleData E W := ⟨2,![0,17,16,5],![2,6,38,16]⟩
def cycle1725_1 : CycleData E W := ⟨2,![1,14,10,2],![3,6,26,4]⟩
def cycle1725_2 : CycleData E W := ⟨2,![3,21,20,13],![4,8,38,28]⟩
def cycle1725_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1725_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1725_5 : CycleData E W := ⟨2,![7,12,19,8],![3,14,28,18]⟩
def data1725 : PartitionData E W := ⟨6,![cycle1725_0,cycle1725_1,cycle1725_2,cycle1725_3,cycle1725_4,cycle1725_5]⟩
lemma valid_data1725 : data1725.Valid src1725 dst1725 Finset.univ := by decide +kernel

def src1726 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1726 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1726_0 : CycleData E W := ⟨2,![0,14,15,5],![2,6,26,16]⟩
def cycle1726_1 : CycleData E W := ⟨2,![1,17,19,8],![3,6,38,18]⟩
def cycle1726_2 : CycleData E W := ⟨2,![2,10,11,7],![3,4,26,14]⟩
def cycle1726_3 : CycleData E W := ⟨1,![3,21,13],![4,8,28]⟩
def cycle1726_4 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1726_5 : CycleData E W := ⟨2,![6,16,20,12],![14,16,38,28]⟩
def data1726 : PartitionData E W := ⟨6,![cycle1726_0,cycle1726_1,cycle1726_2,cycle1726_3,cycle1726_4,cycle1726_5]⟩
lemma valid_data1726 : data1726.Valid src1726 dst1726 Finset.univ := by decide +kernel

def src1727 : E → W := ![2,6,3,4,8,2,16,14,3,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1727 : E → W := ![6,3,4,8,2,16,14,3,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1727_0 : CycleData E W := ⟨2,![0,17,16,5],![2,6,38,16]⟩
def cycle1727_1 : CycleData E W := ⟨2,![1,14,10,2],![3,6,26,4]⟩
def cycle1727_2 : CycleData E W := ⟨1,![3,18,13],![4,8,28]⟩
def cycle1727_3 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle1727_4 : CycleData E W := ⟨1,![6,15,11],![14,16,26]⟩
def cycle1727_5 : CycleData E W := ⟨2,![7,12,19,8],![3,14,28,18]⟩
def data1727 : PartitionData E W := ⟨6,![cycle1727_0,cycle1727_1,cycle1727_2,cycle1727_3,cycle1727_4,cycle1727_5]⟩
lemma valid_data1727 : data1727.Valid src1727 dst1727 Finset.univ := by decide +kernel

def src1728 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1728 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1728_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1728_1 : CycleData E W := ⟨3,![3,21,17,14,6],![3,8,38,6,16]⟩
def cycle1728_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1728_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1728_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle1728_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1728 : PartitionData E W := ⟨6,![cycle1728_0,cycle1728_1,cycle1728_2,cycle1728_3,cycle1728_4,cycle1728_5]⟩
lemma valid_data1728 : data1728.Valid src1728 dst1728 Finset.univ := by decide +kernel

def src1729 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1729 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1729_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,3]⟩
def cycle1729_1 : CycleData E W := ⟨3,![1,17,19,8,10],![4,6,38,18,14]⟩
def cycle1729_2 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1729_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1729_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1729_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1729 : PartitionData E W := ⟨6,![cycle1729_0,cycle1729_1,cycle1729_2,cycle1729_3,cycle1729_4,cycle1729_5]⟩
lemma valid_data1729 : data1729.Valid src1729 dst1729 Finset.univ := by decide +kernel

def src1730 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1730 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1730_0 : CycleData E W := ⟨2,![0,17,20,9],![2,6,38,18]⟩
def cycle1730_1 : CycleData E W := ⟨2,![2,1,14,6],![3,4,6,16]⟩
def cycle1730_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1730_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1730_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle1730_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1730 : PartitionData E W := ⟨6,![cycle1730_0,cycle1730_1,cycle1730_2,cycle1730_3,cycle1730_4,cycle1730_5]⟩
lemma valid_data1730 : data1730.Valid src1730 dst1730 Finset.univ := by decide +kernel

def src1731 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1731 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1731_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1731_1 : CycleData E W := ⟨2,![3,21,15,6],![3,8,38,16]⟩
def cycle1731_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1731_3 : CycleData E W := ⟨2,![14,7,11,17],![6,16,14,26]⟩
def cycle1731_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle1731_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1731 : PartitionData E W := ⟨6,![cycle1731_0,cycle1731_1,cycle1731_2,cycle1731_3,cycle1731_4,cycle1731_5]⟩
lemma valid_data1731 : data1731.Valid src1731 dst1731 Finset.univ := by decide +kernel

def src1732 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1732 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1732_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,3]⟩
def cycle1732_1 : CycleData E W := ⟨2,![1,17,11,10],![4,6,26,14]⟩
def cycle1732_2 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1732_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1732_4 : CycleData E W := ⟨2,![7,15,19,8],![14,16,38,18]⟩
def cycle1732_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1732 : PartitionData E W := ⟨6,![cycle1732_0,cycle1732_1,cycle1732_2,cycle1732_3,cycle1732_4,cycle1732_5]⟩
lemma valid_data1732 : data1732.Valid src1732 dst1732 Finset.univ := by decide +kernel

def src1733 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1733 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1733_0 : CycleData E W := ⟨9,![0,1,2,3,18,12,16,15,7,8,9],![2,6,4,3,8,28,26,38,16,14,18]⟩
def cycle1733_1 : CycleData E W := ⟨9,![4,21,20,19,13,10,11,17,14,6,5],![2,8,38,18,28,4,14,26,6,16,3]⟩
def data1733 : PartitionData E W := ⟨2,![cycle1733_0,cycle1733_1]⟩
lemma valid_data1733 : data1733.Valid src1733 dst1733 Finset.univ := by decide +kernel

def src1734 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1734 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1734_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1734_1 : CycleData E W := ⟨2,![3,21,16,6],![3,8,38,16]⟩
def cycle1734_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1734_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1734_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle1734_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1734 : PartitionData E W := ⟨6,![cycle1734_0,cycle1734_1,cycle1734_2,cycle1734_3,cycle1734_4,cycle1734_5]⟩
lemma valid_data1734 : data1734.Valid src1734 dst1734 Finset.univ := by decide +kernel

def src1735 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1735 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1735_0 : CycleData E W := ⟨9,![4,18,8,11,12,13,1,17,16,6,5],![2,8,18,14,26,28,4,6,38,16,3]⟩
def cycle1735_1 : CycleData E W := ⟨9,![0,14,15,7,10,2,3,21,20,19,9],![2,6,26,16,14,4,3,8,28,38,18]⟩
def data1735 : PartitionData E W := ⟨2,![cycle1735_0,cycle1735_1]⟩
lemma valid_data1735 : data1735.Valid src1735 dst1735 Finset.univ := by decide +kernel

def src1736 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1736 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1736_0 : CycleData E W := ⟨9,![4,18,13,2,6,16,17,14,11,8,9],![2,8,28,4,3,16,38,6,26,14,18]⟩
def cycle1736_1 : CycleData E W := ⟨9,![0,1,10,7,15,12,19,20,21,3,5],![2,6,4,14,16,26,28,18,38,8,3]⟩
def data1736 : PartitionData E W := ⟨2,![cycle1736_0,cycle1736_1]⟩
lemma valid_data1736 : data1736.Valid src1736 dst1736 Finset.univ := by decide +kernel

def src1737 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1737 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1737_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1737_1 : CycleData E W := ⟨3,![3,21,17,14,6],![3,8,38,6,16]⟩
def cycle1737_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1737_3 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle1737_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1737_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1737 : PartitionData E W := ⟨6,![cycle1737_0,cycle1737_1,cycle1737_2,cycle1737_3,cycle1737_4,cycle1737_5]⟩
lemma valid_data1737 : data1737.Valid src1737 dst1737 Finset.univ := by decide +kernel

def src1738 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1738 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1738_0 : CycleData E W := ⟨2,![0,17,19,9],![2,6,38,18]⟩
def cycle1738_1 : CycleData E W := ⟨2,![2,1,14,6],![3,4,6,16]⟩
def cycle1738_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1738_3 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle1738_4 : CycleData E W := ⟨2,![18,8,11,21],![8,18,14,28]⟩
def cycle1738_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1738 : PartitionData E W := ⟨6,![cycle1738_0,cycle1738_1,cycle1738_2,cycle1738_3,cycle1738_4,cycle1738_5]⟩
lemma valid_data1738 : data1738.Valid src1738 dst1738 Finset.univ := by decide +kernel

def src1739 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1739 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1739_0 : CycleData E W := ⟨2,![0,17,20,9],![2,6,38,18]⟩
def cycle1739_1 : CycleData E W := ⟨2,![2,1,14,6],![3,4,6,16]⟩
def cycle1739_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1739_3 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle1739_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1739_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1739 : PartitionData E W := ⟨6,![cycle1739_0,cycle1739_1,cycle1739_2,cycle1739_3,cycle1739_4,cycle1739_5]⟩
lemma valid_data1739 : data1739.Valid src1739 dst1739 Finset.univ := by decide +kernel

def src1740 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1740 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1740_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1740_1 : CycleData E W := ⟨2,![3,21,15,6],![3,8,38,16]⟩
def cycle1740_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1740_3 : CycleData E W := ⟨3,![10,7,14,17,13],![4,14,16,6,26]⟩
def cycle1740_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1740_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1740 : PartitionData E W := ⟨6,![cycle1740_0,cycle1740_1,cycle1740_2,cycle1740_3,cycle1740_4,cycle1740_5]⟩
lemma valid_data1740 : data1740.Valid src1740 dst1740 Finset.univ := by decide +kernel

def src1741 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1741 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1741_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,3]⟩
def cycle1741_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1741_2 : CycleData E W := ⟨3,![2,10,11,21,3],![3,4,14,28,8]⟩
def cycle1741_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1741_4 : CycleData E W := ⟨2,![7,15,19,8],![14,16,38,18]⟩
def cycle1741_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1741 : PartitionData E W := ⟨6,![cycle1741_0,cycle1741_1,cycle1741_2,cycle1741_3,cycle1741_4,cycle1741_5]⟩
lemma valid_data1741 : data1741.Valid src1741 dst1741 Finset.univ := by decide +kernel

def src1742 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1742 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1742_0 : CycleData E W := ⟨3,![0,14,15,20,9],![2,6,16,38,18]⟩
def cycle1742_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1742_2 : CycleData E W := ⟨2,![2,10,7,6],![3,4,14,16]⟩
def cycle1742_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1742_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1742_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1742 : PartitionData E W := ⟨6,![cycle1742_0,cycle1742_1,cycle1742_2,cycle1742_3,cycle1742_4,cycle1742_5]⟩
lemma valid_data1742 : data1742.Valid src1742 dst1742 Finset.univ := by decide +kernel

def src1743 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1743 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1743_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1743_1 : CycleData E W := ⟨2,![3,21,16,6],![3,8,38,16]⟩
def cycle1743_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1743_3 : CycleData E W := ⟨2,![10,7,15,13],![4,14,16,26]⟩
def cycle1743_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1743_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1743 : PartitionData E W := ⟨6,![cycle1743_0,cycle1743_1,cycle1743_2,cycle1743_3,cycle1743_4,cycle1743_5]⟩
lemma valid_data1743 : data1743.Valid src1743 dst1743 Finset.univ := by decide +kernel

def src1744 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1744 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1744_0 : CycleData E W := ⟨2,![0,17,19,9],![2,6,38,18]⟩
def cycle1744_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1744_2 : CycleData E W := ⟨2,![2,10,7,6],![3,4,14,16]⟩
def cycle1744_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1744_4 : CycleData E W := ⟨2,![18,8,11,21],![8,18,14,28]⟩
def cycle1744_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data1744 : PartitionData E W := ⟨6,![cycle1744_0,cycle1744_1,cycle1744_2,cycle1744_3,cycle1744_4,cycle1744_5]⟩
lemma valid_data1744 : data1744.Valid src1744 dst1744 Finset.univ := by decide +kernel

def src1745 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1745 : E → W := ![6,4,3,8,2,3,16,14,18,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1745_0 : CycleData E W := ⟨2,![0,17,20,9],![2,6,38,18]⟩
def cycle1745_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1745_2 : CycleData E W := ⟨2,![2,10,7,6],![3,4,14,16]⟩
def cycle1745_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1745_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1745_5 : CycleData E W := ⟨3,![18,12,15,16,21],![8,28,26,16,38]⟩
def data1745 : PartitionData E W := ⟨6,![cycle1745_0,cycle1745_1,cycle1745_2,cycle1745_3,cycle1745_4,cycle1745_5]⟩
lemma valid_data1745 : data1745.Valid src1745 dst1745 Finset.univ := by decide +kernel

def src1746 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1746 : E → W := ![6,4,3,8,2,3,16,14,18,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1746_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1746_1 : CycleData E W := ⟨3,![3,21,17,14,6],![3,8,38,6,16]⟩
def cycle1746_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1746_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1746_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle1746_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1746 : PartitionData E W := ⟨6,![cycle1746_0,cycle1746_1,cycle1746_2,cycle1746_3,cycle1746_4,cycle1746_5]⟩
lemma valid_data1746 : data1746.Valid src1746 dst1746 Finset.univ := by decide +kernel

def src1747 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1747 : E → W := ![6,4,3,8,2,3,16,14,18,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1747_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,3]⟩
def cycle1747_1 : CycleData E W := ⟨2,![1,17,16,10],![4,6,38,26]⟩
def cycle1747_2 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1747_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1747_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1747_5 : CycleData E W := ⟨2,![8,19,20,12],![14,18,38,28]⟩
def data1747 : PartitionData E W := ⟨6,![cycle1747_0,cycle1747_1,cycle1747_2,cycle1747_3,cycle1747_4,cycle1747_5]⟩
lemma valid_data1747 : data1747.Valid src1747 dst1747 Finset.univ := by decide +kernel

def src1748 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1748 : E → W := ![6,4,3,8,2,3,16,14,18,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1748_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,3]⟩
def cycle1748_1 : CycleData E W := ⟨2,![1,17,16,10],![4,6,38,26]⟩
def cycle1748_2 : CycleData E W := ⟨2,![2,13,18,3],![3,4,28,8]⟩
def cycle1748_3 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle1748_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1748_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data1748 : PartitionData E W := ⟨6,![cycle1748_0,cycle1748_1,cycle1748_2,cycle1748_3,cycle1748_4,cycle1748_5]⟩
lemma valid_data1748 : data1748.Valid src1748 dst1748 Finset.univ := by decide +kernel

def src1749 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1749 : E → W := ![6,4,3,8,2,3,16,14,18,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1749_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1749_1 : CycleData E W := ⟨2,![3,21,15,6],![3,8,38,16]⟩
def cycle1749_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1749_3 : CycleData E W := ⟨2,![14,7,11,17],![6,16,14,26]⟩
def cycle1749_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle1749_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1749 : PartitionData E W := ⟨6,![cycle1749_0,cycle1749_1,cycle1749_2,cycle1749_3,cycle1749_4,cycle1749_5]⟩
lemma valid_data1749 : data1749.Valid src1749 dst1749 Finset.univ := by decide +kernel

def src1750 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1750 : E → W := ![6,4,3,8,2,3,16,14,18,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1750_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,3]⟩
def cycle1750_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1750_2 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1750_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1750_4 : CycleData E W := ⟨2,![7,15,16,11],![14,16,38,26]⟩
def cycle1750_5 : CycleData E W := ⟨2,![8,19,20,12],![14,18,38,28]⟩
def data1750 : PartitionData E W := ⟨6,![cycle1750_0,cycle1750_1,cycle1750_2,cycle1750_3,cycle1750_4,cycle1750_5]⟩
lemma valid_data1750 : data1750.Valid src1750 dst1750 Finset.univ := by decide +kernel

def src1751 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1751 : E → W := ![6,4,3,8,2,3,16,14,18,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1751_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,3]⟩
def cycle1751_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1751_2 : CycleData E W := ⟨2,![2,13,18,3],![3,4,28,8]⟩
def cycle1751_3 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle1751_4 : CycleData E W := ⟨2,![7,15,16,11],![14,16,38,26]⟩
def cycle1751_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data1751 : PartitionData E W := ⟨6,![cycle1751_0,cycle1751_1,cycle1751_2,cycle1751_3,cycle1751_4,cycle1751_5]⟩
lemma valid_data1751 : data1751.Valid src1751 dst1751 Finset.univ := by decide +kernel

def src1752 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1752 : E → W := ![6,4,3,8,2,3,16,14,18,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1752_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1752_1 : CycleData E W := ⟨2,![3,21,16,6],![3,8,38,16]⟩
def cycle1752_2 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1752_3 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1752_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle1752_5 : CycleData E W := ⟨3,![10,14,17,20,13],![4,26,6,38,28]⟩
def data1752 : PartitionData E W := ⟨6,![cycle1752_0,cycle1752_1,cycle1752_2,cycle1752_3,cycle1752_4,cycle1752_5]⟩
lemma valid_data1752 : data1752.Valid src1752 dst1752 Finset.univ := by decide +kernel

def src1753 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1753 : E → W := ![6,4,3,8,2,3,16,14,18,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1753_0 : CycleData E W := ⟨3,![0,17,16,6,5],![2,6,38,16,3]⟩
def cycle1753_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1753_2 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1753_3 : CycleData E W := ⟨1,![4,18,9],![2,8,18]⟩
def cycle1753_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1753_5 : CycleData E W := ⟨2,![8,19,20,12],![14,18,38,28]⟩
def data1753 : PartitionData E W := ⟨6,![cycle1753_0,cycle1753_1,cycle1753_2,cycle1753_3,cycle1753_4,cycle1753_5]⟩
lemma valid_data1753 : data1753.Valid src1753 dst1753 Finset.univ := by decide +kernel

def src1754 : E → W := ![2,6,4,3,8,2,3,16,14,18,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1754 : E → W := ![6,4,3,8,2,3,16,14,18,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1754_0 : CycleData E W := ⟨3,![0,17,16,6,5],![2,6,38,16,3]⟩
def cycle1754_1 : CycleData E W := ⟨1,![1,14,10],![4,6,26]⟩
def cycle1754_2 : CycleData E W := ⟨2,![2,13,18,3],![3,4,28,8]⟩
def cycle1754_3 : CycleData E W := ⟨2,![4,21,20,9],![2,8,38,18]⟩
def cycle1754_4 : CycleData E W := ⟨1,![7,15,11],![14,16,26]⟩
def cycle1754_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data1754 : PartitionData E W := ⟨6,![cycle1754_0,cycle1754_1,cycle1754_2,cycle1754_3,cycle1754_4,cycle1754_5]⟩
lemma valid_data1754 : data1754.Valid src1754 dst1754 Finset.univ := by decide +kernel

def src1755 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1755 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1755_0 : CycleData E W := ⟨9,![4,18,8,10,13,12,16,17,14,6,5],![2,8,18,14,4,28,26,38,6,16,3]⟩
def cycle1755_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,7,15,11,9],![2,6,4,3,8,38,28,18,16,26,14]⟩
def data1755 : PartitionData E W := ⟨2,![cycle1755_0,cycle1755_1]⟩
lemma valid_data1755 : data1755.Valid src1755 dst1755 Finset.univ := by decide +kernel

def src1756 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1756 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1756_0 : CycleData E W := ⟨9,![4,18,8,10,13,12,16,17,14,6,5],![2,8,18,14,4,28,26,38,6,16,3]⟩
def cycle1756_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,7,15,11,9],![2,6,4,3,8,28,38,18,16,26,14]⟩
def data1756 : PartitionData E W := ⟨2,![cycle1756_0,cycle1756_1]⟩
lemma valid_data1756 : data1756.Valid src1756 dst1756 Finset.univ := by decide +kernel

def src1757 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1757 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1757_0 : CycleData E W := ⟨9,![4,18,12,16,17,1,2,6,7,8,9],![2,8,28,26,38,6,4,3,16,18,14]⟩
def cycle1757_1 : CycleData E W := ⟨9,![0,14,15,11,10,13,19,20,21,3,5],![2,6,16,26,14,4,28,18,38,8,3]⟩
def data1757 : PartitionData E W := ⟨2,![cycle1757_0,cycle1757_1]⟩
lemma valid_data1757 : data1757.Valid src1757 dst1757 Finset.univ := by decide +kernel

def src1758 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1758 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1758_0 : CycleData E W := ⟨2,![0,17,11,9],![2,6,26,14]⟩
def cycle1758_1 : CycleData E W := ⟨2,![2,1,14,6],![3,4,6,16]⟩
def cycle1758_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1758_3 : CycleData E W := ⟨2,![18,7,15,21],![8,18,16,38]⟩
def cycle1758_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle1758_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1758 : PartitionData E W := ⟨6,![cycle1758_0,cycle1758_1,cycle1758_2,cycle1758_3,cycle1758_4,cycle1758_5]⟩
lemma valid_data1758 : data1758.Valid src1758 dst1758 Finset.univ := by decide +kernel

def src1759 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1759 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1759_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,3]⟩
def cycle1759_1 : CycleData E W := ⟨2,![1,17,11,10],![4,6,26,14]⟩
def cycle1759_2 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1759_3 : CycleData E W := ⟨2,![4,18,8,9],![2,8,18,14]⟩
def cycle1759_4 : CycleData E W := ⟨1,![7,19,15],![16,18,38]⟩
def cycle1759_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1759 : PartitionData E W := ⟨6,![cycle1759_0,cycle1759_1,cycle1759_2,cycle1759_3,cycle1759_4,cycle1759_5]⟩
lemma valid_data1759 : data1759.Valid src1759 dst1759 Finset.univ := by decide +kernel

def src1760 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1760 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1760_0 : CycleData E W := ⟨2,![0,17,11,9],![2,6,26,14]⟩
def cycle1760_1 : CycleData E W := ⟨2,![2,1,14,6],![3,4,6,16]⟩
def cycle1760_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1760_3 : CycleData E W := ⟨1,![7,20,15],![16,18,38]⟩
def cycle1760_4 : CycleData E W := ⟨2,![10,8,19,13],![4,14,18,28]⟩
def cycle1760_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1760 : PartitionData E W := ⟨6,![cycle1760_0,cycle1760_1,cycle1760_2,cycle1760_3,cycle1760_4,cycle1760_5]⟩
lemma valid_data1760 : data1760.Valid src1760 dst1760 Finset.univ := by decide +kernel

def src1761 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1761 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1761_0 : CycleData E W := ⟨9,![0,17,16,6,2,13,12,11,8,18,4],![2,6,38,16,3,4,28,26,14,18,8]⟩
def cycle1761_1 : CycleData E W := ⟨9,![5,3,21,20,19,7,15,14,1,10,9],![2,3,8,38,28,18,16,26,6,4,14]⟩
def data1761 : PartitionData E W := ⟨2,![cycle1761_0,cycle1761_1]⟩
lemma valid_data1761 : data1761.Valid src1761 dst1761 Finset.univ := by decide +kernel

def src1762 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1762 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1762_0 : CycleData E W := ⟨9,![0,17,16,6,2,13,12,11,8,18,4],![2,6,38,16,3,4,28,26,14,18,8]⟩
def cycle1762_1 : CycleData E W := ⟨9,![5,3,21,20,19,7,15,14,1,10,9],![2,3,8,28,38,18,16,26,6,4,14]⟩
def data1762 : PartitionData E W := ⟨2,![cycle1762_0,cycle1762_1]⟩
lemma valid_data1762 : data1762.Valid src1762 dst1762 Finset.univ := by decide +kernel

def src1763 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1763 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1763_0 : CycleData E W := ⟨9,![4,18,12,11,8,7,16,17,1,2,5],![2,8,28,26,14,18,16,38,6,4,3]⟩
def cycle1763_1 : CycleData E W := ⟨9,![0,14,15,6,3,21,20,19,13,10,9],![2,6,26,16,3,8,38,18,28,4,14]⟩
def data1763 : PartitionData E W := ⟨2,![cycle1763_0,cycle1763_1]⟩
lemma valid_data1763 : data1763.Valid src1763 dst1763 Finset.univ := by decide +kernel

def src1764 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1764 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1764_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1764_1 : CycleData E W := ⟨2,![2,13,15,6],![3,4,26,16]⟩
def cycle1764_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1764_3 : CycleData E W := ⟨3,![14,7,18,21,17],![6,16,18,8,38]⟩
def cycle1764_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1764_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1764 : PartitionData E W := ⟨6,![cycle1764_0,cycle1764_1,cycle1764_2,cycle1764_3,cycle1764_4,cycle1764_5]⟩
lemma valid_data1764 : data1764.Valid src1764 dst1764 Finset.univ := by decide +kernel

def src1765 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1765 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1765_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1765_1 : CycleData E W := ⟨2,![2,13,15,6],![3,4,26,16]⟩
def cycle1765_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1765_3 : CycleData E W := ⟨2,![14,7,19,17],![6,16,18,38]⟩
def cycle1765_4 : CycleData E W := ⟨2,![18,8,11,21],![8,18,14,28]⟩
def cycle1765_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1765 : PartitionData E W := ⟨6,![cycle1765_0,cycle1765_1,cycle1765_2,cycle1765_3,cycle1765_4,cycle1765_5]⟩
lemma valid_data1765 : data1765.Valid src1765 dst1765 Finset.univ := by decide +kernel

def src1766 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1766 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1766_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1766_1 : CycleData E W := ⟨2,![2,13,15,6],![3,4,26,16]⟩
def cycle1766_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1766_3 : CycleData E W := ⟨2,![14,7,20,17],![6,16,18,38]⟩
def cycle1766_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1766_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1766 : PartitionData E W := ⟨6,![cycle1766_0,cycle1766_1,cycle1766_2,cycle1766_3,cycle1766_4,cycle1766_5]⟩
lemma valid_data1766 : data1766.Valid src1766 dst1766 Finset.univ := by decide +kernel

def src1767 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1767 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1767_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1767_1 : CycleData E W := ⟨3,![2,13,17,14,6],![3,4,26,6,16]⟩
def cycle1767_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1767_3 : CycleData E W := ⟨2,![18,7,15,21],![8,18,16,38]⟩
def cycle1767_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1767_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1767 : PartitionData E W := ⟨6,![cycle1767_0,cycle1767_1,cycle1767_2,cycle1767_3,cycle1767_4,cycle1767_5]⟩
lemma valid_data1767 : data1767.Valid src1767 dst1767 Finset.univ := by decide +kernel

def src1768 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1768 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1768_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1768_1 : CycleData E W := ⟨3,![2,13,17,14,6],![3,4,26,6,16]⟩
def cycle1768_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1768_3 : CycleData E W := ⟨1,![7,19,15],![16,18,38]⟩
def cycle1768_4 : CycleData E W := ⟨2,![18,8,11,21],![8,18,14,28]⟩
def cycle1768_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1768 : PartitionData E W := ⟨6,![cycle1768_0,cycle1768_1,cycle1768_2,cycle1768_3,cycle1768_4,cycle1768_5]⟩
lemma valid_data1768 : data1768.Valid src1768 dst1768 Finset.univ := by decide +kernel

def src1769 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1769 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1769_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1769_1 : CycleData E W := ⟨3,![2,13,17,14,6],![3,4,26,6,16]⟩
def cycle1769_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1769_3 : CycleData E W := ⟨1,![7,20,15],![16,18,38]⟩
def cycle1769_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1769_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1769 : PartitionData E W := ⟨6,![cycle1769_0,cycle1769_1,cycle1769_2,cycle1769_3,cycle1769_4,cycle1769_5]⟩
lemma valid_data1769 : data1769.Valid src1769 dst1769 Finset.univ := by decide +kernel

def src1770 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1770 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1770_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1770_1 : CycleData E W := ⟨2,![2,13,15,6],![3,4,26,16]⟩
def cycle1770_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1770_3 : CycleData E W := ⟨2,![18,7,16,21],![8,18,16,38]⟩
def cycle1770_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1770_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1770 : PartitionData E W := ⟨6,![cycle1770_0,cycle1770_1,cycle1770_2,cycle1770_3,cycle1770_4,cycle1770_5]⟩
lemma valid_data1770 : data1770.Valid src1770 dst1770 Finset.univ := by decide +kernel

def src1771 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1771 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1771_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1771_1 : CycleData E W := ⟨2,![2,13,15,6],![3,4,26,16]⟩
def cycle1771_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1771_3 : CycleData E W := ⟨1,![7,19,16],![16,18,38]⟩
def cycle1771_4 : CycleData E W := ⟨2,![18,8,11,21],![8,18,14,28]⟩
def cycle1771_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1771 : PartitionData E W := ⟨6,![cycle1771_0,cycle1771_1,cycle1771_2,cycle1771_3,cycle1771_4,cycle1771_5]⟩
lemma valid_data1771 : data1771.Valid src1771 dst1771 Finset.univ := by decide +kernel

def src1772 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1772 : E → W := ![6,4,3,8,2,3,16,18,14,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1772_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1772_1 : CycleData E W := ⟨2,![2,13,15,6],![3,4,26,16]⟩
def cycle1772_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1772_3 : CycleData E W := ⟨1,![7,20,16],![16,18,38]⟩
def cycle1772_4 : CycleData E W := ⟨1,![8,19,11],![14,18,28]⟩
def cycle1772_5 : CycleData E W := ⟨3,![14,12,18,21,17],![6,26,28,8,38]⟩
def data1772 : PartitionData E W := ⟨6,![cycle1772_0,cycle1772_1,cycle1772_2,cycle1772_3,cycle1772_4,cycle1772_5]⟩
lemma valid_data1772 : data1772.Valid src1772 dst1772 Finset.univ := by decide +kernel

def src1773 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,26,14,28,6,16,26,38,8,18,28,38]
def dst1773 : E → W := ![6,4,3,8,2,3,16,18,14,2,26,14,28,4,16,26,38,6,18,28,38,8]
def cycle1773_0 : CycleData E W := ⟨9,![4,18,8,12,13,10,16,17,14,6,5],![2,8,18,14,28,4,26,38,6,16,3]⟩
def cycle1773_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,7,15,11,9],![2,6,4,3,8,38,28,18,16,26,14]⟩
def data1773 : PartitionData E W := ⟨2,![cycle1773_0,cycle1773_1]⟩
lemma valid_data1773 : data1773.Valid src1773 dst1773 Finset.univ := by decide +kernel

def src1774 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,26,14,28,6,16,26,38,8,18,38,28]
def dst1774 : E → W := ![6,4,3,8,2,3,16,18,14,2,26,14,28,4,16,26,38,6,18,38,28,8]
def cycle1774_0 : CycleData E W := ⟨9,![4,18,8,12,13,10,16,17,14,6,5],![2,8,18,14,28,4,26,38,6,16,3]⟩
def cycle1774_1 : CycleData E W := ⟨9,![0,1,2,3,21,20,19,7,15,11,9],![2,6,4,3,8,28,38,18,16,26,14]⟩
def data1774 : PartitionData E W := ⟨2,![cycle1774_0,cycle1774_1]⟩
lemma valid_data1774 : data1774.Valid src1774 dst1774 Finset.univ := by decide +kernel

def src1775 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,26,14,28,6,16,26,38,8,28,18,38]
def dst1775 : E → W := ![6,4,3,8,2,3,16,18,14,2,26,14,28,4,16,26,38,6,28,18,38,8]
def cycle1775_0 : CycleData E W := ⟨9,![0,17,16,10,2,6,7,8,12,18,4],![2,6,38,26,4,3,16,18,14,28,8]⟩
def cycle1775_1 : CycleData E W := ⟨9,![5,3,21,20,19,13,1,14,15,11,9],![2,3,8,38,18,28,4,6,16,26,14]⟩
def data1775 : PartitionData E W := ⟨2,![cycle1775_0,cycle1775_1]⟩
lemma valid_data1775 : data1775.Valid src1775 dst1775 Finset.univ := by decide +kernel

def src1776 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,26,14,28,6,16,38,26,8,18,28,38]
def dst1776 : E → W := ![6,4,3,8,2,3,16,18,14,2,26,14,28,4,16,38,26,6,18,28,38,8]
def cycle1776_0 : CycleData E W := ⟨2,![0,17,11,9],![2,6,26,14]⟩
def cycle1776_1 : CycleData E W := ⟨2,![2,1,14,6],![3,4,6,16]⟩
def cycle1776_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1776_3 : CycleData E W := ⟨2,![18,7,15,21],![8,18,16,38]⟩
def cycle1776_4 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def cycle1776_5 : CycleData E W := ⟨2,![10,16,20,13],![4,26,38,28]⟩
def data1776 : PartitionData E W := ⟨6,![cycle1776_0,cycle1776_1,cycle1776_2,cycle1776_3,cycle1776_4,cycle1776_5]⟩
lemma valid_data1776 : data1776.Valid src1776 dst1776 Finset.univ := by decide +kernel

def src1777 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,26,14,28,6,16,38,26,8,18,38,28]
def dst1777 : E → W := ![6,4,3,8,2,3,16,18,14,2,26,14,28,4,16,38,26,6,18,38,28,8]
def cycle1777_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,3]⟩
def cycle1777_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1777_2 : CycleData E W := ⟨2,![2,13,21,3],![3,4,28,8]⟩
def cycle1777_3 : CycleData E W := ⟨2,![4,18,8,9],![2,8,18,14]⟩
def cycle1777_4 : CycleData E W := ⟨1,![7,19,15],![16,18,38]⟩
def cycle1777_5 : CycleData E W := ⟨2,![11,16,20,12],![14,26,38,28]⟩
def data1777 : PartitionData E W := ⟨6,![cycle1777_0,cycle1777_1,cycle1777_2,cycle1777_3,cycle1777_4,cycle1777_5]⟩
lemma valid_data1777 : data1777.Valid src1777 dst1777 Finset.univ := by decide +kernel

def src1778 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,26,14,28,6,16,38,26,8,28,18,38]
def dst1778 : E → W := ![6,4,3,8,2,3,16,18,14,2,26,14,28,4,16,38,26,6,28,18,38,8]
def cycle1778_0 : CycleData E W := ⟨2,![0,14,6,5],![2,6,16,3]⟩
def cycle1778_1 : CycleData E W := ⟨1,![1,17,10],![4,6,26]⟩
def cycle1778_2 : CycleData E W := ⟨2,![2,13,18,3],![3,4,28,8]⟩
def cycle1778_3 : CycleData E W := ⟨3,![4,21,16,11,9],![2,8,38,26,14]⟩
def cycle1778_4 : CycleData E W := ⟨1,![7,20,15],![16,18,38]⟩
def cycle1778_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data1778 : PartitionData E W := ⟨6,![cycle1778_0,cycle1778_1,cycle1778_2,cycle1778_3,cycle1778_4,cycle1778_5]⟩
lemma valid_data1778 : data1778.Valid src1778 dst1778 Finset.univ := by decide +kernel

def src1779 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,26,14,28,6,26,16,38,8,18,28,38]
def dst1779 : E → W := ![6,4,3,8,2,3,16,18,14,2,26,14,28,4,26,16,38,6,18,28,38,8]
def cycle1779_0 : CycleData E W := ⟨2,![0,14,11,9],![2,6,26,14]⟩
def cycle1779_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1779_2 : CycleData E W := ⟨2,![2,10,15,6],![3,4,26,16]⟩
def cycle1779_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1779_4 : CycleData E W := ⟨2,![18,7,16,21],![8,18,16,38]⟩
def cycle1779_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data1779 : PartitionData E W := ⟨6,![cycle1779_0,cycle1779_1,cycle1779_2,cycle1779_3,cycle1779_4,cycle1779_5]⟩
lemma valid_data1779 : data1779.Valid src1779 dst1779 Finset.univ := by decide +kernel

def src1780 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,26,14,28,6,26,16,38,8,18,38,28]
def dst1780 : E → W := ![6,4,3,8,2,3,16,18,14,2,26,14,28,4,26,16,38,6,18,38,28,8]
def cycle1780_0 : CycleData E W := ⟨2,![0,14,11,9],![2,6,26,14]⟩
def cycle1780_1 : CycleData E W := ⟨2,![1,17,20,13],![4,6,38,28]⟩
def cycle1780_2 : CycleData E W := ⟨2,![2,10,15,6],![3,4,26,16]⟩
def cycle1780_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1780_4 : CycleData E W := ⟨1,![7,19,16],![16,18,38]⟩
def cycle1780_5 : CycleData E W := ⟨2,![18,8,12,21],![8,18,14,28]⟩
def data1780 : PartitionData E W := ⟨6,![cycle1780_0,cycle1780_1,cycle1780_2,cycle1780_3,cycle1780_4,cycle1780_5]⟩
lemma valid_data1780 : data1780.Valid src1780 dst1780 Finset.univ := by decide +kernel

def src1781 : E → W := ![2,6,4,3,8,2,3,16,18,14,4,26,14,28,6,26,16,38,8,28,18,38]
def dst1781 : E → W := ![6,4,3,8,2,3,16,18,14,2,26,14,28,4,26,16,38,6,28,18,38,8]
def cycle1781_0 : CycleData E W := ⟨2,![0,14,11,9],![2,6,26,14]⟩
def cycle1781_1 : CycleData E W := ⟨3,![1,17,21,18,13],![4,6,38,8,28]⟩
def cycle1781_2 : CycleData E W := ⟨2,![2,10,15,6],![3,4,26,16]⟩
def cycle1781_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1781_4 : CycleData E W := ⟨1,![7,20,16],![16,18,38]⟩
def cycle1781_5 : CycleData E W := ⟨1,![8,19,12],![14,18,28]⟩
def data1781 : PartitionData E W := ⟨6,![cycle1781_0,cycle1781_1,cycle1781_2,cycle1781_3,cycle1781_4,cycle1781_5]⟩
lemma valid_data1781 : data1781.Valid src1781 dst1781 Finset.univ := by decide +kernel

def src1782 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,26,28,6,16,26,38,8,18,28,38]
def dst1782 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,26,28,4,16,26,38,6,18,28,38,8]
def cycle1782_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1782_1 : CycleData E W := ⟨2,![2,13,19,6],![3,4,28,18]⟩
def cycle1782_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1782_3 : CycleData E W := ⟨3,![14,7,18,21,17],![6,16,18,8,38]⟩
def cycle1782_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1782_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1782 : PartitionData E W := ⟨6,![cycle1782_0,cycle1782_1,cycle1782_2,cycle1782_3,cycle1782_4,cycle1782_5]⟩
lemma valid_data1782 : data1782.Valid src1782 dst1782 Finset.univ := by decide +kernel

def src1783 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,26,28,6,16,26,38,8,18,38,28]
def dst1783 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,26,28,4,16,26,38,6,18,38,28,8]
def cycle1783_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1783_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1783_2 : CycleData E W := ⟨3,![4,21,13,10,9],![2,8,28,4,14]⟩
def cycle1783_3 : CycleData E W := ⟨2,![14,7,19,17],![6,16,18,38]⟩
def cycle1783_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1783_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1783 : PartitionData E W := ⟨6,![cycle1783_0,cycle1783_1,cycle1783_2,cycle1783_3,cycle1783_4,cycle1783_5]⟩
lemma valid_data1783 : data1783.Valid src1783 dst1783 Finset.univ := by decide +kernel

def src1784 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,26,28,6,16,26,38,8,28,18,38]
def dst1784 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,26,28,4,16,26,38,6,28,18,38,8]
def cycle1784_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1784_1 : CycleData E W := ⟨2,![2,13,19,6],![3,4,28,18]⟩
def cycle1784_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1784_3 : CycleData E W := ⟨2,![14,7,20,17],![6,16,18,38]⟩
def cycle1784_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1784_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1784 : PartitionData E W := ⟨6,![cycle1784_0,cycle1784_1,cycle1784_2,cycle1784_3,cycle1784_4,cycle1784_5]⟩
lemma valid_data1784 : data1784.Valid src1784 dst1784 Finset.univ := by decide +kernel

def src1785 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,26,28,6,16,38,26,8,18,28,38]
def dst1785 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,26,28,4,16,38,26,6,18,28,38,8]
def cycle1785_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1785_1 : CycleData E W := ⟨2,![2,13,19,6],![3,4,28,18]⟩
def cycle1785_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1785_3 : CycleData E W := ⟨2,![18,7,15,21],![8,18,16,38]⟩
def cycle1785_4 : CycleData E W := ⟨2,![14,8,11,17],![6,16,14,26]⟩
def cycle1785_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1785 : PartitionData E W := ⟨6,![cycle1785_0,cycle1785_1,cycle1785_2,cycle1785_3,cycle1785_4,cycle1785_5]⟩
lemma valid_data1785 : data1785.Valid src1785 dst1785 Finset.univ := by decide +kernel

def src1786 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,26,28,6,16,38,26,8,18,38,28]
def dst1786 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,26,28,4,16,38,26,6,18,38,28,8]
def cycle1786_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1786_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1786_2 : CycleData E W := ⟨3,![4,21,13,10,9],![2,8,28,4,14]⟩
def cycle1786_3 : CycleData E W := ⟨1,![7,19,15],![16,18,38]⟩
def cycle1786_4 : CycleData E W := ⟨2,![14,8,11,17],![6,16,14,26]⟩
def cycle1786_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1786 : PartitionData E W := ⟨6,![cycle1786_0,cycle1786_1,cycle1786_2,cycle1786_3,cycle1786_4,cycle1786_5]⟩
lemma valid_data1786 : data1786.Valid src1786 dst1786 Finset.univ := by decide +kernel

def src1787 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,26,28,6,16,38,26,8,28,18,38]
def dst1787 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,26,28,4,16,38,26,6,28,18,38,8]
def cycle1787_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1787_1 : CycleData E W := ⟨2,![2,13,19,6],![3,4,28,18]⟩
def cycle1787_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1787_3 : CycleData E W := ⟨1,![7,20,15],![16,18,38]⟩
def cycle1787_4 : CycleData E W := ⟨2,![14,8,11,17],![6,16,14,26]⟩
def cycle1787_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1787 : PartitionData E W := ⟨6,![cycle1787_0,cycle1787_1,cycle1787_2,cycle1787_3,cycle1787_4,cycle1787_5]⟩
lemma valid_data1787 : data1787.Valid src1787 dst1787 Finset.univ := by decide +kernel

def src1788 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,26,28,6,26,16,38,8,18,28,38]
def dst1788 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,26,28,4,26,16,38,6,18,28,38,8]
def cycle1788_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1788_1 : CycleData E W := ⟨2,![2,13,19,6],![3,4,28,18]⟩
def cycle1788_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1788_3 : CycleData E W := ⟨2,![18,7,16,21],![8,18,16,38]⟩
def cycle1788_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1788_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1788 : PartitionData E W := ⟨6,![cycle1788_0,cycle1788_1,cycle1788_2,cycle1788_3,cycle1788_4,cycle1788_5]⟩
lemma valid_data1788 : data1788.Valid src1788 dst1788 Finset.univ := by decide +kernel

def src1789 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,26,28,6,26,16,38,8,18,38,28]
def dst1789 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,26,28,4,26,16,38,6,18,38,28,8]
def cycle1789_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1789_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1789_2 : CycleData E W := ⟨3,![4,21,13,10,9],![2,8,28,4,14]⟩
def cycle1789_3 : CycleData E W := ⟨1,![7,19,16],![16,18,38]⟩
def cycle1789_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1789_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1789 : PartitionData E W := ⟨6,![cycle1789_0,cycle1789_1,cycle1789_2,cycle1789_3,cycle1789_4,cycle1789_5]⟩
lemma valid_data1789 : data1789.Valid src1789 dst1789 Finset.univ := by decide +kernel

def src1790 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,26,28,6,26,16,38,8,28,18,38]
def dst1790 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,26,28,4,26,16,38,6,28,18,38,8]
def cycle1790_0 : CycleData E W := ⟨2,![0,1,10,9],![2,6,4,14]⟩
def cycle1790_1 : CycleData E W := ⟨2,![2,13,19,6],![3,4,28,18]⟩
def cycle1790_2 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1790_3 : CycleData E W := ⟨1,![7,20,16],![16,18,38]⟩
def cycle1790_4 : CycleData E W := ⟨1,![8,15,11],![14,16,26]⟩
def cycle1790_5 : CycleData E W := ⟨3,![14,12,18,21,17],![6,26,28,8,38]⟩
def data1790 : PartitionData E W := ⟨6,![cycle1790_0,cycle1790_1,cycle1790_2,cycle1790_3,cycle1790_4,cycle1790_5]⟩
lemma valid_data1790 : data1790.Valid src1790 dst1790 Finset.univ := by decide +kernel

def src1791 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,28,26,6,16,26,38,8,18,28,38]
def dst1791 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,28,26,4,16,26,38,6,18,28,38,8]
def cycle1791_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1791_1 : CycleData E W := ⟨2,![1,14,15,13],![4,6,16,26]⟩
def cycle1791_2 : CycleData E W := ⟨2,![5,2,10,9],![2,3,4,14]⟩
def cycle1791_3 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1791_4 : CycleData E W := ⟨2,![8,7,19,11],![14,16,18,28]⟩
def cycle1791_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1791 : PartitionData E W := ⟨6,![cycle1791_0,cycle1791_1,cycle1791_2,cycle1791_3,cycle1791_4,cycle1791_5]⟩
lemma valid_data1791 : data1791.Valid src1791 dst1791 Finset.univ := by decide +kernel

def src1792 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,28,26,6,16,26,38,8,18,38,28]
def dst1792 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,28,26,4,16,26,38,6,18,38,28,8]
def cycle1792_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1792_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1792_2 : CycleData E W := ⟨2,![4,21,11,9],![2,8,28,14]⟩
def cycle1792_3 : CycleData E W := ⟨2,![14,7,19,17],![6,16,18,38]⟩
def cycle1792_4 : CycleData E W := ⟨2,![10,8,15,13],![4,14,16,26]⟩
def cycle1792_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1792 : PartitionData E W := ⟨6,![cycle1792_0,cycle1792_1,cycle1792_2,cycle1792_3,cycle1792_4,cycle1792_5]⟩
lemma valid_data1792 : data1792.Valid src1792 dst1792 Finset.univ := by decide +kernel

def src1793 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,28,26,6,16,26,38,8,28,18,38]
def dst1793 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,28,26,4,16,26,38,6,28,18,38,8]
def cycle1793_0 : CycleData E W := ⟨9,![4,18,12,16,17,1,2,6,7,8,9],![2,8,28,26,38,6,4,3,18,16,14]⟩
def cycle1793_1 : CycleData E W := ⟨9,![0,14,15,13,10,11,19,20,21,3,5],![2,6,16,26,4,14,28,18,38,8,3]⟩
def data1793 : PartitionData E W := ⟨2,![cycle1793_0,cycle1793_1]⟩
lemma valid_data1793 : data1793.Valid src1793 dst1793 Finset.univ := by decide +kernel

def src1794 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,28,26,6,16,38,26,8,18,28,38]
def dst1794 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,28,26,4,16,38,26,6,18,28,38,8]
def cycle1794_0 : CycleData E W := ⟨2,![0,14,8,9],![2,6,16,14]⟩
def cycle1794_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1794_2 : CycleData E W := ⟨3,![2,10,11,19,6],![3,4,14,28,18]⟩
def cycle1794_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1794_4 : CycleData E W := ⟨2,![18,7,15,21],![8,18,16,38]⟩
def cycle1794_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1794 : PartitionData E W := ⟨6,![cycle1794_0,cycle1794_1,cycle1794_2,cycle1794_3,cycle1794_4,cycle1794_5]⟩
lemma valid_data1794 : data1794.Valid src1794 dst1794 Finset.univ := by decide +kernel

def src1795 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,28,26,6,16,38,26,8,18,38,28]
def dst1795 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,28,26,4,16,38,26,6,18,38,28,8]
def cycle1795_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1795_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1795_2 : CycleData E W := ⟨2,![4,21,11,9],![2,8,28,14]⟩
def cycle1795_3 : CycleData E W := ⟨1,![7,19,15],![16,18,38]⟩
def cycle1795_4 : CycleData E W := ⟨3,![10,8,14,17,13],![4,14,16,6,26]⟩
def cycle1795_5 : CycleData E W := ⟨1,![12,20,16],![26,28,38]⟩
def data1795 : PartitionData E W := ⟨6,![cycle1795_0,cycle1795_1,cycle1795_2,cycle1795_3,cycle1795_4,cycle1795_5]⟩
lemma valid_data1795 : data1795.Valid src1795 dst1795 Finset.univ := by decide +kernel

def src1796 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,28,26,6,16,38,26,8,28,18,38]
def dst1796 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,28,26,4,16,38,26,6,28,18,38,8]
def cycle1796_0 : CycleData E W := ⟨2,![0,14,8,9],![2,6,16,14]⟩
def cycle1796_1 : CycleData E W := ⟨1,![1,17,13],![4,6,26]⟩
def cycle1796_2 : CycleData E W := ⟨3,![2,10,11,19,6],![3,4,14,28,18]⟩
def cycle1796_3 : CycleData E W := ⟨1,![4,3,5],![2,8,3]⟩
def cycle1796_4 : CycleData E W := ⟨1,![7,20,15],![16,18,38]⟩
def cycle1796_5 : CycleData E W := ⟨2,![18,12,16,21],![8,28,26,38]⟩
def data1796 : PartitionData E W := ⟨6,![cycle1796_0,cycle1796_1,cycle1796_2,cycle1796_3,cycle1796_4,cycle1796_5]⟩
lemma valid_data1796 : data1796.Valid src1796 dst1796 Finset.univ := by decide +kernel

def src1797 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,28,26,6,26,16,38,8,18,28,38]
def dst1797 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,28,26,4,26,16,38,6,18,28,38,8]
def cycle1797_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1797_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1797_2 : CycleData E W := ⟨2,![5,2,10,9],![2,3,4,14]⟩
def cycle1797_3 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1797_4 : CycleData E W := ⟨2,![8,7,19,11],![14,16,18,28]⟩
def cycle1797_5 : CycleData E W := ⟨2,![15,12,20,16],![16,26,28,38]⟩
def data1797 : PartitionData E W := ⟨6,![cycle1797_0,cycle1797_1,cycle1797_2,cycle1797_3,cycle1797_4,cycle1797_5]⟩
lemma valid_data1797 : data1797.Valid src1797 dst1797 Finset.univ := by decide +kernel

def src1798 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,28,26,6,26,16,38,8,18,38,28]
def dst1798 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,28,26,4,26,16,38,6,18,38,28,8]
def cycle1798_0 : CycleData E W := ⟨2,![0,1,2,5],![2,6,4,3]⟩
def cycle1798_1 : CycleData E W := ⟨1,![3,18,6],![3,8,18]⟩
def cycle1798_2 : CycleData E W := ⟨2,![4,21,11,9],![2,8,28,14]⟩
def cycle1798_3 : CycleData E W := ⟨1,![7,19,16],![16,18,38]⟩
def cycle1798_4 : CycleData E W := ⟨2,![10,8,15,13],![4,14,16,26]⟩
def cycle1798_5 : CycleData E W := ⟨2,![14,12,20,17],![6,26,28,38]⟩
def data1798 : PartitionData E W := ⟨6,![cycle1798_0,cycle1798_1,cycle1798_2,cycle1798_3,cycle1798_4,cycle1798_5]⟩
lemma valid_data1798 : data1798.Valid src1798 dst1798 Finset.univ := by decide +kernel

def src1799 : E → W := ![2,6,4,3,8,2,3,18,16,14,4,14,28,26,6,26,16,38,8,28,18,38]
def dst1799 : E → W := ![6,4,3,8,2,3,18,16,14,2,14,28,26,4,26,16,38,6,28,18,38,8]
def cycle1799_0 : CycleData E W := ⟨2,![0,17,21,4],![2,6,38,8]⟩
def cycle1799_1 : CycleData E W := ⟨1,![1,14,13],![4,6,26]⟩
def cycle1799_2 : CycleData E W := ⟨2,![5,2,10,9],![2,3,4,14]⟩
def cycle1799_3 : CycleData E W := ⟨2,![3,18,19,6],![3,8,28,18]⟩
def cycle1799_4 : CycleData E W := ⟨1,![7,20,16],![16,18,38]⟩
def cycle1799_5 : CycleData E W := ⟨2,![8,15,12,11],![14,16,26,28]⟩
def data1799 : PartitionData E W := ⟨6,![cycle1799_0,cycle1799_1,cycle1799_2,cycle1799_3,cycle1799_4,cycle1799_5]⟩
lemma valid_data1799 : data1799.Valid src1799 dst1799 Finset.univ := by decide +kernel

def lookupB8 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data1600 else (if j < 2 then data1601 else data1602)) else (if j < 4 then data1603 else (if j < 5 then data1604 else data1605))) else (if j < 9 then (if j < 7 then data1606 else (if j < 8 then data1607 else data1608)) else (if j < 10 then data1609 else (if j < 11 then data1610 else data1611)))) else (if j < 18 then (if j < 15 then (if j < 13 then data1612 else (if j < 14 then data1613 else data1614)) else (if j < 16 then data1615 else (if j < 17 then data1616 else data1617))) else (if j < 21 then (if j < 19 then data1618 else (if j < 20 then data1619 else data1620)) else (if j < 23 then (if j < 22 then data1621 else data1622) else (if j < 24 then data1623 else data1624))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data1625 else (if j < 27 then data1626 else data1627)) else (if j < 29 then data1628 else (if j < 30 then data1629 else data1630))) else (if j < 34 then (if j < 32 then data1631 else (if j < 33 then data1632 else data1633)) else (if j < 35 then data1634 else (if j < 36 then data1635 else data1636)))) else (if j < 43 then (if j < 40 then (if j < 38 then data1637 else (if j < 39 then data1638 else data1639)) else (if j < 41 then data1640 else (if j < 42 then data1641 else data1642))) else (if j < 46 then (if j < 44 then data1643 else (if j < 45 then data1644 else data1645)) else (if j < 48 then (if j < 47 then data1646 else data1647) else (if j < 49 then data1648 else data1649)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data1650 else (if j < 52 then data1651 else data1652)) else (if j < 54 then data1653 else (if j < 55 then data1654 else data1655))) else (if j < 59 then (if j < 57 then data1656 else (if j < 58 then data1657 else data1658)) else (if j < 60 then data1659 else (if j < 61 then data1660 else data1661)))) else (if j < 68 then (if j < 65 then (if j < 63 then data1662 else (if j < 64 then data1663 else data1664)) else (if j < 66 then data1665 else (if j < 67 then data1666 else data1667))) else (if j < 71 then (if j < 69 then data1668 else (if j < 70 then data1669 else data1670)) else (if j < 73 then (if j < 72 then data1671 else data1672) else (if j < 74 then data1673 else data1674))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data1675 else (if j < 77 then data1676 else data1677)) else (if j < 79 then data1678 else (if j < 80 then data1679 else data1680))) else (if j < 84 then (if j < 82 then data1681 else (if j < 83 then data1682 else data1683)) else (if j < 85 then data1684 else (if j < 86 then data1685 else data1686)))) else (if j < 93 then (if j < 90 then (if j < 88 then data1687 else (if j < 89 then data1688 else data1689)) else (if j < 91 then data1690 else (if j < 92 then data1691 else data1692))) else (if j < 96 then (if j < 94 then data1693 else (if j < 95 then data1694 else data1695)) else (if j < 98 then (if j < 97 then data1696 else data1697) else (if j < 99 then data1698 else data1699))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data1700 else (if j < 102 then data1701 else data1702)) else (if j < 104 then data1703 else (if j < 105 then data1704 else data1705))) else (if j < 109 then (if j < 107 then data1706 else (if j < 108 then data1707 else data1708)) else (if j < 110 then data1709 else (if j < 111 then data1710 else data1711)))) else (if j < 118 then (if j < 115 then (if j < 113 then data1712 else (if j < 114 then data1713 else data1714)) else (if j < 116 then data1715 else (if j < 117 then data1716 else data1717))) else (if j < 121 then (if j < 119 then data1718 else (if j < 120 then data1719 else data1720)) else (if j < 123 then (if j < 122 then data1721 else data1722) else (if j < 124 then data1723 else data1724))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data1725 else (if j < 127 then data1726 else data1727)) else (if j < 129 then data1728 else (if j < 130 then data1729 else data1730))) else (if j < 134 then (if j < 132 then data1731 else (if j < 133 then data1732 else data1733)) else (if j < 135 then data1734 else (if j < 136 then data1735 else data1736)))) else (if j < 143 then (if j < 140 then (if j < 138 then data1737 else (if j < 139 then data1738 else data1739)) else (if j < 141 then data1740 else (if j < 142 then data1741 else data1742))) else (if j < 146 then (if j < 144 then data1743 else (if j < 145 then data1744 else data1745)) else (if j < 148 then (if j < 147 then data1746 else data1747) else (if j < 149 then data1748 else data1749)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data1750 else (if j < 152 then data1751 else data1752)) else (if j < 154 then data1753 else (if j < 155 then data1754 else data1755))) else (if j < 159 then (if j < 157 then data1756 else (if j < 158 then data1757 else data1758)) else (if j < 160 then data1759 else (if j < 161 then data1760 else data1761)))) else (if j < 168 then (if j < 165 then (if j < 163 then data1762 else (if j < 164 then data1763 else data1764)) else (if j < 166 then data1765 else (if j < 167 then data1766 else data1767))) else (if j < 171 then (if j < 169 then data1768 else (if j < 170 then data1769 else data1770)) else (if j < 173 then (if j < 172 then data1771 else data1772) else (if j < 174 then data1773 else data1774))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data1775 else (if j < 177 then data1776 else data1777)) else (if j < 179 then data1778 else (if j < 180 then data1779 else data1780))) else (if j < 184 then (if j < 182 then data1781 else (if j < 183 then data1782 else data1783)) else (if j < 185 then data1784 else (if j < 186 then data1785 else data1786)))) else (if j < 193 then (if j < 190 then (if j < 188 then data1787 else (if j < 189 then data1788 else data1789)) else (if j < 191 then data1790 else (if j < 192 then data1791 else data1792))) else (if j < 196 then (if j < 194 then data1793 else (if j < 195 then data1794 else data1795)) else (if j < 198 then (if j < 197 then data1796 else data1797) else (if j < 199 then data1798 else data1799))))))))

def srcTableB8 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src1600 else (if j < 2 then src1601 else src1602)) else (if j < 4 then src1603 else (if j < 5 then src1604 else src1605))) else (if j < 9 then (if j < 7 then src1606 else (if j < 8 then src1607 else src1608)) else (if j < 10 then src1609 else (if j < 11 then src1610 else src1611)))) else (if j < 18 then (if j < 15 then (if j < 13 then src1612 else (if j < 14 then src1613 else src1614)) else (if j < 16 then src1615 else (if j < 17 then src1616 else src1617))) else (if j < 21 then (if j < 19 then src1618 else (if j < 20 then src1619 else src1620)) else (if j < 23 then (if j < 22 then src1621 else src1622) else (if j < 24 then src1623 else src1624))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src1625 else (if j < 27 then src1626 else src1627)) else (if j < 29 then src1628 else (if j < 30 then src1629 else src1630))) else (if j < 34 then (if j < 32 then src1631 else (if j < 33 then src1632 else src1633)) else (if j < 35 then src1634 else (if j < 36 then src1635 else src1636)))) else (if j < 43 then (if j < 40 then (if j < 38 then src1637 else (if j < 39 then src1638 else src1639)) else (if j < 41 then src1640 else (if j < 42 then src1641 else src1642))) else (if j < 46 then (if j < 44 then src1643 else (if j < 45 then src1644 else src1645)) else (if j < 48 then (if j < 47 then src1646 else src1647) else (if j < 49 then src1648 else src1649)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src1650 else (if j < 52 then src1651 else src1652)) else (if j < 54 then src1653 else (if j < 55 then src1654 else src1655))) else (if j < 59 then (if j < 57 then src1656 else (if j < 58 then src1657 else src1658)) else (if j < 60 then src1659 else (if j < 61 then src1660 else src1661)))) else (if j < 68 then (if j < 65 then (if j < 63 then src1662 else (if j < 64 then src1663 else src1664)) else (if j < 66 then src1665 else (if j < 67 then src1666 else src1667))) else (if j < 71 then (if j < 69 then src1668 else (if j < 70 then src1669 else src1670)) else (if j < 73 then (if j < 72 then src1671 else src1672) else (if j < 74 then src1673 else src1674))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src1675 else (if j < 77 then src1676 else src1677)) else (if j < 79 then src1678 else (if j < 80 then src1679 else src1680))) else (if j < 84 then (if j < 82 then src1681 else (if j < 83 then src1682 else src1683)) else (if j < 85 then src1684 else (if j < 86 then src1685 else src1686)))) else (if j < 93 then (if j < 90 then (if j < 88 then src1687 else (if j < 89 then src1688 else src1689)) else (if j < 91 then src1690 else (if j < 92 then src1691 else src1692))) else (if j < 96 then (if j < 94 then src1693 else (if j < 95 then src1694 else src1695)) else (if j < 98 then (if j < 97 then src1696 else src1697) else (if j < 99 then src1698 else src1699))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src1700 else (if j < 102 then src1701 else src1702)) else (if j < 104 then src1703 else (if j < 105 then src1704 else src1705))) else (if j < 109 then (if j < 107 then src1706 else (if j < 108 then src1707 else src1708)) else (if j < 110 then src1709 else (if j < 111 then src1710 else src1711)))) else (if j < 118 then (if j < 115 then (if j < 113 then src1712 else (if j < 114 then src1713 else src1714)) else (if j < 116 then src1715 else (if j < 117 then src1716 else src1717))) else (if j < 121 then (if j < 119 then src1718 else (if j < 120 then src1719 else src1720)) else (if j < 123 then (if j < 122 then src1721 else src1722) else (if j < 124 then src1723 else src1724))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src1725 else (if j < 127 then src1726 else src1727)) else (if j < 129 then src1728 else (if j < 130 then src1729 else src1730))) else (if j < 134 then (if j < 132 then src1731 else (if j < 133 then src1732 else src1733)) else (if j < 135 then src1734 else (if j < 136 then src1735 else src1736)))) else (if j < 143 then (if j < 140 then (if j < 138 then src1737 else (if j < 139 then src1738 else src1739)) else (if j < 141 then src1740 else (if j < 142 then src1741 else src1742))) else (if j < 146 then (if j < 144 then src1743 else (if j < 145 then src1744 else src1745)) else (if j < 148 then (if j < 147 then src1746 else src1747) else (if j < 149 then src1748 else src1749)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src1750 else (if j < 152 then src1751 else src1752)) else (if j < 154 then src1753 else (if j < 155 then src1754 else src1755))) else (if j < 159 then (if j < 157 then src1756 else (if j < 158 then src1757 else src1758)) else (if j < 160 then src1759 else (if j < 161 then src1760 else src1761)))) else (if j < 168 then (if j < 165 then (if j < 163 then src1762 else (if j < 164 then src1763 else src1764)) else (if j < 166 then src1765 else (if j < 167 then src1766 else src1767))) else (if j < 171 then (if j < 169 then src1768 else (if j < 170 then src1769 else src1770)) else (if j < 173 then (if j < 172 then src1771 else src1772) else (if j < 174 then src1773 else src1774))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src1775 else (if j < 177 then src1776 else src1777)) else (if j < 179 then src1778 else (if j < 180 then src1779 else src1780))) else (if j < 184 then (if j < 182 then src1781 else (if j < 183 then src1782 else src1783)) else (if j < 185 then src1784 else (if j < 186 then src1785 else src1786)))) else (if j < 193 then (if j < 190 then (if j < 188 then src1787 else (if j < 189 then src1788 else src1789)) else (if j < 191 then src1790 else (if j < 192 then src1791 else src1792))) else (if j < 196 then (if j < 194 then src1793 else (if j < 195 then src1794 else src1795)) else (if j < 198 then (if j < 197 then src1796 else src1797) else (if j < 199 then src1798 else src1799))))))))

def dstTableB8 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst1600 else (if j < 2 then dst1601 else dst1602)) else (if j < 4 then dst1603 else (if j < 5 then dst1604 else dst1605))) else (if j < 9 then (if j < 7 then dst1606 else (if j < 8 then dst1607 else dst1608)) else (if j < 10 then dst1609 else (if j < 11 then dst1610 else dst1611)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst1612 else (if j < 14 then dst1613 else dst1614)) else (if j < 16 then dst1615 else (if j < 17 then dst1616 else dst1617))) else (if j < 21 then (if j < 19 then dst1618 else (if j < 20 then dst1619 else dst1620)) else (if j < 23 then (if j < 22 then dst1621 else dst1622) else (if j < 24 then dst1623 else dst1624))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst1625 else (if j < 27 then dst1626 else dst1627)) else (if j < 29 then dst1628 else (if j < 30 then dst1629 else dst1630))) else (if j < 34 then (if j < 32 then dst1631 else (if j < 33 then dst1632 else dst1633)) else (if j < 35 then dst1634 else (if j < 36 then dst1635 else dst1636)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst1637 else (if j < 39 then dst1638 else dst1639)) else (if j < 41 then dst1640 else (if j < 42 then dst1641 else dst1642))) else (if j < 46 then (if j < 44 then dst1643 else (if j < 45 then dst1644 else dst1645)) else (if j < 48 then (if j < 47 then dst1646 else dst1647) else (if j < 49 then dst1648 else dst1649)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst1650 else (if j < 52 then dst1651 else dst1652)) else (if j < 54 then dst1653 else (if j < 55 then dst1654 else dst1655))) else (if j < 59 then (if j < 57 then dst1656 else (if j < 58 then dst1657 else dst1658)) else (if j < 60 then dst1659 else (if j < 61 then dst1660 else dst1661)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst1662 else (if j < 64 then dst1663 else dst1664)) else (if j < 66 then dst1665 else (if j < 67 then dst1666 else dst1667))) else (if j < 71 then (if j < 69 then dst1668 else (if j < 70 then dst1669 else dst1670)) else (if j < 73 then (if j < 72 then dst1671 else dst1672) else (if j < 74 then dst1673 else dst1674))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst1675 else (if j < 77 then dst1676 else dst1677)) else (if j < 79 then dst1678 else (if j < 80 then dst1679 else dst1680))) else (if j < 84 then (if j < 82 then dst1681 else (if j < 83 then dst1682 else dst1683)) else (if j < 85 then dst1684 else (if j < 86 then dst1685 else dst1686)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst1687 else (if j < 89 then dst1688 else dst1689)) else (if j < 91 then dst1690 else (if j < 92 then dst1691 else dst1692))) else (if j < 96 then (if j < 94 then dst1693 else (if j < 95 then dst1694 else dst1695)) else (if j < 98 then (if j < 97 then dst1696 else dst1697) else (if j < 99 then dst1698 else dst1699))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst1700 else (if j < 102 then dst1701 else dst1702)) else (if j < 104 then dst1703 else (if j < 105 then dst1704 else dst1705))) else (if j < 109 then (if j < 107 then dst1706 else (if j < 108 then dst1707 else dst1708)) else (if j < 110 then dst1709 else (if j < 111 then dst1710 else dst1711)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst1712 else (if j < 114 then dst1713 else dst1714)) else (if j < 116 then dst1715 else (if j < 117 then dst1716 else dst1717))) else (if j < 121 then (if j < 119 then dst1718 else (if j < 120 then dst1719 else dst1720)) else (if j < 123 then (if j < 122 then dst1721 else dst1722) else (if j < 124 then dst1723 else dst1724))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst1725 else (if j < 127 then dst1726 else dst1727)) else (if j < 129 then dst1728 else (if j < 130 then dst1729 else dst1730))) else (if j < 134 then (if j < 132 then dst1731 else (if j < 133 then dst1732 else dst1733)) else (if j < 135 then dst1734 else (if j < 136 then dst1735 else dst1736)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst1737 else (if j < 139 then dst1738 else dst1739)) else (if j < 141 then dst1740 else (if j < 142 then dst1741 else dst1742))) else (if j < 146 then (if j < 144 then dst1743 else (if j < 145 then dst1744 else dst1745)) else (if j < 148 then (if j < 147 then dst1746 else dst1747) else (if j < 149 then dst1748 else dst1749)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst1750 else (if j < 152 then dst1751 else dst1752)) else (if j < 154 then dst1753 else (if j < 155 then dst1754 else dst1755))) else (if j < 159 then (if j < 157 then dst1756 else (if j < 158 then dst1757 else dst1758)) else (if j < 160 then dst1759 else (if j < 161 then dst1760 else dst1761)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst1762 else (if j < 164 then dst1763 else dst1764)) else (if j < 166 then dst1765 else (if j < 167 then dst1766 else dst1767))) else (if j < 171 then (if j < 169 then dst1768 else (if j < 170 then dst1769 else dst1770)) else (if j < 173 then (if j < 172 then dst1771 else dst1772) else (if j < 174 then dst1773 else dst1774))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst1775 else (if j < 177 then dst1776 else dst1777)) else (if j < 179 then dst1778 else (if j < 180 then dst1779 else dst1780))) else (if j < 184 then (if j < 182 then dst1781 else (if j < 183 then dst1782 else dst1783)) else (if j < 185 then dst1784 else (if j < 186 then dst1785 else dst1786)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst1787 else (if j < 189 then dst1788 else dst1789)) else (if j < 191 then dst1790 else (if j < 192 then dst1791 else dst1792))) else (if j < 196 then (if j < 194 then dst1793 else (if j < 195 then dst1794 else dst1795)) else (if j < 198 then (if j < 197 then dst1796 else dst1797) else (if j < 199 then dst1798 else dst1799))))))))

def caseB8 (i : Fin 200) : Cases := ⟨1600 + i.val,by have := i.isLt; omega⟩
lemma tableB8_valid (i : Fin 200) :
    (lookupB8 i.val).Valid (srcTableB8 i.val) (dstTableB8 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data1600
  · exact valid_data1601
  · exact valid_data1602
  · exact valid_data1603
  · exact valid_data1604
  · exact valid_data1605
  · exact valid_data1606
  · exact valid_data1607
  · exact valid_data1608
  · exact valid_data1609
  · exact valid_data1610
  · exact valid_data1611
  · exact valid_data1612
  · exact valid_data1613
  · exact valid_data1614
  · exact valid_data1615
  · exact valid_data1616
  · exact valid_data1617
  · exact valid_data1618
  · exact valid_data1619
  · exact valid_data1620
  · exact valid_data1621
  · exact valid_data1622
  · exact valid_data1623
  · exact valid_data1624
  · exact valid_data1625
  · exact valid_data1626
  · exact valid_data1627
  · exact valid_data1628
  · exact valid_data1629
  · exact valid_data1630
  · exact valid_data1631
  · exact valid_data1632
  · exact valid_data1633
  · exact valid_data1634
  · exact valid_data1635
  · exact valid_data1636
  · exact valid_data1637
  · exact valid_data1638
  · exact valid_data1639
  · exact valid_data1640
  · exact valid_data1641
  · exact valid_data1642
  · exact valid_data1643
  · exact valid_data1644
  · exact valid_data1645
  · exact valid_data1646
  · exact valid_data1647
  · exact valid_data1648
  · exact valid_data1649
  · exact valid_data1650
  · exact valid_data1651
  · exact valid_data1652
  · exact valid_data1653
  · exact valid_data1654
  · exact valid_data1655
  · exact valid_data1656
  · exact valid_data1657
  · exact valid_data1658
  · exact valid_data1659
  · exact valid_data1660
  · exact valid_data1661
  · exact valid_data1662
  · exact valid_data1663
  · exact valid_data1664
  · exact valid_data1665
  · exact valid_data1666
  · exact valid_data1667
  · exact valid_data1668
  · exact valid_data1669
  · exact valid_data1670
  · exact valid_data1671
  · exact valid_data1672
  · exact valid_data1673
  · exact valid_data1674
  · exact valid_data1675
  · exact valid_data1676
  · exact valid_data1677
  · exact valid_data1678
  · exact valid_data1679
  · exact valid_data1680
  · exact valid_data1681
  · exact valid_data1682
  · exact valid_data1683
  · exact valid_data1684
  · exact valid_data1685
  · exact valid_data1686
  · exact valid_data1687
  · exact valid_data1688
  · exact valid_data1689
  · exact valid_data1690
  · exact valid_data1691
  · exact valid_data1692
  · exact valid_data1693
  · exact valid_data1694
  · exact valid_data1695
  · exact valid_data1696
  · exact valid_data1697
  · exact valid_data1698
  · exact valid_data1699
  · exact valid_data1700
  · exact valid_data1701
  · exact valid_data1702
  · exact valid_data1703
  · exact valid_data1704
  · exact valid_data1705
  · exact valid_data1706
  · exact valid_data1707
  · exact valid_data1708
  · exact valid_data1709
  · exact valid_data1710
  · exact valid_data1711
  · exact valid_data1712
  · exact valid_data1713
  · exact valid_data1714
  · exact valid_data1715
  · exact valid_data1716
  · exact valid_data1717
  · exact valid_data1718
  · exact valid_data1719
  · exact valid_data1720
  · exact valid_data1721
  · exact valid_data1722
  · exact valid_data1723
  · exact valid_data1724
  · exact valid_data1725
  · exact valid_data1726
  · exact valid_data1727
  · exact valid_data1728
  · exact valid_data1729
  · exact valid_data1730
  · exact valid_data1731
  · exact valid_data1732
  · exact valid_data1733
  · exact valid_data1734
  · exact valid_data1735
  · exact valid_data1736
  · exact valid_data1737
  · exact valid_data1738
  · exact valid_data1739
  · exact valid_data1740
  · exact valid_data1741
  · exact valid_data1742
  · exact valid_data1743
  · exact valid_data1744
  · exact valid_data1745
  · exact valid_data1746
  · exact valid_data1747
  · exact valid_data1748
  · exact valid_data1749
  · exact valid_data1750
  · exact valid_data1751
  · exact valid_data1752
  · exact valid_data1753
  · exact valid_data1754
  · exact valid_data1755
  · exact valid_data1756
  · exact valid_data1757
  · exact valid_data1758
  · exact valid_data1759
  · exact valid_data1760
  · exact valid_data1761
  · exact valid_data1762
  · exact valid_data1763
  · exact valid_data1764
  · exact valid_data1765
  · exact valid_data1766
  · exact valid_data1767
  · exact valid_data1768
  · exact valid_data1769
  · exact valid_data1770
  · exact valid_data1771
  · exact valid_data1772
  · exact valid_data1773
  · exact valid_data1774
  · exact valid_data1775
  · exact valid_data1776
  · exact valid_data1777
  · exact valid_data1778
  · exact valid_data1779
  · exact valid_data1780
  · exact valid_data1781
  · exact valid_data1782
  · exact valid_data1783
  · exact valid_data1784
  · exact valid_data1785
  · exact valid_data1786
  · exact valid_data1787
  · exact valid_data1788
  · exact valid_data1789
  · exact valid_data1790
  · exact valid_data1791
  · exact valid_data1792
  · exact valid_data1793
  · exact valid_data1794
  · exact valid_data1795
  · exact valid_data1796
  · exact valid_data1797
  · exact valid_data1798
  · exact valid_data1799

lemma srcB8_row : ∀ (i : Fin 200) (e : E),
    srcTableB8 i.val e = caseSource (caseB8 i) e := by decide +kernel

lemma dstB8_row : ∀ (i : Fin 200) (e : E),
    dstTableB8 i.val e = caseTarget (caseB8 i) e := by decide +kernel

lemma sizeB8 : ∀ i : Fin 200, (lookupB8 i.val).size ≤ 5 →
    (lookupB8 i.val).size = 2 ∧
      (⟨caseKey (caseB8 i),caseKey_lt (caseB8 i)⟩ : Fin 3888) ∈ good := by decide +kernel
lemma certificateB8 (i : Fin 200) : Certificate (caseB8 i) := by
  refine ⟨lookupB8 i.val,?_,sizeB8 i⟩
  have hv := tableB8_valid i
  rw [funext (srcB8_row i),funext (dstB8_row i)] at hv
  exact hv
lemma certificateInterval8 : FiniteIntervals.Covers CertificateAt 1600 1800 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 1600 200 (fun i _ => certificateB8 i)
#print axioms certificateInterval8
end Erdos184Work.FiveRows1
