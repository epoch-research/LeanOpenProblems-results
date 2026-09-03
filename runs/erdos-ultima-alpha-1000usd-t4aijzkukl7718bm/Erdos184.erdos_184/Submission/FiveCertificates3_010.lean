import Submission.FiveCertificates3Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows3
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src2000 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,26,28,6,26,16,27,38,8,28,18,38]
def dst2000 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2000_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2000_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2000_2 : CycleData E W := ⟨3,![2,23,18,11,6],![3,8,38,27,14]⟩
def cycle2000_3 : CycleData E W := ⟨3,![4,3,7,8,9],![2,6,3,16,18]⟩
def cycle2000_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle2000_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,26,28,18,38]⟩
def data2000 : PartitionData E W := ⟨6,![cycle2000_0,cycle2000_1,cycle2000_2,cycle2000_3,cycle2000_4,cycle2000_5]⟩
lemma valid_data2000 : data2000.Valid src2000 dst2000 Finset.univ := by decide +kernel

def src2001 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,26,28,6,26,16,38,27,8,18,28,38]
def dst2001 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2001_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2001_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2001_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2001_3 : CycleData E W := ⟨2,![3,19,11,6],![3,6,27,14]⟩
def cycle2001_4 : CycleData E W := ⟨3,![4,15,16,8,9],![2,6,26,16,18]⟩
def cycle2001_5 : CycleData E W := ⟨2,![12,18,22,13],![26,27,38,28]⟩
def data2001 : PartitionData E W := ⟨6,![cycle2001_0,cycle2001_1,cycle2001_2,cycle2001_3,cycle2001_4,cycle2001_5]⟩
lemma valid_data2001 : data2001.Valid src2001 dst2001 Finset.univ := by decide +kernel

def src2002 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,26,28,6,26,16,38,27,8,18,38,28]
def dst2002 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2002_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2002_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2002_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2002_3 : CycleData E W := ⟨3,![3,15,12,11,6],![3,6,26,27,14]⟩
def cycle2002_4 : CycleData E W := ⟨3,![4,19,18,21,9],![2,6,27,38,18]⟩
def cycle2002_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data2002 : PartitionData E W := ⟨6,![cycle2002_0,cycle2002_1,cycle2002_2,cycle2002_3,cycle2002_4,cycle2002_5]⟩
lemma valid_data2002 : data2002.Valid src2002 dst2002 Finset.univ := by decide +kernel

def src2003 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,26,28,6,26,16,38,27,8,28,18,38]
def dst2003 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2003_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2003_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2003_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2003_3 : CycleData E W := ⟨3,![3,15,12,11,6],![3,6,26,27,14]⟩
def cycle2003_4 : CycleData E W := ⟨3,![4,19,18,22,9],![2,6,27,38,18]⟩
def cycle2003_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data2003 : PartitionData E W := ⟨6,![cycle2003_0,cycle2003_1,cycle2003_2,cycle2003_3,cycle2003_4,cycle2003_5]⟩
lemma valid_data2003 : data2003.Valid src2003 dst2003 Finset.univ := by decide +kernel

def src2004 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,28,26,6,26,16,27,38,8,18,28,38]
def dst2004 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,28,26,4,26,16,27,38,6,18,28,38,8]
def cycle2004_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2004_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,8,4,26,6]⟩
def cycle2004_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2004_3 : CycleData E W := ⟨2,![6,11,17,7],![3,14,27,16]⟩
def cycle2004_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2004_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2004 : PartitionData E W := ⟨6,![cycle2004_0,cycle2004_1,cycle2004_2,cycle2004_3,cycle2004_4,cycle2004_5]⟩
lemma valid_data2004 : data2004.Valid src2004 dst2004 Finset.univ := by decide +kernel

def src2005 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,28,26,6,26,16,27,38,8,18,38,28]
def dst2005 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,28,26,4,26,16,27,38,6,18,38,28,8]
def cycle2005_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2005_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,8,4,26,6]⟩
def cycle2005_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2005_3 : CycleData E W := ⟨2,![6,11,17,7],![3,14,27,16]⟩
def cycle2005_4 : CycleData E W := ⟨3,![20,8,16,13,23],![8,18,16,26,28]⟩
def cycle2005_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2005 : PartitionData E W := ⟨6,![cycle2005_0,cycle2005_1,cycle2005_2,cycle2005_3,cycle2005_4,cycle2005_5]⟩
lemma valid_data2005 : data2005.Valid src2005 dst2005 Finset.univ := by decide +kernel

def src2006 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,28,26,6,26,16,27,38,8,28,18,38]
def dst2006 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,28,26,4,26,16,27,38,6,28,18,38,8]
def cycle2006_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2006_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,8,4,26,6]⟩
def cycle2006_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2006_3 : CycleData E W := ⟨2,![6,11,17,7],![3,14,27,16]⟩
def cycle2006_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2006_5 : CycleData E W := ⟨2,![20,12,18,23],![8,28,27,38]⟩
def data2006 : PartitionData E W := ⟨6,![cycle2006_0,cycle2006_1,cycle2006_2,cycle2006_3,cycle2006_4,cycle2006_5]⟩
lemma valid_data2006 : data2006.Valid src2006 dst2006 Finset.univ := by decide +kernel

def src2007 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,28,26,6,26,16,38,27,8,18,28,38]
def dst2007 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,28,26,4,26,16,38,27,6,18,28,38,8]
def cycle2007_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2007_1 : CycleData E W := ⟨3,![2,1,14,16,7],![3,8,4,26,16]⟩
def cycle2007_2 : CycleData E W := ⟨2,![3,19,11,6],![3,6,27,14]⟩
def cycle2007_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle2007_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2007_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2007 : PartitionData E W := ⟨6,![cycle2007_0,cycle2007_1,cycle2007_2,cycle2007_3,cycle2007_4,cycle2007_5]⟩
lemma valid_data2007 : data2007.Valid src2007 dst2007 Finset.univ := by decide +kernel

def src2008 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,28,26,6,26,16,38,27,8,18,38,28]
def dst2008 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,28,26,4,26,16,38,27,6,18,38,28,8]
def cycle2008_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2008_1 : CycleData E W := ⟨3,![2,1,14,16,7],![3,8,4,26,16]⟩
def cycle2008_2 : CycleData E W := ⟨2,![3,19,11,6],![3,6,27,14]⟩
def cycle2008_3 : CycleData E W := ⟨4,![4,15,13,23,20,9],![2,6,26,28,8,18]⟩
def cycle2008_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2008_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2008 : PartitionData E W := ⟨6,![cycle2008_0,cycle2008_1,cycle2008_2,cycle2008_3,cycle2008_4,cycle2008_5]⟩
lemma valid_data2008 : data2008.Valid src2008 dst2008 Finset.univ := by decide +kernel

def src2009 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,28,26,6,26,16,38,27,8,28,18,38]
def dst2009 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,28,26,4,26,16,38,27,6,28,18,38,8]
def cycle2009_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2009_1 : CycleData E W := ⟨3,![2,1,14,16,7],![3,8,4,26,16]⟩
def cycle2009_2 : CycleData E W := ⟨2,![3,19,11,6],![3,6,27,14]⟩
def cycle2009_3 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle2009_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2009_5 : CycleData E W := ⟨2,![20,12,18,23],![8,28,27,38]⟩
def data2009 : PartitionData E W := ⟨6,![cycle2009_0,cycle2009_1,cycle2009_2,cycle2009_3,cycle2009_4,cycle2009_5]⟩
lemma valid_data2009 : data2009.Valid src2009 dst2009 Finset.univ := by decide +kernel

def src2010 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,28,26,6,26,38,16,27,8,18,28,38]
def dst2010 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,28,26,4,26,38,16,27,6,18,28,38,8]
def cycle2010_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2010_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,8,4,26,6]⟩
def cycle2010_2 : CycleData E W := ⟨3,![4,19,12,21,9],![2,6,27,28,18]⟩
def cycle2010_3 : CycleData E W := ⟨2,![6,11,18,7],![3,14,27,16]⟩
def cycle2010_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2010_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2010 : PartitionData E W := ⟨6,![cycle2010_0,cycle2010_1,cycle2010_2,cycle2010_3,cycle2010_4,cycle2010_5]⟩
lemma valid_data2010 : data2010.Valid src2010 dst2010 Finset.univ := by decide +kernel

def src2011 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,28,26,6,26,38,16,27,8,18,38,28]
def dst2011 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,28,26,4,26,38,16,27,6,18,38,28,8]
def cycle2011_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2011_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,8,4,26,6]⟩
def cycle2011_2 : CycleData E W := ⟨4,![4,19,12,23,20,9],![2,6,27,28,8,18]⟩
def cycle2011_3 : CycleData E W := ⟨2,![6,11,18,7],![3,14,27,16]⟩
def cycle2011_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2011_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2011 : PartitionData E W := ⟨6,![cycle2011_0,cycle2011_1,cycle2011_2,cycle2011_3,cycle2011_4,cycle2011_5]⟩
lemma valid_data2011 : data2011.Valid src2011 dst2011 Finset.univ := by decide +kernel

def src2012 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,28,26,6,26,38,16,27,8,28,18,38]
def dst2012 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,28,26,4,26,38,16,27,6,28,18,38,8]
def cycle2012_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2012_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,8,4,26,6]⟩
def cycle2012_2 : CycleData E W := ⟨3,![4,19,12,21,9],![2,6,27,28,18]⟩
def cycle2012_3 : CycleData E W := ⟨2,![6,11,18,7],![3,14,27,16]⟩
def cycle2012_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2012_5 : CycleData E W := ⟨2,![20,13,16,23],![8,28,26,38]⟩
def data2012 : PartitionData E W := ⟨6,![cycle2012_0,cycle2012_1,cycle2012_2,cycle2012_3,cycle2012_4,cycle2012_5]⟩
lemma valid_data2012 : data2012.Valid src2012 dst2012 Finset.univ := by decide +kernel

def src2013 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,28,26,6,27,16,26,38,8,18,28,38]
def dst2013 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,28,26,4,27,16,26,38,6,18,28,38,8]
def cycle2013_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2013_1 : CycleData E W := ⟨3,![2,1,14,17,7],![3,8,4,26,16]⟩
def cycle2013_2 : CycleData E W := ⟨2,![3,15,11,6],![3,6,27,14]⟩
def cycle2013_3 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2013_4 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,27]⟩
def cycle2013_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2013 : PartitionData E W := ⟨6,![cycle2013_0,cycle2013_1,cycle2013_2,cycle2013_3,cycle2013_4,cycle2013_5]⟩
lemma valid_data2013 : data2013.Valid src2013 dst2013 Finset.univ := by decide +kernel

def src2014 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,28,26,6,27,16,26,38,8,18,38,28]
def dst2014 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,28,26,4,27,16,26,38,6,18,38,28,8]
def cycle2014_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2014_1 : CycleData E W := ⟨3,![2,1,14,17,7],![3,8,4,26,16]⟩
def cycle2014_2 : CycleData E W := ⟨2,![3,15,11,6],![3,6,27,14]⟩
def cycle2014_3 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2014_4 : CycleData E W := ⟨3,![20,8,16,12,23],![8,18,16,27,28]⟩
def cycle2014_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2014 : PartitionData E W := ⟨6,![cycle2014_0,cycle2014_1,cycle2014_2,cycle2014_3,cycle2014_4,cycle2014_5]⟩
lemma valid_data2014 : data2014.Valid src2014 dst2014 Finset.univ := by decide +kernel

def src2015 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,27,28,26,6,27,16,26,38,8,28,18,38]
def dst2015 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,27,28,26,4,27,16,26,38,6,28,18,38,8]
def cycle2015_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2015_1 : CycleData E W := ⟨3,![2,1,14,17,7],![3,8,4,26,16]⟩
def cycle2015_2 : CycleData E W := ⟨2,![3,15,11,6],![3,6,27,14]⟩
def cycle2015_3 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2015_4 : CycleData E W := ⟨2,![8,21,12,16],![16,18,28,27]⟩
def cycle2015_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,26,38]⟩
def data2015 : PartitionData E W := ⟨6,![cycle2015_0,cycle2015_1,cycle2015_2,cycle2015_3,cycle2015_4,cycle2015_5]⟩
lemma valid_data2015 : data2015.Valid src2015 dst2015 Finset.univ := by decide +kernel

def src2016 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,28,26,27,6,26,16,27,38,8,18,28,38]
def dst2016 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,28,26,27,4,26,16,27,38,6,18,28,38,8]
def cycle2016_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2016_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2016_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2016_3 : CycleData E W := ⟨3,![3,15,12,11,6],![3,6,26,28,14]⟩
def cycle2016_4 : CycleData E W := ⟨3,![4,19,22,21,9],![2,6,38,28,18]⟩
def cycle2016_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data2016 : PartitionData E W := ⟨6,![cycle2016_0,cycle2016_1,cycle2016_2,cycle2016_3,cycle2016_4,cycle2016_5]⟩
lemma valid_data2016 : data2016.Valid src2016 dst2016 Finset.univ := by decide +kernel

def src2017 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,28,26,27,6,26,16,27,38,8,18,38,28]
def dst2017 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,28,26,27,4,26,16,27,38,6,18,38,28,8]
def cycle2017_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2017_1 : CycleData E W := ⟨3,![1,20,8,17,14],![4,8,18,16,27]⟩
def cycle2017_2 : CycleData E W := ⟨2,![2,23,11,6],![3,8,28,14]⟩
def cycle2017_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,26,16]⟩
def cycle2017_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2017_5 : CycleData E W := ⟨2,![12,22,18,13],![26,28,38,27]⟩
def data2017 : PartitionData E W := ⟨6,![cycle2017_0,cycle2017_1,cycle2017_2,cycle2017_3,cycle2017_4,cycle2017_5]⟩
lemma valid_data2017 : data2017.Valid src2017 dst2017 Finset.univ := by decide +kernel

def src2018 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,28,26,27,6,26,16,27,38,8,28,18,38]
def dst2018 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,28,26,27,4,26,16,27,38,6,28,18,38,8]
def cycle2018_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2018_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2018_2 : CycleData E W := ⟨2,![2,20,11,6],![3,8,28,14]⟩
def cycle2018_3 : CycleData E W := ⟨3,![4,3,7,8,9],![2,6,3,16,18]⟩
def cycle2018_4 : CycleData E W := ⟨3,![15,12,21,22,19],![6,26,28,18,38]⟩
def cycle2018_5 : CycleData E W := ⟨1,![16,13,17],![16,26,27]⟩
def data2018 : PartitionData E W := ⟨6,![cycle2018_0,cycle2018_1,cycle2018_2,cycle2018_3,cycle2018_4,cycle2018_5]⟩
lemma valid_data2018 : data2018.Valid src2018 dst2018 Finset.univ := by decide +kernel

def src2019 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,28,26,27,6,26,16,38,27,8,18,28,38]
def dst2019 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,28,26,27,4,26,16,38,27,6,18,28,38,8]
def cycle2019_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2019_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2019_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2019_3 : CycleData E W := ⟨4,![4,3,6,11,21,9],![2,6,3,14,28,18]⟩
def cycle2019_4 : CycleData E W := ⟨2,![16,12,22,17],![16,26,28,38]⟩
def cycle2019_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2019 : PartitionData E W := ⟨6,![cycle2019_0,cycle2019_1,cycle2019_2,cycle2019_3,cycle2019_4,cycle2019_5]⟩
lemma valid_data2019 : data2019.Valid src2019 dst2019 Finset.univ := by decide +kernel

def src2020 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,28,26,27,6,26,16,38,27,8,18,38,28]
def dst2020 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,28,26,27,4,26,16,38,27,6,18,38,28,8]
def cycle2020_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2020_1 : CycleData E W := ⟨4,![4,19,14,1,20,9],![2,6,27,4,8,18]⟩
def cycle2020_2 : CycleData E W := ⟨2,![2,23,11,6],![3,8,28,14]⟩
def cycle2020_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,26,16]⟩
def cycle2020_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2020_5 : CycleData E W := ⟨2,![12,22,18,13],![26,28,38,27]⟩
def data2020 : PartitionData E W := ⟨6,![cycle2020_0,cycle2020_1,cycle2020_2,cycle2020_3,cycle2020_4,cycle2020_5]⟩
lemma valid_data2020 : data2020.Valid src2020 dst2020 Finset.univ := by decide +kernel

def src2021 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,28,26,27,6,26,16,38,27,8,28,18,38]
def dst2021 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,28,26,27,4,26,16,38,27,6,28,18,38,8]
def cycle2021_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2021_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2021_2 : CycleData E W := ⟨2,![2,20,11,6],![3,8,28,14]⟩
def cycle2021_3 : CycleData E W := ⟨3,![4,3,7,8,9],![2,6,3,16,18]⟩
def cycle2021_4 : CycleData E W := ⟨3,![16,12,21,22,17],![16,26,28,18,38]⟩
def cycle2021_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2021 : PartitionData E W := ⟨6,![cycle2021_0,cycle2021_1,cycle2021_2,cycle2021_3,cycle2021_4,cycle2021_5]⟩
lemma valid_data2021 : data2021.Valid src2021 dst2021 Finset.univ := by decide +kernel

def src2022 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,28,27,26,6,26,38,16,27,8,18,28,38]
def dst2022 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,28,27,26,4,26,38,16,27,6,18,28,38,8]
def cycle2022_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2022_1 : CycleData E W := ⟨2,![1,23,16,14],![4,8,38,26]⟩
def cycle2022_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2022_3 : CycleData E W := ⟨4,![4,3,6,11,21,9],![2,6,3,14,28,18]⟩
def cycle2022_4 : CycleData E W := ⟨2,![17,22,12,18],![16,38,28,27]⟩
def cycle2022_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2022 : PartitionData E W := ⟨6,![cycle2022_0,cycle2022_1,cycle2022_2,cycle2022_3,cycle2022_4,cycle2022_5]⟩
lemma valid_data2022 : data2022.Valid src2022 dst2022 Finset.univ := by decide +kernel

def src2023 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,28,27,26,6,26,38,16,27,8,18,38,28]
def dst2023 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,28,27,26,4,26,38,16,27,6,18,38,28,8]
def cycle2023_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2023_1 : CycleData E W := ⟨4,![4,15,14,1,20,9],![2,6,26,4,8,18]⟩
def cycle2023_2 : CycleData E W := ⟨2,![2,23,11,6],![3,8,28,14]⟩
def cycle2023_3 : CycleData E W := ⟨2,![3,19,18,7],![3,6,27,16]⟩
def cycle2023_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2023_5 : CycleData E W := ⟨2,![13,12,22,16],![26,27,28,38]⟩
def data2023 : PartitionData E W := ⟨6,![cycle2023_0,cycle2023_1,cycle2023_2,cycle2023_3,cycle2023_4,cycle2023_5]⟩
lemma valid_data2023 : data2023.Valid src2023 dst2023 Finset.univ := by decide +kernel

def src2024 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,28,27,26,6,26,38,16,27,8,28,18,38]
def dst2024 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,28,27,26,4,26,38,16,27,6,28,18,38,8]
def cycle2024_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2024_1 : CycleData E W := ⟨2,![1,23,16,14],![4,8,38,26]⟩
def cycle2024_2 : CycleData E W := ⟨2,![2,20,11,6],![3,8,28,14]⟩
def cycle2024_3 : CycleData E W := ⟨3,![4,3,7,8,9],![2,6,3,16,18]⟩
def cycle2024_4 : CycleData E W := ⟨3,![17,22,21,12,18],![16,38,18,28,27]⟩
def cycle2024_5 : CycleData E W := ⟨1,![15,13,19],![6,26,27]⟩
def data2024 : PartitionData E W := ⟨6,![cycle2024_0,cycle2024_1,cycle2024_2,cycle2024_3,cycle2024_4,cycle2024_5]⟩
lemma valid_data2024 : data2024.Valid src2024 dst2024 Finset.univ := by decide +kernel

def src2025 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,28,27,26,6,27,16,26,38,8,18,28,38]
def dst2025 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,28,27,26,4,27,16,26,38,6,18,28,38,8]
def cycle2025_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2025_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,26]⟩
def cycle2025_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2025_3 : CycleData E W := ⟨3,![3,15,12,11,6],![3,6,27,28,14]⟩
def cycle2025_4 : CycleData E W := ⟨3,![4,19,22,21,9],![2,6,38,28,18]⟩
def cycle2025_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data2025 : PartitionData E W := ⟨6,![cycle2025_0,cycle2025_1,cycle2025_2,cycle2025_3,cycle2025_4,cycle2025_5]⟩
lemma valid_data2025 : data2025.Valid src2025 dst2025 Finset.univ := by decide +kernel

def src2026 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,28,27,26,6,27,16,26,38,8,18,38,28]
def dst2026 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,28,27,26,4,27,16,26,38,6,18,38,28,8]
def cycle2026_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2026_1 : CycleData E W := ⟨3,![1,20,8,17,14],![4,8,18,16,26]⟩
def cycle2026_2 : CycleData E W := ⟨2,![2,23,11,6],![3,8,28,14]⟩
def cycle2026_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,27,16]⟩
def cycle2026_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2026_5 : CycleData E W := ⟨2,![13,12,22,18],![26,27,28,38]⟩
def data2026 : PartitionData E W := ⟨6,![cycle2026_0,cycle2026_1,cycle2026_2,cycle2026_3,cycle2026_4,cycle2026_5]⟩
lemma valid_data2026 : data2026.Valid src2026 dst2026 Finset.univ := by decide +kernel

def src2027 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,14,28,27,26,6,27,16,26,38,8,28,18,38]
def dst2027 : E → W := ![4,8,3,6,2,14,3,16,18,2,14,28,27,26,4,27,16,26,38,6,28,18,38,8]
def cycle2027_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2027_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,26]⟩
def cycle2027_2 : CycleData E W := ⟨2,![2,20,11,6],![3,8,28,14]⟩
def cycle2027_3 : CycleData E W := ⟨3,![4,3,7,8,9],![2,6,3,16,18]⟩
def cycle2027_4 : CycleData E W := ⟨3,![15,12,21,22,19],![6,27,28,18,38]⟩
def cycle2027_5 : CycleData E W := ⟨1,![16,13,17],![16,27,26]⟩
def data2027 : PartitionData E W := ⟨6,![cycle2027_0,cycle2027_1,cycle2027_2,cycle2027_3,cycle2027_4,cycle2027_5]⟩
lemma valid_data2027 : data2027.Valid src2027 dst2027 Finset.univ := by decide +kernel

def src2028 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,16,26,38,27,8,18,28,38]
def dst2028 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,16,26,38,27,6,18,28,38,8]
def cycle2028_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2028_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2028_2 : CycleData E W := ⟨3,![2,23,17,16,7],![3,8,38,26,16]⟩
def cycle2028_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2028_4 : CycleData E W := ⟨2,![4,15,8,9],![2,6,16,18]⟩
def cycle2028_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2028 : PartitionData E W := ⟨6,![cycle2028_0,cycle2028_1,cycle2028_2,cycle2028_3,cycle2028_4,cycle2028_5]⟩
lemma valid_data2028 : data2028.Valid src2028 dst2028 Finset.univ := by decide +kernel

def src2029 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,16,26,38,27,8,18,38,28]
def dst2029 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,16,26,38,27,6,18,38,28,8]
def cycle2029_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2029_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2029_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2029_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2029_4 : CycleData E W := ⟨4,![4,15,16,17,21,9],![2,6,16,26,38,18]⟩
def cycle2029_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2029 : PartitionData E W := ⟨6,![cycle2029_0,cycle2029_1,cycle2029_2,cycle2029_3,cycle2029_4,cycle2029_5]⟩
lemma valid_data2029 : data2029.Valid src2029 dst2029 Finset.univ := by decide +kernel

def src2030 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,16,26,38,27,8,28,18,38]
def dst2030 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,16,26,38,27,6,28,18,38,8]
def cycle2030_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2030_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2030_2 : CycleData E W := ⟨3,![2,23,17,16,7],![3,8,38,26,16]⟩
def cycle2030_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2030_4 : CycleData E W := ⟨2,![4,15,8,9],![2,6,16,18]⟩
def cycle2030_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2030 : PartitionData E W := ⟨6,![cycle2030_0,cycle2030_1,cycle2030_2,cycle2030_3,cycle2030_4,cycle2030_5]⟩
lemma valid_data2030 : data2030.Valid src2030 dst2030 Finset.univ := by decide +kernel

def src2031 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,16,27,26,38,8,18,28,38]
def dst2031 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,16,27,26,38,6,18,28,38,8]
def cycle2031_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2031_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2031_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2031_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2031_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle2031_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data2031 : PartitionData E W := ⟨6,![cycle2031_0,cycle2031_1,cycle2031_2,cycle2031_3,cycle2031_4,cycle2031_5]⟩
lemma valid_data2031 : data2031.Valid src2031 dst2031 Finset.univ := by decide +kernel

def src2032 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,16,27,26,38,8,18,38,28]
def dst2032 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,16,27,26,38,6,18,38,28,8]
def cycle2032_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2032_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2032_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2032_3 : CycleData E W := ⟨3,![20,8,16,13,23],![8,18,16,27,28]⟩
def cycle2032_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle2032_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data2032 : PartitionData E W := ⟨6,![cycle2032_0,cycle2032_1,cycle2032_2,cycle2032_3,cycle2032_4,cycle2032_5]⟩
lemma valid_data2032 : data2032.Valid src2032 dst2032 Finset.univ := by decide +kernel

def src2033 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,16,27,26,38,8,28,18,38]
def dst2033 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,16,27,26,38,6,28,18,38,8]
def cycle2033_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2033_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2033_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2033_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2033_4 : CycleData E W := ⟨3,![10,18,23,20,14],![4,26,38,8,28]⟩
def cycle2033_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data2033 : PartitionData E W := ⟨6,![cycle2033_0,cycle2033_1,cycle2033_2,cycle2033_3,cycle2033_4,cycle2033_5]⟩
lemma valid_data2033 : data2033.Valid src2033 dst2033 Finset.univ := by decide +kernel

def src2034 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,16,27,38,26,8,18,28,38]
def dst2034 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,16,27,38,26,6,18,28,38,8]
def cycle2034_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2034_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2034_2 : CycleData E W := ⟨3,![2,23,18,19,3],![3,8,38,26,6]⟩
def cycle2034_3 : CycleData E W := ⟨2,![4,15,8,9],![2,6,16,18]⟩
def cycle2034_4 : CycleData E W := ⟨2,![6,12,16,7],![3,14,27,16]⟩
def cycle2034_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2034 : PartitionData E W := ⟨6,![cycle2034_0,cycle2034_1,cycle2034_2,cycle2034_3,cycle2034_4,cycle2034_5]⟩
lemma valid_data2034 : data2034.Valid src2034 dst2034 Finset.univ := by decide +kernel

def src2035 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,16,27,38,26,8,18,38,28]
def dst2035 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,16,27,38,26,6,18,38,28,8]
def cycle2035_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2035_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2035_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2035_3 : CycleData E W := ⟨3,![3,15,16,12,6],![3,6,16,27,14]⟩
def cycle2035_4 : CycleData E W := ⟨3,![4,19,18,21,9],![2,6,26,38,18]⟩
def cycle2035_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2035 : PartitionData E W := ⟨6,![cycle2035_0,cycle2035_1,cycle2035_2,cycle2035_3,cycle2035_4,cycle2035_5]⟩
lemma valid_data2035 : data2035.Valid src2035 dst2035 Finset.univ := by decide +kernel

def src2036 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,16,27,38,26,8,28,18,38]
def dst2036 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,16,27,38,26,6,28,18,38,8]
def cycle2036_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2036_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2036_2 : CycleData E W := ⟨3,![2,23,17,12,6],![3,8,38,27,14]⟩
def cycle2036_3 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2036_4 : CycleData E W := ⟨3,![4,19,18,22,9],![2,6,26,38,18]⟩
def cycle2036_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data2036 : PartitionData E W := ⟨6,![cycle2036_0,cycle2036_1,cycle2036_2,cycle2036_3,cycle2036_4,cycle2036_5]⟩
lemma valid_data2036 : data2036.Valid src2036 dst2036 Finset.univ := by decide +kernel

def src2037 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,16,38,26,27,8,18,28,38]
def dst2037 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,16,38,26,27,6,18,28,38,8]
def cycle2037_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2037_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2037_2 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle2037_3 : CycleData E W := ⟨2,![20,8,16,23],![8,18,16,38]⟩
def cycle2037_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle2037_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data2037 : PartitionData E W := ⟨6,![cycle2037_0,cycle2037_1,cycle2037_2,cycle2037_3,cycle2037_4,cycle2037_5]⟩
lemma valid_data2037 : data2037.Valid src2037 dst2037 Finset.univ := by decide +kernel

def src2038 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,16,38,26,27,8,18,38,28]
def dst2038 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,16,38,26,27,6,18,38,28,8]
def cycle2038_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2038_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2038_2 : CycleData E W := ⟨4,![4,19,13,23,20,9],![2,6,27,28,8,18]⟩
def cycle2038_3 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2038_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle2038_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data2038 : PartitionData E W := ⟨6,![cycle2038_0,cycle2038_1,cycle2038_2,cycle2038_3,cycle2038_4,cycle2038_5]⟩
lemma valid_data2038 : data2038.Valid src2038 dst2038 Finset.univ := by decide +kernel

def src2039 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,16,38,26,27,8,28,18,38]
def dst2039 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,16,38,26,27,6,28,18,38,8]
def cycle2039_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2039_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2039_2 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle2039_3 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle2039_4 : CycleData E W := ⟨3,![10,17,23,20,14],![4,26,38,8,28]⟩
def cycle2039_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data2039 : PartitionData E W := ⟨6,![cycle2039_0,cycle2039_1,cycle2039_2,cycle2039_3,cycle2039_4,cycle2039_5]⟩
lemma valid_data2039 : data2039.Valid src2039 dst2039 Finset.univ := by decide +kernel

def src2040 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst2040 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle2040_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2040_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2040_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2040_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2040_4 : CycleData E W := ⟨3,![4,15,16,8,9],![2,6,26,16,18]⟩
def cycle2040_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2040 : PartitionData E W := ⟨6,![cycle2040_0,cycle2040_1,cycle2040_2,cycle2040_3,cycle2040_4,cycle2040_5]⟩
lemma valid_data2040 : data2040.Valid src2040 dst2040 Finset.univ := by decide +kernel

def src2041 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst2041 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle2041_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2041_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2041_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2041_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2041_4 : CycleData E W := ⟨4,![4,15,16,17,21,9],![2,6,26,16,38,18]⟩
def cycle2041_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2041 : PartitionData E W := ⟨6,![cycle2041_0,cycle2041_1,cycle2041_2,cycle2041_3,cycle2041_4,cycle2041_5]⟩
lemma valid_data2041 : data2041.Valid src2041 dst2041 Finset.univ := by decide +kernel

def src2042 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst2042 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle2042_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2042_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2042_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2042_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2042_4 : CycleData E W := ⟨3,![4,15,16,8,9],![2,6,26,16,18]⟩
def cycle2042_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2042 : PartitionData E W := ⟨6,![cycle2042_0,cycle2042_1,cycle2042_2,cycle2042_3,cycle2042_4,cycle2042_5]⟩
lemma valid_data2042 : data2042.Valid src2042 dst2042 Finset.univ := by decide +kernel

def src2043 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst2043 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2043_0 : CycleData E W := ⟨2,![0,1,20,9],![2,4,8,18]⟩
def cycle2043_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2043_2 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,14]⟩
def cycle2043_3 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def cycle2043_4 : CycleData E W := ⟨2,![10,16,22,14],![4,26,38,28]⟩
def cycle2043_5 : CycleData E W := ⟨2,![15,11,12,19],![6,26,14,27]⟩
def data2043 : PartitionData E W := ⟨6,![cycle2043_0,cycle2043_1,cycle2043_2,cycle2043_3,cycle2043_4,cycle2043_5]⟩
lemma valid_data2043 : data2043.Valid src2043 dst2043 Finset.univ := by decide +kernel

def src2044 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,26,38,16,27,8,18,38,28]
def dst2044 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2044_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2044_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2044_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2044_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2044_4 : CycleData E W := ⟨3,![4,15,16,21,9],![2,6,26,38,18]⟩
def cycle2044_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data2044 : PartitionData E W := ⟨6,![cycle2044_0,cycle2044_1,cycle2044_2,cycle2044_3,cycle2044_4,cycle2044_5]⟩
lemma valid_data2044 : data2044.Valid src2044 dst2044 Finset.univ := by decide +kernel

def src2045 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,26,38,16,27,8,28,18,38]
def dst2045 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2045_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2045_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2045_2 : CycleData E W := ⟨3,![2,23,16,15,3],![3,8,38,26,6]⟩
def cycle2045_3 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle2045_4 : CycleData E W := ⟨2,![6,12,18,7],![3,14,27,16]⟩
def cycle2045_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2045 : PartitionData E W := ⟨6,![cycle2045_0,cycle2045_1,cycle2045_2,cycle2045_3,cycle2045_4,cycle2045_5]⟩
lemma valid_data2045 : data2045.Valid src2045 dst2045 Finset.univ := by decide +kernel

def src2046 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,27,16,26,38,8,18,28,38]
def dst2046 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2046_0 : CycleData E W := ⟨2,![0,1,20,9],![2,4,8,18]⟩
def cycle2046_1 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2046_2 : CycleData E W := ⟨2,![4,15,12,5],![2,6,27,14]⟩
def cycle2046_3 : CycleData E W := ⟨2,![6,11,17,7],![3,14,26,16]⟩
def cycle2046_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2046_5 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def data2046 : PartitionData E W := ⟨6,![cycle2046_0,cycle2046_1,cycle2046_2,cycle2046_3,cycle2046_4,cycle2046_5]⟩
lemma valid_data2046 : data2046.Valid src2046 dst2046 Finset.univ := by decide +kernel

def src2047 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,27,16,26,38,8,18,38,28]
def dst2047 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2047_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2047_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2047_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2047_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,27,14]⟩
def cycle2047_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2047_5 : CycleData E W := ⟨3,![16,13,22,18,17],![16,27,28,38,26]⟩
def data2047 : PartitionData E W := ⟨6,![cycle2047_0,cycle2047_1,cycle2047_2,cycle2047_3,cycle2047_4,cycle2047_5]⟩
lemma valid_data2047 : data2047.Valid src2047 dst2047 Finset.univ := by decide +kernel

def src2048 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,27,16,26,38,8,28,18,38]
def dst2048 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2048_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2048_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2048_2 : CycleData E W := ⟨3,![2,23,18,17,7],![3,8,38,26,16]⟩
def cycle2048_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,27,14]⟩
def cycle2048_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2048_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data2048 : PartitionData E W := ⟨6,![cycle2048_0,cycle2048_1,cycle2048_2,cycle2048_3,cycle2048_4,cycle2048_5]⟩
lemma valid_data2048 : data2048.Valid src2048 dst2048 Finset.univ := by decide +kernel

def src2049 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,27,26,16,38,8,18,28,38]
def dst2049 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,27,26,16,38,6,18,28,38,8]
def cycle2049_0 : CycleData E W := ⟨3,![0,10,17,8,9],![2,4,26,16,18]⟩
def cycle2049_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2049_2 : CycleData E W := ⟨2,![2,23,18,7],![3,8,38,16]⟩
def cycle2049_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,14]⟩
def cycle2049_4 : CycleData E W := ⟨1,![11,16,12],![14,26,27]⟩
def cycle2049_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2049 : PartitionData E W := ⟨6,![cycle2049_0,cycle2049_1,cycle2049_2,cycle2049_3,cycle2049_4,cycle2049_5]⟩
lemma valid_data2049 : data2049.Valid src2049 dst2049 Finset.univ := by decide +kernel

def src2050 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,27,26,16,38,8,18,38,28]
def dst2050 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,27,26,16,38,6,18,38,28,8]
def cycle2050_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2050_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2050_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2050_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,27,14]⟩
def cycle2050_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2050_5 : CycleData E W := ⟨3,![17,16,13,22,18],![16,26,27,28,38]⟩
def data2050 : PartitionData E W := ⟨6,![cycle2050_0,cycle2050_1,cycle2050_2,cycle2050_3,cycle2050_4,cycle2050_5]⟩
lemma valid_data2050 : data2050.Valid src2050 dst2050 Finset.univ := by decide +kernel

def src2051 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,27,28,6,27,26,16,38,8,28,18,38]
def dst2051 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,27,28,4,27,26,16,38,6,28,18,38,8]
def cycle2051_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2051_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2051_2 : CycleData E W := ⟨2,![2,23,18,7],![3,8,38,16]⟩
def cycle2051_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,27,14]⟩
def cycle2051_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2051_5 : CycleData E W := ⟨3,![8,21,13,16,17],![16,18,28,27,26]⟩
def data2051 : PartitionData E W := ⟨6,![cycle2051_0,cycle2051_1,cycle2051_2,cycle2051_3,cycle2051_4,cycle2051_5]⟩
lemma valid_data2051 : data2051.Valid src2051 dst2051 Finset.univ := by decide +kernel

def src2052 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,16,26,38,27,8,18,28,38]
def dst2052 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,16,26,38,27,6,18,28,38,8]
def cycle2052_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle2052_1 : CycleData E W := ⟨3,![2,1,10,11,6],![3,8,4,26,14]⟩
def cycle2052_2 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2052_3 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle2052_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,26,38]⟩
def cycle2052_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2052 : PartitionData E W := ⟨6,![cycle2052_0,cycle2052_1,cycle2052_2,cycle2052_3,cycle2052_4,cycle2052_5]⟩
lemma valid_data2052 : data2052.Valid src2052 dst2052 Finset.univ := by decide +kernel

def src2053 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,16,26,38,27,8,18,38,28]
def dst2053 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,16,26,38,27,6,18,38,28,8]
def cycle2053_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2053_1 : CycleData E W := ⟨4,![4,19,14,1,20,9],![2,6,27,4,8,18]⟩
def cycle2053_2 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle2053_3 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2053_4 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,26]⟩
def cycle2053_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2053 : PartitionData E W := ⟨6,![cycle2053_0,cycle2053_1,cycle2053_2,cycle2053_3,cycle2053_4,cycle2053_5]⟩
lemma valid_data2053 : data2053.Valid src2053 dst2053 Finset.univ := by decide +kernel

def src2054 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,16,26,38,27,8,28,18,38]
def dst2054 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,16,26,38,27,6,28,18,38,8]
def cycle2054_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2054_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2054_2 : CycleData E W := ⟨2,![2,20,12,6],![3,8,28,14]⟩
def cycle2054_3 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2054_4 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle2054_5 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,26]⟩
def data2054 : PartitionData E W := ⟨6,![cycle2054_0,cycle2054_1,cycle2054_2,cycle2054_3,cycle2054_4,cycle2054_5]⟩
lemma valid_data2054 : data2054.Valid src2054 dst2054 Finset.univ := by decide +kernel

def src2055 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,16,27,26,38,8,18,28,38]
def dst2055 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,16,27,26,38,6,18,28,38,8]
def cycle2055_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2055_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2055_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2055_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2055_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2055_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data2055 : PartitionData E W := ⟨6,![cycle2055_0,cycle2055_1,cycle2055_2,cycle2055_3,cycle2055_4,cycle2055_5]⟩
lemma valid_data2055 : data2055.Valid src2055 dst2055 Finset.univ := by decide +kernel

def src2056 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,16,27,26,38,8,18,38,28]
def dst2056 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,16,27,26,38,6,18,38,28,8]
def cycle2056_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2056_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2056_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2056_3 : CycleData E W := ⟨3,![20,8,16,13,23],![8,18,16,27,28]⟩
def cycle2056_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2056_5 : CycleData E W := ⟨2,![11,18,22,12],![14,26,38,28]⟩
def data2056 : PartitionData E W := ⟨6,![cycle2056_0,cycle2056_1,cycle2056_2,cycle2056_3,cycle2056_4,cycle2056_5]⟩
lemma valid_data2056 : data2056.Valid src2056 dst2056 Finset.univ := by decide +kernel

def src2057 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,16,27,26,38,8,28,18,38]
def dst2057 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,16,27,26,38,6,28,18,38,8]
def cycle2057_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2057_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2057_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2057_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2057_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2057_5 : CycleData E W := ⟨3,![20,12,11,18,23],![8,28,14,26,38]⟩
def data2057 : PartitionData E W := ⟨6,![cycle2057_0,cycle2057_1,cycle2057_2,cycle2057_3,cycle2057_4,cycle2057_5]⟩
lemma valid_data2057 : data2057.Valid src2057 dst2057 Finset.univ := by decide +kernel

def src2058 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,16,27,38,26,8,18,28,38]
def dst2058 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,16,27,38,26,6,18,28,38,8]
def cycle2058_0 : CycleData E W := ⟨3,![0,14,16,8,9],![2,4,27,16,18]⟩
def cycle2058_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2058_2 : CycleData E W := ⟨3,![2,20,21,12,6],![3,8,18,28,14]⟩
def cycle2058_3 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2058_4 : CycleData E W := ⟨2,![4,19,11,5],![2,6,26,14]⟩
def cycle2058_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2058 : PartitionData E W := ⟨6,![cycle2058_0,cycle2058_1,cycle2058_2,cycle2058_3,cycle2058_4,cycle2058_5]⟩
lemma valid_data2058 : data2058.Valid src2058 dst2058 Finset.univ := by decide +kernel

def src2059 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,16,27,38,26,8,18,38,28]
def dst2059 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,16,27,38,26,6,18,38,28,8]
def cycle2059_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2059_1 : CycleData E W := ⟨3,![1,20,8,16,14],![4,8,18,16,27]⟩
def cycle2059_2 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle2059_3 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2059_4 : CycleData E W := ⟨3,![4,19,18,21,9],![2,6,26,38,18]⟩
def cycle2059_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2059 : PartitionData E W := ⟨6,![cycle2059_0,cycle2059_1,cycle2059_2,cycle2059_3,cycle2059_4,cycle2059_5]⟩
lemma valid_data2059 : data2059.Valid src2059 dst2059 Finset.univ := by decide +kernel

def src2060 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,16,27,38,26,8,28,18,38]
def dst2060 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,16,27,38,26,6,28,18,38,8]
def cycle2060_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2060_1 : CycleData E W := ⟨2,![1,23,17,14],![4,8,38,27]⟩
def cycle2060_2 : CycleData E W := ⟨2,![2,20,12,6],![3,8,28,14]⟩
def cycle2060_3 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2060_4 : CycleData E W := ⟨3,![4,19,18,22,9],![2,6,26,38,18]⟩
def cycle2060_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data2060 : PartitionData E W := ⟨6,![cycle2060_0,cycle2060_1,cycle2060_2,cycle2060_3,cycle2060_4,cycle2060_5]⟩
lemma valid_data2060 : data2060.Valid src2060 dst2060 Finset.univ := by decide +kernel

def src2061 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,16,38,26,27,8,18,28,38]
def dst2061 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,16,38,26,27,6,18,28,38,8]
def cycle2061_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2061_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2061_2 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle2061_3 : CycleData E W := ⟨2,![20,8,16,23],![8,18,16,38]⟩
def cycle2061_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2061_5 : CycleData E W := ⟨2,![11,17,22,12],![14,26,38,28]⟩
def data2061 : PartitionData E W := ⟨6,![cycle2061_0,cycle2061_1,cycle2061_2,cycle2061_3,cycle2061_4,cycle2061_5]⟩
lemma valid_data2061 : data2061.Valid src2061 dst2061 Finset.univ := by decide +kernel

def src2062 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,16,38,26,27,8,18,38,28]
def dst2062 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,16,38,26,27,6,18,38,28,8]
def cycle2062_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2062_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2062_2 : CycleData E W := ⟨4,![4,19,13,23,20,9],![2,6,27,28,8,18]⟩
def cycle2062_3 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2062_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2062_5 : CycleData E W := ⟨2,![11,17,22,12],![14,26,38,28]⟩
def data2062 : PartitionData E W := ⟨6,![cycle2062_0,cycle2062_1,cycle2062_2,cycle2062_3,cycle2062_4,cycle2062_5]⟩
lemma valid_data2062 : data2062.Valid src2062 dst2062 Finset.univ := by decide +kernel

def src2063 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,16,38,26,27,8,28,18,38]
def dst2063 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,16,38,26,27,6,28,18,38,8]
def cycle2063_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2063_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2063_2 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,27,28,18]⟩
def cycle2063_3 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle2063_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2063_5 : CycleData E W := ⟨3,![20,12,11,17,23],![8,28,14,26,38]⟩
def data2063 : PartitionData E W := ⟨6,![cycle2063_0,cycle2063_1,cycle2063_2,cycle2063_3,cycle2063_4,cycle2063_5]⟩
lemma valid_data2063 : data2063.Valid src2063 dst2063 Finset.univ := by decide +kernel

def src2064 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,26,16,27,38,8,18,28,38]
def dst2064 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2064_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2064_1 : CycleData E W := ⟨3,![1,20,8,17,14],![4,8,18,16,27]⟩
def cycle2064_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2064_3 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle2064_4 : CycleData E W := ⟨2,![6,11,16,7],![3,14,26,16]⟩
def cycle2064_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2064 : PartitionData E W := ⟨6,![cycle2064_0,cycle2064_1,cycle2064_2,cycle2064_3,cycle2064_4,cycle2064_5]⟩
lemma valid_data2064 : data2064.Valid src2064 dst2064 Finset.univ := by decide +kernel

def src2065 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,26,16,27,38,8,18,38,28]
def dst2065 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2065_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2065_1 : CycleData E W := ⟨3,![1,20,8,17,14],![4,8,18,16,27]⟩
def cycle2065_2 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle2065_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,26,16]⟩
def cycle2065_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2065_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2065 : PartitionData E W := ⟨6,![cycle2065_0,cycle2065_1,cycle2065_2,cycle2065_3,cycle2065_4,cycle2065_5]⟩
lemma valid_data2065 : data2065.Valid src2065 dst2065 Finset.univ := by decide +kernel

def src2066 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,26,16,27,38,8,28,18,38]
def dst2066 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2066_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2066_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2066_2 : CycleData E W := ⟨2,![2,20,12,6],![3,8,28,14]⟩
def cycle2066_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,26,16]⟩
def cycle2066_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2066_5 : CycleData E W := ⟨2,![8,21,13,17],![16,18,28,27]⟩
def data2066 : PartitionData E W := ⟨6,![cycle2066_0,cycle2066_1,cycle2066_2,cycle2066_3,cycle2066_4,cycle2066_5]⟩
lemma valid_data2066 : data2066.Valid src2066 dst2066 Finset.univ := by decide +kernel

def src2067 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,26,27,16,38,8,18,28,38]
def dst2067 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,26,27,16,38,6,18,28,38,8]
def cycle2067_0 : CycleData E W := ⟨2,![0,1,20,9],![2,4,8,18]⟩
def cycle2067_1 : CycleData E W := ⟨2,![2,23,18,7],![3,8,38,16]⟩
def cycle2067_2 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,14]⟩
def cycle2067_3 : CycleData E W := ⟨2,![8,21,13,17],![16,18,28,27]⟩
def cycle2067_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle2067_5 : CycleData E W := ⟨3,![15,11,12,22,19],![6,26,14,28,38]⟩
def data2067 : PartitionData E W := ⟨6,![cycle2067_0,cycle2067_1,cycle2067_2,cycle2067_3,cycle2067_4,cycle2067_5]⟩
lemma valid_data2067 : data2067.Valid src2067 dst2067 Finset.univ := by decide +kernel

def src2068 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,26,27,16,38,8,18,38,28]
def dst2068 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,26,27,16,38,6,18,38,28,8]
def cycle2068_0 : CycleData E W := ⟨2,![0,1,20,9],![2,4,8,18]⟩
def cycle2068_1 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle2068_2 : CycleData E W := ⟨2,![3,19,18,7],![3,6,38,16]⟩
def cycle2068_3 : CycleData E W := ⟨2,![4,15,11,5],![2,6,26,14]⟩
def cycle2068_4 : CycleData E W := ⟨3,![8,21,22,13,17],![16,18,38,28,27]⟩
def cycle2068_5 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def data2068 : PartitionData E W := ⟨6,![cycle2068_0,cycle2068_1,cycle2068_2,cycle2068_3,cycle2068_4,cycle2068_5]⟩
lemma valid_data2068 : data2068.Valid src2068 dst2068 Finset.univ := by decide +kernel

def src2069 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,26,27,16,38,8,28,18,38]
def dst2069 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,26,27,16,38,6,28,18,38,8]
def cycle2069_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2069_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2069_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2069_3 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle2069_4 : CycleData E W := ⟨3,![6,11,16,17,7],![3,14,26,27,16]⟩
def cycle2069_5 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def data2069 : PartitionData E W := ⟨6,![cycle2069_0,cycle2069_1,cycle2069_2,cycle2069_3,cycle2069_4,cycle2069_5]⟩
lemma valid_data2069 : data2069.Valid src2069 dst2069 Finset.univ := by decide +kernel

def src2070 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,26,38,16,27,8,18,28,38]
def dst2070 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2070_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle2070_1 : CycleData E W := ⟨2,![1,23,16,10],![4,8,38,26]⟩
def cycle2070_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2070_3 : CycleData E W := ⟨2,![3,15,11,6],![3,6,26,14]⟩
def cycle2070_4 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle2070_5 : CycleData E W := ⟨2,![17,22,13,18],![16,38,28,27]⟩
def data2070 : PartitionData E W := ⟨6,![cycle2070_0,cycle2070_1,cycle2070_2,cycle2070_3,cycle2070_4,cycle2070_5]⟩
lemma valid_data2070 : data2070.Valid src2070 dst2070 Finset.univ := by decide +kernel

def src2071 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,26,38,16,27,8,18,38,28]
def dst2071 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2071_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2071_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,27]⟩
def cycle2071_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,14,3,8,18]⟩
def cycle2071_3 : CycleData E W := ⟨2,![3,19,18,7],![3,6,27,16]⟩
def cycle2071_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2071_5 : CycleData E W := ⟨2,![11,16,22,12],![14,26,38,28]⟩
def data2071 : PartitionData E W := ⟨6,![cycle2071_0,cycle2071_1,cycle2071_2,cycle2071_3,cycle2071_4,cycle2071_5]⟩
lemma valid_data2071 : data2071.Valid src2071 dst2071 Finset.univ := by decide +kernel

def src2072 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,26,38,16,27,8,28,18,38]
def dst2072 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2072_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2072_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2072_2 : CycleData E W := ⟨3,![2,23,16,11,6],![3,8,38,26,14]⟩
def cycle2072_3 : CycleData E W := ⟨2,![3,19,18,7],![3,6,27,16]⟩
def cycle2072_4 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle2072_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2072 : PartitionData E W := ⟨6,![cycle2072_0,cycle2072_1,cycle2072_2,cycle2072_3,cycle2072_4,cycle2072_5]⟩
lemma valid_data2072 : data2072.Valid src2072 dst2072 Finset.univ := by decide +kernel

def src2073 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,27,16,26,38,8,18,28,38]
def dst2073 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2073_0 : CycleData E W := ⟨10,![4,19,18,10,1,20,21,13,16,7,6,5],![2,6,38,26,4,8,18,28,27,16,3,14]⟩
def cycle2073_1 : CycleData E W := ⟨10,![0,14,15,3,2,23,22,12,11,17,8,9],![2,4,27,6,3,8,38,28,14,26,16,18]⟩
def data2073 : PartitionData E W := ⟨2,![cycle2073_0,cycle2073_1]⟩
lemma valid_data2073 : data2073.Valid src2073 dst2073 Finset.univ := by decide +kernel

def src2074 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,27,16,26,38,8,18,38,28]
def dst2074 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2074_0 : CycleData E W := ⟨10,![0,1,20,21,18,11,12,13,16,7,3,4],![2,4,8,18,38,26,14,28,27,16,3,6]⟩
def cycle2074_1 : CycleData E W := ⟨10,![5,6,2,23,22,19,15,14,10,17,8,9],![2,14,3,8,28,38,6,27,4,26,16,18]⟩
def data2074 : PartitionData E W := ⟨2,![cycle2074_0,cycle2074_1]⟩
lemma valid_data2074 : data2074.Valid src2074 dst2074 Finset.univ := by decide +kernel

def src2075 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,14,28,27,6,27,16,26,38,8,28,18,38]
def dst2075 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,14,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2075_0 : CycleData E W := ⟨10,![0,14,16,8,21,20,2,3,19,18,11,5],![2,4,27,16,18,28,8,3,6,38,26,14]⟩
def cycle2075_1 : CycleData E W := ⟨10,![4,15,13,12,6,7,17,10,1,23,22,9],![2,6,27,28,14,3,16,26,4,8,38,18]⟩
def data2075 : PartitionData E W := ⟨2,![cycle2075_0,cycle2075_1]⟩
lemma valid_data2075 : data2075.Valid src2075 dst2075 Finset.univ := by decide +kernel

def src2076 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,27,14,28,6,26,16,38,27,8,18,28,38]
def dst2076 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,27,14,28,4,26,16,38,27,6,18,28,38,8]
def cycle2076_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2076_1 : CycleData E W := ⟨2,![1,23,22,14],![4,8,38,28]⟩
def cycle2076_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2076_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2076_4 : CycleData E W := ⟨2,![5,13,21,9],![2,14,28,18]⟩
def cycle2076_5 : CycleData E W := ⟨2,![16,11,18,17],![16,26,27,38]⟩
def data2076 : PartitionData E W := ⟨6,![cycle2076_0,cycle2076_1,cycle2076_2,cycle2076_3,cycle2076_4,cycle2076_5]⟩
lemma valid_data2076 : data2076.Valid src2076 dst2076 Finset.univ := by decide +kernel

def src2077 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,27,14,28,6,26,16,38,27,8,18,38,28]
def dst2077 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,27,14,28,4,26,16,38,27,6,18,38,28,8]
def cycle2077_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2077_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2077_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2077_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2077_4 : CycleData E W := ⟨3,![5,13,22,21,9],![2,14,28,38,18]⟩
def cycle2077_5 : CycleData E W := ⟨2,![16,11,18,17],![16,26,27,38]⟩
def data2077 : PartitionData E W := ⟨6,![cycle2077_0,cycle2077_1,cycle2077_2,cycle2077_3,cycle2077_4,cycle2077_5]⟩
lemma valid_data2077 : data2077.Valid src2077 dst2077 Finset.univ := by decide +kernel

def src2078 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,27,14,28,6,26,16,38,27,8,28,18,38]
def dst2078 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,27,14,28,4,26,16,38,27,6,28,18,38,8]
def cycle2078_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2078_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2078_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2078_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2078_4 : CycleData E W := ⟨2,![5,13,21,9],![2,14,28,18]⟩
def cycle2078_5 : CycleData E W := ⟨3,![8,22,18,11,16],![16,18,38,27,26]⟩
def data2078 : PartitionData E W := ⟨6,![cycle2078_0,cycle2078_1,cycle2078_2,cycle2078_3,cycle2078_4,cycle2078_5]⟩
lemma valid_data2078 : data2078.Valid src2078 dst2078 Finset.univ := by decide +kernel

def src2079 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,27,14,28,6,27,16,26,38,8,18,28,38]
def dst2079 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,27,14,28,4,27,16,26,38,6,18,28,38,8]
def cycle2079_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,28,14]⟩
def cycle2079_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2079_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2079_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,27,14]⟩
def cycle2079_4 : CycleData E W := ⟨3,![4,19,22,21,9],![2,6,38,28,18]⟩
def cycle2079_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data2079 : PartitionData E W := ⟨6,![cycle2079_0,cycle2079_1,cycle2079_2,cycle2079_3,cycle2079_4,cycle2079_5]⟩
lemma valid_data2079 : data2079.Valid src2079 dst2079 Finset.univ := by decide +kernel

def src2080 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,27,14,28,6,27,16,26,38,8,18,38,28]
def dst2080 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,27,14,28,4,27,16,26,38,6,18,38,28,8]
def cycle2080_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,28,14]⟩
def cycle2080_1 : CycleData E W := ⟨3,![1,23,22,18,10],![4,8,28,38,26]⟩
def cycle2080_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2080_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,27,14]⟩
def cycle2080_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2080_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data2080 : PartitionData E W := ⟨6,![cycle2080_0,cycle2080_1,cycle2080_2,cycle2080_3,cycle2080_4,cycle2080_5]⟩
lemma valid_data2080 : data2080.Valid src2080 dst2080 Finset.univ := by decide +kernel

def src2081 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,27,14,28,6,27,16,26,38,8,28,18,38]
def dst2081 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,27,14,28,4,27,16,26,38,6,28,18,38,8]
def cycle2081_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,28,14]⟩
def cycle2081_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2081_2 : CycleData E W := ⟨3,![2,20,21,8,7],![3,8,28,18,16]⟩
def cycle2081_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,27,14]⟩
def cycle2081_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2081_5 : CycleData E W := ⟨1,![16,11,17],![16,27,26]⟩
def data2081 : PartitionData E W := ⟨6,![cycle2081_0,cycle2081_1,cycle2081_2,cycle2081_3,cycle2081_4,cycle2081_5]⟩
lemma valid_data2081 : data2081.Valid src2081 dst2081 Finset.univ := by decide +kernel

def src2082 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,16,26,27,38,8,18,28,38]
def dst2082 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,16,26,27,38,6,18,28,38,8]
def cycle2082_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2082_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2082_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2082_3 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def cycle2082_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2082_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data2082 : PartitionData E W := ⟨6,![cycle2082_0,cycle2082_1,cycle2082_2,cycle2082_3,cycle2082_4,cycle2082_5]⟩
lemma valid_data2082 : data2082.Valid src2082 dst2082 Finset.univ := by decide +kernel

def src2083 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,16,26,27,38,8,18,38,28]
def dst2083 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,16,26,27,38,6,18,38,28,8]
def cycle2083_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2083_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2083_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2083_3 : CycleData E W := ⟨3,![20,8,16,11,23],![8,18,16,26,28]⟩
def cycle2083_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2083_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data2083 : PartitionData E W := ⟨6,![cycle2083_0,cycle2083_1,cycle2083_2,cycle2083_3,cycle2083_4,cycle2083_5]⟩
lemma valid_data2083 : data2083.Valid src2083 dst2083 Finset.univ := by decide +kernel

def src2084 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,16,26,27,38,8,28,18,38]
def dst2084 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,16,26,27,38,6,28,18,38,8]
def cycle2084_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2084_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2084_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2084_3 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def cycle2084_4 : CycleData E W := ⟨1,![10,17,14],![4,26,27]⟩
def cycle2084_5 : CycleData E W := ⟨3,![20,12,13,18,23],![8,28,14,27,38]⟩
def data2084 : PartitionData E W := ⟨6,![cycle2084_0,cycle2084_1,cycle2084_2,cycle2084_3,cycle2084_4,cycle2084_5]⟩
lemma valid_data2084 : data2084.Valid src2084 dst2084 Finset.univ := by decide +kernel

def src2085 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,16,26,38,27,8,18,28,38]
def dst2085 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,16,26,38,27,6,18,28,38,8]
def cycle2085_0 : CycleData E W := ⟨3,![0,10,16,8,9],![2,4,26,16,18]⟩
def cycle2085_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2085_2 : CycleData E W := ⟨3,![2,20,21,12,6],![3,8,18,28,14]⟩
def cycle2085_3 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2085_4 : CycleData E W := ⟨2,![4,19,13,5],![2,6,27,14]⟩
def cycle2085_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data2085 : PartitionData E W := ⟨6,![cycle2085_0,cycle2085_1,cycle2085_2,cycle2085_3,cycle2085_4,cycle2085_5]⟩
lemma valid_data2085 : data2085.Valid src2085 dst2085 Finset.univ := by decide +kernel

def src2086 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,16,26,38,27,8,18,38,28]
def dst2086 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,16,26,38,27,6,18,38,28,8]
def cycle2086_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2086_1 : CycleData E W := ⟨3,![1,20,8,16,10],![4,8,18,16,26]⟩
def cycle2086_2 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle2086_3 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2086_4 : CycleData E W := ⟨3,![4,19,18,21,9],![2,6,27,38,18]⟩
def cycle2086_5 : CycleData E W := ⟨1,![11,22,17],![26,28,38]⟩
def data2086 : PartitionData E W := ⟨6,![cycle2086_0,cycle2086_1,cycle2086_2,cycle2086_3,cycle2086_4,cycle2086_5]⟩
lemma valid_data2086 : data2086.Valid src2086 dst2086 Finset.univ := by decide +kernel

def src2087 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,16,26,38,27,8,28,18,38]
def dst2087 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,16,26,38,27,6,28,18,38,8]
def cycle2087_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2087_1 : CycleData E W := ⟨2,![1,23,17,10],![4,8,38,26]⟩
def cycle2087_2 : CycleData E W := ⟨2,![2,20,12,6],![3,8,28,14]⟩
def cycle2087_3 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2087_4 : CycleData E W := ⟨3,![4,19,18,22,9],![2,6,27,38,18]⟩
def cycle2087_5 : CycleData E W := ⟨2,![8,21,11,16],![16,18,28,26]⟩
def data2087 : PartitionData E W := ⟨6,![cycle2087_0,cycle2087_1,cycle2087_2,cycle2087_3,cycle2087_4,cycle2087_5]⟩
lemma valid_data2087 : data2087.Valid src2087 dst2087 Finset.univ := by decide +kernel

def src2088 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,16,27,38,26,8,18,28,38]
def dst2088 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,16,27,38,26,6,18,28,38,8]
def cycle2088_0 : CycleData E W := ⟨2,![0,10,19,4],![2,4,26,6]⟩
def cycle2088_1 : CycleData E W := ⟨3,![2,1,14,13,6],![3,8,4,27,14]⟩
def cycle2088_2 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2088_3 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle2088_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,27,38]⟩
def cycle2088_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2088 : PartitionData E W := ⟨6,![cycle2088_0,cycle2088_1,cycle2088_2,cycle2088_3,cycle2088_4,cycle2088_5]⟩
lemma valid_data2088 : data2088.Valid src2088 dst2088 Finset.univ := by decide +kernel

def src2089 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,16,27,38,26,8,18,38,28]
def dst2089 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,16,27,38,26,6,18,38,28,8]
def cycle2089_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2089_1 : CycleData E W := ⟨4,![4,19,10,1,20,9],![2,6,26,4,8,18]⟩
def cycle2089_2 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle2089_3 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2089_4 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,27]⟩
def cycle2089_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2089 : PartitionData E W := ⟨6,![cycle2089_0,cycle2089_1,cycle2089_2,cycle2089_3,cycle2089_4,cycle2089_5]⟩
lemma valid_data2089 : data2089.Valid src2089 dst2089 Finset.univ := by decide +kernel

def src2090 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,16,27,38,26,8,28,18,38]
def dst2090 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,16,27,38,26,6,28,18,38,8]
def cycle2090_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2090_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2090_2 : CycleData E W := ⟨2,![2,20,12,6],![3,8,28,14]⟩
def cycle2090_3 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2090_4 : CycleData E W := ⟨3,![4,19,11,21,9],![2,6,26,28,18]⟩
def cycle2090_5 : CycleData E W := ⟨2,![8,22,17,16],![16,18,38,27]⟩
def data2090 : PartitionData E W := ⟨6,![cycle2090_0,cycle2090_1,cycle2090_2,cycle2090_3,cycle2090_4,cycle2090_5]⟩
lemma valid_data2090 : data2090.Valid src2090 dst2090 Finset.univ := by decide +kernel

def src2091 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,16,38,27,26,8,18,28,38]
def dst2091 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,16,38,27,26,6,18,28,38,8]
def cycle2091_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2091_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2091_2 : CycleData E W := ⟨3,![4,19,11,21,9],![2,6,26,28,18]⟩
def cycle2091_3 : CycleData E W := ⟨2,![20,8,16,23],![8,18,16,38]⟩
def cycle2091_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2091_5 : CycleData E W := ⟨2,![12,22,17,13],![14,28,38,27]⟩
def data2091 : PartitionData E W := ⟨6,![cycle2091_0,cycle2091_1,cycle2091_2,cycle2091_3,cycle2091_4,cycle2091_5]⟩
lemma valid_data2091 : data2091.Valid src2091 dst2091 Finset.univ := by decide +kernel

def src2092 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,16,38,27,26,8,18,38,28]
def dst2092 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,16,38,27,26,6,18,38,28,8]
def cycle2092_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2092_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2092_2 : CycleData E W := ⟨4,![4,19,11,23,20,9],![2,6,26,28,8,18]⟩
def cycle2092_3 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2092_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2092_5 : CycleData E W := ⟨2,![12,22,17,13],![14,28,38,27]⟩
def data2092 : PartitionData E W := ⟨6,![cycle2092_0,cycle2092_1,cycle2092_2,cycle2092_3,cycle2092_4,cycle2092_5]⟩
lemma valid_data2092 : data2092.Valid src2092 dst2092 Finset.univ := by decide +kernel

def src2093 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,16,38,27,26,8,28,18,38]
def dst2093 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,16,38,27,26,6,28,18,38,8]
def cycle2093_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2093_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2093_2 : CycleData E W := ⟨3,![4,19,11,21,9],![2,6,26,28,18]⟩
def cycle2093_3 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle2093_4 : CycleData E W := ⟨1,![10,18,14],![4,26,27]⟩
def cycle2093_5 : CycleData E W := ⟨3,![20,12,13,17,23],![8,28,14,27,38]⟩
def data2093 : PartitionData E W := ⟨6,![cycle2093_0,cycle2093_1,cycle2093_2,cycle2093_3,cycle2093_4,cycle2093_5]⟩
lemma valid_data2093 : data2093.Valid src2093 dst2093 Finset.univ := by decide +kernel

def src2094 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,26,16,27,38,8,18,28,38]
def dst2094 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,26,16,27,38,6,18,28,38,8]
def cycle2094_0 : CycleData E W := ⟨10,![0,1,20,21,11,16,7,6,13,18,19,4],![2,4,8,18,28,26,16,3,14,27,38,6]⟩
def cycle2094_1 : CycleData E W := ⟨10,![5,12,22,23,2,3,15,10,14,17,8,9],![2,14,28,38,8,3,6,26,4,27,16,18]⟩
def data2094 : PartitionData E W := ⟨2,![cycle2094_0,cycle2094_1]⟩
lemma valid_data2094 : data2094.Valid src2094 dst2094 Finset.univ := by decide +kernel

def src2095 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,26,16,27,38,8,18,38,28]
def dst2095 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,26,16,27,38,6,18,38,28,8]
def cycle2095_0 : CycleData E W := ⟨10,![0,1,20,21,18,13,12,11,16,7,3,4],![2,4,8,18,38,27,14,28,26,16,3,6]⟩
def cycle2095_1 : CycleData E W := ⟨10,![5,6,2,23,22,19,15,10,14,17,8,9],![2,14,3,8,28,38,6,26,4,27,16,18]⟩
def data2095 : PartitionData E W := ⟨2,![cycle2095_0,cycle2095_1]⟩
lemma valid_data2095 : data2095.Valid src2095 dst2095 Finset.univ := by decide +kernel

def src2096 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,26,16,27,38,8,28,18,38]
def dst2096 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,26,16,27,38,6,28,18,38,8]
def cycle2096_0 : CycleData E W := ⟨10,![0,10,16,8,21,20,2,3,19,18,13,5],![2,4,26,16,18,28,8,3,6,38,27,14]⟩
def cycle2096_1 : CycleData E W := ⟨10,![4,15,11,12,6,7,17,14,1,23,22,9],![2,6,26,28,14,3,16,27,4,8,38,18]⟩
def data2096 : PartitionData E W := ⟨2,![cycle2096_0,cycle2096_1]⟩
lemma valid_data2096 : data2096.Valid src2096 dst2096 Finset.univ := by decide +kernel

def src2097 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,26,16,38,27,8,18,28,38]
def dst2097 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,26,16,38,27,6,18,28,38,8]
def cycle2097_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2097_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2097_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2097_3 : CycleData E W := ⟨2,![3,19,13,6],![3,6,27,14]⟩
def cycle2097_4 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle2097_5 : CycleData E W := ⟨2,![16,11,22,17],![16,26,28,38]⟩
def data2097 : PartitionData E W := ⟨6,![cycle2097_0,cycle2097_1,cycle2097_2,cycle2097_3,cycle2097_4,cycle2097_5]⟩
lemma valid_data2097 : data2097.Valid src2097 dst2097 Finset.univ := by decide +kernel

def src2098 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,26,16,38,27,8,18,38,28]
def dst2098 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,26,16,38,27,6,18,38,28,8]
def cycle2098_0 : CycleData E W := ⟨2,![0,14,19,4],![2,4,27,6]⟩
def cycle2098_1 : CycleData E W := ⟨2,![1,23,11,10],![4,8,28,26]⟩
def cycle2098_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,14,3,8,18]⟩
def cycle2098_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,26,16]⟩
def cycle2098_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2098_5 : CycleData E W := ⟨2,![12,22,18,13],![14,28,38,27]⟩
def data2098 : PartitionData E W := ⟨6,![cycle2098_0,cycle2098_1,cycle2098_2,cycle2098_3,cycle2098_4,cycle2098_5]⟩
lemma valid_data2098 : data2098.Valid src2098 dst2098 Finset.univ := by decide +kernel

def src2099 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,26,16,38,27,8,28,18,38]
def dst2099 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,26,16,38,27,6,28,18,38,8]
def cycle2099_0 : CycleData E W := ⟨2,![0,10,15,4],![2,4,26,6]⟩
def cycle2099_1 : CycleData E W := ⟨2,![1,23,18,14],![4,8,38,27]⟩
def cycle2099_2 : CycleData E W := ⟨3,![2,20,11,16,7],![3,8,28,26,16]⟩
def cycle2099_3 : CycleData E W := ⟨2,![3,19,13,6],![3,6,27,14]⟩
def cycle2099_4 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle2099_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2099 : PartitionData E W := ⟨6,![cycle2099_0,cycle2099_1,cycle2099_2,cycle2099_3,cycle2099_4,cycle2099_5]⟩
lemma valid_data2099 : data2099.Valid src2099 dst2099 Finset.univ := by decide +kernel

def src2100 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,27,16,26,38,8,18,28,38]
def dst2100 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,27,16,26,38,6,18,28,38,8]
def cycle2100_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,27,6]⟩
def cycle2100_1 : CycleData E W := ⟨3,![1,20,8,17,10],![4,8,18,16,26]⟩
def cycle2100_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2100_3 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle2100_4 : CycleData E W := ⟨2,![6,13,16,7],![3,14,27,16]⟩
def cycle2100_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2100 : PartitionData E W := ⟨6,![cycle2100_0,cycle2100_1,cycle2100_2,cycle2100_3,cycle2100_4,cycle2100_5]⟩
lemma valid_data2100 : data2100.Valid src2100 dst2100 Finset.univ := by decide +kernel

def src2101 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,27,16,26,38,8,18,38,28]
def dst2101 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,27,16,26,38,6,18,38,28,8]
def cycle2101_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2101_1 : CycleData E W := ⟨3,![1,20,8,17,10],![4,8,18,16,26]⟩
def cycle2101_2 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle2101_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,27,16]⟩
def cycle2101_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2101_5 : CycleData E W := ⟨1,![11,22,18],![26,28,38]⟩
def data2101 : PartitionData E W := ⟨6,![cycle2101_0,cycle2101_1,cycle2101_2,cycle2101_3,cycle2101_4,cycle2101_5]⟩
lemma valid_data2101 : data2101.Valid src2101 dst2101 Finset.univ := by decide +kernel

def src2102 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,27,16,26,38,8,28,18,38]
def dst2102 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,27,16,26,38,6,28,18,38,8]
def cycle2102_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,27,14]⟩
def cycle2102_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,26]⟩
def cycle2102_2 : CycleData E W := ⟨2,![2,20,12,6],![3,8,28,14]⟩
def cycle2102_3 : CycleData E W := ⟨2,![3,15,16,7],![3,6,27,16]⟩
def cycle2102_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2102_5 : CycleData E W := ⟨2,![8,21,11,17],![16,18,28,26]⟩
def data2102 : PartitionData E W := ⟨6,![cycle2102_0,cycle2102_1,cycle2102_2,cycle2102_3,cycle2102_4,cycle2102_5]⟩
lemma valid_data2102 : data2102.Valid src2102 dst2102 Finset.univ := by decide +kernel

def src2103 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,27,26,16,38,8,18,28,38]
def dst2103 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,27,26,16,38,6,18,28,38,8]
def cycle2103_0 : CycleData E W := ⟨2,![0,1,20,9],![2,4,8,18]⟩
def cycle2103_1 : CycleData E W := ⟨2,![2,23,18,7],![3,8,38,16]⟩
def cycle2103_2 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,14]⟩
def cycle2103_3 : CycleData E W := ⟨2,![8,21,11,17],![16,18,28,26]⟩
def cycle2103_4 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def cycle2103_5 : CycleData E W := ⟨3,![15,13,12,22,19],![6,27,14,28,38]⟩
def data2103 : PartitionData E W := ⟨6,![cycle2103_0,cycle2103_1,cycle2103_2,cycle2103_3,cycle2103_4,cycle2103_5]⟩
lemma valid_data2103 : data2103.Valid src2103 dst2103 Finset.univ := by decide +kernel

def src2104 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,27,26,16,38,8,18,38,28]
def dst2104 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,27,26,16,38,6,18,38,28,8]
def cycle2104_0 : CycleData E W := ⟨2,![0,1,20,9],![2,4,8,18]⟩
def cycle2104_1 : CycleData E W := ⟨2,![2,23,12,6],![3,8,28,14]⟩
def cycle2104_2 : CycleData E W := ⟨2,![3,19,18,7],![3,6,38,16]⟩
def cycle2104_3 : CycleData E W := ⟨2,![4,15,13,5],![2,6,27,14]⟩
def cycle2104_4 : CycleData E W := ⟨3,![8,21,22,11,17],![16,18,38,28,26]⟩
def cycle2104_5 : CycleData E W := ⟨1,![10,16,14],![4,26,27]⟩
def data2104 : PartitionData E W := ⟨6,![cycle2104_0,cycle2104_1,cycle2104_2,cycle2104_3,cycle2104_4,cycle2104_5]⟩
lemma valid_data2104 : data2104.Valid src2104 dst2104 Finset.univ := by decide +kernel

def src2105 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,26,28,14,27,6,27,26,16,38,8,28,18,38]
def dst2105 : E → W := ![4,8,3,6,2,14,3,16,18,2,26,28,14,27,4,27,26,16,38,6,28,18,38,8]
def cycle2105_0 : CycleData E W := ⟨2,![0,14,15,4],![2,4,27,6]⟩
def cycle2105_1 : CycleData E W := ⟨2,![1,20,11,10],![4,8,28,26]⟩
def cycle2105_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2105_3 : CycleData E W := ⟨2,![5,12,21,9],![2,14,28,18]⟩
def cycle2105_4 : CycleData E W := ⟨3,![6,13,16,17,7],![3,14,27,26,16]⟩
def cycle2105_5 : CycleData E W := ⟨1,![8,22,18],![16,18,38]⟩
def data2105 : PartitionData E W := ⟨6,![cycle2105_0,cycle2105_1,cycle2105_2,cycle2105_3,cycle2105_4,cycle2105_5]⟩
lemma valid_data2105 : data2105.Valid src2105 dst2105 Finset.univ := by decide +kernel

def src2106 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,16,26,27,38,8,18,28,38]
def dst2106 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,16,26,27,38,6,18,28,38,8]
def cycle2106_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2106_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2106_2 : CycleData E W := ⟨3,![4,19,23,20,9],![2,6,38,8,18]⟩
def cycle2106_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2106_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle2106_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data2106 : PartitionData E W := ⟨6,![cycle2106_0,cycle2106_1,cycle2106_2,cycle2106_3,cycle2106_4,cycle2106_5]⟩
lemma valid_data2106 : data2106.Valid src2106 dst2106 Finset.univ := by decide +kernel

def src2107 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,16,26,27,38,8,18,38,28]
def dst2107 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,16,26,27,38,6,18,38,28,8]
def cycle2107_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2107_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2107_2 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2107_3 : CycleData E W := ⟨3,![20,8,16,13,23],![8,18,16,26,28]⟩
def cycle2107_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle2107_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data2107 : PartitionData E W := ⟨6,![cycle2107_0,cycle2107_1,cycle2107_2,cycle2107_3,cycle2107_4,cycle2107_5]⟩
lemma valid_data2107 : data2107.Valid src2107 dst2107 Finset.univ := by decide +kernel

def src2108 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,16,26,27,38,8,28,18,38]
def dst2108 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,16,26,27,38,6,28,18,38,8]
def cycle2108_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2108_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2108_2 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2108_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2108_4 : CycleData E W := ⟨3,![10,18,23,20,14],![4,27,38,8,28]⟩
def cycle2108_5 : CycleData E W := ⟨1,![11,17,12],![14,27,26]⟩
def data2108 : PartitionData E W := ⟨6,![cycle2108_0,cycle2108_1,cycle2108_2,cycle2108_3,cycle2108_4,cycle2108_5]⟩
lemma valid_data2108 : data2108.Valid src2108 dst2108 Finset.univ := by decide +kernel

def src2109 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,16,26,38,27,8,18,28,38]
def dst2109 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,16,26,38,27,6,18,28,38,8]
def cycle2109_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2109_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2109_2 : CycleData E W := ⟨3,![2,23,18,19,3],![3,8,38,27,6]⟩
def cycle2109_3 : CycleData E W := ⟨2,![4,15,8,9],![2,6,16,18]⟩
def cycle2109_4 : CycleData E W := ⟨2,![6,12,16,7],![3,14,26,16]⟩
def cycle2109_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data2109 : PartitionData E W := ⟨6,![cycle2109_0,cycle2109_1,cycle2109_2,cycle2109_3,cycle2109_4,cycle2109_5]⟩
lemma valid_data2109 : data2109.Valid src2109 dst2109 Finset.univ := by decide +kernel

def src2110 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,16,26,38,27,8,18,38,28]
def dst2110 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,16,26,38,27,6,18,38,28,8]
def cycle2110_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2110_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2110_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2110_3 : CycleData E W := ⟨3,![3,15,16,12,6],![3,6,16,26,14]⟩
def cycle2110_4 : CycleData E W := ⟨3,![4,19,18,21,9],![2,6,27,38,18]⟩
def cycle2110_5 : CycleData E W := ⟨1,![13,22,17],![26,28,38]⟩
def data2110 : PartitionData E W := ⟨6,![cycle2110_0,cycle2110_1,cycle2110_2,cycle2110_3,cycle2110_4,cycle2110_5]⟩
lemma valid_data2110 : data2110.Valid src2110 dst2110 Finset.univ := by decide +kernel

def src2111 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,16,26,38,27,8,28,18,38]
def dst2111 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,16,26,38,27,6,28,18,38,8]
def cycle2111_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2111_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2111_2 : CycleData E W := ⟨3,![2,23,17,12,6],![3,8,38,26,14]⟩
def cycle2111_3 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2111_4 : CycleData E W := ⟨3,![4,19,18,22,9],![2,6,27,38,18]⟩
def cycle2111_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data2111 : PartitionData E W := ⟨6,![cycle2111_0,cycle2111_1,cycle2111_2,cycle2111_3,cycle2111_4,cycle2111_5]⟩
lemma valid_data2111 : data2111.Valid src2111 dst2111 Finset.univ := by decide +kernel

def src2112 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,16,27,38,26,8,18,28,38]
def dst2112 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,16,27,38,26,6,18,28,38,8]
def cycle2112_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2112_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2112_2 : CycleData E W := ⟨3,![2,23,17,16,7],![3,8,38,27,16]⟩
def cycle2112_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,26,14]⟩
def cycle2112_4 : CycleData E W := ⟨2,![4,15,8,9],![2,6,16,18]⟩
def cycle2112_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2112 : PartitionData E W := ⟨6,![cycle2112_0,cycle2112_1,cycle2112_2,cycle2112_3,cycle2112_4,cycle2112_5]⟩
lemma valid_data2112 : data2112.Valid src2112 dst2112 Finset.univ := by decide +kernel

def src2113 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,16,27,38,26,8,18,38,28]
def dst2113 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,16,27,38,26,6,18,38,28,8]
def cycle2113_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2113_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2113_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2113_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,26,14]⟩
def cycle2113_4 : CycleData E W := ⟨4,![4,15,16,17,21,9],![2,6,16,27,38,18]⟩
def cycle2113_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2113 : PartitionData E W := ⟨6,![cycle2113_0,cycle2113_1,cycle2113_2,cycle2113_3,cycle2113_4,cycle2113_5]⟩
lemma valid_data2113 : data2113.Valid src2113 dst2113 Finset.univ := by decide +kernel

def src2114 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,16,27,38,26,8,28,18,38]
def dst2114 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,16,27,38,26,6,28,18,38,8]
def cycle2114_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2114_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2114_2 : CycleData E W := ⟨3,![2,23,17,16,7],![3,8,38,27,16]⟩
def cycle2114_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,26,14]⟩
def cycle2114_4 : CycleData E W := ⟨2,![4,15,8,9],![2,6,16,18]⟩
def cycle2114_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,26,38]⟩
def data2114 : PartitionData E W := ⟨6,![cycle2114_0,cycle2114_1,cycle2114_2,cycle2114_3,cycle2114_4,cycle2114_5]⟩
lemma valid_data2114 : data2114.Valid src2114 dst2114 Finset.univ := by decide +kernel

def src2115 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,16,38,27,26,8,18,28,38]
def dst2115 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,16,38,27,26,6,18,28,38,8]
def cycle2115_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2115_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2115_2 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,26,28,18]⟩
def cycle2115_3 : CycleData E W := ⟨2,![20,8,16,23],![8,18,16,38]⟩
def cycle2115_4 : CycleData E W := ⟨2,![10,17,22,14],![4,27,38,28]⟩
def cycle2115_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data2115 : PartitionData E W := ⟨6,![cycle2115_0,cycle2115_1,cycle2115_2,cycle2115_3,cycle2115_4,cycle2115_5]⟩
lemma valid_data2115 : data2115.Valid src2115 dst2115 Finset.univ := by decide +kernel

def src2116 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,16,38,27,26,8,18,38,28]
def dst2116 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,16,38,27,26,6,18,38,28,8]
def cycle2116_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2116_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2116_2 : CycleData E W := ⟨4,![4,19,13,23,20,9],![2,6,26,28,8,18]⟩
def cycle2116_3 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2116_4 : CycleData E W := ⟨2,![10,17,22,14],![4,27,38,28]⟩
def cycle2116_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data2116 : PartitionData E W := ⟨6,![cycle2116_0,cycle2116_1,cycle2116_2,cycle2116_3,cycle2116_4,cycle2116_5]⟩
lemma valid_data2116 : data2116.Valid src2116 dst2116 Finset.univ := by decide +kernel

def src2117 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,16,38,27,26,8,28,18,38]
def dst2117 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,16,38,27,26,6,28,18,38,8]
def cycle2117_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2117_1 : CycleData E W := ⟨1,![3,15,7],![3,6,16]⟩
def cycle2117_2 : CycleData E W := ⟨3,![4,19,13,21,9],![2,6,26,28,18]⟩
def cycle2117_3 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle2117_4 : CycleData E W := ⟨3,![10,17,23,20,14],![4,27,38,8,28]⟩
def cycle2117_5 : CycleData E W := ⟨1,![11,18,12],![14,27,26]⟩
def data2117 : PartitionData E W := ⟨6,![cycle2117_0,cycle2117_1,cycle2117_2,cycle2117_3,cycle2117_4,cycle2117_5]⟩
lemma valid_data2117 : data2117.Valid src2117 dst2117 Finset.univ := by decide +kernel

def src2118 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,26,16,27,38,8,18,28,38]
def dst2118 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2118_0 : CycleData E W := ⟨2,![0,1,20,9],![2,4,8,18]⟩
def cycle2118_1 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2118_2 : CycleData E W := ⟨2,![4,15,12,5],![2,6,26,14]⟩
def cycle2118_3 : CycleData E W := ⟨2,![6,11,17,7],![3,14,27,16]⟩
def cycle2118_4 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2118_5 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def data2118 : PartitionData E W := ⟨6,![cycle2118_0,cycle2118_1,cycle2118_2,cycle2118_3,cycle2118_4,cycle2118_5]⟩
lemma valid_data2118 : data2118.Valid src2118 dst2118 Finset.univ := by decide +kernel

def src2119 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,26,16,27,38,8,18,38,28]
def dst2119 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2119_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2119_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2119_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2119_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2119_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2119_5 : CycleData E W := ⟨3,![16,13,22,18,17],![16,26,28,38,27]⟩
def data2119 : PartitionData E W := ⟨6,![cycle2119_0,cycle2119_1,cycle2119_2,cycle2119_3,cycle2119_4,cycle2119_5]⟩
lemma valid_data2119 : data2119.Valid src2119 dst2119 Finset.univ := by decide +kernel

def src2120 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,26,16,27,38,8,28,18,38]
def dst2120 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2120_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2120_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2120_2 : CycleData E W := ⟨3,![2,23,18,17,7],![3,8,38,27,16]⟩
def cycle2120_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2120_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2120_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data2120 : PartitionData E W := ⟨6,![cycle2120_0,cycle2120_1,cycle2120_2,cycle2120_3,cycle2120_4,cycle2120_5]⟩
lemma valid_data2120 : data2120.Valid src2120 dst2120 Finset.univ := by decide +kernel

def src2121 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,26,16,38,27,8,18,28,38]
def dst2121 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2121_0 : CycleData E W := ⟨2,![0,1,20,9],![2,4,8,18]⟩
def cycle2121_1 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2121_2 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,14]⟩
def cycle2121_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def cycle2121_4 : CycleData E W := ⟨2,![10,18,22,14],![4,27,38,28]⟩
def cycle2121_5 : CycleData E W := ⟨2,![15,12,11,19],![6,26,14,27]⟩
def data2121 : PartitionData E W := ⟨6,![cycle2121_0,cycle2121_1,cycle2121_2,cycle2121_3,cycle2121_4,cycle2121_5]⟩
lemma valid_data2121 : data2121.Valid src2121 dst2121 Finset.univ := by decide +kernel

def src2122 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,26,16,38,27,8,18,38,28]
def dst2122 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2122_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2122_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2122_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2122_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2122_4 : CycleData E W := ⟨3,![4,19,18,21,9],![2,6,27,38,18]⟩
def cycle2122_5 : CycleData E W := ⟨2,![16,13,22,17],![16,26,28,38]⟩
def data2122 : PartitionData E W := ⟨6,![cycle2122_0,cycle2122_1,cycle2122_2,cycle2122_3,cycle2122_4,cycle2122_5]⟩
lemma valid_data2122 : data2122.Valid src2122 dst2122 Finset.univ := by decide +kernel

def src2123 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,26,16,38,27,8,28,18,38]
def dst2123 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2123_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2123_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2123_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2123_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2123_4 : CycleData E W := ⟨3,![4,19,18,22,9],![2,6,27,38,18]⟩
def cycle2123_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,26]⟩
def data2123 : PartitionData E W := ⟨6,![cycle2123_0,cycle2123_1,cycle2123_2,cycle2123_3,cycle2123_4,cycle2123_5]⟩
lemma valid_data2123 : data2123.Valid src2123 dst2123 Finset.univ := by decide +kernel

def src2124 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,26,27,16,38,8,18,28,38]
def dst2124 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,26,27,16,38,6,18,28,38,8]
def cycle2124_0 : CycleData E W := ⟨3,![0,10,17,8,9],![2,4,27,16,18]⟩
def cycle2124_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2124_2 : CycleData E W := ⟨2,![2,23,18,7],![3,8,38,16]⟩
def cycle2124_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,14]⟩
def cycle2124_4 : CycleData E W := ⟨1,![11,16,12],![14,27,26]⟩
def cycle2124_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2124 : PartitionData E W := ⟨6,![cycle2124_0,cycle2124_1,cycle2124_2,cycle2124_3,cycle2124_4,cycle2124_5]⟩
lemma valid_data2124 : data2124.Valid src2124 dst2124 Finset.univ := by decide +kernel

def src2125 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,26,27,16,38,8,18,38,28]
def dst2125 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,26,27,16,38,6,18,38,28,8]
def cycle2125_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2125_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2125_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2125_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2125_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2125_5 : CycleData E W := ⟨3,![17,16,13,22,18],![16,27,26,28,38]⟩
def data2125 : PartitionData E W := ⟨6,![cycle2125_0,cycle2125_1,cycle2125_2,cycle2125_3,cycle2125_4,cycle2125_5]⟩
lemma valid_data2125 : data2125.Valid src2125 dst2125 Finset.univ := by decide +kernel

def src2126 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,26,27,16,38,8,28,18,38]
def dst2126 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,26,27,16,38,6,28,18,38,8]
def cycle2126_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2126_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2126_2 : CycleData E W := ⟨2,![2,23,18,7],![3,8,38,16]⟩
def cycle2126_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2126_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2126_5 : CycleData E W := ⟨3,![8,21,13,16,17],![16,18,28,26,27]⟩
def data2126 : PartitionData E W := ⟨6,![cycle2126_0,cycle2126_1,cycle2126_2,cycle2126_3,cycle2126_4,cycle2126_5]⟩
lemma valid_data2126 : data2126.Valid src2126 dst2126 Finset.univ := by decide +kernel

def src2127 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,26,38,16,27,8,18,28,38]
def dst2127 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,26,38,16,27,6,18,28,38,8]
def cycle2127_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2127_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2127_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2127_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2127_4 : CycleData E W := ⟨3,![4,19,18,8,9],![2,6,27,16,18]⟩
def cycle2127_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2127 : PartitionData E W := ⟨6,![cycle2127_0,cycle2127_1,cycle2127_2,cycle2127_3,cycle2127_4,cycle2127_5]⟩
lemma valid_data2127 : data2127.Valid src2127 dst2127 Finset.univ := by decide +kernel

def src2128 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,26,38,16,27,8,18,38,28]
def dst2128 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,26,38,16,27,6,18,38,28,8]
def cycle2128_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2128_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2128_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2128_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2128_4 : CycleData E W := ⟨4,![4,19,18,17,21,9],![2,6,27,16,38,18]⟩
def cycle2128_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2128 : PartitionData E W := ⟨6,![cycle2128_0,cycle2128_1,cycle2128_2,cycle2128_3,cycle2128_4,cycle2128_5]⟩
lemma valid_data2128 : data2128.Valid src2128 dst2128 Finset.univ := by decide +kernel

def src2129 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,14,26,28,6,26,38,16,27,8,28,18,38]
def dst2129 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,14,26,28,4,26,38,16,27,6,28,18,38,8]
def cycle2129_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,27,14]⟩
def cycle2129_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2129_2 : CycleData E W := ⟨3,![2,23,16,12,6],![3,8,38,26,14]⟩
def cycle2129_3 : CycleData E W := ⟨2,![3,19,18,7],![3,6,27,16]⟩
def cycle2129_4 : CycleData E W := ⟨3,![4,15,13,21,9],![2,6,26,28,18]⟩
def cycle2129_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2129 : PartitionData E W := ⟨6,![cycle2129_0,cycle2129_1,cycle2129_2,cycle2129_3,cycle2129_4,cycle2129_5]⟩
lemma valid_data2129 : data2129.Valid src2129 dst2129 Finset.univ := by decide +kernel

def src2130 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,26,14,28,6,26,16,27,38,8,18,28,38]
def dst2130 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,26,14,28,4,26,16,27,38,6,18,28,38,8]
def cycle2130_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,28,14]⟩
def cycle2130_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,27]⟩
def cycle2130_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2130_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2130_4 : CycleData E W := ⟨3,![4,19,22,21,9],![2,6,38,28,18]⟩
def cycle2130_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data2130 : PartitionData E W := ⟨6,![cycle2130_0,cycle2130_1,cycle2130_2,cycle2130_3,cycle2130_4,cycle2130_5]⟩
lemma valid_data2130 : data2130.Valid src2130 dst2130 Finset.univ := by decide +kernel

def src2131 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,26,14,28,6,26,16,27,38,8,18,38,28]
def dst2131 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,26,14,28,4,26,16,27,38,6,18,38,28,8]
def cycle2131_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,28,14]⟩
def cycle2131_1 : CycleData E W := ⟨3,![1,23,22,18,10],![4,8,28,38,27]⟩
def cycle2131_2 : CycleData E W := ⟨2,![2,20,8,7],![3,8,18,16]⟩
def cycle2131_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2131_4 : CycleData E W := ⟨2,![4,19,21,9],![2,6,38,18]⟩
def cycle2131_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data2131 : PartitionData E W := ⟨6,![cycle2131_0,cycle2131_1,cycle2131_2,cycle2131_3,cycle2131_4,cycle2131_5]⟩
lemma valid_data2131 : data2131.Valid src2131 dst2131 Finset.univ := by decide +kernel

def src2132 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,26,14,28,6,26,16,27,38,8,28,18,38]
def dst2132 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,26,14,28,4,26,16,27,38,6,28,18,38,8]
def cycle2132_0 : CycleData E W := ⟨2,![0,14,13,5],![2,4,28,14]⟩
def cycle2132_1 : CycleData E W := ⟨2,![1,23,18,10],![4,8,38,27]⟩
def cycle2132_2 : CycleData E W := ⟨3,![2,20,21,8,7],![3,8,28,18,16]⟩
def cycle2132_3 : CycleData E W := ⟨2,![3,15,12,6],![3,6,26,14]⟩
def cycle2132_4 : CycleData E W := ⟨2,![4,19,22,9],![2,6,38,18]⟩
def cycle2132_5 : CycleData E W := ⟨1,![16,11,17],![16,26,27]⟩
def data2132 : PartitionData E W := ⟨6,![cycle2132_0,cycle2132_1,cycle2132_2,cycle2132_3,cycle2132_4,cycle2132_5]⟩
lemma valid_data2132 : data2132.Valid src2132 dst2132 Finset.univ := by decide +kernel

def src2133 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,26,14,28,6,26,38,16,27,8,18,28,38]
def dst2133 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,26,14,28,4,26,38,16,27,6,18,28,38,8]
def cycle2133_0 : CycleData E W := ⟨3,![0,10,18,8,9],![2,4,27,16,18]⟩
def cycle2133_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2133_2 : CycleData E W := ⟨2,![2,23,17,7],![3,8,38,16]⟩
def cycle2133_3 : CycleData E W := ⟨2,![4,3,6,5],![2,6,3,14]⟩
def cycle2133_4 : CycleData E W := ⟨1,![15,11,19],![6,26,27]⟩
def cycle2133_5 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data2133 : PartitionData E W := ⟨6,![cycle2133_0,cycle2133_1,cycle2133_2,cycle2133_3,cycle2133_4,cycle2133_5]⟩
lemma valid_data2133 : data2133.Valid src2133 dst2133 Finset.univ := by decide +kernel

def src2134 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,26,14,28,6,26,38,16,27,8,18,38,28]
def dst2134 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,26,14,28,4,26,38,16,27,6,18,38,28,8]
def cycle2134_0 : CycleData E W := ⟨3,![0,10,11,15,4],![2,4,27,26,6]⟩
def cycle2134_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2134_2 : CycleData E W := ⟨3,![5,6,2,20,9],![2,14,3,8,18]⟩
def cycle2134_3 : CycleData E W := ⟨2,![3,19,18,7],![3,6,27,16]⟩
def cycle2134_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2134_5 : CycleData E W := ⟨2,![12,16,22,13],![14,26,38,28]⟩
def data2134 : PartitionData E W := ⟨6,![cycle2134_0,cycle2134_1,cycle2134_2,cycle2134_3,cycle2134_4,cycle2134_5]⟩
lemma valid_data2134 : data2134.Valid src2134 dst2134 Finset.univ := by decide +kernel

def src2135 : E → W := ![2,4,8,3,6,2,14,3,16,18,4,27,26,14,28,6,26,38,16,27,8,28,18,38]
def dst2135 : E → W := ![4,8,3,6,2,14,3,16,18,2,27,26,14,28,4,26,38,16,27,6,28,18,38,8]
def cycle2135_0 : CycleData E W := ⟨3,![0,10,11,15,4],![2,4,27,26,6]⟩
def cycle2135_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2135_2 : CycleData E W := ⟨3,![2,23,16,12,6],![3,8,38,26,14]⟩
def cycle2135_3 : CycleData E W := ⟨2,![3,19,18,7],![3,6,27,16]⟩
def cycle2135_4 : CycleData E W := ⟨2,![5,13,21,9],![2,14,28,18]⟩
def cycle2135_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2135 : PartitionData E W := ⟨6,![cycle2135_0,cycle2135_1,cycle2135_2,cycle2135_3,cycle2135_4,cycle2135_5]⟩
lemma valid_data2135 : data2135.Valid src2135 dst2135 Finset.univ := by decide +kernel

def src2136 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,27,28,6,26,38,16,27,8,18,28,38]
def dst2136 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2136_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2136_1 : CycleData E W := ⟨3,![2,1,14,21,7],![3,8,4,28,18]⟩
def cycle2136_2 : CycleData E W := ⟨2,![3,15,11,6],![3,6,26,14]⟩
def cycle2136_3 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2136_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2136_5 : CycleData E W := ⟨2,![12,13,22,16],![26,27,28,38]⟩
def data2136 : PartitionData E W := ⟨6,![cycle2136_0,cycle2136_1,cycle2136_2,cycle2136_3,cycle2136_4,cycle2136_5]⟩
lemma valid_data2136 : data2136.Valid src2136 dst2136 Finset.univ := by decide +kernel

def src2137 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,27,28,6,26,38,16,27,8,18,38,28]
def dst2137 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,27,28,4,26,38,16,27,6,18,38,28,8]
def cycle2137_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2137_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2137_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2137_3 : CycleData E W := ⟨2,![3,15,11,6],![3,6,26,14]⟩
def cycle2137_4 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2137_5 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2137_6 : CycleData E W := ⟨2,![12,13,22,16],![26,27,28,38]⟩
def data2137 : PartitionData E W := ⟨7,![cycle2137_0,cycle2137_1,cycle2137_2,cycle2137_3,cycle2137_4,cycle2137_5,cycle2137_6]⟩
lemma valid_data2137 : data2137.Valid src2137 dst2137 Finset.univ := by decide +kernel

def src2138 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,27,28,6,26,38,16,27,8,28,18,38]
def dst2138 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,27,28,4,26,38,16,27,6,28,18,38,8]
def cycle2138_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2138_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2138_2 : CycleData E W := ⟨3,![2,23,16,11,6],![3,8,38,26,14]⟩
def cycle2138_3 : CycleData E W := ⟨3,![4,3,7,8,9],![2,6,3,18,16]⟩
def cycle2138_4 : CycleData E W := ⟨1,![15,12,19],![6,26,27]⟩
def cycle2138_5 : CycleData E W := ⟨3,![17,22,21,13,18],![16,38,18,28,27]⟩
def data2138 : PartitionData E W := ⟨6,![cycle2138_0,cycle2138_1,cycle2138_2,cycle2138_3,cycle2138_4,cycle2138_5]⟩
lemma valid_data2138 : data2138.Valid src2138 dst2138 Finset.univ := by decide +kernel

def src2139 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,27,28,6,27,16,26,38,8,18,28,38]
def dst2139 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,27,28,4,27,16,26,38,6,18,28,38,8]
def cycle2139_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2139_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2139_2 : CycleData E W := ⟨3,![2,23,18,11,6],![3,8,38,26,14]⟩
def cycle2139_3 : CycleData E W := ⟨3,![4,3,7,8,9],![2,6,3,18,16]⟩
def cycle2139_4 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def cycle2139_5 : CycleData E W := ⟨2,![15,13,22,19],![6,27,28,38]⟩
def data2139 : PartitionData E W := ⟨6,![cycle2139_0,cycle2139_1,cycle2139_2,cycle2139_3,cycle2139_4,cycle2139_5]⟩
lemma valid_data2139 : data2139.Valid src2139 dst2139 Finset.univ := by decide +kernel

def src2140 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,27,28,6,27,16,26,38,8,18,38,28]
def dst2140 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,27,28,4,27,16,26,38,6,18,38,28,8]
def cycle2140_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2140_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2140_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2140_3 : CycleData E W := ⟨3,![3,15,12,11,6],![3,6,27,26,14]⟩
def cycle2140_4 : CycleData E W := ⟨3,![4,19,18,17,9],![2,6,38,26,16]⟩
def cycle2140_5 : CycleData E W := ⟨3,![8,21,22,13,16],![16,18,38,28,27]⟩
def data2140 : PartitionData E W := ⟨6,![cycle2140_0,cycle2140_1,cycle2140_2,cycle2140_3,cycle2140_4,cycle2140_5]⟩
lemma valid_data2140 : data2140.Valid src2140 dst2140 Finset.univ := by decide +kernel

def src2141 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,27,28,6,27,16,26,38,8,28,18,38]
def dst2141 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,27,28,4,27,16,26,38,6,28,18,38,8]
def cycle2141_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2141_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2141_2 : CycleData E W := ⟨3,![2,23,18,11,6],![3,8,38,26,14]⟩
def cycle2141_3 : CycleData E W := ⟨3,![4,3,7,8,9],![2,6,3,18,16]⟩
def cycle2141_4 : CycleData E W := ⟨1,![16,12,17],![16,27,26]⟩
def cycle2141_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,27,28,18,38]⟩
def data2141 : PartitionData E W := ⟨6,![cycle2141_0,cycle2141_1,cycle2141_2,cycle2141_3,cycle2141_4,cycle2141_5]⟩
lemma valid_data2141 : data2141.Valid src2141 dst2141 Finset.univ := by decide +kernel

def src2142 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,28,27,6,26,16,27,38,8,18,28,38]
def dst2142 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,28,27,4,26,16,27,38,6,18,28,38,8]
def cycle2142_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2142_1 : CycleData E W := ⟨3,![1,20,8,17,14],![4,8,18,16,27]⟩
def cycle2142_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2142_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2142_4 : CycleData E W := ⟨3,![6,11,12,21,7],![3,14,26,28,18]⟩
def cycle2142_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2142 : PartitionData E W := ⟨6,![cycle2142_0,cycle2142_1,cycle2142_2,cycle2142_3,cycle2142_4,cycle2142_5]⟩
lemma valid_data2142 : data2142.Valid src2142 dst2142 Finset.univ := by decide +kernel

def src2143 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,28,27,6,26,16,27,38,8,18,38,28]
def dst2143 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,28,27,4,26,16,27,38,6,18,38,28,8]
def cycle2143_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2143_1 : CycleData E W := ⟨3,![1,20,8,17,14],![4,8,18,16,27]⟩
def cycle2143_2 : CycleData E W := ⟨3,![2,23,12,11,6],![3,8,28,26,14]⟩
def cycle2143_3 : CycleData E W := ⟨2,![3,19,21,7],![3,6,38,18]⟩
def cycle2143_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2143_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2143 : PartitionData E W := ⟨6,![cycle2143_0,cycle2143_1,cycle2143_2,cycle2143_3,cycle2143_4,cycle2143_5]⟩
lemma valid_data2143 : data2143.Valid src2143 dst2143 Finset.univ := by decide +kernel

def src2144 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,28,27,6,26,16,27,38,8,28,18,38]
def dst2144 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,28,27,4,26,16,27,38,6,28,18,38,8]
def cycle2144_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2144_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2144_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2144_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2144_4 : CycleData E W := ⟨3,![6,11,12,21,7],![3,14,26,28,18]⟩
def cycle2144_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,27]⟩
def data2144 : PartitionData E W := ⟨6,![cycle2144_0,cycle2144_1,cycle2144_2,cycle2144_3,cycle2144_4,cycle2144_5]⟩
lemma valid_data2144 : data2144.Valid src2144 dst2144 Finset.univ := by decide +kernel

def src2145 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,28,27,6,26,16,38,27,8,18,28,38]
def dst2145 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,28,27,4,26,16,38,27,6,18,28,38,8]
def cycle2145_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2145_1 : CycleData E W := ⟨3,![2,1,14,19,3],![3,8,4,27,6]⟩
def cycle2145_2 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2145_3 : CycleData E W := ⟨3,![6,11,12,21,7],![3,14,26,28,18]⟩
def cycle2145_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2145_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2145 : PartitionData E W := ⟨6,![cycle2145_0,cycle2145_1,cycle2145_2,cycle2145_3,cycle2145_4,cycle2145_5]⟩
lemma valid_data2145 : data2145.Valid src2145 dst2145 Finset.univ := by decide +kernel

def src2146 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,28,27,6,26,16,38,27,8,18,38,28]
def dst2146 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,28,27,4,26,16,38,27,6,18,38,28,8]
def cycle2146_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2146_1 : CycleData E W := ⟨3,![2,1,14,19,3],![3,8,4,27,6]⟩
def cycle2146_2 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2146_3 : CycleData E W := ⟨4,![6,11,12,23,20,7],![3,14,26,28,8,18]⟩
def cycle2146_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2146_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2146 : PartitionData E W := ⟨6,![cycle2146_0,cycle2146_1,cycle2146_2,cycle2146_3,cycle2146_4,cycle2146_5]⟩
lemma valid_data2146 : data2146.Valid src2146 dst2146 Finset.univ := by decide +kernel

def src2147 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,28,27,6,26,16,38,27,8,28,18,38]
def dst2147 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,28,27,4,26,16,38,27,6,28,18,38,8]
def cycle2147_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2147_1 : CycleData E W := ⟨3,![2,1,14,19,3],![3,8,4,27,6]⟩
def cycle2147_2 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2147_3 : CycleData E W := ⟨3,![6,11,12,21,7],![3,14,26,28,18]⟩
def cycle2147_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2147_5 : CycleData E W := ⟨2,![20,13,18,23],![8,28,27,38]⟩
def data2147 : PartitionData E W := ⟨6,![cycle2147_0,cycle2147_1,cycle2147_2,cycle2147_3,cycle2147_4,cycle2147_5]⟩
lemma valid_data2147 : data2147.Valid src2147 dst2147 Finset.univ := by decide +kernel

def src2148 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,28,27,6,26,38,16,27,8,18,28,38]
def dst2148 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,28,27,4,26,38,16,27,6,18,28,38,8]
def cycle2148_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2148_1 : CycleData E W := ⟨4,![2,1,14,13,21,7],![3,8,4,27,28,18]⟩
def cycle2148_2 : CycleData E W := ⟨2,![3,15,11,6],![3,6,26,14]⟩
def cycle2148_3 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2148_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2148_5 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data2148 : PartitionData E W := ⟨6,![cycle2148_0,cycle2148_1,cycle2148_2,cycle2148_3,cycle2148_4,cycle2148_5]⟩
lemma valid_data2148 : data2148.Valid src2148 dst2148 Finset.univ := by decide +kernel

def src2149 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,28,27,6,26,38,16,27,8,18,38,28]
def dst2149 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,28,27,4,26,38,16,27,6,18,38,28,8]
def cycle2149_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2149_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,27]⟩
def cycle2149_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2149_3 : CycleData E W := ⟨2,![3,15,11,6],![3,6,26,14]⟩
def cycle2149_4 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2149_5 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2149_6 : CycleData E W := ⟨1,![12,22,16],![26,28,38]⟩
def data2149 : PartitionData E W := ⟨7,![cycle2149_0,cycle2149_1,cycle2149_2,cycle2149_3,cycle2149_4,cycle2149_5,cycle2149_6]⟩
lemma valid_data2149 : data2149.Valid src2149 dst2149 Finset.univ := by decide +kernel

def src2150 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,28,27,6,26,38,16,27,8,28,18,38]
def dst2150 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,28,27,4,26,38,16,27,6,28,18,38,8]
def cycle2150_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2150_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2150_2 : CycleData E W := ⟨3,![2,23,16,11,6],![3,8,38,26,14]⟩
def cycle2150_3 : CycleData E W := ⟨3,![3,15,12,21,7],![3,6,26,28,18]⟩
def cycle2150_4 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2150_5 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def data2150 : PartitionData E W := ⟨6,![cycle2150_0,cycle2150_1,cycle2150_2,cycle2150_3,cycle2150_4,cycle2150_5]⟩
lemma valid_data2150 : data2150.Valid src2150 dst2150 Finset.univ := by decide +kernel

def src2151 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,28,27,6,27,16,26,38,8,18,28,38]
def dst2151 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,28,27,4,27,16,26,38,6,18,28,38,8]
def cycle2151_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2151_1 : CycleData E W := ⟨3,![1,20,21,13,14],![4,8,18,28,27]⟩
def cycle2151_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2151_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2151_4 : CycleData E W := ⟨3,![6,11,17,8,7],![3,14,26,16,18]⟩
def cycle2151_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data2151 : PartitionData E W := ⟨6,![cycle2151_0,cycle2151_1,cycle2151_2,cycle2151_3,cycle2151_4,cycle2151_5]⟩
lemma valid_data2151 : data2151.Valid src2151 dst2151 Finset.univ := by decide +kernel

def src2152 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,28,27,6,27,16,26,38,8,18,38,28]
def dst2152 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,28,27,4,27,16,26,38,6,18,38,28,8]
def cycle2152_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2152_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,27]⟩
def cycle2152_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2152_3 : CycleData E W := ⟨4,![4,3,6,11,17,9],![2,6,3,14,26,16]⟩
def cycle2152_4 : CycleData E W := ⟨3,![15,16,8,21,19],![6,27,16,18,38]⟩
def cycle2152_5 : CycleData E W := ⟨1,![12,22,18],![26,28,38]⟩
def data2152 : PartitionData E W := ⟨6,![cycle2152_0,cycle2152_1,cycle2152_2,cycle2152_3,cycle2152_4,cycle2152_5]⟩
lemma valid_data2152 : data2152.Valid src2152 dst2152 Finset.univ := by decide +kernel

def src2153 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,26,28,27,6,27,16,26,38,8,28,18,38]
def dst2153 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,26,28,27,4,27,16,26,38,6,28,18,38,8]
def cycle2153_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2153_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,27]⟩
def cycle2153_2 : CycleData E W := ⟨3,![2,23,18,11,6],![3,8,38,26,14]⟩
def cycle2153_3 : CycleData E W := ⟨2,![3,19,22,7],![3,6,38,18]⟩
def cycle2153_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2153_5 : CycleData E W := ⟨2,![8,21,12,17],![16,18,28,26]⟩
def data2153 : PartitionData E W := ⟨6,![cycle2153_0,cycle2153_1,cycle2153_2,cycle2153_3,cycle2153_4,cycle2153_5]⟩
lemma valid_data2153 : data2153.Valid src2153 dst2153 Finset.univ := by decide +kernel

def src2154 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,26,28,6,26,16,27,38,8,18,28,38]
def dst2154 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,26,28,4,26,16,27,38,6,18,28,38,8]
def cycle2154_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2154_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2154_2 : CycleData E W := ⟨3,![2,23,18,11,6],![3,8,38,27,14]⟩
def cycle2154_3 : CycleData E W := ⟨3,![4,3,7,8,9],![2,6,3,18,16]⟩
def cycle2154_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle2154_5 : CycleData E W := ⟨2,![15,13,22,19],![6,26,28,38]⟩
def data2154 : PartitionData E W := ⟨6,![cycle2154_0,cycle2154_1,cycle2154_2,cycle2154_3,cycle2154_4,cycle2154_5]⟩
lemma valid_data2154 : data2154.Valid src2154 dst2154 Finset.univ := by decide +kernel

def src2155 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,26,28,6,26,16,27,38,8,18,38,28]
def dst2155 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,26,28,4,26,16,27,38,6,18,38,28,8]
def cycle2155_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2155_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2155_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2155_3 : CycleData E W := ⟨3,![3,15,12,11,6],![3,6,26,27,14]⟩
def cycle2155_4 : CycleData E W := ⟨3,![4,19,18,17,9],![2,6,38,27,16]⟩
def cycle2155_5 : CycleData E W := ⟨3,![8,21,22,13,16],![16,18,38,28,26]⟩
def data2155 : PartitionData E W := ⟨6,![cycle2155_0,cycle2155_1,cycle2155_2,cycle2155_3,cycle2155_4,cycle2155_5]⟩
lemma valid_data2155 : data2155.Valid src2155 dst2155 Finset.univ := by decide +kernel

def src2156 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,26,28,6,26,16,27,38,8,28,18,38]
def dst2156 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,26,28,4,26,16,27,38,6,28,18,38,8]
def cycle2156_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2156_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2156_2 : CycleData E W := ⟨3,![2,23,18,11,6],![3,8,38,27,14]⟩
def cycle2156_3 : CycleData E W := ⟨3,![4,3,7,8,9],![2,6,3,18,16]⟩
def cycle2156_4 : CycleData E W := ⟨1,![16,12,17],![16,26,27]⟩
def cycle2156_5 : CycleData E W := ⟨3,![15,13,21,22,19],![6,26,28,18,38]⟩
def data2156 : PartitionData E W := ⟨6,![cycle2156_0,cycle2156_1,cycle2156_2,cycle2156_3,cycle2156_4,cycle2156_5]⟩
lemma valid_data2156 : data2156.Valid src2156 dst2156 Finset.univ := by decide +kernel

def src2157 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,26,28,6,26,16,38,27,8,18,28,38]
def dst2157 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,26,28,4,26,16,38,27,6,18,28,38,8]
def cycle2157_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2157_1 : CycleData E W := ⟨3,![2,1,14,21,7],![3,8,4,28,18]⟩
def cycle2157_2 : CycleData E W := ⟨2,![3,19,11,6],![3,6,27,14]⟩
def cycle2157_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2157_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2157_5 : CycleData E W := ⟨2,![12,18,22,13],![26,27,38,28]⟩
def data2157 : PartitionData E W := ⟨6,![cycle2157_0,cycle2157_1,cycle2157_2,cycle2157_3,cycle2157_4,cycle2157_5]⟩
lemma valid_data2157 : data2157.Valid src2157 dst2157 Finset.univ := by decide +kernel

def src2158 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,26,28,6,26,16,38,27,8,18,38,28]
def dst2158 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,26,28,4,26,16,38,27,6,18,38,28,8]
def cycle2158_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2158_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2158_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2158_3 : CycleData E W := ⟨2,![3,19,11,6],![3,6,27,14]⟩
def cycle2158_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2158_5 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2158_6 : CycleData E W := ⟨2,![12,18,22,13],![26,27,38,28]⟩
def data2158 : PartitionData E W := ⟨7,![cycle2158_0,cycle2158_1,cycle2158_2,cycle2158_3,cycle2158_4,cycle2158_5,cycle2158_6]⟩
lemma valid_data2158 : data2158.Valid src2158 dst2158 Finset.univ := by decide +kernel

def src2159 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,26,28,6,26,16,38,27,8,28,18,38]
def dst2159 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,26,28,4,26,16,38,27,6,28,18,38,8]
def cycle2159_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2159_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2159_2 : CycleData E W := ⟨3,![2,23,17,8,7],![3,8,38,16,18]⟩
def cycle2159_3 : CycleData E W := ⟨2,![3,19,11,6],![3,6,27,14]⟩
def cycle2159_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2159_5 : CycleData E W := ⟨3,![21,13,12,18,22],![18,28,26,27,38]⟩
def data2159 : PartitionData E W := ⟨6,![cycle2159_0,cycle2159_1,cycle2159_2,cycle2159_3,cycle2159_4,cycle2159_5]⟩
lemma valid_data2159 : data2159.Valid src2159 dst2159 Finset.univ := by decide +kernel

def src2160 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,28,26,6,26,16,27,38,8,18,28,38]
def dst2160 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,28,26,4,26,16,27,38,6,18,28,38,8]
def cycle2160_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2160_1 : CycleData E W := ⟨3,![1,20,21,13,14],![4,8,18,28,26]⟩
def cycle2160_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2160_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2160_4 : CycleData E W := ⟨3,![6,11,17,8,7],![3,14,27,16,18]⟩
def cycle2160_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2160 : PartitionData E W := ⟨6,![cycle2160_0,cycle2160_1,cycle2160_2,cycle2160_3,cycle2160_4,cycle2160_5]⟩
lemma valid_data2160 : data2160.Valid src2160 dst2160 Finset.univ := by decide +kernel

def src2161 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,28,26,6,26,16,27,38,8,18,38,28]
def dst2161 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,28,26,4,26,16,27,38,6,18,38,28,8]
def cycle2161_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2161_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,26]⟩
def cycle2161_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2161_3 : CycleData E W := ⟨4,![4,3,6,11,17,9],![2,6,3,14,27,16]⟩
def cycle2161_4 : CycleData E W := ⟨3,![15,16,8,21,19],![6,26,16,18,38]⟩
def cycle2161_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2161 : PartitionData E W := ⟨6,![cycle2161_0,cycle2161_1,cycle2161_2,cycle2161_3,cycle2161_4,cycle2161_5]⟩
lemma valid_data2161 : data2161.Valid src2161 dst2161 Finset.univ := by decide +kernel

def src2162 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,28,26,6,26,16,27,38,8,28,18,38]
def dst2162 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,28,26,4,26,16,27,38,6,28,18,38,8]
def cycle2162_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2162_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,26]⟩
def cycle2162_2 : CycleData E W := ⟨3,![2,23,18,11,6],![3,8,38,27,14]⟩
def cycle2162_3 : CycleData E W := ⟨2,![3,19,22,7],![3,6,38,18]⟩
def cycle2162_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2162_5 : CycleData E W := ⟨2,![8,21,12,17],![16,18,28,27]⟩
def data2162 : PartitionData E W := ⟨6,![cycle2162_0,cycle2162_1,cycle2162_2,cycle2162_3,cycle2162_4,cycle2162_5]⟩
lemma valid_data2162 : data2162.Valid src2162 dst2162 Finset.univ := by decide +kernel

def src2163 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,28,26,6,26,16,38,27,8,18,28,38]
def dst2163 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,28,26,4,26,16,38,27,6,18,28,38,8]
def cycle2163_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2163_1 : CycleData E W := ⟨4,![2,1,14,13,21,7],![3,8,4,26,28,18]⟩
def cycle2163_2 : CycleData E W := ⟨2,![3,19,11,6],![3,6,27,14]⟩
def cycle2163_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2163_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2163_5 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2163 : PartitionData E W := ⟨6,![cycle2163_0,cycle2163_1,cycle2163_2,cycle2163_3,cycle2163_4,cycle2163_5]⟩
lemma valid_data2163 : data2163.Valid src2163 dst2163 Finset.univ := by decide +kernel

def src2164 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,28,26,6,26,16,38,27,8,18,38,28]
def dst2164 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,28,26,4,26,16,38,27,6,18,38,28,8]
def cycle2164_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2164_1 : CycleData E W := ⟨2,![1,23,13,14],![4,8,28,26]⟩
def cycle2164_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2164_3 : CycleData E W := ⟨2,![3,19,11,6],![3,6,27,14]⟩
def cycle2164_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2164_5 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2164_6 : CycleData E W := ⟨1,![12,22,18],![27,28,38]⟩
def data2164 : PartitionData E W := ⟨7,![cycle2164_0,cycle2164_1,cycle2164_2,cycle2164_3,cycle2164_4,cycle2164_5,cycle2164_6]⟩
lemma valid_data2164 : data2164.Valid src2164 dst2164 Finset.univ := by decide +kernel

def src2165 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,28,26,6,26,16,38,27,8,28,18,38]
def dst2165 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,28,26,4,26,16,38,27,6,28,18,38,8]
def cycle2165_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2165_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,26]⟩
def cycle2165_2 : CycleData E W := ⟨3,![2,23,17,8,7],![3,8,38,16,18]⟩
def cycle2165_3 : CycleData E W := ⟨2,![3,19,11,6],![3,6,27,14]⟩
def cycle2165_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2165_5 : CycleData E W := ⟨2,![21,12,18,22],![18,28,27,38]⟩
def data2165 : PartitionData E W := ⟨6,![cycle2165_0,cycle2165_1,cycle2165_2,cycle2165_3,cycle2165_4,cycle2165_5]⟩
lemma valid_data2165 : data2165.Valid src2165 dst2165 Finset.univ := by decide +kernel

def src2166 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,28,26,6,26,38,16,27,8,18,28,38]
def dst2166 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,28,26,4,26,38,16,27,6,18,28,38,8]
def cycle2166_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2166_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,8,4,26,6]⟩
def cycle2166_2 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2166_3 : CycleData E W := ⟨3,![6,11,12,21,7],![3,14,27,28,18]⟩
def cycle2166_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2166_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2166 : PartitionData E W := ⟨6,![cycle2166_0,cycle2166_1,cycle2166_2,cycle2166_3,cycle2166_4,cycle2166_5]⟩
lemma valid_data2166 : data2166.Valid src2166 dst2166 Finset.univ := by decide +kernel

def src2167 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,28,26,6,26,38,16,27,8,18,38,28]
def dst2167 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,28,26,4,26,38,16,27,6,18,38,28,8]
def cycle2167_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2167_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,8,4,26,6]⟩
def cycle2167_2 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2167_3 : CycleData E W := ⟨4,![6,11,12,23,20,7],![3,14,27,28,8,18]⟩
def cycle2167_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2167_5 : CycleData E W := ⟨1,![13,22,16],![26,28,38]⟩
def data2167 : PartitionData E W := ⟨6,![cycle2167_0,cycle2167_1,cycle2167_2,cycle2167_3,cycle2167_4,cycle2167_5]⟩
lemma valid_data2167 : data2167.Valid src2167 dst2167 Finset.univ := by decide +kernel

def src2168 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,28,26,6,26,38,16,27,8,28,18,38]
def dst2168 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,28,26,4,26,38,16,27,6,28,18,38,8]
def cycle2168_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2168_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,8,4,26,6]⟩
def cycle2168_2 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2168_3 : CycleData E W := ⟨3,![6,11,12,21,7],![3,14,27,28,18]⟩
def cycle2168_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2168_5 : CycleData E W := ⟨2,![20,13,16,23],![8,28,26,38]⟩
def data2168 : PartitionData E W := ⟨6,![cycle2168_0,cycle2168_1,cycle2168_2,cycle2168_3,cycle2168_4,cycle2168_5]⟩
lemma valid_data2168 : data2168.Valid src2168 dst2168 Finset.univ := by decide +kernel

def src2169 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,28,26,6,27,16,26,38,8,18,28,38]
def dst2169 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,28,26,4,27,16,26,38,6,18,28,38,8]
def cycle2169_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2169_1 : CycleData E W := ⟨3,![1,20,8,17,14],![4,8,18,16,26]⟩
def cycle2169_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2169_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2169_4 : CycleData E W := ⟨3,![6,11,12,21,7],![3,14,27,28,18]⟩
def cycle2169_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2169 : PartitionData E W := ⟨6,![cycle2169_0,cycle2169_1,cycle2169_2,cycle2169_3,cycle2169_4,cycle2169_5]⟩
lemma valid_data2169 : data2169.Valid src2169 dst2169 Finset.univ := by decide +kernel

def src2170 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,28,26,6,27,16,26,38,8,18,38,28]
def dst2170 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,28,26,4,27,16,26,38,6,18,38,28,8]
def cycle2170_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2170_1 : CycleData E W := ⟨3,![1,20,8,17,14],![4,8,18,16,26]⟩
def cycle2170_2 : CycleData E W := ⟨3,![2,23,12,11,6],![3,8,28,27,14]⟩
def cycle2170_3 : CycleData E W := ⟨2,![3,19,21,7],![3,6,38,18]⟩
def cycle2170_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2170_5 : CycleData E W := ⟨1,![13,22,18],![26,28,38]⟩
def data2170 : PartitionData E W := ⟨6,![cycle2170_0,cycle2170_1,cycle2170_2,cycle2170_3,cycle2170_4,cycle2170_5]⟩
lemma valid_data2170 : data2170.Valid src2170 dst2170 Finset.univ := by decide +kernel

def src2171 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,27,28,26,6,27,16,26,38,8,28,18,38]
def dst2171 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,27,28,26,4,27,16,26,38,6,28,18,38,8]
def cycle2171_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2171_1 : CycleData E W := ⟨2,![1,20,13,14],![4,8,28,26]⟩
def cycle2171_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2171_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2171_4 : CycleData E W := ⟨3,![6,11,12,21,7],![3,14,27,28,18]⟩
def cycle2171_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def data2171 : PartitionData E W := ⟨6,![cycle2171_0,cycle2171_1,cycle2171_2,cycle2171_3,cycle2171_4,cycle2171_5]⟩
lemma valid_data2171 : data2171.Valid src2171 dst2171 Finset.univ := by decide +kernel

def src2172 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,28,26,27,6,26,16,27,38,8,18,28,38]
def dst2172 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,28,26,27,4,26,16,27,38,6,18,28,38,8]
def cycle2172_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2172_1 : CycleData E W := ⟨3,![1,20,8,17,14],![4,8,18,16,27]⟩
def cycle2172_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2172_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2172_4 : CycleData E W := ⟨2,![6,11,21,7],![3,14,28,18]⟩
def cycle2172_5 : CycleData E W := ⟨2,![12,22,18,13],![26,28,38,27]⟩
def data2172 : PartitionData E W := ⟨6,![cycle2172_0,cycle2172_1,cycle2172_2,cycle2172_3,cycle2172_4,cycle2172_5]⟩
lemma valid_data2172 : data2172.Valid src2172 dst2172 Finset.univ := by decide +kernel

def src2173 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,28,26,27,6,26,16,27,38,8,18,38,28]
def dst2173 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,28,26,27,4,26,16,27,38,6,18,38,28,8]
def cycle2173_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2173_1 : CycleData E W := ⟨3,![1,20,8,17,14],![4,8,18,16,27]⟩
def cycle2173_2 : CycleData E W := ⟨2,![2,23,11,6],![3,8,28,14]⟩
def cycle2173_3 : CycleData E W := ⟨2,![3,19,21,7],![3,6,38,18]⟩
def cycle2173_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2173_5 : CycleData E W := ⟨2,![12,22,18,13],![26,28,38,27]⟩
def data2173 : PartitionData E W := ⟨6,![cycle2173_0,cycle2173_1,cycle2173_2,cycle2173_3,cycle2173_4,cycle2173_5]⟩
lemma valid_data2173 : data2173.Valid src2173 dst2173 Finset.univ := by decide +kernel

def src2174 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,28,26,27,6,26,16,27,38,8,28,18,38]
def dst2174 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,28,26,27,4,26,16,27,38,6,28,18,38,8]
def cycle2174_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2174_1 : CycleData E W := ⟨3,![1,20,12,13,14],![4,8,28,26,27]⟩
def cycle2174_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2174_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2174_4 : CycleData E W := ⟨2,![6,11,21,7],![3,14,28,18]⟩
def cycle2174_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,27]⟩
def data2174 : PartitionData E W := ⟨6,![cycle2174_0,cycle2174_1,cycle2174_2,cycle2174_3,cycle2174_4,cycle2174_5]⟩
lemma valid_data2174 : data2174.Valid src2174 dst2174 Finset.univ := by decide +kernel

def src2175 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,28,26,27,6,26,16,38,27,8,18,28,38]
def dst2175 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,28,26,27,4,26,16,38,27,6,18,28,38,8]
def cycle2175_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2175_1 : CycleData E W := ⟨3,![2,1,14,19,3],![3,8,4,27,6]⟩
def cycle2175_2 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2175_3 : CycleData E W := ⟨2,![6,11,21,7],![3,14,28,18]⟩
def cycle2175_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2175_5 : CycleData E W := ⟨2,![12,22,18,13],![26,28,38,27]⟩
def data2175 : PartitionData E W := ⟨6,![cycle2175_0,cycle2175_1,cycle2175_2,cycle2175_3,cycle2175_4,cycle2175_5]⟩
lemma valid_data2175 : data2175.Valid src2175 dst2175 Finset.univ := by decide +kernel

def src2176 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,28,26,27,6,26,16,38,27,8,18,38,28]
def dst2176 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,28,26,27,4,26,16,38,27,6,18,38,28,8]
def cycle2176_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2176_1 : CycleData E W := ⟨3,![2,1,14,19,3],![3,8,4,27,6]⟩
def cycle2176_2 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2176_3 : CycleData E W := ⟨3,![6,11,23,20,7],![3,14,28,8,18]⟩
def cycle2176_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2176_5 : CycleData E W := ⟨2,![12,22,18,13],![26,28,38,27]⟩
def data2176 : PartitionData E W := ⟨6,![cycle2176_0,cycle2176_1,cycle2176_2,cycle2176_3,cycle2176_4,cycle2176_5]⟩
lemma valid_data2176 : data2176.Valid src2176 dst2176 Finset.univ := by decide +kernel

def src2177 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,28,26,27,6,26,16,38,27,8,28,18,38]
def dst2177 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,28,26,27,4,26,16,38,27,6,28,18,38,8]
def cycle2177_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2177_1 : CycleData E W := ⟨3,![2,1,14,19,3],![3,8,4,27,6]⟩
def cycle2177_2 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2177_3 : CycleData E W := ⟨2,![6,11,21,7],![3,14,28,18]⟩
def cycle2177_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2177_5 : CycleData E W := ⟨3,![20,12,13,18,23],![8,28,26,27,38]⟩
def data2177 : PartitionData E W := ⟨6,![cycle2177_0,cycle2177_1,cycle2177_2,cycle2177_3,cycle2177_4,cycle2177_5]⟩
lemma valid_data2177 : data2177.Valid src2177 dst2177 Finset.univ := by decide +kernel

def src2178 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,28,27,26,6,26,38,16,27,8,18,28,38]
def dst2178 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,28,27,26,4,26,38,16,27,6,18,28,38,8]
def cycle2178_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2178_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,8,4,26,6]⟩
def cycle2178_2 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2178_3 : CycleData E W := ⟨2,![6,11,21,7],![3,14,28,18]⟩
def cycle2178_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2178_5 : CycleData E W := ⟨2,![13,12,22,16],![26,27,28,38]⟩
def data2178 : PartitionData E W := ⟨6,![cycle2178_0,cycle2178_1,cycle2178_2,cycle2178_3,cycle2178_4,cycle2178_5]⟩
lemma valid_data2178 : data2178.Valid src2178 dst2178 Finset.univ := by decide +kernel

def src2179 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,28,27,26,6,26,38,16,27,8,18,38,28]
def dst2179 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,28,27,26,4,26,38,16,27,6,18,38,28,8]
def cycle2179_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2179_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,8,4,26,6]⟩
def cycle2179_2 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2179_3 : CycleData E W := ⟨3,![6,11,23,20,7],![3,14,28,8,18]⟩
def cycle2179_4 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2179_5 : CycleData E W := ⟨2,![13,12,22,16],![26,27,28,38]⟩
def data2179 : PartitionData E W := ⟨6,![cycle2179_0,cycle2179_1,cycle2179_2,cycle2179_3,cycle2179_4,cycle2179_5]⟩
lemma valid_data2179 : data2179.Valid src2179 dst2179 Finset.univ := by decide +kernel

def src2180 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,28,27,26,6,26,38,16,27,8,28,18,38]
def dst2180 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,28,27,26,4,26,38,16,27,6,28,18,38,8]
def cycle2180_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2180_1 : CycleData E W := ⟨3,![2,1,14,15,3],![3,8,4,26,6]⟩
def cycle2180_2 : CycleData E W := ⟨2,![4,19,18,9],![2,6,27,16]⟩
def cycle2180_3 : CycleData E W := ⟨2,![6,11,21,7],![3,14,28,18]⟩
def cycle2180_4 : CycleData E W := ⟨1,![8,22,17],![16,18,38]⟩
def cycle2180_5 : CycleData E W := ⟨3,![20,12,13,16,23],![8,28,27,26,38]⟩
def data2180 : PartitionData E W := ⟨6,![cycle2180_0,cycle2180_1,cycle2180_2,cycle2180_3,cycle2180_4,cycle2180_5]⟩
lemma valid_data2180 : data2180.Valid src2180 dst2180 Finset.univ := by decide +kernel

def src2181 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,28,27,26,6,27,16,26,38,8,18,28,38]
def dst2181 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,28,27,26,4,27,16,26,38,6,18,28,38,8]
def cycle2181_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2181_1 : CycleData E W := ⟨3,![1,20,8,17,14],![4,8,18,16,26]⟩
def cycle2181_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2181_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2181_4 : CycleData E W := ⟨2,![6,11,21,7],![3,14,28,18]⟩
def cycle2181_5 : CycleData E W := ⟨2,![13,12,22,18],![26,27,28,38]⟩
def data2181 : PartitionData E W := ⟨6,![cycle2181_0,cycle2181_1,cycle2181_2,cycle2181_3,cycle2181_4,cycle2181_5]⟩
lemma valid_data2181 : data2181.Valid src2181 dst2181 Finset.univ := by decide +kernel

def src2182 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,28,27,26,6,27,16,26,38,8,18,38,28]
def dst2182 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,28,27,26,4,27,16,26,38,6,18,38,28,8]
def cycle2182_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2182_1 : CycleData E W := ⟨3,![1,20,8,17,14],![4,8,18,16,26]⟩
def cycle2182_2 : CycleData E W := ⟨2,![2,23,11,6],![3,8,28,14]⟩
def cycle2182_3 : CycleData E W := ⟨2,![3,19,21,7],![3,6,38,18]⟩
def cycle2182_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2182_5 : CycleData E W := ⟨2,![13,12,22,18],![26,27,28,38]⟩
def data2182 : PartitionData E W := ⟨6,![cycle2182_0,cycle2182_1,cycle2182_2,cycle2182_3,cycle2182_4,cycle2182_5]⟩
lemma valid_data2182 : data2182.Valid src2182 dst2182 Finset.univ := by decide +kernel

def src2183 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,14,28,27,26,6,27,16,26,38,8,28,18,38]
def dst2183 : E → W := ![4,8,3,6,2,14,3,18,16,2,14,28,27,26,4,27,16,26,38,6,28,18,38,8]
def cycle2183_0 : CycleData E W := ⟨1,![0,10,5],![2,4,14]⟩
def cycle2183_1 : CycleData E W := ⟨3,![1,20,12,13,14],![4,8,28,27,26]⟩
def cycle2183_2 : CycleData E W := ⟨2,![2,23,19,3],![3,8,38,6]⟩
def cycle2183_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,27,16]⟩
def cycle2183_4 : CycleData E W := ⟨2,![6,11,21,7],![3,14,28,18]⟩
def cycle2183_5 : CycleData E W := ⟨2,![8,22,18,17],![16,18,38,26]⟩
def data2183 : PartitionData E W := ⟨6,![cycle2183_0,cycle2183_1,cycle2183_2,cycle2183_3,cycle2183_4,cycle2183_5]⟩
lemma valid_data2183 : data2183.Valid src2183 dst2183 Finset.univ := by decide +kernel

def src2184 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,16,26,38,27,8,18,28,38]
def dst2184 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,16,26,38,27,6,18,28,38,8]
def cycle2184_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2184_1 : CycleData E W := ⟨3,![2,1,14,21,7],![3,8,4,28,18]⟩
def cycle2184_2 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2184_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2184_4 : CycleData E W := ⟨3,![20,8,16,17,23],![8,18,16,26,38]⟩
def cycle2184_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2184 : PartitionData E W := ⟨6,![cycle2184_0,cycle2184_1,cycle2184_2,cycle2184_3,cycle2184_4,cycle2184_5]⟩
lemma valid_data2184 : data2184.Valid src2184 dst2184 Finset.univ := by decide +kernel

def src2185 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,16,26,38,27,8,18,38,28]
def dst2185 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,16,26,38,27,6,18,38,28,8]
def cycle2185_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2185_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2185_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2185_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2185_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2185_5 : CycleData E W := ⟨2,![8,21,17,16],![16,18,38,26]⟩
def cycle2185_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2185 : PartitionData E W := ⟨7,![cycle2185_0,cycle2185_1,cycle2185_2,cycle2185_3,cycle2185_4,cycle2185_5,cycle2185_6]⟩
lemma valid_data2185 : data2185.Valid src2185 dst2185 Finset.univ := by decide +kernel

def src2186 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,16,26,38,27,8,28,18,38]
def dst2186 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,16,26,38,27,6,28,18,38,8]
def cycle2186_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2186_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2186_2 : CycleData E W := ⟨4,![2,23,17,16,8,7],![3,8,38,26,16,18]⟩
def cycle2186_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2186_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2186_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2186 : PartitionData E W := ⟨6,![cycle2186_0,cycle2186_1,cycle2186_2,cycle2186_3,cycle2186_4,cycle2186_5]⟩
lemma valid_data2186 : data2186.Valid src2186 dst2186 Finset.univ := by decide +kernel

def src2187 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,16,27,26,38,8,18,28,38]
def dst2187 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,16,27,26,38,6,18,28,38,8]
def cycle2187_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2187_1 : CycleData E W := ⟨3,![3,19,23,20,7],![3,6,38,8,18]⟩
def cycle2187_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2187_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2187_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle2187_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data2187 : PartitionData E W := ⟨6,![cycle2187_0,cycle2187_1,cycle2187_2,cycle2187_3,cycle2187_4,cycle2187_5]⟩
lemma valid_data2187 : data2187.Valid src2187 dst2187 Finset.univ := by decide +kernel

def src2188 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,16,27,26,38,8,18,38,28]
def dst2188 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,16,27,26,38,6,18,38,28,8]
def cycle2188_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2188_1 : CycleData E W := ⟨2,![3,19,21,7],![3,6,38,18]⟩
def cycle2188_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2188_3 : CycleData E W := ⟨3,![20,8,16,13,23],![8,18,16,27,28]⟩
def cycle2188_4 : CycleData E W := ⟨2,![10,18,22,14],![4,26,38,28]⟩
def cycle2188_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data2188 : PartitionData E W := ⟨6,![cycle2188_0,cycle2188_1,cycle2188_2,cycle2188_3,cycle2188_4,cycle2188_5]⟩
lemma valid_data2188 : data2188.Valid src2188 dst2188 Finset.univ := by decide +kernel

def src2189 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,16,27,26,38,8,28,18,38]
def dst2189 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,16,27,26,38,6,28,18,38,8]
def cycle2189_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2189_1 : CycleData E W := ⟨2,![3,19,22,7],![3,6,38,18]⟩
def cycle2189_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2189_3 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def cycle2189_4 : CycleData E W := ⟨3,![10,18,23,20,14],![4,26,38,8,28]⟩
def cycle2189_5 : CycleData E W := ⟨1,![11,17,12],![14,26,27]⟩
def data2189 : PartitionData E W := ⟨6,![cycle2189_0,cycle2189_1,cycle2189_2,cycle2189_3,cycle2189_4,cycle2189_5]⟩
lemma valid_data2189 : data2189.Valid src2189 dst2189 Finset.univ := by decide +kernel

def src2190 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,16,27,38,26,8,18,28,38]
def dst2190 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,16,27,38,26,6,18,28,38,8]
def cycle2190_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2190_1 : CycleData E W := ⟨2,![1,20,21,14],![4,8,18,28]⟩
def cycle2190_2 : CycleData E W := ⟨3,![2,23,18,19,3],![3,8,38,26,6]⟩
def cycle2190_3 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2190_4 : CycleData E W := ⟨3,![6,12,16,8,7],![3,14,27,16,18]⟩
def cycle2190_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2190 : PartitionData E W := ⟨6,![cycle2190_0,cycle2190_1,cycle2190_2,cycle2190_3,cycle2190_4,cycle2190_5]⟩
lemma valid_data2190 : data2190.Valid src2190 dst2190 Finset.univ := by decide +kernel

def src2191 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,16,27,38,26,8,18,38,28]
def dst2191 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,16,27,38,26,6,18,38,28,8]
def cycle2191_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2191_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2191_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2191_3 : CycleData E W := ⟨4,![4,3,6,12,16,9],![2,6,3,14,27,16]⟩
def cycle2191_4 : CycleData E W := ⟨3,![15,8,21,18,19],![6,16,18,38,26]⟩
def cycle2191_5 : CycleData E W := ⟨1,![13,22,17],![27,28,38]⟩
def data2191 : PartitionData E W := ⟨6,![cycle2191_0,cycle2191_1,cycle2191_2,cycle2191_3,cycle2191_4,cycle2191_5]⟩
lemma valid_data2191 : data2191.Valid src2191 dst2191 Finset.univ := by decide +kernel

def src2192 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,16,27,38,26,8,28,18,38]
def dst2192 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,16,27,38,26,6,28,18,38,8]
def cycle2192_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2192_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2192_2 : CycleData E W := ⟨3,![2,23,17,12,6],![3,8,38,27,14]⟩
def cycle2192_3 : CycleData E W := ⟨3,![3,19,18,22,7],![3,6,26,38,18]⟩
def cycle2192_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2192_5 : CycleData E W := ⟨2,![8,21,13,16],![16,18,28,27]⟩
def data2192 : PartitionData E W := ⟨6,![cycle2192_0,cycle2192_1,cycle2192_2,cycle2192_3,cycle2192_4,cycle2192_5]⟩
lemma valid_data2192 : data2192.Valid src2192 dst2192 Finset.univ := by decide +kernel

def src2193 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,16,38,26,27,8,18,28,38]
def dst2193 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,16,38,26,27,6,18,28,38,8]
def cycle2193_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2193_1 : CycleData E W := ⟨3,![3,19,13,21,7],![3,6,27,28,18]⟩
def cycle2193_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2193_3 : CycleData E W := ⟨2,![20,8,16,23],![8,18,16,38]⟩
def cycle2193_4 : CycleData E W := ⟨2,![10,17,22,14],![4,26,38,28]⟩
def cycle2193_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data2193 : PartitionData E W := ⟨6,![cycle2193_0,cycle2193_1,cycle2193_2,cycle2193_3,cycle2193_4,cycle2193_5]⟩
lemma valid_data2193 : data2193.Valid src2193 dst2193 Finset.univ := by decide +kernel

def src2194 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,16,38,26,27,8,18,38,28]
def dst2194 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,16,38,26,27,6,18,38,28,8]
def cycle2194_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2194_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2194_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2194_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2194_4 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2194_5 : CycleData E W := ⟨1,![8,21,16],![16,18,38]⟩
def cycle2194_6 : CycleData E W := ⟨2,![17,22,13,18],![26,38,28,27]⟩
def data2194 : PartitionData E W := ⟨7,![cycle2194_0,cycle2194_1,cycle2194_2,cycle2194_3,cycle2194_4,cycle2194_5,cycle2194_6]⟩
lemma valid_data2194 : data2194.Valid src2194 dst2194 Finset.univ := by decide +kernel

def src2195 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,16,38,26,27,8,28,18,38]
def dst2195 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,16,38,26,27,6,28,18,38,8]
def cycle2195_0 : CycleData E W := ⟨3,![0,1,2,6,5],![2,4,8,3,14]⟩
def cycle2195_1 : CycleData E W := ⟨3,![3,19,13,21,7],![3,6,27,28,18]⟩
def cycle2195_2 : CycleData E W := ⟨1,![4,15,9],![2,6,16]⟩
def cycle2195_3 : CycleData E W := ⟨1,![8,22,16],![16,18,38]⟩
def cycle2195_4 : CycleData E W := ⟨3,![10,17,23,20,14],![4,26,38,8,28]⟩
def cycle2195_5 : CycleData E W := ⟨1,![11,18,12],![14,26,27]⟩
def data2195 : PartitionData E W := ⟨6,![cycle2195_0,cycle2195_1,cycle2195_2,cycle2195_3,cycle2195_4,cycle2195_5]⟩
lemma valid_data2195 : data2195.Valid src2195 dst2195 Finset.univ := by decide +kernel

def src2196 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,26,16,38,27,8,18,28,38]
def dst2196 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,26,16,38,27,6,18,28,38,8]
def cycle2196_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2196_1 : CycleData E W := ⟨3,![2,1,14,21,7],![3,8,4,28,18]⟩
def cycle2196_2 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2196_3 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2196_4 : CycleData E W := ⟨2,![20,8,17,23],![8,18,16,38]⟩
def cycle2196_5 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2196 : PartitionData E W := ⟨6,![cycle2196_0,cycle2196_1,cycle2196_2,cycle2196_3,cycle2196_4,cycle2196_5]⟩
lemma valid_data2196 : data2196.Valid src2196 dst2196 Finset.univ := by decide +kernel

def src2197 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,26,16,38,27,8,18,38,28]
def dst2197 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,26,16,38,27,6,18,38,28,8]
def cycle2197_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2197_1 : CycleData E W := ⟨1,![1,23,14],![4,8,28]⟩
def cycle2197_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2197_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2197_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2197_5 : CycleData E W := ⟨1,![8,21,17],![16,18,38]⟩
def cycle2197_6 : CycleData E W := ⟨1,![13,22,18],![27,28,38]⟩
def data2197 : PartitionData E W := ⟨7,![cycle2197_0,cycle2197_1,cycle2197_2,cycle2197_3,cycle2197_4,cycle2197_5,cycle2197_6]⟩
lemma valid_data2197 : data2197.Valid src2197 dst2197 Finset.univ := by decide +kernel

def src2198 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,26,16,38,27,8,28,18,38]
def dst2198 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,26,16,38,27,6,28,18,38,8]
def cycle2198_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2198_1 : CycleData E W := ⟨1,![1,20,14],![4,8,28]⟩
def cycle2198_2 : CycleData E W := ⟨3,![2,23,17,8,7],![3,8,38,16,18]⟩
def cycle2198_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2198_4 : CycleData E W := ⟨2,![4,15,16,9],![2,6,26,16]⟩
def cycle2198_5 : CycleData E W := ⟨2,![21,13,18,22],![18,28,27,38]⟩
def data2198 : PartitionData E W := ⟨6,![cycle2198_0,cycle2198_1,cycle2198_2,cycle2198_3,cycle2198_4,cycle2198_5]⟩
lemma valid_data2198 : data2198.Valid src2198 dst2198 Finset.univ := by decide +kernel

def src2199 : E → W := ![2,4,8,3,6,2,14,3,18,16,4,26,14,27,28,6,26,38,16,27,8,18,28,38]
def dst2199 : E → W := ![4,8,3,6,2,14,3,18,16,2,26,14,27,28,4,26,38,16,27,6,18,28,38,8]
def cycle2199_0 : CycleData E W := ⟨2,![0,10,11,5],![2,4,26,14]⟩
def cycle2199_1 : CycleData E W := ⟨2,![1,23,22,14],![4,8,38,28]⟩
def cycle2199_2 : CycleData E W := ⟨1,![2,20,7],![3,8,18]⟩
def cycle2199_3 : CycleData E W := ⟨2,![3,19,12,6],![3,6,27,14]⟩
def cycle2199_4 : CycleData E W := ⟨3,![4,15,16,17,9],![2,6,26,38,16]⟩
def cycle2199_5 : CycleData E W := ⟨2,![8,21,13,18],![16,18,28,27]⟩
def data2199 : PartitionData E W := ⟨6,![cycle2199_0,cycle2199_1,cycle2199_2,cycle2199_3,cycle2199_4,cycle2199_5]⟩
lemma valid_data2199 : data2199.Valid src2199 dst2199 Finset.univ := by decide +kernel

def lookupB10 (j : ℕ) : PartitionData E W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then data2000 else (if j < 2 then data2001 else data2002)) else (if j < 4 then data2003 else (if j < 5 then data2004 else data2005))) else (if j < 9 then (if j < 7 then data2006 else (if j < 8 then data2007 else data2008)) else (if j < 10 then data2009 else (if j < 11 then data2010 else data2011)))) else (if j < 18 then (if j < 15 then (if j < 13 then data2012 else (if j < 14 then data2013 else data2014)) else (if j < 16 then data2015 else (if j < 17 then data2016 else data2017))) else (if j < 21 then (if j < 19 then data2018 else (if j < 20 then data2019 else data2020)) else (if j < 23 then (if j < 22 then data2021 else data2022) else (if j < 24 then data2023 else data2024))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then data2025 else (if j < 27 then data2026 else data2027)) else (if j < 29 then data2028 else (if j < 30 then data2029 else data2030))) else (if j < 34 then (if j < 32 then data2031 else (if j < 33 then data2032 else data2033)) else (if j < 35 then data2034 else (if j < 36 then data2035 else data2036)))) else (if j < 43 then (if j < 40 then (if j < 38 then data2037 else (if j < 39 then data2038 else data2039)) else (if j < 41 then data2040 else (if j < 42 then data2041 else data2042))) else (if j < 46 then (if j < 44 then data2043 else (if j < 45 then data2044 else data2045)) else (if j < 48 then (if j < 47 then data2046 else data2047) else (if j < 49 then data2048 else data2049)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then data2050 else (if j < 52 then data2051 else data2052)) else (if j < 54 then data2053 else (if j < 55 then data2054 else data2055))) else (if j < 59 then (if j < 57 then data2056 else (if j < 58 then data2057 else data2058)) else (if j < 60 then data2059 else (if j < 61 then data2060 else data2061)))) else (if j < 68 then (if j < 65 then (if j < 63 then data2062 else (if j < 64 then data2063 else data2064)) else (if j < 66 then data2065 else (if j < 67 then data2066 else data2067))) else (if j < 71 then (if j < 69 then data2068 else (if j < 70 then data2069 else data2070)) else (if j < 73 then (if j < 72 then data2071 else data2072) else (if j < 74 then data2073 else data2074))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then data2075 else (if j < 77 then data2076 else data2077)) else (if j < 79 then data2078 else (if j < 80 then data2079 else data2080))) else (if j < 84 then (if j < 82 then data2081 else (if j < 83 then data2082 else data2083)) else (if j < 85 then data2084 else (if j < 86 then data2085 else data2086)))) else (if j < 93 then (if j < 90 then (if j < 88 then data2087 else (if j < 89 then data2088 else data2089)) else (if j < 91 then data2090 else (if j < 92 then data2091 else data2092))) else (if j < 96 then (if j < 94 then data2093 else (if j < 95 then data2094 else data2095)) else (if j < 98 then (if j < 97 then data2096 else data2097) else (if j < 99 then data2098 else data2099))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then data2100 else (if j < 102 then data2101 else data2102)) else (if j < 104 then data2103 else (if j < 105 then data2104 else data2105))) else (if j < 109 then (if j < 107 then data2106 else (if j < 108 then data2107 else data2108)) else (if j < 110 then data2109 else (if j < 111 then data2110 else data2111)))) else (if j < 118 then (if j < 115 then (if j < 113 then data2112 else (if j < 114 then data2113 else data2114)) else (if j < 116 then data2115 else (if j < 117 then data2116 else data2117))) else (if j < 121 then (if j < 119 then data2118 else (if j < 120 then data2119 else data2120)) else (if j < 123 then (if j < 122 then data2121 else data2122) else (if j < 124 then data2123 else data2124))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then data2125 else (if j < 127 then data2126 else data2127)) else (if j < 129 then data2128 else (if j < 130 then data2129 else data2130))) else (if j < 134 then (if j < 132 then data2131 else (if j < 133 then data2132 else data2133)) else (if j < 135 then data2134 else (if j < 136 then data2135 else data2136)))) else (if j < 143 then (if j < 140 then (if j < 138 then data2137 else (if j < 139 then data2138 else data2139)) else (if j < 141 then data2140 else (if j < 142 then data2141 else data2142))) else (if j < 146 then (if j < 144 then data2143 else (if j < 145 then data2144 else data2145)) else (if j < 148 then (if j < 147 then data2146 else data2147) else (if j < 149 then data2148 else data2149)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then data2150 else (if j < 152 then data2151 else data2152)) else (if j < 154 then data2153 else (if j < 155 then data2154 else data2155))) else (if j < 159 then (if j < 157 then data2156 else (if j < 158 then data2157 else data2158)) else (if j < 160 then data2159 else (if j < 161 then data2160 else data2161)))) else (if j < 168 then (if j < 165 then (if j < 163 then data2162 else (if j < 164 then data2163 else data2164)) else (if j < 166 then data2165 else (if j < 167 then data2166 else data2167))) else (if j < 171 then (if j < 169 then data2168 else (if j < 170 then data2169 else data2170)) else (if j < 173 then (if j < 172 then data2171 else data2172) else (if j < 174 then data2173 else data2174))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then data2175 else (if j < 177 then data2176 else data2177)) else (if j < 179 then data2178 else (if j < 180 then data2179 else data2180))) else (if j < 184 then (if j < 182 then data2181 else (if j < 183 then data2182 else data2183)) else (if j < 185 then data2184 else (if j < 186 then data2185 else data2186)))) else (if j < 193 then (if j < 190 then (if j < 188 then data2187 else (if j < 189 then data2188 else data2189)) else (if j < 191 then data2190 else (if j < 192 then data2191 else data2192))) else (if j < 196 then (if j < 194 then data2193 else (if j < 195 then data2194 else data2195)) else (if j < 198 then (if j < 197 then data2196 else data2197) else (if j < 199 then data2198 else data2199))))))))

def srcTableB10 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then src2000 else (if j < 2 then src2001 else src2002)) else (if j < 4 then src2003 else (if j < 5 then src2004 else src2005))) else (if j < 9 then (if j < 7 then src2006 else (if j < 8 then src2007 else src2008)) else (if j < 10 then src2009 else (if j < 11 then src2010 else src2011)))) else (if j < 18 then (if j < 15 then (if j < 13 then src2012 else (if j < 14 then src2013 else src2014)) else (if j < 16 then src2015 else (if j < 17 then src2016 else src2017))) else (if j < 21 then (if j < 19 then src2018 else (if j < 20 then src2019 else src2020)) else (if j < 23 then (if j < 22 then src2021 else src2022) else (if j < 24 then src2023 else src2024))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then src2025 else (if j < 27 then src2026 else src2027)) else (if j < 29 then src2028 else (if j < 30 then src2029 else src2030))) else (if j < 34 then (if j < 32 then src2031 else (if j < 33 then src2032 else src2033)) else (if j < 35 then src2034 else (if j < 36 then src2035 else src2036)))) else (if j < 43 then (if j < 40 then (if j < 38 then src2037 else (if j < 39 then src2038 else src2039)) else (if j < 41 then src2040 else (if j < 42 then src2041 else src2042))) else (if j < 46 then (if j < 44 then src2043 else (if j < 45 then src2044 else src2045)) else (if j < 48 then (if j < 47 then src2046 else src2047) else (if j < 49 then src2048 else src2049)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then src2050 else (if j < 52 then src2051 else src2052)) else (if j < 54 then src2053 else (if j < 55 then src2054 else src2055))) else (if j < 59 then (if j < 57 then src2056 else (if j < 58 then src2057 else src2058)) else (if j < 60 then src2059 else (if j < 61 then src2060 else src2061)))) else (if j < 68 then (if j < 65 then (if j < 63 then src2062 else (if j < 64 then src2063 else src2064)) else (if j < 66 then src2065 else (if j < 67 then src2066 else src2067))) else (if j < 71 then (if j < 69 then src2068 else (if j < 70 then src2069 else src2070)) else (if j < 73 then (if j < 72 then src2071 else src2072) else (if j < 74 then src2073 else src2074))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then src2075 else (if j < 77 then src2076 else src2077)) else (if j < 79 then src2078 else (if j < 80 then src2079 else src2080))) else (if j < 84 then (if j < 82 then src2081 else (if j < 83 then src2082 else src2083)) else (if j < 85 then src2084 else (if j < 86 then src2085 else src2086)))) else (if j < 93 then (if j < 90 then (if j < 88 then src2087 else (if j < 89 then src2088 else src2089)) else (if j < 91 then src2090 else (if j < 92 then src2091 else src2092))) else (if j < 96 then (if j < 94 then src2093 else (if j < 95 then src2094 else src2095)) else (if j < 98 then (if j < 97 then src2096 else src2097) else (if j < 99 then src2098 else src2099))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then src2100 else (if j < 102 then src2101 else src2102)) else (if j < 104 then src2103 else (if j < 105 then src2104 else src2105))) else (if j < 109 then (if j < 107 then src2106 else (if j < 108 then src2107 else src2108)) else (if j < 110 then src2109 else (if j < 111 then src2110 else src2111)))) else (if j < 118 then (if j < 115 then (if j < 113 then src2112 else (if j < 114 then src2113 else src2114)) else (if j < 116 then src2115 else (if j < 117 then src2116 else src2117))) else (if j < 121 then (if j < 119 then src2118 else (if j < 120 then src2119 else src2120)) else (if j < 123 then (if j < 122 then src2121 else src2122) else (if j < 124 then src2123 else src2124))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then src2125 else (if j < 127 then src2126 else src2127)) else (if j < 129 then src2128 else (if j < 130 then src2129 else src2130))) else (if j < 134 then (if j < 132 then src2131 else (if j < 133 then src2132 else src2133)) else (if j < 135 then src2134 else (if j < 136 then src2135 else src2136)))) else (if j < 143 then (if j < 140 then (if j < 138 then src2137 else (if j < 139 then src2138 else src2139)) else (if j < 141 then src2140 else (if j < 142 then src2141 else src2142))) else (if j < 146 then (if j < 144 then src2143 else (if j < 145 then src2144 else src2145)) else (if j < 148 then (if j < 147 then src2146 else src2147) else (if j < 149 then src2148 else src2149)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then src2150 else (if j < 152 then src2151 else src2152)) else (if j < 154 then src2153 else (if j < 155 then src2154 else src2155))) else (if j < 159 then (if j < 157 then src2156 else (if j < 158 then src2157 else src2158)) else (if j < 160 then src2159 else (if j < 161 then src2160 else src2161)))) else (if j < 168 then (if j < 165 then (if j < 163 then src2162 else (if j < 164 then src2163 else src2164)) else (if j < 166 then src2165 else (if j < 167 then src2166 else src2167))) else (if j < 171 then (if j < 169 then src2168 else (if j < 170 then src2169 else src2170)) else (if j < 173 then (if j < 172 then src2171 else src2172) else (if j < 174 then src2173 else src2174))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then src2175 else (if j < 177 then src2176 else src2177)) else (if j < 179 then src2178 else (if j < 180 then src2179 else src2180))) else (if j < 184 then (if j < 182 then src2181 else (if j < 183 then src2182 else src2183)) else (if j < 185 then src2184 else (if j < 186 then src2185 else src2186)))) else (if j < 193 then (if j < 190 then (if j < 188 then src2187 else (if j < 189 then src2188 else src2189)) else (if j < 191 then src2190 else (if j < 192 then src2191 else src2192))) else (if j < 196 then (if j < 194 then src2193 else (if j < 195 then src2194 else src2195)) else (if j < 198 then (if j < 197 then src2196 else src2197) else (if j < 199 then src2198 else src2199))))))))

def dstTableB10 (j : ℕ) : E → W := (if j < 100 then (if j < 50 then (if j < 25 then (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then dst2000 else (if j < 2 then dst2001 else dst2002)) else (if j < 4 then dst2003 else (if j < 5 then dst2004 else dst2005))) else (if j < 9 then (if j < 7 then dst2006 else (if j < 8 then dst2007 else dst2008)) else (if j < 10 then dst2009 else (if j < 11 then dst2010 else dst2011)))) else (if j < 18 then (if j < 15 then (if j < 13 then dst2012 else (if j < 14 then dst2013 else dst2014)) else (if j < 16 then dst2015 else (if j < 17 then dst2016 else dst2017))) else (if j < 21 then (if j < 19 then dst2018 else (if j < 20 then dst2019 else dst2020)) else (if j < 23 then (if j < 22 then dst2021 else dst2022) else (if j < 24 then dst2023 else dst2024))))) else (if j < 37 then (if j < 31 then (if j < 28 then (if j < 26 then dst2025 else (if j < 27 then dst2026 else dst2027)) else (if j < 29 then dst2028 else (if j < 30 then dst2029 else dst2030))) else (if j < 34 then (if j < 32 then dst2031 else (if j < 33 then dst2032 else dst2033)) else (if j < 35 then dst2034 else (if j < 36 then dst2035 else dst2036)))) else (if j < 43 then (if j < 40 then (if j < 38 then dst2037 else (if j < 39 then dst2038 else dst2039)) else (if j < 41 then dst2040 else (if j < 42 then dst2041 else dst2042))) else (if j < 46 then (if j < 44 then dst2043 else (if j < 45 then dst2044 else dst2045)) else (if j < 48 then (if j < 47 then dst2046 else dst2047) else (if j < 49 then dst2048 else dst2049)))))) else (if j < 75 then (if j < 62 then (if j < 56 then (if j < 53 then (if j < 51 then dst2050 else (if j < 52 then dst2051 else dst2052)) else (if j < 54 then dst2053 else (if j < 55 then dst2054 else dst2055))) else (if j < 59 then (if j < 57 then dst2056 else (if j < 58 then dst2057 else dst2058)) else (if j < 60 then dst2059 else (if j < 61 then dst2060 else dst2061)))) else (if j < 68 then (if j < 65 then (if j < 63 then dst2062 else (if j < 64 then dst2063 else dst2064)) else (if j < 66 then dst2065 else (if j < 67 then dst2066 else dst2067))) else (if j < 71 then (if j < 69 then dst2068 else (if j < 70 then dst2069 else dst2070)) else (if j < 73 then (if j < 72 then dst2071 else dst2072) else (if j < 74 then dst2073 else dst2074))))) else (if j < 87 then (if j < 81 then (if j < 78 then (if j < 76 then dst2075 else (if j < 77 then dst2076 else dst2077)) else (if j < 79 then dst2078 else (if j < 80 then dst2079 else dst2080))) else (if j < 84 then (if j < 82 then dst2081 else (if j < 83 then dst2082 else dst2083)) else (if j < 85 then dst2084 else (if j < 86 then dst2085 else dst2086)))) else (if j < 93 then (if j < 90 then (if j < 88 then dst2087 else (if j < 89 then dst2088 else dst2089)) else (if j < 91 then dst2090 else (if j < 92 then dst2091 else dst2092))) else (if j < 96 then (if j < 94 then dst2093 else (if j < 95 then dst2094 else dst2095)) else (if j < 98 then (if j < 97 then dst2096 else dst2097) else (if j < 99 then dst2098 else dst2099))))))) else (if j < 150 then (if j < 125 then (if j < 112 then (if j < 106 then (if j < 103 then (if j < 101 then dst2100 else (if j < 102 then dst2101 else dst2102)) else (if j < 104 then dst2103 else (if j < 105 then dst2104 else dst2105))) else (if j < 109 then (if j < 107 then dst2106 else (if j < 108 then dst2107 else dst2108)) else (if j < 110 then dst2109 else (if j < 111 then dst2110 else dst2111)))) else (if j < 118 then (if j < 115 then (if j < 113 then dst2112 else (if j < 114 then dst2113 else dst2114)) else (if j < 116 then dst2115 else (if j < 117 then dst2116 else dst2117))) else (if j < 121 then (if j < 119 then dst2118 else (if j < 120 then dst2119 else dst2120)) else (if j < 123 then (if j < 122 then dst2121 else dst2122) else (if j < 124 then dst2123 else dst2124))))) else (if j < 137 then (if j < 131 then (if j < 128 then (if j < 126 then dst2125 else (if j < 127 then dst2126 else dst2127)) else (if j < 129 then dst2128 else (if j < 130 then dst2129 else dst2130))) else (if j < 134 then (if j < 132 then dst2131 else (if j < 133 then dst2132 else dst2133)) else (if j < 135 then dst2134 else (if j < 136 then dst2135 else dst2136)))) else (if j < 143 then (if j < 140 then (if j < 138 then dst2137 else (if j < 139 then dst2138 else dst2139)) else (if j < 141 then dst2140 else (if j < 142 then dst2141 else dst2142))) else (if j < 146 then (if j < 144 then dst2143 else (if j < 145 then dst2144 else dst2145)) else (if j < 148 then (if j < 147 then dst2146 else dst2147) else (if j < 149 then dst2148 else dst2149)))))) else (if j < 175 then (if j < 162 then (if j < 156 then (if j < 153 then (if j < 151 then dst2150 else (if j < 152 then dst2151 else dst2152)) else (if j < 154 then dst2153 else (if j < 155 then dst2154 else dst2155))) else (if j < 159 then (if j < 157 then dst2156 else (if j < 158 then dst2157 else dst2158)) else (if j < 160 then dst2159 else (if j < 161 then dst2160 else dst2161)))) else (if j < 168 then (if j < 165 then (if j < 163 then dst2162 else (if j < 164 then dst2163 else dst2164)) else (if j < 166 then dst2165 else (if j < 167 then dst2166 else dst2167))) else (if j < 171 then (if j < 169 then dst2168 else (if j < 170 then dst2169 else dst2170)) else (if j < 173 then (if j < 172 then dst2171 else dst2172) else (if j < 174 then dst2173 else dst2174))))) else (if j < 187 then (if j < 181 then (if j < 178 then (if j < 176 then dst2175 else (if j < 177 then dst2176 else dst2177)) else (if j < 179 then dst2178 else (if j < 180 then dst2179 else dst2180))) else (if j < 184 then (if j < 182 then dst2181 else (if j < 183 then dst2182 else dst2183)) else (if j < 185 then dst2184 else (if j < 186 then dst2185 else dst2186)))) else (if j < 193 then (if j < 190 then (if j < 188 then dst2187 else (if j < 189 then dst2188 else dst2189)) else (if j < 191 then dst2190 else (if j < 192 then dst2191 else dst2192))) else (if j < 196 then (if j < 194 then dst2193 else (if j < 195 then dst2194 else dst2195)) else (if j < 198 then (if j < 197 then dst2196 else dst2197) else (if j < 199 then dst2198 else dst2199))))))))

def caseB10 (i : Fin 200) : Cases := ⟨2000 + i.val,by have := i.isLt; omega⟩
lemma tableB10_valid (i : Fin 200) :
    (lookupB10 i.val).Valid (srcTableB10 i.val) (dstTableB10 i.val) Finset.univ := by
  fin_cases i
  · exact valid_data2000
  · exact valid_data2001
  · exact valid_data2002
  · exact valid_data2003
  · exact valid_data2004
  · exact valid_data2005
  · exact valid_data2006
  · exact valid_data2007
  · exact valid_data2008
  · exact valid_data2009
  · exact valid_data2010
  · exact valid_data2011
  · exact valid_data2012
  · exact valid_data2013
  · exact valid_data2014
  · exact valid_data2015
  · exact valid_data2016
  · exact valid_data2017
  · exact valid_data2018
  · exact valid_data2019
  · exact valid_data2020
  · exact valid_data2021
  · exact valid_data2022
  · exact valid_data2023
  · exact valid_data2024
  · exact valid_data2025
  · exact valid_data2026
  · exact valid_data2027
  · exact valid_data2028
  · exact valid_data2029
  · exact valid_data2030
  · exact valid_data2031
  · exact valid_data2032
  · exact valid_data2033
  · exact valid_data2034
  · exact valid_data2035
  · exact valid_data2036
  · exact valid_data2037
  · exact valid_data2038
  · exact valid_data2039
  · exact valid_data2040
  · exact valid_data2041
  · exact valid_data2042
  · exact valid_data2043
  · exact valid_data2044
  · exact valid_data2045
  · exact valid_data2046
  · exact valid_data2047
  · exact valid_data2048
  · exact valid_data2049
  · exact valid_data2050
  · exact valid_data2051
  · exact valid_data2052
  · exact valid_data2053
  · exact valid_data2054
  · exact valid_data2055
  · exact valid_data2056
  · exact valid_data2057
  · exact valid_data2058
  · exact valid_data2059
  · exact valid_data2060
  · exact valid_data2061
  · exact valid_data2062
  · exact valid_data2063
  · exact valid_data2064
  · exact valid_data2065
  · exact valid_data2066
  · exact valid_data2067
  · exact valid_data2068
  · exact valid_data2069
  · exact valid_data2070
  · exact valid_data2071
  · exact valid_data2072
  · exact valid_data2073
  · exact valid_data2074
  · exact valid_data2075
  · exact valid_data2076
  · exact valid_data2077
  · exact valid_data2078
  · exact valid_data2079
  · exact valid_data2080
  · exact valid_data2081
  · exact valid_data2082
  · exact valid_data2083
  · exact valid_data2084
  · exact valid_data2085
  · exact valid_data2086
  · exact valid_data2087
  · exact valid_data2088
  · exact valid_data2089
  · exact valid_data2090
  · exact valid_data2091
  · exact valid_data2092
  · exact valid_data2093
  · exact valid_data2094
  · exact valid_data2095
  · exact valid_data2096
  · exact valid_data2097
  · exact valid_data2098
  · exact valid_data2099
  · exact valid_data2100
  · exact valid_data2101
  · exact valid_data2102
  · exact valid_data2103
  · exact valid_data2104
  · exact valid_data2105
  · exact valid_data2106
  · exact valid_data2107
  · exact valid_data2108
  · exact valid_data2109
  · exact valid_data2110
  · exact valid_data2111
  · exact valid_data2112
  · exact valid_data2113
  · exact valid_data2114
  · exact valid_data2115
  · exact valid_data2116
  · exact valid_data2117
  · exact valid_data2118
  · exact valid_data2119
  · exact valid_data2120
  · exact valid_data2121
  · exact valid_data2122
  · exact valid_data2123
  · exact valid_data2124
  · exact valid_data2125
  · exact valid_data2126
  · exact valid_data2127
  · exact valid_data2128
  · exact valid_data2129
  · exact valid_data2130
  · exact valid_data2131
  · exact valid_data2132
  · exact valid_data2133
  · exact valid_data2134
  · exact valid_data2135
  · exact valid_data2136
  · exact valid_data2137
  · exact valid_data2138
  · exact valid_data2139
  · exact valid_data2140
  · exact valid_data2141
  · exact valid_data2142
  · exact valid_data2143
  · exact valid_data2144
  · exact valid_data2145
  · exact valid_data2146
  · exact valid_data2147
  · exact valid_data2148
  · exact valid_data2149
  · exact valid_data2150
  · exact valid_data2151
  · exact valid_data2152
  · exact valid_data2153
  · exact valid_data2154
  · exact valid_data2155
  · exact valid_data2156
  · exact valid_data2157
  · exact valid_data2158
  · exact valid_data2159
  · exact valid_data2160
  · exact valid_data2161
  · exact valid_data2162
  · exact valid_data2163
  · exact valid_data2164
  · exact valid_data2165
  · exact valid_data2166
  · exact valid_data2167
  · exact valid_data2168
  · exact valid_data2169
  · exact valid_data2170
  · exact valid_data2171
  · exact valid_data2172
  · exact valid_data2173
  · exact valid_data2174
  · exact valid_data2175
  · exact valid_data2176
  · exact valid_data2177
  · exact valid_data2178
  · exact valid_data2179
  · exact valid_data2180
  · exact valid_data2181
  · exact valid_data2182
  · exact valid_data2183
  · exact valid_data2184
  · exact valid_data2185
  · exact valid_data2186
  · exact valid_data2187
  · exact valid_data2188
  · exact valid_data2189
  · exact valid_data2190
  · exact valid_data2191
  · exact valid_data2192
  · exact valid_data2193
  · exact valid_data2194
  · exact valid_data2195
  · exact valid_data2196
  · exact valid_data2197
  · exact valid_data2198
  · exact valid_data2199

lemma srcB10_row : ∀ (i : Fin 200) (e : E),
    srcTableB10 i.val e = caseSource (caseB10 i) e := by decide +kernel

lemma dstB10_row : ∀ (i : Fin 200) (e : E),
    dstTableB10 i.val e = caseTarget (caseB10 i) e := by decide +kernel

lemma sizeB10 : ∀ i : Fin 200, (lookupB10 i.val).size ≤ 5 →
    (lookupB10 i.val).size = 2 ∧
      (⟨caseKey (caseB10 i),caseKey_lt (caseB10 i)⟩ : Fin 62208) ∈ good := by decide +kernel
lemma certificateB10 (i : Fin 200) : Certificate (caseB10 i) := by
  refine ⟨lookupB10 i.val,?_,sizeB10 i⟩
  have hv := tableB10_valid i
  rw [funext (srcB10_row i),funext (dstB10_row i)] at hv
  exact hv
lemma certificateInterval10 : FiniteIntervals.Covers CertificateAt 2000 2200 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 2000 200 (fun i _ => certificateB10 i)
#print axioms certificateInterval10
end Erdos184Work.FiveRows3
