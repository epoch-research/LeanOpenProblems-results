import Submission.FiveCertificates2Base

/-! Independent circuit certificates for one interval of five-color cases. -/
namespace Erdos184Work.FiveRows2
open LabelKernel Erdos184Serial
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false

def src2000 : E → W := ![2,6,5,3,4,8,2,14,3,16,18,4,5,28,14,26,6,16,26,38,8,28,18,38]
def dst2000 : E → W := ![6,5,3,4,8,2,14,3,16,18,2,5,28,14,26,4,16,26,38,6,28,18,38,8]
def cycle2000_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle2000_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2000_2 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle2000_3 : CycleData E W := ⟨2,![5,20,21,10],![2,8,28,18]⟩
def cycle2000_4 : CycleData E W := ⟨2,![7,14,17,8],![3,14,26,16]⟩
def cycle2000_5 : CycleData E W := ⟨2,![16,9,22,19],![6,16,18,38]⟩
def data2000 : PartitionData E W := ⟨6,![cycle2000_0,cycle2000_1,cycle2000_2,cycle2000_3,cycle2000_4,cycle2000_5]⟩
lemma valid_data2000 : data2000.Valid src2000 dst2000 Finset.univ := by decide +kernel

def src2001 : E → W := ![2,6,5,3,4,8,2,14,3,16,18,4,5,28,14,26,6,16,38,26,8,18,28,38]
def dst2001 : E → W := ![6,5,3,4,8,2,14,3,16,18,2,5,28,14,26,4,16,38,26,6,18,28,38,8]
def cycle2001_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle2001_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2001_2 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle2001_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle2001_4 : CycleData E W := ⟨3,![7,14,19,16,8],![3,14,26,6,16]⟩
def cycle2001_5 : CycleData E W := ⟨2,![9,21,22,17],![16,18,28,38]⟩
def data2001 : PartitionData E W := ⟨6,![cycle2001_0,cycle2001_1,cycle2001_2,cycle2001_3,cycle2001_4,cycle2001_5]⟩
lemma valid_data2001 : data2001.Valid src2001 dst2001 Finset.univ := by decide +kernel

def src2002 : E → W := ![2,6,5,3,4,8,2,14,3,16,18,4,5,28,14,26,6,16,38,26,8,18,38,28]
def dst2002 : E → W := ![6,5,3,4,8,2,14,3,16,18,2,5,28,14,26,4,16,38,26,6,18,38,28,8]
def cycle2002_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,6,5,3,14]⟩
def cycle2002_1 : CycleData E W := ⟨3,![3,15,19,16,8],![3,4,26,6,16]⟩
def cycle2002_2 : CycleData E W := ⟨2,![4,23,12,11],![4,8,28,5]⟩
def cycle2002_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle2002_4 : CycleData E W := ⟨1,![9,21,17],![16,18,38]⟩
def cycle2002_5 : CycleData E W := ⟨2,![13,22,18,14],![14,28,38,26]⟩
def data2002 : PartitionData E W := ⟨6,![cycle2002_0,cycle2002_1,cycle2002_2,cycle2002_3,cycle2002_4,cycle2002_5]⟩
lemma valid_data2002 : data2002.Valid src2002 dst2002 Finset.univ := by decide +kernel

def src2003 : E → W := ![2,6,5,3,4,8,2,14,3,16,18,4,5,28,14,26,6,16,38,26,8,28,18,38]
def dst2003 : E → W := ![6,5,3,4,8,2,14,3,16,18,2,5,28,14,26,4,16,38,26,6,28,18,38,8]
def cycle2003_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle2003_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2003_2 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle2003_3 : CycleData E W := ⟨2,![5,20,21,10],![2,8,28,18]⟩
def cycle2003_4 : CycleData E W := ⟨3,![7,14,19,16,8],![3,14,26,6,16]⟩
def cycle2003_5 : CycleData E W := ⟨1,![9,22,17],![16,18,38]⟩
def data2003 : PartitionData E W := ⟨6,![cycle2003_0,cycle2003_1,cycle2003_2,cycle2003_3,cycle2003_4,cycle2003_5]⟩
lemma valid_data2003 : data2003.Valid src2003 dst2003 Finset.univ := by decide +kernel

def src2004 : E → W := ![2,6,5,3,4,8,2,14,3,16,18,4,5,28,14,26,6,26,16,38,8,18,28,38]
def dst2004 : E → W := ![6,5,3,4,8,2,14,3,16,18,2,5,28,14,26,4,26,16,38,6,18,28,38,8]
def cycle2004_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle2004_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2004_2 : CycleData E W := ⟨3,![4,23,19,16,15],![4,8,38,6,26]⟩
def cycle2004_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle2004_4 : CycleData E W := ⟨2,![7,14,17,8],![3,14,26,16]⟩
def cycle2004_5 : CycleData E W := ⟨2,![9,21,22,18],![16,18,28,38]⟩
def data2004 : PartitionData E W := ⟨6,![cycle2004_0,cycle2004_1,cycle2004_2,cycle2004_3,cycle2004_4,cycle2004_5]⟩
lemma valid_data2004 : data2004.Valid src2004 dst2004 Finset.univ := by decide +kernel

def src2005 : E → W := ![2,6,5,3,4,8,2,14,3,16,18,4,5,28,14,26,6,26,16,38,8,18,38,28]
def dst2005 : E → W := ![6,5,3,4,8,2,14,3,16,18,2,5,28,14,26,4,26,16,38,6,18,38,28,8]
def cycle2005_0 : CycleData E W := ⟨3,![0,1,2,7,6],![2,6,5,3,14]⟩
def cycle2005_1 : CycleData E W := ⟨2,![3,15,17,8],![3,4,26,16]⟩
def cycle2005_2 : CycleData E W := ⟨2,![4,23,12,11],![4,8,28,5]⟩
def cycle2005_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle2005_4 : CycleData E W := ⟨1,![9,21,18],![16,18,38]⟩
def cycle2005_5 : CycleData E W := ⟨3,![16,14,13,22,19],![6,26,14,28,38]⟩
def data2005 : PartitionData E W := ⟨6,![cycle2005_0,cycle2005_1,cycle2005_2,cycle2005_3,cycle2005_4,cycle2005_5]⟩
lemma valid_data2005 : data2005.Valid src2005 dst2005 Finset.univ := by decide +kernel

def src2006 : E → W := ![2,6,5,3,4,8,2,14,3,16,18,4,5,28,14,26,6,26,16,38,8,28,18,38]
def dst2006 : E → W := ![6,5,3,4,8,2,14,3,16,18,2,5,28,14,26,4,26,16,38,6,28,18,38,8]
def cycle2006_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle2006_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2006_2 : CycleData E W := ⟨3,![4,23,19,16,15],![4,8,38,6,26]⟩
def cycle2006_3 : CycleData E W := ⟨2,![5,20,21,10],![2,8,28,18]⟩
def cycle2006_4 : CycleData E W := ⟨2,![7,14,17,8],![3,14,26,16]⟩
def cycle2006_5 : CycleData E W := ⟨1,![9,22,18],![16,18,38]⟩
def data2006 : PartitionData E W := ⟨6,![cycle2006_0,cycle2006_1,cycle2006_2,cycle2006_3,cycle2006_4,cycle2006_5]⟩
lemma valid_data2006 : data2006.Valid src2006 dst2006 Finset.univ := by decide +kernel

def src2007 : E → W := ![2,6,5,3,4,8,2,14,3,18,16,4,5,28,14,26,6,16,26,38,8,18,28,38]
def dst2007 : E → W := ![6,5,3,4,8,2,14,3,18,16,2,5,28,14,26,4,16,26,38,6,18,28,38,8]
def cycle2007_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2007_1 : CycleData E W := ⟨2,![1,19,22,12],![5,6,38,28]⟩
def cycle2007_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2007_3 : CycleData E W := ⟨3,![5,4,15,14,6],![2,8,4,26,14]⟩
def cycle2007_4 : CycleData E W := ⟨2,![7,13,21,8],![3,14,28,18]⟩
def cycle2007_5 : CycleData E W := ⟨3,![20,9,17,18,23],![8,18,16,26,38]⟩
def data2007 : PartitionData E W := ⟨6,![cycle2007_0,cycle2007_1,cycle2007_2,cycle2007_3,cycle2007_4,cycle2007_5]⟩
lemma valid_data2007 : data2007.Valid src2007 dst2007 Finset.univ := by decide +kernel

def src2008 : E → W := ![2,6,5,3,4,8,2,14,3,18,16,4,5,28,14,26,6,16,26,38,8,18,38,28]
def dst2008 : E → W := ![6,5,3,4,8,2,14,3,18,16,2,5,28,14,26,4,16,26,38,6,18,38,28,8]
def cycle2008_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2008_1 : CycleData E W := ⟨2,![1,19,22,12],![5,6,38,28]⟩
def cycle2008_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2008_3 : CycleData E W := ⟨3,![5,4,15,14,6],![2,8,4,26,14]⟩
def cycle2008_4 : CycleData E W := ⟨3,![7,13,23,20,8],![3,14,28,8,18]⟩
def cycle2008_5 : CycleData E W := ⟨2,![9,21,18,17],![16,18,38,26]⟩
def data2008 : PartitionData E W := ⟨6,![cycle2008_0,cycle2008_1,cycle2008_2,cycle2008_3,cycle2008_4,cycle2008_5]⟩
lemma valid_data2008 : data2008.Valid src2008 dst2008 Finset.univ := by decide +kernel

def src2009 : E → W := ![2,6,5,3,4,8,2,14,3,18,16,4,5,28,14,26,6,16,26,38,8,28,18,38]
def dst2009 : E → W := ![6,5,3,4,8,2,14,3,18,16,2,5,28,14,26,4,16,26,38,6,28,18,38,8]
def cycle2009_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2009_1 : CycleData E W := ⟨3,![1,19,22,21,12],![5,6,38,18,28]⟩
def cycle2009_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2009_3 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle2009_4 : CycleData E W := ⟨2,![5,20,13,6],![2,8,28,14]⟩
def cycle2009_5 : CycleData E W := ⟨3,![7,14,17,9,8],![3,14,26,16,18]⟩
def data2009 : PartitionData E W := ⟨6,![cycle2009_0,cycle2009_1,cycle2009_2,cycle2009_3,cycle2009_4,cycle2009_5]⟩
lemma valid_data2009 : data2009.Valid src2009 dst2009 Finset.univ := by decide +kernel

def src2010 : E → W := ![2,6,5,3,4,8,2,14,3,18,16,4,5,28,14,26,6,16,38,26,8,18,28,38]
def dst2010 : E → W := ![6,5,3,4,8,2,14,3,18,16,2,5,28,14,26,4,16,38,26,6,18,28,38,8]
def cycle2010_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2010_1 : CycleData E W := ⟨3,![1,19,14,13,12],![5,6,26,14,28]⟩
def cycle2010_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2010_3 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle2010_4 : CycleData E W := ⟨3,![5,20,8,7,6],![2,8,18,3,14]⟩
def cycle2010_5 : CycleData E W := ⟨2,![9,21,22,17],![16,18,28,38]⟩
def data2010 : PartitionData E W := ⟨6,![cycle2010_0,cycle2010_1,cycle2010_2,cycle2010_3,cycle2010_4,cycle2010_5]⟩
lemma valid_data2010 : data2010.Valid src2010 dst2010 Finset.univ := by decide +kernel

def src2011 : E → W := ![2,6,5,3,4,8,2,14,3,18,16,4,5,28,14,26,6,16,38,26,8,18,38,28]
def dst2011 : E → W := ![6,5,3,4,8,2,14,3,18,16,2,5,28,14,26,4,16,38,26,6,18,38,28,8]
def cycle2011_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2011_1 : CycleData E W := ⟨3,![2,1,19,14,7],![3,5,6,26,14]⟩
def cycle2011_2 : CycleData E W := ⟨2,![3,4,20,8],![3,4,8,18]⟩
def cycle2011_3 : CycleData E W := ⟨2,![5,23,13,6],![2,8,28,14]⟩
def cycle2011_4 : CycleData E W := ⟨1,![9,21,17],![16,18,38]⟩
def cycle2011_5 : CycleData E W := ⟨3,![11,12,22,18,15],![4,5,28,38,26]⟩
def data2011 : PartitionData E W := ⟨6,![cycle2011_0,cycle2011_1,cycle2011_2,cycle2011_3,cycle2011_4,cycle2011_5]⟩
lemma valid_data2011 : data2011.Valid src2011 dst2011 Finset.univ := by decide +kernel

def src2012 : E → W := ![2,6,5,3,4,8,2,14,3,18,16,4,5,28,14,26,6,16,38,26,8,28,18,38]
def dst2012 : E → W := ![6,5,3,4,8,2,14,3,18,16,2,5,28,14,26,4,16,38,26,6,28,18,38,8]
def cycle2012_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2012_1 : CycleData E W := ⟨3,![2,1,19,14,7],![3,5,6,26,14]⟩
def cycle2012_2 : CycleData E W := ⟨3,![3,11,12,21,8],![3,4,5,28,18]⟩
def cycle2012_3 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle2012_4 : CycleData E W := ⟨2,![5,20,13,6],![2,8,28,14]⟩
def cycle2012_5 : CycleData E W := ⟨1,![9,22,17],![16,18,38]⟩
def data2012 : PartitionData E W := ⟨6,![cycle2012_0,cycle2012_1,cycle2012_2,cycle2012_3,cycle2012_4,cycle2012_5]⟩
lemma valid_data2012 : data2012.Valid src2012 dst2012 Finset.univ := by decide +kernel

def src2013 : E → W := ![2,6,5,3,4,8,2,14,3,18,16,4,5,28,14,26,6,26,16,38,8,18,28,38]
def dst2013 : E → W := ![6,5,3,4,8,2,14,3,18,16,2,5,28,14,26,4,26,16,38,6,18,28,38,8]
def cycle2013_0 : CycleData E W := ⟨2,![0,16,14,6],![2,6,26,14]⟩
def cycle2013_1 : CycleData E W := ⟨2,![1,19,22,12],![5,6,38,28]⟩
def cycle2013_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2013_3 : CycleData E W := ⟨3,![5,4,15,17,10],![2,8,4,26,16]⟩
def cycle2013_4 : CycleData E W := ⟨2,![7,13,21,8],![3,14,28,18]⟩
def cycle2013_5 : CycleData E W := ⟨2,![20,9,18,23],![8,18,16,38]⟩
def data2013 : PartitionData E W := ⟨6,![cycle2013_0,cycle2013_1,cycle2013_2,cycle2013_3,cycle2013_4,cycle2013_5]⟩
lemma valid_data2013 : data2013.Valid src2013 dst2013 Finset.univ := by decide +kernel

def src2014 : E → W := ![2,6,5,3,4,8,2,14,3,18,16,4,5,28,14,26,6,26,16,38,8,18,38,28]
def dst2014 : E → W := ![6,5,3,4,8,2,14,3,18,16,2,5,28,14,26,4,26,16,38,6,18,38,28,8]
def cycle2014_0 : CycleData E W := ⟨2,![0,16,14,6],![2,6,26,14]⟩
def cycle2014_1 : CycleData E W := ⟨2,![1,19,22,12],![5,6,38,28]⟩
def cycle2014_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2014_3 : CycleData E W := ⟨3,![5,4,15,17,10],![2,8,4,26,16]⟩
def cycle2014_4 : CycleData E W := ⟨3,![7,13,23,20,8],![3,14,28,8,18]⟩
def cycle2014_5 : CycleData E W := ⟨1,![9,21,18],![16,18,38]⟩
def data2014 : PartitionData E W := ⟨6,![cycle2014_0,cycle2014_1,cycle2014_2,cycle2014_3,cycle2014_4,cycle2014_5]⟩
lemma valid_data2014 : data2014.Valid src2014 dst2014 Finset.univ := by decide +kernel

def src2015 : E → W := ![2,6,5,3,4,8,2,14,3,18,16,4,5,28,14,26,6,26,16,38,8,28,18,38]
def dst2015 : E → W := ![6,5,3,4,8,2,14,3,18,16,2,5,28,14,26,4,26,16,38,6,28,18,38,8]
def cycle2015_0 : CycleData E W := ⟨2,![0,16,14,6],![2,6,26,14]⟩
def cycle2015_1 : CycleData E W := ⟨3,![1,19,23,20,12],![5,6,38,8,28]⟩
def cycle2015_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2015_3 : CycleData E W := ⟨3,![5,4,15,17,10],![2,8,4,26,16]⟩
def cycle2015_4 : CycleData E W := ⟨2,![7,13,21,8],![3,14,28,18]⟩
def cycle2015_5 : CycleData E W := ⟨1,![9,22,18],![16,18,38]⟩
def data2015 : PartitionData E W := ⟨6,![cycle2015_0,cycle2015_1,cycle2015_2,cycle2015_3,cycle2015_4,cycle2015_5]⟩
lemma valid_data2015 : data2015.Valid src2015 dst2015 Finset.univ := by decide +kernel

def src2016 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,5,28,14,26,6,16,26,38,8,18,28,38]
def dst2016 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,5,28,14,26,4,16,26,38,6,18,28,38,8]
def cycle2016_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle2016_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2016_2 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle2016_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle2016_4 : CycleData E W := ⟨1,![7,17,14],![14,16,26]⟩
def cycle2016_5 : CycleData E W := ⟨4,![8,16,19,22,21,9],![3,16,6,38,28,18]⟩
def data2016 : PartitionData E W := ⟨6,![cycle2016_0,cycle2016_1,cycle2016_2,cycle2016_3,cycle2016_4,cycle2016_5]⟩
lemma valid_data2016 : data2016.Valid src2016 dst2016 Finset.univ := by decide +kernel

def src2017 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,5,28,14,26,6,16,26,38,8,18,38,28]
def dst2017 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,5,28,14,26,4,16,26,38,6,18,38,28,8]
def cycle2017_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle2017_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2017_2 : CycleData E W := ⟨3,![4,23,22,18,15],![4,8,28,38,26]⟩
def cycle2017_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle2017_4 : CycleData E W := ⟨1,![7,17,14],![14,16,26]⟩
def cycle2017_5 : CycleData E W := ⟨3,![8,16,19,21,9],![3,16,6,38,18]⟩
def data2017 : PartitionData E W := ⟨6,![cycle2017_0,cycle2017_1,cycle2017_2,cycle2017_3,cycle2017_4,cycle2017_5]⟩
lemma valid_data2017 : data2017.Valid src2017 dst2017 Finset.univ := by decide +kernel

def src2018 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,5,28,14,26,6,16,26,38,8,28,18,38]
def dst2018 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,5,28,14,26,4,16,26,38,6,28,18,38,8]
def cycle2018_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle2018_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2018_2 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle2018_3 : CycleData E W := ⟨2,![5,20,21,10],![2,8,28,18]⟩
def cycle2018_4 : CycleData E W := ⟨1,![7,17,14],![14,16,26]⟩
def cycle2018_5 : CycleData E W := ⟨3,![8,16,19,22,9],![3,16,6,38,18]⟩
def data2018 : PartitionData E W := ⟨6,![cycle2018_0,cycle2018_1,cycle2018_2,cycle2018_3,cycle2018_4,cycle2018_5]⟩
lemma valid_data2018 : data2018.Valid src2018 dst2018 Finset.univ := by decide +kernel

def src2019 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,5,28,14,26,6,16,38,26,8,18,28,38]
def dst2019 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,5,28,14,26,4,16,38,26,6,18,28,38,8]
def cycle2019_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle2019_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2019_2 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle2019_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle2019_4 : CycleData E W := ⟨2,![16,7,14,19],![6,16,14,26]⟩
def cycle2019_5 : CycleData E W := ⟨3,![8,17,22,21,9],![3,16,38,28,18]⟩
def data2019 : PartitionData E W := ⟨6,![cycle2019_0,cycle2019_1,cycle2019_2,cycle2019_3,cycle2019_4,cycle2019_5]⟩
lemma valid_data2019 : data2019.Valid src2019 dst2019 Finset.univ := by decide +kernel

def src2020 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,5,28,14,26,6,16,38,26,8,18,38,28]
def dst2020 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,5,28,14,26,4,16,38,26,6,18,38,28,8]
def cycle2020_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle2020_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2020_2 : CycleData E W := ⟨3,![4,23,22,18,15],![4,8,28,38,26]⟩
def cycle2020_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle2020_4 : CycleData E W := ⟨2,![16,7,14,19],![6,16,14,26]⟩
def cycle2020_5 : CycleData E W := ⟨2,![8,17,21,9],![3,16,38,18]⟩
def data2020 : PartitionData E W := ⟨6,![cycle2020_0,cycle2020_1,cycle2020_2,cycle2020_3,cycle2020_4,cycle2020_5]⟩
lemma valid_data2020 : data2020.Valid src2020 dst2020 Finset.univ := by decide +kernel

def src2021 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,5,28,14,26,6,16,38,26,8,28,18,38]
def dst2021 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,5,28,14,26,4,16,38,26,6,28,18,38,8]
def cycle2021_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle2021_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2021_2 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle2021_3 : CycleData E W := ⟨2,![5,20,21,10],![2,8,28,18]⟩
def cycle2021_4 : CycleData E W := ⟨2,![16,7,14,19],![6,16,14,26]⟩
def cycle2021_5 : CycleData E W := ⟨2,![8,17,22,9],![3,16,38,18]⟩
def data2021 : PartitionData E W := ⟨6,![cycle2021_0,cycle2021_1,cycle2021_2,cycle2021_3,cycle2021_4,cycle2021_5]⟩
lemma valid_data2021 : data2021.Valid src2021 dst2021 Finset.univ := by decide +kernel

def src2022 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,5,28,14,26,6,26,16,38,8,18,28,38]
def dst2022 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,5,28,14,26,4,26,16,38,6,18,28,38,8]
def cycle2022_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle2022_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2022_2 : CycleData E W := ⟨3,![4,23,19,16,15],![4,8,38,6,26]⟩
def cycle2022_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle2022_4 : CycleData E W := ⟨1,![7,17,14],![14,16,26]⟩
def cycle2022_5 : CycleData E W := ⟨3,![8,18,22,21,9],![3,16,38,28,18]⟩
def data2022 : PartitionData E W := ⟨6,![cycle2022_0,cycle2022_1,cycle2022_2,cycle2022_3,cycle2022_4,cycle2022_5]⟩
lemma valid_data2022 : data2022.Valid src2022 dst2022 Finset.univ := by decide +kernel

def src2023 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,5,28,14,26,6,26,16,38,8,18,38,28]
def dst2023 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,5,28,14,26,4,26,16,38,6,18,38,28,8]
def cycle2023_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle2023_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2023_2 : CycleData E W := ⟨4,![4,23,22,19,16,15],![4,8,28,38,6,26]⟩
def cycle2023_3 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle2023_4 : CycleData E W := ⟨1,![7,17,14],![14,16,26]⟩
def cycle2023_5 : CycleData E W := ⟨2,![8,18,21,9],![3,16,38,18]⟩
def data2023 : PartitionData E W := ⟨6,![cycle2023_0,cycle2023_1,cycle2023_2,cycle2023_3,cycle2023_4,cycle2023_5]⟩
lemma valid_data2023 : data2023.Valid src2023 dst2023 Finset.univ := by decide +kernel

def src2024 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,5,28,14,26,6,26,16,38,8,28,18,38]
def dst2024 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,5,28,14,26,4,26,16,38,6,28,18,38,8]
def cycle2024_0 : CycleData E W := ⟨3,![0,1,12,13,6],![2,6,5,28,14]⟩
def cycle2024_1 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2024_2 : CycleData E W := ⟨3,![4,23,19,16,15],![4,8,38,6,26]⟩
def cycle2024_3 : CycleData E W := ⟨2,![5,20,21,10],![2,8,28,18]⟩
def cycle2024_4 : CycleData E W := ⟨1,![7,17,14],![14,16,26]⟩
def cycle2024_5 : CycleData E W := ⟨2,![8,18,22,9],![3,16,38,18]⟩
def data2024 : PartitionData E W := ⟨6,![cycle2024_0,cycle2024_1,cycle2024_2,cycle2024_3,cycle2024_4,cycle2024_5]⟩
lemma valid_data2024 : data2024.Valid src2024 dst2024 Finset.univ := by decide +kernel

def src2025 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,16,26,38,8,18,28,38]
def dst2025 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,16,26,38,6,18,28,38,8]
def cycle2025_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle2025_1 : CycleData E W := ⟨2,![1,19,18,14],![5,6,38,26]⟩
def cycle2025_2 : CycleData E W := ⟨2,![2,13,21,9],![3,5,28,18]⟩
def cycle2025_3 : CycleData E W := ⟨2,![3,15,17,8],![3,4,26,16]⟩
def cycle2025_4 : CycleData E W := ⟨3,![4,23,22,12,11],![4,8,38,28,14]⟩
def cycle2025_5 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def data2025 : PartitionData E W := ⟨6,![cycle2025_0,cycle2025_1,cycle2025_2,cycle2025_3,cycle2025_4,cycle2025_5]⟩
lemma valid_data2025 : data2025.Valid src2025 dst2025 Finset.univ := by decide +kernel

def src2026 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,16,26,38,8,18,38,28]
def dst2026 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,16,26,38,6,18,38,28,8]
def cycle2026_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle2026_1 : CycleData E W := ⟨2,![1,19,18,14],![5,6,38,26]⟩
def cycle2026_2 : CycleData E W := ⟨3,![2,13,22,21,9],![3,5,28,38,18]⟩
def cycle2026_3 : CycleData E W := ⟨2,![3,15,17,8],![3,4,26,16]⟩
def cycle2026_4 : CycleData E W := ⟨2,![4,23,12,11],![4,8,28,14]⟩
def cycle2026_5 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def data2026 : PartitionData E W := ⟨6,![cycle2026_0,cycle2026_1,cycle2026_2,cycle2026_3,cycle2026_4,cycle2026_5]⟩
lemma valid_data2026 : data2026.Valid src2026 dst2026 Finset.univ := by decide +kernel

def src2027 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,16,26,38,8,28,18,38]
def dst2027 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,16,26,38,6,28,18,38,8]
def cycle2027_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle2027_1 : CycleData E W := ⟨2,![1,19,18,14],![5,6,38,26]⟩
def cycle2027_2 : CycleData E W := ⟨2,![2,13,21,9],![3,5,28,18]⟩
def cycle2027_3 : CycleData E W := ⟨2,![3,15,17,8],![3,4,26,16]⟩
def cycle2027_4 : CycleData E W := ⟨2,![4,20,12,11],![4,8,28,14]⟩
def cycle2027_5 : CycleData E W := ⟨2,![5,23,22,10],![2,8,38,18]⟩
def data2027 : PartitionData E W := ⟨6,![cycle2027_0,cycle2027_1,cycle2027_2,cycle2027_3,cycle2027_4,cycle2027_5]⟩
lemma valid_data2027 : data2027.Valid src2027 dst2027 Finset.univ := by decide +kernel

def src2028 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,16,38,26,8,18,28,38]
def dst2028 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,16,38,26,6,18,28,38,8]
def cycle2028_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle2028_1 : CycleData E W := ⟨1,![1,19,14],![5,6,26]⟩
def cycle2028_2 : CycleData E W := ⟨3,![2,13,12,11,3],![3,5,28,14,4]⟩
def cycle2028_3 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle2028_4 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle2028_5 : CycleData E W := ⟨3,![8,17,22,21,9],![3,16,38,28,18]⟩
def data2028 : PartitionData E W := ⟨6,![cycle2028_0,cycle2028_1,cycle2028_2,cycle2028_3,cycle2028_4,cycle2028_5]⟩
lemma valid_data2028 : data2028.Valid src2028 dst2028 Finset.univ := by decide +kernel

def src2029 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,16,38,26,8,18,38,28]
def dst2029 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,16,38,26,6,18,38,28,8]
def cycle2029_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle2029_1 : CycleData E W := ⟨1,![1,19,14],![5,6,26]⟩
def cycle2029_2 : CycleData E W := ⟨3,![2,13,12,11,3],![3,5,28,14,4]⟩
def cycle2029_3 : CycleData E W := ⟨3,![4,23,22,18,15],![4,8,28,38,26]⟩
def cycle2029_4 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle2029_5 : CycleData E W := ⟨2,![8,17,21,9],![3,16,38,18]⟩
def data2029 : PartitionData E W := ⟨6,![cycle2029_0,cycle2029_1,cycle2029_2,cycle2029_3,cycle2029_4,cycle2029_5]⟩
lemma valid_data2029 : data2029.Valid src2029 dst2029 Finset.univ := by decide +kernel

def src2030 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,16,38,26,8,28,18,38]
def dst2030 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,16,38,26,6,28,18,38,8]
def cycle2030_0 : CycleData E W := ⟨2,![0,16,7,6],![2,6,16,14]⟩
def cycle2030_1 : CycleData E W := ⟨1,![1,19,14],![5,6,26]⟩
def cycle2030_2 : CycleData E W := ⟨3,![2,13,12,11,3],![3,5,28,14,4]⟩
def cycle2030_3 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle2030_4 : CycleData E W := ⟨2,![5,20,21,10],![2,8,28,18]⟩
def cycle2030_5 : CycleData E W := ⟨2,![8,17,22,9],![3,16,38,18]⟩
def data2030 : PartitionData E W := ⟨6,![cycle2030_0,cycle2030_1,cycle2030_2,cycle2030_3,cycle2030_4,cycle2030_5]⟩
lemma valid_data2030 : data2030.Valid src2030 dst2030 Finset.univ := by decide +kernel

def src2031 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,26,16,38,8,18,28,38]
def dst2031 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,26,16,38,6,18,28,38,8]
def cycle2031_0 : CycleData E W := ⟨3,![0,19,18,7,6],![2,6,38,16,14]⟩
def cycle2031_1 : CycleData E W := ⟨1,![1,16,14],![5,6,26]⟩
def cycle2031_2 : CycleData E W := ⟨2,![2,13,21,9],![3,5,28,18]⟩
def cycle2031_3 : CycleData E W := ⟨2,![3,15,17,8],![3,4,26,16]⟩
def cycle2031_4 : CycleData E W := ⟨3,![4,23,22,12,11],![4,8,38,28,14]⟩
def cycle2031_5 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def data2031 : PartitionData E W := ⟨6,![cycle2031_0,cycle2031_1,cycle2031_2,cycle2031_3,cycle2031_4,cycle2031_5]⟩
lemma valid_data2031 : data2031.Valid src2031 dst2031 Finset.univ := by decide +kernel

def src2032 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,26,16,38,8,18,38,28]
def dst2032 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,26,16,38,6,18,38,28,8]
def cycle2032_0 : CycleData E W := ⟨3,![0,16,17,7,6],![2,6,26,16,14]⟩
def cycle2032_1 : CycleData E W := ⟨2,![1,19,22,13],![5,6,38,28]⟩
def cycle2032_2 : CycleData E W := ⟨2,![2,14,15,3],![3,5,26,4]⟩
def cycle2032_3 : CycleData E W := ⟨2,![4,23,12,11],![4,8,28,14]⟩
def cycle2032_4 : CycleData E W := ⟨1,![5,20,10],![2,8,18]⟩
def cycle2032_5 : CycleData E W := ⟨2,![8,18,21,9],![3,16,38,18]⟩
def data2032 : PartitionData E W := ⟨6,![cycle2032_0,cycle2032_1,cycle2032_2,cycle2032_3,cycle2032_4,cycle2032_5]⟩
lemma valid_data2032 : data2032.Valid src2032 dst2032 Finset.univ := by decide +kernel

def src2033 : E → W := ![2,6,5,3,4,8,2,14,16,3,18,4,14,28,5,26,6,26,16,38,8,28,18,38]
def dst2033 : E → W := ![6,5,3,4,8,2,14,16,3,18,2,14,28,5,26,4,26,16,38,6,28,18,38,8]
def cycle2033_0 : CycleData E W := ⟨3,![0,19,18,7,6],![2,6,38,16,14]⟩
def cycle2033_1 : CycleData E W := ⟨1,![1,16,14],![5,6,26]⟩
def cycle2033_2 : CycleData E W := ⟨2,![2,13,21,9],![3,5,28,18]⟩
def cycle2033_3 : CycleData E W := ⟨2,![3,15,17,8],![3,4,26,16]⟩
def cycle2033_4 : CycleData E W := ⟨2,![4,20,12,11],![4,8,28,14]⟩
def cycle2033_5 : CycleData E W := ⟨2,![5,23,22,10],![2,8,38,18]⟩
def data2033 : PartitionData E W := ⟨6,![cycle2033_0,cycle2033_1,cycle2033_2,cycle2033_3,cycle2033_4,cycle2033_5]⟩
lemma valid_data2033 : data2033.Valid src2033 dst2033 Finset.univ := by decide +kernel

def src2034 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,5,28,14,26,6,16,26,38,8,18,28,38]
def dst2034 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,5,28,14,26,4,16,26,38,6,18,28,38,8]
def cycle2034_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2034_1 : CycleData E W := ⟨2,![1,19,22,12],![5,6,38,28]⟩
def cycle2034_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2034_3 : CycleData E W := ⟨3,![5,4,15,14,6],![2,8,4,26,14]⟩
def cycle2034_4 : CycleData E W := ⟨1,![7,21,13],![14,18,28]⟩
def cycle2034_5 : CycleData E W := ⟨4,![8,20,23,18,17,9],![3,18,8,38,26,16]⟩
def data2034 : PartitionData E W := ⟨6,![cycle2034_0,cycle2034_1,cycle2034_2,cycle2034_3,cycle2034_4,cycle2034_5]⟩
lemma valid_data2034 : data2034.Valid src2034 dst2034 Finset.univ := by decide +kernel

def src2035 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,5,28,14,26,6,16,26,38,8,18,38,28]
def dst2035 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,5,28,14,26,4,16,26,38,6,18,38,28,8]
def cycle2035_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2035_1 : CycleData E W := ⟨3,![2,1,19,21,8],![3,5,6,38,18]⟩
def cycle2035_2 : CycleData E W := ⟨2,![3,15,17,9],![3,4,26,16]⟩
def cycle2035_3 : CycleData E W := ⟨2,![4,23,12,11],![4,8,28,5]⟩
def cycle2035_4 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def cycle2035_5 : CycleData E W := ⟨2,![13,22,18,14],![14,28,38,26]⟩
def data2035 : PartitionData E W := ⟨6,![cycle2035_0,cycle2035_1,cycle2035_2,cycle2035_3,cycle2035_4,cycle2035_5]⟩
lemma valid_data2035 : data2035.Valid src2035 dst2035 Finset.univ := by decide +kernel

def src2036 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,5,28,14,26,6,16,26,38,8,28,18,38]
def dst2036 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,5,28,14,26,4,16,26,38,6,28,18,38,8]
def cycle2036_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2036_1 : CycleData E W := ⟨3,![2,1,19,22,8],![3,5,6,38,18]⟩
def cycle2036_2 : CycleData E W := ⟨2,![3,15,17,9],![3,4,26,16]⟩
def cycle2036_3 : CycleData E W := ⟨2,![4,20,12,11],![4,8,28,5]⟩
def cycle2036_4 : CycleData E W := ⟨3,![5,23,18,14,6],![2,8,38,26,14]⟩
def cycle2036_5 : CycleData E W := ⟨1,![7,21,13],![14,18,28]⟩
def data2036 : PartitionData E W := ⟨6,![cycle2036_0,cycle2036_1,cycle2036_2,cycle2036_3,cycle2036_4,cycle2036_5]⟩
lemma valid_data2036 : data2036.Valid src2036 dst2036 Finset.univ := by decide +kernel

def src2037 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,5,28,14,26,6,16,38,26,8,18,28,38]
def dst2037 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,5,28,14,26,4,16,38,26,6,18,28,38,8]
def cycle2037_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2037_1 : CycleData E W := ⟨3,![1,19,14,13,12],![5,6,26,14,28]⟩
def cycle2037_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2037_3 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle2037_4 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def cycle2037_5 : CycleData E W := ⟨3,![8,21,22,17,9],![3,18,28,38,16]⟩
def data2037 : PartitionData E W := ⟨6,![cycle2037_0,cycle2037_1,cycle2037_2,cycle2037_3,cycle2037_4,cycle2037_5]⟩
lemma valid_data2037 : data2037.Valid src2037 dst2037 Finset.univ := by decide +kernel

def src2038 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,5,28,14,26,6,16,38,26,8,18,38,28]
def dst2038 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,5,28,14,26,4,16,38,26,6,18,38,28,8]
def cycle2038_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2038_1 : CycleData E W := ⟨3,![1,19,14,13,12],![5,6,26,14,28]⟩
def cycle2038_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2038_3 : CycleData E W := ⟨3,![4,23,22,18,15],![4,8,28,38,26]⟩
def cycle2038_4 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def cycle2038_5 : CycleData E W := ⟨2,![8,21,17,9],![3,18,38,16]⟩
def data2038 : PartitionData E W := ⟨6,![cycle2038_0,cycle2038_1,cycle2038_2,cycle2038_3,cycle2038_4,cycle2038_5]⟩
lemma valid_data2038 : data2038.Valid src2038 dst2038 Finset.univ := by decide +kernel

def src2039 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,5,28,14,26,6,16,38,26,8,28,18,38]
def dst2039 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,5,28,14,26,4,16,38,26,6,28,18,38,8]
def cycle2039_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2039_1 : CycleData E W := ⟨3,![1,19,14,13,12],![5,6,26,14,28]⟩
def cycle2039_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2039_3 : CycleData E W := ⟨2,![4,23,18,15],![4,8,38,26]⟩
def cycle2039_4 : CycleData E W := ⟨3,![5,20,21,7,6],![2,8,28,18,14]⟩
def cycle2039_5 : CycleData E W := ⟨2,![8,22,17,9],![3,18,38,16]⟩
def data2039 : PartitionData E W := ⟨6,![cycle2039_0,cycle2039_1,cycle2039_2,cycle2039_3,cycle2039_4,cycle2039_5]⟩
lemma valid_data2039 : data2039.Valid src2039 dst2039 Finset.univ := by decide +kernel

def src2040 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,5,28,14,26,6,26,16,38,8,18,28,38]
def dst2040 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,5,28,14,26,4,26,16,38,6,18,28,38,8]
def cycle2040_0 : CycleData E W := ⟨2,![0,16,14,6],![2,6,26,14]⟩
def cycle2040_1 : CycleData E W := ⟨2,![1,19,22,12],![5,6,38,28]⟩
def cycle2040_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2040_3 : CycleData E W := ⟨3,![5,4,15,17,10],![2,8,4,26,16]⟩
def cycle2040_4 : CycleData E W := ⟨1,![7,21,13],![14,18,28]⟩
def cycle2040_5 : CycleData E W := ⟨3,![8,20,23,18,9],![3,18,8,38,16]⟩
def data2040 : PartitionData E W := ⟨6,![cycle2040_0,cycle2040_1,cycle2040_2,cycle2040_3,cycle2040_4,cycle2040_5]⟩
lemma valid_data2040 : data2040.Valid src2040 dst2040 Finset.univ := by decide +kernel

def src2041 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,5,28,14,26,6,26,16,38,8,18,38,28]
def dst2041 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,5,28,14,26,4,26,16,38,6,18,38,28,8]
def cycle2041_0 : CycleData E W := ⟨2,![0,16,14,6],![2,6,26,14]⟩
def cycle2041_1 : CycleData E W := ⟨2,![1,19,22,12],![5,6,38,28]⟩
def cycle2041_2 : CycleData E W := ⟨1,![2,11,3],![3,5,4]⟩
def cycle2041_3 : CycleData E W := ⟨3,![5,4,15,17,10],![2,8,4,26,16]⟩
def cycle2041_4 : CycleData E W := ⟨2,![20,7,13,23],![8,18,14,28]⟩
def cycle2041_5 : CycleData E W := ⟨2,![8,21,18,9],![3,18,38,16]⟩
def data2041 : PartitionData E W := ⟨6,![cycle2041_0,cycle2041_1,cycle2041_2,cycle2041_3,cycle2041_4,cycle2041_5]⟩
lemma valid_data2041 : data2041.Valid src2041 dst2041 Finset.univ := by decide +kernel

def src2042 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,5,28,14,26,6,26,16,38,8,28,18,38]
def dst2042 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,5,28,14,26,4,26,16,38,6,28,18,38,8]
def cycle2042_0 : CycleData E W := ⟨2,![0,16,14,6],![2,6,26,14]⟩
def cycle2042_1 : CycleData E W := ⟨3,![2,1,19,22,8],![3,5,6,38,18]⟩
def cycle2042_2 : CycleData E W := ⟨2,![3,15,17,9],![3,4,26,16]⟩
def cycle2042_3 : CycleData E W := ⟨2,![4,20,12,11],![4,8,28,5]⟩
def cycle2042_4 : CycleData E W := ⟨2,![5,23,18,10],![2,8,38,16]⟩
def cycle2042_5 : CycleData E W := ⟨1,![7,21,13],![14,18,28]⟩
def data2042 : PartitionData E W := ⟨6,![cycle2042_0,cycle2042_1,cycle2042_2,cycle2042_3,cycle2042_4,cycle2042_5]⟩
lemma valid_data2042 : data2042.Valid src2042 dst2042 Finset.univ := by decide +kernel

def src2043 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,26,38,8,18,28,38]
def dst2043 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,26,38,6,18,28,38,8]
def cycle2043_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2043_1 : CycleData E W := ⟨3,![1,19,18,12,13],![5,6,38,26,14]⟩
def cycle2043_2 : CycleData E W := ⟨2,![2,14,21,8],![3,5,28,18]⟩
def cycle2043_3 : CycleData E W := ⟨2,![3,11,17,9],![3,4,26,16]⟩
def cycle2043_4 : CycleData E W := ⟨2,![4,23,22,15],![4,8,38,28]⟩
def cycle2043_5 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def data2043 : PartitionData E W := ⟨6,![cycle2043_0,cycle2043_1,cycle2043_2,cycle2043_3,cycle2043_4,cycle2043_5]⟩
lemma valid_data2043 : data2043.Valid src2043 dst2043 Finset.univ := by decide +kernel

def src2044 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,26,38,8,18,38,28]
def dst2044 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,26,38,6,18,38,28,8]
def cycle2044_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2044_1 : CycleData E W := ⟨3,![1,19,18,12,13],![5,6,38,26,14]⟩
def cycle2044_2 : CycleData E W := ⟨3,![2,14,22,21,8],![3,5,28,38,18]⟩
def cycle2044_3 : CycleData E W := ⟨2,![3,11,17,9],![3,4,26,16]⟩
def cycle2044_4 : CycleData E W := ⟨1,![4,23,15],![4,8,28]⟩
def cycle2044_5 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def data2044 : PartitionData E W := ⟨6,![cycle2044_0,cycle2044_1,cycle2044_2,cycle2044_3,cycle2044_4,cycle2044_5]⟩
lemma valid_data2044 : data2044.Valid src2044 dst2044 Finset.univ := by decide +kernel

def src2045 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,26,38,8,28,18,38]
def dst2045 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,26,38,6,28,18,38,8]
def cycle2045_0 : CycleData E W := ⟨2,![0,1,13,6],![2,6,5,14]⟩
def cycle2045_1 : CycleData E W := ⟨2,![2,14,21,8],![3,5,28,18]⟩
def cycle2045_2 : CycleData E W := ⟨2,![3,11,17,9],![3,4,26,16]⟩
def cycle2045_3 : CycleData E W := ⟨1,![4,20,15],![4,8,28]⟩
def cycle2045_4 : CycleData E W := ⟨3,![5,23,19,16,10],![2,8,38,6,16]⟩
def cycle2045_5 : CycleData E W := ⟨2,![7,22,18,12],![14,18,38,26]⟩
def data2045 : PartitionData E W := ⟨6,![cycle2045_0,cycle2045_1,cycle2045_2,cycle2045_3,cycle2045_4,cycle2045_5]⟩
lemma valid_data2045 : data2045.Valid src2045 dst2045 Finset.univ := by decide +kernel

def src2046 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,38,26,8,18,28,38]
def dst2046 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,38,26,6,18,28,38,8]
def cycle2046_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2046_1 : CycleData E W := ⟨2,![1,19,12,13],![5,6,26,14]⟩
def cycle2046_2 : CycleData E W := ⟨2,![2,14,15,3],![3,5,28,4]⟩
def cycle2046_3 : CycleData E W := ⟨2,![4,23,18,11],![4,8,38,26]⟩
def cycle2046_4 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def cycle2046_5 : CycleData E W := ⟨3,![8,21,22,17,9],![3,18,28,38,16]⟩
def data2046 : PartitionData E W := ⟨6,![cycle2046_0,cycle2046_1,cycle2046_2,cycle2046_3,cycle2046_4,cycle2046_5]⟩
lemma valid_data2046 : data2046.Valid src2046 dst2046 Finset.univ := by decide +kernel

def src2047 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,38,26,8,18,38,28]
def dst2047 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,38,26,6,18,38,28,8]
def cycle2047_0 : CycleData E W := ⟨1,![0,16,10],![2,6,16]⟩
def cycle2047_1 : CycleData E W := ⟨3,![2,1,19,11,3],![3,5,6,26,4]⟩
def cycle2047_2 : CycleData E W := ⟨1,![4,23,15],![4,8,28]⟩
def cycle2047_3 : CycleData E W := ⟨2,![5,20,7,6],![2,8,18,14]⟩
def cycle2047_4 : CycleData E W := ⟨2,![8,21,17,9],![3,18,38,16]⟩
def cycle2047_5 : CycleData E W := ⟨3,![13,12,18,22,14],![5,14,26,38,28]⟩
def data2047 : PartitionData E W := ⟨6,![cycle2047_0,cycle2047_1,cycle2047_2,cycle2047_3,cycle2047_4,cycle2047_5]⟩
lemma valid_data2047 : data2047.Valid src2047 dst2047 Finset.univ := by decide +kernel

def src2048 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,16,38,26,8,28,18,38]
def dst2048 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,16,38,26,6,28,18,38,8]
def cycle2048_0 : CycleData E W := ⟨2,![0,1,13,6],![2,6,5,14]⟩
def cycle2048_1 : CycleData E W := ⟨2,![2,14,21,8],![3,5,28,18]⟩
def cycle2048_2 : CycleData E W := ⟨3,![3,11,19,16,9],![3,4,26,6,16]⟩
def cycle2048_3 : CycleData E W := ⟨1,![4,20,15],![4,8,28]⟩
def cycle2048_4 : CycleData E W := ⟨2,![5,23,17,10],![2,8,38,16]⟩
def cycle2048_5 : CycleData E W := ⟨2,![7,22,18,12],![14,18,38,26]⟩
def data2048 : PartitionData E W := ⟨6,![cycle2048_0,cycle2048_1,cycle2048_2,cycle2048_3,cycle2048_4,cycle2048_5]⟩
lemma valid_data2048 : data2048.Valid src2048 dst2048 Finset.univ := by decide +kernel

def src2049 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,26,16,38,8,18,28,38]
def dst2049 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,26,16,38,6,18,28,38,8]
def cycle2049_0 : CycleData E W := ⟨2,![0,16,12,6],![2,6,26,14]⟩
def cycle2049_1 : CycleData E W := ⟨2,![1,19,22,14],![5,6,38,28]⟩
def cycle2049_2 : CycleData E W := ⟨2,![2,13,7,8],![3,5,14,18]⟩
def cycle2049_3 : CycleData E W := ⟨2,![3,11,17,9],![3,4,26,16]⟩
def cycle2049_4 : CycleData E W := ⟨2,![4,20,21,15],![4,8,18,28]⟩
def cycle2049_5 : CycleData E W := ⟨2,![5,23,18,10],![2,8,38,16]⟩
def data2049 : PartitionData E W := ⟨6,![cycle2049_0,cycle2049_1,cycle2049_2,cycle2049_3,cycle2049_4,cycle2049_5]⟩
lemma valid_data2049 : data2049.Valid src2049 dst2049 Finset.univ := by decide +kernel

def src2050 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,26,16,38,8,18,38,28]
def dst2050 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,26,16,38,6,18,38,28,8]
def cycle2050_0 : CycleData E W := ⟨2,![0,16,12,6],![2,6,26,14]⟩
def cycle2050_1 : CycleData E W := ⟨2,![1,19,22,14],![5,6,38,28]⟩
def cycle2050_2 : CycleData E W := ⟨2,![2,13,7,8],![3,5,14,18]⟩
def cycle2050_3 : CycleData E W := ⟨2,![3,11,17,9],![3,4,26,16]⟩
def cycle2050_4 : CycleData E W := ⟨1,![4,23,15],![4,8,28]⟩
def cycle2050_5 : CycleData E W := ⟨3,![5,20,21,18,10],![2,8,18,38,16]⟩
def data2050 : PartitionData E W := ⟨6,![cycle2050_0,cycle2050_1,cycle2050_2,cycle2050_3,cycle2050_4,cycle2050_5]⟩
lemma valid_data2050 : data2050.Valid src2050 dst2050 Finset.univ := by decide +kernel

def src2051 : E → W := ![2,6,5,3,4,8,2,14,18,3,16,4,26,14,5,28,6,26,16,38,8,28,18,38]
def dst2051 : E → W := ![6,5,3,4,8,2,14,18,3,16,2,26,14,5,28,4,26,16,38,6,28,18,38,8]
def cycle2051_0 : CycleData E W := ⟨2,![0,1,13,6],![2,6,5,14]⟩
def cycle2051_1 : CycleData E W := ⟨2,![2,14,21,8],![3,5,28,18]⟩
def cycle2051_2 : CycleData E W := ⟨2,![3,11,17,9],![3,4,26,16]⟩
def cycle2051_3 : CycleData E W := ⟨1,![4,20,15],![4,8,28]⟩
def cycle2051_4 : CycleData E W := ⟨2,![5,23,18,10],![2,8,38,16]⟩
def cycle2051_5 : CycleData E W := ⟨3,![16,12,7,22,19],![6,26,14,18,38]⟩
def data2051 : PartitionData E W := ⟨6,![cycle2051_0,cycle2051_1,cycle2051_2,cycle2051_3,cycle2051_4,cycle2051_5]⟩
lemma valid_data2051 : data2051.Valid src2051 dst2051 Finset.univ := by decide +kernel

def lookupB10 (j : ℕ) : PartitionData E W := (if j < 26 then (if j < 13 then (if j < 6 then (if j < 3 then (if j < 1 then data2000 else (if j < 2 then data2001 else data2002)) else (if j < 4 then data2003 else (if j < 5 then data2004 else data2005))) else (if j < 9 then (if j < 7 then data2006 else (if j < 8 then data2007 else data2008)) else (if j < 11 then (if j < 10 then data2009 else data2010) else (if j < 12 then data2011 else data2012)))) else (if j < 19 then (if j < 16 then (if j < 14 then data2013 else (if j < 15 then data2014 else data2015)) else (if j < 17 then data2016 else (if j < 18 then data2017 else data2018))) else (if j < 22 then (if j < 20 then data2019 else (if j < 21 then data2020 else data2021)) else (if j < 24 then (if j < 23 then data2022 else data2023) else (if j < 25 then data2024 else data2025))))) else (if j < 39 then (if j < 32 then (if j < 29 then (if j < 27 then data2026 else (if j < 28 then data2027 else data2028)) else (if j < 30 then data2029 else (if j < 31 then data2030 else data2031))) else (if j < 35 then (if j < 33 then data2032 else (if j < 34 then data2033 else data2034)) else (if j < 37 then (if j < 36 then data2035 else data2036) else (if j < 38 then data2037 else data2038)))) else (if j < 45 then (if j < 42 then (if j < 40 then data2039 else (if j < 41 then data2040 else data2041)) else (if j < 43 then data2042 else (if j < 44 then data2043 else data2044))) else (if j < 48 then (if j < 46 then data2045 else (if j < 47 then data2046 else data2047)) else (if j < 50 then (if j < 49 then data2048 else data2049) else (if j < 51 then data2050 else data2051))))))

def srcTableB10 (j : ℕ) : E → W := (if j < 26 then (if j < 13 then (if j < 6 then (if j < 3 then (if j < 1 then src2000 else (if j < 2 then src2001 else src2002)) else (if j < 4 then src2003 else (if j < 5 then src2004 else src2005))) else (if j < 9 then (if j < 7 then src2006 else (if j < 8 then src2007 else src2008)) else (if j < 11 then (if j < 10 then src2009 else src2010) else (if j < 12 then src2011 else src2012)))) else (if j < 19 then (if j < 16 then (if j < 14 then src2013 else (if j < 15 then src2014 else src2015)) else (if j < 17 then src2016 else (if j < 18 then src2017 else src2018))) else (if j < 22 then (if j < 20 then src2019 else (if j < 21 then src2020 else src2021)) else (if j < 24 then (if j < 23 then src2022 else src2023) else (if j < 25 then src2024 else src2025))))) else (if j < 39 then (if j < 32 then (if j < 29 then (if j < 27 then src2026 else (if j < 28 then src2027 else src2028)) else (if j < 30 then src2029 else (if j < 31 then src2030 else src2031))) else (if j < 35 then (if j < 33 then src2032 else (if j < 34 then src2033 else src2034)) else (if j < 37 then (if j < 36 then src2035 else src2036) else (if j < 38 then src2037 else src2038)))) else (if j < 45 then (if j < 42 then (if j < 40 then src2039 else (if j < 41 then src2040 else src2041)) else (if j < 43 then src2042 else (if j < 44 then src2043 else src2044))) else (if j < 48 then (if j < 46 then src2045 else (if j < 47 then src2046 else src2047)) else (if j < 50 then (if j < 49 then src2048 else src2049) else (if j < 51 then src2050 else src2051))))))

def dstTableB10 (j : ℕ) : E → W := (if j < 26 then (if j < 13 then (if j < 6 then (if j < 3 then (if j < 1 then dst2000 else (if j < 2 then dst2001 else dst2002)) else (if j < 4 then dst2003 else (if j < 5 then dst2004 else dst2005))) else (if j < 9 then (if j < 7 then dst2006 else (if j < 8 then dst2007 else dst2008)) else (if j < 11 then (if j < 10 then dst2009 else dst2010) else (if j < 12 then dst2011 else dst2012)))) else (if j < 19 then (if j < 16 then (if j < 14 then dst2013 else (if j < 15 then dst2014 else dst2015)) else (if j < 17 then dst2016 else (if j < 18 then dst2017 else dst2018))) else (if j < 22 then (if j < 20 then dst2019 else (if j < 21 then dst2020 else dst2021)) else (if j < 24 then (if j < 23 then dst2022 else dst2023) else (if j < 25 then dst2024 else dst2025))))) else (if j < 39 then (if j < 32 then (if j < 29 then (if j < 27 then dst2026 else (if j < 28 then dst2027 else dst2028)) else (if j < 30 then dst2029 else (if j < 31 then dst2030 else dst2031))) else (if j < 35 then (if j < 33 then dst2032 else (if j < 34 then dst2033 else dst2034)) else (if j < 37 then (if j < 36 then dst2035 else dst2036) else (if j < 38 then dst2037 else dst2038)))) else (if j < 45 then (if j < 42 then (if j < 40 then dst2039 else (if j < 41 then dst2040 else dst2041)) else (if j < 43 then dst2042 else (if j < 44 then dst2043 else dst2044))) else (if j < 48 then (if j < 46 then dst2045 else (if j < 47 then dst2046 else dst2047)) else (if j < 50 then (if j < 49 then dst2048 else dst2049) else (if j < 51 then dst2050 else dst2051))))))

def caseB10 (i : Fin 52) : Cases := ⟨2000 + i.val,by have := i.isLt; omega⟩
lemma tableB10_valid (i : Fin 52) :
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

lemma srcB10_row : ∀ (i : Fin 52) (e : E),
    srcTableB10 i.val e = caseSource (caseB10 i) e := by decide +kernel

lemma dstB10_row : ∀ (i : Fin 52) (e : E),
    dstTableB10 i.val e = caseTarget (caseB10 i) e := by decide +kernel

lemma sizeB10 : ∀ i : Fin 52, (lookupB10 i.val).size ≤ 5 →
    (lookupB10 i.val).size = 2 ∧
      (⟨caseKey (caseB10 i),caseKey_lt (caseB10 i)⟩ : Fin 77760) ∈ good := by decide +kernel
lemma certificateB10 (i : Fin 52) : Certificate (caseB10 i) := by
  refine ⟨lookupB10 i.val,?_,sizeB10 i⟩
  have hv := tableB10_valid i
  rw [funext (srcB10_row i),funext (dstB10_row i)] at hv
  exact hv
lemma certificateInterval10 : FiniteIntervals.Covers CertificateAt 2000 2052 := by
  exact FiniteIntervals.of_fin (P := CertificateAt) 2000 52 (fun i _ => certificateB10 i)
#print axioms certificateInterval10
end Erdos184Work.FiveRows2
