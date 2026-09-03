import Submission.DoublePetersenLower

import Submission.LabelCycleCertificates

import Submission.ParallelFlip



/-! Explicit partitions of doubled Petersen and all canonical circuit cofactors. -/

namespace Erdos184Work.DoublePetersen

open Erdos184Serial LabelKernel

set_option maxHeartbeats 10000000

set_option maxRecDepth 100000

set_option Elab.async false

def canonical : Fin 15 ⊕ Fin 57 → Finset Edge
  | .inl e => Parallel.pair e
  | .inr i => (PetersenBase.edges i).map (Parallel.choiceEmbedding PetersenBase.src PetersenBase.dst (fun _ => false)).edge

def fullCertificate : PartitionData Edge Vertex := ⟨5,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(5,false),(5,true)],![2,3]⟩,⟨6,![(1,false),(7,false),(8,false),(12,false),(13,false),(14,false),(10,false),(2,false)],![0,4,3,8,6,9,7,5]⟩,⟨7,![(1,true),(9,false),(14,true),(6,false),(3,false),(4,false),(12,true),(11,false),(2,true)],![0,4,9,7,2,1,6,8,5]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma fullCertificate_valid : fullCertificate.Valid src dst Finset.univ := by decide +kernel

lemma full_number : HasNumber code Finset.univ 5 :=
  ⟨PartitionData.exists_partition fullCertificate_valid,lower⟩

def cofactor0 : PartitionData Edge Vertex := ⟨4,![⟨0,![(5,false),(5,true)],![2,3]⟩,⟨6,![(1,false),(7,false),(8,false),(12,false),(13,false),(14,false),(10,false),(2,false)],![0,4,3,8,6,9,7,5]⟩,⟨7,![(1,true),(9,false),(14,true),(6,false),(3,false),(4,false),(12,true),(11,false),(2,true)],![0,4,9,7,2,1,6,8,5]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor0 : cofactor0.Valid src dst (Finset.univ \ canonical (.inl 0)) := by decide +kernel

def cofactor1 : PartitionData Edge Vertex := ⟨4,![⟨0,![(3,false),(3,true)],![1,2]⟩,⟨6,![(5,false),(7,false),(9,false),(13,false),(12,false),(11,false),(10,false),(6,false)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,false),(4,false),(12,true),(8,false),(7,true),(9,true),(14,false),(10,true),(2,false)],![0,1,6,8,3,4,9,7,5]⟩,⟨7,![(0,true),(4,true),(13,true),(14,true),(6,true),(5,true),(8,true),(11,true),(2,true)],![0,1,6,9,7,2,3,8,5]⟩]⟩

lemma validCofactor1 : cofactor1.Valid src dst (Finset.univ \ canonical (.inl 1)) := by decide +kernel

def cofactor2 : PartitionData Edge Vertex := ⟨4,![⟨0,![(3,false),(3,true)],![1,2]⟩,⟨6,![(5,false),(7,false),(9,false),(13,false),(12,false),(11,false),(10,false),(6,false)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,false),(4,false),(12,true),(8,false),(5,true),(6,true),(14,false),(9,true),(1,false)],![0,1,6,8,3,2,7,9,4]⟩,⟨7,![(0,true),(4,true),(13,true),(14,true),(10,true),(11,true),(8,true),(7,true),(1,true)],![0,1,6,9,7,5,8,3,4]⟩]⟩

lemma validCofactor2 : cofactor2.Valid src dst (Finset.univ \ canonical (.inl 2)) := by decide +kernel

def cofactor3 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨6,![(5,false),(7,false),(9,false),(13,false),(12,false),(11,false),(10,false),(6,false)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,false),(4,false),(12,true),(8,false),(7,true),(9,true),(14,false),(10,true),(2,false)],![0,1,6,8,3,4,9,7,5]⟩,⟨7,![(0,true),(4,true),(13,true),(14,true),(6,true),(5,true),(8,true),(11,true),(2,true)],![0,1,6,9,7,2,3,8,5]⟩]⟩

lemma validCofactor3 : cofactor3.Valid src dst (Finset.univ \ canonical (.inl 3)) := by decide +kernel

def cofactor4 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨6,![(5,false),(7,false),(9,false),(13,false),(12,false),(11,false),(10,false),(6,false)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,false),(3,false),(5,true),(8,false),(12,true),(13,true),(14,false),(10,true),(2,false)],![0,1,2,3,8,6,9,7,5]⟩,⟨7,![(0,true),(3,true),(6,true),(14,true),(9,true),(7,true),(8,true),(11,true),(2,true)],![0,1,2,7,9,4,3,8,5]⟩]⟩

lemma validCofactor4 : cofactor4.Valid src dst (Finset.univ \ canonical (.inl 4)) := by decide +kernel

def cofactor5 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨6,![(1,false),(7,false),(8,false),(12,false),(13,false),(14,false),(10,false),(2,false)],![0,4,3,8,6,9,7,5]⟩,⟨7,![(1,true),(9,false),(14,true),(6,false),(3,false),(4,false),(12,true),(11,false),(2,true)],![0,4,9,7,2,1,6,8,5]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor5 : cofactor5.Valid src dst (Finset.univ \ canonical (.inl 5)) := by decide +kernel

def cofactor6 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨6,![(1,false),(7,false),(8,false),(12,false),(13,false),(14,false),(10,false),(2,false)],![0,4,3,8,6,9,7,5]⟩,⟨7,![(1,true),(9,false),(13,true),(4,false),(3,false),(5,false),(8,true),(11,false),(2,true)],![0,4,9,6,1,2,3,8,5]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor6 : cofactor6.Valid src dst (Finset.univ \ canonical (.inl 6)) := by decide +kernel

def cofactor7 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨6,![(3,false),(5,false),(8,false),(11,false),(10,false),(14,false),(13,false),(4,false)],![1,2,3,8,5,7,9,6]⟩,⟨7,![(1,false),(9,false),(13,true),(12,false),(8,true),(5,true),(6,false),(10,true),(2,false)],![0,4,9,6,8,3,2,7,5]⟩,⟨7,![(1,true),(9,true),(14,true),(6,true),(3,true),(4,true),(12,true),(11,true),(2,true)],![0,4,9,7,2,1,6,8,5]⟩]⟩

lemma validCofactor7 : cofactor7.Valid src dst (Finset.univ \ canonical (.inl 7)) := by decide +kernel

def cofactor8 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨6,![(1,false),(9,false),(13,false),(4,false),(3,false),(6,false),(10,false),(2,false)],![0,4,9,6,1,2,7,5]⟩,⟨7,![(1,true),(7,false),(5,false),(6,true),(14,false),(13,true),(12,false),(11,false),(2,true)],![0,4,3,2,7,9,6,8,5]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor8 : cofactor8.Valid src dst (Finset.univ \ canonical (.inl 8)) := by decide +kernel

def cofactor9 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨6,![(3,false),(5,false),(8,false),(11,false),(10,false),(14,false),(13,false),(4,false)],![1,2,3,8,5,7,9,6]⟩,⟨7,![(1,false),(7,false),(5,true),(6,false),(14,true),(13,true),(12,false),(11,true),(2,false)],![0,4,3,2,7,9,6,8,5]⟩,⟨7,![(1,true),(7,true),(8,true),(12,true),(4,true),(3,true),(6,true),(10,true),(2,true)],![0,4,3,8,6,1,2,7,5]⟩]⟩

lemma validCofactor9 : cofactor9.Valid src dst (Finset.univ \ canonical (.inl 9)) := by decide +kernel

def cofactor10 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨6,![(3,false),(6,false),(14,false),(9,false),(7,false),(8,false),(12,false),(4,false)],![1,2,7,9,4,3,8,6]⟩,⟨7,![(1,false),(7,true),(5,false),(6,true),(14,true),(13,false),(12,true),(11,false),(2,false)],![0,4,3,2,7,9,6,8,5]⟩,⟨7,![(1,true),(9,true),(13,true),(4,true),(3,true),(5,true),(8,true),(11,true),(2,true)],![0,4,9,6,1,2,3,8,5]⟩]⟩

lemma validCofactor10 : cofactor10.Valid src dst (Finset.univ \ canonical (.inl 10)) := by decide +kernel

def cofactor11 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨6,![(3,false),(6,false),(14,false),(9,false),(7,false),(8,false),(12,false),(4,false)],![1,2,7,9,4,3,8,6]⟩,⟨7,![(1,false),(7,true),(5,false),(3,true),(4,true),(13,false),(14,true),(10,false),(2,false)],![0,4,3,2,1,6,9,7,5]⟩,⟨7,![(1,true),(9,true),(13,true),(12,true),(8,true),(5,true),(6,true),(10,true),(2,true)],![0,4,9,6,8,3,2,7,5]⟩]⟩

lemma validCofactor11 : cofactor11.Valid src dst (Finset.univ \ canonical (.inl 11)) := by decide +kernel

def cofactor12 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨6,![(1,false),(9,false),(14,false),(6,false),(5,false),(8,false),(11,false),(2,false)],![0,4,9,7,2,3,8,5]⟩,⟨7,![(1,true),(7,false),(5,true),(3,false),(4,false),(13,false),(14,true),(10,false),(2,true)],![0,4,3,2,1,6,9,7,5]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor12 : cofactor12.Valid src dst (Finset.univ \ canonical (.inl 12)) := by decide +kernel

def cofactor13 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨6,![(1,false),(9,false),(14,false),(6,false),(5,false),(8,false),(11,false),(2,false)],![0,4,9,7,2,3,8,5]⟩,⟨7,![(1,true),(7,false),(8,true),(12,false),(4,false),(3,false),(6,true),(10,false),(2,true)],![0,4,3,8,6,1,2,7,5]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor13 : cofactor13.Valid src dst (Finset.univ \ canonical (.inl 13)) := by decide +kernel

def cofactor14 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨6,![(1,false),(7,false),(5,false),(3,false),(4,false),(12,false),(11,false),(2,false)],![0,4,3,2,1,6,8,5]⟩,⟨7,![(1,true),(9,false),(13,false),(12,true),(8,false),(5,true),(6,false),(10,false),(2,true)],![0,4,9,6,8,3,2,7,5]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor14 : cofactor14.Valid src dst (Finset.univ \ canonical (.inl 14)) := by decide +kernel

def cofactor15 : PartitionData Edge Vertex := ⟨4,![⟨0,![(2,false),(2,true)],![0,5]⟩,⟨3,![(10,false),(14,false),(13,false),(12,false),(11,false)],![5,7,9,6,8]⟩,⟨7,![(0,true),(4,false),(12,true),(8,false),(5,true),(6,false),(14,true),(9,false),(1,true)],![0,1,6,8,3,2,7,9,4]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor15 : cofactor15.Valid src dst (Finset.univ \ canonical (.inr 0)) := by decide +kernel

def cofactor16 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨3,![(7,false),(9,false),(13,false),(12,false),(8,false)],![3,4,9,6,8]⟩,⟨7,![(0,true),(4,false),(13,true),(14,false),(6,true),(5,false),(8,true),(11,false),(2,true)],![0,1,6,9,7,2,3,8,5]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor16 : cofactor16.Valid src dst (Finset.univ \ canonical (.inr 1)) := by decide +kernel

def cofactor17 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨3,![(5,false),(7,false),(9,false),(14,false),(6,false)],![2,3,4,9,7]⟩,⟨7,![(0,true),(3,false),(5,true),(8,false),(12,true),(13,false),(14,true),(10,false),(2,true)],![0,1,2,3,8,6,9,7,5]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor17 : cofactor17.Valid src dst (Finset.univ \ canonical (.inr 2)) := by decide +kernel

def cofactor18 : PartitionData Edge Vertex := ⟨4,![⟨0,![(2,false),(2,true)],![0,5]⟩,⟨3,![(5,false),(8,false),(11,false),(10,false),(6,false)],![2,3,8,5,7]⟩,⟨7,![(0,true),(3,false),(6,true),(14,false),(13,true),(12,false),(8,true),(7,false),(1,true)],![0,1,2,7,9,6,8,3,4]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor18 : cofactor18.Valid src dst (Finset.univ \ canonical (.inr 3)) := by decide +kernel

def cofactor19 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨3,![(3,false),(6,false),(14,false),(13,false),(4,false)],![1,2,7,9,6]⟩,⟨7,![(1,true),(9,false),(13,true),(12,false),(8,true),(5,false),(6,true),(10,false),(2,true)],![0,4,9,6,8,3,2,7,5]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor19 : cofactor19.Valid src dst (Finset.univ \ canonical (.inr 4)) := by decide +kernel

def cofactor20 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨3,![(3,false),(5,false),(8,false),(12,false),(4,false)],![1,2,3,8,6]⟩,⟨7,![(1,true),(7,false),(5,true),(6,false),(14,true),(13,false),(12,true),(11,false),(2,true)],![0,4,3,2,7,9,6,8,5]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor20 : cofactor20.Valid src dst (Finset.univ \ canonical (.inr 5)) := by decide +kernel

def cofactor21 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨3,![(1,false),(9,false),(14,false),(10,false),(2,false)],![0,4,9,7,5]⟩,⟨7,![(1,true),(7,false),(5,true),(6,false),(14,true),(13,false),(12,true),(11,false),(2,true)],![0,4,3,2,7,9,6,8,5]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor21 : cofactor21.Valid src dst (Finset.univ \ canonical (.inr 6)) := by decide +kernel

def cofactor22 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨3,![(1,false),(7,false),(8,false),(11,false),(2,false)],![0,4,3,8,5]⟩,⟨7,![(1,true),(9,false),(13,true),(12,false),(8,true),(5,false),(6,true),(10,false),(2,true)],![0,4,9,6,8,3,2,7,5]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor22 : cofactor22.Valid src dst (Finset.univ \ canonical (.inr 7)) := by decide +kernel

def cofactor23 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨3,![(10,false),(14,true),(13,false),(12,false),(11,false)],![5,7,9,6,8]⟩,⟨7,![(1,false),(7,true),(8,false),(12,true),(4,false),(3,false),(6,true),(10,true),(2,false)],![0,4,3,8,6,1,2,7,5]⟩,⟨7,![(1,true),(9,true),(13,true),(4,true),(3,true),(5,true),(8,true),(11,true),(2,true)],![0,4,9,6,1,2,3,8,5]⟩]⟩

lemma validCofactor23 : cofactor23.Valid src dst (Finset.univ \ canonical (.inr 8)) := by decide +kernel

def cofactor24 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨3,![(7,false),(9,false),(13,false),(12,false),(8,true)],![3,4,9,6,8]⟩,⟨7,![(1,false),(7,true),(5,true),(3,false),(4,false),(13,true),(14,false),(10,true),(2,false)],![0,4,3,2,1,6,9,7,5]⟩,⟨7,![(1,true),(9,true),(14,true),(6,true),(3,true),(4,true),(12,true),(11,true),(2,true)],![0,4,9,7,2,1,6,8,5]⟩]⟩

lemma validCofactor24 : cofactor24.Valid src dst (Finset.univ \ canonical (.inr 9)) := by decide +kernel

def cofactor25 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨3,![(5,false),(8,true),(11,false),(10,false),(6,false)],![2,3,8,5,7]⟩,⟨7,![(1,false),(7,true),(5,true),(3,false),(4,false),(13,true),(14,false),(10,true),(2,false)],![0,4,3,2,1,6,9,7,5]⟩,⟨7,![(1,true),(9,true),(14,true),(6,true),(3,true),(4,true),(12,true),(11,true),(2,true)],![0,4,9,7,2,1,6,8,5]⟩]⟩

lemma validCofactor25 : cofactor25.Valid src dst (Finset.univ \ canonical (.inr 10)) := by decide +kernel

def cofactor26 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨3,![(5,false),(7,false),(9,false),(14,true),(6,false)],![2,3,4,9,7]⟩,⟨7,![(1,false),(7,true),(8,false),(12,true),(4,false),(3,false),(6,true),(10,true),(2,false)],![0,4,3,8,6,1,2,7,5]⟩,⟨7,![(1,true),(9,true),(13,true),(4,true),(3,true),(5,true),(8,true),(11,true),(2,true)],![0,4,9,6,1,2,3,8,5]⟩]⟩

lemma validCofactor26 : cofactor26.Valid src dst (Finset.univ \ canonical (.inr 11)) := by decide +kernel

def cofactor27 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨3,![(3,true),(6,false),(14,false),(13,false),(4,false)],![1,2,7,9,6]⟩,⟨6,![(5,true),(7,false),(9,false),(13,true),(12,false),(11,true),(10,false),(6,true)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,true),(4,true),(12,true),(8,true),(7,true),(9,true),(14,true),(10,true),(2,true)],![0,1,6,8,3,4,9,7,5]⟩]⟩

lemma validCofactor27 : cofactor27.Valid src dst (Finset.univ \ canonical (.inr 12)) := by decide +kernel

def cofactor28 : PartitionData Edge Vertex := ⟨4,![⟨0,![(2,false),(2,true)],![0,5]⟩,⟨3,![(3,true),(5,false),(8,false),(12,false),(4,false)],![1,2,3,8,6]⟩,⟨6,![(5,true),(7,false),(9,true),(13,false),(12,true),(11,false),(10,false),(6,true)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,true),(4,true),(13,true),(14,true),(10,true),(11,true),(8,true),(7,true),(1,true)],![0,1,6,9,7,5,8,3,4]⟩]⟩

lemma validCofactor28 : cofactor28.Valid src dst (Finset.univ \ canonical (.inr 13)) := by decide +kernel

def cofactor29 : PartitionData Edge Vertex := ⟨4,![⟨0,![(2,false),(2,true)],![0,5]⟩,⟨3,![(3,false),(6,false),(14,false),(13,false),(4,true)],![1,2,7,9,6]⟩,⟨6,![(5,false),(7,true),(9,false),(13,true),(12,true),(11,false),(10,false),(6,true)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,true),(3,true),(5,true),(8,true),(11,true),(10,true),(14,true),(9,true),(1,true)],![0,1,2,3,8,5,7,9,4]⟩]⟩

lemma validCofactor29 : cofactor29.Valid src dst (Finset.univ \ canonical (.inr 14)) := by decide +kernel

def cofactor30 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨3,![(3,false),(5,false),(8,false),(12,false),(4,true)],![1,2,3,8,6]⟩,⟨6,![(5,true),(7,false),(9,false),(13,true),(12,true),(11,false),(10,true),(6,false)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,true),(3,true),(6,true),(14,true),(9,true),(7,true),(8,true),(11,true),(2,true)],![0,1,2,7,9,4,3,8,5]⟩]⟩

lemma validCofactor30 : cofactor30.Valid src dst (Finset.univ \ canonical (.inr 15)) := by decide +kernel

def cofactor31 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨3,![(7,true),(9,false),(13,false),(12,false),(8,false)],![3,4,9,6,8]⟩,⟨6,![(3,false),(5,true),(8,true),(11,false),(10,true),(14,false),(13,true),(4,false)],![1,2,3,8,5,7,9,6]⟩,⟨7,![(1,true),(9,true),(14,true),(6,true),(3,true),(4,true),(12,true),(11,true),(2,true)],![0,4,9,7,2,1,6,8,5]⟩]⟩

lemma validCofactor31 : cofactor31.Valid src dst (Finset.univ \ canonical (.inr 16)) := by decide +kernel

def cofactor32 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨3,![(5,false),(7,false),(9,true),(14,false),(6,false)],![2,3,4,9,7]⟩,⟨6,![(3,false),(5,true),(8,false),(11,true),(10,false),(14,true),(13,true),(4,false)],![1,2,3,8,5,7,9,6]⟩,⟨7,![(1,true),(7,true),(8,true),(12,true),(4,true),(3,true),(6,true),(10,true),(2,true)],![0,4,3,8,6,1,2,7,5]⟩]⟩

lemma validCofactor32 : cofactor32.Valid src dst (Finset.univ \ canonical (.inr 17)) := by decide +kernel

def cofactor33 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨3,![(5,true),(8,false),(11,false),(10,false),(6,false)],![2,3,8,5,7]⟩,⟨6,![(1,false),(7,true),(8,true),(12,false),(13,true),(14,false),(10,true),(2,false)],![0,4,3,8,6,9,7,5]⟩,⟨7,![(1,true),(9,true),(14,true),(6,true),(3,true),(4,true),(12,true),(11,true),(2,true)],![0,4,9,7,2,1,6,8,5]⟩]⟩

lemma validCofactor33 : cofactor33.Valid src dst (Finset.univ \ canonical (.inr 18)) := by decide +kernel

def cofactor34 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨3,![(5,false),(7,false),(9,false),(14,false),(6,true)],![2,3,4,9,7]⟩,⟨6,![(1,false),(7,true),(8,false),(12,true),(13,false),(14,true),(10,true),(2,false)],![0,4,3,8,6,9,7,5]⟩,⟨7,![(1,true),(9,true),(13,true),(4,true),(3,true),(5,true),(8,true),(11,true),(2,true)],![0,4,9,6,1,2,3,8,5]⟩]⟩

lemma validCofactor34 : cofactor34.Valid src dst (Finset.univ \ canonical (.inr 19)) := by decide +kernel

def cofactor35 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨3,![(1,false),(7,false),(8,true),(11,false),(2,false)],![0,4,3,8,5]⟩,⟨6,![(1,true),(9,false),(13,true),(4,false),(3,false),(6,true),(10,false),(2,true)],![0,4,9,6,1,2,7,5]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor35 : cofactor35.Valid src dst (Finset.univ \ canonical (.inr 20)) := by decide +kernel

def cofactor36 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨3,![(3,false),(5,false),(8,true),(12,false),(4,false)],![1,2,3,8,6]⟩,⟨6,![(1,false),(9,true),(13,false),(4,true),(3,true),(6,false),(10,true),(2,false)],![0,4,9,6,1,2,7,5]⟩,⟨7,![(1,true),(7,true),(5,true),(6,true),(14,true),(13,true),(12,true),(11,true),(2,true)],![0,4,3,2,7,9,6,8,5]⟩]⟩

lemma validCofactor36 : cofactor36.Valid src dst (Finset.univ \ canonical (.inr 21)) := by decide +kernel

def cofactor37 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨0,![(12,false),(12,true)],![6,8]⟩,⟨7,![(0,true),(4,false),(13,false),(14,true),(6,false),(5,true),(8,false),(11,false),(2,true)],![0,1,6,9,7,2,3,8,5]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor37 : cofactor37.Valid src dst (Finset.univ \ canonical (.inr 22)) := by decide +kernel

def cofactor38 : PartitionData Edge Vertex := ⟨4,![⟨0,![(2,false),(2,true)],![0,5]⟩,⟨0,![(6,false),(6,true)],![2,7]⟩,⟨7,![(0,true),(4,false),(13,true),(14,false),(10,false),(11,false),(8,true),(7,false),(1,true)],![0,1,6,9,7,5,8,3,4]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor38 : cofactor38.Valid src dst (Finset.univ \ canonical (.inr 23)) := by decide +kernel

def cofactor39 : PartitionData Edge Vertex := ⟨4,![⟨0,![(2,false),(2,true)],![0,5]⟩,⟨0,![(13,false),(13,true)],![6,9]⟩,⟨7,![(0,true),(4,false),(12,false),(8,true),(5,false),(6,true),(14,false),(9,false),(1,true)],![0,1,6,8,3,2,7,9,4]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor39 : cofactor39.Valid src dst (Finset.univ \ canonical (.inr 24)) := by decide +kernel

def cofactor40 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨0,![(5,false),(5,true)],![2,3]⟩,⟨7,![(0,true),(4,false),(12,true),(8,false),(7,false),(9,false),(14,true),(10,false),(2,true)],![0,1,6,8,3,4,9,7,5]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor40 : cofactor40.Valid src dst (Finset.univ \ canonical (.inr 25)) := by decide +kernel

def cofactor41 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨0,![(13,false),(13,true)],![6,9]⟩,⟨7,![(0,true),(3,false),(6,true),(14,false),(9,false),(7,false),(8,true),(11,false),(2,true)],![0,1,2,7,9,4,3,8,5]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor41 : cofactor41.Valid src dst (Finset.univ \ canonical (.inr 26)) := by decide +kernel

def cofactor42 : PartitionData Edge Vertex := ⟨4,![⟨0,![(2,false),(2,true)],![0,5]⟩,⟨0,![(5,false),(5,true)],![2,3]⟩,⟨7,![(0,true),(3,false),(6,false),(14,true),(13,false),(12,true),(8,false),(7,false),(1,true)],![0,1,2,7,9,6,8,3,4]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor42 : cofactor42.Valid src dst (Finset.univ \ canonical (.inr 27)) := by decide +kernel

def cofactor43 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨0,![(6,false),(6,true)],![2,7]⟩,⟨7,![(0,true),(3,false),(5,false),(8,true),(12,false),(13,true),(14,false),(10,false),(2,true)],![0,1,2,3,8,6,9,7,5]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor43 : cofactor43.Valid src dst (Finset.univ \ canonical (.inr 28)) := by decide +kernel

def cofactor44 : PartitionData Edge Vertex := ⟨4,![⟨0,![(2,false),(2,true)],![0,5]⟩,⟨0,![(8,false),(8,true)],![3,8]⟩,⟨7,![(0,true),(3,false),(6,true),(10,false),(11,false),(12,false),(13,true),(9,false),(1,true)],![0,1,2,7,5,8,6,9,4]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor44 : cofactor44.Valid src dst (Finset.univ \ canonical (.inr 29)) := by decide +kernel

def cofactor45 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(14,false),(14,true)],![7,9]⟩,⟨7,![(1,true),(9,false),(13,false),(12,true),(8,false),(5,true),(6,false),(10,false),(2,true)],![0,4,9,6,8,3,2,7,5]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor45 : cofactor45.Valid src dst (Finset.univ \ canonical (.inr 30)) := by decide +kernel

def cofactor46 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(5,false),(5,true)],![2,3]⟩,⟨7,![(1,true),(9,false),(14,true),(6,false),(3,false),(4,false),(12,true),(11,false),(2,true)],![0,4,9,7,2,1,6,8,5]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor46 : cofactor46.Valid src dst (Finset.univ \ canonical (.inr 31)) := by decide +kernel

def cofactor47 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(8,false),(8,true)],![3,8]⟩,⟨7,![(1,true),(7,false),(5,false),(6,true),(14,false),(13,true),(12,false),(11,false),(2,true)],![0,4,3,2,7,9,6,8,5]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor47 : cofactor47.Valid src dst (Finset.univ \ canonical (.inr 32)) := by decide +kernel

def cofactor48 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(12,false),(12,true)],![6,8]⟩,⟨7,![(1,true),(7,false),(5,true),(3,false),(4,false),(13,false),(14,true),(10,false),(2,true)],![0,4,3,2,1,6,9,7,5]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor48 : cofactor48.Valid src dst (Finset.univ \ canonical (.inr 33)) := by decide +kernel

def cofactor49 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(7,false),(7,true)],![3,4]⟩,⟨7,![(1,false),(9,false),(13,true),(12,false),(8,true),(5,true),(6,false),(10,true),(2,false)],![0,4,9,6,8,3,2,7,5]⟩,⟨7,![(1,true),(9,true),(14,true),(6,true),(3,true),(4,true),(12,true),(11,true),(2,true)],![0,4,9,7,2,1,6,8,5]⟩]⟩

lemma validCofactor49 : cofactor49.Valid src dst (Finset.univ \ canonical (.inr 34)) := by decide +kernel

def cofactor50 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(10,false),(10,true)],![5,7]⟩,⟨7,![(1,false),(7,true),(5,false),(6,true),(14,true),(13,false),(12,true),(11,false),(2,false)],![0,4,3,2,7,9,6,8,5]⟩,⟨7,![(1,true),(9,true),(13,true),(4,true),(3,true),(5,true),(8,true),(11,true),(2,true)],![0,4,9,6,1,2,3,8,5]⟩]⟩

lemma validCofactor50 : cofactor50.Valid src dst (Finset.univ \ canonical (.inr 35)) := by decide +kernel

def cofactor51 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(8,false),(8,true)],![3,8]⟩,⟨7,![(1,false),(7,true),(5,true),(3,false),(4,false),(13,true),(14,false),(10,true),(2,false)],![0,4,3,2,1,6,9,7,5]⟩,⟨7,![(1,true),(9,true),(14,true),(6,true),(3,true),(4,true),(12,true),(11,true),(2,true)],![0,4,9,7,2,1,6,8,5]⟩]⟩

lemma validCofactor51 : cofactor51.Valid src dst (Finset.univ \ canonical (.inr 36)) := by decide +kernel

def cofactor52 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨0,![(6,false),(6,true)],![2,7]⟩,⟨6,![(3,true),(5,true),(8,false),(11,true),(10,false),(14,false),(13,true),(4,false)],![1,2,3,8,5,7,9,6]⟩,⟨7,![(0,true),(4,true),(12,true),(8,true),(7,true),(9,true),(14,true),(10,true),(2,true)],![0,1,6,8,3,4,9,7,5]⟩]⟩

lemma validCofactor52 : cofactor52.Valid src dst (Finset.univ \ canonical (.inr 37)) := by decide +kernel

def cofactor53 : PartitionData Edge Vertex := ⟨4,![⟨0,![(2,false),(2,true)],![0,5]⟩,⟨0,![(4,false),(4,true)],![1,6]⟩,⟨6,![(5,true),(7,false),(9,true),(13,false),(12,false),(11,true),(10,true),(6,false)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,true),(3,true),(6,true),(14,true),(13,true),(12,true),(8,true),(7,true),(1,true)],![0,1,2,7,9,6,8,3,4]⟩]⟩

lemma validCofactor53 : cofactor53.Valid src dst (Finset.univ \ canonical (.inr 38)) := by decide +kernel

def cofactor54 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨0,![(4,false),(4,true)],![1,6]⟩,⟨6,![(5,true),(7,false),(9,false),(13,true),(12,true),(11,false),(10,true),(6,false)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,true),(3,true),(6,true),(14,true),(9,true),(7,true),(8,true),(11,true),(2,true)],![0,1,2,7,9,4,3,8,5]⟩]⟩

lemma validCofactor54 : cofactor54.Valid src dst (Finset.univ \ canonical (.inr 39)) := by decide +kernel

def cofactor55 : PartitionData Edge Vertex := ⟨4,![⟨0,![(2,false),(2,true)],![0,5]⟩,⟨0,![(5,false),(5,true)],![2,3]⟩,⟨6,![(3,true),(6,true),(14,false),(9,true),(7,false),(8,false),(12,true),(4,false)],![1,2,7,9,4,3,8,6]⟩,⟨7,![(0,true),(4,true),(13,true),(14,true),(10,true),(11,true),(8,true),(7,true),(1,true)],![0,1,6,9,7,5,8,3,4]⟩]⟩

lemma validCofactor55 : cofactor55.Valid src dst (Finset.univ \ canonical (.inr 40)) := by decide +kernel

def cofactor56 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨0,![(4,false),(4,true)],![1,6]⟩,⟨6,![(5,false),(7,true),(9,true),(13,false),(12,false),(11,true),(10,false),(6,true)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,true),(3,true),(5,true),(8,true),(12,true),(13,true),(14,true),(10,true),(2,true)],![0,1,2,3,8,6,9,7,5]⟩]⟩

lemma validCofactor56 : cofactor56.Valid src dst (Finset.univ \ canonical (.inr 41)) := by decide +kernel

def cofactor57 : PartitionData Edge Vertex := ⟨4,![⟨0,![(2,false),(2,true)],![0,5]⟩,⟨0,![(4,false),(4,true)],![1,6]⟩,⟨6,![(5,false),(7,true),(9,false),(13,true),(12,true),(11,false),(10,false),(6,true)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,true),(3,true),(5,true),(8,true),(11,true),(10,true),(14,true),(9,true),(1,true)],![0,1,2,3,8,5,7,9,4]⟩]⟩

lemma validCofactor57 : cofactor57.Valid src dst (Finset.univ \ canonical (.inr 42)) := by decide +kernel

def cofactor58 : PartitionData Edge Vertex := ⟨4,![⟨0,![(2,false),(2,true)],![0,5]⟩,⟨0,![(3,false),(3,true)],![1,2]⟩,⟨6,![(5,true),(7,false),(9,true),(13,false),(12,true),(11,false),(10,false),(6,true)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,true),(4,true),(13,true),(14,true),(10,true),(11,true),(8,true),(7,true),(1,true)],![0,1,6,9,7,5,8,3,4]⟩]⟩

lemma validCofactor58 : cofactor58.Valid src dst (Finset.univ \ canonical (.inr 43)) := by decide +kernel

def cofactor59 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨0,![(3,false),(3,true)],![1,2]⟩,⟨6,![(5,false),(7,true),(9,true),(13,false),(12,true),(11,false),(10,true),(6,false)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,true),(4,true),(13,true),(14,true),(6,true),(5,true),(8,true),(11,true),(2,true)],![0,1,6,9,7,2,3,8,5]⟩]⟩

lemma validCofactor59 : cofactor59.Valid src dst (Finset.univ \ canonical (.inr 44)) := by decide +kernel

def cofactor60 : PartitionData Edge Vertex := ⟨4,![⟨0,![(2,false),(2,true)],![0,5]⟩,⟨0,![(9,false),(9,true)],![4,9]⟩,⟨6,![(3,false),(5,true),(8,false),(11,true),(10,true),(14,false),(13,false),(4,true)],![1,2,3,8,5,7,9,6]⟩,⟨7,![(0,true),(3,true),(6,true),(14,true),(13,true),(12,true),(8,true),(7,true),(1,true)],![0,1,2,7,9,6,8,3,4]⟩]⟩

lemma validCofactor60 : cofactor60.Valid src dst (Finset.univ \ canonical (.inr 45)) := by decide +kernel

def cofactor61 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨0,![(8,false),(8,true)],![3,8]⟩,⟨6,![(0,true),(3,false),(6,true),(14,false),(13,true),(12,false),(11,false),(2,true)],![0,1,2,7,9,6,8,5]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor61 : cofactor61.Valid src dst (Finset.univ \ canonical (.inr 46)) := by decide +kernel

def cofactor62 : PartitionData Edge Vertex := ⟨4,![⟨0,![(1,false),(1,true)],![0,4]⟩,⟨0,![(3,false),(3,true)],![1,2]⟩,⟨6,![(5,true),(7,false),(9,false),(13,true),(12,false),(11,true),(10,false),(6,true)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,true),(4,true),(12,true),(8,true),(7,true),(9,true),(14,true),(10,true),(2,true)],![0,1,6,8,3,4,9,7,5]⟩]⟩

lemma validCofactor62 : cofactor62.Valid src dst (Finset.univ \ canonical (.inr 47)) := by decide +kernel

def cofactor63 : PartitionData Edge Vertex := ⟨4,![⟨0,![(2,false),(2,true)],![0,5]⟩,⟨0,![(3,false),(3,true)],![1,2]⟩,⟨6,![(5,false),(7,true),(9,false),(13,true),(12,false),(11,true),(10,true),(6,false)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(0,true),(4,true),(12,true),(8,true),(5,true),(6,true),(14,true),(9,true),(1,true)],![0,1,6,8,3,2,7,9,4]⟩]⟩

lemma validCofactor63 : cofactor63.Valid src dst (Finset.univ \ canonical (.inr 48)) := by decide +kernel

def cofactor64 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(8,false),(8,true)],![3,8]⟩,⟨6,![(5,true),(7,true),(9,false),(13,true),(12,false),(11,false),(10,true),(6,false)],![2,3,4,9,6,8,5,7]⟩,⟨7,![(1,true),(9,true),(14,true),(6,true),(3,true),(4,true),(12,true),(11,true),(2,true)],![0,4,9,7,2,1,6,8,5]⟩]⟩

lemma validCofactor64 : cofactor64.Valid src dst (Finset.univ \ canonical (.inr 49)) := by decide +kernel

def cofactor65 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(8,false),(8,true)],![3,8]⟩,⟨6,![(1,true),(9,false),(13,true),(4,false),(3,false),(6,true),(10,false),(2,true)],![0,4,9,6,1,2,7,5]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor65 : cofactor65.Valid src dst (Finset.univ \ canonical (.inr 50)) := by decide +kernel

def cofactor66 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(9,false),(9,true)],![4,9]⟩,⟨6,![(3,true),(5,false),(8,true),(11,false),(10,true),(14,false),(13,false),(4,true)],![1,2,3,8,5,7,9,6]⟩,⟨7,![(1,true),(7,true),(5,true),(6,true),(14,true),(13,true),(12,true),(11,true),(2,true)],![0,4,3,2,7,9,6,8,5]⟩]⟩

lemma validCofactor66 : cofactor66.Valid src dst (Finset.univ \ canonical (.inr 51)) := by decide +kernel

def cofactor67 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(6,false),(6,true)],![2,7]⟩,⟨6,![(1,true),(7,false),(8,true),(12,false),(13,true),(14,false),(10,false),(2,true)],![0,4,3,8,6,9,7,5]⟩,⟨7,![(3,true),(5,true),(7,true),(9,true),(14,true),(10,true),(11,true),(12,true),(4,true)],![1,2,3,4,9,7,5,8,6]⟩]⟩

lemma validCofactor67 : cofactor67.Valid src dst (Finset.univ \ canonical (.inr 52)) := by decide +kernel

def cofactor68 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(7,false),(7,true)],![3,4]⟩,⟨6,![(3,false),(5,true),(8,true),(11,false),(10,true),(14,false),(13,true),(4,false)],![1,2,3,8,5,7,9,6]⟩,⟨7,![(1,true),(9,true),(14,true),(6,true),(3,true),(4,true),(12,true),(11,true),(2,true)],![0,4,9,7,2,1,6,8,5]⟩]⟩

lemma validCofactor68 : cofactor68.Valid src dst (Finset.univ \ canonical (.inr 53)) := by decide +kernel

def cofactor69 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(5,false),(5,true)],![2,3]⟩,⟨6,![(1,true),(7,false),(8,false),(12,true),(13,false),(14,true),(10,false),(2,true)],![0,4,3,8,6,9,7,5]⟩,⟨7,![(3,true),(6,true),(10,true),(11,true),(8,true),(7,true),(9,true),(13,true),(4,true)],![1,2,7,5,8,3,4,9,6]⟩]⟩

lemma validCofactor69 : cofactor69.Valid src dst (Finset.univ \ canonical (.inr 54)) := by decide +kernel

def cofactor70 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(6,false),(6,true)],![2,7]⟩,⟨6,![(1,false),(7,true),(8,false),(12,true),(13,false),(14,true),(10,true),(2,false)],![0,4,3,8,6,9,7,5]⟩,⟨7,![(1,true),(9,true),(13,true),(4,true),(3,true),(5,true),(8,true),(11,true),(2,true)],![0,4,9,6,1,2,3,8,5]⟩]⟩

lemma validCofactor70 : cofactor70.Valid src dst (Finset.univ \ canonical (.inr 55)) := by decide +kernel

def cofactor71 : PartitionData Edge Vertex := ⟨4,![⟨0,![(0,false),(0,true)],![0,1]⟩,⟨0,![(5,false),(5,true)],![2,3]⟩,⟨6,![(1,false),(7,true),(8,true),(12,false),(13,true),(14,false),(10,true),(2,false)],![0,4,3,8,6,9,7,5]⟩,⟨7,![(1,true),(9,true),(14,true),(6,true),(3,true),(4,true),(12,true),(11,true),(2,true)],![0,4,9,7,2,1,6,8,5]⟩]⟩

lemma validCofactor71 : cofactor71.Valid src dst (Finset.univ \ canonical (.inr 56)) := by decide +kernel

lemma canonical_cofactor (i : Fin 15 ⊕ Fin 57) :
    ∃ D, Partition code (Finset.univ \ canonical i) D ∧ D.card = 4 := by

  cases i with

  | inl i =>

    fin_cases i

    · exact PartitionData.exists_partition validCofactor0

    · exact PartitionData.exists_partition validCofactor1

    · exact PartitionData.exists_partition validCofactor2

    · exact PartitionData.exists_partition validCofactor3

    · exact PartitionData.exists_partition validCofactor4

    · exact PartitionData.exists_partition validCofactor5

    · exact PartitionData.exists_partition validCofactor6

    · exact PartitionData.exists_partition validCofactor7

    · exact PartitionData.exists_partition validCofactor8

    · exact PartitionData.exists_partition validCofactor9

    · exact PartitionData.exists_partition validCofactor10

    · exact PartitionData.exists_partition validCofactor11

    · exact PartitionData.exists_partition validCofactor12

    · exact PartitionData.exists_partition validCofactor13

    · exact PartitionData.exists_partition validCofactor14

  | inr i =>

    fin_cases i

    · exact PartitionData.exists_partition validCofactor15

    · exact PartitionData.exists_partition validCofactor16

    · exact PartitionData.exists_partition validCofactor17

    · exact PartitionData.exists_partition validCofactor18

    · exact PartitionData.exists_partition validCofactor19

    · exact PartitionData.exists_partition validCofactor20

    · exact PartitionData.exists_partition validCofactor21

    · exact PartitionData.exists_partition validCofactor22

    · exact PartitionData.exists_partition validCofactor23

    · exact PartitionData.exists_partition validCofactor24

    · exact PartitionData.exists_partition validCofactor25

    · exact PartitionData.exists_partition validCofactor26

    · exact PartitionData.exists_partition validCofactor27

    · exact PartitionData.exists_partition validCofactor28

    · exact PartitionData.exists_partition validCofactor29

    · exact PartitionData.exists_partition validCofactor30

    · exact PartitionData.exists_partition validCofactor31

    · exact PartitionData.exists_partition validCofactor32

    · exact PartitionData.exists_partition validCofactor33

    · exact PartitionData.exists_partition validCofactor34

    · exact PartitionData.exists_partition validCofactor35

    · exact PartitionData.exists_partition validCofactor36

    · exact PartitionData.exists_partition validCofactor37

    · exact PartitionData.exists_partition validCofactor38

    · exact PartitionData.exists_partition validCofactor39

    · exact PartitionData.exists_partition validCofactor40

    · exact PartitionData.exists_partition validCofactor41

    · exact PartitionData.exists_partition validCofactor42

    · exact PartitionData.exists_partition validCofactor43

    · exact PartitionData.exists_partition validCofactor44

    · exact PartitionData.exists_partition validCofactor45

    · exact PartitionData.exists_partition validCofactor46

    · exact PartitionData.exists_partition validCofactor47

    · exact PartitionData.exists_partition validCofactor48

    · exact PartitionData.exists_partition validCofactor49

    · exact PartitionData.exists_partition validCofactor50

    · exact PartitionData.exists_partition validCofactor51

    · exact PartitionData.exists_partition validCofactor52

    · exact PartitionData.exists_partition validCofactor53

    · exact PartitionData.exists_partition validCofactor54

    · exact PartitionData.exists_partition validCofactor55

    · exact PartitionData.exists_partition validCofactor56

    · exact PartitionData.exists_partition validCofactor57

    · exact PartitionData.exists_partition validCofactor58

    · exact PartitionData.exists_partition validCofactor59

    · exact PartitionData.exists_partition validCofactor60

    · exact PartitionData.exists_partition validCofactor61

    · exact PartitionData.exists_partition validCofactor62

    · exact PartitionData.exists_partition validCofactor63

    · exact PartitionData.exists_partition validCofactor64

    · exact PartitionData.exists_partition validCofactor65

    · exact PartitionData.exists_partition validCofactor66

    · exact PartitionData.exists_partition validCofactor67

    · exact PartitionData.exists_partition validCofactor68

    · exact PartitionData.exists_partition validCofactor69

    · exact PartitionData.exists_partition validCofactor70

    · exact PartitionData.exists_partition validCofactor71

lemma cofactor_upper (s : Finset Edge) (hs : Circuit code s) :
    ∃ D, Partition code (Finset.univ \ s) D ∧ D.card = 4 := by

  rcases Parallel.circuit_cases PetersenBase.src PetersenBase.dst hs with ⟨e,rfl⟩ | ⟨t,b,ht,he⟩

  · exact canonical_cofactor (.inl e)

  · obtain ⟨i,rfl⟩ := PetersenBase.catalogue t ht

    rw [he]

    exact Parallel.cofactor_partition PetersenBase.src PetersenBase.dst (PetersenBase.edges i) b 4
      (canonical_cofactor (.inr i))

#print axioms full_number

#print axioms cofactor_upper

end Erdos184Work.DoublePetersen

