import VOA.Classification.COne.OrbIcoVVacKernel
import VOA.Examples.VirasoroFusionNonresonantWard

/-! Actual normalized Verma Ward sequences on both symbol channels.
Nonreal deformation parameters avoid every positive ordinary diagonal;
no generic fusion or Ward-sequence existence is assumed. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA InverseDS.VirasoroVerma VirModule

abbrev incomingWeight (t : ℂ) := vermaBSAWeight 13 t

def symbolTargetWeight (self : Bool) (t : ℂ) : ℂ :=
  if self then incomingWeight t else 0

theorem incoming_gauge (t : ℂ) (ht : t ≠ 0) :
    (-6:ℂ)^2+(t-1)*(-6)-t*incomingWeight t=0 := by
  unfold incomingWeight vermaBSAWeight
  norm_num
  field_simp
  ring

theorem symbol_diagonal_initial (self : Bool) (t : ℂ) (ht : t ≠ 0) :
    wardBSASourceDiagonal (symbolTargetWeight self t) (incomingWeight t) t 13 0 13
      (incomingWeight t+13)=0 := by
  apply (wardBSASourceDiagonal_zero_iff_root _ _ _ _ (-6) 13 0
    (by norm_num) ht (incoming_gauge t ht)).mpr
  cases self
  · refine ⟨12,by norm_num,?_⟩
    unfold symbolTargetWeight incomingWeight vermaBSAWeight fusionRoot
    norm_num
    field_simp
    ring
  · refine ⟨6,by norm_num,?_⟩
    unfold symbolTargetWeight incomingWeight vermaBSAWeight fusionRoot
    norm_num
    field_simp
    ring

theorem symbol_diagonal_nonreal (self : Bool) (t : ℂ) (him : t.im ≠ 0)
    (r : ℕ) (hr : 0 < r) :
    wardBSASourceDiagonal (symbolTargetWeight self t) (incomingWeight t) t 13 r 13
      (incomingWeight t+13) ≠ 0 := by
  have ht : t ≠ 0 := by intro hz; apply him; simp [hz]
  intro hz
  obtain ⟨i,hi,he⟩ := (wardBSASourceDiagonal_zero_iff_root _ _ _ _ (-6) 13 r
    (by norm_num) ht (incoming_gauge t ht)).mp hz
  cases self
  · have ha : (symbolTargetWeight false t+(r:ℂ)-incomingWeight t-
        fusionRoot (incomingWeight t) t (-6) 13 i)*t =
        ((r:ℂ)+12-(i:ℂ))*t-((i:ℂ)-12)*((i:ℂ)-13) := by
      unfold symbolTargetWeight incomingWeight vermaBSAWeight fusionRoot
      norm_num
      field_simp
      ring
    rw [he,sub_self,zero_mul] at ha
    have himEq := congrArg Complex.im ha
    norm_num [Complex.sub_im,Complex.mul_im,Complex.add_im,
      Complex.sub_re,Complex.add_re] at himEq
    have hiR : (r:ℝ)+12-(i:ℝ)=0 :=
      himEq.resolve_right him
    have hir : (r:ℤ)+12-(i:ℤ)=0 := by exact_mod_cast hiR
    omega
  · have ha : (symbolTargetWeight true t+(r:ℂ)-incomingWeight t-
        fusionRoot (incomingWeight t) t (-6) 13 i)*t =
        ((r:ℂ)+6-(i:ℂ))*t-((i:ℂ)-6)*((i:ℂ)-19) := by
      unfold symbolTargetWeight incomingWeight vermaBSAWeight fusionRoot
      norm_num
      field_simp
      ring
    rw [he,sub_self,zero_mul] at ha
    have himEq := congrArg Complex.im ha
    norm_num [Complex.sub_im,Complex.mul_im,Complex.add_im,
      Complex.sub_re,Complex.add_re] at himEq
    have hiR : (r:ℝ)+6-(i:ℝ)=0 :=
      himEq.resolve_right him
    have hir : (r:ℤ)+6-(i:ℤ)=0 := by exact_mod_cast hiR
    have hre := congrArg Complex.re ha
    norm_num [Complex.sub_re,Complex.mul_re,Complex.add_re,
      Complex.sub_im,Complex.add_im] at hre
    rw [hiR,zero_mul] at hre
    have hp : ((i:ℝ)-6)*((i:ℝ)-19)=0 := by linarith
    rcases mul_eq_zero.mp hp with hz | hz
    · have hiz : (i:ℤ)-6=0 := by exact_mod_cast hz
      omega
    · have hiz : (i:ℤ)-19=0 := by exact_mod_cast hz
      omega

theorem highest_mem_level_zero (c h : ℂ) : highestVector c h ∈ sortedSpan c h 0 :=
  negWord_mem_sortedSpan_of_sorted c h sortedWord_nil rfl

attribute [local irreducible] wardSourceAt wardP1Map wardP2Map

set_option maxHeartbeats 1000000 in
theorem exists_symbol_ward_sequence (self : Bool) (t : ℂ) (him : t.im ≠ 0) (R : ℕ) :
    ∃ f : wardSequenceSpace (vermaBSACharge t) (symbolTargetWeight self t),
      f.val 0=highestVector _ _ ∧
      (∀ r<R+3, (wardSourceAt (vermaBSACharge t) (symbolTargetWeight self t)
        (incomingWeight t) t (incomingWeight t) 13 f).val r=0) ∧
      (∀ r<R+2, (wardP1Map (vermaBSACharge t) (symbolTargetWeight self t)
        (incomingWeight t) (incomingWeight t) f).val r=0) ∧
      (∀ r<R+1, (wardP2Map (vermaBSACharge t) (symbolTargetWeight self t)
        (incomingWeight t) (incomingWeight t) f).val r=0) := by
  have ht : t ≠ 0 := by intro hz; apply him; simp [hz]
  have hd := symbol_diagonal_nonreal self t him
  obtain ⟨f,hf0,hf⟩ := exists_ward_partial_kernel (vermaBSACharge t)
    (symbolTargetWeight self t)
    (wardSourceAt (vermaBSACharge t) (symbolTargetWeight self t)
      (incomingWeight t) t (incomingWeight t) 13)
    (fun r => wardBSASourceDiagonal (symbolTargetWeight self t) (incomingWeight t)
      t 13 r 13 (incomingWeight t+13)) (R+3)
    (fun r f hf => wardSourceAt_diagonal _ _ _ _ _ _ r f hf)
    (fun r f hf => wardSourceAt_below _ _ _ _ _ _ r f hf)
    (symbol_diagonal_initial self t ht) (fun r hr _ => hd r hr)
    ⟨highestVector _ _,highest_mem_level_zero _ _⟩
  refine ⟨f,hf0,hf,?_,?_⟩
  · simpa using nonresonant_first_below (symbolTargetWeight self t) (incomingWeight t)
      t 13 (R+3) ht (by norm_num) f hf (fun r hr _ => hd r hr)
  · simpa using nonresonant_second_below (symbolTargetWeight self t) (incomingWeight t)
      t 13 (R+3) ht (by norm_num) f hf (fun r hr _ => hd r hr)

end VOA.Classification.COne.OrbIcoV
