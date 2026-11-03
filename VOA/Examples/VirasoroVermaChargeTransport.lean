/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroVermaUniformStraightening
import VOA.Examples.VirasoroMinimalThreeChargeFamily

/-!
# Transporting creation words between actual charges

The PBW coordinates identify the underlying vector spaces of Verma modules
at different charges. This map preserves all negative modes and each level.
It is not an intertwiner for positive modes: their charge dependence is
exactly the information needed in a norm-derivative calculation.
-/
namespace VOA.InverseDS.VirasoroVerma

/-- Keep every sorted-word coordinate fixed while changing central charge.
The highest weight is fixed, so the descendant scalar parameters agree. -/
noncomputable def chargeTransport (c c' h : ℂ) : Verma c h ≃ₗ[ℂ] Verma c' h :=
  (vermaSortedBasis c h).repr.trans (vermaSortedBasis c' h).repr.symm

/-- Uniform straightening ensures that even an unsorted negative word
is sent to the identical word in the new actual module. -/
theorem chargeTransport_word (c c' h : ℂ) (w : List ℕ) :
    chargeTransport c c' h (negWord c h w) = negWord c' h w := by
  apply (vermaSortedBasis c' h).repr.injective
  change (vermaSortedBasis c' h).repr
    ((vermaSortedBasis c' h).repr.symm ((vermaSortedBasis c h).repr (negWord c h w))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact verma_negWord_coordinates_independent c h c' h w

/-- The coordinate transport preserves the normalized highest vector. -/
@[simp] theorem chargeTransport_highest (c c' h : ℂ) :
    chargeTransport c c' h (highestVector c h) = highestVector c' h :=
  chargeTransport_word c c' h []

/-- Every negative creation mode commutes with the coordinate transport.
This follows on PBW words from prefixing one letter, then by linearity. -/
theorem chargeTransport_creation (c c' h : ℂ) (i : ℕ) (v : Verma c h) :
    chargeTransport c c' h (vermaMode c h (-((i:ℕ):ℤ)-1) v) =
      vermaMode c' h (-((i:ℕ):ℤ)-1) (chargeTransport c c' h v) := by
  have he : (chargeTransport c c' h).toLinearMap.comp (vermaMode c h (-((i:ℕ):ℤ)-1)) =
      (vermaMode c' h (-((i:ℕ):ℤ)-1)).comp (chargeTransport c c' h).toLinearMap := by
    apply (vermaSortedBasis c h).ext
    intro w
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,vermaSortedBasis_apply]
    rw [← negWord_cons,chargeTransport_word,chargeTransport_word,negWord_cons]
  exact LinearMap.congr_fun he v

/-- The same intertwining statement for any strictly negative integer mode. -/
theorem chargeTransport_negative (c c' h : ℂ) (m : ℤ) (hm : m<0) (v : Verma c h) :
    chargeTransport c c' h (vermaMode c h m v) =
      vermaMode c' h m (chargeTransport c c' h v) := by
  have he : m=-((( -m-1).toNat:ℕ):ℤ)-1 := by omega
  rw [he]
  exact chargeTransport_creation c c' h _ v

/-- Transport preserves each actual word level because it preserves every
partition word and its energy, not merely the total underlying space. -/
theorem chargeTransport_level (c c' h : ℂ) (n : ℕ) (v : Verma c h)
    (hv : v∈sortedSpan c h n) : chargeTransport c c' h v∈sortedSpan c' h n := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w,hw,hn,rfl⟩ := hx
    rw [chargeTransport_word]
    exact negWord_mem_sortedSpan_of_sorted c' h hw hn
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using (sortedSpan c' h n).add_mem hx hy
  | smul a x _ hx => simpa only [map_smul] using (sortedSpan c' h n).smul_mem a hx

/-- Apply the charge transport coefficientwise to an actual level sequence. -/
noncomputable def chargeSequence (c c' h : ℂ) :
    wardSequenceSpace c h →ₗ[ℂ] wardSequenceSpace c' h where
  toFun f := ⟨fun r => chargeTransport c c' h (f.val r),
    fun r => chargeTransport_level c c' h r _ (f.property r)⟩
  map_add' f g := by ext r; exact map_add _ _ _
  map_smul' a f := by ext r; exact map_smul (chargeTransport c c' h) a (f.val r)

/-- The finite negative-mode sum transports coefficientwise. All its
indices are strictly negative because the sum uses earlier coefficients. -/
theorem chargeTransport_wardSource (c c' h : ℂ) (f : ℕ → Verma c h) (r : ℕ) :
    chargeTransport c c' h (wardSource c h f r) =
      wardSource c' h (fun j => chargeTransport c c' h (f j)) r := by
  unfold wardSource
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact chargeTransport_negative c c' h _ (by have := j.isLt; omega) _

/-- The first negative descendant is compatible with charge transport. -/
theorem chargeSequence_D1 (c c' h b a : ℂ) (f : wardSequenceSpace c h) :
    chargeSequence c c' h (wardD1Map c h b a f) =
      wardD1Map c' h b a (chargeSequence c c' h f) := by
  apply Subtype.ext
  funext r
  exact map_smul (chargeTransport c c' h) _ _

/-- The second negative descendant is compatible as well; its mode sum
uses the preceding negative-mode transport, and its diagonal is scalar. -/
theorem chargeSequence_D2 (c c' h b a : ℂ) (f : wardSequenceSpace c h) :
    chargeSequence c c' h (wardD2Map c h b a f) =
      wardD2Map c' h b a (chargeSequence c c' h f) := by
  apply Subtype.ext
  funext r
  change chargeTransport c c' h (wardSource c h f.val r+_ • f.val r) = _
  rw [map_add,map_smul,chargeTransport_wardSource]
  rfl

/-- Transport each field-weight component of an actual sequence family. -/
noncomputable def chargeField (c c' h : ℂ) :
    (ℂ → wardSequenceSpace c h) →ₗ[ℂ] (ℂ → wardSequenceSpace c' h) where
  toFun f a := chargeSequence c c' h (f a)
  map_add' f g := by funext a; exact map_add _ _ _
  map_smul' z f := by funext a; exact map_smul (chargeSequence c c' h) z (f a)

/-- The field-weight shift in the first descendant is unchanged by charge. -/
theorem chargeField_A (c c' h b : ℂ) (f : ℂ → wardSequenceSpace c h) :
    chargeField c c' h (wardA c h b f) = wardA c' h b (chargeField c c' h f) := by
  funext a
  exact chargeSequence_D1 c c' h b (a-1) (f (a-1))

/-- The second global negative descendant also transports with its shift. -/
theorem chargeField_B (c c' h b : ℂ) (f : ℂ → wardSequenceSpace c h) :
    chargeField c c' h (wardB c h b f) = wardB c' h b (chargeField c c' h f) := by
  funext a
  exact chargeSequence_D2 c c' h b (a-2) (f (a-2))

/-- The third descendant is the commutator of the first two, so its full
operator, including its noncentral contributions, transports too. -/
theorem chargeField_D3 (c c' h b : ℂ) (f : ℂ → wardSequenceSpace c h) :
    chargeField c c' h (wardNegative c h b 1 f) =
      wardNegative c' h b 1 (chargeField c c' h f) := by
  have he (d : ℂ) : wardNegative d h b 1=wardA d h b*wardB d h b-wardB d h b*wardA d h b := by
    simp [wardNegative,DescendantTower.tower,LieRing.of_associative_ring_bracket]
  simp only [he,LinearMap.sub_apply,Module.End.mul_apply,map_sub,chargeField_A,chargeField_B]

/-- The complete cubic source transports between charges on every input.
This uses the actual operator identity, not only its diagonal coefficients. -/
theorem chargeField_source_three (c c' h b t : ℂ) (f : ℂ → wardSequenceSpace c h) :
    chargeField c c' h (wardBSASourceOperator c h b t 3 3 f) =
      wardBSASourceOperator c' h b t 3 3 (chargeField c c' h f) := by
  simp only [wardBSASourceOperator_three,LinearMap.sub_apply,LinearMap.add_apply,
    LinearMap.smul_apply,Module.End.mul_apply,map_add,map_sub,map_smul,
    chargeField_A,chargeField_B,chargeField_D3]

/-- A sequence supported at one field weight retains that support after
transport; only its actual module states have changed. -/
theorem chargeField_lift (c c' h a : ℂ) (f : wardSequenceSpace c h) :
    chargeField c c' h (wardFieldLift c h a f) =
      wardFieldLift c' h a (chargeSequence c c' h f) := by
  classical
  funext w
  change chargeSequence c c' h (if w=a then f else 0) =
    if w=a then chargeSequence c c' h f else 0
  split_ifs <;> simp

/-- Evaluation gives charge transport for the actual seed-three source
on level sequences. This will remove the choices in the charge family. -/
theorem chargeSequence_source_three (c c' h b t a : ℂ) (f : wardSequenceSpace c h) :
    chargeSequence c c' h (wardSourceAt c h b t a 3 f) =
      wardSourceAt c' h b t a 3 (chargeSequence c c' h f) := by
  have hh := chargeField_source_three c c' h b t (wardFieldLift c h a f)
  rw [chargeField_lift] at hh
  exact congrFun hh (a+3)

/-- Transporting a chosen q=3 kernel preserves all its preterminal zero
equations. No equality between independently chosen whole sequences is needed. -/
theorem chargeSequence_minimalThree_below (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (c c' : ℂ) (r : ℕ) (hr : r<(p-1)*2) :
    (wardSourceAt c' 0 (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
      (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3
      (chargeSequence c c' 0 (minimalThreeChargeKernel p hp hcop c))).val r=0 := by
  rw [← chargeSequence_source_three]
  change chargeTransport c c' 0 (_)=0
  rw [minimalThreeChargeKernel_below p hp hcop c r hr,map_zero]

/-- The actual terminal source has fixed PBW coordinates across all
charges. Triangular uniqueness removes the charge-by-charge choices. -/
theorem chargeTransport_minimalThree_source (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (c c' : ℂ) :
    chargeTransport c c' 0 (minimalThreeChargeSource p hp hcop c) =
      minimalThreeChargeSource p hp hcop c' := by
  have hh := ward_partial_kernel_terminal_unique c' 0
    (wardSourceAt c' 0 (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
      (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3)
    (fun r => wardBSASourceDiagonal 0 (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ)))
      ((3:ℂ)/(p:ℂ)) 3 r 3 (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+3)) ((p-1)*2)
    (fun r f hf => wardSourceAt_diagonal _ _ _ _ _ _ r f hf)
    (fun r hr hrN => minimalThree_diagonal_interior p r hp hcop hr hrN)
    (minimalThree_diagonal_terminal p hp)
    (chargeSequence c c' 0 (minimalThreeChargeKernel p hp hcop c))
    (minimalThreeChargeKernel p hp hcop c') ?_
    (fun r hr => chargeSequence_minimalThree_below p hp hcop c c' r hr)
    (minimalThreeChargeKernel_below p hp hcop c')
  · rw [← chargeSequence_source_three] at hh
    exact hh
  · change chargeTransport c c' 0 ((minimalThreeChargeKernel p hp hcop c).val 0) = _
    rw [minimalThreeChargeKernel_zero,minimalThreeChargeKernel_zero,chargeTransport_highest]

end VOA.InverseDS.VirasoroVerma
