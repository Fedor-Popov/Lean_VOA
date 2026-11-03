import VOA.Classification.COne.OrbIcoVScalarConvolution

/-! A concrete chosen family of genuine finite Verma Ward kernels, and
its exact normalized even scalar recurrence on the nonreal locus. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA InverseDS.VirasoroVerma

noncomputable def genericSymbolWard (self : Bool) (N : ℕ) (t : ℂ) (him : t.im≠0) :
    wardSequenceSpace (vermaBSACharge t) (symbolTargetWeight self t) :=
  Classical.choose (exists_symbol_ward_sequence self t him (2*N))

theorem genericSymbolWard_spec (self : Bool) (N : ℕ) (t : ℂ) (him : t.im≠0) :
    (genericSymbolWard self N t him).val 0=highestVector _ _ ∧
      (∀ r<2*N+3, (wardSourceAt (vermaBSACharge t) (symbolTargetWeight self t)
        (incomingWeight t) t (incomingWeight t) 13
        (genericSymbolWard self N t him)).val r=0) ∧
      (∀ r<2*N+2, (wardP1Map (vermaBSACharge t) (symbolTargetWeight self t)
        (incomingWeight t) (incomingWeight t)
        (genericSymbolWard self N t him)).val r=0) ∧
      (∀ r<2*N+1, (wardP2Map (vermaBSACharge t) (symbolTargetWeight self t)
        (incomingWeight t) (incomingWeight t)
        (genericSymbolWard self N t him)).val r=0) :=
  Classical.choose_spec (exists_symbol_ward_sequence self t him (2*N))

def genericSymbolCoefficient (self : Bool) (N : ℕ) (t : ℂ) (n : ℕ) : ℂ :=
  if him : t.im≠0 then (2:ℂ)^n*uniformProbe (vermaBSACharge t)
    (symbolTargetWeight self t) ((genericSymbolWard self N t him).val (2*n)) else 0

theorem incomingWeight_eq_widthH (t : ℂ) : incomingWeight t=OrbIcoW.widthH t := by
  unfold incomingWeight vermaBSAWeight OrbIcoW.widthH
  norm_num
  ring

theorem genericSymbolCoefficient_zero (self : Bool) (N : ℕ) (t : ℂ) (him : t.im≠0) :
    genericSymbolCoefficient self N t 0=1 := by
  rw [genericSymbolCoefficient,dif_pos him]
  simp only [pow_zero,Nat.mul_zero,one_mul,(genericSymbolWard_spec self N t him).1,
    uniformProbe_highest]

theorem genericSymbolCoefficient_recurrence (self : Bool) (N n : ℕ) (hn : n≤N)
    (t : ℂ) (him : t.im≠0) :
    (∑ q : Fin 7, (if (q:ℕ)≤n then
      OrbIcoW.widthAt self (n-q) q t*genericSymbolCoefficient self N t (n-q) else 0))=0 := by
  have hh := actual_even_width_recurrence (vermaBSACharge t) (incomingWeight t)
    (symbolTargetWeight self t) t N n (genericSymbolWard self N t him) hn
    ((genericSymbolWard_spec self N t him).2.1 (2*n) (by omega))
  simpa only [genericSymbolCoefficient,dif_pos him,OrbIcoW.widthAt,
    ← incomingWeight_eq_widthH,symbolTargetWeight] using hh

end VOA.Classification.COne.OrbIcoV
