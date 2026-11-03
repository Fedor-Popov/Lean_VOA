/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.VirasoroMinimalThreeVacuum

/-!
# The q=3 source family at every central charge

The triangular construction only divides by charge-independent scalar
entries. Keeping the minimal-model seed parameters fixed therefore produces
an actual vacuum vector at every charge. Its L1 equation and nonzero vacuum
survival hold throughout this family. Singularity at L2 remains special.
-/
namespace VOA.InverseDS.VirasoroVerma
open VirModule

/-- The first input defect bound requires no prescribed module charge.
The ordinary interior diagonal condition is its only inversion input. -/
theorem nonresonant_first_below_at_charge (c h b t : ℂ) (N R : ℕ)
    (ht : t≠0) (hN : 2≤N) (f : wardSequenceSpace c h)
    (hf : ∀ r<R, (wardSourceAt c h b t (vermaBSAWeight N t) N f).val r=0)
    (hd : ∀ r, 0<r → r<R → wardBSASourceDiagonal h b t N r N (vermaBSAWeight N t+(N:ℂ))≠0) :
    ∀ r<R-1, (wardP1Map c h b (vermaBSAWeight N t) f).val r=0 := by
  apply ward_zero_of_source_zero _ _ (wardSourceAt c h b t (vermaBSAWeight N t-1) N)
    (fun r => wardBSASourceDiagonal h b t N r N ((vermaBSAWeight N t-1)+(N:ℂ)))
  · exact fun r f hf => wardSourceAt_diagonal _ _ _ _ _ _ r f hf
  · intro r hr
    rw [wardSourceDiagonal_shift_one]
    exact hd (r+1) (by omega) (by omega)
  · intro r hr
    rw [← wardSourceAt_first_defect _ _ _ t N ht hN]
    change vermaMode _ _ 1 _-(_ : ℂ) • _=0
    rw [hf (r+1) (by omega),hf r (by omega),map_zero,smul_zero,sub_zero]

/-- At any module charge, a zero terminal diagonal makes the actual
terminal state quasiprimary. No second Ward equation is asserted here. -/
theorem nonresonant_terminal_L1_at_charge (c h b t : ℂ) (N R : ℕ)
    (ht : t≠0) (hN : 2≤N) (hR : 0<R) (f : wardSequenceSpace c h)
    (hf : ∀ r<R, (wardSourceAt c h b t (vermaBSAWeight N t) N f).val r=0)
    (hd : ∀ r, 0<r → r<R → wardBSASourceDiagonal h b t N r N (vermaBSAWeight N t+(N:ℂ))≠0)
    (hz : wardBSASourceDiagonal h b t N R N (vermaBSAWeight N t+(N:ℂ))=0) :
    vermaMode c h 1 ((wardSourceAt c h b t (vermaBSAWeight N t) N f).val R)=0 := by
  have hh := wardSourceAt_first_defect c h b t N ht hN f
  have he := congrArg (fun g : wardSequenceSpace c h => g.val (R-1)) hh
  dsimp only at he
  rw [wardSourceAt_diagonal _ _ _ _ _ _ _ _
    (nonresonant_first_below_at_charge c h b t N R ht hN f hf hd),wardSourceDiagonal_shift_one,
    show R-1+1=R by omega,hz,zero_smul] at he
  change vermaMode _ _ 1 _-(_ : ℂ) • _=0 at he
  rw [hf (R-1) (by omega),smul_zero,sub_zero] at he
  simpa only [show R-1+1=R by omega] using he

/-- The seed-three diagonal starts at zero at the rational vacuum parameters,
independently of the actual module charge. -/
theorem minimalThree_diagonal_initial (p : ℕ) (hp : 2≤p) :
    wardBSASourceDiagonal 0 (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ)))
      ((3:ℂ)/(p:ℂ)) 3 0 3 (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+3)=0 := by
  have hh := wardBSASourceDiagonal_label_initial (p-1) 3 ((3:ℂ)/(p:ℂ))
    (by omega) (minimal_three_parameter_ne_zero p (by omega))
  norm_num at hh
  rw [fusionThree_minimal_weight_zero p hp] at hh
  exact hh

/-- Every interior seed-three diagonal is nonzero at coprime vacuum labels.
This is a scalar fact, hence usable at every actual module charge. -/
theorem minimalThree_diagonal_interior (p r : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (hr : 0<r) (hrN : r<(p-1)*2) :
    wardBSASourceDiagonal 0 (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ)))
      ((3:ℂ)/(p:ℂ)) 3 r 3 (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+3)≠0 := by
  have hh := wardBSASourceDiagonal_minimal_three p r hp hcop hr hrN
  have hw : fusionKacWeight ((p-1:ℕ):ℂ) ((3:ℂ)-1) ((3:ℂ)/(p:ℂ))=0 := by
    convert fusionThree_minimal_weight_zero p hp using 1 <;> norm_num
  rw [hw] at hh
  exact hh

/-- The terminal scalar is also zero regardless of the actual module charge. -/
theorem minimalThree_diagonal_terminal (p : ℕ) (hp : 2≤p) :
    wardBSASourceDiagonal 0 (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ)))
      ((3:ℂ)/(p:ℂ)) 3 ((p-1)*2) 3 (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+3)=0 := by
  have hh := wardBSASourceDiagonal_label_terminal (p-1) 3 ((3:ℂ)/(p:ℂ))
    (by omega) (minimal_three_parameter_ne_zero p (by omega))
  norm_num at hh
  rw [fusionThree_minimal_weight_zero p hp] at hh
  exact hh

/-- A normalized preterminal actual sequence exists for every charge,
while the seed parameters remain those of the chosen M(p,3) label. -/
theorem exists_minimalThree_charge_kernel (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) (c : ℂ) :
    ∃ f : wardSequenceSpace c 0, f.val 0=highestVector c 0 ∧
      ∀ r<(p-1)*2,
        (wardSourceAt c 0 (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
          (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3 f).val r=0 := by
  refine exists_ward_partial_kernel c 0
    (wardSourceAt c 0 (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
      (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3)
    (fun r => wardBSASourceDiagonal 0 (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ)))
      ((3:ℂ)/(p:ℂ)) 3 r 3 (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))+3)) ((p-1)*2)
    ?_ ?_ (minimalThree_diagonal_initial p hp) ?_ (fusionLeadingState _ _)
  · exact fun r f hf => wardSourceAt_diagonal _ _ _ _ _ _ r f hf
  · exact fun r f hf => wardSourceAt_below _ _ _ _ _ _ r f hf
  · exact fun r hr hrN => minimalThree_diagonal_interior p r hp hcop hr hrN

/-- A chosen actual normalized coefficient sequence at each charge. The
preterminal coefficients and terminal source are fixed by triangularity. -/
noncomputable def minimalThreeChargeKernel (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (c : ℂ) : wardSequenceSpace c 0 := (exists_minimalThree_charge_kernel p hp hcop c).choose

/-- The chosen family begins with the genuine highest vector. -/
theorem minimalThreeChargeKernel_zero (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) (c : ℂ) :
    (minimalThreeChargeKernel p hp hcop c).val 0=highestVector c 0 :=
  (exists_minimalThree_charge_kernel p hp hcop c).choose_spec.1

/-- The chosen actual source vanishes at every preterminal coefficient. -/
theorem minimalThreeChargeKernel_below (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) (c : ℂ) :
    ∀ r<(p-1)*2,
      (wardSourceAt c 0 (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
        (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3 (minimalThreeChargeKernel p hp hcop c)).val r=0 :=
  (exists_minimalThree_charge_kernel p hp hcop c).choose_spec.2

/-- All even preterminal coefficients have nonzero ACTUAL vacuum tests.
The induction uses the actual zero source and its proved two-step formula. -/
theorem minimalThree_kernel_survival_at_charge (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) (c : ℂ)
    (f : wardSequenceSpace c 0)
    (h0 : f.val 0=highestVector c 0)
    (hf : ∀ r<(p-1)*2,
      (wardSourceAt c 0
        (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
        (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3 f).val r=0)
    (j : ℕ) (hj : j<p-1) :
    vermaVacuumSurvival c (f.val (2*j))≠0 := by
  induction j with
  | zero => simp [h0]
  | succ j ih =>
    have hh := vermaVacuumSurvival_sourceAt_three c
      (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
      (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) f (2*j)
    rw [hf (2*j+2) (by omega),map_zero] at hh
    intro hz
    rw [show 2*j+2=2*(j+1) by omega,hz,mul_zero,zero_add] at hh
    exact mul_ne_zero (minimalThree_survival_factor_ne_zero p (j+1) hp hcop)
      (ih (by omega)) hh.symm

/-- The terminal source of any normalized preterminal solution has a
nonzero vacuum projection. The terminal diagonal is zero, leaving the
proved nonzero even-step term. -/
theorem minimalThree_terminal_survival_at_charge (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) (c : ℂ)
    (f : wardSequenceSpace c 0)
    (h0 : f.val 0=highestVector c 0)
    (hf : ∀ r<(p-1)*2,
      (wardSourceAt c 0
        (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
        (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3 f).val r=0) :
    vacuumProjection c
      ((wardSourceAt c 0
        (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
        (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3 f).val ((p-1)*2))≠0 := by
  apply vacuumProjection_ne_zero_of_survival
  have hh := vermaVacuumSurvival_sourceAt_three c
    (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
    (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) f (2*(p-2))
  have hd := wardBSASourceDiagonal_label_terminal (p-1) 3 ((3:ℂ)/(p:ℂ))
    (by omega) (minimal_three_parameter_ne_zero p (by omega))
  norm_num only [show (3:ℂ)-1=2 by norm_num,show (3:ℕ)-1=2 by omega] at hd
  rw [fusionThree_minimal_weight_zero p hp] at hd
  have he : 2*(p-2)+2=(p-1)*2 := by omega
  rw [he,hd,zero_mul,zero_add] at hh
  rw [hh]
  have hk := minimalThree_survival_factor_ne_zero p (p-1) hp hcop
  rw [show 2*(p-1)=(p-1)*2 by omega] at hk
  exact mul_ne_zero hk (minimalThree_kernel_survival_at_charge p hp hcop c f h0 hf (p-2) (by omega))

/-- The terminal actual Verma source at every charge, with fixed q=3
seed parameters. Its vacuum image is the family of interest. -/
noncomputable def minimalThreeChargeSource (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (c : ℂ) : Verma c 0 :=
  (wardSourceAt c 0 (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
    (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3 (minimalThreeChargeKernel p hp hcop c)).val ((p-1)*2)

/-- The actual vacuum source family obtained by projection, at every charge. -/
noncomputable def minimalThreeChargeVacuum (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3)
    (c : ℂ) : VirUniv c := vacuumProjection c (minimalThreeChargeSource p hp hcop c)

/-- Each family member belongs to the expected conformal level. -/
theorem minimalThreeChargeVacuum_level (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) (c : ℂ) :
    minimalThreeChargeVacuum p hp hcop c∈gradingVir c (((p-1)*2:ℕ):ℤ) :=
  vacuumProjection_level c _ _
    ((wardSourceAt c 0 (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ))
      (vermaBSAWeight 3 ((3:ℂ)/(p:ℂ))) 3 (minimalThreeChargeKernel p hp hcop c)).property _)

/-- The actual vacuum source is nonzero at EVERY charge. This statement
concerns vector survival, not its canonical norm or derivative. -/
theorem minimalThreeChargeVacuum_ne_zero (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) (c : ℂ) :
    minimalThreeChargeVacuum p hp hcop c≠0 :=
  minimalThree_terminal_survival_at_charge p hp hcop c (minimalThreeChargeKernel p hp hcop c)
    (minimalThreeChargeKernel_zero p hp hcop c) (minimalThreeChargeKernel_below p hp hcop c)

/-- The whole actual source family is quasiprimary. Only the second
positive-mode equation is sensitive to the special central charge. -/
theorem minimalThreeChargeVacuum_L1 (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) (c : ℂ) :
    Lop c 1 (minimalThreeChargeVacuum p hp hcop c)=0 := by
  have hh := nonresonant_terminal_L1_at_charge c 0
    (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ)) 3 ((p-1)*2)
    (minimal_three_parameter_ne_zero p (by omega)) (by omega) (by omega)
    (minimalThreeChargeKernel p hp hcop c) (minimalThreeChargeKernel_below p hp hcop c)
    (fun r hr hrN => minimalThree_diagonal_interior p r hp hcop hr hrN)
    (minimalThree_diagonal_terminal p hp)
  rw [minimalThreeChargeVacuum,← vacuumProjection_mode]
  change vacuumProjection c (vermaMode c 0 1 _)=0
  rw [minimalThreeChargeSource,hh,map_zero]

/-- At the minimal-model charge the same chosen family member satisfies
the second Ward equation, so it recovers a genuine singular vacuum state. -/
theorem minimalThreeChargeVacuum_L2_at_root (p : ℕ) (hp : 2≤p) (hcop : Nat.Coprime p 3) :
    Lop (vermaBSACharge ((3:ℂ)/(p:ℂ))) 2
      (minimalThreeChargeVacuum p hp hcop (vermaBSACharge ((3:ℂ)/(p:ℂ))))=0 := by
  have hh := nonresonant_terminal_L2 0
    (fusionKacWeight ((p-1:ℕ):ℂ) 0 ((3:ℂ)/(p:ℂ))) ((3:ℂ)/(p:ℂ)) 3 ((p-1)*2)
    (minimal_three_parameter_ne_zero p (by omega)) (by omega)
    (minimalThreeChargeKernel p hp hcop (vermaBSACharge ((3:ℂ)/(p:ℂ))))
    (minimalThreeChargeKernel_below p hp hcop (vermaBSACharge ((3:ℂ)/(p:ℂ))))
    (fun r hr hrN => minimalThree_diagonal_interior p r hp hcop hr hrN)
    (by omega) (minimalThree_diagonal_terminal p hp)
  rw [minimalThreeChargeVacuum,← vacuumProjection_mode]
  change vacuumProjection _ (vermaMode _ 0 2 _)=0
  rw [minimalThreeChargeSource,hh,map_zero]

end VOA.InverseDS.VirasoroVerma
