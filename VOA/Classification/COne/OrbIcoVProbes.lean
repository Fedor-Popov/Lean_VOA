import VOA.Classification.COne.OrbIcoVCasimir

/-! Two actual scalar probes separating the vacuum and spin-six Virasoro channels.
They annihilate every discarded descendant at all output levels. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbIcoV
open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbRat6 OrbIco
  VOA.LatGen VOA.LatGen.Triplet OrbIcoS OrbC2c

/-- The spin-six part of the neutral oscillator probe. -/
def sixthProbe : (orbifold ico).carrier →ₗ[ℂ] ℂ :=
  ((1 / 168 : ℂ) • OrbOctaR.neutralProbe.comp spinCasimir).comp
    (orbifold ico).carrier.subtype

/-- The vacuum part of the neutral oscillator probe. -/
def vacuumProbe : (orbifold ico).carrier →ₗ[ℂ] ℂ :=
  OrbIcoS.neutralProbe - sixthProbe

theorem sixthProbe_apply (x : (orbifold ico).carrier) :
    sixthProbe x = (1 / 168 : ℂ) * OrbOctaR.neutralProbe (spinCasimir (x : Sp)) := rfl

theorem vacuumProbe_apply (x : (orbifold ico).carrier) :
    vacuumProbe x = OrbIcoS.neutralProbe x - sixthProbe x := rfl

theorem sixthProbe_L (k : ℕ) (x : (orbifold ico).carrier) :
    sixthProbe (Wi.L (-(k : ℤ) - 1) x) =
      (if k = 1 then (1 / 2 : ℂ) else 0) * sixthProbe x := by
  rw [sixthProbe_apply, sixthProbe_apply]
  change (1 / 168 : ℂ) * OrbOctaR.neutralProbe
    (spinCasimir (V2v.L (-(k : ℤ) - 1) (x : Sp))) = _
  rw [spinCasimir_L, OrbOctaR.neutralProbe_L]
  ring

theorem vacuumProbe_L (k : ℕ) (x : (orbifold ico).carrier) :
    vacuumProbe (Wi.L (-(k : ℤ) - 1) x) =
      (if k = 1 then (1 / 2 : ℂ) else 0) * vacuumProbe x := by
  rw [vacuumProbe_apply, vacuumProbe_apply, OrbIcoS.neutralProbe_L, sixthProbe_L]
  ring

theorem sixthProbe_vacuum : sixthProbe Wi.vacuum = 0 := by
  rw [sixthProbe_apply]
  change (1 / 168 : ℂ) * OrbOctaR.neutralProbe (spinCasimir V2v.vacuum) = 0
  rw [spinCasimir_vacuum, map_zero, mul_zero]

theorem vacuumProbe_vacuum : vacuumProbe Wi.vacuum = 1 := by
  rw [vacuumProbe_apply, OrbIcoS.neutralProbe_vacuum, sixthProbe_vacuum, sub_zero]

theorem sixthProbe_Xico : sixthProbe Xico = OrbIcoS.neutralProbe Xico := by
  rw [sixthProbe_apply, spinCasimir_Xico, map_smul]
  change (1 / 168 : ℂ) * (168 * OrbIcoS.neutralProbe Xico) = _
  ring

theorem vacuumProbe_Xico : vacuumProbe Xico = 0 := by
  rw [vacuumProbe_apply, sixthProbe_Xico, sub_self]

theorem sixthProbe_L_pow (r : ℕ) (x : (orbifold ico).carrier) :
    sixthProbe ((Wi.L (-2) ^ r) x) = (1 / 2 : ℂ) ^ r * sixthProbe x := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply,
      show (-2 : ℤ) = -(1 : ℕ) - 1 by norm_num, sixthProbe_L, if_pos rfl]
    rw [show (-(1 : ℕ) - 1 : ℤ) = -2 by norm_num, ih, pow_succ']
    ring

theorem vacuumProbe_L_pow (r : ℕ) (x : (orbifold ico).carrier) :
    vacuumProbe ((Wi.L (-2) ^ r) x) = (1 / 2 : ℂ) ^ r * vacuumProbe x := by
  rw [vacuumProbe_apply, OrbIcoS.neutralProbe_L_pow, sixthProbe_L_pow,
    vacuumProbe_apply]
  ring

theorem sixthProbe_errors :
    virError Wi Wi.vacuum ⊔ virError Wi Xico ≤ sixthProbe.ker := by
  have kill1 (v : (orbifold ico).carrier) : sixthProbe (Wi.L (-1) v) = 0 := by
    simpa using sixthProbe_L 0 v
  have kill3 (v : (orbifold ico).carrier) : sixthProbe (Wi.L (-3) v) = 0 := by
    simpa using sixthProbe_L 2 v
  exact sup_le (OrbOctaR.virError_le_ker_of_two_modes Wi _ kill1 kill3 _)
    (OrbOctaR.virError_le_ker_of_two_modes Wi _ kill1 kill3 _)

theorem vacuumProbe_errors :
    virError Wi Wi.vacuum ⊔ virError Wi Xico ≤ vacuumProbe.ker := by
  have kill1 (v : (orbifold ico).carrier) : vacuumProbe (Wi.L (-1) v) = 0 := by
    simpa using vacuumProbe_L 0 v
  have kill3 (v : (orbifold ico).carrier) : vacuumProbe (Wi.L (-3) v) = 0 := by
    simpa using vacuumProbe_L 2 v
  exact sup_le (OrbOctaR.virError_le_ker_of_two_modes Wi _ kill1 kill3 _)
    (OrbOctaR.virError_le_ker_of_two_modes Wi _ kill1 kill3 _)

/-- Actual diagonal measurement matrix, independently of any product coefficients. -/
theorem measurement_determinant (r q : ℕ) :
    vacuumProbe ((Wi.L (-2) ^ r) Wi.vacuum) *
      sixthProbe ((Wi.L (-2) ^ q) Xico) -
    sixthProbe ((Wi.L (-2) ^ r) Wi.vacuum) *
      vacuumProbe ((Wi.L (-2) ^ q) Xico) =
        (1 / 2 : ℂ) ^ (r + q) * OrbIcoS.neutralProbe Xico := by
  rw [vacuumProbe_L_pow, sixthProbe_L_pow, vacuumProbe_L_pow, sixthProbe_L_pow,
    vacuumProbe_vacuum, sixthProbe_vacuum, vacuumProbe_Xico, sixthProbe_Xico]
  ring

end VOA.Classification.COne.OrbIcoV
