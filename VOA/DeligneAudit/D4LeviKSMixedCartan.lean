import VOA.DeligneAudit.D4LeviKSMixedYLower
import VOA.DeligneAudit.D4LeviExtraCartanPositive

/-! Cartan currents separating the X, Y, and Z radical colours. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V) (w : V) (m : ℕ)

noncomputable def cartanBlend (a b c : ℂ) (r : ℕ) :
    Module.End ℂ V :=
  a • ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 0)) r +
  b • ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1)) r +
  c • ρ.op (0 : Fin 28) r

private def blendWeight (a b c : ℂ) (j : Fin 6) : ℂ :=
  a * (letterWeight 0 j : ℂ) + b * (letterWeight 1 j : ℂ) +
    c * (extraWeight j : ℂ)

private theorem cartanBlend_comm (a b c : ℂ) (j : Fin 6)
    (r s : ℕ) (v : V) :
    cartanBlend ρ a b c r (ρ.op (radicalColour j) s v) -
      ρ.op (radicalColour j) s (cartanBlend ρ a b c r v) =
      blendWeight a b c j • ρ.op (radicalColour j) (r + s) v := by
  have h0 := cartan_radical_comm ρ 0 j r s v
  have h1 := cartan_radical_comm ρ 1 j r s v
  have he := extra_comm ρ j r s v
  let R := ρ.op (radicalColour j) s
  let H0 := ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 0)) r
  let H1 := ρ.op (leviColour (VOA.DeligneAudit.A3Sector.simpleH 1)) r
  let E := ρ.op (0 : Fin 28) r
  have hc :
      cartanBlend ρ a b c r (R v) - R (cartanBlend ρ a b c r v) =
        a • (H0 (R v) - R (H0 v)) +
          b • (H1 (R v) - R (H1 v)) +
            c • (E (R v) - R (E v)) := by
    simp only [cartanBlend, LinearMap.add_apply, LinearMap.smul_apply,
      map_add, map_smul, smul_sub]
    abel
  rw [hc, h0, h1, he]
  simp only [blendWeight, add_smul, mul_smul]

private theorem cartanBlend_source_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (a b c : ℂ) (r : ℕ) (hr : 0 < r) :
    cartanBlend ρ a b c r w = 0 := by
  simp [cartanBlend, source_cartan_pos ρ w m h 0 r hr,
    source_cartan_pos ρ w m h 1 r hr,
    source_extra_pos ρ w m h r hr]

private theorem x_select_weight :
    blendWeight (1 : ℂ) 0 (-1) (1 : Fin 6) = 2 ∧
    blendWeight (1 : ℂ) 0 (-1) (4 : Fin 6) = 0 ∧
    blendWeight (1 : ℂ) 0 (-1) (5 : Fin 6) = 0 := by
  norm_num [blendWeight, letterWeight, keyLabel, wordKey, extraWeight]

private theorem y_select_weight :
    blendWeight (-1 : ℂ) 0 (-1) (1 : Fin 6) = 0 ∧
    blendWeight (-1 : ℂ) 0 (-1) (4 : Fin 6) = 2 ∧
    blendWeight (-1 : ℂ) 0 (-1) (5 : Fin 6) = 0 := by
  norm_num [blendWeight, letterWeight, keyLabel, wordKey, extraWeight]

private theorem z_select_weight :
    blendWeight (-1 : ℂ) (-1) 0 (1 : Fin 6) = 0 ∧
    blendWeight (-1 : ℂ) (-1) 0 (4 : Fin 6) = 0 ∧
    blendWeight (-1 : ℂ) (-1) 0 (5 : Fin 6) = 1 := by
  norm_num [blendWeight, letterWeight, keyLabel, wordKey, extraWeight]

noncomputable def xShiftCartan (r : ℕ) : Module.End ℂ V :=
  cartanBlend ρ 1 0 (-1) r

noncomputable def yShiftCartan (r : ℕ) : Module.End ℂ V :=
  cartanBlend ρ (-1) 0 (-1) r

noncomputable def zShiftCartan (r : ℕ) : Module.End ℂ V :=
  cartanBlend ρ (-1) (-1) 0 r

/-- The three Cartan directions have pairings (2,0,0), (0,2,0),
    and (0,0,1) with (X,Y,Z). -/
theorem selective_cartan_pairings (r s : ℕ) (v : V) :
    xShiftCartan ρ r (xOp ρ s v) - xOp ρ s (xShiftCartan ρ r v) =
        (2 : ℂ) • xOp ρ (r + s) v ∧
    xShiftCartan ρ r (yOp ρ s v) - yOp ρ s (xShiftCartan ρ r v) = 0 ∧
    xShiftCartan ρ r (zOp ρ s v) - zOp ρ s (xShiftCartan ρ r v) = 0 ∧
    yShiftCartan ρ r (xOp ρ s v) - xOp ρ s (yShiftCartan ρ r v) = 0 ∧
    yShiftCartan ρ r (yOp ρ s v) - yOp ρ s (yShiftCartan ρ r v) =
        (2 : ℂ) • yOp ρ (r + s) v ∧
    yShiftCartan ρ r (zOp ρ s v) - zOp ρ s (yShiftCartan ρ r v) = 0 ∧
    zShiftCartan ρ r (xOp ρ s v) - xOp ρ s (zShiftCartan ρ r v) = 0 ∧
    zShiftCartan ρ r (yOp ρ s v) - yOp ρ s (zShiftCartan ρ r v) = 0 ∧
    zShiftCartan ρ r (zOp ρ s v) - zOp ρ s (zShiftCartan ρ r v) =
        zOp ρ (r + s) v := by
  have hx := x_select_weight
  have hy := y_select_weight
  have hz := z_select_weight
  simp only [xShiftCartan, yShiftCartan, zShiftCartan, xOp, yOp, zOp]
  constructor
  · simpa [hx.1] using cartanBlend_comm ρ 1 0 (-1) 1 r s v
  constructor
  · simpa [hx.2.1] using cartanBlend_comm ρ 1 0 (-1) 4 r s v
  constructor
  · simpa [hx.2.2] using cartanBlend_comm ρ 1 0 (-1) 5 r s v
  constructor
  · simpa [hy.1] using cartanBlend_comm ρ (-1) 0 (-1) 1 r s v
  constructor
  · simpa [hy.2.1] using cartanBlend_comm ρ (-1) 0 (-1) 4 r s v
  constructor
  · simpa [hy.2.2] using cartanBlend_comm ρ (-1) 0 (-1) 5 r s v
  constructor
  · simpa [hz.1] using cartanBlend_comm ρ (-1) (-1) 0 1 r s v
  constructor
  · simpa [hz.2.1] using cartanBlend_comm ρ (-1) (-1) 0 4 r s v
  · simpa [hz.2.2] using cartanBlend_comm ρ (-1) (-1) 0 5 r s v

/-- A positive selective Cartan mode kills the D4 cyclic source. -/
theorem selective_cartan_source_zero
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (hr : 0 < r) :
    xShiftCartan ρ r w = 0 ∧
    yShiftCartan ρ r w = 0 ∧
    zShiftCartan ρ r w = 0 := by
  exact ⟨cartanBlend_source_zero ρ w m h 1 0 (-1) r hr,
    cartanBlend_source_zero ρ w m h (-1) 0 (-1) r hr,
    cartanBlend_source_zero ρ w m h (-1) (-1) 0 r hr⟩

/-- The mode-shift derivation on an ordered radical word. -/
noncomputable def cartanModeDeriv (a b c : ℂ) (r : ℕ) :
    List (Fin 6 × ℕ) → V
  | [] => 0
  | (j, s) :: ls =>
      blendWeight a b c j • radicalWord ρ w ((j, r + s) :: ls) +
        ρ.op (radicalColour j) s (cartanModeDeriv a b c r ls)

/-- Positive Cartan modes shift one letter at a time, weighted by its root. -/
theorem cartanBlend_word_deriv
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (a b c : ℂ) (r : ℕ) (hr : 0 < r)
    (ls : List (Fin 6 × ℕ)) :
    cartanBlend ρ a b c r (radicalWord ρ w ls) =
      cartanModeDeriv ρ w a b c r ls := by
  induction ls with
  | nil =>
      simpa [radicalWord, cartanModeDeriv] using
        cartanBlend_source_zero ρ w m h a b c r hr
  | cons p ls ih =>
      rcases p with ⟨j, s⟩
      have hc := cartanBlend_comm ρ a b c j r s (radicalWord ρ w ls)
      change cartanBlend ρ a b c r
          (ρ.op (radicalColour j) s (radicalWord ρ w ls)) -
        ρ.op (radicalColour j) s
          (cartanBlend ρ a b c r (radicalWord ρ w ls)) = _ at hc
      change cartanBlend ρ a b c r
          (ρ.op (radicalColour j) s (radicalWord ρ w ls)) = _
      rw [sub_eq_iff_eq_add.mp hc, ih]
      rfl

/-- The three selective currents act as explicit mode-shift derivations on
    every radical word. On XYZ words, their coefficients are the pairings above. -/
theorem selective_cartan_word_deriv
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (r : ℕ) (hr : 0 < r) (ls : List (Fin 6 × ℕ)) :
    xShiftCartan ρ r (radicalWord ρ w ls) =
        cartanModeDeriv ρ w 1 0 (-1) r ls ∧
    yShiftCartan ρ r (radicalWord ρ w ls) =
        cartanModeDeriv ρ w (-1) 0 (-1) r ls ∧
    zShiftCartan ρ r (radicalWord ρ w ls) =
        cartanModeDeriv ρ w (-1) (-1) 0 r ls := by
  exact ⟨cartanBlend_word_deriv ρ w m h 1 0 (-1) r hr ls,
    cartanBlend_word_deriv ρ w m h (-1) 0 (-1) r hr ls,
    cartanBlend_word_deriv ρ w m h (-1) (-1) 0 r hr ls⟩

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.selective_cartan_pairings
#print axioms VOA.DeligneAudit.D4Levi.selective_cartan_source_zero
#print axioms VOA.DeligneAudit.D4Levi.cartanBlend_word_deriv
#print axioms VOA.DeligneAudit.D4Levi.selective_cartan_word_deriv
