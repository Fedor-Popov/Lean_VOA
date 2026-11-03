import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeModeRecurrence

/-! Explicit whole-current preimages in the normalized pure-A mode ring.
Commutation is transported only on that image, never asserted globally. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

def modeCurrent (m : ℕ) (c : Fin 8) : PowerSeries (ModePoly ℂ m) :=
  PowerSeries.mk (fun r => shiftedX ℂ m c r)

def modeCurrentMap (m : ℕ) : P8 ℂ →ₐ[ℂ] PowerSeries (ModePoly ℂ m) :=
  MvPolynomial.aeval (modeCurrent m)

@[simp] theorem modeCurrentMap_X (m : ℕ) (c : Fin 8) :
    modeCurrentMap m (MvPolynomial.X c) = modeCurrent m c :=
  MvPolynomial.aeval_X _ _

theorem modeCurrent_map (m : ℕ) (c : Fin 8) :
    PowerSeries.map (modesMap m).toRingHom (modeCurrent m c) = actualCurrent m c := by
  apply PowerSeries.ext
  intro r
  rw [PowerSeries.coeff_map,modeCurrent,PowerSeries.coeff_mk,actualCurrent_coeff]
  exact modesMap_shiftedX m c r

theorem modesMap_currentMap_coeff (m s : ℕ) (p : P8 ℂ) :
    modesMap m (PowerSeries.coeff s (modeCurrentMap m p)) =
      PowerSeries.coeff s (currentMap m p) := by
  have he : (PowerSeries.mapAlgHom (modesMap m)).comp (modeCurrentMap m) =
      currentMap m := by
    apply MvPolynomial.algHom_ext
    intro c
    simp only [AlgHom.comp_apply,modeCurrentMap_X,currentMap_X,
      PowerSeries.mapAlgHom_apply]
    exact modeCurrent_map m c
  have h := congrArg (PowerSeries.coeff s) (AlgHom.congr_fun he p)
  simpa only [AlgHom.comp_apply,PowerSeries.mapAlgHom_apply,PowerSeries.coeff_map] using h

theorem modesMap_iterate_lower (m : ℕ) (d : Fin 3) (k n : ℕ)
    (p : ModePoly ℂ m) :
    modesMap m (((shiftedLower ℂ m d k : _ → _)^[n]) p) =
      ((g0Deriv m (cubeDirection d) k : _ → _)^[n]) (modesMap m p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply',modesMap_lower,ih,Function.iterate_succ_apply']

def modeHighestCoeff (m r s : ℕ) : ModePoly ℂ m :=
  PowerSeries.coeff s (modeCurrentMap m (MvPolynomial.X 0 ^ r))

theorem modesMap_highestCoeff (m r s : ℕ) :
    modesMap m (modeHighestCoeff m r s) =
      PowerSeries.coeff s (AllM.current m 0 ^ r) := by
  rw [modeHighestCoeff,modesMap_currentMap_coeff,map_pow,currentMap_X,
    modeRecurrence_highest_current]

/-- All three zero-mode strings can be commuted past an arbitrary mode
on the entire coefficient preimage, before ideal reduction. -/
theorem actual_lower_orbit_coeff_eq (m r a b c s ell : ℕ) (d : Fin 3) :
    g0Deriv m (cubeDirection d) ell
      (PowerSeries.coeff s (currentMap m (orbit ℂ r a b c))) =
    ((g0Deriv m 9 0 : _ → _)^[c])
      (((g0Deriv m 8 0 : _ → _)^[b])
        (((g0Deriv m 7 0 : _ → _)^[a])
          (g0Deriv m (cubeDirection d) ell
            (PowerSeries.coeff s (AllM.current m 0 ^ r))))) := by
  let q := modeHighestCoeff m r s
  have he : shiftedLower ℂ m d ell
      (((shiftedLower ℂ m 2 0 : _ → _)^[c])
        (((shiftedLower ℂ m 1 0 : _ → _)^[b])
          (((shiftedLower ℂ m 0 0 : _ → _)^[a]) q))) =
      ((shiftedLower ℂ m 2 0 : _ → _)^[c])
        (((shiftedLower ℂ m 1 0 : _ → _)^[b])
          (((shiftedLower ℂ m 0 0 : _ → _)^[a]) (shiftedLower ℂ m d ell q))) := by
    rw [(shiftedLower_commute ℂ m d 2 ell 0).iterate_right c,
      (shiftedLower_commute ℂ m d 1 ell 0).iterate_right b,
      (shiftedLower_commute ℂ m d 0 ell 0).iterate_right a]
  have h := congrArg (modesMap m) he
  simp only [modesMap_lower,modesMap_iterate_lower] at h
  change _ = _ at h
  have hq : modesMap m q = PowerSeries.coeff s (AllM.current m 0 ^ r) :=
    modesMap_highestCoeff m r s
  rw [hq] at h
  rw [currentMap_orbit,coeff_current_iterate,coeff_current_iterate,coeff_current_iterate]
  exact h

end
#print axioms modesMap_currentMap_coeff
#print axioms actual_lower_orbit_coeff_eq
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
