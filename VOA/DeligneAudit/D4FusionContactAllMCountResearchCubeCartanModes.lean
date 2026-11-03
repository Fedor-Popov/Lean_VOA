import VOA.DeligneAudit.D4FusionContactAllMCountResearchCubeHighest

/-! The actual highest Cartan current is not a uniform shift on all colors.
Its commutator with each negative cube current is the summed-mode current. -/
namespace VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
open VOA.DeligneAudit.D4FusionContact.Polynomial
noncomputable section

theorem cartanWeight_next : ∀ (d : Fin 3) (i j : Fin 8), cubeNext d i = some j →
    AllMNormal.cartanCoeff (cubeColor j) - AllMNormal.cartanCoeff (cubeColor i) = 1 := by
  decide +kernel

theorem actualMode_cartan (m r k : ℕ) (i : Fin 8) :
    g0Deriv m 1 k (actualMode m r i) =
      (AllMNormal.cartanCoeff (cubeColor i):ℂ) • actualMode m (k+r) i := by
  simp only [actualMode,Derivation.map_smul,AllMNormal.cartan_modeX,smul_smul]
  rw [mul_comm]

/-- The nonzero bracket term must be retained when sorting whole currents. -/
theorem cartan_lower_mode (m r k l : ℕ) (d : Fin 3) (i : Fin 8) :
    ⁅g0Deriv m 1 k,g0Deriv m (cubeDirection d) l⁆ (actualMode m r i) =
      g0Deriv m (cubeDirection d) (k+l) (actualMode m r i) := by
  rw [Derivation.commutator_apply,actualMode_lower_mode,actualMode_cartan,
    Derivation.map_smul,actualMode_lower_mode,actualMode_lower_mode]
  cases ht : cubeNext d i with
  | none => simp only [map_zero,smul_zero,sub_self]
  | some j =>
      rw [actualMode_cartan,show k+(l+r) = k+l+r by omega,
        show l+(k+r) = k+l+r by omega,← sub_smul]
      have hn : (AllMNormal.cartanCoeff (cubeColor j):ℂ) -
          (AllMNormal.cartanCoeff (cubeColor i):ℂ) = 1 := by
        exact_mod_cast cartanWeight_next d i j ht
      rw [hn,one_smul]

/-- The genuine current Lie relation on the whole pure-A polynomial image. -/
theorem actual_cartan_lower_bracket (m k l : ℕ) (d : Fin 3) (p : ModePoly ℂ m) :
    ⁅g0Deriv m 1 k,g0Deriv m (cubeDirection d) l⁆ (modesMap m p) =
      g0Deriv m (cubeDirection d) (k+l) (modesMap m p) := by
  have h := map_derivation_to (modesMap m) (shiftedLower ℂ m d (k+l))
    ⁅g0Deriv m 1 k,g0Deriv m (cubeDirection d) l⁆ (fun x => ?_) p
  · rw [modesMap_lower] at h
    exact h.symm
  · rw [shiftedLower_X,modesMap_step,modesMap_X,cartan_lower_mode,actualMode_lower_mode]
    rfl

/-- Already at one site, a zero-weight color disproves a uniform Cartan shift. -/
theorem cartan_uniform_shift_obstruction :
    g0Deriv 1 1 0 (modeX 1 4 0) = 0 ∧ modeX 1 4 0 ≠ 0 := by
  constructor
  · rw [AllMNormal.cartan_modeX]
    rw [show AllMNormal.cartanCoeff 4 = 0 from rfl]
    simp only [Int.cast_zero,zero_smul]
  · simp [modeX]

end
#print axioms cartan_lower_mode
#print axioms actual_cartan_lower_bracket
#print axioms cartan_uniform_shift_obstruction
end VOA.DeligneAudit.D4FusionContact.AllMCountResearch.Cube
