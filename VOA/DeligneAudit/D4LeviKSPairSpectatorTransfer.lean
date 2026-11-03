import VOA.DeligneAudit.D4LeviKSPairXZPrefix

/-! The operator transfer with a zero-mode U spectator. -/

namespace VOA.DeligneAudit.D4Levi

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- On a vector killed by every current mode, a mode word acting on an
    operator word is the reverse-ordered iterated adjoint. -/
theorem pairModeWord_spectator_adjoint
    (F : ℕ → Module.End ℂ V) (w : V)
    (hzero : ∀ r, F r w = 0) (rs : List ℕ)
    (B : Module.End ℂ V) :
    pairModeWord F rs (B w) = pairAdjoint F rs.reverse B w := by
  induction rs with
  | nil => simp [pairModeWord, pairAdjoint]
  | cons r rs ih =>
      rw [List.reverse_cons, pairAdjoint_append]
      simp only [pairModeWord, List.map_cons, List.prod_cons,
        Module.End.mul_apply, pairAdjoint]
      simp only [LinearMap.sub_apply, Module.End.mul_apply,
        hzero, map_zero, sub_zero]
      exact congrArg (F r) ih

/-- The f₃ mode word converts the U spectator into the Y word. -/
theorem fThree_modeWord_uZero_factorial
    (ρ : CurrentModule D4sector.f V) (w : V)
    (hzero : ∀ r, ρ.op (17 : Fin 28) r w = 0)
    (rs : List ℕ) :
    pairModeWord (ρ.op (17 : Fin 28)) rs
        (pairRadicalOp ρ (uZeroWord rs.length) w) =
      (-1 : ℂ) ^ rs.length •
        ((Nat.factorial rs.length : ℂ) •
          pairRadicalOp ρ (yModeWord rs) w) := by
  rw [pairModeWord_spectator_adjoint _ w hzero]
  have h := fThree_adjoint_uZero_factorial_ordered ρ rs.reverse
  simp only [List.length_reverse] at h
  rw [h]
  simp only [LinearMap.smul_apply]
  have hp : (yModeWord rs.reverse).Perm (yModeWord rs) :=
    (List.reverse_perm rs).map (fun r => ((4 : Fin 6), r))
  rw [pairRadicalOp_perm ρ hp]

/-- A PAIR transfer after adjoining the U spectator. The source condition
    isolates precisely the intermediate words that must be higher keys. -/
theorem pairSpectator_transfer_of_sources
    (ρ : CurrentModule D4sector.f V) (w : V) (m i : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (hi : i < (globalKeyBox m).card)
    (rs : List ℕ) (A : Module.End ℂ V)
    (hSources : pairTransferSources (keyPrefix ρ w m i)
      (ρ.op (17 : Fin 28))
      (pairRadicalOp ρ (uZeroWord rs.length) w) rs A) :
    (Nat.factorial rs.length : ℂ) •
        A (pairRadicalOp ρ (yModeWord rs) w) -
      pairAdjoint (ρ.op (17 : Fin 28)) rs A
        (pairRadicalOp ρ (uZeroWord rs.length) w) ∈
          keyPrefix ρ w m i := by
  have hInv : ∀ r x, x ∈ keyPrefix ρ w m i →
      ρ.op (17 : Fin 28) r x ∈ keyPrefix ρ w m i := by
    intro r x hx
    rw [keyPrefix_eq_higher ρ w m h i hi] at hx ⊢
    exact higherOrbit_full_levi_inv ρ w m _ (17 : Fin 28)
      ⟨7, rfl⟩ r hx
  have hmod := pairAntipode_mod (keyPrefix ρ w m i)
    (ρ.op (17 : Fin 28))
    (pairRadicalOp ρ (uZeroWord rs.length) w) hInv rs A hSources
  rw [pairAntipode_eq_sign,
    fThree_modeWord_uZero_factorial ρ w
      (fThree_source_mode_zero ρ w m h) rs] at hmod
  have hsquare : (-1 : ℂ) ^ rs.length * (-1 : ℂ) ^ rs.length = 1 := by
    rw [← pow_add, ← two_mul]
    simp [pow_mul]
  have hscaled := (keyPrefix ρ w m i).smul_mem
    ((-1 : ℂ) ^ rs.length) hmod
  simpa only [smul_sub, map_smul, LinearMap.smul_apply,
    smul_smul, ← mul_assoc, hsquare, one_mul, one_smul]
    using hscaled

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.pairModeWord_spectator_adjoint
#print axioms VOA.DeligneAudit.D4Levi.fThree_modeWord_uZero_factorial
#print axioms VOA.DeligneAudit.D4Levi.pairSpectator_transfer_of_sources
