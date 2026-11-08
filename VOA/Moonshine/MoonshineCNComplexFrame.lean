import VOA.Moonshine.MoonshineCNVertexTarget

/-!
# Complex bilinear frames for indefinite lattice fields

The rank-two frame is explicit and uses no positive-definiteness assumption.
The repository already has `NearVOA`; the target from the preceding construction
converts to that structure without weakening any field requirement.
-/

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators
open IntegralLattice HeisenbergN

/-- Complex bilinear coordinates for the integral lattice pairing. -/
structure ComplexLatticeFrame (L : IntegralLattice) where
  coordinate : L.carrier →+ (Fin (rank L) → ℂ)
  pairing : ∀ x y, ∑ a, coordinate x a * coordinate y a = (L.form x y : ℂ)

/-- The explicit hyperbolic frame, reindexed to the existing Fock carrier. -/
noncomputable def lorentzianComplexFrame : ComplexLatticeFrame lorentzianLattice where
  coordinate :=
    { toFun := fun x a => complexHyperbolicCoordinate x (finCongr lorentzian_rank a)
      map_zero' := by
        ext a
        change complexHyperbolicCoordinate (fun _ => 0) (finCongr lorentzian_rank a) = 0
        generalize finCongr lorentzian_rank a = b
        fin_cases b <;> norm_num [complexHyperbolicCoordinate, lorentzianLattice]
      map_add' := by
        intro x y
        ext a
        change complexHyperbolicCoordinate (fun i => x i + y i) (finCongr lorentzian_rank a) =
          complexHyperbolicCoordinate x (finCongr lorentzian_rank a) +
            complexHyperbolicCoordinate y (finCongr lorentzian_rank a)
        generalize finCongr lorentzian_rank a = b
        fin_cases b <;>
          simp [complexHyperbolicCoordinate, lorentzianLattice] <;> ring }
  pairing := by
    intro x y
    change (∑ a, complexHyperbolicCoordinate x (finCongr lorentzian_rank a) *
      complexHyperbolicCoordinate y (finCongr lorentzian_rank a)) = _
    rw [Equiv.sum_comp (finCongr lorentzian_rank)
      (fun a => complexHyperbolicCoordinate x a * complexHyperbolicCoordinate y a)]
    exact complexHyperbolicCoordinate_pairing x y

/-- The oscillator defined by an arbitrary complex lattice frame. -/
noncomputable def frameOscillator {L : IntegralLattice} (F : ComplexLatticeFrame L)
    (α : L.carrier) (m : ℤ) : Module.End ℂ (FockN (rank L)) :=
  ∑ a, F.coordinate α a • oscN (rank L) 1 a m

theorem frameOscillator_vacuum {L : IntegralLattice} (F : ComplexLatticeFrame L)
    (α : L.carrier) (m : ℤ) (hm : 0 ≤ m) :
    frameOscillator F α m (vacuumN (rank L)) = 0 :=
  complexChargeOscillator_vacuum (F.coordinate α) m hm

theorem frameOscillator_commutator {L : IntegralLattice} (F : ComplexLatticeFrame L)
    (α β : L.carrier) (m n : ℤ) :
    frameOscillator F α m * frameOscillator F β n -
      frameOscillator F β n * frameOscillator F α m =
      (if m + n = 0 then (L.form α β : ℂ) * (m : ℂ) else 0) • LinearMap.id := by
  change ⁅complexChargeOscillator (F.coordinate α) m,
    complexChargeOscillator (F.coordinate β) n⁆ = _
  rw [complexChargeOscillator_commutator, F.pairing]

/-- Fixed-coordinate sign cocycle: the ordered isotropic basis gives `(-1)^(x₁y₀)`. -/
noncomputable def standardLorentzianCocycle (x y : lorentzianLattice.carrier) : ℂ :=
  (-1 : ℂ) ^ (x 1 * y 0)

theorem standardLorentzianCocycle_law (x y z : lorentzianLattice.carrier) :
    standardLorentzianCocycle x y * standardLorentzianCocycle (x + y) z =
      standardLorentzianCocycle y z * standardLorentzianCocycle x (y + z) := by
  simp only [standardLorentzianCocycle, Pi.add_apply, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  congr 1
  change x 1 * y 0 + (x 1 + y 1) * z 0 = y 1 * z 0 + x 1 * (y 0 + z 0)
  ring

theorem standardLorentzianCocycle_commutator (x y : lorentzianLattice.carrier) :
    standardLorentzianCocycle x y * standardLorentzianCocycle y x =
      (-1 : ℂ) ^ lorentzianLattice.form x y := by
  simp only [standardLorentzianCocycle, lorentzian_form_apply,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  congr 1
  ring

theorem standardLorentzianCocycle_normalized (x : lorentzianLattice.carrier) :
    standardLorentzianCocycle 0 x = 1 ∧ standardLorentzianCocycle x 0 = 1 := by
  change (-1 : ℂ) ^ (0 * x 0) = 1 ∧ (-1 : ℂ) ^ (x 1 * 0) = 1
  norm_num

theorem standardLorentzianCocycle_ne_zero (x y : lorentzianLattice.carrier) :
    standardLorentzianCocycle x y ≠ 0 :=
  zpow_ne_zero _ (by norm_num)

/-- Exact conversion to the repository's conformal vertex-algebra structure. -/
def UnboundedConformalVertexAlgebra.toNearVOA {M : Type*} [AddCommGroup M] [Module ℂ M]
    (V : UnboundedConformalVertexAlgebra M) : NearVOA M where
  grading := V.grading
  isInternal := V.isInternal
  Y := V.Y
  vacuum := V.vacuum
  vacuum_mem := V.vacuum_mem
  grading_mode := fun u hu v hv n => V.grading_mode _ _ u v hu hv n
  vacuum_Y := V.vacuum_Y
  creation := V.creation
  locality := V.locality
  regularity := V.regularity
  conformalVector := V.conformalVector
  conformal_mem := V.conformal_mem
  centralCharge := V.centralCharge
  virasoro := V.virasoro
  L0_grading := fun v hv => V.L0_grading _ v hv
  translation := V.translation

end VOA.Moonshine.ConwayNorton
