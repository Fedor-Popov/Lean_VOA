import VOA.Classification.COne.PlusSplitTwistedCharge
import VOA.Moonshine.LatticeTwistedGeneralParity
import VOA.Moonshine.LatticeTwistedGeneralRestriction

/-! # The two rank-one twisted lattice modules and their four parity pieces -/
noncomputable section
namespace VOA.Classification.COne.PlusTwistLattice
open VOA.IntegralLattice VOA.LatGen.Triplet VOA.Moonshine.LatticeTwistedGeneral
open VOA.TwistedHeisenberg VOA.TwistedPlus
open scoped TensorProduct

/-- Either of the two charge lines satisfies the complete general charge interface. -/
def charge (m : ℕ) (t : ZMod 2) : TwistedCharge (latP m) where
  carrier := ℂ
  op := PlusTwistedCharge.eT m t
  op_zero := PlusTwistedCharge.eT_zero m t
  op_mul := PlusTwistedCharge.eT_mul m t
  op_add_two := PlusTwistedCharge.eT_add_two m t

instance (m : ℕ) (t : ZMod 2) : FiniteDimensional ℂ (charge m t).carrier :=
  inferInstanceAs (FiniteDimensional ℂ ℂ)

/-- The honest theta-twisted lattice module, for either charge sign. -/
def twistedModule (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) :
    TwistedModule (thetaV2m m hm) 2 (FockT (rank (latP m)) ⊗[ℂ] ℂ) :=
  latticeTwistedModule (latP m) (latP_even m) (charge m t) (latP_posDef m hm)

/-- Restriction to the plus VOA on the entire twisted carrier. -/
def restrictedModule (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) :
    OrdVModule (V2mPlus m hm) (FockT (rank (latP m)) ⊗[ℂ] ℂ) :=
  fixedOrdModule (twistedModule m hm t)

/-- Two charge signs times two oscillator parities give four ordinary plus modules. -/
def fourModules (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) (odd : Bool) :
    OrdVModule (V2mPlus m hm)
      (plusSub (parityLift (latP m) (latP_even m) (charge m t) (latP_posDef m hm) odd)) :=
  parityModule (latP m) (latP_even m) (charge m t) (latP_posDef m hm) odd

end VOA.Classification.COne.PlusTwistLattice
