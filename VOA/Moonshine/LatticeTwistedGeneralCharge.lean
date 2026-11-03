import VOA.Moonshine.LatticeTwistedVertex

/-! # Charge data for the twisted construction
Only the cocycle multiplication, unit, and trivial action of twice the lattice
are required. No nondegeneracy or irreducibility is assumed. -/
namespace VOA.Moonshine.LatticeTwistedGeneral
open IntegralLattice

structure TwistedCharge (L : IntegralLattice) where
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  op : L.carrier → Module.End ℂ carrier
  op_zero : op 0 = 1
  op_mul : ∀ α β, op α * op β = latticeCocycle L α β • op (α + β)
  op_add_two : ∀ α β, op (α + 2 • β) = op α

attribute [instance] TwistedCharge.addCommGroup TwistedCharge.module

abbrev Space (L : IntegralLattice) (_hEven : L.Even) (C : TwistedCharge L) := C.carrier

noncomputable def eT (L : IntegralLattice) (hEven : L.Even) (C : TwistedCharge L)
    (α : L.carrier) : Module.End ℂ (Space L hEven C) := C.op α

variable (L : IntegralLattice) (hEven : L.Even) (C : TwistedCharge L)

theorem eT_zero : eT L hEven C 0 = 1 := C.op_zero

theorem eT_mul (α β : L.carrier) :
    eT L hEven C α * eT L hEven C β = latticeCocycle L α β • eT L hEven C (α + β) :=
  C.op_mul α β

theorem eT_add_two_nsmul (α β : L.carrier) :
    eT L hEven C (α + 2 • β) = eT L hEven C α := C.op_add_two α β

theorem eT_neg (α : L.carrier) : eT L hEven C (-α) = eT L hEven C α := by
  have h := eT_add_two_nsmul L hEven C (-α) α
  rw [two_smul, neg_add_cancel_left] at h
  exact h.symm

/-- The original unimodular charge space supplies this interface. -/
noncomputable def unimodularCharge (hU : IsUnit (gramMat L).det) : TwistedCharge L where
  carrier := VOA.Moonshine.Extraspecial.Rep (cocMat L) (isUnit_det_cocMat L hEven hU)
  op := IntegralLattice.eT L hEven hU
  op_zero := IntegralLattice.eT_zero L hEven hU
  op_mul := IntegralLattice.eT_mul L hEven hU
  op_add_two := IntegralLattice.eT_add_two_nsmul L hEven hU

end VOA.Moonshine.LatticeTwistedGeneral
