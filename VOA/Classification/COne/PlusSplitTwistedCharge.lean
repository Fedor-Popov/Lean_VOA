import VOA.Classification.COne.PlusSplitTwistedOscillators
import VOA.Moonshine.LatticeTwistedVertex

/-! The two one-dimensional rank-one twisted charge representations.
For the library's canonical rank-one cocycle the extension of L/2L is split.
These are finite charge representations, not yet lattice twisted modules. -/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusTwistedCharge
open VOA.Moonshine.Extraspecial VOA.LatGen.Triplet

/-- Central sign and lattice parity. The first generator is the central involution. -/
abbrev ChargeGroup := Multiplicative (ZMod 2 × ZMod 2)

/-- The two characters of the finite extension with central involution -1. -/
def chargeRep (t : ZMod 2) : Representation ℂ ChargeGroup ℂ where
  toFun g := VOA.Moonshine.Extraspecial.sgn (g.toAdd.1 + t * g.toAdd.2) • (1 : Module.End ℂ ℂ)
  map_one' := by simp [VOA.Moonshine.Extraspecial.sgn_zero]
  map_mul' g h := by
    change VOA.Moonshine.Extraspecial.sgn
      ((g.toAdd.1 + h.toAdd.1) + t * (g.toAdd.2 + h.toAdd.2)) • _ = _
    rw [show (g.toAdd.1 + h.toAdd.1) + t * (g.toAdd.2 + h.toAdd.2) =
      (g.toAdd.1 + t * g.toAdd.2) + (h.toAdd.1 + t * h.toAdd.2) by ring,
      VOA.Moonshine.Extraspecial.sgn_add]
    simp [smul_smul, mul_comm]

theorem chargeRep_central (t : ZMod 2) :
    chargeRep t (Multiplicative.ofAdd (1, 0)) = -(1 : Module.End ℂ ℂ) := by
  simp [chargeRep, VOA.Moonshine.Extraspecial.sgn_one]

theorem chargeRep_generator (t : ZMod 2) :
    chargeRep t (Multiplicative.ofAdd (0, 1)) =
      VOA.Moonshine.Extraspecial.sgn t • (1 : Module.End ℂ ℂ) := by
  simp [chargeRep]

/-- The charge space is a complex line, so every invariant complex subspace
is zero or the whole space. This proves irreducibility of each representation. -/
theorem chargeRep_irreducible (t : ZMod 2) (P : Submodule ℂ ℂ)
    (_hP : ∀ g x, x ∈ P → chargeRep t g x ∈ P) : P = ⊥ ∨ P = ⊤ :=
  eq_bot_or_eq_top P

theorem chargeRep_distinct : chargeRep 0 ≠ chargeRep 1 := by
  intro he
  have h := congrArg (fun ρ : Representation ℂ ChargeGroup ℂ =>
    ρ (Multiplicative.ofAdd (0, 1)) 1) he
  norm_num [chargeRep, VOA.Moonshine.Extraspecial.sgn_zero, VOA.Moonshine.Extraspecial.sgn_one] at h

/-- Action of the lift of a lattice element on the charge line. -/
def eT (m : ℕ) (t : ZMod 2) (a : (latP m).carrier) : Module.End ℂ ℂ :=
  chargeRep t (Multiplicative.ofAdd (0, (Int.cast (a : ℤ) : ZMod 2)))

theorem eT_mul (m : ℕ) (t : ZMod 2) (a b : (latP m).carrier) :
    eT m t a * eT m t b = VOA.IntegralLattice.latticeCocycle (latP m) a b • eT m t (a + b) := by
  rw [PlusCharacterTable.rankOne_cocycle, one_smul]
  unfold eT
  rw [← map_mul]
  congr 1
  change Multiplicative.ofAdd
    ((0, (Int.cast (a : ℤ) : ZMod 2)) + (0, (Int.cast (b : ℤ) : ZMod 2))) = _
  exact congrArg Multiplicative.ofAdd (Prod.ext (zero_add _)
    (Int.cast_add (R := ZMod 2) (a : ℤ) (b : ℤ)).symm)

theorem eT_zero (m : ℕ) (t : ZMod 2) : eT m t 0 = 1 := by
  change chargeRep t (Multiplicative.ofAdd (0, (Int.cast (0 : ℤ) : ZMod 2))) = 1
  exact (chargeRep t).map_one

theorem eT_neg (m : ℕ) (t : ZMod 2) (a : (latP m).carrier) :
    eT m t (-a) = eT m t a := by
  have hn : -(Int.cast (a : ℤ) : ZMod 2) = (Int.cast (a : ℤ) : ZMod 2) :=
    (by decide : ∀ x : ZMod 2, -x = x) _
  change chargeRep t (Multiplicative.ofAdd (0, (Int.cast (-(a : ℤ)) : ZMod 2))) = _
  congr 2
  exact Prod.ext rfl ((Int.cast_neg (a : ℤ)).trans hn)

theorem eT_add_two (m : ℕ) (t : ZMod 2) (a b : (latP m).carrier) :
    eT m t (a + 2 • b) = eT m t a := by
  change chargeRep t (Multiplicative.ofAdd (0, (Int.cast ((a : ℤ) + 2 • (b : ℤ)) : ZMod 2))) = _
  congr 2
  congr 1
  change (Int.cast ((a : ℤ) + 2 • (b : ℤ)) : ZMod 2) = Int.cast (a : ℤ)
  calc
    _ = (Int.cast (a : ℤ) : ZMod 2) + Int.cast (2 • (b : ℤ)) :=
      Int.cast_add (a : ℤ) (2 • (b : ℤ))
    _ = (Int.cast (a : ℤ) : ZMod 2) + 0 := by
      apply congrArg (fun z : ZMod 2 => (Int.cast (a : ℤ) : ZMod 2) + z)
      calc
        _ = (Int.cast ((b : ℤ) + (b : ℤ)) : ZMod 2) :=
          congrArg (fun z : ℤ => (Int.cast z : ZMod 2)) (two_smul ℕ (b : ℤ))
        _ = (Int.cast (b : ℤ) : ZMod 2) + Int.cast (b : ℤ) := Int.cast_add _ _
        _ = 0 := (by decide : ∀ z : ZMod 2, z + z = 0) _
    _ = _ := add_zero _

theorem eT_generator (m : ℕ) (t : ZMod 2) :
    eT m t (1 : ℤ) = VOA.Moonshine.Extraspecial.sgn t • (1 : Module.End ℂ ℂ) := by
  simpa [eT] using chargeRep_generator t

open VOA.Moonshine.LatticeTwisted VOA.TwistedHeisenberg
open scoped TensorProduct

/-- FLM exponential modes on the rank-one oscillator space tensored with the
constructed charge line. No unimodularity assumption occurs. -/
def chargedModes (m : ℕ) (t : ZMod 2) (a : ℤ) (k : ℤ) :
    Module.End ℂ (FockT 1 ⊗[ℂ] ℂ) :=
  YTg (fun _ : Fin 1 => PlusC2.cα m * (a : ℂ)) (2 * (m : ℤ) * a ^ 2)
    ((2 : ℂ) ^ (-(2 * (m : ℤ) * a ^ 2))) (eT m t a) k

theorem chargedModes_truncation (m : ℕ) (t : ZMod 2) (a : ℤ)
    (x : FockT 1 ⊗[ℂ] ℂ) :
    ∃ K : ℤ, ∀ k : ℤ, K ≤ k → chargedModes m t a k x = 0 :=
  YTg_truncation _ _ _ _ x

theorem chargedModes_zero (m : ℕ) (t : ZMod 2) (k : ℤ) :
    chargedModes m t 0 k = if k = -2 then 1 else 0 := by
  simp only [chargedModes, Int.cast_zero, mul_zero, zero_pow (by decide : 2 ≠ 0),
    neg_zero, zpow_zero]
  rw [show eT m t (0 : ℤ) = 1 from eT_zero m t]
  exact YTg_zero_charge (r := 1) (Tm := ℂ) k

/-- The constructed exponential modes have the required theta parity. -/
theorem chargedModes_neg (m : ℕ) (t : ZMod 2) (a k : ℤ) :
    chargedModes m t (-a) k = (-1 : ℂ) ^ k • chargedModes m t a k := by
  have hc : (fun _ : Fin 1 => PlusC2.cα m * ((-a : ℤ) : ℂ)) =
      -(fun _ : Fin 1 => PlusC2.cα m * (a : ℂ)) := by ext i; simp
  have he : eT m t (-a) = eT m t a := eT_neg m t a
  unfold chargedModes
  rw [hc, neg_sq, he, YTg_neg]
  congr 1
  apply neg_one_zpow_congr
  rw [show -k - 2 + 2 * (m : ℤ) * a ^ 2 - k =
    2 * ((m : ℤ) * a ^ 2 - k - 1) by ring, Int.mul_emod]
  norm_num

open VOA.TwistedReduction

/-- The charged fields built from either line representation are mutually
local on every residue class. Extension to composite states and the full
product formula/Jacobi theorem are separate, still open steps. -/
theorem chargedModes_local (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) (a b e e' : ℤ) :
    Local (resc (chargedModes m t a) 2 e) (resc (chargedModes m t b) 2 e') := by
  have hn : pair (fun _ : Fin 1 => PlusC2.cα m * (a : ℂ))
      (fun _ : Fin 1 => PlusC2.cα m * (b : ℂ)) = ((2 * (m : ℤ) * a * b : ℤ) : ℂ) := by
    simp only [pair, Fin.sum_univ_one]
    calc
      _ = (PlusC2.cα m * PlusC2.cα m) * ((a : ℂ) * (b : ℂ)) := by ring
      _ = _ := by rw [PlusC2.cα_sq m hm]; push_cast; ring
  have heven : Even (2 * (m : ℤ) * a * b) := ⟨(m : ℤ) * a * b, by ring⟩
  have hg : eT m t b * eT m t a =
      (-1 : ℂ) ^ (2 * (m : ℤ) * a * b).natAbs • (eT m t a * eT m t b) := by
    rw [heven.natAbs.neg_one_pow, one_smul, eT_mul, eT_mul,
      PlusCharacterTable.rankOne_cocycle, PlusCharacterTable.rankOne_cocycle, one_smul, one_smul]
    congr 1
    exact add_comm _ _
  exact YTg_local _ _ _ hn _ _ _ _ _ _ hg e e'

/-- The sum of the two generator-charge fields at the expected E zero mode.
This remains a field-level construction until full twisted Jacobi is proved. -/
def EZero (m : ℕ) (t : ZMod 2) : Module.End ℂ (FockT 1 ⊗[ℂ] ℂ) :=
  chargedModes m t 1 (2 * m - 2) + chargedModes m t (-1) (2 * m - 2)

theorem EZero_tmul (m : ℕ) (t : ZMod 2) (x : FockT 1) (z : ℂ) :
    EZero m t (x ⊗ₜ[ℂ] z) =
      PlusTwistedOscillators.chargedZeroMode m (VOA.Moonshine.Extraspecial.sgn t) x ⊗ₜ[ℂ] z := by
  have hn : -(2 * (m : ℤ) - 2) - 2 + 2 * (m : ℤ) = 0 := by ring
  have he : eT m t (-1 : ℤ) = eT m t (1 : ℤ) := eT_neg m t (1 : ℤ)
  have hc : (2 : ℂ) ^ (-(2 * (m : ℤ))) = ((2 : ℂ) ^ (2 * m))⁻¹ := by
    rw [zpow_neg]
    congr 1
  simp only [EZero, chargedModes, LinearMap.add_apply, Int.cast_one, Int.cast_neg,
    one_pow, neg_one_sq, mul_one, mul_neg, hn, he, eT_generator, YTg_tmul, hc,
    LinearMap.smul_apply, Module.End.one_apply, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul', PlusTwistedOscillators.chargedZeroMode,
    LinearMap.add_apply, TensorProduct.add_tmul, smul_add, smul_smul]
  simp only [div_eq_mul_inv, mul_comm (VOA.Moonshine.Extraspecial.sgn t)]

/-- Both finite charge characters give the expected even oscillator E value. -/
theorem EZero_vacuum (m : ℕ) (t : ZMod 2) :
    EZero m t (vacT 1 ⊗ₜ[ℂ] (1 : ℂ)) =
      ((PlusCharacterTable.twistedScale m : ℂ) * VOA.Moonshine.Extraspecial.sgn t) •
        (vacT 1 ⊗ₜ[ℂ] (1 : ℂ)) := by
  rw [EZero_tmul, PlusTwistedOscillators.chargedZeroMode_vacuum, TensorProduct.smul_tmul']

/-- Both finite charge characters give the expected odd oscillator E value. -/
theorem EZero_first (m : ℕ) (hm : 1 ≤ m) (t : ZMod 2) :
    EZero m t (MvPolynomial.X (0, (0 : Fin 1)) ⊗ₜ[ℂ] (1 : ℂ)) =
      (-(PlusCharacterTable.twistedScale m : ℂ) * VOA.Moonshine.Extraspecial.sgn t * (4*m-1)) •
        (MvPolynomial.X (0, (0 : Fin 1)) ⊗ₜ[ℂ] (1 : ℂ)) := by
  rw [EZero_tmul, PlusTwistedOscillators.chargedZeroMode_first m hm, TensorProduct.smul_tmul']

end VOA.Classification.COne.PlusTwistedCharge
