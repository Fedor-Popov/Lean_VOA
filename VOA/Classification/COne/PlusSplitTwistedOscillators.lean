import VOA.Classification.COne.PlusSplitUntwistedCharacters
import VOA.Moonshine.HeisenbergTwistedModuleInstance
import VOA.Moonshine.TwistedSectorDim
import VOA.Moonshine.LatticeTwistedLeading

/-! # Rank-one twisted oscillator tops and the charged-field calculation

These are concrete calculations on the existing twisted Fock space. The
Heisenberg twisted module is genuine. The charged zero-mode below is the FLM
dressing candidate; no lattice twisted Jacobi identity or plus Zhu character
is asserted. The current lattice twisted-module constructor requires
unimodularity and cannot be specialized to the rank-one lattice at m >= 1.
-/
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.PlusTwistedOscillators
open VOA.Moonshine VOA.TwistedHeisenberg VOA.TwistedSector
  VOA.Moonshine.LatticeTwisted HeisenbergN MvPolynomial PlusCharacterTable PlusC2

def evenWeight (q : ℚ) : Submodule ℂ (FockT 1) := weightT 1 q ⊓ fockTPlus 1
def oddWeight (q : ℚ) : Submodule ℂ (FockT 1) := weightT 1 q ⊓ fockTMinus 1

theorem even_top : evenWeight (1 / 16) = ℂ ∙ vacT 1 := by
  have he : (1 / 16 : ℚ) = levelT 1 0 := by norm_num [levelT]
  rw [evenWeight, he, weightT_levelT,
    inf_eq_left.mpr (gradingT_le_fockTPlus (by decide : Even 0)), gradingT_zero]

theorem odd_top : oddWeight (9 / 16) = gradingT 1 1 := by
  have he : (9 / 16 : ℚ) = levelT 1 1 := by norm_num [levelT]
  rw [oddWeight, he, weightT_levelT,
    inf_eq_left.mpr (gradingT_le_fockTMinus (by decide : Odd 1))]

theorem even_top_finrank : Module.finrank ℂ (evenWeight (1 / 16)) = 1 := by
  rw [even_top, finrank_span_singleton (by exact one_ne_zero : vacT 1 ≠ 0)]

theorem odd_top_finrank : Module.finrank ℂ (oddWeight (9 / 16)) = 1 := by
  rw [odd_top, finrank_gradingT_one]

theorem evenWeight_eq_bot_of_lt (q : ℚ) (hq : q < 1 / 16) : evenWeight q = ⊥ := by
  rw [evenWeight, weightT_eq_bot_of_lt (by simpa using hq), bot_inf_eq]

theorem oddWeight_eq_bot_of_lt (q : ℚ) (hq : q < 9 / 16) : oddWeight q = ⊥ := by
  by_cases he : ∃ d, levelT 1 d = q
  · obtain ⟨d, rfl⟩ := he
    have hd : d = 0 := by
      dsimp [levelT] at hq
      have : (d : ℚ) < 1 := by linarith
      have hd1 : d < 1 := by exact_mod_cast this
      omega
    subst d
    rw [oddWeight, weightT_levelT, gradingT_inf_fockTMinus (by decide : Even 0)]
  · push Not at he
    rw [oddWeight, weightT_eq_bot he, bot_inf_eq]

theorem first_oscillator_mem : (X (0, (0 : Fin 1)) : FockT 1) ∈ gradingT 1 1 := by
  simpa [gradingT, wT] using isWeightedHomogeneous_X ℂ (wT (r := 1)) (0, (0 : Fin 1))

/-- These are the actual conformal modes of the rank-one twisted Heisenberg module. -/
theorem conformal_top_actions :
    (heisTwistedModule 1).YM (heisVOA1 1).conformalVector 2 (vacT 1) =
      (1 / 16 : ℂ) • vacT 1 ∧
    (heisTwistedModule 1).YM (heisVOA1 1).conformalVector 2 (X (0, (0 : Fin 1))) =
      (9 / 16 : ℂ) • X (0, (0 : Fin 1)) := by
  simp only [heisTwistedModule_YM, YT_omega_two]
  constructor
  · simpa using L0T_vacT 1
  · have h := L0T_of_mem_gradingT first_oscillator_mem
    norm_num [levelT] at h ⊢
    exact h

theorem dressing_zero_one (v : Fin 1 → ℂ) : DD v 0 (1 : FockT 1) = 1 := by
  rw [DD_one]; simp [sMz]

theorem dressing_zero_first (c : ℂ) :
    DD (fun _ : Fin 1 => c) 0 (X (0, (0 : Fin 1))) =
      (1 - 2*c*c) • X (0, (0 : Fin 1)) := by
  have h := DD_X_mul (fun _ : Fin 1 => c) (0, (0 : Fin 1)) 0 (1 : FockT 1)
  rw [mul_one, dressing_zero_one, mul_one, DD_one] at h
  have h1 : sMz (fun _ : Fin 1 => c) 1 = (2*c) • X (0, (0 : Fin 1)) := by
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, sMz_natCast, sM, nexp_succ]
    simp [dM, vVarT, smul_smul]
  norm_num only [Nat.cast_zero, mul_zero, zero_add] at h
  rw [h, h1, smul_smul]
  rw [sub_smul, one_smul]
  congr 2; ring

/-- The FLM candidate for o(e^alpha + e^-alpha) on either scalar central
character. Establishing its extension to a lattice twisted module is open. -/
def chargedZeroMode (m : ℕ) (s : ℂ) : Module.End ℂ (FockT 1) :=
  (s / (2 : ℂ)^(2*m)) •
    (DD (fun _ : Fin 1 => cα m) 0 + DD (fun _ : Fin 1 => -cα m) 0)

theorem chargedZeroMode_vacuum (m : ℕ) (s : ℂ) :
    chargedZeroMode m s (vacT 1) = ((twistedScale m : ℂ)*s) • vacT 1 := by
  simp only [chargedZeroMode, LinearMap.smul_apply, LinearMap.add_apply, vacT,
    dressing_zero_one, ← two_smul ℂ, smul_smul]
  congr 1
  simp only [twistedScale, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_pow]
  ring

theorem chargedZeroMode_first (m : ℕ) (hm : 1 ≤ m) (s : ℂ) :
    chargedZeroMode m s (X (0, (0 : Fin 1))) =
      (-(twistedScale m : ℂ)*s*(4*m-1)) • X (0, (0 : Fin 1)) := by
  simp only [chargedZeroMode, LinearMap.smul_apply, LinearMap.add_apply,
    dressing_zero_first, ← add_smul, smul_smul]
  congr 1
  have hc := cα_sq m hm
  simp only [twistedScale, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_pow]
  calc
    _ = (2/(2 : ℂ)^(2*m))*s*(1-2*(cα m*cα m)) := by ring
    _ = _ := by rw [hc]; ring

end VOA.Classification.COne.PlusTwistedOscillators
