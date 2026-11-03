/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TrialityRoot
import VOA.Moonshine.FrameSign
import VOA.Examples.TripletWpTwoMixed

/-!
# The root `sl₂` triple on `V_L`, and its exponentials on the current space  (M8g ingredient)

For a root `α` (`⟨α,α⟩ = 2`) of an even positive-definite lattice `L`, the weight-one states

  `e := e^α`,   `h := α(−1)𝟙 = vSchur α 1 ⊗ e⁰` (`hSt α`),   `f := e^{−α}`

span a copy of `sl₂` under the zero modes `Q_{±α} = (e^{±α})₍₀₎`.  With `ε := ε(α,−α)`
(`= ε(−α,α)`, a sign):

  `Q_α : e ↦ 0, h ↦ −2e, f ↦ εh`;     `Q_{−α} : e ↦ −εh, h ↦ 2f, f ↦ 0`

(`Qscr_vec3_pos`, `Qscr_vec3_neg`).  Both are nilpotent of order 3 on `span{e,h,f}`, so the root
exponentials `exp(c·Q_{±α})` (`rootExp`) act there by explicit quadratic formulas
(`rootExp_vec3_pos`, `rootExp_vec3_neg`).  A root `β ⟂ α` acts trivially (`rootExp_vec3_orth`),
and a momentum-sign automorphism acts by `(−1)^{χ(α)}` on `e, f` and trivially on `h`
(`chiLat_vec3`).  These are the only inputs needed to evaluate DGM's triality on the currents
of `V_{N(A₁²⁴)}` (`TrialityCurrents.lean`).

The key Fock computation is `EE(β)_{−1} S₁(α) = −⟨α,β⟩` (`EEVec_neg_one_vSchur_one`), i.e.
`Q_β (α(−1)𝟙) = −⟨α,β⟩ e^β` (`Qscr_hSt`).

## Status
`sorry`-free, no new axioms.  Unconditional (given `L` even, positive definite).
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN VOA.LatGen.Screen

variable (L : IntegralLattice)

/-! ## §1  The Heisenberg state and the zero-mode table -/

/-- The Heisenberg current state `α(−1)𝟙 = S₁(α) ⊗ e⁰`. -/
noncomputable def hSt (α : L.carrier) : LatModuleGen L := latStateGen L (vSchur L α 1) 0

theorem hSt_neg (α : L.carrier) : hSt L (-α) = -hSt L α := by
  rw [hSt, hSt, WpC2.vSchur_one', WpC2.vSchur_one', WpC2.vVar_neg', latStateGen, latStateGen,
    TensorProduct.neg_tmul]

theorem latStateGen_smul_one (c : ℂ) (γ : L.carrier) :
    latStateGen L (c • (1 : FockN (rank L))) γ = c • latChargeGen L γ := by
  rw [latChargeGen, latStateGen, latStateGen, TensorProduct.smul_tmul', vacuumN]

/-- `EE(β)_{−1} S₁(α) = −⟨α,β⟩`. -/
theorem EEVec_neg_one_vSchur_one (hPos : L.PosDef) (α β : L.carrier) :
    EEVec L β (-1) (vSchur L α 1) = -((L.form α β : ℤ) : ℂ) • (1 : FockN (rank L)) := by
  rw [WpC2.EEVec_eq_weight_bounded_sum' L β (-1) (Screen.vSchur_mem_gradingWN L α 1)]
  rw [show max (0 : ℤ) (-1) = 0 by norm_num, show ((1 : ℕ) : ℤ) + (-1) = 0 by norm_num,
    Finset.Icc_self, Finset.sum_singleton]
  rw [show (0 : ℤ).toNat = 0 from rfl, show ((0 : ℤ) - (-1)).toNat = 1 from rfl, vSchur_zero,
    one_mul, show (1 : ℕ) = 0 + 1 from rfl, aExpVec_succ, Finset.sum_range_one, aExpVec_zero]
  norm_num only [Nat.cast_zero, zero_add, inv_one, one_smul, LinearMap.comp_id,
    LinearMap.neg_apply]
  have h := WpC2.chargeOsc_vSchur L hPos α β 1 1 (by omega)
  norm_num at h
  rw [h, vSchur_zero, neg_smul]

/-- `Q_β e^γ = 0` whenever `⟨β,γ⟩ ≥ 0`. -/
theorem Qscr_latChargeGen_of_nonneg {β γ : L.carrier} (h : 0 ≤ L.form β γ) :
    Qscr L β (latChargeGen L γ) = 0 := by
  rw [Qscr_latChargeGen, EEVec_vacuum, if_neg (by omega), latStateGen, TensorProduct.zero_tmul,
    smul_zero]

/-- `Q_α e^{−α} = ε(α,−α)·α(−1)𝟙` for a root `α`. -/
theorem Qscr_latChargeGen_neg {α : L.carrier} (hα : L.form α α = 2) :
    Qscr L α (latChargeGen L (-α)) = latticeCocycle L α (-α) • hSt L α := by
  rw [Qscr_latChargeGen, EEVec_vacuum, map_neg, hα,
    if_pos (by norm_num), add_neg_cancel, hSt]
  norm_num

/-- `Q_β (α(−1)𝟙) = −⟨α,β⟩ e^β`. -/
theorem Qscr_hSt (hPos : L.PosDef) (α β : L.carrier) :
    Qscr L β (hSt L α) = -((L.form α β : ℤ) : ℂ) • latChargeGen L β := by
  rw [hSt, Qscr_latStateGen, latticeCocycle_zero_right, one_smul, map_zero, sub_zero,
    EEVec_neg_one_vSchur_one L hPos, add_zero, latStateGen_smul_one]

theorem latticeCocycle_neg_self_comm (α : L.carrier) :
    latticeCocycle L (-α) α = latticeCocycle L α (-α) := by
  rw [latticeCocycle_neg_left, latticeCocycle_neg_right]

/-! ## §2  The triple `x₁ e + x₂ h + x₃ f` -/

/-- `x₁ e^α + x₂ α(−1)𝟙 + x₃ e^{−α}`. -/
noncomputable def vec3 (α : L.carrier) (x₁ x₂ x₃ : ℂ) : LatModuleGen L :=
  x₁ • latChargeGen L α + x₂ • hSt L α + x₃ • latChargeGen L (-α)

theorem vec3_zero (α : L.carrier) : vec3 L α 0 0 0 = 0 := by simp [vec3]

theorem vec3_add (α : L.carrier) (x₁ x₂ x₃ y₁ y₂ y₃ : ℂ) :
    vec3 L α x₁ x₂ x₃ + vec3 L α y₁ y₂ y₃ = vec3 L α (x₁ + y₁) (x₂ + y₂) (x₃ + y₃) := by
  simp only [vec3, add_smul]; abel

theorem vec3_smul (α : L.carrier) (c x₁ x₂ x₃ : ℂ) :
    c • vec3 L α x₁ x₂ x₃ = vec3 L α (c * x₁) (c * x₂) (c * x₃) := by
  simp only [vec3, smul_add, smul_smul]

theorem vec3_neg (α : L.carrier) (x₁ x₂ x₃ : ℂ) :
    -vec3 L α x₁ x₂ x₃ = vec3 L α (-x₁) (-x₂) (-x₃) := by
  rw [← neg_one_smul ℂ, vec3_smul]; simp

theorem vec3_congr (α : L.carrier) {x₁ x₂ x₃ y₁ y₂ y₃ : ℂ} (h₁ : x₁ = y₁) (h₂ : x₂ = y₂)
    (h₃ : x₃ = y₃) : vec3 L α x₁ x₂ x₃ = vec3 L α y₁ y₂ y₃ := by rw [h₁, h₂, h₃]

theorem Qscr_vec3_pos (hPos : L.PosDef) {α : L.carrier} (hα : L.form α α = 2) (x₁ x₂ x₃ : ℂ) :
    Qscr L α (vec3 L α x₁ x₂ x₃)
      = vec3 L α (-2 * x₂) (latticeCocycle L α (-α) * x₃) 0 := by
  have h1 := Qscr_latChargeGen_of_nonneg L (β := α) (γ := α) (by rw [hα]; norm_num)
  have h2 := Qscr_hSt L hPos α α
  rw [hα] at h2
  have h3 := Qscr_latChargeGen_neg L hα
  simp only [vec3, map_add, map_smul, h1, h2, h3]
  rw [smul_smul, smul_smul, zero_smul]
  push_cast
  module

theorem Qscr_vec3_neg (hPos : L.PosDef) {α : L.carrier} (hα : L.form α α = 2) (x₁ x₂ x₃ : ℂ) :
    Qscr L (-α) (vec3 L α x₁ x₂ x₃)
      = vec3 L α 0 (-(latticeCocycle L α (-α)) * x₁) (2 * x₂) := by
  have hα' : L.form (-α) (-α) = 2 := by simp [hα]
  have h1 : Qscr L (-α) (latChargeGen L α) = -(latticeCocycle L α (-α)) • hSt L α := by
    have := Qscr_latChargeGen_neg L hα'
    rw [neg_neg, latticeCocycle_neg_self_comm, hSt_neg, smul_neg] at this
    rw [this, neg_smul]
  have h2 := Qscr_hSt L hPos α (-α)
  rw [map_neg, hα] at h2
  have h3 := Qscr_latChargeGen_of_nonneg L (β := -α) (γ := -α) (by rw [hα']; norm_num)
  simp only [vec3, map_add, map_smul, h1, h2, h3]
  rw [smul_smul, smul_smul, smul_zero]
  push_cast
  module

/-! ## §3  The exponentials on the triple -/

variable (hPos : L.PosDef) (hEven : L.Even)

/-- On a vector killed by `Q_α³`, `exp(c·Q_α) v = v + c Q_α v + (c²/2) Q_α² v`. -/
theorem rootExp_apply_of_cube {α : L.carrier} (hα : L.form α α = 2) (c : ℂ) {v : LatModuleGen L}
    (h3 : Qscr L α (Qscr L α (Qscr L α v)) = 0) :
    rootExp L hEven hPos hα c v = v + c • Qscr L α v + (c ^ 2 / 2) • Qscr L α (Qscr L α v) := by
  have hpow : ∀ k : ℕ, ((latticeVOAGen L hEven hPos).zeroMode (c • latChargeGen L α) 1 ^ k) v
      = c ^ k • (Qscr L α ^ k) v := by
    intro k
    rw [zeroMode_smul_latChargeGen, smul_pow, LinearMap.smul_apply]
  rw [rootExp_apply, VOA.expFun_eq_expSum _ (N := 3) (by
    rw [hpow, show (Qscr L α ^ 3) v = Qscr L α (Qscr L α (Qscr L α v)) by
      simp [pow_succ, Module.End.mul_apply], h3, smul_zero])]
  simp only [VOA.expSum, Finset.sum_range_succ, Finset.sum_range_zero, hpow, pow_zero, pow_one,
    pow_two, Module.End.mul_apply, Module.End.one_apply, zero_add, Nat.factorial, Nat.cast_one,
    Nat.succ_eq_add_one, inv_one, smul_smul]
  rw [show ((((1 + 1) * (1 * 1) : ℕ) : ℂ))⁻¹ * (c * c) = c ^ 2 / 2 by push_cast; ring]
  simp [pow_two]

theorem rootExp_vec3_pos {α : L.carrier} (hα : L.form α α = 2) (c x₁ x₂ x₃ : ℂ) :
    rootExp L hEven hPos hα c (vec3 L α x₁ x₂ x₃)
      = vec3 L α (x₁ - 2 * c * x₂ - c ^ 2 * latticeCocycle L α (-α) * x₃)
          (x₂ + c * latticeCocycle L α (-α) * x₃) x₃ := by
  rw [rootExp_apply_of_cube L hPos hEven hα c (by
    rw [Qscr_vec3_pos L hPos hα, Qscr_vec3_pos L hPos hα, Qscr_vec3_pos L hPos hα]
    simp only [mul_zero, vec3_zero])]
  rw [Qscr_vec3_pos L hPos hα, Qscr_vec3_pos L hPos hα, vec3_smul, vec3_smul, vec3_add, vec3_add]
  apply vec3_congr <;> ring

theorem rootExp_vec3_neg {α : L.carrier} (hα : L.form α α = 2) (hα' : L.form (-α) (-α) = 2)
    (c x₁ x₂ x₃ : ℂ) :
    rootExp L hEven hPos hα' c (vec3 L α x₁ x₂ x₃)
      = vec3 L α x₁ (x₂ - c * latticeCocycle L α (-α) * x₁)
          (x₃ + 2 * c * x₂ - c ^ 2 * latticeCocycle L α (-α) * x₁) := by
  rw [rootExp_apply_of_cube L hPos hEven hα' c (by
    rw [Qscr_vec3_neg L hPos hα, Qscr_vec3_neg L hPos hα, Qscr_vec3_neg L hPos hα]
    simp only [mul_zero, vec3_zero])]
  rw [Qscr_vec3_neg L hPos hα, Qscr_vec3_neg L hPos hα, vec3_smul, vec3_smul, vec3_add, vec3_add]
  apply vec3_congr <;> ring

/-- A root orthogonal to `α` acts trivially on the `α`-triple. -/
theorem Qscr_vec3_orth (hPos : L.PosDef) {α β : L.carrier} (hαβ : L.form α β = 0) (x₁ x₂ x₃ : ℂ) :
    Qscr L β (vec3 L α x₁ x₂ x₃) = 0 := by
  have h1 := Qscr_latChargeGen_of_nonneg L (β := β) (γ := α) (by rw [form_symm, hαβ])
  have h2 := Qscr_hSt L hPos α β
  have h3 := Qscr_latChargeGen_of_nonneg L (β := β) (γ := -α)
    (by rw [map_neg, form_symm, hαβ, neg_zero])
  simp only [vec3, map_add, map_smul, h1, h2, h3, hαβ]
  simp

theorem rootExp_vec3_orth {α β : L.carrier} (hβ : L.form β β = 2) (hαβ : L.form α β = 0)
    (c x₁ x₂ x₃ : ℂ) : rootExp L hEven hPos hβ c (vec3 L α x₁ x₂ x₃) = vec3 L α x₁ x₂ x₃ :=
  rootExp_apply_of_Qscr_eq_zero L hEven hPos hβ c (Qscr_vec3_orth L hPos hαβ x₁ x₂ x₃)

/-! ## §4  Momentum signs on the triple -/

theorem chiLat_vec3 (χ : L.carrier →+ ZMod 2) (α : L.carrier) (x₁ x₂ x₃ : ℂ) :
    chiLat L χ (vec3 L α x₁ x₂ x₃)
      = vec3 L α (chiSign L χ α * x₁) x₂ (chiSign L χ α * x₃) := by
  simp only [vec3, map_add, map_smul, latChargeGen, hSt, chiLat_latStateGen, chiSign_zero,
    chiSign_neg, one_smul, smul_smul]
  ring_nf

end VOA.LatGen
