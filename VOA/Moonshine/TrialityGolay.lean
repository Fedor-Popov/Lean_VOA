/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.TrialityRoot
import VOA.Moonshine.FrameSign
import VOA.Moonshine.LeechLatticeVOA

/-!
# FLM/DGM triality on the Niemeier lattice VOA `V_{N(A₁²⁴)}`  (Moonshine step M8g untwisted half)

## The mathematics (Dolan–Goddard–Montague, CMP 179 (1996), §§6.3, 7; hep-th/9410029)

Let `C` be the extended Golay code and `N := N(A₁²⁴) = Γ_Golay = {x/√2 : x ∈ ℤ²⁴, x mod 2 ∈ C}`
(vendored as `Leech.golayLattice`: carrier `ρ⁻¹(C) ⊆ ℤ²⁴`, form `x·y/2`).  Its roots are
`α_j = 2e_j` (`⟨α_j,α_j⟩ = 2`, mutually orthogonal), so `V_N ⊇ ŝl₂^{24}` at level one, with, in
coordinate `j`, the Cartan current `H_j = (α_j(−1)𝟙)₍₀₎` and `E_j = (e^{α_j})₍₀₎`,
`F_j = ε_j (e^{−α_j})₍₀₎` (`ε_j = ε(α_j,−α_j)`, so that `[E_j,F_j] = H_j`).

`Λ₀ := ker (parity) = A`, `parity(x) = (∑ xᵢ)/2 mod 2` (`Leech.parity`, `Leech.range_inclG`), is
FLM's `Λ ∩ N`, isometric to the index-2 sublattice `Λ₀ = ker β` of the Leech lattice
(`Moonshine.lambda0Equiv`).  DGM's two commuting involutions of `V_N` are

* `χ = θ₁ = exp(iπ/√2·1·p) = ∏_j exp(iπ H_j/2)`: on `e^λ` it is `i^{∑ xᵢ} = (−1)^{parity λ}` —
  the momentum sign `chiAut parity` (rotation by `π` about the **Heisenberg** axis in each
  `su(2)_j`);
* `θ`: the lift of `−1` (rotation by `π` about the `e+f` axis in each `su(2)_j`),

and `V₀⁺ = V_{Λ₀}^+ = V_N^{⟨θ, χ⟩}` (DGM (6.66), (7.18)).  DGM's triality on `V_N` (their (7.5),
(7.6), with the modification (7.8) in one coordinate `l`, mandatory for `d = 24` because
`24/8` is odd) is

  `σ = ∏_j exp( iπ/√2 (J₀^{j1} + J₀^{j2}) )`,   `J^{j1} = H_j/2`,  `J^{j2} = (E_j+F_j)/2`

(rotation by `π` about the axis bisecting the Heisenberg axis and the `e+f` axis, DGM (7.7):
`J^{j1} ↔ J^{j2}`, `J^{j3} ↦ −J^{j3}`).  **Remark**: the formula
`J^{j1}+J^{j2}` is right only in DGM's labelling, where `ζ₁ʲ = a^j_{−1}|0⟩/√2` is the
*Heisenberg* current and `ζ₂ʲ ∝ |√2eⱼ⟩ + |−√2eⱼ⟩` the `e+f` current; it is not "two off-diagonal
currents".  `σ` swaps `θ ↔ χ`, fixes `θχ`, preserves `V₀⁺`, and maps `V₀⁻ ↔ V₁⁺` (DGM Prop. 7.2).

### The form used here (conjugation of `χ`, so that `σ² = 1` is free)

In `SL₂`, with `g := exp((1−√2)E)·exp((√2/4)F)` one has `g H g⁻¹ = (H+E+F)/√2`, hence
`g·exp(iπH/2)·g⁻¹ = exp(iπ/√2·(H/2 + (E+F)/2))` **exactly** (as `SL₂` matrices, not only in
`PSL₂`; checked numerically).  Therefore, with `G := ∏_j g_j`,

  `σ_DGM = G χ G⁻¹`   and the (7.8)-modified   `σ := G (χ z_l) G⁻¹`,

where `z_l = (−1)^{x_l}` (`chiAut` of `x ↦ x_l mod 2`) is the central element `exp(2πi n·J^l)`.
Since `(χ z_l)² = 1` (`chiAut_sq`), `σ² = 1` is immediate; and `Θ := σ χ σ` is the inner lift
`∏_j exp(iπ(E_j+F_j)/2)` of `−1` (in `SL₂`: `σ_j (iσ₁) σ_j⁻¹ = iσ₂` exactly).

### The weight-2 trace (numerical certificate for the (7.8) modification)

`V_N` at weight 2 is `24·(3+1) ⊕ C(24,2)·9 ⊕ 759·2⁸ = 196884`.  Projecting with
`¼∑_{k∈⟨χ,Θ⟩}` (legitimate since `σ` normalises `⟨χ,Θ⟩`), using `SU(2)` traces (`σ_j`: 0 on
spin ½, −1 on spin 1; `σ_jχ_j`, `σ_jΘ_j`: −√2 on spin ½, +1 on spin 1; `σ_jχ_jΘ_j`: 0, −1):

  `tr(σ | V₀⁺₂) = 300 + 8·∑_{octads c} (−1)^{c·u}`,

where `u ∈ F₂²⁴/C` is the modification (`u = 0`: DGM (7.5); `u = e_l`: DGM (7.8)).  Golay
octad counts give `∑ = 759` for `u = 0` and `253` for `u = e_l`, so

  `tr(σ_DGM(7.5) | V₀⁺₂) = 6372`,   `tr(σ_DGM(7.8) | V₀⁺₂) = 2324`.

Consistency check (Monster character table, values on `196884 = 1 + 196883`): if `σ` extends to
`σ̃ ∈ Aut V♮ = 𝕄` with `V₀⁺ = V♮^E`, `E ≅ 2²`, then `σ̃` normalises `E` (Galois correspondence),
fixes one `k₀ ∈ E`, swaps the other two, and
`tr(σ|V₀⁺₂) = ¼(tr σ̃ + tr σ̃k₀ + 2 tr σ̃k₁)` with `σ̃, σ̃k₀` involutions and `σ̃k₁` of order 4;
the maximum possible value is `¼(4372 + 4372 + 2·276) = 2324` (2A, 2A, 4A).  So `6372` is
**impossible** for a Monster element — the unmodified (7.5) `σ` is *not* the restriction of
FLM's triality — while the (7.8) value saturates the bound.  The ambiguity `u` is exactly the
"which of `T₊/T₋` is `T₀`" question of M8g (θ = (−1)^{d/8} = −1 on `T`).

## What is formalised here
* `golayN`, `golayVOA : VertexOperatorAlgebra` — `V_{N(A₁²⁴)}` (`c = 24`), roots `golayRoot j`.
* `golayChi` (= `χ`, `chiAut parity`), `golayChiMod` (= `χ z₀`, DGM (7.8) with `l = 0`).
* `golayG` (= `G`), `golaySigma := G (χ z₀) G⁻¹`, `golaySigma_sq : σ² = 1`,
  `golaySigma_ne_one`.
* `golayTheta := σ χ σ`, `golayTheta_sq`, `golaySigma_conj_theta : σ Θ σ = χ`.
* `golayK := ⟨χ, Θ⟩`, `golayV0 := V_N^{⟨χ,Θ⟩}` (orbifold VOA), `golaySigma0 : Aut golayV0`,
  `golaySigma0_sq`, and `mem_golayV0_momentum` (all momenta of `V_N^{⟨χ,Θ⟩}` lie in `Λ₀`).

## Status
`sorry`-free, no new axioms; unconditional.  Proved downstream: `golaySigma0_ne_one` and
`σ (α_j(−1)𝟙) = e^{α_j} + ε_j e^{−α_j}` (`TrialityCurrents.lean`); `Θ` anticommutes with the
Heisenberg modes and maps `F_λ → F_{−λ}` (`TrialityTheta.lean`).  The isomorphism
`golayV0 ≅ V0P` is proved downstream: `golayToV0` with `golayToV0_isVOAHom`
(`FrameBridgeGolay.lean`).
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.Triality

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice VOA.LatGen HeisenbergN

/-! ## §1  The Niemeier lattice `N(A₁²⁴)` and its lattice VOA -/

/-- `N(A₁²⁴) = Γ_Golay` as a `VOA.IntegralLattice`. -/
noncomputable abbrev golayN : VOA.IntegralLattice.{0} := ofEbeling Leech.golayLattice

theorem golayN_even : golayN.Even :=
  ofEbeling_even _ ((latticeOfCode_isEven Code.golay Leech.golay_le_dual).mpr Code.golay_isDoublyEven)

theorem golayN_posDef : golayN.PosDef :=
  ofEbeling_posDef _ (latticeOfCode_isPosDef Code.golay Leech.golay_le_dual)

theorem golayN_rank : rank golayN = 24 := Leech.golayLattice_rank

/-- **The Niemeier lattice VOA** `V_{N(A₁²⁴)}`. -/
noncomputable def golayVOA : VertexOperatorAlgebra (LatModuleGen golayN) :=
  latticeVOAGen golayN golayN_even golayN_posDef

theorem golayVOA_centralCharge : golayVOA.centralCharge = 24 := by
  rw [golayVOA, latticeVOAGen_centralCharge, golayN_rank]; norm_num

/-- The coordinate vector `x ∈ ℤ²⁴` of a lattice point of `N(A₁²⁴)`. -/
def gv (x : golayN.carrier) : Fin 24 → ℤ := (show ↥Leech.preG from x).1

theorem gv_add (x y : golayN.carrier) : gv (x + y) = gv x + gv y := rfl

theorem gv_neg (x : golayN.carrier) : gv (-x) = -gv x := rfl

theorem golayN_form (x y : golayN.carrier) :
    golayN.form x y = (gv x ⬝ᵥ gv y) / 2 := rfl

/-- The root `α_j = 2e_j` of `N(A₁²⁴)`. -/
def golayRoot (j : Fin 24) : golayN.carrier :=
  show ↥Leech.preG from ⟨(2 : ℤ) • Pi.single j 1, two_smul_mem_preimageOfCode Code.golay _⟩

theorem golayRoot_coe (j : Fin 24) : gv (golayRoot j) = (2 : ℤ) • Pi.single j 1 := rfl

theorem golayRoot_form (j k : Fin 24) :
    golayN.form (golayRoot j) (golayRoot k) = if j = k then 2 else 0 := by
  rw [golayN_form, golayRoot_coe, golayRoot_coe]
  by_cases h : j = k
  · subst h; simp [dotProduct, Pi.single_apply]
  · rw [if_neg h]; simp [dotProduct, Pi.single_apply, Ne.symm h]

theorem golayRoot_norm (j : Fin 24) : golayN.form (golayRoot j) (golayRoot j) = 2 := by
  rw [golayRoot_form, if_pos rfl]

theorem golayRoot_neg_norm (j : Fin 24) : golayN.form (-golayRoot j) (-golayRoot j) = 2 := by
  simp only [map_neg, LinearMap.neg_apply, neg_neg, golayRoot_norm]

/-! ## §2  The momentum signs `χ` and `z_l` -/

/-- DGM's `θ₁`-character: `parity(x) = (∑ xᵢ)/2 mod 2`; its kernel is `Λ₀ = A`. -/
noncomputable def golayParity : golayN.carrier →+ ZMod 2 := Leech.parity.toAddMonoidHom

theorem golayParity_apply (x : golayN.carrier) : golayParity x = Leech.parity x := rfl

theorem golayParity_eq_zero_iff (x : golayN.carrier) :
    golayParity x = 0 ↔ (4 : ℤ) ∣ ∑ i, gv x i := Leech.parity_eq_zero_iff x

/-- The coordinate character `z_l(x) = x_l mod 2`. -/
def golayCoord (l : Fin 24) : golayN.carrier →+ ZMod 2 where
  toFun x := ((gv x l : ℤ) : ZMod 2)
  map_zero' := by show (((0 : Fin 24 → ℤ) l : ℤ) : ZMod 2) = 0; simp
  map_add' x y := by
    show ((gv (x + y) l : ℤ) : ZMod 2) = _
    rw [gv_add, Pi.add_apply, Int.cast_add]

theorem golayParity_root (j : Fin 24) : golayParity (golayRoot j) = 1 := by
  rw [golayParity_apply]
  show ((((∑ i, ((2 : ℤ) • (Pi.single j 1 : Fin 24 → ℤ)) i) / 2 : ℤ)) : ZMod 2) = 1
  rw [show (∑ i, ((2 : ℤ) • (Pi.single j 1 : Fin 24 → ℤ)) i) = 2 by
    simp [Pi.single_apply]]
  decide

theorem golayCoord_root (l j : Fin 24) : golayCoord l (golayRoot j) = 0 := by
  change ((((2 : ℤ) • (Pi.single j 1 : Fin 24 → ℤ)) l : ℤ) : ZMod 2) = 0
  rw [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  rw [show ((2 : ℤ) : ZMod 2) = 0 from rfl, zero_mul]

/-- DGM's `χ = θ₁ = ∏_j exp(iπ H_j/2)`: the momentum sign `(−1)^{parity}`. -/
noncomputable def golayChi : Aut golayVOA := chiAut golayN golayParity golayN_even golayN_posDef

/-- The DGM (7.8)-modified rotation centre `χ z₀`. -/
noncomputable def golayChiMod : Aut golayVOA :=
  chiAut golayN (golayParity + golayCoord 0) golayN_even golayN_posDef

theorem golayChi_sq : golayChi * golayChi = 1 := chiAut_sq _ _ _ _

theorem golayChiMod_sq : golayChiMod * golayChiMod = 1 := chiAut_sq _ _ _ _

theorem latChargeGen_ne_zero' (γ : golayN.carrier) : latChargeGen golayN γ ≠ 0 :=
  Screen.latStateGen_ne_zero golayN one_ne_zero γ

theorem golayChiMod_root (j : Fin 24) :
    golayChiMod (latChargeGen golayN (golayRoot j)) = -latChargeGen golayN (golayRoot j) := by
  show chiLat golayN _ (latStateGen golayN _ _) = _
  rw [chiLat_latStateGen, chiSign_of_ne_zero]
  · rw [neg_one_smul]; rfl
  · rw [AddMonoidHom.add_apply, golayParity_root, golayCoord_root, add_zero]; exact one_ne_zero

theorem golayChiMod_ne_one : golayChiMod ≠ 1 := by
  intro h
  have h1 := golayChiMod_root 0
  rw [h] at h1
  have h2 : (2 : ℂ) • latChargeGen golayN (golayRoot 0) = 0 := by
    rw [two_smul]; nth_rewrite 1 [show latChargeGen golayN (golayRoot 0)
      = (1 : Aut golayVOA) (latChargeGen golayN (golayRoot 0)) from rfl]
    rw [h1, neg_add_cancel]
  exact latChargeGen_ne_zero' _ ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

/-! ## §3  The rotation `G = ∏_j exp((1−√2)E_j) exp((√2/4)F_j)` and the triality `σ` -/

/-- The cocycle sign `ε_j = ε(α_j, −α_j)` normalising `F_j = ε_j (e^{−α_j})₍₀₎`. -/
noncomputable def golayEps (j : Fin 24) : ℂ :=
  latticeCocycle golayN (golayRoot j) (-golayRoot j)

/-- `g_j = exp((1−√2)E_j)·exp((√2/4)F_j)`: in `SL₂` it rotates the Heisenberg axis onto the
bisector of the Heisenberg and `e+f` axes (`g H g⁻¹ = (H+E+F)/√2`). -/
noncomputable def golayG1 (j : Fin 24) : Aut golayVOA :=
  rootExp golayN golayN_even golayN_posDef (golayRoot_norm j) ((1 - Real.sqrt 2 : ℝ) : ℂ) *
    rootExp golayN golayN_even golayN_posDef (golayRoot_neg_norm j)
      (((Real.sqrt 2 / 4 : ℝ) : ℂ) * golayEps j)

/-- `G = g₀ g₁ ⋯ g₂₃`. -/
noncomputable def golayG : Aut golayVOA := (List.ofFn golayG1).prod

/-- **FLM/DGM triality on `V_{N(A₁²⁴)}`**, in the (7.8)-modified form `σ = G (χ z₀) G⁻¹`. -/
noncomputable def golaySigma : Aut golayVOA := golayG * golayChiMod * golayG⁻¹

/-- `σ² = 1`. -/
theorem golaySigma_sq : golaySigma * golaySigma = 1 := by
  rw [golaySigma]
  calc golayG * golayChiMod * golayG⁻¹ * (golayG * golayChiMod * golayG⁻¹)
      = golayG * (golayChiMod * golayChiMod) * golayG⁻¹ := by group
    _ = 1 := by rw [golayChiMod_sq]; group

theorem golaySigma_ne_one : golaySigma ≠ 1 := by
  intro h
  apply golayChiMod_ne_one
  have : golayChiMod = golayG⁻¹ * golaySigma * golayG := by rw [golaySigma]; group
  rw [this, h]; group

/-! ## §4  `Θ = σχσ`, the group `⟨χ, Θ⟩`, and the restriction of `σ` to `V_N^{⟨χ,Θ⟩}` -/

/-- `Θ := σ χ σ` — the inner lift `∏ exp(iπ(E_j+F_j)/2)` of `−1` (DGM's `θ`, up to a character). -/
noncomputable def golayTheta : Aut golayVOA := golaySigma * golayChi * golaySigma

theorem golayTheta_sq : golayTheta * golayTheta = 1 := by
  rw [golayTheta]
  calc golaySigma * golayChi * golaySigma * (golaySigma * golayChi * golaySigma)
      = golaySigma * golayChi * (golaySigma * golaySigma) * golayChi * golaySigma := by group
    _ = golaySigma * (golayChi * golayChi) * golaySigma := by rw [golaySigma_sq]; group
    _ = golaySigma * golaySigma := by rw [golayChi_sq]; group
    _ = 1 := golaySigma_sq

theorem golaySigma_conj_chi : golaySigma * golayChi * golaySigma = golayTheta := rfl

theorem golaySigma_conj_theta : golaySigma * golayTheta * golaySigma = golayChi := by
  rw [golayTheta]
  calc golaySigma * (golaySigma * golayChi * golaySigma) * golaySigma
      = (golaySigma * golaySigma) * golayChi * (golaySigma * golaySigma) := by group
    _ = golayChi := by rw [golaySigma_sq]; group

/-- `K = ⟨χ, Θ⟩`. -/
noncomputable def golayK : Subgroup (Aut golayVOA) := Subgroup.closure {golayChi, golayTheta}

theorem golaySigma_inv : golaySigma⁻¹ = golaySigma :=
  inv_eq_of_mul_eq_one_right golaySigma_sq

theorem golaySigma_normalises (g : Aut golayVOA) (hg : g ∈ golayK) :
    golaySigma * g * golaySigma ∈ golayK := by
  have hconj : ∀ x : Aut golayVOA, golaySigma * x * golaySigma = MulAut.conj golaySigma x := by
    intro x; rw [MulAut.conj_apply, golaySigma_inv]
  rw [hconj]
  have hle : golayK.map (MulAut.conj golaySigma).toMonoidHom ≤ golayK := by
    rw [golayK, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl
    · show MulAut.conj golaySigma golayChi ∈ _
      rw [← hconj, golaySigma_conj_chi]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · show MulAut.conj golaySigma golayTheta ∈ _
      rw [← hconj, golaySigma_conj_theta]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
  exact hle ⟨g, hg, rfl⟩

/-- `V_N^{⟨χ,Θ⟩}` — DGM's `V₀⁺` (modulo the open identification of `Θ` with a lift of `−1`). -/
noncomputable def golayV0 : VertexOperatorAlgebra (orbifold golayK).carrier := orbifoldVOA golayK

theorem golayV0_centralCharge : golayV0.centralCharge = 24 := golayVOA_centralCharge

/-- **The triality `σ₀` on `V_N^{⟨χ,Θ⟩}`.** -/
noncomputable def golaySigma0 : Aut golayV0 :=
  orbifoldInvol golayK golaySigma_sq golaySigma_normalises

/-- `σ₀² = 1`. -/
theorem golaySigma0_sq : golaySigma0 * golaySigma0 = 1 := orbifoldInvol_sq _ _ _

theorem golaySigma0_coe (v : (orbifold golayK).carrier) :
    ((golaySigma0 v : (orbifold golayK).carrier) : LatModuleGen golayN) = golaySigma v :=
  orbifoldInvol_coe _ _ _ v

/-- Every state of `V_N^{⟨χ,Θ⟩}` has all its momenta in `Λ₀ = ker parity`. -/
theorem mem_golayV0_momentum {v : LatModuleGen golayN} (hv : v ∈ (orbifold golayK).carrier)
    (μ : golayN.carrier) (hμ : golayParity μ ≠ 0) : coordEα golayN μ v = 0 := by
  have h : golayChi v = v := hv golayChi (Subgroup.subset_closure (Set.mem_insert _ _))
  exact (chiLat_eq_self_iff golayN golayParity v).mp h μ hμ

end VOA.Moonshine.Triality
