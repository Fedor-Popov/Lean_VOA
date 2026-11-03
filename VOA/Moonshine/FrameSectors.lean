/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.FrameSign
import VOA.Moonshine.PlusWeightTwo

/-!
# The Golay frame of the untwisted sector: `V_Λ⁺ = V₀⁺ ⊕ V₃⁺`  (Moonshine step M8e)

## The sublattice `Λ₀`

In the vendored model (`VOA/LatticesAndCodes/Leech/Defs.lean`, Ebeling §2.8) the Leech lattice is
`Λ = 2A ∪ (u + 2A) ⊆ ℤ²⁴` with form `x·y/8`, where `A = {a ∈ ρ⁻¹(Golay) | 4 ∣ ∑ aᵢ}` and
`u = (5,1,…,1)`.  The homomorphism `Leech.beta : Λ → ℤ/2`, `x ↦ x₀ mod 2`, has kernel

  `Λ₀ := ker β = 2A`   (`Leech.range_inclL`),

of index `2` (`Leech.card_quotient_inclL`).  The doubling map `a ↦ 2a` is an *isometry*
`A ≅ Λ₀` (`Leech.inclL_bilin`: `(2a)·(2b)/8 = a·b/2`), and `A ⊆ Γ_Golay = N(A₁²⁴)` (the Golay
lattice with the halved form `x·y/2`, `Leech.golayLattice`; roots `±2eᵢ`) is again of index `2`
(`Leech.card_quotient_inclG`).  So `Λ₀ ≅ A` is the common index-`2` sublattice of `Λ` and of the
Niemeier lattice `N(A₁²⁴)` — this is FLM's `Λ₀ = Λ ∩ N(A₁²⁴)`.  It is **not** `√2·Γ_Golay`
(that lattice has minimum `4·2 = 8`, while `Λ₀` contains the norm-`4` vectors `2a` with
`a = (±2,±2,0,…)`).  `Λ \ Λ₀ = u + 2A` consists of the vectors with all coordinates odd.

*Numerical check* (Python, the cyclic Golay code with generator `x¹¹+x¹⁰+x⁶+x⁵+x⁴+x²+1`): of the
`196560` norm-`4` vectors of `Λ`, `98256 = 1104 + 97152` lie in `Λ₀` and `98304 = 24·2¹²` in
`Λ \ Λ₀`.  Hence the expected split of `(V_Λ⁺)₂ = 98580` is `dim (V₀⁺)₂ = 300 + 49128 = 49428`,
`dim (V₃⁺)₂ = 49152`; both are proved in `FrameCount.lean` (`finrank_V0_grading_two`,
`finrank_V3_grading_two`).

## The sectors

`Λ₀ = ker β` and `β = ⟨8e₀,·⟩ mod 2`, so the momentum-sign automorphism `g = g_β`
(`LatGen.chiAut`, `Moonshine/FrameSign.lean`) acts on `p ⊗ e^α` by `(-1)^{β(α)}`.  It commutes with
`θ`, hence acts on `V_Λ⁺`, and

* `frameSector 0 = V₀⁺` — the `θ`-fixed states with all momenta in `Λ₀`
  (`mem_frameSector_zero_iff`);
* `frameSector 1 = V₃⁺` — the `θ`-fixed states with all momenta in `Λ \ Λ₀`
  (`mem_frameSector_one_iff`).

## Main results
* `Moonshine.frameAut : Aut leechVOA`, `frameAut_sq`, `frameAut_comm_leechTheta`.
* `Moonshine.frameSector : ZMod 2 → Submodule ℂ VPlus`, `frameSector_isInternal`
  (`V_Λ⁺ = V₀⁺ ⊕ V₃⁺`), `frameSector_smul_mem` (`u ∈ V_i`, `v ∈ V_j ⇒ u₍ₙ₎v ∈ V_{i+j}`).
* `Moonshine.frameSector_graded` — the sectors are graded (stable under the weight projections).
* `Moonshine.V0Sub : VOASubalgebra leechVOA` (`= V_Λ^{⟨θ,g⟩}`), `Moonshine.V0P :
  VertexOperatorAlgebra`, `V0P_centralCharge : c = 24`, `mem_V0Sub_iff`, and
  `frameSector_zero_eq_comap` identifying its carrier with `V₀⁺ ⊆ V_Λ⁺`.
* `Moonshine.lambda0`, `Moonshine.lambda0_eq_range_inclL`, `Moonshine.lambda0Equiv` (`A ≃ Λ₀`),
  `Moonshine.lambda0Equiv_form` (it is an isometry).
* `Moonshine.finrank_frameSector_grading_two_add` — `dim (V₀⁺)₂ + dim (V₃⁺)₂ = 98580`.

## Status
All declarations `sorry`-free; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`.
Unconditional.  The individual weight-`2` dimensions `49428`/`49152` are in `FrameWeightTwo.lean`
and `FrameCount.lean`.  **Not done:** the
identification of `V0P` with the `θ`-orbifold of the lattice VOA `V_{Λ₀}` (true by construction
up to the bridge `ofEbeling` for `Λ₀`, not stated); the twisted-sector split is in
`Moonshine/FrameTwisted.lean`.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine

open LatGen IntegralLattice Module

/-! ## §1  `Λ₀ = ker β` -/

/-- The Golay-frame character `β : Λ → ℤ/2`, `x ↦ x₀ mod 2`. -/
noncomputable def frameChar : leech.carrier →+ ZMod 2 := Leech.beta.toAddMonoidHom

theorem frameChar_apply (α : leech.carrier) : frameChar α = Leech.beta α := rfl

/-- **`Λ₀`**, the index-`2` sublattice `ker β = 2A` of the Leech lattice. -/
noncomputable def lambda0 : Submodule ℤ leech.carrier := LinearMap.ker Leech.beta

theorem mem_lambda0 (α : leech.carrier) : α ∈ lambda0 ↔ frameChar α = 0 := LinearMap.mem_ker

theorem lambda0_eq_range_inclL : lambda0 = LinearMap.range Leech.inclL := Leech.range_inclL.symm

/-- `a ↦ 2a` identifies `A` with `Λ₀`. -/
noncomputable def lambda0Equiv : ↥Leech.subA ≃ₗ[ℤ] ↥lambda0 :=
  (LinearEquiv.ofInjective Leech.inclL Leech.inclL_injective).trans
    (LinearEquiv.ofEq _ _ lambda0_eq_range_inclL.symm)

/-- `A ≃ Λ₀` is an isometry: the Leech form on `Λ₀` is the halved Golay form on `A`. -/
theorem lambda0Equiv_form (a b : ↥Leech.subA) :
    leech.form (lambda0Equiv a : leech.carrier) (lambda0Equiv b : leech.carrier)
      = Leech.subALattice.bilin a b :=
  Leech.inclL_bilin a b

/-- `[Λ : Λ₀] = 2`. -/
theorem card_quotient_lambda0 : Nat.card (leech.carrier ⧸ lambda0) = 2 := by
  have h := Leech.card_quotient_inclL
  rw [Leech.range_inclL] at h
  exact h

/-! ## §2  The automorphism `g` and the sectors -/

/-- The Golay-frame automorphism `g(p ⊗ e^α) = (-1)^{β(α)} p ⊗ e^α` of `V_Λ`. -/
noncomputable def frameAut : Aut leechVOA := chiAut leech frameChar leech_even leech_posDef

theorem frameAut_apply (v : LatModuleGen leech) : frameAut v = chiLat leech frameChar v := rfl

theorem frameAut_sq : frameAut * frameAut = 1 := chiAut_sq leech frameChar leech_even leech_posDef

theorem frameAut_comm_leechTheta : frameAut * leechTheta = leechTheta * frameAut :=
  chiAut_mul_thetaAut leech frameChar leech_even leech_posDef

/-- The carrier type of `V_Λ⁺`. -/
abbrev VPlus : Type := ↥(orbifold (Subgroup.zpowers leechTheta)).carrier

theorem chiLat_mem_plus {v : LatModuleGen leech}
    (hv : v ∈ (orbifold (Subgroup.zpowers leechTheta)).carrier) :
    chiLat leech frameChar v ∈ (orbifold (Subgroup.zpowers leechTheta)).carrier := by
  rw [mem_leechVOAPlus_iff] at hv ⊢
  rw [← chiLat_thetaLat, hv]

/-- `g` restricted to `V_Λ⁺`. -/
noncomputable def plusFrame : VPlus →ₗ[ℂ] VPlus :=
  ((chiLat leech frameChar).toLinearMap.comp
    (orbifold (Subgroup.zpowers leechTheta)).carrier.subtype).codRestrict _
    (fun v => chiLat_mem_plus v.2)

@[simp] theorem plusFrame_coe (v : VPlus) :
    ((plusFrame v : VPlus) : LatModuleGen leech) = chiLat leech frameChar v := rfl

theorem plusFrame_plusFrame (v : VPlus) : plusFrame (plusFrame v) = v :=
  Subtype.ext (chiLat_chiLat leech frameChar v)

/-- `g` as an automorphism of `V_Λ⁺`. -/
noncomputable def plusFrameAut : Aut leechVOAPlus where
  toLinearEquiv := LinearEquiv.ofInvolutive plusFrame plusFrame_plusFrame
  map_smul' u n v := Subtype.ext (frameAut.map_smul (u : LatModuleGen leech) n v)
  map_vacuum := Subtype.ext frameAut.map_vacuum
  map_omega := Subtype.ext frameAut.map_omega

theorem plusFrameAut_coe (v : VPlus) :
    ((plusFrameAut v : VPlus) : LatModuleGen leech) = chiLat leech frameChar v := rfl

/-- **The frame sectors** `V_i := {v ∈ V_Λ⁺ | g v = (-1)^i v}`; `V₀⁺ = frameSector 0`,
`V₃⁺ = frameSector 1`. -/
noncomputable def frameSector (i : ZMod 2) : Submodule ℂ VPlus :=
  Module.End.eigenspace (plusFrameAut.toLinearEquiv : Module.End ℂ VPlus)
    (Moonshine.Extraspecial.sgn i)

theorem mem_frameSector' {i : ZMod 2} {v : VPlus} :
    v ∈ frameSector i ↔ plusFrameAut v = Moonshine.Extraspecial.sgn i • v := by
  rw [frameSector, Module.End.mem_eigenspace_iff]
  rfl

theorem mem_frameSector {i : ZMod 2} {v : VPlus} :
    v ∈ frameSector i ↔ chiLat leech frameChar v = Moonshine.Extraspecial.sgn i • (v : LatModuleGen leech) := by
  rw [mem_frameSector', ← Subtype.coe_inj]
  rfl

/-- **`V₀⁺`: all momenta in `Λ₀`.** -/
theorem mem_frameSector_zero_iff (v : VPlus) :
    v ∈ frameSector 0 ↔ ∀ α, α ∉ lambda0 → coordEα leech α v = 0 := by
  rw [mem_frameSector, Moonshine.Extraspecial.sgn_zero, one_smul, chiLat_eq_self_iff]
  simp only [mem_lambda0]

/-- **`V₃⁺`: all momenta in `Λ \ Λ₀`.** -/
theorem mem_frameSector_one_iff (v : VPlus) :
    v ∈ frameSector 1 ↔ ∀ α, α ∈ lambda0 → coordEα leech α v = 0 := by
  rw [mem_frameSector, Moonshine.Extraspecial.sgn_one, neg_one_smul, chiLat_eq_neg_iff]
  simp only [mem_lambda0]

theorem frameSector_zero_eq : frameSector 0 = LinearMap.ker (plusFrame - 1) := by
  ext v
  rw [mem_frameSector', Moonshine.Extraspecial.sgn_zero, one_smul,
    LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  rfl

theorem frameSector_one_eq : frameSector 1 = LinearMap.ker (plusFrame + 1) := by
  ext v
  rw [mem_frameSector', Moonshine.Extraspecial.sgn_one, neg_one_smul,
    LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg]
  rfl

/-- **`V_Λ⁺ = V₀⁺ ⊕ V₃⁺`** (internal direct sum). -/
theorem frameSector_isInternal : DirectSum.IsInternal frameSector := by
  rw [DirectSum.isInternal_submodule_iff_isCompl frameSector (i := 0) (j := 1) (by decide)
    (by ext k; fin_cases k <;>
      simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff] <;>
      first | exact Or.inl rfl | exact Or.inr rfl), frameSector_zero_eq, frameSector_one_eq]
  exact isCompl_ker_sub_one_ker_add_one plusFrame plusFrame_plusFrame

theorem leechVOAPlus_smul_smul_smul (s t : ℂ) (u : VPlus) (n : ℤ) (v : VPlus) :
    leechVOAPlus.smul (s • u) n (t • v) = (s * t) • leechVOAPlus.smul u n v := by
  simp only [PreVertexAlgebra.smul_def, mode_apply, map_smul]
  rw [show (s • leechVOAPlus.Y u) (-n - 1) = s • leechVOAPlus.Y u (-n - 1) from rfl,
    LinearMap.smul_apply, smul_smul, mul_comm]

/-- **The `ℤ/2`-grading of products**: `u ∈ V_i`, `v ∈ V_j ⇒ u₍ₙ₎v ∈ V_{i+j}`. -/
theorem frameSector_smul_mem {i j : ZMod 2} {u v : VPlus} (hu : u ∈ frameSector i)
    (hv : v ∈ frameSector j) (n : ℤ) : leechVOAPlus.smul u n v ∈ frameSector (i + j) := by
  rw [mem_frameSector'] at hu hv ⊢
  rw [plusFrameAut.map_smul, hu, hv, leechVOAPlus_smul_smul_smul, Moonshine.Extraspecial.sgn_add]

/-- The sectors are graded: each is stable under the weight projections of `V_Λ⁺`. -/
theorem frameSector_graded (i : ZMod 2) (n : ℤ) {v : VPlus} (hv : v ∈ frameSector i) :
    piHom leechVOAPlus n v ∈ frameSector i := by
  rw [mem_frameSector'] at hv ⊢
  rw [Aut.map_piHom, hv, map_smul]

/-! ## §3  `V₀⁺` is a vertex operator algebra -/

/-- `V₀⁺ = (V_Λ⁺)^{⟨g⟩}` as a subalgebra of `V_Λ⁺`. -/
noncomputable def V0Sub : VOASubalgebra leechVOAPlus := orbifold (Subgroup.zpowers plusFrameAut)

theorem V0Sub_carrier : V0Sub.carrier = frameSector 0 := by
  ext v
  rw [V0Sub, mem_orbifold_zpowers_iff, mem_frameSector', Moonshine.Extraspecial.sgn_zero, one_smul]

/-- **`V₀⁺` is a vertex operator algebra** (the `g`-fixed subVOA of `V_Λ⁺`, i.e. the
`⟨θ, g⟩`-orbifold of `V_Λ`). -/
noncomputable def V0P : VertexOperatorAlgebra V0Sub.carrier := V0Sub.toVOA

/-- `c(V₀⁺) = 24`. -/
theorem V0P_centralCharge : V0P.centralCharge = 24 := by
  rw [V0P, VOASubalgebra.toVOA_centralCharge, leechVOAPlus_centralCharge]

/-! ## §4  Weight two -/

/-- For a linear involution `f` preserving a finite-dimensional `G`, the two eigenspaces split
`G`. -/
theorem finrank_comap_ker_add {M : Type*} [AddCommGroup M] [Module ℂ M] (f : M →ₗ[ℂ] M)
    (hf : ∀ x, f (f x) = x) (G : Submodule ℂ M) (hG : ∀ x ∈ G, f x ∈ G) [FiniteDimensional ℂ G] :
    finrank ℂ ↥((LinearMap.ker (f - 1)).comap G.subtype)
      + finrank ℂ ↥((LinearMap.ker (f + 1)).comap G.subtype) = finrank ℂ G := by
  set fG : G →ₗ[ℂ] G := f.restrict hG with hfG
  have h1 : (LinearMap.ker (f - 1)).comap G.subtype = LinearMap.ker (fG - 1) := by
    ext x
    simp only [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
      Submodule.coe_subtype, sub_eq_zero, hfG, Subtype.ext_iff, LinearMap.coe_restrict_apply]
  have h2 : (LinearMap.ker (f + 1)).comap G.subtype = LinearMap.ker (fG + 1) := by
    ext x
    simp only [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      Submodule.coe_subtype, hfG, Subtype.ext_iff, LinearMap.coe_restrict_apply,
      Submodule.coe_add, Submodule.coe_zero]
  rw [h1, h2]
  exact Submodule.finrank_add_eq_of_isCompl
    (isCompl_ker_sub_one_ker_add_one fG fun x => Subtype.ext (hf x))

/-- **`dim (V₀⁺)₂ + dim (V₃⁺)₂ = dim (V_Λ⁺)₂ = 98580`.** -/
theorem finrank_frameSector_grading_two_add :
    finrank ℂ ↥((frameSector 0).comap (leechVOAPlus.grading 2).subtype)
      + finrank ℂ ↥((frameSector 1).comap (leechVOAPlus.grading 2).subtype) = 98580 := by
  haveI := leechVOAPlus.finrank 2
  rw [frameSector_zero_eq, frameSector_one_eq,
    finrank_comap_ker_add plusFrame plusFrame_plusFrame _
      (fun x hx => plusFrameAut.map_grading hx), leechVOAPlus_finrank_grading_two]

end VOA.Moonshine
