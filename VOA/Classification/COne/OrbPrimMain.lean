import VOA.Classification.COne.OrbPrimSpectrum

/-! # OrbPrim: the B2 residual after (I) and (H1a)

`OrbPrimInvariant` proves the invariant theory (I) and `OrbPrimSpectrum` proves the primary
spectrum bound (H1a) of `V₂`. What remains of `OrbSpan.TetraPrimaryReduction` is the existence of
a polynomial model `T₂ : ℂ[x,y,z] → V₂` of the primaries (`V2TModel`): equivariance for `A₄`,
primary values of the right weight, rank `2n + 1` in degree `n`, the top channel, `r² ↦ 0`
modulo descendants, and the second channel at weight `36`.

`tetraPrimaryReduction_of_v2TModel`, `tetra_c2Cofinite_of_v2TModel`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbPrim
open VOA VertexOperatorAlgebra MvPolynomial OrbSpan OrbC2b OrbC2c OrbC2Fix VOA.LatGen
  VOA.LatGen.Triplet

universe u

/-- The `V₂`-level model without the spectrum bound (which is proved separately). -/
structure V2TModel {V : Type u} [AddCommGroup V] [Module ℂ V] {W₀ : VertexOperatorAlgebra V}
    (G : Subgroup (Aut W₀)) (T₂ : P3 →ₗ[ℂ] V) (φ : G →* (P3 ≃ₐ[ℂ] P3)) : Prop where
  /-- `G` acts on `T₂` through `φ`. -/
  eqv : ∀ (g : G) (F : P3), (g : Aut W₀) (T₂ F) = T₂ (φ g F)
  fix : ∀ (g : G) (F : P3), IsA4Inv F → φ g F = F
  gen1 : ∃ g : G, ∀ F, φ g F = s1 F
  gen2 : ∃ g : G, ∀ F, φ g F = s2 F
  gen3 : ∃ g : G, ∀ F, φ g F = rename cyc F
  hom : ∀ (g : G) (F : P3) (n : ℕ), F.IsHomogeneous n → (φ g F).IsHomogeneous n
  vac : T₂ 1 = W₀.vacuum
  grad : ∀ (F : P3) (n : ℕ), F.IsHomogeneous n → T₂ F ∈ W₀.grading ((n : ℤ) ^ 2)
  /-- (H1b) primary values. -/
  primVal : ∀ (F : P3) (n : ℕ), 1 ≤ n → F.IsHomogeneous n → T₂ F ∈ prim W₀ ((n : ℤ) ^ 2)
  /-- (H1c) rank `2n + 1` in degree `n`. -/
  rank : ∀ n : ℕ, 2 * n + 1 ≤
    Module.finrank ℂ (Submodule.span ℂ (T₂ '' {F | F.IsHomogeneous n}))
  /-- (H2) the top channel. -/
  top : ∀ (G H : P3) (s m : ℕ), G.IsHomogeneous s → H.IsHomogeneous m → 1 ≤ s → 1 ≤ m →
    ∃ c : ℂ, T₂ (G * H) - c • W₀.smul (T₂ G) (-((2 * s * m : ℕ) : ℤ) - 1) (T₂ H) ∈
      lowerDesc W₀ (((s + m : ℕ) : ℤ) ^ 2)
  r2 : T₂ r2 ∈ lowerDesc W₀ 4
  /-- (N) the second channel `v₍₋₁₂₎u` at weight `36`. -/
  six : ∃ c d : ℂ, c ≠ 0 ∧
    W₀.smul (T₂ I4) (-12) (T₂ I3) - c • T₂ I6 - d • T₂ (I3 * I3) ∈ lowerDesc W₀ 36

theorem V2TModel.toSplit {V : Type u} [AddCommGroup V] [Module ℂ V]
    {W₀ : VertexOperatorAlgebra V} {G : Subgroup (Aut W₀)} {T₂ : P3 →ₗ[ℂ] V}
    {φ : G →* (P3 ≃ₐ[ℂ] P3)} (h : V2TModel G T₂ φ) (hS : PrimSpectrumBound W₀) :
    V2ModelSplit G T₂ φ :=
  ⟨h.eqv, h.fix, h.gen1, h.gen2, h.gen3, h.hom, h.vac, h.grad, hS, h.primVal, h.rank, h.top,
    h.r2, h.six⟩

/-- **B2 primary reduction**, conditional only on the polynomial model `V2TModel`. -/
theorem tetraPrimaryReduction_of_v2TModel {T₂ : P3 →ₗ[ℂ] LatModuleGen (latP 1)}
    {φ : tetra →* (P3 ≃ₐ[ℂ] P3)} (h : V2TModel tetra T₂ φ) : TetraPrimaryReduction :=
  tetraPrimaryReduction_of_v2ModelSplit (h.toSplit primSpectrumBound_V2)

theorem tetrahedralVirasoroSpan_of_v2TModel {T₂ : P3 →ₗ[ℂ] LatModuleGen (latP 1)}
    {φ : tetra →* (P3 ≃ₐ[ℂ] P3)} (h : V2TModel tetra T₂ φ) : TetrahedralVirasoroSpan :=
  tetrahedralVirasoroSpan_of_primaryReduction (tetraPrimaryReduction_of_v2TModel h)

/-- `C₂` for `V₂^{A₄}` from the polynomial model and the corrected Dong--Jiang relations. -/
theorem tetra_c2Cofinite_of_v2TModel {T₂ : P3 →ₗ[ℂ] LatModuleGen (latP 1)}
    {φ : tetra →* (P3 ≃ₐ[ℂ] P3)} (h : V2TModel tetra T₂ φ)
    (hr : TetrahedralDongJiangRelationsCorrected) : C2Cofinite (orbifoldVOA tetra) :=
  tetra_c2Cofinite_of_primaryReduction (tetraPrimaryReduction_of_v2TModel h) hr

end VOA.Classification.COne.OrbPrim
