import VOA.Classification.COne.MainConverse
import VOA.Classification.COne.OrbC2dExceptional

/-!
# B3 narrowed to two concrete models and the icosahedral case

`FiniteV2OrbifoldRationalOfC2Fact` (B3) quantifies over EVERY finite subgroup of `Aut V₂`, but the
converse of Gannon–Rayhaun consumes it only at the three exceptional groups.  This file

* splits the consumed part into three named Props, one per group:
  `CubicModelRationalOfC2` (the tetrahedral case, stated for the single concrete model
  `(V₈⁺)^{ℤ/3} = orbifoldVOA (zpowers kleinCubic)`), `InvolutionModelRationalOfC2` (the octahedral
  case, for the single concrete model `(V₂^{A₄})^{ℤ/2}`), and `IcosahedralV2OrbifoldRationalOfC2`
  (the `A₅` case, left isolated);
* proves that the two model Props are EQUIVALENT to the statements for every abstract `A₄`
  (resp. `S₄`) subgroup, using the proved conjugacy theorems (`OrbC2d.tetrahedralConjugacy`,
  `OrbC2d.octahedralConjugacy`) and the proved model isomorphisms (`OrbC2b.tetra_cubic_iso`,
  `OrbC2b.octa_involution_iso`);
* proves that B3 implies each of the three (so none is stronger than B3);
* re-assembles the converse of Gannon–Rayhaun from the three narrower Props
  (`gannonRayhaunConverse_of_models`).

No new mathematics about rationality is claimed here: all three Props remain OPEN.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbRat2

open VOA VertexOperatorAlgebra OrbC2b

/-! ## Transport along VOA isomorphisms -/

section Transport

universe u

variable {𝒱 𝒲 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] [AddCommGroup 𝒲] [Module ℂ 𝒲]
  {V : VertexOperatorAlgebra 𝒱} {T : VertexOperatorAlgebra 𝒲}

theorem VOAIsomorphic.symm' (h : VOAIsomorphic V T) : VOAIsomorphic T V := by
  obtain ⟨e, he, hω⟩ := h
  exact ⟨e.symm, isVOAHom_symm' e he, symm_conformal e hω⟩

theorem c2Cofinite_iff_of_iso (h : VOAIsomorphic V T) : C2Cofinite V ↔ C2Cofinite T := by
  obtain ⟨e, he, hω⟩ := h
  exact ⟨ConverseUniverse.c2Cofinite_of_iso e.symm (isVOAHom_symm' e he),
    ConverseUniverse.c2Cofinite_of_iso e he⟩

theorem admissiblyRational_iff_of_iso (h : VOAIsomorphic V T) :
    AdmissiblyRational V ↔ AdmissiblyRational T := by
  obtain ⟨e, he, hω⟩ := h
  exact ⟨admissiblyRational_of_iso e.symm (isVOAHom_symm' e he) (symm_conformal e hω),
    admissiblyRational_of_iso e he hω⟩

/-- "C₂ implies rational" is invariant under VOA isomorphism. -/
theorem rationalOfC2_iff_of_iso (h : VOAIsomorphic V T) :
    (C2Cofinite V → AdmissiblyRational V) ↔ (C2Cofinite T → AdmissiblyRational T) := by
  rw [c2Cofinite_iff_of_iso h, admissiblyRational_iff_of_iso h]

end Transport

/-! ## The three narrowed Props -/

/-- The concrete tetrahedral model `(V₈⁺)^{ℤ/3}`: the fixed points of the constructed order-three
automorphism `kleinCubic` of `orbifoldVOA klein ≅ V₈⁺` (`klein_iso_plus_four`). -/
abbrev cubicModel := orbifoldVOA (Subgroup.zpowers kleinCubic)

/-- The concrete octahedral model `(V₂^{A₄})^{ℤ/2}`. -/
abbrev involutionModel := orbifoldVOA (Subgroup.zpowers tetraInvolution)

/-- OPEN (true: Dong–Jiang, J. Algebra 377 (2013), arXiv:1209.1168; also Carnahan–Miyamoto
arXiv:1603.05645v4 Cor. 5.25 for solvable groups, McRae arXiv:1910.13226v2 Cor. 4.23):
rationality of the tetrahedral model, given its C₂-cofiniteness. -/
def CubicModelRationalOfC2 : Prop :=
  C2Cofinite cubicModel → AdmissiblyRational cubicModel

/-- OPEN (true: Carnahan–Miyamoto Cor. 5.25, McRae Cor. 4.23): rationality of the octahedral
model, given its C₂-cofiniteness. -/
def InvolutionModelRationalOfC2 : Prop :=
  C2Cofinite involutionModel → AdmissiblyRational involutionModel

/-- OPEN (true: McRae Cor. 4.23 with Xu arXiv:2608.13872v2 Thm 1.1 / Cor 1.2): the icosahedral
case, isolated. -/
def IcosahedralV2OrbifoldRationalOfC2 : Prop :=
  ∀ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* alternatingGroup (Fin 5)) →
    C2Cofinite (orbifoldVOA G) → AdmissiblyRational (orbifoldVOA G)

/-- The part of B3 that the converse actually consumes. -/
def ExceptionalV2OrbifoldRationalOfC2 : Prop :=
  ∀ G : Subgroup (Aut (V2m 1 le_rfl)), IsExceptionalV2Group G →
    C2Cofinite (orbifoldVOA G) → AdmissiblyRational (orbifoldVOA G)

/-! ## Model equivalences -/

/-- The tetrahedral model Prop is exactly the statement for every abstract `A₄` subgroup. -/
theorem cubicModelRationalOfC2_iff :
    CubicModelRationalOfC2 ↔
      ∀ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* alternatingGroup (Fin 4)) →
        C2Cofinite (orbifoldVOA G) → AdmissiblyRational (orbifoldVOA G) := by
  have hm := rationalOfC2_iff_of_iso tetra_cubic_iso
  constructor
  · intro h G hG
    obtain ⟨g, hg⟩ := OrbC2d.tetrahedralConjugacy G hG
    have hc : VOAIsomorphic (orbifoldVOA G) (orbifoldVOA tetra) := by
      rw [← hg]; exact orbifold_conj_iso g G
    exact (rationalOfC2_iff_of_iso hc).mpr (hm.mp h)
  · intro h
    exact hm.mpr (h tetra tetra_group)

/-- The octahedral model Prop is exactly the statement for every abstract `S₄` subgroup. -/
theorem involutionModelRationalOfC2_iff :
    InvolutionModelRationalOfC2 ↔
      ∀ G : Subgroup (Aut (V2m 1 le_rfl)), Nonempty (G ≃* Equiv.Perm (Fin 4)) →
        C2Cofinite (orbifoldVOA G) → AdmissiblyRational (orbifoldVOA G) := by
  have hm := rationalOfC2_iff_of_iso octa_involution_iso
  constructor
  · intro h G hG
    obtain ⟨g, hg⟩ := OrbC2d.octahedralConjugacy G hG
    have hc : VOAIsomorphic (orbifoldVOA G) (orbifoldVOA octa) := by
      rw [← hg]; exact orbifold_conj_iso g G
    exact (rationalOfC2_iff_of_iso hc).mpr (hm.mp h)
  · intro h
    exact hm.mpr (h octa octa_group)

/-- The consumed part of B3 follows from the two concrete models and the icosahedral case. -/
theorem exceptionalV2OrbifoldRationalOfC2_of_models (hC : CubicModelRationalOfC2)
    (hI : InvolutionModelRationalOfC2) (hIco : IcosahedralV2OrbifoldRationalOfC2) :
    ExceptionalV2OrbifoldRationalOfC2 := by
  intro G hG
  rcases hG with h | h | h
  · exact cubicModelRationalOfC2_iff.mp hC G h
  · exact involutionModelRationalOfC2_iff.mp hI G h
  · exact hIco G h

/-- B3 implies the consumed part. -/
theorem exceptionalV2OrbifoldRationalOfC2_of_finite (h : FiniteV2OrbifoldRationalOfC2Fact) :
    ExceptionalV2OrbifoldRationalOfC2 := by
  intro G hG
  letI := exceptionalV2Group_finite hG
  exact h G

/-- The consumed part is equivalent to the three narrowed Props together. -/
theorem exceptionalV2OrbifoldRationalOfC2_iff :
    ExceptionalV2OrbifoldRationalOfC2 ↔
      CubicModelRationalOfC2 ∧ InvolutionModelRationalOfC2 ∧
        IcosahedralV2OrbifoldRationalOfC2 := by
  constructor
  · intro h
    refine ⟨cubicModelRationalOfC2_iff.mpr fun G hG => h G (Or.inl hG),
      involutionModelRationalOfC2_iff.mpr fun G hG => h G (Or.inr (Or.inl hG)),
      fun G hG => h G (Or.inr (Or.inr hG))⟩
  · rintro ⟨hC, hI, hIco⟩
    exact exceptionalV2OrbifoldRationalOfC2_of_models hC hI hIco

theorem cubicModelRationalOfC2_of_finite (h : FiniteV2OrbifoldRationalOfC2Fact) :
    CubicModelRationalOfC2 :=
  (exceptionalV2OrbifoldRationalOfC2_iff.mp (exceptionalV2OrbifoldRationalOfC2_of_finite h)).1

theorem involutionModelRationalOfC2_of_finite (h : FiniteV2OrbifoldRationalOfC2Fact) :
    InvolutionModelRationalOfC2 :=
  (exceptionalV2OrbifoldRationalOfC2_iff.mp (exceptionalV2OrbifoldRationalOfC2_of_finite h)).2.1

theorem icosahedralV2OrbifoldRationalOfC2_of_finite (h : FiniteV2OrbifoldRationalOfC2Fact) :
    IcosahedralV2OrbifoldRationalOfC2 :=
  (exceptionalV2OrbifoldRationalOfC2_iff.mp (exceptionalV2OrbifoldRationalOfC2_of_finite h)).2.2

/-! ## The converse from the narrowed inputs -/

theorem exceptionalOrbifold_nice_of_narrowed (hSolv : SolvableExceptionalOrbifoldC2Fact)
    (hXu : XuIcosahedralPoissonRelations) (hRat : ExceptionalV2OrbifoldRationalOfC2)
    (hPU : ExceptionalOrbifoldPositiveWeightsFact)
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hG : IsExceptionalV2Group G) :
    Nice (orbifoldVOA G) ∧ (orbifoldVOA G).centralCharge = 1 := by
  letI := exceptionalV2Group_finite hG
  have hC2 := exceptionalOrbifold_c2_of_inputs hSolv hXu G hG
  have hSR : StronglyRational (orbifoldVOA G) :=
    ⟨⟨exceptionalOrbifold_isSimple G, exceptionalOrbifold_selfDual G, hC2⟩, hRat G hG hC2⟩
  exact ⟨⟨hSR, hPU G hG hSR⟩, exceptionalOrbifold_centralCharge G⟩

theorem nice_of_hasCOneLabel_exceptional_of_narrowed (hSolv : SolvableExceptionalOrbifoldC2Fact)
    (hXu : XuIcosahedralPoissonRelations) (hRat : ExceptionalV2OrbifoldRationalOfC2)
    (hPU : ExceptionalOrbifoldPositiveWeightsFact)
    {𝒱 : Type} [AddCommGroup 𝒱] [Module ℂ 𝒱] (V : VertexOperatorAlgebra 𝒱)
    {l : COneLabel} (hl : l.IsExceptional) (h : HasCOneLabel V l) :
    Nice V ∧ V.centralCharge = 1 := by
  have hex : ∃ G, IsExceptionalV2Group G ∧ VOAIsomorphic V (orbifoldVOA G) := by
    cases l with
    | tetra => obtain ⟨G, hG, hV⟩ := h; exact ⟨G, Or.inl hG, hV⟩
    | octa => obtain ⟨G, hG, hV⟩ := h; exact ⟨G, Or.inr (Or.inl hG), hV⟩
    | icosa => obtain ⟨G, hG, hV⟩ := h; exact ⟨G, Or.inr (Or.inr hG), hV⟩
    | lat _ => exact hl.elim
    | plus _ => exact hl.elim
  obtain ⟨G, hG, e, he, hω⟩ := hex
  have hN := exceptionalOrbifold_nice_of_narrowed hSolv hXu hRat hPU G hG
  refine ⟨⟨stronglyRational_of_iso e he hω hN.1.1,
    pseudoUnitary_of_iso e he hω hN.1.2⟩, ?_⟩
  rw [centralCharge_eq_of_iso e he hω hN.1.1.simple.vacuum_ne_zero, hN.2]

/-- The converse of Gannon–Rayhaun with B3 replaced by its consumed part. -/
theorem gannonRayhaunConverse_of_narrowed (hSolv : SolvableExceptionalOrbifoldC2Fact)
    (hXu : XuIcosahedralPoissonRelations) (hRat : ExceptionalV2OrbifoldRationalOfC2)
    (hPU : ExceptionalOrbifoldPositiveWeightsFact) : GannonRayhaunConverse.{0} := by
  intro 𝒱 _ _ V hV
  obtain ⟨l, hl⟩ := (inCOneList_iff_exists_label V).mp hV
  cases l with
  | lat m => exact nice_of_hasCOneLabel_lat V m hl
  | plus m => exact nice_of_hasCOneLabel_plus_of_rational v2mPlusRationalFactGe2_holds V m hl
  | tetra =>
    exact nice_of_hasCOneLabel_exceptional_of_narrowed hSolv hXu hRat hPU V (l := .tetra) trivial hl
  | octa =>
    exact nice_of_hasCOneLabel_exceptional_of_narrowed hSolv hXu hRat hPU V (l := .octa) trivial hl
  | icosa =>
    exact nice_of_hasCOneLabel_exceptional_of_narrowed hSolv hXu hRat hPU V (l := .icosa) trivial hl

/-- The converse of Gannon–Rayhaun with B3 replaced by the two concrete models and the
isolated icosahedral case (B2, B4, B5 unchanged). -/
theorem gannonRayhaunConverse_of_models (hSolv : SolvableExceptionalOrbifoldC2Fact)
    (hXu : XuIcosahedralPoissonRelations) (hC : CubicModelRationalOfC2)
    (hI : InvolutionModelRationalOfC2) (hIco : IcosahedralV2OrbifoldRationalOfC2)
    (hPU : ExceptionalOrbifoldPositiveWeightsFact) : GannonRayhaunConverse.{0} :=
  gannonRayhaunConverse_of_narrowed hSolv hXu
    (exceptionalV2OrbifoldRationalOfC2_of_models hC hI hIco) hPU

end VOA.Classification.COne.OrbRat2
