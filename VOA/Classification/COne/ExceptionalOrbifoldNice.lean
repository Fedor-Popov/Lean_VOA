import VOA.Classification.COne.ExceptionalOrbifoldC2
import VOA.Classification.COne.PlusUnitaryFinal
import VOA.Classification.COne.ConverseUniverseTransport
import VOA.Classification.COne.V2Icosahedral

/-!
# Exceptional orbifolds: structural theorems and explicit remaining inputs

The structural results hold in every carrier universe. The final niceness and
converse assembly below is explicitly at universe zero, matching the existing
plus-rationality input; no claim of universe-polymorphic rationality transport
is made. Every literature input below is a `def ... : Prop`, never an axiom.

Literature sources:
* Miyamoto, CMP 335 (2015), 1279–1286, arXiv:1306.5031: solvable finite groups.
* Carnahan–Miyamoto, arXiv:1603.05645v4, Corollary 5.25: regularity for solvable
  finite groups; the ambient VOA must be simple, regular, nonnegatively graded,
  and self-dual. This does not handle `A₅`.
* McRae, CMP 383 (2021), 1939–2019, arXiv:1910.13226v2, Corollary 4.23:
  strong rationality of a finite orbifold PROVIDED it is C₂-cofinite.
* Dong–Ren–Xu, Adv. Math. 321 (2017), 1–30, arXiv:1507.03306v2, Theorem 3.3
  and Remark 3.4: twisted-sector completeness assumes the fixed-point algebra
  is rational and C₂-cofinite; Corollary 3.5 additionally needs twisted-sector
  positivity. It does not prove the missing C₂-cofiniteness.
* Xu's arXiv:2608.13872v2 is accessible: Theorem 1.1 and Corollary 1.2 state
  the icosahedral C₂ and strong-rationality results. `ExceptionalOrbifoldC2`
  separates the unproved VOA relations from the proved final linear algebra.

Dead ends: subgroup inclusion only embeds fixed-point algebras, and does not
make C₂-cofiniteness descend to a smaller subalgebra. Finite strong generation
alone does not give finite-dimensional C₂ quotient. Neither a character nor
the numerical determinant proves twisted-sector completeness or the VOA
coefficient identities. No use is made of the gapped arXiv:1812.00570 claim.
-/

namespace VOA.Classification.COne
open VOA VertexOperatorAlgebra

/-- The three exceptional abstract group types, imposed on actual subgroups of `Aut V₂`. -/
def IsExceptionalV2Group (G : Subgroup (Aut (V2m 1 le_rfl))) : Prop :=
  Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
  Nonempty (G ≃* Equiv.Perm (Fin 4)) ∨
  Nonempty (G ≃* alternatingGroup (Fin 5))

theorem exceptionalV2Group_finite {G : Subgroup (Aut (V2m 1 le_rfl))}
    (hG : IsExceptionalV2Group G) : Finite G := by
  rcases hG with h | h | h
  all_goals
    obtain ⟨e⟩ := h
    exact Finite.of_equiv _ e.symm.toEquiv

/-- The exceptional group predicate has actual witnesses in all three cases. -/
theorem exceptionalV2Group_exists :
    (∃ G : Subgroup (Aut (V2m 1 le_rfl)),
      Nonempty (G ≃* alternatingGroup (Fin 4)) ∧ IsExceptionalV2Group G) ∧
    (∃ G : Subgroup (Aut (V2m 1 le_rfl)),
      Nonempty (G ≃* Equiv.Perm (Fin 4)) ∧ IsExceptionalV2Group G) ∧
    (∃ G : Subgroup (Aut (V2m 1 le_rfl)),
      Nonempty (G ≃* alternatingGroup (Fin 5)) ∧ IsExceptionalV2Group G) := by
  obtain ⟨G₄, h₄⟩ := exists_A4_subgroup
  obtain ⟨Gₛ, hₛ⟩ := exists_S4_subgroup
  obtain ⟨G₅, h₅⟩ := exists_A5_subgroup
  exact ⟨⟨G₄, h₄, Or.inl h₄⟩, ⟨Gₛ, hₛ, Or.inr (Or.inl hₛ)⟩,
    ⟨G₅, h₅, Or.inr (Or.inr h₅)⟩⟩

/-- Full CFT type, including a one-dimensional degree-zero piece and finite graded pieces. -/
theorem exceptionalOrbifold_cftType (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G] :
    (∀ n : ℤ, n < 0 → (orbifoldVOA G).grading n = ⊥) ∧
    Module.finrank ℂ ((orbifoldVOA G).grading 0) = 1 ∧
    (∀ n : ℤ, FiniteDimensional ℂ ((orbifoldVOA G).grading n)) :=
  ⟨(orbifoldVOA G).positivity,
    VertexOperatorAlgebra.finrank_grading_zero_eq_one
      (exceptionalOrbifold_isSimple G).vacuum_ne_zero,
    (orbifoldVOA G).finrank⟩

universe u

/-- Structural properties transport to any universe and any finite-group orbifold label. -/
theorem exceptionalOrbifold_structural_of_iso {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (V : VertexOperatorAlgebra 𝒱) {H : Type} [Group H] [Finite H]
    (h : IsV2Orbifold V H) : V.IsSimple ∧ V.SelfDual ∧ V.centralCharge = 1 := by
  obtain ⟨G, ⟨eG⟩, e, he, hω⟩ := h
  letI : Finite G := Finite.of_equiv H eG.symm.toEquiv
  refine ⟨ConverseUniverse.isSimple_of_iso e he (exceptionalOrbifold_isSimple G),
    ConverseUniverse.selfDual_of_iso e he hω (exceptionalOrbifold_selfDual G), ?_⟩
  rw [ConverseUniverse.centralCharge_eq_of_iso e he hω
    (exceptionalOrbifold_isSimple G).vacuum_ne_zero, exceptionalOrbifold_centralCharge]

/-- The cheap part of all three exceptional clauses, including the extra weight-one vanishing. -/
theorem exceptionalOrbifold_structural_of_label {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (V : VertexOperatorAlgebra 𝒱) {l : COneLabel} (hl : l.IsExceptional)
    (h : HasCOneLabel V l) : V.IsSimple ∧ V.SelfDual ∧ V.centralCharge = 1 ∧
      Module.finrank ℂ (V.grading 1) = 0 := by
  have hs : V.IsSimple ∧ V.SelfDual ∧ V.centralCharge = 1 := by
    cases l with
    | tetra => exact exceptionalOrbifold_structural_of_iso V h
    | octa => exact exceptionalOrbifold_structural_of_iso V h
    | icosa => exact exceptionalOrbifold_structural_of_iso V h
    | lat _ => exact hl.elim
    | plus _ => exact hl.elim
  exact ⟨hs.1, hs.2.1, hs.2.2, finrank_one_of_exceptional hl h⟩

/-- Miyamoto's solvable-orbifold C₂ theorem specialized to `V₂` and the solvable
exceptional groups `A₄`, `S₄`. Source: arXiv:1306.5031, main theorem.
Their solvability and the analytic orbifold theorem are not proved here. -/
def SolvableExceptionalOrbifoldC2Fact : Prop :=
  ∀ G : Subgroup (Aut (V2m 1 le_rfl)),
    (Nonempty (G ≃* alternatingGroup (Fin 4)) ∨ Nonempty (G ≃* Equiv.Perm (Fin 4))) →
    C2Cofinite (orbifoldVOA G)

/-- McRae Corollary 4.23, arXiv:1910.13226v2, specialized to the already
strongly rational `V₂`. C₂-cofiniteness is an essential hypothesis. -/
def FiniteV2OrbifoldRationalOfC2Fact : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))) [Finite G],
    C2Cofinite (orbifoldVOA G) → AdmissiblyRational (orbifoldVOA G)

/-- The positive-weight part of GR Proposition 3.2 and Appendix A
(https://arxiv.org/html/2609.00122), restricted to exceptional orbifolds.
One route is DRX Theorem 3.3/Corollary 3.5 plus positive twisted-sector weights;
the required sector constructions and completeness are NOT formalized here.
See also Wu–Zhang arXiv:1603.01797 for `S₄`, `A₅`. Rationality is retained explicitly. -/
def ExceptionalOrbifoldPositiveWeightsFact : Prop :=
  ∀ G : Subgroup (Aut (V2m 1 le_rfl)), IsExceptionalV2Group G →
    StronglyRational (orbifoldVOA G) → PseudoUnitary (orbifoldVOA G)

/-- C₂ for all three cases, conditional on the solvable theorem and Xu's VOA relations. -/
theorem exceptionalOrbifold_c2_of_inputs (hSolv : SolvableExceptionalOrbifoldC2Fact)
    (hXu : XuIcosahedralPoissonRelations) (G : Subgroup (Aut (V2m 1 le_rfl)))
    (hG : IsExceptionalV2Group G) : C2Cofinite (orbifoldVOA G) := by
  rcases hG with h | h | h
  · exact hSolv G (Or.inl h)
  · exact hSolv G (Or.inr h)
  · exact (exceptionalOrbifold_icosa_c2_of_relations hXu G h).1

/-- All four remaining inputs are visible; simplicity and self-duality are proved. -/
theorem exceptionalOrbifold_nice_of_inputs (hSolv : SolvableExceptionalOrbifoldC2Fact)
    (hXu : XuIcosahedralPoissonRelations) (hRat : FiniteV2OrbifoldRationalOfC2Fact)
    (hPU : ExceptionalOrbifoldPositiveWeightsFact)
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hG : IsExceptionalV2Group G) :
    Nice (orbifoldVOA G) ∧ (orbifoldVOA G).centralCharge = 1 := by
  letI := exceptionalV2Group_finite hG
  have hC2 := exceptionalOrbifold_c2_of_inputs hSolv hXu G hG
  have hSR : StronglyRational (orbifoldVOA G) :=
    ⟨⟨exceptionalOrbifold_isSimple G, exceptionalOrbifold_selfDual G, hC2⟩, hRat G hC2⟩
  exact ⟨⟨hSR, hPU G hG hSR⟩, exceptionalOrbifold_centralCharge G⟩

/-- Exceptional converse clauses, explicitly for carrier universe zero. -/
theorem nice_of_hasCOneLabel_exceptional_of_inputs (hSolv : SolvableExceptionalOrbifoldC2Fact)
    (hXu : XuIcosahedralPoissonRelations) (hRat : FiniteV2OrbifoldRationalOfC2Fact)
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
  have hN := exceptionalOrbifold_nice_of_inputs hSolv hXu hRat hPU G hG
  refine ⟨⟨stronglyRational_of_iso e he hω hN.1.1,
    pseudoUnitary_of_iso e he hω hN.1.2⟩, ?_⟩
  rw [centralCharge_eq_of_iso e he hω hN.1.1.simple.vacuum_ne_zero, hN.2]

/-- The complete universe-zero converse, conditional on plus rationality and the
four exceptional inputs. This is not an unconditional converse. -/
theorem gannonRayhaunConverse_of_exceptional_inputs (hPlus : V2mPlusRationalFactGe2)
    (hSolv : SolvableExceptionalOrbifoldC2Fact) (hXu : XuIcosahedralPoissonRelations)
    (hRat : FiniteV2OrbifoldRationalOfC2Fact) (hPU : ExceptionalOrbifoldPositiveWeightsFact) :
    GannonRayhaunConverse.{0} := by
  intro 𝒱 _ _ V hV
  obtain ⟨l, hl⟩ := (inCOneList_iff_exists_label V).mp hV
  cases l with
  | lat m => exact nice_of_hasCOneLabel_lat V m hl
  | plus m => exact nice_of_hasCOneLabel_plus_of_rational hPlus V m hl
  | tetra =>
    exact nice_of_hasCOneLabel_exceptional_of_inputs hSolv hXu hRat hPU V (l := .tetra) trivial hl
  | octa =>
    exact nice_of_hasCOneLabel_exceptional_of_inputs hSolv hXu hRat hPU V (l := .octa) trivial hl
  | icosa =>
    exact nice_of_hasCOneLabel_exceptional_of_inputs hSolv hXu hRat hPU V (l := .icosa) trivial hl

end VOA.Classification.COne
