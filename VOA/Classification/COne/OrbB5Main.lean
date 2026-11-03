import VOA.Classification.COne.OrbB5Vacuum
import VOA.Classification.COne.OrbB5Pairing
import VOA.Classification.COne.OrbC2dExceptional
import VOA.Classification.COne.OrbPos12Reduction

/-! # B5: current map and the tetrahedral closure

## Existing reductions, checked against declarations rather than old docstrings

* OrbPos8 proves positive weights for arbitrary irreducible nonidentity V2
  twists, with gap 1/100 for orders at most five. Its B5 endpoint needs only
  `OrbPos2.ExceptionalDRXEmbedding`. Twisted-weight arithmetic is not open.
* OrbPos9's canonical extension algebra and associativity are proved.
  OrbPos10 proves `ExceptionalFreeSimpleTargets`; that is not an open leaf.
* The most decomposed pre-existing endpoint is OrbPos12's
  `exceptionalOrbifoldPositiveWeightsFact_of_projections_awayFixed`.
  Its exact leaves are `OrbPos11.ExceptionalSectorProjections` and
  `OrbPos12.ExceptionalActionJacobiAwayFixed`.
* OrbPos13 proves the first equivalent to
  `OrbPos10.ExceptionalSimpleActionMonodromy`; OrbPos12 proves the second
  equivalent to `OrbPos11.ExceptionalActionTwistedJacobi`.
  Neither equivalence proves either side. These are well-posed mathematical
  obligations supported by McRae's categorical and twisted-field dictionary
  theorems (arXiv:1910.13226v2, Sections 3 and 4), not known false propositions.
* The older `V2InnerTwistedSpectrum` asks for uniform parity, stronger than
  OrbPos8's inclusion with a weight-dependent integer label. It remains
  unproved as named, but unnecessary for B5. Likewise
  `V2TorusOrdinaryUntwist` and the equivalent
  `V2TorusLatticeEnergyRealization` remain stronger, bypassed classification
  obligations. Constructed lattice modules do not prove those universal claims.

## New closure

OrbB5Tetra applies OrbZhuParity's already proved conformal polynomial to
arbitrary actual bottom spaces. OrbB5Vacuum identifies the zero bottom by
the even/odd Zhu decomposition. Thus all A4 embeddings have positive
non-vacuum weights, without strong rationality or DRX. The exact remaining
group cases are the standard S4 embedding and all A5 embeddings, as the iff
below states. This does not prove the universal categorical leaves above.

## Remaining work and estimates (planning estimates, not measured bounds)

* Sector projections: OrbB5Pairing supplies haploidity, the actual averaging
  equation, invariant symmetric evaluation, and normalization equivalence.
  Still construct a copairing with zig-zags and dimension |G|, then prove
  action-linearity, sector support and the identity sum. Roughly 800--2000
  lines of categorical/VOA work; small symbolic proofs rather than certificates.
* Nonfixed Jacobi: use OrbPos12 normalized branches and OrbPos13 braided
  exchange, then glue product/reversed-product/iterate channels and extract
  fractional coefficients. Roughly 1000--2500 lines by comparison with the
  existing HKLLoc files; finite scoped elaboration, no coefficient brute force.
* Direct S4/A5 Zhu route: obtain a conformal annihilator and a vacuum-fiber
  description. The A4 proof here shows what would suffice. No comparable
  complete S4/A5 Zhu input was located; certificate sizes cannot responsibly
  be inferred from the 13-root A4 table. A4 itself uses symbolic span arguments
  and 13 scalar arithmetic cases, with no new lattice coefficient certificate.

## Dead ends with explicit evidence

* OrbPos13.descendedMonodromy_eq_id: descent through a unital action already
  forces the descended endomorphism to be the identity. Schur does not create
  a group label. U-linear spectral idempotents do not establish A-linearity.
* OrbPos13.ambientSymmetry_mem_fixed_iff: applying G cannot move a nonfixed
  insertion into the fixed algebra, so fixed-insertion Jacobi is insufficient.
* OrbSpan.latticeVirUnitary is a form on the vacuum carrier, not an invariant
  positive form on every orbifold module. OrbPrim's primary dimensions have
  the same ambient-carrier limitation. OrbRat6's conjugation and top-line
  characters supply constructed modules, not their exhaustion; they do help
  through the proved OrbZhuParity relation used in the new A4 proof.
* Moonshine.latticeTwistedModule requires a unimodular Gram matrix and is a
  theta-twist construction. A1 has Gram determinant 2; it is not directly an
  A1 all-sector classification theorem. OrbPos7 already supplies inner twists.
* Rigidity APIs requiring `Nice (orbifoldVOA G)` assume positivity and are
  circular here. None is used in the new positivity proof.
-/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbB5
open VOA OrbC2b OrbC2c

/-- B5 for every tetrahedral embedding, without a rationality premise. -/
theorem tetrahedral_orbifold_pseudoUnitary
    (G : Subgroup (Aut (V2m 1 le_rfl)))
    (hG : Nonempty (G ≃* alternatingGroup (Fin 4))) : PseudoUnitary (orbifoldVOA G) := by
  obtain ⟨e, he, hω⟩ := tetrahedralStandardForm_of_conjugacy
    OrbC2d.tetrahedralConjugacy G hG
  exact pseudoUnitary_of_iso e he hω tetra_pseudoUnitary

/-- The remaining B5 inputs are only the standard octahedral orbifold and
the icosahedral embeddings. The A4 case has been discharged. -/
theorem exceptionalOrbifoldPositiveWeightsFact_of_octa_icosa
    (hOcta : StronglyRational (orbifoldVOA octa) → PseudoUnitary (orbifoldVOA octa))
    (hIcosa : ∀ G : Subgroup (Aut (V2m 1 le_rfl)),
      Nonempty (G ≃* alternatingGroup (Fin 5)) →
      StronglyRational (orbifoldVOA G) → PseudoUnitary (orbifoldVOA G)) :
    ExceptionalOrbifoldPositiveWeightsFact := by
  intro G hG hSR
  rcases hG with hG | hG | hG
  · exact tetrahedral_orbifold_pseudoUnitary G hG
  · obtain ⟨e, he, hω⟩ := octahedralStandardForm_of_conjugacy
      OrbC2d.octahedralConjugacy G hG
    have hs := isVOAHom_symm' e he
    have hωs := symm_conformal e hω
    exact pseudoUnitary_of_iso e he hω
      (hOcta (stronglyRational_of_iso e.symm hs hωs hSR))
  · exact hIcosa G hG hSR

/-- The new two-group reduction is lossless. -/
theorem exceptionalOrbifoldPositiveWeightsFact_iff_octa_icosa :
    ExceptionalOrbifoldPositiveWeightsFact ↔
      (StronglyRational (orbifoldVOA octa) → PseudoUnitary (orbifoldVOA octa)) ∧
      (∀ G : Subgroup (Aut (V2m 1 le_rfl)),
        Nonempty (G ≃* alternatingGroup (Fin 5)) →
        StronglyRational (orbifoldVOA G) → PseudoUnitary (orbifoldVOA G)) := by
  refine ⟨fun h => ⟨h octa (Or.inr (Or.inl octa_group)),
    fun G hG => h G (Or.inr (Or.inr hG))⟩, ?_⟩
  rintro ⟨hO, hI⟩
  exact exceptionalOrbifoldPositiveWeightsFact_of_octa_icosa hO hI

end VOA.Classification.COne.OrbB5
