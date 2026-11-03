import VOA.Classification.COne.OrbRat2Reduction
import VOA.Classification.COne.OrbRatStatement

/-!
# The solvable exceptional cases need only CYCLIC orbifold rationality

`V₂^{A₄} ≅ (V₈⁺)^{ℤ/3}` (proved, `OrbC2b.tetra_cubic_iso`) and `V₂^{S₄} ≅ (V₂^{A₄})^{ℤ/2}`
(proved, `OrbC2b.octa_involution_iso`), and `V₈⁺` is strongly rational (proved,
`OrbC2b.klein_stronglyRational`).  Hence

* the tetrahedral model is ONE instance of the order-three cyclic orbifold theorem over the
  strongly rational `V₈⁺` (`cubicModelRationalOfC2_of_cyclic`).  This is exactly the theorem
  Dong–Jiang use (arXiv:1209.1168, §4, proof of Thm 4.6: Miyamoto arXiv:0909.3665 Cor. 7;
  equivalently Miyamoto arXiv:1003.0237 for `ℤ/3`);
* the octahedral model is then ONE instance of the involution orbifold theorem over the
  (strongly rational) tetrahedral model, given the tetrahedral `C₂` input of B2
  (`involutionModelRationalOfC2_of_involution`);
* so the converse of Gannon–Rayhaun needs, for rationality, only `CyclicOrbifoldRationalOfC2.{0}`
  and the isolated icosahedral case (`gannonRayhaunConverse_of_cyclic`).

The cyclic Props are OPEN (stated in `OrbRatStatement`, never axioms).
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbRat2

open VOA VertexOperatorAlgebra OrbC2b

theorem kleinCubic_isOfFinOrder : IsOfFinOrder kleinCubic :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, kleinCubic_cube⟩

theorem tetraInvolution_mul_self : tetraInvolution * tetraInvolution = 1 := by
  rw [← pow_two]; exact tetraInvolution_square

/-- The tetrahedral model from the `ℤ/3` orbifold theorem over `V₈⁺`. -/
theorem cubicModelRationalOfC2_of_cyclic (h : OrbRat.CyclicOrbifoldRationalOfC2.{0}) :
    CubicModelRationalOfC2 :=
  fun hC2 => h _ (orbifoldVOA klein) kleinCubic kleinCubic_isOfFinOrder klein_stronglyRational hC2

/-- The standard tetrahedral orbifold is strongly rational once the model is rational and it is
`C₂`-cofinite. -/
theorem tetra_stronglyRational_of_cubic (hC : CubicModelRationalOfC2)
    (hT : C2Cofinite (orbifoldVOA tetra)) : StronglyRational (orbifoldVOA tetra) := by
  letI : Finite tetra := Finite.of_equiv (alternatingGroup (Fin 4)) tetra_group.some.symm.toEquiv
  refine ⟨⟨exceptionalOrbifold_isSimple tetra, exceptionalOrbifold_selfDual tetra, hT⟩, ?_⟩
  exact (admissiblyRational_iff_of_iso tetra_cubic_iso).mp
    (hC ((c2Cofinite_iff_of_iso tetra_cubic_iso).mpr hT))

/-- The octahedral model from the involution orbifold theorem over the tetrahedral model. -/
theorem involutionModelRationalOfC2_of_involution
    (h : OrbRat.InvolutionOrbifoldRationalOfC2.{0}) (hC : CubicModelRationalOfC2)
    (hT : C2Cofinite (orbifoldVOA tetra)) : InvolutionModelRationalOfC2 :=
  fun hC2 => h _ (orbifoldVOA tetra) tetraInvolution tetraInvolution_mul_self
    (tetra_stronglyRational_of_cubic hC hT) hC2

/-- The converse of Gannon–Rayhaun with B3 replaced by the cyclic orbifold theorem and the
isolated icosahedral case (B2, B4, B5 unchanged). -/
theorem gannonRayhaunConverse_of_cyclic (hSolv : SolvableExceptionalOrbifoldC2Fact)
    (hXu : XuIcosahedralPoissonRelations) (hCyc : OrbRat.CyclicOrbifoldRationalOfC2.{0})
    (hIco : IcosahedralV2OrbifoldRationalOfC2)
    (hPU : ExceptionalOrbifoldPositiveWeightsFact) : GannonRayhaunConverse.{0} := by
  have hC := cubicModelRationalOfC2_of_cyclic hCyc
  have hT : C2Cofinite (orbifoldVOA tetra) := hSolv tetra (Or.inl tetra_group)
  exact gannonRayhaunConverse_of_models hSolv hXu hC
    (involutionModelRationalOfC2_of_involution (OrbRat.cyclic_involution hCyc) hC hT) hIco hPU

end VOA.Classification.COne.OrbRat2
