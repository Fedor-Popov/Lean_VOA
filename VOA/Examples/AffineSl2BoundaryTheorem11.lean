import VOA.Examples.AffineSl2BoundaryMainTheorems

/-!
# Arakawa--Dai Theorem 1.1 in the paper's form

T. Arakawa, X. Dai, *Classical freeness of affine vertex algebras of sl₂ at boundary admissible
levels*, arXiv:2609.33348, Theorem 1.1: for every integer `m ≥ 1`, with
`V = L_k(sl₂)`, `k = -2 + 2/(2m+1)`, the canonical map `J∞ R_V → gr^F V` is an isomorphism of
(conformally graded) Poisson vertex algebras; moreover `R_V ≅ ℂ[e,h,f]/(e Q^m, h Q^m, f Q^m)`,
`Q = h² + 4ef`.

This file assembles the main results of `AffineSl2BoundaryMainTheorems` into one statement
about `R_V` itself, removing the need to read the presented and the intrinsic statements side by
side.  Nothing is re-proved: every mathematical input is an existing theorem.

What the Lean objects are.

* `R_V` is `A₂ (vacuum m) = V ⧸ C₂(V)`, Zhu's C₂ algebra of the actual simple quotient.
* `canonicalC2Map m hm : ℂ[e,h,f]/(X·Q^m) →ₐ R_V` is the map `X_i ↦ [x_{-1}𝟙]`
  (`canonicalC2Map_mk_e/h/f`); it is the underlying map of `baseC2AlgEquiv`
  (`baseC2AlgEquiv_apply`), so the presentation isomorphism is canonical *as a theorem*.
* `J∞ R_V` is *constructed* as the presented arc algebra `PresentedJet (baseIdeal m)` together with
  the arc `c2UniversalArc m hm : R_V → (J∞ R_V)[[t]]`, transported through `baseC2AlgEquiv`.
  `c2UniversalArc_universal` proves that this pair has the universal property of the arc algebra
  of `R_V` (every arc `R_V → A[[t]]` is uniquely the base change of the universal arc), so it is
  the arc algebra of `R_V` up to unique isomorphism.  There is no separately constructed functor
  `J∞` on abstract commutative algebras in the library.
* `c2ToArc m hm : R_V → J∞ R_V` is the zero-jet embedding, the constant coefficient of the
  universal arc (`c2ToArc_eq_constantCoeff`).
* The canonical map `J∞ R_V → gr^F V` is characterised, as in the paper, as the unique algebra map
  commuting with the translations and restricting on `R_V` to the canonical map
  `c2ToLiAlgebra : R_V → gr^F V` (`[a] ↦` its degree-zero Li symbol).  Theorem 1.1 states that
  `arcPoissonEquiv m hm`, a `PoissonVertexAlgebra.Equiv` (an algebra isomorphism preserving the
  translation and every nonnegative λ-product), has exactly this underlying map, and that it
  preserves the conformal grading in both directions.
-/
namespace VOA.AffineSl2BoundaryClassicalFreeness
open BoundaryAuxiliary AffineSl2BoundarySingularFamily AffineSl2BoundaryCharacter
noncomputable section

/-- The canonical map `ℂ[e,h,f]/(X·Q^m) → R_V`, `X_i ↦ [x_{-1}𝟙]` with `(x_0,x_1,x_2) = (e,h,f)`. -/
def canonicalC2Map (m : ℕ) (hm : 1 ≤ m) :
    (BasePoly ℂ ⧸ baseIdeal (R := ℂ) m) →ₐ[ℂ] A₂ (AffineSl2BoundaryCharacter.vacuum m) :=
  baseC2Map (BoundaryArcLiMap.simpleVOA (uniformCandidate m hm)) (fun _ => 1)
    (fun i => ⟨BoundaryArcLiMap.gen (uniformCandidate m hm) i,
      BoundaryArcLiMap.gen_mem (uniformCandidate m hm) i⟩)
    (baseIdeal m) (uniformCandidate m hm).baseC2Relations

/-- The presentation isomorphism `baseC2AlgEquiv` is the canonical map. -/
theorem baseC2AlgEquiv_apply (m : ℕ) (hm : 1 ≤ m) (x : BasePoly ℂ ⧸ baseIdeal (R := ℂ) m) :
    baseC2AlgEquiv m hm x = canonicalC2Map m hm x := rfl

/-- On generators the canonical map sends `X_i` to the C₂ class of the `i`-th current state
(paper order `e,h,f`; `symbolToCurrentColor` converts to the library's current colours
`e = 0, f = 1, h = 2`). -/
theorem canonicalC2Map_mk_X (m : ℕ) (hm : 1 ≤ m) (i : Fin 3) :
    canonicalC2Map m hm (Ideal.Quotient.mk (baseIdeal (R := ℂ) m) (MvPolynomial.X i)) =
      mk₂ (AffineSl2BoundaryCharacter.vacuum m)
        ((QuotVOA.maxGradedIdeal (AffineVOA.affineSl2VOA_closed (level m)
          (level_noncritical m))).mkQ
          (AffineVOA.J (level m) (AffineSl2UniversalC2PBW.symbolToCurrentColor i) (-1)
            (AffineVOA.vacuumA (level m)))) := by
  change MvPolynomial.aeval _ (MvPolynomial.X i) = _
  rw [MvPolynomial.aeval_X]
  rfl

/-- The same generator formula, stated with the packaged current `BoundaryArcLiMap.gen`. -/
theorem canonicalC2Map_mk_X_gen (m : ℕ) (hm : 1 ≤ m) (i : Fin 3) :
    canonicalC2Map m hm (Ideal.Quotient.mk (baseIdeal (R := ℂ) m) (MvPolynomial.X i)) =
      mk₂ (AffineSl2BoundaryCharacter.vacuum m)
        (BoundaryArcLiMap.gen (uniformCandidate m hm) i) := by
  change MvPolynomial.aeval _ (MvPolynomial.X i) = _
  rw [MvPolynomial.aeval_X]

/-- `e ↦ [e_{-1}𝟙]`. -/
theorem baseC2AlgEquiv_mk_e (m : ℕ) (hm : 1 ≤ m) :
    baseC2AlgEquiv m hm (Ideal.Quotient.mk (baseIdeal (R := ℂ) m) (MvPolynomial.X 0)) =
      mk₂ (AffineSl2BoundaryCharacter.vacuum m)
        ((QuotVOA.maxGradedIdeal (AffineVOA.affineSl2VOA_closed (level m)
          (level_noncritical m))).mkQ
          (AffineVOA.J (level m) 0 (-1) (AffineVOA.vacuumA (level m)))) := by
  rw [baseC2AlgEquiv_apply, canonicalC2Map_mk_X]
  rfl

/-- `h ↦ [h_{-1}𝟙]` (library current colour `2`). -/
theorem baseC2AlgEquiv_mk_h (m : ℕ) (hm : 1 ≤ m) :
    baseC2AlgEquiv m hm (Ideal.Quotient.mk (baseIdeal (R := ℂ) m) (MvPolynomial.X 1)) =
      mk₂ (AffineSl2BoundaryCharacter.vacuum m)
        ((QuotVOA.maxGradedIdeal (AffineVOA.affineSl2VOA_closed (level m)
          (level_noncritical m))).mkQ
          (AffineVOA.J (level m) 2 (-1) (AffineVOA.vacuumA (level m)))) := by
  rw [baseC2AlgEquiv_apply, canonicalC2Map_mk_X]
  rfl

/-- `f ↦ [f_{-1}𝟙]` (library current colour `1`). -/
theorem baseC2AlgEquiv_mk_f (m : ℕ) (hm : 1 ≤ m) :
    baseC2AlgEquiv m hm (Ideal.Quotient.mk (baseIdeal (R := ℂ) m) (MvPolynomial.X 2)) =
      mk₂ (AffineSl2BoundaryCharacter.vacuum m)
        ((QuotVOA.maxGradedIdeal (AffineVOA.affineSl2VOA_closed (level m)
          (level_noncritical m))).mkQ
          (AffineVOA.J (level m) 1 (-1) (AffineVOA.vacuumA (level m)))) := by
  rw [baseC2AlgEquiv_apply, canonicalC2Map_mk_X]
  rfl

/-- The canonical map `ℂ[e,h,f]/(X·Q^m) → R_V` is bijective. -/
theorem canonicalC2Map_bijective (m : ℕ) (hm : 1 ≤ m) :
    Function.Bijective (canonicalC2Map m hm) :=
  (baseC2AlgEquiv m hm).bijective

/-- The universal arc of `R_V`, valued in `J∞ R_V`, transported from the presentation. -/
def c2UniversalArc (m : ℕ) (hm : 1 ≤ m) :
    A₂ (AffineSl2BoundaryCharacter.vacuum m) →ₐ[ℂ]
      PowerSeries (InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m)) :=
  (InfiniteJet.universalArc (baseIdeal (R := ℂ) m)).comp (baseC2AlgEquiv m hm).symm.toAlgHom

/-- `(J∞ R_V, c2UniversalArc)` represents arcs of `R_V`: every arc `R_V → A[[t]]` is the
coefficientwise base change of the universal arc along a unique algebra map `J∞ R_V → A`. -/
theorem c2UniversalArc_universal (m : ℕ) (hm : 1 ≤ m) {A : Type*} [CommRing A] [Algebra ℂ A]
    (u : A₂ (AffineSl2BoundaryCharacter.vacuum m) →ₐ[ℂ] PowerSeries A) :
    ∃! f : InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m) →ₐ[ℂ] A,
      (PowerSeries.mapAlgHom f).comp (c2UniversalArc m hm) = u := by
  set e := baseC2AlgEquiv m hm
  have key : ∀ f : InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m) →ₐ[ℂ] A,
      (PowerSeries.mapAlgHom f).comp (c2UniversalArc m hm) = u ↔
        (PowerSeries.mapAlgHom f).comp (InfiniteJet.universalArc (baseIdeal (R := ℂ) m)) =
          u.comp e.toAlgHom := by
    intro f
    constructor
    · intro h
      apply AlgHom.ext
      intro x
      have hx := DFunLike.congr_fun h (e x)
      simpa [c2UniversalArc, e] using hx
    · intro h
      apply AlgHom.ext
      intro a
      have ha := DFunLike.congr_fun h (e.symm a)
      simpa [c2UniversalArc, e] using ha
  obtain ⟨f, hf, huniq⟩ :=
    InfiniteJet.existsUnique_arcLift (baseIdeal (R := ℂ) m) (u.comp e.toAlgHom)
  exact ⟨f, (key f).mpr hf, fun g hg => huniq g ((key g).mp hg)⟩

/-- The zero-jet embedding `R_V → J∞ R_V`. -/
def c2ToArc (m : ℕ) (hm : 1 ≤ m) :
    A₂ (AffineSl2BoundaryCharacter.vacuum m) →ₐ[ℂ]
      InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m) :=
  (InfiniteJet.baseToJet (baseIdeal (R := ℂ) m)).comp (baseC2AlgEquiv m hm).symm.toAlgHom

/-- The zero-jet embedding is the constant coefficient of the universal arc. -/
theorem c2ToArc_eq_constantCoeff (m : ℕ) (hm : 1 ≤ m)
    (a : A₂ (AffineSl2BoundaryCharacter.vacuum m)) :
    c2ToArc m hm a = PowerSeries.constantCoeff (c2UniversalArc m hm a) := rfl

/-- Two algebra maps out of a presented arc algebra that intertwine its translation with a fixed
operator and agree on the order-zero generators are equal. -/
theorem presentedJet_algHom_ext {σ B : Type*} [CommRing B] [Algebra ℂ B]
    (I : Ideal (MvPolynomial σ ℂ)) (D : B → B)
    (F G : InfiniteJet.PresentedJet I →ₐ[ℂ] B)
    (hF : ∀ x, F (InfiniteJet.translation I x) = D (F x))
    (hG : ∀ x, G (InfiniteJet.translation I x) = D (G x))
    (h0 : ∀ i, F (InfiniteJet.generator I i 0) = G (InfiniteJet.generator I i 0)) : F = G := by
  have hgen : ∀ i n, F (InfiniteJet.generator I i n) = G (InfiniteJet.generator I i n) := by
    intro i n
    induction n with
    | zero => exact h0 i
    | succ n ih => rw [InfiniteJet.generator_succ, map_smul, map_smul, hF, hG, ih]
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro v
  exact hgen v.1 v.2

/-- The arc isomorphism restricts on `R_V ⊂ J∞ R_V` to the canonical map `R_V → gr^F V`. -/
theorem arcPoissonEquiv_c2ToArc (m : ℕ) (hm : 1 ≤ m)
    (a : A₂ (AffineSl2BoundaryCharacter.vacuum m)) :
    (arcPoissonEquiv m hm).toAlgEquiv (c2ToArc m hm a) =
      c2ToLiAlgebra (AffineSl2BoundaryCharacter.vacuum m) a := by
  set e := baseC2AlgEquiv m hm
  obtain ⟨b, rfl⟩ := e.surjective a
  have hb : c2ToArc m hm (e b) = InfiniteJet.baseToJet (baseIdeal (R := ℂ) m) b := by
    simp [c2ToArc, e]
  rw [hb]
  have hcomp : ((arcPoissonEquiv m hm).toAlgEquiv.toAlgHom).comp
      (InfiniteJet.baseToJet (baseIdeal (R := ℂ) m)) =
      (c2ToLiAlgebra (AffineSl2BoundaryCharacter.vacuum m)).comp e.toAlgHom := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change (arcPoissonEquiv m hm).toAlgEquiv
        (InfiniteJet.baseToJet (baseIdeal (R := ℂ) m)
          (Ideal.Quotient.mkₐ ℂ (baseIdeal (R := ℂ) m) (MvPolynomial.X i))) =
      c2ToLiAlgebra (AffineSl2BoundaryCharacter.vacuum m)
        (e (Ideal.Quotient.mk (baseIdeal (R := ℂ) m) (MvPolynomial.X i)))
    rw [InfiniteJet.baseToJet_mk_X]
    change (uniformCandidate m hm).arcLiPoissonHom.toAlgHom
        (InfiniteJet.presentedJetMk (baseIdeal m) (MvPolynomial.X (i, 0))) = _
    rw [Candidate.arcLiPoissonHom_mk, baseC2AlgEquiv_apply, canonicalC2Map_mk_X_gen]
    unfold BoundaryArcLiMap.polynomialMap liInfiniteJetPolynomialMap InfiniteJet.derivationJetEval
    rw [MvPolynomial.aeval_X]
    simp only [FiniteJet.dividedIterate, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
      one_smul]
    exact (c2ToLiAlgebra_homogeneous (AffineSl2BoundaryCharacter.vacuum m) 1
      ⟨BoundaryArcLiMap.gen (uniformCandidate m hm) i,
        BoundaryArcLiMap.gen_mem (uniformCandidate m hm) i⟩).symm
  exact DFunLike.congr_fun hcomp b

/-- The arc isomorphism is the *unique* algebra map `J∞ R_V → gr^F V` that commutes with the
translations and restricts on `R_V` to the canonical map `R_V → gr^F V`. -/
theorem eq_arcPoissonEquiv_of_c2ToArc (m : ℕ) (hm : 1 ≤ m)
    (F : InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m) →ₐ[ℂ]
      liAssociatedGraded (AffineSl2BoundaryCharacter.vacuum m))
    (hT : ∀ x, F ((arcPVA m).translation x) =
      (liPoissonVertexAlgebra (AffineSl2BoundaryCharacter.vacuum m)).translation (F x))
    (hR : ∀ a, F (c2ToArc m hm a) = c2ToLiAlgebra (AffineSl2BoundaryCharacter.vacuum m) a) :
    F = (arcPoissonEquiv m hm).toAlgEquiv.toAlgHom := by
  apply presentedJet_algHom_ext (baseIdeal (R := ℂ) m)
    (liPoissonVertexAlgebra (AffineSl2BoundaryCharacter.vacuum m)).translation
  · intro x
    rw [← arcPVA_translation]
    exact hT x
  · intro x
    rw [← arcPVA_translation]
    exact (arcPoissonEquiv m hm).map_translation x
  · intro i
    have hx : InfiniteJet.generator (baseIdeal (R := ℂ) m) i 0 =
        c2ToArc m hm (baseC2AlgEquiv m hm
          (Ideal.Quotient.mk (baseIdeal (R := ℂ) m) (MvPolynomial.X i))) := by
      change _ = InfiniteJet.baseToJet (baseIdeal (R := ℂ) m) ((baseC2AlgEquiv m hm).symm
        (baseC2AlgEquiv m hm (Ideal.Quotient.mk (baseIdeal (R := ℂ) m) (MvPolynomial.X i))))
      rw [AlgEquiv.symm_apply_apply]
      exact (InfiniteJet.baseToJet_mk_X (baseIdeal (R := ℂ) m) i).symm
    change F _ = (arcPoissonEquiv m hm).toAlgEquiv _
    rw [hx, hR, arcPoissonEquiv_c2ToArc]

/-- **Arakawa--Dai, Theorem 1.1** (arXiv:2609.33348), for every `m ≥ 1`, with
`V = vacuum m = L_{-2+2/(2m+1)}(sl₂)` (the quotient of the universal affine VOA by its maximal
proper graded ideal) and `R_V = A₂ V`:

1. the canonical map `ℂ[e,h,f]/(e Q^m, h Q^m, f Q^m) → R_V`, `X_i ↦ [x_{-1}𝟙]`, is bijective, so
   `R_V ≅ ℂ[e,h,f]/(X·Q^m)` canonically (the paper asserts only the surjection; the isomorphism is
   a consequence);
2. `J∞ R_V`, realised as `PresentedJet (baseIdeal m)` with arc `c2UniversalArc m hm`, has the
   universal property of the arc algebra of `R_V`;
3. the map underlying the PVA isomorphism `arcPoissonEquiv m hm : J∞ R_V ≅ gr^F V` restricts on
   `R_V` to the canonical map `c2ToLiAlgebra : R_V → gr^F V`;
4. it is the unique algebra map `J∞ R_V → gr^F V` commuting with translation and extending
   `c2ToLiAlgebra`, i.e. it *is* the canonical map of the paper;
5. it and its inverse preserve the conformal grading.

Thus the canonical map `J∞ R_V → gr^F V` is an isomorphism of conformally graded Poisson vertex
algebras (`PoissonVertexAlgebra.Equiv`: an algebra isomorphism preserving translation and every
nonnegative λ-product).  The only hypothesis is `1 ≤ m`. -/
theorem arakawaDai_theorem_1_1 (m : ℕ) (hm : 1 ≤ m) :
    Function.Bijective (canonicalC2Map m hm) ∧
    (∀ i : Fin 3,
      canonicalC2Map m hm (Ideal.Quotient.mk (baseIdeal (R := ℂ) m) (MvPolynomial.X i)) =
        mk₂ (AffineSl2BoundaryCharacter.vacuum m)
          ((QuotVOA.maxGradedIdeal (AffineVOA.affineSl2VOA_closed (level m)
            (level_noncritical m))).mkQ
            (AffineVOA.J (level m) (AffineSl2UniversalC2PBW.symbolToCurrentColor i) (-1)
              (AffineVOA.vacuumA (level m))))) ∧
    (∀ (A : Type) [CommRing A] [Algebra ℂ A]
        (u : A₂ (AffineSl2BoundaryCharacter.vacuum m) →ₐ[ℂ] PowerSeries A),
      ∃! f : InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m) →ₐ[ℂ] A,
        (PowerSeries.mapAlgHom f).comp (c2UniversalArc m hm) = u) ∧
    (∀ a, (arcPoissonEquiv m hm).toAlgEquiv (c2ToArc m hm a) =
      c2ToLiAlgebra (AffineSl2BoundaryCharacter.vacuum m) a) ∧
    (∀ F : InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m) →ₐ[ℂ]
        liAssociatedGraded (AffineSl2BoundaryCharacter.vacuum m),
      (∀ x, F ((arcPVA m).translation x) =
        (liPoissonVertexAlgebra (AffineSl2BoundaryCharacter.vacuum m)).translation (F x)) →
      (∀ a, F (c2ToArc m hm a) = c2ToLiAlgebra (AffineSl2BoundaryCharacter.vacuum m) a) →
      F = (arcPoissonEquiv m hm).toAlgEquiv.toAlgHom) ∧
    (∀ (N : ℕ) (x : InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m)),
      (arcPoissonEquiv m hm).toAlgEquiv x ∈
        BoundaryArcConformalSqueeze.liConformalPiece (AffineSl2BoundaryCharacter.vacuum m) N ↔
        x ∈ arcConformalPiece m N) :=
  ⟨canonicalC2Map_bijective m hm, canonicalC2Map_mk_X m hm,
    fun _ _ _ u => c2UniversalArc_universal m hm u, arcPoissonEquiv_c2ToArc m hm,
    eq_arcPoissonEquiv_of_c2ToArc m hm, arcPoissonEquiv_conformal_iff m hm⟩

end
end VOA.AffineSl2BoundaryClassicalFreeness
