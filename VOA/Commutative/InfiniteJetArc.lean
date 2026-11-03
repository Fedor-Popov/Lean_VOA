/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VOA.Commutative.InfiniteJet
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The arc universal property of the infinite jet presentation

For every commutative `R`-algebra `A`, algebra maps from the presented infinite jet algebra
to `A` correspond to algebra maps from the original presented algebra to `A[[t]]`.
The power series are arbitrary: no derivation, characteristic-zero assumption, or choice of
factorial normalization is needed. This is the Hasse--Schmidt universal property of arcs.
-/

namespace VOA.InfiniteJet

open scoped BigOperators

noncomputable section

universe uR uσ uA
variable {R : Type uR} {σ : Type uσ} {A : Type uA}
  [CommRing R] [CommRing A] [Algebra R A]

/-- Evaluate a jet coordinate at a coefficient of a chosen generator power series. -/
def seriesJetEval (x : σ → PowerSeries A) : JetPoly R σ →ₐ[R] A :=
  MvPolynomial.aeval fun v => PowerSeries.coeff v.2 (x v.1)

@[simp] theorem seriesJetEval_X (x : σ → PowerSeries A) (i : σ) (n : ℕ) :
    seriesJetEval (R := R) x (MvPolynomial.X (i, n)) = PowerSeries.coeff n (x i) := by
  simp [seriesJetEval]

/-- Finite relation coefficients evaluate to coefficients of substitution in arbitrary series. -/
theorem seriesJetEval_ofFinite_relationCoeff (x : σ → PowerSeries A)
    (m n : ℕ) (hn : n ≤ m) (f : MvPolynomial σ R) :
    seriesJetEval x (ofFinite (R := R) m (FiniteJet.relationCoeff m n f)) =
      PowerSeries.coeff n (MvPolynomial.aeval x f) := by
  induction f using MvPolynomial.induction_on generalizing n with
  | C r =>
      cases n with
      | zero => simp [ofFinite, seriesJetEval, PowerSeries.algebraMap_apply]
      | succ n => simp [ofFinite, seriesJetEval, PowerSeries.algebraMap_apply]
  | add f g hf hg =>
      simp only [FiniteJet.relationCoeff_add, map_add, hf n hn, hg n hn]
  | mul_X f i hf =>
      rw [FiniteJet.relationCoeff_mul, map_sum, map_sum, map_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro ab hab
      have hab' := Finset.mem_antidiagonal.mp hab
      rw [map_mul, map_mul, hf ab.1 (by omega), FiniteJet.relationCoeff_X,
        FiniteJet.jetVariable_of_le m i ab.2 (by omega), ofFinite_X, seriesJetEval_X]
      simp

/-- Vanishing of the base relations as series implies vanishing of all infinite jet relations. -/
theorem seriesJetEval_jetIdeal_le_ker (x : σ → PowerSeries A)
    (I : Ideal (MvPolynomial σ R))
    (hI : ∀ f ∈ I, MvPolynomial.aeval x f = 0) :
    jetIdeal I ≤ RingHom.ker (seriesJetEval (R := R) x).toRingHom := by
  rw [jetIdeal, Ideal.span_le]
  rintro f ⟨m, g, hg, rfl⟩
  have hfinite : FiniteJet.jetIdeal m I ≤
      RingHom.ker ((seriesJetEval (R := R) x).comp (ofFinite m)).toRingHom := by
    rw [FiniteJet.jetIdeal, Ideal.span_le]
    rintro _ ⟨fj, rfl⟩
    change seriesJetEval x (ofFinite m (FiniteJet.jetCoeff m fj.2 fj.1.1)) = 0
    rw [FiniteJet.jetCoeff_apply, seriesJetEval_ofFinite_relationCoeff x m fj.2
      (Nat.le_of_lt_succ fj.2.isLt), hI fj.1.1 fj.1.2, map_zero]
  exact hfinite hg

/-- The generator series associated with a point of the presented infinite jet algebra. -/
def pointSeries (I : Ideal (MvPolynomial σ R)) (f : PresentedJet I →ₐ[R] A)
    (i : σ) : PowerSeries A :=
  PowerSeries.mk fun n => f (presentedJetMk I (MvPolynomial.X (i, n)))

@[simp] theorem coeff_pointSeries (I : Ideal (MvPolynomial σ R))
    (f : PresentedJet I →ₐ[R] A) (i : σ) (n : ℕ) :
    PowerSeries.coeff n (pointSeries I f i) =
      f (presentedJetMk I (MvPolynomial.X (i, n))) := by
  simp [pointSeries]

theorem seriesJetEval_pointSeries (I : Ideal (MvPolynomial σ R))
    (f : PresentedJet I →ₐ[R] A) :
    seriesJetEval (pointSeries I f) = f.comp (presentedJetMk I) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨i, n⟩
  simp

/-- Generator series attached to any jet point satisfy the original relations. -/
theorem pointSeries_relations (I : Ideal (MvPolynomial σ R))
    (f : PresentedJet I →ₐ[R] A) (g : MvPolynomial σ R) (hg : g ∈ I) :
    MvPolynomial.aeval (pointSeries I f) g = 0 := by
  apply PowerSeries.ext
  intro n
  rw [← seriesJetEval_ofFinite_relationCoeff (pointSeries I f) n n le_rfl g,
    seriesJetEval_pointSeries, AlgHom.comp_apply, map_zero]
  have hmem : ofFinite n (FiniteJet.relationCoeff n n g) ∈ jetIdeal I :=
    ofFinite_mem_jetIdeal n I _ (FiniteJet.relationCoeff_mem_jetIdeal n n I g hg le_rfl)
  have hz : presentedJetMk I (ofFinite n (FiniteJet.relationCoeff n n g)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [hz, map_zero]

/-- A point of the infinite jet presentation gives an arc of the base algebra. -/
def toArc (I : Ideal (MvPolynomial σ R)) (f : PresentedJet I →ₐ[R] A) :
    (MvPolynomial σ R ⧸ I) →ₐ[R] PowerSeries A :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval (pointSeries I f))
    (pointSeries_relations I f)

@[simp] theorem toArc_mk_X (I : Ideal (MvPolynomial σ R))
    (f : PresentedJet I →ₐ[R] A) (i : σ) :
    toArc I f (Ideal.Quotient.mkₐ R I (MvPolynomial.X i)) = pointSeries I f i := by
  simp [toArc]

/-- Generator series supplied by an arc satisfy the base relations. -/
theorem arcGenerator_relations (I : Ideal (MvPolynomial σ R))
    (u : (MvPolynomial σ R ⧸ I) →ₐ[R] PowerSeries A)
    (g : MvPolynomial σ R) (hg : g ∈ I) :
    MvPolynomial.aeval (fun i => u (Ideal.Quotient.mkₐ R I (MvPolynomial.X i))) g = 0 := by
  have he : MvPolynomial.aeval (fun i => u (Ideal.Quotient.mkₐ R I (MvPolynomial.X i))) =
      u.comp (Ideal.Quotient.mkₐ R I) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  rw [he, AlgHom.comp_apply]
  have hz : Ideal.Quotient.mkₐ R I g = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hg
  rw [hz, map_zero]

/-- An arbitrary arc determines a point of the infinite jet algebra by its coefficients. -/
def ofArc (I : Ideal (MvPolynomial σ R))
    (u : (MvPolynomial σ R ⧸ I) →ₐ[R] PowerSeries A) : PresentedJet I →ₐ[R] A :=
  Ideal.Quotient.liftₐ (jetIdeal I)
    (seriesJetEval (fun i => u (Ideal.Quotient.mkₐ R I (MvPolynomial.X i))))
    (fun _ hg => RingHom.mem_ker.mp
      (seriesJetEval_jetIdeal_le_ker _ I (arcGenerator_relations I u) hg))

@[simp] theorem ofArc_mk_X (I : Ideal (MvPolynomial σ R))
    (u : (MvPolynomial σ R ⧸ I) →ₐ[R] PowerSeries A) (i : σ) (n : ℕ) :
    ofArc I u (presentedJetMk I (MvPolynomial.X (i, n))) =
      PowerSeries.coeff n (u (Ideal.Quotient.mkₐ R I (MvPolynomial.X i))) := by
  simp [ofArc, presentedJetMk, seriesJetEval]

@[simp] theorem ofArc_toArc (I : Ideal (MvPolynomial σ R))
    (f : PresentedJet I →ₐ[R] A) : ofArc I (toArc I f) = f := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i, n⟩
  change ofArc I (toArc I f) (presentedJetMk I (MvPolynomial.X (i, n))) =
    f (presentedJetMk I (MvPolynomial.X (i, n)))
  rw [ofArc_mk_X, toArc_mk_X, coeff_pointSeries]

@[simp] theorem toArc_ofArc (I : Ideal (MvPolynomial σ R))
    (u : (MvPolynomial σ R ⧸ I) →ₐ[R] PowerSeries A) : toArc I (ofArc I u) = u := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change toArc I (ofArc I u) (Ideal.Quotient.mkₐ R I (MvPolynomial.X i)) = _
  rw [toArc_mk_X]
  apply PowerSeries.ext
  intro n
  simp

/-- The arc/Hasse--Schmidt universal property of the infinite jet presentation. -/
def arcEquiv (I : Ideal (MvPolynomial σ R)) :
    (PresentedJet I →ₐ[R] A) ≃ ((MvPolynomial σ R ⧸ I) →ₐ[R] PowerSeries A) where
  toFun := toArc I
  invFun := ofArc I
  left_inv := ofArc_toArc I
  right_inv := toArc_ofArc I

/-- The universal arc of the base presented algebra with values in its infinite jet algebra. -/
def universalArc (I : Ideal (MvPolynomial σ R)) :
    (MvPolynomial σ R ⧸ I) →ₐ[R] PowerSeries (PresentedJet I) :=
  toArc I (AlgHom.id R (PresentedJet I))

/-- Every arc obtained from a jet point is coefficientwise base change of the universal arc. -/
theorem toArc_eq_map_universalArc (I : Ideal (MvPolynomial σ R))
    (f : PresentedJet I →ₐ[R] A) :
    toArc I f = (PowerSeries.mapAlgHom f).comp (universalArc I) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change toArc I f (Ideal.Quotient.mkₐ R I (MvPolynomial.X i)) =
    PowerSeries.mapAlgHom f (toArc I (AlgHom.id R (PresentedJet I))
      (Ideal.Quotient.mkₐ R I (MvPolynomial.X i)))
  rw [toArc_mk_X, toArc_mk_X]
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.mapAlgHom_apply]

/-- The presented infinite jet algebra represents arcs: every arc is uniquely induced by
an algebra map from it, applied coefficientwise to the universal arc. -/
theorem existsUnique_arcLift (I : Ideal (MvPolynomial σ R))
    (u : (MvPolynomial σ R ⧸ I) →ₐ[R] PowerSeries A) :
    ∃! f : PresentedJet I →ₐ[R] A,
      (PowerSeries.mapAlgHom f).comp (universalArc I) = u := by
  refine ⟨ofArc I u, ?_, ?_⟩
  · change (PowerSeries.mapAlgHom (ofArc I u)).comp (universalArc I) = u
    rw [← toArc_eq_map_universalArc, toArc_ofArc]
  · intro f hf
    apply (arcEquiv I).injective
    change toArc I f = toArc I (ofArc I u)
    rw [toArc_ofArc, toArc_eq_map_universalArc, hf]

/-- The arc correspondence is natural in the target coefficient algebra. -/
theorem toArc_natural {C : Type*} [CommRing C] [Algebra R C]
    (I : Ideal (MvPolynomial σ R)) (f : PresentedJet I →ₐ[R] A) (g : A →ₐ[R] C) :
    toArc I (g.comp f) = (PowerSeries.mapAlgHom g).comp (toArc I f) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change toArc I (g.comp f) (Ideal.Quotient.mkₐ R I (MvPolynomial.X i)) =
    PowerSeries.mapAlgHom g (toArc I f (Ideal.Quotient.mkₐ R I (MvPolynomial.X i)))
  rw [toArc_mk_X, toArc_mk_X]
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.mapAlgHom_apply]

/-- A homomorphism of base presented algebras induces a homomorphism of their arc algebras. -/
def arcMap {τ : Type*} (I : Ideal (MvPolynomial σ R)) (J : Ideal (MvPolynomial τ R))
    (f : (MvPolynomial σ R ⧸ I) →ₐ[R] (MvPolynomial τ R ⧸ J)) :
    PresentedJet I →ₐ[R] PresentedJet J :=
  ofArc I ((universalArc J).comp f)

theorem arcMap_universal {τ : Type*}
    (I : Ideal (MvPolynomial σ R)) (J : Ideal (MvPolynomial τ R))
    (f : (MvPolynomial σ R ⧸ I) →ₐ[R] (MvPolynomial τ R ⧸ J)) :
    (PowerSeries.mapAlgHom (arcMap I J f)).comp (universalArc I) =
      (universalArc J).comp f := by
  rw [← toArc_eq_map_universalArc]
  exact toArc_ofArc I _

@[simp] theorem arcMap_id (I : Ideal (MvPolynomial σ R)) :
    arcMap I I (AlgHom.id R (MvPolynomial σ R ⧸ I)) = AlgHom.id R (PresentedJet I) := by
  simp only [arcMap, AlgHom.comp_id, universalArc, ofArc_toArc]

/-- Functoriality also proves that the represented arc algebra is independent of presentation. -/
theorem arcMap_comp {τ υ : Type*}
    (I : Ideal (MvPolynomial σ R)) (J : Ideal (MvPolynomial τ R))
    (L : Ideal (MvPolynomial υ R))
    (f : (MvPolynomial σ R ⧸ I) →ₐ[R] (MvPolynomial τ R ⧸ J))
    (g : (MvPolynomial τ R ⧸ J) →ₐ[R] (MvPolynomial υ R ⧸ L)) :
    arcMap I L (g.comp f) = (arcMap J L g).comp (arcMap I J f) := by
  apply (arcEquiv I).injective
  change toArc I (arcMap I L (g.comp f)) =
    toArc I ((arcMap J L g).comp (arcMap I J f))
  rw [toArc_natural]
  change toArc I (ofArc I ((universalArc L).comp (g.comp f))) =
    (PowerSeries.mapAlgHom (arcMap J L g)).comp
      (toArc I (ofArc I ((universalArc J).comp f)))
  rw [toArc_ofArc, toArc_ofArc]
  exact (congrArg (fun h => h.comp f) (arcMap_universal J L g)).symm

/-- Isomorphic base algebras have canonically isomorphic presented arc algebras. -/
def arcEquivOfBaseEquiv {τ : Type*}
    (I : Ideal (MvPolynomial σ R)) (J : Ideal (MvPolynomial τ R))
    (e : (MvPolynomial σ R ⧸ I) ≃ₐ[R] (MvPolynomial τ R ⧸ J)) :
    PresentedJet I ≃ₐ[R] PresentedJet J :=
  AlgEquiv.ofAlgHom (arcMap I J e.toAlgHom) (arcMap J I e.symm.toAlgHom)
    (by rw [← arcMap_comp]; simp)
    (by rw [← arcMap_comp]; simp)

@[simp] theorem coeff_universalArc_X (I : Ideal (MvPolynomial σ R)) (i : σ) (n : ℕ) :
    PowerSeries.coeff n (universalArc I (Ideal.Quotient.mkₐ R I (MvPolynomial.X i))) =
      presentedJetMk I (MvPolynomial.X (i, n)) := by
  change PowerSeries.coeff n (toArc I (AlgHom.id R (PresentedJet I))
    (Ideal.Quotient.mkₐ R I (MvPolynomial.X i))) = _
  rw [toArc_mk_X, coeff_pointSeries]
  rfl

/-- Arc algebras preserve surjections of base algebras. Coefficients of a preimage of each
base generator provide preimages of every jet generator. -/
theorem arcMap_surjective {τ : Type*}
    (I : Ideal (MvPolynomial σ R)) (J : Ideal (MvPolynomial τ R))
    (f : (MvPolynomial σ R ⧸ I) →ₐ[R] (MvPolynomial τ R ⧸ J))
    (hf : Function.Surjective f) : Function.Surjective (arcMap I J f) := by
  have hgen : ∀ i : τ × ℕ, ∃ a, arcMap I J f a = presentedJetMk J (MvPolynomial.X i) := by
    rintro ⟨i, n⟩
    obtain ⟨a, ha⟩ := hf (Ideal.Quotient.mkₐ R J (MvPolynomial.X i))
    have h := DFunLike.congr_fun (arcMap_universal I J f) a
    have hc := congrArg (PowerSeries.coeff n) h
    simp only [AlgHom.comp_apply, PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map] at hc
    rw [ha, coeff_universalArc_X] at hc
    exact ⟨PowerSeries.coeff n (universalArc I a), hc⟩
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  change ∃ a, arcMap I J f a = presentedJetMk J p
  induction p using MvPolynomial.induction_on with
  | C r =>
      exact ⟨algebraMap R (PresentedJet I) r, by simp [presentedJetMk]⟩
  | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
  | mul_X p i hp =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hgen i
      exact ⟨a * b, by rw [map_mul, ha, hb, map_mul]⟩

end
end VOA.InfiniteJet
