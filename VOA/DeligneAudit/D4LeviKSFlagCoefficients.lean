import VOA.DeligneAudit.D4LeviKSRelativeSeries
import VOA.DeligneAudit.D4LeviKSFlagZStep

/-! Homogeneous coefficient spaces for the relative flag reductions. -/

namespace VOA.DeligneAudit.D4Levi

open MvPolynomial

variable {A : Type*} [CommRing A] [Algebra ℂ A]

noncomputable def ksBlockCoefficient (n d : ℕ)
    (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) : Submodule ℂ A :=
  ((symmetricSubalgebra (Fin n) ℂ).toSubmodule ⊓
    homogeneousSubmodule (Fin n) ℂ d).map φ.toLinearMap

theorem ksBlockCoefficient_mul (n e f : ℕ)
    (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) (U W : A)
    (hU : U ∈ ksBlockCoefficient n e φ) (hW : W ∈ ksBlockCoefficient n f φ) :
    U * W ∈ ksBlockCoefficient n (e + f) φ := by
  obtain ⟨P, ⟨hP, hdP⟩, rfl⟩ := hU
  obtain ⟨Q, ⟨hQ, hdQ⟩, rfl⟩ := hW
  exact ⟨P * Q, ⟨(symmetricSubalgebra (Fin n) ℂ).mul_mem hP hQ, hdP.mul hdQ⟩,
    map_mul φ P Q⟩

theorem ksBlockCoefficient_hsymm (n d : ℕ)
    (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) :
    φ (hsymm (Fin n) ℂ d) ∈ ksBlockCoefficient n d φ :=
  ⟨_, ⟨hsymm_isSymmetric _ _ _, ksHsymm_homogeneous n d⟩, rfl⟩

theorem ksBlockCoefficient_one (n : ℕ)
    (φ : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) :
    1 ∈ ksBlockCoefficient n 0 φ :=
  ⟨1, ⟨(symmetricSubalgebra (Fin n) ℂ).one_mem, isHomogeneous_one _ _⟩, map_one φ⟩

noncomputable def ksTargetXMap (a b c : ℕ) :
    MvPolynomial (Fin a) ℂ →ₐ[ℂ] MvPolynomial (PairTarget a b c) ℂ :=
  rename Sum.inl

noncomputable def ksTargetYMap (a b c : ℕ) :
    MvPolynomial (Fin b) ℂ →ₐ[ℂ] MvPolynomial (PairTarget a b c) ℂ :=
  rename (fun y => Sum.inr (Sum.inl y))

noncomputable def ksTargetZMap (a b c : ℕ) :
    MvPolynomial (Fin c) ℂ →ₐ[ℂ] MvPolynomial (PairTarget a b c) ℂ :=
  rename (fun z => Sum.inr (Sum.inr z))

theorem ksTargetXMap_symmetric (a b c : ℕ) (P : MvPolynomial (Fin a) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin a) ℂ) :
    ksTargetXMap a b c P ∈ pairTargetSymmetric a b c :=
  pairTarget_symmetric_X_mem a b c P hP

theorem ksTargetYMap_symmetric (a b c : ℕ) (P : MvPolynomial (Fin b) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin b) ℂ) :
    ksTargetYMap a b c P ∈ pairTargetSymmetric a b c :=
  pairTarget_symmetric_Y_mem a b c P hP

theorem ksTargetZMap_symmetric (a b c : ℕ) (P : MvPolynomial (Fin c) ℂ)
    (hP : P ∈ symmetricSubalgebra (Fin c) ℂ) :
    ksTargetZMap a b c P ∈ pairTargetSymmetric a b c :=
  pairTarget_symmetric_Z_mem a b c P hP

noncomputable def ksFlagZCoefficient (a b c d : ℕ) :
    Submodule ℂ (MvPolynomial (PairTarget a b c) ℂ) :=
  ksBlockCoefficient c d (ksTargetZMap a b c)

theorem ksFlagZCoefficient_symmetric (a b c d : ℕ)
    (P : MvPolynomial (PairTarget a b c) ℂ) (hP : P ∈ ksFlagZCoefficient a b c d) :
    P ∈ pairTargetSymmetric a b c := by
  obtain ⟨Q, ⟨hQ, _⟩, rfl⟩ := hP
  exact ksTargetZMap_symmetric a b c Q hQ

noncomputable def ksFlagRelationImage (m a b c d : ℕ) :
    Submodule ℂ (MvPolynomial (PairTarget a b c) ℂ) :=
  (ksFlagMaximalRelationSpan m a b c d).map
    (Subalgebra.val (pairTargetSymmetric a b c)).toLinearMap

/-- Multiplication by a separately symmetric target factor preserves flag relations. -/
theorem ksFlagRelationImage_mul (m a b c d : ℕ)
    (U T : MvPolynomial (PairTarget a b c) ℂ)
    (hU : U ∈ pairTargetSymmetric a b c) (hT : T ∈ ksFlagRelationImage m a b c d) :
    U * T ∈ ksFlagRelationImage m a b c d := by
  obtain ⟨Q, hQ, rfl⟩ := hT
  exact ⟨⟨U, hU⟩ * Q, ksFlagMaximalRelationSpan_mul_mem m a b c d ⟨U, hU⟩ Q hQ, rfl⟩

theorem ksFlagRelationImage_mono (m a b c d e : ℕ) (hde : d ≤ e) :
    ksFlagRelationImage m a b c d ≤ ksFlagRelationImage m a b c e :=
  Submodule.map_mono (ksFlagMaximalRelationSpan_mono_degree m a b c d e hde)

end VOA.DeligneAudit.D4Levi

#print axioms VOA.DeligneAudit.D4Levi.ksBlockCoefficient_mul
#print axioms VOA.DeligneAudit.D4Levi.ksBlockCoefficient_hsymm
#print axioms VOA.DeligneAudit.D4Levi.ksBlockCoefficient_one
#print axioms VOA.DeligneAudit.D4Levi.ksTargetXMap_symmetric
#print axioms VOA.DeligneAudit.D4Levi.ksTargetYMap_symmetric
#print axioms VOA.DeligneAudit.D4Levi.ksTargetZMap_symmetric
#print axioms VOA.DeligneAudit.D4Levi.ksFlagZCoefficient_symmetric
#print axioms VOA.DeligneAudit.D4Levi.ksFlagRelationImage_mul
#print axioms VOA.DeligneAudit.D4Levi.ksFlagRelationImage_mono
