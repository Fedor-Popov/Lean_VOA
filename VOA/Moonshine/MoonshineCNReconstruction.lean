import VOA.Moonshine.MoonshineCNChargeTranslation

/-!
# Complex-frame lattice construction: Reconstruction

Structural adaptation of `LatticeGenWordFields` using a complex bilinear
frame. The carrier, formal-distribution conventions and finite-support proofs
are preserved. No positive-definiteness hypothesis is introduced.
-/

set_option maxHeartbeats 1600000
set_option linter.style.longLine false

namespace VOA.Moonshine.ConwayNorton

open scoped BigOperators TensorProduct
open Module (End)
open IntegralLattice HeisenbergN LatGen Reconstruction

variable {L : IntegralLattice} (F : ComplexLatticeFrame L)

noncomputable def frameWordFieldWithTruncation (α : L.carrier) :
    List (ℕ × Fin (rank L)) → { f : FormalDist (End ℂ (LatModuleGen L)) // IsField f }
  | [] => ⟨canonicalChargedField F α, canonicalChargedField_isField F α⟩
  | (ia :: rest) =>
      let p := frameWordFieldWithTruncation α rest
      ⟨nprod (frameDerivativeCurrent_isField F ia.2 ia.1) p.2,
        (frameDerivativeCurrent_isField F ia.2 ia.1).nprod p.2⟩


noncomputable def frameWordField (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    FormalDist (End ℂ (LatModuleGen L)) := (frameWordFieldWithTruncation F α l).1


theorem frameWordField_isField (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    IsField (frameWordField F l α) := (frameWordFieldWithTruncation F α l).2

@[simp] theorem frameWordField_nil (α : L.carrier) : frameWordField F [] α = canonicalChargedField F α := rfl


theorem frameWordField_cons (ia : ℕ × Fin (rank L)) (rest : List (ℕ × Fin (rank L))) (α : L.carrier) :
    frameWordField F (ia :: rest) α
      = nprod (frameDerivativeCurrent_isField F ia.2 ia.1) (frameWordField_isField F rest α) := rfl


theorem frameWordField_DCovariant  :
    ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
      Reconstruction.DCovariant (frameTranslation F) (frameWordField F l α)
  | [], α => by rw [frameWordField_nil]; exact frameTranslation_canonicalChargedField_DCovariant F α
  | (ia :: rest), α => by
      rw [frameWordField_cons]
      exact Reconstruction.DCovariant.nprod (frameDerivativeCurrent_isField F ia.2 ia.1)
        (frameWordField_isField F rest α) (frameTranslation_frameDerivativeCurrent_DCovariant F ia.2 ia.1)
        (frameWordField_DCovariant rest α)


noncomputable def frameWordState (L : IntegralLattice) : List (ℕ × Fin (rank L)) → L.carrier → LatModuleGen L
  | [], α => latChargeGen L α
  | (ia :: rest), α =>
      LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 ia.2 ia.1) (frameWordState L rest α)

@[simp] theorem frameWordState_nil (α : L.carrier) : frameWordState L [] α = latChargeGen L α := rfl


theorem frameWordState_cons (L : IntegralLattice) (ia : ℕ × Fin (rank L)) (rest : List (ℕ × Fin (rank L))) (α : L.carrier) :
    frameWordState L (ia :: rest) α
      = LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 ia.2 ia.1)
          (frameWordState L rest α) := rfl


theorem frameWordField_vacuum_neg :
    ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier) {q : ℤ}, q < 0 →
      (frameWordField F l α) q (latVacuumGen L) = 0
  | [], α, q, hq => by rw [frameWordField_nil, canonicalChargedField_vacuum, if_neg (by omega)]
  | (ia :: rest), α, q, hq => by
      rw [frameWordField_cons]
      exact nprod_vacuum_neg_gen (frameDerivativeCurrent_isField F ia.2 ia.1) (frameWordField_isField F rest α)
        (latVacuumGen L) (fun s hs => frameDerivativeCurrent_vacuum_neg F ia.2 ia.1 hs)
        (fun s hs => frameWordField_vacuum_neg rest α hs) hq


theorem frameWordField_vacuum_base :
    ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
      (frameWordField F l α) 0 (latVacuumGen L) = frameWordState L l α
  | [], α => by rw [frameWordField_nil, frameWordState_nil, canonicalChargedField_creation_z0]
  | (ia :: rest), α => by
      rw [frameWordField_cons,
        nprod_vacuum_base_gen (frameDerivativeCurrent_isField F ia.2 ia.1) (frameWordField_isField F rest α)
          (latVacuumGen L) (fun s hs => frameDerivativeCurrent_vacuum_neg F ia.2 ia.1 hs)
          (fun s hs => frameWordField_vacuum_neg F rest α hs),
        frameDerivativeCurrent_zero_op, frameWordField_vacuum_base rest α, frameWordState_cons]


theorem frameWordState_eq (L : IntegralLattice) (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    frameWordState L l α = (wordStateN l) ⊗ₜ[ℂ] eGen L α := by
  induction l with
  | nil => rw [frameWordState_nil, wordStateN_nil, latChargeGen, latStateGen, vacuumN]
  | cons ia rest ih =>
      rw [frameWordState_cons, ih, wordStateN_cons, LinearMap.rTensor_tmul]
      congr 1
      rw [currentN_apply, oscN_neg (rank L) 1 ia.2 (show -((ia.1 : ℤ)) - 1 < 0 by omega),
        show (-(-((ia.1 : ℤ)) - 1) - 1).toNat = ia.1 from by omega, mulXN_apply]


theorem frameWordState_span (L : IntegralLattice) :
    Submodule.span ℂ (Set.range (Function.uncurry (frameWordState L))) = ⊤ := by
  set S := Submodule.span ℂ (Set.range (Function.uncurry (frameWordState L))) with hS
  have hmono : ∀ (a : (ℕ × Fin (rank L)) →₀ ℕ) (α : L.carrier),
      (MvPolynomial.monomial a (1 : ℂ)) ⊗ₜ[ℂ] eGen L α ∈ S := by
    intro a α
    have hword : frameWordState L (HeisenbergN.monoWordN a) α
        = (MvPolynomial.monomial a (1 : ℂ)) ⊗ₜ[ℂ] eGen L α := by
      rw [frameWordState_eq, HeisenbergN.wordStateN_monoWordN]
    rw [← hword]
    exact Submodule.subset_span ⟨(HeisenbergN.monoWordN a, α), rfl⟩
  have hpe : ∀ (p : FockN (rank L)) (α : L.carrier), p ⊗ₜ[ℂ] eGen L α ∈ S := by
    intro p α
    rw [← MvPolynomial.support_sum_monomial_coeff p, TensorProduct.sum_tmul]
    refine Submodule.sum_mem _ (fun a _ => ?_)
    rw [show (MvPolynomial.monomial a (MvPolynomial.coeff a p))
          = (MvPolynomial.coeff a p) • MvPolynomial.monomial a (1 : ℂ) from by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
      ← TensorProduct.smul_tmul' (MvPolynomial.coeff a p) (MvPolynomial.monomial a (1 : ℂ))
        (eGen L α)]
    exact Submodule.smul_mem _ _ (hmono a α)
  rw [hS, eq_top_iff, ← TensorProduct.span_tmul_eq_top ℂ (FockN (rank L)) (L.carrier →₀ ℂ),
    Submodule.span_le]
  rintro _ ⟨p, g, rfl⟩
  rw [SetLike.mem_coe]
  induction g using Finsupp.induction_linear with
  | zero => erw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add g1 g2 h1 h2 =>
      erw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h1 h2
  | single α c =>
      rw [show (Finsupp.single α c : L.carrier →₀ ℂ) = c • eGen L α from by
          rw [eGen, Finsupp.smul_single, smul_eq_mul, mul_one]]
      erw [TensorProduct.tmul_smul]
      exact Submodule.smul_mem _ _ (hpe p α)


theorem frameDerivativeCurrent_local_frameWordField (hEven : L.Even)  (a : Fin (rank L)) (i : ℕ) :
    ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
      Local (frameDerivativeCurrent F a i) (frameWordField F l α)
  | [], α => by rw [frameWordField_nil]; exact frameDerivativeCurrent_local_canonicalChargedField F a i α
  | (jb :: rest), α => by
      rw [frameWordField_cons]
      have hab : Local (frameDerivativeCurrent F jb.2 jb.1) (frameWordField F rest α) :=
        frameDerivativeCurrent_local_frameWordField hEven jb.2 jb.1 rest α
      have hac : Local (frameDerivativeCurrent F jb.2 jb.1) (frameDerivativeCurrent F a i) :=
        frameDerivativeCurrent_local F jb.2 a jb.1 i
      have hbc : Local (frameWordField F rest α) (frameDerivativeCurrent F a i) :=
        (frameDerivativeCurrent_local_frameWordField hEven a i rest α).symm
      exact (dong_neg (frameDerivativeCurrent_isField F jb.2 jb.1) (frameWordField_isField F rest α)
        hab hac hbc).symm


theorem canonicalChargedField_local_frameWordField (hEven : L.Even)  (α : L.carrier) :
    ∀ (l : List (ℕ × Fin (rank L))) (β : L.carrier),
      Local (canonicalChargedField F α) (frameWordField F l β)
  | [], β => by rw [frameWordField_nil]; exact canonicalChargedField_local F hEven α β
  | (jb :: rest), β => by
      rw [frameWordField_cons]
      have hab : Local (frameDerivativeCurrent F jb.2 jb.1) (frameWordField F rest β) :=
        frameDerivativeCurrent_local_frameWordField F hEven jb.2 jb.1 rest β
      have hac : Local (frameDerivativeCurrent F jb.2 jb.1) (canonicalChargedField F α) :=
        frameDerivativeCurrent_local_canonicalChargedField F jb.2 jb.1 α
      have hbc : Local (frameWordField F rest β) (canonicalChargedField F α) :=
        (canonicalChargedField_local_frameWordField hEven α rest β).symm
      exact (dong_neg (frameDerivativeCurrent_isField F jb.2 jb.1) (frameWordField_isField F rest β)
        hab hac hbc).symm


theorem frameWordField_local (hEven : L.Even)  :
    ∀ (l₁ : List (ℕ × Fin (rank L))) (α₁ : L.carrier) (l₂ : List (ℕ × Fin (rank L))) (α₂ : L.carrier),
      Local (frameWordField F l₁ α₁) (frameWordField F l₂ α₂)
  | [], α₁, l₂, α₂ => by rw [frameWordField_nil]; exact canonicalChargedField_local_frameWordField F hEven α₁ l₂ α₂
  | (ia :: rest), α₁, l₂, α₂ => by
      rw [frameWordField_cons]
      have hab : Local (frameDerivativeCurrent F ia.2 ia.1) (frameWordField F rest α₁) :=
        frameDerivativeCurrent_local_frameWordField F hEven ia.2 ia.1 rest α₁
      have hac : Local (frameDerivativeCurrent F ia.2 ia.1) (frameWordField F l₂ α₂) :=
        frameDerivativeCurrent_local_frameWordField F hEven ia.2 ia.1 l₂ α₂
      have hbc : Local (frameWordField F rest α₁) (frameWordField F l₂ α₂) :=
        frameWordField_local hEven rest α₁ l₂ α₂
      exact dong_neg (frameDerivativeCurrent_isField F ia.2 ia.1) (frameWordField_isField F rest α₁) hab hac hbc


theorem frameStateField_exists (hEven : L.Even)  :
    ∃ Yfull : LatModuleGen L →ₗ[ℂ] FormalDist (End ℂ (LatModuleGen L)),
      (∀ (lα : List (ℕ × Fin (rank L)) × L.carrier),
        Yfull (Function.uncurry (frameWordState L) lα)
          = Function.uncurry (fun l α => frameWordField F l α) lα) ∧
      (∀ u : LatModuleGen L, IsField (Yfull u)) ∧
      (∀ u v : LatModuleGen L, Local (Yfull u) (Yfull v)) ∧
      (∀ u : LatModuleGen L, (Yfull u) 0 (latVacuumGen L) = u) ∧
      (∀ u : LatModuleGen L, ∀ q : ℤ, q < 0 → (Yfull u) q (latVacuumGen L) = 0) ∧
      (∀ u : LatModuleGen L, Reconstruction.DCovariant (frameTranslation F) (Yfull u)) :=
  Reconstruction.reconstruct (latVacuumGen L) (Function.uncurry (frameWordState L))
    (Function.uncurry (fun l α => frameWordField F l α)) (frameTranslation F)
    (frameWordState_span L)
    (fun lα => frameWordField_isField F lα.1 lα.2)
    (fun lα₁ lα₂ => frameWordField_local F hEven lα₁.1 lα₁.2 lα₂.1 lα₂.2)
    (fun lα => frameWordField_vacuum_base F lα.1 lα.2)
    (fun lα _q hq => frameWordField_vacuum_neg F lα.1 lα.2 hq)
    (frameTranslation_vacuum F)
    (fun lα => frameWordField_DCovariant F lα.1 lα.2)


end VOA.Moonshine.ConwayNorton
