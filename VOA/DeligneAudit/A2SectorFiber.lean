/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2SectorTensor
import VOA.DeligneAudit.A2SectorNakayama
import VOA.Commutative.SymmetricPolynomialTensorCoefficients

/-!
# The current-only carrier over the symmetric polynomials of the current roots

`W_m = currentCarrier Q m 0` is a module over `B_m = ℂ[z₁,…,z_m]^{S_m}` by multiplication (the
current equations are collision conditions, and a symmetric polynomial factors out of every
collision: `projectedDiagonal_mul`).  The graded Nakayama bound (`SectorNakayama`) gives

  `dim (W_m)_a ≤ Σ_{b ≤ a} dim Fib(W_m)_b · p_{≤m}(a - b)`,

where `Fib(W_m) = W_m / B_{m,+} W_m` is the fibre at the origin and `dim (B_m)_n ≤ p_{≤m}(n)`
(a symmetric polynomial is determined by its coefficients at monotone exponents, `Idx`).

In the paper (B5–B8 with U4 = Chari–Fourier–Khandai and U5 = Ravinder/Feigin), `W_m` is free over
`B_m` with fibre of graded character `F_m`; only the fibre bound `dim Fib(W_m)_b ≤ [q^b] F_m` is
needed here.
-/

namespace VOA.DeligneAudit.SectorFiber

open VOA.DeligneAuxiliaryCollision VOA.QuadraticCurrentFunctionalCarrier
open VOA.DeligneAudit.SectorTensor VOA.DeligneAudit.SectorNakayama
open VOA.DeligneAudit.A2 (partitionsLe)
open Module

noncomputable section

variable {K σ ρ : Type*} [Field K] [Fintype σ] (Q : ρ → σ × σ → K) (m : ℕ)

/-- The symmetric polynomials in the current roots. -/
abbrev SymAlg := MvPolynomial.symmetricSubalgebra (Fin (m + 0)) K

/-- Homogeneous symmetric polynomials of degree `n`. -/
def symDeg (n : ℕ) : Submodule K (SymAlg (K := K) m) :=
  (MvPolynomial.homogeneousSubmodule (Fin (m + 0)) K n).comap
    (MvPolynomial.symmetricSubalgebra (Fin (m + 0)) K).val.toLinearMap

/-- The carrier pieces, inside the ambient tensor polynomials. -/
def carrierDeg (a : ℕ) : Submodule K (TensorPolynomial (K := K) (σ := σ) m 0) :=
  (degreePiece (currentCarrier Q m 0) a).map (currentCarrier Q m 0).subtype

instance (n : ℕ) : FiniteDimensional K (symDeg (K := K) m n) := by
  haveI : FiniteDimensional K (MvPolynomial.homogeneousSubmodule (Fin (m + 0)) K n) := by
    have := VOA.MvPolynomialFiniteHomogeneous.finiteDimensional_weightedHomogeneousSubmodule
      (K := K) (I := Fin (m + 0)) (fun _ => 1) (by intros; simp) n
    exact this
  let f : symDeg (K := K) m n →ₗ[K] MvPolynomial.homogeneousSubmodule (Fin (m + 0)) K n :=
    { toFun := fun s => ⟨s.1.1, s.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective f fun s s' h => ?_
  have h' := Subtype.ext_iff.mp h
  exact Subtype.ext (Subtype.ext h')

instance (a : ℕ) : FiniteDimensional K (carrierDeg Q m a) := by
  unfold carrierDeg
  infer_instance

theorem finrank_carrierDeg (a : ℕ) :
    finrank K (carrierDeg Q m a) = finrank K (degreePiece (currentCarrier Q m 0) a) :=
  (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).finrank_eq.symm

/-- Multiplication by a symmetric polynomial preserves the current carrier. -/
theorem mul_mem_currentCarrier (f : MvPolynomial (Fin (m + 0)) K) (hf : f.IsSymmetric)
    {p : TensorPolynomial (K := K) (σ := σ) m 0} (hp : p ∈ currentCarrier Q m 0) :
    (fun t => f * p t) ∈ currentCarrier Q m 0 := by
  refine ⟨fun e g he t => ?_, fun r ij t => ?_⟩
  · rw [map_mul, hf e, hp.1 e g he t]
  · have h := hp.2 r ij t
    unfold currentReadback at h ⊢
    rw [projectedDiagonal_mul, h, mul_zero]

/-- The graded action of the symmetric polynomials on the carrier. -/
theorem gradedAction : GradedAction (symDeg (K := K) m) (carrierDeg Q m) where
  one_mem := by
    change (1 : MvPolynomial (Fin (m + 0)) K) ∈ MvPolynomial.homogeneousSubmodule _ K 0
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_one _ _
  mul_mem := by
    intro n k r r' hr hr'
    have h1 : r.1.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hr
    have h2 : r'.1.IsHomogeneous k := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hr'
    change (r.1 * r'.1) ∈ MvPolynomial.homogeneousSubmodule _ K (n + k)
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact h1.mul h2
  smul_mem := by
    intro n a r x hr hx
    obtain ⟨p, hp, rfl⟩ := hx
    have hr' : r.1.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule _ _).mp hr
    refine ⟨⟨fun t => r.1 * p.1 t, mul_mem_currentCarrier Q m r.1 r.2 p.2⟩, fun t => ?_, rfl⟩
    exact hr'.mul (hp t)

/-- **Dimension of homogeneous symmetric polynomials** is at most `p_{≤m}(n)`. -/
theorem finrank_symDeg_le (n : ℕ) : finrank K (symDeg (K := K) m n) ≤ partitionsLe m n := by
  classical
  let f : symDeg (K := K) m n →ₗ[K] (Idx m n → K) :=
    { toFun := fun s i => MvPolynomial.coeff (expOf i) s.1.1
      map_add' := fun _ _ => by funext i; simp
      map_smul' := fun _ _ => by funext i; simp }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    have hhom : s.1.1.IsHomogeneous n := (MvPolynomial.mem_homogeneousSubmodule _ _).mp s.2
    have hsym := (VOA.SymmetricPolynomialTensorCoefficients.isSymmetric_iff_coefficients
      s.1.1).mp s.1.2
    apply Subtype.ext; apply Subtype.ext
    apply MvPolynomial.ext
    intro β
    simp only [ZeroMemClass.coe_zero, MvPolynomial.coeff_zero]
    by_cases hw : Finsupp.weight (fun _ => (1 : ℕ)) β = n
    · let srt := Tuple.sort (⇑β)
      have hmono : Monotone (⇑β ∘ srt) := Tuple.monotone_sort _
      have hsum : ∑ k, (⇑β ∘ srt) k = n := by
        rw [← hw, weight_one_eq_sum]
        exact Equiv.sum_comp srt (⇑β)
      obtain ⟨i, hi⟩ := exists_toExp m _ hmono n hsum
      have hβ : β = (expOf i).mapDomain srt := by
        ext k
        rw [Finsupp.mapDomain_equiv_apply, expOf, Finsupp.coe_equivFunOnFinite_symm, hi]
        simp
      rw [hβ, hsym srt (expOf i)]
      exact congrFun hs i
    · refine hhom.coeff_eq_zero ?_
      rw [Finsupp.degree_eq_weight_one]
      exact hw
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, card_idx] at this
  exact this

/-- **Graded Nakayama for the current-only carrier.** -/
theorem finrank_current_le_fiber (a : ℕ) :
    finrank K (degreePiece (currentCarrier Q m 0) a) ≤
      ∑ b ∈ Finset.range (a + 1), fiberDim (symDeg (K := K) m) (carrierDeg Q m) b *
        partitionsLe m (a - b) := by
  rw [← finrank_carrierDeg]
  refine (finrank_le_sum_fiberDim (gradedAction Q m) a).trans ?_
  exact Finset.sum_le_sum fun b _ => Nat.mul_le_mul_left _ (finrank_symDeg_le m _)

end

end VOA.DeligneAudit.SectorFiber

section AxiomAudit
#print axioms VOA.DeligneAudit.SectorFiber.finrank_symDeg_le
#print axioms VOA.DeligneAudit.SectorFiber.finrank_current_le_fiber
end AxiomAudit
