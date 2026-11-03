/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.CyclicEvalEndpoint

/-!
# The level-one input stated intrinsically: Heisenberg separation of the charge sectors

`FockCoordinates` asks for the lattice (Frenkel–Kac) model of the charge-`r` sectors of `B`.
The cyclic-evaluation bound only uses a weaker, intrinsic consequence: **a single functional
`β` on `B` detects every Heisenberg descendant** — for `b` of `h₀`-charge `2r` and energy `E`,
if `β(F(h_1, h_2, …) b) = 0` for every `F` of weighted degree `E - r²`, then `b = 0`
(`HeisenbergSeparation`). In the lattice model `β` is the coefficient of `e^{rα}`.

* `finrank_le_gapTwoCoefficient_of_dual` — the inverse-system bound for an injective map into
  the dual of the degree-`D` polynomials, vanishing on the Cartan ideal (the dual form of
  `finrank_le_gapTwoCoefficient_of_cyclicEvaluation`; proved outright);
* `finrank_le_of_heisenberg` — a space embedded in the invariant tensors of weight `N` has
  dimension at most `gapTwoCoefficient N r`, from a `CyclicDual` and a `HeisenbergSeparation`;
* `heisenbergSeparation_of_fock` — Fock coordinates imply Heisenberg separation (so the
  intrinsic input is weaker);
* `bCartanCalc` — **proved**: the positive Cartan modes `J^h_{i+1}` of the actual `L_1(sl₂)`
  commute (from the current algebra), giving the polynomial calculus `F ↦ F(h_1, h_2, …)`;
* `LevelOneHeisenbergSeparation` — the intrinsic level-one input, a statement about
  `L_1(sl₂)` and its own Cartan modes only; `levelOneHeisenbergSeparation_of_fock` derives it
  from `LevelOneFockCoordinates`;
* `leeYang_gradedUnitary_of_affine_heisenberg` — **Affine GU ⇒ Lee–Yang GU**,
  `#print axioms`-clean, conditional on `hA` (the hypothesis), `models`, `sep`, `lower`.
-/

namespace VOA.CyclicEval

open MvPolynomial VOA.InvariantSymbol TensorProduct Module
open VOA.GradedUnitaryCohomology VOA.LeeYangTransferAssembly VOA.ConcreteHodge
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

/-! ### The dual form of the inverse-system bound -/

theorem eq_zero_of_isWeightedHomogeneous_neg {F : MvPolynomial ℕ ℂ} {D : ℤ} (hD : D < 0)
    (hF : IsWeightedHomogeneous modeWeightZ F D) : F = 0 := by
  ext α
  rw [coeff_zero]
  by_contra hne
  have := hF hne
  have := weight_modeWeightZ_nonneg α
  omega

theorem finrank_le_gapTwoCoefficient_of_dual_aux {V : Type*} [AddCommGroup V] [Module ℂ V]
    (N E : ℤ) (r D : ℕ) (hE : (D : ℤ) = E) (hDN : ((r * (r + 1) + D : ℕ) : ℤ) = N)
    (Ψ : V →ₗ[ℂ] Module.Dual ℂ (weightedHomogeneousSubmodule ℂ modeWeightZ E))
    (hinj : Function.Injective Ψ)
    (hann : ∀ v (F : weightedHomogeneousSubmodule ℂ modeWeightZ E),
      (F : MvPolynomial ℕ ℂ) ∈ cartanIdeal r → Ψ v F = 0) :
    finrank ℂ V ≤ LeeYangTransferAssembly.gapTwoCoefficient N r := by
  classical
  subst hE
  let H0 := weightedHomogeneousSubmodule ℂ modeWeightZ (D : ℤ)
  let L0 : H0 →ₗ[ℂ] (Sorted r D → ℂ) := (sortedCoeffs r D).comp H0.subtype
  have hΦ : ∀ x, Ψ x ∈ (LinearMap.ker L0).dualAnnihilator := by
    intro x
    rw [Submodule.mem_dualAnnihilator]
    intro F hF
    have hFh : IsWeightedHomogeneous modeWeightZ (F : MvPolynomial ℕ ℂ) (D : ℤ) :=
      (mem_weightedHomogeneousSubmodule _ _ _ _).mp F.2
    have hzero : cartanEval r F = 0 := by
      apply eq_zero_of_sorted_coeff _ (cartanEval_isSymmetric r F)
        (cartanEval_isHomogeneous r D F hFh)
      intro β
      exact congrFun (LinearMap.mem_ker.mp hF) β
    exact hann x F (RingHom.mem_ker.mpr hzero)
  let Ψ' : V →ₗ[ℂ] (LinearMap.ker L0).dualAnnihilator := Ψ.codRestrict _ hΦ
  have hΨ' : Function.Injective Ψ' := fun a b h => hinj (congrArg Subtype.val h)
  haveI : Fintype (Sorted r D) := Fintype.ofFinite _
  haveI : FiniteDimensional ℂ (H0 ⧸ LinearMap.ker L0) :=
    Module.Finite.equiv L0.quotKerEquivRange.symm
  haveI : FiniteDimensional ℂ (LinearMap.ker L0).dualAnnihilator :=
    Module.Finite.equiv (Submodule.dualQuotEquivDualAnnihilator _)
  calc finrank ℂ V
      ≤ finrank ℂ (LinearMap.ker L0).dualAnnihilator :=
        LinearMap.finrank_le_finrank_of_injective hΨ'
    _ = finrank ℂ (Module.Dual ℂ (H0 ⧸ LinearMap.ker L0)) :=
        (Submodule.dualQuotEquivDualAnnihilator _).finrank_eq.symm
    _ = finrank ℂ (H0 ⧸ LinearMap.ker L0) := Subspace.dual_finrank_eq
    _ = finrank ℂ (LinearMap.range L0) := L0.quotKerEquivRange.finrank_eq
    _ ≤ finrank ℂ (Sorted r D → ℂ) := Submodule.finrank_le _
    _ = Nat.card (Sorted r D) := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_nat_card]
    _ ≤ _ := card_sorted_le hDN

/-- **The inverse-system bound, dual form.** An injective linear map into the dual of the
weighted-degree-`(N - r(r+1))` polynomials whose values vanish on the Cartan ideal bounds the
dimension by `gapTwoCoefficient N r`. -/
theorem finrank_le_gapTwoCoefficient_of_dual {V : Type*} [AddCommGroup V] [Module ℂ V]
    (N : ℤ) (r : ℕ)
    (Ψ : V →ₗ[ℂ] Module.Dual ℂ (weightedHomogeneousSubmodule ℂ modeWeightZ (N - r * (r + 1))))
    (hinj : Function.Injective Ψ)
    (hann : ∀ v (F : weightedHomogeneousSubmodule ℂ modeWeightZ (N - r * (r + 1))),
      (F : MvPolynomial ℕ ℂ) ∈ cartanIdeal r → Ψ v F = 0) :
    finrank ℂ V ≤ LeeYangTransferAssembly.gapTwoCoefficient N r := by
  by_cases hN : N - r * (r + 1) < 0
  · have hzero : ∀ v, Ψ v = 0 := by
      intro v
      ext F
      have hF0 : (F : MvPolynomial ℕ ℂ) = 0 :=
        eq_zero_of_isWeightedHomogeneous_neg hN
          ((mem_weightedHomogeneousSubmodule _ _ _ _).mp F.2)
      have : F = 0 := Subtype.ext hF0
      rw [this, map_zero, LinearMap.zero_apply]
    haveI : Subsingleton V := ⟨fun a b => hinj (by rw [hzero a, hzero b])⟩
    rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _
  replace hN := not_lt.mp hN
  obtain ⟨D, hD⟩ : ∃ D : ℕ, (D : ℤ) = N - r * (r + 1) := ⟨(N - r * (r + 1)).toNat, by omega⟩
  exact finrank_le_gapTwoCoefficient_of_dual_aux N _ r D hD (by push_cast; omega) Ψ hinj hann

/-! ### Heisenberg separation -/

section Abstract

variable {M B : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup B] [Module ℂ B]
variable {κ : Type*} {ρ : κ → Module.End ℂ M} {σ : κ → Module.End ℂ B}
variable {hz : κ} {hpos : ℕ → κ}
variable {Mdeg : ℤ → Submodule ℂ M} {Bdeg : ℤ → Submodule ℂ B}

variable (σ hz hpos Bdeg) in
/-- **Heisenberg separation of the charge-`r` sector of `B`**: with the polynomial calculus `πB`
of the positive Cartan modes, one functional `β` detects every vector of charge `2r` and energy
`E` through the Cartan monomials of weighted degree `E - r²`. -/
structure HeisenbergSeparation (r : ℕ) where
  β : Module.Dual ℂ B
  πB : MvPolynomial ℕ ℂ →ₐ[ℂ] Module.End ℂ B
  πB_X : ∀ i, πB (X i) = σ (hpos i)
  sep : ∀ (E : ℤ) (b : B), b ∈ Bdeg E → σ hz b = (2 * (r : ℂ)) • b →
    (∀ F : MvPolynomial ℕ ℂ, IsWeightedHomogeneous modeWeightZ F (E - (r : ℤ) * r) →
      β (πB F b) = 0) → b = 0

variable {r : ℕ}

/-- For invariant `x`, `Φ_x(w ∘ π F) = F(h_1, h_2, …) Φ_x(w)`. -/
theorem contract_π_eq (D : CyclicDual ρ hz hpos Mdeg r) (H : HeisenbergSeparation σ hz hpos Bdeg r)
    {x : M ⊗[ℂ] B} (hx : IsInv ρ σ x) (F : MvPolynomial ℕ ℂ) :
    contract (D.w ∘ₗ D.π F) x = H.πB F (contract D.w x) := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul,
      contract_smul, LinearMap.smul_apply]
    rfl
  | add p q hp hq =>
    rw [map_add, LinearMap.comp_add, contract_add, hp, hq, map_add, LinearMap.add_apply]
  | mul_X p i hp =>
    have hcomp : D.w ∘ₗ D.π (p * X i) = -((D.w ∘ₗ D.π p) ∘ₗ ρ (hpos i)) := by
      rw [map_mul, D.π_X, mul_neg, Module.End.mul_eq_comp, LinearMap.comp_neg,
        LinearMap.comp_assoc]
    rw [hcomp, contract_neg, contract_comp_of_isInv hx, neg_neg, hp, mul_comm, map_mul, H.πB_X,
      Module.End.mul_apply]

/-- **The invariant-tensor bound from a cyclic dual and Heisenberg separation.** -/
theorem finrank_le_of_heisenberg (D : CyclicDual ρ hz hpos Mdeg r)
    (H : HeisenbergSeparation σ hz hpos Bdeg r) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (N : ℤ) (ι : V →ₗ[ℂ] M ⊗[ℂ] B) (hι : Function.Injective ι)
    (hinv : ∀ v, IsInv ρ σ (ι v)) (hwt : ∀ v, ι v ∈ tensorWeight Mdeg Bdeg N) :
    finrank ℂ V ≤ LeeYangTransferAssembly.gapTwoCoefficient N r := by
  let H0 := weightedHomogeneousSubmodule ℂ modeWeightZ (N - r * (r + 1))
  let y : V →ₗ[ℂ] B := contract D.w ∘ₗ ι
  let Ψ : V →ₗ[ℂ] Module.Dual ℂ H0 :=
    LinearMap.mk₂ ℂ (fun v (F : H0) => H.β (H.πB F (y v)))
      (fun v v' F => by simp only [map_add])
      (fun c v F => by simp only [map_smul, smul_eq_mul])
      (fun v F F' => by simp only [Submodule.coe_add, map_add, LinearMap.add_apply])
      (fun c v F => by simp only [Submodule.coe_smul, map_smul, LinearMap.smul_apply,
        smul_eq_mul])
  have hΨ : ∀ v (F : H0), Ψ v F = H.β (H.πB F (y v)) := fun v F => rfl
  have hcharge : ∀ v, σ hz (y v) = (2 * (r : ℂ)) • y v := by
    intro v
    have := charge_contract_π D (hinv v) 1
    simpa only [map_one, LinearMap.comp_id] using this
  refine finrank_le_gapTwoCoefficient_of_dual N r Ψ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    rw [Submodule.mem_bot]
    have hyv : y v = 0 := by
      refine H.sep (N - r) (y v) (contract_mem_of_tensorWeight D.w D.supp (hwt v)) (hcharge v)
        fun F hF => ?_
      have he : (N - r) - (r : ℤ) * r = N - r * (r + 1) := by ring
      rw [he] at hF
      have := LinearMap.congr_fun hv ⟨F, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hF⟩
      rw [hΨ] at this
      exact this
    exact hι (by rw [eq_zero_of_contract_cyclic D.w D.cyclic (hinv v) hyv, map_zero])
  · intro v F hF
    rw [hΨ]
    change H.β (H.πB F (contract D.w (ι v))) = 0
    rw [← contract_π_eq D H (hinv v), D.cartan F hF, contract_zero, map_zero]

/-- **Fock coordinates imply Heisenberg separation**, given the Cartan polynomial calculus
and `[h₀, h_{i+1}] = 0`. -/
def heisenbergSeparation_of_fock (Φ : FockCoordinates σ hz hpos Bdeg r)
    (πB : MvPolynomial ℕ ℂ →ₐ[ℂ] Module.End ℂ B) (πB_X : ∀ i, πB (X i) = σ (hpos i))
    (comm : ∀ i, Commute (σ hz) (σ (hpos i))) : HeisenbergSeparation σ hz hpos Bdeg r where
  β := lcoeff ℂ 0 ∘ₗ Φ.φ
  πB := πB
  πB_X := πB_X
  sep := by
    intro E b hb hc hβ
    -- the Cartan calculus preserves the charge-`2r` sector
    have hcomm : ∀ F, Commute (σ hz) (πB F) := by
      intro F
      induction F using MvPolynomial.induction_on with
      | C a =>
        rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
        exact Algebra.commutes a _ |>.symm
      | add p q hp hq => rw [map_add]; exact hp.add_right hq
      | mul_X p i hp => rw [map_mul, πB_X]; exact hp.mul_right (comm i)
    have hcharge : ∀ F, σ hz (πB F b) = (2 * (r : ℂ)) • πB F b := by
      intro F
      rw [← Module.End.mul_apply, (hcomm F).eq, Module.End.mul_apply, hc, map_smul]
    have hφ : ∀ F, Φ.φ (πB F b) = oscD F (Φ.φ b) := by
      intro F
      induction F using MvPolynomial.induction_on with
      | C a =>
        rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes,
          Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
          map_smul, LinearMap.smul_apply]
        rfl
      | add p q hp hq => rw [map_add, LinearMap.add_apply, map_add, hp, hq, map_add,
          LinearMap.add_apply]
      | mul_X p i hp =>
        rw [mul_comm, map_mul, Module.End.mul_apply, πB_X, Φ.intertwine _ (hcharge p), hp,
          map_mul, oscD_X, Module.End.mul_apply]
    apply Φ.inj E b hb hc
    have hdeg := Φ.degree E b hb hc
    ext α
    rw [coeff_zero]
    by_cases hα : Finsupp.weight modeWeightZ α = E - (r : ℤ) * r
    · have h1 := hβ (monomial α 1) (isWeightedHomogeneous_monomial _ _ _ hα)
      change coeff 0 (Φ.φ (πB (monomial α 1) b)) = 0 at h1
      rw [← constantCoeff_eq, hφ, constantCoeff_oscD, modePairing_monomial] at h1
      exact (mul_eq_zero.mp h1).resolve_right (pairConst_ne_zero α)
    · by_contra hne
      exact hα (hdeg hne)

end Abstract

/-! ### The assembly with Heisenberg separation -/

section Assembly

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
variable {κ : Type*} {σ : κ → Module.End ℂ B} {hz : κ} {hpos : ℕ → κ}
variable {Bdeg : ℤ → Submodule ℂ B}

/-- **The leading-symbol upper bound from symbol models and Heisenberg separation.** -/
theorem leadingInvariantSymbolBound_of_heisenberg (S : ConcreteKahlerGeometry)
    (oddZero : ∀ n (hp : IsPosOn (S.geometry n).P ⊤) (p : ℕ),
      finrank ℂ ((S.model n hp).leadCohom (2 * (p : ℤ) + 1, 0)) = 0)
    (negZero : ∀ n (hp : IsPosOn (S.geometry n).P ⊤) (j : ℤ), j < 0 →
      finrank ℂ ((S.model n hp).leadCohom (j, 0)) = 0)
    (model : ∀ n (hp : IsPosOn (S.geometry n).P ⊤) (r : ℕ),
      SymbolCyclicModel σ hz hpos Bdeg (S.model n hp) n r)
    (sep : ∀ r : ℕ, HeisenbergSeparation σ hz hpos Bdeg r) :
    LeadingInvariantSymbolBound S := by
  intro n hp j
  by_cases hj : j < 0
  · rw [negZero n hp j hj]; exact Nat.zero_le _
  rcases Int.even_or_odd' j with ⟨r', hr | hr⟩
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, r' = (r : ℤ) := ⟨r'.toNat, by omega⟩
    subst hr
    rw [leadingCoefficient_even]
    exact finrank_le_of_heisenberg (model n hp r).dual (sep r) n (model n hp r).ι
      (model n hp r).injective (model n hp r).inv (model n hp r).weight
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, r' = (r : ℤ) := ⟨r'.toNat, by omega⟩
    subst hr
    rw [oddZero n hp r]; exact Nat.zero_le _

end Assembly

/-! ### The actual level-one module -/

open Sl2CosetConcrete

theorem fabc_two_two (c : Fin 3) : AffineVOA.fabc 2 2 c = 0 := by
  fin_cases c <;> rfl

/-- The Cartan modes of the actual `L_1(sl₂)` commute away from total mode zero. -/
theorem bMode_h_commute (m n : ℤ) (hmn : m + n ≠ 0) :
    Commute (mode (BSVA.Y (bAction.current 2)) m) (mode (BSVA.Y (bAction.current 2)) n) := by
  have h := bAction.current_comm 2 2 m n
  simp only [fabc_two_two, zero_smul, Finset.sum_const_zero, zero_add, if_neg hmn] at h
  exact sub_eq_zero.mp h

theorem bHPos_commute (i j : ℕ) : Commute (bMode (bHPos i)) (bMode (bHPos j)) :=
  bMode_h_commute _ _ (by push_cast; omega)

theorem bHZero_commute (i : ℕ) : Commute (bMode bHZero) (bMode (bHPos i)) :=
  bMode_h_commute _ _ (by push_cast; omega)

/-- The commutative algebra generated by the positive Cartan modes of `L_1(sl₂)`. -/
abbrev BCartanAlg : Subalgebra ℂ (Module.End ℂ BSpace) :=
  Algebra.adjoin ℂ (Set.range fun i : ℕ => bMode (bHPos i))

instance bCartanAlg_isMulCommutative : IsMulCommutative BCartanAlg :=
  Algebra.isMulCommutative_adjoin ℂ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (bHPos_commute i j).eq)

open scoped IsMulCommutative

/-- **The Cartan polynomial calculus of `L_1(sl₂)`**: `F ↦ F(h_1, h_2, …)` (proved). -/
def bCartanCalc : MvPolynomial ℕ ℂ →ₐ[ℂ] Module.End ℂ BSpace :=
  BCartanAlg.val.comp
    (aeval fun i => (⟨bMode (bHPos i), Algebra.subset_adjoin ⟨i, rfl⟩⟩ : BCartanAlg))

@[simp] theorem bCartanCalc_X (i : ℕ) : bCartanCalc (X i) = bMode (bHPos i) := by
  simp [bCartanCalc]

/-- Intrinsic level-one input (proved: `levelOneHeisenbergSeparation_of_singular
LevelOneHeis.levelOneBottomDetected LevelOneHeis.levelOneHeisenbergSingular`): **Heisenberg
separation of the charge sectors of `L_1(sl₂)`.** For every `r`, one functional `β` detects
every vector of `h₀`-charge `2r` and energy `E` through the Cartan monomials `F(h_1, h_2, …)`
of weighted degree `E - r²`. (In the lattice model `β` is the coefficient of `e^{rα}`; implied
by `LevelOneFockCoordinates`.) -/
def LevelOneHeisenbergSeparation : Prop :=
  ∀ r : ℕ, ∃ β : Module.Dual ℂ BSpace, ∀ (E : ℤ) (b : BSpace), b ∈ bWeight E →
    bMode bHZero b = (2 * (r : ℂ)) • b →
    (∀ F : MvPolynomial ℕ ℂ, IsWeightedHomogeneous modeWeightZ F (E - (r : ℤ) * r) →
      β (bCartanCalc F b) = 0) → b = 0

/-- The intrinsic input as `HeisenbergSeparation` data. -/
def LevelOneHeisenbergSeparation.toSep (h : LevelOneHeisenbergSeparation) (r : ℕ) :
    HeisenbergSeparation bMode bHZero bHPos bWeight r where
  β := (h r).choose
  πB := bCartanCalc
  πB_X := bCartanCalc_X
  sep := (h r).choose_spec

/-- **Fock coordinates imply the intrinsic Heisenberg separation** (proved). -/
theorem levelOneHeisenbergSeparation_of_fock (fock : LevelOneFockCoordinates) :
    LevelOneHeisenbergSeparation := fun r =>
  let H := heisenbergSeparation_of_fock (fock r) bCartanCalc bCartanCalc_X bHZero_commute
  ⟨H.β, H.sep⟩

/-- **Affine GU ⇒ Lee–Yang GU**, with the leading-symbol bound from the symbol models and the
intrinsic Heisenberg separation of `L_1(sl₂)` (odd/negative `2R` vanishing proved).
`#print axioms`-clean, conditional on `hA` (the hypothesis), `models`, `sep`, `lower`. -/
theorem leeYang_gradedUnitary_of_affine_heisenberg
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (models : EndpointSymbolModels hA) (sep : LevelOneHeisenbergSeparation)
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_levelOne_rr_bound hA
    (leadingInvariantSymbolBound_of_heisenberg _ (endpoint_oddZero hA) (endpoint_negZero hA)
      models sep.toSep) lower

/-! ### Heisenberg separation from the structure of the charge sectors -/

theorem bWeight_neg {E : ℤ} (hE : E < 0) : bWeight E = ⊥ :=
  Sl2CosetConcrete.simpleNatSupported 1 bNoncritical (E : ℂ) (by
    rintro ⟨n, hn⟩
    have h : ((n : ℤ) : ℂ) = (E : ℂ) := by exact_mod_cast hn
    have := Int.cast_injective h
    omega)

theorem bMode_mem_bWeight (k : Fin 3 × ℕ) {E : ℤ} {b : BSpace} (hb : b ∈ bWeight E) :
    bMode k b ∈ bWeight (E - k.2) := by
  have h := BSVA.grading_mode _ (bAction.current_weight k.1) b hb (k.2 : ℤ)
  unfold bWeight
  convert h using 2
  push_cast; ring

/-- Intrinsic level-one input (proved: `LevelOneHeis.levelOneBottomDetected`,
`LevelOneHeisBottom.lean`): **the charge-`r` bottom space is detected by one functional** —
the vectors of `h₀`-charge `2r` and energy `r²` form a space of dimension at most one (in the
lattice model, spanned by `e^{rα}`). -/
def LevelOneBottomDetected : Prop :=
  ∀ r : ℕ, ∃ β : Module.Dual ℂ BSpace, ∀ b : BSpace, b ∈ bWeight ((r : ℤ) * r) →
    bMode bHZero b = (2 * (r : ℂ)) • b → β b = 0 → b = 0

/-- Intrinsic level-one input (proved: `LevelOneHeis.levelOneHeisenbergSingular`,
`LevelOneHeisSingular.lean`): **Heisenberg-singular vectors of charge `2r` sit at energy `r²`**
— a vector of `h₀`-charge `2r` killed by every positive Cartan mode `J^h_{i+1}` vanishes
unless its energy is `r²` (in the lattice model the Heisenberg-singular vectors of the charge-`r`
sector are the multiples of `e^{rα}`; intrinsically, the commutant of the Heisenberg subalgebra
in `L_1(sl₂)` is trivial). -/
def LevelOneHeisenbergSingular : Prop :=
  ∀ (r : ℕ) (E : ℤ) (b : BSpace), b ∈ bWeight E → bMode bHZero b = (2 * (r : ℂ)) • b →
    (∀ i, bMode (bHPos i) b = 0) → E ≠ (r : ℤ) * r → b = 0

/-- **Heisenberg separation from the two structural inputs** (proved): descend along the
positive Cartan modes; the descent stops at Heisenberg-singular vectors, which sit at the bottom,
where one functional detects them. -/
theorem levelOneHeisenbergSeparation_of_singular (hbot : LevelOneBottomDetected)
    (hsing : LevelOneHeisenbergSingular) : LevelOneHeisenbergSeparation := by
  intro r
  obtain ⟨β, hβ⟩ := hbot r
  refine ⟨β, ?_⟩
  let P : ℤ → Prop := fun E => ∀ b : BSpace, b ∈ bWeight E →
    bMode bHZero b = (2 * (r : ℂ)) • b →
    (∀ F : MvPolynomial ℕ ℂ, IsWeightedHomogeneous modeWeightZ F (E - (r : ℤ) * r) →
      β (bCartanCalc F b) = 0) → b = 0
  have step : ∀ E : ℤ, (∀ E' < E, P E') → P E := by
    intro E IH b hb hc hF
    have hzero : ∀ i, bMode (bHPos i) b = 0 := by
      intro i
      refine IH (E - ((i : ℤ) + 1)) (by omega) _ ?_ ?_ ?_
      · have := bMode_mem_bWeight (bHPos i) hb
        simpa using this
      · rw [← Module.End.mul_apply, (bHZero_commute i).eq, Module.End.mul_apply, hc, map_smul]
      · intro F hF'
        have hdeg : IsWeightedHomogeneous modeWeightZ (F * X i) (E - (r : ℤ) * r) := by
          have := hF'.mul (isWeightedHomogeneous_X ℂ modeWeightZ i)
          convert this using 1
          simp only [modeWeightZ]; ring
        have := hF (F * X i) hdeg
        rwa [map_mul, Module.End.mul_apply, bCartanCalc_X] at this
    by_cases hE : E = (r : ℤ) * r
    · subst hE
      refine hβ b hb hc ?_
      have := hF 1 (by rw [sub_self]; exact isWeightedHomogeneous_one ℂ modeWeightZ)
      rwa [map_one, Module.End.one_apply] at this
    · exact hsing r E b hb hc hzero hE
  suffices H : ∀ N : ℕ, ∀ E : ℤ, E ≤ N → P E by
    intro E
    by_cases hE : E < 0
    · intro b hb _ _
      rw [bWeight_neg hE] at hb
      exact (Submodule.mem_bot ℂ).mp hb
    · exact H E.toNat E (Int.self_le_toNat E)
  intro N
  induction N with
  | zero =>
    intro E hE
    apply step
    intro E' hE' b hb _ _
    rw [bWeight_neg (by omega)] at hb
    exact (Submodule.mem_bot ℂ).mp hb
  | succ N ih =>
    intro E hE
    apply step
    intro E' hE'
    exact ih E' (by push_cast at hE; omega)

/-- **Affine GU ⇒ Lee–Yang GU**, with the level-one input split into its two structural
statements about `L_1(sl₂)`. `#print axioms`-clean, conditional on `hA` (the hypothesis),
`models`, `hbot`, `hsing`, `lower`. -/
theorem leeYang_gradedUnitary_of_affine_heisenbergSingular
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (models : EndpointSymbolModels hA) (hbot : LevelOneBottomDetected)
    (hsing : LevelOneHeisenbergSingular)
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_heisenberg hA models
    (levelOneHeisenbergSeparation_of_singular hbot hsing) lower

end

end VOA.CyclicEval
