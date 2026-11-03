/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Foundations.PBWBasis
import VOA.Foundations.PBWTheorem.LieRep

/-!
# `PBWBasis` holds: the ordered creation monomials form a basis of the affine vacuum module

We prove the named hypothesis `VOA.PBWBasis κ hκ b k` for every Lie algebra `𝔤` with invariant
form, every ordered basis `b` and every level `k` (`VOA.pbwBasis_holds`).

## Proof

* `p = nonnegSub` (`𝔤[t] ⊕ ℂC ⊕ ℂℓ₀`), with the explicit complement `negComp` spanned by the
  negative loop modes `y (i,n) = b i ⊗ t^{-n-1}` (`negComp_isCompl`), indexed by `A = ι ×ₗ ℕ`.
* The relative PBW representation `PBWTheorem.rep` of `ĝ` on `Multiset A →₀ ℂ` (built from the
  character `vacuumChar k`) gives a linear map `Φ : 𝒱(𝔤,k) → Multiset A →₀ ℂ`,
  `[a] ↦ a · (0 ⊗ 1)`; it is `ĝ`-equivariant (`Φ_rho`) and sends an ordered creation monomial to
  the corresponding basis vector (`Φ_negWord_sorted`).
* Conversely `Ψ : single m u ↦ u • (sorted creation monomial of m)` is `ĝ`-equivariant
  (`Ψ_act`, an induction on the degree mirroring the defining recursion of `act`).
* `Φ ∘ Ψ = id` on basis vectors, and `Ψ ∘ Φ = id` on all creation monomials, hence everywhere by
  the spanning theorem `AffineLie.negSpan_eq_top`.  So `Φ` is a linear equivalence, and the
  basis `B μ = negWord (pbwWord b μ)` is the pull-back of the standard basis.

No PBW statement is assumed: the only inputs are `PBWTheorem.rep` (proved from Mathlib) and the
spanning theorem.
-/

set_option linter.unusedSectionVars false

namespace VOA

open AffineLie Finsupp Module

universe u

namespace VacuumBasis

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  (κ : LinearMap.BilinForm ℂ 𝔤) (hκ : κ.IsInvariant)
  {ι : Type*} [LinearOrder ι] (b : Module.Basis ι ℂ 𝔤)

/-! ## §1  The negative loop modes and the complement -/

/-- The negative loop mode indexed by `(i, n)`: `b i ⊗ t^{-n-1}`. -/
noncomputable def yMode (a : ι ×ₗ ℕ) : AffineLie 𝔤 κ hκ :=
  ofLoop κ hκ (b (ofLex a).1) (-((ofLex a).2 : ℤ) - 1)

/-- The loop component, as a linear map. -/
noncomputable def loopPart : AffineLie 𝔤 κ hκ →ₗ[ℂ] (ℤ →₀ 𝔤) where
  toFun X := X.carrier.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem yMode_linearIndependent : LinearIndependent ℂ (yMode κ hκ b) := by
  have h := Finsupp.linearIndependent_single (R := ℂ) (φ := fun _ : ℤ => ι)
    (fun _ i => b i) (fun _ => b.linearIndependent)
  have hinj : Function.Injective
      (fun a : ι ×ₗ ℕ => (⟨-((ofLex a).2 : ℤ) - 1, (ofLex a).1⟩ : Σ _ : ℤ, ι)) := by
    intro a a' h'
    simp only [Sigma.mk.injEq] at h'
    obtain ⟨h1, h2⟩ := h'
    have h2' := eq_of_heq h2
    apply ofLex.injective
    ext
    · exact h2'
    · have : ((ofLex a).2 : ℤ) = (ofLex a').2 := by omega
      exact_mod_cast this
  refine LinearIndependent.of_comp (loopPart κ hκ) ?_
  convert h.comp _ hinj using 1

/-- The complement: the span of the negative loop modes. -/
noncomputable def negComp : Submodule ℂ (AffineLie 𝔤 κ hκ) :=
  Submodule.span ℂ (Set.range (yMode κ hκ b))

/-- The basis of the complement. -/
noncomputable def negBasis : Module.Basis (ι ×ₗ ℕ) ℂ (negComp κ hκ b) :=
  Module.Basis.span (yMode_linearIndependent κ hκ b)

@[simp] theorem negBasis_apply (a : ι ×ₗ ℕ) :
    (negBasis κ hκ b a : AffineLie 𝔤 κ hκ) = yMode κ hκ b a :=
  Module.Basis.coe_span_apply _ a

theorem mem_negComp_carrier {X : AffineLie 𝔤 κ hκ} (hX : X ∈ negComp κ hκ b) :
    X.carrier.1 ∈ supported 𝔤 ℂ (Set.Iio (0 : ℤ)) ∧ X.carrier.2 = 0 := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨a, rfl⟩ := hX
      refine ⟨single_mem_supported ℂ _ (Set.mem_Iio.mpr (by omega)), rfl⟩
  | zero => exact ⟨Submodule.zero_mem _, rfl⟩
  | add X Y _ _ hX hY =>
      exact ⟨Submodule.add_mem _ hX.1 hY.1, by
        change X.carrier.2 + Y.carrier.2 = 0; rw [hX.2, hY.2, add_zero]⟩
  | smul r X _ hX =>
      exact ⟨Submodule.smul_mem _ r hX.1, by
        change r • X.carrier.2 = 0; rw [hX.2, smul_zero]⟩

theorem negComp_isCompl : IsCompl (nonnegSub κ hκ).toSubmodule (negComp κ hκ b) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro X hp hc
    obtain ⟨h1, h2⟩ := mem_negComp_carrier κ hκ b hc
    have hp' : X.carrier.1 ∈ supported 𝔤 ℂ (Set.Ici (0 : ℤ)) := hp
    have h0 : X.carrier.1 = 0 := by
      ext n
      by_contra hn
      have a1 := (mem_supported ℂ _).mp h1 (Finsupp.mem_support_iff.mpr hn)
      have a2 := (mem_supported ℂ _).mp hp' (Finsupp.mem_support_iff.mpr hn)
      simp only [Set.mem_Iio, Set.mem_Ici] at a1 a2
      omega
    obtain ⟨⟨f, c, d⟩⟩ := X
    simp only at h0 h2
    rw [Prod.mk_eq_zero] at h2
    obtain ⟨rfl, rfl⟩ := h2
    subst h0
    rfl
  · rw [codisjoint_iff, eq_top_iff]
    rintro X -
    induction (mem_span_gens κ hκ X) using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨⟨x, n⟩, rfl⟩ | hy
        · rcases (by omega : n < 0 ∨ 0 ≤ n) with hn | hn
          · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) - 1 := ⟨(-n - 1).toNat, by omega⟩
            refine Submodule.mem_sup_right ?_
            have hx : x = (b.repr x).sum fun i c => c • b i := by
              rw [← Finsupp.linearCombination_apply, b.linearCombination_repr]
            rw [Finsupp.sum] at hx
            simp only
            rw [← ofLoopₗ_apply, hx, map_sum]
            refine Submodule.sum_mem _ fun i _ => ?_
            rw [map_smul]
            refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨toLex (i, m), ?_⟩)
            rfl
          · exact Submodule.mem_sup_left (ofLoop_mem_nonnegSub κ hκ x hn)
        · rcases hy with rfl | hy
          · exact Submodule.mem_sup_left (C_mem_nonnegSub κ hκ)
          · rw [Set.mem_singleton_iff] at hy; subst hy
            exact Submodule.mem_sup_left (ell0_mem_nonnegSub κ hκ)
    | zero => exact Submodule.zero_mem _
    | add a b' _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul c a _ ha => exact Submodule.smul_mem _ c ha

/-! ## §2  The relative PBW representation and the map `Φ` -/

open scoped TensorProduct

variable (k : ℂ)

local notation "ACT" => PBWTheorem.act (nonnegSub κ hκ) (negComp_isCompl κ hκ b)
  (negBasis κ hκ b) (vacuumChar κ hκ k)

/-- The relative PBW representation of `ĝ` on `Multiset (ι ×ₗ ℕ) →₀ ℂ`. -/
noncomputable def pbwRep :
    AffineLie 𝔤 κ hκ →ₗ⁅ℂ⁆ Module.End ℂ (Multiset (ι ×ₗ ℕ) →₀ ℂ) :=
  PBWTheorem.rep (nonnegSub κ hκ) (negComp_isCompl κ hκ b) (negBasis κ hκ b) (vacuumChar κ hκ k)

theorem pbwRep_apply (z : AffineLie 𝔤 κ hκ) (v : Multiset (ι ×ₗ ℕ) →₀ ℂ) :
    pbwRep κ hκ b k z v = ACT z v := rfl

/-- `U(ĝ)` acting on the PBW module. -/
noncomputable def pbwT : UEnv 𝔤 κ hκ →ₐ[ℂ] Module.End ℂ (Multiset (ι ×ₗ ℕ) →₀ ℂ) :=
  UniversalEnvelopingAlgebra.lift ℂ (pbwRep κ hκ b k)

/-- `a ↦ a · (0 ⊗ 1)`. -/
noncomputable def Φ0 : UEnv 𝔤 κ hκ →ₗ[ℂ] (Multiset (ι ×ₗ ℕ) →₀ ℂ) where
  toFun a := pbwT κ hκ b k a (single 0 1)
  map_add' a a' := by rw [map_add, LinearMap.add_apply]
  map_smul' r a := by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply]

theorem Φ0_vanish {a : UEnv 𝔤 κ hκ} (ha : a ∈ vacuumIdeal κ hκ k) : Φ0 κ hκ b k a = 0 := by
  let B : UEnv 𝔤 κ hκ →ₗ[ℂ] ℂ →ₗ[ℂ] (Multiset (ι ×ₗ ℕ) →₀ ℂ) :=
    LinearMap.lcomp ℂ _ (Finsupp.lsingle 0) ∘ₗ (pbwT κ hκ b k).toLinearMap
  have hB : ∀ y u, B y u = pbwT κ hκ b k y (single 0 u) := fun _ _ => rfl
  let L0 := TensorProduct.lift B
  have hle : PBWTheorem.balancing (nonnegSub κ hκ) (vacuumChar κ hκ k) ≤ LinearMap.ker L0 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, x, u, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, L0, TensorProduct.lift.tmul, hB,
      map_mul, Module.End.mul_apply, pbwT, UniversalEnvelopingAlgebra.lift_ι_apply]
    rw [pbwRep_apply, PBWTheorem.act_p_zero, sub_self]
  have h := hle (tmul_one_mem_balancing_of_mem_vacuumIdeal κ hκ k ha)
  rw [LinearMap.mem_ker, TensorProduct.lift.tmul, hB] at h
  exact h

/-- The map `Φ : 𝒱(𝔤,k) → Multiset (ι ×ₗ ℕ) →₀ ℂ`, `[a] ↦ a · (0 ⊗ 1)`. -/
noncomputable def Φ : vacuumSpace κ hκ k →ₗ[ℂ] (Multiset (ι ×ₗ ℕ) →₀ ℂ) :=
  ((vacuumIdeal κ hκ k).restrictScalars ℂ).liftQ (Φ0 κ hκ b k)
      (fun _ ha => Φ0_vanish κ hκ b k ha) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv ℂ (vacuumIdeal κ hκ k)).symm.toLinearMap

theorem Φ_mk (a : UEnv 𝔤 κ hκ) :
    Φ κ hκ b k (Submodule.Quotient.mk a) = pbwT κ hκ b k a (single 0 1) := rfl

theorem Φ_vacuum : Φ κ hκ b k (vacuumVector κ hκ k) = single 0 1 := by
  rw [vacuumVector, Φ_mk, map_one, Module.End.one_apply]

theorem Φ_rho (z : AffineLie 𝔤 κ hκ) (v : vacuumSpace κ hκ k) :
    Φ κ hκ b k (vacuumRho κ hκ k z v) = ACT z (Φ κ hκ b k v) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [vacuumRho_mk, Φ_mk, Φ_mk, map_mul, Module.End.mul_apply, pbwT,
    UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

/-- The letter of `𝔤 × ℕ` attached to `a = (i, n)`. -/
noncomputable def letter (a : ι ×ₗ ℕ) : 𝔤 × ℕ := (b (ofLex a).1, (ofLex a).2)

theorem Φ_negWord_sorted (l : List (ι ×ₗ ℕ)) (hl : l.Pairwise (· ≤ ·)) :
    Φ κ hκ b k (negWord κ hκ k (l.map (letter b))) = single (↑l : Multiset (ι ×ₗ ℕ)) 1 := by
  induction l with
  | nil => simpa using Φ_vacuum κ hκ b k
  | cons a l ih =>
      rw [List.pairwise_cons] at hl
      rw [List.map_cons, letter, negWord_cons, Φ_rho, ih hl.2, ← yMode, ← negBasis_apply,
        PBWTheorem.act_y_low _ _ _ _ (fun c hc => hl.1 c (Multiset.mem_coe.mp hc))]
      rfl

/-! ## §3  The inverse map `Ψ` and its equivariance -/

/-- The sorted creation monomial of a multiset of letters. -/
noncomputable def sortedWord (m : Multiset (ι ×ₗ ℕ)) : vacuumSpace κ hκ k :=
  negWord κ hκ k ((m.sort (· ≤ ·)).map (letter b))

/-- `Ψ : single m u ↦ u • (sorted creation monomial of m)`. -/
noncomputable def Ψ : (Multiset (ι ×ₗ ℕ) →₀ ℂ) →ₗ[ℂ] vacuumSpace κ hκ k :=
  Finsupp.lsum ℂ fun m => LinearMap.toSpanSingleton ℂ _ (sortedWord κ hκ b k m)

theorem Ψ_single (m : Multiset (ι ×ₗ ℕ)) (u : ℂ) :
    Ψ κ hκ b k (single m u) = u • sortedWord κ hκ b k m := by
  simp [Ψ]

theorem Ψ_low {a : ι ×ₗ ℕ} {m : Multiset (ι ×ₗ ℕ)} (h : ∀ c ∈ m, a ≤ c) (u : ℂ) :
    Ψ κ hκ b k (single (a ::ₘ m) u) =
      vacuumRho κ hκ k (yMode κ hκ b a) (Ψ κ hκ b k (single m u)) := by
  rw [Ψ_single, Ψ_single, map_smul, sortedWord, sortedWord, Multiset.sort_cons _ _ _ h,
    List.map_cons, letter, negWord_cons]
  rfl

/-- On the vacuum, `p = 𝔤[t] ⊕ ℂC ⊕ ℂℓ₀` acts through the character `vacuumChar k`. -/
theorem rho_vacuum_of_mem_nonneg {X : AffineLie 𝔤 κ hκ} (hX : X ∈ nonnegSub κ hκ) :
    vacuumRho κ hκ k X (vacuumVector κ hκ k) = (k * X.carrier.2.1) • vacuumVector κ hκ k := by
  obtain ⟨⟨f, c, d⟩⟩ := X
  have hf : f ∈ supported 𝔤 ℂ (Set.Ici (0 : ℤ)) := hX
  let incl : (ℤ →₀ 𝔤) →ₗ[ℂ] AffineLie 𝔤 κ hκ :=
    { toFun := fun g => ofProd κ hκ (g, 0, 0)
      map_add' := fun g g' => by rw [← of_add]; simp [Prod.mk_add_mk]
      map_smul' := fun r g => by rw [RingHom.id_apply, ← of_smul]; simp [Prod.smul_mk] }
  have hdecomp : (⟨(f, c, d)⟩ : AffineLie 𝔤 κ hκ) = incl f + (c • C κ hκ + d • ell0 κ hκ) := by
    change ofProd κ hκ (f, c, d) = ofProd κ hκ (f, 0, 0) + _
    rw [C, ell0, ← of_smul, ← of_smul, ← of_add, ← of_add]
    congr 1
    ext <;> simp
  have hloop : vacuumRho κ hκ k (incl f) (vacuumVector κ hκ k) = 0 := by
    conv_lhs => rw [← f.sum_single, Finsupp.sum, map_sum, map_sum]
    rw [LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun n hn => ?_
    have hn' : (0 : ℤ) ≤ n := (mem_supported ℂ f).mp hf (Finset.mem_coe.mpr hn)
    exact vacuum_pos_annihilate κ hκ k (f n) n hn'
  change _ = (k * c) • _
  rw [hdecomp, map_add, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, hloop, vacuum_acts_central, vacuum_ell0_annihilate,
    LinearMap.smul_apply, LinearMap.id_apply, smul_zero, add_zero, zero_add, smul_smul, mul_comm]

theorem Ψ_act_aux (n : ℕ) :
    ∀ m : Multiset (ι ×ₗ ℕ), Multiset.card m = n → ∀ (z : AffineLie 𝔤 κ hκ) (u : ℂ),
      Ψ κ hκ b k (ACT z (single m u)) = vacuumRho κ hκ k z (Ψ κ hκ b k (single m u)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hmn z u
    have IH : ∀ j < Multiset.card m, ∀ (w : AffineLie 𝔤 κ hκ) (v : Multiset (ι ×ₗ ℕ) →₀ ℂ),
        v ∈ PBWTheorem.Fil (K := ℂ) (ι ×ₗ ℕ) ℂ j →
          Ψ κ hκ b k (ACT w v) = vacuumRho κ hκ k w (Ψ κ hκ b k v) := by
      intro j hj w v hv
      exact PBWTheorem.eq_on_Fil (f := Ψ κ hκ b k ∘ₗ ACT w)
        (f' := vacuumRho κ hκ k w ∘ₗ Ψ κ hκ b k)
        (fun m' u' hm' => ih (Multiset.card m') (by omega) m' rfl w u') hv
    induction z using PBWTheorem.gen_induction (nonnegSub κ hκ) (negComp_isCompl κ hκ b)
      (negBasis κ hκ b) with
    | h0 => simp
    | hadd z z' h h' => simp only [map_add, LinearMap.add_apply, h, h']
    | hsmul r z h => simp only [map_smul, LinearMap.smul_apply, h]
    | hy a =>
        by_cases h : ∀ c ∈ m, a ≤ c
        · rw [PBWTheorem.act_y_low _ _ _ _ h, negBasis_apply, Ψ_low κ hκ b k h]
        · have hm := PBWTheorem.ne_zero_of_not_lb h
          have hba : PBWTheorem.mmin m hm < a := by
            by_contra hc
            exact h fun c hc' => (not_lt.mp hc).trans (PBWTheorem.mmin_le m hm hc')
          obtain ⟨b0, m', hb0, hba', rfl⟩ : ∃ b0 m', (∀ c ∈ m', b0 ≤ c) ∧ b0 < a ∧
              m = b0 ::ₘ m' :=
            ⟨_, _, PBWTheorem.mmin_lb m hm, hba,
              (Multiset.cons_erase (PBWTheorem.mmin_mem m hm)).symm⟩
          have hlt : Multiset.card m' < Multiset.card (b0 ::ₘ m') := by simp
          have hlow : ∀ c ∈ a ::ₘ m', b0 ≤ c := by
            intro c hc'
            rcases Multiset.mem_cons.mp hc' with rfl | hc'
            · exact hba'.le
            · exact hb0 c hc'
          set X := ACT (negBasis κ hκ b a : AffineLie 𝔤 κ hκ) (single m' u) with hX
          have hXmem := PBWTheorem.act_y_sub_mem (nonnegSub κ hκ) (negComp_isCompl κ hκ b)
            (negBasis κ hκ b) (vacuumChar κ hκ k) a m' u
          have e1 : Ψ κ hκ b k (ACT (negBasis κ hκ b b0 : AffineLie 𝔤 κ hκ) X) =
              vacuumRho κ hκ k (negBasis κ hκ b b0 : AffineLie 𝔤 κ hκ) (Ψ κ hκ b k X) := by
            have hsplit : X = (X - single (a ::ₘ m') u) + single (a ::ₘ m') u := by abel
            rw [hsplit, map_add, map_add, map_add, map_add,
              IH _ hlt _ _ hXmem, PBWTheorem.act_y_low _ _ _ _ hlow, negBasis_apply,
              Ψ_low κ hκ b k hlow]
          rw [PBWTheorem.act_y_cons _ _ _ _ hba' hb0, map_add, e1, hX,
            ih _ (hmn ▸ hlt) m' rfl, ih _ (hmn ▸ hlt) m' rfl, Ψ_low κ hκ b k hb0, negBasis_apply,
            negBasis_apply, vacuumRho_comm κ hκ k (yMode κ hκ b a)]
    | hp x =>
        by_cases hm : m = 0
        · subst hm
          rw [PBWTheorem.act_p_zero, Ψ_single, Ψ_single, vacuumChar_apply, map_smul]
          have hw : sortedWord κ hκ b k 0 = vacuumVector κ hκ k := by
            simp [sortedWord]
          rw [hw, rho_vacuum_of_mem_nonneg κ hκ k x.2, smul_smul, mul_comm u]
        · obtain ⟨b0, m', hb0, rfl⟩ : ∃ b0 m', (∀ c ∈ m', b0 ≤ c) ∧ m = b0 ::ₘ m' :=
            ⟨_, _, PBWTheorem.mmin_lb m hm, (Multiset.cons_erase (PBWTheorem.mmin_mem m hm)).symm⟩
          have hlt : Multiset.card m' < Multiset.card (b0 ::ₘ m') := by simp
          have hXmem := PBWTheorem.act_p_mem (nonnegSub κ hκ) (negComp_isCompl κ hκ b)
            (negBasis κ hκ b) (vacuumChar κ hκ k) x m' u
          rw [PBWTheorem.act_p_cons _ _ _ _ x hb0, map_add, IH _ hlt _ _ hXmem,
            ih _ (hmn ▸ hlt) m' rfl, ih _ (hmn ▸ hlt) m' rfl, Ψ_low κ hκ b k hb0, negBasis_apply,
            vacuumRho_comm κ hκ k (x : AffineLie 𝔤 κ hκ)]

/-- **`Ψ` is `ĝ`-equivariant.** -/
theorem Ψ_act (z : AffineLie 𝔤 κ hκ) (v : Multiset (ι ×ₗ ℕ) →₀ ℂ) :
    Ψ κ hκ b k (ACT z v) = vacuumRho κ hκ k z (Ψ κ hκ b k v) := by
  have : Ψ κ hκ b k ∘ₗ ACT z = vacuumRho κ hκ k z ∘ₗ Ψ κ hκ b k :=
    Finsupp.lhom_ext fun m u => Ψ_act_aux κ hκ b k _ m rfl z u
  exact LinearMap.congr_fun this v

/-! ## §4  `Φ` is a linear equivalence -/

theorem Φ_Ψ_single (m : Multiset (ι ×ₗ ℕ)) (u : ℂ) :
    Φ κ hκ b k (Ψ κ hκ b k (single m u)) = single m u := by
  rw [Ψ_single, map_smul, sortedWord,
    Φ_negWord_sorted κ hκ b k _ (Multiset.pairwise_sort m (· ≤ ·)), Multiset.sort_eq,
    Finsupp.smul_single, smul_eq_mul, mul_one]

theorem Ψ_Φ_negWord (L : List (𝔤 × ℕ)) :
    Ψ κ hκ b k (Φ κ hκ b k (negWord κ hκ k L)) = negWord κ hκ k L := by
  induction L with
  | nil =>
      rw [negWord_nil, Φ_vacuum, Ψ_single, one_smul]
      simp [sortedWord]
  | cons p L ih =>
      obtain ⟨x, n⟩ := p
      rw [negWord_cons, Φ_rho, Ψ_act, ih]

/-- **`Φ` is a linear equivalence** `𝒱(𝔤,k) ≃ Multiset (ι ×ₗ ℕ) →₀ ℂ`. -/
noncomputable def ΦEquiv : vacuumSpace κ hκ k ≃ₗ[ℂ] (Multiset (ι ×ₗ ℕ) →₀ ℂ) :=
  LinearEquiv.ofLinear (Φ κ hκ b k) (Ψ κ hκ b k)
    (Finsupp.lhom_ext fun m u => Φ_Ψ_single κ hκ b k m u)
    (LinearMap.ext_on_range (negSpan_eq_top κ hκ k) fun L => Ψ_Φ_negWord κ hκ b k L)

/-! ## §5  The ordered word of an exponent function -/

/-- The ordered list of letters of `μ`. -/
noncomputable def wordA (μ : (ι ×ₗ ℕ) →₀ ℕ) : List (ι ×ₗ ℕ) :=
  (μ.support.sort (· ≤ ·)).flatMap fun p => List.replicate (μ p) p

theorem pbwWord_eq_map (μ : (ι ×ₗ ℕ) →₀ ℕ) : pbwWord b μ = (wordA μ).map (letter b) := by
  simp [pbwWord, wordA, List.map_flatMap, List.map_replicate, letter]

theorem wordA_pairwise (μ : (ι ×ₗ ℕ) →₀ ℕ) : (wordA μ).Pairwise (· ≤ ·) := by
  rw [wordA, List.pairwise_flatMap]
  refine ⟨fun a _ => List.pairwise_replicate.mpr (Or.inr le_rfl), ?_⟩
  refine (Finset.pairwise_sort μ.support (· ≤ ·)).imp fun {a a'} h => ?_
  intro x hx y hy
  rw [List.eq_of_mem_replicate hx, List.eq_of_mem_replicate hy]
  exact h

theorem wordA_coe (μ : (ι ×ₗ ℕ) →₀ ℕ) :
    (↑(wordA μ) : Multiset (ι ×ₗ ℕ)) = Finsupp.toMultiset μ := by
  rw [wordA, ← Multiset.coe_bind, Finset.sort_eq, Finsupp.toMultiset_apply, Finsupp.sum,
    Finset.sum_eq_multiset_sum, Multiset.bind, Multiset.join]
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  rw [Multiset.coe_replicate, Multiset.nsmul_singleton]

end VacuumBasis

open VacuumBasis in
/-- **PBW for the affine vacuum module, proved.**  For every Lie algebra `𝔤` with invariant
form `κ`, every ordered basis `b` of `𝔤` and every level `k`, the ordered creation monomials
`negWord (pbwWord b μ)` form a basis of `𝒱(𝔤,k)`. -/
theorem pbwBasis_holds {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (κ : LinearMap.BilinForm ℂ 𝔤) (hκ : κ.IsInvariant)
    {ι : Type*} [LinearOrder ι] (b : Module.Basis ι ℂ 𝔤) (k : ℂ) : PBWBasis κ hκ b k := by
  let e : Multiset (ι ×ₗ ℕ) ≃ ((ι ×ₗ ℕ) →₀ ℕ) := Multiset.toFinsupp.toEquiv
  refine ⟨((Finsupp.basisSingleOne).reindex e).map (ΦEquiv κ hκ b k).symm, fun μ => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.reindex_apply, Finsupp.coe_basisSingleOne,
    LinearEquiv.symm_apply_eq]
  change _ = Φ κ hκ b k _
  rw [pbwWord_eq_map, Φ_negWord_sorted κ hκ b k _ (wordA_pairwise μ), wordA_coe]
  change single (Multiset.toFinsupp.symm μ) 1 = _
  rw [(Multiset.toFinsupp_eq_iff.mp (Multiset.toFinsupp.apply_symm_apply μ)).symm]

end VOA

section AxiomAudit
#print axioms VOA.VacuumBasis.negComp_isCompl
#print axioms VOA.VacuumBasis.Ψ_act
#print axioms VOA.VacuumBasis.ΦEquiv
#print axioms VOA.pbwBasis_holds
end AxiomAudit
