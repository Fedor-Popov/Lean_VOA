/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2SectorHeadline
import VOA.DeligneAudit.A2SectorGlobal
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Step B8 for A₂: reduction to freeness and local comparisons

* `Mspace` is a module over the symmetric polynomials `B_m` (`smul_mem_Mspace`): the power sums act
  through the Cartan loop operators (`p_r(z) δ = (h ⊗ t^r) δ`), and the power sums generate `B_m`
  in characteristic zero (Newton's identities, fundamental theorem of symmetric polynomials).
* `B_m ≅ ℂ[e₁,…,e_m]` is a noetherian UFD; the tensor polynomials are torsion-free over it.
* **`carrierGeneration_of`**: B8 (`W_m ⊂ M_m`) follows from three named inputs, the paper's
  B6 and the two local comparisons of the codimension-one argument:
  - `MFreeness`: `M_m` is a finite free `B_m`-module (B6; uses U4, U5 and the generic rank);
  - `GenericComparison`: `Δ^n W_m ⊂ M_m` for the discriminant `Δ = ∏_{i≠j}(z_i - z_j)`
    (interpolation over `P_m[Δ⁻¹]`, audit repair 1);
  - `DivisorComparison`: at every height-one prime `p ∋ Δ` of `B_m`, a witness `s ∉ p` with
    `s W_m ⊂ M_m` (the two-point comparison B7 with flat base change, audit repair 2).
  Normality of `B_m` is then the proved globalization `SectorGlobal.mem_of_local_witnesses`.
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial VOA.AffineSl3 VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorFiber
open VOA.DeligneAudit.SectorFiberModule VOA.QuadraticCurrentFunctionalCarrier
open VOA.HeightOneGlobalization

noncomputable section

/-! ## `M_m` is a `B_m`-module -/

theorem applyWord_smul (m : ℕ) (s : SymAlg (K := ℂ) m) :
    ∀ (l : List (Fin 8 × ℕ)) (v : TensorPolynomial (K := ℂ) (σ := Fin 8) m 0),
      applyWord bracketTable m l (s • v) = s • applyWord bracketTable m l v
  | [], _ => rfl
  | (xs :: l), v => by
      change loopOp bracketTable m xs.1 xs.2 (applyWord bracketTable m l (s • v)) = _
      rw [applyWord_smul m s l v, loopOp_smul]
      rfl

theorem applyWord_append (m : ℕ) (l l' : List (Fin 8 × ℕ))
    (v : TensorPolynomial (K := ℂ) (σ := Fin 8) m 0) :
    applyWord bracketTable m (l ++ l') v =
      applyWord bracketTable m l (applyWord bracketTable m l' v) := by
  induction l with
  | nil => rfl
  | cons xs l ih =>
      change loopOp _ _ _ _ (applyWord _ _ (l ++ l') v) = _
      rw [ih]
      rfl

/-- The symmetric polynomials preserving `M_m`. -/
def stab (m : ℕ) : Subalgebra ℂ (SymAlg (K := ℂ) m) where
  carrier := {s | ∀ x ∈ Mspace bracketTable m (5 : Fin 8), s • x ∈ Mspace bracketTable m 5}
  mul_mem' {s t} hs ht x hx := by rw [mul_smul]; exact hs _ (ht x hx)
  add_mem' {s t} hs ht x hx := by rw [add_smul]; exact Submodule.add_mem _ (hs x hx) (ht x hx)
  algebraMap_mem' c x hx := by
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ c hx

theorem psumS_mem_stab (m r : ℕ) : psumS m r ∈ stab m := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      rw [← applyWord_smul, ← loopOp_cartan_deltaVec m 6 (by decide) r]
      refine Submodule.subset_span ⟨l ++ [(6, r)], ?_⟩
      show applyWord bracketTable m (l ++ [(6, r)]) (deltaVec m 5) = _
      rw [applyWord_append]
      rfl
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem esymmS_mem_stab (m : ℕ) : ∀ k, esymmS m k ∈ stab m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have : esymmS m 0 = 1 := Subtype.ext (by simp [esymmS])
        rw [this]; exact Subalgebra.one_mem _
      · -- Newton: k e_k = (-1)^(k+1) Σ_{a<k} (-1)^a e_a p_{k-a}
        have hN := mul_esymm_eq_sum (Fin (m + 0)) ℂ k
        have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
        have heq : esymmS m k = (k : ℂ)⁻¹ • (((-1 : ℂ) ^ (k + 1)) •
            ∑ a ∈ Finset.antidiagonal k with a.1 < k,
              ((-1 : ℂ) ^ a.1) • (esymmS m a.1 * psumS m a.2)) := by
          apply Subtype.ext
          simp only [Subalgebra.coe_smul, Subalgebra.coe_mul, esymmS, psumS,
            AddSubmonoidClass.coe_finsetSum]
          rw [eq_inv_smul_iff₀ hkC]
          simp only [smul_eq_C_mul, map_pow, map_neg, map_one, Finset.mul_sum] at hN ⊢
          rw [show (MvPolynomial.C (k : ℂ) : MvPolynomial (Fin (m + 0)) ℂ) = (k : MvPolynomial _ ℂ) by
            simp, hN]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
        rw [heq]
        have hterm : ∀ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
            ((-1 : ℂ) ^ a.1) • (esymmS m a.1 * psumS m a.2) ∈ stab m := by
          intro a ha
          have h1 : esymmS m a.1 * psumS m a.2 ∈ stab m :=
            (stab m).mul_mem (ih a.1 (Finset.mem_filter.mp ha).2) (psumS_mem_stab m a.2)
          exact (stab m).smul_mem h1 _
        have hsum := (stab m).sum_mem hterm
        exact (stab m).smul_mem ((stab m).smul_mem hsum ((-1 : ℂ) ^ (k + 1))) ((k : ℂ)⁻¹)

theorem stab_eq_top (m : ℕ) : stab m = ⊤ := by
  rw [eq_top_iff]
  intro s _
  obtain ⟨p, rfl⟩ := esymmAlgHom_surjective (σ := Fin (m + 0)) (n := m) ℂ (by simp) s
  have hr : esymmAlgHom (Fin (m + 0)) ℂ m p ∈ (aeval fun i : Fin m =>
      (⟨esymm (Fin (m + 0)) ℂ (i + 1), esymm_isSymmetric _ _ _⟩ : SymAlg (K := ℂ) m)).range :=
    ⟨p, rfl⟩
  rw [aeval_range] at hr
  refine Algebra.adjoin_le ?_ hr
  rintro _ ⟨i, rfl⟩
  exact esymmS_mem_stab m (i + 1)

/-- **`M_m` is stable under the symmetric polynomials.** -/
theorem smul_mem_Mspace (m : ℕ) (s : SymAlg (K := ℂ) m)
    {x : TensorPolynomial (K := ℂ) (σ := Fin 8) m 0} (hx : x ∈ Mspace bracketTable m (5 : Fin 8)) :
    s • x ∈ Mspace bracketTable m 5 := by
  have : s ∈ stab m := by rw [stab_eq_top]; trivial
  exact this x hx

/-- `M_m` as a `B_m`-submodule. -/
def MspaceR (m : ℕ) : Submodule (SymAlg (K := ℂ) m) (TensorPolynomial (K := ℂ) (σ := Fin 8) m 0) where
  carrier := Mspace bracketTable m (5 : Fin 8)
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' s _ hx := smul_mem_Mspace m s hx

/-! ## `B_m` is a noetherian UFD; torsion-freeness; the discriminant -/

theorem card_fin_add_zero (m : ℕ) : Fintype.card (Fin (m + 0)) = m := by simp

/-- `B_m ≅ ℂ[e₁,…,e_m]`. -/
def symEquiv (m : ℕ) : MvPolynomial (Fin m) ℂ ≃ₐ[ℂ] SymAlg (K := ℂ) m :=
  esymmAlgEquiv (Fin (m + 0)) ℂ (card_fin_add_zero m)

instance (m : ℕ) : UniqueFactorizationMonoid (SymAlg (K := ℂ) m) :=
  (symEquiv m).toMulEquiv.uniqueFactorizationMonoid inferInstance

instance (m : ℕ) : IsNoetherianRing (SymAlg (K := ℂ) m) :=
  isNoetherianRing_of_ringEquiv (MvPolynomial (Fin m) ℂ) (symEquiv m).toRingEquiv

theorem torsionFree (m : ℕ) (s : SymAlg (K := ℂ) m)
    (x : TensorPolynomial (K := ℂ) (σ := Fin 8) m 0) (hs : s ≠ 0) (h : s • x = 0) : x = 0 := by
  funext t
  have ht := congrFun h t
  rw [smul_apply_sym] at ht
  have hs' : (s : MvPolynomial (Fin (m + 0)) ℂ) ≠ 0 := fun h0 => hs (Subtype.ext h0)
  exact (mul_eq_zero.mp ht).resolve_left hs'

/-- The discriminant `∏_{i ≠ j} (z_i - z_j)` as a symmetric polynomial. -/
def discS (m : ℕ) : SymAlg (K := ℂ) m :=
  ⟨∏ i : Fin (m + 0), ∏ j : Fin (m + 0), if i = j then 1 else (X i - X j), by
    intro e
    simp only [map_prod]
    conv_rhs => rw [← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun i _ => ?_
    conv_rhs => rw [← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [EmbeddingLike.apply_eq_iff_eq]
    split_ifs <;> simp⟩

theorem discS_ne_zero (m : ℕ) : discS m ≠ 0 := by
  intro h
  have h' := congrArg Subtype.val h
  simp only [discS, ZeroMemClass.coe_zero] at h'
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp h'
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hi
  split_ifs at hj with hij
  · exact one_ne_zero hj
  · exact hij (X_injective (sub_eq_zero.mp hj))

/-! ## The named B6/B8 inputs and the reduction -/

set_option synthInstance.maxHeartbeats 400000

/-- **B6**: `M_m` is a finite free module over `B_m` (paper: the global Weyl module surjects onto
`M_m`, U4 + U5 bound its fibre by the generic rank `8^m`, which is attained by interpolation). -/
structure MFreeness : Prop where
  free : ∀ m, Module.Free (SymAlg (K := ℂ) m) (MspaceR m)
  finite : ∀ m, Module.Finite (SymAlg (K := ℂ) m) (MspaceR m)

/-- **Generic comparison**: a power of the discriminant moves `W_m` into `M_m` (paper:
interpolation at distinct points over `P_m[Δ⁻¹]`, then descent to `B_m[Δ⁻¹]`). -/
structure GenericComparison : Prop where
  le : ∀ m, ∀ x ∈ currentCarrier fullMatrix m 0, ∃ n : ℕ,
    discS m ^ n • x ∈ Mspace bracketTable m (5 : Fin 8)

/-- **Divisor comparison**: at every height-one prime of `B_m` containing the discriminant there is
a local denominator witness (paper: two-point comparison B7 at the prime `(Δ)`, with flat base
change and `Tor₁` vanishing). -/
structure DivisorComparison : Prop where
  le : ∀ m, ∀ x ∈ currentCarrier fullMatrix m 0, ∀ p : HeightOnePrime (SymAlg (K := ℂ) m),
    discS m ∈ p.asIdeal → ∃ s : SymAlg (K := ℂ) m, s ∉ p.asIdeal ∧
      s • x ∈ Mspace bracketTable m (5 : Fin 8)

/-- **B8 from B6 and the two local comparisons** (normality of `B_m` proved). -/
theorem carrierGeneration_of (hF : MFreeness) (hG : GenericComparison)
    (hD : DivisorComparison) : CarrierGeneration := by
  refine ⟨fun m x hx => ?_⟩
  haveI := hF.free m
  haveI := hF.finite m
  let b := Module.Free.chooseBasis (SymAlg (K := ℂ) m) (MspaceR m)
  obtain ⟨n, hn⟩ := hG.le m x hx
  have hΔn : discS m ^ n ≠ 0 := pow_ne_zero n (discS_ne_zero m)
  change x ∈ MspaceR m
  refine SectorGlobal.mem_of_local_witnesses (torsionFree m) (MspaceR m) b x
    ⟨_, hΔn, hn⟩ fun p => ?_
  by_cases hp : discS m ∈ p.asIdeal
  · exact hD.le m x hx p hp
  · exact ⟨discS m ^ n, fun h => hp (p.isPrime.mem_of_pow_mem n h), hn⟩

open VOA.DeligneHigherRankConditionalCapstone in
/-- **A₂ Deligne classical freeness from eight named inputs** (B1, B6, generic and divisor
comparisons of B8, U5, U6, (⋆), Kac–Wakimoto). -/
theorem classicallyFree_of_B8Inputs (F : ℕ → PowerSeries ℚ)
    (hL : CasimirLayerBound) (hF : MFreeness) (hG : GenericComparison) (hD : DivisorComparison)
    (hU5 : SectorWeyl.FusionModuleBound F)
    (hU6 : MixedFusionRecursion F demazureHilbSeries)
    (hstar : StarIdentity) (hkw : KacWakimotoLowerBound) :
    CaseClassicallyFree .A2 W explicitPresentation ∧
      RingHom.ker (MvPolynomial.aeval fun i =>
        liDegreeZeroClass W 1 ⟨explicitPresentation.gen i,
          explicitPresentation.gen_weight_one i⟩).toRingHom = I2ns :=
  classicallyFree_of_weylInputs F hL (carrierGeneration_of hF hG hD) hU5 hU6 hstar hkw

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.smul_mem_Mspace
#print axioms VOA.DeligneAudit.A2.carrierGeneration_of
#print axioms VOA.DeligneAudit.A2.classicallyFree_of_B8Inputs
end AxiomAudit
