/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.SymbolModelJetDual
import VOA.Examples.SymbolModelKoszul

/-!
# Input (A) for the polynomial image, and the endpoint reduced to strictness

* `jetImgRho r` — the mode derivations restricted to `A_r = jetImage r`;
* `jetDeg r d` — the conformal grading of `A_r` (jet-index weight `d - r`; `u_j, v_j` have
  conformal weight `j + 1/2`, and elements of `A_r` have degree `2r` in `u, v`);
* `jetCyclicDual r : CyclicDual (jetImgRho r) bHZero bHPos (jetDeg r) r` — **input (A) for the
  polynomial image `A_r`, proved outright** (cyclicity, support, charge `2r`, relations (A1));
* `GrJetStrict r` — **strictness** (an input here; constructed for every `r` downstream, see
  its docstring): an injective, degree-preserving intertwiner from the
  actual `gr_r L_{-4/3}(sl₂)` (with its induced mode action) into `A_r` (with the derivation
  action). In the notes this is the filtered Adamović leading-symbol map `gr_r A → A_r`
  (`e ↦ X, f ↦ -Z, h ↦ -2Y, T ↦ -J`) together with the kernel-zero character squeeze
  (`JetStrictSqueeze`);
* `GrJetStrict.toGrCyclicVector` — strictness gives input (A) on the concrete `gr_r A`;
* `leeYang_gradedUnitary_of_affine_jetStrict` — **Affine GU ⇒ Lee–Yang GU**,
  `#print axioms`-clean, conditional on `hA` (the hypothesis), `strict` (strictness for
  `r ≥ 1`), `koszul` (the concrete leading Koszul data), `lower` (classical Rogers–Ramanujan);
* `grJetStrict_zero`, `jetW_zprod_zero` — sanity checks: strictness holds at `r = 0`, and the
  cyclic vector of `A_r` is nonzero (value `1` on `Z_0^r`).

Everything is proved outright from the listed hypotheses.
-/

namespace VOA.SymbolModel

open MvPolynomial VOA.CyclicEval VOA.InvariantSymbol VOA.GradedUnitaryCohomology
open VOA.LeeYangTransferAssembly VOA.ConcreteHodge Sl2CosetConcrete

noncomputable section

/-! ### The restricted action and grading -/

/-- The mode derivations restricted to `A_r`. -/
def jetImgRho (r : ℕ) (k : Fin 3 × ℕ) : Module.End ℂ (jetImage r) :=
  (jetRho k).restrict (jetDer_jetImage k r)

@[simp] theorem jetImgRho_coe (r : ℕ) (k : Fin 3 × ℕ) (m : jetImage r) :
    ((jetImgRho r k m : jetImage r) : JetPoly) = jetDer k m := rfl

/-- The jet-index weight. -/
def jetWt (x : Fin 2 × ℕ) : ℤ := (x.2 : ℤ)

/-- The conformal grading of `A_r`: conformal weight `d` is jet-index weight `d - r`. -/
def jetDeg (r : ℕ) (d : ℤ) : Submodule ℂ (jetImage r) :=
  (weightedHomogeneousSubmodule ℂ jetWt (d - r)).comap (jetImage r).subtype

/-- The base-point evaluation on `A_r`. -/
def jetW (r : ℕ) : Module.Dual ℂ (jetImage r) := evalBase.toLinearMap ∘ₗ (jetImage r).subtype

theorem word_jetImgRho (r : ℕ) (l : List (Fin 3 × ℕ)) (m : jetImage r) :
    ((word (jetImgRho r) l m : jetImage r) : JetPoly) = word jetRho l m := by
  induction l generalizing m with
  | nil => simp [word]
  | cons k l ih =>
    simp only [word, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
    rw [jetImgRho_coe, ih]; rfl

/-! ### Evaluation kills nonzero jet-index weight -/

theorem evalBase_eq_zero_of_weighted {Q : JetPoly} {δ : ℤ} (hδ : δ ≠ 0)
    (hQ : IsWeightedHomogeneous jetWt Q δ) : evalBase Q = 0 := by
  classical
  rw [evalBase, aeval_def, eval₂_eq]
  refine Finset.sum_eq_zero fun s hs => ?_
  have hw := hQ (mem_support_iff.mp hs)
  obtain ⟨x, hx, hx2⟩ : ∃ x ∈ s.support, x.2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hδ
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    refine Finset.sum_eq_zero fun x hx => ?_
    simp [jetWt, h x hx]
  rw [Finset.prod_eq_zero hx, mul_zero]
  have hb : baseVal x = 0 := by
    simp only [baseVal]
    rw [if_neg]
    rintro rfl
    exact hx2 rfl
  rw [hb, zero_pow (Finsupp.mem_support_iff.mp hx)]

/-! ### The cyclic dual vector of `A_r` -/

theorem jetImg_cartanCommute (r : ℕ) : CartanCommute (jetImgRho r) bHPos := fun i j =>
  LinearMap.ext fun m => Subtype.ext (jetDer_h_comm (i + 1) (j + 1) m)

theorem jetImg_h0_comm (r : ℕ) : ∀ i, Commute (jetImgRho r bHZero) (jetImgRho r (bHPos i)) :=
  fun i => LinearMap.ext fun m => Subtype.ext (jetDer_h_comm 0 (i + 1) m)

theorem jetImg_calc_coe (r : ℕ) (F : MvPolynomial ℕ ℂ) (m : jetImage r) :
    ((cartanCalc (jetImgRho r) bHPos (jetImg_cartanCommute r) F m : jetImage r) : JetPoly) =
      jetCalc F m := by
  have h := algHom_comp_eq_of_X (cartanCalc (jetImgRho r) bHPos (jetImg_cartanCommute r))
    jetCalc (jetImage r).subtype (fun i => by
      rw [cartanCalc_X, cartanCalc_X, LinearMap.comp_neg, LinearMap.neg_comp]
      rfl) F
  exact LinearMap.congr_fun h m

theorem killU_jetCalc (F : MvPolynomial ℕ ℂ) (Q : JetPoly) :
    killU (jetCalc F Q) = jetCalc F (killU Q) := by
  have h := algHom_comp_eq_of_X jetCalc jetCalc killU.toLinearMap (fun i => by
    rw [cartanCalc_X, LinearMap.comp_neg, LinearMap.neg_comp]
    congr 1
    exact LinearMap.ext fun Q => killU_jetDer_h (i + 1) Q) F
  exact LinearMap.congr_fun h Q

/-- **Input (A) for the polynomial image `A_r`**, as a `CyclicVector`. -/
def jetCyclicVector (r : ℕ) :
    CyclicVector (jetImgRho r) bHZero bHPos (jetDeg r) (jetImg_cartanCommute r) r where
  w := jetW r
  cyclic m hm := Subtype.ext (jet_cyclic m fun l => by
    have := hm l
    rwa [jetW, LinearMap.comp_apply, Submodule.subtype_apply, word_jetImgRho] at this)
  supp d hd m hm := evalBase_eq_zero_of_weighted (by omega) hm
  charge := by
    refine LinearMap.ext fun m => ?_
    simp only [jetW, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.smul_apply,
      AlgHom.toLinearMap_apply]
    rw [jetImgRho_coe, ← evalBase_killU, killU_jetDer_h,
      jetDer_h0_zSpan_pow r _ (killU_jetImage r m m.2), map_smul,
      evalBase_killU, smul_eq_mul]
  cartan F hF := by
    refine LinearMap.ext fun m => ?_
    simp only [jetW, LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply,
      LinearMap.zero_apply]
    rw [jetImg_calc_coe, ← evalBase_killU, killU_jetCalc,
      jetCalc_zSpan_pow r hF _ (killU_jetImage r m m.2), map_zero]

/-- **Input (A) for the polynomial image `A_r`**, proved outright. -/
def jetCyclicDual (r : ℕ) : CyclicDual (jetImgRho r) bHZero bHPos (jetDeg r) r :=
  (jetCyclicVector r).toCyclicDual (jetImg_h0_comm r)

/-! ### Strictness and the endpoint -/

/-- **Strictness**: an injective, degree-preserving intertwiner from the actual
`gr_r L_{-4/3}(sl₂)` into the polynomial image `A_r`. Constructed for every `r`:
`grJetStrict_zero` (`r = 0`) and `grJetStrict_of_leadingSymbol_product` (`JetStrictEndpoint.lean`)
from the constructed leading-symbol maps and the proved `JetProductBound`, as assembled in
`TwoSeries.leeYang_symbolBound` (`TwoSeriesLeeYang.lean`). -/
structure GrJetStrict (r : ℕ) where
  f : GrA r →ₗ[ℂ] jetImage r
  injective : Function.Injective f
  intertwine : ∀ k, f ∘ₗ grRho r k = jetImgRho r k ∘ₗ f
  degree : ∀ d, ∀ m ∈ grDeg r d, f m ∈ jetDeg r d

/-- Strictness, as a strict cyclic image. -/
def GrJetStrict.toStrictCyclicImage {r : ℕ} (S : GrJetStrict r) : GrStrictCyclicImage r where
  M' := jetImage r
  ρ' := jetImgRho r
  deg' := jetDeg r
  dual := jetCyclicDual r
  f := S.f
  injective := S.injective
  intertwine := S.intertwine
  degree := S.degree

/-- **Strictness gives input (A) on the concrete `gr_r A`.** -/
def GrJetStrict.toGrCyclicVector {r : ℕ} (S : GrJetStrict r) : GrCyclicVector r :=
  S.toStrictCyclicImage.toGrCyclicVector

/-- **Affine GU ⇒ Lee–Yang GU, with input (A) reduced to strictness.** `#print axioms`-clean,
conditional on `hA` (the hypothesis), `strict` (strictness `gr_r A ↪ A_r` for `r ≥ 1`), `koszul`
(the concrete leading Koszul data), `lower` (classical Rogers–Ramanujan). -/
theorem leeYang_gradedUnitary_of_affine_jetStrict
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (strict : ∀ r : ℕ, GrJetStrict (r + 1)) (koszul : EndpointGrLeadKoszul hA)
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_grLeadKoszul hA (fun r => (strict r).toGrCyclicVector) koszul
    lower

/-! ### Sanity checks (non-vacuity) -/

theorem evalBase_genCoeff_two_zero : evalBase (genCoeff 2 0) = 1 := by
  rw [genCoeff, genSer_two, zSer, PowerSeries.coeff_mul, Finset.antidiagonal_zero,
    Finset.sum_singleton]
  simp [colSer, evalBase, baseVal]

theorem zprod_zero_mem (r : ℕ) : zprod (fun _ : Fin r => 0) ∈ jetImage r := by
  rw [zprod, Finset.prod_const, Finset.card_univ, Fintype.card_fin, jetImage]
  exact Submodule.pow_mem_pow _
    (Submodule.subset_span (Set.mem_range.mpr ⟨((2 : Fin 4), 0), rfl⟩)) r

/-- The cyclic vector of `A_r` is nonzero: it takes the value `1` on `Z_0^r`. -/
theorem jetW_zprod_zero (r : ℕ) : jetW r ⟨_, zprod_zero_mem r⟩ = 1 := by
  simp [jetW, zprod, evalBase_genCoeff_two_zero]

theorem grDeg_zero_eq_zero {d : ℤ} (hd : d ≠ 0) {m : GrA 0} (hm : m ∈ grDeg 0 d) : m = 0 := by
  obtain ⟨⟨y, hy⟩, hy', rfl⟩ := Submodule.mem_map.mp hm
  have hy0 : y = 0 := by
    change y ∈ affineFlag.piece 0 d at hy'
    rcases lt_or_gt_of_ne hd with hdn | hdp
    · have h := affineFlag.le_grading 0 d hy'
      rwa [AVOA.positivity d hdn, Submodule.mem_bot] at h
    · rw [affineFlag.bot d hdp, Submodule.mem_bot] at hy'
      exact hy'
  subst hy0
  rfl

/-- The constant `1 ∈ A_0`. -/
def oneJet : jetImage 0 :=
  ⟨1, by rw [jetImage, pow_zero]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩⟩

theorem oneJet_ne_zero : oneJet ≠ 0 := fun h => one_ne_zero (congrArg Subtype.val h)

theorem grVac_w_ne_zero : grCyclicVector_zero.w grVac ≠ 0 := by
  intro h
  apply grVac_ne_zero
  refine grCyclicVector_zero.cyclic grVac fun l => ?_
  cases l with
  | nil => simpa [word] using h
  | cons k l =>
    simp only [word, List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [grRho_zero_eq_zero, LinearMap.zero_apply, map_zero]

/-- **Strictness holds at `r = 0`** (the vacuum line maps to the constants): the strictness
hypothesis is satisfiable with these conventions. -/
def grJetStrict_zero : GrJetStrict 0 where
  f := (grCyclicVector_zero.w grVac)⁻¹ •
      (LinearMap.toSpanSingleton ℂ (jetImage 0) oneJet ∘ₗ grCyclicVector_zero.w)
  injective := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    obtain ⟨c, rfl⟩ := grA_zero_eq x
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
      map_smul, smul_smul] at hx
    rw [inv_mul_cancel₀ grVac_w_ne_zero, mul_one] at hx
    rcases smul_eq_zero.mp hx with h | h
    · rw [h, zero_smul]
    · exact absurd h oneJet_ne_zero
  intertwine k := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, grRho_zero_eq_zero, LinearMap.zero_apply,
      map_zero]
    apply Subtype.ext
    simp [oneJet, jetImgRho_coe]
  degree d m hm := by
    by_cases hd : d = 0
    · subst hd
      change (_ : JetPoly) ∈ weightedHomogeneousSubmodule ℂ jetWt _
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
        Submodule.coe_smul]
      refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ ?_)
      rw [mem_weightedHomogeneousSubmodule]
      simpa [oneJet] using isWeightedHomogeneous_one ℂ jetWt
    · rw [grDeg_zero_eq_zero hd hm, map_zero]; exact Submodule.zero_mem _

end

end VOA.SymbolModel
