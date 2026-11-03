/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.SymbolModelCore
import VOA.Examples.LevelOneHeisEndpoint

/-!
# The concrete symbol module `gr_r L_{-4/3}(sl₂)` with its induced mode action

`EndpointSymbolModels hA` asks, for every weight `n` and degree `r`, for *some* module `M` with a
cyclic dual vector and an injective Koszul embedding of the leading cohomology into
`(M ⊗ L_1)^{g[t]}_n`. Here `M` is constructed, with no hypotheses, as the actual associated graded
piece of the corrected filtration of the actual simple affine factor `ASpace = L_{-4/3}(sl₂)`:

* `aFil p = ⨆_m affineFlag.piece p m` — the corrected piece `F_p` (all conformal weights);
* `aMode_aFil` — the nonnegative current modes preserve `F_p` (Li-goodness,
  `BRSTGoodnessMatter.aMode_flag`);
* `GrA r = F_r / F_{r-1}` (`F_{-1} = 0`), with the **induced** mode action
  `grRho r (a, m) = [J^a_m]` for `m ≥ 0` and the conformal grading `grDeg r d`;
* `grRho_cartan_comm` — the induced Cartan modes `h_i`, `h_j` (`i, j ≥ 0`) commute;
* `grCyclicVector_zero` — **input (A) at `r = 0` is proved**: `gr_0 A` is the vacuum line.

The two remaining mathematical inputs are then stated on this concrete module:

* `GrCyclicVector r` — input (A): a cyclic functional on `gr_r A` (negative-transpose action of
  the full nonnegative-mode algebra), of conformal degree `r`, charge `2r`, killed by `I_r`;
* `GrKoszulEmbedding C n r` — the leading Koszul identification, as an injective map
  `H⁰(Q⁻)_{(2r,0)}(n) ↪ (gr_r A ⊗ L_1)^{g[t]}_n`.

`endpointSymbolModels_of_gr` builds `EndpointSymbolModels hA` from them, and
`leeYang_gradedUnitary_of_affine_grSymbols` is the endpoint: **Affine GU ⇒ Lee–Yang GU**,
`#print axioms`-clean, conditional on `hA` (the hypothesis), `cyc` (input (A) for `r ≥ 1`),
`koszul` (the concrete Koszul embedding), `lower` (the classical Rogers–Ramanujan lower bound).
The variant `leeYang_gradedUnitary_of_affine_grStrict` replaces `cyc` by the audit's
decomposition: an injective intertwiner of `gr_r A` into some module with a cyclic dual vector
(strictness + cyclicity of the image).
-/

namespace VOA.SymbolModel

open VOA.CyclicEval VOA.InvariantSymbol VOA.GradedUnitaryCohomology
open VOA.LeeYangTransferAssembly VOA.ConcreteHodge Sl2CosetConcrete
open TensorProduct MvPolynomial

noncomputable section

/-! ### The corrected filtration of `ASpace`, all weights at once -/

/-- The corrected piece `F_p` of the simple affine factor (all conformal weights). -/
def aFil (p : ℕ) : Submodule ℂ ASpace := ⨆ m : ℤ, affineFlag.piece p m

/-- `F_{p-1}`, with `F_{-1} = 0`. -/
def aFilLT : ℕ → Submodule ℂ ASpace
  | 0 => ⊥
  | q + 1 => aFil q

theorem aFil_mono {p q : ℕ} (h : p ≤ q) : aFil p ≤ aFil q :=
  iSup_mono fun m => affineFlag.mono m h

theorem aFilLT_le (p : ℕ) : aFilLT p ≤ aFil p := by
  cases p with
  | zero => exact bot_le
  | succ q => exact aFil_mono (Nat.le_succ q)

theorem eN_natCast (m : ℕ) : eN (m : ℤ) = 0 := by simp [eN]

/-- **The nonnegative current modes preserve the corrected pieces.** -/
theorem aMode_aFil (a : Fin 3) (m : ℕ) (p : ℕ) : ∀ x ∈ aFil p, aMode a m x ∈ aFil p := by
  intro x hx
  refine Submodule.iSup_induction _ (motive := fun x => aMode a m x ∈ aFil p) hx ?_
    (by beta_reduce; rw [map_zero]; exact Submodule.zero_mem _)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact add_mem hx hy)
  intro d y hy
  have h := aMode_flag a m p d y hy
  rw [eN_natCast, add_zero] at h
  exact Submodule.mem_iSup_of_mem _ h

theorem aMode_aFilLT (a : Fin 3) (m : ℕ) (p : ℕ) : ∀ x ∈ aFilLT p, aMode a m x ∈ aFilLT p := by
  cases p with
  | zero =>
    intro x hx
    rw [aFilLT, Submodule.mem_bot] at hx
    rw [hx, map_zero]; exact Submodule.zero_mem _
  | succ q => exact aMode_aFil a m q

/-! ### The associated graded piece and its induced action -/

/-- The kernel `F_{r-1}` inside `F_r`. -/
def grKer (r : ℕ) : Submodule ℂ (aFil r) := (aFilLT r).comap (aFil r).subtype

/-- **`gr_r A = F_r / F_{r-1}`** for the actual simple affine factor. -/
abbrev GrA (r : ℕ) : Type := aFil r ⧸ grKer r

/-- The restriction of `J^a_m` (`m ≥ 0`) to `F_r`. -/
def aModeRestr (r : ℕ) (k : Fin 3 × ℕ) : Module.End ℂ (aFil r) :=
  (aMode k.1 k.2).restrict (aMode_aFil k.1 k.2 r)

theorem aModeRestr_ker (r : ℕ) (k : Fin 3 × ℕ) : grKer r ≤ (grKer r).comap (aModeRestr r k) := by
  intro x hx
  exact aMode_aFilLT k.1 k.2 r _ hx

/-- **The induced action** of the nonnegative current modes on `gr_r A`:
`(a, m) ↦ [J^a_m]`. -/
def grRho (r : ℕ) (k : Fin 3 × ℕ) : Module.End ℂ (GrA r) :=
  (grKer r).mapQ (grKer r) (aModeRestr r k) (aModeRestr_ker r k)

@[simp] theorem grRho_mk (r : ℕ) (k : Fin 3 × ℕ) (x : aFil r) :
    grRho r k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨aMode k.1 k.2 x, aMode_aFil k.1 k.2 r x x.2⟩ := rfl

/-- The conformal grading of `gr_r A`: the image of `affineFlag.piece r d`. -/
def grDeg (r : ℕ) (d : ℤ) : Submodule ℂ (GrA r) :=
  ((affineFlag.piece r d).comap (aFil r).subtype).map (grKer r).mkQ

/-! ### Commutation of the Cartan modes -/

theorem fabc_two_two (c : Fin 3) : AffineVOA.fabc 2 2 c = 0 := by
  fin_cases c <;> rfl

/-- `h_i h_j = h_j h_i` on `ASpace` for `i, j ≥ 0`. -/
theorem aMode_cartan_comm (i j : ℕ) :
    aMode 2 i * aMode 2 j = aMode 2 j * aMode 2 i := by
  have h := aAction.current_comm 2 2 i j
  simp only [fabc_two_two, zero_smul, Finset.sum_const_zero, zero_add] at h
  have h' : aMode 2 i * aMode 2 j - aMode 2 j * aMode 2 i = 0 := by
    change mode (ASVA.Y (aAction.current 2)) i * mode (ASVA.Y (aAction.current 2)) j -
      mode (ASVA.Y (aAction.current 2)) j * mode (ASVA.Y (aAction.current 2)) i = 0
    rw [h]
    split_ifs with hij
    · have hi : (i : ℤ) = 0 := by omega
      rw [hi]; simp
    · rfl
  exact sub_eq_zero.mp h'

/-- The induced Cartan modes commute on `gr_r A`. -/
theorem grRho_cartan_comm (r i j : ℕ) : Commute (grRho r (2, i)) (grRho r (2, j)) := by
  apply Submodule.linearMap_qext
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Module.End.mul_apply,
    grRho_mk]
  congr 1
  apply Subtype.ext
  exact LinearMap.congr_fun (aMode_cartan_comm i j) x

theorem grCartanCommute (r : ℕ) : CartanCommute (grRho r) bHPos :=
  fun i j => grRho_cartan_comm r (i + 1) (j + 1)

theorem grZero_comm (r : ℕ) : ∀ i, Commute (grRho r bHZero) (grRho r (bHPos i)) :=
  fun i => grRho_cartan_comm r 0 (i + 1)

/-! ### The two remaining inputs, on the concrete module -/

/-- **Input (A) on the concrete `gr_r A`** (OPEN for `r ≥ 1`): a cyclic functional on
`gr_r L_{-4/3}(sl₂)` for the negative-transpose action of the full nonnegative-mode algebra, of
conformal degree `r`, charge `2r`, annihilated by the symmetric-center Cartan ideal `I_r`. -/
abbrev GrCyclicVector (r : ℕ) : Type :=
  CyclicVector (grRho r) bHZero bHPos (grDeg r) (grCartanCommute r) r

/-- **The leading Koszul embedding into the concrete `gr_r A ⊗ L_1`** (OPEN): an injective map
`H⁰(Q⁻)_{(2r,0)}(n) ↪ (gr_r A ⊗ L_1)^{g[t]}_n`. -/
structure GrKoszulEmbedding {K : Type*} [AddCommGroup K] [Module ℂ K] (C : KahlerComplex K)
    (n : ℤ) (r : ℕ) where
  ι : C.leadCohom (2 * (r : ℤ), 0) →ₗ[ℂ] GrA r ⊗[ℂ] BSpace
  injective : Function.Injective ι
  inv : ∀ v, IsInv (grRho r) bMode (ι v)
  weight : ∀ v, ι v ∈ tensorWeight (grDeg r) bWeight n

/-- The symbol model on the concrete `gr_r A`. -/
def GrKoszulEmbedding.toSymbolCyclicModel {K : Type*} [AddCommGroup K] [Module ℂ K]
    {C : KahlerComplex K} {n : ℤ} {r : ℕ} (E : GrKoszulEmbedding C n r)
    (V : GrCyclicVector r) : SymbolCyclicModel bMode bHZero bHPos bWeight C n r where
  M := GrA r
  ρ := grRho r
  Mdeg := grDeg r
  dual := V.toCyclicDual (grZero_comm r)
  ι := E.ι
  injective := E.injective
  inv := E.inv
  weight := E.weight

/-! ### Input (A) at `r = 0` -/

theorem aFil_zero_le : aFil 0 ≤ ℂ ∙ ASVA.vacuum := by
  refine iSup_le fun m => ?_
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · intro x hx
    have h := affineFlag.le_grading 0 m hx
    rw [AVOA.positivity m hm, Submodule.mem_bot] at h
    rw [h]; exact Submodule.zero_mem _
  · rw [affineFlag.vacuum_zero]; exact le_rfl
  · rw [affineFlag.bot m hm]; exact bot_le

theorem vacuum_mem_aFil_zero : ASVA.vacuum ∈ aFil 0 := by
  have h : ASVA.vacuum ∈ affineFlag.piece 0 0 := by
    rw [affineFlag.vacuum_zero]; exact Submodule.mem_span_singleton_self _
  exact Submodule.mem_iSup_of_mem 0 h

/-- The vacuum class in `gr_0 A`. -/
def grVac : GrA 0 := Submodule.Quotient.mk ⟨ASVA.vacuum, vacuum_mem_aFil_zero⟩

theorem grKer_zero : grKer 0 = ⊥ := by
  rw [grKer, aFilLT, Submodule.comap_bot, Submodule.ker_subtype]

theorem grVac_ne_zero : grVac ≠ 0 := by
  intro h
  rw [grVac, Submodule.Quotient.mk_eq_zero, grKer_zero, Submodule.mem_bot] at h
  exact aVacuum_ne_zero (congrArg Subtype.val h)

theorem grA_zero_eq (x : GrA 0) : ∃ c : ℂ, x = c • grVac := by
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (aFil_zero_le hy)
  refine ⟨c, ?_⟩
  rw [grVac, ← Submodule.Quotient.mk_smul]
  congr 1
  exact Subtype.ext hc.symm

theorem grRho_vac (k : Fin 3 × ℕ) : grRho 0 k grVac = 0 := by
  rw [grVac, grRho_mk, Submodule.Quotient.mk_eq_zero, grKer_zero, Submodule.mem_bot]
  apply Subtype.ext
  exact ASVA.smul_vacuum_eq_zero _ (by positivity)

theorem grRho_zero_eq_zero (k : Fin 3 × ℕ) : grRho 0 k = 0 := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨c, rfl⟩ := grA_zero_eq x
  rw [map_smul, grRho_vac, smul_zero, LinearMap.zero_apply]

theorem cartanCalc_zero_apply (F : MvPolynomial ℕ ℂ) (x : GrA 0) :
    cartanCalc (grRho 0) bHPos (grCartanCommute 0) F x = constantCoeff F • x := by
  induction F using MvPolynomial.induction_on generalizing x with
  | C a =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      MvPolynomial.algebraMap_eq, constantCoeff_C]
    rfl
  | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, map_add, add_smul]
  | mul_X p i hp =>
    rw [map_mul, Module.End.mul_apply, cartanCalc_X, grRho_zero_eq_zero, neg_zero,
      LinearMap.zero_apply, map_zero, map_mul, constantCoeff_X, mul_zero, zero_smul]

theorem constantCoeff_eq_zero_of_mem_cartanIdeal_zero {F : MvPolynomial ℕ ℂ}
    (hF : F ∈ cartanIdeal 0) : constantCoeff F = 0 := by
  have h : cartanEval 0 F = 0 := hF
  have hz : cartanEval 0 = (aeval (0 : ℕ → MvPolynomial (Fin 0) ℂ)) := by
    rw [cartanEval]
    congr 1
    funext m
    simp [cartanGen, MvPolynomial.psum]
  rw [hz, MvPolynomial.aeval_zero, MvPolynomial.algebraMap_eq] at h
  exact (MvPolynomial.C_injective _ _) (h.trans MvPolynomial.C_0.symm)

/-- **Input (A) at `r = 0`, proved**: the dual of the vacuum class. -/
def grCyclicVector_zero : GrCyclicVector 0 :=
  have hex : ∃ w : Module.Dual ℂ (GrA 0), w grVac ≠ 0 := by
    by_contra h
    push Not at h
    exact grVac_ne_zero ((Module.forall_dual_apply_eq_zero_iff ℂ grVac).mp h)
  { w := hex.choose
    cyclic := fun m hm => by
      obtain ⟨c, rfl⟩ := grA_zero_eq m
      have h := hm []
      simp only [word, List.map_nil, List.prod_nil, Module.End.one_apply, map_smul,
        smul_eq_mul, mul_eq_zero] at h
      rcases h with h | h
      · rw [h, zero_smul]
      · exact absurd h hex.choose_spec
    supp := fun d hd m hm => by
      obtain ⟨⟨y, hy⟩, hy', rfl⟩ := Submodule.mem_map.mp hm
      have hy0 : y = 0 := by
        change y ∈ affineFlag.piece 0 d at hy'
        rcases lt_or_gt_of_ne hd with hdn | hdp
        · have h := affineFlag.le_grading 0 d hy'
          rwa [AVOA.positivity d (by exact_mod_cast hdn), Submodule.mem_bot] at h
        · rw [affineFlag.bot d (by exact_mod_cast hdp), Submodule.mem_bot] at hy'
          exact hy'
      subst hy0
      have : (⟨0, hy⟩ : aFil 0) = 0 := rfl
      rw [this, map_zero, map_zero]
    charge := by
      rw [grRho_zero_eq_zero, LinearMap.comp_zero]
      simp
    cartan := fun F hF => by
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.comp_apply, cartanCalc_zero_apply,
        constantCoeff_eq_zero_of_mem_cartanIdeal_zero hF, zero_smul, map_zero,
        LinearMap.zero_apply] }

/-! ### The endpoint -/

/-- OPEN (leading Koszul identification): the concrete Koszul embeddings for the endpoint
geometry, at every weight `n` and degree `r`. -/
abbrev EndpointGrKoszul (hA : GradedUnitary affineForm affineRealStructure affineFlag) :=
  ∀ n (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤) (r : ℕ),
    GrKoszulEmbedding ((endpointKahler hA).model n hp) n r

/-- OPEN (input (A) for `r ≥ 1`): the concrete cyclic dual vectors of `gr_r A`. -/
abbrev GrCyclicVectorsPos : Type := ∀ r : ℕ, GrCyclicVector (r + 1)

/-- All concrete cyclic dual vectors, the `r = 0` one being proved. -/
def grCyclicVectors (cyc : GrCyclicVectorsPos) : ∀ r : ℕ, GrCyclicVector r
  | 0 => grCyclicVector_zero
  | r + 1 => cyc r

/-- **`EndpointSymbolModels` from the concrete inputs.** -/
def endpointSymbolModels_of_gr (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (cyc : GrCyclicVectorsPos) (koszul : EndpointGrKoszul hA) : EndpointSymbolModels hA :=
  fun n hp r => (koszul n hp r).toSymbolCyclicModel (grCyclicVectors cyc r)

/-- **Affine GU ⇒ Lee–Yang GU, with the symbol module the concrete `gr_r L_{-4/3}(sl₂)`.**
`#print axioms`-clean, conditional on `hA` (the hypothesis), `cyc` (input (A) for `r ≥ 1`),
`koszul` (the concrete leading Koszul embedding), `lower` (classical Rogers–Ramanujan). -/
theorem leeYang_gradedUnitary_of_affine_grSymbols
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (cyc : GrCyclicVectorsPos) (koszul : EndpointGrKoszul hA)
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  VOA.LevelOneHeis.leeYang_gradedUnitary_of_affine_symbolModels hA
    (endpointSymbolModels_of_gr hA cyc koszul) lower

/-! ### Input (A) from strictness and cyclicity of an image -/

/-- **Strictness + cyclicity of the image** (the decomposition of input (A) in
the affine cyclic-dual bridge): an injective, degree-preserving
intertwiner of `gr_r A` into a module (in the application: the polynomial image `A_r`) carrying a cyclic
dual vector. -/
structure GrStrictCyclicImage (r : ℕ) where
  M' : Type
  [acg : AddCommGroup M']
  [mod : Module ℂ M']
  ρ' : Fin 3 × ℕ → Module.End ℂ M'
  deg' : ℤ → Submodule ℂ M'
  dual : CyclicDual ρ' bHZero bHPos deg' r
  f : GrA r →ₗ[ℂ] M'
  injective : Function.Injective f
  intertwine : ∀ k, f ∘ₗ grRho r k = ρ' k ∘ₗ f
  degree : ∀ d, ∀ m ∈ grDeg r d, f m ∈ deg' d

attribute [instance] GrStrictCyclicImage.acg GrStrictCyclicImage.mod

/-- The strict cyclic image gives input (A) on `gr_r A`. -/
def GrStrictCyclicImage.toGrCyclicVector {r : ℕ} (S : GrStrictCyclicImage r) :
    GrCyclicVector r :=
  (S.dual.comap S.f S.injective S.intertwine S.degree).toCyclicVector (grCartanCommute r)

/-- **Affine GU ⇒ Lee–Yang GU, with input (A) split as in the audit**: strictness of
`gr_r A` into a module with a cyclic dual vector, for `r ≥ 1`. `#print axioms`-clean,
conditional on `hA`, `strict`, `koszul`, `lower`. -/
theorem leeYang_gradedUnitary_of_affine_grStrict
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (strict : ∀ r : ℕ, GrStrictCyclicImage (r + 1)) (koszul : EndpointGrKoszul hA)
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_grSymbols hA (fun r => (strict r).toGrCyclicVector) koszul
    lower

end

end VOA.SymbolModel
