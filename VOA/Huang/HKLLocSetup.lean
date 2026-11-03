/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Huang.HKLExtModes
import VOA.Huang.HexagonCloseResidual
import VOA.Huang.PentagonCloseEdges
import VOA.Huang.HKLLocRational

/-!
# HKL locality, setup: the product and iterate of an algebra object, and single-valuedness

For an algebra object `(A, μ)` in the category of ordinary modules of a strongly rational `V`:

* `prodOp F μ : ProductSpace F A A A A` — `x, u ↦ μ(𝒴_{A,A}(x, z) μ(u))`, the product
  `Y_W(a, z₁) Y_W(b, z₂) c` after inserting the universal intertwiner;
* `iterOp F μ : IterateSpace F A A A A` — `u, z ↦ μ(𝒴_{A,A}(μ(u), z) ·)`, the iterate
  `Y_W(Y_W(a, z₀) b, z₂) c`;
* `iterate_eq_product` — **associativity of `μ` gives `It = Pr`** on the real four-point
  segment (`evalAssoc_fourPoint`, the library's analytic associator);
* `restrict_braiding_prodOp`, `skewP_iterOp` — **commutativity of `μ`** for both FHL phases
  (`Ω₀` = `Phase.upper`, `Ω₋₁` = its inverse): the inner braiding of a product is trivial, and the
  skew of the iterate is the product;
* **single-valuedness** — trivial twist forces integral intermediate weights
  (`prodCoef_int`, `iterCoef_int`), hence `prodL`/`iterL` depend only on `e^λ`
  (`prodL_congr`, `iterL_congr`), and their composites with a logarithm are holomorphic across
  the branch cut (`differentiableAt_comp_clog`).

No `sorry`, no new axioms.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace VOA.Huang.HKLLoc

open CategoryTheory
open VOA VOA.Huang.TensorCat VOA.Huang.FusionUnit VOA.Huang.FusionProduct
open VOA.Huang.TensorCat.BraidRibbon VOA.Huang.TensorCat.HexagonClose VOA.Huang.HKLExt
open Complex

universe u

/-! ## Integral exponents and logarithms -/

/-- A sum `Σ c_w e^{e_w λ}` with integral exponents depends only on `e^λ`. -/
theorem tsum_exp_congr (c e : ℂ → ℂ) (he : ∀ w, c w ≠ 0 → ∃ n : ℤ, e w = n) {L₁ L₂ : ℂ}
    (hL : Complex.exp L₁ = Complex.exp L₂) :
    ∑' w, c w * Complex.exp (e w * L₁) = ∑' w, c w * Complex.exp (e w * L₂) := by
  refine tsum_congr fun w => ?_
  by_cases hc : c w = 0
  · rw [hc, zero_mul, zero_mul]
  · obtain ⟨n, hn⟩ := he w hc
    rw [hn, Complex.exp_int_mul, Complex.exp_int_mul, hL]

/-- `e^{nL}` with `n` integral depends only on `e^L`. -/
theorem exp_int_congr (n : ℤ) {L₁ L₂ : ℂ} (hL : Complex.exp L₁ = Complex.exp L₂) :
    Complex.exp (n * L₁) = Complex.exp (n * L₂) := by
  rw [Complex.exp_int_mul, Complex.exp_int_mul, hL]

/-- Real part of any logarithm. -/
theorem re_of_exp_eq {L z : ℂ} (h : Complex.exp L = z) : L.re = Real.log ‖z‖ := by
  rw [← h, Complex.norm_exp, Real.log_exp]

/-- **A single-valued function of the logarithm is holomorphic across the branch cut.** If
`g L` depends only on `e^L` and `g` is holomorphic at every logarithm of `z ≠ 0`, then
`z ↦ g (log z)` is holomorphic at `z` (near the negative axis, use `log(-z) + πi`). -/
theorem differentiableAt_comp_clog {g : ℂ → ℂ}
    (hg : ∀ L₁ L₂, Complex.exp L₁ = Complex.exp L₂ → g L₁ = g L₂) {z : ℂ} (hz : z ≠ 0)
    (hd : ∀ L, Complex.exp L = z → DifferentiableAt ℂ g L) :
    DifferentiableAt ℂ (fun z => g (Complex.log z)) z := by
  by_cases hs : z ∈ Complex.slitPlane
  · exact (hd _ (Complex.exp_log hz)).comp z (Complex.differentiableAt_log hs)
  · have hs' : -z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff] at hs ⊢
      push Not at hs
      have hre : z.re ≤ 0 := hs.1
      have him : z.im = 0 := by
        by_contra h
        exact hz (by
          have := hs.2
          exact absurd this h)
      left
      have : z.re ≠ 0 := fun h0 => hz (Complex.ext h0 him)
      simp only [Complex.neg_re]
      exact neg_pos.2 (lt_of_le_of_ne hre this)
    have hexp : ∀ u : ℂ, u ≠ 0 → Complex.exp (Complex.log (-u) + Real.pi * Complex.I) = u := by
      intro u hu
      rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.2 hu), Complex.exp_pi_mul_I]
      ring
    have hev : (fun z => g (Complex.log z)) =ᶠ[nhds z]
        fun u => g (Complex.log (-u) + Real.pi * Complex.I) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with u hu
      exact hg _ _ ((Complex.exp_log hu).trans (hexp u hu).symm)
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
    exact (hd _ (hexp z hz)).comp z
      ((differentiableAt_id.neg.clog hs').add_const _)

/-- `e^{n log z} = z^n` for integral `n`. -/
theorem exp_int_mul_log (n : ℤ) {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (n * Complex.log z) = z ^ n := by
  rw [Complex.exp_int_mul, Complex.exp_log hz]

/-! ## Tests with integral weights -/

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {V : VertexOperatorAlgebra 𝒱}

/-- A four-point test whose four weights are integers. -/
def IntTest {X Y Z T : Ordinary V} (d : FourPointTest X Y Z T) : Prop :=
  (∃ a : ℤ, d.α = a) ∧ (∃ b : ℤ, d.β = b) ∧ (∃ c : ℤ, d.γ = c) ∧ (∃ e : ℤ, d.δ = e)

theorem IntTest.swapM {X Y Z T : Ordinary V} {d : FourPointTest X Y Z T} (h : IntTest d) :
    IntTest d.swapM :=
  ⟨h.2.1, h.1, h.2.2.1, h.2.2.2⟩

theorem IntTest.lowerK {X Y Z T : Ordinary V} {d : FourPointTest X Y Z T} (h : IntTest d)
    (j : ℕ) : IntTest (d.lowerK j) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨e, he⟩⟩ := h
  refine ⟨⟨b, hb⟩, ⟨c, hc⟩, ⟨a, ha⟩, ⟨e - j, ?_⟩⟩
  change d.δ - j = _
  rw [he]; push_cast; ring

/-- The integer `δ - α - β - γ` of an integral test. -/
theorem IntTest.total {X Y Z T : Ordinary V} {d : FourPointTest X Y Z T} (h : IntTest d) :
    ∃ n : ℤ, d.δ - d.α - d.β - d.γ = n := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨e, he⟩⟩ := h
  exact ⟨e - a - b - c, by rw [ha, hb, hc, he]; push_cast; ring⟩

/-! ## The product and the iterate of an algebra object -/

variable (F : FusionChoice V) {A : Ordinary V} (μ : tensorObj F A A ⟶ A)

/-- The product `x, u ↦ μ(𝒴_{A,A}(x, z) μ(u))` (inputs `A` and `A ⊠ A`). -/
def prodOp : ProductSpace F A A A A :=
  postcompose (F A (tensorObj F A A)).intertwiner A.isMod (tensorHom F (𝟙 A) μ ≫ μ)

/-- The iterate `u, z ↦ μ(𝒴_{A,A}(μ(u), z) ·)` (inputs `A ⊠ A` and `A`). -/
def iterOp : IterateSpace F A A A A :=
  postcompose (F (tensorObj F A A) A).intertwiner A.isMod (tensorHom F μ (𝟙 A) ≫ μ)

theorem prodOp_val (n : ℂ) (x : A.carrier) (u : (tensorObj F A A).carrier) :
    (prodOp F μ).val n x u = μ.val ((F A A).intertwiner.val n x (μ.val u)) := by
  change (tensorHom F (𝟙 A) μ ≫ μ).val ((F A (tensorObj F A A)).intertwiner.val n x u) = _
  rw [Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply]

theorem iterOp_val (n : ℂ) (u : (tensorObj F A A).carrier) (z : A.carrier) :
    (iterOp F μ).val n u z = μ.val ((F A A).intertwiner.val n (μ.val u) z) := by
  change (tensorHom F μ (𝟙 A) ≫ μ).val ((F (tensorObj F A A) A).intertwiner.val n u z) = _
  rw [Ordinary.comp_apply, tensorHom_intertwiner, Ordinary.id_apply]

/-! ## Integral intermediate weights -/

variable {F μ}

theorem mu_mem_weight {X Y : Ordinary V} {α β : ℂ} {x : X.carrier} {y : Y.carrier}
    (hx : x ∈ X.isMod.weight α) (hy : y ∈ Y.isMod.weight β) (n : ℂ)
    (g : tensorObj F X Y ⟶ A) :
    g.val ((F X Y).intertwiner.val n x y) ∈ A.isMod.weight (α + β - n - 1) :=
  hom_mem_weight (A₂ := (tensorObj F X Y).isMod) (A₃ := A.isMod) g.property
    (VOA.Huang.FusionTop.mem_weight (F X Y).intertwiner.property hx hy n)

variable (htw : (twistIso A).hom = 𝟙 A)
include htw

/-- With trivial twist, a nonzero product coefficient of `prodOp` sits at an integral weight. -/
theorem prodCoef_int (d : FourPointTest A A A A) {w : ℂ}
    (hw : prodCoef F (prodOp F μ) d w ≠ 0) : ∃ k : ℤ, (k : ℂ) = w := by
  by_contra hk
  push Not at hk
  apply hw
  have hm := mu_mem_weight (F := F) d.hy d.hz (d.β + d.γ - w - 1) μ
  rw [show d.β + d.γ - (d.β + d.γ - w - 1) - 1 = w by ring,
    weight_eq_bot_of_not_int htw hk, Submodule.mem_bot] at hm
  rw [prodCoef, prodOp_val, hm]
  erw [LinearMap.map_zero, LinearMap.map_zero, LinearMap.map_zero]

/-- With trivial twist, a nonzero iterate coefficient of `iterOp` sits at an integral weight. -/
theorem iterCoef_int (d : FourPointTest A A A A) {w : ℂ}
    (hw : iterCoef F (iterOp F μ) d w ≠ 0) : ∃ k : ℤ, (k : ℂ) = w := by
  by_contra hk
  push Not at hk
  apply hw
  have hm := mu_mem_weight (F := F) d.hx d.hy (d.α + d.β - w - 1) μ
  rw [show d.α + d.β - (d.α + d.β - w - 1) - 1 = w by ring,
    weight_eq_bot_of_not_int htw hk, Submodule.mem_bot] at hm
  rw [iterCoef, iterOp_val, hm]
  erw [LinearMap.map_zero, LinearMap.zero_apply, LinearMap.map_zero, LinearMap.map_zero]

theorem prodL_exp_int {d : FourPointTest A A A A} (hd : IntTest d) (w : ℂ)
    (hw : prodCoef F (prodOp F μ) d w ≠ 0) : ∃ n : ℤ, d.δ - d.α - w = n := by
  obtain ⟨k, hk⟩ := prodCoef_int htw d hw
  obtain ⟨⟨a, ha⟩, -, -, ⟨e, he⟩⟩ := hd
  exact ⟨e - a - k, by rw [ha, he, ← hk]; push_cast; ring⟩

theorem iterL_exp_int {d : FourPointTest A A A A} (hd : IntTest d) (w : ℂ)
    (hw : iterCoef F (iterOp F μ) d w ≠ 0) : ∃ n : ℤ, w - d.α - d.β = n := by
  obtain ⟨k, hk⟩ := iterCoef_int htw d hw
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, -, -⟩ := hd
  exact ⟨k - a - b, by rw [ha, hb, ← hk]; push_cast; ring⟩

/-- `prodL` of `prodOp` depends only on `e^λ`. -/
theorem prodL_congr {d : FourPointTest A A A A} (hd : IntTest d) {L₁ L₂ : ℂ}
    (hL : Complex.exp L₁ = Complex.exp L₂) :
    prodL F (prodOp F μ) d L₁ = prodL F (prodOp F μ) d L₂ :=
  tsum_exp_congr _ (fun w => d.δ - d.α - w) (prodL_exp_int htw hd) hL

/-- `iterL` of `iterOp` depends only on `e^ℓ`. -/
theorem iterL_congr {d : FourPointTest A A A A} (hd : IntTest d) {L₁ L₂ : ℂ}
    (hL : Complex.exp L₁ = Complex.exp L₂) :
    iterL F (iterOp F μ) d L₁ = iterL F (iterOp F μ) d L₂ :=
  tsum_exp_congr _ (fun w => w - d.α - d.β) (iterL_exp_int htw hd) hL

omit htw in
variable (hV : StronglyRational V) in
include htw hV in
/-- `ζ ↦ prodL (log ζ)` is holomorphic on `‖ζ‖ > 1` (across the negative axis too). -/
theorem differentiableAt_prodL_log {d : FourPointTest A A A A} (hd : IntTest d) {ζ : ℂ}
    (hζ : 1 < ‖ζ‖) :
    DifferentiableAt ℂ (fun ζ => prodL F (prodOp F μ) d (Complex.log ζ)) ζ := by
  have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hζ; linarith
  refine differentiableAt_comp_clog (fun _ _ h => prodL_congr htw hd h) hζ0 fun L hL => ?_
  have hre : 0 < L.re := by rw [re_of_exp_eq hL]; exact Real.log_pos hζ
  exact (analyticOnNhd_prodL F hV (prodOp F μ) d L hre).differentiableAt

omit htw in
variable (hV : StronglyRational V) in
include htw hV in
/-- `ρ ↦ iterL (log ρ)` is holomorphic on `0 < ‖ρ‖ < 1` (across the negative axis too). -/
theorem differentiableAt_iterL_log {d : FourPointTest A A A A} (hd : IntTest d) {ρ : ℂ}
    (hρ0 : ρ ≠ 0) (hρ : ‖ρ‖ < 1) :
    DifferentiableAt ℂ (fun ρ => iterL F (iterOp F μ) d (Complex.log ρ)) ρ := by
  refine differentiableAt_comp_clog (fun _ _ h => iterL_congr htw hd h) hρ0 fun L hL => ?_
  have hre : L.re < 0 := by
    rw [re_of_exp_eq hL]; exact Real.log_neg (norm_pos_iff.2 hρ0) hρ
  exact (analyticOnNhd_iterL F hV (iterOp F μ) d L hre).differentiableAt

omit htw

/-! ## Associativity: `It = Pr` -/

variable (hV : StronglyRational V)

/-- **Associativity of `μ` gives `It = Pr`** on the real four-point segment. -/
theorem iterate_eq_product
    (hassoc : tensorHom F μ (𝟙 A) ≫ μ =
      (evalAssoc F (ordinaryFourPointInput_pbw F hV) A A A).hom ≫ tensorHom F (𝟙 A) μ ≫ μ) :
    iterateEvaluation F (iterOp F μ) = productEvaluation F (prodOp F μ) := by
  rw [iterOp, hassoc]
  exact evalAssoc_fourPoint F (ordinaryFourPointInput_pbw F hV) A A A A _

/-! ## Commutativity for both phases -/

/-- The two FHL phases. -/
def IsFHLPhase (p : Phase) : Prop := p = Phase.upper ∨ p = Phase.upper.inv

theorem comm_phase (hcomm : (braiding F A A).hom ≫ μ = μ) {p : Phase} (hp : IsFHLPhase p) :
    (braidingP p F A A).hom ≫ μ = μ := by
  rcases hp with rfl | rfl
  · exact hcomm
  · rw [braidingP_inv Phase.upper F A A]
    conv_lhs => rw [← hcomm]
    exact Iso.inv_hom_id_assoc _ _

/-- The inner braiding of `prodOp` is trivial. -/
theorem restrict_braiding_prodOp (hcomm : (braiding F A A).hom ≫ μ = μ) {p : Phase}
    (hp : IsFHLPhase p) :
    restrictInputs (𝟙 A) (braidingP p F A A).hom (prodOp F μ) = prodOp F μ := by
  apply Subtype.ext
  funext n
  ext x u
  change (prodOp F μ).val n ((𝟙 A : A ⟶ A).val x) ((braidingP p F A A).hom.val u) =
    (prodOp F μ).val n x u
  rw [prodOp_val, prodOp_val, Ordinary.id_apply, ← Ordinary.comp_apply, comm_phase hcomm hp]

/-- The skew of the iterate is the product. -/
theorem skewP_iterOp (hcomm : (braiding F A A).hom ≫ μ = μ) {p : Phase} (hp : IsFHLPhase p) :
    skewP p (tensorObj F A A) A A (iterOp F μ) = prodOp F μ := by
  rw [iterOp, ← postcompose_braidingP_comp p F (X := A) (Y := tensorObj F A A)]
  rw [prodOp]
  congr 1
  rw [← Category.assoc, ← braidingP_naturality p F (𝟙 A) μ, Category.assoc,
    comm_phase hcomm hp]

end VOA.Huang.HKLLoc
