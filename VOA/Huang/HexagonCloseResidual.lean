import VOA.Huang.HexagonCloseFinal
import VOA.Huang.HexagonCloseChart4

/-! # Hexagon closure: the half-plane continuation of products, proved

`ProductHalfPlaneContinuation F` holds for every strongly rational `W`
(`productHalfPlaneContinuation_pbw`).  An ordinary product four-point function is a finite
sum (over simple external summands, `product_reassemble`, and over the classes mod `ℤ` of the
intermediate weights, `classMin`) of pieces `ζ^{δ-α-r} G(1/ζ)`, where `G` is Huang's product
series (`prodSeries`) of irreducible modules; `G` satisfies a Fuchsian equation with rational
coefficients, poles only at `x = 1` (`Convergence.HuangProductODE`, proved:
`ModuleC2.huangODEInput_holds`), so it continues to each half plane
(`fuchsian_halfPlane_continuation`, Möbius charts + `FrobeniusLog.fundamental_system`).

Consequently (`HexagonCloseFinal`) the hexagons hold and the braided monoidal category of ordinary
modules exists, unconditionally for strongly rational `W` (only `VOA.pbw`):
`hexagonInput_pbw`, `braidedCategory_stronglyRational_pbw`.
-/

noncomputable section
namespace VOA.Huang.TensorCat
open VOA VOA.Huang.FusionUnit VOA.Huang.FusionProduct CategoryTheory
open VOA.Huang.MatrixCoeff
open Complex Filter Topology
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

namespace HexagonClose

open BraidRibbon

/-! ## Classes modulo `ℤ` of a finite set of complex numbers -/

open Classical in
/-- The elements of `S` with minimal real part in their class modulo `ℤ`. -/
def classMin (S : Finset ℂ) : Finset ℂ :=
  S.filter fun h => ∀ h' ∈ S, (∃ k : ℤ, h' = h + k) → h.re ≤ h'.re

theorem mem_classMin {S : Finset ℂ} {r : ℂ} :
    r ∈ classMin S ↔ r ∈ S ∧ ∀ h' ∈ S, (∃ k : ℤ, h' = r + k) → r.re ≤ h'.re := by
  classical
  unfold classMin
  rw [Finset.mem_filter]

theorem exists_classMin (S : Finset ℂ) {h : ℂ} (hh : h ∈ S) :
    ∃ r ∈ classMin S, ∃ n : ℕ, h = r + n := by
  classical
  set T := S.filter fun h' => ∃ k : ℤ, h' = h + k with hT
  have hTne : T.Nonempty := ⟨h, Finset.mem_filter.2 ⟨hh, 0, by simp⟩⟩
  obtain ⟨r, hrT, hrmin⟩ := T.exists_min_image Complex.re hTne
  obtain ⟨hrS, kr, hkr⟩ := Finset.mem_filter.1 hrT
  refine ⟨r, mem_classMin.2 ⟨hrS, fun h' hh' ⟨k', hk'⟩ => ?_⟩, ?_⟩
  · exact hrmin h' (Finset.mem_filter.2 ⟨hh', kr + k', by rw [hk', hkr]; push_cast; ring⟩)
  · have hle := hrmin h (Finset.mem_filter.2 ⟨hh, 0, by simp⟩)
    rw [hkr] at hle
    simp only [Complex.add_re, Complex.intCast_re] at hle
    have hk0 : kr ≤ 0 := by exact_mod_cast (by linarith : (kr : ℝ) ≤ 0)
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -kr)
    refine ⟨n, ?_⟩
    rw [hkr]
    have : ((n : ℕ) : ℂ) = ((-kr : ℤ) : ℂ) := by rw [hn]; push_cast; ring
    rw [this]; push_cast; ring

theorem classMin_unique {S : Finset ℂ} {r r' : ℂ} (hr : r ∈ classMin S) (hr' : r' ∈ classMin S)
    {k : ℤ} (hk : r' = r + k) : r = r' := by
  have h1 := (mem_classMin.1 hr).2 r' (mem_classMin.1 hr').1 ⟨k, hk⟩
  have h2 := (mem_classMin.1 hr').2 r (mem_classMin.1 hr).1 ⟨-k, by rw [hk]; push_cast; ring⟩
  have hre : r'.re = r.re + k := by rw [hk]; simp
  have hk0 : (k : ℝ) = 0 := by linarith
  have : k = 0 := by exact_mod_cast hk0
  rw [hk, this]; simp

theorem classMin_add_nat_inj {S : Finset ℂ} {r r' : ℂ} (hr : r ∈ classMin S)
    (hr' : r' ∈ classMin S) {n n' : ℕ} (h : r + n = r' + n') : r = r' ∧ n = n' := by
  have e : r' = r + ((n - n' : ℤ) : ℂ) := by push_cast; linear_combination -h
  have hrr := classMin_unique hr hr' e
  refine ⟨hrr, ?_⟩
  rw [← hrr] at h
  exact_mod_cast add_left_cancel h

/-! ## Products: linearity, maps, classes -/

variable (F : FusionChoice W) {X Y Z T X' Y' Z' T' : Ordinary W}

variable (hV : StronglyRational W)
include hV

theorem summable_prodL (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) {lam : ℂ}
    (hlam : 0 < lam.re) :
    Summable fun w => prodCoef F J d w * Complex.exp ((d.δ - d.α - w) * lam) := by
  obtain ⟨B, hB⟩ := exists_im_bound hV (tensorObj F Y Z)
  set C : ℝ := Real.exp ((|B| + |(d.δ - d.α).im|) * |lam.im|) with hC
  have hR : 1 < Real.exp lam.re := Real.one_lt_exp_iff.2 hlam
  refine Summable.of_norm_bounded ((summable_norm_prodCoef_ge F hV J d hR).mul_right C)
    (fun w => ?_)
  rw [norm_mul]
  by_cases hc : prodCoef F J d w = 0
  · rw [hc, norm_zero, zero_mul, zero_mul, zero_mul]
  have hwb : (F Y Z).isMod.weight w ≠ ⊥ := fun hb => hc (prodCoef_eq_zero_of_bot F J d hb)
  have him : |(d.δ - d.α - w).im| ≤ |B| + |(d.δ - d.α).im| := by
    have : (d.δ - d.α - w).im = (d.δ - d.α).im - w.im := by simp
    rw [this]
    refine (abs_sub _ _).trans ?_
    have : |w.im| ≤ |B| := (hB w hwb).trans (le_abs_self B)
    linarith
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ((norm_exp_mul_le _ _).trans ?_) (norm_nonneg _)
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm lam.re]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right him (abs_nonneg _)

omit hV in
theorem prodCoef_add (J₁ J₂ : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T) (w : ℂ) :
    prodCoef F (J₁ + J₂) d w = prodCoef F J₁ d w + prodCoef F J₂ d w := by
  change d.functional ((J₁.val _ + J₂.val _) d.x _) = _
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add]; rfl

theorem prodL_finset_sum {ι : Type*} (S : Finset ι) (J : ι → ProductSpace F X Y Z T)
    (d : FourPointTest X Y Z T) {lam : ℂ} (hlam : 0 < lam.re) :
    prodL F (∑ i ∈ S, J i) d lam = ∑ i ∈ S, prodL F (J i) d lam := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, prodL]
    refine (tsum_congr fun w => ?_).trans tsum_zero
    change d.functional ((0 : IntertwiningModes _ _ _) _ d.x _) * _ = 0
    simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, prodL, prodL, prodL,
      ← (summable_prodL F hV (J a) d hlam).tsum_add (summable_prodL F hV _ d hlam)]
    refine tsum_congr fun w => ?_
    rw [prodCoef_add]; ring

omit hV in
theorem prodL_map (f : X' ⟶ X) (g : Y' ⟶ Y) (h : Z' ⟶ Z) (k : T ⟶ T')
    (I : ProductSpace F X Y Z T) (d : FourPointTest X' Y' Z' T') (lam : ℂ) :
    prodL F (productMap F f g h k I) d lam = prodL F I ((d.inputs f g h).output k) lam := by
  refine tsum_congr fun w => ?_
  congr 1
  change d.functional (k.val (I.val _ (f.val d.x) ((tensorHom F g h).val _))) = _
  rw [tensorHom_intertwiner]
  rfl

/-! ## Weight classes of an ordinary module -/

omit hV in
theorem weight_mem_presentation {M : Ordinary W} (P : SimplePresentation M) {w : ℂ}
    (hw : M.isMod.weight w ≠ ⊥) : ∃ i, ∃ n : ℕ, w = (P.part i).h + n := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hw
  have hex : ∃ j, (P.proj j).val v ≠ 0 := by
    by_contra h
    push Not at h
    apply hv0
    rw [← P.total v]
    simp [h]
  obtain ⟨j, hj⟩ := hex
  have hmem : (P.proj j).val v ∈ (P.part j).isMod.weight w :=
    hom_mem_weight (P.proj j).property hv
  have hne : (P.part j).isMod.weight w ≠ ⊥ := by
    intro hb
    rw [hb] at hmem
    exact hj ((Submodule.mem_bot ℂ).1 hmem)
  obtain ⟨n, hn⟩ := (P.part j).isLow w hne
  exact ⟨j, n, hn⟩

/-- The weights of an ordinary module lie in finitely many disjoint progressions `r + ℕ`, with
nothing below `r` in the class of `r`. -/
theorem exists_weight_classes (M : Ordinary W) :
    ∃ R : Finset ℂ, (∀ w, M.isMod.weight w ≠ ⊥ → ∃ r ∈ R, ∃ n : ℕ, w = r + n) ∧
      (∀ r ∈ R, ∀ j : ℕ, M.isMod.weight (r - ((j : ℂ) + 1)) = ⊥) ∧
      (∀ r ∈ R, ∀ r' ∈ R, ∀ n n' : ℕ, r + n = r' + n' → r = r' ∧ n = n') := by
  classical
  have hΦ := PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV
  obtain ⟨P⟩ := simplePresentation_nonempty hV hΦ M
  set S : Finset ℂ := Finset.univ.image fun i => (P.part i).h with hS
  have hcover : ∀ w, M.isMod.weight w ≠ ⊥ → ∃ r ∈ classMin S, ∃ n : ℕ, w = r + n := by
    intro w hw
    obtain ⟨i, n, hn⟩ := weight_mem_presentation P hw
    obtain ⟨r, hr, m, hm⟩ := exists_classMin S (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    exact ⟨r, hr, m + n, by rw [hn, hm]; push_cast; ring⟩
  refine ⟨classMin S, hcover, fun r hr j => ?_, fun r hr r' hr' n n' h =>
    classMin_add_nat_inj hr hr' h⟩
  by_contra hne
  obtain ⟨r', hr', n', hn'⟩ := hcover _ hne
  have e : r' = r + ((-(j + 1 : ℤ) - n' : ℤ) : ℂ) := by push_cast; linear_combination -hn'
  have hrr := classMin_unique hr hr' e
  rw [← hrr] at hn'
  have : ((n' : ℂ)) = -((j : ℂ) + 1) := by linear_combination -hn'
  have h2 : ((n' : ℤ) : ℂ) = ((-(j + 1 : ℤ)) : ℂ) := by push_cast; exact this
  have h3 : (n' : ℤ) = -(j + 1 : ℤ) := by exact_mod_cast h2
  omega

/-- **Class decomposition of a product**: `prodL J d λ = Σ_r e^{(δ-α-r)λ} G_r(e^{-λ})` with
`G_r = Σ_n c_{r+n} xⁿ`. -/
theorem prodL_eq_classes (J : ProductSpace F X Y Z T) (d : FourPointTest X Y Z T)
    {R : Finset ℂ} (hcover : ∀ w, (F Y Z).isMod.weight w ≠ ⊥ → ∃ r ∈ R, ∃ n : ℕ, w = r + n)
    (hinj : ∀ r ∈ R, ∀ r' ∈ R, ∀ n n' : ℕ, r + n = r' + n' → r = r' ∧ n = n')
    {lam : ℂ} (hlam : 0 < lam.re) :
    prodL F J d lam = ∑ r ∈ R, Complex.exp ((d.δ - d.α - r) * lam) *
      VOA.Huang.FrobeniusLog.psEval (PowerSeries.mk fun n => prodCoef F J d (r + n))
        (Complex.exp (-lam)) := by
  set f : ℂ → ℂ := fun w => prodCoef F J d w * Complex.exp ((d.δ - d.α - w) * lam) with hf
  have hfs : Summable f := summable_prodL F hV J d hlam
  set g : R × ℕ → ℂ := fun p => (p.1 : ℂ) + p.2 with hg
  have hginj : Function.Injective g := by
    intro p p' h
    obtain ⟨h1, h2⟩ := hinj p.1 p.1.2 p'.1 p'.1.2 p.2 p'.2 h
    exact Prod.ext (Subtype.ext h1) h2
  have hsupp : Function.support f ⊆ Set.range g := by
    intro w hw
    have hc : prodCoef F J d w ≠ 0 := fun h0 => hw (by simp [hf, h0])
    have hwb : (F Y Z).isMod.weight w ≠ ⊥ := fun hb => hc (prodCoef_eq_zero_of_bot F J d hb)
    obtain ⟨r, hr, n, hn⟩ := hcover w hwb
    exact ⟨(⟨r, hr⟩, n), hn.symm⟩
  have hfg : Summable (f ∘ g) := hfs.comp_injective hginj
  change ∑' w, f w = _
  rw [← hginj.tsum_eq hsupp, show (∑' p : R × ℕ, f (g p)) = ∑' p, (f ∘ g) p from rfl,
    hfg.tsum_prod]
  change ∑' (r : R), (fun r : ℂ => ∑' n : ℕ, f (r + n)) r = _
  rw [Finset.tsum_subtype R (fun r : ℂ => ∑' n : ℕ, f (r + n))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [VOA.Huang.FrobeniusLog.psEval, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_mk, ← Complex.exp_nat_mul, hf]
  dsimp only
  have : Complex.exp ((d.δ - d.α - (r + n)) * lam) =
      Complex.exp ((d.δ - d.α - r) * lam) * Complex.exp (n * -lam) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [this]; ring

/-! ## Huang's equation for each piece -/

/-- Each class piece of a product of irreducible modules satisfies Huang's rational Fuchsian
equation (`HuangProductODE`, proved for strongly rational `W`). -/
theorem ratFuchsian_piece {P₁ P₂ P₃ P₄ : LWModule W} (i₁ : P₁.IsIrreducibleLW)
    (i₂ : P₂.IsIrreducibleLW) (i₃ : P₃.IsIrreducibleLW) (i₄ : P₄.IsIrreducibleLW)
    (I : ProductSpace F (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)
      (Ordinary.of P₄.isMod))
    (d : FourPointTest (Ordinary.of P₁.isMod) (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)
      (Ordinary.of P₄.isMod)) {r : ℂ}
    (hbelow : ∀ j : ℕ,
      (F (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)).isMod.weight (r - ((j : ℂ) + 1)) = ⊥) :
    VOA.Huang.Convergence.RatFuchsian 1 (-(d.β + d.γ - r - 1) - 1)
      (PowerSeries.mk fun n => prodCoef F I d (r + n)) := by
  set Y₂ := (F (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)).intertwiner.val with hY₂
  have hbase : VOA.Huang.MatrixCoeff.IsBase Y₂ d.y d.z (d.β + d.γ - r - 1) := by
    intro j
    have hm := VOA.Huang.FusionTop.mem_weight
      (F (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)).intertwiner.property d.hy d.hz
      (d.β + d.γ - r - 1 + ((j : ℂ) + 1))
    rw [show d.β + d.γ - (d.β + d.γ - r - 1 + ((j : ℂ) + 1)) - 1 = r - ((j : ℂ) + 1) by ring,
      hbelow j] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  have h := (VOA.Huang.ModuleC2.huangODEInput_holds V W hV).1 P₁ P₂ P₃ P₄ i₁ i₂ i₃ i₄
    (F (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)).isMod I.property
    (F (Ordinary.of P₂.isMod) (Ordinary.of P₃.isMod)).intertwiner.property d.hx d.hy d.hz
    d.supported hbase
  convert h using 1
  ext n
  rw [PowerSeries.coeff_mk, VOA.Huang.MatrixCoeff.coeff_prodSeries, prodCoef,
    VOA.Huang.MatrixCoeff.prodCoeff]
  congr 3
  · ring_nf
  · congr 1; ring_nf

/-! ## Assembly -/

/-- **Products continue to the half planes** (strongly rational `W`). -/
theorem productHalfPlaneContinuation_pbw : ProductHalfPlaneContinuation F := by
  intro A B C T J d s hs
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hss' : (-s) * (-s) = 1 := by rw [neg_mul_neg]; exact hss
  have hΦ := PzTensorDecompPBW.finite_Φ_of_stronglyRational_voaPBW hV
  obtain ⟨PA⟩ := simplePresentation_nonempty hV hΦ A
  obtain ⟨PB⟩ := simplePresentation_nonempty hV hΦ B
  obtain ⟨PC⟩ := simplePresentation_nonempty hV hΦ C
  obtain ⟨PD⟩ := simplePresentation_nonempty hV hΦ T
  choose R hcover hbelow hinj using fun j : ExternalIndex PA PB PC PD =>
    exists_weight_classes hV (tensorObj F (Ordinary.of (PB.part j.2.1).isMod)
      (Ordinary.of (PC.part j.2.2.1).isMod))
  set dj : ∀ j : ExternalIndex PA PB PC PD, FourPointTest (Ordinary.of (PA.part j.1).isMod)
      (Ordinary.of (PB.part j.2.1).isMod) (Ordinary.of (PC.part j.2.2.1).isMod)
      (Ordinary.of (PD.part j.2.2.2).isMod) := fun j =>
    (d.inputs (PA.proj j.1) (PB.proj j.2.1) (PC.proj j.2.2.1)).output (PD.inc j.2.2.2) with hdj
  have hpiece : ∀ j : ExternalIndex PA PB PC PD, ∀ r ∈ R j, ∃ Ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ Ψ (Lhs (-s)) ∧ ∀ x ∈ Lhs (-s), ‖x‖ < 1 →
        Ψ x = VOA.Huang.FrobeniusLog.psEval
          (PowerSeries.mk fun n => prodCoef F (productComponent F PA PB PC PD J j) (dj j) (r + n))
          x := by
    intro j r hr
    obtain ⟨s₀, b, c, p, hcp, hFE⟩ := ratFuchsian_piece F hV (PA.irreducible j.1)
      (PB.irreducible j.2.1) (PC.irreducible j.2.2.1) (PD.irreducible j.2.2.2)
      (productComponent F PA PB PC PD J j) (dj j) (hbelow j r hr)
    exact fuchsian_halfPlane_continuation (fun i hi => by simpa using hcp i hi) hFE hss'
  choose! Ψ hΨa hΨeq using hpiece
  refine ⟨fun ζ => ∑ j : ExternalIndex PA PB PC PD, ∑ r ∈ R j,
    Complex.exp ((d.δ - d.α - r) * Complex.log ζ) * Ψ j r (1 / ζ), ?_, ?_⟩
  · -- analyticity
    refine DifferentiableOn.analyticOnNhd (fun ζ hζ => ?_)
      (isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im))
    have hζ : 0 < s * ζ.im := hζ
    have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hζ; simp at hζ
    have hslit : ζ ∈ Complex.slitPlane := by
      refine Or.inr fun h => ?_
      rw [h, mul_zero] at hζ
      exact lt_irrefl _ hζ
    have hinv : 1 / ζ ∈ Lhs (-s) := by
      change 0 < -s * (1 / ζ).im
      rw [im_one_div]
      have hn : 0 < Complex.normSq ζ := Complex.normSq_pos.2 hζ0
      rw [show -s * (-ζ.im / Complex.normSq ζ) = s * ζ.im / Complex.normSq ζ by ring]
      exact div_pos hζ hn
    refine (DifferentiableAt.fun_sum fun j _ => DifferentiableAt.fun_sum fun r _ => ?_
      ).differentiableWithinAt
    refine ((differentiableAt_id.clog hslit).const_mul _).cexp.mul ?_
    have hd : DifferentiableAt ℂ (fun ζ : ℂ => 1 / ζ) ζ :=
      (differentiableAt_const 1).div differentiableAt_id hζ0
    exact (((hΨa j r ‹_›) _ hinv).differentiableAt).comp ζ hd
  · -- agreement for `|ζ| > 1`
    intro ζ hζ hζ1
    have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hζ; simp at hζ
    have hlam : 0 < (Complex.log ζ).re := by rw [Complex.log_re]; exact Real.log_pos hζ1
    have hJ := product_reassemble F PA PB PC PD J
    have h1 : prodL F J d (Complex.log ζ) = ∑ j : ExternalIndex PA PB PC PD,
        prodL F (productComponent F PA PB PC PD J j) (dj j) (Complex.log ζ) := by
      conv_lhs => rw [← hJ]
      rw [prodL_finset_sum F hV _ _ d hlam]
      exact Finset.sum_congr rfl fun j _ => prodL_map F _ _ _ _ _ d _
    rw [h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [prodL_eq_classes F hV _ (dj j) (hcover j) (hinj j) hlam]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hexp : Complex.exp (-Complex.log ζ) = 1 / ζ := by
      rw [Complex.exp_neg, Complex.exp_log hζ0, one_div]
    have hinv : 1 / ζ ∈ Lhs (-s) := by
      change 0 < -s * (1 / ζ).im
      rw [im_one_div]
      have hn : 0 < Complex.normSq ζ := Complex.normSq_pos.2 hζ0
      rw [show -s * (-ζ.im / Complex.normSq ζ) = s * ζ.im / Complex.normSq ζ by ring]
      exact div_pos hζ hn
    have hnorm : ‖1 / ζ‖ < 1 := by
      rw [norm_div, norm_one, div_lt_one (norm_pos_iff.2 hζ0)]; exact hζ1
    rw [hexp, hΨeq j r hr (1 / ζ) hinv hnorm]
    rfl

/-! ## Headlines -/

/-- **The hexagon input holds** for every strongly rational `W` and every choice of fusion
products: both analytic hexagons (FHL `Ω₀` and `Ω₋₁`). `#print axioms`: Lean's three
standard axioms only (the proof uses the theorem `VOA.pbw`). -/
theorem hexagonInput_pbw : HexagonInput F :=
  hexagonInput_of_halfPlane F hV (productHalfPlaneContinuation_pbw F hV)

/-- **The braided monoidal category of ordinary modules** of a strongly rational VOA, on
`monoidalCategoryOfStronglyRational_pbw F hV`, braiding `braiding F` (FHL's `Ω₀`). No hexagon
hypothesis. -/
abbrev braidedCategory_stronglyRational_pbw :
    @BraidedCategory (Ordinary W) _ (monoidalCategoryOfStronglyRational_pbw F hV) :=
  braidedCategoryOfStronglyRational_pbw F hV (hexagonInput_pbw F hV)

theorem braidedCategory_stronglyRational_pbw_braiding (X Y : Ordinary W) :
    @BraidedCategory.braiding (Ordinary W) _ (monoidalCategoryOfStronglyRational_pbw F hV)
      (braidedCategory_stronglyRational_pbw F hV) X Y = braiding F X Y := rfl

omit F in
/-- Existence form: a strongly rational VOA has a braided monoidal category of ordinary modules. -/
theorem nonempty_braidedCategory_stronglyRational_pbw :
    ∃ M : MonoidalCategory (Ordinary W), Nonempty (@BraidedCategory (Ordinary W) _ M) :=
  ⟨monoidalCategoryOfStronglyRational_pbw (fusionChoice_pbw hV) hV,
    ⟨braidedCategory_stronglyRational_pbw (fusionChoice_pbw hV) hV⟩⟩

end HexagonClose
end VOA.Huang.TensorCat
