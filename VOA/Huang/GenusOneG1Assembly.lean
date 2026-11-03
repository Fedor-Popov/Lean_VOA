import VOA.Huang.VerlindeTransportSplit

/-!
# (G1) in function-space form: the exact interface for the genus-one argument

`VacuumChannelFunctionsInput` asks, for every instance of
`VerlindeTransport.VacuumChannelTransportInput`, for Huang's genus-one data on
SOME complex vector space `K` of functions: an `S`-operator, A- and B-cycle
transports, an `S`-stable remainder `R` (the non-vacuum channels), vacuum-channel
functions `Ψ_x` independent modulo `R`, `S(Ψ_x) = Σ_y S_xy Ψ_y`,
`T_B ∘ S = S ∘ T_A` on the `Ψ_x` (Prop. 4.5), A-cycle eigenvalues `Ω` with
`Ω_{v0} ≠ 0` (Lemma 4.2 (4.10)), and B-cycle matrix `κ · transferMatrix c β`,
`κ ≠ 0` (Lemma 4.2 (4.11)).

* `vacuumChannelTransportInput_of_functionsInput` — the assembly: these data give
  (G1), by `vacuumChannelTransport_of_functions`.
* `functionsInput_of_vacuumChannelTransportInput` — the converse, with the trivial
  witness `K = ι → ℂ`, `Ψ_x = e_x`, `R = 0`.

So `VacuumChannelFunctionsInput ↔ VacuumChannelTransportInput`: the Prop is TRUE
exactly when (G1) is (which is machine-checked equivalent to
`FusionEigenInput ∧ ZigzagNonzeroInput`, Huang's Thm 5.2 and Prop. 5.1), and it is
NOT narrower. Its only purpose is to fix the shape; the content of the genus-one
argument is to produce these data with `K` the actual two-point functions, which the
converse witness does not do.
-/
noncomputable section
namespace VOA.Huang.GenusOneG1
open VOA VOA.Classification.COne VOA.Huang.ZhuModData VOA.Huang.VerlindeTransport
  VOA.Huang.TensorCat
open scoped BigOperators

universe u w

/-- Huang's genus-one vacuum-channel data on some space of functions. -/
def VacuumChannelFunctionsInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ v0 : ι, Nonempty (ModuleEquiv W (D.Mfam v0).isMod (adjointModule W)) →
      ∀ (F : FusionChoice W) (H : OrdinaryFourPointInput F) (a b : ι)
        (c : TransferChoice F D a b) (β : ∀ x, Fin (c.r x) → ℂ), IsTransferScalar F H c β →
        ∃ (K : Type w) (_ : AddCommGroup K) (_ : Module ℂ K) (R : Submodule ℂ K)
          (Sop tA tB : K →ₗ[ℂ] K) (Ψ : ι → K) (Ω : ι → ℂ) (κ : ℂ),
          κ ≠ 0 ∧ Ω v0 ≠ 0 ∧
          (∀ r ∈ R, Sop r ∈ R) ∧
          (∀ x, Sop (Ψ x) = ∑ y, D.repS x y • Ψ y) ∧
          (∀ x, tB (Sop (Ψ x)) = Sop (tA (Ψ x))) ∧
          (∀ x, tA (Ψ x) - Ω x • Ψ x ∈ R) ∧
          (∀ x, tB (Ψ x) - ∑ z, (κ * transferMatrix c β x z) • Ψ z ∈ R) ∧
          (∀ e : ι → ℂ, ∑ z, e z • Ψ z ∈ R → e = 0)

/-- **Assembly**: Huang's genus-one data give (G1). -/
theorem vacuumChannelTransportInput_of_functionsInput
    (h : VacuumChannelFunctionsInput.{u, w}) : VacuumChannelTransportInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0 F H a b c β hβ
  obtain ⟨K, _, _, R, Sop, tA, tB, Ψ, Ω, κ, hκ, hΩ, hSR, hS, hcomm, hA, hB, hind⟩ :=
    h 𝒱 W hNice ι D hZ hirr hcomp v0 hv0 F H a b c β hβ
  refine ⟨fun x => Ω x / κ, div_ne_zero hΩ hκ, fun x z => ?_⟩
  exact vacuumChannelTransport_of_functions R Sop tA tB Ψ D.repS (transferMatrix c β) Ω κ hκ
    hSR hS hcomm hA hB hind x z

/-- The converse, with a trivial witness: the Prop is exactly as strong as (G1). -/
theorem functionsInput_of_vacuumChannelTransportInput
    (h : VacuumChannelTransportInput.{u, w}) : VacuumChannelFunctionsInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp v0 hv0 F H a b c β hβ
  obtain ⟨Ω, hΩ, hrow⟩ := h 𝒱 W hNice ι D hZ hirr hcomp v0 hv0 F H a b c β hβ
  classical
  let S : Matrix ι ι ℂ := Matrix.of D.repS
  let B : Matrix ι ι ℂ := Matrix.of (transferMatrix c β)
  let e : ι → (ι → ℂ) := fun x => Pi.single x 1
  have hvec : ∀ (M : Matrix ι ι ℂ) (x : ι), Matrix.vecMul (e x) M = ∑ y, M x y • e y := by
    intro M x
    funext z
    simp only [e, Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨ι → ℂ, inferInstance, inferInstance, ⊥, Matrix.vecMulLinear S,
    Matrix.vecMulLinear (Matrix.diagonal Ω), Matrix.vecMulLinear B, e, Ω, 1, one_ne_zero, hΩ,
    fun r hr => by rw [Submodule.mem_bot] at hr ⊢; rw [hr, map_zero], fun x => ?_, fun x => ?_,
    fun x => ?_, fun x => ?_, fun f hf => ?_⟩
  · exact hvec S x
  · -- `T_B (S e_x) = S (T_A e_x)` is the (G1) identity row by row
    simp only [Matrix.coe_vecMulLinear]
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hvec, hvec]
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 1
    rw [Matrix.diagonal_mul]
    simp only [S, B, Matrix.mul_apply, Matrix.of_apply]
    exact hrow x z
  · simp only [Matrix.coe_vecMulLinear]
    rw [hvec]
    have : ∑ y, Matrix.diagonal Ω x y • e y = Ω x • e x := by
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _ hy; simp [Matrix.diagonal_apply_ne _ (Ne.symm hy)]
      · intro hx; exact absurd (Finset.mem_univ x) hx
    rw [this, sub_self]; exact Submodule.zero_mem _
  · simp only [Matrix.coe_vecMulLinear, one_mul]
    rw [hvec]
    simp [B]
  · rw [Submodule.mem_bot] at hf
    funext z
    have := congrFun hf z
    simpa [e, Pi.single_apply] using this

/-- The function-space form is exactly (G1). -/
theorem functionsInput_iff : VacuumChannelFunctionsInput.{u, w} ↔
    VacuumChannelTransportInput.{u, w} :=
  ⟨vacuumChannelTransportInput_of_functionsInput, functionsInput_of_vacuumChannelTransportInput⟩

end VOA.Huang.GenusOneG1
