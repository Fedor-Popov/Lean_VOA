import VOA.Examples.VirasoroVacuumEvaluation
import VOA.Examples.LeeYangTransferAssemblySimple

/-! # The conformal Virasoro map, without coset identification

A conformal vector in any VOA defines a homomorphism from the universal
Virasoro vacuum VOA. The product assertion follows from the iterate identity
and creation-word spanning, so it is not an additional reconstruction input.
-/

namespace VOA.LeeYangShortcut

open VirModule VirSimple VirDeformModes

noncomputable section

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- The Virasoro representation already present in a VOA. -/
def conformalData (W : VertexOperatorAlgebra E) : CentralVirasoroData E where
  L := W.L
  central := W.centralCharge • 1
  comm m n := by
    rw [W.L_virasoro]
    by_cases h : m + n = 0 <;> simp [h, smul_smul]
  central_comm n := by
    change (W.centralCharge • (1 : Module.End ℂ E)) * W.L n = _
    simp

/-- Universal evaluation at the vacuum for a specified matching charge. -/
def conformalEval (W : VertexOperatorAlgebra E) {c : ℂ}
    (hc : W.centralCharge = c) : VirUniv c →ₗ[ℂ] E :=
  (fixedVacuum (conformalData W) (by simp [conformalData, hc]) W.vacuum
    (fun n hn => by
      change W.L n W.vacuum = 0
      rw [VertexOperatorAlgebra.L_def, ← PreVertexAlgebra.smul_def]
      exact W.toPreVertexAlgebra.smul_vacuum_nonneg _ (by omega))).eval

@[simp] theorem conformalEval_vacuum (W : VertexOperatorAlgebra E) {c : ℂ}
    (hc : W.centralCharge = c) : conformalEval W hc (vacVec c) = W.vacuum :=
  VacuumVirasoroRealization.eval_vacuum _

/-- Universal evaluation intertwines every Virasoro mode. -/
theorem conformalEval_L (W : VertexOperatorAlgebra E) {c : ℂ}
    (hc : W.centralCharge = c) (n : ℤ) (v : VirUniv c) :
    conformalEval W hc (Lop c n v) = W.L n (conformalEval W hc v) := by
  unfold conformalEval
  rw [show Lop c n = virVacRho c (VOA.L n) from rfl,
    VacuumVirasoroRealization.eval_action]
  change fixedRho (conformalData W) (by simp [conformalData, hc]) (VOA.L n) _ = _
  rw [fixedRho_L]
  rfl

@[simp] theorem conformalEval_conformal (W : VertexOperatorAlgebra E) {c : ℂ}
    (hc : W.centralCharge = c) :
    conformalEval W hc (virasoroVOA c).conformalVector = W.conformalVector := by
  change conformalEval W hc (Lop c (-2) (vacVec c)) = _
  rw [conformalEval_L, conformalEval_vacuum, VertexOperatorAlgebra.L_def,
    ← PreVertexAlgebra.smul_def]
  exact W.smul_vacuum_neg_one _

private def iterateTerm {X : Type*} [AddCommGroup X] [Module ℂ X]
    (V : VertexOperatorAlgebra X) (a b x : X) (l n i : ℤ) : X :=
  (negOnePow i * cbz l i) • (V.smul a (l - i) (V.smul b (n + i) x) -
    negOnePow l • V.smul b (l + n - i) (V.smul a i x))

private theorem iterateTerm_finite {X : Type*} [AddCommGroup X] [Module ℂ X]
    (V : VertexOperatorAlgebra X) (a b x : X) (l n : ℤ) :
    Function.HasFiniteSupport (iterateTerm V a b x l n) := by
  obtain ⟨N0, h0⟩ := V.toPreVertexAlgebra.smul_eventually_zero b x
  obtain ⟨N1, h1⟩ := V.toPreVertexAlgebra.smul_eventually_zero a x
  refine (Set.finite_Icc 0 (max (N0 - n) N1)).subset ?_
  intro i hi
  rw [Function.mem_support] at hi
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · simp [iterateTerm, cbz_apply_neg l h]
  · simp [iterateTerm, h0 (n + i) (by omega), h1 i (by omega)]

private theorem iterateTerm_sum {X : Type*} [AddCommGroup X] [Module ℂ X]
    (V : VertexOperatorAlgebra X) (a b x : X) (l n : ℤ) :
    (∑ᶠ i, iterateTerm V a b x l n i) = V.smul (V.smul a l b) n x := by
  have h := V.jacobi a b x l 0 n
  conv_rhs at h =>
    rw [finsum_eq_single _ (0 : ℤ)
      (fun i hi => by rw [cbz_zero_left, if_neg hi, zero_smul])]
  simpa [iterateTerm, cbz_zero_left] using h

/-- States whose fields are intertwined by a specified linear map. -/
def intertwinedStates {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (V : VertexOperatorAlgebra X)
    (W : VertexOperatorAlgebra Y) (f : X →ₗ[ℂ] Y) : Submodule ℂ X where
  carrier := {a | ∀ n x, f (V.smul a n x) = W.smul (f a) n (f x)}
  zero_mem' := by intro n x; simp
  add_mem' := by
    intro a b ha hb n x
    simp only [PreVertexAlgebra.smul_add_left, map_add, ha n x, hb n x]
  smul_mem' := by
    intro r a ha n x
    simp only [PreVertexAlgebra.smul_smul_left, map_smul, ha n x]

/-- Jacobi propagates field intertwining from two states to every product of them. -/
theorem intertwinedStates_product {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (V : VertexOperatorAlgebra X)
    (W : VertexOperatorAlgebra Y) (f : X →ₗ[ℂ] Y) {a b : X}
    (ha : a ∈ intertwinedStates V W f) (hb : b ∈ intertwinedStates V W f) (l : ℤ) :
    V.smul a l b ∈ intertwinedStates V W f := by
  intro n x
  rw [ha l b, ← iterateTerm_sum, ← iterateTerm_sum,
    map_finsum f (iterateTerm_finite V a b x l n)]
  apply finsum_congr
  intro i
  change ∀ n x, f (V.smul a n x) = W.smul (f a) n (f x) at ha
  change ∀ n x, f (V.smul b n x) = W.smul (f b) n (f x) at hb
  simp only [iterateTerm, map_smul, map_sub, ha, hb]

/-- The universal evaluation preserves all vertex products. -/
theorem conformalEval_hom (W : VertexOperatorAlgebra E) {c : ℂ}
    (hc : W.centralCharge = c) :
    IsVOAHom (virasoroVOA c) W (conformalEval W hc) := by
  let F := conformalEval W hc
  let S := intertwinedStates (virasoroVOA c) W F
  have hvac : vacVec c ∈ S := by
    intro n x
    change F ((virasoroVOA c).smul (virasoroVOA c).vacuum n x) = _
    rw [PreVertexAlgebra.smul_vacuum_left]
    change F (if n = -1 then x else 0) = W.smul (conformalEval W hc (vacVec c)) n (F x)
    rw [conformalEval_vacuum, PreVertexAlgebra.smul_vacuum_left]
    split_ifs <;> simp
  have homega : (virasoroVOA c).conformalVector ∈ S := by
    intro n x
    change conformalEval W hc ((virasoroVOA c).smul _ n x) = _
    rw [conformalEval_conformal]
    have hh := conformalEval_L W hc (n - 1) x
    rw [← virasoroVOA_L_eq_Lop] at hh
    simpa only [VertexOperatorAlgebra.L_def,
      sub_add_cancel, PreVertexAlgebra.smul_def] using hh
  have hw (w : List ℕ) : negWordVir c w ∈ S := by
    induction w with
    | nil => exact hvac
    | cons i w ih =>
      rw [negWordVir_cons]
      have hh := intertwinedStates_product (virasoroVOA c) W F homega ih (-(i : ℤ) - 1)
      simpa only [← virasoroVOA_L_eq_Lop, VertexOperatorAlgebra.L_def,
        PreVertexAlgebra.smul_def, show -(i : ℤ) - 2 + 1 = -(i : ℤ) - 1 by omega] using hh
  have htop : S = ⊤ := by
    apply top_unique
    rw [← negSpanVir_eq_top c, negSpanVir]
    exact Submodule.span_le.mpr (by rintro _ ⟨w, rfl⟩; exact hw w)
  refine ⟨conformalEval_vacuum W hc, fun a n x => ?_⟩
  have ha : a ∈ S := by rw [htop]; trivial
  exact ha n x

/-- Universal evaluation preserves each homogeneous weight. -/
theorem conformalEval_grading (W : VertexOperatorAlgebra E) {c : ℂ}
    (hc : W.centralCharge = c) {n : ℤ} {x : VirUniv c}
    (hx : x ∈ (virasoroVOA c).grading n) :
    conformalEval W hc x ∈ W.grading n := by
  apply LeeYangTransferAssembly.mem_grading_of_L_zero W
  rw [← (conformalEval_hom W hc).map_L (conformalEval_conformal W hc),
    (virasoroVOA c).L_zero_grading x hx, map_smul]

/-- The concrete Virasoro map defined by the actual coset stress tensor. -/
def virasoroToCoset : VirUniv LeeYang.leeYangC →ₗ[ℂ] Sl2CosetConcrete.CosetSpace :=
  conformalEval Sl2CosetConcrete.cosetVOA rfl

/-- No external coset identification is needed for the VOA map. -/
theorem virasoroToCoset_hom :
    IsVOAHom (virasoroVOA LeeYang.leeYangC) Sl2CosetConcrete.cosetVOA virasoroToCoset :=
  conformalEval_hom Sl2CosetConcrete.cosetVOA rfl

@[simp] theorem virasoroToCoset_vacuum :
    virasoroToCoset (vacVec LeeYang.leeYangC) = Sl2CosetConcrete.cosetVOA.vacuum :=
  conformalEval_vacuum Sl2CosetConcrete.cosetVOA rfl

@[simp] theorem virasoroToCoset_conformal :
    virasoroToCoset (virasoroVOA LeeYang.leeYangC).conformalVector =
      Sl2CosetConcrete.cosetVOA.conformalVector :=
  conformalEval_conformal Sl2CosetConcrete.cosetVOA rfl

end
end VOA.LeeYangShortcut
