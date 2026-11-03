import VOA.Huang.GenusOneBlockSpace
import VOA.Huang.GenusOneTraceSpace

/-!
# Finite interpolation and the remaining trace-spanning obligation

An analytic insertion block is determined by finitely many numbers at any one
point of the upper half-plane. Consequently trace spanning reduces to realization
of this finite initial-value data. The realization itself remains open; Miyamoto,
math/0010180, Theorem 4.15 proves it by cusp expansion and Lemmas 4.10–4.14.
-/
namespace VOA.Huang.GenusOne
open VOA Complex
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M}

/-- Restriction discards the unconstrained values outside the upper half-plane. -/
noncomputable def insertionRestrict :
    (M → ℂ → ℂ) →ₗ[ℂ] (M → UpperHalfPlane → ℂ) where
  toFun F w τ := F w τ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def insertionBlockSpace (A : OrdVModule W M) : Submodule ℂ (M → UpperHalfPlane → ℂ) :=
  (insertionAnalyticBlocks A).map insertionRestrict

/-- A fixed finite set determines every block at every point of the upper half-plane. -/
def InsertionDetermining (A : OrdVModule W M) (U : Finset M) : Prop :=
  ∀ F : M → ℂ → ℂ, IsInsertionAnalyticBlock A F →
    ∀ z₀ ∈ imGT 0, (∀ w ∈ U, F w z₀ = 0) →
      ∀ w z, z ∈ imGT 0 → F w z = 0

theorem exists_insertionDetermining (hAC2 : FusionC2.ModuleC2Cofinite A.toWeakModule) :
    ∃ U : Finset M, InsertionDetermining A U :=
  exists_finite_insertion_determining_set hAC2

noncomputable def insertionBlockEval (U : Finset M) (τ : UpperHalfPlane) :
    insertionBlockSpace A →ₗ[ℂ] (U → ℂ) where
  toFun F w := F.val w.val τ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem insertionBlockEval_injective {U : Finset M} (hU : InsertionDetermining A U)
    (τ : UpperHalfPlane) : Function.Injective (insertionBlockEval (A := A) U τ) := by
  intro f g he
  obtain ⟨F, hF, hFr⟩ := Submodule.mem_map.mp f.property
  obtain ⟨G, hG, hGr⟩ := Submodule.mem_map.mp g.property
  have hF' : IsInsertionAnalyticBlock A F := hF
  have hG' : IsInsertionAnalyticBlock A G := hG
  have hzero := hU _ (hF'.sub hG') (τ : ℂ) τ.im_pos (fun w hw => by
    have hew := congrFun he (⟨w, hw⟩ : U)
    change f.val w τ = g.val w τ at hew
    have hfw := congrFun (congrFun hFr w) τ
    have hgw := congrFun (congrFun hGr w) τ
    change F w (τ : ℂ) = f.val w τ at hfw
    change G w (τ : ℂ) = g.val w τ at hgw
    exact sub_eq_zero.mpr (hfw.trans (hew.trans hgw.symm)))
  apply Subtype.ext
  funext w σ
  have hfw := congrFun (congrFun hFr w) σ
  have hgw := congrFun (congrFun hGr w) σ
  change F w (σ : ℂ) = f.val w σ at hfw
  change G w (σ : ℂ) = g.val w σ at hgw
  exact hfw.symm.trans ((sub_eq_zero.mp (hzero w σ σ.im_pos)).trans hgw)

/-- Finite dimensionality of all analytic blocks, not just the trace subspace. -/
theorem finiteDimensional_insertionBlockSpace
    (hAC2 : FusionC2.ModuleC2Cofinite A.toWeakModule) :
    FiniteDimensional ℂ (insertionBlockSpace A) := by
  classical
  obtain ⟨U, hU⟩ := exists_insertionDetermining hAC2
  exact FiniteDimensional.of_injective (insertionBlockEval U ⟨Complex.I, by simp⟩)
    (insertionBlockEval_injective hU _)

theorem finrank_insertionBlockSpace_le {U : Finset M} (hU : InsertionDetermining A U)
    (τ : UpperHalfPlane) : Module.finrank ℂ (insertionBlockSpace A) ≤ U.card := by
  classical
  simpa using LinearMap.finrank_le_finrank_of_injective
    (insertionBlockEval_injective hU τ)

variable {ι : Type u} [Fintype ι]

/-- Narrower realization target: match finitely many insertion values at one point.
This is a consequence of Miyamoto Theorem 4.15 for the intended complete family;
no modular transformation or analytic equality on a domain is part of this target. -/
def InsertionTraceInterpolation (A : OrdVModule W M) (Mfam : ι → IrrModule W)
    (h : ι → ℂ) (U : Finset M) (τ₀ : UpperHalfPlane) : Prop :=
  ∀ F : M → ℂ → ℂ, IsInsertionAnalyticBlock A F →
    ∃ Z : ∀ j, IntertwiningOperator A (Mfam j).isMod (Mfam j).isMod,
      ∀ w ∈ U, F w (τ₀ : ℂ) = ∑ j, traceFunction (Z j) (h j) w τ₀

theorem insertionTraceInterpolation_of_spanning (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hspan : InsertionTraceSpanning A Mfam h) (U : Finset M) (τ₀ : UpperHalfPlane) :
    InsertionTraceInterpolation A Mfam h U τ₀ := by
  intro F hF
  obtain ⟨Z, hZ⟩ := hspan F hF
  exact ⟨Z, fun w _ => hZ w τ₀⟩

/-- Analytic determinacy upgrades finite initial-value realization to full trace spanning. -/
theorem insertionTraceSpanning_of_interpolation (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    {U : Finset M} (hU : InsertionDetermining A U) (τ₀ : UpperHalfPlane)
    (hint : InsertionTraceInterpolation A Mfam h U τ₀) :
    InsertionTraceSpanning A Mfam h := by
  classical
  intro F hF
  obtain ⟨Z, hZ⟩ := hint F hF
  let G : M → ℂ → ℂ := ∑ i, anEval (trace (Z i)) (h i - W.centralCharge / 24)
  have hG : IsInsertionAnalyticBlock A G :=
    (insertionAnalyticBlocks A).sum_mem fun i _ =>
      isInsertionAnalyticBlock_trace_of_irreducible hC2 hA (Z i) (hcw i)
  have hGeq (w : M) (τ : UpperHalfPlane) : G w τ = ∑ i, traceFunction (Z i) (h i) w τ := by
    simp only [G, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [anEval_of_mem _ _ _ τ.im_pos, qEvalC_coe]
    rfl
  have hzero := hU _ (hF.sub hG) (τ₀ : ℂ) τ₀.im_pos
    (fun w hw => sub_eq_zero.mpr ((hZ w hw).trans (hGeq w τ₀).symm))
  exact ⟨Z, fun w τ => (sub_eq_zero.mp (hzero w τ τ.im_pos)).trans (hGeq w τ)⟩

/-- A lossless finite-data reduction: the determining set is produced from C₂. -/
theorem exists_insertionTraceSpanning_iff_interpolation (hC2 : C2Cofinite W)
    (hA : A.IsIrreducible) (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i)) :
    ∃ U : Finset M, InsertionDetermining A U ∧ ∀ τ₀ : UpperHalfPlane,
      (InsertionTraceSpanning A Mfam h ↔ InsertionTraceInterpolation A Mfam h U τ₀) := by
  obtain ⟨U, hU⟩ := exists_insertionDetermining (moduleC2_of_irreducible hC2 hA)
  exact ⟨U, hU, fun τ₀ => ⟨fun hs => insertionTraceInterpolation_of_spanning Mfam h hs U τ₀,
    fun hi => insertionTraceSpanning_of_interpolation hC2 hA Mfam h hcw hU τ₀ hi⟩⟩

end VOA.Huang.GenusOne
