import VOA.DeligneAudit.D4FusionToroidalFusionD4
import VOA.DeligneAudit.DeligneFusionD1TensorGCyclic

/-!
# Cyclicity of the pure toroidal evaluation tensor

Lagrange interpolation separates local `u` currents at distinct `t` points.
The checked one-site cyclicity then spans the tensor product.
-/

namespace VOA.DeligneAudit.Toroidal

open VOA.DeligneAudit.D1TensorG VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.DeligneSector.D4

noncomputable section

variable (S : DeligneSectorData)
variable (hskew : ∀ a b c, S.f a b c = -S.f b a c)
variable {N : ℕ} (z : Fin N → ℂ)

def evalCyclic : Submodule ℂ (D1TensorG.Space S.n N) :=
  Submodule.span ℂ (Set.range fun l : List (TLtr S.n) =>
    evalWord (d1EvalAction S.f S.jacobi hskew z) l (D1TensorG.generator S.c₀))

theorem evalCyclic_generator :
    D1TensorG.generator S.c₀ ∈ evalCyclic S hskew z :=
  Submodule.subset_span ⟨[], rfl⟩

theorem evalCyclic_op (c : Fin S.n) (i s : ℕ) :
    evalCyclic S hskew z ≤ (evalCyclic S hskew z).comap
      ((d1EvalAction S.f S.jacobi hskew z).op c i s) := by
  rw [evalCyclic, Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  exact Submodule.subset_span ⟨(c, i, s) :: l, rfl⟩

/-- Distinct evaluation points separate the action at every site. -/
theorem evalCyclic_local (hz : Function.Injective z) (q : Fin N)
    (c : Fin S.n) (i : ℕ) :
    evalCyclic S hskew z ≤ (evalCyclic S hskew z).comap
      (localOp q ((D1SiteG.rep S.f S.jacobi hskew).op c i)) := by
  let B : Fin N → Module.End ℂ (D1TensorG.Space S.n N) := fun j =>
    localOp j ((D1SiteG.rep S.f S.jacobi hskew).op c i)
  have hinv : ∀ s, evalCyclic S hskew z ≤ (evalCyclic S hskew z).comap
      (JetInterpolation.jetOp z B (fun _ => 0) s) := by
    intro s
    have heq : JetInterpolation.jetOp z B (fun _ => 0) s =
        (d1EvalAction S.f S.jacobi hskew z).op c i s := by
      simp [JetInterpolation.jetOp, B, d1EvalAction_op, D1SiteG.rep]
    rw [heq]
    exact evalCyclic_op S hskew z c i s
  exact (JetInterpolation.invariant_jetOp_iff z hz B (fun _ => 0)
    (evalCyclic S hskew z)).mp hinv |>.1 q

private theorem localOp_insert (q : Fin N) (A : Module.End ℂ (D1SiteG.Space S.n))
    (v : Fin N → D1SiteG.Space S.n) (x : D1SiteG.Space S.n) :
    localOp q A ((PiTensorProduct.tprod ℂ).toLinearMap v q x) =
      (PiTensorProduct.tprod ℂ).toLinearMap v q (A x) := by
  change localOp q A (PiTensorProduct.tprod ℂ (Function.update v q x)) = _
  rw [localOp_tprod]
  simp only [Function.update_self, Function.update_idem,
    MultilinearMap.toLinearMap_apply]

/-- The checked site word certificate and local invariance span all tensors. -/
theorem evalCyclic_top (hz : Function.Injective z) :
    evalCyclic S hskew z = ⊤ := by
  have hsite := D1SiteG.cyclic_top S.f S.jacobi hskew S.c₀ S.depth S.cyclic
  let P := evalCyclic S hskew z
  have hpartial : ∀ T : Finset (Fin N), ∀ v : Fin N → D1SiteG.Space S.n,
      PiTensorProduct.tprod ℂ
        (fun q => if q ∈ T then v q else D1SiteG.w S.c₀) ∈ P := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro v
        simpa only [Finset.notMem_empty, if_false] using
          evalCyclic_generator S hskew z
    | @insert q T hq ih =>
        intro v
        let base : Fin N → D1SiteG.Space S.n := fun j =>
          if j ∈ T then v j else D1SiteG.w S.c₀
        let E : D1SiteG.Space S.n →ₗ[ℂ] D1TensorG.Space S.n N :=
          (PiTensorProduct.tprod ℂ).toLinearMap base q
        have hbase : base q = D1SiteG.w S.c₀ := by simp only [base, if_neg hq]
        have hword : ∀ l : List (Fin S.n × ℕ),
            E (wordOp (D1SiteG.rep S.f S.jacobi hskew) l (D1SiteG.w S.c₀)) ∈ P := by
          intro l
          induction l with
          | nil =>
              change PiTensorProduct.tprod ℂ
                (Function.update base q (D1SiteG.w S.c₀)) ∈ P
              rw [← hbase, Function.update_eq_self]
              exact ih v
          | cons a l ihl =>
              change E ((D1SiteG.rep S.f S.jacobi hskew).op a.1 a.2
                (wordOp (D1SiteG.rep S.f S.jacobi hskew) l (D1SiteG.w S.c₀))) ∈ P
              rw [← localOp_insert S q]
              exact evalCyclic_local S hskew z hz q a.1 a.2 ihl
        have hmap : D1SiteG.cyclic S.f S.jacobi hskew S.c₀ ≤ P.comap E := by
          rw [D1SiteG.cyclic, Submodule.span_le]
          rintro _ ⟨l, rfl⟩
          exact hword l
        have hx : E (v q) ∈ P := hmap (hsite ▸ Submodule.mem_top)
        have he : (fun j => if j ∈ insert q T then v j else D1SiteG.w S.c₀) =
            Function.update base q (v q) := by
          funext j
          by_cases hjq : j = q
          · subst j
            simp only [Finset.mem_insert_self, if_true, Function.update_self]
          · simp only [Finset.mem_insert, hjq, false_or, base,
              Function.update_of_ne hjq]
        rw [he]
        exact hx
  apply top_unique
  rw [← PiTensorProduct.span_tprod_eq_top]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, rfl⟩
  simpa only [Finset.mem_univ, if_true] using hpartial Finset.univ v

theorem d4_evalCyclic_top (N : ℕ) :
    evalCyclic D4sector D1SiteG.D4Check.table_skewC (D1TensorG.points N) = ⊤ :=
  evalCyclic_top D4sector D1SiteG.D4Check.table_skewC
    (D1TensorG.points N) (D1TensorG.points_injective N)

end

end VOA.DeligneAudit.Toroidal

#print axioms VOA.DeligneAudit.Toroidal.evalCyclic_local
#print axioms VOA.DeligneAudit.Toroidal.evalCyclic_top
#print axioms VOA.DeligneAudit.Toroidal.d4_evalCyclic_top
