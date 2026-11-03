import VOA.Huang.LogHuangODEProductSpan
import VOA.Modules.LogModuleC1Dual

/-! The actual generalized dual-C1 cutoff supplies bounded Nat-level
transpose-mode reduction in every lower generalized-weight coset. -/
set_option maxSynthPendingDepth 3
namespace VOA.Huang.LogHuangODEProduct
open VOA VOA.C2Rigid VOA.LogTensor
open scoped BigOperators
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}

/-- The genuine restricted-dual C1 theorem gives precisely the graded data
needed by the regular product descent, with no semisimple premise. -/
theorem exists_DualC1Graded (hC2 : C2Cofinite W) (N : LogVModule W M)
    (hfg : FinGen N.toWeakModule) {h : ℂ} (hl : CosetBase N.toGW h) :
    ∃ B : ℕ, DualC1Graded N.toGW h B := by
  obtain ⟨b,hb⟩ := ModuleC2.dualC1_generalized_cutoff hC2 N hfg
  let B : ℕ := Nat.ceil (b-h.re)+1
  refine ⟨B,?_⟩
  intro n hn f
  have hre : b < (h+(n : ℂ)).re := by
    have hc : b-h.re ≤ (Nat.ceil (b-h.re) : ℝ) := Nat.le_ceil _
    have hnr : (B : ℝ)<n := by exact_mod_cast hn
    simp only [Complex.add_re,Complex.natCast_re]
    dsimp [B] at hnr
    push_cast at hnr
    linarith
  let S : Submodule ℂ (Module.Dual ℂ (N.weight (h+n))) := Submodule.span ℂ
    {φ | ∃ (d m : ℕ) (v : V) (g : M →ₗ[ℂ] ℂ), 1 ≤ d ∧ 2 * d ≤ m + 1 ∧ m + 1 - d ≤ n ∧
      v∈W.grading (d : ℤ) ∧ φ=(g ∘ₗ mode (N.YM v) (m : ℤ)).domRestrict (N.weight (h+n))}
  change f.domRestrict (N.weight (h+n))∈S
  refine Submodule.span_induction (p := fun φ _ => φ∈S) ?_
    S.zero_mem (fun φ ψ _ _ hφ hψ => S.add_mem hφ hψ)
    (fun c φ _ hφ => S.smul_mem c hφ) (hb (h+n) hre f)
  rintro φ ⟨d,m,v,g,hd,hm,hv,rfl⟩
  have hd0 : 0 ≤ d := by omega
  have hm0 : 0 ≤ m := by omega
  have hdc : (d.toNat : ℤ)=d := Int.toNat_of_nonneg hd0
  have hmc : (m.toNat : ℤ)=m := Int.toNat_of_nonneg hm0
  by_cases hmn : m + 1 - d ≤ (n : ℤ)
  · apply Submodule.subset_span
    refine ⟨d.toNat,m.toNat,v,g,by omega,by omega,by omega,?_,?_⟩
    · simpa only [hdc] using hv
    · simp only [hmc]
  · have hz : (g ∘ₗ mode (N.YM v) m).domRestrict (N.weight (h+n))=0 := by
      ext x
      change g (mode (N.YM v) m (x : M))=0
      have hw := N.mode_mem_weight hv x.property m
      have hx0 : mode (N.YM v) m (x : M)=0 :=
        eq_zero_of_mem_weight_neg hl hw (j := (n : ℤ)+d-m-1)
          (by push_cast; ring) (by omega)
      rw [hx0,map_zero]
    rw [hz]
    exact S.zero_mem

end VOA.Huang.LogHuangODEProduct
