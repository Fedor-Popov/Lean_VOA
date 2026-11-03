import VOA.Classification.COne.OrbIcoZVacuum
import VOA.Classification.COne.OrbIcoZSymbolic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Actual nonzero bottom spaces supply conformal eigenfunctionals on Zhu's algebra. -/
set_option Elab.async false
set_option maxSynthPendingDepth 3
noncomputable section
namespace VOA.Classification.COne.OrbIcoZ
open VOA VertexOperatorAlgebra OrbZhu OrbB5 OrbIco Polynomial

/-- This is extracted from an actual bottom vector, with no dimension or exhaustion assumption. -/
theorem exists_bottomEigenfunctional {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule Wi M) {h : ℂ} (hl : IsLowestWeight N h) (hne : N.weight h ≠ ⊥) :
    ∃ f : A Wi →ₗ[ℂ] ℂ, f (mk Wi Wi.vacuum) = 1 ∧
      ∀ z, f (omegaL Wi z) = h * f z := by
  obtain ⟨x, hx, hxn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  let v : N.weight h := ⟨x, hx⟩
  have hv : v ≠ 0 := by
    intro he
    exact hxn (congrArg Subtype.val he)
  obtain ⟨l, hlv⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  let f : A Wi →ₗ[ℂ] ℂ :=
    { toFun := fun z => l (actA N hl z v)
      map_add' := fun z t => by simp [map_add, LinearMap.add_apply]
      map_smul' := fun c z => by simp [map_smul, LinearMap.smul_apply] }
  refine ⟨f, ?_, ?_⟩
  · change l (actA N hl (VOA.one Wi) v) = 1
    rw [actA_one, Module.End.one_apply]
    exact hlv
  · intro z
    have he := actA_omegaL_pow N hl 1 z
    have he' : actA N hl (omegaL Wi z) = h • actA N hl z := by simpa using he
    change l (actA N hl (omegaL Wi z) v) = h * l (actA N hl z v)
    rw [he', LinearMap.smul_apply, map_smul, smul_eq_mul]

theorem exists_topEigenfunctional {M : Type} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule Wi M) {h : ℂ} (hl : IsLowestWeight N h) (hne : N.weight h ≠ ⊥) :
    ∃ f : A Wi →ₗ[ℂ] ℂ, f (selfMode 71) ≠ 0 ∧
      ∀ z, f (omegaL Wi z) = h * f z := by
  obtain ⟨f, hf1, hf⟩ := exists_bottomEigenfunctional N hl hne
  obtain ⟨c, hc, he⟩ := self_top_Zhu_nonzero
  refine ⟨f, ?_, hf⟩
  rw [he, map_smul, smul_eq_mul, hf1, mul_one]
  exact hc

section
variable (h : ℂ) (f : A Wi →ₗ[ℂ] ℂ)
    (hf : ∀ z, f (omegaL Wi z) = h * f z)
include hf

theorem eigenfunctional_aeval (P : ℂ[X]) (z : A Wi) :
    f (aeval (omegaL Wi) P z) = P.eval h * f z := by
  have hp (n : ℕ) : ∀ z, f ((omegaL Wi ^ n) z) = h^n * f z := by
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ', Module.End.mul_apply, hf, ih, pow_succ']
      ring
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add, LinearMap.add_apply, map_add, hP, hQ, Polynomial.eval_add, add_mul]
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, smul_eq_mul, hp, Polynomial.eval_monomial]
    ring

def scalarSym (k : ℤ) (a : ℤ → A Wi) : SymRel → ℂ
  | [] => 0
  | p :: r => (bivarEval k p.2).eval h * f (a (k - p.1)) + scalarSym k a r

theorem scalarSym_sound (k : ℤ) (a : ℤ → A Wi) (r : SymRel) :
    f (evalSym Wi k a r) = scalarSym h f k a r := by
  induction r with
  | nil => simp [evalSym, scalarSym]
  | cons p r ih =>
    rw [evalSym, map_add, eigenfunctional_aeval h f hf, ih, scalarSym]

end
end VOA.Classification.COne.OrbIcoZ
