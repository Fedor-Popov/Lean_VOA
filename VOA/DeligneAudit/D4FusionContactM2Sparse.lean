import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-! # Sparse integer coefficient identities and ideal-membership transport -/

namespace VOA.DeligneAudit.D4FusionContact.M2Certificate

open scoped BigOperators

noncomputable section

abbrev SparseRow (n : ℕ) := List (Fin n × ℤ)

def sparse {n : ℕ} (l : SparseRow n) (j : Fin n) : ℤ :=
  (l.map fun x => if j = x.1 then x.2 else 0).sum

def combine {n : ℕ} (l : List (ℤ × SparseRow n)) : Fin n → ℤ :=
  (l.map fun x => x.1 • sparse x.2).sum

variable {n : ℕ} {V : Type*} [AddCommGroup V]

def evalZ (b : Fin n → V) : (Fin n → ℤ) →ₗ[ℤ] V where
  toFun c := ∑ j, c j • b j
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem evalZ_single (b : Fin n → V) (j : Fin n) (c : ℤ) :
    evalZ b (fun i => if i = j then c else 0) = c • b j := by
  simp [evalZ, ite_smul]

theorem evalZ_sparse (b : Fin n → V) (l : SparseRow n) :
    evalZ b (sparse l) = (l.map fun x => x.2 • b x.1).sum := by
  induction l with
  | nil => simp [sparse, evalZ]
  | cons x l ih =>
      have he : sparse (x::l) = (fun j => if j = x.1 then x.2 else 0) + sparse l := by
        funext j
        simp only [sparse, List.map_cons, List.sum_cons, Pi.add_apply]
      rw [he, map_add, evalZ_single, ih]
      rfl

theorem evalZ_combine (b : Fin n → V) (l : List (ℤ × SparseRow n)) :
    evalZ b (combine l) = (l.map fun x => x.1 • evalZ b (sparse x.2)).sum := by
  induction l with
  | nil => simp [combine]
  | cons x l ih =>
      simp only [combine, List.map_cons, List.sum_cons] at ih ⊢
      rw [map_add, map_smul, ih]

variable [Module ℂ V]

/-- A checked integer row identity and nonzero normalization give
actual submodule membership. This is symbolic linear algebra; closed
certificate data are checked independently in small finite modules. -/
theorem row_mem_of_identity (P : Submodule ℂ V) (b : Fin n → V)
    (raw normal : SparseRow n) (earlier : List (ℤ × SparseRow n))
    (scale factor : ℤ) (hfactor : factor ≠ 0)
    (hid : scale • sparse raw = factor • sparse normal + combine earlier)
    (hraw : evalZ b (sparse raw) ∈ P)
    (hearlier : ∀ x ∈ earlier, evalZ b (sparse x.2) ∈ P) :
    evalZ b (sparse normal) ∈ P := by
  have hscale : scale • evalZ b (sparse raw) ∈ P := by
    simpa only [Int.cast_smul_eq_zsmul] using P.smul_mem (scale : ℂ) hraw
  have he := congrArg (evalZ b) hid
  simp only [map_smul, map_add] at he
  have hcomb : evalZ b (combine earlier) ∈ P := by
    rw [evalZ_combine]
    apply list_sum_mem
    intro v hv
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    simpa only [Int.cast_smul_eq_zsmul] using P.smul_mem (x.1 : ℂ) (hearlier x hx)
  have hn := P.sub_mem hscale hcomb
  rw [he, add_sub_cancel_right] at hn
  have hc : (factor : ℂ) • evalZ b (sparse normal) ∈ P := by
    simpa only [Int.cast_smul_eq_zsmul] using hn
  exact (Submodule.smul_mem_iff _ (by exact_mod_cast hfactor : (factor : ℂ) ≠ 0)).mp hc

end
end VOA.DeligneAudit.D4FusionContact.M2Certificate
