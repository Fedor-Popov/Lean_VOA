import VOA.DeligneAudit.D4LevelReductionGradeFiltration
import Mathlib.Tactic.Module
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! The node-one fundamental coweight on the radical key filtration. -/

namespace VOA.DeligneAudit.D4LevelReduction

open VOA.DeligneAudit.SectorWeyl
open VOA.DeligneAudit.UnivG
open VOA.DeligneAudit.DeligneSector.D4
open VOA.DeligneAudit.DeligneSector.Sparse
open VOA.DeligneAudit.D4Levi

/-- The vector-node coweight of a current colour. -/
def currentAlphaGrade : Fin 28 → ℤ
  | 7 | 10 | 12 | 13 | 14 | 15 => 1
  | 19 | 22 | 24 | 25 | 26 | 27 => -1
  | _ => 0

set_option maxHeartbeats 8000000 in
/-- The doubled fundamental coweight has the prescribed adjoint eigenvalues. -/
theorem doubledGradeCartan_coefficients : ∀ a z : Fin 28,
    2 * fZ br 0 a z + 2 * fZ br 1 a z + fZ br 2 a z + fZ br 3 a z =
      if z = a then 2 * currentAlphaGrade a else 0 := by
  decide +kernel

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (ρ : CurrentModule D4sector.f V)

/-- Twice the zero-mode action of the node-one fundamental coweight. -/
noncomputable def doubledGradeCartan : V →ₗ[ℂ] V :=
  (2 : ℂ) • ρ.op (0 : Fin 28) 0 + (2 : ℂ) • ρ.op (1 : Fin 28) 0 +
    ρ.op (2 : Fin 28) 0 + ρ.op (3 : Fin 28) 0

/-- Each current shifts the intrinsic vector-node grade by its root coefficient. -/
theorem doubledGradeCartan_comm (a : Fin 28) (r : ℕ) (v : V) :
    doubledGradeCartan ρ (ρ.op a r v) - ρ.op a r (doubledGradeCartan ρ v) =
      (2 * (currentAlphaGrade a : ℂ)) • ρ.op a r v := by
  have hc (z : Fin 28) :
      2 * D4sector.f (0 : Fin 28) a z + 2 * D4sector.f (1 : Fin 28) a z +
        D4sector.f (2 : Fin 28) a z + D4sector.f (3 : Fin 28) a z =
          if z = a then 2 * (currentAlphaGrade a : ℂ) else 0 := by
    change 2 * fD4 0 a z + 2 * fD4 1 a z + fD4 2 a z + fD4 3 a z = _
    simpa only [fD4, fC, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_ite,
      Int.cast_zero] using
      congrArg (fun n : ℤ => (n : ℂ)) (doubledGradeCartan_coefficients a z)
  calc
    _ = (2 : ℂ) • (ρ.op (0 : Fin 28) 0 (ρ.op a r v) - ρ.op a r (ρ.op (0 : Fin 28) 0 v)) +
        (2 : ℂ) • (ρ.op (1 : Fin 28) 0 (ρ.op a r v) - ρ.op a r (ρ.op (1 : Fin 28) 0 v)) +
        (ρ.op (2 : Fin 28) 0 (ρ.op a r v) - ρ.op a r (ρ.op (2 : Fin 28) 0 v)) +
        (ρ.op (3 : Fin 28) 0 (ρ.op a r v) - ρ.op a r (ρ.op (3 : Fin 28) 0 v)) := by
          simp only [doubledGradeCartan, LinearMap.add_apply, LinearMap.smul_apply,
            map_add, map_smul]
          module
    _ = ∑ z : Fin 28,
        (2 * D4sector.f (0 : Fin 28) a z + 2 * D4sector.f (1 : Fin 28) a z +
          D4sector.f (2 : Fin 28) a z + D4sector.f (3 : Fin 28) a z) • ρ.op z r v := by
      rw [ρ.comm, ρ.comm, ρ.comm, ρ.comm]
      simp only [zero_add, Finset.smul_sum, smul_smul, ← Finset.sum_add_distrib,
        ← add_smul]
      rfl
    _ = _ := by simp only [hc, ite_smul, zero_smul]; simp

/-- The reductive Levi preserves the vector-node coweight eigenspaces. -/
theorem doubledGradeCartan_comm_levi (a : Fin 28) (ha : IsLevi a) (r : ℕ) (v : V) :
    doubledGradeCartan ρ (ρ.op a r v) = ρ.op a r (doubledGradeCartan ρ v) := by
  have hz : currentAlphaGrade a = 0 := by
    obtain ⟨i, rfl⟩ := ha
    fin_cases i <;> rfl
  have hc := doubledGradeCartan_comm ρ a r v
  simpa only [hz, Int.cast_zero, mul_zero, zero_smul, sub_eq_zero] using hc

variable (w : V)

/-- Every radical key has its recorded intrinsic vector-node grade. -/
theorem doubledGradeCartan_key (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0))
    (k : RadicalKey) {v : V} (hv : v ∈ keyLayer ρ w k) :
    doubledGradeCartan ρ v = (2 * (keyAlphaGrade m k : ℂ)) • v := by
  have hzero := extra_weight_key ρ w m h k hv
  have hone := cartan_weight_key ρ w m h 1 k hv
  have htwo := cartan_weight_key ρ w m h 0 k hv
  have hthree := cartan_weight_key ρ w m h 2 k hv
  change ρ.op (1 : Fin 28) 0 v = _ at hone
  change ρ.op (2 : Fin 28) 0 v = _ at htwo
  change ρ.op (3 : Fin 28) 0 v = _ at hthree
  simp only [doubledGradeCartan, LinearMap.add_apply, LinearMap.smul_apply,
    hzero, hone, htwo, hthree, smul_smul, ← add_smul]
  congr 1
  simp [extraLabel, keyLabel, keyAlphaGrade, keyDepth]
  ring

/-- Levi words preserve the coweight eigenvalue of their input. -/
theorem doubledGradeCartan_leviWord (l : List (Fin 28 × ℕ))
    (hl : l.Forall (fun p => IsLevi p.1)) (v : V) :
    doubledGradeCartan ρ (wordOp ρ l v) = wordOp ρ l (doubledGradeCartan ρ v) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.forall_cons] at hl
    change doubledGradeCartan ρ (ρ.op x.1 x.2 (wordOp ρ l v)) = _
    rw [doubledGradeCartan_comm_levi ρ x.1 hl.1, ih hl.2]
    rfl

/-- A complete Levi key orbit lies in one intrinsic grade eigenspace. -/
theorem keyOrbit_le_gradeEigenspace (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (k : RadicalKey) :
    keyOrbit ρ w k ≤
      Module.End.eigenspace (doubledGradeCartan ρ) (2 * (keyAlphaGrade m k : ℂ)) := by
  rw [keyOrbit, Submodule.span_le]
  rintro v ⟨l, r, hl, hk, rfl⟩
  apply Module.End.mem_eigenspace_iff.mpr
  change doubledGradeCartan ρ (wordOp ρ (l ++ r.map fun p => (radicalColour p.1, p.2)) w) =
    (2 * (keyAlphaGrade m k : ℂ)) •
      wordOp ρ (l ++ r.map fun p => (radicalColour p.1, p.2)) w
  erw [wordOp_append ρ l (r.map fun p => (radicalColour p.1, p.2)) w]
  change doubledGradeCartan ρ (wordOp ρ l (radicalWord ρ w r)) = _
  rw [doubledGradeCartan_leviWord ρ l hl,
    doubledGradeCartan_key ρ w m h k (hk ▸ radicalWord_mem_key ρ w r), wordOp_smul]
  rfl

/-- The radical letter-count layer has the intrinsic coweight eigenvalue. -/
theorem alphaLayer_le_gradeEigenspace (m : ℕ)
    (h : Sat D4sector.f ρ w (ravFam D4sector m 0)) (κ : ℤ) :
    alphaLayer ρ w m κ ≤ Module.End.eigenspace (doubledGradeCartan ρ) (2 * (κ : ℂ)) := by
  apply iSup_le
  intro k
  apply iSup_le
  intro _
  apply iSup_le
  intro hk
  simpa only [hk] using keyOrbit_le_gradeEigenspace ρ w m h k

end VOA.DeligneAudit.D4LevelReduction

#print axioms VOA.DeligneAudit.D4LevelReduction.doubledGradeCartan_comm
#print axioms VOA.DeligneAudit.D4LevelReduction.doubledGradeCartan_key
#print axioms VOA.DeligneAudit.D4LevelReduction.keyOrbit_le_gradeEigenspace
#print axioms VOA.DeligneAudit.D4LevelReduction.alphaLayer_le_gradeEigenspace
