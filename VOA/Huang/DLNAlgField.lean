import VOA.Huang.DLNAlgWord
import Mathlib.FieldTheory.Galois.Basic

/-!
# The missing twist law suffices for descent of S

This is a conditional algebraic descent theorem. Over a finite Galois defining
field, a square-Galois twist law forces S to lie in every intermediate field
containing T and S squared. Taking that field to contain a primitive root at
the order of T gives the desired conductor bound. The twist law is NOT
deduced from Verlinde or from the signed-row law.
-/

noncomputable section

namespace VOA.Huang.DLNAlg

open Matrix

/-- A monoid calculation underlying descent. The two braid relations and the
equal squares make a multiplier commuting with T trivial. -/
theorem multiplier_eq_one {M : Type*} [Monoid M] (S T U G S' : M)
    (hS : IsUnit S) (hU : IsUnit U)
    (hb : S * T * S = U * S * U) (hb' : S' * T * S' = U * S' * U)
    (hsq : S' * S' = S * S) (hrow : S' = G * S) (hcomm : G * T = T * G) : G = 1 := by
  have hconj : G * S * G = S := by
    apply hS.mul_right_cancel
    calc
      (G * S * G) * S = (G * S) * (G * S) := by simp only [mul_assoc]
      _ = S * S := by rw [← hrow]; exact hsq
  have hleft : (G * S) * T * (G * S) = S * T * S := by
    calc
      (G * S) * T * (G * S) = G * S * (T * G) * S := by simp only [mul_assoc]
      _ = G * S * (G * T) * S := by rw [← hcomm]
      _ = (G * S * G) * T * S := by simp only [mul_assoc]
      _ = S * T * S := by rw [hconj]
  have he : U * S * U = U * (G * S) * U := by
    rw [← hb, ← hleft, ← hrow]
    exact hb'
  have hg : S = G * S := hU.mul_left_cancel (hU.mul_right_cancel he)
  apply hS.mul_right_cancel
  simpa using hg.symm

variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Field L]

/-- Entrywise automorphism fixes S once it fixes T, S squared, and satisfies
the square-Galois twist relation. Inverses are supplied as U to avoid any
unspoken invertibility requirement for matrix inversion. -/
theorem map_S_eq_of_map_T_eq (S T U : Matrix ι ι L) (σ : L ≃+* L)
    (hS : IsUnit S) (hU : IsUnit U) (hb : S * T * S = U * S * U)
    (hT : T.map σ = T) (hUi : U.map σ = U)
    (hC : (S * S).map σ = S * S) (G : Matrix ι ι L)
    (hrow : S.map σ = G * S)
    (htwist : (T.map σ).map σ * G = G * T) : S.map σ = S := by
  have hb' : S.map σ * T * S.map σ = U * S.map σ * U := by
    have hh := congrArg (fun A : Matrix ι ι L => A.map σ) hb
    simpa only [Matrix.map_mul, hT, hUi] using hh
  have hsq : S.map σ * S.map σ = S * S := by
    simpa only [Matrix.map_mul] using hC
  have hc : G * T = T * G := by simpa only [hT] using htwist.symm
  have hg := multiplier_eq_one S T U G (S.map σ) hS hU hb hb' hsq hrow hc
  simpa only [hg, one_mul] using hrow

variable [Algebra ℚ L]

/-- DLN's extra square-Galois twist law on a specified defining field.
This is a predicate on S and T, not a claim for arbitrary modular data. -/
def GaloisTwistLaw (S T : Matrix ι ι L) : Prop :=
  ∀ σ : L ≃ₐ[ℚ] L, ∃ G : Matrix ι ι L,
    S.map σ = G * S ∧ (T.map σ).map σ * G = G * T

/-- The field descent step. It needs neither cyclotomicity nor a congruence
kernel: finite Galois theory and the explicit twist law suffice. -/
theorem S_entries_mem_of_twist [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (K : IntermediateField ℚ L) (S T U : Matrix ι ι L)
    (hS : IsUnit S) (hU : IsUnit U) (hb : S * T * S = U * S * U)
    (hT : ∀ i j, T i j ∈ K) (hUi : ∀ i j, U i j ∈ K)
    (hC : ∀ i j, (S * S) i j ∈ K) (htwist : GaloisTwistLaw S T) :
    ∀ i j, S i j ∈ K := by
  intro i j
  rw [← IsGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have fix : ∀ x ∈ K, σ x = x := (IntermediateField.mem_fixingSubgroup_iff K σ).mp hσ
  obtain ⟨G, hrow, htw⟩ := htwist σ
  have he := map_S_eq_of_map_T_eq S T U σ.toRingEquiv hS hU hb
    (by ext a b; exact fix _ (hT a b))
    (by ext a b; exact fix _ (hUi a b))
    (by ext a b; exact fix _ (hC a b)) G hrow htw
  exact congrFun (congrFun he i) j

/-- The descent theorem applied to a genuine modular-group representation.
Charge conjugation is retained as membership of `rho(-1)` in the base field. -/
theorem repS_entries_mem_of_twist [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (K : IntermediateField ℚ L) (ρ : VOA.Huang.DLN.SL2Z →* Matrix ι ι L)
    (hT : ∀ i j, ρ ModularGroup.T i j ∈ K)
    (hTi : ∀ i j, ρ ModularGroup.T⁻¹ i j ∈ K)
    (hC : ∀ i j, ρ (-1) i j ∈ K)
    (htwist : GaloisTwistLaw (ρ ModularGroup.S) (ρ ModularGroup.T)) :
    ∀ i j, ρ ModularGroup.S i j ∈ K := by
  have hb : ModularGroup.S * ModularGroup.T * ModularGroup.S =
      ModularGroup.T⁻¹ * ModularGroup.S * ModularGroup.T⁻¹ := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
        Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_fin_two]
  have hSS : ModularGroup.S * ModularGroup.S = -1 := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact congrFun (congrFun ModularGroup.S_mul_S_eq i) j
  apply S_entries_mem_of_twist K (ρ ModularGroup.S) (ρ ModularGroup.T)
    (ρ ModularGroup.T⁻¹) ((Group.isUnit _).map ρ) ((Group.isUnit _).map ρ)
  · simpa only [map_mul] using congrArg ρ hb
  · exact hT
  · exact hTi
  · simpa only [← map_mul, hSS] using hC
  · exact htwist

/-- An explicit conductor-field version: diagonal entries and inverse entries
are powers of `zeta`, and the square of S has integral entries. If `zeta` is
a primitive N-th root, the conclusion is membership in the N-th cyclotomic
field inside L. No claim that the twist law follows from Verlinde is made. -/
theorem S_entries_mem_adjoin_of_twist [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (S T U : Matrix ι ι L) (ζ : L) (e : ι → ℤ) (C : Matrix ι ι ℤ)
    (hS : IsUnit S) (hU : IsUnit U) (hb : S * T * S = U * S * U)
    (hT : T = Matrix.diagonal (fun i => ζ ^ e i))
    (hUi : U = Matrix.diagonal (fun i => ζ ^ (-e i)))
    (hC : S * S = C.map (Int.castRingHom L)) (htwist : GaloisTwistLaw S T) :
    ∀ i j, S i j ∈ IntermediateField.adjoin ℚ ({ζ} : Set L) := by
  let K : IntermediateField ℚ L := IntermediateField.adjoin ℚ ({ζ} : Set L)
  have hz : ζ ∈ K := IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)
  apply S_entries_mem_of_twist K S T U hS hU hb
  · intro i j
    rw [hT]
    by_cases h : i = j
    · subst j; simpa using K.pow_mem hz (e i)
    · simp [h]
  · intro i j
    rw [hUi]
    by_cases h : i = j
    · subst j; simpa using K.pow_mem hz (-e i)
    · simp [h]
  · intro i j
    rw [hC]
    exact K.intCast_mem (C i j)
  · exact htwist

end VOA.Huang.DLNAlg
