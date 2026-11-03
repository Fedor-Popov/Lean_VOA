import VOA.DeligneAudit.SL4TFullFlagFinite
import VOA.DeligneAudit.SL4TFiniteFiltrationRank

/-! # Dimension accounting for the filtration by powers of a root -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

variable {A : Type*} [CommRing A]

/-- The annihilator presentation of one successive root-power layer. -/
def rootPowerLayerIdeal (z : A) (i : ℕ) : Ideal A :=
  (Ideal.span {z ^ (i + 1)}).colon {z ^ i}

theorem root_mem_powerLayerIdeal (z : A) (i : ℕ) : z ∈ rootPowerLayerIdeal z i := by
  apply Submodule.mem_colon_singleton.mpr
  change z * z ^ i ∈ Ideal.span {z ^ (i + 1)}
  rw [← pow_succ']
  exact Ideal.subset_span rfl

theorem rootPowerLayerIdeal_mem (z x : A) (i : ℕ) :
    x ∈ rootPowerLayerIdeal z i ↔ x * z ^ i ∈ Ideal.span {z ^ (i + 1)} :=
  Submodule.mem_colon_singleton

variable [Algebra ℂ A]

/-- The dimension of a power ideal splits into the next ideal and the annihilator quotient. -/
theorem rootPowerLayer_finrank [FiniteDimensional ℂ A] (z : A) (i : ℕ) :
    Module.finrank ℂ (Ideal.span {z ^ i}) =
      Module.finrank ℂ (Ideal.span {z ^ (i + 1)}) +
        Module.finrank ℂ (A ⧸ rootPowerLayerIdeal z i) := by
  let S := (Ideal.span {z ^ i}).restrictScalars ℂ
  let T := (Ideal.span {z ^ (i + 1)}).restrictScalars ℂ
  let f := T.mkQ.comp (LinearMap.mul ℂ A (z ^ i))
  have hk : LinearMap.ker f = (rootPowerLayerIdeal z i).restrictScalars ℂ := by
    ext x
    change T.mkQ (z ^ i * x) = 0 ↔ x ∈ rootPowerLayerIdeal z i
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      rootPowerLayerIdeal_mem, mul_comm]
    rfl
  have hr : LinearMap.range f = S.map T.mkQ := by
    rw [LinearMap.range_comp, Ideal.range_mul]
  have he := f.quotKerEquivRange.finrank_eq
  rw [hk, hr] at he
  have hTS : T ≤ S := by
    apply Ideal.span_le.mpr
    rintro x rfl
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hs := submodule_finrank_sup_eq S T
  rw [sup_of_le_left hTS, ← he] at hs
  exact hs

/-- Summing all power layers recovers the dimension of a finite algebra
when the root is nilpotent. -/
theorem rootPowerFiltration_finrank [FiniteDimensional ℂ A] (z : A) (N : ℕ)
    (hz : z ^ N = 0) :
    Module.finrank ℂ A =
      ∑ i ∈ Finset.range N, Module.finrank ℂ (A ⧸ rootPowerLayerIdeal z i) := by
  have hsum : ∀ n, Module.finrank ℂ A =
      (∑ i ∈ Finset.range n, Module.finrank ℂ (A ⧸ rootPowerLayerIdeal z i)) +
        Module.finrank ℂ (Ideal.span {z ^ n}) := by
    intro n
    induction n with
    | zero =>
        rw [Finset.sum_range_zero, zero_add, pow_zero, Ideal.span_singleton_one]
        exact ((Submodule.topEquiv : (⊤ : Submodule A A) ≃ₗ[A] A).restrictScalars
          ℂ).finrank_eq.symm
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, rootPowerLayer_finrank z n]
        omega
  have ht := hsum N
  rw [hz, Ideal.span_singleton_zero] at ht
  have hzero : Module.finrank ℂ (⊥ : Ideal A) = 0 :=
    Module.finrank_zero_of_subsingleton
  simpa only [hzero, add_zero] using ht

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.root_mem_powerLayerIdeal
#print axioms VOA.DeligneAudit.SL4T.rootPowerLayerIdeal_mem
#print axioms VOA.DeligneAudit.SL4T.rootPowerLayer_finrank
#print axioms VOA.DeligneAudit.SL4T.rootPowerFiltration_finrank
