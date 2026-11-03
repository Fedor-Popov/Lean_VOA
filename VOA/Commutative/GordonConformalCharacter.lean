/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Commutative.GordonSectorTransport
import VOA.Commutative.GordonSectorCharacter
import VOA.Commutative.QSeriesNonnegative

/-! # The actual global auxiliary arc Hilbert bound

Canonical quotient sectors and the genuine pair/partition filtration inject
into the finite profile/residual cutoff of the literal Section 5 source sum.
Coefficient positivity justifies adding the unused terms.
-/
namespace VOA.GordonConformalCharacter
open scoped BigOperators
open VOA.BoundaryAuxiliary VOA.BoundaryAuxiliarySectors VOA.GordonPairTelescope
open VOA.GordonPartitionProfile VOA.GordonSectorTransport VOA.GordonSectorCharacter VOA.QSeries
noncomputable section

abbrev SectorIndex (m N : ℕ) := Σ t : Index N,
  Σ R : PairCount t.val.1.val t.val.2.1.val, Profile (m + 1) R.val

abbrev MasterIndex (m N : ℕ) := (↑(profileCutoff m N)) ×
  Fin (N + 1) × Fin (N + 1) × Fin (N + 1)

def sectorToMaster (m N : ℕ) (v : SectorIndex m N) : MasterIndex m N := by
  rcases v with ⟨t, R, r⟩
  have hRa := pairCount_le_left t.val.1.val t.val.2.1.val R
  have hRb := pairCount_le_right t.val.1.val t.val.2.1.val R
  have ht := t.property
  have hr : (∑ i, r.val i) ≤ R.val := by
    calc
      _ ≤ ∑ i, (i.val + 1) * r.val i :=
        Finset.sum_le_sum (fun i _ => by nlinarith [Nat.zero_le (r.val i)])
      _ = _ := r.property
  exact (⟨r.val, (mem_profileCutoff m N r.val).mpr (by omega)⟩,
    ⟨t.val.1.val - R.val, by omega⟩,
    ⟨t.val.2.1.val - R.val, by omega⟩,
    t.val.2.2)

/-- Sector labels are recovered from the profile and its three residual multiplicities. -/
theorem sectorToMaster_injective (m N : ℕ) : Function.Injective (sectorToMaster m N) := by
  rintro ⟨a, R, r⟩ ⟨b, S, s⟩ h
  have hr : r.val = s.val := congrArg (fun z : MasterIndex m N => z.1.val) h
  have he : a.val.1.val - R.val = b.val.1.val - S.val :=
    congrArg (fun z : MasterIndex m N => z.2.1.val) h
  have hf : a.val.2.1.val - R.val = b.val.2.1.val - S.val :=
    congrArg (fun z : MasterIndex m N => z.2.2.1.val) h
  have hh : a.val.2.2.val = b.val.2.2.val :=
    congrArg (fun z : MasterIndex m N => z.2.2.2.val) h
  have hR : R.val = S.val := by
    have hp := r.property
    have hq := s.property
    rw [hr] at hp
    exact hp.symm.trans hq
  have hRa := pairCount_le_left a.val.1.val a.val.2.1.val R
  have hRb := pairCount_le_right a.val.1.val a.val.2.1.val R
  have hSa := pairCount_le_left b.val.1.val b.val.2.1.val S
  have hSb := pairCount_le_right b.val.1.val b.val.2.1.val S
  have hab : a = b := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext; omega
    · apply Prod.ext
      · apply Fin.ext; omega
      · exact Fin.ext hh
  subst b
  have hRS : R = S := Fin.ext hR
  subst S
  have hrs : r = s := Subtype.ext hr
  subst s
  rfl

def masterTerm (m N : ℕ) (v : MasterIndex m N) : ℚ :=
  PowerSeries.coeff N (multiplicityResidualTerm (K := ℚ) v.1.val
    v.2.1.val v.2.2.1.val v.2.2.2.val)

theorem masterTerm_nonneg (m N : ℕ) (v : MasterIndex m N) : 0 ≤ masterTerm m N v :=
  nonnegativeCoefficients_multiplicityResidualTerm _ _ _ _ N

/-- Injecting a finite set of nonnegative summands into a larger finite set preserves the bound. -/
theorem sum_le_sum_of_injection {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : ι → κ) (hf : Function.Injective f) (g : κ → ℚ) (hg : ∀ j, 0 ≤ g j) :
    (∑ i, g (f i)) ≤ ∑ j, g j := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.image f, g j :=
      (Finset.sum_image (fun i _ j _ h => hf h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => hg j)

/-- The finite master index is precisely the cutoff proved for the literal source series. -/
theorem sum_masterTerm_eq_source (m N : ℕ) :
    (∑ v : MasterIndex m N, masterTerm m N v) =
      PowerSeries.coeff N (multiplicitySource (K := ℚ) m) := by
  rw [coeff_multiplicitySource]
  simp only [masterTerm, MasterIndex, Fintype.sum_prod_type, map_sum]
  rw [Finset.univ_eq_attach (profileCutoff m N),
    Finset.sum_attach (profileCutoff m N) (fun r : Fin (m + 1) → ℕ =>
      ∑ s : Fin (N + 1), ∑ t : Fin (N + 1), ∑ c : Fin (N + 1),
        PowerSeries.coeff N (multiplicityResidualTerm (K := ℚ) r s.val t.val c.val))]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => ∑ t : Fin (N + 1), ∑ c : Fin (N + 1),
    PowerSeries.coeff N (multiplicityResidualTerm (K := ℚ) r s t.val c.val))]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ => ∑ c : Fin (N + 1),
    PowerSeries.coeff N (multiplicityResidualTerm (K := ℚ) r s t c.val))]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Fin.sum_univ_eq_sum_range (fun c : ℕ =>
    PowerSeries.coeff N (multiplicityResidualTerm (K := ℚ) r s t c))]

/-- The full finite sector/profile sum is bounded by the actual literal source coefficient. -/
theorem sum_sectorProfiles_le_source (m N : ℕ) :
    (∑ t : Index N, ∑ R : PairCount t.val.1.val t.val.2.1.val,
      ∑ r : Profile (m + 1) R.val,
        PowerSeries.coeff N (multiplicityResidualTerm (K := ℚ) r.val
          (t.val.1.val - R.val) (t.val.2.1.val - R.val) t.val.2.2.val)) ≤
      PowerSeries.coeff N (multiplicitySource (K := ℚ) m) := by
  rw [← sum_masterTerm_eq_source]
  have h := sum_le_sum_of_injection (sectorToMaster m N) (sectorToMaster_injective m N)
    (masterTerm m N) (masterTerm_nonneg m N)
  simpa only [Fintype.sum_sigma, masterTerm, sectorToMaster] using h

/-- The global Gordon Hilbert bound for the actual auxiliary arc quotient. -/
theorem auxiliaryPiece_finrank_le_source {K : Type*} [Field K] [CharZero K] (m N : ℕ) :
    (Module.finrank K (auxiliaryPiece (K := K) (m + 1) N) : ℚ) ≤
      PowerSeries.coeff N (multiplicitySource (K := ℚ) m) := by
  have h := auxiliaryPiece_finrank_le_sum_original_sectors (K := K) (m + 1) N
  have hq := Nat.cast_le (α := ℚ).mpr h
  rw [Nat.cast_sum] at hq
  refine hq.trans ((Finset.sum_le_sum ?_).trans (sum_sectorProfiles_le_source m N))
  intro t _
  have hN : N - (t.val.1.val + t.val.2.1.val + t.val.2.2.val) +
      t.val.1.val + t.val.2.1.val + t.val.2.2.val = N := by have h := t.property; omega
  simpa only [hN] using sector_finrank_le_profile_sum (K := K) m
    (N - (t.val.1.val + t.val.2.1.val + t.val.2.2.val))
    t.val.1.val t.val.2.1.val t.val.2.2.val

/-- Sections 2--5 on the actual original arc presentation, evaluated as the
boundary product. No VOA relation or character premise enters this bound. -/
theorem sourcePiece_finrank_le_product {K : Type*} [Field K] [CharZero K] (m N : ℕ) :
    (Module.finrank K (sourcePiece (K := K) (m + 1) N) : ℚ) ≤
      PowerSeries.coeff N ((PowerSeries.expand (2 * (m + 1) + 1) (by omega) euler) ^ 3 *
        (reciprocalEuler : PowerSeries ℚ) ^ 3) := by
  have h := Nat.cast_le (α := ℚ).mpr
    (sourcePiece_finrank_le_auxiliaryPiece (K := K) (m + 1) N)
  have haux := auxiliaryPiece_finrank_le_source (K := K) m N
  rw [multiplicitySource_product] at haux
  exact h.trans haux

end
end VOA.GordonConformalCharacter
