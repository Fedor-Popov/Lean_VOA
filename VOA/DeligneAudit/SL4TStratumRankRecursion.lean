import VOA.DeligneAudit.SL4TStratumPowerLayers

/-! # The dimension recursion for the full-flag stratum quotient -/

namespace VOA.DeligneAudit.SL4T

noncomputable section

attribute [local instance 2000] Fin.fintype Fin.instOfNat

variable {A : Type*} [CommRing A] [Algebra ℂ A]

omit [CommRing A] [Algebra ℂ A] in
/-- Reindexing a selected alphabet changes its list only by a permutation. -/
theorem selectedAlphabet_map_perm {B D : ℕ} (Y : Finset (Fin B))
    (e : Fin B ↪ Fin D) (x : Fin D → A) :
    ((Y.map e).toList.map x).Perm (Y.toList.map fun a => x (e a)) := by
  classical
  have hp : (Y.map e).toList.Perm (Y.toList.map e) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _)
      ((Finset.nodup_toList _).map e.injective)).mpr
    intro a
    simp
  simpa only [List.map_map, Function.comp_def] using hp.map x

/-- The stratum relations give the refined dimension recursion in any generated algebra. -/
theorem stratumRootPowerFiltration_finrank_le [FiniteDimensional ℂ A] {B : ℕ}
    (x : Fin (B + 1) → A) (Y : Finset (Fin B)) (N k j : ℕ)
    (hN : 0 < N) (hlen : B + 1 = N + k) (hk : k ≤ N)
    (he : D4Levi.ksEPoly (List.ofFn x) = 1) (hx : ∀ a, x a ^ N = 0)
    (hm : ∀ cols : Fin j → ℕ,
      remainderTopMinor (Y.toList.map fun a => x a.succ) N j cols = 0)
    (hg : Function.Surjective (MvPolynomial.aeval x : MvPolynomial (Fin (B + 1)) ℂ →ₐ[ℂ] A)) :
    Module.finrank ℂ A ≤
      k * Module.finrank ℂ (FullFlagStratumRing B N j Y) +
        (N - k) * Module.finrank ℂ (FullFlagStratumRing B (N - 1) j Y) := by
  rw [rootPowerFiltration_finrank (x 0) N (hx 0)]
  calc
    _ ≤ ∑ i ∈ Finset.range N, if i < k then
        Module.finrank ℂ (FullFlagStratumRing B N j Y)
        else Module.finrank ℂ (FullFlagStratumRing B (N - 1) j Y) := by
      apply Finset.sum_le_sum
      intro i hi
      split_ifs with hik
      · exact stratumRootPowerLayer_rank_le x Y N j i he hx hm hg
      · exact stratumRootPowerLayer_lower_rank_le x Y N k j i hN hlen he hx
          (by omega) hm hg
    _ = _ := by
      rw [show Finset.range N = Finset.range (k + (N - k)) by congr 1; omega,
        Finset.sum_range_add]
      have hleft : (∑ i ∈ Finset.range k, if i < k then
          Module.finrank ℂ (FullFlagStratumRing B N j Y)
          else Module.finrank ℂ (FullFlagStratumRing B (N - 1) j Y)) =
          k * Module.finrank ℂ (FullFlagStratumRing B N j Y) := by
        simp [Finset.sum_ite_of_true (fun i hi => Finset.mem_range.mp hi)]
      rw [hleft]
      simp

/-- Deleting the first root outside the subalphabet gives the two smaller stratum bounds. -/
theorem fullFlagStratum_finrank_recursion (B N k j : ℕ) (Y : Finset (Fin B))
    (hN : 0 < N) (hlen : B + 1 = N + k) (hk : k ≤ N) :
    Module.finrank ℂ (FullFlagStratumRing (B + 1) N j (Y.map (Fin.succEmb B))) ≤
      k * Module.finrank ℂ (FullFlagStratumRing B N j Y) +
        (N - k) * Module.finrank ℂ (FullFlagStratumRing B (N - 1) j Y) := by
  let Z := Y.map (Fin.succEmb B)
  let x := fullFlagStratumRoot (B + 1) N j Z
  letI := fullFlagStratum_finite (B + 1) N j Z
  apply stratumRootPowerFiltration_finrank_le x Y N k j hN hlen hk
    (fullFlagStratum_elementary _ _ _ _) (fullFlagStratumRoot_pow _ _ _ _)
  · intro cols
    have hp := selectedAlphabet_map_perm Y (Fin.succEmb B) x
    exact (remainderTopMinor_perm hp N j cols).symm.trans
      (fullFlagStratum_minor_zero _ _ _ _ cols)
  · rw [fullFlagStratum_aeval]
    exact Ideal.Quotient.mkₐ_surjective ℂ _

end

end VOA.DeligneAudit.SL4T

#print axioms VOA.DeligneAudit.SL4T.selectedAlphabet_map_perm
#print axioms VOA.DeligneAudit.SL4T.stratumRootPowerFiltration_finrank_le
#print axioms VOA.DeligneAudit.SL4T.fullFlagStratum_finrank_recursion
