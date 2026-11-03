import VOA.Classification.COne.OrbPrimUnitary
import VOA.Classification.COne.OrbPrimGlue
import VOA.Classification.COne.FeiginFuchsLower
import VOA.Moonshine.LatticeGradedDim

/-! # OrbPrim (H1a): the Virasoro primary spectrum of `V₂`, proved

`primSpectrumBound_V2 : PrimSpectrumBound (V2m 1 le_rfl)`: `V₂ = V_{√2ℤ}` has no Virasoro
primaries off the squares, and at most `2n + 1` independent primaries in weight `n²`.

Proof.
* `V2_dim_eq`: `dim (V₂)_n = Σ_{k ≤ n} e_k · dim L(1,k)_{n-k}` with `e_{μ²} = 2μ + 1` and
  `e_k = 0` off the squares. Both sides equal `p(n) + 2 Σ_{μ ≥ 1, μ² ≤ n} p(n - μ²)`:
  the left side by the lattice dimension formula (`finrank_gradingLatGen_eq_sum`,
  `fockCount_one_eq_card_partition`); the right side by Feigin--Fuchs
  (`dim L(1,μ²)_m = p(m) - p(m - 2μ - 1)`, `virC1RadicalLevelBound_holds`), the non-square
  Verma irreducibility (`vermaSimpleLevel_one_finrank_of_not_sq`) and telescoping.
* `finrank_prim_le_of_unitary` (`OrbPrimUnitary`) with the Fock-space unitary form
  `OrbSpan.v2VirUnitary_holds`.
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbPrim
open VOA VertexOperatorAlgebra OrbSpan Finset VOA.InverseDS.VirasoroVerma VOA.LatGen
  VOA.LatGen.Triplet
open scoped Classical

/-- `p(n)`, the number of partitions (the library's Verma PBW count). -/
abbrev pc (n : ℕ) : ℕ := Fintype.card (VermaPartitions n)

/-- `p` extended by zero to `ℤ`. -/
def Pz (t : ℤ) : ℤ := if t < 0 then 0 else (pc t.toNat : ℤ)

theorem Pz_of_neg {t : ℤ} (ht : t < 0) : Pz t = 0 := if_pos ht

theorem Pz_natCast (m : ℕ) : Pz (m : ℤ) = pc m := by
  rw [Pz, if_neg (by omega), Int.toNat_natCast]

/-- The multiplicities `e_{μ²} = 2μ + 1`, `e_k = 0` off the squares. -/
def eV2 (k : ℕ) : ℕ := if Nat.sqrt k ^ 2 = k then 2 * Nat.sqrt k + 1 else 0

/-! ## Characters of `L(1, k)` -/

theorem ell_sq (μ n : ℕ) (h : μ ^ 2 ≤ n) :
    (Module.finrank ℂ (vermaSimpleLevel 1 ((μ ^ 2 : ℕ) : ℂ) (n - μ ^ 2)) : ℤ) =
      Pz ((n : ℤ) - (μ : ℤ) ^ 2) - Pz ((n : ℤ) - ((μ : ℤ) + 1) ^ 2) := by
  have hcast : (n : ℤ) - (μ : ℤ) ^ 2 = ((n - μ ^ 2 : ℕ) : ℤ) := by push_cast [h]; ring
  rw [hcast, Pz_natCast]
  by_cases hlow : n - μ ^ 2 ≤ 2 * μ
  · rw [Pz_of_neg (by nlinarith), sub_zero,
      vermaSimpleLevel_finrank_of_det_ne_zero 1 _ (n - μ ^ 2)
        (vermaGramMatrix_one_sq_det_ne_zero μ hlow)]
  · obtain ⟨m, hm⟩ : ∃ m, n - μ ^ 2 = 2 * μ + 1 + m := ⟨n - μ ^ 2 - (2 * μ + 1), by omega⟩
    have hcast2 : (n : ℤ) - ((μ : ℤ) + 1) ^ 2 = (m : ℤ) := by
      have : (n : ℤ) = (μ : ℤ) ^ 2 + 2 * μ + 1 + m := by
        have h' : n = μ ^ 2 + (2 * μ + 1 + m) := by omega
        rw [h']; push_cast; ring
      rw [this]; ring
    rw [hcast2, Pz_natCast, hm]
    have e1 := vermaSimpleLevel_finrank_add_radicalLevel 1 ((μ ^ 2 : ℕ) : ℂ) (2 * μ + 1 + m)
    have e2 := virC1RadicalLevelBound_holds μ m
    have e3 := card_le_finrank_vermaRadicalLevel_one_sq μ m
    unfold pc
    omega

/-! ## Telescoping and symmetric sums -/

theorem telescope (a : ℕ → ℤ) (M : ℕ) :
    ∑ μ ∈ range (M + 1), (2 * (μ : ℤ) + 1) * (a μ - a (μ + 1)) =
      a 0 + ∑ i ∈ range M, 2 * a (i + 1) - (2 * (M : ℤ) + 1) * a (M + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    push_cast; ring

theorem sum_Icc_symm (H : ℤ → ℤ) (M : ℕ) :
    ∑ t ∈ Icc (-(M : ℤ)) M, H t = H 0 + ∑ i ∈ range M, (H ((i : ℤ) + 1) + H (-((i : ℤ) + 1))) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hset : Icc (-((M + 1 : ℕ) : ℤ)) ((M + 1 : ℕ) : ℤ) =
        insert (-((M : ℤ) + 1)) (insert ((M : ℤ) + 1) (Icc (-(M : ℤ)) M)) := by
      ext t; simp only [mem_Icc, mem_insert]; push_cast; omega
    rw [hset, sum_insert (by simp only [mem_insert, mem_Icc]; omega),
      sum_insert (by simp only [mem_Icc]; omega), ih, sum_range_succ]
    ring

/-! ## Both sides of the dimension identity -/

theorem rhs_eq (n : ℕ) :
    ((∑ k ∈ range (n + 1), eV2 k *
        Module.finrank ℂ (vermaSimpleLevel 1 (k : ℂ) (n - k)) : ℕ) : ℤ) =
      Pz n + ∑ i ∈ range n, 2 * Pz ((n : ℤ) - ((i : ℤ) + 1) ^ 2) := by
  -- restrict to squares
  have h1 : ∑ k ∈ range (n + 1), eV2 k * Module.finrank ℂ (vermaSimpleLevel 1 (k : ℂ) (n - k)) =
      ∑ μ ∈ (range (n + 1)).filter (fun μ => μ ^ 2 ≤ n),
        (2 * μ + 1) * Module.finrank ℂ (vermaSimpleLevel 1 ((μ ^ 2 : ℕ) : ℂ) (n - μ ^ 2)) := by
    rw [← sum_filter_add_sum_filter_not (range (n + 1)) (fun k => Nat.sqrt k ^ 2 = k)]
    rw [sum_eq_zero (s := (range (n + 1)).filter (fun k => ¬ Nat.sqrt k ^ 2 = k))
      (fun k hk => by rw [eV2, if_neg (mem_filter.mp hk).2, zero_mul]), add_zero]
    refine sum_nbij' (fun k => Nat.sqrt k) (fun μ => μ ^ 2) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [mem_filter, mem_range] at hk ⊢
      refine ⟨?_, by rw [hk.2]; omega⟩
      have := Nat.sqrt_le_self k; omega
    · intro μ hμ
      simp only [mem_filter, mem_range] at hμ ⊢
      refine ⟨?_, by rw [Nat.sqrt_eq']⟩
      have : μ ≤ μ ^ 2 := by nlinarith
      omega
    · intro k hk
      simp only [mem_filter, mem_range] at hk
      exact hk.2
    · intro μ _; exact Nat.sqrt_eq' μ
    · intro k hk
      simp only [mem_filter, mem_range] at hk
      rw [eV2, if_pos hk.2, hk.2]
  rw [h1]
  push_cast
  calc ∑ μ ∈ (range (n + 1)).filter (fun μ => μ ^ 2 ≤ n), (2 * (μ : ℤ) + 1) *
        (Module.finrank ℂ (vermaSimpleLevel 1 ((μ ^ 2 : ℕ) : ℂ) (n - μ ^ 2)) : ℤ)
      = ∑ μ ∈ (range (n + 1)).filter (fun μ => μ ^ 2 ≤ n), (2 * (μ : ℤ) + 1) *
          (Pz ((n : ℤ) - (μ : ℤ) ^ 2) - Pz ((n : ℤ) - ((μ : ℤ) + 1) ^ 2)) :=
        sum_congr rfl (fun μ hμ => by rw [ell_sq μ n (mem_filter.mp hμ).2])
    _ = ∑ μ ∈ range (n + 1), (2 * (μ : ℤ) + 1) *
          (Pz ((n : ℤ) - (μ : ℤ) ^ 2) - Pz ((n : ℤ) - ((μ : ℤ) + 1) ^ 2)) := by
        refine sum_filter_of_ne (fun μ _ hne => ?_)
        by_contra hμ
        apply hne
        have h2 : (n : ℤ) < (μ : ℤ) ^ 2 := by exact_mod_cast (not_le.mp hμ)
        have h3 : (μ : ℤ) ^ 2 ≤ ((μ : ℤ) + 1) ^ 2 := by nlinarith [Int.natCast_nonneg μ]
        rw [Pz_of_neg (by linarith), Pz_of_neg (by linarith), sub_zero, mul_zero]
    _ = Pz n + ∑ i ∈ range n, 2 * Pz ((n : ℤ) - ((i : ℤ) + 1) ^ 2) := by
        have ht := telescope (fun μ => Pz ((n : ℤ) - (μ : ℤ) ^ 2)) n
        push_cast at ht
        rw [ht, sub_zero, Pz_of_neg (show (n : ℤ) - ((n : ℤ) + 1) ^ 2 < 0 by nlinarith),
          mul_zero, sub_zero]

theorem fock_term (n : ℕ) (t : ℤ) (ht : halfNorm (latP 1) t ≤ n) :
    (fockCount 1 ((n : ℤ) - halfNorm (latP 1) t).toNat : ℤ) = Pz ((n : ℤ) - t ^ 2) := by
  rw [halfNorm_latP] at ht ⊢
  have ht' : t ^ 2 ≤ (n : ℤ) := by push_cast at ht; linarith
  rw [fockCount_one_eq_card_partition, ← card_vermaPartitions_eq,
    show ((n : ℤ) - ((1 : ℕ) : ℤ) * t ^ 2) = (n : ℤ) - t ^ 2 by push_cast; ring, Pz,
    if_neg (by linarith)]

theorem normLE_sub (n : ℕ) (t : ℤ) (ht : halfNorm (latP 1) t ≤ n) :
    t ∈ (Icc (-(n : ℤ)) n : Finset ℤ) := by
  rw [halfNorm_latP] at ht
  have ht' : t ^ 2 ≤ (n : ℤ) := by push_cast at ht; linarith
  have : |t| ≤ t ^ 2 := by
    rcases eq_or_ne t 0 with h0 | h0
    · rw [h0]; simp
    · have h1 : 1 ≤ |t| := Int.one_le_abs h0
      nlinarith [sq_abs t]
  rw [mem_Icc]
  constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]

theorem Pz_outside (n : ℕ) (t : ℤ) (ht : ¬ halfNorm (latP 1) t ≤ n) :
    Pz ((n : ℤ) - t ^ 2) = 0 := by
  rw [halfNorm_latP] at ht
  push Not at ht
  exact Pz_of_neg (by push_cast at ht; linarith)

theorem lhs_eq (n : ℕ) :
    (Module.finrank ℂ ((V2m 1 le_rfl).grading (n : ℤ)) : ℤ) =
      Pz n + ∑ i ∈ range n, 2 * Pz ((n : ℤ) - ((i : ℤ) + 1) ^ 2) := by
  change (Module.finrank ℂ (gradingLatGen (latP 1) ((n : ℕ) : ℤ)) : ℤ) = _
  rw [finrank_gradingLatGen_eq_sum (latP 1) (latP_posDef 1 le_rfl) n, rank_latP]
  push_cast
  refine (Finset.sum_congr rfl (g := fun t : ℤ => Pz ((n : ℤ) - t ^ 2)) (fun t ht =>
    fock_term n t ((mem_normLE _ _).mp ht))).trans ?_
  refine (Finset.sum_subset (s₂ := (Icc (-(n : ℤ)) n : Finset ℤ))
    (fun t ht => normLE_sub n t ((mem_normLE _ _).mp ht))
    (fun t _ ht => Pz_outside n t (fun h => ht ((mem_normLE _ _).mpr h)))).trans ?_
  rw [sum_Icc_symm]
  simp only [neg_sq, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  congr 1
  refine sum_congr rfl fun i _ => by ring

/-- **The graded dimension of `V₂` in Virasoro characters.** -/
theorem V2_dim_eq (n : ℕ) :
    Module.finrank ℂ ((V2m 1 le_rfl).grading (n : ℤ)) =
      ∑ k ∈ range (n + 1), eV2 k *
        Module.finrank ℂ (vermaSimpleLevel (V2m 1 le_rfl).centralCharge (k : ℂ) (n - k)) := by
  have hc : (V2m 1 le_rfl).centralCharge = 1 := by
    rw [V2m, latticeVOAGen_centralCharge, rank_latP]; simp
  rw [hc]
  have := (lhs_eq n).trans (rhs_eq n).symm
  exact_mod_cast this

/-- **(H1a) The Virasoro primary spectrum of `V₂`.** -/
theorem primSpectrumBound_V2 : PrimSpectrumBound (V2m 1 le_rfl) := by
  obtain ⟨U⟩ := v2VirUnitary_holds
  have key : ∀ N : ℕ, Module.finrank ℂ (prim (V2m 1 le_rfl) N) ≤ eV2 N := fun N =>
    finrank_prim_le_of_unitary U N eV2 (fun n _ => V2_dim_eq n)
  refine ⟨fun N hN => ?_, fun n => ?_⟩
  · by_cases hneg : N < 0
    · rw [eq_bot_iff]
      intro x hx
      have := ((mem_prim _).mp hx).1
      rwa [(V2m 1 le_rfl).positivity N hneg] at this
    · obtain ⟨N', rfl⟩ : ∃ N' : ℕ, N = (N' : ℤ) := ⟨N.toNat, by omega⟩
      have he : eV2 N' = 0 := by
        rw [eV2, if_neg]
        intro hsq
        exact hN (Nat.sqrt N') (by exact_mod_cast hsq)
      have h0 := key N'
      rw [he, Nat.le_zero] at h0
      haveI : FiniteDimensional ℂ ((V2m 1 le_rfl).grading (N' : ℤ)) := (V2m 1 le_rfl).finrank _
      haveI : FiniteDimensional ℂ (prim (V2m 1 le_rfl) (N' : ℤ)) :=
        Submodule.finiteDimensional_of_le inf_le_left
      exact Submodule.finrank_eq_zero.mp h0
  · have h := key (n ^ 2)
    rw [eV2, if_pos (by rw [Nat.sqrt_eq']), Nat.sqrt_eq'] at h
    have hc : ((n ^ 2 : ℕ) : ℤ) = (n : ℤ) ^ 2 := by push_cast; ring
    rw [hc] at h
    exact h

end VOA.Classification.COne.OrbPrim
