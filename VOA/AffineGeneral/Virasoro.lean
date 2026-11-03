import VOA.AffineGeneral.SugawaraEnergy
import VOA.AffineGeneral.VARec
import VOA.Core.BorcherdsIdentity
/-!
# The actual sl3 Sugawara Virasoro algebra

*General-`𝔤` port* of `VOA/Examples/AffineSl3Virasoro.lean` (generated mechanically from that file):
the index type is `ι`, the Lie data is `D : LieData κ ι`, the dual Coxeter number is `D.h`.  Where the
text below says sl₃, `Fin 8`, `6` or `3`, read `𝔤`, `ι`, `2 * D.h` and `D.h`.

The generic vertex-algebra commutator theorem is reused from VARec;
all currents, tensors and scalar contractions here are those of sl3.
The trace contraction is eight and the adjoint Casimir is six, yielding
central charge 8k/(k+3). No higher-rank determinant statement is used.
-/
set_option maxHeartbeats 1600000
open VOA VOA.AffineGeneral VOA.AffineGeneral.SugawaraCov
open scoped BigOperators
open Module (End)
open VOA.AffineLie
namespace VOA.AffineGeneral

open LieData
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (D : LieData κ ι)

/-- The sl3 Sugawara central charge, using dimension eight and dual Coxeter number three. -/
noncomputable def centralChargeA (k : ℂ) : ℂ := (Fintype.card ι : ℂ) * k / (k + D.h)

/-- Reconstructed translation covariance expressed as the associative commutator. -/
theorem Ltrans_comm_Ycoeff (k : ℂ) (hk : k+D.h ≠ 0) (u : Vacuum D k) (s : ℤ) :
    ⁅Ltrans D k, (YA D k hk u) s⁆ = (s+1) • (YA D k hk u) (s+1) := by
  rw [LieRing.of_associative_ring_bracket]
  exact YA_DCov D k hk u s

/-- Sugawara translation annihilates the vacuum. -/
theorem Ltrans_vac (k : ℂ) : Ltrans D k (vacuumA D k) = 0 := Ltrans_vacuum D k

/-- Products in the reconstructed graded vertex algebra are the actual field modes. -/
theorem affineVertexAlgebra_smul (k : ℂ) (hk : k+D.h ≠ 0) (u : Vacuum D k) (j : ℤ) (v : Vacuum D k) :
    (affineVertexAlgebra D k hk).smul u j v = mode (YA D k hk u) j v := rfl

/-- `ω₍ⱼ₎ω = mode (YA ω) j ω`, the state the commutator formula feeds into `YA`. -/
noncomputable def omegaJomega (k : ℂ) (hk : k + D.h ≠ 0) (j : ℤ) : Vacuum D k :=
  mode (YA D k hk (omegaA D k)) j (omegaA D k)

/-- The explicitly named Sugawara self-product is the same state product
provided by the affine vertex algebra structure. -/
theorem omegaJomega_eq (k : ℂ) (hk : k + D.h ≠ 0) (j : ℤ) :
    omegaJomega D k hk j = (affineVertexAlgebra D k hk).smul (omegaA D k) j (omegaA D k) := rfl

/-- `ω₍ⱼ₎ω ∈ gradingZA (3-j)` (VA1, since `ω ∈ gradingZA 2`). -/
theorem omegaJomega_mem (k : ℂ) (hk : k + D.h ≠ 0) (j : ℤ) :
    omegaJomega D k hk j ∈ gradingZA D k (3 - j) := by
  have h := hYA_grading D k hk (omegaA D k) (omegaA_mem D k) (omegaA D k) (omegaA_mem D k) j
  rwa [show (2 : ℤ) + 2 - j - 1 = 3 - j from by ring] at h

/-- For `j ≥ 4`, `ω₍ⱼ₎ω = 0` (lands in negative degree). -/
theorem omegaJomega_eq_zero (k : ℂ) (hk : k + D.h ≠ 0) {j : ℤ} (hj : 4 ≤ j) :
    omegaJomega D k hk j = 0 := by
  have hmem := omegaJomega_mem D k hk j
  rw [gradingZA_positivity D k (3 - j) (by omega), Submodule.mem_bot] at hmem
  exact hmem

/-- `ω₍₁₎ω = 2 • ω` (since `L₀ω = mode(YA ω) 1 ω = 2ω`, ω ∈ gradingZA 2). -/
theorem omegaJomega_one (k : ℂ) (hk : k + D.h ≠ 0) :
    omegaJomega D k hk 1 = (2 : ℂ) • omegaA D k := by
  rw [omegaJomega, hYA_L0 D k hk (omegaA D k) (omegaA_mem D k)]
  norm_num

/-- `ω₍₀₎ω = Ltrans k ω` (the `L₋₁`-descendant; `mode (YA ω) 0 = Ltrans k`). -/
theorem omegaJomega_zero (k : ℂ) (hk : k + D.h ≠ 0) :
    omegaJomega D k hk 0 = Ltrans D k (omegaA D k) := by
  rw [omegaJomega, mode_YA_omega_zero]

/-- `mode (YA (ω₍₀₎ω)) c = -(c:ℂ) • mode (YA ω) (c-1)` (the `j=0` translation term):
`YA(ω₍₀₎ω) = YA(L₋₁ω) = ∂(YA ω)`, then `mode (∂ g) c = -c • mode g (c-1)`. -/
theorem mode_YA_omegaJomega_zero (k : ℂ) (hk : k + D.h ≠ 0) (c : ℤ) :
    mode (YA D k hk (omegaJomega D k hk 0)) c = (-(c : ℂ)) • mode (YA D k hk (omegaA D k)) (c - 1) := by
  rw [omegaJomega_zero, ← mode_YA_omega_zero D k hk, hYA_translation D k hk, mode_deriv,
    ← Int.cast_smul_eq_zsmul ℂ (-c)]
  push_cast
  rfl

/-! ## The commutator sum collapses to `j ∈ {0,1,2,3}` -/

/-- The `j`-th term of the commutator formula, as a function of `j : ℕ`. -/
noncomputable def commTerm (k : ℂ) (hk : k + D.h ≠ 0) (m n : ℤ) (j : ℕ) : End ℂ (Vacuum D k) :=
  gBinom (m + 1) j • mode (YA D k hk (omegaJomega D k hk (j : ℤ))) (m + 1 + (n + 1) - (j : ℤ))

/-- The commutator term vanishes for `j ≥ 4` (the state `ω₍ⱼ₎ω = 0`). -/
theorem commTerm_eq_zero (k : ℂ) (hk : k + D.h ≠ 0) (m n : ℤ) {j : ℕ} (hj : 4 ≤ j) :
    commTerm D k hk m n j = 0 := by
  rw [commTerm, omegaJomega_eq_zero D k hk (by exact_mod_cast hj), map_zero]
  show gBinom (m + 1) j • mode (0 : FormalDist (End ℂ (Vacuum D k)))
      (m + 1 + (n + 1) - (j : ℤ)) = 0
  rw [mode_zero, smul_zero]

/-- The commutator term vanishes when `ω₍ⱼ₎ω = 0` (the OPE-order locality vanishing, `j ≥ N`). -/
theorem commTerm_zero_of_smul_zero (k : ℂ) (hk : k + D.h ≠ 0) (m n : ℤ) {j : ℕ}
    (h : (affineVertexAlgebra D k hk).smul (omegaA D k) (j : ℤ) (omegaA D k) = 0) : commTerm D k hk m n j = 0 := by
  rw [commTerm, show omegaJomega D k hk (j : ℤ) = 0 from by rw [omegaJomega_eq]; exact h, map_zero]
  show gBinom (m + 1) j • mode (0 : FormalDist (End ℂ (Vacuum D k)))
      (m + 1 + (n + 1) - (j : ℤ)) = 0
  rw [mode_zero, smul_zero]

/-- **The commutator formula collapsed**: `[Lₘ, Lₙ] = ∑_{j<4} commTerm j`.  Robust to the OPE
order `N`: terms with `j ≥ 4` vanish (`commTerm_eq_zero`, grading) and terms with `N ≤ j < 4`
vanish (`commTerm_zero_of_smul_zero`, locality), so `range N` and `range 4` agree either way. -/
theorem comm_eq_range4 (k : ℂ) (hk : k + D.h ≠ 0) (m n : ℤ) :
    ⁅mode (YA D k hk (omegaA D k)) (m + 1), mode (YA D k hk (omegaA D k)) (n + 1)⁆
      = ∑ j ∈ Finset.range 4, commTerm D k hk m n j := by
  obtain ⟨N, hN, hvan⟩ := VARec.smul_zero_ge (affineVertexAlgebra D k hk) (Ltrans D k)
    (fun u s => Ltrans_comm_Ycoeff D k hk u s) (Ltrans_vac D k) (omegaA D k) (omegaA D k) (m + 1) (n + 1)
  rw [show (affineVertexAlgebra D k hk).Y = YA D k hk from rfl] at hN
  rw [hN]
  rw [show (∑ j : Fin N, gBinom (m + 1) (j : ℕ)
        • mode (YA D k hk ((affineVertexAlgebra D k hk).smul (omegaA D k) (j : ℕ) (omegaA D k)))
            (m + 1 + (n + 1) - (j : ℕ)))
      = ∑ j ∈ Finset.range N, commTerm D k hk m n j from by
    rw [← Fin.sum_univ_eq_sum_range (fun j => commTerm D k hk m n j) N]
    rfl]
  rcases le_total N 4 with hle | hle
  · refine Finset.sum_subset
      (fun j hj => Finset.mem_range.mpr (by rw [Finset.mem_range] at hj; omega))
      (fun j _ hjn => ?_)
    rw [Finset.mem_range, not_lt] at hjn
    exact commTerm_zero_of_smul_zero D k hk m n (hvan j hjn)
  · refine (Finset.sum_subset
      (fun j hj => Finset.mem_range.mpr (by rw [Finset.mem_range] at hj; omega))
      (fun j _ hj4 => ?_)).symm
    rw [Finset.mem_range, not_lt] at hj4
    exact commTerm_eq_zero D k hk m n hj4

/-! ## §B  Generalized binomial values `gBinom (n) k` for `k = 1, 2, 3` -/

/-- The first generalized binomial coefficient is n, for any integer n.
This remains valid for negative mode indices. -/
theorem gBinom_one (n : ℤ) : gBinom n 1 = (n : ℂ) := by
  simp [gBinom]

/-- The second generalized binomial coefficient is n(n-1)/2. This explicit
polynomial supplies the quadratic mode coefficient in the commutator. -/
theorem gBinom_two (n : ℤ) : gBinom n 2 = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
  simp [gBinom, Finset.prod_range_succ]

/-- The third generalized binomial coefficient is n(n-1)(n-2)/6. It provides
the cubic polynomial needed in the Virasoro central term. -/
theorem gBinom_three (n : ℤ) :
    gBinom n 3 = (n : ℂ) * ((n : ℂ) - 1) * ((n : ℂ) - 2) / 6 := by
  rw [gBinom, show (3 : ℕ).factorial = 6 from rfl]
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero]
  push_cast; ring

/-! ## §C  Current primality `L₁(J^c₋₁|0⟩) = 0` (the weight-1 primary condition) -/



/-- `J^c₋₁|0⟩ ∈ gradingZA 1`. -/
theorem current_state_mem (k : ℂ) (c : ι) : J D k c (-1) (vacuumA D k) ∈ gradingZA D k 1 := by
  have h := J_mem_gradingZA D k c (-1) 0 (vacuumA_mem_gradingZA_zero D k)
  rwa [show (0 : ℤ) - (-1) = 1 from by ring] at h

/-- A zero-mode current annihilates degree-`0` states (`= ℂ·|0⟩`). -/
theorem J_zero_grading0 (k : ℂ) (bb : ι) {y : Vacuum D k} (hy : y ∈ gradingZA D k 0) :
    J D k bb 0 y = 0 := by
  rw [gradingZA_zero_eq_span_vacuum] at hy
  induction hy using Submodule.span_induction with
  | mem z hz => rw [Set.mem_singleton_iff] at hz; subst hz; exact J_vacuum_nonneg D k bb (le_refl 0)
  | zero => rw [map_zero]
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

/-- `J^aa₀ (J^c₋₁|0⟩) = ∑_d f(aa,c,d) • J^d₋₁|0⟩` (zero mode acting; no central, modes `0,-1`). -/
theorem J0_current (k : ℂ) (c aa : ι) :
    J D k aa 0 (J D k c (-1) (vacuumA D k))
      = ∑ d : ι, structureConstant D aa c d • J D k d (-1) (vacuumA D k) := by
  have hb := J_bracket D k aa c 0 (-1)
  rw [if_neg (by norm_num : ¬ (0 : ℤ) + (-1) = 0), add_zero,
    show (0 : ℤ) + (-1) = -1 from by ring] at hb
  have happ := congrArg (fun (R : End ℂ (Vacuum D k)) => R (vacuumA D k)) hb
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply,
    LinearMap.smul_apply] at happ
  rw [J_vacuum_nonneg D k aa (le_refl 0), map_zero, sub_zero] at happ
  exact happ

/-- `J^bb₁ (J^d₋₁|0⟩) = (k·κ(bb,d)) • |0⟩` (central term, modes `1,-1`). -/
theorem J1_neg1_vac (k : ℂ) (bb d : ι) :
    J D k bb 1 (J D k d (-1) (vacuumA D k)) = (k * formTable D bb d) • vacuumA D k := by
  have hb := J_bracket D k bb d 1 (-1)
  rw [if_pos (by norm_num : (1 : ℤ) + (-1) = 0), show (1 : ℤ) + (-1) = 0 from by ring] at hb
  have happ := congrArg (fun (R : End ℂ (Vacuum D k)) => R (vacuumA D k)) hb
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.id_apply] at happ
  rw [J_vacuum_nonneg D k bb (by norm_num : (0 : ℤ) ≤ 1), map_zero, sub_zero] at happ
  rw [show (∑ x : ι, structureConstant D bb d x • J D k x 0 (vacuumA D k)) = 0 from
    Finset.sum_eq_zero (fun x _ => by
      rw [J_vacuum_nonneg D k x (by norm_num : (0 : ℤ) ≤ 0), smul_zero]),
    zero_add] at happ
  rw [happ, show ((1 : ℤ) : ℂ) = 1 from by norm_num, one_mul]

/-- The `p`-summand of `(nprod (Jfield aa)(Jfield bb))(-3)`: modes `(-p-1, p+2)`. -/
noncomputable def sug1TermJ (k : ℂ) (aa bb : ι) (p : ℤ) : End ℂ (Vacuum D k) :=
  if 0 ≤ p then J D k aa (-p - 1) * J D k bb (p + 2) else J D k bb (p + 2) * J D k aa (-p - 1)

/-- Evaluate one quadratic current summand on a module state. Normal ordering chooses the
composition order from the sign of p, while the two mode indices sum to one; this is the
summand used to compute L1 on current states. -/
theorem sug1TermJ_apply (k : ℂ) (aa bb : ι) (p : ℤ) (x : Vacuum D k) :
    sug1TermJ D k aa bb p x
      = if 0 ≤ p then J D k aa (-p - 1) (J D k bb (p + 2) x) else J D k bb (p + 2) (J D k aa (-p - 1) x) := by
  rw [sug1TermJ]; split_ifs <;> rw [Module.End.mul_apply]

/-- The `(-3)`-coefficient of `nprod (Jfield aa)(Jfield bb)` acting on `x`. -/
theorem nprod_neg_three_coeff (k : ℂ) (aa bb : ι) (x : Vacuum D k) :
    nprod (Jfield_isField D k aa) (Jfield_isField D k bb) (-3) x
      = ∑ᶠ p : ℤ, sug1TermJ D k aa bb p x := by
  rw [nprod_apply]
  refine finsum_congr fun p => ?_
  rw [normalOrdered_apply, Jfield_apply, Jfield_apply, sug1TermJ_apply,
      show -(-3 - p) - 1 = p + 2 from by ring]
  by_cases hp : 0 ≤ p
  · rw [if_pos hp, if_pos hp, Module.End.mul_apply]
  · rw [if_neg hp, if_neg hp, Module.End.mul_apply]

/-- The `Lsug 1` action (the `(-3)`-coefficient analog of `Lsug0_apply`). -/
theorem Lsug1_apply (k : ℂ) (x : Vacuum D k) :
    Lsug D k 1 x
      = c0 D k • ∑ aa : ι, ∑ bb : ι,
          kappaInv D aa bb • ∑ᶠ p : ℤ, sug1TermJ D k aa bb p x := by
  rw [Lsug_def, mode_apply, show (-((1 : ℤ) + 1) - 1 : ℤ) = -3 from by ring, sugawaraField]
  show (c0 D k • (Reconstruction.evalAt (-3) x
      (∑ aa : ι, ∑ bb : ι,
        kappaInv D aa bb • nprod (Jfield_isField D k aa) (Jfield_isField D k bb)))) = _
  rw [map_sum]
  refine congrArg (c0 D k • ·) ?_
  refine Finset.sum_congr rfl fun aa _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun bb _ => ?_
  rw [map_smul]
  refine congrArg (kappaInv D aa bb • ·) ?_
  rw [Reconstruction.evalAt_apply, nprod_neg_three_coeff]

/-- For `p ≠ -1`, `sug1TermJ aa bb p (J^c₋₁|0⟩) = 0`. -/
theorem sug1TermJ_current_off (k : ℂ) (c aa bb : ι) {p : ℤ} (hp : p ≠ -1) :
    sug1TermJ D k aa bb p (J D k c (-1) (vacuumA D k)) = 0 := by
  rw [sug1TermJ_apply]
  by_cases h0 : 0 ≤ p
  · rw [if_pos h0,
      J_gradingZA_eq_zero D k bb (show (1 : ℤ) < p + 2 from by omega) (current_state_mem D k c),
      map_zero]
  · rw [if_neg h0]
    rw [not_le] at h0
    rcases lt_or_eq_of_le (show p ≤ -2 from by omega) with hlt | heq
    · rw [J_gradingZA_eq_zero D k aa (show (1 : ℤ) < -p - 1 from by omega) (current_state_mem D k c),
        map_zero]
    · rw [show p + 2 = 0 from by rw [heq]; norm_num, show -p - 1 = 1 from by rw [heq]; norm_num]
      refine J_zero_grading0 D k bb ?_
      have h := J_mem_gradingZA D k aa 1 1 (current_state_mem D k c)
      rwa [show (1 : ℤ) - 1 = 0 from by ring] at h

/-- The value of `sug1TermJ` at `p = -1`. -/
theorem sug1TermJ_current_at_neg1 (k : ℂ) (c aa bb : ι) :
    sug1TermJ D k aa bb (-1) (J D k c (-1) (vacuumA D k))
      = (∑ d : ι, structureConstant D aa c d * k * formTable D bb d) • vacuumA D k := by
  rw [sug1TermJ_apply, if_neg (by norm_num : ¬ (0 : ℤ) ≤ -1),
    show (-1 : ℤ) + 2 = 1 from by ring, show (-(-1) - 1 : ℤ) = 0 from by ring,
    J0_current, map_sum]
  rw [show (∑ d : ι, J D k bb 1 (structureConstant D aa c d • J D k d (-1) (vacuumA D k)))
      = ∑ d : ι, (structureConstant D aa c d * k * formTable D bb d) • vacuumA D k from
    Finset.sum_congr rfl (fun d _ => by
      rw [map_smul, J1_neg1_vac, smul_smul]
      congr 1; ring)]
  rw [Finset.sum_smul]

/-- The collapse: `∑ᶠ_p sug1TermJ aa bb p (J^c₋₁|0⟩) = (∑_d f(aa,c,d) k κ(bb,d)) • |0⟩`. -/
theorem sug1TermJ_current_finsum (k : ℂ) (c aa bb : ι) :
    (∑ᶠ p : ℤ, sug1TermJ D k aa bb p (J D k c (-1) (vacuumA D k)))
      = (∑ d : ι, structureConstant D aa c d * k * formTable D bb d) • vacuumA D k := by
  rw [finsum_eq_single _ (-1) (fun p hp => sug1TermJ_current_off D k c aa bb hp)]
  exact sug1TermJ_current_at_neg1 D k c aa bb

/-- **Current primality**: `mode (YA ω) 2 (J^c₋₁|0⟩) = 0` (the current `J^c` is a weight-`1`
primary; `ω₍₂₎(J^c₋₁|0⟩) = 0`). -/
theorem current_primary (k : ℂ) (hk : k + D.h ≠ 0) (c : ι) :
    mode (YA D k hk (omegaA D k)) 2 (J D k c (-1) (vacuumA D k)) = 0 := by
  have hmode : mode (YA D k hk (omegaA D k)) 2 = Lsug D k 1 := by
    rw [YA_omega_eq, Lsug_def]; rfl
  rw [hmode, Lsug1_apply]
  have key : (∑ aa : ι, ∑ bb : ι,
        kappaInv D aa bb • ∑ᶠ p : ℤ, sug1TermJ D k aa bb p (J D k c (-1) (vacuumA D k)))
      = (∑ aa : ι, ∑ bb : ι, ∑ d : ι,
          kappaInv D aa bb * (structureConstant D aa c d * k * formTable D bb d)) • vacuumA D k := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun aa _ => ?_)
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl (fun bb _ => ?_)
    rw [sug1TermJ_current_finsum, smul_smul, Finset.mul_sum]
  rw [key, show (∑ aa : ι, ∑ bb : ι, ∑ d : ι,
        kappaInv D aa bb * (structureConstant D aa c d * k * formTable D bb d)) = 0 from by
    have hinv (a d : ι) : ∑ b, kappaInv D a b * formTable D b d = if d = a then 1 else 0 := by
      have h := kappaInv_kappa D d a
      convert h using 1
      apply Finset.sum_congr rfl
      intro b _
      rw [kappa_symm D b d, kappaInv_symm D a b, mul_comm]
    calc
      _ = ∑ a : ι, ∑ d : ι,
          (structureConstant D a c d * k) * (∑ b : ι, kappaInv D a b * formTable D b d) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = (∑ a : ι, structureConstant D a c a) * k := by
        simp only [hinv, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true, Finset.sum_mul]
      _ = 0 := by rw [structureConstant_diag_sum, zero_mul],
    zero_smul, smul_zero]

/-! ## §D  The current covariance `[Lₘ, J^c_μ] = -μ J^c_{m+μ}` via Borcherds + primality -/

/-- `:a(z) 1: = a(z)`: the normal-ordered product with the identity field is the identity. -/
theorem nprod_idFieldA {k : ℂ} {a : FormalDist (End ℂ (Vacuum D k))} (ha : IsField a) :
    nprod ha (idFieldA_isField D k) = a := by
  funext s
  apply LinearMap.ext; intro x
  rw [nprod_apply, finsum_eq_single _ s]
  · rw [normalOrdered_apply]
    have hid : (idFieldA D k) (s - s) = LinearMap.id := by
      change (if s - s = 0 then (LinearMap.id : End ℂ (Vacuum D k)) else 0) = LinearMap.id
      rw [if_pos (by ring)]
    by_cases h : 0 ≤ s
    · rw [if_pos h, hid]; rfl
    · rw [if_neg h, hid]; rfl
  · intro m hm
    rw [normalOrdered_apply]
    have hid : (idFieldA D k) (s - m) = 0 := by
      change (if s - m = 0 then (LinearMap.id : End ℂ (Vacuum D k)) else 0) = 0
      rw [if_neg (by omega)]
    by_cases h : 0 ≤ m
    · rw [if_pos h, hid]; simp
    · rw [if_neg h, hid]; simp

/-- The vertex field of the current state `J^c₋₁|0⟩` is the current field `J^c(z)`. -/
theorem YA_current_state (k : ℂ) (hk : k + D.h ≠ 0) (c : ι) :
    YA D k hk (J D k c (-1) (vacuumA D k)) = Jfield D k c := by
  have hws : wordStateA D k [(c, 0)] = J D k c (-1) (vacuumA D k) := by
    rw [wordStateA_cons, wordStateA_nil]; norm_num
  rw [← hws, YA_wordState, YwordA_cons]
  show nprod (genFieldA_isField D k c 0) (idFieldA_isField D k) = Jfield D k c
  rw [nprod_idFieldA, genFieldA_zero]

/-- `mode (Jfield c) μ = J^c_μ`. -/
theorem mode_Jfield (k : ℂ) (c : ι) (μ : ℤ) : mode (Jfield D k c) μ = J D k c μ := by
  rw [mode_apply, Jfield_apply, show -(-μ - 1) - 1 = μ from by ring]

/-- The `j`-th term of the current commutator formula (the OPE-coefficient feeds the current
state `J^c₋₁|0⟩` into `YA`). -/
noncomputable def covTerm (k : ℂ) (hk : k + D.h ≠ 0) (c : ι) (m μ : ℤ) (j : ℕ) :
    End ℂ (Vacuum D k) :=
  gBinom (m + 1) j • mode (YA D k hk ((affineVertexAlgebra D k hk).smul (omegaA D k) (j : ℤ)
    (J D k c (-1) (vacuumA D k)))) (m + 1 + μ - (j : ℤ))

/-- If a conformal-current operator-product coefficient is the zero state, its entire contribution
to the mode commutator vanishes. Linearity of the state-field map and of mode extraction
removes it, regardless of the binomial coefficient. -/
theorem covTerm_zero_of_smul (k : ℂ) (hk : k + D.h ≠ 0) (c : ι) (m μ : ℤ) {j : ℕ}
    (h : (affineVertexAlgebra D k hk).smul (omegaA D k) (j : ℤ) (J D k c (-1) (vacuumA D k)) = 0) :
    covTerm D k hk c m μ j = 0 := by
  rw [covTerm, h, map_zero]
  show gBinom (m + 1) j • mode (0 : FormalDist (End ℂ (Vacuum D k))) (m + 1 + μ - (j : ℤ)) = 0
  rw [mode_zero, smul_zero]

/-- `ω₍ⱼ₎(J^c₋₁|0⟩) = 0` for `j ≥ 2`: at `j = 2` it is primality `current_primary`; for `j ≥ 3`
the state lands in negative degree. -/
theorem smul_omega_current_ge2 (k : ℂ) (hk : k + D.h ≠ 0) (c : ι) {j : ℕ} (hj : 2 ≤ j) :
    (affineVertexAlgebra D k hk).smul (omegaA D k) (j : ℤ) (J D k c (-1) (vacuumA D k)) = 0 := by
  rw [affineVertexAlgebra_smul]
  rcases Nat.lt_or_ge j 3 with h3 | h3
  · obtain rfl : j = 2 := by omega
    exact_mod_cast current_primary D k hk c
  · have hmem := hYA_grading D k hk (omegaA D k) (omegaA_mem D k)
      (J D k c (-1) (vacuumA D k)) (current_state_mem D k c) (j : ℤ)
    rw [show (2 : ℤ) + 1 - (j : ℤ) - 1 = 2 - (j : ℤ) from by ring] at hmem
    rw [gradingZA_positivity D k (2 - (j : ℤ)) (by omega), Submodule.mem_bot] at hmem
    exact hmem

/-- `covTerm 0 = -(m+1+μ) • J^c_{m+μ}` (the translation/derivative term `ω₍₀₎ = L₋₁`). -/
theorem covTerm_zero_eq (k : ℂ) (hk : k + D.h ≠ 0) (c : ι) (m μ : ℤ) :
    covTerm D k hk c m μ 0 = ((-(m + 1 + μ) : ℤ) : ℂ) • J D k c (m + μ) := by
  rw [covTerm, Nat.cast_zero, gBinom_zero, one_smul, sub_zero, affineVertexAlgebra_smul,
    hYA_translation D k hk (J D k c (-1) (vacuumA D k)), mode_deriv,
    show m + 1 + μ - 1 = m + μ from by ring, YA_current_state, mode_Jfield,
    ← Int.cast_smul_eq_zsmul ℂ (-(m + 1 + μ))]

/-- `covTerm 1 = (m+1) • J^c_{m+μ}` (the weight term `ω₍₁₎ = L₀`, weight `1`). -/
theorem covTerm_one_eq (k : ℂ) (hk : k + D.h ≠ 0) (c : ι) (m μ : ℤ) :
    covTerm D k hk c m μ 1 = ((m + 1 : ℤ) : ℂ) • J D k c (m + μ) := by
  rw [covTerm, Nat.cast_one, gBinom_one, affineVertexAlgebra_smul,
    hYA_L0 D k hk (J D k c (-1) (vacuumA D k)) (current_state_mem D k c), Int.cast_one, one_smul,
    show m + 1 + μ - 1 = m + μ from by ring, YA_current_state, mode_Jfield]

/-- **The current covariance** (the weight-`1` primary OPE): `[Lₘ, J^c_μ] = -μ • J^c_{m+μ}`. -/
theorem Lcomm_J (k : ℂ) (hk : k + D.h ≠ 0) (m : ℤ) (c : ι) (μ : ℤ) :
    ⁅mode (YA D k hk (omegaA D k)) (m + 1), J D k c μ⁆ = ((-μ : ℤ) : ℂ) • J D k c (m + μ) := by
  obtain ⟨N, hN, hvan⟩ := VARec.smul_zero_ge (affineVertexAlgebra D k hk) (Ltrans D k)
    (fun u s => Ltrans_comm_Ycoeff D k hk u s) (Ltrans_vac D k) (omegaA D k) (J D k c (-1) (vacuumA D k))
    (m + 1) μ
  rw [show (affineVertexAlgebra D k hk).Y = YA D k hk from rfl] at hN
  rw [show mode (YA D k hk (J D k c (-1) (vacuumA D k))) μ = J D k c μ from by
    rw [YA_current_state, mode_Jfield]] at hN
  rw [hN]
  rw [show (∑ j : Fin N, gBinom (m + 1) (j : ℕ)
        • mode (YA D k hk ((affineVertexAlgebra D k hk).smul (omegaA D k) (j : ℕ) (J D k c (-1) (vacuumA D k))))
            (m + 1 + μ - (j : ℕ)))
      = ∑ j ∈ Finset.range N, covTerm D k hk c m μ j from by
    rw [← Fin.sum_univ_eq_sum_range (fun j => covTerm D k hk c m μ j) N]; rfl]
  have hcollapse : (∑ j ∈ Finset.range N, covTerm D k hk c m μ j)
      = ∑ j ∈ Finset.range 2, covTerm D k hk c m μ j := by
    rcases le_total N 2 with hle | hle
    · refine Finset.sum_subset
        (fun j hj => Finset.mem_range.mpr (by rw [Finset.mem_range] at hj; omega))
        (fun j _ hjn => ?_)
      rw [Finset.mem_range, not_lt] at hjn
      exact covTerm_zero_of_smul D k hk c m μ (hvan j hjn)
    · refine (Finset.sum_subset
        (fun j hj => Finset.mem_range.mpr (by rw [Finset.mem_range] at hj; omega))
        (fun j _ hj2 => ?_)).symm
      rw [Finset.mem_range, not_lt] at hj2
      exact covTerm_zero_of_smul D k hk c m μ (smul_omega_current_ge2 D k hk c hj2)
  rw [hcollapse, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    covTerm_zero_eq, covTerm_one_eq, ← add_smul]
  congr 1
  push_cast; ring

/-! ## §E  `ω₍₂₎ω = 0` and `ω₍₃₎ω = (c/2)|0⟩` -/

/-- The conformal vector in creation form: `ω = c₀ ∑_{a,b} κ⁻¹(a,b) J^a₋₁ J^b₋₁|0⟩`. -/
theorem omegaA_creation_form (k : ℂ) :
    omegaA D k = c0 D k • ∑ aa : ι, ∑ bb : ι,
      kappaInv D aa bb • J D k aa (-1) (J D k bb (-1) (vacuumA D k)) := by
  rw [omegaA_eq, sugawaraField]
  show (c0 D k • (Reconstruction.evalAt 0 (vacuumA D k)
      (∑ aa : ι, ∑ bb : ι,
        kappaInv D aa bb • nprod (Jfield_isField D k aa) (Jfield_isField D k bb)))) = _
  rw [map_sum]
  refine congrArg (c0 D k • ·) ?_
  refine Finset.sum_congr rfl fun aa _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun bb _ => ?_
  rw [map_smul]
  refine congrArg (kappaInv D aa bb • ·) ?_
  rw [Reconstruction.evalAt_apply,
    nprod_vacuum_base_gen (Jfield_isField D k aa) (Jfield_isField D k bb) (vacuumA D k)
      (fun q hq => Jfield_vacuum_neg D k aa hq) (fun q hq => Jfield_vacuum_neg D k bb hq),
    Jfield_apply, Jfield_apply, show (-(0 : ℤ) - 1) = -1 from by ring]

/-- The current covariance applied to a state:
`Lₘ(J^a_ν y) = J^a_ν(Lₘ y) + (-ν)•J^a_{m+ν} y`. -/
theorem Lcomm_J_apply (k : ℂ) (hk : k + D.h ≠ 0) (m : ℤ) (a : ι) (ν : ℤ) (y : Vacuum D k) :
    mode (YA D k hk (omegaA D k)) (m + 1) (J D k a ν y)
      = J D k a ν (mode (YA D k hk (omegaA D k)) (m + 1) y) + ((-ν : ℤ) : ℂ) • J D k a (m + ν) y := by
  have h := Lcomm_J D k hk m a ν
  rw [LieRing.of_associative_ring_bracket] at h
  have happ := congrArg (fun (R : End ℂ (Vacuum D k)) => R y) h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at happ
  rw [sub_eq_iff_eq_add] at happ
  rw [happ]; abel

/-- `∑_{aa,bb} κ⁻¹(aa,bb) • ∑_d f(aa,bb,d) • V d = 0` (κ⁻¹ symmetric · `f` antisymmetric). -/
theorem contract_antisymm (k : ℂ) (V : ι → Vacuum D k) :
    (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb • ∑ d : ι, structureConstant D aa bb d • V d) = 0 := by
  have e1 : (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb • ∑ d : ι, structureConstant D aa bb d • V d)
      = ∑ aa : ι, ∑ bb : ι, ∑ d : ι, (kappaInv D aa bb * structureConstant D aa bb d) • V d := by
    refine Finset.sum_congr rfl (fun aa _ => Finset.sum_congr rfl (fun bb _ => ?_))
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun d _ => by rw [smul_smul])
  rw [e1, Finset.sum_congr rfl (fun aa _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_eq_zero (fun d _ => ?_)
  rw [show (∑ aa : ι, ∑ bb : ι, (kappaInv D aa bb * structureConstant D aa bb d) • V d)
      = (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb * structureConstant D aa bb d) • V d from by
    rw [Finset.sum_smul]; exact Finset.sum_congr rfl (fun aa _ => by rw [Finset.sum_smul])]
  rw [kappaInv_structureConstant_antisymm_zero, zero_smul]

/-- `L₁(J^a₋₁ J^b₋₁|0⟩) = ∑_d f(a,b,d) • J^d₋₁|0⟩` (Leibniz: `[L₁,J^a₋₁]=J^a₀`, primality kills
the other term). -/
theorem L1_on_two_currents (k : ℂ) (hk : k + D.h ≠ 0) (aa bb : ι) :
    mode (YA D k hk (omegaA D k)) 2 (J D k aa (-1) (J D k bb (-1) (vacuumA D k)))
      = ∑ d : ι, structureConstant D aa bb d • J D k d (-1) (vacuumA D k) := by
  have h := Lcomm_J_apply D k hk 1 aa (-1) (J D k bb (-1) (vacuumA D k))
  rw [show (1 : ℤ) + 1 = 2 from by ring, show (1 : ℤ) + (-1) = 0 from by ring,
    show ((-(-1) : ℤ) : ℂ) = 1 from by norm_num, one_smul, current_primary D k hk bb, map_zero,
    zero_add, J0_current D k bb aa] at h
  exact h

/-- `L₂(J^a₋₁ J^b₋₁|0⟩) = (k·κ(a,b)) • |0⟩` (Leibniz: `[L₂,J^a₋₁]=J^a₁`, grading kills the other
term; the central level-`k` term survives). -/
theorem L2_on_two_currents (k : ℂ) (hk : k + D.h ≠ 0) (aa bb : ι) :
    mode (YA D k hk (omegaA D k)) 3 (J D k aa (-1) (J D k bb (-1) (vacuumA D k)))
      = (k * formTable D aa bb) • vacuumA D k := by
  have hinner : mode (YA D k hk (omegaA D k)) 3 (J D k bb (-1) (vacuumA D k)) = 0 := by
    have hmem := hYA_grading D k hk (omegaA D k) (omegaA_mem D k) (J D k bb (-1) (vacuumA D k))
      (current_state_mem D k bb) 3
    rw [show (2 : ℤ) + 1 - 3 - 1 = -1 from by ring,
      gradingZA_positivity D k (-1) (by norm_num), Submodule.mem_bot] at hmem
    exact hmem
  have h := Lcomm_J_apply D k hk 2 aa (-1) (J D k bb (-1) (vacuumA D k))
  rw [show (2 : ℤ) + 1 = 3 from by ring, show (2 : ℤ) + (-1) = 1 from by ring,
    show ((-(-1) : ℤ) : ℂ) = 1 from by norm_num, one_smul, J1_neg1_vac, hinner, map_zero,
    zero_add] at h
  exact h

/-- **`ω₍₂₎ω = 0`** (the OPE coefficient `T₍₂₎T = 0`). -/
theorem omegaJomega_two_eq_zero (k : ℂ) (hk : k + D.h ≠ 0) : omegaJomega D k hk 2 = 0 := by
  show mode (YA D k hk (omegaA D k)) 2 (omegaA D k) = 0
  nth_rewrite 2 [omegaA_creation_form]
  rw [map_smul, map_sum]
  rw [show (∑ aa : ι, mode (YA D k hk (omegaA D k)) 2
        (∑ bb : ι, kappaInv D aa bb • J D k aa (-1) (J D k bb (-1) (vacuumA D k))))
      = ∑ aa : ι, ∑ bb : ι, kappaInv D aa bb •
          (∑ d : ι, structureConstant D aa bb d • J D k d (-1) (vacuumA D k)) from
    Finset.sum_congr rfl (fun aa _ => by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun bb _ => by rw [map_smul, L1_on_two_currents]))]
  rw [contract_antisymm, smul_zero]

/-- **`ω₍₃₎ω = (c/2)|0⟩`** (the OPE coefficient `T₍₃₎T = (c/2)·1`; `c = 8k/(k+3)`). -/
theorem omegaJomega_three (k : ℂ) (hk : k + D.h ≠ 0) :
    omegaJomega D k hk 3 = (centralChargeA D k / 2) • vacuumA D k := by
  show mode (YA D k hk (omegaA D k)) 3 (omegaA D k) = (centralChargeA D k / 2) • vacuumA D k
  nth_rewrite 2 [omegaA_creation_form]
  rw [map_smul, map_sum]
  rw [show (∑ aa : ι, mode (YA D k hk (omegaA D k)) 3
        (∑ bb : ι, kappaInv D aa bb • J D k aa (-1) (J D k bb (-1) (vacuumA D k))))
      = ∑ aa : ι, ∑ bb : ι, kappaInv D aa bb • ((k * formTable D aa bb) • vacuumA D k) from
    Finset.sum_congr rfl (fun aa _ => by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun bb _ => by rw [map_smul, L2_on_two_currents]))]
  rw [show (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb • ((k * formTable D aa bb) • vacuumA D k))
      = (k * ∑ aa : ι, ∑ bb : ι, kappaInv D aa bb * formTable D aa bb) • vacuumA D k from by
    rw [show (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb • ((k * formTable D aa bb) • vacuumA D k))
        = ∑ aa : ι, ∑ bb : ι, (k * (kappaInv D aa bb * formTable D aa bb)) • vacuumA D k from
      Finset.sum_congr rfl (fun aa _ => Finset.sum_congr rfl (fun bb _ => by
        rw [smul_smul]; congr 1; ring))]
    rw [show (∑ aa : ι, ∑ bb : ι, (k * (kappaInv D aa bb * formTable D aa bb)) • vacuumA D k)
        = (∑ aa : ι, ∑ bb : ι, k * (kappaInv D aa bb * formTable D aa bb)) • vacuumA D k from by
      rw [Finset.sum_smul]; exact Finset.sum_congr rfl (fun aa _ => by rw [Finset.sum_smul])]
    congr 1
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun aa _ => by rw [Finset.mul_sum])]
  have htrace : (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb * formTable D aa bb) =
      (Fintype.card ι : ℂ) := trace_kappaInv_formTable D
  rw [htrace, smul_smul]
  congr 1
  simp only [c0, centralChargeA]
  field_simp


/-! ## §F  VOA1: the Sugawara Virasoro relation `hYA_virasoro` -/

/-- **VOA1** (`hYA_virasoro`): the full Sugawara Virasoro relation
`[Lₘ, Lₙ] = (m−n)·L_{m+n} + δ_{m+n,0}·(m³−m)/12·c·1`, with `c = centralChargeA k = 8k/(k+3)`.
Obtained from the collapsed Borcherds commutator `[Lₘ,Lₙ] = ∑_{j<4} commTermⱼ` by evaluating the
four OPE coefficients: `ω₍₀₎ω = L₋₁ω` (translation), `ω₍₁₎ω = 2ω` (weight), `ω₍₂₎ω = 0`, and
`ω₍₃₎ω = (c/2)|0⟩` (central charge). -/
theorem hYA_virasoro (k : ℂ) (hk : k + D.h ≠ 0) (m n : ℤ) :
    ⁅mode (YA D k hk (omegaA D k)) (m + 1), mode (YA D k hk (omegaA D k)) (n + 1)⁆
      = ((m : ℂ) - n) • mode (YA D k hk (omegaA D k)) (m + n + 1)
        + (if m + n = 0 then
            (((m : ℂ) ^ 3 - m) / 12 * centralChargeA D k) • (1 : End ℂ (Vacuum D k))
           else 0) := by
  have hct0 : commTerm D k hk m n 0
      = (-((m + n + 2 : ℤ) : ℂ)) • mode (YA D k hk (omegaA D k)) (m + n + 1) := by
    rw [commTerm]
    simp only [Nat.cast_zero]
    rw [gBinom_zero, one_smul, sub_zero, show m + 1 + (n + 1) = m + n + 2 from by ring,
      mode_YA_omegaJomega_zero, show (m + n + 2 : ℤ) - 1 = m + n + 1 from by ring]
  have hct1 : commTerm D k hk m n 1
      = ((m + 1 : ℤ) : ℂ) • ((2 : ℂ) • mode (YA D k hk (omegaA D k)) (m + n + 1)) := by
    rw [commTerm]
    simp only [Nat.cast_one]
    rw [gBinom_one, omegaJomega_one, map_smul, mode_smul,
      show m + 1 + (n + 1) - 1 = m + n + 1 from by ring]
  have hct2 : commTerm D k hk m n 2 = 0 := by
    rw [commTerm]
    simp only [Nat.cast_ofNat]
    rw [omegaJomega_two_eq_zero D k hk, map_zero, mode_zero, smul_zero]
  have hct3 : commTerm D k hk m n 3
      = if m + n = 0 then
          (((m : ℂ) ^ 3 - m) / 12 * centralChargeA D k) • (1 : End ℂ (Vacuum D k)) else 0 := by
    rw [commTerm]
    simp only [Nat.cast_ofNat]
    rw [gBinom_three, omegaJomega_three, map_smul, YA_vacuum, mode_smul,
      show m + 1 + (n + 1) - 3 = m + n - 1 from by ring]
    by_cases hmn : m + n = 0
    · rw [if_pos hmn]
      have hone : mode (1 : FormalDist (End ℂ (Vacuum D k))) (m + n - 1)
          = (1 : End ℂ (Vacuum D k)) := by
        rw [mode_apply, show -(m + n - 1) - 1 = -(m + n) from by ring, hmn, neg_zero,
          FormalDist.one_apply, if_pos rfl]
      rw [hone, smul_smul]
      congr 1
      push_cast; ring
    · rw [if_neg hmn]
      have hone : mode (1 : FormalDist (End ℂ (Vacuum D k))) (m + n - 1) = 0 := by
        rw [mode_apply, FormalDist.one_apply, if_neg (by omega : ¬ -(m + n - 1) - 1 = 0)]
      rw [hone, smul_zero, smul_zero]
  rw [comm_eq_range4, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hct2, add_zero, hct0, hct1, hct3]
  congr 1
  rw [smul_smul, ← add_smul]
  congr 1
  push_cast; ring

/-- **The universal affine VOA `V^k(𝔤)`** for any finite-dimensional Lie algebra `𝔤` with Lie data `D`
(basis, `κ`-dual family, adjoint Casimir `2h`) at non-critical level `k + h ≠ 0`.  Grading, creation,
locality, Virasoro relations (central charge `dim 𝔤 · k / (k + h)`), `L₀`-grading and translation are
all proved internally. -/
noncomputable def affineVOA (k : ℂ) (hk : k+D.h ≠ 0) :
    VertexOperatorAlgebra (Vacuum D k) where
  toPreVertexAlgebra := affineVertexAlgebra D k hk
  conformalVector := omegaA D k
  conformal_mem := omegaA_mem D k
  centralCharge := centralChargeA D k
  virasoro := hYA_virasoro D k hk
  L0_grading := hYA_L0 D k hk
  translation := hYA_translation D k hk
  positivity := gradingZA_positivity D k
  vacuum_grade := gradingZA_zero_eq_smul_vacuum D k

end VOA.AffineGeneral
