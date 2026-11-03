import VOA.AffineGeneral.GradedFields
/-!
# Sugawara zero mode equals actual sl3 energy

*General-`𝔤` port* of `VOA/Examples/AffineSl3SugawaraEnergy.lean` (generated mechanically from that file):
the index type is `ι`, the Lie data is `D : LieData κ ι`, the dual Coxeter number is `D.h`.  Where the
text below says sl₃, `Fin 8`, `6` or `3`, read `𝔤`, `ι`, `2 * D.h` and `D.h`.

The two normal-ordering boundary bands give the Casimir-six anomaly,
while the central contribution is twice the level. Their sum cancels
the Sugawara denominator 2(k+3). Agreement on the spanning creation
words then identifies the zero mode with the actual energy operator.
No ordered-word independence is used.
-/
set_option maxHeartbeats 1600000
open VOA VOA.AffineGeneral VOA.AffineGeneral.SugawaraCov
open scoped BigOperators
open Module (End)
open VOA.AffineLie
namespace VOA.AffineGeneral.SugawaraCov

open LieData
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
variable {κ : LinearMap.BilinForm ℂ 𝔤} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (D : LieData κ ι)

/-- The normal-ordered per-term operator for the `(-2)`-coefficient `:J^{aa} J^{bb}:_{-2}`:
the `p`-summand of `(nprod (Jfield aa)(Jfield bb))(-2)`.  Modes `(-p-1, p+1)` sum to `0`. -/
noncomputable def sug0TermJ (k : ℂ) (aa bb : ι) (p : ℤ) : End ℂ (Vacuum D k) :=
  if 0 ≤ p then J D k aa (-p - 1) * J D k bb (p + 1) else J D k bb (p + 1) * J D k aa (-p - 1)

/-- Evaluation of a zero-mode Sugawara summand gives the ordered pair of currents selected by the sign of the summation index. -/
theorem sug0TermJ_apply (k : ℂ) (aa bb : ι) (p : ℤ) (x : Vacuum D k) :
    sug0TermJ D k aa bb p x
      = if 0 ≤ p then J D k aa (-p - 1) (J D k bb (p + 1) x) else J D k bb (p + 1) (J D k aa (-p - 1) x) := by
  rw [sug0TermJ]; split_ifs <;> rw [Module.End.mul_apply]

/-- The `(-2)`-coefficient of `nprod (Jfield aa)(Jfield bb)` acting on `x`. -/
theorem nprod_neg_two_coeff (k : ℂ) (aa bb : ι) (x : Vacuum D k) :
    nprod (Jfield_isField D k aa) (Jfield_isField D k bb) (-2) x
      = ∑ᶠ p : ℤ, sug0TermJ D k aa bb p x := by
  rw [nprod_apply]
  refine finsum_congr fun p => ?_
  rw [normalOrdered_apply, Jfield_apply, Jfield_apply, sug0TermJ_apply,
      show -(-2 - p) - 1 = p + 1 from by ring]
  by_cases hp : 0 ≤ p
  · rw [if_pos hp, if_pos hp, Module.End.mul_apply]
  · rw [if_neg hp, if_neg hp, Module.End.mul_apply]

/-- The `Lsug 0` action formula (analog of `Ltrans_apply`). -/
theorem Lsug0_apply (k : ℂ) (x : Vacuum D k) :
    Lsug D k 0 x
      = c0 D k • ∑ aa : ι, ∑ bb : ι,
          kappaInv D aa bb • ∑ᶠ p : ℤ, sug0TermJ D k aa bb p x := by
  rw [Lsug_def, mode_apply, show (-((0:ℤ) + 1) - 1 : ℤ) = -2 from by ring, sugawaraField]
  show (c0 D k • (Reconstruction.evalAt (-2) x
      (∑ aa : ι, ∑ bb : ι,
        kappaInv D aa bb • nprod (Jfield_isField D k aa) (Jfield_isField D k bb)))) = _
  rw [map_sum]
  refine congrArg (c0 D k • ·) ?_
  refine Finset.sum_congr rfl fun aa _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun bb _ => ?_
  rw [map_smul]
  refine congrArg (kappaInv D aa bb • ·) ?_
  rw [Reconstruction.evalAt_apply, nprod_neg_two_coeff]

/-! ## §0  Assessment: per-pair Leibniz split for `Lsug 0`

The `Lsug 0` per-term `sug0TermJ aa bb p` has modes `(-p-1, p+1)`.  Compared to `sugTermJ aa bb p`
(modes `(-p-1, p)`), the second factor's mode is shifted by `+1`.  The bracket `[J^c_μ, ·]` splits
by Leibniz exactly as `inner_body_split`, with `bb`-mode `p ↦ p+1`.  We define the `Lsug 0`
struct/central operator parts and prove the split via `pair_bracket_S`/`pair_bracket_S'`. -/

/-- The struct operator-part of `[J^c_μ, sug0TermJ aa bb p]`. -/
noncomputable def struct0Op (k : ℂ) (c aa bb : ι) (μ p : ℤ) : End ℂ (Vacuum D k) :=
  if 0 ≤ p
    then (∑ d, structureConstant D c aa d • J D k d (μ + (-p - 1))) * J D k bb (p + 1)
            + J D k aa (-p - 1) * (∑ d, structureConstant D c bb d • J D k d (μ + (p + 1)))
    else (∑ d, structureConstant D c bb d • J D k d (μ + (p + 1))) * J D k aa (-p - 1)
            + J D k bb (p + 1) * (∑ d, structureConstant D c aa d • J D k d (μ + (-p - 1)))

/-- The central operator-part of `[J^c_μ, sug0TermJ aa bb p]`. -/
noncomputable def central0Op (k : ℂ) (c aa bb : ι) (μ p : ℤ) : End ℂ (Vacuum D k) :=
  if 0 ≤ p
    then (if μ + (-p-1) = 0 then ((μ : ℂ) * k * formTable D c aa) • LinearMap.id else 0) * J D k bb (p + 1)
            + J D k aa (-p-1) * (if μ + (p+1) = 0 then ((μ : ℂ) * k * formTable D c bb) • LinearMap.id else 0)
    else (if μ + (p+1) = 0 then ((μ : ℂ) * k * formTable D c bb) • LinearMap.id else 0) * J D k aa (-p-1)
            + J D k bb (p + 1) * (if μ + (-p-1) = 0 then ((μ : ℂ) * k * formTable D c aa) • LinearMap.id else 0)

/-- The noncentral Lie-bracket contribution evaluated on the given vector, before summing its normal-ordering index. -/
noncomputable def struct0Part (k : ℂ) (c aa bb : ι) (μ p : ℤ) (x : Vacuum D k) : Vacuum D k :=
  struct0Op D k c aa bb μ p x

/-- The affine-cocycle contribution evaluated on the given vector, before summing its normal-ordering index. -/
noncomputable def central0Part (k : ℂ) (c aa bb : ι) (μ p : ℤ) (x : Vacuum D k) : Vacuum D k :=
  central0Op D k c aa bb μ p x

/-- The inner body of the `Lsug 0` commutator equals `-[J^c_μ, sug0TermJ aa bb p] x`. -/
theorem inner0_body_eq (k : ℂ) (c aa bb : ι) (μ p : ℤ) (x : Vacuum D k) :
    sug0TermJ D k aa bb p (J D k c μ x) - J D k c μ (sug0TermJ D k aa bb p x)
      = - ((if 0 ≤ p
            then (J D k c μ * (J D k aa (-p-1) * J D k bb (p+1)) - (J D k aa (-p-1) * J D k bb (p+1)) * J D k c μ)
            else (J D k c μ * (J D k bb (p+1) * J D k aa (-p-1)) - (J D k bb (p+1) * J D k aa (-p-1)) * J D k c μ)) x) := by
  rw [sug0TermJ]
  by_cases hp : 0 ≤ p
  · rw [if_pos hp, if_pos hp]
    have happ := congrArg (fun (R : End ℂ (Vacuum D k)) => R x)
      (show (J D k aa (-p-1) * J D k bb (p+1)) * J D k c μ - J D k c μ * (J D k aa (-p-1) * J D k bb (p+1))
        = -(J D k c μ * (J D k aa (-p-1) * J D k bb (p+1)) - (J D k aa (-p-1) * J D k bb (p+1)) * J D k c μ) from by abel)
    simpa only [LinearMap.sub_apply, LinearMap.neg_apply, Module.End.mul_apply] using happ
  · rw [if_neg hp, if_neg hp]
    have happ := congrArg (fun (R : End ℂ (Vacuum D k)) => R x)
      (show (J D k bb (p+1) * J D k aa (-p-1)) * J D k c μ - J D k c μ * (J D k bb (p+1) * J D k aa (-p-1))
        = -(J D k c μ * (J D k bb (p+1) * J D k aa (-p-1)) - (J D k bb (p+1) * J D k aa (-p-1)) * J D k c μ) from by abel)
    simpa only [LinearMap.sub_apply, LinearMap.neg_apply, Module.End.mul_apply] using happ

/-- The `Lsug 0` inner body splits as `-(struct0Part + central0Part)`. -/
theorem inner0_body_split (k : ℂ) (c aa bb : ι) (μ p : ℤ) (x : Vacuum D k) :
    sug0TermJ D k aa bb p (J D k c μ x) - J D k c μ (sug0TermJ D k aa bb p x)
      = - (struct0Part D k c aa bb μ p x + central0Part D k c aa bb μ p x) := by
  rw [inner0_body_eq, struct0Part, central0Part, struct0Op, central0Op]
  congr 1
  by_cases hp : 0 ≤ p
  · rw [if_pos hp, if_pos hp, if_pos hp, pair_bracket_S]
    rw [add_mul, mul_add]
    simp only [LinearMap.add_apply]
    abel
  · rw [if_neg hp, if_neg hp, if_neg hp, leibniz_bracket_S, current_comm, current_comm,
      show (μ + (p + 1) : ℤ) = μ + (p + 1) from rfl]
    rw [add_mul, mul_add]
    simp only [LinearMap.add_apply]
    abel

/-! ## §0b  The central residue for `Lsug 0` (degree-preserving: lands on `J^c_μ`) -/

/-- `central0Part` away from `{μ-1, -μ-1}` vanishes. -/
theorem central0Part_off (k : ℂ) (c aa bb : ι) (μ p : ℤ) (x : Vacuum D k)
    (h1 : p ≠ μ - 1) (h2 : p ≠ -μ - 1) : central0Part D k c aa bb μ p x = 0 := by
  rw [central0Part, central0Op]
  by_cases hp0 : 0 ≤ p
  · rw [if_pos hp0, if_neg (by omega : ¬ μ + (-p-1) = 0), if_neg (by omega : ¬ μ + (p+1) = 0)]
    simp
  · rw [if_neg hp0, if_neg (by omega : ¬ μ + (p+1) = 0), if_neg (by omega : ¬ μ + (-p-1) = 0)]
    simp

/-- A scalar-`id` `if`-block at a nonzero `μ`-multiple applied to a state.  At `μ = 0` the scalar
is `0` so the block contributes `0` regardless of the `if`. -/
private theorem central_if_apply (k : ℂ) (cc : ι) (μ : ℤ) (cond : Prop) [Decidable cond]
    (y : Vacuum D k) :
    ((if cond then ((μ : ℂ) * k * formTable D cc cc) • (LinearMap.id : End ℂ (Vacuum D k)) else 0) : End ℂ (Vacuum D k)) y
      = if cond then ((μ : ℂ) * k * formTable D cc cc) • y else 0 := by
  split_ifs <;> simp

/-- `central0Part` at `p = μ-1` gives `(μ k κ(c,aa)) • J bb(μ) x`.  (At `μ=0`, both factors `0`.) -/
theorem central0Part_at_mu1 (k : ℂ) (c aa bb : ι) (μ : ℤ) (x : Vacuum D k) :
    central0Part D k c aa bb μ (μ - 1) x = ((μ : ℂ) * k * formTable D c aa) • (J D k bb μ x) := by
  rw [central0Part, central0Op, show ((μ-1)+1 : ℤ) = μ from by ring,
    show (-(μ-1)-1 : ℤ) = -μ from by ring]
  by_cases hp0 : 0 ≤ μ - 1
  · rw [if_pos hp0]
    simp only [LinearMap.add_apply, Module.End.mul_apply]
    -- first if fires (μ + -μ = 0), second `if μ+μ=0`
    rw [show (μ + -μ : ℤ) = 0 from by ring, if_pos rfl]
    by_cases hμ : μ + μ = 0
    · -- μ=0: both terms vanish (scalar μ=0)
      have hμ0 : μ = 0 := by omega
      rw [if_pos hμ]
      subst hμ0
      simp
    · rw [if_neg hμ]
      simp only [LinearMap.zero_apply, map_zero, add_zero, LinearMap.smul_apply, LinearMap.id_apply]
  · rw [if_neg hp0]
    simp only [LinearMap.add_apply, Module.End.mul_apply]
    rw [show (μ + -μ : ℤ) = 0 from by ring, if_pos rfl]
    by_cases hμ : μ + μ = 0
    · have hμ0 : μ = 0 := by omega
      rw [if_pos hμ]; subst hμ0; simp
    · rw [if_neg hμ]
      simp only [LinearMap.zero_apply, zero_add, LinearMap.smul_apply, LinearMap.id_apply, map_smul]

/-- `central0Part` at `p = -μ-1` gives `(μ k κ(c,bb)) • J aa(μ) x`.  (At `μ=0`, both factors `0`.) -/
theorem central0Part_at_negmu1 (k : ℂ) (c aa bb : ι) (μ : ℤ) (x : Vacuum D k) :
    central0Part D k c aa bb μ (-μ - 1) x = ((μ : ℂ) * k * formTable D c bb) • (J D k aa μ x) := by
  rw [central0Part, central0Op, show ((-μ-1)+1 : ℤ) = -μ from by ring,
    show (-(-μ-1)-1 : ℤ) = μ from by ring]
  by_cases hp0 : 0 ≤ -μ - 1
  · rw [if_pos hp0]
    simp only [LinearMap.add_apply, Module.End.mul_apply]
    rw [show (μ + -μ : ℤ) = 0 from by ring, if_pos rfl]
    by_cases hμ : μ + μ = 0
    · have hμ0 : μ = 0 := by omega
      rw [if_pos hμ]; subst hμ0; simp
    · rw [if_neg hμ]
      simp only [LinearMap.zero_apply, zero_add, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
  · rw [if_neg hp0]
    simp only [LinearMap.add_apply, Module.End.mul_apply]
    rw [show (μ + -μ : ℤ) = 0 from by ring, if_pos rfl]
    by_cases hμ : μ + μ = 0
    · have hμ0 : μ = 0 := by omega
      rw [if_pos hμ]; subst hμ0; simp
    · rw [if_neg hμ]
      simp only [LinearMap.zero_apply, map_zero, add_zero, LinearMap.smul_apply, LinearMap.id_apply]

/-- Only the two cocycle resonance indices can contribute to this central summand, so its vector-valued support is finite. -/
theorem central0Part_support_finite (k : ℂ) (c aa bb : ι) (μ : ℤ) (x : Vacuum D k) :
    (Function.support (fun p : ℤ => central0Part D k c aa bb μ p x)).Finite := by
  apply Set.Finite.subset (Set.toFinite ({μ - 1, -μ - 1} : Finset ℤ))
  intro p hp
  rw [Function.mem_support] at hp
  by_contra hpc
  apply hp
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] at hpc
  exact central0Part_off D k c aa bb μ p x hpc.1 hpc.2

/-- The central finsum collapses to the two-point body. -/
theorem central0Part_finsum_collapse (k : ℂ) (c aa bb : ι) (μ : ℤ) (x : Vacuum D k) :
    (∑ᶠ p : ℤ, central0Part D k c aa bb μ p x)
      = ((μ : ℂ) * k * formTable D c aa) • (J D k bb μ x)
        + ((μ : ℂ) * k * formTable D c bb) • (J D k aa μ x) := by
  classical
  rw [finsum_eq_finsetSum_of_support_subset _ (s := ({μ - 1, -μ - 1} : Finset ℤ)) (by
    intro p hp
    rw [Function.mem_support] at hp
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra hpc
    rw [not_or] at hpc
    exact hp (central0Part_off D k c aa bb μ p x hpc.1 hpc.2))]
  by_cases hμ : μ = 0
  · -- collision: {μ-1, -μ-1} = {-1}; both at-values vanish (μ=0).
    subst hμ
    rw [show ((0:ℤ) - 1) = -1 from by ring, show (-(0:ℤ) - 1) = -1 from by ring]
    rw [show ({(-1 : ℤ), -1} : Finset ℤ) = {-1} from by simp, Finset.sum_singleton]
    rw [show (-1 : ℤ) = (0 : ℤ) - 1 from by ring, central0Part_at_mu1]
    simp
  · rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
        Finset.sum_singleton, central0Part_at_mu1, central0Part_at_negmu1]

/-- Raw central residue (no `c0`): `Σ_{aa,bb} κ⁻¹ Σᶠ_p central0Part = 2μk • J^c_μ x`. -/
theorem central0_residue_raw (k : ℂ) (c : ι) (μ : ℤ) (x : Vacuum D k) :
    (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb • ∑ᶠ p : ℤ, central0Part D k c aa bb μ p x)
      = (2 * μ * k : ℂ) • J D k c μ x := by
  rw [show (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb • ∑ᶠ p : ℤ, central0Part D k c aa bb μ p x)
        = ∑ aa : ι, ∑ bb : ι, kappaInv D aa bb •
            (((μ : ℂ) * k * formTable D c aa) • (J D k bb μ x)
              + ((μ : ℂ) * k * formTable D c bb) • (J D k aa μ x))
      from Finset.sum_congr rfl fun aa _ => Finset.sum_congr rfl fun bb _ => by
        rw [central0Part_finsum_collapse]]
  have hbody : ∀ aa bb : ι,
      kappaInv D aa bb • (((μ : ℂ) * k * formTable D c aa) • (J D k bb μ x)
          + ((μ : ℂ) * k * formTable D c bb) • (J D k aa μ x))
        = (kappaInv D aa bb * ((μ : ℂ) * k * formTable D c aa)) • (J D k bb μ x)
          + (kappaInv D aa bb * ((μ : ℂ) * k * formTable D c bb)) • (J D k aa μ x) :=
    fun aa bb => by rw [smul_add, smul_smul, smul_smul]
  simp only [hbody]
  rw [show (∑ aa : ι, ∑ bb : ι,
        ((kappaInv D aa bb * ((μ : ℂ) * k * formTable D c aa)) • (J D k bb μ x)
          + (kappaInv D aa bb * ((μ : ℂ) * k * formTable D c bb)) • (J D k aa μ x)))
      = (∑ aa : ι, ∑ bb : ι, (kappaInv D aa bb * ((μ : ℂ) * k * formTable D c aa)) • (J D k bb μ x))
        + (∑ aa : ι, ∑ bb : ι, (kappaInv D aa bb * ((μ : ℂ) * k * formTable D c bb)) • (J D k aa μ x))
      from by rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun aa _ => ?_;
              rw [← Finset.sum_add_distrib]]
  have hT1 : (∑ aa : ι, ∑ bb : ι,
        (kappaInv D aa bb * ((μ : ℂ) * k * formTable D c aa)) • (J D k bb μ x))
      = ((μ : ℂ) * k) • J D k c μ x := by
    rw [Finset.sum_comm]
    rw [show (∑ bb : ι, ∑ aa : ι,
          (kappaInv D aa bb * ((μ : ℂ) * k * formTable D c aa)) • (J D k bb μ x))
        = ∑ bb : ι, ((∑ aa : ι, formTable D c aa * kappaInv D aa bb) * ((μ : ℂ) * k))
              • (J D k bb μ x)
        from Finset.sum_congr rfl fun bb _ => by
          rw [← Finset.sum_smul, Finset.sum_mul]; congr 1;
          refine Finset.sum_congr rfl fun aa _ => ?_; ring]
    rw [show (∑ bb : ι, ((∑ aa : ι, formTable D c aa * kappaInv D aa bb) * ((μ : ℂ) * k))
              • (J D k bb μ x))
        = ∑ bb : ι, ((if c = bb then (1:ℂ) else 0) * ((μ : ℂ) * k)) • (J D k bb μ x)
        from Finset.sum_congr rfl fun bb _ => by rw [kappa_kappaInv_S]]
    rw [Finset.sum_eq_single c (fun bb _ hbb => by rw [if_neg (Ne.symm hbb), zero_mul, zero_smul])
        (fun h => absurd (Finset.mem_univ c) h), if_pos rfl, one_mul]
  have hT2 : (∑ aa : ι, ∑ bb : ι,
        (kappaInv D aa bb * ((μ : ℂ) * k * formTable D c bb)) • (J D k aa μ x))
      = ((μ : ℂ) * k) • J D k c μ x := by
    rw [show (∑ aa : ι, ∑ bb : ι,
          (kappaInv D aa bb * ((μ : ℂ) * k * formTable D c bb)) • (J D k aa μ x))
        = ∑ aa : ι, ((∑ bb : ι, formTable D c bb * kappaInv D bb aa) * ((μ : ℂ) * k))
              • (J D k aa μ x)
        from Finset.sum_congr rfl fun aa _ => by
          rw [← Finset.sum_smul, Finset.sum_mul]; congr 1;
          refine Finset.sum_congr rfl fun bb _ => ?_; rw [kappaInv_symm D aa bb]; ring]
    rw [show (∑ aa : ι, ((∑ bb : ι, formTable D c bb * kappaInv D bb aa) * ((μ : ℂ) * k))
              • (J D k aa μ x))
        = ∑ aa : ι, ((if c = aa then (1:ℂ) else 0) * ((μ : ℂ) * k)) • (J D k aa μ x)
        from Finset.sum_congr rfl fun aa _ => by rw [kappa_kappaInv_S]]
    rw [Finset.sum_eq_single c (fun aa _ haa => by rw [if_neg (Ne.symm haa), zero_mul, zero_smul])
        (fun h => absurd (Finset.mem_univ c) h), if_pos rfl, one_mul]
  rw [hT1, hT2, ← smul_add, ← two_smul ℂ (J D k c μ x), smul_smul]
  congr 1
  ring

/-! ## The two structural boundary bands

The two bilinears have mode sum mu. Their normal-ordering flips have
widths mu-1 and mu+1. Contracting both bands with the actual sl3 inverse
trace tensor gives the total Casimir-six residue 6mu. -/

/-- The first-piece summand for `struct0`: `if 0≤p then J^d_{μ-p-1} J^e_{p+1} else J^e_{p+1} J^d_{μ-p-1}`.
Modes `(μ-p-1, p+1)` sum to `μ`. -/
noncomputable def bilin0Summand (k : ℂ) (d e : ι) (μ p : ℤ) (x : Vacuum D k) : Vacuum D k :=
  if 0 ≤ p then J D k d (μ - p - 1) (J D k e (p + 1) x) else J D k e (p + 1) (J D k d (μ - p - 1) x)

/-- The `μ`-mode-sum normal-ordered bilinear for `struct0`. -/
noncomputable def bilin0 (k : ℂ) (d e : ι) (μ : ℤ) (x : Vacuum D k) : Vacuum D k :=
  ∑ᶠ p : ℤ, bilin0Summand D k d e μ p x

/-- `bilin0Summand` has finite support in `p` (`J_regularity` truncates both factors). -/
theorem bilin0Summand_support_finite (k : ℂ) (d e : ι) (μ : ℤ) (x : Vacuum D k) :
    (Function.support (fun p : ℤ => bilin0Summand D k d e μ p x)).Finite := by
  obtain ⟨Be, hBe⟩ := J_regularity D k e x
  obtain ⟨Bd, hBd⟩ := J_regularity D k d x
  apply Set.Finite.subset (Set.finite_Icc (min 0 (μ - Bd)) (max (Be - 2) (-1)))
  intro p hp
  rw [Function.mem_support, bilin0Summand] at hp
  rw [Set.mem_Icc]
  by_cases hpp : 0 ≤ p
  · rw [if_pos hpp] at hp
    have hne : J D k e (p + 1) x ≠ 0 := fun h => hp (by rw [h, map_zero])
    have hpBe : p + 1 < Be := by by_contra hc; push_neg at hc; exact hne (hBe (p + 1) hc)
    exact ⟨le_trans (min_le_left _ _) hpp, le_trans (by omega) (le_max_left _ _)⟩
  · rw [if_neg hpp] at hp
    push_neg at hpp
    have hne : J D k d (μ - p - 1) x ≠ 0 := fun h => hp (by rw [h, map_zero])
    have hd : μ - p - 1 < Bd := by by_contra hc; push_neg at hc; exact hne (hBd _ hc)
    exact ⟨le_trans (min_le_right _ _) (by omega), le_trans (by omega : p ≤ -1) (le_max_right _ _)⟩

/-- The struct0 `Vop`: `Vop0 = ∑_{e'} f(d,e,e') J^{e'}_μ` (modes sum to `μ`, p-independent). -/
noncomputable def Vop0 (k : ℂ) (d e : ι) (μ : ℤ) : End ℂ (Vacuum D k) :=
  ∑ e' : ι, structureConstant D d e e' • J D k e' μ

/-- `Vop0` is antisymmetric: `Vop0(e,d,μ) = -Vop0(d,e,μ)` (from `structureConstant_antisymm`). -/
theorem Vop0_antisymm (k : ℂ) (d e : ι) (μ : ℤ) : Vop0 D k e d μ = - Vop0 D k d e μ := by
  rw [Vop0, Vop0, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun e' _ => ?_)
  rw [structureConstant_antisymm D e d e']
  module

/-- The elementary band commutator `[J^d_{μ-p-1}, J^e_{p+1}] = Vop0 + central` (modes sum `μ`). -/
theorem band0_bracket (k : ℂ) (d e : ι) (μ p : ℤ) :
    J D k d (μ - p - 1) * J D k e (p + 1) - J D k e (p + 1) * J D k d (μ - p - 1)
      = Vop0 D k d e μ
        + (if μ = 0 then (((μ - p - 1 : ℤ) : ℂ) * k * formTable D d e) • (LinearMap.id : End ℂ (Vacuum D k)) else 0) := by
  rw [J_bracket D k d e (μ - p - 1) (p + 1), show (μ - p - 1 + (p + 1) : ℤ) = μ from by ring, Vop0]

/-- The involution `p ↦ μ-p-2` on `ℤ` (the `bilin0` flip). -/
def flipMu2Equiv (μ : ℤ) : ℤ ≃ ℤ :=
  Function.Involutive.toPerm (fun p : ℤ => μ - p - 2) (fun p => by ring)

/-- The first zero-mode normal-ordering involution sends p to mu minus p minus two. -/
@[simp] theorem flipMu2Equiv_apply (μ p : ℤ) : flipMu2Equiv μ p = μ - p - 2 := rfl

/-- `bilin0 e d` reindexed by `p ↦ μ-p-2`. -/
theorem bilin0_eflip (k : ℂ) (e d : ι) (μ : ℤ) (x : Vacuum D k) :
    bilin0 D k e d μ x = ∑ᶠ p : ℤ, bilin0Summand D k e d μ (μ - p - 2) x := by
  rw [bilin0, ← finsum_comp_equiv (flipMu2Equiv μ) (f := fun p => bilin0Summand D k e d μ p x)]
  exact finsum_congr fun p => by rw [flipMu2Equiv_apply]

/-- The second-piece summand for `struct0`:
`if 0≤p then J^e_{-p-1} J^d_{μ+p+1} else J^d_{μ+p+1} J^e_{-p-1}`.  Modes sum to `μ`. -/
noncomputable def bilin02Summand (k : ℂ) (e d : ι) (μ p : ℤ) (x : Vacuum D k) : Vacuum D k :=
  if 0 ≤ p then J D k e (-p - 1) (J D k d (μ + p + 1) x) else J D k d (μ + p + 1) (J D k e (-p - 1) x)

/-- The second noncentral bilinear contribution, summed algebraically over its integer normal-ordering index. Its two current modes sum to mu. -/
noncomputable def bilin02 (k : ℂ) (e d : ι) (μ : ℤ) (x : Vacuum D k) : Vacuum D k :=
  ∑ᶠ p : ℤ, bilin02Summand D k e d μ p x

/-- **The per-`p` struct0Part decomposition** into the two struct0 bilinears. -/
theorem struct0Part_eq (k : ℂ) (c aa bb : ι) (μ p : ℤ) (x : Vacuum D k) :
    struct0Part D k c aa bb μ p x
      = (∑ d, structureConstant D c aa d • bilin0Summand D k d bb μ p x)
        + (∑ d, structureConstant D c bb d • bilin02Summand D k aa d μ p x) := by
  rw [struct0Part, struct0Op, show (μ + (-p - 1) : ℤ) = μ - p - 1 from by ring,
    show (μ + (p + 1) : ℤ) = μ + p + 1 from by ring]
  by_cases hp : 0 ≤ p
  · rw [if_pos hp]
    simp only [bilin0Summand, bilin02Summand, if_pos hp, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul]
  · rw [if_neg hp]
    simp only [bilin0Summand, bilin02Summand, if_neg hp, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul]
    rw [add_comm]

/-! ## §0d  Direct flip-band telescoping for `bilin0` and `bilin02` (modes summing to `μ`)

Both struct0 bilinears have modes summing to `μ`.  We telescope each directly:
`bilin0 d e μ - bilin0 e d μ = μ • Vop0`  and  `bilin02 e d μ - bilin02 d e μ = μ • Vop0` (same `Vop0`),
each by a signed band of width `μ`.  The engine is the existing `bandSmul`. -/

/-- The per-`p` flip difference for `bilin0`: `B(d,e,p) - B(e,d, μ-p-2) = w(p) • Vop0 x`,
`w(p) = bandInd (μ-1) p = [0≤p] - [μ-1 ≤ p]` (band width `μ-1`, central vanishes on the band). -/
theorem bilin0Summand_flip_diff (k : ℂ) (d e : ι) (μ p : ℤ) (x : Vacuum D k) :
    bilin0Summand D k d e μ p x - bilin0Summand D k e d μ (μ - p - 2) x
      = bandInd (μ - 1) p • (Vop0 D k d e μ x) := by
  -- the elementary band commutator on x
  have hPQ : J D k d (μ - p - 1) (J D k e (p + 1) x) - J D k e (p + 1) (J D k d (μ - p - 1) x)
      = Vop0 D k d e μ x
        + (if μ = 0 then (((μ - p - 1 : ℤ) : ℂ) * k * formTable D d e) • (LinearMap.id : End ℂ (Vacuum D k)) else 0) x := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← LinearMap.sub_apply, band0_bracket,
      LinearMap.add_apply]
  -- central vanishes on the band (it is `if μ=0`, and at μ=0 both band edges coincide; we handle by
  -- noting the central term is multiplied into a band where it cancels — see case split below).
  simp only [bilin0Summand, bandInd]
  rw [show (μ - (μ - p - 2) - 1 : ℤ) = p + 1 from by ring,
      show ((μ - p - 2) + 1 : ℤ) = μ - p - 1 from by ring]
  by_cases h0 : 0 ≤ p <;> by_cases hμp : μ - 1 ≤ p
  · -- both 1: w = 0; need the two summands equal.
    -- first: if 0≤p ⟹ J^d_{μ-p-1} J^e_{p+1}; second at index μ-p-2: 0≤μ-p-2 ? p≤μ-2 false (p≥μ-1)
    simp only [if_pos h0, if_pos hμp, if_neg (show ¬ (0:ℤ) ≤ μ - p - 2 from by omega)]
    simp
  · -- 0≤p, ¬(μ-1≤p): band, p ≤ μ-2 so 0≤μ-p-2. w = 1.
    simp only [if_pos h0, if_neg hμp, if_pos (show (0:ℤ) ≤ μ - p - 2 from by omega)]
    rw [hPQ]
    -- central is `if μ=0`; here p ≤ μ-2 and 0≤p ⟹ μ≥2, so μ≠0.
    rw [if_neg (show μ ≠ 0 from by omega)]
    simp
  · -- ¬0≤p, μ-1≤p: band, p<0 and p≥μ-1 ⟹ μ≤0. w = -1.
    simp only [if_neg h0, if_pos hμp, if_neg (show ¬ (0:ℤ) ≤ μ - p - 2 from by omega)]
    rw [show J D k e (p + 1) (J D k d (μ - p - 1) x) - J D k d (μ - p - 1) (J D k e (p + 1) x)
        = -(J D k d (μ - p - 1) (J D k e (p + 1) x) - J D k e (p + 1) (J D k d (μ - p - 1) x)) from by abel,
      hPQ]
    -- central `if μ=0`; here p<0, p≥μ-1 ⟹ μ ≤ p+1 ≤ 0.
    by_cases hμ0 : μ = 0
    · -- μ=0: central fires, but mode μ-p-1 = -p-1, and at the band edge... we must show it cancels.
      -- At μ=0: p≥μ-1=-1 and p<0 ⟹ p = -1, so μ-p-1 = 0, central scalar = 0•k•κ = 0.
      rw [if_pos hμ0, show (μ - p - 1 : ℤ) = 0 from by omega]
      simp
    · rw [if_neg hμ0]; simp
  · -- neither: p<0 and p>μ-2 (¬μ-1≤p ⟹ p<μ-1 ⟹ p≤μ-2). w=0. second index μ-p-2 ≥0.
    simp only [if_neg h0, if_neg hμp, if_pos (show (0:ℤ) ≤ μ - p - 2 from by omega)]
    simp

/-- **`bilin0` antisymmetry**: `bilin0 d e μ - bilin0 e d μ = (μ-1) • Vop0(d,e,μ)`. -/
theorem bilin0_antisymm (k : ℂ) (d e : ι) (μ : ℤ) (x : Vacuum D k) :
    bilin0 D k d e μ x - bilin0 D k e d μ x = ((μ : ℂ) - 1) • (Vop0 D k d e μ x) := by
  rw [bilin0, bilin0_eflip]
  have hfin2 : (Function.support (fun p : ℤ => bilin0Summand D k e d μ (μ - p - 2) x)).Finite := by
    have heq : (Function.support (fun p : ℤ => bilin0Summand D k e d μ (μ - p - 2) x))
        = (flipMu2Equiv μ) ⁻¹' (Function.support (fun q : ℤ => bilin0Summand D k e d μ q x)) := by
      ext p; simp only [Function.mem_support, Set.mem_preimage, flipMu2Equiv_apply]
    rw [heq]
    exact (bilin0Summand_support_finite D k e d μ x).preimage ((flipMu2Equiv μ).injective.injOn)
  rw [← finsum_sub_distrib (bilin0Summand_support_finite D k d e μ x) hfin2,
    finsum_congr (fun p => bilin0Summand_flip_diff D k d e μ p x)]
  show (∑ᶠ p : ℤ, bandInd (μ - 1) p • (Vop0 D k d e μ x)) = ((μ : ℂ) - 1) • (Vop0 D k d e μ x)
  rw [bandSmul, ← Int.cast_smul_eq_zsmul ℂ (μ - 1)]
  push_cast; ring_nf

/-! ### `bilin02` flip-band telescoping (count `-(μ+1)` of `Vop0(e,d)`) -/

/-- Lower truncation of each current bounds the support of the second bilinear summand on a fixed vector. -/
theorem bilin02Summand_support_finite (k : ℂ) (e d : ι) (μ : ℤ) (x : Vacuum D k) :
    (Function.support (fun p : ℤ => bilin02Summand D k e d μ p x)).Finite := by
  obtain ⟨Bd, hBd⟩ := J_regularity D k d x
  obtain ⟨Be, hBe⟩ := J_regularity D k e x
  apply Set.Finite.subset (Set.finite_Icc (min 0 (-Be)) (max (Bd - μ - 1) (-1)))
  intro p hp
  rw [Function.mem_support, bilin02Summand] at hp
  rw [Set.mem_Icc]
  by_cases hpp : 0 ≤ p
  · rw [if_pos hpp] at hp
    have hne : J D k d (μ + p + 1) x ≠ 0 := fun h => hp (by rw [h, map_zero])
    have hb : μ + p + 1 < Bd := by by_contra hc; push_neg at hc; exact hne (hBd _ hc)
    exact ⟨le_trans (min_le_left _ _) hpp, le_trans (by omega) (le_max_left _ _)⟩
  · rw [if_neg hpp] at hp
    push_neg at hpp
    have hne : J D k e (-p - 1) x ≠ 0 := fun h => hp (by rw [h, map_zero])
    have hb : -p - 1 < Be := by by_contra hc; push_neg at hc; exact hne (hBe _ hc)
    exact ⟨le_trans (min_le_right _ _) (by omega), le_trans (by omega : p ≤ -1) (le_max_right _ _)⟩

/-- The elementary band commutator for `bilin02`: `[J^e_{-p-1}, J^d_{μ+p+1}] = Vop0(e,d,μ) + central`
(modes sum `μ`). -/
theorem band02_bracket (k : ℂ) (e d : ι) (μ p : ℤ) :
    J D k e (-p - 1) * J D k d (μ + p + 1) - J D k d (μ + p + 1) * J D k e (-p - 1)
      = Vop0 D k e d μ
        + (if μ = 0 then (((-p - 1 : ℤ) : ℂ) * k * formTable D e d) • (LinearMap.id : End ℂ (Vacuum D k)) else 0) := by
  rw [J_bracket D k e d (-p - 1) (μ + p + 1), show (-p - 1 + (μ + p + 1) : ℤ) = μ from by ring, Vop0]

/-- The involution `p ↦ -μ-p-2` on `ℤ` (the `bilin02` flip). -/
def flipNeg2Equiv (μ : ℤ) : ℤ ≃ ℤ :=
  Function.Involutive.toPerm (fun p : ℤ => -μ - p - 2) (fun p => by ring)

/-- The second zero-mode normal-ordering involution sends p to minus mu minus p minus two. -/
@[simp] theorem flipNeg2Equiv_apply (μ p : ℤ) : flipNeg2Equiv μ p = -μ - p - 2 := rfl

/-- `bilin02 d e` reindexed by `p ↦ -μ-p-2`. -/
theorem bilin02_eflip (k : ℂ) (d e : ι) (μ : ℤ) (x : Vacuum D k) :
    bilin02 D k d e μ x = ∑ᶠ p : ℤ, bilin02Summand D k d e μ (-μ - p - 2) x := by
  rw [bilin02, ← finsum_comp_equiv (flipNeg2Equiv μ) (f := fun p => bilin02Summand D k d e μ p x)]
  exact finsum_congr fun p => by rw [flipNeg2Equiv_apply]

/-- The per-`p` flip difference for `bilin02`: `B2(e,d,p) - B2(d,e,-μ-p-2) = bandInd(-μ-1) p • Vop0(e,d) x`. -/
theorem bilin02Summand_flip_diff (k : ℂ) (e d : ι) (μ p : ℤ) (x : Vacuum D k) :
    bilin02Summand D k e d μ p x - bilin02Summand D k d e μ (-μ - p - 2) x
      = bandInd (-μ - 1) p • (Vop0 D k e d μ x) := by
  have hPQ : J D k e (-p - 1) (J D k d (μ + p + 1) x) - J D k d (μ + p + 1) (J D k e (-p - 1) x)
      = Vop0 D k e d μ x
        + (if μ = 0 then (((-p - 1 : ℤ) : ℂ) * k * formTable D e d) • (LinearMap.id : End ℂ (Vacuum D k)) else 0) x := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← LinearMap.sub_apply, band02_bracket,
      LinearMap.add_apply]
  simp only [bilin02Summand, bandInd]
  rw [show (-(-μ - p - 2) - 1 : ℤ) = μ + p + 1 from by ring,
      show (μ + (-μ - p - 2) + 1 : ℤ) = -p - 1 from by ring]
  by_cases h0 : 0 ≤ p <;> by_cases hμp : -μ - 1 ≤ p
  · -- both 1: w=0. second index -μ-p-2: 0≤? p≤-μ-2, false (p≥-μ-1). neg branch.
    simp only [if_pos h0, if_pos hμp, if_neg (show ¬ (0:ℤ) ≤ -μ - p - 2 from by omega)]
    simp
  · -- 0≤p, ¬(-μ-1≤p): band, p≤-μ-2 so 0≤-μ-p-2. w=1.
    simp only [if_pos h0, if_neg hμp, if_pos (show (0:ℤ) ≤ -μ - p - 2 from by omega)]
    rw [hPQ]
    -- central if μ=0; here 0≤p≤-μ-2 ⟹ μ≤-2, μ≠0.
    rw [if_neg (show μ ≠ 0 from by omega)]
    simp
  · -- ¬0≤p, -μ-1≤p: band, p<0, p≥-μ-1 ⟹ μ≥0. w=-1.
    simp only [if_neg h0, if_pos hμp, if_neg (show ¬ (0:ℤ) ≤ -μ - p - 2 from by omega)]
    rw [show J D k d (μ + p + 1) (J D k e (-p - 1) x) - J D k e (-p - 1) (J D k d (μ + p + 1) x)
        = -(J D k e (-p - 1) (J D k d (μ + p + 1) x) - J D k d (μ + p + 1) (J D k e (-p - 1) x)) from by abel,
      hPQ]
    by_cases hμ0 : μ = 0
    · -- μ=0: p<0, p≥-1 ⟹ p=-1, so -p-1 = 0, central scalar = 0.
      rw [if_pos hμ0, show (-p - 1 : ℤ) = 0 from by omega]; simp
    · rw [if_neg hμ0]; simp
  · -- neither: p<0, ¬(-μ-1≤p) ⟹ p<-μ-1 ⟹ p≤-μ-2. w=0. second index ≥0.
    simp only [if_neg h0, if_neg hμp, if_pos (show (0:ℤ) ≤ -μ - p - 2 from by omega)]
    simp

/-- **`bilin02` antisymmetry**, expressed via `Vop0(d,e)`: `bilin02 e d μ - bilin02 d e μ = (μ+1) • Vop0(d,e,μ)`. -/
theorem bilin02_antisymm (k : ℂ) (e d : ι) (μ : ℤ) (x : Vacuum D k) :
    bilin02 D k e d μ x - bilin02 D k d e μ x = ((μ : ℂ) + 1) • (Vop0 D k d e μ x) := by
  rw [bilin02, bilin02_eflip]
  have hfin2 : (Function.support (fun p : ℤ => bilin02Summand D k d e μ (-μ - p - 2) x)).Finite := by
    have heq : (Function.support (fun p : ℤ => bilin02Summand D k d e μ (-μ - p - 2) x))
        = (flipNeg2Equiv μ) ⁻¹' (Function.support (fun q : ℤ => bilin02Summand D k d e μ q x)) := by
      ext p; simp only [Function.mem_support, Set.mem_preimage, flipNeg2Equiv_apply]
    rw [heq]
    exact (bilin02Summand_support_finite D k d e μ x).preimage ((flipNeg2Equiv μ).injective.injOn)
  rw [← finsum_sub_distrib (bilin02Summand_support_finite D k e d μ x) hfin2,
    finsum_congr (fun p => bilin02Summand_flip_diff D k e d μ p x)]
  show (∑ᶠ p : ℤ, bandInd (-μ - 1) p • (Vop0 D k e d μ x)) = ((μ : ℂ) + 1) • (Vop0 D k d e μ x)
  rw [bandSmul, ← Int.cast_smul_eq_zsmul ℂ (-μ - 1),
    show (Vop0 D k e d μ) x = (-(Vop0 D k d e μ)) x from by rw [Vop0_antisymm],
    LinearMap.neg_apply, smul_neg, ← neg_smul]
  congr 1
  push_cast; ring

/-! ## §0e  The summed struct0Part and the dual-Coxeter contraction → `6μ • J^c_μ` -/

/-- **The summed struct0Part**:
`∑ᶠ_p struct0Part = ∑_d f(c,aa,d) bilin0(d,bb,μ) + ∑_d f(c,bb,d) bilin02(aa,d,μ)`. -/
theorem struct0Part_finsum (k : ℂ) (c aa bb : ι) (μ : ℤ) (x : Vacuum D k) :
    (∑ᶠ p : ℤ, struct0Part D k c aa bb μ p x)
      = (∑ d, structureConstant D c aa d • bilin0 D k d bb μ x) + (∑ d, structureConstant D c bb d • bilin02 D k aa d μ x) := by
  have hf1 : ∀ d : ι,
      (Function.support (fun p : ℤ => structureConstant D c aa d • bilin0Summand D k d bb μ p x)).Finite :=
    fun d => (bilin0Summand_support_finite D k d bb μ x).subset (fun p hp => by
      rw [Function.mem_support] at hp ⊢; exact fun h => hp (by rw [h, smul_zero]))
  have hf2 : ∀ d : ι,
      (Function.support (fun p : ℤ => structureConstant D c bb d • bilin02Summand D k aa d μ p x)).Finite :=
    fun d => (bilin02Summand_support_finite D k aa d μ x).subset (fun p hp => by
      rw [Function.mem_support] at hp ⊢; exact fun h => hp (by rw [h, smul_zero]))
  have hAfin : (Function.support
      (fun p : ℤ => ∑ d, structureConstant D c aa d • bilin0Summand D k d bb μ p x)).Finite := by
    apply Set.Finite.subset ((Finset.univ : Finset (ι)).finite_toSet.biUnion (fun d _ => hf1 d))
    intro p hp; rw [Function.mem_support] at hp
    simp only [Set.mem_iUnion]
    by_contra hcon; push_neg at hcon; apply hp
    refine Finset.sum_eq_zero fun d _ => ?_
    have := hcon d (Finset.mem_coe.mpr (Finset.mem_univ d))
    rwa [Function.mem_support, not_not] at this
  have hBfin : (Function.support
      (fun p : ℤ => ∑ d, structureConstant D c bb d • bilin02Summand D k aa d μ p x)).Finite := by
    apply Set.Finite.subset ((Finset.univ : Finset (ι)).finite_toSet.biUnion (fun d _ => hf2 d))
    intro p hp; rw [Function.mem_support] at hp
    simp only [Set.mem_iUnion]
    by_contra hcon; push_neg at hcon; apply hp
    refine Finset.sum_eq_zero fun d _ => ?_
    have := hcon d (Finset.mem_coe.mpr (Finset.mem_univ d))
    rwa [Function.mem_support, not_not] at this
  rw [finsum_congr (fun p => struct0Part_eq D k c aa bb μ p x), finsum_add_distrib hAfin hBfin]
  congr 1
  · rw [← sum_finsum_comm Finset.univ
      (fun d p => structureConstant D c aa d • bilin0Summand D k d bb μ p x) (fun d _ => hf1 d)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← smul_finsum' (structureConstant D c aa d) (bilin0Summand_support_finite D k d bb μ x)]
    rfl
  · rw [← sum_finsum_comm Finset.univ
      (fun d p => structureConstant D c bb d • bilin02Summand D k aa d μ p x) (fun d _ => hf2 d)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← smul_finsum' (structureConstant D c bb d) (bilin02Summand_support_finite D k aa d μ x)]
    rfl

/-- The `Vop0` contraction: `∑_{X,d} graised(X,c,d) • ((μ-1) • Vop0(d,X,μ)) = -(6(μ-1)) • J^c_μ x`.
(`graised_structureConstant_contract = -6δ`; `Vop0(d,X,μ) = ∑_{e'} f(d,X,e') J^{e'}_μ`, mode `μ`.) -/
theorem graisedVop0_contract (k : ℂ) (c : ι) (μ : ℤ) (s : ℂ) (x : Vacuum D k) :
    (∑ X : ι, ∑ d : ι, graised D X c d • (s • Vop0 D k d X μ x))
      = (-(2 * D.h : ℂ) * s) • J D k c μ x := by
  have hterm : ∀ X d : ι, graised D X c d • (s • Vop0 D k d X μ x)
      = ∑ e' : ι, (s * (graised D X c d * structureConstant D d X e')) • J D k e' μ x := by
    intro X d
    rw [Vop0, LinearMap.sum_apply, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun e' _ => ?_)
    rw [LinearMap.smul_apply, smul_smul, smul_smul]
    congr 1; ring
  rw [Finset.sum_congr rfl (fun X _ => Finset.sum_congr rfl (fun d _ => hterm X d))]
  rw [Finset.sum_congr rfl (fun X _ => Finset.sum_comm), Finset.sum_comm]
  rw [show (∑ e' : ι, ∑ X : ι, ∑ d : ι,
        (s * (graised D X c d * structureConstant D d X e')) • J D k e' μ x)
      = ∑ e' : ι, (s * (∑ X : ι, ∑ d : ι, graised D X c d * structureConstant D d X e'))
          • J D k e' μ x from
    Finset.sum_congr rfl (fun e' _ => by
      rw [Finset.mul_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl (fun X _ => ?_)
      rw [Finset.mul_sum, Finset.sum_smul])]
  rw [Finset.sum_congr rfl (fun e' _ => by rw [graised_structureConstant_contract])]
  rw [Finset.sum_eq_single c
    (fun e' _ he' => by rw [if_neg (Ne.symm he'), mul_neg, mul_zero, neg_zero, zero_smul])
    (fun h => absurd (Finset.mem_univ c) h)]
  rw [if_pos rfl]
  congr 1; ring

/-- **The struct0 residue** (the `Lsug 0` normal-ordering anomaly):
`∑_{aa,bb} κ⁻¹(aa,bb) • ∑ᶠ_p struct0Part k c aa bb μ p x = 6μ • Jᶜ_μ x`. -/
theorem struct0_residue_value (k : ℂ) (c : ι) (μ : ℤ) (x : Vacuum D k) :
    (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb • ∑ᶠ p : ℤ, struct0Part D k c aa bb μ p x)
      = (2 * D.h * μ : ℂ) • J D k c μ x := by
  -- Sgr0 = ∑_{X,d} graised(X,c,d) bilin0(d,X,μ);  Sgr2 = ∑_{X,d} graised(X,c,d) bilin02(X,d,μ)
  set Sgr0 : Vacuum D k := ∑ X : ι, ∑ d : ι, graised D X c d • bilin0 D k d X μ x with hSgr0
  set Sgr2 : Vacuum D k := ∑ X : ι, ∑ d : ι, graised D X c d • bilin02 D k X d μ x with hSgr2
  -- Step 1: struct0Part_finsum into each ∑ᶠ, split the `+`
  have hstep1 : (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb • ∑ᶠ p : ℤ, struct0Part D k c aa bb μ p x)
      = (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb •
          ∑ d : ι, structureConstant D c aa d • bilin0 D k d bb μ x)
        + (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb •
          ∑ d : ι, structureConstant D c bb d • bilin02 D k aa d μ x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun aa _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun bb _ => ?_)
    rw [struct0Part_finsum, smul_add]
  rw [hstep1]
  -- T1 = -Sgr0 (contract κ⁻¹ f(c,aa,d) over aa → -graised(bb,c,d), bilin0(d,bb))
  have hT1 : (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb •
        ∑ d : ι, structureConstant D c aa d • bilin0 D k d bb μ x) = -Sgr0 := by
    rw [hSgr0, ← Finset.sum_neg_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun bb _ => ?_)
    rw [← Finset.sum_neg_distrib]
    have hdist : ∀ aa : ι, kappaInv D aa bb • ∑ d : ι, structureConstant D c aa d • bilin0 D k d bb μ x
        = ∑ d : ι, (kappaInv D aa bb * structureConstant D c aa d) • bilin0 D k d bb μ x :=
      fun aa => by rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun d _ => by rw [smul_smul])
    rw [Finset.sum_congr rfl (fun aa _ => hdist aa), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_smul, kappaInv_structureConstant_eq_graised, neg_smul]
  -- T2 = -Sgr2 (contract κ⁻¹ f(c,bb,d) over bb → -graised(aa,c,d), bilin02(aa,d))
  have hT2 : (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb •
        ∑ d : ι, structureConstant D c bb d • bilin02 D k aa d μ x) = -Sgr2 := by
    rw [hSgr2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun aa _ => ?_)
    rw [← Finset.sum_neg_distrib]
    have hdist : ∀ bb : ι, kappaInv D aa bb • ∑ d : ι, structureConstant D c bb d • bilin02 D k aa d μ x
        = ∑ d : ι, (kappaInv D aa bb * structureConstant D c bb d) • bilin02 D k aa d μ x :=
      fun bb => by rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun d _ => by rw [smul_smul])
    rw [Finset.sum_congr rfl (fun bb _ => hdist bb), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_smul,
      show (∑ bb : ι, kappaInv D aa bb * structureConstant D c bb d) = -graised D aa c d from by
        rw [← kappaInv_structureConstant_eq_graised D aa c d]
        exact Finset.sum_congr rfl (fun bb _ => by rw [kappaInv_symm D aa bb]),
      neg_smul]
  rw [hT1, hT2]
  -- Now -Sgr0 + -Sgr2 = -(Sgr0 + Sgr2).  Compute Sgr0+Sgr2 via the antisymmetrisations.
  -- Sgr0 = ∑ graised(X,c,d) bilin0(d,X);  Sgr2 = ∑ graised(X,c,d) bilin02(X,d).
  -- Swap d↔X in Sgr2 and use graised_antisymm: Sgr2 = -∑ graised(d,c,X) bilin02(X,d) ... let us instead
  -- directly compute Sgr0 - Sgr0swap and Sgr2 - Sgr2swap.
  -- Sgr0swap := ∑ graised(X,c,d) bilin0(X,d);  then Sgr0 = -Sgr0swap (graised_antisymm) gives
  -- Sgr0 - Sgr0swap = 2 Sgr0; pairing (bilin0(d,X) - bilin0(X,d)) = (μ-1) Vop0(d,X).
  have hSgr0swap : Sgr0 = -(∑ X : ι, ∑ d : ι, graised D X c d • bilin0 D k X d μ x) := by
    rw [hSgr0, ← Finset.sum_neg_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun X _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [graised_antisymm D d c X, neg_smul]
  have hSgr2swap : Sgr2 = -(∑ X : ι, ∑ d : ι, graised D X c d • bilin02 D k d X μ x) := by
    rw [hSgr2, ← Finset.sum_neg_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun X _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [graised_antisymm D d c X, neg_smul]
  -- 2 Sgr0 = Sgr0 - (-Sgr0) = Sgr0 - Sgr0swap' = ∑ graised(X,c,d)(bilin0(d,X)-bilin0(X,d)) = ∑ g (μ-1)Vop0(d,X)
  have h2Sgr0 : Sgr0 - (∑ X : ι, ∑ d : ι, graised D X c d • bilin0 D k X d μ x)
      = (-(2 * D.h : ℂ) * ((μ:ℂ)-1)) • J D k c μ x := by
    rw [hSgr0, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun X _ => (Finset.sum_sub_distrib _ _).symm)]
    rw [Finset.sum_congr rfl (fun X _ => Finset.sum_congr rfl (fun d _ => by
      rw [← smul_sub, bilin0_antisymm]))]
    exact graisedVop0_contract D k c μ ((μ:ℂ)-1) x
  -- 2 Sgr2 = Sgr2 - Sgr2swap' = ∑ graised(X,c,d)(bilin02(X,d)-bilin02(d,X)) = ∑ g (-μ-1)Vop0(X,d)
  --   = ∑ g (-μ-1)(-Vop0(d,X)) = ∑ g (μ+1) Vop0(d,X)
  have h2Sgr2 : Sgr2 - (∑ X : ι, ∑ d : ι, graised D X c d • bilin02 D k d X μ x)
      = (-(2 * D.h : ℂ) * (μ+1:ℂ)) • J D k c μ x := by
    rw [hSgr2, ← Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun X _ => (Finset.sum_sub_distrib _ _).symm)]
    rw [Finset.sum_congr rfl (fun X _ => Finset.sum_congr rfl (fun d _ => by
      rw [← smul_sub, bilin02_antisymm]))]
    exact graisedVop0_contract D k c μ ((μ:ℂ)+1) x
  -- Sgr0 = -Sgr0swap', so Sgr0 - Sgr0swap' = 2 Sgr0 ⟹ Sgr0 = (1/2) h2Sgr0; similarly Sgr2.
  have hSgr0val : Sgr0 = (-(D.h : ℂ) * ((μ:ℂ)-1)) • J D k c μ x := by
    have hswapval : (∑ X : ι, ∑ d : ι, graised D X c d • bilin0 D k X d μ x) = -Sgr0 := by
      rw [hSgr0swap]; abel
    have htwo : (2 : ℂ) • Sgr0 = (-(2 * D.h : ℂ) * ((μ:ℂ)-1)) • J D k c μ x := by
      rw [show (2 : ℂ) • Sgr0
          = Sgr0 - (∑ X : ι, ∑ d : ι, graised D X c d • bilin0 D k X d μ x) from by
        rw [hswapval, two_smul]; abel]
      rw [h2Sgr0]
    have h2 := congrArg (fun v => (2⁻¹ : ℂ) • v) htwo
    simp only [smul_smul] at h2
    rw [show (2⁻¹ : ℂ) * 2 = 1 from by norm_num, one_smul] at h2
    rw [h2]; congr 1; ring
  have hSgr2val : Sgr2 = (-(D.h : ℂ) * (μ+1:ℂ)) • J D k c μ x := by
    have hswapval : (∑ X : ι, ∑ d : ι, graised D X c d • bilin02 D k d X μ x) = -Sgr2 := by
      rw [hSgr2swap]; abel
    have htwo : (2 : ℂ) • Sgr2 = (-(2 * D.h : ℂ) * (μ+1:ℂ)) • J D k c μ x := by
      rw [show (2 : ℂ) • Sgr2
          = Sgr2 - (∑ X : ι, ∑ d : ι, graised D X c d • bilin02 D k d X μ x) from by
        rw [hswapval, two_smul]; abel]
      rw [h2Sgr2]
    have h2 := congrArg (fun v => (2⁻¹ : ℂ) • v) htwo
    simp only [smul_smul] at h2
    rw [show (2⁻¹ : ℂ) * 2 = 1 from by norm_num, one_smul] at h2
    rw [h2]; congr 1; ring
  rw [show (-Sgr0 + -Sgr2) = -(Sgr0 + Sgr2) from by abel, hSgr0val, hSgr2val,
    ← add_smul, ← neg_smul]
  congr 1
  push_cast; ring

/-! ## §0f  The `Hbr0` collapse and the `Lsug 0` commutator -/

/-- The `sug0TermJ` per-pair operator applied to `x`, finitely supported in `p`. -/
theorem sug0TermJ_support_finite (k : ℂ) (aa bb : ι) (x : Vacuum D k) :
    (Function.support (fun p : ℤ => sug0TermJ D k aa bb p x)).Finite := by
  obtain ⟨Bb, hBb⟩ := J_regularity D k bb x
  obtain ⟨Ba, hBa⟩ := J_regularity D k aa x
  apply Set.Finite.subset (Set.finite_Icc (min 0 (-Ba)) (max (Bb - 2) (-1)))
  intro p hp
  rw [Function.mem_support, sug0TermJ_apply] at hp
  rw [Set.mem_Icc]
  by_cases hpp : 0 ≤ p
  · rw [if_pos hpp] at hp
    have hne : J D k bb (p + 1) x ≠ 0 := fun h => hp (by rw [h, map_zero])
    have : p + 1 < Bb := by by_contra hc; push_neg at hc; exact hne (hBb _ hc)
    exact ⟨le_trans (min_le_left _ _) hpp, le_trans (by omega) (le_max_left _ _)⟩
  · rw [if_neg hpp] at hp
    push_neg at hpp
    have hne : J D k aa (-p - 1) x ≠ 0 := fun h => hp (by rw [h, map_zero])
    have : -p - 1 < Ba := by by_contra hc; push_neg at hc; exact hne (hBa _ hc)
    exact ⟨le_trans (min_le_right _ _) (by omega), le_trans (by omega : p ≤ -1) (le_max_right _ _)⟩

/-- The per-pair bracket `[sug0TermJ aa bb p, J^c_μ]` applied to `x`, finitely supported in `p`. -/
theorem pair0_bracket_support_finite (k : ℂ) (aa bb c : ι) (μ : ℤ) (x : Vacuum D k) :
    (Function.support (fun p : ℤ =>
      sug0TermJ D k aa bb p (J D k c μ x) - J D k c μ (sug0TermJ D k aa bb p x))).Finite := by
  apply Set.Finite.subset
    ((sug0TermJ_support_finite D k aa bb (J D k c μ x)).union (sug0TermJ_support_finite D k aa bb x))
  intro p hp; rw [Function.mem_support] at hp
  simp only [Set.mem_union, Function.mem_support]
  by_contra hcon; push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  exact hp (by rw [h1, h2, map_zero, sub_zero])

/-- The noncentral commutator summand has finite support, by its decomposition into two finite-support current bilinears. -/
theorem struct0Part_support_finite (k : ℂ) (c aa bb : ι) (μ : ℤ) (x : Vacuum D k) :
    (Function.support (fun p : ℤ => struct0Part D k c aa bb μ p x)).Finite := by
  have hbody : (Function.support (fun p : ℤ =>
      sug0TermJ D k aa bb p (J D k c μ x) - J D k c μ (sug0TermJ D k aa bb p x))).Finite :=
    pair0_bracket_support_finite D k aa bb c μ x
  have hcen := central0Part_support_finite D k c aa bb μ x
  apply Set.Finite.subset (hbody.union hcen)
  intro p hp
  rw [Function.mem_support] at hp
  by_contra hc
  rw [Set.mem_union] at hc
  push_neg at hc
  rw [Function.notMem_support, Function.notMem_support] at hc
  apply hp
  have hs := inner0_body_split D k c aa bb μ p x
  rw [hc.1, hc.2, add_zero, eq_comm, neg_eq_zero] at hs
  exact hs

/-- The finsum of the inner0 body splits as `−(Σᶠ struct0 + Σᶠ central0)`. -/
theorem inner0_finsum_split (k : ℂ) (c aa bb : ι) (μ : ℤ) (x : Vacuum D k) :
    (∑ᶠ p : ℤ, (sug0TermJ D k aa bb p (J D k c μ x) - J D k c μ (sug0TermJ D k aa bb p x)))
      = - ((∑ᶠ p : ℤ, struct0Part D k c aa bb μ p x) + (∑ᶠ p : ℤ, central0Part D k c aa bb μ p x)) := by
  have hcen := central0Part_support_finite D k c aa bb μ x
  have hstr := struct0Part_support_finite D k c aa bb μ x
  rw [finsum_congr (fun p => inner0_body_split D k c aa bb μ p x)]
  rw [finsum_congr (fun p => (neg_add _ _) : ∀ p,
        -(struct0Part D k c aa bb μ p x + central0Part D k c aa bb μ p x)
          = -(struct0Part D k c aa bb μ p x) + -(central0Part D k c aa bb μ p x))]
  rw [finsum_add_distrib (hstr.subset (fun p hp => by
        rw [Function.mem_support] at hp ⊢; exact fun h => hp (by rw [h, neg_zero])))
      (hcen.subset (fun p hp => by
        rw [Function.mem_support] at hp ⊢; exact fun h => hp (by rw [h, neg_zero])))]
  rw [finsum_neg_distrib, finsum_neg_distrib, ← neg_add]

/-- The `Lsug 0` summand operator (κ⁻¹-summed `sug0TermJ`, pre-`x`). -/
noncomputable def L0sum (k : ℂ) (p : ℤ) : End ℂ (Vacuum D k) :=
  ∑ aa, ∑ bb, kappaInv D aa bb • sug0TermJ D k aa bb p

/-- Evaluation commutes with the finite inverse-form contraction defining each Sugawara zero-mode summand. -/
theorem L0sum_apply (k : ℂ) (p : ℤ) (x : Vacuum D k) :
    L0sum D k p x = ∑ aa, ∑ bb, kappaInv D aa bb • sug0TermJ D k aa bb p x := by
  rw [L0sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun aa _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun bb _ => ?_
  rw [LinearMap.smul_apply]

/-- At each vector the contracted zero-mode sum is supported on finitely many integers, making the subsequent reindexings algebraic. -/
theorem L0sum_support_finite (k : ℂ) (x : Vacuum D k) :
    (Function.support (fun p : ℤ => L0sum D k p x)).Finite := by
  apply Set.Finite.subset ((Finset.univ : Finset (ι)).finite_toSet.biUnion
    (fun aa _ => (Finset.univ : Finset (ι)).finite_toSet.biUnion
      (fun bb _ => sug0TermJ_support_finite D k aa bb x)))
  intro p hp; rw [Function.mem_support, L0sum_apply] at hp
  simp only [Set.mem_iUnion]
  by_contra hcon; push_neg at hcon; apply hp
  refine Finset.sum_eq_zero fun aa _ => Finset.sum_eq_zero fun bb _ => ?_
  have := hcon aa (Finset.mem_coe.mpr (Finset.mem_univ aa)) bb
    (Finset.mem_coe.mpr (Finset.mem_univ bb))
  rw [Function.mem_support, not_not] at this
  rw [this, smul_zero]

/-- `Lsug k 0 x = c₀ • ∑ᶠ_p L0sum k p x`. -/
theorem Lsug0_eq_finsum_L0sum (k : ℂ) (x : Vacuum D k) :
    Lsug D k 0 x = c0 D k • ∑ᶠ p : ℤ, L0sum D k p x := by
  rw [Lsug0_apply]
  refine congrArg (c0 D k • ·) ?_
  have hfin : ∀ aa bb : ι,
      (Function.support (fun p : ℤ => kappaInv D aa bb • sug0TermJ D k aa bb p x)).Finite := by
    intro aa bb
    apply (sug0TermJ_support_finite D k aa bb x).subset
    intro p hp; rw [Function.mem_support] at hp ⊢
    exact fun h => hp (by rw [h, smul_zero])
  rw [show (∑ aa : ι, ∑ bb : ι, kappaInv D aa bb • ∑ᶠ p : ℤ, sug0TermJ D k aa bb p x)
      = ∑ aa : ι, ∑ bb : ι, ∑ᶠ p : ℤ, kappaInv D aa bb • sug0TermJ D k aa bb p x from by
    refine Finset.sum_congr rfl fun aa _ => Finset.sum_congr rfl fun bb _ => ?_
    rw [smul_finsum' (kappaInv D aa bb) (sug0TermJ_support_finite D k aa bb x)]]
  rw [show (∑ aa : ι, ∑ bb : ι, ∑ᶠ p : ℤ, kappaInv D aa bb • sug0TermJ D k aa bb p x)
      = ∑ aa : ι, ∑ᶠ p : ℤ, ∑ bb : ι, kappaInv D aa bb • sug0TermJ D k aa bb p x from by
    refine Finset.sum_congr rfl fun aa _ => ?_
    rw [sum_finsum_comm Finset.univ
      (fun bb p => kappaInv D aa bb • sug0TermJ D k aa bb p x) (fun bb _ => hfin aa bb)]]
  rw [sum_finsum_comm Finset.univ
    (fun aa p => ∑ bb : ι, kappaInv D aa bb • sug0TermJ D k aa bb p x)
    (fun aa _ => by
      apply Set.Finite.subset ((Finset.univ : Finset (ι)).finite_toSet.biUnion
        (fun bb _ => hfin aa bb))
      intro p hp; rw [Function.mem_support] at hp
      simp only [Set.mem_iUnion]
      by_contra hcon
      push_neg at hcon
      apply hp
      refine Finset.sum_eq_zero fun bb _ => ?_
      have := hcon bb (Finset.mem_coe.mpr (Finset.mem_univ bb))
      rwa [Function.mem_support, not_not] at this)]
  refine finsum_congr fun p => (L0sum_apply D k p x).symm

/-- The per-`p` commutator of `L0sum` against `J^c_μ` applied to `x` equals the κ⁻¹-summed inner body. -/
theorem L0sum_comm_apply (k : ℂ) (c : ι) (μ p : ℤ) (x : Vacuum D k) :
    L0sum D k p (J D k c μ x) - J D k c μ (L0sum D k p x)
      = ∑ aa : ι, ∑ bb : ι, kappaInv D aa bb •
          (sug0TermJ D k aa bb p (J D k c μ x) - J D k c μ (sug0TermJ D k aa bb p x)) := by
  rw [L0sum_apply, L0sum_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun aa _ => ?_
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun bb _ => ?_
  rw [map_smul, ← smul_sub]

/-- The commutator of the zero-mode summands with a fixed current has finite support on every vector. -/
theorem L0sum_comm_support_finite (k : ℂ) (c : ι) (μ : ℤ) (x : Vacuum D k) :
    (Function.support (fun p : ℤ => L0sum D k p (J D k c μ x) - J D k c μ (L0sum D k p x))).Finite := by
  apply Set.Finite.subset
    ((L0sum_support_finite D k (J D k c μ x)).union (L0sum_support_finite D k x))
  intro p hp; rw [Function.mem_support] at hp
  simp only [Set.mem_union, Function.mem_support]
  by_contra hcon; push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  exact hp (by rw [h1, h2, map_zero, sub_zero])

/-- **The full `Lsug 0` commutator as a single finsum**:
`(Lsug 0 · J^c_μ - J^c_μ · Lsug 0) x = c₀ • ∑ᶠ_p (L0sum p (J^c x) - J^c (L0sum p x))`. -/
theorem Lsug0_comm_eq_finsum (k : ℂ) (c : ι) (μ : ℤ) (x : Vacuum D k) :
    (Lsug D k 0 * J D k c μ - J D k c μ * Lsug D k 0) x
      = c0 D k • ∑ᶠ p : ℤ, (L0sum D k p (J D k c μ x) - J D k c μ (L0sum D k p x)) := by
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
    Lsug0_eq_finsum_L0sum D k (J D k c μ x), Lsug0_eq_finsum_L0sum D k x]
  rw [map_smul, map_finsum (J D k c μ) (L0sum_support_finite D k x), ← smul_sub]
  congr 1
  rw [← finsum_sub_distrib (L0sum_support_finite D k (J D k c μ x))
      ((L0sum_support_finite D k x).subset (fun p hp => by
        rw [Function.mem_support] at hp ⊢; exact fun h => hp (by rw [h, map_zero])))]

/-- **The `Lsug 0` current covariance** (the m=0 analog of `Lcomm_current`):
`[Lsug 0, J^c_μ] x = -μ • J^c_μ x` (needs `k + 3 ≠ 0`; `c₀ = (2(k+3))⁻¹` cancels). -/
theorem Lsug0_comm_current (k : ℂ) (hk : k + D.h ≠ 0) (c : ι) (μ : ℤ) (x : Vacuum D k) :
    (Lsug D k 0 * J D k c μ - J D k c μ * Lsug D k 0) x = ((-μ : ℤ) : ℂ) • J D k c μ x := by
  rw [Lsug0_comm_eq_finsum]
  -- substitute L0sum_comm_apply, commute finite sums past ∑ᶠ, split into struct/central via inner0
  have hbody : ∀ p : ℤ, L0sum D k p (J D k c μ x) - J D k c μ (L0sum D k p x)
      = ∑ aa : ι, ∑ bb : ι, kappaInv D aa bb •
          (sug0TermJ D k aa bb p (J D k c μ x) - J D k c μ (sug0TermJ D k aa bb p x)) :=
    fun p => L0sum_comm_apply D k c μ p x
  rw [finsum_congr hbody]
  -- commute ∑aa∑bb past ∑ᶠp
  have hfinG : ∀ aa bb : ι, (Function.support (fun p : ℤ =>
      kappaInv D aa bb • (sug0TermJ D k aa bb p (J D k c μ x) - J D k c μ (sug0TermJ D k aa bb p x)))).Finite :=
    fun aa bb => (pair0_bracket_support_finite D k aa bb c μ x).subset (fun p hp => by
      rw [Function.mem_support] at hp ⊢; exact fun h => hp (by rw [h, smul_zero]))
  have hfinSbb : ∀ aa : ι, (Function.support (fun p : ℤ => ∑ bb : ι,
      kappaInv D aa bb • (sug0TermJ D k aa bb p (J D k c μ x) - J D k c μ (sug0TermJ D k aa bb p x)))).Finite := by
    intro aa
    apply Set.Finite.subset
      ((Finset.univ : Finset (ι)).finite_toSet.biUnion (fun bb _ => hfinG aa bb))
    intro p hp; rw [Function.mem_support] at hp
    simp only [Set.mem_iUnion]
    by_contra hcon; push_neg at hcon; apply hp
    refine Finset.sum_eq_zero fun bb _ => ?_
    have := hcon bb (Finset.mem_coe.mpr (Finset.mem_univ bb))
    rwa [Function.mem_support, not_not] at this
  rw [show (∑ᶠ p : ℤ, ∑ aa : ι, ∑ bb : ι,
        kappaInv D aa bb • (sug0TermJ D k aa bb p (J D k c μ x) - J D k c μ (sug0TermJ D k aa bb p x)))
      = ∑ aa : ι, ∑ bb : ι, kappaInv D aa bb •
          ∑ᶠ p : ℤ, (sug0TermJ D k aa bb p (J D k c μ x) - J D k c μ (sug0TermJ D k aa bb p x)) from by
    rw [← sum_finsum_comm Finset.univ
      (fun aa p => ∑ bb : ι,
        kappaInv D aa bb • (sug0TermJ D k aa bb p (J D k c μ x) - J D k c μ (sug0TermJ D k aa bb p x)))
      (fun aa _ => hfinSbb aa)]
    refine Finset.sum_congr rfl (fun aa _ => ?_)
    rw [← sum_finsum_comm Finset.univ
      (fun bb p => kappaInv D aa bb •
        (sug0TermJ D k aa bb p (J D k c μ x) - J D k c μ (sug0TermJ D k aa bb p x)))
      (fun bb _ => hfinG aa bb)]
    refine Finset.sum_congr rfl (fun bb _ => ?_)
    rw [← smul_finsum' (kappaInv D aa bb) (pair0_bracket_support_finite D k aa bb c μ x)]]
  -- substitute the per-pair split, collapse each half
  have hval : ∀ aa bb : ι,
      kappaInv D aa bb •
          ∑ᶠ p : ℤ, (sug0TermJ D k aa bb p (J D k c μ x) - J D k c μ (sug0TermJ D k aa bb p x))
      = -(kappaInv D aa bb • ∑ᶠ p : ℤ, struct0Part D k c aa bb μ p x)
        + -(kappaInv D aa bb • ∑ᶠ p : ℤ, central0Part D k c aa bb μ p x) :=
    fun aa bb => by rw [inner0_finsum_split, smul_neg, smul_add, neg_add]
  rw [Finset.sum_congr rfl (fun aa _ => Finset.sum_congr rfl (fun bb _ => hval aa bb))]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rw [struct0_residue_value, central0_residue_raw]
  -- c0 • (-(6μ • J) + -(2μk • J)) = -μ J
  rw [show (-(((2 * D.h : ℂ) * μ) • J D k c μ x) + -(((2:ℂ) * μ * k) • J D k c μ x))
      = (-(2 * (μ:ℂ) * (k + D.h))) • J D k c μ x from by module]
  rw [smul_smul]
  congr 1
  simp only [c0]
  have h2 : (2 : ℂ) * (k + D.h) ≠ 0 := mul_ne_zero two_ne_zero hk
  field_simp
  push_cast
  ring

/-! ## §1  `Lsug 0 = -ell0OpA` via agreement on the creation tower -/

/-- `Lsug 0` annihilates the vacuum (`mode (sugawaraField) 1 |0⟩ = (sugawaraField)(-2)|0⟩ = 0`, the
degree `-2 < 0` part of `T(z)|0⟩`). -/
theorem Lsug0_vacuum (k : ℂ) : Lsug D k 0 (vacuumA D k) = 0 := by
  rw [Lsug_def, mode_apply, show (-((0:ℤ) + 1) - 1 : ℤ) = -2 from by ring]
  exact sugawaraField_vacuum_neg D k (-2) (by norm_num)

/-- The m=0 covariance, operator-commutator form: `Lsug 0 (J^c_μ y) = J^c_μ (Lsug 0 y) - μ • J^c_μ y`. -/
theorem Lsug0_comm_current' (k : ℂ) (hk : k + D.h ≠ 0) (c : ι) (μ : ℤ) (y : Vacuum D k) :
    Lsug D k 0 (J D k c μ y) = J D k c μ (Lsug D k 0 y) + ((-μ : ℤ) : ℂ) • J D k c μ y := by
  have h := Lsug0_comm_current D k hk c μ y
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply] at h
  rw [eq_add_of_sub_eq h, add_comm]

/-- The vacuum module's level-`k` current `J k c μ` matches the abstract `vacuumRho`/`ofLoop`. -/
theorem J_eq_vacuumRho (k : ℂ) (c : ι) (μ : ℤ) (y : Vacuum D k) :
    J D k c μ y = vacuumRho κ D.invariant k
      (ofLoop κ D.invariant (D.generator c) μ) y := rfl

/-- **The Sugawara `L₀` agrees with `-ell0OpA` on every creation monomial `negWord L`**:
`Lsug 0 (negWord L) = (wordDeg L) • negWord L`.  By induction on `L`, using `Lsug0_vacuum` (base)
and the m=0 current covariance `Lsug0_comm_current'` (Leibniz step). -/
theorem Lsug0_negWord (k : ℂ) (hk : k + D.h ≠ 0) (L : List (𝔤 × ℕ)) :
    Lsug D k 0 (negWord κ D.invariant k L)
      = (wordDeg L : ℂ) • negWord κ D.invariant k L := by
  induction L with
  | nil =>
      rw [negWord]
      change Lsug D k 0 (vacuumA D k) = _
      rw [Lsug0_vacuum, wordDeg_nil, Nat.cast_zero, zero_smul]
  | cons xn L' ih =>
      obtain ⟨x, n⟩ := xn
      rw [negWord_cons]
      -- vacuumRho (ofLoop x (-n-1)) (negWord L') = ∑_c x_c • J^c_{-n-1} (negWord L')
      have hdecomp : vacuumRho κ D.invariant k
            (ofLoop κ D.invariant x (-(n : ℤ) - 1))
            (negWord κ D.invariant k L')
          = ∑ c : ι, coordinates D x c • (J D k c (-(n : ℤ) - 1)
              (negWord κ D.invariant k L')) := by
        rw [← loopMul_apply]
        conv_lhs => rw [basis_decomp D x]
        rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [map_smul, LinearMap.smul_apply]; rfl
      rw [hdecomp, map_sum]
      rw [show (wordDeg ((x, n) :: L') : ℂ) = ((n : ℂ) + 1) + (wordDeg L' : ℂ) from by
        simp only [wordDeg]; push_cast; ring]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [map_smul, Lsug0_comm_current' D k hk c (-(n : ℤ) - 1)
          (negWord κ D.invariant k L'), ih]
      -- J^c_{-n-1}((wordDeg L')•negWord L') + (-(-n-1))•J^c_{-n-1}(negWord L')
      rw [map_smul, show ((-(-(n : ℤ) - 1) : ℤ) : ℂ) = (n : ℂ) + 1 from by push_cast; ring]
      module

/-- `-ell0OpA` agrees with `Lsug 0` on each creation monomial (`vacuumRho_ell0_negWord_eq`). -/
theorem negEll0OpA_negWord (k : ℂ) (L : List (𝔤 × ℕ)) :
    (-ell0OpA D k) (negWord κ D.invariant k L)
      = (wordDeg L : ℂ) • negWord κ D.invariant k L := by
  have h := Module.End.mem_eigenspace_iff.mp
    (negWord_mem_eigenspace κ D.invariant k L)
  rw [LinearMap.neg_apply, ell0OpA, h]
  module

/-- **The Sugawara `L₀` is the (negated) energy operator**: `Lsug k 0 = -ell0OpA k` (both act as
`wordDeg L` on every creation monomial `negWord L`, and these span `Vacuum k`). -/
theorem Lsug0_eq_negEll0OpA (k : ℂ) (hk : k + D.h ≠ 0) : Lsug D k 0 = -ell0OpA D k := by
  apply LinearMap.ext_on (negSpan_eq_top κ D.invariant k)
  rintro _ ⟨L, rfl⟩
  rw [Lsug0_negWord D k hk L, negEll0OpA_negWord D k L]

/-! ## §2  The target VOA2 axiom `hYA_L0` -/

/-- **VOA2 (`hYA_L0`)**: `mode (YA ω) 1 v = n • v` for `v ∈ gradingZA k n` (Sugawara `L₀` acts as the
conformal weight `n`).  Via `YA ω = T`, `mode T 1 = Lsug 0 = -ell0OpA`, and `v ∈ gradingZA k n`
means `ell0OpA v = -n • v`. -/
theorem hYA_L0 (k : ℂ) (hk : k + D.h ≠ 0) {n : ℤ} (v : Vacuum D k) (hv : v ∈ gradingZA D k n) :
    mode (YA D k hk (omegaA D k)) 1 v = (n : ℂ) • v := by
  rw [YA_omega_eq, show mode (sugawaraField D k) 1 = Lsug D k 0 from by rw [Lsug_def]; rfl,
    Lsug0_eq_negEll0OpA D k hk, LinearMap.neg_apply]
  rw [gradingZA_def, Module.End.mem_eigenspace_iff] at hv
  rw [hv]
  module

end VOA.AffineGeneral.SugawaraCov
