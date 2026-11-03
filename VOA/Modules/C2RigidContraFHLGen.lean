import VOA.Modules.C2RigidContraFHLBase
import VOA.Modules.C2RigidContraFHLComul

/-!
# Port of `Modules/ContragredientFHLGen.lean` from `OrdVModule` to `GWModule`

Input to the McRae rigidity argument.  Statements and proofs are those of the original file, with the
structure `OrdVModule` replaced by `C2Rigid.GWModule` (graded weak modules, `L₀` possibly
non-semisimple) and the namespace `VOA` replaced by `VOA.C2Rigid`.  See
`Modules/C2RigidGraded.lean` for why this is the only change needed.
-/


namespace VOA.C2Rigid
open VertexOperatorAlgebra
open Module (End Dual)
open scoped BigOperators
open Classical

universe u
variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]
variable {W : VertexOperatorAlgebra 𝒱} {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- **General nested `dualAdj` expansion** (no qp): the nested dualAdj of `u, v` is the explicit
double `Y_M` tower over `(j₁, j₂)`. -/
theorem nested_dualAdj_gen (N : GWModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q)
    (k₁ k₂ : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    dualAdj N q v k₂ (matchIdx p k₁ α) (dualAdj N p u k₁ α xα)
      = (-1 : ℂ) ^ (p + q) •
          ∑ j₂ ∈ Finset.range (q.toNat + 1), ∑ j₁ ∈ Finset.range (p.toNat + 1),
            (((j₁.factorial : ℂ)⁻¹) * ((j₂.factorial : ℂ)⁻¹)) •
              mode (N.YM ((W.L 1 ^ j₂) v)) (2 * q - k₂ - 2 - (j₂ : ℤ))
                (mode (N.YM ((W.L 1 ^ j₁) u)) (2 * p - k₁ - 2 - (j₁ : ℤ)) xα) := by
  rw [dualAdj_clean N hv k₂ (dualAdj_mem N p u k₁ α xα)]
  rw [dualAdj_clean N hu k₁ hxα]
  have hinner : ∀ j₂ : ℕ,
      (mode (N.YM ((W.L 1 ^ j₂) v)) (2 * q - k₂ - 2 - (j₂ : ℤ)))
          ((-1 : ℂ) ^ p • ∑ j₁ ∈ Finset.range (p.toNat + 1),
            ((j₁.factorial : ℂ)⁻¹) • mode (N.YM ((W.L 1 ^ j₁) u)) (2 * p - k₁ - 2 - (j₁ : ℤ)) xα)
        = (-1 : ℂ) ^ p • ∑ j₁ ∈ Finset.range (p.toNat + 1),
            ((j₁.factorial : ℂ)⁻¹) •
              mode (N.YM ((W.L 1 ^ j₂) v)) (2 * q - k₂ - 2 - (j₂ : ℤ))
                (mode (N.YM ((W.L 1 ^ j₁) u)) (2 * p - k₁ - 2 - (j₁ : ℤ)) xα) := by
    intro j₂
    rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl (fun j₁ _ => ?_)
    rw [map_smul]
  simp only [hinner]
  simp only [Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun j₂ _ => ?_)
  refine Finset.sum_congr rfl (fun j₁ _ => ?_)
  congr 1
  rw [show (-1 : ℂ) ^ (p + q) = (-1 : ℂ) ^ q * (-1 : ℂ) ^ p from by
    rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), add_comm q p]]
  ring

/-- **Per-(a,b) N.jacobi bridge for the LHS bracket.** -/
theorem lhs_pair_jacobi (N : GWModule W M) (u v : 𝒱)
    (ℓ m n : ℤ) (p q : ℤ) (xα : M) (a b : ℕ) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (n + i) - 2 - (b : ℤ))
            (mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) xα)
          - negOnePow ℓ • mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (m + i) - 2 - (a : ℤ))
              (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) xα)))
      = ∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
          mode (N.YM (W.smul ((W.L 1 ^ b) v) (ℓ + i) ((W.L 1 ^ a) u)))
            ((2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i) xα := by
  have hjac := N.jacobi ((W.L 1 ^ b) v) ((W.L 1 ^ a) u) xα ℓ
    (2 * q - ℓ - n - 2 - (b : ℤ)) (2 * p - ℓ - m - 2 - (a : ℤ))
  rw [← hjac]
  refine finsum_congr (fun i => ?_)
  rw [show 2 * q - (n + i) - 2 - (b : ℤ) = ℓ + (2 * q - ℓ - n - 2 - (b : ℤ)) - i from by ring,
      show 2 * p - (ℓ + m - i) - 2 - (a : ℤ) = (2 * p - ℓ - m - 2 - (a : ℤ)) + i from by ring,
      show 2 * p - (m + i) - 2 - (a : ℤ) = ℓ + (2 * p - ℓ - m - 2 - (a : ℤ)) - i from by ring,
      show 2 * q - (ℓ + n - i) - 2 - (b : ℤ) = (2 * q - ℓ - n - 2 - (b : ℤ)) + i from by ring]

/-- Bracket combine for fixed `i`. -/
theorem lhs_summand_combine (N : GWModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q)
    (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) (i : ℤ) :
    (negOnePow i * cbz ℓ i) •
        (dualAdj N q v (n + i) (matchIdx p (ℓ + m - i) α) (dualAdj N p u (ℓ + m - i) α xα)
          - negOnePow ℓ • dualAdj N p u (m + i) (matchIdx q (ℓ + n - i) α)
              (dualAdj N q v (ℓ + n - i) α xα))
      = (-1 : ℂ) ^ (p + q) • ∑ b ∈ Finset.range (q.toNat + 1), ∑ a ∈ Finset.range (p.toNat + 1),
          (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) •
            ((negOnePow i * cbz ℓ i) •
              (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (n + i) - 2 - (b : ℤ))
                  (mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) xα)
                - negOnePow ℓ • mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (m + i) - 2 - (a : ℤ))
                    (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) xα))) := by
  set T1 : ℕ → ℕ → M := fun b a =>
    mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (n + i) - 2 - (b : ℤ))
      (mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) xα) with hT1
  set T2 : ℕ → ℕ → M := fun b a =>
    mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (m + i) - 2 - (a : ℤ))
      (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) xα) with hT2
  have hN1 : dualAdj N q v (n + i) (matchIdx p (ℓ + m - i) α) (dualAdj N p u (ℓ + m - i) α xα)
      = (-1 : ℂ) ^ (p + q) • ∑ b ∈ Finset.range (q.toNat + 1), ∑ a ∈ Finset.range (p.toNat + 1),
          (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) • T1 b a :=
    nested_dualAdj_gen N hu hv (ℓ + m - i) (n + i) hxα
  have hN2 : dualAdj N p u (m + i) (matchIdx q (ℓ + n - i) α) (dualAdj N q v (ℓ + n - i) α xα)
      = (-1 : ℂ) ^ (p + q) • ∑ b ∈ Finset.range (q.toNat + 1), ∑ a ∈ Finset.range (p.toNat + 1),
          (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) • T2 b a := by
    rw [nested_dualAdj_gen N hv hu (ℓ + n - i) (m + i) hxα]
    rw [show (-1 : ℂ) ^ (q + p) = (-1 : ℂ) ^ (p + q) from by rw [add_comm]]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hT2]; congr 1; ring
  rw [hN1, hN2]
  rw [smul_comm (negOnePow ℓ) ((-1:ℂ)^(p+q))]
  rw [← smul_sub, smul_comm (negOnePow i * cbz ℓ i) ((-1:ℂ)^(p+q))]
  congr 1
  rw [smul_sub]
  simp only [Finset.smul_sum, smul_smul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [smul_sub, smul_smul]
  congr 1
  · congr 1; ring
  · show (negOnePow i * cbz ℓ i * (negOnePow ℓ * ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹))) • T2 b a
      = ((a.factorial : ℂ)⁻¹ * (b.factorial : ℂ)⁻¹ * (negOnePow i * cbz ℓ i) * negOnePow ℓ) • T2 b a
    congr 1; ring

/-- **Finiteness of the per-(a,b) LHS bracket summand** (over `i`). -/
theorem lhs_pair_summand_fin (N : GWModule W M) (u v : 𝒱)
    (ℓ m n : ℤ) (p q : ℤ) (xα : M) (a b : ℕ) :
    Function.HasFiniteSupport (fun i : ℤ => (negOnePow i * cbz ℓ i) •
        (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (n + i) - 2 - (b : ℤ))
            (mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) xα)
          - negOnePow ℓ • mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (m + i) - 2 - (a : ℤ))
              (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) xα))) := by
  obtain ⟨Ku, hKu⟩ := N.truncation ((W.L 1 ^ a) u) xα
  obtain ⟨Kv, hKv⟩ := N.truncation ((W.L 1 ^ b) v) xα
  show (Function.support _).Finite
  apply Set.Finite.subset (Set.finite_Icc 0
    (max (Ku - (2*p - (ℓ+m) - 2 - (a:ℤ))) (Kv - (2*q - (ℓ+n) - 2 - (b:ℤ)))))
  intro i hi
  rw [Function.mem_support] at hi
  rw [Set.mem_Icc]
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · rw [cbz_apply_neg ℓ h, mul_zero, zero_smul]
  · have h1 : mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) xα = 0 :=
      hKu _ (by omega)
    have hvinner : mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) xα = 0 :=
      hKv _ (by omega)
    rw [h1, map_zero, hvinner, map_zero, smul_zero, sub_zero, smul_zero]

/-- A finite Finset-sum of finite-support functions has finite support. -/
theorem hasFiniteSupport_finsetSum {ι κ : Type*} {G : Type*} [AddCommMonoid G]
    (s : Finset κ) (F : κ → ι → G) (hF : ∀ k ∈ s, Function.HasFiniteSupport (F k)) :
    Function.HasFiniteSupport (fun i => ∑ k ∈ s, F k i) := by
  classical
  show (Function.support (fun i => ∑ k ∈ s, F k i)).Finite
  apply Set.Finite.subset (s.finite_toSet.biUnion (fun k _ => (hF k (by assumption))))
  intro i hi
  rw [Function.mem_support] at hi
  simp only [Set.mem_iUnion]
  by_contra hcon
  simp only [not_exists] at hcon
  apply hi
  refine Finset.sum_eq_zero (fun k hk => ?_)
  by_contra hne
  exact hcon k (Finset.mem_coe.mpr hk) (Function.mem_support.mpr hne)

/-- **General LHS reduction** of `DualAdjResidualMvecAt` (NO quasi-primary assumption). -/
theorem lhs_gen_eq (N : GWModule W M) {p : ℤ} {u : 𝒱} (hu : u ∈ W.grading p)
    {q : ℤ} {v : 𝒱} (hv : v ∈ W.grading q)
    (ℓ m n : ℤ) {α : ℂ} {xα : M} (hxα : xα ∈ N.weight α) :
    (∑ᶠ i : ℤ, (negOnePow i * cbz ℓ i) •
        (dualAdj N q v (n + i) (matchIdx p (ℓ + m - i) α) (dualAdj N p u (ℓ + m - i) α xα)
          - negOnePow ℓ • dualAdj N p u (m + i) (matchIdx q (ℓ + n - i) α)
              (dualAdj N q v (ℓ + n - i) α xα)))
      = (-1 : ℂ) ^ (p + q) •
          ∑ b ∈ Finset.range (q.toNat + 1), ∑ a ∈ Finset.range (p.toNat + 1),
            (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) •
              ∑ᶠ i : ℤ, cbz (2 * q - ℓ - n - 2 - (b : ℤ)) i •
                mode (N.YM (W.smul ((W.L 1 ^ b) v) (ℓ + i) ((W.L 1 ^ a) u)))
                  ((2 * q - ℓ - n - 2 - (b : ℤ)) + (2 * p - ℓ - m - 2 - (a : ℤ)) - i) xα := by
  have smulFin : ∀ a b : ℕ, Function.HasFiniteSupport
      (fun i : ℤ => (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) •
        ((negOnePow i * cbz ℓ i) •
          (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (n + i) - 2 - (b : ℤ))
              (mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) xα)
            - negOnePow ℓ • mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (m + i) - 2 - (a : ℤ))
                (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) xα)))) := by
    intro a b
    show (Function.support _).Finite
    apply Set.Finite.subset (lhs_pair_summand_fin N u v ℓ m n p q xα a b)
    intro i hi
    rw [Function.mem_support] at hi ⊢
    intro hzero
    apply hi
    rw [hzero, smul_zero]
  rw [finsum_congr (fun i => lhs_summand_combine N hu hv ℓ m n hxα i)]
  rw [← smul_finsum' ((-1 : ℂ) ^ (p + q)) (f := fun i => ∑ b ∈ Finset.range (q.toNat + 1),
        ∑ a ∈ Finset.range (p.toNat + 1), (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) •
          ((negOnePow i * cbz ℓ i) •
            (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (n + i) - 2 - (b : ℤ))
                (mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) xα)
              - negOnePow ℓ • mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (m + i) - 2 - (a : ℤ))
                  (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) xα)))) ?_]
  · congr 1
    rw [finsum_sum_comm (Finset.range (q.toNat + 1))
          (fun i b => ∑ a ∈ Finset.range (p.toNat + 1),
            (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) •
              ((negOnePow i * cbz ℓ i) •
                (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (n + i) - 2 - (b : ℤ))
                    (mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) xα)
                  - negOnePow ℓ • mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (m + i) - 2 - (a : ℤ))
                      (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) xα)))) ?_]
    · refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [finsum_sum_comm (Finset.range (p.toNat + 1))
            (fun i a => (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) •
              ((negOnePow i * cbz ℓ i) •
                (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (n + i) - 2 - (b : ℤ))
                    (mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) xα)
                  - negOnePow ℓ • mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (m + i) - 2 - (a : ℤ))
                      (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) xα)))) ?_]
      · refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← smul_finsum' (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹))
              (lhs_pair_summand_fin N u v ℓ m n p q xα a b)]
        congr 1
        exact lhs_pair_jacobi N u v ℓ m n p q xα a b
      · intro a _
        exact smulFin a b
    · intro b _
      exact hasFiniteSupport_finsetSum (Finset.range (p.toNat + 1))
        (fun a i => (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) •
          ((negOnePow i * cbz ℓ i) •
            (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (n + i) - 2 - (b : ℤ))
                (mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) xα)
              - negOnePow ℓ • mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (m + i) - 2 - (a : ℤ))
                  (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) xα))))
        (fun a _ => smulFin a b)
  · exact hasFiniteSupport_finsetSum (Finset.range (q.toNat + 1))
      (fun b i => ∑ a ∈ Finset.range (p.toNat + 1),
        (((a.factorial : ℂ)⁻¹) * ((b.factorial : ℂ)⁻¹)) •
          ((negOnePow i * cbz ℓ i) •
            (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (n + i) - 2 - (b : ℤ))
                (mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (ℓ + m - i) - 2 - (a : ℤ)) xα)
              - negOnePow ℓ • mode (N.YM ((W.L 1 ^ a) u)) (2 * p - (m + i) - 2 - (a : ℤ))
                  (mode (N.YM ((W.L 1 ^ b) v)) (2 * q - (ℓ + n - i) - 2 - (b : ℤ)) xα))))
      (fun b _ => hasFiniteSupport_finsetSum (Finset.range (p.toNat + 1)) _
        (fun a _ => smulFin a b))
end VOA.C2Rigid