import VOA.Huang.LiRegularJacobi
import VOA.Modules.ContragredientClose
import VOA.Modules.ZhuRingResidue

/-! # The opposite mode system of an ordinary module, and its regular representation

For an ordinary module `N : OrdVModule W M`, FHL's opposite vertex operator
`Y°(u,x) = Y(e^{xL(1)}(−x⁻²)^{L(0)}u, x⁻¹)` has modes

  `u°ₖ = (−1)^{wt u} Σⱼ (1/j!) (L(1)ʲu)₍₂ wt u − k − 2 − j₎`     (homogeneous `u`),

which are exactly the library's `dualAdj` operators (projection-free by `dualAdj_clean`).
The module FHL identity `dualAdjResidualMvec_holds` (proved in the library) is the
opposite Jacobi identity.  This file assembles these modes into an `OppBase`
(`oppBase N`) and hence, by `LiRegularJacobi`, obtains for every `z ≠ 0` the weak
module `(D_{P(z)}(M), Y^R)` of Li's regular representation
(`regularRepR N hz : WeakModule W (D_{P(z)}(M))`).

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.VertexOperatorAlgebra
open scoped BigOperators

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

section Opp

variable (N : OrdVModule W M)

/-- The opposite modes of a homogeneous state, as a linear family on `W.grading wt`. -/
noncomputable def oppFam (wt : ℤ) : W.grading wt →ₗ[ℂ] ℤ → Module.End ℂ M where
  toFun u := fun k => (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1),
    ((j.factorial : ℂ)⁻¹) • mode (N.YM ((W.L 1 ^ j) (u : V))) (2 * wt - k - 2 - (j : ℤ))
  map_add' u v := by
    funext k
    simp only [Submodule.coe_add, map_add, mode_add, smul_add, Finset.sum_add_distrib,
      Pi.add_apply]
  map_smul' c u := by
    funext k
    simp only [Submodule.coe_smul, map_smul, mode_smul, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.sum_congr rfl fun j _ => smul_comm ((j.factorial : ℂ)⁻¹) c _, ← Finset.smul_sum,
      smul_comm]

/-- **The opposite modes** `u°ₖ`, linear in the state. -/
noncomputable def oppB : V →ₗ[ℂ] ℤ → Module.End ℂ M :=
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  (DFinsupp.lsum ℂ (oppFam N)).comp (DirectSum.decomposeLinearEquiv W.grading).toLinearMap

theorem oppB_homog {wt : ℤ} {u : V} (hu : u ∈ W.grading wt) (k : ℤ) :
    oppB N u k = (-1 : ℂ) ^ wt • ∑ j ∈ Finset.range (wt.toNat + 1),
      ((j.factorial : ℂ)⁻¹) • mode (N.YM ((W.L 1 ^ j) u)) (2 * wt - k - 2 - (j : ℤ)) := by
  letI := DirectSum.IsInternal.chooseDecomposition W.grading W.isInternal
  have hcollapse : oppB N u = oppFam N wt ⟨u, hu⟩ := by
    change (DFinsupp.lsum ℂ (oppFam N)) (DirectSum.decompose W.grading u) = _
    rw [DirectSum.decompose_of_mem W.grading hu]
    exact DFinsupp.lsum_single ℂ (oppFam N) wt ⟨u, hu⟩
  rw [hcollapse]; rfl

/-- On homogeneous vectors the opposite modes are the library's `dualAdj`. -/
theorem oppB_eq_dualAdj {wt : ℤ} {u : V} (hu : u ∈ W.grading wt) (k : ℤ) {α : ℂ} {x : M}
    (hx : x ∈ N.weight α) : oppB N u k x = dualAdj N wt u k α x := by
  rw [dualAdj_clean N hu k hx, oppB_homog N hu]
  simp only [LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]

theorem mem_iSup_weight_ord (x : M) : x ∈ ⨆ α, N.weight α := by
  rw [N.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top

/-- Upper truncation of the opposite modes. -/
theorem oppB_trunc (u : V) (x : M) : ∃ K : ℤ, ∀ n : ℤ, n ≤ K → oppB N u n x = 0 := by
  refine Submodule.iSup_induction N.weight (motive := fun x => ∃ K : ℤ, ∀ n : ℤ, n ≤ K →
    oppB N u n x = 0) (mem_iSup_weight_ord N x) ?_ ⟨0, fun _ _ => map_zero _⟩ ?_
  · intro α x hx
    refine reduce_homogeneous W (P := fun u => ∃ K : ℤ, ∀ n : ℤ, n ≤ K → oppB N u n x = 0)
      ?_ ⟨0, fun n _ => by simp⟩ ?_ u
    · intro wt u hu
      obtain ⟨K, hK⟩ := dualAdj_eventually_zero_below N hu hx
      exact ⟨K, fun n hn => by rw [oppB_eq_dualAdj N hu n hx]; exact hK n hn⟩
    · rintro u v ⟨K, hK⟩ ⟨K', hK'⟩
      exact ⟨min K K', fun n hn => by
        rw [map_add, Pi.add_apply, LinearMap.add_apply, hK n (by omega), hK' n (by omega),
          add_zero]⟩
  · rintro x y ⟨K, hK⟩ ⟨K', hK'⟩
    exact ⟨min K K', fun n hn => by rw [map_add, hK n (by omega), hK' n (by omega), add_zero]⟩

theorem oppB_vacuum (n : ℤ) (x : M) : oppB N W.vacuum n x = if n = -1 then x else 0 := by
  rw [oppB_homog N W.vacuum_mem_grading_zero]
  simp only [zpow_zero, one_smul, Int.toNat_zero, zero_add, Finset.range_one,
    Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero,
    Module.End.one_apply, CharP.cast_eq_zero, sub_zero, mul_zero]
  rw [N.vacuum_YM, mode_one]
  by_cases h : n = -1
  · subst h; simp
  · rw [if_neg (by omega), if_neg h]; rfl

/-- The left side of the opposite Jacobi identity, as a function of the summation index. -/
noncomputable def oppJacL (a b : V) (x : M) (l m n : ℤ) (i : ℤ) : M :=
  (negOnePow i * cbz l i) •
    (oppB N b (n + i) (oppB N a (l + m - i) x)
      - negOnePow l • oppB N a (m + i) (oppB N b (l + n - i) x))

noncomputable def oppJacR (a b : V) (x : M) (l m n : ℤ) (i : ℤ) : M :=
  cbz m i • oppB N (W.smul a (l + i) b) (m + n - i) x

theorem oppJacL_fin (a b : V) (x : M) (l m n : ℤ) :
    (Function.support (oppJacL N a b x l m n)).Finite := by
  obtain ⟨Ka, hKa⟩ := oppB_trunc N a x
  obtain ⟨Kb, hKb⟩ := oppB_trunc N b x
  apply (Set.finite_Icc 0 (max (l + m - Ka) (l + n - Kb))).subset
  intro i hi
  rw [Function.mem_support] at hi
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · simp [oppJacL, cbz_apply_neg l h]
  · rw [oppJacL, hKa _ (by omega), hKb _ (by omega), map_zero, map_zero, smul_zero, sub_zero,
      smul_zero]

theorem oppJacR_fin (a b : V) (x : M) (l m n : ℤ) :
    (Function.support (oppJacR N a b x l m n)).Finite := by
  obtain ⟨R, hR⟩ := W.regularity a b
  apply (Set.finite_Icc 0 (R - l)).subset
  intro i hi
  rw [Function.mem_support] at hi
  refine ⟨not_lt.mp fun h => hi ?_, not_lt.mp fun h => hi ?_⟩
  · simp [oppJacR, cbz_apply_neg m h]
  · rw [oppJacR, show W.smul a (l + i) b = 0 from hR _ (by omega)]
    simp

/-- The opposite Jacobi identity for homogeneous states and vectors (the library's module FHL
identity, transported to `oppB`). -/
theorem oppB_jacobi_homog {wtu wtv : ℤ} {a b : V} (ha : a ∈ W.grading wtu)
    (hb : b ∈ W.grading wtv) {α : ℂ} {x : M} (hx : x ∈ N.weight α) (l m n : ℤ) :
    (∑ᶠ i, oppJacL N a b x l m n i) = ∑ᶠ i, oppJacR N a b x l m n i := by
  have h := dualAdjResidualMvec_holds N wtu a ha wtv b hb l m n α x hx
  unfold DualAdjResidualMvecAt at h
  convert h using 2
  · funext i
    rw [oppJacL, oppB_eq_dualAdj N ha _ hx, oppB_eq_dualAdj N hb _ hx,
      oppB_eq_dualAdj N hb _ (dualAdj_mem N wtu a _ α x),
      oppB_eq_dualAdj N ha _ (dualAdj_mem N wtv b _ α x)]
  · funext i
    rw [oppJacR, oppB_eq_dualAdj N (W.smul_mem_grading ha hb (l + i)) _ hx]

theorem oppB_jacobi (a b : V) (x : M) (l m n : ℤ) :
    (∑ᶠ i, oppJacL N a b x l m n i) = ∑ᶠ i, oppJacR N a b x l m n i := by
  -- additivity in each argument, from finite supports
  have addx : ∀ (a b : V) (x y : M) (i : ℤ),
      oppJacL N a b (x + y) l m n i = oppJacL N a b x l m n i + oppJacL N a b y l m n i ∧
      oppJacR N a b (x + y) l m n i = oppJacR N a b x l m n i + oppJacR N a b y l m n i := by
    intro a b x y i
    constructor
    · simp only [oppJacL, map_add, smul_add, smul_sub]; abel
    · simp only [oppJacR, map_add, smul_add]
  have adda : ∀ (a a' b : V) (x : M) (i : ℤ),
      oppJacL N (a + a') b x l m n i = oppJacL N a b x l m n i + oppJacL N a' b x l m n i ∧
      oppJacR N (a + a') b x l m n i = oppJacR N a b x l m n i + oppJacR N a' b x l m n i := by
    intro a a' b x i
    constructor
    · simp only [oppJacL, map_add, Pi.add_apply, LinearMap.add_apply, smul_add, smul_sub]; abel
    · simp only [oppJacR, PreVertexAlgebra.smul_add_left, map_add, Pi.add_apply,
        LinearMap.add_apply, smul_add]
  have addb : ∀ (a b b' : V) (x : M) (i : ℤ),
      oppJacL N a (b + b') x l m n i = oppJacL N a b x l m n i + oppJacL N a b' x l m n i ∧
      oppJacR N a (b + b') x l m n i = oppJacR N a b x l m n i + oppJacR N a b' x l m n i := by
    intro a b b' x i
    constructor
    · simp only [oppJacL, map_add, Pi.add_apply, LinearMap.add_apply, smul_add, smul_sub]; abel
    · rw [oppJacR, oppJacR, oppJacR, show W.smul a (l + i) (b + b')
          = W.smul a (l + i) b + W.smul a (l + i) b' from map_add _ _ _]
      simp only [map_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  -- the predicate
  let P : V → V → M → Prop := fun a b x =>
    (∑ᶠ i, oppJacL N a b x l m n i) = ∑ᶠ i, oppJacR N a b x l m n i
  have hx0 : ∀ a b, P a b 0 := fun a b => by
    simp [P, oppJacL, oppJacR]
  have hxadd : ∀ a b x y, P a b x → P a b y → P a b (x + y) := by
    intro a b x y hx hy
    simp only [P] at *
    rw [finsum_congr fun i => (addx a b x y i).1, finsum_congr fun i => (addx a b x y i).2,
      finsum_add_distrib (oppJacL_fin N a b x l m n) (oppJacL_fin N a b y l m n),
      finsum_add_distrib (oppJacR_fin N a b x l m n) (oppJacR_fin N a b y l m n), hx, hy]
  have ha0 : ∀ b x, P 0 b x := fun b x => by simp [P, oppJacL, oppJacR]
  have haadd : ∀ a a' b x, P a b x → P a' b x → P (a + a') b x := by
    intro a a' b x h h'
    simp only [P] at *
    rw [finsum_congr fun i => (adda a a' b x i).1, finsum_congr fun i => (adda a a' b x i).2,
      finsum_add_distrib (oppJacL_fin N a b x l m n) (oppJacL_fin N a' b x l m n),
      finsum_add_distrib (oppJacR_fin N a b x l m n) (oppJacR_fin N a' b x l m n), h, h']
  have hb0 : ∀ a x, P a 0 x := fun a x => by
    simp only [P, oppJacL, oppJacR, map_zero, Pi.zero_apply, LinearMap.zero_apply]
    simp
  have hbadd : ∀ a b b' x, P a b x → P a b' x → P a (b + b') x := by
    intro a b b' x h h'
    simp only [P] at *
    rw [finsum_congr fun i => (addb a b b' x i).1, finsum_congr fun i => (addb a b b' x i).2,
      finsum_add_distrib (oppJacL_fin N a b x l m n) (oppJacL_fin N a b' x l m n),
      finsum_add_distrib (oppJacR_fin N a b x l m n) (oppJacR_fin N a b' x l m n), h, h']
  change P a b x
  refine reduce_homogeneous W (P := fun a => P a b x) ?_ (ha0 b x)
    (fun a a' h h' => haadd a a' b x h h') a
  intro wtu a ha
  refine reduce_homogeneous W (P := fun b => P a b x) ?_ (hb0 a x)
    (fun b b' h h' => hbadd a b b' x h h') b
  intro wtv b hb
  refine Submodule.iSup_induction N.weight (motive := fun x => P a b x)
    (mem_iSup_weight_ord N x) ?_ (hx0 a b) (fun x y hx hy => hxadd a b x y hx hy)
  intro α x hx
  exact oppB_jacobi_homog N ha hb hx l m n

/-- **The opposite mode system of an ordinary module.** -/
noncomputable def oppBase : OppBase W M where
  B := oppB N
  trunc := oppB_trunc N
  vacuum := oppB_vacuum N
  jacobi := fun a b x l m n => oppB_jacobi N a b x l m n

/-- **Li's regular representation `(D_{P(z)}(M), Y^R)`** of an ordinary module, a weak
`V`-module for every `z ≠ 0` (Li, *Regular representations I*, Theorem 3.17). -/
noncomputable def regularRepR {z : ℂ} (hz : z ≠ 0) : WeakModule W ((oppBase N).Dsub z) :=
  (oppBase N).weakModuleR z hz

end Opp

end VOA.Huang.LiRegular
