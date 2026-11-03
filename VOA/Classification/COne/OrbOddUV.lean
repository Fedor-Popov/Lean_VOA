import VOA.Classification.COne.OrbOddChain
import VOA.Classification.COne.OrbOddPrim

/-!
# OrbOdd (6): `[u] * [v] = c · q([ω]) [u]` in `A(V₂^{A₄})`

`u = tetraU` (weight 9), `v = tetraV` (weight 16), both Virasoro primaries, `τ`-odd/even.

* `s7_zero`: the level-seven singular vector of `M(1,9)` vanishes on `u` (it is a primary in the
  lower descendants; unitarity).
* `tetra_uv_chain`: `∃ c, u₍₁₅₎v = c u ∧ ∀ N ≤ 16, u₍₁₅₋N₎v = c · x_{15-N}` with the explicit
  Virasoro words `x_k` of `OrbOddData*` (from `chain_main`, the odd sector being the
  `(-1)`-eigenspace of `τ`, whose primaries of weight `≤ 25` are classified by `odd_prim`).
* `tetra_uv_zhu`: `[u] * [v] = c · q([ω]) [u]` with the explicit degree-8 polynomial
  `q = qList` (rational coefficients), for the same `c`.

No lattice computation enters: everything beyond the structural facts is the Virasoro algebra at
`c = 1` (kernel-checked normal ordering up to level 16).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096

noncomputable section

namespace VOA.Classification.COne.OrbOdd

open VOA VertexOperatorAlgebra OrbSpan OrbPrim OrbC2b OrbC2c OrbRat2 OrbZhu
  VOA.LatGen VOA.LatGen.Triplet Polynomial

/-- `tetra ≅ A₄` is finite (the same instance as in `OrbZhuGraded`). -/
noncomputable local instance tetraFintypeUV : Fintype tetra :=
  @Fintype.ofFinite _ (Finite.of_equiv (alternatingGroup (Fin 4)) tetra_group.some.symm.toEquiv)

theorem wt_cc : Wt.centralCharge = ((1 : ℚ) : ℂ) := by
  rw [exceptionalOrbifold_centralCharge]; norm_num

theorem tetraU_prim : ∀ m : ℕ, 1 ≤ m → Wt.L (m : ℤ) tetraU = 0 := by
  intro m hm
  have h := ((mem_prim _).mp (tT_prim isA4Inv_I3 I3_hom)).2 (m - 1)
  rwa [show ((m - 1 : ℕ) : ℤ) + 1 = m by omega] at h

theorem tetraV_prim : ∀ m : ℕ, 1 ≤ m → Wt.L (m : ℤ) tetraV = 0 := by
  intro m hm
  have h := ((mem_prim _).mp (tT_prim isA4Inv_I4 I4_hom)).2 (m - 1)
  rwa [show ((m - 1 : ℕ) : ℤ) + 1 = m by omega] at h

theorem tetraU_L0 : Wt.L 0 tetraU = ((9 : ℚ) : ℂ) • tetraU := by
  rw [Wt.L_zero_grading tetraU tetraU_mem]; norm_num

theorem s7v_spec : ∀ p ∈ s7v, p.2.sum = 7 ∧ p.2 ≠ [] ∧ posW p.2 = true := by
  decide +kernel

/-- The singular vector `s₇ u` vanishes in `W`. -/
theorem s7_zero : evV Wt tetraU s7v = 0 := by
  have h1 := s7chk_sound wt_cc tetraU_prim tetraU_L0 s7chk_one
  have h2 := s7chk_sound wt_cc tetraU_prim tetraU_L0 s7chk_two
  have hp : evV Wt tetraU s7v ∈ prim Wt (9 + (7 : ℕ)) := by
    rw [mem_prim]
    refine ⟨evV_mem_grading tetraU_mem (fun p hp => (s7v_spec p hp).1), fun m => ?_⟩
    have := L_pos_of_L1_L2 (by simpa using h1) (by simpa using h2) (m + 1) (by omega)
    simpa using this
  have hl := evV_mem_lowerDesc tetraU_mem (N := 7) (v := s7v) s7v_spec
  exact prim_lowerDesc_eq_zero hp hl

/-- The odd sector: the `(-1)`-eigenspace of `τ`. -/
def oddS : Submodule ℂ (orbifold tetra).carrier :=
  LinearMap.ker (tetraInvolution.toLinearEquiv.toLinearMap + LinearMap.id)

theorem mem_oddS {y : (orbifold tetra).carrier} : y ∈ oddS ↔ tetraInvolution y = -y := by
  rw [oddS, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]
  rfl

theorem tau_L (n : ℤ) (y : (orbifold tetra).carrier) :
    tetraInvolution (Wt.L n y) = Wt.L n (tetraInvolution y) := by
  rw [VertexOperatorAlgebra.L_def, ← PreVertexAlgebra.smul_def, ← PreVertexAlgebra.smul_def]
  have := tetraInvolution.map_smul' Wt.conformalVector (n + 1) y
  rw [tetraInvolution.map_omega] at this
  exact this

theorem oddS_L (n : ℤ) (y : (orbifold tetra).carrier) (hy : y ∈ oddS) : Wt.L n y ∈ oddS := by
  rw [mem_oddS] at hy ⊢
  rw [tau_L, show tetraInvolution y = -y from hy, map_neg]

theorem oddS_uv (k : ℤ) : Wt.smul tetraU k tetraV ∈ oddS := by
  rw [mem_oddS]
  have := tetraInvolution.map_smul' tetraU k tetraV
  change tetraInvolution (Wt.smul tetraU k tetraV) = _
  rw [this, show tetraInvolution.toLinearEquiv tetraU = -tetraU from tetraInvolution_U,
    show tetraInvolution.toLinearEquiv tetraV = tetraV from tetraInvolution_V,
    ← neg_one_smul ℂ tetraU, PreVertexAlgebra.smul_smul_left, neg_one_smul]

theorem oddS_prim (N : ℤ) (hN : N ≤ 25) (y : (orbifold tetra).carrier) (hy : y ∈ oddS)
    (hp : y ∈ prim Wt N) : (N = 9 → ∃ c : ℂ, y = c • tetraU) ∧ (N ≠ 9 → y = 0) := by
  have h := odd_prim hN hp (mem_oddS.mp hy)
  refine ⟨fun h9 => ?_, fun h9 => ?_⟩
  · rw [oddTarget, if_pos h9, Submodule.mem_span_singleton] at h
    obtain ⟨a, ha⟩ := h
    exact ⟨a, ha.symm⟩
  · rw [oddTarget, if_neg h9] at h
    exact (Submodule.mem_bot ℂ).mp h

/-- The products `u₍ₖ₎ v`, `-1 ≤ k ≤ 15`, as explicit Virasoro words on `u`. -/
theorem tetra_uv_chain : ∃ c : ℂ, Wt.smul tetraU 15 tetraV = c • tetraU ∧
    ∀ N : ℕ, N ≤ 16 → Wt.smul tetraU (15 - (N : ℤ)) tetraV = c • evV Wt tetraU (xsN N) :=
  chain_main wt_cc tetraU_mem tetraU_prim tetraV_mem tetraV_prim s7_zero oddS
    (mem_oddS.mpr tetraInvolution_U) oddS_L oddS_uv oddS_prim

/-! ## The Zhu product -/

/-- The binomial coefficients `C(9, m)`. -/
def b9 : ℕ → ℚ
  | 0 => 1 | 1 => 9 | 2 => 36 | 3 => 84 | 4 => 126 | 5 => 126 | 6 => 84 | 7 => 36 | 8 => 9
  | 9 => 1 | _ => 0

theorem cbz_nine (m : ℕ) (hm : m < 10) : cbz 9 (m : ℤ) = ((b9 m : ℚ) : ℂ) := by
  rw [cbz_apply_nonneg _ (by omega), Int.toNat_natCast, gBinom]
  interval_cases m <;> norm_num [b9, Finset.prod_range_succ, Nat.factorial]

/-- Partial sums of the Zhu polynomial of `u * v`. -/
def qPart : ℕ → PL
  | 0 => []
  | n + 1 => paddL (qPart n) (pscaleL (b9 n) (zhuV 9 (xsN (16 - n))))

/-- The Zhu polynomial `q` of `[u] * [v] / c`. -/
def qList : PL := [(101 : ℚ) / 12547518984, (-901509041 : ℚ) / 2213382348777600,
  (1884404070869 : ℚ) / 398408822779968000, (-6773430161261 : ℚ) / 358567940501971200,
  (11188459335227 : ℚ) / 325970855001792000, (-1409403466699 : ℚ) / 44820992562746400,
  (1659339096799 : ℚ) / 112052481406866000, (-1865186137 : ℚ) / 560262407034330,
  (221091457 : ℚ) / 823915304462250]

set_option maxRecDepth 100000 in
theorem qPart_ten : ptrim (qPart 10) = qList := by decide +kernel

theorem posV_xsN (N : ℕ) (hN : N ≤ 16) : posV (xsN N) = true := by
  simp only [posV, List.all_eq_true]
  intro p hp
  exact (levelOK_spec N hN p hp).2

theorem mk_uv_partial (c : ℂ)
    (hN : ∀ N : ℕ, N ≤ 16 → Wt.smul tetraU (15 - (N : ℤ)) tetraV = c • evV Wt tetraU (xsN N)) :
    ∀ n : ℕ, n ≤ 10 →
      ∑ m ∈ Finset.range n, cbz 9 (m : ℤ) • mk Wt (Wt.smul tetraU ((m : ℤ) - 1) tetraV) =
        c • aeval (omegaL Wt) (zp (qPart n)) (mk Wt tetraU) := by
  intro n
  induction n with
  | zero => intro _; simp [qPart, zp]
  | succ n ih =>
    intro hn
    rw [Finset.sum_range_succ, ih (by omega), cbz_nine n (by omega)]
    have e := hN (16 - n) (by omega)
    rw [show (15 : ℤ) - ((16 - n : ℕ) : ℤ) = (n : ℤ) - 1 by omega] at e
    have hpos := posV_xsN (16 - n) (by omega)
    have hmk := mk_evV Wt (h := 9) (x := tetraU) (by simpa using tetraU_mem) _ hpos
    rw [e, map_smul, hmk]
    simp only [qPart, zp_paddL, zp_pscaleL, map_add, map_mul, aeval_C, LinearMap.add_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, smul_add]
    push_cast
    rw [smul_comm]

/-- `[u] * [v] = c · q([ω]) [u]` with `u₍₁₅₎ v = c u`. -/
theorem tetra_uv_zhu : ∃ c : ℂ, Wt.smul tetraU 15 tetraV = c • tetraU ∧
    Amul (zhuRingData_holds Wt) (mk Wt tetraU) (mk Wt tetraV) =
      c • aeval (omegaL Wt) (zp qList) (mk Wt tetraU) := by
  obtain ⟨c, h15, hN⟩ := tetra_uv_chain
  refine ⟨c, h15, ?_⟩
  rw [Amul_mk, ZhuW2.zhuMul_of_mem_grading Wt tetraU_mem, map_sum]
  simp only [map_smul]
  have := mk_uv_partial c hN 10 le_rfl
  rw [show ((9 : ℤ).toNat + 1) = 10 by rfl, this, ← qPart_ten, zp_ptrim]

end VOA.Classification.COne.OrbOdd
