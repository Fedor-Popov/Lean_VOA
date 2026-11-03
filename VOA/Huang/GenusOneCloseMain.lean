import VOA.Huang.GenusOneClosePair
import VOA.Huang.LiConverseMain
import VOA.Huang.GenusOneModularity
import VOA.Modularity.BlockTranslation

/-!
# One-point genus-one S-closure for intertwining operators

The translation `τ ↦ τ+1` acts on the finite-dimensional space of analytic
insertion blocks and preserves the trace range. If the trace range were proper,
the quotient would contain a `T`-eigenvector `[F]`; subtracting traces of the
other `T`-eigenvalues leaves `F(τ+1) = μF(τ) + G(τ)` with `G` a trace sum of
eigenvalue `μ`. The analytic log-pair theorem then forces `G = 0` and puts `F`
in the trace range: a contradiction. Hence every analytic insertion block is a
sum of intertwiner traces (Miyamoto, math/0010180, Theorem 4.15), and with the
S-covariance of the block space (ibid., Theorem 5.1) the space of one-point
trace functions is S-invariant.

The final theorem consumes only strong rationality (with the PBW theorem `VOA.pbw` used through the
Zhu/Li inputs), irreducibility of the insertion
module, and a complete irredundant family of irreducible modules.
-/
namespace VOA.Huang.GenusOne.Close
open VOA Complex
open scoped BigOperators Real
universe u
variable {V M : Type u} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup M] [Module ℂ M] {W : VertexOperatorAlgebra V}
  {A : OrdVModule W M}

/-! ## Translation -/

theorem mem_imGT_add_one' {z : ℂ} (hz : z ∈ imGT 0) : z + 1 ∈ imGT 0 := by
  change (0 : ℝ) < (z + 1).im
  simpa using hz

theorem IsInsertionAnalyticBlock.translate {F : M → ℂ → ℂ} (hF : IsInsertionAnalyticBlock A F) :
    IsInsertionAnalyticBlock A (fun v z => F v (z + 1)) where
  holo := fun v => by
    intro z hz
    have hd : DifferentiableAt ℂ (F v) (z + 1) :=
      (hF.holo v).differentiableAt ((isOpen_imGT 0).mem_nhds (mem_imGT_add_one' hz))
    exact (hd.comp z ((differentiable_id.add_const 1) z)).differentiableWithinAt
  addv := fun v w z => hF.addv v w (z + 1)
  smulv := fun c v z => hF.smulv c v (z + 1)
  vanish := fun ka hka a ha v => by
    funext z
    exact congrFun (hF.vanish ka hka a ha v) (z + 1)
  negTwo := fun ka hka a ha v z hz => by
    have h := hF.negTwo ka hka a ha v (z + 1) (mem_imGT_add_one' hz)
    refine Eq.trans ?_ h
    congr 1
    refine finsum_congr (fun m => ?_)
    rw [zhuGC_add_one]
  omega := fun v z hz => by
    have h := hF.omega v (z + 1) (mem_imGT_add_one' hz)
    have hd : _root_.deriv (fun z => F v (z + 1)) z = _root_.deriv (F v) (z + 1) :=
      deriv_comp_add_const (f := F v) (a := 1) (x := z)
    rw [h, hd]
    congr 1
    refine finsum_congr (fun m => ?_)
    rw [zhuGC_add_one]

theorem coe_one_vadd (τ : UpperHalfPlane) :
    (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) = (τ : ℂ) + 1 := by
  rw [UpperHalfPlane.coe_vadd]
  push_cast
  ring

/-- Translation of functions on the upper half-plane. -/
noncomputable def shiftₗ : (M → UpperHalfPlane → ℂ) →ₗ[ℂ] (M → UpperHalfPlane → ℂ) where
  toFun f w τ := f w ((1 : ℝ) +ᵥ τ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [AddCommGroup M] [Module ℂ M] in
theorem shiftₗ_apply (f : M → UpperHalfPlane → ℂ) (w : M) (τ : UpperHalfPlane) :
    shiftₗ f w τ = f w ((1 : ℝ) +ᵥ τ) := rfl

omit [AddCommGroup M] [Module ℂ M] in
theorem shiftₗ_injective : Function.Injective (shiftₗ (M := M)) := by
  intro f g hfg
  funext w τ
  have h := congrFun (congrFun hfg w) ((-1 : ℝ) +ᵥ τ)
  simp only [shiftₗ_apply, vadd_vadd, add_neg_cancel, zero_vadd] at h
  exact h

theorem shiftₗ_mem {f : M → UpperHalfPlane → ℂ} (hf : f ∈ insertionBlockSpace A) :
    shiftₗ f ∈ insertionBlockSpace A := by
  obtain ⟨F, hF, rfl⟩ := Submodule.mem_map.mp hf
  refine Submodule.mem_map.mpr ⟨fun v z => F v (z + 1),
    IsInsertionAnalyticBlock.translate (hF : IsInsertionAnalyticBlock A F), ?_⟩
  funext w τ
  change F w ((τ : ℂ) + 1) = F w (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ)
  rw [coe_one_vadd]

/-! ## Trace families under translation -/

variable {ι : Type u} [Fintype ι]

/-- The `T`-eigenvalue of the traces on the `i`-th module. -/
noncomputable def tEig (W : VertexOperatorAlgebra V) (h : ι → ℂ) (i : ι) : ℂ :=
  cexp (2 * π * I * (h i - W.centralCharge / 24))

omit [Fintype ι] in
theorem tEig_ne_zero (h : ι → ℂ) (i : ι) : tEig W h i ≠ 0 := Complex.exp_ne_zero _

theorem traceFamily_mem (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Mfam : ι → IrrModule W) (h : ι → ℂ) (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (Z : ∀ i, IntertwiningOperator A (Mfam i).isMod (Mfam i).isMod) :
    traceFamilyLinear hC2 hA Mfam h hcw Z ∈ insertionBlockSpace A := by
  classical
  let G : M → ℂ → ℂ := ∑ i, anEval (trace (Z i)) (h i - W.centralCharge / 24)
  have hG : IsInsertionAnalyticBlock A G :=
    (insertionAnalyticBlocks A).sum_mem fun i _ =>
      isInsertionAnalyticBlock_trace_of_irreducible hC2 hA (Z i) (hcw i)
  refine Submodule.mem_map.mpr ⟨G, hG, ?_⟩
  funext w τ
  change G w τ = ∑ i, traceFunction (Z i) (h i) w τ
  simp only [G, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [anEval_of_mem _ _ _ τ.im_pos, qEvalC_coe]
  rfl

theorem traceFunction_smul (hC2 : C2Cofinite W) (hA : A.IsIrreducible) {N' : Type u}
    [AddCommGroup N'] [Module ℂ N'] {Nm : OrdVModule W N'} {h : ℂ}
    (hcw : HasConformalWeight Nm h) (c : ℂ) (Y : IntertwiningOperator A Nm Nm)
    (w : M) (τ : UpperHalfPlane) :
    traceFunction (c • Y) h w τ = c * traceFunction Y h w τ :=
  congrFun (congrFun ((traceFunctionLinear hC2 hA hcw).map_smul c Y) w) τ

theorem shift_traceFamily (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Mfam : ι → IrrModule W) (h : ι → ℂ) (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (Z : ∀ i, IntertwiningOperator A (Mfam i).isMod (Mfam i).isMod) :
    shiftₗ (traceFamilyLinear hC2 hA Mfam h hcw Z) =
      traceFamilyLinear hC2 hA Mfam h hcw (fun i => tEig W h i • Z i) := by
  funext w τ
  change (∑ i, traceFunction (Z i) (h i) w ((1 : ℝ) +ᵥ τ)) =
    ∑ i, traceFunction (tEig W h i • Z i) (h i) w τ
  apply Finset.sum_congr rfl
  intro i _
  rw [traceFunction_smul hC2 hA (hcw i), traceFunction_translate (Z i) (hcw i) w
    (coe_one_vadd τ)]
  rfl

/-! ## Conversion of formal trace sums at a common base -/

theorem good_shift {χ : FormalQSeries} {b : ℂ} (k : ℕ) (hχ : Good (b + (k : ℂ)) χ) :
    Good b χ ∧ ∀ z ∈ imGT 0, qEvalC χ b z = qEvalC χ (b + (k : ℂ)) z := by
  have hterm : ∀ z n, qTerm χ b (n + k) z =
      cexp (2 * π * I * (k : ℂ) * z) * qTerm χ (b + (k : ℂ)) n z := by
    intro z n
    simp only [qTerm]
    rw [show b + ((n + k : ℕ) : ℂ) = b + (k : ℂ) + (n : ℂ) by push_cast; ring,
      show 2 * (π : ℂ) * I * ((n + k : ℕ) : ℂ) * z =
        2 * π * I * (k : ℂ) * z + 2 * π * I * (n : ℂ) * z by push_cast; ring,
      Complex.exp_add]
    ring
  have hsum : ∀ z ∈ imGT 0, Summable (fun n : ℕ => qTerm χ b n z) := by
    intro z hz
    apply (summable_nat_add_iff k).mp
    exact ((hχ.2 z hz).mul_left (cexp (2 * π * I * (k : ℂ) * z))).congr
      fun n => (hterm z n).symm
  refine ⟨⟨QSeriesAt.of_add_nat k hχ.1, hsum⟩, fun z hz => ?_⟩
  have hsplit := (hsum z hz).sum_add_tsum_nat_add k
  have hzero : ∑ i ∈ Finset.range k, qTerm χ b i z = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [qTerm, QSeriesAt.coeff_below hχ.1 (Finset.mem_range.mp hi), zero_mul]
  rw [hzero, zero_add, tsum_congr (hterm z), tsum_mul_left] at hsplit
  rw [qEvalC, qEvalC, qSeriesC, qSeriesC, ← hsplit, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The complete family as bundled lowest-weight modules. -/
def lwFam (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i)) (i : ι) : LWModule W where
  carrier := (Mfam i).carrier
  isMod := (Mfam i).isMod
  h := h i
  isLow := (hcw i).2
  realized := (hcw i).1

theorem qEvalC_suppAt_sum (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Mfam : ι → IrrModule W) (h : ι → ℂ) (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    {b : ℂ} {Z : ∀ i, IntertwiningOperator A (Mfam i).isMod (Mfam i).isMod}
    (hZ : SuppAt (lwFam Mfam h hcw) b Z) (w : M) (τ : UpperHalfPlane) :
    qEvalC ((∑ i, trace (Z i)) w) b τ = traceFamilyLinear hC2 hA Mfam h hcw Z w τ := by
  classical
  have hgood : ∀ i, Good b (trace (Z i) w) ∧
      qEvalC (trace (Z i) w) b τ = traceFunction (Z i) (h i) w τ := by
    intro i
    by_cases hi : Z i = 0
    · rw [hi, trace_zero_apply]
      refine ⟨good_zero, ?_⟩
      rw [qEvalC_zero]
      exact (congrFun (congrFun ((traceFunctionLinear hC2 hA (hcw i)).map_zero) w) τ).symm
    · obtain ⟨k, hk⟩ := hZ i hi
      have hk' : h i - W.centralCharge / 24 = b + (k : ℂ) := by
        change h i = _ at hk
        rw [hk]; ring
      have hG : Good (b + (k : ℂ)) (trace (Z i) w) := by
        rw [← hk']
        exact ⟨trace_mem_QSeriesAt (Z i) (hcw i) w, fun z hz =>
          summable_qTerm _ _ (traceSubexponential_of_irreducible hC2 hA (Z i) (hcw i) w) hz⟩
      obtain ⟨hGb, heq⟩ := good_shift k hG
      refine ⟨hGb, ?_⟩
      rw [heq _ τ.im_pos, ← hk', qEvalC_coe]
      rfl
  rw [LinearMap.coe_sum, Finset.sum_apply, qEvalC_sum _ _ _ fun i _ => (hgood i).1.2 τ τ.im_pos]
  change _ = ∑ i, traceFunction (Z i) (h i) w τ
  exact Finset.sum_congr rfl fun i _ => (hgood i).2

/-! ## The spanning theorem -/

/-- **Trace spanning** (Miyamoto, math/0010180, Theorem 4.15), from the
quotient bimodule and the Li lifting inputs. -/
theorem insertionTraceSpanning_of_inputs (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Mfam : ι → IrrModule W) (h : ι → ℂ) (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hB : InsertionTopBimoduleExists A (lwFam Mfam h hcw))
    (hlift : InsertionTopSurjectivity A (lwFam Mfam h hcw)) :
    InsertionTraceSpanning A Mfam h := by
  classical
  haveI := finiteDimensional_insertionBlockSpace (moduleC2_of_irreducible hC2 hA)
  set E := insertionBlockSpace A with hE
  set Tr := insertionTraceRange hC2 hA Mfam h hcw with hTr
  set tr := traceFamilyLinear hC2 hA Mfam h hcw with htr
  have memTr : ∀ x : E, x ∈ Tr ↔ ∃ Z, tr Z = x.val := fun x => Iff.rfl
  suffices htop : Tr = ⊤ by
    intro F hF
    let x : E := ⟨insertionRestrict F, ⟨F, hF, rfl⟩⟩
    have hx : x ∈ Tr := by rw [htop]; trivial
    obtain ⟨Z, hZ⟩ := hx
    exact ⟨Z, fun w τ => (congrFun (congrFun hZ w) τ).symm⟩
  by_contra hne
  let T : Module.End ℂ E := shiftₗ.restrict (fun f hf => shiftₗ_mem hf)
  have hTval : ∀ x : E, (T x).val = shiftₗ x.val := fun x => rfl
  have hTTr : Tr ≤ Tr.comap T := by
    intro x hx
    obtain ⟨Z, hZ⟩ := (memTr x).mp hx
    exact (memTr (T x)).mpr ⟨fun i => tEig W h i • Z i, by
      rw [hTval, ← hZ, htr, shift_traceFamily]⟩
  -- a translate in the trace range came from the trace range
  have hpre : ∀ x : E, T x ∈ Tr → x ∈ Tr := by
    intro x hx
    obtain ⟨Z, hZ⟩ := (memTr (T x)).mp hx
    refine (memTr x).mpr ⟨fun i => (tEig W h i)⁻¹ • Z i, shiftₗ_injective ?_⟩
    rw [shift_traceFamily, ← hTval, ← hZ]
    congr 1
    funext i
    rw [smul_smul, mul_inv_cancel₀ (tEig_ne_zero h i), one_smul]
  let Tbar : Module.End ℂ (E ⧸ Tr) := Tr.mapQ Tr T hTTr
  haveI : Nontrivial (E ⧸ Tr) := Submodule.Quotient.nontrivial_iff.mpr hne
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue Tbar
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective Tr x
  have hfTr : f ∉ Tr := fun hf => hx.2 ((Submodule.Quotient.mk_eq_zero Tr).mpr hf)
  have hfx : T f - μ • f ∈ Tr := by
    have h1 := hx.apply_eq_smul
    rw [Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul] at h1
    exact (Submodule.Quotient.eq Tr).mp h1
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul, sub_zero] at hfx
    exact hfTr (hpre f hfx)
  obtain ⟨Z, hZ⟩ := (memTr _).mp hfx
  -- split the trace family by `T`-eigenvalue
  let Z₁ : ∀ i, IntertwiningOperator A (Mfam i).isMod (Mfam i).isMod :=
    fun i => if tEig W h i = μ then Z i else 0
  let Z₂ : ∀ i, IntertwiningOperator A (Mfam i).isMod (Mfam i).isMod :=
    fun i => if tEig W h i = μ then 0 else (tEig W h i - μ)⁻¹ • Z i
  let g : E := ⟨tr Z₂, traceFamily_mem hC2 hA Mfam h hcw Z₂⟩
  have hgTr : g ∈ Tr := (memTr g).mpr ⟨Z₂, rfl⟩
  let f' : E := f - g
  have hf'Tr : f' ∉ Tr := fun h' => hfTr (by simpa [f'] using Tr.add_mem h' hgTr)
  have hZsplit : Z - (fun i => tEig W h i • Z₂ i) + μ • Z₂ - Z₁ = 0 := by
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, Z₁, Z₂]
    by_cases hi : tEig W h i = μ
    · simp [hi]
    · simp only [hi, if_false, smul_smul]
      have hc : tEig W h i * (tEig W h i - μ)⁻¹ = 1 + μ * (tEig W h i - μ)⁻¹ := by
        rw [← sub_eq_iff_eq_add, ← sub_mul, mul_inv_cancel₀ (sub_ne_zero.mpr hi)]
      rw [hc, add_smul, one_smul]
      abel
  have hshift : shiftₗ f'.val = μ • f'.val + tr Z₁ := by
    have h1 : shiftₗ f.val = μ • f.val + tr Z := by
      rw [hZ]
      change shiftₗ f.val = μ • f.val + (shiftₗ f.val - μ • f.val)
      abel
    have h2 : shiftₗ (tr Z₂) = tr (fun i => tEig W h i • Z₂ i) := by
      rw [htr, shift_traceFamily]
    have h3 := congrArg tr hZsplit
    simp only [map_add, map_sub, map_smul, map_zero] at h3
    change shiftₗ (f.val - tr Z₂) = μ • (f.val - tr Z₂) + tr Z₁
    rw [map_sub, h1, h2, smul_sub]
    linear_combination (exp := 1) h3
  have hZ₁eig : shiftₗ (tr Z₁) = μ • tr Z₁ := by
    rw [htr, shift_traceFamily, ← map_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, Z₁]
    by_cases hi : tEig W h i = μ
    · simp [hi]
    · simp [hi]
  -- analytic representatives
  obtain ⟨F, hF, hFr⟩ := Submodule.mem_map.mp f'.property
  let G : M → ℂ → ℂ := ∑ i, anEval (trace (Z₁ i)) (h i - W.centralCharge / 24)
  have hG : IsInsertionAnalyticBlock A G :=
    (insertionAnalyticBlocks A).sum_mem fun i _ =>
      isInsertionAnalyticBlock_trace_of_irreducible hC2 hA (Z₁ i) (hcw i)
  have hGr : ∀ w (τ : UpperHalfPlane), G w τ = tr Z₁ w τ := by
    intro w τ
    change G w τ = ∑ i, traceFunction (Z₁ i) (h i) w τ
    simp only [G, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [anEval_of_mem _ _ _ τ.im_pos, qEvalC_coe]
    rfl
  have hFr' : ∀ w (τ : UpperHalfPlane), F w τ = f'.val w τ := fun w τ =>
    congrFun (congrFun hFr w) τ
  have hFper : ∀ w, ∀ z ∈ imGT 0, F w (z + 1) = μ * F w z + G w z := by
    intro w z hz
    let τ : UpperHalfPlane := ⟨z, hz⟩
    have h1 := congrFun (congrFun hshift w) τ
    rw [shiftₗ_apply] at h1
    have e1 : F w (z + 1) = f'.val w ((1 : ℝ) +ᵥ τ) := by
      rw [← hFr']; congr 1; rw [coe_one_vadd]
    rw [e1, h1, Pi.add_apply, Pi.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show z = (τ : ℂ) from rfl, hFr', hGr]
  have hGper : ∀ w, ∀ z ∈ imGT 0, G w (z + 1) = μ * G w z := by
    intro w z hz
    let τ : UpperHalfPlane := ⟨z, hz⟩
    have h1 := congrFun (congrFun hZ₁eig w) τ
    rw [shiftₗ_apply] at h1
    have e1 : G w (z + 1) = tr Z₁ w ((1 : ℝ) +ᵥ τ) := by
      rw [← hGr]; congr 1; rw [coe_one_vadd]
    rw [e1, h1, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, show z = (τ : ℂ) from rfl, hGr]
  -- the analytic logarithmic pair
  obtain ⟨-, b, Z'', hZ'', hFZ⟩ := log_pair_resolve (moduleC2_of_irreducible hC2 hA)
    (lwFam Mfam h hcw) hB hlift hF hG hμ0 hFper hGper
  apply hf'Tr
  refine (memTr f').mpr ⟨Z'', ?_⟩
  funext w τ
  rw [← hFr', hFZ w τ τ.im_pos]
  exact (qEvalC_suppAt_sum hC2 hA Mfam h hcw hZ'' w τ).symm

/-- **One-point S-closure from the two algebraic inputs.** -/
theorem insertionSClosure_of_inputs (hC2 : C2Cofinite W) (hA : A.IsIrreducible)
    (Mfam : ι → IrrModule W) (h : ι → ℂ) (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hB : InsertionTopBimoduleExists A (lwFam Mfam h hcw))
    (hlift : InsertionTopSurjectivity A (lwFam Mfam h hcw)) :
    InsertionSClosure A Mfam h :=
  insertionSClosure_of_covariance_spanning hC2 hA Mfam h hcw
    (insertionSBlockCovariance_of_irreducible hA)
    (insertionTraceSpanning_of_inputs hC2 hA Mfam h hcw hB hlift)

/-- **One-point modular S-closure for intertwining operators**
(Miyamoto, math/0010180, Theorems 4.15 and 5.1; Huang 2005): for a strongly
rational VOA, an irreducible insertion module, and a complete irredundant family
of irreducible modules with their conformal weights, the S-transform of every
one-point trace function `Tr 𝒴(w,·) q^{L(0)−c/24}` is a linear combination of
such trace functions, with coefficients uniform in the square-homogeneous
insertion vector. -/
theorem insertionSClosure_of_stronglyRational_pbw (hV : StronglyRational W)
    (hA : A.IsIrreducible) (Mfam : ι → IrrModule W) (h : ι → ℂ)
    (hcw : ∀ i, HasConformalWeight (Mfam i).isMod (h i))
    (hcomplete : ∀ Q : LWModule W, Q.IsIrreducibleLW → ∃ i, LWModule.Iso W Q (lwFam Mfam h hcw i))
    (hne : ∀ i j, i ≠ j →
      IsEmpty (AModEquiv W (lwFam Mfam h hcw i).toAMod (lwFam Mfam h hcw j).toAMod)) :
    InsertionSClosure A Mfam h := by
  have hP : ∀ i, (lwFam Mfam h hcw i).IsIrreducibleLW := fun i => (Mfam i).irreducible
  exact insertionSClosure_of_inputs hV.toStronglyFinite.c2Cofinite hA Mfam h hcw
    (LiConverse.insertionTopBimoduleExists_of_stronglyRational_pbw A hV (lwFam Mfam h hcw)
      hcomplete hP hne)
    (LiRegular.insertionTopSurjectivity_of_stronglyRational hV A (lwFam Mfam h hcw) hP)

end VOA.Huang.GenusOne.Close
