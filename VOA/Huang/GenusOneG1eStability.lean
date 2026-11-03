import VOA.Huang.GenusOneG1dBracket
import VOA.Huang.GenusOneCloseMain

/-!
# (N3) `ChannelSStability` from the bracket-coordinate expansion of an iterate channel

Step (5a) of the proof of (G1).

**The reduction.** An `(a,b)`-orthogonal channel `C` (inner `Y_in : M_a ⊗ M_b → M_k`, outer
`Y_out` of type `(M_y / M_k M_y)`) has a bracket-coordinate expansion
`C.eval ins τ u = Σ_m coef_m u^{β_m − κ} Tr_{M_y} o_{Y_out}(v_m) q^{L₀−c/24}` whose data
`(coef_m, v_m ∈ M_k, β_m = L[0]-weight of v_m)` depend ONLY on the inner part and the insertion,
not on `(y, Y_out)` nor on `τ` (`v_m` are the bracket modes `(w_a)[s] w_b` of `Y_in`). This is the
named input `InnerBracketSharp` (TRUE: Zhu/Huang coordinate change for intertwining operators,
`Y_in(e^{u L(0)} w_a, e^u − 1) = Y_in[w_a, u]`; it is the same coordinate change as
`VacuumChannelBracketSharp`, for a general irreducible inner module).

Given it, the S-transform of `C` is computed termwise with the proved one-point S-closure for
intertwining operators (`insertionSClosure_of_stronglyRational_pbw`), applied THREE times: with
`tf_Y(Sτ) = τ^β Σ_j tf_{Z_j}(τ)` one gets `tf_Y(Sτ) = e^{2πiβ} (Sτ)^{−β} Σ_{j,l,n} tf_{Z_{jln}}(τ)`
(the S-action has order dividing 4 up to the scalar `e^{2πiβ}`, so it is invertible on the trace
functions), `e^{2πiβ} = e^{2πi h_k}` is constant (`β ∈ h_k + ℤ`), and
`e^{iπκ} τ^{−κ} (−u/τ)^{β−κ} (Sτ)^{−β} = u^{β−κ}` (`log τ + log Sτ = iπ`,
`log(−u/τ) = log u + log Sτ`). So `e^{iπκ} τ^{−κ} C(Sτ, −u/τ) = e^{2πi h_k} Σ_{jln} C_{jln}(τ, u)`
with `C_{jln}` the channels with the SAME inner part and outer `Z_{jln}`: they are again
`(a,b)`-orthogonal channels, so the S-transform lies in `Rspan`.

* `log_neg_div_eq` — `log(−u/τ) = log u + log(Sτ)` on the right half-plane;
* `sClosure_fam` — the one-point S-closure re-indexed for a `ModularData` family (label set in
  universe `w`);
* `InnerBracketSharp`, `ChannelBracketSharpInput` — the named coordinate-change input;
* `channelSStability_of_bracket` — (N3) for one instance;
* `channelSStabilityInput_of_bracket : ChannelBracketSharpInput → ChannelSStabilityInput`.
-/

noncomputable section

namespace VOA.Huang.GenusOneG1e

open VOA VOA.Huang VOA.Huang.TensorCat VOA.Huang.FusionProduct VOA.Huang.FusionUnit
  VOA.Huang.VerlindeTransport VOA.Huang.VerlindeFusion VOA.Huang.GenusOneG1c
  VOA.Huang.GenusOneG1d CategoryTheory Complex VOA.Classification.COne VOA.Huang.ZhuModData
open VOA.Huang.GenusOne (sqL traceFunction InsertionSClosure)
open scoped BigOperators

universe u w

/-! ## §1 A logarithm identity -/

/-- `log(−u/τ) = log u + log(Sτ)` when `u` and `−u/τ` lie in the right half-plane. -/
theorem log_neg_div_eq (τ : UpperHalfPlane) {u : ℂ} (hu : 0 < u.re) (hv : 0 < (-u / τ).re) :
    log (-u / τ) = log u + log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hSne : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) ≠ 0 := UpperHalfPlane.ne_zero _
  have hu0 : u ≠ 0 := fun h => by rw [h, Complex.zero_re] at hu; exact lt_irrefl _ hu
  have hv0 : -u / τ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hu0) hτ
  have heq : -u / τ = u * ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) := by
    rw [coe_S_smul]; ring
  have hexp : exp (log (-u / τ)) =
      exp (log u + log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)) := by
    rw [exp_add, exp_log hv0, exp_log hu0, exp_log hSne, heq]
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have him := congrArg Complex.im hk
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, add_zero, mul_one, Complex.intCast_re,
    Complex.intCast_im, zero_add] at him
  have h2pi : ((2 : ℂ) * (Real.pi : ℂ)).re = 2 * Real.pi := by
    rw [show ((2 : ℂ) * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [h2pi, Complex.log_im, Complex.log_im, Complex.log_im] at him
  have ha1 : |(-u / τ).arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hv)
  have ha2 : |u.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu)
  have hSim : 0 < ((ModularGroup.S • τ : UpperHalfPlane) : ℂ).im := (ModularGroup.S • τ).im_pos
  have ha3 : 0 ≤ ((ModularGroup.S • τ : UpperHalfPlane) : ℂ).arg :=
    Complex.arg_nonneg_iff.mpr hSim.le
  have ha4 : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ).arg < Real.pi :=
    Complex.arg_lt_pi_iff.mpr (Or.inr hSim.ne')
  have hk0 : k = 0 := by
    have hpi := Real.pi_pos
    have h1 := abs_lt.mp ha1
    have h2 := abs_lt.mp ha2
    have hk1 : (-1 : ℝ) < k := by nlinarith
    have hk2 : (k : ℝ) < 1 := by nlinarith
    have : (-1 : ℤ) < k := by exact_mod_cast hk1
    have : k < 1 := by exact_mod_cast hk2
    omega
  rw [hk0] at hk
  simp only [Int.cast_zero, zero_mul, add_zero] at hk
  exact hk

/-! ## §2 One-point S-closure on a `ModularData` family -/

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}
  {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- A copy of the label set in the universe of the VOA (the S-closure theorem is stated for label
sets in that universe). The argument `W` only fixes the universe. -/
abbrev Lab (_W : VertexOperatorAlgebra 𝒱) (ι : Type w) [Fintype ι] : Type u :=
  ULift.{u} (Fin (Fintype.card ι))

/-- The label of a copied index. -/
def lab (W : VertexOperatorAlgebra 𝒱) (ι : Type w) [Fintype ι] (j : Lab W ι) : ι :=
  (Fintype.equivFin ι).symm j.down

omit [DecidableEq ι] in
theorem lab_surj (W : VertexOperatorAlgebra 𝒱) (x : ι) : ∃ j : Lab W ι, lab W ι j = x :=
  ⟨ULift.up (Fintype.equivFin ι x), by simp [lab]⟩

omit [DecidableEq ι] in
theorem lab_injective (W : VertexOperatorAlgebra 𝒱) : Function.Injective (lab W ι) := by
  intro i j h
  unfold lab at h
  exact ULift.ext _ _ ((Fintype.equivFin ι).symm.injective h)

/-- **One-point S-closure for the intertwiners `(M_y / M_k M_y)` of a `ModularData` family**
(`insertionSClosure_of_stronglyRational_pbw`, re-indexed): for every outer intertwiner `Y` there
are intertwiners `Z_j` into the members `M_{lab j}`, uniform in the square-homogeneous insertion
and in `τ`, with `tf_Y(w, Sτ) = τ^α Σ_j tf_{Z_j}(w, τ)`. -/
theorem sClosure_fam (hV : StronglyRational W) (D : VOA.ModularData W ι)
    (hirr : Irredundant D.Mfam) (hcomp : Complete D.Mfam) (k y : ι)
    (Y : IntertwiningOperator (lwOf D k).isMod (lwOf D y).isMod (lwOf D y).isMod) :
    ∃ Z : ∀ j : Lab W ι, IntertwiningOperator (lwOf D k).isMod (lwOf D (lab W ι j)).isMod
        (lwOf D (lab W ι j)).isMod,
      ∀ (α : ℂ) (w : (lwOf D k).carrier), sqL (lwOf D k).isMod 0 w = α • w →
        ∀ τ : UpperHalfPlane, traceFunction Y (D.h y) w (ModularGroup.S • τ) =
          (τ : ℂ) ^ α * ∑ j, traceFunction (Z j) (D.h (lab W ι j)) w τ := by
  obtain ⟨i, rfl⟩ := lab_surj W y
  have hcl : InsertionSClosure (lwOf D k).isMod (fun j : Lab W ι => D.Mfam (lab W ι j))
      (fun j => D.h (lab W ι j)) := by
    refine GenusOne.Close.insertionSClosure_of_stronglyRational_pbw hV (D.Mfam k).irreducible
      _ _ (fun j => D.hasWeight _) ?_ ?_
    · intro Q hQ
      obtain ⟨x, hx⟩ := hcomp (IrrLWModule.forget ⟨Q, hQ⟩)
      obtain ⟨j, rfl⟩ := lab_surj W x
      exact ⟨j, hx⟩
    · intro i j hij
      obtain ⟨Pr⟩ := zhuPBWBottomInput_of_pbw 𝒱 W
      constructor
      intro e
      let Pi : IrrLWModule W := ⟨GenusOne.Close.lwFam (fun j : Lab W ι => D.Mfam (lab W ι j))
        (fun j => D.h (lab W ι j)) (fun j => D.hasWeight _) i, (D.Mfam (lab W ι i)).irreducible⟩
      let Pj : IrrLWModule W := ⟨GenusOne.Close.lwFam (fun j : Lab W ι => D.Mfam (lab W ι j))
        (fun j => D.h (lab W ι j)) (fun j => D.hasWeight _) j, (D.Mfam (lab W ι j)).irreducible⟩
      have hf : forwardMapIrr W (Quotient.mk (IrrLWModule.setoid W) Pi) =
          forwardMapIrr W (Quotient.mk (IrrLWModule.setoid W) Pj) := by
        rw [forwardMapIrr_mk, forwardMapIrr_mk]
        exact Quotient.sound ⟨e⟩
      have he := Quotient.exact ((zhuBijective Pr).1 hf)
      exact hij (lab_injective W (hirr _ _ he))
  exact hcl i Y

/-! ## §3 The named coordinate-change input -/

/-- **The sharp bracket-coordinate expansion of an iterate channel with inner intertwiner `Y_in`**
(TRUE: Zhu's coordinate change for intertwining operators, `Y_in(e^{u L(0)} w_a, e^u − 1) w_b =
Y_in[w_a, u] w_b = Σ_s (w_a)[s] w_b u^{−s−1}`, with `(w_a)[s] w_b` of `L[0]`-weight
`κ − s − 1 ∈ h_Q + ℕ` (`L[0]` is triangular with diagonal `L(0)`, so its eigenvalues on an
irreducible module lie in `h_Q + ℕ`; zero components get `β = h_Q`); the genus-one trace of the
outer intertwiner at `1` is the one-point
function `traceFunction`; the double series is absolutely convergent near the collision).
The data `(coef, v, β)` depend only on the insertion and on `Y_in`, NOT on the outer intertwiner,
the traced module, or `τ` — the defining feature (the `v_m` are vectors of the inner module).
For `Q = V`, `Y_out = Y_{M_x}` this is `VacuumChannelBracketSharp`. -/
def InnerBracketSharp (D : VOA.ModularData W ι) {a b : ι} (Q : LWModule W)
    (Yin : IntertwiningOperator (lwOf D a).isMod (lwOf D b).isMod Q.isMod) : Prop :=
  ∀ ins : Insertion D a b, ∃ (coef : ℕ → ℂ) (v : ℕ → Q.carrier) (β : ℕ → ℂ),
    (∀ m, sqL Q.isMod 0 (v m) = β m • v m) ∧ (∀ m, ∃ n : ℕ, β m = Q.h + n) ∧
    ∀ (y : ι) (Yout : IntertwiningOperator Q.isMod (lwOf D y).isMod (lwOf D y).isMod)
      (τ : UpperHalfPlane), ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → 0 < (exp u - 1).re →
        Summable (fun m => coef m * exp ((β m - ins.κ) * log u) *
          traceFunction Yout (D.h y) (v m) τ) ∧
        ∑ i, ∑ j, exp (ins.αa i * u) * iterF (Q := Q) (N := lwOf D y) Yout Yin (ins.wa i)
            (ins.wb j) (ins.αa i) (ins.αb j) τ (exp u - 1) =
          ∑' m, coef m * exp ((β m - ins.κ) * log u) * traceFunction Yout (D.h y) (v m) τ

/-- The coordinate-change input for every instance and every irreducible inner module. -/
def ChannelBracketSharpInput : Prop :=
  ∀ (𝒱 : Type u) [AddCommGroup 𝒱] [Module ℂ 𝒱] (W : VertexOperatorAlgebra 𝒱), Nice W →
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (D : VOA.ModularData W ι),
      ZhuModularityAnalytic D → Irredundant D.Mfam → Complete D.Mfam →
      ∀ (a b : ι) (Q : LWModule W), Q.IsIrreducibleLW →
        ∀ Yin : IntertwiningOperator (lwOf D a).isMod (lwOf D b).isMod Q.isMod,
          InnerBracketSharp D Q Yin

/-! ## §4 (N3) -/

/-- The triple S-closure: `tf_Y(w, Sτ) = e^{2πi h_k} e^{−β log Sτ} Σ_{jln} tf_{Z_{jln}}(w, τ)`. -/
theorem triple_closure (D : VOA.ModularData W ι) (k : ι)
    (Zf : ∀ (y : ι) (_ : IntertwiningOperator (lwOf D k).isMod (lwOf D y).isMod (lwOf D y).isMod)
      (j : Lab W ι), IntertwiningOperator (lwOf D k).isMod (lwOf D (lab W ι j)).isMod
        (lwOf D (lab W ι j)).isMod)
    (hZf : ∀ (y : ι) (Y : IntertwiningOperator (lwOf D k).isMod (lwOf D y).isMod (lwOf D y).isMod)
      (α : ℂ) (w : (lwOf D k).carrier), sqL (lwOf D k).isMod 0 w = α • w →
        ∀ τ : UpperHalfPlane, traceFunction Y (D.h y) w (ModularGroup.S • τ) =
          (τ : ℂ) ^ α * ∑ j, traceFunction (Zf y Y j) (D.h (lab W ι j)) w τ)
    (y : ι) (Y : IntertwiningOperator (lwOf D k).isMod (lwOf D y).isMod (lwOf D y).isMod)
    (α : ℂ) (n : ℤ) (hα : α = D.h k + n) (w : (lwOf D k).carrier)
    (hw : sqL (lwOf D k).isMod 0 w = α • w) (τ : UpperHalfPlane) :
    traceFunction Y (D.h y) w (ModularGroup.S • τ) =
      exp (2 * (Real.pi : ℂ) * I * D.h k) *
        exp (-(α * log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ))) *
        ∑ p : Lab W ι × Lab W ι × Lab W ι,
          traceFunction (Zf (lab W ι p.2.1) (Zf (lab W ι p.1) (Zf y Y p.1) p.2.1) p.2.2)
            (D.h (lab W ι p.2.2)) w τ := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hSne : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) ≠ 0 := UpperHalfPlane.ne_zero _
  have h2 : ∀ j, traceFunction (Zf y Y j) (D.h (lab W ι j)) w τ =
      ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) ^ α * (τ : ℂ) ^ α *
        ∑ l, ∑ n, traceFunction (Zf (lab W ι l) (Zf (lab W ι j) (Zf y Y j) l) n)
          (D.h (lab W ι n)) w τ := by
    intro j
    have h := hZf (lab W ι j) (Zf y Y j) α w hw (ModularGroup.S • τ)
    rw [S_smul_S_smul] at h
    rw [h, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => hZf (lab W ι l) _ α w hw τ
  have hsum : ∀ f : Lab W ι × Lab W ι × Lab W ι → ℂ,
      ∑ p, f p = ∑ j, ∑ l, ∑ n, f (j, l, n) := by
    intro f
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
  rw [hZf y Y α w hw τ, hsum, Finset.sum_congr rfl (fun j _ => h2 j), ← Finset.mul_sum]
  rw [Complex.cpow_def_of_ne_zero hτ, Complex.cpow_def_of_ne_zero hSne]
  have hLL := log_add_log_S τ
  have h2πn : exp (2 * (Real.pi : ℂ) * I * α) = exp (2 * (Real.pi : ℂ) * I * D.h k) := by
    rw [hα, mul_add, exp_add, show 2 * (Real.pi : ℂ) * I * (n : ℂ) = n * (2 * Real.pi * I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hE : exp (log (τ : ℂ) * α) * (exp (log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) * α) *
      exp (log (τ : ℂ) * α)) = exp (2 * (Real.pi : ℂ) * I * α) *
        exp (-(α * log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ))) := by
    rw [← exp_add, ← exp_add, ← exp_add]
    congr 1
    linear_combination (2 * α) * hLL
  rw [← h2πn, ← hE]
  ring

/-- **(N3) for one instance, from the bracket expansion of the orthogonal channels.** The
S-transform of an `(a,b)`-orthogonal channel `C` is, near the collision, `e^{2πi h_k}` times a
finite sum of `(a,b)`-orthogonal channels with the same inner part (`k`, `q`) and outer
intertwiners produced by the one-point S-closure. -/
theorem channelSStability_of_bracket (F : FusionChoice W) (hV : StronglyRational W)
    (D : VOA.ModularData W ι) (hirr : Irredundant D.Mfam) (hcomp : Complete D.Mfam) {a b : ι}
    (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b))
    (η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a))
    (hB : ∀ (k : ι)
      (Yin : IntertwiningOperator (lwOf D a).isMod (lwOf D b).isMod (lwOf D k).isMod),
      InnerBracketSharp D (lwOf D k) Yin) :
    ChannelSStability F η' η := by
  intro C
  have hcl := fun (y : ι)
      (Y : IntertwiningOperator (lwOf D C.k).isMod (lwOf D y).isMod (lwOf D y).isMod) =>
    sClosure_fam hV D hirr hcomp C.k y Y
  choose Zf hZf using hcl
  let Cp : Lab W ι × Lab W ι × Lab W ι → ABChannel F D a b η' := fun p =>
    { k := C.k, y := lab W ι p.2.2, q := C.q, hq := C.hq,
      Yout := Zf (lab W ι p.2.1) (Zf (lab W ι p.1) (Zf C.y C.Yout p.1) p.2.1) p.2.2 }
  set e : ℂ := exp (2 * (Real.pi : ℂ) * I * D.h C.k) with he
  set G : FunSpace D a b := fun ins τ u => exp ((Real.pi : ℂ) * I * ins.κ) *
    exp (-(ins.κ * log τ)) * C.eval ins (ModularGroup.S • τ) (-u / τ) with hG
  set Sf : FunSpace D a b := ∑ p, (fun ins τ u => (Cp p).eval ins τ u) with hSf
  have hSmem : Sf ∈ Rspan η' η := Submodule.sum_mem _ fun p _ =>
    Submodule.mem_sup_left (Submodule.subset_span (Set.mem_union_left _ ⟨Cp p, rfl⟩))
  have hZ : G - e • Sf ∈ germZero D a b := by
    intro ins τ
    obtain ⟨coef, v, β, hsq, hβ, hE⟩ := hB C.k C.inner ins
    obtain ⟨δ0, hδ0, h0⟩ := hE C.y C.Yout (ModularGroup.S • τ)
    choose δp hδp hp using fun p : Lab W ι × Lab W ι × Lab W ι =>
      hE (lab W ι p.2.2) (Cp p).Yout τ
    obtain ⟨δ1, hδ1, hδ1le⟩ := exists_pos_le_fintype δp hδp
    have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
    have hτn : 0 < ‖(τ : ℂ)‖ := norm_pos_iff.mpr hτ
    refine ⟨min (δ0 * ‖(τ : ℂ)‖) δ1, lt_min (mul_pos hδ0 hτn) hδ1, fun u hu => ?_⟩
    obtain ⟨hn, hre, hre'⟩ := hu
    have hn0 : ‖-u / (τ : ℂ)‖ < δ0 := by
      rw [norm_div, norm_neg, div_lt_iff₀ hτn]; exact lt_of_lt_of_le hn (min_le_left _ _)
    have hnp : ∀ p, ‖u‖ < δp p := fun p =>
      lt_of_lt_of_le (lt_of_lt_of_le hn (min_le_right _ _)) (hδ1le p)
    have hpu := re_pos_of_re_exp_sub_one_pos hre
    have hpv := re_pos_of_re_exp_sub_one_pos hre'
    have hlog := log_neg_div_eq τ hpu hpv
    have hLL := log_add_log_S τ
    have hGv : G ins τ u = exp ((Real.pi : ℂ) * I * ins.κ) * exp (-(ins.κ * log τ)) *
        ∑' m, coef m * exp ((β m - ins.κ) * log (-u / τ)) *
          traceFunction C.Yout (D.h C.y) (v m) (ModularGroup.S • τ) := by
      simp only [hG]
      unfold ABChannel.eval
      rw [(h0 (-u / τ) hn0 hre').2]
    have hSv : Sf ins τ u = ∑ p, ∑' m, coef m * exp ((β m - ins.κ) * log u) *
        traceFunction (Cp p).Yout (D.h (lab W ι p.2.2)) (v m) τ := by
      simp only [hSf, Finset.sum_apply]
      exact Finset.sum_congr rfl fun p _ => (hp p u (hnp p) hre).2
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hGv, hSv, ← Summable.tsum_finsetSum (fun p _ => (hp p u (hnp p) hre).1), sub_eq_zero,
      ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    obtain ⟨n, hn⟩ := hβ m
    have hn' : β m = D.h C.k + ((n : ℤ) : ℂ) := by rw [hn]; push_cast; rfl
    rw [hlog, triple_closure D C.k Zf hZf C.y C.Yout (β m) n hn' (v m) (hsq m) τ,
      ← Finset.mul_sum]
    have hsame : (∑ p, traceFunction (Cp p).Yout (D.h (lab W ι p.2.2)) (v m) τ) =
        ∑ p : Lab W ι × Lab W ι × Lab W ι,
          traceFunction (Zf (lab W ι p.2.1) (Zf (lab W ι p.1) (Zf C.y C.Yout p.1) p.2.1) p.2.2)
            (D.h (lab W ι p.2.2)) (v m) τ := rfl
    rw [hsame]
    generalize (∑ p : Lab W ι × Lab W ι × Lab W ι,
      traceFunction (Zf (lab W ι p.2.1) (Zf (lab W ι p.1) (Zf C.y C.Yout p.1) p.2.1) p.2.2)
        (D.h (lab W ι p.2.2)) (v m) τ) = T
    have hX : exp ((Real.pi : ℂ) * I * ins.κ) * exp (-(ins.κ * log τ)) *
        exp ((β m - ins.κ) * (log u + log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ))) *
        exp (-(β m * log ((ModularGroup.S • τ : UpperHalfPlane) : ℂ))) =
          exp ((β m - ins.κ) * log u) := by
      rw [← exp_add, ← exp_add, ← exp_add]
      congr 1
      linear_combination (-ins.κ) * hLL
    rw [← he]
    linear_combination (coef m * e * T) * hX
  have hsplit : G = (G - e • Sf) + e • Sf := by abel
  change G ∈ Rspan η' η
  rw [hsplit]
  exact Submodule.add_mem _ (Submodule.mem_sup_right hZ) (Submodule.smul_mem _ _ hSmem)

/-- **(N3) for every instance from the coordinate-change input.** -/
theorem channelSStabilityInput_of_bracket (h : ChannelBracketSharpInput.{u, w}) :
    ChannelSStabilityInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D hZ hirr hcomp F a b c η' _
  exact channelSStability_of_bracket F hNice.1 D hirr hcomp η' c.η fun k Yin =>
    h 𝒱 W hNice ι D hZ hirr hcomp a b (lwOf D k) (lwOf_irreducible D k) Yin

end VOA.Huang.GenusOneG1e
