import VOA.Huang.LiConverseTarget

/-! # The numeric Jacobi identity of the reconstructed intertwiner

In the target frame `D_{P(−1)}(P₃')` the maps `Φ_w : P₂ → D` are `V ⊗ V`-equivariant
(`PhiT_equiv`, `PhiT_M`).  Translating the base by `+1` puts `P₂` at `0` and `M` at `1`; the
three-way relation of the translated frame (`threeWay_gen`) is then, after composing with
`e^{L(1)}` on `P₃'`, the Jacobi identity at `x = 1` of the trilinear form

  `G(w, y, g) = Φ_w(y)(e^{L(1)} g)`,   `w ∈ M`, `y ∈ P₂`, `g ∈ P₃'`

with `P₃` (through the opposite modes of `P₃'`) at `∞`:  `numeric_jacobi`.

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.VertexOperatorAlgebra VOA.Huang.LiFusion VOA.Huang.HuangODEContra VOA.FZ
  FusionTop LaurentPolynomial VHat VHat.DLM3
open scoped BigOperators Polynomial

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## Generalities -/

theorem expOp_comm {E : Type*} [AddCommGroup E] [Module ℂ E] {A : Module.End ℂ E}
    (hA : LocNil A) (c : ℂ) (x : E) : A (expOp hA c x) = expOp hA c (A x) := by
  obtain ⟨J, hJ⟩ := hA x
  have hJ' : (A ^ J) (A x) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hJ, map_zero]
  rw [expOp_eq_sum hA c hJ, expOp_eq_sum hA c hJ', map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, ← Module.End.mul_apply, ← pow_succ', pow_succ, Module.End.mul_apply]

theorem expOp_fix {E : Type*} [AddCommGroup E] [Module ℂ E] {A : Module.End ℂ E}
    (hA : LocNil A) (c : ℂ) {x : E} (hx : A x = 0) : expOp hA c x = x := by
  rw [expOp_eq_sum hA c (J := 1) (by simpa using hx)]
  simp

theorem OppBase.ext' {E : Type*} [AddCommGroup E] [Module ℂ E] {B₁ B₂ : OppBase W E}
    (h : ∀ a n y, B₁.B a n y = B₂.B a n y) : B₁ = B₂ := by
  obtain ⟨b₁, t₁, v₁, j₁⟩ := B₁
  obtain ⟨b₂, t₂, v₂, j₂⟩ := B₂
  have : b₁ = b₂ := LinearMap.ext fun a => funext fun n => LinearMap.ext fun y => h a n y
  subst this
  rfl

section Final

variable (A : OrdVModule W M) {P₂ P₃ : LWModule W} (T : fzSpace A P₂ P₃)
  (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
  (hrat : AdmissiblyRational W) (hP₃ : P₃.IsIrreducibleLW) (hP₂ : P₂.IsIrreducibleLW)

/-- The translation parameter `−(−1) = 1`. -/
abbrev zT : ℂ := -(-1 : ℂ)

/-- `L(1)` on `P₃'`. -/
noncomputable abbrev XQ (P₃ : LWModule W) : Module.End ℂ (Q₃ P₃).carrier := L1m (Qm P₃)

theorem XQ_locNil (P₃ : LWModule W) : LocNil (XQ P₃) := L1m_locNil (Qm P₃)

/-- The translated base of the target frame. -/
noncomputable abbrev Ts (P₃ : LWModule W) : OppBase W (Q₃ P₃).carrier := transBase (Qm P₃) zT

theorem Ts_B (P₃ : LWModule W) (a : V) (n : ℤ) (y : (Q₃ P₃).carrier) :
    (Ts P₃).B a n y
      = expOp (XQ_locNil P₃) zT (oppB (Qm P₃) a n (expOp (XQ_locNil P₃) (-zT) y)) := rfl

/-- The translation datum of the translated base. -/
noncomputable def TsShift (P₃ : LWModule W) : (Ts P₃).Shift where
  X := XQ P₃
  locNil := XQ_locNil P₃
  comm a n y := by
    rw [Ts_B, Ts_B, Ts_B, expOp_comm, ← expOp_comm (XQ_locNil P₃) (-zT), ← map_sub]
    have := L1_oppB (Qm P₃) a n (expOp (XQ_locNil P₃) (-zT) y)
    rw [show oppB (Qm P₃) a n (L1m (Qm P₃) (expOp (XQ_locNil P₃) (-zT) y))
        = oppB (Qm P₃) a n (XQ P₃ (expOp (XQ_locNil P₃) (-zT) y)) from rfl] at this
    change expOp _ zT (L1m (Qm P₃) _ - _) = _
    rw [this, map_smul]

theorem Ts_back (P₃ : LWModule W) : (Ts P₃).tBase (TsShift P₃) (-zT) = oppBase (Qm P₃) := by
  refine OppBase.ext' fun a n y => ?_
  change expOp (XQ_locNil P₃) (-zT) ((Ts P₃).B a n (expOp (XQ_locNil P₃) (-(-zT)) y)) = _
  rw [Ts_B]
  simp only [expOp_add]
  norm_num [expOp_zero]
  rfl

theorem zT_ne_zero : zT ≠ 0 := neg_neg_one_ne_zero

/-- The reconstructed trilinear form `G(w, y, g) = Φ_w(y)(e^{L(1)} g)`. -/
noncomputable def Gt (w : M) (y : P₂.carrier) (g : (Q₃ P₃).carrier) : ℂ :=
  ((PhiT A T Pr hrat hP₃ hP₂ w y : (oppBase (Qm P₃)).Dsub (-1)) : Module.Dual ℂ (Q₃ P₃).carrier)
    (expOp (XQ_locNil P₃) zT g)

/-- **The numeric Jacobi identity at `x = 1`** (finite form). -/
theorem numeric_jacobi (a : V) (l m : ℤ) (x : M) (y : P₂.carrier) (g : (Q₃ P₃).carrier) :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      ∑ k ∈ Finset.range J, (cbz l k * (-1 : ℂ) ^ k) *
          Gt A T Pr hrat hP₃ hP₂ x y (oppB (Qm P₃) a (l + m - k) g)
        - ∑ i ∈ Finset.range J, (cbz l i * (-1 : ℂ) ^ (l - i)) *
          Gt A T Pr hrat hP₃ hP₂ x (mode (P₂.isMod.YM a) (m + i) y) g
      = ∑ i ∈ Finset.range J, cbz m i *
          Gt A T Pr hrat hP₃ hP₂ (mode (A.YM a) (l + i) x) y g := by
  set α : Module.Dual ℂ (Q₃ P₃).carrier :=
    ((PhiT A T Pr hrat hP₃ hP₂ x y : (oppBase (Qm P₃)).Dsub (-1)) :
      Module.Dual ℂ (Q₃ P₃).carrier) with hαdef
  have hα : (oppBase (Qm P₃)).InD (-1) α := (PhiT A T Pr hrat hP₃ hP₂ x y).2
  have hαT : (Ts P₃).InD zT α := (inD_iff_trans (Qm P₃) α).1 hα
  have h3 := (Ts P₃).threeWay_gen (TsShift P₃) zT_ne_zero hαT a l m
  obtain ⟨KR, hKR⟩ := (Ts P₃).rModes_trunc zT_ne_zero hαT a
  obtain ⟨KL, hKL⟩ := (Ts P₃).lModes_trunc (TsShift P₃) zT_ne_zero hαT a
  set g' := expOp (XQ_locNil P₃) zT g
  obtain ⟨K₀, hK₀⟩ := (Ts P₃).mixTerm_eventually_zero zT a l m g'
  refine ⟨max K₀ (max (KR - m).toNat (KL - l).toNat), fun J hJ => ?_⟩
  have hJ0 : K₀ ≤ J := le_trans (le_max_left _ _) hJ
  have hJR : KR ≤ m + J := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hJ; omega
  have hJL : KL ≤ l + J := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hJ; omega
  have h3g := LinearMap.congr_fun h3 g'
  rw [sumR_eq _ _ hKR l m J hJR, sumR_eq _ _ hKL m l J hJL] at h3g
  -- the three pieces
  have hmix : ((Ts P₃).mixOp zT a l m).dualMap α g'
      = ∑ k ∈ Finset.range J, (cbz l k * (-1 : ℂ) ^ k) *
          Gt A T Pr hrat hP₃ hP₂ x y (oppB (Qm P₃) a (l + m - k) g) := by
    rw [LinearMap.dualMap_apply, (Ts P₃).mixOp_eq_sum zT a l m g' (K₀ := J)
      (fun k hk => hK₀ k (le_trans hJ0 hk)), map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [OppBase.mixTerm, map_smul, smul_eq_mul, Ts_B, expOp_cancel_neg, Gt]
    norm_num
    exact Or.inl rfl
  have hR : ∀ i : ℕ, (Ts P₃).rModes zT_ne_zero a α (m + i) g'
      = Gt A T Pr hrat hP₃ hP₂ x (mode (P₂.isMod.YM a) (m + i) y) g := by
    intro i
    rw [OppBase.rModes, Gt, PhiT_equiv, Lt_mode_coe]
  have hL : ∀ i : ℕ, (Ts P₃).lModes (TsShift P₃) zT_ne_zero a α (l + i) g'
      = Gt A T Pr hrat hP₃ hP₂ (mode (A.YM a) (l + i) x) y g := by
    intro i
    rw [OppBase.lModes, Ts_back, OppBase.yR_congr _ (show -zT = (-1 : ℂ) by norm_num) _
      neg_one_ne_zero', hαdef, Gt, ← PhiT_M, regularRepR_mode]
  rw [LinearMap.sub_apply, hmix, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.coeFn_sum,
    Finset.sum_apply] at h3g
  simp only [LinearMap.smul_apply, smul_eq_mul, hR, hL] at h3g
  have e1 : (-zT) = (-1 : ℂ) := by norm_num
  have e2 : zT = (1 : ℂ) := by norm_num
  simp only [e1, e2, one_zpow, mul_one] at h3g
  exact h3g

end Final

end VOA.Huang.LiRegular
