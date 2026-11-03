import VOA.Huang.LiConverseUniv
import VOA.Huang.LiConverseFrame
import VOA.Huang.LiRegularOmega
import VOA.Huang.HuangODEContra

/-! # The source frame: extending the top datum over `P₃'` inside `D_{P(−1)}(M)`

Fix a Frenkel–Zhu top datum `T ∈ fzSpace A P₂ P₃` and a bottom vector `y₀` of `P₂`.  For a
bottom vector `u` of the contragredient `P₃'`, the functional `λ_{y₀,u}(w) = ⟨T(w)y₀, u⟩` on `M`
vanishes on `O(M)`, so (`LiRegularOmega`) it lies in Li's regular representation `D_{P(−1)}(M)`,
is a lowest-weight vector for `Y^R`, and `Y^R`'s zero mode is the contragredient action of `A(V)`.
The universal property of the irreducible `P₃'` (`LiConverseUniv`) extends `u ↦ λ_{y₀,u}` to a
`Y^R`-module map `Ψ_{y₀} : P₃' → D_{P(−1)}(M)`.

* `Psi_equiv`, `Psi_bot`, `Psi_add`, `Psi_smul` — the extension and its linearity in `y₀`;
* `Psi_yL_lower`, `Psi_yL_zero` — `Y^L` acts on `Ψ_{y₀}(g)` through the zero mode on `y₀`;
* `source_restricted` — the restricted three-point identities, the input of `frame_change`.

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.VertexOperatorAlgebra VOA.Huang.LiFusion VOA.Huang.HuangODEContra VOA.FZ
  FusionTop LaurentPolynomial VHat VHat.DLM3
open scoped BigOperators Polynomial

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

/-! ## The contragredient modes as transposed opposite modes -/

theorem dualPairing_contra_mode {E : Type u} [AddCommGroup E] [Module ℂ E] (N : OrdVModule W E)
    (a : V) (k : ℤ) (x : E) (f : RestrictedDual N) :
    dualPairing N x (mode ((contragredientModule N).YM a) k f)
      = dualPairing N (oppB N a k x) f := by
  have hx : x ∈ ⨆ α : ℂ, N.weight α := by
    rw [N.isInternal.submodule_iSup_eq_top]; exact Submodule.mem_top
  induction hx using Submodule.iSup_induction' with
  | mem α x hx =>
    refine reduce_homogeneous W (P := fun a => dualPairing N x
      (mode ((contragredientModule N).YM a) k f) = dualPairing N (oppB N a k x) f) ?_ ?_ ?_ a
    · intro wt a ha
      change dualPairing N x (mode (YMdual N a) k f) = _
      rw [dualPairing_mode_dualAdj N ha k f hx, oppB_eq_dualAdj N ha k hx]
    · simp only [map_zero, mode_zero, LinearMap.zero_apply, Pi.zero_apply]
      rw [dualPairing_zero_x]
    · intro a b ha hb
      simp only [map_add, mode_add, LinearMap.add_apply, Pi.add_apply]
      rw [ha, hb, dualPairing_add_x]
  | zero => rw [map_zero, dualPairing_zero_x, dualPairing_zero_x]
  | add x y _ _ hx hy => rw [map_add, dualPairing_add_x, dualPairing_add_x, hx, hy]

theorem sumR_one_nat {G : Type*} [AddCommGroup G] [Module ℂ G] (r : ℤ → G) (k : ℕ) (m : ℤ) :
    sumR 1 r k m = ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℕ) : ℂ) • r (m + i) := by
  rw [sumR]
  refine (finsum_eq_sum_of_support_subset _ fun i hi => ?_).trans
    (Finset.sum_congr rfl fun i hi => ?_)
  · rw [Function.mem_support] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    exact hi (by rw [cbz_lt (p := (k : ℤ)) (c := (i : ℤ)) (by positivity) (by omega), zero_mul,
      zero_smul])
  · rw [Finset.mem_range] at hi
    rw [cbz_natCast_eq_choose (by omega), one_zpow, mul_one]

theorem toL_lz_pow_T (k : ℕ) (m : ℤ) :
    Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * LaurentPolynomial.T m
      = ∑ i ∈ Finset.range (k + 1), (((k.choose i : ℕ) : ℂ)) • (LaurentPolynomial.T (m + i) : ℂ[T;T⁻¹]) := by
  rw [add_pow, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [one_pow, mul_one, map_mul, map_pow, Polynomial.toLaurent_X, map_natCast, T_pow, mul_one,
    mul_comm, ← mul_assoc, ← T_add, mul_comm, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

section Source

variable (A : OrdVModule W M) {P₂ P₃ : LWModule W} (T : fzSpace A P₂ P₃)

/-- The contragredient of `P₃`, the input slot of `Y^R`. -/
noncomputable abbrev Q₃ (P₃ : LWModule W) : LWModule W := contraLW P₃

/-- `Y^R` on `D_{P(−1)}(M)`. -/
noncomputable abbrev Rs : WeakModule W ((oppBase A).Dsub (-1)) := regularRepR A neg_one_ne_zero'

/-- `Y^L` on `D_{P(−1)}(M)`. -/
noncomputable abbrev Ls : WeakModule W ((oppBase A).Dsub (-1)) := regularRepL A neg_one_ne_zero'

/-- The top functional `λ_{y₀,u}(w) = ⟨T(w)y₀, u⟩`. -/
noncomputable def lamTop (y₀ : bot P₂) (u : (pBotAmMod (Q₃ P₃)).carrier) : Module.Dual ℂ M where
  toFun w := dualPairing P₃.isMod (T.val w y₀ : P₃.carrier) (pBotIncl (Q₃ P₃) u)
  map_add' w w' := by simp only [map_add, LinearMap.add_apply, Submodule.coe_add,
    dualPairing_add_x]
  map_smul' c w := by simp only [map_smul, LinearMap.smul_apply, Submodule.coe_smul,
    dualPairing_smul_x, RingHom.id_apply, smul_eq_mul]

theorem lamTop_perp (y₀ : bot P₂) (u : (pBotAmMod (Q₃ P₃)).carrier) :
    ∀ x ∈ fzO A.toWeakModule, lamTop A T y₀ u x = 0 := by
  intro x hx
  change dualPairing P₃.isMod (T.val x y₀ : P₃.carrier) _ = 0
  rw [T.2.1 x hx]
  simp [dualPairing_zero_x]

/-- The bottom map `u ↦ λ_{y₀,u}` into `D_{P(−1)}(M)`. -/
noncomputable def phiTop (y₀ : bot P₂) : (pBotAmMod (Q₃ P₃)).carrier →ₗ[ℂ] (oppBase A).Dsub (-1) where
  toFun u := ⟨lamTop A T y₀ u, inD_of_perp (N := A) (lamTop_perp A T y₀ u)⟩
  map_add' u u' := by
    apply Subtype.ext
    ext w
    change dualPairing _ _ (pBotIncl _ (u + u')) = dualPairing _ _ (pBotIncl _ u)
      + dualPairing _ _ (pBotIncl _ u')
    rw [map_add]; exact LinearMap.map_add _ _ _
  map_smul' c u := by
    apply Subtype.ext
    ext w
    change dualPairing _ _ (pBotIncl _ (c • u)) = c • dualPairing _ _ (pBotIncl _ u)
    rw [map_smul]; exact LinearMap.map_smul _ _ _

/-- The pairing as a linear functional of the vector. -/
noncomputable def dpx {E : Type u} [AddCommGroup E] [Module ℂ E] (N : OrdVModule W E)
    (f : RestrictedDual N) : E →ₗ[ℂ] ℂ where
  toFun x := dualPairing N x f
  map_add' x y := dualPairing_add_x N x y f
  map_smul' c x := dualPairing_smul_x N c x f

theorem lamTop_apply (y₀ : bot P₂) (u : (pBotAmMod (Q₃ P₃)).carrier) (w : M) :
    lamTop A T y₀ u w = dualPairing P₃.isMod (T.val w y₀ : P₃.carrier) (pBotIncl (Q₃ P₃) u) := rfl

theorem phiTop_coe (y₀ : bot P₂) (u : (pBotAmMod (Q₃ P₃)).carrier) :
    ((phiTop A T y₀ u : (oppBase A).Dsub (-1)) : Module.Dual ℂ M) = lamTop A T y₀ u := rfl

/-- The zero mode of `Y^R` on the top functionals is the contragredient `A(V)`-action. -/
theorem phiTop_act (y₀ : bot P₂) (a : V) (u : (pBotAmMod (Q₃ P₃)).carrier) :
    phiTop A T y₀ ((pBotAmMod (Q₃ P₃)).ρ (mkAnFull W 0 a) u)
      = oLevW (Rs A) (0 : ℤ) a (phiTop A T y₀ u) := by
  refine reduce_homogeneous W (P := fun a => phiTop A T y₀ ((pBotAmMod (Q₃ P₃)).ρ
    (mkAnFull W 0 a) u) = oLevW (Rs A) (0 : ℤ) a (phiTop A T y₀ u)) ?_ ?_ ?_ a
  · intro k a ha
    rcases lt_or_ge k 0 with hk | hk
    · have : a = 0 := by
        have h := VOA.VertexOperatorAlgebra.L_one_pow_eq_zero W ha (j := 0) (by omega)
        simpa using h
      subst this
      simp only [map_zero, LinearMap.zero_apply]
    obtain ⟨w₀, rfl⟩ : ∃ w₀ : ℕ, k = w₀ := ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩
    apply Subtype.ext
    ext w
    rw [phiTop_coe, lamTop_apply, pBotIncl_act, oLevW_homogeneous _ 0 ha]
    change dualPairing _ _ (mode ((contragredientModule P₃.isMod).YM a) _ _) = _
    rw [dualPairing_contra_mode, oLevW_homogeneous _ 0 ha]
    change _ = (((mode ((regularRepR A neg_one_ne_zero').YM a) ((w₀ : ℤ) - 1 + 0)
      (phiTop A T y₀ u)) : (oppBase A).Dsub (-1)) : Module.Dual ℂ M) w
    rw [regularRepR_mode, phiTop_coe, add_zero,
      yR_zero_of_perp (N := A) (lamTop_perp A T y₀ u) ha w, oppB_homog P₃.isMod ha, Int.toNat_natCast]
    change dpx P₃.isMod _ (((-1 : ℂ) ^ (w₀ : ℤ) • ∑ j ∈ Finset.range (w₀ + 1),
      ((j.factorial : ℂ)⁻¹) • mode (P₃.isMod.YM ((W.L 1 ^ j) a))
        (2 * (w₀ : ℤ) - ((w₀ : ℤ) - 1) - 2 - (j : ℤ))) (T.val w y₀ : P₃.carrier)) = _
    simp only [LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply, map_smul, map_sum,
      smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have hmem : (W.L 1 ^ j) a ∈ W.grading ((w₀ - j : ℕ) : ℤ) := by
      have := L_one_pow_mem W ha j
      rwa [show ((w₀ : ℤ) - (j : ℤ)) = ((w₀ - j : ℕ) : ℤ) by omega] at this
    rw [lamTop_apply, T.2.2.1 (w₀ - j) _ hmem w y₀,
      show 2 * (w₀ : ℤ) - ((w₀ : ℤ) - 1) - 2 - (j : ℤ) = ((w₀ - j : ℕ) : ℤ) - 1 by
        push_cast [Nat.cast_sub (show j ≤ w₀ by omega)]; ring]
    rfl
  · simp only [map_zero, LinearMap.zero_apply]
  · intro a b ha hb
    simp only [map_add, LinearMap.add_apply] at ha hb ⊢
    rw [ha, hb]

/-- The top functionals are lowest-weight vectors for `Y^R`. -/
theorem phiTop_lowest (y₀ : bot P₂) :
    LowestSet (Rs A) (Set.range (phiTop A T y₀)) := by
  rintro _ ⟨u, rfl⟩ k a ha n hn
  rcases lt_or_ge k 0 with hk | hk
  · have : a = 0 := by
      have h := VOA.VertexOperatorAlgebra.L_one_pow_eq_zero W ha (j := 0) (by omega)
      simpa using h
    subst this
    simp
  obtain ⟨w₀, rfl⟩ : ∃ w₀ : ℕ, k = w₀ := ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩
  apply Subtype.ext
  change ((mode ((regularRepR A neg_one_ne_zero').YM a) n (phiTop A T y₀ u) :
    (oppBase A).Dsub (-1)) : Module.Dual ℂ M) = 0
  rw [regularRepR_mode, phiTop_coe, yR_lower_of_perp (N := A) (lamTop_perp A T y₀ u) ha hn]

variable {T} in
/-- The existence of the extension `Ψ_{y₀}`. -/
theorem exists_Psi (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
    (hrat : AdmissiblyRational W) (hP₃ : P₃.IsIrreducibleLW) (y₀ : bot P₂) :
    ∃ Φ : (Q₃ P₃).carrier →ₗ[ℂ] (oppBase A).Dsub (-1),
      (∀ (a : V) (p : ℤ) (y : (Q₃ P₃).carrier),
        Φ (mode ((Q₃ P₃).isMod.YM a) p y) = mode ((Rs A).YM a) p (Φ y)) ∧
      ∀ u, Φ (pBotIncl (Q₃ P₃) u) = phiTop A T y₀ u :=
  exists_hom_of_bottom Pr hrat (Q₃ P₃) (contraLW_isIrreducibleLW hP₃) (Rs A)
    (genAdmLev (Rs A) _ (phiTop_lowest A T y₀)) (phiTop A T y₀)
    (fun u => mem_genAdmLev_zero (Rs A) _ (phiTop_lowest A T y₀) ⟨u, rfl⟩)
    (fun a u => phiTop_act A T y₀ a u)

theorem phiTop_add (y y' : bot P₂) : phiTop A T (y + y') = phiTop A T y + phiTop A T y' := by
  ext u w
  change dualPairing _ ((T.val w (y + y') : P₃.carrier)) _
    = dualPairing _ (T.val w y : P₃.carrier) _ + dualPairing _ (T.val w y' : P₃.carrier) _
  rw [map_add, Submodule.coe_add, dualPairing_add_x]

theorem phiTop_smul (c : ℂ) (y : bot P₂) : phiTop A T (c • y) = c • phiTop A T y := by
  ext u w
  change dualPairing _ ((T.val w (c • y) : P₃.carrier)) _ = c * dualPairing _ (T.val w y : P₃.carrier) _
  rw [map_smul, Submodule.coe_smul, dualPairing_smul_x]

/-- `Y^L` and `Y^R` commute on `D_{P(−1)}(M)`, as weak-module modes. -/
theorem LR_comm (a b : V) (m n : ℤ) (x : (oppBase A).Dsub (-1)) :
    mode ((Ls A).YM a) m (mode ((Rs A).YM b) n x) = mode ((Rs A).YM b) n (mode ((Ls A).YM a) m x) := by
  apply Subtype.ext
  rw [regularRepL_mode, regularRepR_mode, regularRepR_mode, regularRepL_mode]
  exact yL_yR_comm A (-1) neg_one_ne_zero' x.2 a b m n

/-- Uniqueness of `Y^R`-module maps out of `P₃'`. -/
theorem homExt_Q (hP₃ : P₃.IsIrreducibleLW) (Φ Φ' : (Q₃ P₃).carrier →ₗ[ℂ] (oppBase A).Dsub (-1))
    (hΦ : ∀ (a : V) (p : ℤ) (g : (Q₃ P₃).carrier),
      Φ (mode ((Q₃ P₃).isMod.YM a) p g) = mode ((Rs A).YM a) p (Φ g))
    (hΦ' : ∀ (a : V) (p : ℤ) (g : (Q₃ P₃).carrier),
      Φ' (mode ((Q₃ P₃).isMod.YM a) p g) = mode ((Rs A).YM a) p (Φ' g))
    (hb : ∀ u, Φ (pBotIncl (Q₃ P₃) u) = Φ' (pBotIncl (Q₃ P₃) u)) : Φ = Φ' :=
  hom_ext_of_bottom (Q₃ P₃) (contraLW_isIrreducibleLW hP₃) (Rs A) Φ Φ' hΦ hΦ' hb

section Psi

variable (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
  (hrat : AdmissiblyRational W) (hP₃ : P₃.IsIrreducibleLW)

/-- **The extension `Ψ_{y₀} : P₃' → D_{P(−1)}(M)`** of the top datum. -/
noncomputable def Psi (y₀ : bot P₂) : (Q₃ P₃).carrier →ₗ[ℂ] (oppBase A).Dsub (-1) :=
  (exists_Psi A (T := T) Pr hrat hP₃ y₀).choose

theorem Psi_equiv (y₀ : bot P₂) (a : V) (p : ℤ) (g : (Q₃ P₃).carrier) :
    Psi A T Pr hrat hP₃ y₀ (mode ((Q₃ P₃).isMod.YM a) p g)
      = mode ((Rs A).YM a) p (Psi A T Pr hrat hP₃ y₀ g) :=
  (exists_Psi A (T := T) Pr hrat hP₃ y₀).choose_spec.1 a p g

theorem Psi_bot (y₀ : bot P₂) (u : (pBotAmMod (Q₃ P₃)).carrier) :
    Psi A T Pr hrat hP₃ y₀ (pBotIncl (Q₃ P₃) u) = phiTop A T y₀ u :=
  (exists_Psi A (T := T) Pr hrat hP₃ y₀).choose_spec.2 u

theorem Psi_add (y y' : bot P₂) :
    Psi A T Pr hrat hP₃ (y + y') = Psi A T Pr hrat hP₃ y + Psi A T Pr hrat hP₃ y' := by
  refine homExt_Q A hP₃ _ _ (Psi_equiv A T Pr hrat hP₃ _) (fun a p g => ?_) (fun u => ?_)
  · simp only [LinearMap.add_apply, Psi_equiv, map_add]
  · simp only [LinearMap.add_apply, Psi_bot, phiTop_add]

theorem Psi_smul (c : ℂ) (y : bot P₂) :
    Psi A T Pr hrat hP₃ (c • y) = c • Psi A T Pr hrat hP₃ y := by
  refine homExt_Q A hP₃ _ _ (Psi_equiv A T Pr hrat hP₃ _) (fun a p g => ?_) (fun u => ?_)
  · simp only [LinearMap.smul_apply, Psi_equiv, map_smul]
  · simp only [LinearMap.smul_apply, Psi_bot, phiTop_smul]

/-- `Y^L` lowering modes kill `Ψ_{y₀}(g)`. -/
theorem Psi_yL_lower (y₀ : bot P₂) {w₀ : ℕ} {b : V} (hb : b ∈ W.grading (w₀ : ℤ)) {n : ℤ}
    (hn : (w₀ : ℤ) ≤ n) (g : (Q₃ P₃).carrier) :
    mode ((Ls A).YM b) n (Psi A T Pr hrat hP₃ y₀ g) = 0 := by
  have h := homExt_Q A hP₃ ((mode ((Ls A).YM b) n).comp (Psi A T Pr hrat hP₃ y₀)) 0
    (fun a p g => by
      simp only [LinearMap.comp_apply, Psi_equiv]
      exact LR_comm A b a n p _)
    (fun a p g => by simp)
    (fun u => by
      simp only [LinearMap.comp_apply, Psi_bot, LinearMap.zero_apply]
      apply Subtype.ext
      rw [regularRepL_mode, phiTop_coe]
      exact yL_lower_of_perp (N := A) (lamTop_perp A T y₀ u) hb hn)
  exact LinearMap.congr_fun h g

/-- The zero mode of a weight-`w₀` state on a bottom vector of `P₂`. -/
noncomputable def zm {w₀ : ℕ} {b : V} (hb : b ∈ W.grading (w₀ : ℤ)) (y₀ : bot P₂) : bot P₂ :=
  ⟨mode (P₂.isMod.YM b) ((w₀ : ℤ) - 1) y₀, by
    have := mode_mem_weight P₂.isMod hb y₀.2 ((w₀ : ℤ) - 1)
    convert this using 2; push_cast; ring⟩

/-- The zero mode of `Y^L` on `Ψ_{y₀}(g)` is `Ψ_{o(b)y₀}(g)`. -/
theorem Psi_yL_zero (y₀ : bot P₂) {w₀ : ℕ} (hw₀ : 1 ≤ w₀) {b : V} (hb : b ∈ W.grading (w₀ : ℤ))
    (g : (Q₃ P₃).carrier) :
    mode ((Ls A).YM b) ((w₀ : ℤ) - 1) (Psi A T Pr hrat hP₃ y₀ g)
      = Psi A T Pr hrat hP₃ (zm hb y₀) g := by
  have h := homExt_Q A hP₃ ((mode ((Ls A).YM b) ((w₀ : ℤ) - 1)).comp (Psi A T Pr hrat hP₃ y₀))
    (Psi A T Pr hrat hP₃ (zm hb y₀))
    (fun a p g => by
      simp only [LinearMap.comp_apply, Psi_equiv]
      exact LR_comm A b a _ p _)
    (Psi_equiv A T Pr hrat hP₃ _)
    (fun u => by
      simp only [LinearMap.comp_apply, Psi_bot]
      apply Subtype.ext
      rw [regularRepL_mode, phiTop_coe, phiTop_coe]
      ext w
      rw [yL_zero_of_perp (N := A) (lamTop_perp A T y₀ u) hw₀ hb w, lamTop_apply, lamTop_apply,
        T.2.2.2 w₀ hw₀ b hb w y₀ (zm hb y₀) rfl])
  exact LinearMap.congr_fun h g

/-- The bilinear form `H_{y₀}(g, w) = Ψ_{y₀}(g)(w)`. -/
noncomputable def Hs (y₀ : bot P₂) : (Q₃ P₃).carrier →ₗ[ℂ] M →ₗ[ℂ] ℂ :=
  ((oppBase A).Dsub (-1)).subtype.comp (Psi A T Pr hrat hP₃ y₀)

/-- The `A(V)`-action on the bottom of `P₂`. -/
noncomputable def zmA (a : V) (y₀ : bot P₂) : bot P₂ := (pBotAmMod P₂).ρ (mkAnFull W 0 a) y₀

theorem zmA_eq {k : ℕ} {a : V} (ha : a ∈ W.grading ((k : ℤ) + 1)) (y₀ : bot P₂) :
    zmA a y₀ = zm (w₀ := k + 1) (by push_cast; exact ha) y₀ := by
  apply Subtype.ext
  have h := pBotIncl_act P₂ a y₀
  rw [oLevW_homogeneous _ 0 ha] at h
  change pBotIncl P₂ (zmA a y₀) = _ at h
  rw [show ((zmA a y₀ : bot P₂) : P₂.carrier) = pBotIncl P₂ (zmA a y₀) from rfl, h]
  change _ = mode (P₂.isMod.YM a) (((k + 1 : ℕ) : ℤ) - 1) y₀
  rw [show (k : ℤ) + 1 - 1 + 0 = ((k + 1 : ℕ) : ℤ) - 1 by push_cast; ring]
  rfl

/-- The zero-mode term `Z(a, g, w) = Ψ_{o(a)y₀}(g)(w)`. -/
noncomputable def Zs (y₀ : bot P₂) (a : V) (g : (Q₃ P₃).carrier) (w : M) : ℂ :=
  Hs A T Pr hrat hP₃ (zmA a y₀) g w

theorem lz_neg_one : lz (-1 : ℂ) = Polynomial.X + 1 := by simp [lz]

/-- **The restricted source identities** (the input of `frame_change`). -/
theorem source_restricted (y₀ : bot P₂) :
    ∀ (k : ℕ) (a : V), a ∈ W.grading ((k : ℤ) + 1) → ∀ (ρ : ℂ[T;T⁻¹]) (g : (Q₃ P₃).carrier)
      (w : M), sdiff A (Q₃ P₃).isMod (Hs A T Pr hrat hP₃ y₀) a
        (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * ρ) g w
        = ev1 ρ * Zs A T Pr hrat hP₃ y₀ a g w := by
  intro k a ha ρ g w
  have hb : a ∈ W.grading (((k + 1 : ℕ) : ℤ)) := by push_cast; exact ha
  induction ρ using LaurentPolynomial.induction_on' with
  | add f f' hf hf' => rw [mul_add, sdiff_add, hf, hf', map_add, add_mul]
  | C_mul_T m c =>
    have key : sdiff A (Q₃ P₃).isMod (Hs A T Pr hrat hP₃ y₀) a
        (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * LaurentPolynomial.T m) g w
        = (-1 : ℂ) ^ m * Zs A T Pr hrat hP₃ y₀ a g w := by
      have h3 := LinearMap.congr_fun ((oppBase A).threeWay_gen (oppShift A) neg_one_ne_zero'
        (Psi A T Pr hrat hP₃ y₀ g).2 a k m) w
      rw [OppBase.mixOp_nonneg, lz_neg_one, neg_neg, sumR_one_nat] at h3
      have hR : ∀ n : ℤ, (oppBase A).rModes neg_one_ne_zero' a (Psi A T Pr hrat hP₃ y₀ g : Module.Dual ℂ M) n
          = ((Psi A T Pr hrat hP₃ y₀ (mode ((Q₃ P₃).isMod.YM a) n g) : (oppBase A).Dsub (-1))
            : Module.Dual ℂ M) := by
        intro n
        rw [Psi_equiv, regularRepR_mode]; rfl
      have hL : ∀ n : ℤ, (oppBase A).lModes (oppShift A) neg_one_ne_zero' a (Psi A T Pr hrat hP₃ y₀ g : Module.Dual ℂ M) n
          = ((mode ((Ls A).YM a) n (Psi A T Pr hrat hP₃ y₀ g) : (oppBase A).Dsub (-1))
            : Module.Dual ℂ M) := by
        intro n
        rw [regularRepL_mode]; rfl
      have hsum : sumR (-1) ((oppBase A).lModes (oppShift A) neg_one_ne_zero' a (Psi A T Pr hrat hP₃ y₀ g : Module.Dual ℂ M)) m k
          = (-1 : ℂ) ^ m • ((Psi A T Pr hrat hP₃ (zmA a y₀) g : (oppBase A).Dsub (-1))
            : Module.Dual ℂ M) := by
        rw [sumR, finsum_eq_single _ 0 (fun i hi => by
          rw [hL, Psi_yL_lower A T Pr hrat hP₃ y₀ hb (by push_cast; omega), ZeroMemClass.coe_zero,
            smul_zero])]
        rw [hL, Nat.cast_zero, add_zero, sub_zero, cbz_zero, one_mul, zmA_eq ha]
        congr 2
        have := Psi_yL_zero A T Pr hrat hP₃ y₀ (w₀ := k + 1) (by omega) hb g
        rw [show (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) by push_cast; ring] at this
        exact this
      rw [hsum] at h3
      simp only [hR, LinearMap.sub_apply, LinearMap.coeFn_sum, Finset.sum_apply,
        LinearMap.smul_apply, LinearMap.dualMap_apply] at h3
      have hn : nres (Q₃ P₃).isMod.toWeakModule a
          (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * LaurentPolynomial.T m)
          = ∑ i ∈ Finset.range (k + 1), ((k.choose i : ℕ) : ℂ) •
              mode ((Q₃ P₃).isMod.YM a) (m + i) := by
        rw [toL_lz_pow_T, nres_sum]
        simp only [nres_smul, nres_T]
      rw [sdiff, hn, Zs]
      simp only [LinearMap.smul_apply, LinearMap.coeFn_sum, Finset.sum_apply, map_sum, map_smul,
        LinearMap.sum_apply, smul_eq_mul] at h3 ⊢
      exact h3
    rw [show Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k)
          * (LaurentPolynomial.C c * LaurentPolynomial.T m)
        = c • (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * LaurentPolynomial.T m) by
          rw [smul_eq_C_mul]; ring,
      sdiff_smul, key, map_mul, ev1_C, ev1_T]
    ring

end Psi

end Source

end VOA.Huang.LiRegular
