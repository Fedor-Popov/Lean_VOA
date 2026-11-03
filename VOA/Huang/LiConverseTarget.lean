import VOA.Huang.LiConverseSource

/-! # The target frame: `D_{P(−1)}(P₃')` and the extension over `P₂`

The frame change (`frame_change`) turns the source identities (`source_restricted`) into
restricted identities in the frame where `P₃'` is the regular slot.  For `w ∈ M` and a bottom
vector `y₀` of `P₂`, the functional `λ_{w,y₀}(g) = Ψ_{y₀}(g)(w)` on `P₃'` then:

* lies in Li's `D_{P(−1)}(P₃')` (`lamT_inD`);
* carries the `M`-action as `Y^R` (`lamT_yR`: `Y^R(b)ₙ λ_{w,y₀} = λ_{bₙw, y₀}`);
* is a lowest-weight vector for `Y^L` with zero mode the `A(V)`-action on `y₀`
  (`lamT_yL_lower`, `lamT_yL_zero`).

No `sorry`, no axioms beyond Lean's.
-/

namespace VOA.Huang.LiRegular

open VOA VOA.VertexOperatorAlgebra VOA.Huang.LiFusion VOA.Huang.HuangODEContra VOA.FZ
  FusionTop LaurentPolynomial VHat VHat.DLM3
open scoped BigOperators Polynomial

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}
  {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- A residue against a test function supported in degrees `≥ N` vanishes on a vector killed by
all modes of index `≥ N`. -/
theorem nres_T_mul_poly_eq_zero (A : WeakModule W M) (b : V) (w : M) {N : ℤ}
    (hN : ∀ n : ℤ, N ≤ n → mode (A.YM b) n w = 0) (p : ℂ[X]) :
    nres A b (LaurentPolynomial.T N * Polynomial.toLaurent p) w = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, mul_add, nres_add, LinearMap.add_apply, hp, hq, add_zero]
  | monomial j c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, Polynomial.toLaurent_C, toLaurent_X_pow',
      mul_left_comm, ← T_add, nres_CT, LinearMap.smul_apply, hN _ (by omega), smul_zero]

theorem ev1_toL (p : ℂ[X]) : ev1 (Polynomial.toLaurent p) = p.eval (-1) := by
  rw [ev1, eval₂_toLaurent, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]; rfl

section Target

variable (A : OrdVModule W M) {P₂ P₃ : LWModule W} (T : fzSpace A P₂ P₃)
  (Pr : BottomProjection (parabolicRepOfAMod W (regularAMod W)))
  (hrat : AdmissiblyRational W) (hP₃ : P₃.IsIrreducibleLW)

/-- The regular slot of the target frame. -/
noncomputable abbrev Qm (P₃ : LWModule W) : OrdVModule W (Q₃ P₃).carrier := (Q₃ P₃).isMod

/-- **The restricted target identities** (from `frame_change`). -/
theorem target_zero_mode (y₀ : bot P₂) {k : ℕ} {b : V} (hb : b ∈ W.grading ((k : ℤ) + 1))
    (σ : ℂ[T;T⁻¹]) (g : (Q₃ P₃).carrier) (w : M) :
    tdiff A (Qm P₃) (Hs A T Pr hrat hP₃ y₀) b
        (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * σ) g w
      = ev1 σ * Zs A T Pr hrat hP₃ y₀ b g w :=
  frame_change A (Qm P₃) (Hs A T Pr hrat hP₃ y₀) (Zs A T Pr hrat hP₃ y₀)
    (source_restricted A T Pr hrat hP₃ y₀) k b hb σ g w

theorem target_strict (y₀ : bot P₂) {k : ℕ} {b : V} (hb : b ∈ W.grading (k : ℤ))
    (σ : ℂ[T;T⁻¹]) (g : (Q₃ P₃).carrier) (w : M) :
    tdiff A (Qm P₃) (Hs A T Pr hrat hP₃ y₀) b
        (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * σ) g w = 0 := by
  rcases k with _ | k
  · exact tdiff_low A (Qm P₃) _ (le_refl _) hb _ g w
  · rw [pow_succ, map_mul, mul_assoc]
    rw [target_zero_mode A T Pr hrat hP₃ y₀ (by push_cast at hb; exact hb), map_mul,
      ev1_X_add_one, zero_mul, zero_mul]

/-- The functional `λ_{w,y₀}(g) = Ψ_{y₀}(g)(w)` on `P₃'`. -/
noncomputable def lamT (w : M) (y₀ : bot P₂) : Module.Dual ℂ (Q₃ P₃).carrier :=
  (Hs A T Pr hrat hP₃ y₀).flip w

theorem lamT_apply (w : M) (y₀ : bot P₂) (g : (Q₃ P₃).carrier) :
    lamT A T Pr hrat hP₃ w y₀ g = Hs A T Pr hrat hP₃ y₀ g w := rfl

/-- The basic transfer: `λ(Res ψ Y°(b)·) = Ψ(Res ψ Y(b) w)` for strictly restricted `ψ`. -/
theorem lamT_ys_strict (w : M) (y₀ : bot P₂) {k : ℕ} {b : V} (hb : b ∈ W.grading (k : ℤ))
    (σ : ℂ[T;T⁻¹]) :
    (oppBase (Qm P₃)).ys b (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * σ)
        (lamT A T Pr hrat hP₃ w y₀)
      = lamT A T Pr hrat hP₃ (nres A.toWeakModule b
          (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k) * σ) w) y₀ := by
  ext g
  have h := target_strict A T Pr hrat hP₃ y₀ hb σ g w
  rw [tdiff, sub_eq_zero] at h
  rw [OppBase.ys_apply, lamT_apply, lamT_apply]
  exact h

/-- Witnesses for homogeneous states. -/
theorem lamT_wit (w : M) (y₀ : bot P₂) {k : ℕ} {b : V} (hb : b ∈ W.grading (k : ℤ)) :
    ∃ N : ℤ, ∀ N' : ℤ, N ≤ N' → (oppBase (Qm P₃)).Wit (-1) b (lamT A T Pr hrat hP₃ w y₀) k N' := by
  obtain ⟨N, hN⟩ := A.toWeakModule.truncation b w
  refine ⟨N, fun N' hN' q => ?_⟩
  rw [show (LaurentPolynomial.T N' : ℂ[T;T⁻¹]) * Polynomial.toLaurent (lz (-1) ^ k * q)
      = Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k)
        * (LaurentPolynomial.T N' * Polynomial.toLaurent q) by
      rw [lz_neg_one, map_mul]; ring,
    lamT_ys_strict A T Pr hrat hP₃ w y₀ hb]
  rw [show Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k)
        * (LaurentPolynomial.T N' * Polynomial.toLaurent q)
      = LaurentPolynomial.T N' * Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k * q) by
      rw [map_mul]; ring,
    nres_T_mul_poly_eq_zero A.toWeakModule b w (fun n hn => hN n (by omega))]
  ext g
  simp [lamT_apply]

/-- `λ_{w,y₀} ∈ D_{P(−1)}(P₃')`. -/
theorem lamT_inD (w : M) (y₀ : bot P₂) :
    (oppBase (Qm P₃)).InD (-1) (lamT A T Pr hrat hP₃ w y₀) := by
  intro b
  refine reduce_homogeneous W (P := fun b => ∃ (k : ℕ) (N : ℤ),
    (oppBase (Qm P₃)).Wit (-1) b (lamT A T Pr hrat hP₃ w y₀) k N) ?_ ?_ ?_ b
  · intro k b hb
    rcases lt_or_ge k 0 with hk | hk
    · have : b = 0 := by
        have h := VOA.VertexOperatorAlgebra.L_one_pow_eq_zero W hb (j := 0) (by omega)
        simpa using h
      subst this
      exact ⟨0, 0, fun q => by rw [OppBase.ys_zero_a]⟩
    obtain ⟨k, rfl⟩ : ∃ k' : ℕ, k = k' := ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩
    obtain ⟨N, hN⟩ := lamT_wit A T Pr hrat hP₃ w y₀ hb
    exact ⟨k, N, hN N le_rfl⟩
  · exact ⟨0, 0, fun q => by rw [OppBase.ys_zero_a]⟩
  · rintro b b' ⟨k, N, h⟩ ⟨k', N', h'⟩
    exact ⟨max k k', max N N', OppBase.Wit.add_a (h.mono (le_max_left _ _) (le_max_left _ _))
      (h'.mono (le_max_right _ _) (le_max_right _ _))⟩

theorem lamT_add_w (w w' : M) (y₀ : bot P₂) :
    lamT A T Pr hrat hP₃ (w + w') y₀ = lamT A T Pr hrat hP₃ w y₀ + lamT A T Pr hrat hP₃ w' y₀ := by
  ext g; simp [lamT_apply]

theorem lamT_smul_w (c : ℂ) (w : M) (y₀ : bot P₂) :
    lamT A T Pr hrat hP₃ (c • w) y₀ = c • lamT A T Pr hrat hP₃ w y₀ := by
  ext g; simp [lamT_apply]

theorem lamT_zero_w (y₀ : bot P₂) : lamT A T Pr hrat hP₃ 0 y₀ = 0 := by
  ext g; simp [lamT_apply]

/-- **`Y^R` on `λ_{w,y₀}` is the `M`-action**: `Y^R(b)ₙ λ_{w,y₀} = λ_{bₙ w, y₀}`. -/
theorem lamT_yR (w : M) (y₀ : bot P₂) (b : V) (n : ℤ) :
    (oppBase (Qm P₃)).yR (-1) neg_one_ne_zero' b n (lamT A T Pr hrat hP₃ w y₀)
      = lamT A T Pr hrat hP₃ (mode (A.YM b) n w) y₀ := by
  have hD := lamT_inD A T Pr hrat hP₃ w y₀
  refine reduce_homogeneous W (P := fun b => (oppBase (Qm P₃)).yR (-1) neg_one_ne_zero' b n
    (lamT A T Pr hrat hP₃ w y₀) = lamT A T Pr hrat hP₃ (mode (A.YM b) n w) y₀) ?_ ?_ ?_ b
  · intro k b hb
    rcases lt_or_ge k 0 with hk | hk
    · have : b = 0 := by
        have h := VOA.VertexOperatorAlgebra.L_one_pow_eq_zero W hb (j := 0) (by omega)
        simpa using h
      subst this
      have h0 := OppBase.yR_smul_a neg_one_ne_zero' hD (0 : ℂ) (0 : V) n
      rw [zero_smul, zero_smul] at h0
      rw [h0]; simp [lamT_zero_w]
    obtain ⟨k, rfl⟩ : ∃ k' : ℕ, k = k' := ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩
    obtain ⟨N, hN⟩ := lamT_wit A T Pr hrat hP₃ w y₀ hb
    obtain ⟨Nt, hNt⟩ := A.toWeakModule.truncation b w
    set N' := max N Nt
    obtain ⟨A', B', hAB⟩ := bezout neg_one_ne_zero' (N' - n).toNat k
    rw [OppBase.yR_eq neg_one_ne_zero' (hN N' (le_max_left _ _)) n (N' - n).toNat (by omega)
      A' B' hAB]
    rw [show (LaurentPolynomial.T n : ℂ[T;T⁻¹]) * Polynomial.toLaurent (B' * lz (-1) ^ k)
        = Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k)
          * (LaurentPolynomial.T n * Polynomial.toLaurent B') by
        rw [lz_neg_one, map_mul]; ring,
      lamT_ys_strict A T Pr hrat hP₃ w y₀ hb]
    congr 1
    have hB : B' * (Polynomial.X + 1 : ℂ[X]) ^ k = 1 - A' * Polynomial.X ^ (N' - n).toNat := by
      rw [← lz_neg_one]; linear_combination hAB
    rw [show Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k)
          * (LaurentPolynomial.T n * Polynomial.toLaurent B')
        = LaurentPolynomial.T n - LaurentPolynomial.T (n + ((N' - n).toNat : ℕ))
          * Polynomial.toLaurent A' by
        calc Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k)
              * (LaurentPolynomial.T n * Polynomial.toLaurent B')
            = LaurentPolynomial.T n * Polynomial.toLaurent (B' * (Polynomial.X + 1 : ℂ[X]) ^ k) := by
              rw [map_mul]; ring
          _ = LaurentPolynomial.T n * Polynomial.toLaurent (1 - A' * Polynomial.X ^ (N' - n).toNat) := by
              rw [hB]
          _ = _ := by
              rw [map_sub, map_one, map_mul, toLaurent_X_pow', T_add]; ring]
    rw [nres_sub, LinearMap.sub_apply, nres_T,
      nres_T_mul_poly_eq_zero A.toWeakModule b w (fun m hm => hNt m (by omega)), sub_zero]
  · have h0 := OppBase.yR_smul_a neg_one_ne_zero' hD (0 : ℂ) (0 : V) n
    rw [zero_smul, zero_smul] at h0
    show _ = _
    rw [h0]; simp [lamT_zero_w]
  · intro b b' hb hb'
    show _ = _
    rw [OppBase.yR_add_a neg_one_ne_zero' hD, hb, hb', map_add, mode_add, LinearMap.add_apply,
      lamT_add_w]

/-- **`Y^L` on `λ_{w,y₀}`**: lowering modes vanish and the zero mode is the `A(V)`-action
on `y₀`. -/
theorem lamT_yL (w : M) (y₀ : bot P₂) {k : ℕ} {b : V} (hb : b ∈ W.grading ((k : ℤ) + 1))
    {n : ℤ} (hn : (k : ℤ) ≤ n) :
    (transBase (Qm P₃) (-(-1 : ℂ))).yR (-(-1 : ℂ)) neg_neg_one_ne_zero b n
        (lamT A T Pr hrat hP₃ w y₀)
      = if n = k then lamT A T Pr hrat hP₃ w (zmA b y₀) else 0 := by
  have hD := lamT_inD A T Pr hrat hP₃ w y₀
  have hDT := (inD_iff_trans (Qm P₃) (lamT A T Pr hrat hP₃ w y₀)).1 hD
  obtain ⟨kk, NN, hW⟩ := hDT b
  obtain ⟨Nt, hNt⟩ := A.toWeakModule.truncation b w
  set kk' := max kk Nt.toNat
  set L : ℕ := (NN - n).toNat + 1
  obtain ⟨A', B', hAB⟩ := bezout neg_neg_one_ne_zero L kk'
  obtain ⟨n', rfl⟩ : ∃ n' : ℕ, n = n' := ⟨n.toNat, by omega⟩
  rw [OppBase.yR_eq neg_neg_one_ne_zero (hW.mono (le_max_left _ _) le_rfl) (n' : ℤ) L
    (by omega) A' B' hAB, T_mul_toLaurent_nat, ys_trans_poly]
  have hk : k ≤ n' := by omega
  have hpoly : (Polynomial.X ^ n' * (B' * lz (-(-1 : ℂ)) ^ kk')).comp
        (Polynomial.X + Polynomial.C (-(-1 : ℂ)))
      = (Polynomial.X + 1 : ℂ[X]) ^ k * ((Polynomial.X + 1 : ℂ[X]) ^ (n' - k)
          * B'.comp (Polynomial.X + 1) * Polynomial.X ^ kk') := by
    simp only [lz, neg_neg, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.sub_comp, Polynomial.C_comp, map_one, add_sub_cancel_right, Polynomial.one_comp]
    rw [show n' = k + (n' - k) by omega, pow_add, Nat.add_sub_cancel_left]
    ring
  rw [hpoly, map_mul]
  ext g
  have h := target_zero_mode A T Pr hrat hP₃ y₀ hb (Polynomial.toLaurent
    ((Polynomial.X + 1 : ℂ[X]) ^ (n' - k) * B'.comp (Polynomial.X + 1) * Polynomial.X ^ kk')) g w
  rw [tdiff, ← map_mul] at h
  have hres : nres A.toWeakModule b (Polynomial.toLaurent ((Polynomial.X + 1 : ℂ[X]) ^ k
      * ((Polynomial.X + 1 : ℂ[X]) ^ (n' - k) * B'.comp (Polynomial.X + 1)
        * Polynomial.X ^ kk'))) w = 0 := by
    rw [show (Polynomial.X + 1 : ℂ[X]) ^ k * ((Polynomial.X + 1 : ℂ[X]) ^ (n' - k)
          * B'.comp (Polynomial.X + 1) * Polynomial.X ^ kk')
        = Polynomial.X ^ kk' * ((Polynomial.X + 1 : ℂ[X]) ^ k * ((Polynomial.X + 1 : ℂ[X]) ^ (n' - k)
          * B'.comp (Polynomial.X + 1))) by ring,
      ← T_mul_toLaurent_nat]
    exact nres_T_mul_poly_eq_zero A.toWeakModule b w (fun m hm => hNt m (by omega)) _
  rw [hres, map_zero, sub_zero, ev1_toL] at h
  rw [OppBase.ys_apply, ← map_mul]
  change Hs A T Pr hrat hP₃ y₀ _ w = _
  rw [h]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_comp, add_neg_cancel, neg_add_cancel]
  have hB0 : B'.eval 0 * (-1 : ℂ) ^ kk' = 1 := by
    have := congrArg (Polynomial.eval 0) hAB
    simpa [lz, L] using this
  by_cases hnk : (n' : ℤ) = k
  · have : n' = k := by omega
    subst this
    rw [if_pos rfl, Nat.sub_self, pow_zero, one_mul, hB0, one_mul]
    rfl
  · rw [if_neg hnk, zero_pow (by omega), zero_mul, zero_mul, zero_mul]
    rfl

theorem lamT_add_y (w : M) (y y' : bot P₂) :
    lamT A T Pr hrat hP₃ w (y + y') = lamT A T Pr hrat hP₃ w y + lamT A T Pr hrat hP₃ w y' := by
  ext g
  simp only [lamT_apply, Hs, LinearMap.comp_apply, Psi_add, LinearMap.add_apply,
    Submodule.subtype_apply, Submodule.coe_add]

theorem lamT_smul_y (w : M) (c : ℂ) (y : bot P₂) :
    lamT A T Pr hrat hP₃ w (c • y) = c • lamT A T Pr hrat hP₃ w y := by
  ext g
  simp only [lamT_apply, Hs, LinearMap.comp_apply, Psi_smul, LinearMap.smul_apply,
    Submodule.subtype_apply, Submodule.coe_smul]

/-- `Y^R` on `D_{P(−1)}(P₃')`. -/
noncomputable abbrev Rt (P₃ : LWModule W) : WeakModule W ((oppBase (Qm P₃)).Dsub (-1)) :=
  regularRepR (Qm P₃) neg_one_ne_zero'

/-- `Y^L` on `D_{P(−1)}(P₃')`. -/
noncomputable abbrev Lt (P₃ : LWModule W) : WeakModule W ((oppBase (Qm P₃)).Dsub (-1)) :=
  regularRepL (Qm P₃) neg_one_ne_zero'

theorem LR_comm_t (a b : V) (m n : ℤ) (x : (oppBase (Qm P₃)).Dsub (-1)) :
    mode ((Lt P₃).YM a) m (mode ((Rt P₃).YM b) n x)
      = mode ((Rt P₃).YM b) n (mode ((Lt P₃).YM a) m x) := by
  apply Subtype.ext
  rw [regularRepL_mode, regularRepR_mode, regularRepR_mode, regularRepL_mode]
  exact yL_yR_comm (Qm P₃) (-1) neg_one_ne_zero' x.2 a b m n

/-- The bottom map `u ↦ λ_{w,u}` into `D_{P(−1)}(P₃')`. -/
noncomputable def phiT (w : M) : (pBotAmMod P₂).carrier →ₗ[ℂ] (oppBase (Qm P₃)).Dsub (-1) where
  toFun u := ⟨lamT A T Pr hrat hP₃ w u, lamT_inD A T Pr hrat hP₃ w u⟩
  map_add' u u' := Subtype.ext (lamT_add_y A T Pr hrat hP₃ w u u')
  map_smul' c u := Subtype.ext (lamT_smul_y A T Pr hrat hP₃ w c u)

theorem phiT_coe (w : M) (u : (pBotAmMod P₂).carrier) :
    ((phiT A T Pr hrat hP₃ w u : (oppBase (Qm P₃)).Dsub (-1)) : Module.Dual ℂ (Q₃ P₃).carrier)
      = lamT A T Pr hrat hP₃ w u := rfl

theorem Lt_mode_coe (b : V) (n : ℤ) (x : (oppBase (Qm P₃)).Dsub (-1)) :
    ((mode ((Lt P₃).YM b) n x : (oppBase (Qm P₃)).Dsub (-1)) : Module.Dual ℂ (Q₃ P₃).carrier)
      = (transBase (Qm P₃) (-(-1 : ℂ))).yR (-(-1 : ℂ)) neg_neg_one_ne_zero b n x :=
  regularRepL_mode (Qm P₃) neg_one_ne_zero' b n x

theorem pBot_rho_vacuum (P : LWModule W) (u : (pBotAmMod P).carrier) :
    (pBotAmMod P).ρ (mkAnFull W 0 W.vacuum) u = u := by
  apply Subtype.ext
  have h := pBotIncl_act P W.vacuum u
  rw [oLevW_vacuum] at h
  exact h

theorem phiT_lowest (w : M) : LowestSet (Lt P₃) (Set.range (phiT A T Pr hrat hP₃ w)) := by
  rintro _ ⟨u, rfl⟩ k a ha n hn
  apply Subtype.ext
  rw [Lt_mode_coe, phiT_coe, ZeroMemClass.coe_zero]
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have : a = 0 := by
      have h := VOA.VertexOperatorAlgebra.L_one_pow_eq_zero W ha (j := 0) (by omega)
      simpa using h
    subst this
    have h0 := OppBase.yR_smul_a neg_neg_one_ne_zero
      ((inD_iff_trans (Qm P₃) _).1 (lamT_inD A T Pr hrat hP₃ w u)) (0 : ℂ) (0 : V) n
    rw [zero_smul, zero_smul] at h0
    exact h0
  · rw [W.vacuum_grade, Submodule.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [OppBase.yR_smul_a neg_neg_one_ne_zero
      ((inD_iff_trans (Qm P₃) _).1 (lamT_inD A T Pr hrat hP₃ w u)), OppBase.yR_vacuum,
      if_neg (by omega), smul_zero]
  · obtain ⟨k', rfl⟩ : ∃ k' : ℕ, k = (k' : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
    rw [lamT_yL A T Pr hrat hP₃ w u ha (by omega), if_neg (by omega)]

theorem phiT_act (w : M) (a : V) (u : (pBotAmMod P₂).carrier) :
    phiT A T Pr hrat hP₃ w ((pBotAmMod P₂).ρ (mkAnFull W 0 a) u)
      = oLevW (Lt P₃) (0 : ℤ) a (phiT A T Pr hrat hP₃ w u) := by
  refine reduce_homogeneous W (P := fun a => phiT A T Pr hrat hP₃ w ((pBotAmMod P₂).ρ
    (mkAnFull W 0 a) u) = oLevW (Lt P₃) (0 : ℤ) a (phiT A T Pr hrat hP₃ w u)) ?_ ?_ ?_ a
  · intro k a ha
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · have : a = 0 := by
        have h := VOA.VertexOperatorAlgebra.L_one_pow_eq_zero W ha (j := 0) (by omega)
        simpa using h
      subst this
      simp only [map_zero, LinearMap.zero_apply]
    · rw [W.vacuum_grade, Submodule.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      simp only [map_smul, LinearMap.smul_apply, pBot_rho_vacuum, oLevW_vacuum]
    · obtain ⟨k', rfl⟩ : ∃ k' : ℕ, k = (k' : ℤ) + 1 := ⟨(k - 1).toNat, by omega⟩
      apply Subtype.ext
      rw [oLevW_homogeneous _ 0 ha, Lt_mode_coe, phiT_coe, phiT_coe,
        lamT_yL A T Pr hrat hP₃ w u ha (by omega), if_pos (by ring)]
      rfl
  · simp only [map_zero, LinearMap.zero_apply]
  · intro a b ha hb
    simp only [map_add, LinearMap.add_apply] at ha hb ⊢
    rw [ha, hb]

variable {T} in
theorem exists_PhiT (hP₂ : P₂.IsIrreducibleLW) (w : M) :
    ∃ Φ : P₂.carrier →ₗ[ℂ] (oppBase (Qm P₃)).Dsub (-1),
      (∀ (a : V) (p : ℤ) (y : P₂.carrier),
        Φ (mode (P₂.isMod.YM a) p y) = mode ((Lt P₃).YM a) p (Φ y)) ∧
      ∀ u, Φ (pBotIncl P₂ u) = phiT A T Pr hrat hP₃ w u :=
  exists_hom_of_bottom Pr hrat P₂ hP₂ (Lt P₃)
    (genAdmLev (Lt P₃) _ (phiT_lowest A T Pr hrat hP₃ w)) (phiT A T Pr hrat hP₃ w)
    (fun u => mem_genAdmLev_zero (Lt P₃) _ (phiT_lowest A T Pr hrat hP₃ w) ⟨u, rfl⟩)
    (fun a u => phiT_act A T Pr hrat hP₃ w a u)

section PhiT

variable (hP₂ : P₂.IsIrreducibleLW)

/-- **The extension `Φ_w : P₂ → D_{P(−1)}(P₃')`**. -/
noncomputable def PhiT (w : M) : P₂.carrier →ₗ[ℂ] (oppBase (Qm P₃)).Dsub (-1) :=
  (exists_PhiT A (T := T) Pr hrat hP₃ hP₂ w).choose

theorem PhiT_equiv (w : M) (a : V) (p : ℤ) (y : P₂.carrier) :
    PhiT A T Pr hrat hP₃ hP₂ w (mode (P₂.isMod.YM a) p y)
      = mode ((Lt P₃).YM a) p (PhiT A T Pr hrat hP₃ hP₂ w y) :=
  (exists_PhiT A (T := T) Pr hrat hP₃ hP₂ w).choose_spec.1 a p y

theorem PhiT_bot (w : M) (u : (pBotAmMod P₂).carrier) :
    PhiT A T Pr hrat hP₃ hP₂ w (pBotIncl P₂ u) = phiT A T Pr hrat hP₃ w u :=
  (exists_PhiT A (T := T) Pr hrat hP₃ hP₂ w).choose_spec.2 u

theorem homExt_P₂ (hP₂ : P₂.IsIrreducibleLW) (Φ Φ' : P₂.carrier →ₗ[ℂ] (oppBase (Qm P₃)).Dsub (-1))
    (hΦ : ∀ (a : V) (p : ℤ) (y : P₂.carrier),
      Φ (mode (P₂.isMod.YM a) p y) = mode ((Lt P₃).YM a) p (Φ y))
    (hΦ' : ∀ (a : V) (p : ℤ) (y : P₂.carrier),
      Φ' (mode (P₂.isMod.YM a) p y) = mode ((Lt P₃).YM a) p (Φ' y))
    (hb : ∀ u, Φ (pBotIncl P₂ u) = Φ' (pBotIncl P₂ u)) : Φ = Φ' :=
  hom_ext_of_bottom P₂ hP₂ (Lt P₃) Φ Φ' hΦ hΦ' hb

/-- **`Y^R` on `Φ_w(y)` is the `M`-action**. -/
theorem PhiT_M (w : M) (b : V) (n : ℤ) (y : P₂.carrier) :
    mode ((Rt P₃).YM b) n (PhiT A T Pr hrat hP₃ hP₂ w y)
      = PhiT A T Pr hrat hP₃ hP₂ (mode (A.YM b) n w) y := by
  have h := homExt_P₂ hP₂ ((mode ((Rt P₃).YM b) n).comp (PhiT A T Pr hrat hP₃ hP₂ w))
    (PhiT A T Pr hrat hP₃ hP₂ (mode (A.YM b) n w))
    (fun a p y => by
      simp only [LinearMap.comp_apply, PhiT_equiv]
      exact (LR_comm_t a b p n _).symm)
    (PhiT_equiv A T Pr hrat hP₃ hP₂ _)
    (fun u => by
      simp only [LinearMap.comp_apply, PhiT_bot]
      apply Subtype.ext
      rw [regularRepR_mode, phiT_coe, phiT_coe]
      exact lamT_yR A T Pr hrat hP₃ w u b n)
  exact LinearMap.congr_fun h y

theorem PhiT_add (w w' : M) :
    PhiT A T Pr hrat hP₃ hP₂ (w + w')
      = PhiT A T Pr hrat hP₃ hP₂ w + PhiT A T Pr hrat hP₃ hP₂ w' := by
  refine homExt_P₂ hP₂ _ _ (PhiT_equiv A T Pr hrat hP₃ hP₂ _) (fun a p y => ?_) (fun u => ?_)
  · simp only [LinearMap.add_apply, PhiT_equiv, map_add]
  · simp only [LinearMap.add_apply, PhiT_bot]
    exact Subtype.ext (lamT_add_w A T Pr hrat hP₃ w w' u)

theorem PhiT_smul (c : ℂ) (w : M) :
    PhiT A T Pr hrat hP₃ hP₂ (c • w) = c • PhiT A T Pr hrat hP₃ hP₂ w := by
  refine homExt_P₂ hP₂ _ _ (PhiT_equiv A T Pr hrat hP₃ hP₂ _) (fun a p y => ?_) (fun u => ?_)
  · simp only [LinearMap.smul_apply, PhiT_equiv, map_smul]
  · simp only [LinearMap.smul_apply, PhiT_bot]
    exact Subtype.ext (lamT_smul_w A T Pr hrat hP₃ c w u)

end PhiT

end Target

end VOA.Huang.LiRegular
