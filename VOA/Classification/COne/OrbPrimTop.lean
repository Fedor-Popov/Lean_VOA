import VOA.Classification.COne.OrbPrimMultiplet

/-! # OrbPrim (H2): the top channel of products of primaries of `V₂`

Normalize the multiplet as `w_{n,k} = ((2n-k)!/(2n)!) f₀^k e^{nα}` (so `e₀ w_{n,k} = ε k w_{n,k-1}`,
matching `x ∂_y` on the binary form `x^{2n-k} y^k`). Then for `s, m ≥ 0`, `i ≤ 2s`, `j ≤ 2m`:

  `top_w`: `w_{s,i}₍₋₂ₛₘ₋₁₎ w_{m,j} ≡ ε(s,m) · w_{s+m,i+j}` modulo lower Virasoro descendants,

i.e. the top channel is multiplication of binary forms (the Cartan product).

Proof: induction on `i + j`. The base `e^{sα}₍₋₂ₛₘ₋₁₎e^{mα} = ε e^{(s+m)α}` is the lattice product
formula. In the step the difference `Φ` has `h₀`-eigenvalue `2(s+m) - 2(i+j)` and `e₀ Φ` is a
combination of earlier differences (both `e₀` and `w ↦ e₀ w` are derivations); `ekernel` shows that
such a vector lies in the descendants: its primary part is a multiple of `w_{s+m,i+j}`
(eigenvalues of `h₀` on the multiplet are distinct) which `e₀` does not kill, while `e₀` maps
the primary part into `Prim ∩ Desc = 0` (unitarity).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbPrim
open VOA VertexOperatorAlgebra OrbSpan Finset VOA.LatGen VOA.LatGen.Triplet HeisenbergN
  OrbRat6 Screening VOA.IntegralLattice

universe u

/-! ## Weight-one zero modes preserve primaries and descendants -/

section Generic
variable {V : Type u} [AddCommGroup V] [Module ℂ V] (W : VertexOperatorAlgebra V) {a : V}

theorem scr_comm_L (ha : a ∈ W.grading 1) (m : ℤ) (x : V) :
    screening W a (W.L m x) = W.L m (screening W a x) := by
  have h := screening_comm_mode W a W.conformalVector (m + 1) x
  rw [screening_conformalVector W ha] at h
  have h0 : W.smul 0 (m + 1) x = 0 := by
    rw [PreVertexAlgebra.smul_def, map_zero]; rfl
  rw [h0, sub_eq_zero] at h
  exact h

theorem scr_lowerDesc (ha : a ∈ W.grading 1) {N : ℤ} {x : V} (hx : x ∈ lowerDesc W N) :
    screening W a x ∈ lowerDesc W N := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, y, hy, rfl⟩ := hz
    rw [scr_comm_L W ha]
    exact Submodule.subset_span ⟨m, _, screening_mem_grading W ha hy, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem scr_prim (ha : a ∈ W.grading 1) {N : ℤ} {x : V} (hx : x ∈ prim W N) :
    screening W a x ∈ prim W N := by
  rw [mem_prim] at hx ⊢
  refine ⟨screening_mem_grading W ha hx.1, fun m => ?_⟩
  rw [← scr_comm_L W ha, hx.2 m, map_zero]

theorem prim_inf_lowerDesc (U : VirUnitaryForm W) (N : ℤ) : prim W N ⊓ lowerDesc W N = ⊥ := by
  rw [eq_bot_iff]
  intro p hpd
  rw [Submodule.mem_inf] at hpd
  obtain ⟨hp, hd⟩ := hpd
  rw [Submodule.mem_bot]
  apply U.self_eq_zero
  rw [mem_prim] at hp
  have horth : ∀ z ∈ lowerDesc W N, U.form p z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨m, y, hy, rfl⟩ := hz
      rw [show -(m : ℤ) - 1 = -((m : ℤ) + 1) by ring, ← U.adjoint, hp.2 m, map_zero,
        LinearMap.zero_apply]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [LinearMap.map_smulₛₗ, hx, smul_zero]
  exact horth p hd

end Generic

/-! ## `e₀`, `h₀` on `V₂` -/

theorem chargeGen_pos_grading : latChargeGen (latP 1) (a1 1) ∈ V2v.grading 1 := by
  have h := chargeGen_grading 1
  simpa [a1] using h

theorem eo_eq_scr (x : Sp) : eo x = screening V2v (latChargeGen (latP 1) (a1 1)) x := by
  rw [eo_eq]; rfl

theorem hSt_grading : hSt (latP 1) (a1 1) ∈ V2v.grading 1 := by
  have h := screening_mem_grading V2v chargeGen_pos_grading chargeGen_neg_grading
  rw [screening_apply] at h
  have he : V2v.smul (latChargeGen (latP 1) (a1 1)) 0 (latChargeGen (latP 1) (-a1 1)) =
      eps1 • hSt (latP 1) (a1 1) := smul_e_f
  change V2v.smul (latChargeGen (latP 1) (a1 1)) 0 (latChargeGen (latP 1) (-a1 1)) ∈ _ at h
  rw [he] at h
  have := (V2v.grading 1).smul_mem eps1 h
  rwa [smul_smul, show eps1 * eps1 = 1 from eps1_sq, one_smul] at this

theorem ho_eq_scr (x : Sp) : ho x = screening V2v (hSt (latP 1) (a1 1)) x := by
  rw [VertexOperatorAlgebra.zeroMode_apply, show (1 : ℤ) - 1 = 0 by norm_num]; rfl

theorem eo_lowerDesc {N : ℤ} {x : Sp} (hx : x ∈ lowerDesc V2v N) : eo x ∈ lowerDesc V2v N := by
  rw [eo_eq_scr]; exact scr_lowerDesc V2v chargeGen_pos_grading hx

theorem ho_lowerDesc {N : ℤ} {x : Sp} (hx : x ∈ lowerDesc V2v N) : ho x ∈ lowerDesc V2v N := by
  rw [ho_eq_scr]; exact scr_lowerDesc V2v hSt_grading hx

theorem eo_prim {N : ℤ} {x : Sp} (hx : x ∈ prim V2v N) : eo x ∈ prim V2v N := by
  rw [eo_eq_scr]; exact scr_prim V2v chargeGen_pos_grading hx

theorem ho_prim {N : ℤ} {x : Sp} (hx : x ∈ prim V2v N) : ho x ∈ prim V2v N := by
  rw [ho_eq_scr]; exact scr_prim V2v hSt_grading hx

theorem eo_grading {k : ℤ} {x : Sp} (hx : x ∈ V2v.grading k) : eo x ∈ V2v.grading k := by
  rw [eo_eq_scr]; exact screening_mem_grading V2v chargeGen_pos_grading hx

theorem eo_smul (a : Sp) (n : ℤ) (b : Sp) :
    eo (V2v.smul a n b) = V2v.smul (eo a) n b + V2v.smul a n (eo b) := by
  rw [eo_eq, eo_eq, eo_eq]
  exact zeroMode_leibniz V2v _ a b n

theorem ho_smul (a : Sp) (n : ℤ) (b : Sp) :
    ho (V2v.smul a n b) = V2v.smul (ho a) n b + V2v.smul a n (ho b) := by
  rw [ho_eq_scr, ho_eq_scr, ho_eq_scr, screening_apply, screening_apply, screening_apply]
  exact zeroMode_leibniz V2v _ a b n

theorem ho_vn (n k : ℕ) : ho (vn n k) = (((2 * n : ℕ) : ℂ) - 2 * k) • vn n k :=
  H_Fpow V_HF (ho_chargeGen n) k

/-! ## The `e₀`-kernel lemma -/

theorem vn_eq_zero_of_gt (n k : ℕ) (hk : 2 * n < k) : vn n k = 0 := by
  have h := vn_bigrad n k
  rw [bigradα_eq_bot_of_neg _ _ (by nlinarith), Submodule.mem_bot] at h
  exact h

/-- A weight-`N²` vector of `h₀`-weight `2N - 2t` (`t ≥ 1`) whose `e₀`-image is a descendant
is itself a descendant. -/
theorem ekernel (N t : ℕ) (ht : 1 ≤ t) {x : Sp} (hx : x ∈ V2v.grading ((N : ℤ) ^ 2))
    (hh : ho x = (((2 * N : ℕ) : ℂ) - 2 * t) • x)
    (he : eo x ∈ lowerDesc V2v ((N : ℤ) ^ 2)) : x ∈ lowerDesc V2v ((N : ℤ) ^ 2) := by
  obtain ⟨U⟩ := v2VirUnitary_holds
  have hdec := virPrimaryDecomp_of_unitary U ((N : ℤ) ^ 2) hx
  obtain ⟨p, hp, d, hd, rfl⟩ := Submodule.mem_sup.mp hdec
  have hinf := prim_inf_lowerDesc V2v U ((N : ℤ) ^ 2)
  -- the primary part is an `h₀`-eigenvector
  have hhp : ho p = (((2 * N : ℕ) : ℂ) - 2 * t) • p := by
    have h1 : ho p - (((2 * N : ℕ) : ℂ) - 2 * t) • p ∈ prim V2v ((N : ℤ) ^ 2) :=
      Submodule.sub_mem _ (ho_prim hp) (Submodule.smul_mem _ _ hp)
    have h2 : ho p - (((2 * N : ℕ) : ℂ) - 2 * t) • p ∈ lowerDesc V2v ((N : ℤ) ^ 2) := by
      have : ho p - (((2 * N : ℕ) : ℂ) - 2 * t) • p =
          -(ho d - (((2 * N : ℕ) : ℂ) - 2 * t) • d) := by
        rw [map_add, smul_add] at hh
        rw [neg_sub, eq_sub_iff_add_eq]
        rw [← sub_eq_zero] at hh ⊢
        rw [← hh]; abel
      rw [this]
      exact Submodule.neg_mem _ (Submodule.sub_mem _ (ho_lowerDesc hd) (Submodule.smul_mem _ _ hd))
    have h3 : ho p - (((2 * N : ℕ) : ℂ) - 2 * t) • p ∈ prim V2v ((N : ℤ) ^ 2) ⊓
        lowerDesc V2v ((N : ℤ) ^ 2) := ⟨h1, h2⟩
    rw [hinf, Submodule.mem_bot, sub_eq_zero] at h3
    exact h3
  -- `e₀ p = 0`
  have hep : eo p = 0 := by
    have h1 : eo p ∈ lowerDesc V2v ((N : ℤ) ^ 2) := by
      have : eo p = eo (p + d) - eo d := by rw [map_add]; abel
      rw [this]; exact Submodule.sub_mem _ he (eo_lowerDesc hd)
    have h3 : eo p ∈ prim V2v ((N : ℤ) ^ 2) ⊓ lowerDesc V2v ((N : ℤ) ^ 2) := ⟨eo_prim hp, h1⟩
    rwa [hinf, Submodule.mem_bot] at h3
  -- expand `p` in the multiplet basis
  have hp' := hp
  rw [prim_V2_sq_eq_span, Submodule.mem_span_range_iff_exists_fun] at hp'
  obtain ⟨c, hc⟩ := hp'
  have hli := Fintype.linearIndependent_iff.mp (vn_linearIndependent N)
  -- only the coefficient at `t` survives
  have hct : ∀ k : Fin (2 * N + 1), (k : ℕ) ≠ t → c k = 0 := by
    have hsum : ∑ k : Fin (2 * N + 1), (c k * (2 * (t : ℂ) - 2 * (k : ℕ))) • vn N k = 0 := by
      have e1 : ho p = ∑ k : Fin (2 * N + 1), (c k * (((2 * N : ℕ) : ℂ) - 2 * (k : ℕ))) •
          vn N k := by
        rw [← hc, map_sum]
        refine sum_congr rfl fun k _ => ?_
        rw [map_smul, ho_vn, smul_smul]
      have e2 : (((2 * N : ℕ) : ℂ) - 2 * t) • p = ∑ k : Fin (2 * N + 1),
          (c k * (((2 * N : ℕ) : ℂ) - 2 * t)) • vn N k := by
        rw [← hc, smul_sum]
        refine sum_congr rfl fun k _ => ?_
        rw [smul_smul, mul_comm]
      have := hhp
      rw [e1, e2, ← sub_eq_zero, ← sum_sub_distrib] at this
      rw [← this]
      refine sum_congr rfl fun k _ => ?_
      rw [← sub_smul]; congr 1; ring
    intro k hk
    have := hli _ hsum k
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exfalso; apply hk
      have : (t : ℂ) = (k : ℕ) := by linear_combination h / 2
      exact_mod_cast this.symm
  by_cases htN : t ≤ 2 * N
  · -- `p = c_t v_t`, and `e₀ v_t ≠ 0`
    set kt : Fin (2 * N + 1) := ⟨t, by omega⟩
    have hpt : p = c kt • vn N t := by
      rw [← hc, Fintype.sum_eq_single kt (fun k hk => by
        rw [hct k (fun h => hk (Fin.ext h)), zero_smul])]
    have hct0 : c kt = 0 := by
      rw [hpt, map_smul] at hep
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      rw [eo_vn, smul_smul] at hep
      rcases smul_eq_zero.mp hep with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact h
        · exfalso
          refine mul_ne_zero (mul_ne_zero eps1_ne_zero (by exact_mod_cast Nat.succ_ne_zero t')) ?_ h
          rw [sub_ne_zero]; intro h'
          have : 2 * N = t' := by exact_mod_cast h'
          omega
      · exact absurd h (vn_ne_zero N t' (by omega))
    rw [hpt, hct0, zero_smul, zero_add]
    exact hd
  · have hp0 : p = 0 := by
      rw [← hc]
      exact sum_eq_zero fun k _ => by
        rw [hct k (by have := k.2; omega), zero_smul]
    rw [hp0, zero_add]; exact hd

/-! ## The normalized multiplet and the top channel -/

/-- `c_{n,k} = (2n-k)!/(2n)!`. -/
def cnk (n k : ℕ) : ℂ := ((2 * n - k).factorial : ℂ) / ((2 * n).factorial : ℂ)

/-- `w_{n,k} = c_{n,k} f₀^k e^{nα}`. -/
def wv (n k : ℕ) : Sp := cnk n k • vn n k

theorem wv_zero (n : ℕ) : wv n 0 = latChargeGen (latP 1) (n : ℤ) := by
  rw [wv, cnk, Nat.sub_zero, div_self (by exact_mod_cast (Nat.factorial_ne_zero _)), one_smul]
  rfl

theorem wv_prim (n k : ℕ) : wv n k ∈ prim V2v ((n : ℤ) ^ 2) :=
  Submodule.smul_mem _ _ (vn_prim n k)

theorem wv_grading (n k : ℕ) : wv n k ∈ V2v.grading ((n : ℤ) ^ 2) :=
  ((mem_prim V2v).mp (wv_prim n k)).1

theorem ho_wv (n k : ℕ) : ho (wv n k) = (((2 * n : ℕ) : ℂ) - 2 * k) • wv n k := by
  rw [wv, map_smul, ho_vn, smul_comm]

theorem eo_wv_zero (n : ℕ) : eo (wv n 0) = 0 := by
  rw [wv_zero]; exact eo_chargeGen n

theorem eo_wv (n k : ℕ) (hk : k + 1 ≤ 2 * n) :
    eo (wv n (k + 1)) = (eps1 * (k + 1 : ℕ)) • wv n k := by
  rw [wv, wv, map_smul, eo_vn, smul_smul, smul_smul]
  congr 1
  have hf : ((2 * n - k).factorial : ℂ) = ((2 * n - k : ℕ) : ℂ) * ((2 * n - (k + 1)).factorial : ℂ) := by
    rw [show 2 * n - k = (2 * n - (k + 1)) + 1 by omega, Nat.factorial_succ]
    push_cast; ring
  have hcast : (((2 * n : ℕ) : ℂ) - k) = ((2 * n - k : ℕ) : ℂ) := by
    rw [Nat.cast_sub (by omega)]
  rw [cnk, cnk, hf, hcast]
  push_cast
  ring

theorem eo_wv' (n i : ℕ) (hi : i ≤ 2 * n) :
    eo (wv n i) = if i = 0 then 0 else (eps1 * (i : ℂ)) • wv n (i - 1) := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [if_pos rfl, eo_wv_zero]
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [if_neg (by omega), eo_wv n k hi, Nat.add_sub_cancel]

/-- The cocycle sign of the top channel. -/
def topSign (s m : ℕ) : ℂ := latticeCocycle (latP 1) (s : ℤ) (m : ℤ)

theorem smul_chargeGen_bottom (s m : ℤ) :
    V2v.smul (latChargeGen (latP 1) s) (-(latP 1).form s m - 1) (latChargeGen (latP 1) m) =
      latticeCocycle (latP 1) s m • latChargeGen (latP 1) (s + m) := by
  have hY : V2v.Y (latChargeGen (latP 1) s) = Yeαvec (latP 1) s := by
    have hw := YfullGen_word (latP 1) (latP_even 1) (latP_posDef 1 le_rfl) [] s
    rw [YwordLatGen_nil] at hw
    exact hw
  rw [PreVertexAlgebra.smul_def, hY]
  simp only [mode_apply, latChargeGen]
  rw [Yeαvec_tmul, show -(-(latP 1).form s m - 1) - 1 - (latP 1).form s m = (0 : ℤ) by ring,
    EEVec_vacuum, if_pos (le_refl (0 : ℤ)), Int.toNat_zero, vSchur_zero]
  rfl

/-- The top-channel mode index `-2sm-1`. -/
def topIdx (s m : ℕ) : ℤ := -((2 * s * m : ℕ) : ℤ) - 1

/-- **The top channel is the Cartan product.** -/
theorem top_wv (s m : ℕ) : ∀ t : ℕ, ∀ i j : ℕ, i + j = t → i ≤ 2 * s → j ≤ 2 * m →
    V2v.smul (wv s i) (topIdx s m) (wv m j) - topSign s m • wv (s + m) (i + j) ∈
      lowerDesc V2v (((s + m : ℕ) : ℤ) ^ 2) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro i j hij hi hj
  rcases Nat.eq_zero_or_pos t with rfl | htpos
  · obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := ⟨by omega, by omega⟩
    have h := smul_chargeGen_bottom (s : ℤ) (m : ℤ)
    rw [latP_form] at h
    rw [wv_zero, wv_zero, wv_zero, topIdx, topSign,
      show -((2 * s * m : ℕ) : ℤ) - 1 = -(2 * ((1 : ℕ) : ℤ) * (s : ℤ) * (m : ℤ)) - 1 by
        push_cast; ring, h]
    push_cast
    rw [sub_self]; exact Submodule.zero_mem _
  · set Φ := fun a b : ℕ =>
      V2v.smul (wv s a) (topIdx s m) (wv m b) - topSign s m • wv (s + m) (a + b) with hΦ
    change Φ i j ∈ _
    have hN : (((s + m : ℕ) : ℤ) ^ 2) = ((s : ℤ) ^ 2 + (m : ℤ) ^ 2 + 2 * s * m) := by
      push_cast; ring
    -- grading
    have hgr : Φ i j ∈ V2v.grading (((s + m : ℕ) : ℤ) ^ 2) := by
      refine Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ (wv_grading _ _))
      have h := V2v.smul_mem_grading (wv_grading s i) (wv_grading m j) (topIdx s m)
      rw [topIdx] at h
      convert h using 2
      push_cast; ring
    -- `h₀`-weight
    have hho : ho (Φ i j) = (((2 * (s + m) : ℕ) : ℂ) - 2 * t) • Φ i j := by
      subst hij
      simp only [hΦ]
      rw [map_sub, map_smul, ho_smul, ho_wv, ho_wv, ho_wv, PreVertexAlgebra.smul_smul_left,
        PreVertexAlgebra.smul_smul_right]
      push_cast
      module
    -- `e₀` maps into the descendants
    have heo : eo (Φ i j) ∈ lowerDesc V2v (((s + m : ℕ) : ℤ) ^ 2) := by
      have hsplit : eo (Φ i j) =
          (if i = 0 then 0 else (eps1 * (i : ℂ)) • Φ (i - 1) j) +
          (if j = 0 then 0 else (eps1 * (j : ℂ)) • Φ i (j - 1)) := by
        simp only [hΦ]
        rw [map_sub, map_smul, eo_smul, eo_wv' s i hi, eo_wv' m j hj,
          eo_wv' (s + m) (i + j) (by omega)]
        by_cases hi0 : i = 0 <;> by_cases hj0 : j = 0
        · omega
        · subst hi0
          simp only [if_true, if_neg hj0, zero_add, PreVertexAlgebra.smul_zero_left,
            PreVertexAlgebra.smul_smul_right]
          module
        · subst hj0
          simp only [if_true, if_neg hi0, add_zero, PreVertexAlgebra.smul_zero_right,
            PreVertexAlgebra.smul_smul_left]
          module
        · simp only [if_neg hi0, if_neg hj0, if_neg (show ¬ i + j = 0 by omega),
            PreVertexAlgebra.smul_smul_left, PreVertexAlgebra.smul_smul_right,
            show i - 1 + j = i + j - 1 by omega, show i + (j - 1) = i + j - 1 by omega]
          push_cast
          module
      rw [hsplit]
      refine Submodule.add_mem _ ?_ ?_
      · split_ifs with hi0
        · exact Submodule.zero_mem _
        · exact Submodule.smul_mem _ _ (ih (i - 1 + j) (by omega) (i - 1) j rfl (by omega) hj)
      · split_ifs with hj0
        · exact Submodule.zero_mem _
        · exact Submodule.smul_mem _ _ (ih (i + (j - 1)) (by omega) i (j - 1) rfl hi (by omega))
    have hk := ekernel (s + m) t htpos hgr (by rw [hho]) heo
    exact hk

end VOA.Classification.COne.OrbPrim
