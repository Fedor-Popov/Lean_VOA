import VOA.Classification.COne.OrbPrimSpectrum
import VOA.Classification.COne.OrbRat6V2

/-! # OrbPrim (H1): the primaries of `V₂` in weight `n²` are the `sl₂`-multiplet of `e^{nα}`

With `f₀ = (e^{-α})₍₀₎` (`OrbRat6.fo`) and `v_{n,k} = f₀^k e^{nα}`:

* `vn_prim`: every `v_{n,k}` is a Virasoro primary of weight `n²` (`f₀` commutes with all
  `L(m)`, because a weight-one screening kills `ω`; `e^{nα}` is primary by `LLGen_tmul`);
* `vn_ne_zero`: `v_{n,k} ≠ 0` for `k ≤ 2n` (`e₀ v_{n,k+1} = ε(k+1)(2n-k) v_{n,k}`);
* `vn_linearIndependent`: they lie in distinct charge sectors `n - k`;
* `finrank_prim_V2_sq : dim Prim_{n²}(V₂) = 2n + 1` and
  `prim_V2_sq_eq_span : Prim_{n²}(V₂) = span {v_{n,k} : k ≤ 2n}` (with the upper bound
  `primSpectrumBound_V2`).
-/

set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
noncomputable section
namespace VOA.Classification.COne.OrbPrim
open VOA VertexOperatorAlgebra OrbSpan Finset VOA.LatGen VOA.LatGen.Triplet HeisenbergN
  OrbRat6

/-- `V₂`. -/
abbrev V2v : VertexOperatorAlgebra Sp := V2m 1 le_rfl

theorem chargeGen_grading (n : ℤ) : latChargeGen (latP 1) n ∈ V2v.grading (n ^ 2) := by
  have h := bigradα_le_gradingLatGen (latP 1) 0 n (show latChargeGen (latP 1) n ∈
    bigradα (latP 1) (0, n) from ⟨_, one_mem_Z0, rfl⟩)
  rw [halfNorm_latP, zero_add] at h
  change latChargeGen (latP 1) n ∈ gradingLatGen (latP 1) (n ^ 2)
  simpa using h

theorem chargeGen_primary (n : ℤ) (m : ℕ) :
    V2v.L ((m : ℤ) + 1) (latChargeGen (latP 1) n) = 0 := by
  rw [V2v, V2m, latticeVOAGen_L, latChargeGen, LLGen_tmul _ (latP_posDef 1 le_rfl),
    LvirN_vacuum _ _ (by omega), chargeOsc_vacuum _ _ _ (by omega), if_neg (by omega)]
  simp [latStateGen]

theorem fo_eq_screening (x : Sp) : fo x = Screening.screening V2v (latChargeGen (latP 1) (-a1 1)) x := by
  rw [fo_eq]; rfl

theorem chargeGen_neg_grading : latChargeGen (latP 1) (-a1 1) ∈ V2v.grading 1 := by
  have h := chargeGen_grading (-1)
  simpa [a1] using h

theorem fo_L (m : ℤ) (x : Sp) : fo (V2v.L m x) = V2v.L m (fo x) := by
  have h := Screening.screening_comm_mode V2v (latChargeGen (latP 1) (-a1 1)) V2v.conformalVector (m + 1) x
  rw [Screening.screening_conformalVector V2v chargeGen_neg_grading] at h
  have h0 : V2v.smul 0 (m + 1) x = 0 := by
    rw [PreVertexAlgebra.smul_def, map_zero]; rfl
  rw [h0, sub_eq_zero] at h
  rw [fo_eq_screening, fo_eq_screening]
  exact h

theorem fo_grading {k : ℤ} {x : Sp} (hx : x ∈ V2v.grading k) : fo x ∈ V2v.grading k := by
  rw [fo_eq_screening]; exact Screening.screening_mem_grading V2v chargeGen_neg_grading hx

theorem fo_prim {N : ℤ} {x : Sp} (hx : x ∈ prim V2v N) : fo x ∈ prim V2v N := by
  rw [mem_prim] at hx ⊢
  refine ⟨fo_grading hx.1, fun m => ?_⟩
  rw [← fo_L, hx.2 m, map_zero]

/-- `v_{n,k} = f₀^k e^{nα}`. -/
def vn (n k : ℕ) : Sp := (fo ^ k) (latChargeGen (latP 1) (n : ℤ))

theorem chargeGen_prim (n : ℤ) : latChargeGen (latP 1) n ∈ prim V2v (n ^ 2) := by
  rw [mem_prim]
  exact ⟨chargeGen_grading n, fun m => chargeGen_primary n m⟩

theorem vn_prim (n k : ℕ) : vn n k ∈ prim V2v ((n : ℤ) ^ 2) := by
  induction k with
  | zero => simpa [vn] using chargeGen_prim (n : ℤ)
  | succ k ih =>
    have : vn n (k + 1) = fo (vn n k) := by
      simp only [vn, pow_succ', Module.End.mul_apply]
    rw [this]
    exact fo_prim ih

theorem vn_bigrad (n k : ℕ) :
    vn n k ∈ bigradα (latP 1) ((k : ℤ) * (2 * (n : ℤ) - (k : ℤ)), ((n : ℤ) - (k : ℤ) : ℤ)) := by
  induction k with
  | zero => simpa [vn] using (show latChargeGen (latP 1) (n : ℤ) ∈
      bigradα (latP 1) (0, (n : ℤ)) from ⟨_, one_mem_Z0, rfl⟩)
  | succ k ih =>
    have : vn n (k + 1) = fo (vn n k) := by
      simp only [vn, pow_succ', Module.End.mul_apply]
    rw [this]
    have h := Qscr_mem_bigradα (latP 1) (-a1 1) ih
    convert h using 3
    · rw [latP_form]; simp [a1]; ring
    · change ((n : ℤ) - ((k + 1 : ℕ) : ℤ)) = ((n : ℤ) - k) + -1
      push_cast; ring

theorem eo_chargeGen (n : ℕ) : eo (latChargeGen (latP 1) (n : ℤ)) = 0 :=
  Qscr_latChargeGen_of_nonneg (latP 1) (β := a1 1) (γ := (n : ℤ))
    (by rw [latP_form]; simp [a1])

theorem ho_chargeGen (n : ℕ) :
    ho (latChargeGen (latP 1) (n : ℤ)) = ((2 * n : ℕ) : ℂ) • latChargeGen (latP 1) (n : ℤ) := by
  rw [VertexOperatorAlgebra.zeroMode_apply, show (1 : ℤ) - 1 = 0 by norm_num,
    show latChargeGen (latP 1) (n : ℤ) = latStateGen (latP 1) (vacuumN _) (n : ℤ) from rfl,
    smul_hSt_zero_latStateGen, latP_form]
  congr 1

theorem eo_vn (n k : ℕ) :
    eo (vn n (k + 1)) = (eps1 * (k + 1) * (((2 * n : ℕ) : ℂ) - k)) • vn n k :=
  E_Fpow V_EF V_HF (eo_chargeGen n) (ho_chargeGen n) k

theorem eps1_ne_zero : eps1 ≠ 0 := by
  rcases eps1_cases with h | h <;> rw [h] <;> norm_num

theorem vn_ne_zero (n : ℕ) : ∀ k ≤ 2 * n, vn n k ≠ 0 := by
  intro k hk
  induction k with
  | zero => exact latChargeGen_ne_zero 1 (n : ℤ)
  | succ k ih =>
    intro h0
    have he := eo_vn n k
    rw [h0, map_zero] at he
    have hc : eps1 * (k + 1) * (((2 * n : ℕ) : ℂ) - k) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero eps1_ne_zero (by exact_mod_cast Nat.succ_ne_zero k)) ?_
      rw [sub_ne_zero]
      intro hk'
      have : 2 * n = k := by exact_mod_cast hk'
      omega
    exact ih (by omega) ((smul_eq_zero.mp he.symm).resolve_left hc)

theorem vn_linearIndependent (n : ℕ) :
    LinearIndependent ℂ (fun k : Fin (2 * n + 1) => vn n k) := by
  let idx : Fin (2 * n + 1) → ℤ × (latP 1).carrier :=
    fun k => (((k : ℕ) : ℤ) * (2 * (n : ℤ) - ((k : ℕ) : ℤ)), ((n : ℤ) - ((k : ℕ) : ℤ) : ℤ))
  have hinj : Function.Injective idx := by
    intro a b h
    have h2 := congrArg Prod.snd h
    simp only [idx] at h2
    apply Fin.ext
    have : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := by
      have h2' : (n : ℤ) - ((a : ℕ) : ℤ) = (n : ℤ) - ((b : ℕ) : ℤ) := h2
      omega
    exact_mod_cast this
  refine iSupIndep.linearIndependent (fun k => bigradα (latP 1) (idx k))
    ((bigradα_iSupIndep (latP 1)).comp hinj) (fun k => vn_bigrad n k)
    (fun k => vn_ne_zero n k (by omega))

/-- **`dim Prim_{n²}(V₂) = 2n + 1`.** -/
theorem finrank_prim_V2_sq (n : ℕ) : Module.finrank ℂ (prim V2v ((n : ℤ) ^ 2)) = 2 * n + 1 := by
  haveI : FiniteDimensional ℂ (V2v.grading ((n : ℤ) ^ 2)) := V2v.finrank _
  haveI : FiniteDimensional ℂ (prim V2v ((n : ℤ) ^ 2)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  refine le_antisymm (primSpectrumBound_V2.2 n) ?_
  have hli := vn_linearIndependent n
  have hle : Submodule.span ℂ (Set.range fun k : Fin (2 * n + 1) => vn n k) ≤
      prim V2v ((n : ℤ) ^ 2) :=
    Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact vn_prim n k)
  have := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hli, Fintype.card_fin] at this
  exact this

/-- **`Prim_{n²}(V₂)` is spanned by the `sl₂`-multiplet `f₀^k e^{nα}`, `0 ≤ k ≤ 2n`.** -/
theorem prim_V2_sq_eq_span (n : ℕ) :
    prim V2v ((n : ℤ) ^ 2) = Submodule.span ℂ (Set.range fun k : Fin (2 * n + 1) => vn n k) := by
  haveI : FiniteDimensional ℂ (V2v.grading ((n : ℤ) ^ 2)) := V2v.finrank _
  haveI : FiniteDimensional ℂ (prim V2v ((n : ℤ) ^ 2)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hle : Submodule.span ℂ (Set.range fun k : Fin (2 * n + 1) => vn n k) ≤
      prim V2v ((n : ℤ) ^ 2) :=
    Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact vn_prim n k)
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [finrank_prim_V2_sq, finrank_span_eq_card (vn_linearIndependent n), Fintype.card_fin]

end VOA.Classification.COne.OrbPrim
