import VOA.DeligneAudit.DeligneFusionCLNormal

/-!
# The `θ`-box (CL Lemma 3.5.1, 3.6.2, Prop. 3.6.3 at the vector level)

* `box_mod`: the graded `sl₂[t]` box theorem (Chari–Pressley Prop. 6.1, `weyl_span_box_graded`) for a
  vector that is highest weight only *modulo* a stable subspace `S`;
* `theta_box`: for `ȳ = f₂(c) w`, every bihomogeneous `f_θ`-polynomial applied to `ȳ` is a combination of
  `f_θ`-box monomials (box `N`) of the same bidegree applied to `ȳ`, modulo normal words with
  `σ = |a| + Σa + Σc' > Σc`.  The subspace `NW(σ > Σc)` is stable under `f_θ ⊗ tᵏ`, `e_θ ⊗ t` and
  `h_θ ⊗ t^{k+1}` (`eθ_nw`, `hθ_nw`, `fθ_nw`), contains `e_θ(1)ȳ = 0` and `h_θ(k+1)ȳ`, and contains
  `f_θ(0)^{N+1}ȳ` by `G0` (CL Prop. 3.3.3 + the `E₂`-calculus).
-/

namespace VOA.DeligneAudit.CLNormal

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CLFilt VOA.DeligneAudit.Sl2Weyl

noncomputable section

section BoxMod

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (F : ℕ → Module.End ℂ V)
  (hFF : ∀ i j, F i * F j = F j * F i)

/-- The graded box theorem modulo a stable subspace. -/
theorem box_mod {E1 : Module.End ℂ V} {H : ℕ → Module.End ℂ V}
    (hEF : ∀ k, E1 * F k - F k * E1 = H (k + 1))
    (hHF : ∀ m k, H (m + 1) * F k - F k * H (m + 1) = (-2 : ℂ) • F (m + 1 + k))
    (S : Submodule ℂ V) (hSF : ∀ k, S ≤ S.comap (F k)) (hSE : S ≤ S.comap E1)
    (hSH : ∀ m, S ≤ S.comap (H (m + 1)))
    {y : V} (hE : E1 y ∈ S) (hH : ∀ m, H (m + 1) y ∈ S) (m : ℕ) (hN : (F 0 ^ (m + 1)) y ∈ S)
    {p : R} {n : ℕ × ℕ} (hp : MvPolynomial.IsWeightedHomogeneous om p n) :
    Sl2Weyl.evAlg F hFF p y ∈
      Submodule.span ℂ {v | ∃ f, BoxP m f ∧ Finsupp.weight om f = n ∧
        v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) y} ⊔ S := by
  let FQ : ℕ → Module.End ℂ (V ⧸ S) := fun k => S.mapQ S (F k) (hSF k)
  let EQ : Module.End ℂ (V ⧸ S) := S.mapQ S E1 hSE
  let HQ : ℕ → Module.End ℂ (V ⧸ S) := fun k => if h : 1 ≤ k then
    S.mapQ S (H (k - 1 + 1)) (hSH (k - 1)) else 0
  have hHQ : ∀ m, HQ (m + 1) = S.mapQ S (H (m + 1)) (hSH m) := by
    intro m; simp only [HQ, dif_pos (show 1 ≤ m + 1 by omega)]; rfl
  have qext : ∀ (A B : Module.End ℂ (V ⧸ S)), (∀ v, A (S.mkQ v) = B (S.mkQ v)) → A = B := by
    intro A B hAB; ext v; exact hAB v
  have hFFQ : ∀ i j, FQ i * FQ j = FQ j * FQ i := by
    intro i j; refine qext _ _ fun v => ?_
    simp only [Module.End.mul_apply, FQ, Submodule.mkQ_apply, Submodule.mapQ_apply]
    rw [← Module.End.mul_apply (F i), hFF, Module.End.mul_apply]
  have hEFQ : ∀ k, EQ * FQ k - FQ k * EQ = HQ (k + 1) := by
    intro k; rw [hHQ]; refine qext _ _ fun v => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, FQ, EQ, Submodule.mkQ_apply,
      Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub]
    congr 1
    have := congrArg (fun T => T v) (hEF k)
    simpa only [LinearMap.sub_apply, Module.End.mul_apply] using this
  have hHFQ : ∀ m k, HQ (m + 1) * FQ k - FQ k * HQ (m + 1) = (-2 : ℂ) • FQ (m + 1 + k) := by
    intro m k; rw [hHQ]; refine qext _ _ fun v => ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, FQ,
      Submodule.mkQ_apply, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub,
      ← Submodule.Quotient.mk_smul]
    congr 1
    have := congrArg (fun T => T v) (hHF m k)
    simpa only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply] using this
  have hE' : EQ (S.mkQ y) = 0 := by
    simp only [EQ, Submodule.mkQ_apply, Submodule.mapQ_apply]
    exact (Submodule.Quotient.mk_eq_zero S).mpr hE
  have hH' : ∀ m, HQ (m + 1) (S.mkQ y) = 0 := by
    intro m; rw [hHQ]
    simp only [Submodule.mkQ_apply, Submodule.mapQ_apply]
    exact (Submodule.Quotient.mk_eq_zero S).mpr (hH m)
  have hiter : ∀ K (v : V), (FQ 0 ^ K) (S.mkQ v) = S.mkQ ((F 0 ^ K) v) := by
    intro K; induction K with
    | zero => intro v; rfl
    | succ K ih => intro v; rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]; rfl
  have hN' : (FQ 0 ^ (m + 1)) (S.mkQ y) = 0 := by
    rw [hiter]; exact (Submodule.Quotient.mk_eq_zero S).mpr hN
  have hsp := weyl_span_box_graded FQ hFFQ hEFQ hHFQ hE' hH' m hN' hp
  have key := CLFilt.evAlg_mkQ F hFF S hSF hFFQ p y
  rw [key] at hsp
  have : S.mkQ (Sl2Weyl.evAlg F hFF p y) ∈
      (Submodule.span ℂ {v | ∃ f, BoxP m f ∧ Finsupp.weight om f = n ∧
        v = Sl2Weyl.evAlg F hFF (MvPolynomial.monomial f 1) y}).map S.mkQ := by
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_ hsp
    rintro _ ⟨f, hf, hw, rfl⟩
    exact ⟨_, ⟨f, hf, hw, rfl⟩, (CLFilt.evAlg_mkQ F hFF S hSF hFFQ _ y).symm⟩
  rw [← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_comm] at this
  exact this

end BoxMod

section Theta

/-- The subspace `NW(σ > d)`. -/
abbrev Sθ {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V) (w : V)
    (d : ℕ) : Submodule ℂ V := NW ρ w (fun a' _ c' => d + 1 ≤ σ a' c')

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule (bracketTable) V} {w : V}
  {N : ℕ} (hR : MabRel ρ w N 0)

theorem fθ_comm (ρ : CurrentModule (bracketTable) V) (i j : ℕ) :
    ρ.op 5 i * ρ.op 5 j = ρ.op 5 j * ρ.op 5 i := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

include hR

theorem eθ_f2w (m : ℕ) (c : List ℕ) : ρ.op 2 m (Fx ρ 4 c w) = 0 := by
  have := push ρ 4 (ρ.op 2 m) _ (fun s => c_eθf4 ρ m s) c w ⊥ (by rw [e_w hR (by decide) m]; simp)
    (fun c1 s c2 _ => by
      rw [comm_block_apply ρ 4 _ (fun t => c_e1f4 ρ (m + s) t), e_w hR (by decide) (m + s)]; simp)
  simpa using this


omit hR in
theorem Sθ_fθ (d k : ℕ) : Sθ ρ w d ≤ (Sθ ρ w d).comap (ρ.op 5 k) := fun x hx =>
  map_NW _ (fun a b c hp => by rw [fθ_nw]; exact nw_mem hp) hx

theorem Sθ_eθ (d : ℕ) : Sθ ρ w d ≤ (Sθ ρ w d).comap (ρ.op 2 1) := fun x hx =>
  map_NW _ (fun a b c hp => NW_mono (fun a' b' c' h => le_trans hp h) (eθ_nw hR 1 le_rfl a b c)) hx

theorem Sθ_hθ (d m : ℕ) :
    Sθ ρ w d ≤ (Sθ ρ w d).comap (ρ.op 6 (m + 1) + ρ.op 7 (m + 1)) := fun x hx =>
  map_NW _ (fun a b c hp => NW_mono (fun a' b' c' h => by
    obtain ⟨ha, _, _, has, _, hcs, _⟩ := h
    simp only [σ] at hp ⊢; omega) (hθ_nw hR (m + 1) a b c)) hx

/-- **The `θ`-box** (CL Prop. 3.6.3, vector level). -/
theorem theta_box (c : List ℕ) {p : R} {n : ℕ × ℕ} (hp : MvPolynomial.IsWeightedHomogeneous om p n) :
    Sl2Weyl.evAlg (fun k => ρ.op 5 k) (fθ_comm ρ) p (Fx ρ 4 c w) ∈
      Submodule.span ℂ {v | ∃ f, BoxP N f ∧ Finsupp.weight om f = n ∧
        v = Sl2Weyl.evAlg (fun k => ρ.op 5 k) (fθ_comm ρ) (MvPolynomial.monomial f 1) (Fx ρ 4 c w)} ⊔
      Sθ ρ w c.sum := by
  refine box_mod (fun k => ρ.op 5 k) (fθ_comm ρ) (E1 := ρ.op 2 1)
    (H := fun k => ρ.op 6 k + ρ.op 7 k) (fun k => ?_) (fun m k => ?_) _ (fun k => Sθ_fθ _ k)
    (Sθ_eθ hR _) (fun m => Sθ_hθ hR _ m) ?_ (fun m => ?_) N (G0 hR c) hp
  · rw [c_eθf5, add_comm 1 k]; abel
  · rw [add_mul, mul_add, (c_h1 ρ (m + 1) k).2.1, (c_h2 ρ (m + 1) k).2.1]
    rw [show (-2 : ℂ) • ρ.op 5 (m + 1 + k) = (-1 : ℂ) • ρ.op 5 (m + 1 + k) + (-1 : ℂ) • ρ.op 5 (m + 1 + k)
      by rw [← add_smul]; norm_num]
    abel
  · rw [eθ_f2w hR 1 c]; exact Submodule.zero_mem _
  · have h := hθ_nw hR (m + 1) [] [] c
    refine NW_mono (fun a' b' c' hr => ?_) h
    obtain ⟨ha, hb, _, _, _, _, hsum⟩ := hr
    rw [List.length_nil, List.length_eq_zero_iff] at ha hb
    subst ha hb
    simp only [σ, List.length_nil, List.sum_nil] at hsum ⊢; omega

end Theta

end

end VOA.DeligneAudit.CLNormal

section AxiomAudit
#print axioms VOA.DeligneAudit.CLNormal.Sub_le_FSub
#print axioms VOA.DeligneAudit.CLNormal.G0
#print axioms VOA.DeligneAudit.CLNormal.theta_box
end AxiomAudit
