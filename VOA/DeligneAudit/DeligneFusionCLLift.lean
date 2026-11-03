import VOA.DeligneAudit.DeligneFusionCLNormal

/-!
# The degree–weight lift of a current module

`CurrentModule` modules are not assumed graded.  To project onto a fixed `t`-degree and weight we lift a
module `V` to `Ṽ = (ℕ × ℤ²) →₀ V`, where `x ⊗ tᵏ` moves the key by `(k, wt x)`.  The bracket table is
weight-additive (`table_gw`), so `Ṽ` is again a module (`liftRep`), `w̃ = single 0 w` satisfies the same
relations (`mabRel_lift`), a normal word of `w̃` is a single-key vector (`nw_lift`), and the coordinate
projection `proj K` cuts every span of normal words down to the words of key `K` (`proj_NW`).
`evD d` evaluates back to `V` in degree `d`.
-/

namespace VOA.DeligneAudit.CLLift

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CLNormal

noncomputable section

/-- The root-lattice weight of a generator (`e₁, e₂, e_θ, f₁, f₂, f_θ, h₁, h₂`). -/
def gw : Fin 8 → ℤ × ℤ := ![(1, 0), (0, 1), (1, 1), (-1, 0), (0, -1), (-1, -1), (0, 0), (0, 0)]

set_option maxHeartbeats 4000000 in
/-- The bracket table is weight-additive. -/
theorem table_gw (a b e : Fin 8) (h : bracketTable a b e ≠ 0) : gw e = gw a + gw b := by
  fin_cases a <;> fin_cases b <;> fin_cases e <;> simp_all [bracketTable, gw] <;> decide

/-- Keys: `t`-degree and weight. -/
abbrev Kt := ℕ × (ℤ × ℤ)

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V)

/-- The lifted operator `x ⊗ tᵏ`. -/
def liftOp (c : Fin 8) (k : ℕ) : (Kt →₀ V) →ₗ[ℂ] (Kt →₀ V) :=
  Finsupp.lmapDomain V ℂ (fun p : Kt => p + (k, gw c)) ∘ₗ Finsupp.mapRange.linearMap (ρ.op c k)

theorem liftOp_single (c : Fin 8) (k : ℕ) (p : Kt) (v : V) :
    liftOp ρ c k (Finsupp.single p v) = Finsupp.single (p + (k, gw c)) (ρ.op c k v) := by
  simp [liftOp]

/-- The lifted current module. -/
def liftRep : CurrentModule (bracketTable) (Kt →₀ V) where
  op := liftOp ρ
  comm := by
    intro a b r s f
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
        simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib, smul_add] at hf hg ⊢
        rw [← hf, ← hg]; abel
    | single p v =>
        rw [liftOp_single, liftOp_single, liftOp_single, liftOp_single]
        have k1 : p + (s, gw b) + (r, gw a) = p + (r + s, gw a + gw b) := by
          ext <;> simp <;> ring
        have k2 : p + (r, gw a) + (s, gw b) = p + (r + s, gw a + gw b) := by
          ext <;> simp <;> ring
        rw [k1, k2, ← Finsupp.single_sub, ρ.comm a b r s v, Finsupp.single_finset_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [liftOp_single, ← Finsupp.smul_single]
        by_cases h : bracketTable a b e = 0
        · simp [h]
        · rw [table_gw a b e h]

@[simp] theorem liftRep_op (c : Fin 8) (k : ℕ) : (liftRep ρ).op c k = liftOp ρ c k := rfl

theorem iterate_single (c : Fin 8) (k : ℕ) (p : Kt) (v : V) : ∀ n,
    (liftOp ρ c k)^[n] (Finsupp.single p v) =
      Finsupp.single (p + n • ((k, gw c) : Kt)) ((ρ.op c k)^[n] v)
  | 0 => by simp
  | n + 1 => by
      rw [Function.iterate_succ_apply', iterate_single c k p v n, liftOp_single,
        Function.iterate_succ_apply', succ_nsmul, add_assoc]

/-- The lift of `w`. -/
def wl (w : V) : Kt →₀ V := Finsupp.single 0 w

theorem mabRel_lift {w : V} {a b : ℕ} (h : MabRel ρ w a b) : MabRel (liftRep ρ) (wl w) a b where
  raising e he r := by simp [wl, liftOp_single, h.raising e he r]
  cartan_pos hh h6 r hr := by simp [wl, liftOp_single, h.cartan_pos hh h6 r hr]
  cartan_zero hh h6 := by
    have hg : gw hh = 0 := by
      have : hh = 6 ∨ hh = 7 := by omega
      rcases this with rfl | rfl <;> rfl
    simp [wl, liftOp_single, h.cartan_zero hh h6, hg, Finsupp.smul_single]
    rfl
  lowering_f1 := by simp [wl, iterate_single, h.lowering_f1]
  lowering_f2 := by simp [wl, iterate_single, h.lowering_f2]
  trunc_f1 := by simp [wl, liftOp_single, h.trunc_f1]
  trunc_f2 := by simp [wl, liftOp_single, h.trunc_f2]
  trunc_theta := by simp [wl, liftOp_single, h.trunc_theta]

theorem Fx_lift (d : Fin 8) (p : Kt) (v : V) : ∀ l : List ℕ,
    Fx (liftRep ρ) d l (Finsupp.single p v) =
      Finsupp.single (p + (l.sum, (l.length : ℤ) • gw d)) (Fx ρ d l v)
  | [] => by
      rw [Fx_nil, Module.End.one_apply, Fx_nil, Module.End.one_apply]; congr 1; ext <;> simp
  | (s :: l) => by
      rw [Fx_cons, Module.End.mul_apply, Fx_lift d p v l, liftRep_op, liftOp_single, Fx_cons,
        Module.End.mul_apply]
      congr 1
      ext <;> simp [add_smul] <;> ring

/-- The key of the normal word `f₁(a) f_θ(b) f₂(c)`. -/
def keyT (a b c : List ℕ) : Kt :=
  (a.sum + b.sum + c.sum, ((a.length : ℤ) • gw 3 + (b.length : ℤ) • gw 5 + (c.length : ℤ) • gw 4))

theorem keyT_eq {a b c a' b' c' : List ℕ} (h : keyT a b c = keyT a' b' c') :
    a.sum + b.sum + c.sum = a'.sum + b'.sum + c'.sum ∧ a.length + b.length = a'.length + b'.length ∧
      b.length + c.length = b'.length + c'.length := by
  simp only [keyT, gw, Prod.ext_iff] at h
  simp at h
  omega

theorem nw_lift (w : V) (a b c : List ℕ) :
    nw (liftRep ρ) (wl w) a b c = Finsupp.single (keyT a b c) (nw ρ w a b c) := by
  simp only [nw, wl, Fx_lift]
  congr 1
  ext <;> simp [keyT] <;> ring

/-- The coordinate projection onto key `K`. -/
def proj (K : Kt) : (Kt →₀ V) →ₗ[ℂ] (Kt →₀ V) := Finsupp.lsingle K ∘ₗ Finsupp.lapply K

theorem proj_single (K p : Kt) (v : V) :
    proj K (Finsupp.single p v) = if p = K then Finsupp.single p v else 0 := by
  simp only [proj, LinearMap.coe_comp, Function.comp_apply, Finsupp.lapply_apply,
    Finsupp.lsingle_apply, Finsupp.single_apply]
  split_ifs with h
  · subst h; rfl
  · simp

theorem proj_nw (w : V) (a b c : List ℕ) :
    proj (keyT a b c) (nw (liftRep ρ) (wl w) a b c) = nw (liftRep ρ) (wl w) a b c := by
  rw [nw_lift, proj_single, if_pos rfl]

/-- The projection onto key `K` cuts a span of normal words down to the words of key `K`. -/
theorem proj_NW (w : V) (K : Kt) {P : List ℕ → List ℕ → List ℕ → Prop} {x : Kt →₀ V}
    (hx : x ∈ NW (liftRep ρ) (wl w) P) :
    proj K x ∈ NW (liftRep ρ) (wl w) (fun a b c => P a b c ∧ keyT a b c = K) :=
  map_NW _ (fun a b c hp => by
    rw [nw_lift, proj_single]
    split_ifs with h
    · rw [← nw_lift]; exact nw_mem ⟨hp, h⟩
    · exact Submodule.zero_mem _) hx

/-- Evaluation back to `V` in degree `d`. -/
def evD (d : ℕ) : (Kt →₀ V) →ₗ[ℂ] V :=
  Finsupp.lsum ℂ (fun p : Kt => if p.1 = d then LinearMap.id else 0)

theorem evD_single (d : ℕ) (p : Kt) (v : V) :
    evD d (Finsupp.single p v) = if p.1 = d then v else 0 := by
  simp only [evD, Finsupp.lsum_single]
  split_ifs <;> simp

end

end VOA.DeligneAudit.CLLift
