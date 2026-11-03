import VOA.DeligneAudit.DeligneFusionECalc

/-!
# Normal words `f₁(a) f_θ(b) f₂(c) w` and how the `sl₃[t]` operators act on them

For a module with `MabRel ρ w N 0`, the *normal word* `nw a b c = f₁(a) f_θ(b) f₂(c) w` (`f₂` acts first).
This file records, with exact bookkeeping of lengths and mode sums, what each operator does to a normal
word (all statements are span memberships, proved by pushing the operator through the three blocks):

* `fθ_nw`, `f1_nw`: `f_θ`, `f₁` just prepend a letter;
* `shift_nw`: a Cartan-type operator (`h₁`, `h₂`, `h_θ`) shifts one mode by `k` (lengths fixed, sums grow);
* `e1_nw`: `e₁ ⊗ tᵏ` either lowers `#f_θ` or keeps all lengths with larger sums (CL Lemma 3.2.1 (ii));
* `e2_nw`, `eθ_nw`: with `σ(a, c) = |a| + Σa + Σc`, `e₂ ⊗ tᵐ` (`m ≥ 1`) raises `σ` by at least `m`, and
  `e_θ ⊗ tᵐ` (`m ≥ 1`) does not lower it (the bookkeeping behind CL Lemma 3.5.1 / 3.6.2);
* `f2_nw`: `f₂` keeps normal form (`[f₂, f₁] = f_θ`), preserving the total degree;
* `uword_eq_nw`: a `u`-word applied to `w` is a normal word with the same index;
* `Sub_le_FSub`: CL's filtration piece `Sub_{>j}` lies in the span of normal words of index `> j`.
-/

namespace VOA.DeligneAudit.CLNormal

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CLFilt

noncomputable section

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V)

/-! ## Blocks -/

/-- The block `op d s₁ ⋯ op d s_n` (the last mode acts first). -/
def Fx (d : Fin 8) : List ℕ → Module.End ℂ V
  | [] => 1
  | (s :: l) => ρ.op d s * Fx d l

@[simp] theorem Fx_nil (d : Fin 8) : Fx ρ d [] = 1 := rfl

@[simp] theorem Fx_cons (d : Fin 8) (s : ℕ) (l : List ℕ) : Fx ρ d (s :: l) = ρ.op d s * Fx ρ d l := rfl

theorem Fx_append (d : Fin 8) (l l' : List ℕ) : Fx ρ d (l ++ l') = Fx ρ d l * Fx ρ d l' := by
  induction l with
  | nil => simp
  | cons s l ih => simp [ih, mul_assoc]

theorem wordOp_map (d : Fin 8) : ∀ (l : List ℕ) (v : V),
    wordOp ρ (l.map fun s => (d, s)) v = Fx ρ d l v
  | [], _ => rfl
  | (s :: l), v => by
      change ρ.op d s (wordOp ρ (l.map fun s => (d, s)) v) = _
      rw [wordOp_map d l v]; rfl

/-- The operator commutation `[op x r, op y s] = ∑ₑ c_{xy}^e op e (r+s)`. -/
theorem opc (x y : Fin 8) (r s : ℕ) :
    ρ.op x r * ρ.op y s = ρ.op y s * ρ.op x r + ∑ e, bracketTable x y e • ρ.op e (r + s) := by
  ext v
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.coeFn_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  rw [comm_apply x y r s v]

/-- Pushing an operator `D` through a block, with `[D, op d s] = C s`. -/
theorem push (d : Fin 8) (D : Module.End ℂ V) (C : ℕ → Module.End ℂ V)
    (h : ∀ s, D * ρ.op d s = ρ.op d s * D + C s) :
    ∀ (l : List ℕ) (v : V) (M : Submodule ℂ V), Fx ρ d l (D v) ∈ M →
      (∀ l1 s l2, l = l1 ++ s :: l2 → Fx ρ d l1 (C s (Fx ρ d l2 v)) ∈ M) → D (Fx ρ d l v) ∈ M
  | [], v, M, hD, _ => by simpa using hD
  | (s :: l), v, M, hD, hC => by
      have e1 : D (Fx ρ d (s :: l) v) = ρ.op d s (D (Fx ρ d l v)) + C s (Fx ρ d l v) := by
        rw [Fx_cons, Module.End.mul_apply, ← Module.End.mul_apply D, h]; rfl
      rw [e1]
      refine M.add_mem ?_ (by simpa using hC [] s l rfl)
      have := push d D C h l v (M.comap (ρ.op d s)) (by simpa using hD) (fun l1 s' l2 hl => by
        have := hC (s :: l1) s' l2 (by rw [hl]; rfl)
        simpa using this)
      exact this

/-- A commuting operator passes through a block. -/
theorem comm_block (d : Fin 8) (D : Module.End ℂ V) (h : ∀ s, D * ρ.op d s = ρ.op d s * D) :
    ∀ l, D * Fx ρ d l = Fx ρ d l * D
  | [] => by simp
  | (s :: l) => by rw [Fx_cons, ← mul_assoc, h, mul_assoc, comm_block d D h l, mul_assoc]

theorem comm_block_apply (d : Fin 8) (D : Module.End ℂ V) (h : ∀ s, D * ρ.op d s = ρ.op d s * D)
    (l : List ℕ) (v : V) : D (Fx ρ d l v) = Fx ρ d l (D v) := by
  rw [← Module.End.mul_apply, comm_block ρ d D h l, Module.End.mul_apply]

/-- Shift through a block: `[D, op d s] = α · op d (k+s)` and `D v = β v` (`β = 0` if `k ≥ 1`). -/
theorem shift_block (d : Fin 8) (D : Module.End ℂ V) (α β : ℂ) (k : ℕ)
    (h : ∀ s, D * ρ.op d s = ρ.op d s * D + α • ρ.op d (k + s)) (v : V) (hv : D v = β • v)
    (hk : 1 ≤ k → β = 0) (l : List ℕ) :
    D (Fx ρ d l v) ∈ Submodule.span ℂ {x | ∃ l' : List ℕ, l'.length = l.length ∧ l'.sum = l.sum + k ∧
      x = Fx ρ d l' v} := by
  refine push ρ d D _ h l v _ ?_ ?_
  · rw [hv, map_smul]
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl, by simp, rfl⟩)
    · rw [hk hk1, zero_smul]; exact Submodule.zero_mem _
  · rintro l1 s l2 rfl
    rw [LinearMap.smul_apply, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨l1 ++ (k + s) :: l2, by simp, ?_, ?_⟩)
    · simp; ring
    · rw [Fx_append, Fx_cons, Module.End.mul_apply, Module.End.mul_apply]

/-! ## Normal words -/

variable (w : V)

/-- The normal word `f₁(a) f_θ(b) f₂(c) w`. -/
def nw (a b c : List ℕ) : V := Fx ρ 3 a (Fx ρ 5 b (Fx ρ 4 c w))

/-- The span of normal words satisfying `P`. -/
def NW (P : List ℕ → List ℕ → List ℕ → Prop) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ a b c, P a b c ∧ v = nw ρ w a b c}

variable {ρ w}

theorem nw_mem {P : List ℕ → List ℕ → List ℕ → Prop} {a b c : List ℕ} (h : P a b c) :
    nw ρ w a b c ∈ NW ρ w P :=
  Submodule.subset_span ⟨a, b, c, h, rfl⟩

theorem NW_mono {P Q : List ℕ → List ℕ → List ℕ → Prop} (h : ∀ a b c, P a b c → Q a b c) :
    NW ρ w P ≤ NW ρ w Q :=
  Submodule.span_mono fun _ ⟨a, b, c, hp, hv⟩ => ⟨a, b, c, h a b c hp, hv⟩

/-- A linear map sending generators to generators maps the span. -/
theorem map_NW (T : Module.End ℂ V) {P Q : List ℕ → List ℕ → List ℕ → Prop}
    (h : ∀ a b c, P a b c → T (nw ρ w a b c) ∈ NW ρ w Q) {x : V} (hx : x ∈ NW ρ w P) :
    T x ∈ NW ρ w Q := by
  have : NW ρ w P ≤ (NW ρ w Q).comap T := by
    rw [NW, Submodule.span_le]
    rintro _ ⟨a, b, c, hp, rfl⟩
    exact h a b c hp
  exact this hx

theorem Fx3_nw (a1 a b c : List ℕ) : Fx ρ 3 a1 (nw ρ w a b c) = nw ρ w (a1 ++ a) b c := by
  simp [nw, Fx_append, Module.End.mul_apply]

/-- Prefixing `f₁(a₁)` maps `NW P` into `NW Q`. -/
theorem Fx3_NW (a1 : List ℕ) {P Q : List ℕ → List ℕ → List ℕ → Prop}
    (h : ∀ a b c, P a b c → Q (a1 ++ a) b c) {x : V} (hx : x ∈ NW ρ w P) :
    Fx ρ 3 a1 x ∈ NW ρ w Q :=
  map_NW _ (fun a b c hp => by rw [Fx3_nw]; exact nw_mem (h a b c hp)) hx

/-! ## Commutators of `sl₃` used below -/

section Comm

variable (ρ)

theorem c_f1f5 (r s : ℕ) : ρ.op 3 r * ρ.op 5 s = ρ.op 5 s * ρ.op 3 r := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

theorem c_f5f3 (r s : ℕ) : ρ.op 5 r * ρ.op 3 s = ρ.op 3 s * ρ.op 5 r := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

theorem c_f4f5 (r s : ℕ) : ρ.op 4 r * ρ.op 5 s = ρ.op 5 s * ρ.op 4 r := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

theorem c_f4f3 (r s : ℕ) : ρ.op 4 r * ρ.op 3 s = ρ.op 3 s * ρ.op 4 r + ρ.op 5 (r + s) := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

theorem c_e1f3 (r s : ℕ) : ρ.op 0 r * ρ.op 3 s = ρ.op 3 s * ρ.op 0 r + ρ.op 6 (r + s) := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

theorem c_e1f5 (r s : ℕ) : ρ.op 0 r * ρ.op 5 s = ρ.op 5 s * ρ.op 0 r + (-1 : ℂ) • ρ.op 4 (r + s) := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

theorem c_e1f4 (r s : ℕ) : ρ.op 0 r * ρ.op 4 s = ρ.op 4 s * ρ.op 0 r := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

theorem c_e2f3 (r s : ℕ) : ρ.op 1 r * ρ.op 3 s = ρ.op 3 s * ρ.op 1 r := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

theorem c_e2f5 (r s : ℕ) : ρ.op 1 r * ρ.op 5 s = ρ.op 5 s * ρ.op 1 r + ρ.op 3 (r + s) := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

theorem c_e2f4 (r s : ℕ) : ρ.op 1 r * ρ.op 4 s = ρ.op 4 s * ρ.op 1 r + ρ.op 7 (r + s) := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

theorem c_eθf3 (r s : ℕ) : ρ.op 2 r * ρ.op 3 s = ρ.op 3 s * ρ.op 2 r + (-1 : ℂ) • ρ.op 1 (r + s) := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

theorem c_eθf5 (r s : ℕ) :
    ρ.op 2 r * ρ.op 5 s = ρ.op 5 s * ρ.op 2 r + (ρ.op 6 (r + s) + ρ.op 7 (r + s)) := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

theorem c_eθf4 (r s : ℕ) : ρ.op 2 r * ρ.op 4 s = ρ.op 4 s * ρ.op 2 r + ρ.op 0 (r + s) := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

theorem c_h1 (r s : ℕ) :
    ρ.op 6 r * ρ.op 3 s = ρ.op 3 s * ρ.op 6 r + (-2 : ℂ) • ρ.op 3 (r + s) ∧
    ρ.op 6 r * ρ.op 5 s = ρ.op 5 s * ρ.op 6 r + (-1 : ℂ) • ρ.op 5 (r + s) ∧
    ρ.op 6 r * ρ.op 4 s = ρ.op 4 s * ρ.op 6 r + (1 : ℂ) • ρ.op 4 (r + s) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [opc] <;> simp [Fin.sum_univ_eight, bracketTable]

theorem c_h2 (r s : ℕ) :
    ρ.op 7 r * ρ.op 3 s = ρ.op 3 s * ρ.op 7 r + (1 : ℂ) • ρ.op 3 (r + s) ∧
    ρ.op 7 r * ρ.op 5 s = ρ.op 5 s * ρ.op 7 r + (-1 : ℂ) • ρ.op 5 (r + s) ∧
    ρ.op 7 r * ρ.op 4 s = ρ.op 4 s * ρ.op 7 r + (-2 : ℂ) • ρ.op 4 (r + s) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [opc] <;> simp [Fin.sum_univ_eight, bracketTable]

end Comm

/-! ## Lowering operators -/

theorem f1_nw (k : ℕ) (a b c : List ℕ) : ρ.op 3 k (nw ρ w a b c) = nw ρ w (k :: a) b c := rfl

theorem fθ_nw (k : ℕ) (a b c : List ℕ) : ρ.op 5 k (nw ρ w a b c) = nw ρ w a (k :: b) c := by
  simp only [nw]
  rw [← Module.End.mul_apply (ρ.op 5 k), comm_block ρ 3 _ (fun s => c_f5f3 ρ k s) a]
  rfl

/-- `f₂` keeps the normal form: `f₂(k)·nw a b c` is a combination of normal words with the same
total length shape (`|a'| + |b'| = |a| + |b|`, `|b'| + |c'| = |b| + |c| + 1`) and total degree `+ k`. -/
theorem f2_nw (k : ℕ) (a b c : List ℕ) :
    ρ.op 4 k (nw ρ w a b c) ∈ NW ρ w (fun a' b' c' => a'.length + b'.length = a.length + b.length ∧
      b'.length + c'.length = b.length + c.length + 1 ∧
      a'.sum + b'.sum + c'.sum = a.sum + b.sum + c.sum + k) := by
  refine push ρ 3 (ρ.op 4 k) (fun s => ρ.op 5 (k + s)) (fun s => c_f4f3 ρ k s) a _ _ ?_ ?_
  · rw [← Module.End.mul_apply (ρ.op 4 k), comm_block ρ 5 _ (fun s => c_f4f5 ρ k s) b]
    exact nw_mem (a := a) (b := b) (c := k :: c) ⟨rfl, by simp; ring, by simp; try ring⟩
  · rintro a1 s a2 rfl
    have : Fx ρ 3 a1 (ρ.op 5 (k + s) (Fx ρ 3 a2 (Fx ρ 5 b (Fx ρ 4 c w)))) =
        nw ρ w (a1 ++ a2) ((k + s) :: b) c := by
      rw [← Module.End.mul_apply (ρ.op 5 (k + s)), comm_block ρ 3 _ (fun t => c_f5f3 ρ (k + s) t) a2]
      simp [nw, Fx_append, Module.End.mul_apply]
    rw [this]
    exact nw_mem ⟨by simp; ring, by simp; ring, by simp; try ring⟩

/-! ## Cartan-type operators shift one mode -/

/-- The shift relation: equal lengths, sums grow, total sum grows by `k`. -/
def ShiftRel (k : ℕ) (a b c a' b' c' : List ℕ) : Prop :=
  a'.length = a.length ∧ b'.length = b.length ∧ c'.length = c.length ∧ a.sum ≤ a'.sum ∧
    b.sum ≤ b'.sum ∧ c.sum ≤ c'.sum ∧ a'.sum + b'.sum + c'.sum = a.sum + b.sum + c.sum + k

/-- A Cartan-type operator shifts one mode of a normal word by `k`. -/
theorem shift_nw (D : Module.End ℂ V) (α3 α5 α4 β : ℂ) (k : ℕ)
    (h3 : ∀ s, D * ρ.op 3 s = ρ.op 3 s * D + α3 • ρ.op 3 (k + s))
    (h5 : ∀ s, D * ρ.op 5 s = ρ.op 5 s * D + α5 • ρ.op 5 (k + s))
    (h4 : ∀ s, D * ρ.op 4 s = ρ.op 4 s * D + α4 • ρ.op 4 (k + s))
    (hw : D w = β • w) (hk : 1 ≤ k → β = 0) (a b c : List ℕ) :
    D (nw ρ w a b c) ∈ NW ρ w (ShiftRel k a b c) := by
  refine push ρ 3 D _ h3 a _ _ ?_ ?_
  · refine push ρ 5 D _ h5 b _ ((NW ρ w (ShiftRel k a b c)).comap (Fx ρ 3 a)) ?_ ?_
    · refine push ρ 4 D _ h4 c _ (((NW ρ w (ShiftRel k a b c)).comap (Fx ρ 3 a)).comap (Fx ρ 5 b)) ?_ ?_
      · simp only [Submodule.mem_comap]
        rw [hw, map_smul, map_smul, map_smul]
        rcases Nat.eq_zero_or_pos k with rfl | hk1
        · exact Submodule.smul_mem _ _ (nw_mem ⟨rfl, rfl, rfl, le_rfl, le_rfl, le_rfl, by simp⟩)
        · rw [hk hk1, zero_smul]; exact Submodule.zero_mem _
      · rintro c1 s c2 rfl
        simp only [Submodule.mem_comap, LinearMap.smul_apply, map_smul]
        refine Submodule.smul_mem _ _ ?_
        have : Fx ρ 3 a (Fx ρ 5 b (Fx ρ 4 c1 (ρ.op 4 (k + s) (Fx ρ 4 c2 w)))) =
            nw ρ w a b (c1 ++ (k + s) :: c2) := by simp [nw, Fx_append, Module.End.mul_apply]
        rw [this]; exact nw_mem ⟨rfl, rfl, by simp, le_rfl, le_rfl, by simp; try omega, by simp; try ring⟩
    · rintro b1 s b2 rfl
      simp only [Submodule.mem_comap, LinearMap.smul_apply, map_smul]
      refine Submodule.smul_mem _ _ ?_
      have : Fx ρ 3 a (Fx ρ 5 b1 (ρ.op 5 (k + s) (Fx ρ 5 b2 (Fx ρ 4 c w)))) =
          nw ρ w a (b1 ++ (k + s) :: b2) c := by simp [nw, Fx_append, Module.End.mul_apply]
      rw [this]; exact nw_mem ⟨rfl, by simp, rfl, le_rfl, by simp; try omega, le_rfl, by simp; try ring⟩
  · rintro a1 s a2 rfl
    rw [LinearMap.smul_apply, map_smul]
    refine Submodule.smul_mem _ _ ?_
    have : Fx ρ 3 a1 (ρ.op 3 (k + s) (Fx ρ 3 a2 (Fx ρ 5 b (Fx ρ 4 c w)))) =
        nw ρ w (a1 ++ (k + s) :: a2) b c := by simp [nw, Fx_append, Module.End.mul_apply]
    rw [this]; exact nw_mem ⟨by simp, rfl, rfl, by simp; try omega, le_rfl, le_rfl, by simp; try ring⟩

variable {N : ℕ} (hR : MabRel ρ w N 0)
include hR

/-- `D w = β w` for a Cartan mode, with `β = 0` in positive degree. -/
theorem cartan_w (hh : Fin 8) (hh6 : 6 ≤ hh.val) (k : ℕ) :
    ρ.op hh k w = (if k = 0 then (N : ℂ) else 0) • w := by
  split_ifs with hk
  · subst hk; simpa using hR.cartan_zero hh hh6
  · rw [zero_smul]; exact hR.cartan_pos hh hh6 k (by omega)

theorem h1_nw (k : ℕ) (a b c : List ℕ) : ρ.op 6 k (nw ρ w a b c) ∈ NW ρ w (ShiftRel k a b c) :=
  shift_nw _ (-2) (-1) 1 _ k (fun s => (c_h1 ρ k s).1) (fun s => (c_h1 ρ k s).2.1)
    (fun s => (c_h1 ρ k s).2.2) (cartan_w hR 6 (by decide) k) (fun hk => by simp; omega) a b c

theorem h2_nw (k : ℕ) (a b c : List ℕ) : ρ.op 7 k (nw ρ w a b c) ∈ NW ρ w (ShiftRel k a b c) :=
  shift_nw _ 1 (-1) (-2) _ k (fun s => (c_h2 ρ k s).1) (fun s => (c_h2 ρ k s).2.1)
    (fun s => (c_h2 ρ k s).2.2) (cartan_w hR 7 (by decide) k) (fun hk => by simp; omega) a b c

/-- `h_θ = h₁ + h₂`. -/
theorem hθ_nw (k : ℕ) (a b c : List ℕ) :
    (ρ.op 6 k + ρ.op 7 k) (nw ρ w a b c) ∈ NW ρ w (ShiftRel k a b c) := by
  rw [LinearMap.add_apply]; exact Submodule.add_mem _ (h1_nw hR k a b c) (h2_nw hR k a b c)

theorem e_w {e : Fin 8} (he : e.val < 3) (k : ℕ) : ρ.op e k w = 0 := hR.raising e he k

/-! ## Raising operators -/

/-- **`e₁ ⊗ tᵏ` on a normal word** (CL Lemma 3.2.1 (ii)): every term either has fewer `f_θ` letters,
or the same `f_θ`, `f₂` lengths and larger-or-equal mode sums. -/
theorem e1_nw (k : ℕ) (a b c : List ℕ) :
    ρ.op 0 k (nw ρ w a b c) ∈ NW ρ w (fun _ b' c' => b'.length < b.length ∨
      (b'.length = b.length ∧ c'.length = c.length ∧ b.sum ≤ b'.sum ∧ c.sum ≤ c'.sum)) := by
  set M := NW ρ w (fun _ b' c' => b'.length < b.length ∨
      (b'.length = b.length ∧ c'.length = c.length ∧ b.sum ≤ b'.sum ∧ c.sum ≤ c'.sum))
  refine push ρ 3 (ρ.op 0 k) _ (fun s => c_e1f3 ρ k s) a _ M ?_ ?_
  · refine push ρ 5 (ρ.op 0 k) _ (fun s => c_e1f5 ρ k s) b _ (M.comap (Fx ρ 3 a)) ?_ ?_
    · rw [← Module.End.mul_apply (ρ.op 0 k), comm_block ρ 4 _ (fun s => c_e1f4 ρ k s) c,
        Module.End.mul_apply, e_w hR (by decide) k]
      simp
    · rintro b1 s b2 rfl
      simp only [Submodule.mem_comap, LinearMap.smul_apply, map_smul]
      refine Submodule.smul_mem _ _ ?_
      have : Fx ρ 3 a (Fx ρ 5 b1 (ρ.op 4 (k + s) (Fx ρ 5 b2 (Fx ρ 4 c w)))) =
          nw ρ w a (b1 ++ b2) ((k + s) :: c) := by
        rw [← Module.End.mul_apply (ρ.op 4 (k + s)), comm_block ρ 5 _ (fun t => c_f4f5 ρ (k + s) t) b2]
        simp [nw, Fx_append, Module.End.mul_apply]
      rw [this]; exact nw_mem (Or.inl (by simp))
  · rintro a1 s a2 rfl
    have h1 := h1_nw hR (k + s) a2 b c
    exact Fx3_NW a1 (fun a' b' c' ⟨_, hb, hc, _, hbs, hcs, _⟩ => Or.inr ⟨hb, hc, hbs, hcs⟩) h1

/-- The `σ`-statistic `|a| + Σa + Σc`. -/
def σ (a c : List ℕ) : ℕ := a.length + a.sum + c.sum

omit hR in
theorem nw_nil_nil (c : List ℕ) : nw ρ w [] [] c = Fx ρ 4 c w := rfl

/-- `e₂ ⊗ tᵐ` (`m ≥ 1`) raises `σ` by at least `m`. -/
theorem e2_nw (m : ℕ) (hm : 1 ≤ m) (a b c : List ℕ) :
    ρ.op 1 m (nw ρ w a b c) ∈ NW ρ w (fun a' _ c' => σ a c + m ≤ σ a' c') := by
  set M := NW ρ w (fun a' _ c' => σ a c + m ≤ σ a' c')
  refine push ρ 3 (ρ.op 1 m) (fun _ => 0) (fun s => by rw [add_zero]; exact c_e2f3 ρ m s) a _ M ?_
    (fun _ _ _ _ => by simp)
  refine push ρ 5 (ρ.op 1 m) _ (fun s => c_e2f5 ρ m s) b _ (M.comap (Fx ρ 3 a)) ?_ ?_
  · refine push ρ 4 (ρ.op 1 m) _ (fun s => c_e2f4 ρ m s) c _ ((M.comap (Fx ρ 3 a)).comap (Fx ρ 5 b))
      (by rw [e_w hR (by decide) m]; simp) ?_
    rintro c1 s c2 rfl
    simp only [Submodule.mem_comap]
    have h2 := h2_nw hR (m + s) [] [] c2
    rw [nw_nil_nil] at h2
    refine map_NW (Fx ρ 3 a * Fx ρ 5 b * Fx ρ 4 c1) (fun a' b' c' hr => ?_) h2
    obtain ⟨ha, hb, hc, _, _, _, hsum⟩ := hr
    rw [List.length_nil, List.length_eq_zero_iff] at ha hb
    subst ha hb
    have : (Fx ρ 3 a * Fx ρ 5 b * Fx ρ 4 c1) (nw ρ w [] [] c') = nw ρ w a b (c1 ++ c') := by
      simp [nw, Fx_append, Module.End.mul_apply]
    rw [this]; refine nw_mem ?_
    simp only [σ, List.sum_append, List.sum_cons, List.sum_nil] at hsum ⊢; omega
  · rintro b1 s b2 rfl
    simp only [Submodule.mem_comap]
    have : Fx ρ 3 a (Fx ρ 5 b1 (ρ.op 3 (m + s) (Fx ρ 5 b2 (Fx ρ 4 c w)))) =
        nw ρ w (a ++ [m + s]) (b1 ++ b2) c := by
      rw [← comm_block_apply ρ 5 _ (fun t => c_f1f5 ρ (m + s) t) b1]
      simp [nw, Fx_append, Module.End.mul_apply]
    rw [this]; refine nw_mem ?_
    simp only [σ, List.length_append, List.sum_append, List.length_cons, List.length_nil,
      List.sum_cons, List.sum_nil]; omega

/-- `e_θ ⊗ tᵐ` (`m ≥ 1`) does not lower `σ`. -/
theorem eθ_nw (m : ℕ) (hm : 1 ≤ m) (a b c : List ℕ) :
    ρ.op 2 m (nw ρ w a b c) ∈ NW ρ w (fun a' _ c' => σ a c ≤ σ a' c') := by
  set M := NW ρ w (fun a' _ c' => σ a c ≤ σ a' c')
  refine push ρ 3 (ρ.op 2 m) _ (fun s => c_eθf3 ρ m s) a _ M ?_ ?_
  · refine push ρ 5 (ρ.op 2 m) _ (fun s => c_eθf5 ρ m s) b _ (M.comap (Fx ρ 3 a)) ?_ ?_
    · refine push ρ 4 (ρ.op 2 m) _ (fun s => c_eθf4 ρ m s) c _ ((M.comap (Fx ρ 3 a)).comap (Fx ρ 5 b))
        (by rw [e_w hR (by decide) m]; simp) ?_
      rintro c1 s c2 rfl
      rw [← Module.End.mul_apply (ρ.op 0 (m + s)), comm_block ρ 4 _ (fun t => c_e1f4 ρ (m + s) t) c2,
        Module.End.mul_apply, e_w hR (by decide) (m + s)]
      simp
    · rintro b1 s b2 rfl
      simp only [Submodule.mem_comap]
      have h := hθ_nw hR (m + s) [] b2 c
      refine map_NW (Fx ρ 3 a * Fx ρ 5 b1) (fun a' b' c' hr => ?_) h
      obtain ⟨ha, _, _, _, _, hc, _⟩ := hr
      rw [List.length_nil, List.length_eq_zero_iff] at ha
      subst ha
      have : (Fx ρ 3 a * Fx ρ 5 b1) (nw ρ w [] b' c') = nw ρ w a (b1 ++ b') c' := by
        simp [nw, Fx_append, Module.End.mul_apply]
      rw [this]; refine nw_mem ?_
      simp only [σ]; omega
  · rintro a1 s a2 rfl
    rw [LinearMap.smul_apply, map_smul]
    refine Submodule.smul_mem _ _ ?_
    have h := e2_nw hR (m + s) (by omega) a2 b c
    refine Fx3_NW a1 (fun a' b' c' hr => ?_) h
    simp only [σ, List.length_append, List.sum_append, List.length_cons, List.sum_cons] at hr ⊢
    omega

/-! ## `u`-words and the filtration -/

/-- The `f_θ`-modes of a word. -/
def uθ : List (Fin 8 × ℕ) → List ℕ
  | [] => []
  | (x :: u) => if x.1 = 5 then x.2 :: uθ u else uθ u

/-- The `f₂`-modes of a word. -/
def u2 : List (Fin 8 × ℕ) → List ℕ
  | [] => []
  | (x :: u) => if x.1 = 4 then x.2 :: u2 u else u2 u

omit hR in
/-- A `u`-word applied to `w` is the normal word of its `f_θ`- and `f₂`-modes. -/
theorem uword_eq_nw : ∀ u : List (Fin 8 × ℕ), (∀ x ∈ u, uLetter x) →
    wordOp ρ u w = nw ρ w [] (uθ u) (u2 u)
  | [], _ => rfl
  | (⟨d, s⟩ :: u), hu => by
      have ih := uword_eq_nw u (fun y hy => hu y (List.mem_cons_of_mem _ hy))
      change ρ.op d s (wordOp ρ u w) = _
      rw [ih]
      rcases hu _ List.mem_cons_self with h | h <;> simp only at h <;> subst h
      · simp only [uθ, u2, show ¬ ((4 : Fin 8) = 5) by decide, if_false, if_true]
        simp only [nw, Fx_nil, Module.End.one_apply, Fx_cons, Module.End.mul_apply]
        rw [comm_block_apply ρ 5 _ (fun t => c_f4f5 ρ s t)]
      · simp only [uθ, u2, show ¬ ((5 : Fin 8) = 4) by decide, if_false, if_true]
        exact fθ_nw s [] _ _

omit [AddCommGroup V] [Module ℂ V] hR in
theorem idx_uword : ∀ u : List (Fin 8 × ℕ), (∀ x ∈ u, uLetter x) →
    idx u = (((uθ u).length, (u2 u).length), ((uθ u).sum, (u2 u).sum))
  | [], _ => rfl
  | (⟨d, s⟩ :: u), hu => by
      have ih := idx_uword u (fun y hy => hu y (List.mem_cons_of_mem _ hy))
      rw [idx_cons, ih]
      rcases hu _ List.mem_cons_self with h | h <;> simp only at h <;> subst h
      · simp [uθ, u2, idxL]; omega
      · simp [uθ, u2, idxL]; omega

/-- The normal words of index higher than `j`. -/
def FSub (j : Idx) : Submodule ℂ V :=
  NW ρ w (fun _ b c => Higher ((b.length, c.length), (b.sum, c.sum)) j)

omit [AddCommGroup V] [Module ℂ V] hR in
theorem higher_mono {j : Idx} {bL cL bS cS bL' cL' bS' cS' : ℕ}
    (h : Higher ((bL, cL), (bS, cS)) j)
    (h' : bL' < bL ∨ (bL' = bL ∧ cL' = cL ∧ bS ≤ bS' ∧ cS ≤ cS')) :
    Higher ((bL', cL'), (bS', cS')) j := by
  obtain ⟨⟨j1, j2⟩, j3, j4⟩ := j
  simp only [Higher, Prod.mk.injEq] at h ⊢
  omega

/-- CL's `W_{>j}` (`Sub`) lies in the span of normal words of index `> j`. -/
theorem Sub_le_FSub (j : Idx) : Sub ρ w (fun i => Higher i j) ≤ FSub (ρ := ρ) (w := w) j := by
  have inv : ∀ (x : Fin 8 × ℕ), g1Letter x → ∀ v ∈ FSub (ρ := ρ) (w := w) j,
      ρ.op x.1 x.2 v ∈ FSub (ρ := ρ) (w := w) j := by
    rintro ⟨d, k⟩ hx v hv
    unfold FSub at hv ⊢
    have h0 : ∀ a b c, Higher ((b.length, c.length), (b.sum, c.sum)) j →
        ρ.op 0 k (nw ρ w a b c) ∈
          NW ρ w (fun _ b c => Higher ((b.length, c.length), (b.sum, c.sum)) j) := fun a b c hp =>
      NW_mono (fun a' b' c' hr => higher_mono hp hr) (e1_nw hR k a b c)
    have h3 : ∀ a b c, Higher ((b.length, c.length), (b.sum, c.sum)) j →
        ρ.op 3 k (nw ρ w a b c) ∈
          NW ρ w (fun _ b c => Higher ((b.length, c.length), (b.sum, c.sum)) j) := fun a b c hp =>
      nw_mem (a := k :: a) hp
    have h6 : ∀ a b c, Higher ((b.length, c.length), (b.sum, c.sum)) j →
        ρ.op 6 k (nw ρ w a b c) ∈
          NW ρ w (fun _ b c => Higher ((b.length, c.length), (b.sum, c.sum)) j) := fun a b c hp =>
      NW_mono (fun a' b' c' hr => higher_mono hp (Or.inr ⟨hr.2.1, hr.2.2.1, hr.2.2.2.2.1,
        hr.2.2.2.2.2.1⟩)) (h1_nw hR k a b c)
    rcases hx with h | h | h <;> simp only at h <;> subst h
    · exact map_NW _ h0 hv
    · exact map_NW _ h3 hv
    · exact map_NW _ h6 hv
  rw [CLFilt.Sub, Submodule.span_le]
  rintro _ ⟨g, u, hg, hu, hP, rfl⟩
  rw [wordOp_append]
  have base : wordOp ρ u w ∈ FSub (ρ := ρ) (w := w) j := by
    rw [uword_eq_nw u hu]; refine nw_mem ?_
    rw [idx_uword u hu] at hP; exact hP
  clear hP
  induction g with
  | nil => exact base
  | cons x g ih =>
      exact inv x (hg x List.mem_cons_self) _ (ih fun y hy => hg y (List.mem_cons_of_mem _ hy))

/-! ## CL Prop. 3.3.3 in the `θ`-direction with `f₂`-modes: `f_θ(0)^{N+1} f₂(c) w` -/

omit hR in
theorem pow_eq_Fx (d : Fin 8) : ∀ k, ρ.op d 0 ^ k = Fx ρ d (List.replicate k 0)
  | 0 => rfl
  | k + 1 => by rw [pow_succ', pow_eq_Fx d k]; rfl

omit hR in
theorem Fw_eq_Fx (d : Fin 8) : ∀ l, ECalc.Fw (fun k => ρ.op d k) l = Fx ρ d l
  | [] => rfl
  | (k :: l) => by simp only [ECalc.Fw, Fx_cons, Fw_eq_Fx d l]

omit hR in
theorem c_h2e2 (p q : ℕ) : ρ.op 7 p * ρ.op 1 q - ρ.op 1 q * ρ.op 7 p = (2 : ℂ) • ρ.op 1 (p + q) := by
  rw [opc]; simp [Fin.sum_univ_eight, bracketTable]

/-- `e₂` raises the `σ`-bound. -/
theorem e2_NW (m : ℕ) (hm : 1 ≤ m) (t : ℕ) {x : V} (hx : x ∈ NW ρ w (fun a' _ c' => t ≤ σ a' c')) :
    ρ.op 1 m x ∈ NW ρ w (fun a' _ c' => t + m ≤ σ a' c') :=
  map_NW _ (fun a b c hp => NW_mono (fun a' b' c' hr => by omega) (e2_nw hR m hm a b c)) hx

omit hR in
/-- `f₁ ⊗ tˢ` raises the `σ`-bound by `s + 1`. -/
theorem f1_NW (s t : ℕ) {x : V} (hx : x ∈ NW ρ w (fun a' _ c' => t ≤ σ a' c')) :
    ρ.op 3 s x ∈ NW ρ w (fun a' _ c' => t + s + 1 ≤ σ a' c') :=
  map_NW _ (fun a b c hp => nw_mem (a := s :: a) (by simp only [σ, List.length_cons, List.sum_cons] at hp ⊢; omega)) hx

/-- The `E₂`-word lemma behind `G0`. -/
theorem G0_aux (q : ℕ) : ∀ l : List ℕ, (∀ s ∈ l, 1 ≤ s) → ∀ n,
    (ρ.op 5 0 ^ n) (ECalc.Ew (fun s => ρ.op 1 s) l ((ρ.op 4 0 ^ q) w)) ∈
        NW ρ w (fun a' _ c' => l.sum ≤ σ a' c') ∧
      (N + 1 ≤ n → (ρ.op 5 0 ^ n) (ECalc.Ew (fun s => ρ.op 1 s) l ((ρ.op 4 0 ^ q) w)) ∈
        NW ρ w (fun a' _ c' => l.sum + 1 ≤ σ a' c'))
  | [], _, n => by
      simp only [ECalc.Ew, Module.End.one_apply, List.sum_nil]
      refine ⟨?_, fun hn => ?_⟩
      · rw [pow_eq_Fx, pow_eq_Fx]
        exact nw_mem (a := []) (by simp)
      · have h := CLGT.prop333 ρ w hR n n (n + q) le_rfl (by omega)
        have hM : CLGT.Mv ρ w n (n + q) n = (ρ.op 5 0 ^ n) ((ρ.op 4 0 ^ q) w) := by
          simp [CLGT.Mv, Module.End.mul_apply, show n + q - n = q by omega]
        rw [hM] at h
        refine (Submodule.span_le.mpr ?_) h
        rintro _ ⟨C', hC', -, -, rfl⟩
        have : CLGT.Mv ρ w n (n + q) C' = nw ρ w (List.replicate (n - C') 0) (List.replicate C' 0)
            (List.replicate (n + q - C') 0) := by
          simp only [CLGT.Mv, nw, pow_eq_Fx, Module.End.mul_apply]
        rw [this]; refine nw_mem ?_
        simp only [σ, List.length_replicate, List.sum_replicate, smul_eq_mul, mul_zero]; omega
  | (s :: l), hl, n => by
      have hs : 1 ≤ s := hl s List.mem_cons_self
      have ih := G0_aux q l (fun t ht => hl t (List.mem_cons_of_mem _ ht))
      set X := ECalc.Ew (fun s => ρ.op 1 s) l ((ρ.op 4 0 ^ q) w)
      have hYX : ρ.op 5 0 * ρ.op 1 s - ρ.op 1 s * ρ.op 5 0 = -ρ.op 3 s := by
        rw [c_e2f5]; simp
      have hYZ : ρ.op 5 0 * -ρ.op 3 s = -ρ.op 3 s * ρ.op 5 0 := by
        rw [mul_neg, neg_mul, c_f5f3]
      have hcp := CLGT.comm_pow hYX hYZ n
      have hexp : (ρ.op 5 0 ^ n) (ECalc.Ew (fun s => ρ.op 1 s) (s :: l) ((ρ.op 4 0 ^ q) w)) =
          ρ.op 1 s ((ρ.op 5 0 ^ n) X) + (-(n : ℂ)) • ρ.op 3 s ((ρ.op 5 0 ^ (n - 1)) X) := by
        simp only [ECalc.Ew, Module.End.mul_apply]
        rw [← Module.End.mul_apply (ρ.op 5 0 ^ n), hcp]
        simp [Module.End.mul_apply, neg_smul]
        rfl
      rw [hexp]
      have t2 : (-(n : ℂ)) • ρ.op 3 s ((ρ.op 5 0 ^ (n - 1)) X) ∈
          NW ρ w (fun a' _ c' => (s :: l).sum + 1 ≤ σ a' c') := by
        refine Submodule.smul_mem _ _ ?_
        have := f1_NW s l.sum (ih (n - 1)).1
        refine NW_mono (fun a' b' c' h => ?_) this
        simp only [List.sum_cons]; omega
      refine ⟨Submodule.add_mem _ ?_ (NW_mono (fun a' b' c' h => by omega) t2),
        fun hn => Submodule.add_mem _ ?_ t2⟩
      · have := e2_NW hR s hs l.sum (ih n).1
        refine NW_mono (fun a' b' c' h => ?_) this
        simp only [List.sum_cons]; omega
      · have := e2_NW hR s hs (l.sum + 1) ((ih n).2 hn)
        refine NW_mono (fun a' b' c' h => ?_) this
        simp only [List.sum_cons]; omega

/-- **`G0`**: `f_θ(0)^{N+1} f₂(c) w` is a combination of normal words with `σ > Σc`
(CL Prop. 3.3.3 transported to arbitrary `f₂`-modes by the `E₂`-calculus). -/
theorem G0 (c : List ℕ) :
    (ρ.op 5 0 ^ (N + 1)) (Fx ρ 4 c w) ∈ NW ρ w (fun a' _ c' => c.sum + 1 ≤ σ a' c') := by
  have hEW := ECalc.fword_mem_EW (E := fun s => ρ.op 1 s) (H := fun p => ρ.op 7 p)
    (F := fun k => ρ.op 4 k) (fun s k => by rw [c_e2f4]; abel)
    (fun p k => by rw [(c_h2 ρ p k).2.2]; abel) (fun p q => c_h2e2 p q)
    (fun i j => CLFilt.f2_comm ρ i j) (y := w) (fun s => e_w hR (by decide) s)
    (fun p hp => hR.cartan_pos 7 (by decide) p hp) c
  rw [Fw_eq_Fx] at hEW
  have : ECalc.EW (fun s => ρ.op 1 s) (fun k => ρ.op 4 k) w c.length c.sum ≤
      (NW ρ w (fun a' _ c' => c.sum + 1 ≤ σ a' c')).comap (ρ.op 5 0 ^ (N + 1)) := by
    rw [ECalc.EW, Submodule.span_le]
    rintro _ ⟨l, hl, hsum, rfl⟩
    have := (G0_aux hR (c.length + l.length) l hl (N + 1)).2 le_rfl
    rw [hsum] at this
    exact this
  exact this hEW

end

end VOA.DeligneAudit.CLNormal
