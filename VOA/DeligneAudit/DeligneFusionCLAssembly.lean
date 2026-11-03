import VOA.DeligneAudit.DeligneFusionCLTheta
import VOA.DeligneAudit.DeligneFusionCLLift
import VOA.DeligneAudit.DeligneFusionCLCount

/-!
# Assembly of the Chari–Loktev spanning theorem `CLSpanning N`

Work in the degree–weight lift `Ṽ` of a module with `MabRel ρ w N 0` (`CLLift`).  Let `CLS` be the span of the
CL words `f₁(a) f_θ(b) f₂(c) w̃` with `(a, b, c)` admissible.  Every normal word lies in `CLS`, by
well-founded induction on CL's order at a fixed key (`nw_mem_CLS`).  One step:

1. `step1` — the `α₂`-box (`alpha2_box`, exact) puts `c` into the box `N`;
2. `step2` — the `θ`-box (`theta_box`) puts `b` into the box `N`, modulo normal words with `σ > Σc`; at the
   same key these are strictly higher (fewer `f_θ`, or larger `Σc'`);
3. `step3` — part (i) (`part_i`) puts `a` into the box `N − ℓ₁ + ℓ₂`, modulo `Sub_{>j} ≤ FSub_{>j}`.

The coordinate projection onto the key keeps exactly the terms of the right degree and weight.  Back in
`V`, PBW (`cycDeg_le_sortedLow`) reduces `cycDeg ρ w d` to lowering words, which are normal-word
combinations of the same degree (`lowword_NW`), and `evD d` transports the lifted spanning.
-/

namespace VOA.DeligneAudit.CLAssembly

open VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.CLFilt VOA.DeligneAudit.CLNormal
  VOA.DeligneAudit.CLLift VOA.DeligneAudit.CL VOA.DeligneAudit.Sl2Weyl

noncomputable section

/-! ## Monomials and lists -/

/-- The monomial of a list of modes. -/
def mono (l : List ℕ) : R := (l.map fun i => (MvPolynomial.X i : R)).prod

theorem mono_eq (l : List ℕ) : mono l = MvPolynomial.monomial (Multiset.toFinsupp (l : Multiset ℕ)) 1 := by
  induction l with
  | nil => simp [mono]
  | cons x l ih =>
      rw [mono, List.map_cons, List.prod_cons, ← mono, ih, MvPolynomial.X, MvPolynomial.monomial_mul,
        one_mul, ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton]

/-- The sorted list of a monomial exponent. -/
def lst (g : ℕ →₀ ℕ) : List ℕ := (Finsupp.toMultiset g).sort (· ≤ ·)

theorem lst_coe (g : ℕ →₀ ℕ) : ((lst g : List ℕ) : Multiset ℕ) = Finsupp.toMultiset g :=
  Multiset.sort_eq _ _

theorem monomial_eq_mono (g : ℕ →₀ ℕ) : MvPolynomial.monomial g (1 : ℂ) = mono (lst g) := by
  rw [mono_eq, lst_coe, (Multiset.toFinsupp_eq_iff).mpr rfl]

theorem lst_sorted (g : ℕ →₀ ℕ) : (lst g).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _

theorem mem_lst {g : ℕ →₀ ℕ} {x : ℕ} : x ∈ lst g ↔ x ∈ g.support := by
  rw [lst, Multiset.mem_sort, Finsupp.mem_toMultiset]

theorem length_lst (g : ℕ →₀ ℕ) : (lst g).length = Finsupp.degree g := by
  rw [lst, Multiset.length_sort, Finsupp.card_toMultiset]; rfl

theorem boxP_lst {m : ℕ} {g : ℕ →₀ ℕ} (h : BoxP m g) : ∀ x ∈ lst g, x + (lst g).length ≤ m := by
  intro x hx; rw [length_lst]; exact h x (mem_lst.mp hx)

theorem evAlg_mono {V : Type*} [AddCommGroup V] [Module ℂ V] (F : ℕ → Module.End ℂ V)
    (hFF : ∀ i j, F i * F j = F j * F i) (l : List ℕ) :
    Sl2Weyl.evAlg F hFF (mono l) = (l.map F).prod := by
  rw [mono, map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => evAlg_z F hFF i

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem prod_eq_Fx (ρ : CurrentModule (bracketTable) V) (d : Fin 8) :
    ∀ l : List ℕ, (l.map (ρ.op d)).prod = Fx ρ d l
  | [] => rfl
  | (s :: l) => by rw [List.map_cons, List.prod_cons, prod_eq_Fx ρ d l]; rfl

theorem evAlg_mono_Fx (ρ : CurrentModule (bracketTable) V) (d : Fin 8)
    (hFF : ∀ i j, ρ.op d i * ρ.op d j = ρ.op d j * ρ.op d i) (l : List ℕ) :
    Sl2Weyl.evAlg (fun k => ρ.op d k) hFF (mono l) = Fx ρ d l := by
  rw [evAlg_mono, ← prod_eq_Fx]

theorem mono_hom (l : List ℕ) : ∃ n, MvPolynomial.IsWeightedHomogeneous om (mono l) n :=
  ⟨_, by rw [mono_eq]; exact MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl⟩

/-! ## Admissibility from boxes -/

theorem boxT_of {B : ℤ} {l : List ℕ} (hs : l.Pairwise (· ≤ ·))
    (h : ∀ x ∈ l, (x : ℤ) ≤ B) : BoxT B l := ⟨hs, h⟩

theorem adm_of {N : ℕ} {a b c : List ℕ} (ha : a.Pairwise (· ≤ ·)) (hb : b.Pairwise (· ≤ ·))
    (hc : c.Pairwise (· ≤ ·)) (hbN : ∀ x ∈ b, x + b.length ≤ N) (hcN : ∀ x ∈ c, x + c.length ≤ N)
    (haN : ∀ x ∈ a, x + a.length ≤ ((N : ℤ) - b.length + c.length).toNat) : Adm N (a, b, c) := by
  refine ⟨⟨hb, fun x hx => ?_⟩, ⟨hc, fun x hx => ?_⟩, ⟨ha, fun x hx => ?_⟩⟩
  · have := hbN x hx; dsimp only; omega
  · have := hcN x hx; dsimp only; omega
  · dsimp only at hx ⊢; have := haN x hx; have := List.length_pos_of_mem hx; omega

/-! ## Modes of `u`-words -/

theorem uθ_append (l1 l2 : List (Fin 8 × ℕ)) : uθ (l1 ++ l2) = uθ l1 ++ uθ l2 := by
  induction l1 with
  | nil => rfl
  | cons x l ih => simp only [List.cons_append, uθ]; split_ifs <;> simp [ih]

theorem u2_append (l1 l2 : List (Fin 8 × ℕ)) : u2 (l1 ++ l2) = u2 l1 ++ u2 l2 := by
  induction l1 with
  | nil => rfl
  | cons x l ih => simp only [List.cons_append, u2]; split_ifs <;> simp [ih]

theorem uθ_map5 (b : List ℕ) : uθ (b.map fun s => ((5 : Fin 8), s)) = b := by
  induction b with
  | nil => rfl
  | cons s b ih => simp [uθ, ih]

theorem uθ_map4 (c : List ℕ) : uθ (c.map fun s => ((4 : Fin 8), s)) = [] := by
  induction c with
  | nil => rfl
  | cons s c ih => simp only [List.map_cons, uθ, ih]; rfl

theorem u2_map5 (b : List ℕ) : u2 (b.map fun s => ((5 : Fin 8), s)) = [] := by
  induction b with
  | nil => rfl
  | cons s b ih => simp only [List.map_cons, u2, ih]; rfl

theorem u2_map4 (c : List ℕ) : u2 (c.map fun s => ((4 : Fin 8), s)) = c := by
  induction c with
  | nil => rfl
  | cons s c ih => simp [u2, ih]

/-! ## The lifted module -/

section Lifted

variable (ρ : CurrentModule (bracketTable) V) (w : V) (N : ℕ)

/-- The span of the lifted CL words. -/
abbrev CLS : Submodule ℂ (Kt →₀ V) := NW (liftRep ρ) (wl w) (fun a b c => Adm N (a, b, c))

/-- The index of `(b, c)`. -/
abbrev idx' (b c : List ℕ) : Idx := ((b.length, c.length), (b.sum, c.sum))

/-- The induction hypothesis at `(a, b, c)`. -/
def IHat (a b c : List ℕ) : Prop :=
  ∀ a' b' c', keyT a' b' c' = keyT a b c → Higher (idx' b' c') (idx' b c) →
    nw (liftRep ρ) (wl w) a' b' c' ∈ CLS ρ w N

variable {ρ w N}

theorem proj_CLS (K : Kt) {x : Kt →₀ V} (hx : x ∈ CLS ρ w N) : proj K x ∈ CLS ρ w N :=
  NW_mono (fun _ _ _ h => h.1) (proj_NW ρ w K hx)

/-- Projection of a span of normal words whose key-`K` members are in `CLS`. -/
theorem proj_NW_CLS (K : Kt) {P : List ℕ → List ℕ → List ℕ → Prop}
    (h : ∀ a b c, P a b c → keyT a b c = K → nw (liftRep ρ) (wl w) a b c ∈ CLS ρ w N) {x : Kt →₀ V}
    (hx : x ∈ NW (liftRep ρ) (wl w) P) : proj K x ∈ CLS ρ w N := by
  have h2 := proj_NW ρ w K hx
  have : NW (liftRep ρ) (wl w) (fun a b c => P a b c ∧ keyT a b c = K) ≤ CLS ρ w N := by
    rw [NW, Submodule.span_le]
    rintro _ ⟨a, b, c, ⟨hp, hk⟩, rfl⟩
    exact h a b c hp hk
  exact this h2

theorem mem_of_proj {a b c : List ℕ} {M S : Submodule ℂ (Kt →₀ V)}
    (h : nw (liftRep ρ) (wl w) a b c ∈ M ⊔ S) (hM : ∀ x ∈ M, proj (keyT a b c) x ∈ CLS ρ w N)
    (hS : ∀ x ∈ S, proj (keyT a b c) x ∈ CLS ρ w N) : nw (liftRep ρ) (wl w) a b c ∈ CLS ρ w N := by
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h
  rw [← proj_nw, ← hyz, map_add]
  exact Submodule.add_mem _ (hM y hy) (hS z hz)

theorem IHat_congr {a b c b' c' : List ℕ} (hk : keyT a b' c' = keyT a b c)
    (hl : b'.length = b.length ∧ c'.length = c.length ∧ b'.sum = b.sum ∧ c'.sum = c.sum)
    (IH : IHat ρ w N a b c) : IHat ρ w N a b' c' := by
  intro a'' b'' c'' hk' hh
  refine IH a'' b'' c'' (hk'.trans hk) ?_
  simpa [idx', hl.1, hl.2.1, hl.2.2.1, hl.2.2.2] using hh

variable (hR : MabRel ρ w N 0)
include hR

/-- **Step 3**: `b`, `c` in their boxes; part (i) puts `a` into its box. -/
theorem step3 (a b c : List ℕ) (hbs : b.Pairwise (· ≤ ·)) (hcs : c.Pairwise (· ≤ ·))
    (hbN : ∀ x ∈ b, x + b.length ≤ N) (hcN : ∀ x ∈ c, x + c.length ≤ N) (IH : IHat ρ w N a b c) :
    nw (liftRep ρ) (wl w) a b c ∈ CLS ρ w N := by
  have hL := mabRel_lift ρ hR
  set u : List (Fin 8 × ℕ) := b.map (fun s => ((5 : Fin 8), s)) ++ c.map (fun s => ((4 : Fin 8), s))
    with hudef
  have hu : ∀ x ∈ u, uLetter x := by
    intro x hx
    rcases List.mem_append.mp hx with h | h <;> obtain ⟨s, _, rfl⟩ := List.mem_map.mp h
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hwu : wordOp (liftRep ρ) u (wl w) = nw (liftRep ρ) (wl w) [] b c := by
    rw [hudef, wordOp_append, wordOp_map, wordOp_map]; rfl
  have hidx : idx u = idx' b c := by
    rw [idx_uword u hu, hudef, uθ_append, u2_append, uθ_map5, uθ_map4, u2_map5, u2_map4]
    simp
  have hp := part_i (liftRep ρ) (wl w) hL u hu (mono a)
  rw [evAlg_mono_Fx, hwu, hidx, Fx3_nw, List.append_nil] at hp
  refine mem_of_proj hp ?_ ?_
  · intro x hx
    refine proj_CLS _ ((Submodule.span_le.mpr ?_) hx)
    rintro _ ⟨f, hf, rfl⟩
    rw [monomial_eq_mono, evAlg_mono_Fx, Fx3_nw, List.append_nil]
    refine nw_mem (adm_of (lst_sorted f) hbs hcs hbN hcN ?_)
    exact boxP_lst hf
  · intro x hx
    refine proj_NW_CLS _ (fun a' b' c' hh hk => IH a' b' c' hk hh) (Sub_le_FSub hL _ hx)

/-- **Step 2**: `c` in its box; the `θ`-box puts `b` into its box. -/
theorem step2 (a b c : List ℕ) (hcs : c.Pairwise (· ≤ ·)) (hcN : ∀ x ∈ c, x + c.length ≤ N)
    (IH : IHat ρ w N a b c) : nw (liftRep ρ) (wl w) a b c ∈ CLS ρ w N := by
  have hL := mabRel_lift ρ hR
  obtain ⟨n, hn⟩ := mono_hom b
  have ht := theta_box hL c hn
  rw [evAlg_mono_Fx] at ht
  have h2 := Submodule.mem_map_of_mem (f := Fx (liftRep ρ) 3 a) ht
  rw [Submodule.map_sup] at h2
  refine mem_of_proj h2 ?_ ?_
  · intro x hx
    have hx' : x ∈ NW (liftRep ρ) (wl w) (fun a' b' c' => a' = a ∧ c' = c ∧ b'.Pairwise (· ≤ ·) ∧
        ∀ y ∈ b', y + b'.length ≤ N) := by
      rw [Submodule.map_span] at hx
      refine (Submodule.span_le.mpr ?_) hx
      rintro _ ⟨_, ⟨g, hg, -, rfl⟩, rfl⟩
      rw [monomial_eq_mono, evAlg_mono_Fx]
      exact nw_mem ⟨rfl, rfl, lst_sorted g, boxP_lst hg⟩
    refine proj_NW_CLS _ (fun a' b' c' hP hk => ?_) hx'
    obtain ⟨rfl, rfl, hbs', hbN'⟩ := hP
    obtain ⟨h1, h2, h3⟩ := keyT_eq hk
    exact step3 hR a' b' c' hbs' hcs hbN' hcN (IHat_congr hk ⟨by omega, rfl, by omega, rfl⟩ IH)
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have := Fx3_NW (Q := fun a' b' c' => ∃ a'', a' = a ++ a'' ∧ c.sum + 1 ≤ σ a'' c') a
      (fun a'' b'' c'' h => ⟨a'', rfl, h⟩) hy
    refine proj_NW_CLS _ (fun a' b' c' hP hk => ?_) this
    obtain ⟨a'', rfl, hσ⟩ := hP
    refine IH _ b' c' hk ?_
    obtain ⟨h1, h2, h3⟩ := keyT_eq hk
    simp only [σ, List.length_append, List.sum_append] at hσ h1 h2 h3
    simp only [idx', Higher, Prod.mk.injEq]
    rcases Nat.eq_zero_or_pos a''.length with h0 | h0
    · rw [List.length_eq_zero_iff] at h0
      subst h0
      simp only [List.length_nil, List.sum_nil] at hσ h1 h2 h3
      omega
    · omega

/-- **Step 1**: the `α₂`-box puts `c` into its box. -/
theorem step1 (a b c : List ℕ) (IH : IHat ρ w N a b c) :
    nw (liftRep ρ) (wl w) a b c ∈ CLS ρ w N := by
  have hL := mabRel_lift ρ hR
  obtain ⟨n, hn⟩ := mono_hom c
  have ht := alpha2_box (liftRep ρ) (wl w) hL hn
  rw [evAlg_mono_Fx] at ht
  have h2 := Submodule.mem_map_of_mem (f := Fx (liftRep ρ) 3 a * Fx (liftRep ρ) 5 b) ht
  have hx' : nw (liftRep ρ) (wl w) a b c ∈ NW (liftRep ρ) (wl w) (fun a' b' c' => a' = a ∧ b' = b ∧
      c'.Pairwise (· ≤ ·) ∧ ∀ y ∈ c', y + c'.length ≤ N) := by
    rw [Submodule.map_span] at h2
    refine (Submodule.span_le.mpr ?_) h2
    rintro _ ⟨_, ⟨g, hg, -, rfl⟩, rfl⟩
    rw [monomial_eq_mono, evAlg_mono_Fx]
    exact nw_mem ⟨rfl, rfl, lst_sorted g, boxP_lst hg⟩
  refine mem_of_proj (S := ⊥) (Submodule.mem_sup_left hx') ?_ (fun x hx => by
    rw [(Submodule.mem_bot ℂ).mp hx, map_zero]; exact Submodule.zero_mem _)
  intro x hx
  refine proj_NW_CLS _ (fun a' b' c' hP hk => ?_) hx
  obtain ⟨rfl, rfl, hcs', hcN'⟩ := hP
  obtain ⟨h1, h2, h3⟩ := keyT_eq hk
  exact step2 hR a' b' c' hcs' hcN' (IHat_congr hk ⟨rfl, by omega, rfl, by omega⟩ IH)

/-- **Every lifted normal word lies in the span of the CL words.** -/
theorem nw_mem_CLS (a b c : List ℕ) : nw (liftRep ρ) (wl w) a b c ∈ CLS ρ w N := by
  suffices H : ∀ D L e2 e1 (a b c : List ℕ), a.sum + b.sum + c.sum = D → b.length = L →
      D - c.sum = e2 → D - b.sum = e1 → nw (liftRep ρ) (wl w) a b c ∈ CLS ρ w N from
    H _ _ _ _ a b c rfl rfl rfl rfl
  intro D L
  induction L using Nat.strong_induction_on with
  | _ L ihL =>
  intro e2
  induction e2 using Nat.strong_induction_on with
  | _ e2 ihe2 =>
  intro e1
  induction e1 using Nat.strong_induction_on with
  | _ e1 ihe1 =>
  intro a b c hD hL he2 he1
  refine step1 hR a b c (fun a' b' c' hk hh => ?_)
  obtain ⟨h1, h2, h3⟩ := keyT_eq hk
  simp only [idx', Higher, Prod.mk.injEq] at hh
  rcases hh with hh | hh | ⟨⟨hb, hc⟩, hh⟩
  · exact ihL _ (by omega) _ _ a' b' c' (by omega) rfl rfl rfl
  · omega
  · rcases hh with hh | ⟨hh, hh'⟩
    · exact ihe2 _ (by omega) _ a' b' c' (by omega) (by omega) rfl rfl
    · exact ihe1 _ (by omega) a' b' c' (by omega) (by omega) (by omega) rfl

end Lifted

/-! ## Back to `V` -/

section Final

variable {ρ : CurrentModule (bracketTable) V} {w : V}

/-- A lowering word applied to `w` is a combination of normal words of the same degree. -/
theorem lowword_NW : ∀ l : List (Fin 8 × ℕ), (∀ x ∈ l, lowSl3 x.1) →
    wordOp ρ l w ∈ NW ρ w (fun a b c => a.sum + b.sum + c.sum = SectorGraded.wordDeg l)
  | [], _ => nw_mem (a := []) (b := []) (c := []) (by simp [SectorGraded.wordDeg])
  | (⟨d, k⟩ :: l), hl => by
      have ih := lowword_NW l (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      have hdeg : SectorGraded.wordDeg ((d, k) :: l) = k + SectorGraded.wordDeg l := by
        simp [SectorGraded.wordDeg]
      change ρ.op d k (wordOp ρ l w) ∈ _
      rw [hdeg]
      have hd := hl _ List.mem_cons_self
      unfold lowSl3 at hd
      have : d = 3 ∨ d = 4 ∨ d = 5 := by
        rcases d with ⟨d, hd8⟩
        simp only at hd
        rcases (show d = 3 ∨ d = 4 ∨ d = 5 by omega) with h | h | h <;> subst h <;> simp [Fin.ext_iff]
      rcases this with rfl | rfl | rfl
      · exact map_NW _ (fun a b c hp => by
          rw [f1_nw]; exact nw_mem (by simp only [List.sum_cons]; omega)) ih
      · exact map_NW _ (fun a b c hp => NW_mono (fun a' b' c' h => by omega) (f2_nw k a b c)) ih
      · exact map_NW _ (fun a b c hp => by
          rw [fθ_nw]; exact nw_mem (by simp only [List.sum_cons]; omega)) ih

theorem cycDeg_le_NW {N : ℕ} (hR : MabRel ρ w N 0) (d : ℕ) :
    cycDeg ρ w d ≤ NW ρ w (fun a b c => a.sum + b.sum + c.sum = d) := by
  have hw : ∀ (a : Fin 8) r, ¬ lowSl3 a → ρ.op a r w ∈ ℂ ∙ w ∧ (1 ≤ r → ρ.op a r w = 0) := by
    intro a r ha
    unfold lowSl3 at ha
    by_cases h3 : a.val < 3
    · rw [hR.raising a h3 r]; exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
    · have h6 : 6 ≤ a.val := by omega
      refine ⟨?_, fun hr => hR.cartan_pos a h6 r hr⟩
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · rw [hR.cartan_zero a h6]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
      · rw [hR.cartan_pos a h6 r hr]; exact Submodule.zero_mem _
  refine (cycDeg_le_sortedLow keySl3 lowSl3 ρ keySl3_low hw d).trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨l, -, hlow, hd, rfl⟩
  rw [← hd]
  exact lowword_NW l hlow

theorem wordOp_clWord (a b c : List ℕ) : wordOp ρ (clWord (a, b, c)) w = nw ρ w a b c := by
  simp only [clWord, wordOp_append, wordOp_map]; rfl

end Final

/-- **The Chari–Loktev spanning theorem for `sl₃`, `λ = N(ω₁+ω₂)`**: in every module with the
relations `MabRel ρ w N 0`, the degree-`d` part of the cyclic module is spanned by the CL words. -/
theorem clSpanning (N : ℕ) : CLSpanning N := by
  intro V _ _ ρ w hR d
  refine (cycDeg_le_NW hR d).trans ?_
  rw [NW, Submodule.span_le]
  rintro _ ⟨a, b, c, hd, rfl⟩
  have h := Submodule.mem_map_of_mem (f := evD d) (nw_mem_CLS hR a b c)
  rw [nw_lift, evD_single, if_pos (by simp [keyT, hd])] at h
  refine (Submodule.map_le_iff_le_comap.mpr ?_) h
  rw [CLS, NW, Submodule.span_le]
  rintro _ ⟨a', b', c', hadm, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  rw [nw_lift, evD_single]
  split_ifs with hk
  · refine Submodule.subset_span ⟨⟨(a', b', c'), hadm, ?_⟩, wordOp_clWord a' b' c'⟩
    simp only [keyT] at hk; simp only [tdeg]; omega
  · exact Submodule.zero_mem _

/-- **(S1), the dimension bound**: in every module with `MabRel ρ w N 0`, the degree-`d` part of the
cyclic module has dimension at most `demazureHilb N d` (the CL count). -/
theorem finrank_cycDeg_le {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : CurrentModule (bracketTable) V}
    {w : V} {N : ℕ} (hR : MabRel ρ w N 0) (d : ℕ) :
    Module.finrank ℂ (cycDeg ρ w d) ≤ A2.demazureHilb N d := by
  haveI : Fintype (CLIdx N d) := (CLIdx_finite N d).fintype
  have hle := clSpanning N V ρ w hR d
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i : CLIdx N d => wordOp ρ (clWord i.1) w)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  calc Module.finrank ℂ (cycDeg ρ w d)
      ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range fun i : CLIdx N d => wordOp ρ (clWord i.1) w)) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (CLIdx N d) := finrank_range_le_card _
    _ = (CLIdx N d).ncard := by rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    _ = A2.demazureHilb N d := clCount N d

/-- With spanning proved, the character identity rests on `CLIndependence` alone. -/
theorem Mchar_eq_of_independence (N : ℕ) (hi : CLIndependence N) :
    SectorWeyl.Mchar N 0 = A2.demazureHilbSeries N :=
  Mchar_eq_of_spanning_independence N (clSpanning N) hi

end

end VOA.DeligneAudit.CLAssembly

section AxiomAudit
#print axioms VOA.DeligneAudit.CLAssembly.nw_mem_CLS
#print axioms VOA.DeligneAudit.CLAssembly.clSpanning
#print axioms VOA.DeligneAudit.CLAssembly.finrank_cycDeg_le
#print axioms VOA.DeligneAudit.CLAssembly.Mchar_eq_of_independence
end AxiomAudit
