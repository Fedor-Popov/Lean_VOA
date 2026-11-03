import VOA.DeligneAudit.DeligneFusionLattice
import VOA.DeligneAudit.DeligneFusionDemazure
import VOA.DeligneAudit.DeligneFusionUniv

/-!
# The Chari–Loktev family `𝔅_N` and the sharp residuals for `M_{N,0}`

`𝔅_N` (CL (2.6) at `r = 2`, `λ = N(ω₁+ω₂)`): words `f₁(a) f_θ(b) f₂(c)` with `a, b, c` weakly increasing,
`max b ≤ N − |b|`, `max c ≤ N − |c|`, `max a ≤ N + |c| − |b| − |a|`; `f₂` acts first.

Named statements:
* `CLCount N` — the degree-`d` part of `𝔅_N` has `demazureHilb N d` elements (pure combinatorics);
* `CLIndependence N` — `𝔅_N · e^{Nθ}` is linearly independent in `V_{A₂}` (Conjecture CL-V; checked
  numerically for `N ≤ 4`);
* `CLSpanning N` — `𝔅_N · w` spans every `M_{N,0}`-module degree by degree (Chari–Loktev).

Proved: `demazureRealization_of_CL : CLCount N → CLIndependence N → DemazureRealization N`, and
`Mchar_eq_of_CL : CLSpanning N → CLCount N → CLIndependence N → Mchar N 0 = demazureHilbSeries N`.
-/

namespace VOA.DeligneAudit.CL

open VOA VOA.LatGen VOA.CartanLattices VOA.AffineSl3 VOA.DeligneAudit.SectorWeyl VOA.DeligneAudit.FusionLattice

noncomputable section

/-- A weakly increasing tuple with entries `≤ B` (`B : ℤ`, so a negative bound forces the empty tuple). -/
def BoxT (B : ℤ) (s : List ℕ) : Prop := s.Pairwise (· ≤ ·) ∧ ∀ x ∈ s, (x : ℤ) ≤ B

/-- The CL admissibility of `(a, b, c)` = `(f₁-part, f_θ-part, f₂-part)`. -/
def Adm (N : ℕ) (i : List ℕ × List ℕ × List ℕ) : Prop :=
  BoxT ((N : ℤ) - i.2.1.length) i.2.1 ∧ BoxT ((N : ℤ) - i.2.2.length) i.2.2 ∧
    BoxT ((N : ℤ) + i.2.2.length - i.2.1.length - i.1.length) i.1

/-- The word of an index triple; `wordOp` applies the last letter first, so `f₂` acts first. -/
def clWord (i : List ℕ × List ℕ × List ℕ) : List (Fin 8 × ℕ) :=
  i.1.map (fun s => ((3 : Fin 8), s)) ++ i.2.1.map (fun s => ((5 : Fin 8), s)) ++
    i.2.2.map (fun s => ((4 : Fin 8), s))

/-- The `t`-degree of an index triple. -/
def tdeg (i : List ℕ × List ℕ × List ℕ) : ℕ := i.1.sum + i.2.1.sum + i.2.2.sum

/-- The degree-`d` part of `𝔅_N`. -/
def CLIdx (N d : ℕ) : Set (List ℕ × List ℕ × List ℕ) := {i | Adm N i ∧ tdeg i = d}

theorem wordDeg_clWord (i : List ℕ × List ℕ × List ℕ) :
    VOA.DeligneAudit.SectorGraded.wordDeg (clWord i) = tdeg i := by
  simp [clWord, tdeg, VOA.DeligneAudit.SectorGraded.wordDeg, Function.comp_def]; omega

/-! ## Finiteness -/

theorem finite_lists (L B : ℕ) : {l : List ℕ | l.length ≤ L ∧ ∀ x ∈ l, x ≤ B}.Finite := by
  haveI : Finite {x : ℕ // x ≤ B} := Finite.of_injective (fun x => (⟨x.1, by have := x.2; omega⟩ : Fin (B + 1)))
    (fun x y h => by simp only [Fin.mk.injEq] at h; exact Subtype.ext h)
  refine ((List.finite_length_le {x : ℕ // x ≤ B} L).image (List.map Subtype.val)).subset ?_
  rintro l ⟨hl, hb⟩
  exact ⟨l.pmap Subtype.mk hb, by simpa using hl, by simp [List.map_pmap]⟩

theorem boxT_bound {B : ℤ} {s : List ℕ} (h : BoxT B s) (x : ℕ) (hx : x ∈ s) : x ≤ B.toNat := by
  have := h.2 x hx; omega

theorem CLIdx_finite (N d : ℕ) : (CLIdx N d).Finite := by
  -- all entries are `≤ d` and all lengths are `≤ d + 3N + 1` (entries are bounded, lengths by positivity)
  have hS := ((finite_lists (3 * N + 1) (3 * N + 1)).prod
    ((finite_lists (3 * N + 1) (3 * N + 1)).prod (finite_lists (3 * N + 1) (3 * N + 1))))
  refine hS.subset ?_
  rintro ⟨a, b, c⟩ ⟨⟨hb, hc, ha⟩, -⟩
  simp only [Set.mem_prod, Set.mem_setOf_eq]
  dsimp only at hb hc ha
  have hb' := fun x hx => hb.2 x hx
  have hc' := fun x hx => hc.2 x hx
  have ha' := fun x hx => ha.2 x hx
  have lenb : b.length ≤ N := by
    rcases b with _ | ⟨x, b'⟩
    · simp
    · have := hb' x List.mem_cons_self; simp only [List.length_cons] at this ⊢; push_cast at this; omega
  have lenc : c.length ≤ N := by
    rcases c with _ | ⟨x, c'⟩
    · simp
    · have := hc' x List.mem_cons_self; simp only [List.length_cons] at this ⊢; push_cast at this; omega
  have lena : a.length ≤ 2 * N := by
    rcases a with _ | ⟨x, a'⟩
    · simp
    · have := ha' x List.mem_cons_self; simp only [List.length_cons] at this ⊢; push_cast at this
      omega
  refine ⟨⟨by omega, fun x hx => ?_⟩, ⟨by omega, fun x hx => ?_⟩, ⟨by omega, fun x hx => ?_⟩⟩
  · have := ha' x hx; omega
  · have := hb' x hx; omega
  · have := hc' x hx; omega

/-! ## The named statements -/

/-- **CL count** (pure combinatorics): `|𝔅_N ∩ deg d| = demazureHilb N d`. -/
def CLCount (N : ℕ) : Prop := ∀ d, (CLIdx N d).ncard = A2.demazureHilb N d

/-- **Conjecture CL-V**: `𝔅_N · e^{Nθ}` is linearly independent in `V_{A₂}`, degree by degree. -/
def CLIndependence (N : ℕ) : Prop :=
  ∀ d, LinearIndependent ℂ (fun i : CLIdx N d => wordOp latRep (clWord i.1) (ch N N))

/-- **CL spanning** (Chari–Loktev). -/
def CLSpanning (N : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : CurrentModule (bracketTable) V) (w : V),
    MabRel ρ w N 0 → ∀ d, cycDeg ρ w d ≤
      Submodule.span ℂ (Set.range fun i : CLIdx N d => wordOp ρ (clWord i.1) w)

/-! ## Consequences -/

theorem wordOp_mem_grading (l : List (Fin 8 × ℕ)) {k : ℤ} {x : LatModuleGen a2}
    (hx : x ∈ WA.grading k) :
    wordOp latRep l x ∈ WA.grading (k - VOA.DeligneAudit.SectorGraded.wordDeg l) := by
  induction l with
  | nil => simpa [VOA.DeligneAudit.SectorGraded.wordDeg] using hx
  | cons y l ih =>
      have h := WA.grading_mode (Xs y.1) (Xs_mem y.1) _ ih y.2
      have e : (1 : ℤ) + (k - VOA.DeligneAudit.SectorGraded.wordDeg l) - y.2 - 1 =
          k - VOA.DeligneAudit.SectorGraded.wordDeg (y :: l) := by
        simp [VOA.DeligneAudit.SectorGraded.wordDeg]; ring
      rw [e] at h
      exact h

theorem cycDeg_latRep_le (N d : ℕ) :
    cycDeg latRep (ch N N) d ≤ gradingLatGen a2 ((N : ℤ) * N - d) := by
  rw [cycDeg, Submodule.span_le]
  rintro _ ⟨l, hl, rfl⟩
  have h0 : ch N N ∈ WA.grading ((N : ℤ) * N) := by
    have := latChargeGen_mem_grading a2 (lv (N : ℤ) N)
    rw [halfNorm_lv] at this
    simpa using this
  have := wordOp_mem_grading l h0
  rw [hl] at this
  exact this

instance (N d : ℕ) : FiniteDimensional ℂ (cycDeg latRep (ch N N) d) := by
  haveI := gradingLatGen_finrank_of_posDef a2 a2_even a2_posDef ((N : ℤ) * N - d)
  exact Submodule.finiteDimensional_of_le (cycDeg_latRep_le N d)

theorem clWord_mem (N d : ℕ) (i : CLIdx N d) :
    wordOp latRep (clWord i.1) (ch N N) ∈ cycDeg latRep (ch N N) d :=
  Submodule.subset_span ⟨clWord i.1, by rw [wordDeg_clWord]; exact i.2.2, rfl⟩

/-- `ncard ≤ finrank` for an independent family landing in a finite-dimensional submodule. -/
theorem ncard_le_finrank_cyc (N d : ℕ) (h : CLIndependence N) :
    (CLIdx N d).ncard ≤ Module.finrank ℂ (cycDeg latRep (ch N N) d) := by
  haveI : Fintype (CLIdx N d) := (CLIdx_finite N d).fintype
  have hli : LinearIndependent ℂ
      (fun i : CLIdx N d => (⟨_, clWord_mem N d i⟩ : cycDeg latRep (ch N N) d)) := by
    apply LinearIndependent.of_comp (cycDeg latRep (ch N N) d).subtype
    exact h d
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
  exact hli.fintype_card_le_finrank

/-- **U7 from the CL family**: `CLCount N → CLIndependence N → DemazureRealization N`. -/
theorem demazureRealization_of_CL (N : ℕ) (hc : CLCount N) (hi : CLIndependence N) :
    A2.DemazureRealization N :=
  ⟨LatModuleGen a2, inferInstance, inferInstance, latRep, ch N N, latRep_mabRel N,
    fun d => hc d ▸ ncard_le_finrank_cyc N d hi⟩

/-- **The dimension equality**: with CL spanning, count and independence, the universal
character `Mchar N 0` is the GT polynomial `demazureHilbSeries N`. -/
theorem Mchar_eq_of_CL (N : ℕ) (hs : CLSpanning N) (hc : CLCount N) (hi : CLIndependence N) :
    Mchar N 0 = A2.demazureHilbSeries N := by
  ext d
  rw [Mchar, A2.demazureHilbSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  norm_cast
  haveI : Fintype (CLIdx N d) := (CLIdx_finite N d).fintype
  have hsp := hs _ (univRep N 0) (SectorWeyl.wU N 0) (univ_mabRel N 0) d
  haveI := FiniteDimensional.span_of_finite ℂ
    (Set.finite_range fun i : CLIdx N d => wordOp (univRep N 0) (clWord i.1) (SectorWeyl.wU N 0))
  haveI : FiniteDimensional ℂ (cycDeg (univRep N 0) (SectorWeyl.wU N 0) d) :=
    Submodule.finiteDimensional_of_le hsp
  apply le_antisymm
  · calc Module.finrank ℂ (cycDeg (univRep N 0) (SectorWeyl.wU N 0) d)
        ≤ Module.finrank ℂ (Submodule.span ℂ
            (Set.range fun i : CLIdx N d => wordOp (univRep N 0) (clWord i.1) (SectorWeyl.wU N 0))) :=
          Submodule.finrank_mono hsp
      _ ≤ Fintype.card (CLIdx N d) := finrank_range_le_card _
      _ = A2.demazureHilb N d := by rw [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card', hc d]
  · calc A2.demazureHilb N d = (CLIdx N d).ncard := (hc d).symm
      _ ≤ Module.finrank ℂ (cycDeg latRep (ch N N) d) := ncard_le_finrank_cyc N d hi
      _ ≤ _ := finrank_cycDeg_le_univ (latRep_mabRel N) d

end

end VOA.DeligneAudit.CL

section AxiomAudit
#print axioms VOA.DeligneAudit.CL.demazureRealization_of_CL
#print axioms VOA.DeligneAudit.CL.Mchar_eq_of_CL
end AxiomAudit
