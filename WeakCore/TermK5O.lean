import WeakCore.TermK5P

/-!
# TermK5O: the post-publish provenance at the own cells with a start frontier (runAgree)

`PfrProvE` covers the own start cells with no frontier. `PfrProvO` is its shape at the own start
cells that already have a frontier (planted, not yet published): either the run `st → cc` has not
published `l` (`SoloNP`), or it published `l` at `c1` (thread `th1`), and every unit added at `l`
beyond the start count has a witness index at most `th1.vs.vWr`. After that publish the count is
fixed: the step's ghost `g.zf` covers `PubZO` (the cells the run has published), and no `bufInit`
hits them (`hZo`).
-/

namespace TermK5O

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermTyped TermGlob TermOwnG0Defs TermK5Defs TermK5P
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The labels the run `st → c0` has published (at its first `publish` naming them). -/
def PubZO (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (E0 : TEnv) (st c0 : Cfg) (l : AllocLabel) :
    Prop :=
  ∃ c1 th1 c1' cl, SoloNP p k arch i l st c1 ∧ c1.ths[i]? = some th1 ∧ PubAt th1 l ∧
    c1' ∈ threadSteps p k arch c1 i ∧ Solo p k arch i c1' c0 ∧ E0.sto l = some cl ∧ cl.owner = some E0.tid ∧
    ∃ f, E0.pfr l = some f

/-- (runAgree) The provenance of the counts at the own start cells with a frontier. -/
def PfrProvO (p : Prog) (k : Promises.Knobs) (arch : Arch) (j : Nat) (H : AllocLabel → Nat → Ts → Prop)
    (E0 : TEnv) (st cc : Cfg) (E : TEnv) : Prop :=
  ∀ l c f, E0.sto l = some c → c.owner = some E0.tid → E0.pfr l = some f →
    SoloNP p k arch j l st cc ∨
    ∃ c1 th1 c1', SoloNP p k arch j l st c1 ∧ c1.ths[j]? = some th1 ∧
      PubAt th1 l ∧ c1' ∈ threadSteps p k arch c1 j ∧ Solo p k arch j c1' cc ∧
      ∀ N e us, c.ty = .array (.lit N) e → accs e = some us →
        ∀ o, o < E.ini l * nWords us → ¬ o < E0.ini l * nWords us → ∃ τ, τ ≤ th1.vs.vWr ∧ H l o τ

theorem pfrProvO_start (p : Prog) (k : Promises.Knobs) (arch : Arch) (j : Nat) (H : AllocLabel → Nat → Ts → Prop)
    (E0 : TEnv) (st : Cfg) : PfrProvO p k arch j H E0 st st E0 :=
  fun _ _ _ _ _ _ => .inl (.refl _)

/-- No `bufInit` of the run's current thread at a label the run has published (`hZo`). -/
theorem pubZO_noBufInit {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 : TEnv} {st c0 : Cfg}
    {th : TTh}
    (hZo : ∀ c1 th1 c1' l cl f, SoloNP p k arch i l st c1 → c1.ths[i]? = some th1 → PubAt th1 l →
      c1' ∈ threadSteps p k arch c1 i → Solo p k arch i c1' c0 → E0.sto l = some cl →
      cl.owner = some E0.tid → E0.pfr l = some f → ¬ BufInitOn th l) :
    ∀ l, BufInitOn th l → ¬ PubZO p k arch i E0 st c0 l :=
  fun l hb ⟨c1, th1, c1', cl, h1, h2, h3, h4, h5, h6, h7, f, h8⟩ => hZo c1 th1 c1' l cl f h1 h2 h3 h4 h5 h6 h7 h8 hb

/-- `PubZO` extends along a thread step. -/
theorem pubZO_snoc {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 : TEnv} {st c0 c0' : Cfg}
    {l : AllocLabel} (h : PubZO p k arch i E0 st c0 l) (hs : c0' ∈ threadSteps p k arch c0 i) :
    PubZO p k arch i E0 st c0' l :=
  let ⟨c1, th1, c1', cl, h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  ⟨c1, th1, c1', cl, h1, h2, h3, h4, solo_trans h5 (.thread hs (.refl _)), h6, h7, h8⟩

/-- **`PfrProvO` along a thread step** `c0 → c0'` (thread `th → th'`, environment `E → E'`,
footprint at a `g` whose `g.zf` covers `PubZO st c0`):
- unpublished, the step not at a `publish` naming `l`: `SoloNP` extends;
- unpublished, the step at a `publish` naming `l`: `c0` is the publish point, and the new units'
  witnesses lie at most `th'.vWr = th.vWr` (`hU`, `hvw`);
- published: the count stays (`IniFixZ`, the frontier being kept by `Ext`), and the run after the
  publish extends. -/
theorem pfrProvO_thread {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat}
    {H : AllocLabel → Nat → Ts → Prop} {E0 E E' : TEnv} {st c0 c0' : Cfg} {th th' : TTh} {g : G}
    {n0 v0 : Nat} {s s' : St}
    (hP : PfrProvO p k arch i H E0 st c0 E) (hF : Foot g E E' s s') (hb : FrBound E0 n0 v0 E)
    (hx : Ext E0 E) (hz : ∀ l, PubZO p k arch i E0 st c0 l → g.zf l)
    (hs : c0' ∈ threadSteps p k arch c0 i) (hth : c0.ths[i]? = some th)
    (hvw : ∀ l, PubAt th l → th'.vs.vWr = th.vs.vWr)
    (hU : ∀ l c, E0.sto l = some c → c.owner = some E0.tid → ∀ N e us, c.ty = .array (.lit N) e →
      accs e = some us → ∀ o, o < E'.ini l * nWords us → ¬ o < E0.ini l * nWords us →
        ∃ τ, τ ≤ th'.vs.vWr ∧ H l o τ) :
    PfrProvO p k arch i H E0 st c0' E' := by
  intro l c f hc0 ho hf0
  have hc : E.sto l = some c := (hb.2.2.2.1.2 l c hc0).1
  have hf : E.pfr l = some f := hx.2.2.2.2.2.2.1 l f hf0
  have hnf : ¬ FreshIn g s.nalloc s'.nalloc l := fun hl => by rw [(hF.2 l hl).1] at hc; cases hc
  rcases hP l c f hc0 ho hf0 with hsolo | ⟨c1, th1, c1', hsolo, hth1, hpub, hs1, h1c, hu⟩
  · by_cases hpl : PubAt th l
    · refine .inr ⟨c0, th, c0', hsolo, hth, hpl, hs, .refl _, fun N e us hT hus o ho1 ho2 => ?_⟩
      rw [← hvw l hpl]
      exact hU l c hc0 ho N e us hT hus o ho1 ho2
    · refine .inl (soloNP_snocT hsolo hs fun th0 h0 => ?_)
      rw [hth] at h0
      cases h0
      exact hpl
  · have hini : E'.ini l = E.ini l :=
      (hF.1.iniFixZ l c f (hz l ⟨c1, th1, c1', c, hsolo, hth1, hpub, hs1, h1c, hc0, ho, f, hf0⟩) hnf hc hf).1
    refine .inr ⟨c1, th1, c1', hsolo, hth1, hpub, hs1, solo_trans h1c (.thread hs (.refl _)),
      fun N e us hT hus o ho1 ho2 => ?_⟩
    rw [hini] at ho1
    exact hu N e us hT hus o ho1 ho2

/-- **`PfrProvO` along a promise step** (the environment is kept). -/
theorem pfrProvO_prom {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat}
    {H : AllocLabel → Nat → Ts → Prop} {E0 E : TEnv} {st c0 : Cfg} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hP : PfrProvO p k arch i H E0 st c0 E) (hw : w < c0.mem.size) :
    PfrProvO p k arch i H E0 st (promise c0 i a v w) E := by
  intro l c f hc0 ho hf0
  rcases hP l c f hc0 ho hf0 with hsolo | ⟨c1, th1, c1', hsolo, hth1, hpub, hs1, h1c, hu⟩
  · exact .inl (soloNP_snocP hsolo hw)
  · exact .inr ⟨c1, th1, c1', hsolo, hth1, hpub, hs1, solo_trans h1c (.prom a v w hw (.refl _)), hu⟩

/-- (IO1) An extern move keeps the post-publish provenance. -/
theorem pfrProvO_ext {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat}
    {H : AllocLabel → Nat → Ts → Prop} {E0 E : TEnv} {st c0 c0' : Cfg}
    (hP : PfrProvO p k arch i H E0 st c0 E) (hs : c0' ∈ extSteps c0 i) : PfrProvO p k arch i H E0 st c0' E := by
  intro l c f hc0 ho hf0
  rcases hP l c f hc0 ho hf0 with hsolo | ⟨c1, th1, c1', hsolo, hth1, hpub, hs1, h1c, hu⟩
  · exact .inl (soloNP_snocE hsolo hs)
  · exact .inr ⟨c1, th1, c1', hsolo, hth1, hpub, hs1, solo_trans h1c (.ext hs (.refl _)), hu⟩

end TermK5O

#print axioms TermK5O.pfrProvO_start
#print axioms TermK5O.pfrProvO_ext
#print axioms TermK5O.pubZO_noBufInit
#print axioms TermK5O.pubZO_snoc
#print axioms TermK5O.pfrProvO_thread
#print axioms TermK5O.pfrProvO_prom
