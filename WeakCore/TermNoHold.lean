import WeakCore.TermInterf
import WeakCore.TermK5P
import WeakCore.TermK5O

/-!
# TermNoHold: stage-A certificate arguments

1. `certified_promLoc`: an outstanding promise of a certified thread typed at
   `E0` lies at a cell of `E0` or at one of the thread's labels yet to
   allocate (index at least its allocation count at the start).  Proved along
   the certificate with the tied typed run (`solo_typedXF`, `solo_typedX` with
   the run's new labels tracked, `FreshRun`); run-level hypotheses `hsc`/`hwin`
   along the certificate, as in `TermTyped.certified_prefixHeld`.
2. Field forms: `promLocP` (the `PromLocF`, at a promise step) and
   `promLocT` (at a thread step, the stepper's promises at the source).
-/

namespace TermNoHold
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermFul TermGlob TermTyped TermMain TermInterf
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## The run's new labels -/

/-- Every label that is a cell of `E` but not of the start `E0` is one of
thread `g.i`'s labels with index at least `n0`. -/
def FreshRun (g : G) (E0 : TEnv) (n0 : Nat) (E : TEnv) : Prop :=
  ∀ l c, E0.sto l = none → E.sto l = some c → ∃ j, n0 ≤ j ∧ l = freshLabel g.lbase g.n g.i j

/-- `InvAtX` with the allocation count bounded below by `na0` and `FreshRun`
at the same environment; (iniop) and the run's count locality `IniLoc` at the start labels `Z`. -/
def InvAtXFZ (Z : AllocLabel → Prop) (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (E0 : TEnv)
    (n0 v0 na0 : Nat) (c : Cfg) (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) (Ea : TEnv := E0) (Eu : TEnv := Ea) : Prop :=
  ∃ th E, c.ths[i]? = some th ∧ Ext E0 E ∧ ThInvE p E th ∧ MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧
    StoClo E ∧ (gOf p k arch c i).boxFence = true ∧ FrBound E0 n0 v0 E ∧ FrRunA E0 n0 v0 E (stOf c.mem c.pairs th) Ea Eu ∧
    na0 ≤ th.nalloc ∧ FreshRun (gOf p k arch c i) E0 na0 E ∧ TermTyped.IniLoc Z E0 E ∧
    TermTyped.IniHeld H E0 E th.vs.vWr

/-- `InvAtXFZ` with no locality labels. -/
abbrev InvAtXF (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (E0 : TEnv) (n0 v0 na0 : Nat) (c : Cfg)
    (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) (Ea : TEnv := E0) (Eu : TEnv := Ea) : Prop :=
  InvAtXFZ (fun _ => False) p k arch i E0 n0 v0 na0 c H Ea Eu

theorem InvAtXFZ.toInvAt {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 : TEnv} {Eu Ea : TEnv} {n0 v0 na0 : Nat}
    {c : Cfg} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} (h : InvAtXFZ Z p k arch i E0 n0 v0 na0 c H (Ea := Ea) (Eu := Eu)) :
    InvAt p k arch i c :=
  let ⟨th, E, hth, _, h1, h2, _, hbo, _⟩ := h
  ⟨th, hth, E, h1, h2, hbo⟩

/-- The start: the invariant's own environment. -/
theorem InvAtXF_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E : TEnv} {c : Cfg} {th : TTh}
    (hth : c.ths[i]? = some th) (hT : ThInvE p E th)
    (hm : MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th)) (hSC : StoClo E)
    (hbo : (gOf p k arch c i).boxFence = true) (hrc : TermTyped.RiniCoh E (stOf c.mem c.pairs th))
    (hfl : ∀ l cl f, E.sto l = some cl → E.pfr l = some f → f ≤ c.mem.size - 1) (Z : AllocLabel → Prop := fun _ => False)
    (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) :
    InvAtXFZ Z p k arch i E c.mem.size th.vs.vWr th.nalloc c H := by
  obtain ⟨ρ, η, cx, rfl, h⟩ := hT
  exact ⟨th, CE η, hth, Ext_refl (Coh_CE η) (CohR_CE η), ⟨ρ, η, cx, rfl, h⟩, hm, hSC, hbo,
    FrBound_refl _ _ _, frRunA_start hm hrc hfl,
    Nat.le_refl _, (fun l c h0 h => by rw [h0] at h; cases h), TermTyped.IniLoc_refl _ _,
    TermTyped.IniHeld_refl _ _ _⟩

/-- (certWin-D) `InvAtXF_of` anchored at any `Ea` with `AnchR` there (the post-step start). -/
theorem InvAtXF_ofA {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E Eu Ea : TEnv} {c : Cfg} {th : TTh}
    (hth : c.ths[i]? = some th) (hT : ThInvE p E th)
    (hm : MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th)) (hSC : StoClo E)
    (hbo : (gOf p k arch c i).boxFence = true) (hA : AnchR Eu Ea E (stOf c.mem c.pairs th)) (hx : Ea = E ∨ Ext Ea E)
    (Z : AllocLabel → Prop := fun _ => False) (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) :
    InvAtXFZ Z p k arch i E c.mem.size th.vs.vWr th.nalloc c H Ea Eu := by
  obtain ⟨ρ, η, cx, rfl, h⟩ := hT
  exact ⟨th, CE η, hth, Ext_refl (Coh_CE η) (CohR_CE η), ⟨ρ, η, cx, rfl, h⟩, hm, hSC, hbo,
    FrBound_refl _ _ _, frRunA_startA hA hx,
    Nat.le_refl _, (fun l c h0 h => by rw [h0] at h; cases h), TermTyped.IniLoc_refl _ _,
    TermTyped.IniHeld_refl _ _ _⟩

/-- `gOf` is constant along a solo run. -/
theorem gOf_solo {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c' : Cfg}
    (h : Solo p k arch i c c') : gOf p k arch c' i = gOf p k arch c i := by
  induction h with
  | refl => rfl
  | thread hs _ ih => exact ih.trans (TermTyped.gOf_thread hs)
  | prom _ _ _ _ _ ih => exact ih.trans gOf_promise
  | ext hs _ ih => exact ih.trans (gOf_ext hs)

/-- **The tied typed run with the new labels** (`solo_typedX` plus
`FreshRun`): along `Solo` from `c`, at every certified configuration reached,
thread `i`'s invariant holds at an extension of `E0`, and every cell new
since `E0` is one of `i`'s labels of index at least `na0`. -/
theorem solo_typedXF {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c : Cfg} {E0 : TEnv} {Eu Ea : TEnv}
    {n0 v0 na0 : Nat} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch Eu Ea i c0)
    (h0 : InvAtXFZ Z p k arch i E0 n0 v0 na0 c H (Ea := Ea) (Eu := Eu)) {c2 : Cfg} (h : Solo p k arch i c c2)
    (hc2 : Certified p k arch c2 i)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h)
    (hHr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) → H l o τ := by
      exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    InvAtXFZ Z p k arch i E0 n0 v0 na0 c2 H (Ea := Ea) (Eu := Eu) := by
  refine (run_inv (c1 := c2) (P := fun c0 => Solo p k arch i c c0 ∧ InvAtXFZ Z p k arch i E0 n0 v0 na0 c0 H (Ea := Ea) (Eu := Eu)) ?_ ?_ ?_ h
    (.refl _) ⟨.refl _, h0⟩).2
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hna, hfresh, hIL, hIH⟩ hs hrest
    have hc0' : Certified p k arch c0' i := certified_back hrest hc2
    have hcert0 : Certified p k arch c0 i := certified_back (.thread hs hrest) hc2
    obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc0'
    rw [hth] at hth'
    cases hth'
    obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, hrp⟩ := hTE
    have hscope := hsc c0 hc0 hcert0 th hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hT htv hi
    obtain ⟨-, hstep⟩ := tstep_footprintQ (hRP := hrp) (hPS := hPS) (hSub := hSub) (hSig := hSig) (g := { gOf p k arch c0 i with zf := Z }) hP rfl
      (Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth)))
      (tstep_notDone hr) hscope hT hi hE htv hm hbo (PAx_of_step hs hc0' hth)
      (hwin c0 hc0 hcert0 th hth ρ η cx hE hT htv hi hm (frRunA_ext hfr hx) hfr.2.1.1 hfr.2.1.2.2.1) (hZ := ZOK_of_not (hZr c0 hc0 hcert0 th hth))
    obtain ⟨E', hF, hx', hT', hm', hbB⟩ := hstep r hr hpa
    have hA' := anchR_tstep hF hm' hbB hE hT htv hi hm hscope (TermViewInv.envVR_solo hvI hc0 hth) hr (frRunA_ext hfr hx) hfr.2.1
    have hwu := tstep_wrUp _ _ _ _ r hr
    have hfb' := FrBound_foot hF hwu hfb hfr.1
    have hg : gOf p k arch c0' i = gOf p k arch c0 i := TermTyped.gOf_thread hs
    refine ⟨solo_trans hc0 (.thread hs (.refl _)), r.2.2, E', e3, Ext_trans hx hx', hT', ?_,
      StoClo_EFoot hF.1 hSC, by rw [hg]; exact hbo, hfb'.1, ?_, Nat.le_trans hna hwu.2.2.1, ?_,
      TermTyped.IniLoc_foot hF (fun _ h => h) hfb hIL,
      TermTyped.IniHeld_foot hF hwu.1 hfb (hHr c0 hc0 hcert0 th hth) hIH⟩
    · rw [hg, e1, e2]
      exact hm'
    · rw [e1, e2]
      exact ⟨hfb'.2, hA', hfr.2.2⟩
    · intro l cl h0l hl
      rw [hg]
      rcases hF.1.2.2.1 l with e | ⟨⟨j, hj1, -, hlj⟩, -⟩
      · rw [e] at hl
        exact hfresh l cl h0l hl
      · exact ⟨j, Nat.le_trans hna hj1, hlj⟩
  · rintro c0 a v w ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hna, hfresh, hIL, hIH⟩ hw _
    have hpi := promise_inv (a := a) (v := v) (w := w) hth
    refine ⟨solo_trans hc0 (.prom a v w hw (.refl _)), _, E, hpi.2.1, hx, hTE, ?_, hSC,
      by rw [gOf_promise]; exact hbo, hfb, ?_, hna, by rw [gOf_promise]; exact hfresh, hIL, hIH⟩
    · rw [gOf_promise, hpi.2.2]
      exact MemInv_promSt hm
    · exact frRunA_prom hth hfr
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hna, hfresh, hIL, hIH⟩ hs _
    obtain ⟨x1, a1, e1, evs, hterm, rfl⟩ := extSteps_thread hs hth
    exact ⟨solo_trans hc0 (.ext hs (.refl _)), _, E, set_self hth, hx, TermTyped.ThInvE_emit hterm hTE,
      by rw [gOf_ext hs]; exact hm, hSC, by rw [gOf_ext hs]; exact hbo, hfb, hfr, hna, by rw [gOf_ext hs]; exact hfresh, hIL, hIH⟩

/-- (S1b) `InvAtXFZ` with the run's publish provenance `PfrProvE` from the run start `st`. -/
def InvAtXFP (Z : AllocLabel → Prop) (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (E0 : TEnv)
    (n0 v0 na0 : Nat) (st c : Cfg) (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) : Prop :=
  ∃ th E, c.ths[i]? = some th ∧ Ext E0 E ∧ ThInvE p E th ∧ MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧
    StoClo E ∧ (gOf p k arch c i).boxFence = true ∧ FrBound E0 n0 v0 E ∧ FrRunA E0 n0 v0 E (stOf c.mem c.pairs th) ∧
    na0 ≤ th.nalloc ∧ FreshRun (gOf p k arch c i) E0 na0 E ∧ TermTyped.IniLoc Z E0 E ∧
    TermTyped.IniHeld H E0 E th.vs.vWr ∧ TermK5Defs.PfrProvE p k arch i H E0 st c E ∧
    TermK5O.PfrProvO p k arch i H E0 st c E

theorem InvAtXFP.toF {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 : TEnv} {n0 v0 na0 : Nat}
    {st c : Cfg} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop}
    (h : InvAtXFP Z p k arch i E0 n0 v0 na0 st c H) : InvAtXFZ Z p k arch i E0 n0 v0 na0 c H :=
  let ⟨th, E, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, _⟩ := h
  ⟨th, E, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩

/-- (S1b) The start of `InvAtXFP`: the invariant's own environment, nothing published. -/
theorem InvAtXFP_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E : TEnv} {c : Cfg} {th : TTh}
    (hth : c.ths[i]? = some th) (hT : ThInvE p E th)
    (hm : MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th)) (hSC : StoClo E)
    (hbo : (gOf p k arch c i).boxFence = true) (hrc : TermTyped.RiniCoh E (stOf c.mem c.pairs th))
    (hfl : ∀ l cl f, E.sto l = some cl → E.pfr l = some f → f ≤ c.mem.size - 1) (Z : AllocLabel → Prop := fun _ => False)
    (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) :
    InvAtXFP Z p k arch i E c.mem.size th.vs.vWr th.nalloc c c H := by
  obtain ⟨ρ, η, cx, rfl, h⟩ := hT
  exact ⟨th, CE η, hth, Ext_refl (Coh_CE η) (CohR_CE η), ⟨ρ, η, cx, rfl, h⟩, hm, hSC, hbo,
    FrBound_refl _ _ _, frRunA_start hm hrc hfl,
    Nat.le_refl _, (fun l c h0 h => by rw [h0] at h; cases h), TermTyped.IniLoc_refl _ _,
    TermTyped.IniHeld_refl _ _ _, TermK5P.pfrProvE_start _ _ _ _ _ _ _, TermK5O.pfrProvO_start _ _ _ _ _ _ _⟩

/-- (shared) **`xfz_thread` from a given footprint**: the tied run's components at the new
environment, plus any property `Q` the footprint supplies. -/
theorem xfz_of_foot {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 E Eu Ea : TEnv} {n0 v0 na0 : Nat}
    {Z W : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} {c0 c0' : Cfg} {th : TTh}
    {Q : TTh → TEnv → Prop}
    (hth : c0.ths[i]? = some th) (hx : Ext E0 E) (hSC : StoClo E)
    (hbo : (gOf p k arch c0 i).boxFence = true) (hfb : FrBound E0 n0 v0 E)
    (hfr : FrRunA E0 n0 v0 E (stOf c0.mem c0.pairs th) Ea Eu) (hna : na0 ≤ th.nalloc)
    (hfresh : FreshRun (gOf p k arch c0 i) E0 na0 E) (hIL : TermTyped.IniLoc Z E0 E)
    (hIH : TermTyped.IniHeld H E0 E th.vs.vWr)
    (hs : c0' ∈ threadSteps p k arch c0 i) (hc0' : Certified p k arch c0' i)
    (hHr : ∀ l o τ, (c0.mem.size ≤ τ ∨ (τ ∈ th.promises ∧ ∃ m, c0.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) →
      H l o τ)
    (hstep : ∀ r ∈ tstep { ({ gOf p k arch c0 i with zf := fun l => Z l ∨ W l } : G) with
        pf := fun l => TermOwnG0Defs.PubAt th l } c0.mem c0.pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', Foot { ({ gOf p k arch c0 i with zf := fun l => Z l ∨ W l } : G) with
          pf := fun l => TermOwnG0Defs.PubAt th l } E E' (stOf c0.mem c0.pairs th) (stOf r.1 r.2.1 r.2.2) ∧
        Ext E E' ∧ ThInvE p E' r.2.2 ∧
        MemInv { ({ gOf p k arch c0 i with zf := fun l => Z l ∨ W l } : G) with
          pf := fun l => TermOwnG0Defs.PubAt th l } E' (stOf r.1 r.2.1 r.2.2) ∧
        (∀ l, TermOwnG0Defs.PubAt th l → E'.pfr l ≠ none) ∧ AnchR Eu Ea E' (stOf r.1 r.2.1 r.2.2) ∧
        Q r.2.2 E') :
    ∃ th' E' s s', c0'.ths[i]? = some th' ∧
      Foot { ({ gOf p k arch c0 i with zf := fun l => Z l ∨ W l } : G) with
        pf := fun l => TermOwnG0Defs.PubAt th l } E E' s s' ∧
      (∀ l, TermOwnG0Defs.PubAt th l → E'.pfr l ≠ none) ∧
      (∀ l, TermOwnG0Defs.PubAt th l → th'.vs.vWr = th.vs.vWr) ∧
      Ext E0 E' ∧ ThInvE p E' th' ∧ MemInv (gOf p k arch c0' i) E' (stOf c0'.mem c0'.pairs th') ∧
      StoClo E' ∧ (gOf p k arch c0' i).boxFence = true ∧ FrBound E0 n0 v0 E' ∧
      FrRunA E0 n0 v0 E' (stOf c0'.mem c0'.pairs th') Ea Eu ∧ na0 ≤ th'.nalloc ∧
      FreshRun (gOf p k arch c0' i) E0 na0 E' ∧ TermTyped.IniLoc Z E0 E' ∧
      TermTyped.IniHeld H E0 E' th'.vs.vWr ∧ Q th' E' := by
  obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc0'
  rw [hth] at hth'
  cases hth'
  obtain ⟨E', hF, hx', hT', hm', hD, hA', hQ⟩ := hstep r hr hpa
  have hwu := tstep_wrUp _ _ _ _ r hr
  have hfb' := FrBound_foot hF hwu hfb hfr.1
  have hg : gOf p k arch c0' i = gOf p k arch c0 i := TermTyped.gOf_thread hs
  refine ⟨r.2.2, E', _, _, e3, hF, hD, fun l hl => TermK5V.pub_vWr hl hr, Ext_trans hx hx', hT', ?_,
    StoClo_EFoot hF.1 hSC, by rw [hg]; exact hbo, hfb'.1, ?_, Nat.le_trans hna hwu.2.2.1, ?_,
    TermTyped.IniLoc_foot hF (fun _ h => .inl h) hfb hIL, TermTyped.IniHeld_foot hF hwu.1 hfb hHr hIH, hQ⟩
  · rw [hg, e1, e2]
    exact hm'
  · rw [e1, e2]
    exact ⟨hfb'.2, hA', hfr.2.2⟩
  · intro l cl h0l hl
    rw [hg]
    rcases hF.1.2.2.1 l with e | ⟨⟨j, hj1, -, hlj⟩, -⟩
    · rw [e] at hl
      exact hfresh l cl h0l hl
    · exact ⟨j, Nat.le_trans hna hj1, hlj⟩

/-- (runAgree; shared) **One thread step of the tied typed run** (`InvAtXFZ`'s components), at
a footprint whose ghost `zf` is `Z ∨ W` and whose `pf` is the stepper's `publish` labels: the caller
excludes a `bufInit` at `Z ∨ W` (`hZW`) and carries its own provenance facts along `hF`/`hD`/`hvw`. -/
theorem xfz_thread {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 E Eu Ea : TEnv} {n0 v0 na0 : Nat}
    {Z W : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} {c0 c0' : Cfg} {th : TTh} [ProgRetIall p] [WrIniC]
    (hP : ProgT p) (hsc0 : ScopeAt p i c0) (hvI0 : TermViewInv.ViewInv c0) (hwin0 : NoHoldPubA p k arch Eu Ea i c0)
    (hth : c0.ths[i]? = some th) (hx : Ext E0 E) (hTE : ThInvE p E th)
    (hm : MemInv (gOf p k arch c0 i) E (stOf c0.mem c0.pairs th)) (hSC : StoClo E)
    (hbo : (gOf p k arch c0 i).boxFence = true) (hfb : FrBound E0 n0 v0 E)
    (hfr : FrRunA E0 n0 v0 E (stOf c0.mem c0.pairs th) Ea Eu) (hna : na0 ≤ th.nalloc)
    (hfresh : FreshRun (gOf p k arch c0 i) E0 na0 E) (hIL : TermTyped.IniLoc Z E0 E)
    (hIH : TermTyped.IniHeld H E0 E th.vs.vWr)
    (hs : c0' ∈ threadSteps p k arch c0 i) (hc0' : Certified p k arch c0' i)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hZW : ∀ l, BufInitOn th l → Z l ∨ W l → False)
    (hHr : ∀ l o τ, (c0.mem.size ≤ τ ∨ (τ ∈ th.promises ∧ ∃ m, c0.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) →
      H l o τ) :
    ∃ th' E' s s', c0'.ths[i]? = some th' ∧
      Foot { ({ gOf p k arch c0 i with zf := fun l => Z l ∨ W l } : G) with
        pf := fun l => TermOwnG0Defs.PubAt th l } E E' s s' ∧
      (∀ l, TermOwnG0Defs.PubAt th l → E'.pfr l ≠ none) ∧
      (∀ l, TermOwnG0Defs.PubAt th l → th'.vs.vWr = th.vs.vWr) ∧
      Ext E0 E' ∧ ThInvE p E' th' ∧ MemInv (gOf p k arch c0' i) E' (stOf c0'.mem c0'.pairs th') ∧
      StoClo E' ∧ (gOf p k arch c0' i).boxFence = true ∧ FrBound E0 n0 v0 E' ∧
      FrRunA E0 n0 v0 E' (stOf c0'.mem c0'.pairs th') Ea Eu ∧ na0 ≤ th'.nalloc ∧
      FreshRun (gOf p k arch c0' i) E0 na0 E' ∧ TermTyped.IniLoc Z E0 E' ∧
      TermTyped.IniHeld H E0 E' th'.vs.vWr := by
  obtain ⟨th', r, hth', hr, -, -, -, -⟩ := taken_promAbove hs hc0'
  rw [hth] at hth'
  cases hth'
  obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, hrp⟩ := hTE
  have hscope := hsc0 th hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hT htv hi
  obtain ⟨-, hstep⟩ := TermK5P.tstep_footprintKQ (hRP := hrp) (hPS := hPS) (hSub := hSub) (hSig := hSig)
    (g := { ({ gOf p k arch c0 i with zf := fun l => Z l ∨ W l } : G) with
      pf := fun l => TermOwnG0Defs.PubAt th l }) hP rfl
    (Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth)))
    (tstep_notDone hr) hscope hT hi hE htv hm hbo (PAx_of_step hs hc0' hth)
    (hwin0 th hth ρ η cx hE hT htv hi hm (frRunA_ext hfr hx) hfr.2.1.1 hfr.2.1.2.2.1) hZW (fun _ h => h)
  obtain ⟨th', E', s, s', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -⟩ :=
    xfz_of_foot (Q := fun _ _ => True) hth hx hSC hbo hfb hfr hna hfresh hIL hIH hs hc0' hHr
      (fun r hr hpa => let ⟨E', a1, a2, a3, a4, a5, a6⟩ := hstep r hr hpa
        ⟨E', a1, a2, a3, a4, a5, anchR_tstep a1 a4 a6 hE hT htv hi hm hscope (TermViewInv.envVR_solo (p := p) (k := k) (arch := arch) hvI0 (.refl _) hth) hr (frRunA_ext hfr hx) hfr.2.1, trivial⟩)
  exact ⟨th', E', s, s', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-- (runAgree; shared) **One promise step of the tied typed run** (`InvAtXFZ`'s components, the
environment kept). -/
theorem xfz_prom {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 E Eu Ea : TEnv} {n0 v0 na0 : Nat}
    {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} {c0 : Cfg} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts}
    (hth : c0.ths[i]? = some th) (hx : Ext E0 E) (hTE : ThInvE p E th)
    (hm : MemInv (gOf p k arch c0 i) E (stOf c0.mem c0.pairs th)) (hSC : StoClo E)
    (hbo : (gOf p k arch c0 i).boxFence = true) (hfb : FrBound E0 n0 v0 E)
    (hfr : FrRunA E0 n0 v0 E (stOf c0.mem c0.pairs th) Ea Eu) (hna : na0 ≤ th.nalloc)
    (hfresh : FreshRun (gOf p k arch c0 i) E0 na0 E) (hIL : TermTyped.IniLoc Z E0 E)
    (hIH : TermTyped.IniHeld H E0 E th.vs.vWr) :
    ∃ th', (promise c0 i a v w).ths[i]? = some th' ∧ Ext E0 E ∧ ThInvE p E th' ∧
      MemInv (gOf p k arch (promise c0 i a v w) i) E (stOf (promise c0 i a v w).mem (promise c0 i a v w).pairs th') ∧
      StoClo E ∧ (gOf p k arch (promise c0 i a v w) i).boxFence = true ∧ FrBound E0 n0 v0 E ∧
      FrRunA E0 n0 v0 E (stOf (promise c0 i a v w).mem (promise c0 i a v w).pairs th') Ea Eu ∧ na0 ≤ th'.nalloc ∧
      FreshRun (gOf p k arch (promise c0 i a v w) i) E0 na0 E ∧ TermTyped.IniLoc Z E0 E ∧
      TermTyped.IniHeld H E0 E th'.vs.vWr := by
  have hpi := promise_inv (a := a) (v := v) (w := w) hth
  refine ⟨_, hpi.2.1, hx, hTE, ?_, hSC, by rw [gOf_promise]; exact hbo, hfb, ?_, hna,
    by rw [gOf_promise]; exact hfresh, hIL, hIH⟩
  · rw [gOf_promise, hpi.2.2]
    exact MemInv_promSt hm
  · exact frRunA_prom hth hfr

theorem solo_typedXFP {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c : Cfg} {E0 : TEnv}
    {n0 v0 na0 : Nat} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    {st : Cfg} (h0 : InvAtXFP Z p k arch i E0 n0 v0 na0 st c H) {c2 : Cfg} (h : Solo p k arch i c c2)
    (hc2 : Certified p k arch c2 i)
    (hrl : ∀ l, E0.rini l ≤ E0.ini l)
    (hZp : ∀ c1 th1 c1' c3 th3 l cl, TermOwnG0Defs.SoloNP p k arch i l st c1 → c1.ths[i]? = some th1 →
      TermOwnG0Defs.PubAt th1 l → c1' ∈ threadSteps p k arch c1 i → Solo p k arch i c1' c3 →
      Certified p k arch c3 i → c3.ths[i]? = some th3 → E0.sto l = some cl → cl.owner = some E0.tid →
      ¬ BufInitOn th3 l)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h)
    (hHr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) → H l o τ := by
      exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    InvAtXFP Z p k arch i E0 n0 v0 na0 st c2 H := by
  refine (run_inv (c1 := c2) (P := fun c0 => Solo p k arch i c c0 ∧ InvAtXFP Z p k arch i E0 n0 v0 na0 st c0 H) ?_ ?_ ?_ h
    (.refl _) ⟨.refl _, h0⟩).2
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hna, hfresh, hIL, hIH, hPV, hPO⟩ hs hrest
    have hc0' : Certified p k arch c0' i := certified_back hrest hc2
    have hcert0 : Certified p k arch c0 i := certified_back (.thread hs hrest) hc2
    obtain ⟨th', E', s, s', hth', hF, hD, hvw, hx', hT', hm', hSC', hbo', hfb', hfr', hna', hfresh', hIL', hIH'⟩ :=
      xfz_thread (W := fun l => TermK5P.PubZ E0 E l ∨ TermK5O.PubZO p k arch i E0 st c0 l) (hPS := hPS)
        (hSub := hSub) (hSig := hSig) hP (hsc c0 hc0 hcert0) (TermViewInv.viewInv_solo hvI hc0) (hwin c0 hc0 hcert0) hth hx hTE hm hSC hbo hfb hfr
        hna hfresh hIL hIH hs hc0'
        (fun l hbi hz => hz.elim (hZr c0 hc0 hcert0 th hth l hbi) fun hz => hz.elim
          (TermK5P.pubZ_noBufInit hPV (fun c1 th1 c1' l cl h1 h2 h3 h4 h5 h6 h7 _ =>
            hZp c1 th1 c1' c0 th l cl h1 h2 h3 h4 h5 hcert0 hth h6 h7) l hbi)
          (TermK5O.pubZO_noBufInit (fun c1 th1 c1' l cl _ h1 h2 h3 h4 h5 h6 h7 _ =>
            hZp c1 th1 c1' c0 th l cl h1 h2 h3 h4 h5 hcert0 hth h6 h7) l hbi))
        (hHr c0 hc0 hcert0 th hth)
    have hU := (hIH' hrl).2.1
    exact ⟨solo_trans hc0 (.thread hs (.refl _)), th', E', hth', hx', hT', hm', hSC', hbo', hfb', hfr', hna',
      hfresh', hIL', hIH', TermK5P.pfrProv_thread hPV hF hfb (fun _ h => h) (fun _ h => .inr (.inl h)) hD hs hth hvw hU,
      TermK5O.pfrProvO_thread hPO hF hfb hx (fun _ h => .inr (.inr h)) hs hth hvw hU⟩
  · rintro c0 a v w ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hna, hfresh, hIL, hIH, hPV, hPO⟩ hw _
    obtain ⟨th', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
      xfz_prom (a := a) (v := v) (w := w) hth hx hTE hm hSC hbo hfb hfr hna hfresh hIL hIH
    exact ⟨solo_trans hc0 (.prom a v w hw (.refl _)), th', E, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      TermK5P.pfrProv_prom hPV hw, TermK5O.pfrProvO_prom hPO hw⟩
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hna, hfresh, hIL, hIH, hPV, hPO⟩ hs _
    obtain ⟨x1, a1, e1, evs, hterm, rfl⟩ := extSteps_thread hs hth
    exact ⟨solo_trans hc0 (.ext hs (.refl _)), _, E, set_self hth, hx, TermTyped.ThInvE_emit hterm hTE,
      by rw [gOf_ext hs]; exact hm, hSC, by rw [gOf_ext hs]; exact hbo, hfb, hfr, hna, by rw [gOf_ext hs]; exact hfresh, hIL, hIH,
      TermK5P.pfrProv_ext hPV hs, TermK5O.pfrProvO_ext hPO hs⟩

/-- **`certified_promLoc`**: an outstanding promise of a certified thread
lies at a cell of the start environment `E0` or at one of the thread's labels
of index at least `na0` (its allocation count at the start).  The promise is
fulfilled along the certificate by a single-word write `SW` at a typed
configuration (`certified_fulfilC`, `solo_typedXF`), which lands on a cell of
that configuration's environment (`SWOne_holds`); that cell is `E0`'s or new
in the run (`FreshRun`). -/
theorem certified_promLoc {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {E0 : TEnv} {Eu Ea : TEnv}
    {n0 v0 na0 : Nat} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch Eu Ea i c0)
    (h0 : InvAtXF p k arch i E0 n0 v0 na0 c (Ea := Ea) (Eu := Eu)) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ TermFul.promsOf c i) (hm : c.mem[t]? = some m) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    (∃ cl, E0.sto m.loc.label = some cl) ∨ ∃ j, na0 ≤ j ∧ m.loc.label = freshLabel c.lbase c.n i j := by
  obtain ⟨m', hm', c1, c2, th1, h1, h2, hc2, hth1, -, -, -, hsw⟩ := certified_fulfilC hc (pwf_of_inv h0.toInvAt) ht
  rw [hm] at hm'
  cases hm'
  have hc1 : Certified p k arch c1 i := certified_back (.thread h2 (.refl _)) hc2
  obtain ⟨th1', E1, hth1', -, ⟨ρ, η, cx, rfl, hE, hT, htv, hi, -⟩, hmi1, -, -, -, -, -, hfresh, -, -⟩ :=
    solo_typedXF hP hsc hvI hwin h0 h1 hc1 hPS hSub hSig
  rw [hth1] at hth1'
  cases hth1'
  have hscope := hsc c1 h1 hc1 th1 hth1 (TermTyped.not_spawnT_of_steps hth1 h2) ρ η cx hE hT htv hi
  obtain ⟨cl, -, -, -, -, hcl, -⟩ :=
    SWOne_holds p _ _ _ _ ρ η cx _ _ hE hT htv hi hmi1 (TermTyped.scopeD_SW hscope hsw) (certified_promAboveSt hc1 hth1) hsw
  cases e : E0.sto m.loc.label with
  | some cl0 => exact .inl ⟨cl0, rfl⟩
  | none =>
    obtain ⟨j, hj, hl⟩ := hfresh _ cl e hcl
    rw [gOf_solo h1] at hl
    exact .inr ⟨j, hj, hl⟩

#print axioms solo_typedXF
#print axioms certified_promLoc

/-! ## Field forms -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

theorem promise_lbase (c : Cfg) (i : Nat) (a : Address) (v : WeakMem.Val) (w : Ts) :
    (promise c i a v w).lbase = c.lbase := by
  unfold promise
  split <;> rfl

/-- **The `PromLocF`** at a promise step, from `certified_promLoc` at
the promised configuration, started at the promiser's cut (`SysInvN.thr`).
Run hypothesis `hrun`: scope and `NoHoldPub` along the certificate. -/
theorem promLocP (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hrun : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
      {a : Address} {v : WeakMem.Val} {w : Ts},
      PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      ∀ S, ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S →
      ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j →
        ScopeAt p j c1 ∧ NoHoldPubA p k arch (Cut Eg j S) (Cut Eg j S) j c1)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    (∃ cl, cutSto Eg j a.label = some cl) ∨ ∃ m, th.nalloc ≤ m ∧ a.label = freshLabel c.lbase c.n j m := by
  obtain ⟨S, hS⟩ := X.inv.thr j th X.hth
  obtain ⟨-, hTE, hm, -⟩ := id hS
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hSC : StoClo (Cut Eg j S) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  have h0 := InvAtXF_of (p := p) (k := k) (arch := arch) hpi.2.1 hTE
    (by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm) hSC (by rw [gOf_promise]; exact X.inv.bf)
    (by rw [hpi.2.2]; exact TermTyped.riniCoh_promSt (X.inv.riniCoh j th S X.hth))
    (fun l cl f hs hp => Nat.le_trans (X.inv.frlt l cl f (cutSto_sub hs) hp)
      (by show c.mem.size - 1 ≤ (promise c j a v w).mem.size - 1; rw [hpi.1, Array.size_push]; exact Nat.sub_le_sub_right (Nat.le_succ _) 1))
  have ht : c.mem.size ∈ TermFul.promsOf (promise c j a v w) j := by
    rw [TermFul.promsOf_some hpi.2.1]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have hmt : (promise c j a v w).mem[c.mem.size]? = some ⟨a, v, w⟩ := by
    rw [hpi.1]; exact Array.getElem?_push_size
  have h := certified_promLoc hP (fun c1 h1 h2 => (hrun X S hS c1 h1 h2).1) (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc')
    (fun c1 h1 h2 => (hrun X S hS c1 h1 h2).2)
    h0 X.cert ht hmt
  simp only [promise_lbase, TermStep.promise_n, TermStep.promise_size] at h
  exact h hPS hSub hSig

/-- **`certified_promLoc` at a thread step**: every promise the stepper has
at the source lies at a cell of its cut or at one of its labels yet to
allocate.  Certification of the source: the step followed by the
successor's certificate. -/
theorem promLocT (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (hrun : ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ScopeAt p i c1 ∧ NoHoldPubA p k arch (Cut Eg i S) (Cut Eg i S) i c1)
    {t : Ts} {m : Msg} (ht : t ∈ th.promises) (hm : c.mem[t]? = some m) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    (∃ cl, cutSto Eg i m.loc.label = some cl) ∨
      ∃ j, th.nalloc ≤ j ∧ m.loc.label = freshLabel c.lbase c.n i j := by
  obtain ⟨S, hS⟩ := X.inv.thr i th X.hth
  obtain ⟨-, hTE, hmi, -⟩ := id hS
  have hSC : StoClo (Cut Eg i S) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  have h0 := InvAtXF_of (p := p) (k := k) (arch := arch) X.hth hTE hmi hSC X.inv.bf
    (X.inv.riniCoh i th S X.hth) (fun l cl f hs hp => X.inv.frlt l cl f (cutSto_sub hs) hp)
  have hc : Certified p k arch c i := by
    obtain ⟨c'', hs, hn⟩ := X.cert
    exact ⟨c'', .thread X.hc' hs, hn⟩
  exact certified_promLoc hP (fun c1 h1 h2 => (hrun S hS c1 h1 h2).1) (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') (fun c1 h1 h2 => (hrun S hS c1 h1 h2).2) h0 hc
    (by rw [TermFul.promsOf_some X.hth]; exact ht) hm hPS hSub hSig

/-- The run-level premise of `promLocP` (scope and `NoHoldPub` along the
certificate of every reachable promise step), as a named obligation. -/
def CertRunP (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ S, ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S →
    ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j →
      ScopeAt p j c1 ∧ NoHoldPubA p k arch (Cut Eg j S) (Cut Eg j S) j c1

/-- **The `PromLocF` discharged** from `ProgT` and `CertRunP`. -/
theorem promLocF_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : PromLocF p k arch Sp Init MintOK c0 :=
  fun X => promLocP (hV0 := hV0) hP hrun X hPS hSub hSig

end

#print axioms promLocP
#print axioms promLocT
#print axioms promLocF_of

/-! ## The numeric predecessor at an epoch unit (the `PromPred`, epoch case)

The certificate fulfils the promise `t` by a step at a typed configuration
`c1`.  At an epoch-counter unit that step is an RMW (E's structural fact: plain
word stores need a token no epoch protocol hands out), whose read is the
message adjacent below `t` (`stepRmw_ful`: `rmwAdjacent`, `tr < t`), typed and
numeric at a non-ghost word (`fetch_ful_core`/cas load paths).  That one-step,
stage-A fact is the named hypothesis `StepPredNum`; the certificate argument
and the transport back to `c` (`PredAt_prefix`) are proved here. -/

/-- `PromPred` restricted to epoch-counter units (the only case consumed). -/
def PromPredE (E : TEnv) (s : St) : Prop :=
  ∀ t m, t ∈ s.promises → s.mem[t]? = some m → IniWr E m.loc → ∀ n P, WordAt E m.loc n P → P.epoch = true →
    ∃ w, PredAt s.mem m.loc t w ∧ ∃ k, w.val = .num k

/-- (named hypothesis; one step, stage A, no run) **A typed step that fulfils
an own promise at an initialised epoch-counter unit reads the numeric message
adjacent below it.**  Discharge sketch: (E) only RMWs write epoch units
(`storeWord*` need `tok r (some (P, i))`, never handed out for epoch `P`;
`casCell`/`fetchCell`/`storePub`/`storeOwn` need `wordOf … = none`; `stp`/`casp`
target `word2`/`epair`), so the fulfil is `stepRmw`'s; `stepRmw_ful` gives
`rmwAdjacent mem a tr t`, `tr < t`, `mr.loc = a`, i.e. `PredAt mem a t (mw mr)`;
the read value is typed (`fetch_ful_core`'s `hcell`, the cas load path) and a
non-ghost word value is a number. -/
def StepPredNum (p : Prog) : Prop :=
  ∀ (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (ρ : Nat → Nat) (η : TEnv) (cx : Cx), g.p = p →
    EnvOK p η → Typed p cx th.term → TvOK cx → FInv ρ η th.σs (Resume p th.stack) cx th.env →
    MemInv g (CE η) (stOf mem pairs th) → StepScope cx th.term → PromAbove (stOf mem pairs th) →
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
    ∀ t m, t ∈ th.promises → t ∉ r.2.2.promises → mem[t]? = some m → IniWr (CE η) m.loc →
      ∀ n P, WordAt (CE η) m.loc n P → P.epoch = true → ∃ w, PredAt mem m.loc t w ∧ ∃ k, w.val = .num k

/-- `IniWr` and `WordAt` survive an extension. -/
theorem IniWr_ext {E E' : TEnv} (hx : Ext E E') {a : Address} {c : Cell} (hc : E.sto a.label = some c)
    (h : IniWr E a) : IniWr E' a := by
  intro c' N e us hc' hT hus
  rw [hx.2.2.2.2.1 _ _ hc] at hc'
  cases hc'
  have h1 := h c N e us hc hT hus
  have h2 : E.rc a.label ≤ E'.rc a.label := by
    unfold TEnv.rc
    have a1 := hx.2.2.2.2.2.1 a.label
    have a2 := hx.rini a.label
    omega
  exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ h2)

theorem WordAt_ext {E E' : TEnv} (hx : Ext E E') {a : Address} {n : Nat} {P : Proto} (h : WordAt E a n P) :
    WordAt E' a n P := by
  obtain ⟨c, hc, h1, h2⟩ := h
  exact ⟨c, hx.2.2.2.2.1 _ _ hc, h1, h2⟩

/-- **The epoch predecessor from the certificate.** -/
theorem certified_promPredE {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {E0 : TEnv}
    {n0 v0 na0 : Nat} [ProgRetIall p] [WrIniC] (hP : ProgT p) (hstep : StepPredNum p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (h0 : InvAtXF p k arch i E0 n0 v0 na0 c) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ TermFul.promsOf c i) (hm : c.mem[t]? = some m) (hIW : IniWr E0 m.loc)
    {n : Nat} {P : Proto} (hW : WordAt E0 m.loc n P) (hep : P.epoch = true) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ w, PredAt c.mem m.loc t w ∧ ∃ k, w.val = .num k := by
  have hpwf := pwf_of_inv h0.toInvAt
  obtain ⟨m', hm', c1, c2, th1, h1, h2, hc2, hth1, hm1, ht1, hn2, -⟩ := certified_fulfilC hc hpwf ht
  rw [hm] at hm'
  cases hm'
  have hc1 : Certified p k arch c1 i := certified_back (.thread h2 (.refl _)) hc2
  obtain ⟨th1', E1, hth1', hx1, ⟨ρ, η, cx, rfl, hE, hT, htv, hi, hrp⟩, hmi1, -⟩ := solo_typedXF hP hsc hvI hwin h0 h1 hc1 hPS hSub hSig
  rw [hth1] at hth1'
  cases hth1'
  have hscope := hsc c1 h1 hc1 th1 hth1 (TermTyped.not_spawnT_of_steps hth1 h2) ρ η cx hE hT htv hi
  obtain ⟨th', r, hth', hr, e1, e2, e3, -⟩ := threadSteps_inv h2
  rw [hth1] at hth'
  cases hth'
  have hpa : PromAbove (stOf r.1 r.2.1 r.2.2) := by
    have h := certified_promAboveSt hc2 e3
    rw [e1, e2] at h
    exact h
  have hn : t ∉ r.2.2.promises := by rw [TermFul.promsOf_some e3] at hn2; exact hn2
  replace hscope : StepScope cx th1.term := by
    rcases hscope with h | ⟨-, hcap⟩
    · exact h
    · have e := ((tstep_cap hP hcap hT hi hE htv hrp hPS).2 r hr).2.2.2.2.1
      simp only [stOf] at e
      exact absurd (e ▸ ht1) hn
  obtain ⟨c0, hc0, -⟩ := id hW
  obtain ⟨w, hpw, hnum⟩ := hstep (gOf p k arch c1 i) c1.mem c1.pairs th1 ρ η cx rfl hE hT htv hi hmi1 hscope
    (certified_promAboveSt hc1 hth1) r hr hpa t m ht1 hn hm1 (IniWr_ext hx1 hc0 hIW) n P (WordAt_ext hx1 hW) hep
  obtain ⟨th0, -, hth0, -⟩ := h0
  obtain ⟨-, -, -, -, -, hme, -⟩ := solo_winInv h1 (winInv_refl hth0)
  have htlt : t < c.mem.size := (hpwf.2 t ht).1
  have hp : ∀ t', t' < c.mem.size → c1.mem[t']? = c.mem[t']? := fun t' h' => by
    have e : c.mem[t']? = some c.mem[t'] := by simp [h']
    rw [e]; exact hme t' _ e
  exact ⟨w, (PredAt_prefix hp (Nat.le_of_lt htlt)).2 hpw, hnum⟩

/-- **`PromPredE` at a thread step** (field form, at the stepper's cut). -/
theorem promPredT {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    [ProgRetIall p] [WrIniC] (hP : ProgT p) (hstep : StepPredNum p)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hrun : ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ScopeAt p i c1 ∧ NoHoldPubA p k arch (Cut Eg i S) (Cut Eg i S) i c1) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PromPredE (CE η) (stOf c.mem c.pairs th) := by
  intro t m ht hm hIW n P hW hep
  rw [Y.1] at hIW hW
  obtain ⟨S', hS'⟩ := X.inv.thr i th X.hth
  obtain ⟨-, hTE, hmi, -⟩ := id hS'
  have hSC : StoClo (Cut Eg i S') := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  have h0 := InvAtXF_of (p := p) (k := k) (arch := arch) X.hth hTE hmi hSC X.inv.bf
    (X.inv.riniCoh i th S' X.hth) (fun l cl f hs hp => X.inv.frlt l cl f (cutSto_sub hs) hp)
  have hc : Certified p k arch c i := by
    obtain ⟨c'', hs, hn⟩ := X.cert
    exact ⟨c'', .thread X.hc' hs, hn⟩
  exact certified_promPredE hP hstep (fun c1 h1 h2 => (hrun S' hS' c1 h1 h2).1) (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc')
    (fun c1 h1 h2 => (hrun S' hS' c1 h1 h2).2) h0 hc
    (by rw [TermFul.promsOf_some X.hth]; exact ht) hm hIW hW hep hPS hSub hSig

#print axioms certified_promPredE
#print axioms InvAtXFP.toF
#print axioms InvAtXFP_of
#print axioms xfz_thread
#print axioms xfz_prom
#print axioms solo_typedXFP
#print axioms promPredT

end TermNoHold
