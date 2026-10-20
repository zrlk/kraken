import WeakCore.TermOwnK5
import WeakCore.TermPlantAtW
import WeakCore.TermOwnX2

/-!
# TermNoBufOwn: no certificate `bufInit` at an own cell without its own key

At an own cell `x` of the stepper with no own key of `x` in its frame and private holding
(`(Tot i + HP i) (.own x) = 0`, the negation of `TermPlantAtT.KeyG`), the own-key bound `OwnXLe 0`
holds at the step (`TermOwnX2.ownXLe_start_le`), so no own-mode use of `x` occurs along a certificate run
(`TermOwnK5.ownXLe0_prom_noOwnUse`, `ownXLe0_run_noOwnUse`), and no `bufInit` there targets `x`
(`TermOwnK5.bufInit_ne_of_use`): `noBufF_noKey` (promise step), `noBufT_noKey` (thread step).
-/

namespace TermNoBufOwn
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnK5 TermCertScope
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A typing without own use of `x` excludes `BufInitOn th x`. -/
theorem not_bufInitOn {p : Prog} {th : TTh} {x : AllocLabel}
    (h : ∃ ρ η cx Rf Rs, EnvOK p η ∧ Typed p cx th.term ∧ FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧
      ∀ a t c₁ rt ws ad g, cx.use a = .ok (t, c₁) →
        ((∃ u, cellOf t = some (.own, u)) ∨ ∃ n u k, bufOf t = some (.own, n, u, k)) →
        evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad g] → ad.label ≠ x) :
    ¬ BufInitOn th x := by
  rintro ⟨y, bb, ib, v, e, rt, w, ad, g, hterm, hev, hw, hl⟩
  exact bufInit_ne_of_use hterm h rt w ad g hev hw hl

/-- **No `bufInit` at a key-less own cell** along a promise step's certificate runs. -/
theorem noBufF_noKey [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : CertWinP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {x : AllocLabel} {cl : Cell} (hsto : Eg.sto x = some cl) (hin : cl.owner = some j ∨ Eg.pfr x ≠ none)
    (hk0 : (Tot j + HP j) (.own x) = 0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j → ∀ th1, c1.ths[j]? = some th1 →
      ¬ BufInitOn th1 x := by
  intro c1 h1 hc1 th1 hth1
  obtain ⟨S, hS⟩ := X.inv.thr j th X.hth
  obtain ⟨th2, hth2, h⟩ := ownXLe0_prom_noOwnUse hP (winQP hsc hw X hS) (TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw)
    (ownXLe_start_le X.inv X.hth hS hsto hin (Nat.le_of_eq hk0)) X.hw h1 hc1 hPS hSub hSig
  obtain rfl : th2 = th1 := Option.some.inj (hth2.symm.trans hth1)
  exact not_bufInitOn h

/-- **No `bufInit` at a key-less own cell** along a thread step's certificate runs (from `c'`). -/
theorem noBufT_noKey [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeC p k arch Sp Init MintOK c0) (hw : CertWinC p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    {x : AllocLabel} {cl : Cell} (hsto : Eg.sto x = some cl) (hin : cl.owner = some i ∨ Eg.pfr x ≠ none)
    (hk0 : (Tot i + HP i) (.own x) = 0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ c1, Solo p k arch i c' c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ¬ BufInitOn th1 x := by
  intro c1 h1 hc1 th1 hth1
  obtain ⟨S, hS⟩ := X.inv.thr i th X.hth
  obtain ⟨th2, hth2, h⟩ := ownXLe0_run_noOwnUse hP (winQC hsc hw X hS) (TermViewInv.viewInv_run hV0 X.run)
    (ownXLe_start_le X.inv X.hth hS hsto hin (Nat.le_of_eq hk0)) (.thread X.hc' h1) hc1 hPS hSub hSig
  obtain rfl : th2 = th1 := Option.some.inj (hth2.symm.trans hth1)
  exact not_bufInitOn h

/-- (F side of `noFul_pre`) **The plant edge stays outstanding along a promise step's certificate
runs** not publishing `l` (start `promise c j a v w`, `NFInv` carried by `nfInv_prom`). -/
theorem noFul_preP {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : CertWinP p k arch Sp Init MintOK c0)
    (hNP : TermPtrKey.NoFulPlRunGL p k arch)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hk : k.storeDepRts = true) {l : AllocLabel} {cl : Cell} {f t : Ts}
    (hsto : Eg.sto l = some cl) (hown : cl.owner = some j) (hf : Eg.pfr l = some f)
    (hnp : TermPlantAtT.KeyG Tot HP j l) (htm : TermPtrRts.tminG Eg c j l = some t) :
    ∀ c2 th2, TermOwnG0Defs.SoloNP p k arch j l (promise c j a v w) c2 → Certified p k arch c2 j →
      c2.ths[j]? = some th2 → t ∈ th2.promises := by
  obtain ⟨S, hS⟩ := X.inv.thr j th X.hth
  exact TermPlantAtW.noFul_ofNF hNP hps hk
    (TermPtrKey.nfInv_prom (TermPlantAtW.nfInv_pre hps h0d X.inv X.run X.hth hS hk hsto hown hf hnp htm))
    (fun c2 h2 hc2 => hsc X c2 h2 hc2) (TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw) (fun c2 h2 hc2 => (hw X).1 S hS c2 h2 hc2)

/-- **The window along a promise step's certificate** at a key-holding own frontier cell `l`:
every certified configuration reached without publishing `l` has `vWr ≤ mP.view`, `mP` the plant
edge's message (`TermPtrRts.winLe_gen`). -/
theorem winF {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : CertWinP p k arch Sp Init MintOK c0)
    (hNP : TermPtrKey.NoFulPlRunGL p k arch)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hk : k.storeDepRts = true) {l : AllocLabel} {cl : Cell} {f t : Ts} {mP : Msg}
    (hsto : Eg.sto l = some cl) (hown : cl.owner = some j) (hf : Eg.pfr l = some f)
    (hnp : TermPlantAtT.KeyG Tot HP j l) (htm : TermPtrRts.tminG Eg c j l = some t) (hmP : c.mem[t]? = some mP) :
    ∀ c2 th2, TermOwnG0Defs.SoloNP p k arch j l (promise c j a v w) c2 → Certified p k arch c2 j →
      c2.ths[j]? = some th2 → th2.vs.vWr ≤ mP.view := by
  intro c2 th2 h2 hc2 hth2
  have hNo := noFul_preP (hV0 := hV0) hps h0d hsc hw hNP X hk hsto hown hf hnp htm
  have hlt : t < c.mem.size := TermMem.lt_of_get hmP
  have hmB : ∀ c3, TermOwnG0Defs.SoloNP p k arch j l (promise c j a v w) c3 → c3.mem[t]? = some mP :=
    fun c3 h3 => W2New.solo_mem h3.toSolo (by
      rw [(TermLiveProps.promise_ext _ _ a v w).get t hlt]; exact hmP)
  obtain ⟨cs, hs, hn⟩ := hc2
  exact TermPtrRts.winLe_gen (j := j) (a := l) hNo hmB hs hn h2 th2 hth2 (hNo c2 th2 h2 ⟨cs, hs, hn⟩ hth2)

/-- **A solo run either never publishes `l`, or splits at its first `publish` naming `l`.** -/
theorem solo_split {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {l : AllocLabel} {c c2 : Cfg}
    (h : Solo p k arch i c c2) :
    TermOwnG0Defs.SoloNP p k arch i l c c2 ∨
      ∃ c1 th1 c1', TermOwnG0Defs.SoloNP p k arch i l c c1 ∧ c1.ths[i]? = some th1 ∧
        TermOwnG0Defs.PubAt th1 l ∧ c1' ∈ threadSteps p k arch c1 i ∧ Solo p k arch i c1' c2 := by
  induction h with
  | refl => exact .inl (.refl _)
  | thread hs hrest ih =>
    rename_i c3 c4 c5
    by_cases hp : ∃ th, c3.ths[i]? = some th ∧ TermOwnG0Defs.PubAt th l
    · obtain ⟨th, hth, hpa⟩ := hp
      exact .inr ⟨c3, th, c4, .refl _, hth, hpa, hs, hrest⟩
    · have hn : ∀ th, c3.ths[i]? = some th → ¬ TermOwnG0Defs.PubAt th l := fun th h1 h2 => hp ⟨th, h1, h2⟩
      rcases ih with h1 | ⟨c1, th1, c1', h1, hth1, hpa, hs1, hr1⟩
      · exact .inl (.thread hs hn h1)
      · exact .inr ⟨c1, th1, c1', .thread hs hn h1, hth1, hpa, hs1, hr1⟩
  | prom a v w hw hrest ih =>
    rcases ih with h1 | ⟨c1, th1, c1', h1, hth1, hpa, hs1, hr1⟩
    · exact .inl (.prom a v w hw h1)
    · exact .inr ⟨c1, th1, c1', .prom a v w hw h1, hth1, hpa, hs1, hr1⟩

/-- **No `bufInit` at an own cell after the run publishes it** (thread step, from `c'`; the promise
step's form is `TermK5R.bufInitPubFR`). -/
theorem noBufT_pub [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeC p k arch Sp Init MintOK c0) (hw : CertWinC p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    {l : AllocLabel} {cl : Cell} (hsto : Eg.sto l = some cl) (hin : cl.owner = some i ∨ Eg.pfr l ≠ none)
    {c1 c1' c2 : Cfg} {th1 th2 : TTh} (h1 : Solo p k arch i c' c1)
    (hth1 : c1.ths[i]? = some th1) (hpub : TermOwnG0Defs.PubAt th1 l) (hs : c1' ∈ threadSteps p k arch c1 i)
    (h2 : Solo p k arch i c1' c2) (hc2 : Certified p k arch c2 i) (hth2 : c2.ths[i]? = some th2)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ¬ BufInitOn th2 l := by
  obtain ⟨y1, a1, e1, rt1, ws1, ad1, hterm1, hea1, hws1, hx1⟩ := hpub
  obtain ⟨S, hS⟩ := X.inv.thr i th X.hth
  obtain ⟨th3, hth3, h⟩ := ownXLe_pub_noOwnUse hP (winQC hsc hw X hS) (TermViewInv.viewInv_run hV0 X.run) (ownXLe_start X.inv X.hth hS hsto hin)
    (.thread X.hc' h1) hs hth1 hterm1 hea1 hws1 hx1 h2 hc2 hPS hSub hSig
  obtain rfl : th3 = th2 := Option.some.inj (hth3.symm.trans hth2)
  exact not_bufInitOn h

/-- **The window along a thread step's certificate** at a key-holding own frontier cell `l` that the
step does not publish: every certified configuration reached from `c'` without publishing `l` has
`vWr ≤ mP.view` (`TermPlantAtW.noFul_pre` re-rooted at `c'`, `TermPtrRts.winLe_gen`). -/
theorem winT {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0)
    (hps : TermScope.ProgScopeOK p = true) (h0d : TermScope.RunScopeR p k arch Sp c0)
    (hCW : CertWinC p k arch Sp Init MintOK c0) (hNP : TermPtrKey.NoFulPlRunGL p k arch)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (hk : k.storeDepRts = true) {l : AllocLabel} {cl : Cell} {f t : Ts} {mP : Msg}
    (hsto : Eg.sto l = some cl) (hown : cl.owner = some i) (hf : Eg.pfr l = some f)
    (hnp : TermPlantAtT.KeyG Tot HP i l) (htm : TermPtrRts.tminG Eg c i l = some t) (hmP : c.mem[t]? = some mP)
    (hpub : ¬ TermOwnG0Defs.PubAt th l) :
    ∀ c2 th2, TermOwnG0Defs.SoloNP p k arch i l c' c2 → Certified p k arch c2 i →
      c2.ths[i]? = some th2 → th2.vs.vWr ≤ mP.view := by
  intro c2 th2 h2 hc2 hth2
  have hNo0 := TermPlantAtW.noFul_pre (hV0 := hV0) hps h0d hCW hNP X hk hsto hown hf hnp htm
  have hNo : ∀ c3 th3, TermOwnG0Defs.SoloNP p k arch i l c' c3 → Certified p k arch c3 i →
      c3.ths[i]? = some th3 → t ∈ th3.promises := fun c3 th3 hs hc h3 =>
    hNo0 c3 th3 (.thread X.hc' (fun th0 h0 => by rw [X.hth] at h0; cases h0; exact hpub) hs) hc h3
  obtain ⟨cs, hs, hn⟩ := hc2
  exact TermPtrRts.winLe_gen (j := i) (a := l) hNo (TermPlantAtN.mem_along X.hr X.e1 hmP) hs hn h2 th2 hth2
    (hNo c2 th2 h2 ⟨cs, hs, hn⟩ hth2)

end TermNoBufOwn

#print axioms TermNoBufOwn.not_bufInitOn
#print axioms TermNoBufOwn.noBufF_noKey
#print axioms TermNoBufOwn.noBufT_noKey
#print axioms TermNoBufOwn.noFul_preP
#print axioms TermNoBufOwn.winF
#print axioms TermNoBufOwn.solo_split
#print axioms TermNoBufOwn.noBufT_pub
#print axioms TermNoBufOwn.winT
