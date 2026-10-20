import WeakCore.TermNoHold

/-!
# TermXFO: the tied typed run with the post-publish provenance only (runAgree)

The thread-step consumers of `RunAgreeT` (`TermPlantF.pubPromOK_of`, `W2Pub.pubWordW_of`) run the
certificate of the stepper's successor from its post-step environment `E'`. Their run carries
`PfrProvO` (the counts at the own cells of `E'` with a frontier, `TermK5O`) but not `PfrProvE`: the
step's fresh cells have no frontier in `E'`, and `PfrProvE`'s ghost would need their post-publish
`bufInit` exclusion. `solo_typedXFO` is `TermNoHold.solo_typedXFP` without the `PfrProvE` half,
from the shared step lemmas `xfz_thread`/`xfz_prom`; `certified_promNotUndefXO` composes
`TermTyped.certified_promNotUndefX` (the value), `TermTyped.certified_promTypedX` (the fulfilling
configuration) and `solo_typedXFO` (the environment there).
-/

namespace TermXFO
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermFul TermGlob TermTyped TermMain TermInterf TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- `InvAtXFZ` with the run's post-publish provenance `PfrProvO` from the run start `st`. -/
def InvAtXFO (Z : AllocLabel → Prop) (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (E0 : TEnv)
    (n0 v0 na0 : Nat) (st c : Cfg) (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) (Ea : TEnv := E0) (Eu : TEnv := Ea) : Prop :=
  ∃ th E, c.ths[i]? = some th ∧ Ext E0 E ∧ ThInvE p E th ∧ MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧
    StoClo E ∧ (gOf p k arch c i).boxFence = true ∧ FrBound E0 n0 v0 E ∧ FrRunA E0 n0 v0 E (stOf c.mem c.pairs th) Ea Eu ∧
    na0 ≤ th.nalloc ∧ FreshRun (gOf p k arch c i) E0 na0 E ∧ TermTyped.IniLoc Z E0 E ∧
    TermTyped.IniHeld H E0 E th.vs.vWr ∧ TermK5O.PfrProvO p k arch i H E0 st c E

theorem InvAtXFO.toF {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 : TEnv} {Eu Ea : TEnv} {n0 v0 na0 : Nat}
    {st c : Cfg} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop}
    (h : InvAtXFO Z p k arch i E0 n0 v0 na0 st c H (Ea := Ea) (Eu := Eu)) : InvAtXFZ Z p k arch i E0 n0 v0 na0 c H (Ea := Ea) (Eu := Eu) :=
  let ⟨th, E, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, _⟩ := h
  ⟨th, E, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩

theorem InvAtXFO.toZ {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 : TEnv} {Eu Ea : TEnv} {n0 v0 na0 : Nat}
    {st c : Cfg} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop}
    (h : InvAtXFO Z p k arch i E0 n0 v0 na0 st c H (Ea := Ea) (Eu := Eu)) : InvAtXZ Z p k arch i E0 n0 v0 c H (Ea := Ea) (Eu := Eu) :=
  let ⟨th, E, a1, a2, a3, a4, a5, a6, a7, a8, _, _, a11, a12, _⟩ := h
  ⟨th, E, a1, a2, a3, a4, a5, a6, a7, a8, a11, a12⟩

/-- The start: the invariant's own environment, nothing published (from `InvAtXFP_of`). -/
theorem InvAtXFO_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E : TEnv} {c : Cfg} {th : TTh}
    (hth : c.ths[i]? = some th) (hT : ThInvE p E th)
    (hm : MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th)) (hSC : StoClo E)
    (hbo : (gOf p k arch c i).boxFence = true) (hrc : TermTyped.RiniCoh E (stOf c.mem c.pairs th))
    (hfl : ∀ l cl f, E.sto l = some cl → E.pfr l = some f → f ≤ c.mem.size - 1) (Z : AllocLabel → Prop := fun _ => False)
    (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) :
    InvAtXFO Z p k arch i E c.mem.size th.vs.vWr th.nalloc c c H :=
  let ⟨th, E, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, _, a14⟩ := InvAtXFP_of hth hT hm hSC hbo hrc hfl Z H
  ⟨th, E, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a14⟩

/-- (certWin-D) `InvAtXFO_of` anchored at any `Ea` with `AnchR` there (the post-step start). -/
theorem InvAtXFO_ofA {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E Eu Ea : TEnv} {c : Cfg} {th : TTh}
    (hth : c.ths[i]? = some th) (hT : ThInvE p E th)
    (hm : MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th)) (hSC : StoClo E)
    (hbo : (gOf p k arch c i).boxFence = true) (hA : AnchR Eu Ea E (stOf c.mem c.pairs th)) (hx : Ea = E ∨ Ext Ea E)
    (Z : AllocLabel → Prop := fun _ => False) (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) :
    InvAtXFO Z p k arch i E c.mem.size th.vs.vWr th.nalloc c c H Ea Eu := by
  obtain ⟨ρ, η, cx, rfl, h⟩ := hT
  exact ⟨th, CE η, hth, Ext_refl (Coh_CE η) (CohR_CE η), ⟨ρ, η, cx, rfl, h⟩, hm, hSC, hbo,
    FrBound_refl _ _ _, frRunA_startA hA hx,
    Nat.le_refl _, (fun l c h0 h => by rw [h0] at h; cases h), TermTyped.IniLoc_refl _ _,
    TermTyped.IniHeld_refl _ _ _, TermK5O.pfrProvO_start _ _ _ _ _ _ _⟩

/-- (certWin-D) **The post-step start**: at a thread step `c → c'` (`TCtx`), the S6 witness `E'` (`TOutC`)
is anchored at the pre-step cut `Cut Eg i S` (`AnchR`, `Ext`), from `ThSysAt` at `S` (the cut's typing and
`MemInv`), the scope at `c`, and the stepper's frontier change only at a published label (`PfrG` at
`pf := PubAt th`; a `bufInit` publishes nothing).  Pre-step data only. -/
theorem anchPost [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 c c' : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {η : TEnv}
    {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res} {Rf Rs H : Res} {cr2 db2 : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (hCE : CE η = Cut Eg i S)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs H cr2 db2 δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hPfr : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    (hsc : ScopeAt p i c) :
    AnchR (Cut Eg i S) (Cut Eg i S) E' (stOf r.1 r.2.1 r.2.2) ∧ Ext (Cut Eg i S) E' := by
  obtain ⟨hF, hRE, hm', -, -, -, -, -, -, -, -, -, -, -, hWL⟩ := Z
  obtain ⟨-, η'', -, -, -, rfl, -⟩ := hRE
  obtain ⟨-, ⟨ρ', η', cx', hCE', hE', hT', htv', hi', -⟩, hm, -⟩ := hS
  have e : CE η' = CE η := hCE'.trans hCE.symm
  have hm0 : MemInv (gOf p k arch c i) (CE η') (stOf c.mem c.pairs th) := by rw [hCE']; exact hm
  rw [← e] at hF hPfr hWL
  have hb : ∀ l, (CE η').sto l ≠ none → (CE η'').pfr l ≠ (CE η').pfr l →
      ∀ x bb ib v e0, th.term ≠ .let_ x (.bufInit bb ib v) e0 := by
    intro l hs hne x bb ib v e0 hterm
    obtain ⟨y, a, e1, -, -, -, hpub, -⟩ := hPfr l hs hne
    rw [hpub] at hterm; cases hterm
  have hA := anchR_post hF hm' hb hE' hT' htv' hi' hm0 (hsc th X.hth (TermStep.not_spawnT_of_mem X.hr) ρ' η' cx' hE' hT' htv' hi')
    (TermViewInv.envVR_of_run hV0 X.run X.hth) X.hr (hWL (noPfr (CE η')))
    (by rw [hCE']; exact X.inv.riniCoh i th S X.hth)
    (fun l cl f hs hp => by rw [hCE'] at hs hp; exact X.inv.frlt l cl f (cutSto_sub hs) hp)
  have hx := ext_post hF hm0.2.2.2.1 fun l hl => by
    rw [hCE']; exact (X.inv.gfresh X.hth r.2.2.nalloc l hl).2.1
  have e2 : CE η' = Cut Eg i S := hCE'
  rw [← e2]; exact ⟨hA, hx⟩

/-- **The tied typed run with the post-publish provenance**: `InvAtXFO` along `Solo` from `c`; the
ghost `zf` covers `Z` and the labels the run has published (`PubZO`), where no `bufInit` follows
(`hZo`). -/
theorem solo_typedXFO {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c : Cfg} {E0 : TEnv} {Eu Ea : TEnv}
    {n0 v0 na0 : Nat} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch Eu Ea i c0)
    {st : Cfg} (h0 : InvAtXFO Z p k arch i E0 n0 v0 na0 st c H (Ea := Ea) (Eu := Eu)) {c2 : Cfg} (h : Solo p k arch i c c2)
    (hc2 : Certified p k arch c2 i)
    (hrl : ∀ l, E0.rini l ≤ E0.ini l)
    (hZo : ∀ c1 th1 c1' c3 th3 l cl f, TermOwnG0Defs.SoloNP p k arch i l st c1 → c1.ths[i]? = some th1 →
      TermOwnG0Defs.PubAt th1 l → c1' ∈ threadSteps p k arch c1 i → Solo p k arch i c1' c3 →
      Certified p k arch c3 i → c3.ths[i]? = some th3 → E0.sto l = some cl → cl.owner = some E0.tid →
      E0.pfr l = some f → ¬ BufInitOn th3 l)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i →
      ∀ th1, c1.ths[i]? = some th1 → ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h)
    (hHr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) → H l o τ := by
      exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    InvAtXFO Z p k arch i E0 n0 v0 na0 st c2 H (Ea := Ea) (Eu := Eu) := by
  refine (run_inv (c1 := c2) (P := fun c0 => Solo p k arch i c c0 ∧ InvAtXFO Z p k arch i E0 n0 v0 na0 st c0 H (Ea := Ea) (Eu := Eu))
    ?_ ?_ h (.refl _) ⟨.refl _, h0⟩).2
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hna, hfresh, hIL, hIH, hPO⟩ hs hrest
    have hc0' : Certified p k arch c0' i := certified_back hrest hc2
    have hcert0 : Certified p k arch c0 i := certified_back (.thread hs hrest) hc2
    obtain ⟨th', E', s, s', hth', hF, -, hvw, hx', hT', hm', hSC', hbo', hfb', hfr', hna', hfresh', hIL', hIH'⟩ :=
      xfz_thread (W := fun l => TermK5O.PubZO p k arch i E0 st c0 l) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP
        (hsc c0 hc0 hcert0) (TermViewInv.viewInv_solo hvI hc0) (hwin c0 hc0 hcert0) hth hx hTE hm hSC hbo hfb hfr hna hfresh hIL hIH hs hc0'
        (fun l hbi hz => hz.elim (hZr c0 hc0 hcert0 th hth l hbi)
          (TermK5O.pubZO_noBufInit (fun c1 th1 c1' l cl f h1 h2 h3 h4 h5 h6 h7 h8 =>
            hZo c1 th1 c1' c0 th l cl f h1 h2 h3 h4 h5 hcert0 hth h6 h7 h8) l hbi))
        (hHr c0 hc0 hcert0 th hth)
    exact ⟨solo_trans hc0 (.thread hs (.refl _)), th', E', hth', hx', hT', hm', hSC', hbo', hfb', hfr', hna',
      hfresh', hIL', hIH', TermK5O.pfrProvO_thread hPO hF hfb hx (fun _ h => .inr h) hs hth hvw (hIH' hrl).2.1⟩
  · rintro c0 a v w ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hna, hfresh, hIL, hIH, hPO⟩ hw _
    obtain ⟨th', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
      xfz_prom (a := a) (v := v) (w := w) hth hx hTE hm hSC hbo hfb hfr hna hfresh hIL hIH
    exact ⟨solo_trans hc0 (.prom a v w hw (.refl _)), th', E, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      TermK5O.pfrProvO_prom hPO hw⟩

/-- **A certified thread's promise, with the post-publish provenance at the fulfilling
configuration**: the value is defined (`certified_promNotUndefX`), the fulfilling configuration `c2`
(`certified_promTypedX`), and the environment there from `solo_typedXFO`, where the promise is no
longer outstanding, so `MemInv` types its word. -/
theorem certified_promNotUndefXO {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {E0 : TEnv} {Eu Ea : TEnv} {n0 v0 na0 : Nat} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} [ProgRetIall p] [WrIniC]
    (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch Eu Ea i c0)
    {st : Cfg} (h0 : InvAtXFO Z p k arch i E0 n0 v0 na0 st c H (Ea := Ea) (Eu := Eu)) (hc : Certified p k arch c i)
    (hrl : ∀ l, E0.rini l ≤ E0.ini l)
    (hZo : ∀ c1 th1 c1' c3 th3 l cl f, TermOwnG0Defs.SoloNP p k arch i l st c1 → c1.ths[i]? = some th1 →
      TermOwnG0Defs.PubAt th1 l → c1' ∈ threadSteps p k arch c1 i → Solo p k arch i c1' c3 →
      Certified p k arch c3 i → c3.ths[i]? = some th3 → E0.sto l = some cl → cl.owner = some E0.tid →
      E0.pfr l = some f → ¬ BufInitOn th3 l)
    {t : Ts} {m : Msg} (ht : t ∈ TermFul.promsOf c i) (hm : c.mem[t]? = some m)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i →
      ∀ th1, c1.ths[i]? = some th1 → ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h)
    (hHr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) → H l o τ := by
      exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    m.val ≠ .undef ∧ ∃ c2 th2 E2, Solo p k arch i c c2 ∧ Certified p k arch c2 i ∧
      c2.ths[i]? = some th2 ∧ Ext E0 E2 ∧ ThInvE p E2 th2 ∧
      MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      (∀ cl, E0.sto m.loc.label = some cl → WordOK E2 cl.ty m.loc.offset (mw m)) ∧
      FrBound E0 n0 v0 E2 ∧ IniLoc Z E0 E2 ∧ IniHeld H E0 E2 th2.vs.vWr ∧
      TermK5O.PfrProvO p k arch i H E0 st c2 E2 := by
  have hnu := (certified_promNotUndefX hP hsc hvI hwin h0.toZ hc ht hm hPS hSub hSig hZr hHr).1
  obtain ⟨c1, c2, th1, th2, -, -, -, -, h1, -, h2, hc2, -, hth2, -, -, -, -, -, -, -, -, -, -, -, -, hm2, -, hn2, -⟩ :=
    certified_promTypedX hP hsc hvI hwin h0.toZ hc ht hm hPS hSub hSig hZr hHr
  have h12 : Solo p k arch i c c2 := solo_trans h1 (.thread h2 (.refl _))
  obtain ⟨th2', E2, hth2', hx2, hT2, hm2i, -, -, hfb2, -, -, -, hIL2, hIH2, hPO2⟩ :=
    solo_typedXFO hP hsc hvI hwin h0 h12 hc2 hrl hZo hPS hSub hSig hZr hHr
  rw [hth2] at hth2'
  cases hth2'
  refine ⟨hnu, c2, th2, E2, h12, hc2, hth2, hx2, hT2, hm2i, fun cl hcl => ?_, hfb2, hIL2, hIH2, hPO2⟩
  rcases hm2i.1.1 t m cl hn2 hm2 (hx2.2.2.2.2.1 _ _ hcl) with h | h
  · exact absurd h hnu
  · exact h

end TermXFO

#print axioms TermXFO.InvAtXFO.toF
#print axioms TermXFO.InvAtXFO.toZ
#print axioms TermXFO.InvAtXFO_of
#print axioms TermXFO.solo_typedXFO
#print axioms TermXFO.certified_promNotUndefXO
