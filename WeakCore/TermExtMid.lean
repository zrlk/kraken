import WeakCore.TermSpawnMidM0
import WeakCore.TermExtStep
/-!
# TermExtMid — `SysInvN` across an extern step (E2)

* `ext_of_site` — the continuation of `let x = ext n a in e` is typed (`OpT.ext`: the argument is used, `x` is bound
  at `n.sig.2`) given a value of `n.sig.2` at resource zero.
* `sysInvN_extSet` — thread `i` replaced in place by that continuation (`TermSetTh.sysInvN_setC`).
* `sysInvN_extStep` — **the extern arm**: `emit`/`exitEv` bind `()` (the trace is not part of `SysInvN`);
  `current` binds the thread's box word `loc ⟨l, 0⟩`, first allocating the box (`TermBox.sysInvN_box`,
  `tidLbl := some (freshLabel …)`) when the thread has none (`curCfg_none`).

(IO1) `Ext` needs `th.promises = []` only for `ExtNeedsNoProm` (`exitEv`, `current()`); `emit` goes through
`sysInvN_extSet`, which never reads promises. Only the first-use `current()` arm uses the empty promise set
(`TermBox.sysInvN_box`).
-/

namespace TermExtMid
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermSpawn TermExtStep
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem ext_of_site {p : Prog} {E : TEnv} {th th' : TTh} {Tot : Res} {x : String} {n : ExtName} {a : At}
    {e : Expr} {ws : List Word} (hterm : th.term = .let_ x (.ext n a) e)
    (hpt : th'.term = e) (hpe : th'.env = (x, n.sig.2, ws) :: th.env) (hps : th'.σs = th.σs)
    (hpk : th'.stack = th.stack)
    (hvr : ∀ (ρ : Nat → Nat) (η : TEnv), CE η = E →
      VR ρ η n.sig.2 (shp n.sig.2) ws ∧ VRR ρ η n.sig.2 (shp n.sig.2) ws .zero)
    (hl : Lay th.σs n.sig.2 n.sig.2 ws)
    (hR : ThInvRE p E th Tot) (hE' : ThInvE p E th) :
    ThInvRE p E th' Tot ∧ ThInvE p E th' := by
  have htb : tb 0 n.sig.2 = true := by cases n <;> simp [ExtName.sig, tb]
  have hmg : mg n.sig.2 = true := by cases n <;> simp [ExtName.sig, mg]
  constructor
  · obtain ⟨ρ, η, cx, Rf, Rs, hCE, hE, hT, htv, hi, hsum, hpw⟩ := hR
    have hT2 := hT.2
    rw [hterm] at hT2
    obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hT2
    cases hop with
    | ext hu hsub hb =>
      have hret : c'.ret = cx.ret := (bind_ret hb).trans (use_ret hu)
      have htv1 := use_TvOK hu htv
      have htv' := (bind_TvOK hb htv1.1 (by cases n <;> simp [ExtName.sig, tb]) hmg).1
      obtain ⟨rt, ws0, R, Rr, -, -, -, -, hi1, hle⟩ := useR hu hi hE.2.2
      have hf := bindRZ hb (FInvR_mono hi1 (le_of_add_le hle)) (RLink_of hE.2.1 hE.2.2) (hvr ρ η hCE).2 hl
      refine ⟨ρ, η, c', Rf, Rs, hCE, hE, ⟨by rw [hpt]; exact he, by rw [hpt]; exact hck⟩, htv',
        by rw [hps, hpk, hpe]; exact hf, hsum, ?_⟩
      intro fr rest hst ws1
      rw [hpk] at hst
      rw [hret, hps]; exact hpw fr rest hst ws1
  · obtain ⟨ρ, η, cx, hCE, hE, hT, htv, hi, hpw⟩ := hE'
    rw [hterm] at hT
    cases hT with
    | let_ hop he =>
      rename_i c'
      cases hop with
      | ext hu hsub hb =>
        have hret : c'.ret = cx.ret := (bind_ret hb).trans (use_ret hu)
        have htv1 := use_TvOK hu htv
        have htv' := (bind_TvOK hb htv1.1 (by cases n <;> simp [ExtName.sig, tb]) hmg).1
        obtain ⟨hi1, -⟩ := use_FInv hu hi
        refine ⟨ρ, η, c', hCE, hE, by rw [hpt]; exact he, htv',
          by rw [hps, hpe, hpk]; exact bind_FInv hb hi1 (hvr ρ η hCE).1 hl, ?_⟩
        show RetPw th'.σs th'.stack c'.ret
        rw [hret, hps, hpk]; exact hpw

theorem vrr_unit {ρ : Nat → Nat} {η : TEnv} : VRR ρ η .unit (shp .unit) [] .zero := by
  simp [VRR]

theorem vr_unit {ρ : Nat → Nat} {η : TEnv} : VR ρ η .unit (shp .unit) [] := by
  simp [VR, shp]

theorem cutSto_box {Eg : GEnv} {l : AllocLabel} {j : Nat} (hs : Eg.sto l = some ⟨.unit, none⟩)
    (hp : Eg.pfr l = some 0) : cutSto Eg j l = some ⟨.unit, none⟩ := by
  unfold cutSto GEnv.InCut GEnv.Shared
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨_, hs, Or.inr ⟨0, hp⟩⟩), hs]

theorem ownLive_setC {Eg : GEnv} {c : Cfg} {i : Nat} {th' : TTh} {tr : List Event} (h : OwnLive Eg c) :
    OwnLive Eg (TermSetTh.setC c i th' tr) := by
  unfold OwnLive at *; rw [TermSetTh.setC_size]; exact h

theorem obsAll_setC {Eg : GEnv} {c : Cfg} {i : Nat} {th' : TTh} {tr : List Event} (h : ObsAll Eg c) :
    ObsAll Eg (TermSetTh.setC c i th' tr) := by
  unfold ObsAll at *; simpa only [TermSetTh.setC_size, TermSetTh.setC_mem, TermSetTh.setC_pairs] using h

/-- The box word names only its label. -/
theorem names_tid {L a : AllocLabel} {w : Word} (hw : w ∈ TermPtrRts.pubWords .tid [cst (.loc ⟨L, 0⟩ 0)])
    (hn : TermPtrRts.Names a w) : a = L := by
  obtain ⟨a', g, hva, rfl⟩ := hn
  have hw' : w = cst (.loc ⟨L, 0⟩ 0) := by
    simp [TermPtrRts.pubWords, TermPtrRts.sNo] at hw; exact hw
  subst hw'
  have e1 : a' = ⟨L, 0⟩ := by
    simp [cst, Promises.TVal.mk0] at hva; exact hva.1.symm
  subst e1
  rfl

theorem lay_tid (σs : List Ty) (L : AllocLabel) : Lay σs .tid .tid [cst (.loc ⟨L, 0⟩ 0)] :=
  ⟨fun us h => by simp [accs] at h; subst h; rfl, by first | rfl | simp [etok, close, substTs, skel],
    by simp [wc, accs], trivial, by first | rfl | simp [etok, close, substTs, lyt]⟩

theorem vr_tid {ρ : Nat → Nat} {η : TEnv} {L : AllocLabel} (hs : η.sto L = some ⟨.unit, none⟩)
    (hp : η.pfr L = some 0) :
    VR ρ η .tid (shp .tid) [cst (.loc ⟨L, 0⟩ 0)] ∧ VRR ρ η .tid (shp .tid) [cst (.loc ⟨L, 0⟩ 0)] .zero :=
  ⟨⟨L, ⟨.unit, none⟩, rfl, hs, rfl, 0, hp, .inr fun _ _ => Nat.zero_le _⟩,
    ⟨L, ⟨.unit, none⟩, rfl, hs, rfl, 0, hp, .inr fun _ _ => Nat.zero_le _⟩, rfl⟩

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}

/-- **The extern continuation as a thread replacement**: thread `i` at `let x = ext n a in e` continues with
`x := ws` (a value of `n.sig.2` at resource zero, naming only labelled cells not owned by `i`). -/
theorem sysInvN_extSet {i : Nat} {th : TTh} {x : String} {n : ExtName} {a : At} {e : Expr} {ws : List Word}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hth : c.ths[i]? = some th)
    (hterm : th.term = .let_ x (.ext n a) e)
    (hvr : ∀ (S : AllocLabel → Prop) (ρ : Nat → Nat) (η : TEnv), CE η = Cut Eg i S →
      VR ρ η n.sig.2 (shp n.sig.2) ws ∧ VRR ρ η n.sig.2 (shp n.sig.2) ws .zero)
    (hl : Lay th.σs n.sig.2 n.sig.2 ws)
    (hlbl : ∀ w ∈ TermPtrRts.pubWords n.sig.2 ws, ∀ l, TermPtrRts.Names l w → Eg.pfr l ≠ none ∨ Eg.box l ≠ none)
    (hrts : ∀ w ∈ TermPtrRts.pubWords n.sig.2 ws, ∀ a0 cl, TermPtrRts.Names a0 w → Eg.sto a0 = some cl →
      cl.owner ≠ some i)
    (tr : List Event) :
    SysInvN p k arch Init MintOK (TermSetTh.setC c i { th with term := e, env := (x, n.sig.2, ws) :: th.env } tr)
      Eg Tot HP HS cr db := by
  obtain ⟨S, hRE, hE, hrest⟩ := hN.thr i th hth
  have hx := ext_of_site (th' := { th with term := e, env := (x, n.sig.2, ws) :: th.env }) hterm rfl rfl rfl rfl
    (hvr S) hl hRE hE
  refine TermSetTh.sysInvN_setC hN hth ⟨rfl, rfl, rfl, rfl⟩ ⟨S, hx.1, hx.2, hrest⟩ ?_ ?_ (hN.tidBox i th hth)
  · intro hk
    obtain ⟨hL1, hL2⟩ := (hN.ptrGL hk).2.1 i th hth
    refine ⟨?_, hL2⟩
    intro y rt ws1 hm
    rcases List.mem_cons.1 hm with h | h
    · cases h; exact hlbl
    · exact hL1 y rt ws1 h
  · intro hk t a0 cl hs ho hR0
    obtain ⟨hR1, hR2⟩ := hR0
    refine ⟨?_, hR2⟩
    intro y rt ws1 hm w hw hn
    rcases List.mem_cons.1 hm with h | h
    · cases h; exact absurd ho (hrts w hw a0 cl hn hs)
    · exact hR1 y rt ws1 h w hw hn

end

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}

theorem pubWords_unit {w : Word} (hw : w ∈ TermPtrRts.pubWords .unit []) : False := by
  simp [TermPtrRts.pubWords] at hw

/-- `current()`, second call (`tidLbl = some l`): the box is already there. -/
theorem curCfg_some {c : Cfg} {i : Nat} {th : TTh} {x : String} {e : Expr} {l : AllocLabel}
    (htl : th.tidLbl = some l) :
    curCfg c i th x e = TermSetTh.setC c i
      { th with term := e, env := (x, ExtName.current.sig.2, [cst (.loc ⟨l, 0⟩ 0)]) :: th.env } c.trace := by
  unfold curCfg; rw [htl]; rfl

/-- `current()`, first call: `curCfg` is the box step (`thB`) followed by the replacement. -/
theorem curCfg_none {c : Cfg} {i : Nat} {th : TTh} {x : String} {e : Expr} {l : AllocLabel}
    (htl : th.tidLbl = none) (hl : l = freshLabel c.lbase c.n i th.nalloc) :
    curCfg c i th x e = TermSetTh.setC (TermSetTh.setC c i (TermBox.thB th (some l)) c.trace) i
      { (TermBox.thB th (some l)) with term := e, env := (x, ExtName.current.sig.2, [cst (.loc ⟨l, 0⟩ 0)]) :: th.env }
      c.trace := by
  subst hl
  have e : ∀ (t1 t2 : TTh), (c.ths.set! i t1).set! i t2 = c.ths.set! i t2 := by
    intro t1 t2
    apply Array.ext_getElem?
    intro j
    by_cases h : i = j
    · subst h; simp [Array.set!, Array.getElem?_setIfInBounds]
    · simp [Array.set!, h]
  unfold curCfg TermSetTh.setC
  rw [htl]
  simp only [e]
  rfl

/-- **The extern arm**: `SysInvN` (with `OwnLive`, `ObsAll`) across an `Ext` step.  `emit`/`exitEv` bind `()`;
`current` binds the thread's box word, first allocating the box (`TermBox.sysInvN_box`) if it has none. -/
theorem sysInvN_extStep {c' : Cfg}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    (hX : Ext p k arch c c') :
    ∃ (Eg' : GEnv) (Tot' HP' : Nat → Res) (HS' : Res) (cr' db' : Nat → Ts → Res),
      SysInvN p k arch Init MintOK c' Eg' Tot' HP' HS' cr' db' ∧ OwnLive Eg' c' ∧ ObsAll Eg' c' := by
  obtain ⟨i, x, n, a, e, th, rt, ws, hth, hterm, hnp, hev, -, rfl⟩ := hX.elim
  cases n with
  | emit =>
    exact ⟨_, _, _, _, _, _, sysInvN_extSet hN hth hterm (fun _ _ _ _ => ⟨vr_unit, vrr_unit⟩) (Lay_unitT _)
      (fun w hw => (pubWords_unit hw).elim) (fun w hw => (pubWords_unit hw).elim) _,
      ownLive_setC hOL, obsAll_setC hObs⟩
  | exitEv =>
    exact ⟨_, _, _, _, _, _, sysInvN_extSet hN hth hterm (fun _ _ _ _ => ⟨vr_unit, vrr_unit⟩) (Lay_unitT _)
      (fun w hw => (pubWords_unit hw).elim) (fun w hw => (pubWords_unit hw).elim) _,
      ownLive_setC hOL, obsAll_setC hObs⟩
  | current =>
    show ∃ (Eg' : GEnv) (Tot' HP' : Nat → Res) (HS' : Res) (cr' db' : Nat → Ts → Res),
      SysInvN p k arch Init MintOK (curCfg c i th x e) Eg' Tot' HP' HS' cr' db' ∧
        OwnLive Eg' (curCfg c i th x e) ∧ ObsAll Eg' (curCfg c i th x e)
    cases htl : th.tidLbl with
    | some l =>
      obtain ⟨hs, hp⟩ := hN.tidBox i th hth l htl
      rw [curCfg_some htl]
      exact ⟨_, _, _, _, _, _, sysInvN_extSet hN hth hterm
        (fun S _ η hCE => vr_tid (by rw [← CE_sto, hCE, Cut_sto]; exact cutSto_box hs hp)
          (by rw [← CE_pfr, hCE]; exact hp))
        (lay_tid _ l)
        (fun w hw l' hn => by rw [names_tid hw hn]; exact .inl (by rw [hp]; simp))
        (fun w hw a0 cl hn hs' => by
          rw [names_tid hw hn, hs] at hs'; cases hs'; simp) _,
        ownLive_setC hOL, obsAll_setC hObs⟩
    | none =>
      have hnp : th.promises = [] := hnp (.inr rfl)
      obtain ⟨L, hL⟩ : ∃ L, L = freshLabel c.lbase c.n i th.nalloc := ⟨_, rfl⟩
      have hB := TermBox.sysInvN_box (tl := some L) hN hOL hth hnp hL (.inr rfl)
      have hG := hN.fresh i th hth th.nalloc (Nat.le_refl _)
      have hOL1 := TermBox.ownLive_box (i := i) (th' := TermBox.thB th (some L)) (tr := c.trace) (l := L) hOL
      have hObs1 := TermBox.obsAll_box (i := i) (th' := TermBox.thB th (some L)) (tr := c.trace) (l := L)
        (by subst hL; exact hG.1) (by subst hL; exact hG.2.2.2.1)
        (fun t m ht he => by
          subst hL; have := hG.2.2.2.2 t m ht he; rw [hnp] at this; cases this) hObs
      have hth1 := TermSetTh.setC_self (th' := TermBox.thB th (some L)) (tr := c.trace) hth
      have hs : (TermBox.EgB Eg L).sto L = some ⟨.unit, none⟩ := TermBox.EgB_sto_self
      have hp : (TermBox.EgB Eg L).pfr L = some 0 := TermBox.EgB_pfr_self
      rw [curCfg_none htl hL]
      exact ⟨_, _, _, _, _, _, sysInvN_extSet hB hth1 hterm
        (fun S _ η hCE => vr_tid (by rw [← CE_sto, hCE, Cut_sto]; exact cutSto_box hs hp)
          (by rw [← CE_pfr, hCE]; exact hp))
        (lay_tid _ L)
        (fun w hw l' hn => by rw [names_tid hw hn]; exact .inl (by rw [hp]; simp))
        (fun w hw a0 cl hn hs' => by
          rw [names_tid hw hn, hs] at hs'; cases hs'; simp) _,
        ownLive_setC hOL1, obsAll_setC hObs1⟩

end

end TermExtMid

#print axioms TermExtMid.ext_of_site
#print axioms TermExtMid.vrr_unit
#print axioms TermExtMid.vr_unit
#print axioms TermExtMid.cutSto_box
#print axioms TermExtMid.ownLive_setC
#print axioms TermExtMid.obsAll_setC
#print axioms TermExtMid.names_tid
#print axioms TermExtMid.lay_tid
#print axioms TermExtMid.vr_tid
#print axioms TermExtMid.sysInvN_extSet
#print axioms TermExtMid.pubWords_unit
#print axioms TermExtMid.curCfg_some
#print axioms TermExtMid.curCfg_none
#print axioms TermExtMid.sysInvN_extStep
