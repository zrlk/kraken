/-
Stage B, S4g: the typed run along certifying runs, and the S3 fix.

1. Certification and `PromAbove`/`PAx`: certification gives `PromAbove` at
   every certified configuration (`certified_promAboveSt`), hence for the
   *taken* result of a thread step into a certified configuration
   (`taken_promAbove`) and `PAx` at its source (`PAx_of_step`).  It does not
   give `PromAbove` for every result of `tstep` (a load may read a message
   above an own promise; that result is not certified).
2. The typed run (`solo_typedL`, `solo_typedW`, `solo_typedP`): along `Solo`
   from a configuration where thread `i` satisfies `ThInvM`, `ThInvM` holds at
   every certified configuration reached, with the scope (`ScopeAt`) as a
   run-level hypothesis.  Promise steps use `MemInv_promSt`
   (`ThInvM_promise_tr`).
3. The S3 fix: `certified_promQC` (the hypothesis of `certified_promQ` gets
   `Certified c1 i`), `certified_promTyped` (the fulfilling step happens at a
   typed configuration and lands in a typed one), `certified_promWordOK` (an
   outstanding promise's message is typed by `MemOKP` after its fulfil), and
   state-local versions of `certified_noPairProm`/`certified_promWord`.
4. `SWOne_holds` (single-word writes land on `.one` units, op by op),
   `wordOK_good` (the value-level fact) and `pwf_of_inv`, discharging the
   corollaries: `certified_noPairPromS`/`certified_promWordS` (from
   `StepPresW`) and `certified_noPairPromP`/`certified_promWordP` (from
   `ProgT`, via `TermStep.stepPresW_of`).
5. (S7f) The tied run: `InvAtX` (the invariant at an `Ext`ension of the start
   environment `E0`), `solo_typedX` (by `tstep_footprint`), and the tied
   certificate facts at `E0`'s cells (`certified_promTypedX`,
   `certified_promWordX`, `certified_noPairPromX`); value-level facts
   (`wordOK_one`, `wordOK_word`, `wordOK_pubRef`, `AtOff_word_lit`); `FlipOK`
   (`flipOK_cert`) and the plant's type facts (`plant_typeFacts`, `plant_hpl`).
6. (Gap a) A fulfilled promise is the thread's coherence point (`FulC`,
   `tstep_fulC`), so an own non-ghost word promise is a number
   (`own_num`, `certified_promNumX`, `certified_promWordNX`).  (Gap b) Cell
   types are closed (`StoClo`, kept by `EFoot`: `StoClo_EFoot`; carried in
   `InvAtX`).
-/
import WeakCore.TermGlob
import WeakCore.TermPlant
import WeakCore.TermViewInvH

namespace TermTyped
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Runs -/

/-- Induction along a prefix of a run into `c1`. -/
theorem run_inv {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c1 : Cfg} {P : Cfg → Prop}
    (hstep : ∀ c0 c0', P c0 → c0' ∈ threadSteps p k arch c0 i → Solo p k arch i c0' c1 → P c0')
    (hprom : ∀ c0 a v w, P c0 → w < c0.mem.size → Solo p k arch i (promise c0 i a v w) c1 →
      P (promise c0 i a v w))
    (hext : ∀ c0 c0', P c0 → c0' ∈ extSteps c0 i → Solo p k arch i c0' c1 → P c0')
    {c c2 : Cfg} (h : Solo p k arch i c c2) (h2 : Solo p k arch i c2 c1) (h0 : P c) : P c2 := by
  revert h0 h2
  induction h with
  | refl => exact fun _ h0 => h0
  | thread hs hrest ih => exact fun h2 h0 => ih h2 (hstep _ _ h0 hs (solo_trans hrest h2))
  | prom a v w hw hrest ih => exact fun h2 h0 => ih h2 (hprom _ a v w h0 hw (solo_trans hrest h2))
  | ext hs hrest ih => exact fun h2 h0 => ih h2 (hext _ _ h0 hs (solo_trans hrest h2))

theorem gOf_thread {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c' : Cfg}
    (hs : c' ∈ threadSteps p k arch c i) : gOf p k arch c' i = gOf p k arch c i := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := TermStep.step_thread_inv hs
  simp [gOf, Cfg.n]

/-! ### The typing invariants across an `emit` (the continuation, `x : ()`) -/

/-- `ThInvE` across an `emit` (`OpT.ext`: the argument is used, `x` is bound at `()`). -/
theorem ThInvE_emit {p : Prog} {E : TEnv} {th : TTh} {x : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.ext .emit a) e) (h : ThInvE p E th) :
    ThInvE p E { th with term := e, env := (x, .unit, []) :: th.env } := by
  obtain ⟨ρ, η, cx, hCE, hE, hT, htv, hi, hpw⟩ := h
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
    rename_i c'
    cases hop with
    | ext hu _ hsub hb =>
      have hret : c'.ret = cx.ret := (bind_ret hb).trans (use_ret hu)
      have htv1 := use_TvOK hu htv
      have htv' := (bind_TvOK hb htv1.1 (by simp [ExtName.sig, tb]) (by simp [ExtName.sig, mg])).1
      obtain ⟨hi1, -⟩ := use_FInv hu hi
      refine ⟨ρ, η, c', hCE, hE, he, htv', bind_FInv hb hi1 (by simp [ExtName.sig, VR, shp]) (Lay_unitT _), ?_⟩
      show RetPw th.σs th.stack c'.ret
      rw [hret]; exact hpw

/-- `ThInvRE` across an `emit` (the argument's resources are released into the frame). -/
theorem ThInvRE_emit {p : Prog} {E : TEnv} {th : TTh} {Tot : Res} {x : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.ext .emit a) e) (hR : ThInvRE p E th Tot) :
    ThInvRE p E { th with term := e, env := (x, .unit, []) :: th.env } Tot := by
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hE, hT, htv, hi, hsum, hpw⟩ := hR
  have hT2 := hT.2
  rw [hterm] at hT2
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hT2
  cases hop with
  | ext hu _ hsub hb =>
    have hret : c'.ret = cx.ret := (bind_ret hb).trans (use_ret hu)
    have htv1 := use_TvOK hu htv
    have htv' := (bind_TvOK hb htv1.1 (by simp [ExtName.sig, tb]) (by simp [ExtName.sig, mg])).1
    obtain ⟨rt, ws0, R, Rr, -, -, -, -, hi1, hle⟩ := useR hu hi hE.2.2
    have hf := bindRZ hb (FInvR_mono hi1 (le_of_add_le hle)) (RLink_of hE.2.1 hE.2.2) (by simp [ExtName.sig, VRR, shp]) (Lay_unitT _)
    refine ⟨ρ, η, c', Rf, Rs, hCE, hE, ⟨he, hck⟩, htv', hf, hsum, ?_⟩
    intro fr rest hst ws1
    rw [hret]; exact hpw fr rest hst ws1

/-- `ThInvM` across an `emit` (the machine state `stOf` is unchanged). -/
theorem ThInvM_emit {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : String} {a : At}
    {e : Expr} (hterm : th.term = .let_ x (.ext .emit a) e) (h : ThInvM p g mem pairs th) :
    ThInvM p g mem pairs { th with term := e, env := (x, .unit, []) :: th.env } := by
  obtain ⟨E, hT, hm, hb⟩ := h
  exact ⟨E, ThInvE_emit hterm hT, hm, hb⟩

/-! ### (M1) The result words of a non-`current` extern are a value of `n.sig.2` -/

private theorem extArg_one {ρ : Nat → Nat} {η : TEnv} {o : Opq} {sh : Shp} {ws : List Word}
    (h : VR ρ η (.opq o) sh ws) : ∃ w, ws = [w] := by
  obtain ⟨m, hm⟩ := h
  rcases ws with _ | ⟨w, _ | ⟨w2, ws⟩⟩ <;> simp at hm
  exact ⟨w, rfl⟩

private theorem extArg_pair {ρ : Nat → Nat} {η : TEnv} {o : Opq} {sg : Bool} {wd : Wd} {sh : Shp} {ws : List Word}
    (h : VR ρ η (.prod (.opq o) (.fix sg wd)) sh ws) (hwc : sh.wc ≠ none) : ∃ w1 w2, ws = [w1, w2] := by
  obtain ⟨ra, rb, rfl, h⟩ := h
  cases hra : ra.wc with
  | none => simp [Shp.wc, hra] at hwc
  | some k =>
    obtain ⟨-, ⟨m, hm⟩, -, m2, hm2, -⟩ := h k hra
    rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩ <;> rcases k with _ | _ | _ | k <;> simp at hm hm2
    exact ⟨w1, w2, rfl⟩

theorem shape_opq (o : Opq) (x : Word) : ShapeC (.opq o) [x] := by
  intro us h; simp [accs] at h; subst h; rfl

theorem Lay_opq (σs : List Ty) (o : Opq) (x : Word) : Lay σs (.opq o) (.opq o) [x] :=
  ⟨shape_opq o x, rfl, by simp [wc, accs], trivial, rfl⟩

private theorem mod_pw2 (m : Nat) (w : Wd) : m % 2 ^ Wd.bits w < pw2 w := by
  rw [pw2]; exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- (M1) The results of a non-`current` extern, at the argument of its signature, are a resource-free value of the
result type with its own layout. -/
theorem ext_res {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {n : ExtName} {i : Nat} {ws : List Word} {tr : List Event}
    {rs : List Word} {rt : Ty} (hn : n ≠ .current) (hvr : VR ρ η n.sig.1 (shp rt) ws) (hwc : wc rt ≠ none)
    (hrs : rs ∈ n.resultsL i ws tr) :
    VRR ρ η n.sig.2 (shp n.sig.2) rs .zero ∧ Lay σs n.sig.2 n.sig.2 rs := by
  rw [mem_resultsL] at hrs
  rw [← shp_wc] at hwc
  cases n with
  | current => exact absurd rfl hn
  | mmioR w acc o =>
    obtain ⟨r, rfl⟩ := extArg_one hvr
    simp only [ExtName.Admits] at hrs; subst hrs
    refine ⟨⟨_, _, rfl, .zero, .zero, rfl, by simp [shp, Shp.wc, wc, accs], fun k hk => ?_⟩,
      Lay_pair (ws := [_]) (us := [_]) (Lay_opq σs _ _) (Lay_fix σs _ _ _)⟩
    simp [shp, Shp.wc, wc, accs, nWords, Acc.size] at hk; subst hk
    exact ⟨by simp, ⟨⟨_, rfl⟩, rfl⟩, ⟨rfl, _, rfl, mod_pw2 _ _⟩, rfl⟩
  | mmioW w acc o =>
    obtain ⟨r, v, rfl⟩ := extArg_pair hvr hwc
    simp only [ExtName.Admits] at hrs; subst hrs
    exact ⟨⟨⟨_, rfl⟩, rfl⟩, Lay_opq σs _ _⟩
  | regAt nb w acc st tk k =>
    obtain ⟨b, rfl⟩ := extArg_one hvr
    simp only [ExtName.Admits] at hrs; subst hrs
    refine ⟨⟨_, _, rfl, .zero, .zero, rfl, by simp [shp, Shp.wc, wc, accs], fun k hk => ?_⟩,
      Lay_pair (ws := [_]) (us := [_]) (Lay_opq σs _ _) (Lay_opq σs _ _)⟩
    simp [shp, Shp.wc, wc, accs, nWords, Acc.size] at hk; subst hk
    exact ⟨by simp, ⟨⟨_, rfl⟩, rfl⟩, ⟨_, rfl⟩, rfl⟩
  | devRecv w =>
    obtain ⟨r, rfl⟩ := extArg_one hvr
    simp only [ExtName.Admits] at hrs; subst hrs
    exact ⟨⟨⟨rfl, _, rfl, mod_pw2 _ _⟩, rfl⟩, Lay_fix σs _ _ _⟩
  | devChoice w =>
    simp only [ExtName.Admits] at hrs
    obtain ⟨v, hv, rfl⟩ := hrs
    exact ⟨⟨⟨rfl, _, rfl, by rw [pw2]; exact hv⟩, rfl⟩, Lay_fix σs _ _ _⟩
  | _ =>
    rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩ <;>
      simp only [ExtName.Admits] at hrs <;> subst hrs <;>
      exact ⟨by simp [ExtName.sig, VRR], Lay_unitT _⟩


/-- (M1) `extSteps_thread` with the argument words and the admitted results of a non-`current` extern. -/
theorem extSteps_res {c c' : Cfg} {i : Nat} {th : TTh} (h : c' ∈ extSteps c i) (hth : c.ths[i]? = some th) :
    (∃ x n a e rt ws rs, th.term = .let_ x (.ext n a) e ∧ n ≠ .current ∧ evalAt th.env a = some (rt, ws) ∧
      rs ∈ n.resultsL i ws c.trace ∧
      c' = { c with ths := c.ths.set! i { th with term := e, env := (x, n.sig.2, rs) :: th.env,
                                                  vs := { th.vs with
                                                    vRd := (if n = .park then parkVs c.mem.size th else th.vs).vRd,
                                                    vPreBase := (if n = .park then parkVs c.mem.size th else th.vs).vPreBase },
                                                  permit := if n = .park then none else th.permit },
                    trace := c.trace ++ n.events ws rs }) ∨
    (∃ x a e l, th.term = .let_ x (.ext .current a) e ∧ th.tidLbl = some l ∧
      c' = { c with ths := c.ths.set! i { th with term := e, env := (x, .tid, [cst (.loc ⟨l, 0⟩ 0)]) :: th.env } }) := by
  rcases extSteps_thread h hth with h1 | h1
  · obtain ⟨th', x, n, a, e, rt, ws, rs, hth', hterm, -, hev, hrs, rfl⟩ := extSteps_elim h
    rw [hth] at hth'; cases hth'
    obtain ⟨x0, n0, a0, e0, evs, rs0, hterm0, hn0, -⟩ := h1
    rw [hterm] at hterm0; cases hterm0
    refine .inl ⟨x, n, a, e, rt, ws, rs, hterm, hn0, hev, hrs, ?_⟩
    cases n <;> first | exact absurd rfl hn0 | rfl | skip
    cases hp : th.permit <;> simp [extCfg, parkVs, hp]
  · exact .inr h1

/-- (M1) `ThInvE` across a non-`current` extern (`x` is bound at `n.sig.2` to the admitted results; `permit` is
irrelevant to typing). -/
theorem ThInvE_ext {p : Prog} {E : TEnv} {th : TTh} {x : String} {n : ExtName} {a : At} {e : Expr} {rt : Ty}
    {ws rs : List Word} {i : Nat} {tr : List Event} {vv : VState} {pm : Option Ts} (hn : n ≠ .current)
    (hterm : th.term = .let_ x (.ext n a) e) (hev : evalAt th.env a = some (rt, ws)) (hrs : rs ∈ n.resultsL i ws tr)
    (h : ThInvE p E th) :
    ThInvE p E { th with term := e, env := (x, n.sig.2, rs) :: th.env, vs := vv, permit := pm } := by
  obtain ⟨ρ, η, cx, hCE, hE, hT, htv, hi, hpw⟩ := h
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
    rename_i c'
    cases hop with
    | ext hu _ hsub hb =>
      have hret : c'.ret = cx.ret := (bind_ret hb).trans (use_ret hu)
      have htv1 := use_TvOK hu htv
      have htv' := (bind_TvOK hb htv1.1 (TermTv.extSig_tb _ _) (TermTv.extSig_mg _)).1
      obtain ⟨hi1, rt1, ws1, hev1, hvr1, hl1⟩ := use_FInv hu hi
      rw [hev] at hev1; cases hev1
      obtain ⟨hz, hl⟩ := ext_res (σs := th.σs) hn (VR_sub hi1.1 hsub _ _ hvr1) hl1.2.2.1 hrs
      refine ⟨ρ, η, c', hCE, hE, he, htv', bind_FInv hb hi1 (VRR_VR _ (RLink_of hE.2.1 hE.2.2) hz) hl, ?_⟩
      show RetPw th.σs th.stack c'.ret
      rw [hret]; exact hpw

/-- (M1) `ThInvRE` across a non-`current` extern (the argument's resources are released into the frame; the
results are resource-free). -/
theorem ThInvRE_ext {p : Prog} {E : TEnv} {th : TTh} {Tot : Res} {x : String} {n : ExtName} {a : At} {e : Expr}
    {rt : Ty} {ws rs : List Word} {i : Nat} {tr : List Event} {vv : VState} {pm : Option Ts} (hn : n ≠ .current)
    (hterm : th.term = .let_ x (.ext n a) e) (hev : evalAt th.env a = some (rt, ws)) (hrs : rs ∈ n.resultsL i ws tr)
    (hR : ThInvRE p E th Tot) :
    ThInvRE p E { th with term := e, env := (x, n.sig.2, rs) :: th.env, vs := vv, permit := pm } Tot := by
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hE, hT, htv, hi, hsum, hpw⟩ := hR
  have hT2 := hT.2
  rw [hterm] at hT2
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hT2
  cases hop with
  | ext hu _ hsub hb =>
    have hret : c'.ret = cx.ret := (bind_ret hb).trans (use_ret hu)
    have htv1 := use_TvOK hu htv
    have htv' := (bind_TvOK hb htv1.1 (TermTv.extSig_tb _ _) (TermTv.extSig_mg _)).1
    obtain ⟨rt1, ws1, R, Rr, hev1, hvr1, hl1, -, hi1, hle⟩ := useR hu hi hE.2.2
    rw [hev] at hev1; cases hev1
    obtain ⟨hz, hl⟩ := ext_res (σs := th.σs) hn (VR_sub hi1.1.1 hsub _ _ hvr1) hl1.2.2.1 hrs
    have hf := bindRZ hb (FInvR_mono hi1 (le_of_add_le hle)) (RLink_of hE.2.1 hE.2.2) hz hl
    refine ⟨ρ, η, c', Rf, Rs, hCE, hE, ⟨he, hck⟩, htv', hf, hsum, ?_⟩
    intro fr rest hst ws1
    rw [hret]; exact hpw fr rest hst ws1

/-- (M1) `ThInvM` across a non-`current` extern (the machine state `stOf` is unchanged). -/
theorem ThInvM_ext {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : String} {n : ExtName}
    {a : At} {e : Expr} {rt : Ty} {ws rs : List Word} {i : Nat} {tr : List Event} {vr vp : Ts} {pm : Option Ts}
    (hn : n ≠ .current)
    (hterm : th.term = .let_ x (.ext n a) e) (hev : evalAt th.env a = some (rt, ws)) (hrs : rs ∈ n.resultsL i ws tr)
    (h : ThInvM p g mem pairs th) :
    ThInvM p g mem pairs
      { th with term := e, env := (x, n.sig.2, rs) :: th.env, vs := { th.vs with vRd := vr, vPreBase := vp },
                permit := pm } := by
  obtain ⟨E, hT, hm, hb⟩ := h
  exact ⟨E, ThInvE_ext hn hterm hev hrs hT, hm, hb⟩

/-! ### (C) The typing invariants across a boxed `current()` (the continuation, `x : tid` at the box word) -/

private theorem lay_tidT (σs : List Ty) (L : AllocLabel) : Lay σs .tid .tid [cst (.loc ⟨L, 0⟩ 0)] :=
  ⟨fun us h => by simp [accs] at h; subst h; rfl, by first | rfl | simp [etok, close, substTs, skel],
    by simp [wc, accs], trivial, by first | rfl | simp [etok, close, substTs, lyt]⟩

private theorem vr_tidT {ρ : Nat → Nat} {η : TEnv} {L : AllocLabel} (hs : η.sto L = some ⟨.unit, none⟩)
    (hp : η.pfr L = some 0) :
    VR ρ η .tid (shp .tid) [cst (.loc ⟨L, 0⟩ 0)] ∧ VRR ρ η .tid (shp .tid) [cst (.loc ⟨L, 0⟩ 0)] .zero :=
  ⟨⟨L, ⟨.unit, none⟩, rfl, hs, rfl, 0, hp, .inr fun _ _ => Nat.zero_le _⟩,
    ⟨L, ⟨.unit, none⟩, rfl, hs, rfl, 0, hp, .inr fun _ _ => Nat.zero_le _⟩, rfl⟩

/-- (C) `ThInvE` across a boxed `current()`: `x` is bound at `tid` to the box word; the box is a
`unit` cell of `E` with frontier `0`. -/
theorem ThInvE_cur {p : Prog} {E : TEnv} {th : TTh} {x : String} {a : At} {e : Expr} {l : AllocLabel}
    (hterm : th.term = .let_ x (.ext .current a) e) (hs : E.sto l = some ⟨.unit, none⟩) (hp : E.pfr l = some 0)
    (h : ThInvE p E th) :
    ThInvE p E { th with term := e, env := (x, .tid, [cst (.loc ⟨l, 0⟩ 0)]) :: th.env } := by
  obtain ⟨ρ, η, cx, hCE, hE, hT, htv, hi, hpw⟩ := h
  subst hCE
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
    rename_i c'
    cases hop with
    | ext hu _ hsub hb =>
      have hret : c'.ret = cx.ret := (bind_ret hb).trans (use_ret hu)
      have htv1 := use_TvOK hu htv
      have htv' := (bind_TvOK hb htv1.1 (by simp [ExtName.sig, tb]) (by simp [ExtName.sig, mg])).1
      obtain ⟨hi1, -⟩ := use_FInv hu hi
      refine ⟨ρ, η, c', rfl, hE, he, htv', bind_FInv hb hi1 (vr_tidT (ρ := ρ) hs hp).1 (lay_tidT _ _), ?_⟩
      show RetPw th.σs th.stack c'.ret
      rw [hret]; exact hpw

/-- (C) `ThInvRE` across a boxed `current()` (the box word is held at resource zero). -/
theorem ThInvRE_cur {p : Prog} {E : TEnv} {th : TTh} {Tot : Res} {x : String} {a : At} {e : Expr}
    {l : AllocLabel} (hterm : th.term = .let_ x (.ext .current a) e) (hs : E.sto l = some ⟨.unit, none⟩)
    (hp : E.pfr l = some 0) (hR : ThInvRE p E th Tot) :
    ThInvRE p E { th with term := e, env := (x, .tid, [cst (.loc ⟨l, 0⟩ 0)]) :: th.env } Tot := by
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hE, hT, htv, hi, hsum, hpw⟩ := hR
  subst hCE
  have hT2 := hT.2
  rw [hterm] at hT2
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hT2
  cases hop with
  | ext hu _ hsub hb =>
    have hret : c'.ret = cx.ret := (bind_ret hb).trans (use_ret hu)
    have htv1 := use_TvOK hu htv
    have htv' := (bind_TvOK hb htv1.1 (by simp [ExtName.sig, tb]) (by simp [ExtName.sig, mg])).1
    obtain ⟨rt, ws0, R, Rr, -, -, -, -, hi1, hle⟩ := useR hu hi hE.2.2
    have hf := bindRZ hb (FInvR_mono hi1 (le_of_add_le hle)) (RLink_of hE.2.1 hE.2.2) (vr_tidT (ρ := ρ) hs hp).2
      (lay_tidT _ _)
    refine ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hf, hsum, ?_⟩
    intro fr rest hst ws1
    rw [hret]; exact hpw fr rest hst ws1

/-- (C) `ThInvM` across a boxed `current()`, given the box facts at every environment. -/
theorem ThInvM_cur {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : String} {a : At}
    {e : Expr} {l : AllocLabel} (hterm : th.term = .let_ x (.ext .current a) e)
    (hbox : ∀ E, ThInvE p E th → MemInv g E (stOf mem pairs th) → E.sto l = some ⟨.unit, none⟩ ∧ E.pfr l = some 0)
    (h : ThInvM p g mem pairs th) :
    ThInvM p g mem pairs { th with term := e, env := (x, .tid, [cst (.loc ⟨l, 0⟩ 0)]) :: th.env } := by
  obtain ⟨E, hT, hm, hb⟩ := h
  obtain ⟨hs, hp⟩ := hbox E hT hm
  exact ⟨E, ThInvE_cur hterm hs hp hT, hm, hb⟩

theorem gOf_promise {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c : Cfg} {a : Address}
    {v : WeakMem.Val} {w : Ts} : gOf p k arch (promise c i a v w) i = gOf p k arch c i := by
  unfold gOf Cfg.n
  rw [promise_size]
  unfold promise
  split <;> rfl

theorem tstep_notDone {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hr : r ∈ tstep g mem pairs th) : isDone th = false := by
  cases h : isDone th with
  | false => rfl
  | true =>
      exfalso
      unfold isDone at h
      split at h
      next a ht hs => simp [tstep, ht, hs] at hr
      next => cases h

/-! ## Task 1: what certification gives the next step -/

/-- **L1, state form.** -/
theorem certified_promAboveSt {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {th : TTh} (hc : Certified p k arch c i) (hth : c.ths[i]? = some th) :
    PromAbove (stOf c.mem c.pairs th) :=
  fun _ ht _ hm => certified_promAbove hc hth ht hm

/-- **The taken result keeps `PromAbove`**: a thread step into a certified
configuration. -/
theorem taken_promAbove {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (hs : c' ∈ threadSteps p k arch c i) (hc : Certified p k arch c' i) :
    ∃ th r, c.ths[i]? = some th ∧ r ∈ tstep (gOf p k arch c i) c.mem c.pairs th ∧
      c'.mem = r.1 ∧ c'.pairs = r.2.1 ∧ c'.ths[i]? = some r.2.2 ∧
      PromAbove (stOf r.1 r.2.1 r.2.2) := by
  obtain ⟨th, r, hth, hr, e1, e2, e3, -⟩ := threadSteps_inv hs
  refine ⟨th, r, hth, hr, e1, e2, e3, ?_⟩
  have h := certified_promAboveSt hc e3
  rw [e1, e2] at h
  exact h

/-- **`PAx` at the source of a thread step into a certified configuration.** -/
theorem PAx_of_step {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat} {th : TTh}
    (hs : c' ∈ threadSteps p k arch c i) (hc : Certified p k arch c' i) (hth : c.ths[i]? = some th) :
    PAx (gOf p k arch c i) c.mem c.pairs th := by
  obtain ⟨th', r, hth', hr, -, -, -, hpa⟩ := taken_promAbove hs hc
  rw [hth] at hth'
  cases hth'
  exact .inr ⟨r, hr, hpa⟩

/-- **What certification gives for the next step**: no promises, or `PAx`, or
the certifying run starts with a promise step (then nothing is said about the
thread's own `tstep` at `c`). -/
theorem certified_next {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {th : TTh}
    (hc : Certified p k arch c i) (hth : c.ths[i]? = some th) :
    th.promises = [] ∨ PAx (gOf p k arch c i) c.mem c.pairs th ∨
      (∃ a v w, w < c.mem.size ∧ Certified p k arch (promise c i a v w) i) ∨
      ∃ c'', c'' ∈ extSteps c i ∧ Certified p k arch c'' i := by
  obtain ⟨c', hs, hn⟩ := hc
  cases hs with
  | refl => left; simpa [noPromises, hth] using hn
  | thread hs1 hrest => right; left; exact PAx_of_step hs1 ⟨_, hrest, hn⟩ hth
  | prom a v w hw hrest => right; right; left; exact ⟨a, v, w, hw, _, hrest, hn⟩
  | ext hs1 hrest => right; right; right; exact ⟨_, hs1, _, hrest, hn⟩

/-! ## Task 2: the typed run -/

/-- `ThInvM` under a promise step (`MemInv_promSt`; `ThInvE` does not read
the promises). -/
theorem ThInvM_promise_tr {p : Prog} {g : G} {c : Cfg} {i : Nat} {th : TTh} {a : Address} {v : WeakMem.Val}
    {w : Ts} (hth : c.ths[i]? = some th) (h : ThInvM p g c.mem c.pairs th) :
    ThInvM p g (promise c i a v w).mem (promise c i a v w).pairs
      { th with promises := th.promises ++ [c.mem.size] } := by
  obtain ⟨E, hE, hm, hbo⟩ := h
  refine ⟨E, hE, ?_, hbo⟩
  rw [(promise_inv (a := a) (v := v) (w := w) hth).2.2]
  exact MemInv_promSt hm

/-- The scope of a thread, at every typing of its frame. -/
def ScopeOK (p : Prog) (th : TTh) : Prop :=
  ∀ ρ η cx, EnvOK p η → Typed p cx th.term → TvOK cx → FInv ρ η th.σs (Resume p th.stack) cx th.env →
    ScopeD th.σs cx th.term

/-- (option (3)) A capability step writes nothing (`SW`). -/
theorem SW_cap {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {loc : Address} {val : WeakMem.Val}
    (hc : CapT th.term) (h : SW g mem pairs th loc val) : False := by
  obtain ⟨x, e, ⟨a, b, he⟩ | ⟨a, he⟩ | ⟨a, he⟩⟩ := hc <;>
  rcases h with ⟨x', op, e', ht, hw⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, -⟩ <;>
  rw [he] at ht <;> cases ht <;>
  rcases hw with ⟨_, _, _, _, _, _, _, hu, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hop, -⟩ <;>
  first | (simp [UnitsOp] at hu) | cases hop

/-- (option (3)) A writing step in the run scope is in the plain scope. -/
theorem scopeD_SW {σs : List Ty} {cx : Cx} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {loc : Address} {val : WeakMem.Val} (hsc : ScopeD σs cx th.term) (hsw : SW g mem pairs th loc val) :
    StepScope cx th.term :=
  hsc.elim id fun h => (SW_cap h.2 hsw).elim

theorem ThInvS_of {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    (h : ThInvM p g mem pairs th) (hs : ScopeOK p th) (hw : PubWinS p g mem pairs th) :
    ThInvS p g mem pairs th := by
  obtain ⟨E, ⟨ρ, η, cx, rfl, hE, hT, htv, hi, hrp⟩, hm, hbo⟩ := h
  exact ⟨ρ, η, cx, hE, hT, htv, hi, hm, hs ρ η cx hE hT htv hi, hbo, hw ρ η cx hE hT htv hi hm, hrp⟩

/-- Thread `i` of `c` satisfies the stage-A invariant. -/
def InvAt (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (c : Cfg) : Prop :=
  ∃ th, c.ths[i]? = some th ∧ ThInvM p (gOf p k arch c i) c.mem c.pairs th

/-- (C) Thread `i` of `c` is not at a boxed `current()` (one whose thread already has its box). -/
def CurFree (i : Nat) (c : Cfg) : Prop :=
  ∀ th, c.ths[i]? = some th → ∀ x a e, th.term = .let_ x (.ext .current a) e → th.tidLbl = none

/-- (C) **The pre-C certificate scope**: no configuration of the run from `c` sits at a boxed `current()`
(before C every `current()` needed an empty promise set, so no certificate run took one).  The unanchored
typed run (`InvAt`, `OwnZeroAt`: a fresh environment per step, no anchor for the box facts) is restricted to
it; the finals use the anchored run (`solo_typedX`, `TidAt`), which has no such restriction. -/
def NoBoxedCur (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (c : Cfg) : Prop :=
  ∀ c0, Solo p k arch i c c0 → CurFree i c0

/-- (C) Thread `i`'s box label, if any, is a `unit` box of `E0` at frontier `0` (`TidBox` at an anchor). -/
def TidAt (i : Nat) (c : Cfg) (E0 : TEnv) : Prop :=
  ∀ th, c.ths[i]? = some th → ∀ l, th.tidLbl = some l → E0.sto l = some ⟨.unit, none⟩ ∧ E0.pfr l = some 0

/-- (C) A promise step keeps the thread's box label. -/
theorem tidAt_prom {i : Nat} {c : Cfg} {E0 : TEnv} {a : Address} {v : WeakMem.Val} {w : Ts} (h0 : TidAt i c E0) :
    TidAt i (promise c i a v w) E0 := by
  intro th' hth' l hl
  cases hc : c.ths[i]? with
  | none =>
    unfold promise at hth'; rw [hc] at hth'; rw [hc] at hth'; cases hth'
  | some th =>
    rw [(promise_inv (a := a) (v := v) (w := w) hc).2.1] at hth'; cases hth'
    exact h0 th hc l hl

/-- (C) Along `Solo` the thread's box label is unchanged (a boxless `current()` is no `extSteps` move). -/
theorem tidAt_solo {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c0 : Cfg} {E0 : TEnv}
    (h : Solo p k arch i c c0) (h0 : TidAt i c E0) : TidAt i c0 E0 := by
  revert h0
  induction h with
  | refl => exact id
  | thread hs _ ih =>
    intro h0
    apply ih
    intro th' hth' l hl
    obtain ⟨th, r, hth, hr, -, -, hth2, -⟩ := threadSteps_inv hs
    rw [hth2] at hth'; cases hth'
    exact h0 th hth l (by rw [← TermTidLbl.tstep_tidLbl hr]; exact hl)
  | prom a v w _ _ ih => exact fun h0 => ih (tidAt_prom h0)
  | @ext c1 _ _ hs _ ih =>
    intro h0
    apply ih
    intro th' hth' l hl
    obtain ⟨th, hth, h | h⟩ := extSteps_shape hs
    · obtain ⟨x, n, a, e, evs, rs, -, -, -, rfl⟩ := h
      rw [set_self hth] at hth'; cases hth'
      exact h0 th hth l hl
    · obtain ⟨x, a, e, l', -, -, rfl⟩ := h
      rw [set_self (tr := c1.trace) hth] at hth'; cases hth'
      exact h0 th hth l hl

/-- (C) `TidAt`'s box facts at an `Ext`ension of the anchor. -/
theorem tidBox_ext {E0 E : TEnv} {l : AllocLabel} (hx : Ext E0 E)
    (h : E0.sto l = some ⟨.unit, none⟩ ∧ E0.pfr l = some 0) : E.sto l = some ⟨.unit, none⟩ ∧ E.pfr l = some 0 :=
  ⟨hx.2.2.2.2.1 l _ h.1, hx.2.2.2.2.2.2.1 l 0 h.2⟩

/-- (C) `TidAt` moves to an `Ext`ension of the anchor. -/
theorem tidAt_mono {i : Nat} {c : Cfg} {E0 E : TEnv} (hx : Ext E0 E) (h : TidAt i c E0) : TidAt i c E :=
  fun th hth l hl => tidBox_ext hx (h th hth l hl)

/-- (C) `TidAt` across a thread step. -/
theorem tidAt_thread {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c' : Cfg} {E0 : TEnv}
    (hs : c' ∈ threadSteps p k arch c i) (h : TidAt i c E0) : TidAt i c' E0 :=
  tidAt_solo (.thread hs (.refl _)) h

/-- `InvAt` across an extern move (C: not at a boxed `current()`, `CurFree`). -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem InvAt_ext {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c' : Cfg} (h : InvAt p k arch i c)
    (hs : c' ∈ extSteps c i) (hnb : CurFree i c) : InvAt p k arch i c' := by
  obtain ⟨th, hth, hinv⟩ := h
  rcases extSteps_res hs hth with ⟨x, n, a, e, rt, ws, rs, hterm, hn, hev, hrs, rfl⟩ | ⟨x, a, e, l, hterm, htl, -⟩
  · exact ⟨_, set_self hth, by rw [gOf_ext hs]; exact ThInvM_ext hn hterm hev hrs hinv⟩
  · rw [hnb th hth _ _ _ hterm] at htl; cases htl

/-- Thread `i` of `c` is in scope. -/
def ScopeAt (p : Prog) (i : Nat) (c : Cfg) : Prop := ∀ th, c.ths[i]? = some th → ¬ SpawnT th.term → ScopeOK p th

/-- A thread with a thread step is not at a spawn site (`ScopeAt`'s carve-out). -/
theorem not_spawnT_of_steps {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat} {th : TTh}
    (hth : c.ths[i]? = some th) (h : c' ∈ threadSteps p k arch c i) : ¬ SpawnT th.term := by
  obtain ⟨th', r, hth', hr, -⟩ := threadSteps_inv h
  rw [hth] at hth'
  cases hth'
  exact not_spawnT_of_mem hr

/-! ## (certWin-D, F1) The anchored antecedents and the run invariant `AnchR` -/

/-- (certWin-D, F1) At an anchor cell, `ini` exceeds the anchor's only up to `rini`. -/
def IniAnch (E0 E : TEnv) : Prop := ∀ l, E.sto l ≠ none → E.ini l ≤ max (E0.ini l) (E.rini l)

/-- (certWin-D, F1; A″) At an own cell, unseen, of positive width: a slot whose units all carry a
non-promise, non-`undef` message at or below `E1`'s frontier is counted by `rini`. -/
def RiniMem (E1 E : TEnv) (s : St) : Prop :=
  ∀ l c N e us j, E.sto l = some c → c.owner = some E.tid → ¬ E.seen l →
    c.ty = .array (.lit N) e → accs e = some us → 0 < nWords us → j < N →
    (∀ o, j * nWords us ≤ o → o < (j + 1) * nWords us →
      ∃ (t : Nat) (m : Msg), t ∉ s.promises ∧ s.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ m.val ≠ .undef ∧
        (∀ f, E1.pfr l = some f → t ≤ f)) →
    j < E.rini l

/-- (run invariant) At own cells without an anchor frontier, `ini ≤ rini`. -/
def IniLeR (E0 E : TEnv) : Prop :=
  ∀ l, E0.pfr l = none → OwnAt E l → E.ini l ≤ E.rini l

/-- The anchor with every frontier erased (for the n-case of `WrLocA2`). -/
def noPfr (E : TEnv) : TEnv := { E with pfr := fun _ => none }

/-- (L437) The run bound: at an own positive-width array cell of `E`, `E1`'s frontier lies below memory
(sto-gated: box labels carry frontiers without cells). -/
def PfrLtS (E1 E : TEnv) (s : St) : Prop :=
  ∀ l c N e us f, E.sto l = some c → c.owner = some E.tid → c.ty = .array (.lit N) e → accs e = some us →
    0 < nWords us → 0 < N → E1.pfr l = some f → f < s.mem.size


/-- (A″) `E1`'s frontiers are kept. -/
def PfrKA (E1 E : TEnv) : Prop := ∀ l f, E1.pfr l = some f → E.pfr l = some f

/-- (run invariant; A″) The anchored antecedents at `E1` (`E0` the unplanted cut below it), `IniLeR`,
the new frontiers' bound and `E1`'s frontiers kept. -/
def AnchR (E0 E1 E : TEnv) (s : St) : Prop :=
  IniAnch E1 E ∧ IniLeR E1 E ∧ RiniMem E1 E s ∧ PfrLtS E1 E s ∧ PfrKA E1 E

/-- Where a non-promise message of the post-state of a step lies (`WrLoc`): an old non-promise
message, a fresh label, an initialised unit of the pre-environment, or a slot a `bufInit` counts. -/
def WrLoc (g : G) (E E' : TEnv) (s s' : St) : Prop :=
  ∀ (t : Nat) (m : Msg), t ∉ s'.promises → s'.mem[t]? = some m →
    (t ∉ s.promises ∧ s.mem[t]? = some m) ∨ FreshIn g s.nalloc s'.nalloc m.loc.label ∨
    (∃ c, E.sto m.loc.label = some c ∧ InitR E c m.loc.label m.loc.offset) ∨
    (∃ c n, E.sto m.loc.label = some c ∧ n + 1 ≤ E'.rini m.loc.label ∧
      ∀ N e us, c.ty = .array (.lit N) e → accs e = some us → m.loc.offset < (n + 1) * nWords us)

/-- Where a non-promise message of a thread step's result lies (`WrSite`, the step-only half of
`WrLoc`): an old non-promise message, a fresh label, an initialised unit of `E`, or a slot of the
buffer a `bufInit` writes, below the written index plus one. -/
def WrSite (g : G) (E : TEnv) (mem : Memory) (pairs : List Ts) (th : TTh) (r : Memory × List Ts × TTh) :
    Prop :=
  ∀ (t : Nat) (m : Msg), t ∉ r.2.2.promises → r.1[t]? = some m →
    (t ∉ th.promises ∧ mem[t]? = some m) ∨ FreshIn g th.nalloc r.2.2.nalloc m.loc.label ∨
    (∃ c, E.sto m.loc.label = some c ∧ InitR E c m.loc.label m.loc.offset) ∨
    (∃ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e ∧ ∃ rt w ad rti wi n c,
      evalAt th.env bb = some (rt, [w]) ∧ w.val = .loc ad 0 ∧ evalAt th.env ib = some (rti, [wi]) ∧
      numOf [wi] = some n ∧ ad.label = m.loc.label ∧ E.sto m.loc.label = some c ∧
      ∀ N el us, c.ty = .array (.lit N) el → accs el = some us → m.loc.offset < (n + 1) * nWords us)

/-- (A″) `WrSite` whose initialised-unit branch also gives `InitRr`, a fresh timestamp, a timestamp
above the pre-frontier, or a seen label. -/
def WrSiteA (g : G) (E : TEnv) (mem : Memory) (pairs : List Ts) (th : TTh) (r : Memory × List Ts × TTh) :
    Prop :=
  ∀ (t : Nat) (m : Msg), t ∉ r.2.2.promises → r.1[t]? = some m →
    (t ∉ th.promises ∧ mem[t]? = some m) ∨ FreshIn g th.nalloc r.2.2.nalloc m.loc.label ∨
    (∃ c, E.sto m.loc.label = some c ∧ InitR E c m.loc.label m.loc.offset ∧
      (InitRr E c m.loc.label m.loc.offset ∨ mem.size ≤ t ∨ (∀ f, E.pfr m.loc.label = some f → f < t) ∨
        E.seen m.loc.label)) ∨
    (∃ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e ∧ ∃ rt w ad rti wi n c,
      evalAt th.env bb = some (rt, [w]) ∧ w.val = .loc ad 0 ∧ evalAt th.env ib = some (rti, [wi]) ∧
      numOf [wi] = some n ∧ ad.label = m.loc.label ∧ E.sto m.loc.label = some c ∧
      ∀ N el us, c.ty = .array (.lit N) el → accs el = some us → m.loc.offset < (n + 1) * nWords us)

/-- (certWin-D, F1) **The typed write-location fact**: a typed, in-scope thread step writes only
where `WrSite` says.  Proved downstream (`TermAnch.wrIniC`, from `TermPlantF.SWIni` and
`TermB5.tstep_newR`); theorems take it as an instance argument. -/
class WrIniC : Prop where
  wr : ∀ {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh}, EnvOK p η → Typed p cx th.term → TvOK cx →
    FInv ρ η th.σs (Resume p th.stack) cx th.env → MemInv g (CE η) (stOf mem pairs th) →
    ScopeD th.σs cx th.term → r ∈ tstep g mem pairs th → WrSite g (CE η) mem pairs th r
  /-- (A″, the `WrSiteA`; placeholder field) -/
  wrA : ∀ {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh}, EnvOK p η → Typed p cx th.term → TvOK cx →
    FInv ρ η th.σs (Resume p th.stack) cx th.env → MemInv g (CE η) (stOf mem pairs th) →
    ScopeD th.σs cx th.term → (∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws → w.view ≤ w.rts) →
    r ∈ tstep g mem pairs th → WrSiteA g (CE η) mem pairs th r

/-- `WrSite` plus the count a `bufInit` leaves gives `WrLoc`. -/
theorem wrLoc_of {g : G} {E E' : TEnv} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (hs : WrSite g E mem pairs th r)
    (hb : ∀ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e → BufInitBump th bb ib E') :
    WrLoc g E E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  intro t m ht hmt
  rcases hs t m ht hmt with h | h | h | ⟨x, bb, ib, v, e, hterm, rt, w, ad, rti, wi, n, c, hea, hw, hei, hn, hl, hc, hlt⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · refine .inr (.inr (.inr ⟨c, n, hc, ?_, hlt⟩))
    rw [← hl]; exact (hb x bb ib v e hterm rt w ad rti wi n hea hw hei hn).2

/-- (certWin-D, post-step start) `WrLoc` with the `bufInit` branch weakened against an anchor `E0`: the
slot bound, or the label's frontier unchanged from `E0`. -/
def WrLocA (E0 : TEnv) (g : G) (E E' : TEnv) (s s' : St) : Prop :=
  ∀ (t : Nat) (m : Msg), t ∉ s'.promises → s'.mem[t]? = some m →
    (t ∉ s.promises ∧ s.mem[t]? = some m) ∨ FreshIn g s.nalloc s'.nalloc m.loc.label ∨
    (∃ c, E.sto m.loc.label = some c ∧ InitR E c m.loc.label m.loc.offset) ∨
    (∃ c n, E.sto m.loc.label = some c ∧ (n + 1 ≤ E'.rini m.loc.label ∨ E'.pfr m.loc.label = E0.pfr m.loc.label) ∧
      ∀ N e us, c.ty = .array (.lit N) e → accs e = some us → m.loc.offset < (n + 1) * nWords us)

theorem WrLoc.toA {E0 : TEnv} {g : G} {E E' : TEnv} {s s' : St} (h : WrLoc g E E' s s') : WrLocA E0 g E E' s s' := by
  intro t m ht hm
  rcases h t m ht hm with h | h | h | ⟨c, n, hc, hn, ho⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr ⟨c, n, hc, .inl hn, ho⟩))

theorem anchSlot_lt {j K w o : Nat} (_hw : 0 < w) (h1 : j * w ≤ o) (h2 : o < K * w) : j < K :=
  Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt h1 h2)

/-- `PrivCoh` gives `RiniMem` at a label without a frontier. -/
theorem riniMem_priv {E : TEnv} {s : St} (hpc : PrivCoh E s) {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty}
    {us : List Acc} {j : Nat} (hpf : E.pfr l = none) (hc : E.sto l = some c) (hown : c.owner = some E.tid)
    (hty : c.ty = .array (.lit N) e) (hus : accs e = some us) (hw : 0 < nWords us) (hjN : j < N)
    (hall : ∀ o, j * nWords us ≤ o → o < (j + 1) * nWords us →
      ∃ (t : Nat) (m : Msg), t ∉ s.promises ∧ s.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ m.val ≠ .undef) :
    j < E.rini l := by
  by_cases hj : j < E.rc l
  · exact Nat.lt_of_lt_of_le hj (Nat.min_le_right _ _)
  · obtain ⟨t, m, ht, hm, hl, hv⟩ := hall (j * nWords us) (Nat.le_refl _)
      (by rw [Nat.succ_mul]; omega)
    have hu : PrivU E m.loc := by
      refine ⟨c, N, e, us, by rw [hl]; exact hc, hown, by rw [hl]; exact hpf, hty, hus, ?_, ?_⟩
      · rw [hl]; exact Nat.mul_le_mul_right _ (Nat.le_of_not_lt hj)
      · rw [hl]; exact Nat.mul_lt_mul_of_pos_right hjN hw
    exact (hv (hpc t m ht hm hu).2).elim

/-- `OwnHidP.2`'s contrapositive: an own cell without a frontier has `ini ≤ rini`. -/
theorem iniLe_of_hid {E : TEnv} {mem : Memory} {vs : VState} {P : List Ts} (h : OwnHidP E mem vs P)
    {l : AllocLabel} {c : Cell} (hc : E.sto l = some c) (hown : c.owner = some E.tid) (hpf : E.pfr l = none) :
    E.ini l ≤ E.rini l := by
  apply Nat.le_of_not_lt
  intro hlt
  have hrc : E.rc l < E.ini l := by unfold TEnv.rc; omega
  obtain ⟨f, hf, -⟩ := h.2 l c hc hown hrc
  rw [hpf] at hf; cases hf

/-- (i′ seed) Past the real count of an own buffer with a frontier, the non-promise messages at or
below the frontier are `undef`. -/
def RiniCoh (E : TEnv) (s : St) : Prop :=
  ∀ (t : Nat) (m : Msg) (c : Cell) (N : Nat) (e : Ty) (us : List Acc) (f : Ts),
    t ∉ s.promises → s.mem[t]? = some m → E.sto m.loc.label = some c → c.owner = some E.tid →
    E.pfr m.loc.label = some f → t ≤ f → c.ty = .array (.lit N) e → accs e = some us →
    E.rc m.loc.label * nWords us ≤ m.loc.offset → m.loc.offset < N * nWords us → m.val = .undef

/-- **The seed**: `PrivCoh` (labels without a frontier) and `RiniCoh` (labels with one) give the
`RiniMem` body at every own buffer, ungated (no `E0` gate, no `¬ seen`), at `E1 = E`. -/
theorem riniSlot_of {E : TEnv} {s : St} (hpc : PrivCoh E s) (h : RiniCoh E s) {l : AllocLabel} {c : Cell}
    {N : Nat} {e : Ty} {us : List Acc} {j : Nat} (hc : E.sto l = some c) (hown : c.owner = some E.tid)
    (hty : c.ty = .array (.lit N) e) (hus : accs e = some us) (hw : 0 < nWords us) (hjN : j < N)
    (hall : ∀ o, j * nWords us ≤ o → o < (j + 1) * nWords us →
      ∃ (t : Nat) (m : Msg), t ∉ s.promises ∧ s.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ m.val ≠ .undef ∧
        (∀ f, E.pfr l = some f → t ≤ f)) :
    j < E.rini l := by
  cases hp : E.pfr l with
  | none =>
    exact TermTyped.riniMem_priv hpc hp hc hown hty hus hw hjN fun o h1 h2 => by
      obtain ⟨t, m, ht, hm, hl, hv, -⟩ := hall o h1 h2
      exact ⟨t, m, ht, hm, hl, hv⟩
  | some f =>
    by_cases hj : j < E.rc l
    · exact Nat.lt_of_lt_of_le hj (Nat.min_le_right _ _)
    · obtain ⟨t, m, ht, hm, hl, hv, hf⟩ := hall (j * nWords us) (Nat.le_refl _)
        (by rw [Nat.succ_mul]; omega)
      have hl1 : m.loc.label = l := by rw [hl]
      refine absurd (h t m c N e us f ht hm (by rw [hl1]; exact hc) hown (by rw [hl1]; exact hp) (hf f hp)
        hty hus ?_ ?_) hv
      · rw [hl]; exact Nat.mul_le_mul_right _ (Nat.le_of_not_lt hj)
      · rw [hl]; exact Nat.mul_lt_mul_of_pos_right hjN hw

/-- **The seed at a typed start** (`MemInv` carries `PrivCoh`). -/
theorem riniSlot_start {g : G} {E : TEnv} {s : St} (hm : MemInv g E s) (h : RiniCoh E s) {l : AllocLabel}
    {c : Cell} {N : Nat} {e : Ty} {us : List Acc} {j : Nat} (hc : E.sto l = some c)
    (hown : c.owner = some E.tid) (hty : c.ty = .array (.lit N) e) (hus : accs e = some us)
    (hw : 0 < nWords us) (hjN : j < N)
    (hall : ∀ o, j * nWords us ≤ o → o < (j + 1) * nWords us →
      ∃ (t : Nat) (m : Msg), t ∉ s.promises ∧ s.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ m.val ≠ .undef ∧
        (∀ f, E.pfr l = some f → t ≤ f)) :
    j < E.rini l :=
  riniSlot_of hm.2.2.2.1.2 h hc hown hty hus hw hjN hall

/-- `RiniCoh` across a promise (the new message is a promise). -/
theorem riniCoh_promSt {E : TEnv} {s : St} {a : Address} {v : WeakMem.Val} {w : Ts} (h : RiniCoh E s) :
    RiniCoh E (promSt s a v w) := by
  intro t m c N e us f ht hm hc hown hpf htf hty hus h1 h2
  simp only [promSt, List.mem_append, List.mem_singleton, not_or] at ht hm
  exact h t m c N e us f ht.1 (by simpa [Array.getElem?_push, ht.2] using hm) hc hown hpf htf hty hus h1 h2

/-- **A positive-width own array cell puts a message in memory** (`OwnOKPF`: `BufOK`'s full-length words,
each `LatestSF` at a message; `wc` of an array is `none`). -/
theorem memPos_of_own {g : G} {E : TEnv} {s : St} (hm : MemInv g E s) {l : AllocLabel} {c : Cell} {N : Nat}
    {e : Ty} {us : List Acc} (hc : E.sto l = some c) (hown : c.owner = some E.tid)
    (hty : c.ty = .array (.lit N) e) (hus : accs e = some us) (hw : 0 < nWords us) (hN : 0 < N) :
    0 < s.mem.size := by
  obtain ⟨vals, hC, hL, -⟩ := hm.2.1 l c hc hown
  have hlen : 0 < vals.length := by
    rcases hC with ⟨hwc, -⟩ | ⟨N', e', us', hT, hus', -, hl, -⟩
    · rw [hty] at hwc; cases hwc
    · rw [hty] at hT; cases hT; rw [hus] at hus'; cases hus'; rw [hl]; exact Nat.mul_pos hN hw
  obtain ⟨⟨m, hm', -⟩, -⟩ := hL 0 vals[0] (List.getElem?_eq_getElem hlen)
  refine Classical.byContradiction fun hn => ?_
  rw [Array.getElem?_eq_none (Nat.le_trans (Nat.le_of_not_lt hn) (Nat.zero_le _))] at hm'; cases hm'

/-- **The seed** from a `frlt`-shaped bound (`f ≤ size - 1` at cells) and `MemInv`. -/
theorem pfrLtS_start {g : G} {E1 E : TEnv} {s : St} (hm : MemInv g E s)
    (hfl : ∀ l c f, E.sto l = some c → E1.pfr l = some f → f ≤ s.mem.size - 1) : PfrLtS E1 E s := by
  intro l c N e us f hc hown hty hus hw hN hf
  exact Nat.lt_of_le_of_lt (hfl l c f hc hf) (Nat.sub_lt (memPos_of_own hm hc hown hty hus hw hN) Nat.one_pos)

/-- **`PfrLtS` along a thread step** (old cells keep it as memory grows; a fresh cell has no frontier). -/
theorem pfrLtS_step {W : Ty → Prop} {g : G} {E1 E E' : TEnv} {s s' : St} (h : PfrLtS E1 E s) (hK : PfrKA E1 E)
    (hF : EFootB W g E E' s s') (hfr : FreshLP g E s) (hsz : s.mem.size ≤ s'.mem.size) : PfrLtS E1 E' s' := by
  intro l c N e us f hc hown hty hus hw hN hf
  have htid : E'.tid = E.tid := hF.2.1
  rcases hF.2.2.1 l with es | ⟨⟨j, hj, -, rfl⟩, -⟩
  · rw [es] at hc
    exact Nat.lt_of_lt_of_le (h l c N e us f hc (by rw [htid] at hown; exact hown) hty hus hw hN hf) hsz
  · have hE := hK _ f hf
    rw [(hfr.1 j hj).2.2.2] at hE; cases hE

/-- **The start**: the invariant's own environment satisfies `AnchR` at itself. -/
theorem anchR_start {g : G} {E : TEnv} {s : St} (hm : MemInv g E s) (hrc : RiniCoh E s)
    (hfl : ∀ l c f, E.sto l = some c → E.pfr l = some f → f ≤ s.mem.size - 1) : AnchR E E E s :=
  ⟨fun l _ => Nat.le_max_left _ _, fun l hpf ⟨c, hc, hown⟩ => iniLe_of_hid hm.2.2.2.2.2.1 hc hown hpf,
    fun _ _ _ _ _ _ hc hown _ hty hus hw hjN hall => riniSlot_start hm hrc hc hown hty hus hw hjN hall,
    pfrLtS_start hm hfl, fun _ _ h => h⟩

/-- (A″) **The start at the planted cut**: `E1` (planted, at `s1`) over the unplanted cut `E0` (at `s0`),
with the same cells, owner and at least `E0`'s `rini`, every non-promise message of `s1` one of `s0`,
and `E1`'s new frontiers below `s1`'s memory. -/
theorem anchR_plant {g : G} {E0 E1 : TEnv} {s0 s1 : St} (hpc0 : PrivCoh E0 s0) (hm1 : MemInv g E1 s1)
    (hsto : ∀ l c, E1.sto l = some c → c.owner = some E1.tid → E0.sto l = some c) (htid : E1.tid = E0.tid)
    (hri : ∀ l, E0.rini l ≤ E1.rini l)
    (hmem : ∀ (t : Nat) (m : Msg), t ∉ s1.promises → s1.mem[t]? = some m → t ∉ s0.promises ∧ s0.mem[t]? = some m)
    (hpl : PfrLtS E1 E1 s1) (hrc1 : RiniCoh E1 s1) : AnchR E0 E1 E1 s1 := by
  refine ⟨fun l _ => Nat.le_max_left _ _, fun l hpf ⟨c, hc, hown⟩ => iniLe_of_hid hm1.2.2.2.2.2.1 hc hown hpf,
    ?_, hpl, fun _ _ h => h⟩
  intro l c N e us j hc hown _ hty hus hw hjN hall
  by_cases h0' : E0.pfr l ≠ none
  · exact riniSlot_start hm1 hrc1 hc hown hty hus hw hjN hall
  have h0 : E0.pfr l = none := Classical.byContradiction h0'
  by_cases hpf1 : E1.pfr l = none
  · refine riniMem_priv hm1.2.2.2.1.2 hpf1 hc hown hty hus hw hjN fun o h1 h2 => ?_
    obtain ⟨t, m, ht, hm, hl, hv, -⟩ := hall o h1 h2
    exact ⟨t, m, ht, hm, hl, hv⟩
  · have hown0 : c.owner = some E0.tid := by rw [← htid]; exact hown
    refine Nat.lt_of_lt_of_le (riniMem_priv hpc0 h0 (hsto l c hc hown) hown0 hty hus hw hjN fun o h1 h2 => ?_) (hri l)
    obtain ⟨t, m, ht, hm, hl, hv, -⟩ := hall o h1 h2
    obtain ⟨ht0, hm0'⟩ := hmem t m ht hm
    exact ⟨t, m, ht0, hm0', hl, hv⟩

/-- **A step that keeps `E`**, every non-promise message and grows the memory keeps `AnchR`. -/
theorem anchR_keep {E0 E1 E : TEnv} {s s' : St} (h : AnchR E0 E1 E s)
    (hmem : ∀ (t : Nat) (m : Msg), t ∉ s'.promises → s'.mem[t]? = some m → t ∉ s.promises ∧ s.mem[t]? = some m)
    (hsz : s.mem.size ≤ s'.mem.size) : AnchR E0 E1 E s' := by
  obtain ⟨hA, hL, hR, hP, hK⟩ := h
  refine ⟨hA, hL, fun l c N e us j hc hown hns hty hus hw hjN hall =>
    hR l c N e us j hc hown hns hty hus hw hjN ?_,
    fun l c N e us f h1 h2 h3 h4 h5 h6 h7 => Nat.lt_of_lt_of_le (hP l c N e us f h1 h2 h3 h4 h5 h6 h7) hsz, hK⟩
  intro o h1 h2
  obtain ⟨t, m, ht, hm, hl, hv, hb⟩ := hall o h1 h2
  obtain ⟨ht', hm'⟩ := hmem t m ht hm
  exact ⟨t, m, ht', hm', hl, hv, hb⟩

/-- A label of the post-environment with a frontier is not one the step allocates. -/
theorem notFresh_pfr {W : Ty → Prop} {g : G} {E E' : TEnv} {s s' : St} (hF : EFootB W g E E' s s')
    (hfr : FreshLP g E s) {l : AllocLabel} (hf : FreshIn g s.nalloc s'.nalloc l) (hc' : E'.sto l ≠ none) :
    E'.pfr l = none := by
  obtain ⟨j, hj, -, rfl⟩ := hf
  have h0 := hfr.1 j hj
  rcases hF.2.2.2.2.2.1 (freshLabel g.lbase g.n g.i j) with e | ⟨-, F, -, -, -, ⟨c, hc, -⟩, -⟩ | ⟨-, -, he⟩
  · rw [e]; exact h0.2.2.2
  · rw [h0.1] at hc; cases hc
  · exact (hc' he).elim

theorem sto_of_pfr {W : Ty → Prop} {g : G} {E E' : TEnv} {s s' : St} (hF : EFootB W g E E' s s')
    (hfr : FreshLP g E s) {l : AllocLabel} {c : Cell} (hc' : E'.sto l = some c) (hpf : E'.pfr l ≠ none) :
    E.sto l = some c := by
  rcases hF.2.2.1 l with e | ⟨hf, -⟩
  · rw [← e]; exact hc'
  · exact (hpf (notFresh_pfr hF hfr hf (by rw [hc']; exact fun h => by cases h))).elim

/-- (A″) `WrLocA` whose initialised-unit branch also gives `InitRr`, a fresh timestamp, a timestamp
above the pre-frontier, or a seen label. -/
def WrLocA2 (E0 : TEnv) (g : G) (E E' : TEnv) (s s' : St) : Prop :=
  ∀ (t : Nat) (m : Msg), t ∉ s'.promises → s'.mem[t]? = some m →
    (t ∉ s.promises ∧ s.mem[t]? = some m) ∨ FreshIn g s.nalloc s'.nalloc m.loc.label ∨
    (∃ c, E.sto m.loc.label = some c ∧ InitR E c m.loc.label m.loc.offset ∧
      (InitRr E c m.loc.label m.loc.offset ∨ s.mem.size ≤ t ∨ (∀ f, E.pfr m.loc.label = some f → f < t) ∨
        E.seen m.loc.label)) ∨
    (∃ c n, E.sto m.loc.label = some c ∧ (n + 1 ≤ E'.rini m.loc.label ∨ E'.pfr m.loc.label = E0.pfr m.loc.label) ∧
      ∀ N e us, c.ty = .array (.lit N) e → accs e = some us → m.loc.offset < (n + 1) * nWords us)

/-- `WrSiteA` plus the count a `bufInit` leaves gives `WrLocA2` at every anchor. -/
theorem wrLocA2_of {g : G} {E E' : TEnv} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (hs : WrSiteA g E mem pairs th r)
    (hb : ∀ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e → BufInitBump th bb ib E') (E0 : TEnv) :
    WrLocA2 E0 g E E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  intro t m ht hmt
  rcases hs t m ht hmt with h | h | h | ⟨x, bb, ib, v, e, hterm, rt, w, ad, rti, wi, n, c, hea, hw, hei, hn, hl, hc, hlt⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · refine .inr (.inr (.inr ⟨c, n, hc, .inl ?_, hlt⟩))
    rw [← hl]; exact (hb x bb ib v e hterm rt w ad rti wi n hea hw hei hn).2

/-- (A″) **`RiniMem` at an old cell** across a step: a cell of the source (own, unseen, no `Ez`
frontier, a frontier in the result) whose slot is filled in the result's memory below `Ea`'s frontier
is counted by any `rini` above the source's. -/
theorem riniMemA_old {g : G} {Ez Ea E E' : TEnv} {s s' : St} (hL : IniLeR Ea E) (hR : RiniMem Ea E s)
    (hP : PfrLtS Ea E s) (hK : PfrKA Ea E) (hfr : FreshLP g E s) (hwl : WrLocA2 Ez g E E' s s')
    {l : AllocLabel} {c : Cell} {N : Nat} {e : Ty} {us : List Acc} {j : Nat} (hz : Ez.pfr l = none)
    (hrl : E.rini l ≤ E'.rini l) (hpf' : E'.pfr l ≠ none) (hc : E.sto l = some c)
    (hown : c.owner = some E.tid) (hns : ¬ E.seen l) (hty : c.ty = .array (.lit N) e) (hus : accs e = some us)
    (hw : 0 < nWords us) (hjN : j < N)
    (hall : ∀ o, j * nWords us ≤ o → o < (j + 1) * nWords us →
      ∃ (t : Nat) (m : Msg), t ∉ s'.promises ∧ s'.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ m.val ≠ .undef ∧
        ∀ f, Ea.pfr l = some f → t ≤ f) :
    j < E'.rini l := by
  by_cases hold : ∀ o, j * nWords us ≤ o → o < (j + 1) * nWords us →
      ∃ (t : Nat) (m : Msg), t ∉ s.promises ∧ s.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ m.val ≠ .undef ∧
        ∀ f, Ea.pfr l = some f → t ≤ f
  · exact Nat.lt_of_lt_of_le (hR l c N e us j hc hown hns hty hus hw hjN hold) hrl
  · obtain ⟨o, h1, h2, hno⟩ : ∃ o, j * nWords us ≤ o ∧ o < (j + 1) * nWords us ∧
        ¬ ∃ (t : Nat) (m : Msg), t ∉ s.promises ∧ s.mem[t]? = some m ∧ m.loc = ⟨l, o⟩ ∧ m.val ≠ .undef ∧
          ∀ f, Ea.pfr l = some f → t ≤ f := by
      refine Classical.byContradiction fun hn => hold fun o h1 h2 => Classical.byContradiction fun hx => hn ⟨o, h1, h2, hx⟩
    obtain ⟨t, m, ht, hmt, hl, hv, hb⟩ := hall o h1 h2
    rcases hwl t m ht hmt with ⟨ht0, hm0⟩ | hf | ⟨c2, hc2, hI, hI2⟩ | ⟨c2, n, hc2, hn, ho⟩
    · exact (hno ⟨t, m, ht0, hm0, hl, hv, hb⟩).elim
    · have hlab : m.loc.label = l := by rw [hl]
      rw [hlab] at hf
      obtain ⟨j', hj', -, rfl⟩ := hf
      rw [(hfr.1 j' hj').1] at hc; cases hc
    · rw [hl] at hc2 hI hI2
      rw [hc] at hc2; cases hc2
      cases hEa : Ea.pfr l with
      | none =>
        have hIL := hL l hEa ⟨c, hc, hown⟩
        have hlt := hI N e us hty hus
        exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (anchSlot_lt hw h1 hlt) hIL) hrl
      | some F =>
        have htF := hb F hEa
        rcases hI2 with hr | hs | hp | hsn
        · have hlt := hr N e us hty hus
          exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (anchSlot_lt hw h1 hlt) (Nat.min_le_right _ _)) hrl
        · exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans hs htF) (hP l c N e us F hc hown hty hus hw (Nat.lt_of_le_of_lt (Nat.zero_le _) hjN) hEa)) (Nat.lt_irrefl _)
        · exact absurd (Nat.lt_of_le_of_lt htF (hp F (hK l F hEa))) (Nat.lt_irrefl _)
        · exact (hns hsn).elim
    · rw [hl] at hc2 ho hn
      rw [hc] at hc2; cases hc2
      rcases hn with hn | hn
      · exact Nat.lt_of_lt_of_le (anchSlot_lt hw h1 (ho N e us hty hus)) hn
      · exact (hpf' (hn.trans hz)).elim

/-- **A thread step keeps `AnchR`**, given where the post-state's non-promise messages lie. -/
theorem anchR_stepA {W : Ty → Prop} {g : G} {E0 Ez Ea E E' : TEnv} {s s' : St} (h : AnchR E0 Ea E s)
    (hF : EFootB W g E E' s s') (hfr : FreshLP g E s) (hm' : MemInv g E' s')
    (hsub : ∀ l c, Ea.sto l = some c → E.sto l = some c) (hsz : s.mem.size ≤ s'.mem.size)
    (hwl : WrLocA2 Ez g E E' s s') (hz : ∀ l, Ez.pfr l = none) : AnchR E0 Ea E' s' := by
  obtain ⟨hA, hL, hR, hP, hK⟩ := h
  have hri : ∀ l, E.rini l ≤ E'.rini l := hF.2.2.2.2.2.2.2.2.2.1
  have htid : E'.tid = E.tid := hF.2.1
  have hK' : PfrKA Ea E' := by
    intro l f hf
    have hEf := hK l f hf
    rcases hF.2.2.2.2.2.1 l with e | ⟨hn, -⟩ | ⟨-, hn, -⟩
    · rw [e]; exact hEf
    · rw [hEf] at hn; cases hn
    · rw [hEf] at hn; cases hn
  refine ⟨?_, ?_, ?_, pfrLtS_step hP hK hF hfr hsz, hK'⟩
  · -- IniAnch
    intro l hl
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hl
    have := hri l
    have hEi : E.ini l ≤ max (Ea.ini l) (E'.rini l) := by
      by_cases hEs : E.sto l = none
      · rcases hF.2.2.1 l with e | ⟨⟨j, hj, -, rfl⟩, -⟩
        · rw [e, hEs] at hc; cases hc
        · rw [(hfr.1 j hj).2.2.1]; exact Nat.zero_le _
      · have hA' := hA l hEs
        omega
    rcases (hF.2.2.2.2.1 l).2 with e | ⟨j, hj, -, rfl⟩ | ⟨-, h, -⟩
    · rw [e]; exact hEi
    · -- fresh at this step: an own cell without a frontier, so `ini ≤ rini` (hidden units)
      have hEs : E.sto (freshLabel g.lbase g.n g.i j) = none := (hfr.1 j hj).1
      rcases hF.2.2.1 (freshLabel g.lbase g.n g.i j) with e | ⟨-, T, hT, -⟩
      · rw [e, hEs] at hc; cases hc
      · have hpf' : E'.pfr (freshLabel g.lbase g.n g.i j) = none := by
          rcases hF.2.2.2.2.2.1 (freshLabel g.lbase g.n g.i j) with e | ⟨-, F, -, -, -, ⟨c1, hc1, -⟩, -⟩ | ⟨-, -, hn⟩
          · rw [e]; exact (hfr.1 j hj).2.2.2
          · rw [hEs] at hc1; cases hc1
          · rw [hn] at hc; cases hc
        have := iniLe_of_hid hm'.2.2.2.2.2.1 hT (by rw [htid]) hpf'
        omega
    · omega
  · -- IniLeR
    intro l h0 ⟨c, hc', hown'⟩
    by_cases hpf' : E'.pfr l = none
    · exact iniLe_of_hid hm'.2.2.2.2.2.1 hc' hown' hpf'
    · have hc := sto_of_pfr hF hfr hc' hpf'
      have hown : c.owner = some E.tid := by rw [← htid]; exact hown'
      have hIH := hL l h0 ⟨c, hc, hown⟩
      have := hri l
      rcases (hF.2.2.2.2.1 l).2 with e | ⟨j, hj, -, rfl⟩ | ⟨-, h, -⟩
      · rw [e]; omega
      · rw [(hfr.1 j hj).1] at hc; cases hc
      · omega
  · -- RiniMem
    intro l c N e us j hc' hown' hns' hty hus hw hjN hall
    by_cases hpf' : E'.pfr l = none
    · refine riniMem_priv hm'.2.2.2.1.2 hpf' hc' hown' hty hus hw hjN fun o h1 h2 => ?_
      obtain ⟨t, m, ht, hm, hl, hv, -⟩ := hall o h1 h2
      exact ⟨t, m, ht, hm, hl, hv⟩
    · exact riniMemA_old hL hR hP hK hfr hwl (hz l) (hri l) hpf' (sto_of_pfr hF hfr hc' hpf')
        (by rw [← htid]; exact hown') (fun h => hns' (hF.2.2.2.2.2.2.1 l h)) hty hus hw hjN hall


/-- (S7b′, F2′ step 2 part 3) **stageB `NoHoldPub`**: thread `i` of `c` meets
`publish`'s run-level premise at every typing of its frame (`PubWinS`, whose
conclusion is now the memory/promise-level `NoHold`: no outstanding own promise
holds the published cell's unseen frontier, plus the ghost `ini ≤ rini`; the
step derives `PubWin` from it by `PubWin_of_NoHold`). -/
def NoHoldPub (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (c : Cfg) : Prop :=
  ∀ th, c.ths[i]? = some th → PubWinS p (gOf p k arch c i) c.mem c.pairs th

/-- (certWin-D; A″) `PubWinS` restricted to the typings anchored at `E1` over the unplanted `E0`:
`Ext E1 (CE η)`, `IniAnch` and `RiniMem`. -/
def PubWinSA (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (E0 E1 : TEnv) : Prop :=
  ∀ ρ η cx, EnvOK p η → Typed p cx th.term → TvOK cx → FInv ρ η th.σs (Resume p th.stack) cx th.env →
    MemInv g (CE η) (stOf mem pairs th) → Ext E1 (CE η) → IniAnch E1 (CE η) →
    RiniMem E1 (CE η) (stOf mem pairs th) → PubWinT (CE η) (stOf mem pairs th) th

/-- (certWin-D) **`NoHoldPub` anchored at `E0`**: thread `i` of `c` meets `publish`'s run-level premise
at every typing of its frame anchored at `E0` (`PubWinSA`). -/
def NoHoldPubA (p : Prog) (k : Promises.Knobs) (arch : Arch) (E0 E1 : TEnv) (i : Nat) (c : Cfg) : Prop :=
  ∀ th, c.ths[i]? = some th → PubWinSA p (gOf p k arch c i) c.mem c.pairs th E0 E1

/-- (D+) `PubWinT` at the unseen publishes only (α ∪ γ); seen publishes (β) follow from `MemInv`
(`TermDPlus.noHold_seen`). -/
def PubWinTN (E : TEnv) (s : St) (th : TTh) : Prop :=
  ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad 0] → ¬ E.seen ad.label → NoHold E s ad.label

/-- (D+) `PubWinSA` with `PubWinTN`: the anchored typings, unseen publishes only. -/
def PubWinSAN (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (E0 E1 : TEnv) : Prop :=
  ∀ ρ η cx, EnvOK p η → Typed p cx th.term → TvOK cx → FInv ρ η th.σs (Resume p th.stack) cx th.env →
    MemInv g (CE η) (stOf mem pairs th) → Ext E1 (CE η) → IniAnch E1 (CE η) →
    RiniMem E1 (CE η) (stOf mem pairs th) → PubWinTN (CE η) (stOf mem pairs th) th

/-- (D+, N3′) **`NoHoldPubA` at the unseen publishes only** (`PubWinSAN`); `TermDPlus.noHoldPubA_of_N`
restores `NoHoldPubA`. -/
def NoHoldPubN (p : Prog) (k : Promises.Knobs) (arch : Arch) (E0 E1 : TEnv) (i : Nat) (c : Cfg) : Prop :=
  ∀ th, c.ths[i]? = some th → PubWinSAN p (gOf p k arch c i) c.mem c.pairs th E0 E1

/-- **The typed run, local form.**  If the taken step at every certified
configuration reached from `c` preserves the invariant (`hloc`, given the
typed, in-scope source, `PromAbove` of the result and `PAx` of the source),
then thread `i` satisfies `ThInvM` at every certified configuration reached
from `c`. -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem solo_typedL {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c : Cfg}
    (hloc : ∀ c0 th r, Solo p k arch i c c0 → Certified p k arch c0 i → c0.ths[i]? = some th →
      ThInvS p (gOf p k arch c0 i) c0.mem c0.pairs th → r ∈ tstep (gOf p k arch c0 i) c0.mem c0.pairs th →
      PromAbove (stOf r.1 r.2.1 r.2.2) → PAx (gOf p k arch c0 i) c0.mem c0.pairs th →
      ThInvM p (gOf p k arch c0 i) r.1 r.2.1 r.2.2)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPub p k arch i c0)
    (h0 : InvAt p k arch i c) (hnb : NoBoxedCur p k arch i c) {c2 : Cfg} (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i) :
    InvAt p k arch i c2 := by
  refine (run_inv (c1 := c2) (P := fun c0 => Solo p k arch i c c0 ∧ InvAt p k arch i c0) ?_ ?_ ?_ h
    (.refl _) ⟨.refl _, h0⟩).2
  · rintro c0 c0' ⟨hc0, th, hth, hinv⟩ hs hrest
    have hc0' : Certified p k arch c0' i := certified_back hrest hc2
    have hcert0 : Certified p k arch c0 i := certified_back (.thread hs hrest) hc2
    obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc0'
    rw [hth] at hth'
    cases hth'
    have hS := ThInvS_of hinv (hsc c0 hc0 hcert0 th hth (not_spawnT_of_mem hr)) (hwin c0 hc0 hcert0 th hth)
    have hr' := hloc c0 th r hc0 hcert0 hth hS hr hpa (PAx_of_step hs hc0' hth)
    refine ⟨solo_trans hc0 (.thread hs (.refl _)), r.2.2, e3, ?_⟩
    rw [gOf_thread hs, e1, e2]
    exact hr'
  · rintro c0 a v w ⟨hc0, th, hth, hinv⟩ hw _
    refine ⟨solo_trans hc0 (.prom a v w hw (.refl _)), _,
      (promise_inv (a := a) (v := v) (w := w) hth).2.1, ?_⟩
    rw [gOf_promise]
    exact ThInvM_promise_tr hth hinv
  · rintro c0 c0' ⟨hc0, hinv⟩ hs _
    exact ⟨solo_trans hc0 (.ext hs (.refl _)), InvAt_ext hinv hs (hnb c0 hc0)⟩

/-- **The typed run** from the restated (taken-result) dispatch `StepPresW`:
no hypothesis beyond the initial invariant and the run-level scope. -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem solo_typedW {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c : Cfg}
    (hpres : StepPresW p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPub p k arch i c0)
    (h0 : InvAt p k arch i c) (hnb : NoBoxedCur p k arch i c) {c2 : Cfg} (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i) :
    InvAt p k arch i c2 :=
  solo_typedL (fun _ _ r _ _ hth hS hr hpa _ =>
    hpres _ _ _ _ rfl (Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth))) hS r hr hpa) hsc hvI hwin h0 hnb h hc2

/-- **The typed run from `ProgT`**: `StepPresW` is `TermStep.stepPresW_of`. -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem solo_typedP {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c : Cfg} [ProgRetIall p] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPub p k arch i c0)
    (h0 : InvAt p k arch i c) (hnb : NoBoxedCur p k arch i c) {c2 : Cfg} (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    InvAt p k arch i c2 :=
  solo_typedW (stepPresW_of hP hPS hSub hSig) hsc hvI hwin h0 hnb h hc2

/-! ## Task 3: the S3 fix -/

/-- **Task 3, typed.**  Every outstanding promise of a certified thread whose
invariant holds is fulfilled by a step taken at a typed, in-scope,
`PromAbove` configuration `c1` (a single-word write `SW` of its message), into
a configuration `c2` where the invariant holds and the message is no longer a
promise. -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem certified_promTyped {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    (hpres : StepPresW p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPub p k arch i c0)
    (h0 : InvAt p k arch i c) (hnb : NoBoxedCur p k arch i c) (hc : Certified p k arch c i) (hw : PWF c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m) :
    ∃ c1 c2 th1 th2, Solo p k arch i c c1 ∧ Certified p k arch c1 i ∧ c2 ∈ threadSteps p k arch c1 i ∧
      Certified p k arch c2 i ∧ c1.ths[i]? = some th1 ∧ c2.ths[i]? = some th2 ∧
      ThInvS p (gOf p k arch c1 i) c1.mem c1.pairs th1 ∧ PromAbove (stOf c1.mem c1.pairs th1) ∧
      ThInvM p (gOf p k arch c2 i) c2.mem c2.pairs th2 ∧
      c1.mem[t]? = some m ∧ c2.mem[t]? = some m ∧ t ∈ th1.promises ∧ t ∉ th2.promises ∧
      SW (gOf p k arch c1 i) c1.mem c1.pairs th1 m.loc m.val := by
  obtain ⟨m', hm', c1, c2, th1, h1, h2, hc2, hth1, hm1, ht1, hn2, hsw⟩ := certified_fulfilC hc hw ht
  rw [hm] at hm'
  cases hm'
  have hc1 : Certified p k arch c1 i := certified_back (.thread h2 (.refl _)) hc2
  obtain ⟨th1', hth1', hinv1⟩ := solo_typedW hpres hsc hvI hwin h0 hnb h1 hc1
  rw [hth1] at hth1'
  cases hth1'
  have h12 : Solo p k arch i c c2 := solo_trans h1 (.thread h2 (.refl _))
  obtain ⟨th2, hth2, hinv2⟩ := solo_typedW hpres hsc hvI hwin h0 hnb h12 hc2
  obtain ⟨th', r, hth', hr, e1, -, -, -⟩ := threadSteps_inv h2
  rw [hth1] at hth'
  cases hth'
  have hm2 : c2.mem[t]? = some m := by rw [e1]; exact (tstep_grow hr).1 t m hm1
  refine ⟨c1, c2, th1, th2, h1, hc1, h2, hc2, hth1, hth2,
    ThInvS_of hinv1 (hsc c1 h1 hc1 th1 hth1 (not_spawnT_of_mem hr)) (hwin c1 h1 hc1 th1 hth1), certified_promAboveSt hc1 hth1, hinv2, hm1, hm2, ht1,
    ?_, hsw⟩
  rwa [promsOf_some hth2] at hn2

/-- **The promised message is typed once fulfilled** (no typing hypothesis):
in the invariant's environment `E2` after the fulfilling step, if the label is
in Σ, the message is `undef` or a `WordOK` word of the cell's type. -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem certified_promWordOK {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    (hpres : StepPresW p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPub p k arch i c0)
    (h0 : InvAt p k arch i c) (hnb : NoBoxedCur p k arch i c) (hc : Certified p k arch c i) (hw : PWF c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m) :
    ∃ c2 th2 E2, Solo p k arch i c c2 ∧ Certified p k arch c2 i ∧ c2.ths[i]? = some th2 ∧
      ThInvE p E2 th2 ∧ MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      ∀ cl, E2.sto m.loc.label = some cl → m.val = .undef ∨ WordOK E2 cl.ty m.loc.offset (mw m) := by
  obtain ⟨c1, c2, -, th2, h1, -, h2, hc2, -, hth2, -, -, ⟨E2, hE2, hm2i, -⟩, -, hm2, -, hn2, -⟩ :=
    certified_promTyped hpres hsc hvI hwin h0 hnb hc hw ht hm
  exact ⟨c2, th2, E2, solo_trans h1 (.thread h2 (.refl _)), hc2, hth2, hE2, hm2i,
    fun cl hcl => hm2i.1.1 t m cl hn2 hm2 hcl⟩

/-- A closed, state-local stage-A statement: a single-word write of a typed,
in-scope, `PromAbove` thread lands on a `.one` unit of a component of the
target cell's type (to be proved op by op from the store typing rules). -/
def SWOne (p : Prog) : Prop :=
  ∀ (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (ρ : Nat → Nat) (η : TEnv) (cx : Cx)
    (loc : Address) (val : WeakMem.Val), EnvOK p η → Typed p cx th.term → TvOK cx →
    FInv ρ η th.σs (Resume p th.stack) cx th.env → MemInv g (CE η) (stOf mem pairs th) →
    StepScope cx th.term → PromAbove (stOf mem pairs th) → SW g mem pairs th loc val →
    ∃ cl o U us j, (CE η).sto loc.label = some cl ∧ AtOff cl.ty o U ∧ accs U = some us ∧
      TermFul.OneAt us j ∧ loc.offset = o + j

/-- **`certified_noPairProm` without run-level typing**: from the state-local
`SWOne`, an outstanding promise lies in a `.one` unit of the cell type `cl.ty`
that the fulfilling configuration's environment gives its label, so in no
`word2` unit of it. -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem certified_noPairPromT {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    (hpres : StepPresW p) (hone : SWOne p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPub p k arch i c0)
    (h0 : InvAt p k arch i c) (hnb : NoBoxedCur p k arch i c) (hc : Certified p k arch c i) (hw : PWF c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m) :
    ∃ c1 th1 E1 cl, Solo p k arch i c c1 ∧ Certified p k arch c1 i ∧ c1.ths[i]? = some th1 ∧
      ThInvE p E1 th1 ∧ MemInv (gOf p k arch c1 i) E1 (stOf c1.mem c1.pairs th1) ∧
      E1.sto m.loc.label = some cl ∧
      ∀ o2 r P, AtOff cl.ty o2 (.word2 r P) → m.loc.offset ≠ o2 ∧ m.loc.offset ≠ o2 + 1 := by
  obtain ⟨c1, -, th1, -, h1, hc1, -, -, hth1, -, hS, hpa, -, -, -, -, -, hsw⟩ :=
    certified_promTyped hpres hsc hvI hwin h0 hnb hc hw ht hm
  obtain ⟨ρ, η, cx, hE, hT, htv, hi, hmi, hscope, -, -, hrp⟩ := hS
  obtain ⟨cl, o, U, us, j, hcl, h1o, hus, hj, ho⟩ :=
    hone _ _ _ _ ρ η cx _ _ hE hT htv hi hmi (scopeD_SW hscope hsw) hpa hsw
  refine ⟨c1, th1, CE η, cl, h1, hc1, hth1, ⟨ρ, η, cx, rfl, hE, hT, htv, hi, hrp⟩, hmi, hcl,
    fun o2 r P h2 => ?_⟩
  rw [ho]
  exact TermGlob.oneAt_word2 h1o hus hj h2

/-- **`certified_promWord` without run-level typing**: from a value-level fact
`hG` (a `WordOK` word at a `.word n P` position satisfies `Good n P`), an
outstanding promise at a `.word n P` position of its cell's type (in the
environment after its fulfil) is `undef` or satisfies `Good n P`. -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem certified_promWordT {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    (Good : Idx → Proto → WeakMem.Val → Prop)
    (hG : ∀ (E : TEnv) (T : Ty) (o : Nat) (w : Word) (n : Idx) (P : Proto), WordOK E T o w →
      AtOff T o (.word n P) → Good n P w.val)
    (hpres : StepPresW p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPub p k arch i c0)
    (h0 : InvAt p k arch i c) (hnb : NoBoxedCur p k arch i c) (hc : Certified p k arch c i) (hw : PWF c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m) :
    ∃ c2 th2 E2, Solo p k arch i c c2 ∧ Certified p k arch c2 i ∧ c2.ths[i]? = some th2 ∧
      ThInvE p E2 th2 ∧ MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      ∀ cl n P, E2.sto m.loc.label = some cl → AtOff cl.ty m.loc.offset (.word n P) →
        m.val = .undef ∨ Good n P m.val := by
  obtain ⟨c2, th2, E2, h2, hc2, hth2, hE2, hm2, hok⟩ := certified_promWordOK hpres hsc hvI hwin h0 hnb hc hw ht hm
  refine ⟨c2, th2, E2, h2, hc2, hth2, hE2, hm2, fun cl n P hcl hP => ?_⟩
  rcases hok cl hcl with h | h
  · exact .inl h
  · exact .inr (hG E2 cl.ty _ _ n P h hP)

/-! ## SWOne, op by op: single-word writes land on `.one` units

`SWAt η loc`: `loc` is word `j` of a `.one` unit of a component `U` (at `o`) of
the type of `loc`'s cell in `η`.  The address comes from the static type of
the pointer operand (`VR` at `ptr`/`loc` is mode-independent); the unit list
`us` is the runtime pointee's, which agrees with the closed static pointee's
(`pub_accs` and its buffer analogues; needs `opaqueOK` of the pointee, which
every store-like rule supplies). -/

/-- The conclusion of `SWOne` at one address. -/
def SWAt (η : TEnv) (loc : Address) : Prop :=
  ∃ cl o U us j, η.sto loc.label = some cl ∧ AtOff cl.ty o U ∧ accs U = some us ∧
    TermFul.OneAt us j ∧ loc.offset = o + j

theorem swAt_offs {η : TEnv} {b : Address} {c : Cell} {U : Ty} {us : List Acc} {j : Nat}
    (hsto : η.sto b.label = some c) (hat : AtOff c.ty b.offset U) (hus : accs U = some us)
    (hj : TermFul.OneAt us j) : SWAt η (offs b j) :=
  ⟨c, b.offset, U, us, j, hsto, hat, hus, hj, rfl⟩

theorem swAt_one {η : TEnv} {b : Address} {c : Cell} {U : Ty}
    (hsto : η.sto b.label = some c) (hat : AtOff c.ty b.offset U) (hus : accs U = some [.one]) :
    SWAt η b :=
  ⟨c, b.offset, U, [.one], 0, hsto, hat, hus, .here _, rfl⟩

/-- (B5) The units `us` an access writes from address `b` are those of a component of `b`'s cell
type at `b`'s offset: what every store-like op's typing gives, whatever the unit's role. -/
def UnitsAt (η : TEnv) (b : Address) (us : List Acc) : Prop :=
  ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ accs U = some us

theorem swAt_of_ua {η : TEnv} {b : Address} {us : List Acc} {j : Nat} (h : UnitsAt η b us)
    (hj : TermFul.OneAt us j) : SWAt η (offs b j) :=
  let ⟨_, _, hsto, hat, hus⟩ := h; swAt_offs hsto hat hus hj

/-- **A reference's or locative's target**, from the static type alone. -/
theorem ptr_target {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) :
    ∃ c U, η.sto b.label = some c ∧ AtOff c.ty b.offset U ∧ Fd U (cl ρ η.wit 0 0 u) := by
  obtain ⟨rt', ws, hea', hv, -⟩ := peek_VR hvars hp
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  rcases ht with rfl | rfl
  · simp only [VR] at hv
    obtain ⟨a', c, hws, hoff, hsto, hcty, -, hacc⟩ := hv
    have hpw : pw.val = .loc a' 0 := by simpa using hws
    have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
    subst e
    refine ⟨c, c.ty, hsto, ?_, hcty⟩
    rw [hoff]; exact Fd_AtOff Fd.refl hacc
  · simp only [VR] at hv
    rcases hv with ⟨hws, -⟩ | ⟨a', c, U, hws, hsto, hat, hFd, -, -⟩
    · have hpw : pw.val = .null := by simpa using hws
      simp [addrOf, hpw] at hb
    · have hpw : pw.val = .loc a' 0 := by simpa using hws
      have e : b = a' := by simp [addrOf, hpw] at hb; exact hb.symm
      subst e
      exact ⟨c, U, hsto, hat, hFd⟩

/-- A cell operation (`store`, `xchg`) through a pointer or locative. -/
theorem cell_ua {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {a : At} {t u rt ru : Ty} {μ μr : Mode} {pw : Word} {b : Address}
    {us : List Acc}
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hp : cx.peek a = .ok t) (hc : cellOf t = some (μ, u)) (ho : cx.opaqueOK u = true)
    (hea : evalAt env a = some (rt, [pw])) (hcr : cellOf rt = some (μr, ru)) (hb : addrOf pw = some b)
    (hus : accs ru = some us) : UnitsAt η b us := by
  obtain ⟨c, U, hsto, hat, hFd⟩ := ptr_target hi.2.1 hp (cell_cases hc) hea hb
  have hacc : accs U = some us := by
    rw [Fd_accs hFd, ← pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hp hc ho hea hcr,
      hus]
  exact ⟨_, _, hsto, hat, hacc⟩

theorem store_ua {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {rl : Bool} {a v : At}
    {tok : Option At} {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.store rl a v tok) c') (hsc : OpScope cx (.store rl a v tok))
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s (.store rl a v tok) pw b rel us ws) : UnitsAt η b us := by
  obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
  cases hop with
  | storeOwn hp _ hc _ hu' hsub _ =>
      exact cell_ua hi hE htv hp hc (sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus
  | storePub hp _ hc _ hu' hsub _ _ =>
      exact cell_ua hi hE htv hp hc (sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus
  | storeRgn hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeCap hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeWordGive hp hw | storeWordKeep hp hw | storeWordHand hp hw =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      rcases ht with rfl | rfl
      · exact cell_ua hi hE htv hp rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea hcr hb hus
      · exact cell_ua hi hE htv hp rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea hcr hb hus

theorem xchg_ua {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {a v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchg a v) c') (hsc : OpScope cx (.xchg a v))
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s (.xchg a v) pw b rel us ws) : UnitsAt η b us := by
  obtain ⟨-, rt, rv, μr, ru, hea, -, hcr, hb, hus⟩ := hu
  cases hop with
  | xchg hp hx hu' hsub _ =>
      cases hx with
      | rgn _ hc _ _ _ => exact absurd hc (hsc _ hp _ _)
      | own _ hc _ =>
          exact cell_ua hi hE htv hp hc (sub_opaqueOK (hsub.elim id id)
            (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)) hea hcr hb hus

/-- The runtime element's units are the closed static element's. -/
theorem buf_accs {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {b : At} {t u rt ur : Ty} {μ μr : Mode} {n k : Idx} {ws : List Word}
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η)
    (hp : cx.peek b = .ok t) (hbuf : bufOf t = some (μ, n, u, k)) (ho : cx.opaqueOK u = true)
    (htb : tb cx.ke.length u = true)
    (hea : evalAt env b = some (rt, ws)) (hbe : bufElem rt = some (μr, ur)) :
    accs ur = accs (cl ρ η.wit 0 0 u) :=
  (accs_of_elyt (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2).trans
    (accs_WitL hi.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho (lt_of_guardT htb hi.2.2.2.2.1))

/-- Shared slot fact of the `ldl`/`stl` lane ops: the cell at the lane word
`j0 / w0.lanes` of the buffer is a `.lanes sg0 w0` unit (shared by `ldl_rdC`/`stl_ua`). -/
theorem lane_slotN {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {bb i : At} {rt t1 u0 : Ty} {pw : Word} {iws : List Word} {μ0 : Mode}
    {j0 : Nat} {a0 : Address} {sg0 : Bool} {w0 : Wd}
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hx : ∃ t u n k jj q, cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧
      IntIdx cx i jj ∧ LtI cx jj (.smul q.2.lanes n) ∧ LtI cx jj (.smul q.2.lanes k))
    (hea : evalAt env bb = some (rt, [pw])) (hei : evalAt env i = some (t1, iws))
    (hbe : bufElem rt = some (μ0, u0)) (hnj : numOf iws = some j0) (hb : addrOf pw = some a0)
    (hlo0 : lanesOf u0 = some (sg0, w0)) :
    ∃ c, η.sto a0.label = some c ∧
      AtOff c.ty (offs a0 (j0 / w0.lanes)).offset (cl ρ η.wit 0 0 (.lanes sg0 w0)) := by
  obtain ⟨t, u, n, k, jj, q, hp, hbuf, hlo, hint, hlt, hltk⟩ := hx
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  simp only at hu hlt hltk
  subst hu
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei', hwi, -⟩ := atom_num hi.2.1 hpi hti
  have hJ0 : ev ρ jj < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi.1
  have hJk0 : ev ρ jj < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi.1
  have hJ : ev ρ jj / w.lanes < ev ρ n :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
  have hJk : ev ρ jj / w.lanes < ev ρ k :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
  obtain ⟨rt', pw', ad, c, μr, ur, us', hea', hwv, hbe', hus', hsto, hat, -, -, hsku, -⟩ :=
    slot_viewN (ev ρ jj / w.lanes) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  rw [hbe] at hbe'
  simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
  obtain ⟨rfl, rfl⟩ := hbe'
  rw [hei] at hei'
  simp only [Option.some.injEq, Prod.mk.injEq] at hei'
  obtain ⟨rfl, rfl⟩ := hei'
  have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
  subst hj0
  simp only [lanesOf, Option.some.injEq, Prod.mk.injEq] at hlo0
  obtain ⟨rfl, rfl⟩ := hlo0
  have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
  subst e
  have e1 : ev ρ jj / w.lanes * nWords [Acc.one] = ev ρ jj / w.lanes := by simp [nWords, Acc.size]
  rw [e1] at hat
  exact ⟨_, hsto, hat⟩

#print axioms lane_slotN

/-- Shared slot fact of the `ldlw`/`stlw` lane ops: the cell at word `i0` of the
buffer is a `.lanes sg0 w0` unit (shared by `ldlw_rdC`/`stlw_ua`). -/
theorem lane_slotW {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {bb wi : At} {rt t1 u0 : Ty} {pw : Word} {iws : List Word} {μ0 : Mode}
    {i0 : Nat} {a0 : Address} {sg0 : Bool} {w0 : Wd}
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hx : ∃ t u n k jw q, cx.peek bb = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧
      IntIdx cx wi jw ∧ LtI cx jw n ∧ LtI cx jw k)
    (hea : evalAt env bb = some (rt, [pw])) (hei : evalAt env wi = some (t1, iws))
    (hbe : bufElem rt = some (μ0, u0)) (hni : numOf iws = some i0) (hb : addrOf pw = some a0)
    (hlo0 : lanesOf u0 = some (sg0, w0)) :
    ∃ c, η.sto a0.label = some c ∧ AtOff c.ty (offs a0 i0).offset (cl ρ η.wit 0 0 (.lanes sg0 w0)) := by
  obtain ⟨t, u, n, k, jw, q, hp, hbuf, hlo, hint, hlt, hltk⟩ := hx
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  simp only at hu
  subst hu
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨rt', w', ad, c, μr, ur, us', rti, wwi, hea', hwv, hei', hni', hbe', hus', hsto, hat, -, -,
    hsku, -, -, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus'
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  rw [hei] at hei'
  simp only [Option.some.injEq, Prod.mk.injEq] at hei'
  obtain ⟨rfl, rfl⟩ := hei'
  rw [hni] at hni'
  simp only [Option.some.injEq] at hni'
  subst hni'
  rw [hbe] at hbe'
  simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
  obtain ⟨rfl, rfl⟩ := hbe'
  simp only [lanesOf, Option.some.injEq, Prod.mk.injEq] at hlo0
  obtain ⟨rfl, rfl⟩ := hlo0
  have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
  subst e
  have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
  rw [e1] at hat
  exact ⟨_, hsto, hat⟩

#print axioms lane_slotW

/-- Shared slot fact of the `loadAt`/`xchgAt` buffer ops (shared by
`loadAt_rdC`/`xchgAt_ua`). -/
theorem buf_slot {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {bb i : At} {t u rt ti u0 : Ty} {μ μ0 : Mode} {n k j : Idx}
    {pw : Word} {iws : List Word} {j0 : Nat} {a0 : Address} {us : List Acc}
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hp : cx.peek bb = .ok t) (hbuf : bufOf t = some (μ, n, u, k)) (hint : IntIdx cx i j)
    (hlt : LtI cx j n) (hltk : LtI cx j k) (ho : cx.opaqueOK u = true)
    (hea : evalAt env bb = some (rt, [pw])) (hei : evalAt env i = some (ti, iws))
    (hbe : bufElem rt = some (μ0, u0)) (hnj : numOf iws = some j0) (hb : addrOf pw = some a0)
    (hus : accs u0 = some us) :
    ∃ c, η.sto a0.label = some c ∧ AtOff c.ty (offs a0 (j0 * nWords us)).offset (cl ρ η.wit 0 0 u) ∧
      accs (cl ρ η.wit 0 0 u) = some us ∧ tb cx.ke.length u = true := by
  obtain ⟨rt', w, ad, c, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, -, -, -, -,
    htb, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  rw [hei] at hei'
  simp only [Option.some.injEq, Prod.mk.injEq] at hei'
  obtain ⟨rfl, rfl⟩ := hei'
  rw [hbe] at hbe'
  simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
  obtain ⟨rfl, rfl⟩ := hbe'
  rw [hnj] at hnj'
  simp only [Option.some.injEq] at hnj'
  subst hnj'
  rw [hus] at hus'
  simp only [Option.some.injEq] at hus'
  subst hus'
  have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
  subst e
  exact ⟨c, hsto, hat, (buf_accs hi hE hp hbuf ho htb hea hbe).symm.trans hus, htb⟩

#print axioms buf_slot

/-- Shared slot fact of the `loadAtF`/`xchgAtF` field ops (shared by
`loadAtF_rdC`/`xchgAtF_ua`). -/
theorem bufF_slot {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {bb i : At} {q : List Nat} {t u cT rt ti u0 c0 : Ty} {μ μ0 : Mode} {n k j : Idx}
    {pw : Word} {iws : List Word} {j0 o0 : Nat} {a0 : Address} {us0 cs : List Acc}
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hp : cx.peek bb = .ok t) (hbuf : bufOf t = some (μ, n, u, k)) (hct : compTy u q = some cT)
    (hopu : cx.opaqueOK u = true) (hint : IntIdx cx i j)
    (hlt : LtI cx j n) (hltk : LtI cx j k) (ho : cx.opaqueOK cT = true)
    (hea : evalAt env bb = some (rt, [pw])) (hei : evalAt env i = some (ti, iws))
    (hbe : bufElem rt = some (μ0, u0)) (hnj : numOf iws = some j0) (hb : addrOf pw = some a0)
    (hus0 : accs u0 = some us0) (hco0 : compOff u0 q = some (c0, o0)) (hcs : accs c0 = some cs) :
    ∃ cc, η.sto a0.label = some cc ∧
      AtOff cc.ty (offs a0 (j0 * nWords us0 + o0)).offset (cl ρ η.wit 0 0 cT) ∧
      accs (cl ρ η.wit 0 0 cT) = some cs ∧ tb cx.ke.length cT = true := by
  obtain ⟨rt', w, ad, cc, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, -, -,
    hsku, hsig, htbu, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hopu
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  rw [hei] at hei'
  simp only [Option.some.injEq, Prod.mk.injEq] at hei'
  obtain ⟨rfl, rfl⟩ := hei'
  rw [hbe] at hbe'
  simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
  obtain ⟨rfl, rfl⟩ := hbe'
  rw [hnj] at hnj'
  simp only [Option.some.injEq] at hnj'
  subst hnj'
  rw [hus0] at hus'
  simp only [Option.some.injEq] at hus'
  subst hus'
  have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
  subst e
  obtain ⟨cR, o, hco, -, -, -, hato⟩ := compOff_rt q _ _ u0 us0 hct hsku hsig hus0
  rw [hco0] at hco
  simp only [Option.some.injEq, Prod.mk.injEq] at hco
  obtain ⟨rfl, rfl⟩ := hco
  have htbc := TermStep.tb_compTy q _ _ hct htbu
  refine ⟨cc, hsto, ?_, (accs_WitL hi.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho
    (lt_of_guardT htbc hi.2.2.2.2.1)).symm.trans
    ((accs_of_elyt (compOff_lyt q _ _ u0 c0 o0 hct hsku (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2
      hco0)).symm.trans hcs), htbc⟩
  simpa [offs, Nat.add_assoc] using AtOff_trans hat hato

#print axioms bufF_slot


theorem xchgAt_ua {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAt bb i v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s (.xchgAt bb i v) pw b rel us ws) : UnitsAt η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, hea, hei, -, hbe, hnj, hb, hus, rfl⟩ := hu
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨c, hsto, hat, hacc, -⟩ := buf_slot hi hE htv hp hbuf hint hlt hltk ho hea hei hbe hnj hb hus
      exact ⟨_, _, hsto, hat, hacc⟩

theorem xchgAtF_ua {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At} {q : List Nat}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAtF bb i q v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s (.xchgAtF bb i q v) pw b rel us ws) : UnitsAt η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, us0, c0, o0, hea, hei, -, hbe, hnj, hb, hus0, hco0, hus, rfl⟩ :=
    hu
  cases hop with
  | xchgAtF hp hbuf hct hopu _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨cc, hsto, hat, hacc, -⟩ :=
        bufF_slot hi hE htv hp hbuf hct hopu hint hlt hltk ho hea hei hbe hnj hb hus0 hco0 hus
      exact ⟨_, _, hsto, hat, hacc⟩

theorem bufInit_ua {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.bufInit bb i v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s (.bufInit bb i v) pw b rel us ws) : UnitsAt η b us := by
  obtain ⟨-, rt, t1, t2, iws, μ0, u0, j0, a0, μ', n', e', ψ, hea, hei, -, hbe, hnj, hb, hus, -, rfl⟩ := hu
  cases hop with
  | bufInit hu' hbuf hint heq hlt hu2 hsub _ =>
      obtain ⟨t, u, n, k, jj, c₁, tv, c₂, hu', hbuf, hint, heq, hlt, hu2, hsub⟩ :
          ∃ t u n k jj c₁ tv c₂, cx.use bb = .ok (t, c₁) ∧ bufOf t = some (.own, n, u, k) ∧
            IntIdx c₁ i jj ∧ EqI c₁ jj k ∧ LtI c₁ k n ∧ c₁.use v = .ok (tv, c₂) ∧ SubS c₂ tv u :=
        ⟨_, _, _, _, _, _, _, _, hu', hbuf, hint, heq, hlt, hu2, hsub⟩
      have ht : t = .refine (.loc .own (.array n u)) (.ini k) := by
        unfold bufOf at hbuf; split at hbuf
        · simp only [Option.some.injEq, Prod.mk.injEq] at hbuf
          obtain ⟨h1, rfl, rfl, rfl⟩ := hbuf; subst h1; rfl
        · simp at hbuf
      subst ht
      have htu := use_TvOK hu' htv
      obtain ⟨hi1, rb, wsb, hea', hvb, hlb⟩ := use_FInv hu' hi
      have hJK : ev ρ jj = ev ρ k := heq ρ hi1.1
      have hKN : ev ρ k < ev ρ n := hlt ρ hi1.1
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rti, wsi, hei', hvi, -⟩ := peek_VR hi1.2.1 hpi
      obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intS hti hvi)
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq] at hei'
      obtain ⟨rfl, rfl⟩ := hei'
      have hj0 : j0 = ev ρ jj := by simp [numOf, hwi] at hnj; exact hnj.symm
      subst hj0
      simp only [VR] at hvb
      obtain ⟨hv, -⟩ := hvb
      rcases hv with ⟨-, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat0, hFU, -, -⟩
      · have he0 := Fd_nonmu he0 (fun b => by simp [cl])
        simp only [cl, clI_zero, Ty.array.injEq, Idx.lit.injEq] at he0
        omega
      obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hwv : pw.val = .loc ad 0 := by simpa using hws
      have e : a0 = ad := by simp [addrOf, hwv] at hb; exact hb.symm
      subst e
      simp only [cl, clI_zero] at hat0
      have htb1 : tb c₁.ke.length u = true := by
        have h := htu.2.1
        rw [← htu.2.2] at h
        simp [tb] at h
        exact h
      have ho : c₁.opaqueOK u = true :=
        sub_opaqueOK hsub (peek_opaqueOK htu.1 (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu2).1)
      have hacc : accs (cl ρ η.wit 0 0 u) = some us :=
        (accs_WitL hi1.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho (lt_of_guardT htb1 hi1.2.2.2.2.1)).symm.trans
          ((accs_of_elyt (buf_lyt hlb.2.2.2.2 hbe).2).symm.trans hus)
      have hel := AtOff.elem (n := ev ρ n) hacc (show ev ρ jj < ev ρ n by omega)
        (AtOff.here (Or.inl (by simp [hacc])))
      refine ⟨_, _, hsto, ?_, hacc⟩
      simpa [offs] using AtOff_trans hat0 hel

theorem stl_ua {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stl bb i v) c')
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hu : UnitsOp g env s (.stl bb i v) pw b rel us ws) : UnitsAt η b us := by
  obtain ⟨-, rfl, rt, t1, t2, iws, vs, μ0, u0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, hbe, hnj, -,
    hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stl hp hbuf hlo hint hlt hltk _ _ _ =>
      obtain ⟨c, hsto, hat⟩ :=
        lane_slotN hi htv ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩ hea hei hbe hnj hb hlo0
      exact ⟨_, _, hsto, hat, by simp [cl, accs]⟩

theorem stlw_ua {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb wi jl v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.stlw bb wi jl v) c')
    (hi : FInv ρ η σs K cx env) (htv : TvOK cx)
    (hu : UnitsOp g env s (.stlw bb wi jl v) pw b rel us ws) : UnitsAt η b us := by
  obtain ⟨-, rfl, rt, t1, t2, t3, iws, jws, vs, μ0, u0, i0, j0, y, a0, sg0, w0, s1, old, x0, hea, hei, -, -,
    hbe, hni, -, -, hb, hlo0, rfl, -⟩ := hu
  cases hop with
  | stlw hp hbuf hlo hint hlt hltk _ _ _ _ _ =>
      obtain ⟨c, hsto, hat⟩ :=
        lane_slotW hi htv ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk⟩ hea hei hbe hni hb hlo0
      exact ⟨_, _, hsto, hat, by simp [cl, accs]⟩

/-- A target whose closed static pointee is a one-word unit. -/
theorem tgt_sw {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b)
    (hacc : accs (cl ρ η.wit 0 0 u) = some [.one]) : SWAt η b := by
  obtain ⟨c, U, hsto, hat, hFd⟩ := ptr_target hvars hp ht hea hb
  exact swAt_one hsto hat ((Fd_accs hFd).trans hacc)

/-- The mode of a word reference, from the scope's (`own`/`pub`). -/
theorem word_mode {t u' : Ty} {μ μ' : Mode} {r : Idx} {P : Proto}
    (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P)) (ht' : t = .ptr μ' u' ∨ t = .loc μ' u')
    (hμ' : μ' = .own ∨ μ' = .pub) : μ = .own ∨ μ = .pub := by
  rcases ht with rfl | rfl <;> rcases ht' with h | h <;> cases h <;> exact hμ'

theorem fetch_sw {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx c' : Cx} {x : String} {o : FetchOp} {acq rel : Bool}
    {a v : At} {t : Ty} {pw : Word} {loc : Address}
    (hop : OpT p cx x (.fetch o acq rel a v) c') (hsc : OpScope cx (.fetch o acq rel a v))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env a = some (t, [pw])) (hb : addrOf pw = some loc) : SWAt η loc := by
  cases hop with
  | fetchCell hp _ hc =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact tgt_sw hi.2.1 hp (cell_cases hc) hea hb (by simp [cl, accs])
      · exact tgt_sw hi.2.1 hp (cell_cases hc) hea hb (by simp [cl, accs])
  | fetchEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      have hμ := word_mode ht ht' hμ'
      exact tgt_sw hi.2.1 hp ht hea hb
        (by simp [cl, accs, pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep])
  | fetchShare hp hw _ _ _ hok =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      simp only [fetchOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact tgt_sw hi.2.1 hp ht hea hb (by simp [cl, accs, hok.1.1.1.1])

theorem cas_sw {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {acq rel : Bool} {w e v : At} {tn : String}
    {ok fail : Expr} {t : Ty} {pw : Word} {loc : Address}
    (hT : Typed p cx (.cas acq rel w e v tn ok fail)) (hsc : StepScope cx (.cas acq rel w e v tn ok fail))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env w = some (t, [pw])) (hb : addrOf pw = some loc) : SWAt η loc := by
  cases hT with
  | casCell hp _ hc hraw =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact tgt_sw hi.2.1 hp (cell_cases hc) hea hb (accs_cl_one hraw)
      · exact tgt_sw hi.2.1 hp (cell_cases hc) hea hb (accs_cl_one hraw)
  | casShare hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      exact tgt_sw hi.2.1 hp ht hea hb (by simp [cl, accs, hg])
  | casTake hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      exact tgt_sw hi.2.1 hp ht hea hb (by simp [cl, accs, hg])
  | casEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      rcases hsc _ hp with ⟨μ', r', P', ht', hμ'⟩ | ⟨u, -, hnw⟩
      · have hμ := word_mode ht ht' hμ'
        exact tgt_sw hi.2.1 hp ht hea hb
          (by simp [cl, accs, pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep])
      · rw [hw] at hnw; cases hnw

/-- The dispatcher over the `storeUnits`-issuing ops. -/
theorem unitsOp_ua {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {op : Op}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x op c') (hsc : OpScope cx op)
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s op pw b rel us ws) : UnitsAt η b us := by
  cases op
  case store => exact store_ua hop hsc hi hE htv hu
  case xchg => exact xchg_ua hop hsc hi hE htv hu
  case xchgAt => exact xchgAt_ua hop hi hE htv hu
  case xchgAtF => exact xchgAtF_ua hop hi hE htv hu
  case bufInit => exact bufInit_ua hop hi hE htv hu
  case stl => exact stl_ua hop hi htv hu
  case stlw => exact stlw_ua hop hi htv hu
  all_goals simp [UnitsOp] at hu

theorem unitsOp_sw {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {op : Op}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word} {j : Nat}
    (hop : OpT p cx x op c') (hsc : OpScope cx op)
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s op pw b rel us ws) (hj : TermFul.OneAt us j) : SWAt η (offs b j) :=
  swAt_of_ua (unitsOp_ua hop hsc hi hE htv hu) hj

/-- **`SWOne` holds**: every single-word write of a typed, in-scope thread
lands on word `j` of a `.one` unit of a component of its cell's type. -/
theorem SWOne_holds (p : Prog) : SWOne p := by
  intro g mem pairs th ρ η cx loc val hE hT htv hi hm hsc _ hsw
  show SWAt η loc
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, -, -, hb, -⟩
  · rw [hterm] at hT hsc
    cases hT with
    | let_ hop _ =>
        rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, rfl, -⟩ |
            ⟨o, acq, rel, a, v, t, t', pw, nw, tr, mr, rfl, hea, -, hb, -⟩
        · exact unitsOp_sw hop hsc hi hE htv hu hj
        · exact fetch_sw hop hsc hi hE htv hm hea hb
  · rw [hterm] at hT hsc
    exact cas_sw hT hsc hi hE htv hm hea hb

/-! ## (B4 §3.3) Single-word writes are not `undef`

`VR` at a laid-out type never puts `undef` at a `.one` unit (`VR_one_nundef`:
the one-word arms hold a number, a location or `null`; a sum's first word is
its tag or a reference); a store's data words are a value of the closed
pointee (`useVal_cl`), whose units are the store's.  So an `SW` value is not
`undef`, except a fetch-op's, which combines the message it read (`SW_nundef`). -/

/-- No word starting a `.one` unit of `us` in `ws` is `undef`. -/
def NUAt (us : List Acc) (ws : List Word) : Prop :=
  ∀ j w, TermFul.OneAt us j → ws[j]? = some w → w.val ≠ .undef

theorem oneAt_append : ∀ (ua ub : List Acc) {j : Nat}, TermFul.OneAt (ua ++ ub) j →
    (j < nWords ua ∧ TermFul.OneAt ua j) ∨ (nWords ua ≤ j ∧ TermFul.OneAt ub (j - nWords ua))
  | [], ub, j, h => by right; simpa [nWords] using h
  | u :: ua, ub, _, h => by
      rw [List.cons_append] at h
      have e : nWords (u :: ua) = u.size + nWords ua := by simp [nWords]
      cases h with
      | here _ => left; exact ⟨by simp only [nWords, List.map_cons, List.sum_cons, Acc.size]; omega, .here _⟩
      | @cons _ _ j' h' =>
          rcases oneAt_append ua ub h' with ⟨hl, h⟩ | ⟨hl, h⟩
          · left; exact ⟨by rw [e]; omega, .cons _ h⟩
          · right
            refine ⟨by rw [e]; omega, ?_⟩
            have e2 : j' + u.size - nWords (u :: ua) = j' - nWords ua := by rw [e]; omega
            rw [e2]; exact h

theorem oneAt_single {j : Nat} (h : TermFul.OneAt [.one] j) : j = 0 := by
  cases h with
  | here => rfl
  | cons _ h => cases h

theorem nWords_eq_one {us : List Acc} (h : nWords us = 1) : us = [.one] := by
  match us, h with
  | [], h => simp [nWords] at h
  | [.one], _ => rfl
  | .one :: u :: us, h => cases u <;> simp [nWords, Acc.size] at h <;> omega
  | .two :: us, h => simp [nWords, Acc.size] at h <;> omega

theorem nu_nil {ws : List Word} : NUAt [] ws := by
  intro j w hj _; cases hj

theorem oneAt_not_two {us : List Acc} {j : Nat} (h : TermFul.OneAt us j) : us ≠ [.two] := by
  cases h with
  | here _ => simp
  | cons u h =>
      intro e
      simp only [List.cons.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      cases h

theorem nu_two {ws : List Word} : NUAt [.two] ws :=
  fun _ _ hj _ => absurd rfl (oneAt_not_two hj)

theorem nu_single {us : List Acc} {ws : List Word} {v : WeakMem.Val} (h : ws.map (·.val) = [v])
    (hv : v ≠ .undef) : NUAt us ws := by
  intro j w _ hw
  obtain ⟨w0, rfl, e⟩ := map_singleton h
  cases j with
  | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
      subst hw
      intro hu; apply hv; rw [← e]; exact hu
  | succ j => simp at hw

theorem accs_iex_cases (t : Ty) : accs (.iex t) = accs t ∨ accs (.iex t) = some [] ∨
    accs (.iex t) = some [.two] ∨ (accs (.iex t) = some [.one] ∧ (Ty.iex t).rawWords = some 1) := by
  by_cases hc : t.countI 0 ≥ 2
  · cases hr : (Ty.iex t).rawWords with
    | none => left; simp [accs, hc, hr]
    | some k =>
        match k, hr with
        | 0, hr => right; left; simp [accs, hc, hr]
        | 1, hr => right; right; right; exact ⟨by simp [accs, hc, hr], rfl⟩
        | 2, hr => right; right; left; simp [accs, hc, hr]
        | k + 3, hr => left; simp [accs, hc, hr]
  · left; simp [accs, hc]

theorem accs_tex_cases (κ : Kind) (t : Ty) : accs (.tex κ t) = accs t ∨ accs (.tex κ t) = some [] ∨
    accs (.tex κ t) = some [.two] ∨
      (accs (.tex κ t) = some [.one] ∧ (Ty.tex κ t).rawWords = some 1) := by
  by_cases hc : t.countT 0 ≥ 2
  · cases hr : (Ty.tex κ t).rawWords with
    | none => left; simp [accs, hc, hr]
    | some k =>
        match k, hr with
        | 0, hr => right; left; simp [accs, hc, hr]
        | 1, hr => right; right; right; exact ⟨by simp [accs, hc, hr], rfl⟩
        | 2, hr => right; right; left; simp [accs, hc, hr]
        | k + 3, hr => left; simp [accs, hc, hr]
  · left; simp [accs, hc]

/-- A decoded sum's first word is its tag (a number) or a reference. -/
theorem decodeArm_head {tr : Tier} {as : List Ty} {ws : List Word} {r : Nat × List Word}
    (h : decodeArm tr as ws = some r) {w : Word} (hw : ws[0]? = some w) : w.val ≠ .undef := by
  unfold decodeArm at h
  split at h
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
    subst hw
    split at h <;> simp_all
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
    subst hw
    split at h <;> simp_all
  · cases h

/-- **`VR` puts no `undef` at a `.one` unit** of a laid-out type. -/
theorem VR_one_nundef : ∀ (T : Ty) {ρ : Nat → Nat} {η : TEnv} {ws : List Word} {us : List Acc},
    VR ρ η T (shp T) ws → accs T = some us → NUAt us ws := by
  intro T
  induction T with
  | unit | void | share _ | cap _ _ | tok _ _ | tok2 _ _ _ _ | tokE _ _ _ =>
      intro ρ η ws us _ hus
      simp only [accs, Option.some.injEq] at hus
      subst hus; exact nu_nil
  | word2 _ _ | epair _ _ =>
      intro ρ η ws us _ hus
      simp only [accs, Option.some.injEq] at hus
      subst hus; exact nu_two
  | array _ _ _ | tvar _ =>
      intro ρ η ws us _ hus
      simp [accs] at hus
  | int =>
      intro ρ η ws us hv _
      simp only [VR] at hv
      obtain ⟨n, hn⟩ := hv
      exact nu_single hn (by simp)
  | opq _ =>
      intro ρ η ws us hv _
      simp only [VR] at hv
      obtain ⟨n, hn⟩ := hv
      exact nu_single hn (by simp)
  | tid =>
      intro ρ η ws us hv _
      simp only [VR] at hv
      obtain ⟨n, c, hn, -⟩ := hv
      exact nu_single hn (by simp)
  | intS _ =>
      intro ρ η ws us hv _
      simp only [VR] at hv
      exact nu_single hv (by simp)
  | fix _ _ =>
      intro ρ η ws us hv _
      simp only [VR] at hv
      obtain ⟨-, n, hn, -⟩ := hv
      exact nu_single hn (by simp)
  | lanes _ _ =>
      intro ρ η ws us hv _
      simp only [VR] at hv
      obtain ⟨-, n, hn⟩ := hv
      exact nu_single hn (by simp)
  | code _ _ _ _ =>
      intro ρ η ws us hv _
      simp only [VR] at hv
      obtain ⟨i, d, hn, -⟩ := hv
      exact nu_single hn (by simp)
  | ptr _ _ _ =>
      intro ρ η ws us hv _
      simp only [VR] at hv
      obtain ⟨a, c, hn, -⟩ := hv
      exact nu_single hn (by simp)
  | ptrOpt _ _ _ =>
      intro ρ η ws us hv _
      simp only [VR] at hv
      rcases hv with hn | ⟨a, c, hn, -⟩
      · exact nu_single hn (by simp)
      · exact nu_single hn (by simp)
  | loc _ _ _ =>
      intro ρ η ws us hv _
      simp only [VR] at hv
      rcases hv with ⟨hn, -⟩ | ⟨a, c, U, hn, -⟩
      · exact nu_single hn (by simp)
      · exact nu_single hn (by simp)
  | word _ P =>
      intro ρ η ws us hv hus
      simp only [VR] at hv
      cases hg : P.ghost
      · obtain ⟨n, hn, -⟩ := hv.2 hg
        exact nu_single hn (by simp)
      · simp only [accs, hg, ite_true, Option.some.injEq] at hus
        subst hus; exact nu_nil
  | refine t _ ih =>
      intro ρ η ws us hv hus
      simp only [VR, shp] at hv
      simp only [accs] at hus
      exact ih hv.1 hus
  | mu t ih =>
      intro ρ η ws us hv hus
      simp only [VR, shp] at hv
      simp only [accs] at hus
      exact ih hv hus
  | iall t ih =>
      intro ρ η ws us hv hus
      simp only [VR, shp] at hv
      simp only [accs] at hus
      exact ih (hv 0) hus
  | iex t ih =>
      intro ρ η ws us hv hus
      simp only [VR, shp] at hv
      obtain ⟨n, rb, w', e, hv⟩ := hv
      simp only [Shp.iex.injEq] at e
      obtain ⟨-, rfl⟩ := e
      rcases accs_iex_cases t with e | e | e | ⟨e, hr⟩ <;> rw [e] at hus
      · exact ih hv hus
      · cases hus; exact nu_nil
      · cases hus; exact nu_two
      · cases hus
        obtain ⟨ut, hut, hn⟩ := accs_inner (rawWords_iex_inner hr)
        rw [nWords_eq_one hn] at hut
        exact ih hv hut
  | tex κ t ih =>
      intro ρ η ws us hv hus
      simp only [VR, shp] at hv
      obtain ⟨n, rb, s, e, -, -, hv⟩ := hv
      simp only [Shp.tex.injEq] at e
      obtain ⟨-, rfl⟩ := e
      rcases accs_tex_cases κ t with e | e | e | ⟨e, hr⟩ <;> rw [e] at hus
      · exact ih hv hus
      · cases hus; exact nu_nil
      · cases hus; exact nu_two
      · cases hus
        obtain ⟨ut, hut, hn⟩ := accs_inner (rawWords_tex_inner hr)
        rw [nWords_eq_one hn] at hut
        exact ih hv hut
  | prod a b iha ihb =>
      intro ρ η ws us hv hus j w hj hw
      simp only [VR, shp] at hv
      obtain ⟨ra, rb, e, hsp⟩ := hv
      simp only [Shp.prod.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      cases ha : accs a with
      | none => simp [accs, ha] at hus
      | some ua =>
      cases hb : accs b with
      | none => simp [accs, ha, hb] at hus
      | some ub =>
      simp [accs, ha, hb] at hus
      subst hus
      obtain ⟨-, hva, hvb⟩ := hsp (nWords ua) (by rw [shp_wc]; simp [wc, ha])
      rcases oneAt_append ua ub hj with ⟨hl, hj'⟩ | ⟨hl, hj'⟩
      · exact iha hva ha j w hj' (by simpa [List.getElem?_take, hl] using hw)
      · exact ihb hvb hb (j - nWords ua) w hj' (by rw [List.getElem?_drop, Nat.add_sub_cancel' hl]; exact hw)
  | sum a b _ _ =>
      intro ρ η ws us hv hus j w hj hw
      have hj0 : us = [.one] ∧ j = 0 := by
        simp only [accs] at hus
        split at hus
        · simp only [Option.some.injEq] at hus
          subst hus
          exact absurd rfl (oneAt_not_two hj)
        · simp only [Option.some.injEq] at hus
          subst hus
          exact ⟨rfl, oneAt_single hj⟩
      obtain ⟨rfl, rfl⟩ := hj0
      simp only [VR] at hv
      obtain ⟨n, Ra, Rb, -, hb | ⟨jj, pp, hdec, -⟩⟩ := hv
      · obtain ⟨-, x, s, B, hmap, -⟩ := hb
        exact nu_single (us := [.one]) hmap (by simp) 0 w (.here _) hw
      · exact decodeArm_head hdec hw

/-- A used operand at a subtype of a pointee `u`: its words are a value of
`u`'s closure (`ownStoreVal` without the runtime pointee). -/
theorem useVal_cl {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx c₁ : Cx}
    {env : Env} {v : At} {tv u rv : Ty} {ws : List Word}
    (hi : FInv ρ η σs K cx env) (hco : Coh η) (htv : TvOK cx) (hu : cx.use v = .ok (tv, c₁))
    (hsub : SubS c₁ tv u) (htb : tb cx.ke.length u = true) (hev : evalAt env v = some (rv, ws)) :
    VR (fun _ => 0) (CE η) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) ws := by
  obtain ⟨hp, hf, -, -⟩ := use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub (peek_opaqueOK htv hp)
  obtain ⟨rv', ws', hev', hvv, hlv⟩ := peek_VR hi.2.1 hp
  rw [hev] at hev'
  simp only [Option.some.injEq, Prod.mk.injEq] at hev'
  obtain ⟨rfl, rfl⟩ := hev'
  have hsat : Sat c₁.facts ρ := by rw [hf]; exact hi.1
  obtain ⟨hs, -⟩ := Lay_canon hsub hlv
  have hvu : VR ρ η u (shp (close σs u)) ws := by rw [← hs]; exact VR_sub hsat hsub _ _ hvv
  have hsigu : sig (close σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi.2.2.2.1 ρ ho (lt_of_guardT htb hi.2.2.2.2.1)
  rw [← shp_of_sig hsigu]
  exact (VR_close hco ρ u [] 0 ρ (fun _ => 0) (shp (close σs u)) ws (fun k => rfl)
    (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hvu

theorem nu_num {us : List Acc} {ws : List Word} {n : Nat} (h : ws.map (·.val) = [.num n]) : NUAt us ws :=
  nu_single h (by simp)

/-- A cell operation's data words, at the pointee's closure. -/
theorem cell_nu {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c₁ : Cx} {env : Env} {a v : At} {t u tv rt ru rv : Ty} {μ μr : Mode} {pw : Word}
    {us : List Acc} {ws : List Word}
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hp : cx.peek a = .ok t) (hc : cellOf t = some (μ, u)) (hu : cx.use v = .ok (tv, c₁))
    (hsub : SubS c₁ tv u) (hea : evalAt env a = some (rt, [pw])) (hcr : cellOf rt = some (μr, ru))
    (hus : accs ru = some us) (hev : evalAt env v = some (rv, ws)) : NUAt us ws := by
  have ho : cx.opaqueOK u = true :=
    sub_opaqueOK hsub (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu).1)
  have hacc : accs (cl ρ η.wit 0 0 u) = some us :=
    (pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hp hc ho hea hcr).symm.trans hus
  exact VR_one_nundef _ (useVal_cl hi hE.2.1 htv hu hsub (tb_cellOf (peek_tb htv hp) hc) hev) hacc

theorem store_nu {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {rl : Bool} {a v : At}
    {tok : Option At} {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.store rl a v tok) c') (hsc : OpScope cx (.store rl a v tok))
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s (.store rl a v tok) pw b rel us ws) : NUAt us ws := by
  obtain ⟨-, rt, rv, μr, ru, hea, hev, hcr, -, hus⟩ := hu
  cases hop with
  | storeOwn hp _ hc _ hu' hsub _ => exact cell_nu hi hE htv hp hc hu' hsub hea hcr hus hev
  | storePub hp _ hc _ hu' hsub _ _ => exact cell_nu hi hE htv hp hc hu' hsub hea hcr hus hev
  | storeRgn hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeCap hp _ hc => exact absurd hc (hsc _ hp _ _)
  | storeWordGive _ _ hu' _ hint | storeWordKeep _ _ hu' _ hint | storeWordHand _ _ hu' _ hint =>
      obtain ⟨ti, hpi, hti⟩ := hint
      obtain ⟨rt', w, hev', hw, -⟩ := atom_num (use_FInv hu' hi).1.2.1 hpi hti
      rw [hev] at hev'
      simp only [Option.some.injEq, Prod.mk.injEq] at hev'
      obtain ⟨-, rfl⟩ := hev'
      exact nu_single (v := w.val) (by simp) (by rw [hw]; simp)

theorem xchg_nu {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {a v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchg a v) c') (hsc : OpScope cx (.xchg a v))
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s (.xchg a v) pw b rel us ws) : NUAt us ws := by
  obtain ⟨-, rt, rv, μr, ru, hea, hev, hcr, -, hus⟩ := hu
  cases hop with
  | xchg hp hx hu' hsub _ =>
      cases hx with
      | rgn _ hc _ _ _ => exact absurd hc (hsc _ hp _ _)
      | own _ hc _ => exact cell_nu hi hE htv hp hc hu' (hsub.elim id id) hea hcr hus hev

theorem xchgAt_nu {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAt bb i v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s (.xchgAt bb i v) pw b rel us ws) : NUAt us ws := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, hea, -, hev, hbe, -, -, hus, -⟩ := hu
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, htb, -⟩ :=
        slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
      exact VR_one_nundef _ (useVal_cl hi hE.2.1 htv hu' hsub htb hev)
        ((buf_accs hi hE hp hbuf ho htb hea hbe).symm.trans hus)

theorem xchgAtF_nu {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At} {q : List Nat}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.xchgAtF bb i q v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s (.xchgAtF bb i q v) pw b rel us ws) : NUAt us ws := by
  obtain ⟨-, rt, t1, t2, iws, μ, u0, j0, a0, us0, c0, o0, hea, hei, hev, hbe, hnj, hb, hus0, hco0, hus, -⟩ :=
    hu
  cases hop with
  | xchgAtF hp hbuf hct hopu _ hint hlt hltk hu' hsub _ =>
      have ho := sub_opaqueOK hsub
        (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu').1)
      obtain ⟨rt', w, ad, cc, μr, ur, us', rti, wi, hea', hwv, hei', hnj', hbe', hus', hsto, hat, -, -,
        hsku, hsig, htbu, -⟩ := slot_view hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hopu
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      rw [hbe] at hbe'
      simp only [Option.some.injEq, Prod.mk.injEq] at hbe'
      obtain ⟨rfl, rfl⟩ := hbe'
      exact VR_one_nundef _ (useVal_cl hi hE.2.1 htv hu' hsub (TermStep.tb_compTy q _ _ hct htbu) hev)
        ((accs_WitL hi.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho
          (lt_of_guardT (TermStep.tb_compTy q _ _ hct htbu) hi.2.2.2.2.1)).symm.trans
          ((accs_of_elyt (compOff_lyt q _ _ u0 c0 o0 hct hsku (peek_buf_lyt hi.2.1 hp hbuf hea hbe).2
            hco0)).symm.trans hus))

theorem bufInit_nu {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {bb i v : At}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x (.bufInit bb i v) c')
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s (.bufInit bb i v) pw b rel us ws) : NUAt us ws := by
  obtain ⟨-, rt, t1, t2, iws, μ0, u0, j0, a0, μ', n', e', ψ, hea, -, hev, hbe, -, -, hus, -, -⟩ := hu
  cases hop with
  | bufInit hu' hbuf hint heq hlt hu2 hsub _ =>
      obtain ⟨t, u, n, k, c₁, tv, c₂, hu', hbuf, hu2, hsub⟩ :
          ∃ t u n k c₁ tv c₂, cx.use bb = .ok (t, c₁) ∧ bufOf t = some (.own, n, u, k) ∧
            c₁.use v = .ok (tv, c₂) ∧ SubS c₂ tv u :=
        ⟨_, _, _, _, _, _, _, hu', hbuf, hu2, hsub⟩
      have ht : t = .refine (.loc .own (.array n u)) (.ini k) := by
        unfold bufOf at hbuf; split at hbuf
        · simp only [Option.some.injEq, Prod.mk.injEq] at hbuf
          obtain ⟨h1, rfl, rfl, rfl⟩ := hbuf; subst h1; rfl
        · simp at hbuf
      subst ht
      have htu := use_TvOK hu' htv
      obtain ⟨hi1, rb, wsb, hea', -, hlb⟩ := use_FInv hu' hi
      rw [hea] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      have htb1 : tb c₁.ke.length u = true := by
        have h := htu.2.1
        rw [← htu.2.2] at h
        simp [tb] at h
        exact h
      have ho : c₁.opaqueOK u = true :=
        sub_opaqueOK hsub (peek_opaqueOK htu.1 (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) hu2).1)
      have hacc : accs (cl ρ η.wit 0 0 u) = some us :=
        (accs_WitL hi1.2.2.2.1 (fun k => (hE.2.1 k).1) ρ ho (lt_of_guardT htb1 hi1.2.2.2.2.1)).symm.trans
          ((accs_of_elyt (buf_lyt hlb.2.2.2.2 hbe).2).symm.trans hus)
      exact VR_one_nundef _ (useVal_cl hi1 hE.2.1 htu.1 hu2 hsub htb1 hev) hacc

/-- The dispatcher over the `storeUnits`-issuing ops: the data words are not
`undef` at `.one` units. -/
theorem unitsOp_nu {p : Prog} {g : G} {s : St} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {cx c' : Cx} {env : Env} {x : String} {op : Op}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hop : OpT p cx x op c') (hsc : OpScope cx op)
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hu : UnitsOp g env s op pw b rel us ws) : NUAt us ws := by
  cases op
  case store => exact store_nu hop hsc hi hE htv hu
  case xchg => exact xchg_nu hop hsc hi hE htv hu
  case xchgAt => exact xchgAt_nu hop hi hE htv hu
  case xchgAtF => exact xchgAtF_nu hop hi hE htv hu
  case bufInit => exact bufInit_nu hop hi hE htv hu
  case stl =>
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩ := hu
    exact nu_single rfl (by intro h; cases h)
  case stlw =>
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, rfl⟩ := hu
    exact nu_single rfl (by intro h; cases h)
  all_goals simp [UnitsOp] at hu

/-- A `cas`'s new value is not `undef`. -/
theorem cas_nu {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {acq rel : Bool} {w e v : At} {tn : String} {ok fail : Expr} {t3 : Ty} {nw : Word}
    (hT : Typed p cx (.cas acq rel w e v tn ok fail))
    (hi : FInv ρ η σs K cx env) (hE : EnvOK p η) (htv : TvOK cx)
    (hev : evalAt env v = some (t3, [nw])) : nw.val ≠ .undef := by
  cases hT with
  | casCell hp _ hc hraw _ _ hu' _ hsubv =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact VR_one_nundef _ (useVal_cl hi hE.2.1 htv hu' hsubv (tb_cellOf (peek_tb htv hp) hc) hev)
          (accs_cl_one hraw) 0 nw (.here _) rfl
      · exact VR_one_nundef _ (useVal_cl hi hE.2.1 htv hu' hsubv (tb_cellOf (peek_tb htv hp) hc) hev)
          (accs_cl_one hraw) 0 nw (.here _) rfl
  | casShare _ _ _ _ hiv | casTake _ _ _ _ hiv | casEpoch _ _ _ _ _ hiv =>
      obtain ⟨ti, hpi, hti⟩ := hiv
      obtain ⟨rt', w', hev', hw, -⟩ := atom_num hi.2.1 hpi hti
      rw [hev] at hev'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hev'
      obtain ⟨-, rfl⟩ := hev'
      rw [hw]; simp

/-- **(B4 §3.3) An `SW` value is not `undef`**, but for a fetch-op's (whose
value combines the message the RMW read: fix (a)). -/
theorem SW_nundef {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {loc : Address} {val : WeakMem.Val}
    (hE : EnvOK p η) (hT : Typed p cx th.term) (htv : TvOK cx) (hi : FInv ρ η th.σs K cx th.env)
    (hsc : StepScope cx th.term) (hsw : SW g mem pairs th loc val) :
    val ≠ .undef ∨ ∃ x o acq rel a v e, th.term = .let_ x (.fetch o acq rel a v) e := by
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, -, -, hev, -, -, -, rfl⟩
  · rw [hterm] at hT hsc
    cases hT with
    | let_ hop _ =>
        rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, hwj, -, rfl⟩ |
            ⟨o, acq, rel, a, v, t, t', pw, nw, tr, mr, rfl, -⟩
        · exact .inl (unitsOp_nu hop hsc hi hE htv hu j w hj hwj)
        · exact .inr ⟨x, o, acq, rel, a, v, e, hterm⟩
  · rw [hterm] at hT
    exact .inl (cas_nu hT hi hE htv hev)

/-! ## The value-level fact (`hG`) and the discharged corollaries -/

theorem take_one_drop {α : Type} : ∀ {l : List α} {i : Nat} {x : α}, l[i]? = some x → (l.drop i).take 1 = [x]
  | [], _, _, h => by simp at h
  | a :: l, 0, x, h => by simp at h; simp [h]
  | a :: l, i + 1, x, h => by simp only [List.getElem?_cons_succ] at h; simpa using take_one_drop h

/-- **`hG`**: a `WordOK` word at a non-ghost `.word n P` position holds a
number in a state of `P`. -/
theorem wordOK_good {E : TEnv} {T : Ty} {o : Nat} {w : Word} {n : Idx} {P : Proto}
    (h : WordOK E T o w) (hP : AtOff T o (.word n P)) (hg : P.ghost = false) :
    ∃ k, w.val = .num k ∧ InP P k := by
  obtain ⟨b, S, ws, o', w0, hseg, ⟨⟨hvr, hvd⟩, hsh⟩, hw0, hle, hbo⟩ := h
  have hlt0 : o' < ws.length := (List.getElem?_eq_some_iff.1 hw0).1
  obtain ⟨hatS, usS, hS⟩ : AtOff S o' (.word n P) ∧ ∃ us, accs S = some us := by
    rcases hseg with ⟨rfl, rfl, hT⟩ | ⟨N, us, j, rfl, hus, hj, rfl⟩
    · subst hbo
      exact ⟨by simpa using hP, Option.ne_none_iff_exists'.1 hT⟩
    · refine ⟨?_, us, hus⟩
      rcases AtOff_arr_elem hP rfl with h | ⟨us', j', o'', hus', hj', ho, hat⟩
      · cases h
      · rw [hus] at hus'
        cases hus'
        have hlt1 : o' < nWords us := hsh us hus ▸ hlt0
        have hlt2 : o'' + nWords [Acc.one] ≤ nWords us := AtOff_bound hat hus (accs_word hg)
        have hlt2' : o'' < nWords us := by have h1 : nWords [Acc.one] = 1 := rfl; omega
        have e : o' + j * nWords us = o'' + j' * nWords us := by omega
        have e2 := congrArg (· % nWords us) e
        simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2'] at e2
        exact e2 ▸ hat
  obtain ⟨nn, hwcU, -, hvrU, -⟩ :=
    VR_at E.unsee hatS hvr hvd (by simp [wc, hS, hsh usS hS])
  have hnn : nn = 1 := by simp [wc, accs, hg, nWords, Acc.size] at hwcU; omega
  subst hnn
  rw [take_one_drop hw0] at hvrU
  simp only [VR] at hvrU
  obtain ⟨k, hk, hin⟩ := hvrU.2 hg
  refine ⟨k, ?_, hin⟩
  rw [← hle.1]
  simpa using hk

/-- `PWF` from the invariant: pair starts and promises are messages
(`MemOKP`, `MemInv_promLt`) and promises are not pair starts (`MemInv_nopair`). -/
theorem pwf_of_inv {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c : Cfg}
    (h0 : InvAt p k arch i c) : PWF c i := by
  obtain ⟨th, hth, E, -, hm, -⟩ := h0
  refine ⟨fun q hq => Nat.lt_of_succ_lt (hm.1.2.2 q hq), fun t ht => ?_⟩
  rw [promsOf_some hth] at ht
  exact ⟨MemInv_promLt hm t ht, MemInv_nopair hm t ht⟩

/-- **`certified_noPairProm`, discharged**: only `StepPresW`, the scope, the
invariant and certification remain. -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem certified_noPairPromS {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    (hpres : StepPresW p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPub p k arch i c0)
    (h0 : InvAt p k arch i c) (hnb : NoBoxedCur p k arch i c) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m) :
    ∃ c1 th1 E1 cl, Solo p k arch i c c1 ∧ Certified p k arch c1 i ∧ c1.ths[i]? = some th1 ∧
      ThInvE p E1 th1 ∧ MemInv (gOf p k arch c1 i) E1 (stOf c1.mem c1.pairs th1) ∧
      E1.sto m.loc.label = some cl ∧
      ∀ o2 r P, AtOff cl.ty o2 (.word2 r P) → m.loc.offset ≠ o2 ∧ m.loc.offset ≠ o2 + 1 :=
  certified_noPairPromT hpres (SWOne_holds p) hsc hvI hwin h0 hnb hc (pwf_of_inv h0) ht hm

/-- **`certified_promWord`, discharged**: an outstanding promise at a
`.word n P` position of its cell's type (in the environment after its fulfil)
is `undef`, or, if `P` is not ghost, a number in a state of `P`. -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem certified_promWordS {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    (hpres : StepPresW p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPub p k arch i c0)
    (h0 : InvAt p k arch i c) (hnb : NoBoxedCur p k arch i c) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m) :
    ∃ c2 th2 E2, Solo p k arch i c c2 ∧ Certified p k arch c2 i ∧ c2.ths[i]? = some th2 ∧
      ThInvE p E2 th2 ∧ MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      ∀ cl n P, E2.sto m.loc.label = some cl → AtOff cl.ty m.loc.offset (.word n P) →
        m.val = .undef ∨ (P.ghost = false → ∃ k, m.val = .num k ∧ InP P k) :=
  certified_promWordT (fun _ P v => P.ghost = false → ∃ k, v = .num k ∧ InP P k)
    (fun _ _ _ _ _ _ h hP hg => wordOK_good h hP hg) hpres hsc hvI hwin h0 hnb hc (pwf_of_inv h0) ht hm

/-- `certified_noPairPromS` from `ProgT`. -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem certified_noPairPromP {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    [ProgRetIall p] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPub p k arch i c0)
    (h0 : InvAt p k arch i c) (hnb : NoBoxedCur p k arch i c) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ c1 th1 E1 cl, Solo p k arch i c c1 ∧ Certified p k arch c1 i ∧ c1.ths[i]? = some th1 ∧
      ThInvE p E1 th1 ∧ MemInv (gOf p k arch c1 i) E1 (stOf c1.mem c1.pairs th1) ∧
      E1.sto m.loc.label = some cl ∧
      ∀ o2 r P, AtOff cl.ty o2 (.word2 r P) → m.loc.offset ≠ o2 ∧ m.loc.offset ≠ o2 + 1 :=
  certified_noPairPromS (stepPresW_of hP hPS hSub hSig) hsc hvI hwin h0 hnb hc ht hm

/-- `certified_promWordS` from `ProgT`. -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem certified_promWordP {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    [ProgRetIall p] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPub p k arch i c0)
    (h0 : InvAt p k arch i c) (hnb : NoBoxedCur p k arch i c) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ c2 th2 E2, Solo p k arch i c c2 ∧ Certified p k arch c2 i ∧ c2.ths[i]? = some th2 ∧
      ThInvE p E2 th2 ∧ MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      ∀ cl n P, E2.sto m.loc.label = some cl → AtOff cl.ty m.loc.offset (.word n P) →
        m.val = .undef ∨ (P.ghost = false → ∃ k, m.val = .num k ∧ InP P k) :=
  certified_promWordS (stepPresW_of hP hPS hSub hSig) hsc hvI hwin h0 hnb hc ht hm

/-! ## (B4) Frontier bounds along the typed run

A thread step only raises `vWr`, memory's size and the allocation count, and an
allocation raises `vWr` to the old memory size less one (`WrUp`).  So a
frontier set during a run (`publish`: the current `vWr`) is at least the start
`vWr`, and at a label allocated during the run at least the start size less
one; a box created during the run has its frontier there too (`EFoot`).  The
framework mirrors `TermStepper.VMono`. -/

/-- (B4) A step raises `vWr`, memory's size and the allocation count, and an
allocation raises `vWr` to the old memory size less one. -/
def WrUp (s s' : St) : Prop :=
  s.vs.vWr ≤ s'.vs.vWr ∧ s.mem.size ≤ s'.mem.size ∧ s.nalloc ≤ s'.nalloc ∧
    (s.nalloc < s'.nalloc → s.mem.size ≤ s'.vs.vWr + 1)

@[simp] theorem WrUp.refl' (s : St) : WrUp s s :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _)⟩

theorem WrUp.trans {s1 s2 s3 : St} (a : WrUp s1 s2) (b : WrUp s2 s3) : WrUp s1 s3 := by
  refine ⟨Nat.le_trans a.1 b.1, Nat.le_trans a.2.1 b.2.1, Nat.le_trans a.2.2.1 b.2.2.1, fun h => ?_⟩
  by_cases h1 : s1.nalloc < s2.nalloc
  · exact Nat.le_trans (a.2.2.2 h1) (Nat.add_le_add_right b.1 1)
  · have h2 : s2.nalloc < s3.nalloc := by have := a.2.2.1; omega
    exact Nat.le_trans a.2.1 (b.2.2.2 h2)

theorem WrUp.of {s s' : St} (h1 : s.vs.vWr ≤ s'.vs.vWr) (h2 : MemExt s.mem s'.mem)
    (h3 : s'.nalloc = s.nalloc) : WrUp s s' :=
  ⟨h1, memExt_size h2, by rw [h3]; exact Nat.le_refl _,
    fun h => by rw [h3] at h; exact absurd h (Nat.lt_irrefl _)⟩

@[simp] theorem fenceS_wrUp (s : St) (f : WeakMem.Fence) : WrUp s (fenceS s f) := by
  cases f <;> exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _)⟩

theorem loadUnits_nallocT {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us k s →
      r.1.nalloc = s.nalloc
  | [], _, s, r, hr => by simp only [loadUnits, List.mem_singleton] at hr; subst hr; rfl
  | .one :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, -, ⟨s', ws⟩, hmem, rfl⟩ := hr
      have := loadUnits_nallocT us (k + 1) _ (s', ws) hmem; exact this
  | .two :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, -, ⟨s', ws⟩, hmem, rfl⟩ := hr
      have := loadUnits_nallocT us (k + 2) _ (s', ws) hmem; exact this

theorem loadUnits_wrUp (arch : Arch) (pw : Word) (a : Address) (acq : Bool) (us : List Acc) (k : Nat) (s : St)
    {s' : St} {ws : List Word} (h : (s', ws) ∈ loadUnits arch pw a acq us k s) : WrUp s s' := by
  have e1 := (loadUnits_keep us k s (s', ws) h).1
  have e2 := loadUnits_vWr us k s (s', ws) h
  have e3 := loadUnits_nallocT us k s (s', ws) h
  simp only at e1 e2 e3
  exact WrUp.of (Nat.le_of_eq e2.symm) (by rw [e1]; exact MemExt.rfl' _) e3

theorem storeUnits_nallocT {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      s'.nalloc = s.nalloc
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; rfl
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, -, hs⟩ := hs
      have := storeUnits_nallocT us ws (i + 1) _ s' hs; exact this
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel = R at hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at hs
      have := storeUnits_nallocT us ws (i + 2) _ s' hs; exact this
  | .one :: _, [], _, _, _, hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, hs => by simp [storeUnits] at hs

theorem storeUnits_wrUp (k : Promises.Knobs) (arch : Arch) (pw : Word) (a : Address) (rel : Bool)
    (us : List Acc) (ws : List Word) (i : Nat) (s : St) {s' : St}
    (h : s' ∈ storeUnits k arch pw a rel us ws i s) : WrUp s s' :=
  WrUp.of (storeUnits_vWr_mono us ws i s s' h) (storeUnits_grow us ws i s s' h).1
    (storeUnits_nallocT us ws i s s' h)

theorem alloc_wrUp {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s s' : St} {pw : Word} (h : (s', pw) ∈ alloc k arch lbl us ws s) : WrUp s s' := by
  obtain ⟨s1, hs, -, -, -, e5, -, e7, -, -, esz, -⟩ := alloc_unf h
  have h1 := storeUnits_vWr_mono us ws 0 s1 s' hs
  have h2 := memExt_size (storeUnits_grow us ws 0 s1 s' hs).1
  have h3 := storeUnits_nallocT us ws 0 s1 s' hs
  have h4 := alloc_size_fr h
  simp only at h1 h2 h3 h4
  rw [e7] at h1
  have h5 : s.vs.vWr ≤ s'.vs.vWr := Nat.le_trans (Nat.le_max_left _ _) h1
  exact ⟨h5, by omega, by omega, fun _ => h4⟩

@[simp] theorem allocBuf_wrUp (lbl : AllocLabel) (n : Nat) (zero : Option (List WeakMem.Val)) (s : St) :
    WrUp s (allocBuf lbl n zero s).1 := by
  have h2 := memExt_size (allocBuf_grow (lbl := lbl) (n := n) (zero := zero) (s := s)).1
  refine ⟨Nat.le_max_left _ _, h2, Nat.le_succ _, fun _ => ?_⟩
  show s.mem.size ≤ max s.vs.vWr (s.mem.size + n - 1) + 1
  have := Nat.le_max_right s.vs.vWr (s.mem.size + n - 1)
  omega

theorem lockFence_vWrT (arch : Arch) (x : Promises.Thread) :
    (if arch = .tso then Promises.stepFence x .sy else x).vs.vWr = x.vs.vWr := by
  split
  · rfl
  · rfl

theorem stepRmw_vWrUp_at {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel) :
    th.vs.vWr ≤ th'.vs.vWr := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, -, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [lockFence_vWrT]; exact Nat.le_refl _
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [lockFence_vWrT]; exact Nat.le_max_left _ _
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨-, rfl, rfl⟩ := hf
          rw [lockFence_vWrT]; exact Nat.le_max_left _ _

theorem stepRmw_vWrUp {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) :
    th.vs.vWr ≤ th'.vs.vWr := by
  have hx := stepRmw_vWrUp_at (th := if arch = .tso then Promises.stepFence th .sy else th) h
  rwa [lockFence_vWrT] at hx

theorem stepRmwPair_vWrUp_at {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈ Promises.stepRmwPairAt arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel) :
    th.vs.vWr ≤ th'.vs.vWr := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, _, t1, _, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [lockFence_vWrT]; exact Nat.le_refl _
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [lockFence_vWrT]; exact Nat.le_max_left _ _
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, _, hf⟩ := h
    split at hf
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨-, rfl, rfl, rfl⟩ := hf
      rw [lockFence_vWrT]; exact Nat.le_max_left _ _
    · cases hf

theorem stepRmwPair_vWrUp {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈ Promises.stepRmwPair arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel) :
    th.vs.vWr ≤ th'.vs.vWr := by
  have hx := stepRmwPair_vWrUp_at (th := if arch = .tso then Promises.stepFence th .sy else th) h
  rwa [lockFence_vWrT] at hx

theorem rmw_wrUp {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts} {s s' : St}
    {r0 r1 r2 : Word} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs (mth s r0 r1 r2) dst a cmp newv deps acq rel)
    (hm : s'.mem = mem') (hv : s'.vs = th'.vs) (hs : s.mem = mem) (hn : s'.nalloc = s.nalloc) : WrUp s s' :=
  WrUp.of (by rw [hv]; exact stepRmw_vWrUp h)
    (by rw [hm, hs]; exact stepRmw_memExt (x := (mem', th')) h) hn

theorem rmwPair_wrUp {arch : Arch} {mem : Memory} {pairs : List Ts} {s s' : St}
    {r0 r1 r2 : Word} {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs (mth s r0 r1 r2) d0 d1 a c0 c1 n0 n1 deps acq rel)
    (hm : s'.mem = mem') (hv : s'.vs = th'.vs) (hs : s.mem = mem) (hn : s'.nalloc = s.nalloc) : WrUp s s' :=
  WrUp.of (by rw [hv]; exact stepRmwPair_vWrUp h)
    (by rw [hm, hs]; exact (stepRmwPair_grow (x := (mem', pairs', th')) h).1) hn

macro "flatWU" : tactic => `(tactic|
  simp (config := {contextual := true}) only [ol, Option.mem_toList,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, List.mem_map, List.mem_flatMap,
    List.mem_filterMap, List.mem_singleton, List.not_mem_nil, Prod.exists,
    Prod.mk.injEq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, forall_eq',
    Option.some.injEq, Option.pure_def, Option.bind_some, reduceCtorEq, false_implies,
    implies_true, WrUp.refl', fenceS_wrUp, allocBuf_wrUp, Option.toList_none, Option.toList_some,
    Option.bind_none, Option.map_none, Option.map_some, Option.mem_def,
    Option.bind_eq_bind, Option.map_eq_map, Option.ite_none_left_eq_some, Option.ite_none_right_eq_some])

macro "closeWU" : tactic => `(tactic| first
    | done
    | exact WrUp.refl' _
    | exact fenceS_wrUp _ _
    | exact allocBuf_wrUp _ _ _ _
    | exact loadUnits_wrUp _ _ _ _ _ _ _ (by assumption)
    | exact storeUnits_wrUp _ _ _ _ _ _ _ _ _ (by assumption)
    | exact alloc_wrUp (by assumption)
    | exact WrUp.trans (loadUnits_wrUp _ _ _ _ _ _ _ (by assumption))
        (storeUnits_wrUp _ _ _ _ _ _ _ _ _ (by assumption))
    | exact WrUp.trans (alloc_wrUp (by assumption)) (fenceS_wrUp _ _)
    | exact WrUp.trans (loadUnits_wrUp _ _ _ _ _ _ _ (by assumption))
        (loadUnits_wrUp _ _ _ _ _ _ _ (by assumption)))

macro "crushWU1" : tactic => `(tactic| (
  repeat' split
  all_goals (try flatWU)
  all_goals (try intros)
  all_goals (try subst_vars)
  all_goals (try closeWU)))

macro "crushWU" : tactic => `(tactic| (
  intro r hin
  revert hin
  crushWU1
  all_goals (try (rename_i hh; revert hh; crushWU1))
  all_goals (try (rename_i hh; revert hh; crushWU1))))

theorem projM_wrUp (g : G) (s : St) (t : Ty) (ws : List Word) :
    ∀ r ∈ projM g s t ws, WrUp s r.1 := by
  unfold projM
  crushWU

theorem injM_wrUp (g : G) (s : St) (t : Ty) (j : Nat) (p : List Word) :
    ∀ r ∈ injM g s t j p, WrUp s r.1 := by
  unfold injM
  crushWU

theorem evalOp_wrUp (g : G) (env : Env) (σs : List Ty) (s : St) (op : Op) :
    ∀ r ∈ evalOp g env σs s op, WrUp s r.1 := by
  cases op <;> simp only [evalOp]
  all_goals crushWU
  all_goals first
    | exact WrUp.trans (projM_wrUp _ _ _ _ _ (by assumption)) (injM_wrUp _ _ _ _ _ _ (by assumption))
    | exact rmw_wrUp (by assumption) (by rfl) (by rfl) (by rfl) (by rfl)

theorem enter_nallocT {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At}
    (h : enter g th f ts a = some th') : th'.vs = th.vs ∧ th'.nalloc = th.nalloc := by
  unfold enter at h
  simp only [bind, Option.bind] at h
  repeat' (first | (split at h) | (dsimp only at h; split at h))
  all_goals first
    | (simp at h; done)
    | (simp only [pure, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩)

theorem enter_wrUp {g : G} {mem : Memory} {pairs : List Ts} {th th0 th' : TTh} {f : String}
    {ts : List Ty} {a : At} (h : enter g th0 f ts a = some th') (hv : th0.vs = th.vs)
    (hn : th0.nalloc = th.nalloc) : WrUp (stOf mem pairs th) (stOf mem pairs th') := by
  obtain ⟨e1, e2⟩ := enter_nallocT h
  exact WrUp.of (show th.vs.vWr ≤ th'.vs.vWr by rw [e1, hv]; exact Nat.le_refl _) (MemExt.rfl' _)
    (show th'.nalloc = th.nalloc by rw [e2, hn])

/-- (B4) A thread step raises `vWr`, memory's size and the allocation count;
an allocation raises `vWr` to the old size less one. -/
theorem tstep_wrUp (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) :
    ∀ r ∈ tstep g mem pairs th, WrUp (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  unfold tstep
  crushWU
  all_goals first
    | exact evalOp_wrUp _ _ _ _ _ _ (by assumption)
    | exact WrUp.trans (projM_wrUp _ _ _ _ _ (by assumption)) (injM_wrUp _ _ _ _ _ _ (by assumption))
    | exact enter_wrUp (by assumption) (by rfl) (by rfl)
    | exact rmw_wrUp (by assumption) (by rfl) (by rfl) (by rfl) (by rfl)
    | exact rmwPair_wrUp (by assumption) (by rfl) (by rfl) (by rfl) (by rfl)

/-- (B4) **The frontier bound** of an environment `E` reached from `E0` along a
typed run started at memory size `n0` and `vWr` `v0`: (i) a cell's frontier set
during the run is at least `v0`; (ii) at a label allocated during the run, at
least `n0 - 1`; (iii) a box created during the run has its frontier at least
`n0 - 1`. -/
def FrBound (E0 : TEnv) (n0 v0 : Nat) (E : TEnv) : Prop :=
  (∀ l c f, E0.pfr l = none → E.sto l = some c → E.pfr l = some f → v0 ≤ f) ∧
  (∀ l c f, E0.sto l = none → E.sto l = some c → E.pfr l = some f → n0 ≤ f + 1) ∧
  (∀ l B, E0.box l = none → E.box l = some B → n0 ≤ B.fr + 1) ∧
  (E.tid = E0.tid ∧ ∀ l c, E0.sto l = some c → E.sto l = some c ∧
    (c.owner ≠ some E0.tid → E.ini l = E0.ini l ∧ E.pfr l = E0.pfr l)) ∧
  (∀ l B, E0.box l = some B → E0.sto l = none → E.box l = some B ∧ E.sto l = none ∧ E.pfr l = E0.pfr l)

/-- (B4) The run-state half of the frontier bound: `vWr` and memory's size
only grew, and once a label was allocated during the run `vWr` is at least
`n0 - 1`. -/
def FrRun (E0 : TEnv) (n0 v0 : Nat) (E : TEnv) (s : St) : Prop :=
  v0 ≤ s.vs.vWr ∧ n0 ≤ s.mem.size ∧ ∀ l c, E0.sto l = none → E.sto l = some c → n0 ≤ s.vs.vWr + 1

theorem FrBound_refl (E : TEnv) (n0 v0 : Nat) : FrBound E n0 v0 E :=
  ⟨fun _ _ _ h0 _ h => absurd (h0.symm.trans h) (fun e => by cases e), fun _ _ _ h0 h _ => absurd (h0.symm.trans h) (fun e => by cases e),
    fun _ _ h0 h => absurd (h0.symm.trans h) (fun e => by cases e), ⟨rfl, fun _ _ h => ⟨h, fun _ => ⟨rfl, rfl⟩⟩⟩,
    fun _ _ h hs => ⟨h, hs, rfl⟩⟩

/-- (B4) **`FrBound`/`FrRun` along a thread step** (its footprint `Foot` and
`tstep_wrUp`): a `publish` sets the frontier to the current `vWr`; a fresh cell
has no frontier; a fresh box's frontier is at least the old size less one. -/
theorem FrBound_foot {g : G} {E0 E E' : TEnv} {n0 v0 : Nat} {s s' : St} (hF : Foot g E E' s s')
    (hw : WrUp s s') (hb : FrBound E0 n0 v0 E) (hr : FrRun E0 n0 v0 E s) :
    FrBound E0 n0 v0 E' ∧ FrRun E0 n0 v0 E' s' := by
  obtain ⟨⟨-, htd, hst, hbx, hin, hpf, -⟩, hbl⟩ := hF
  have hfr : ∀ l, FreshIn g s.nalloc s'.nalloc l → s.nalloc < s'.nalloc := fun l ⟨j, h1, h2, _⟩ => by omega
  refine ⟨⟨fun l c f h0 hc hf => ?_, fun l c f h0 hc hf => ?_, fun l B h0 hB => ?_,
    ⟨htd.trans hb.2.2.2.1.1, fun l c h0 => ?_⟩, fun l B h0 hs0 => ?_⟩,
    Nat.le_trans hr.1 hw.1, Nat.le_trans hr.2.1 hw.2.1, fun l c h0 hc => ?_⟩
  · rcases hpf l with e | ⟨-, F, e, hvF, -⟩ | ⟨-, -, e⟩
    · rw [e] at hf
      rcases hst l with e' | ⟨hl, -⟩
      · rw [e'] at hc; exact hb.1 l c f h0 hc hf
      · rw [(hbl l hl).2.2.2] at hf; cases hf
    · rw [e] at hf; cases hf; exact Nat.le_trans hr.1 hvF
    · rw [e] at hc; cases hc
  · rcases hpf l with e | ⟨-, F, e, hvF, -, ⟨c1, hc1, -⟩, -⟩ | ⟨-, -, e⟩
    · rw [e] at hf
      rcases hst l with e' | ⟨hl, -⟩
      · rw [e'] at hc; exact hb.2.1 l c f h0 hc hf
      · rw [(hbl l hl).2.2.2] at hf; cases hf
    · rw [e] at hf; cases hf; exact Nat.le_trans (hr.2.2 l c1 h0 hc1) (Nat.add_le_add_right hvF 1)
    · rw [e] at hc; cases hc
  · rcases hbx l with e | ⟨-, B', e, -, hB', -⟩
    · rw [e] at hB; exact hb.2.2.1 l B h0 hB
    · rw [e] at hB; cases hB; exact Nat.le_trans hr.2.1 hB'
  · obtain ⟨hc, hn⟩ := hb.2.2.2.1.2 l c h0
    have hnf : ¬ FreshIn g s.nalloc s'.nalloc l := fun hl => by rw [(hbl l hl).1] at hc; cases hc
    have hs' : E'.sto l = some c := by
      rcases hst l with e | ⟨hl, -⟩
      · rw [e]; exact hc
      · exact absurd hl hnf
    refine ⟨hs', fun ho => ?_⟩
    obtain ⟨hi0, hp0⟩ := hn ho
    have hno : ¬ OwnAt E l := fun ⟨c1, hc1, ho1⟩ => by
      rw [hc] at hc1; cases hc1; rw [hb.2.2.2.1.1] at ho1; exact ho ho1
    refine ⟨?_, ?_⟩
    · rcases (hin l).2 with e | hl | ⟨ho', -⟩
      · rw [e]; exact hi0
      · exact absurd hl hnf
      · exact absurd ho' hno
    · rcases hpf l with e | ⟨-, F, -, -, -, ho', -⟩ | ⟨hl, -⟩
      · rw [e]; exact hp0
      · exact absurd ho' hno
      · exact absurd hl hnf
  · obtain ⟨hB, hs, hp⟩ := hb.2.2.2.2 l B h0 hs0
    have hnf : ¬ FreshIn g s.nalloc s'.nalloc l := fun hl => by rw [(hbl l hl).2.1] at hB; cases hB
    refine ⟨?_, ?_, ?_⟩
    · rcases hbx l with e | ⟨hl, -⟩
      · rw [e]; exact hB
      · exact absurd hl hnf
    · rcases hst l with e | ⟨hl, -⟩
      · rw [e]; exact hs
      · exact absurd hl hnf
    · rcases hpf l with e | ⟨-, F, -, -, -, ⟨c1, hc1, -⟩, -⟩ | ⟨hl, -⟩
      · rw [e]; exact hp
      · rw [hs] at hc1; cases hc1
      · exact absurd hl hnf
  · rcases hst l with e | ⟨hl, -⟩
    · rw [e] at hc; exact Nat.le_trans (hr.2.2 l c h0 hc) (Nat.add_le_add_right hw.1 1)
    · exact Nat.le_trans hr.2.1 (hw.2.2.2 (hfr l hl))

/-- (iniop) The run's count locality at the start cells in `Z` with a start frontier: the counts
are unchanged and the frontier stays set. -/
def IniLoc (Z : AllocLabel → Prop) (E0 E : TEnv) : Prop :=
  ∀ a c f, Z a → E0.sto a = some c → E0.pfr a = some f →
    E.ini a = E0.ini a ∧ E.rini a = E0.rini a ∧ ∃ f', E.pfr a = some f'

theorem IniLoc_refl (Z : AllocLabel → Prop) (E : TEnv) : IniLoc Z E E :=
  fun _ _ f _ _ hf => ⟨rfl, rfl, f, hf⟩

/-- (iniop) **`IniLoc` along a thread step** whose ghost `g.zf` covers `Z` (`EFoot.iniFixZ`), beside
`FrBound` (which keeps the start cells; `Foot` rules out fresh ones). -/
theorem IniLoc_foot {Z : AllocLabel → Prop} {g : G} {E0 E E' : TEnv} {n0 v0 : Nat} {s s' : St}
    (hF : Foot g E E' s s') (hZ : ∀ l, Z l → g.zf l) (hb : FrBound E0 n0 v0 E) (hI : IniLoc Z E0 E) :
    IniLoc Z E0 E' := by
  intro a c f hz hc0 hf0
  obtain ⟨hi, hr, f1, hf1⟩ := hI a c f hz hc0 hf0
  have hc : E.sto a = some c := (hb.2.2.2.1.2 a c hc0).1
  have hnf : ¬ FreshIn g s.nalloc s'.nalloc a := fun hl => by
    rw [(hF.2 a hl).1] at hc; cases hc
  obtain ⟨hi', hr'⟩ := hF.1.iniFixZ a c f1 (hZ a hz) hnf hc hf1
  refine ⟨hi'.trans hi, hr'.trans hr, ?_⟩
  rcases hF.1.2.2.2.2.2.1 a with e | ⟨-, F, e, -⟩ | ⟨hl, -⟩
  · exact ⟨f1, e.trans hf1⟩
  · exact ⟨F, e⟩
  · exact absurd hl hnf

/-- (G-b) The run's held counts: given `rini ≤ ini` at the start, `rini ≤ ini` holds, every unit
of a start own buffer counted by `E.ini` beyond `E0.ini` has a write index `τ ≤ v` with `H l o τ`, and
(IniCap) a start cell's count is at most its start count or its real count, and (RiniArr) at a start
cell that is not a buffer the real count has not risen. -/
def IniHeld (H : AllocLabel → Nat → Ts → Prop) (E0 E : TEnv) (v : Nat) : Prop :=
  (∀ l, E0.rini l ≤ E0.ini l) → (∀ l, E.rini l ≤ E.ini l) ∧
    (∀ l c, E0.sto l = some c → c.owner = some E0.tid → ∀ N e us, c.ty = .array (.lit N) e → accs e = some us →
      ∀ o, o < E.ini l * nWords us → ¬ o < E0.ini l * nWords us → ∃ τ, τ ≤ v ∧ H l o τ) ∧
    (∀ l c, E0.sto l = some c → E.ini l ≤ max (E0.ini l) (E.rini l)) ∧
    ∀ l c, E0.sto l = some c → (¬ ∃ N e us, c.ty = .array (.lit N) e ∧ accs e = some us) →
      E.rini l ≤ E0.rini l

theorem IniHeld_refl (H : AllocLabel → Nat → Ts → Prop) (E : TEnv) (v : Nat) : IniHeld H E E v :=
  fun h => ⟨h, fun _ _ _ _ _ _ _ _ _ _ h1 h2 => absurd h1 h2, fun _ _ _ => Nat.le_max_left _ _,
    fun _ _ _ _ => Nat.le_refl _⟩

/-- (G-b) **`IniHeld` along a thread step**: a newly counted unit is a newly real one (`EFoot`'s
`ini ≤ max ini rini′`, `rini ≤ ini` before), written at `τ ≤ vWr′` (`RiniW`): a new message or a
promise at that unit, which `hW` makes `H`; (RiniArr) at a start non-buffer cell, never fresh, the
footprint's `riniArr` keeps the real count. -/
theorem IniHeld_foot {H : AllocLabel → Nat → Ts → Prop} {g : G} {E0 E E' : TEnv} {n0 v0 : Nat} {s s' : St}
    (hF : Foot g E E' s s') (hv : s.vs.vWr ≤ s'.vs.vWr) (hb : FrBound E0 n0 v0 E)
    (hW : ∀ l o τ, (s.mem.size ≤ τ ∨ (τ ∈ s.promises ∧ ∃ m, s.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) → H l o τ)
    (hI : IniHeld H E0 E s.vs.vWr) : IniHeld H E0 E' s'.vs.vWr := by
  intro hr0
  obtain ⟨hrl, hu, hcap, hna⟩ := hI hr0
  refine ⟨hF.1.2.2.2.2.2.2.2.2.2.2.1 hrl, fun l c hc0 ho N e us hT hus o ho1 ho2 => ?_, fun l c hc0 => ?_,
    fun l c hc0 hnb => ?_⟩
  rotate_left
  · have hc : E.sto l = some c := (hb.2.2.2.1.2 l c hc0).1
    have hnf : ¬ FreshIn g s.nalloc s'.nalloc l := fun hl => by rw [(hF.2 l hl).1] at hc; cases hc
    have hrm : E.rini l ≤ E'.rini l := hF.1.2.2.2.2.2.2.2.2.2.1 l
    have h0 := hcap l c hc0
    rcases (hF.1.2.2.2.2.1 l).2 with e1 | hl | ⟨-, hmx, -⟩
    · rw [e1]; exact Nat.le_trans h0 (Nat.max_le.2 ⟨Nat.le_max_left _ _, Nat.le_trans hrm (Nat.le_max_right _ _)⟩)
    · exact absurd hl hnf
    · refine Nat.le_trans hmx (Nat.max_le.2 ⟨Nat.le_trans h0 ?_, Nat.le_max_right _ _⟩)
      exact Nat.max_le.2 ⟨Nat.le_max_left _ _, Nat.le_trans hrm (Nat.le_max_right _ _)⟩
  · have hc : E.sto l = some c := (hb.2.2.2.1.2 l c hc0).1
    have hnf : ¬ FreshIn g s.nalloc s'.nalloc l := fun hl => by rw [(hF.2 l hl).1] at hc; cases hc
    refine Nat.le_trans ?_ (hna l c hc0 hnb)
    rcases Nat.lt_or_ge (E.rini l) (E'.rini l) with hlt | hge
    · rcases hF.1.riniArr l c hc hlt with hl | hab
      · exact absurd hl hnf
      · exact absurd hab hnb
    · exact hge
  have hc : E.sto l = some c := (hb.2.2.2.1.2 l c hc0).1
  by_cases hlt : o < E.ini l * nWords us
  · obtain ⟨τ, h1, h2⟩ := hu l c hc0 ho N e us hT hus o hlt ho2
    exact ⟨τ, Nat.le_trans h1 hv, h2⟩
  · have hnf : ¬ FreshIn g s.nalloc s'.nalloc l := fun hl => by rw [(hF.2 l hl).1] at hc; cases hc
    rcases (hF.1.2.2.2.2.1 l).2 with e1 | hl | ⟨-, hmx, -⟩
    · rw [e1] at ho1; exact absurd ho1 hlt
    · exact absurd hl hnf
    · have hge : E.rini l * nWords us ≤ o :=
        Nat.le_trans (Nat.mul_le_mul_right _ (hrl l)) (Nat.le_of_not_lt hlt)
      have hlt' : o < E'.rini l * nWords us := by
        rcases Nat.le_total (E.ini l) (E'.rini l) with h | h
        · exact Nat.lt_of_lt_of_le ho1 (Nat.mul_le_mul_right _ (Nat.le_trans hmx (Nat.max_le.2 ⟨h, Nat.le_refl _⟩)))
        · exact absurd (Nat.lt_of_lt_of_le ho1
            (Nat.mul_le_mul_right _ (Nat.le_trans hmx (Nat.max_le.2 ⟨Nat.le_refl _, h⟩)))) hlt
      obtain ⟨τ, h1, h2⟩ := hF.1.riniW l c hc N e us hT hus o hge hlt'
      exact ⟨τ, h1, hW l o τ h2⟩

/-- (G-b) The write witnesses of a run from the plant configuration (memory `mem0`, promises `P0`):
a message new since the plant, or a promise outstanding at the plant at that unit. -/
def WitP (mem0 : Memory) (P0 : List Ts) (l : AllocLabel) (o : Nat) (τ : Ts) : Prop :=
  mem0.size ≤ τ ∨ (τ ∈ P0 ∧ ∃ m, mem0[τ]? = some m ∧ m.loc = ⟨l, o⟩)

/-- (G-b) A run's write witnesses are `WitP` of the plant (`WinInv`), the run-wide `hHr`. -/
theorem witP_run {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {cP c : Cfg} {thP : TTh}
    (hthP : cP.ths[i]? = some thP) (hpl : ∀ t, t ∈ thP.promises → t < cP.mem.size) (hW : WinInv cP i c) :
    ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) →
        WitP cP.mem thP.promises l o τ := by
  intro c1 h1 _ th1 hth1 l o τ hτ
  obtain ⟨thW0, thW, hW0P, hW0t, -, hme, hpr, -, -⟩ := solo_winInv h1 hW
  rw [hthP] at hW0P; cases hW0P
  rw [hth1] at hW0t; cases hW0t
  have hsz := TermFul.memExt_size hme
  rcases hτ with h | ⟨hu, m, hm1, hl⟩
  · exact Or.inl (Nat.le_trans hsz h)
  · rcases hpr τ hu with h | h
    · have hlt0 := hpl τ h
      have hm0 : cP.mem[τ]? = some cP.mem[τ] := by simp [hlt0]
      have e' : c1.mem[τ]? = some m := hm1
      rw [hme τ _ hm0] at e'
      cases e'
      exact Or.inr ⟨h, _, hm0, hl⟩
    · exact Or.inl h

/-! ## S7f: the tied typed run -/

/-- (Gap b) **Every cell type of `E` is closed.**  Cells are created only by
allocation, at `cl ρ η.wit 0 0 τ` (`new`) or an array of it (`newBuf`), closed
by `Clo_cl` from `Coh`; the step footprint `EFoot` records it at the fresh
labels. -/
def StoClo (E : TEnv) : Prop := ∀ l c, E.sto l = some c → Clo c.ty

/-- (Gap b) **`StoClo` along a thread step** (any step family: its footprint
`EFoot`; `bufInit`'s `withSto`, `publish` and the box allocations keep `sto`,
`new`/`newBuf` add closed cells). -/
theorem StoClo_EFoot {W : Ty → Prop} {g : G} {E E' : TEnv} {s s' : St} (h : EFootB W g E E' s s') (hc : StoClo E) :
    StoClo E' := by
  intro l c hl
  rcases h.2.2.1 l with e | ⟨-, T, hT, hclo, -⟩
  · rw [e] at hl; exact hc l c hl
  · rw [hT] at hl; cases hl; exact hclo.1

/-! ## (certWin-D, F1) `AnchR` along the typed run -/

/-- (certWin-D) `FrRun` with the anchored antecedents (`AnchR`, at the run anchor `Ea`, by default the
run start `E0`) at the same state. -/
def FrRunA (E0 : TEnv) (n0 v0 : Nat) (E : TEnv) (s : St) (Ea : TEnv := E0) (Eu : TEnv := Ea) : Prop :=
  FrRun E0 n0 v0 E s ∧ AnchR Eu Ea E s ∧ (Ea = E0 ∨ Ext Ea E0)

/-- The run anchor `Ea` is extended by the run's environment. -/
theorem frRunA_ext {E0 E Eu Ea : TEnv} {n0 v0 : Nat} {s : St} (h : FrRunA E0 n0 v0 E s Ea Eu) (hx : Ext E0 E) :
    Ext Ea E := by
  rcases h.2.2 with rfl | h'
  · exact hx
  · exact Ext_trans h' hx

/-- A `bufInit` step's footprint counts the written slot (`BufInitBump`). -/
def BumpIf (th : TTh) (E' : TEnv) : Prop :=
  ∀ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e → BufInitBump th bb ib E'

/-- (BII, moved from `TermBiiS`) **`tstep_footprint` at a `bufInit`**: the footprint's environment
counts the written slot. -/
theorem tstep_footprintB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hZ : ZOK g (CE η) th)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    {x : String} {b i v : At} {e : Expr} (hterm : th.term = .let_ x (.bufInit b i v) e) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ Ext (CE η) E' ∧
        ThInvE p E' r.2.2 ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧ BufInitBump th b i E' := by
  have h := tstepM_bufInitB hterm hP hT hi hE htv hm hZ hRP hPS
  refine ⟨h.1, fun r hr hpa => ?_⟩
  obtain ⟨E', hF, h1, h2, hB⟩ := h.2 r hr hpa
  have hF' : Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := ⟨hF, fun l hl => fresh_blank hm hl⟩
  have hx : Ext (CE η) E' := by
    obtain ⟨_, η', _, hce, _⟩ := h1
    subst hce; exact Foot_ext hF'
  exact ⟨E', hF', hx, h1, h2, hB⟩

/-- `BumpIf` from a `bufInit` footprint's `BufInitBump`. -/
theorem bumpIf_of {th : TTh} {E' : TEnv} {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.bufInit b i v) e) (h : BufInitBump th b i E') : BumpIf th E' := by
  intro x' b' i' v' e' ht
  rw [hterm] at ht
  simp only [Expr.let_.injEq, Op.bufInit.injEq] at ht
  obtain ⟨-, ⟨rfl, rfl, -⟩, -⟩ := ht
  exact h

/-- **`tstep_footprint` with the count a `bufInit` leaves** (`BumpIf`): `tstep_footprintB` at a
`bufInit`, `tstep_footprint` elsewhere. -/
theorem tstep_footprintQ {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : ScopeD th.σs cx th.term)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hZ : ZOK g (CE η) th := by exact fun _ _ h => False.elim h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ Ext (CE η) E' ∧
        ThInvE p E' r.2.2 ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧ BumpIf th E' := by
  by_cases hb : ∃ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e
  · obtain ⟨x, bb, ib, v, e, hterm⟩ := hb
    have h := tstep_footprintB hP hT hi hE htv hm hZ hRP hPS hterm
    refine ⟨h.1, fun r hr hpa => ?_⟩
    obtain ⟨E', h1, h2, h3, h4, h5⟩ := h.2 r hr hpa
    exact ⟨E', h1, h2, h3, h4, bumpIf_of hterm h5⟩
  · have h := tstep_footprint hP hp hn hnd hsc hT hi hE htv hm hbf hpx hwin hRP hPS hSub hSig hZ hPb
    refine ⟨h.1, fun r hr hpa => ?_⟩
    obtain ⟨E', h1, h2, h3, h4⟩ := h.2 r hr hpa
    exact ⟨E', h1, h2, h3, h4, fun x bb ib v e ht => (hb ⟨x, bb, ib, v, e, ht⟩).elim⟩

/-- **A typed thread step keeps `AnchR`**: `anchR_stepA` with the write locations of `WrIniC` and the
count of `BumpIf`. -/
theorem anchR_tstep [WrIniC] {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
    {ρ : Nat → Nat} {η : TEnv} {r : Memory × List Ts × TTh} {Eu E0 E' : TEnv}
    (hF : Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) (hm' : MemInv g E' (stOf r.1 r.2.1 r.2.2))
    (hb : BumpIf th E') (hE : EnvOK p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : ScopeD th.σs cx th.term) (hvr : ∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws → w.view ≤ w.rts)
    (hr : r ∈ tstep g mem pairs th) (hx : Ext E0 (CE η))
    (hA : AnchR Eu E0 (CE η) (stOf mem pairs th)) : AnchR Eu E0 E' (stOf r.1 r.2.1 r.2.2) :=
  anchR_stepA hA hF.1 hm.2.2.2.1 hm' (fun l c h => hx.2.2.2.2.1 l c h)
    (TermLiveProps.tstep_ext g mem pairs th r hr).mem.size (wrLocA2_of (WrIniC.wrA hE hT htv hi hm hsc hvr hr) hb (noPfr Eu)) (fun _ => rfl)

/-- (certWin-D) **The post-step anchor**: a thread step from `CE η` to `E'` that is no `bufInit` wherever
the frontier of a cell of `CE η` changes keeps `AnchR` at `CE η` itself (the start of a run at the
successor, anchored at the pre-step environment). -/
theorem anchR_post [WrIniC] {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
    {ρ : Nat → Nat} {η : TEnv} {r : Memory × List Ts × TTh} {E' : TEnv}
    (hF : EFoot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) (hm' : MemInv g E' (stOf r.1 r.2.1 r.2.2))
    (hb : ∀ l, (CE η).sto l ≠ none → E'.pfr l ≠ (CE η).pfr l → ∀ x bb ib v e, th.term ≠ .let_ x (.bufInit bb ib v) e)
    (hE : EnvOK p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : ScopeD th.σs cx th.term) (hvr : ∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws → w.view ≤ w.rts)
    (hr : r ∈ tstep g mem pairs th)
    (hwl : WrLocA2 (noPfr (CE η)) g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2))
    (hrc : RiniCoh (CE η) (stOf mem pairs th))
    (hfl : ∀ l c f, (CE η).sto l = some c → (CE η).pfr l = some f → f ≤ mem.size - 1) :
    AnchR (CE η) (CE η) E' (stOf r.1 r.2.1 r.2.2) := by
  exact anchR_stepA (Ez := noPfr (CE η)) (anchR_start hm hrc hfl) hF hm.2.2.2.1 hm' (fun _ _ h => h)
    (TermLiveProps.tstep_ext g mem pairs th r hr).mem.size hwl (fun _ => rfl)

/-- (certWin-D) A footprint from `CE η` to `CE η'` whose fresh labels were blank is an extension. -/
theorem ext_post {W : Ty → Prop} {g : G} {η η' : TEnv} {s s' : St} (hF : EFootB W g (CE η) (CE η') s s')
    (hfr : FreshLP g (CE η) s) (hbx : ∀ l, FreshIn g s.nalloc s'.nalloc l → (CE η).box l = none) :
    Ext (CE η) (CE η') := by
  refine Foot_ext ⟨hF.toP, fun l hl => ?_⟩
  obtain ⟨j, hj, hj', rfl⟩ := hl
  have h0 := hfr.1 j hj
  exact ⟨h0.1, hbx _ ⟨j, hj, hj', rfl⟩, h0.2.2.1, h0.2.2.2⟩

/-- **A promise step keeps `AnchR`** (the environment kept; the new message is a promise). -/
theorem anchR_prom {Eu E0 E : TEnv} {c : Cfg} {i : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hth : c.ths[i]? = some th) (h : AnchR Eu E0 E (stOf c.mem c.pairs th)) :
    AnchR Eu E0 E (stOf (promise c i a v w).mem (promise c i a v w).pairs
      { th with promises := th.promises ++ [c.mem.size] }) := by
  rw [(promise_inv (a := a) (v := v) (w := w) hth).2.2]
  refine anchR_keep h (fun t m ht hm => ?_) ?_
  · simp only [promSt, stOf, List.mem_append, List.mem_singleton, not_or] at ht hm ⊢
    refine ⟨ht.1, ?_⟩
    simpa [Array.getElem?_push, ht.2] using hm
  · simp [promSt, stOf]

/-- `FrRunA` at a promise step. -/
theorem frRunA_prom {E0 E Eu Ea : TEnv} {n0 v0 : Nat} {c : Cfg} {i : Nat} {th : TTh} {a : Address}
    {v : WeakMem.Val} {w : Ts} (hth : c.ths[i]? = some th) (h : FrRunA E0 n0 v0 E (stOf c.mem c.pairs th) Ea Eu) :
    FrRunA E0 n0 v0 E (stOf (promise c i a v w).mem (promise c i a v w).pairs
      { th with promises := th.promises ++ [c.mem.size] }) Ea Eu := by
  refine ⟨?_, anchR_prom hth h.2.1, h.2.2⟩
  rw [(promise_inv (a := a) (v := v) (w := w) hth).2.2]
  refine ⟨h.1.1, ?_, h.1.2.2⟩
  show n0 ≤ (c.mem.push ⟨a, v, w⟩).size
  rw [Array.size_push]
  exact Nat.le_succ_of_le h.1.2.1

/-- `FrRunA` at the start, anchored at any `Ea` with `AnchR` there (a post-step start). -/
theorem frRunA_startA {E Eu Ea : TEnv} {s : St} (hA : AnchR Eu Ea E s) (hx : Ea = E ∨ Ext Ea E) :
    FrRunA E s.mem.size s.vs.vWr E s Ea Eu :=
  ⟨⟨Nat.le_refl _, Nat.le_refl _, fun _ _ h0 h => absurd (h0.symm.trans h) (fun e => by cases e)⟩, hA, hx⟩

/-- `FrRunA` at the start (the invariant's own environment). -/
theorem frRunA_start {g : G} {E : TEnv} {s : St} (hm : MemInv g E s) (hrc : RiniCoh E s)
    (hfl : ∀ l c f, E.sto l = some c → E.pfr l = some f → f ≤ s.mem.size - 1) : FrRunA E s.mem.size s.vs.vWr E s :=
  ⟨⟨Nat.le_refl _, Nat.le_refl _, fun _ _ h0 h => absurd (h0.symm.trans h) (fun e => by cases e)⟩,
    anchR_start hm hrc hfl, .inl rfl⟩

/-- (S7f) Thread `i` of `c` satisfies the stage-A invariant at an extension
(`Ext`) of the start environment `E0`; (B4) with the frontier bound from a
start at memory size `n0` and `vWr` `v0` (`FrBound`, `FrRun`); (iniop) with the run's count
locality `IniLoc` at the start labels `Z`. -/
def InvAtXZ (Z : AllocLabel → Prop) (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (E0 : TEnv)
    (n0 v0 : Nat) (c : Cfg) (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) (Ea : TEnv := E0) (Eu : TEnv := Ea) : Prop :=
  ∃ th E, c.ths[i]? = some th ∧ Ext E0 E ∧ ThInvE p E th ∧ MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧
    StoClo E ∧ (gOf p k arch c i).boxFence = true ∧ FrBound E0 n0 v0 E ∧ FrRunA E0 n0 v0 E (stOf c.mem c.pairs th) Ea Eu ∧
    IniLoc Z E0 E ∧ IniHeld H E0 E th.vs.vWr

/-- `InvAtXZ` with no locality labels. -/
abbrev InvAtX (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (E0 : TEnv) (n0 v0 : Nat) (c : Cfg)
    (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) (Ea : TEnv := E0) (Eu : TEnv := Ea) : Prop :=
  InvAtXZ (fun _ => False) p k arch i E0 n0 v0 c H Ea Eu

theorem InvAtXZ.toInvAt {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 : TEnv} {Eu Ea : TEnv} {n0 v0 : Nat}
    {c : Cfg} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} (h : InvAtXZ Z p k arch i E0 n0 v0 c H (Ea := Ea) (Eu := Eu)) :
    InvAt p k arch i c :=
  let ⟨th, E, hth, _, h1, h2, _, hbo, _⟩ := h
  ⟨th, hth, E, h1, h2, hbo⟩

/-- (S7f) The start: the invariant's own environment. -/
theorem InvAtX_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E : TEnv} {c : Cfg} {th : TTh}
    (hth : c.ths[i]? = some th) (hT : ThInvE p E th)
    (hm : MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th)) (hSC : StoClo E) (hbo : (gOf p k arch c i).boxFence = true)
    (hrc : RiniCoh E (stOf c.mem c.pairs th)) (hfl : ∀ l cl f, E.sto l = some cl → E.pfr l = some f → f ≤ c.mem.size - 1)
    (Z : AllocLabel → Prop := fun _ => False) (H : AllocLabel → Nat → Ts → Prop := fun _ _ _ => True) :
    InvAtXZ Z p k arch i E c.mem.size th.vs.vWr c H := by
  obtain ⟨ρ, η, cx, rfl, h⟩ := hT
  exact ⟨th, CE η, hth, Ext_refl (Coh_CE η) (CohR_CE η), ⟨ρ, η, cx, rfl, h⟩, hm, hSC, hbo,
    FrBound_refl _ _ _, frRunA_start hm hrc hfl,
    IniLoc_refl _ _, IniHeld_refl _ _ _⟩

/-- **(S7f) The typed run, tied**: along `Solo` from `c`, at every certified
configuration reached, thread `i`'s invariant holds at an extension of the
start environment `E0` (thread steps by the exact footprint `tstep_footprint`,
`Foot_ext`; promise steps keep the environment).  In particular every cell of
`E0` keeps its `Cell` (type and owner). -/
theorem solo_typedX {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c : Cfg} {E0 : TEnv} {Eu Ea : TEnv}
    {n0 v0 : Nat} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch Eu Ea i c0)
    (h0 : InvAtXZ Z p k arch i E0 n0 v0 c H (Ea := Ea) (Eu := Eu)) (hTA : TidAt i c E0) {c2 : Cfg} (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h)
    (hHr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) → H l o τ := by
      exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    InvAtXZ Z p k arch i E0 n0 v0 c2 H (Ea := Ea) (Eu := Eu) := by
  refine (run_inv (c1 := c2) (P := fun c0 => Solo p k arch i c c0 ∧ InvAtXZ Z p k arch i E0 n0 v0 c0 H (Ea := Ea) (Eu := Eu)) ?_ ?_ ?_ h
    (.refl _) ⟨.refl _, h0⟩).2
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hIL, hIH⟩ hs hrest
    have hc0' : Certified p k arch c0' i := certified_back hrest hc2
    have hcert0 : Certified p k arch c0 i := certified_back (.thread hs hrest) hc2
    obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc0'
    rw [hth] at hth'
    cases hth'
    obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, hrp⟩ := hTE
    have hscope := hsc c0 hc0 hcert0 th hth (not_spawnT_of_mem hr) ρ η cx hE hT htv hi
    obtain ⟨-, hstep⟩ := tstep_footprintQ (g := { gOf p k arch c0 i with zf := Z }) hP rfl
      (Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth)))
      (tstep_notDone hr) hscope hT hi hE htv hm hbo (PAx_of_step hs hc0' hth)
      (hwin c0 hc0 hcert0 th hth ρ η cx hE hT htv hi hm (frRunA_ext hfr hx) hfr.2.1.1 hfr.2.1.2.2.1) (hZ := ZOK_of_not (hZr c0 hc0 hcert0 th hth)) (hRP := hrp) (hPS := hPS) (hSub := hSub) (hSig := hSig)
    obtain ⟨E', hF, hx', hT', hm', hbB⟩ := hstep r hr hpa
    have hA' := anchR_tstep hF hm' hbB hE hT htv hi hm hscope (TermViewInv.envVR_solo hvI hc0 hth) hr (frRunA_ext hfr hx) hfr.2.1
    have hfb' := FrBound_foot hF (tstep_wrUp _ _ _ _ r hr) hfb hfr.1
    refine ⟨solo_trans hc0 (.thread hs (.refl _)), r.2.2, E', e3, Ext_trans hx hx', hT', ?_,
      StoClo_EFoot hF.1 hSC, by rw [gOf_thread hs]; exact hbo, hfb'.1, ?_, IniLoc_foot hF (fun _ h => h) hfb hIL,
      ?_⟩
    · rw [gOf_thread hs, e1, e2]
      exact hm'
    · rw [e1, e2]
      exact ⟨hfb'.2, hA', hfr.2.2⟩
    · exact IniHeld_foot hF (tstep_wrUp _ _ _ _ r hr).1 hfb (hHr c0 hc0 hcert0 th hth) hIH
  · rintro c0 a v w ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hIL, hIH⟩ hw _
    refine ⟨solo_trans hc0 (.prom a v w hw (.refl _)), _, E,
      (promise_inv (a := a) (v := v) (w := w) hth).2.1, hx, hTE, ?_, hSC, by rw [gOf_promise]; exact hbo,
      hfb, ?_, hIL, hIH⟩
    · rw [gOf_promise, (promise_inv (a := a) (v := v) (w := w) hth).2.2]
      exact MemInv_promSt hm
    · exact frRunA_prom hth hfr
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hIL, hIH⟩ hs _
    rcases extSteps_res hs hth with ⟨x1, n1, a1, e1, rt1, ws1, rs1, hterm, hn1, hev1, hrs1, rfl⟩ | ⟨x1, a1, e1, l, hterm, htl, rfl⟩
    · exact ⟨solo_trans hc0 (.ext hs (.refl _)), _, E, set_self hth, hx, ThInvE_ext hn1 hterm hev1 hrs1 hTE,
        by rw [gOf_ext hs]; exact hm, hSC, by rw [gOf_ext hs]; exact hbo, hfb, hfr, hIL, hIH⟩
    · obtain ⟨hbs, hbp⟩ := tidBox_ext hx (tidAt_solo hc0 hTA th hth l htl)
      exact ⟨solo_trans hc0 (.ext hs (.refl _)), _, E, set_self (tr := c0.trace) hth, hx, ThInvE_cur hterm hbs hbp hTE,
        by rw [gOf_ext hs]; exact hm, hSC, by rw [gOf_ext hs]; exact hbo, hfb, hfr, hIL, hIH⟩

/-- **(S7f) The fulfilling step, tied**: an outstanding promise is fulfilled
by a single-word write `SW` taken at a typed, in-scope, `PromAbove`
configuration `c1` whose environment `CE η` extends `E0`, into `c2` whose
environment `E2` extends `E0`; there the message is no promise. -/
theorem certified_promTypedX {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {E0 : TEnv} {Eu Ea : TEnv}
    {n0 v0 : Nat} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch Eu Ea i c0)
    (h0 : InvAtXZ Z p k arch i E0 n0 v0 c H (Ea := Ea) (Eu := Eu)) (hTA : TidAt i c E0) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h)
    (hHr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) → H l o τ := by
      exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    ∃ c1 c2 th1 th2 ρ η cx E2, Solo p k arch i c c1 ∧ Certified p k arch c1 i ∧
      c2 ∈ threadSteps p k arch c1 i ∧ Certified p k arch c2 i ∧
      c1.ths[i]? = some th1 ∧ c2.ths[i]? = some th2 ∧
      Ext E0 (CE η) ∧ EnvOK p η ∧ Typed p cx th1.term ∧ TvOK cx ∧
      FInv ρ η th1.σs (Resume p th1.stack) cx th1.env ∧
      MemInv (gOf p k arch c1 i) (CE η) (stOf c1.mem c1.pairs th1) ∧ ScopeD th1.σs cx th1.term ∧
      PromAbove (stOf c1.mem c1.pairs th1) ∧
      Ext E0 E2 ∧ ThInvE p E2 th2 ∧ MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      c1.mem[t]? = some m ∧ c2.mem[t]? = some m ∧ t ∈ th1.promises ∧ t ∉ th2.promises ∧
      SW (gOf p k arch c1 i) c1.mem c1.pairs th1 m.loc m.val ∧ FrBound E0 n0 v0 E2 ∧ IniLoc Z E0 E2 ∧
      IniHeld H E0 E2 th2.vs.vWr := by
  obtain ⟨m', hm', c1, c2, th1, h1, h2, hc2, hth1, hm1, ht1, hn2, hsw⟩ :=
    certified_fulfilC hc (pwf_of_inv h0.toInvAt) ht
  rw [hm] at hm'
  cases hm'
  have hc1 : Certified p k arch c1 i := certified_back (.thread h2 (.refl _)) hc2
  obtain ⟨th1', E1, hth1', hx1, ⟨ρ, η, cx, rfl, hE, hT, htv, hi, -⟩, hmi1, -⟩ := solo_typedX hP hsc hvI hwin h0 hTA h1 hc1 hPS hSub hSig hZr hHr
  rw [hth1] at hth1'
  cases hth1'
  have h12 : Solo p k arch i c c2 := solo_trans h1 (.thread h2 (.refl _))
  obtain ⟨th2, E2, hth2, hx2, hT2, hm2i, -, -, hfb2, -, hIL2, hIH2⟩ := solo_typedX hP hsc hvI hwin h0 hTA h12 hc2 hPS hSub hSig hZr hHr
  obtain ⟨th', r, hth', hr, e1, -, -, -⟩ := threadSteps_inv h2
  rw [hth1] at hth'
  cases hth'
  have hm2 : c2.mem[t]? = some m := by rw [e1]; exact (tstep_grow hr).1 t m hm1
  refine ⟨c1, c2, th1, th2, ρ, η, cx, E2, h1, hc1, h2, hc2, hth1, hth2, hx1, hE, hT, htv, hi, hmi1,
    hsc c1 h1 hc1 th1 hth1 (not_spawnT_of_mem hr) ρ η cx hE hT htv hi, certified_promAboveSt hc1 hth1, hx2, hT2, hm2i, hm1, hm2,
    ht1, ?_, hsw, hfb2, hIL2, hIH2⟩
  rwa [promsOf_some hth2] at hn2

/-- **(S7f) `certified_promWordOK`, tied and at `E0`'s cells**: if the
promise's label has cell `cl` in the start environment, the message is
`undef` or a `WordOK` word of `cl.ty` in an extension `E2` of `E0`. -/
theorem certified_promWordX {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {E0 : TEnv} {Eu Ea : TEnv}
    {n0 v0 : Nat} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch Eu Ea i c0)
    (h0 : InvAtX p k arch i E0 n0 v0 c (Ea := Ea) (Eu := Eu)) (hTA : TidAt i c E0) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ c2 th2 E2, Solo p k arch i c c2 ∧ Certified p k arch c2 i ∧ c2.ths[i]? = some th2 ∧ Ext E0 E2 ∧
      ThInvE p E2 th2 ∧ MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      (∀ cl, E0.sto m.loc.label = some cl → m.val = .undef ∨ WordOK E2 cl.ty m.loc.offset (mw m)) ∧
      FrBound E0 n0 v0 E2 := by
  obtain ⟨c1, c2, -, th2, -, -, -, E2, h1, -, h2, hc2, -, hth2, -, -, -, -, -, -, -, -, hx2, hT2, hm2i,
    -, hm2, -, hn2, -, hfb2, -⟩ := certified_promTypedX hP hsc hvI hwin h0 hTA hc ht hm hPS hSub hSig
  exact ⟨c2, th2, E2, solo_trans h1 (.thread h2 (.refl _)), hc2, hth2, hx2, hT2, hm2i,
    fun cl hcl => hm2i.1.1 t m cl hn2 hm2 (hx2.2.2.2.2.1 _ _ hcl), hfb2⟩

/-- **(S7f) `certified_noPairProm`, tied and at `E0`'s cells**: an
outstanding promise lies in no `word2` unit of the start cell of its label. -/
theorem certified_noPairPromX {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {E0 : TEnv} {Eu Ea : TEnv}
    [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch Eu Ea i c0)
    {n0 v0 : Nat} (h0 : InvAtX p k arch i E0 n0 v0 c (Ea := Ea) (Eu := Eu)) (hTA : TidAt i c E0) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ cl, E0.sto m.loc.label = some cl →
      ∀ o2 r P, AtOff cl.ty o2 (.word2 r P) → m.loc.offset ≠ o2 ∧ m.loc.offset ≠ o2 + 1 := by
  intro cl0 hcl0 o2 r P h2
  obtain ⟨c1, c2, th1, th2, ρ, η, cx, E2, -, -, -, -, -, -, hx1, hE, hT, htv, hi, hmi, hscope, hpa, -, -, -, -, -,
    -, -, hsw, -⟩ := certified_promTypedX hP hsc hvI hwin h0 hTA hc ht hm hPS hSub hSig
  obtain ⟨cl, o, U, us, j, hcl, h1o, hus, hj, ho⟩ :=
    SWOne_holds p _ _ _ _ ρ η cx _ _ hE hT htv hi hmi (scopeD_SW hscope hsw) hpa hsw
  rw [hx1.2.2.2.2.1 _ _ hcl0] at hcl
  cases hcl
  rw [ho]
  exact TermGlob.oneAt_word2 h1o hus hj h2

/-! ## (B4 §3.3, fix (a)) A fetch-op's fulfils write numbers

A fetch-op's `SW` writes `o.kind.apply mr.val nw.val`.  At a typed state the
value read is typed (`pubIntCell` / `wordCellF` / `locCell`: an `Int` cell or
a non-ghost protocol word, the thread's own promises skipped by `PromAbove`),
and the operand is a number, so the written value is a number
(`FetchOp.apply_num`).  No hypothesis on foreign messages is needed: the
typed load lemmas already discharge every readable message. -/

/-- The core, at any address: given the cell's load fact `hcell` (the value
read satisfies `Q`) and that `Q` of one word is a number, every promise the
step fulfils holds a number. -/
theorem fetch_ful_core {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {x : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr}
    {ad : Address} {pw nw : Word} {rt rv : Ty} {dd : Nat} {Q : List Word → Prop}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e)
    (hea : evalAt th.env a = some (rt, [pw])) (haddr : addrOf pw = some ad)
    (hev : evalAt th.env v = some (rv, [nw])) (hnw : nw.val = .num dd)
    (hcell : ∀ s1 ws, (s1, ws) ∈ loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th) →
      PromAbove s1 → Q ws)
    (hq : ∀ rd, Q [rd] → ∃ n, rd.val = .num n)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hpr : PromAbove (stOf r.1 r.2.1 r.2.2))
    {t : Ts} {m : Msg} (ht : t ∈ th.promises) (hn : t ∉ r.2.2.promises) (hmt : mem[t]? = some m) :
    ∃ n, m.val = .num n := by
  have hd : dataE 1 nw = .const nw.val := by simp [dataE, hnw]
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad o.kind
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS { th with term := e, env := (x, fetchRtTy rt, [th'.regs 1]) :: th.env }
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, evalOp, hea, hev, haddr, List.map_map]; rfl
  rw [key, List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, -, s2, hs2, hsame⟩ :=
    stepRmw_splitF (s := stOf mem pairs th) (FetchOp.kind_isFetch o) hd hin
  have hp2 : PromAbove s2 :=
    PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
  have hp1' : PromAbove (bumpRel (lockR g.arch (stOf mem pairs th) s1) _) := storeUnits_promAbove hs2 hp2
  have hp1 : PromAbove s1 := fun t ht m hm => hp1' t ht m hm
  obtain ⟨n, hn1⟩ := hq rd (hcell s1 [rd] hl1 hp1)
  obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hl1
  have hlk : (lockS g.arch (setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs)).promises = s2.promises := by
    unfold lockS; split <;> rfl
  have hn2 : t ∉ s2.promises := by
    rw [← hlk, ← hsame.2.2.2.1]; exact hn
  have ht1 : t ∈ (bumpRel (lockR g.arch (stOf mem pairs th) s1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)).promises := by
    show t ∈ s1.promises
    rw [k3]; exact ht
  obtain ⟨j, w, s0, m', -, hw, he, -, hm0, -, hv, -⟩ := (storeUnits_ful _ _ _ _ _ hs2).2.2 t ht1 hn2
  have hlt : t < (bumpRel (lockR g.arch (stOf mem pairs th) s1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)).mem.size := by
    show t < s1.mem.size
    rw [k1]; exact lt_of_get hmt
  have hm1 := memExt_back he hlt hm0
  have hm2 : mem[t]? = some m' := by
    have e1 : (bumpRel (lockR g.arch (stOf mem pairs th) s1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)).mem = mem := k1
    rw [e1] at hm1; exact hm1
  rw [hmt] at hm2
  cases hm2
  cases j with
  | succ j => simp at hw
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
    subst hw
    obtain ⟨k, hk⟩ := FetchOp.apply_num o n dd
    refine ⟨k, ?_⟩
    rw [hv]
    simp [cst, Promises.TVal.mk0, hn1, hnw, hk]

/-- A fetch-op through a pointer (`tstepM_fetch`'s cases). -/
theorem fetch_ful_numP {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} {μ : Mode} {u : Ty}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e) (_hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hpr : PromAbove (stOf r.1 r.2.1 r.2.2))
    {t : Ts} {m : Msg} (ht : t ∈ th.promises) (hn : t ∉ r.2.2.promises) (hmt : mem[t]? = some m) :
    ∃ n, m.val = .num n := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  cases hop with
  | fetchCell hp _ hc hu hsub hb =>
    rw [hpk] at hp; cases hp
    rcases hc with hc | ⟨r, hc, -⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨lab, pw, ru, hea, hpw, -, -, hcell⟩ :=
        pubIntCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hi hE htv hm
      obtain ⟨hi1, rv, wsv, hev, hvv, -⟩ := use_FInv hu hi
      have hvi := VR_sub hi1.1 hsub _ _ hvv
      simp only [VR] at hvi
      obtain ⟨dd, hdd⟩ := hvi
      obtain ⟨nw, rfl, hnwv⟩ := map_singleton hdd
      refine fetch_ful_core (Q := fun ws => ∃ n, ws.map (·.val) = [.num n]) hterm hea
        (by simp [addrOf, hpw]) hev hnwv (fun s1 ws hl hp1 => (hcell s1 ws hl hp1).2.1)
        (fun rd hq => ?_) hr hpr ht hn hmt
      obtain ⟨n, hn'⟩ := hq
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn'
      exact ⟨n, hn'⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      rcases hμ with h | h <;> cases h
  | fetchEpoch hp hw hep _ hj heq hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwf hpk (.inl rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      have := pwf_epochOK hpwf hep
      unfold epochOK at this; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1.2
    obtain ⟨lab, pw, μ', r', hea, hpw, -, hcell⟩ :=
      wordCellF (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ hg hi hE htv hm
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_num hi.2.1 htvk hjo
    have hj1 := heq ρ hi.1
    simp only [ev] at hj1
    rw [hj1] at hnwv
    refine fetch_ful_core (Q := fun ws => VR ρ η (.word r P) (shp (.word r' P)) ws) hterm hea
      (by simp [addrOf, hpw]) hev hnwv (fun s1 ws hl hp1 => (hcell s1 ws hl hp1).2.1)
      (fun rd hq => ?_) hr hpr ht hn hmt
    simp only [VR] at hq
    obtain ⟨n, hn', -⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn'
    exact ⟨n, hn'⟩
  | fetchShare hp hw hep hj heq hok hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwf hpk (.inl rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      unfold fetchOK at hok; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact hok.1.1.1.1
    obtain ⟨lab, pw, μ', r', hea, hpw, -, hcell⟩ :=
      wordCellF (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ hg hi hE htv hm
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_num hi.2.1 htvk hjo
    rename_i d
    have hjd := heq ρ hi.1
    simp only [ev] at hjd
    rw [hjd] at hnwv
    refine fetch_ful_core (Q := fun ws => VR ρ η (.word r P) (shp (.word r' P)) ws) hterm hea
      (by simp [addrOf, hpw]) hev hnwv (fun s1 ws hl hp1 => (hcell s1 ws hl hp1).2.1)
      (fun rd hq => ?_) hr hpr ht hn hmt
    simp only [VR] at hq
    obtain ⟨n, hn', -⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn'
    exact ⟨n, hn'⟩

/-- A fetch-op through a locative (`tstepM_fetchLoc`'s cases). -/
theorem fetch_ful_numL {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} {μ : Mode} {u : Ty}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e) (_hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hpr : PromAbove (stOf r.1 r.2.1 r.2.2))
    {t : Ts} {m : Msg} (ht : t ∈ th.promises) (hn : t ∉ r.2.2.promises) (hmt : mem[t]? = some m) :
    ∃ n, m.val = .num n := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  cases hop with
  | fetchCell hp _ hc hu hsub hb =>
    rw [hpk] at hp; cases hp
    rcases hc with hc | ⟨r, hc, -⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hus1 : accs (cl ρ η.wit 0 0 .int) = some [.one] := by simp [cl, accs]
      obtain ⟨ad, pw, μr, ru, hea, haddr, -, -, -, -, hld, -, -⟩ :=
        locCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
          (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
      obtain ⟨hi1, rv, wsv, hev, hvv, -⟩ := use_FInv hu hi
      have hvi := VR_sub hi1.1 hsub _ _ hvv
      simp only [VR] at hvi
      obtain ⟨dd, hdd⟩ := hvi
      obtain ⟨nw, rfl, hnwv⟩ := map_singleton hdd
      refine fetch_ful_core (Q := fun ws => ∃ n, ws.map (·.val) = [.num n]) hterm hea haddr hev hnwv
        (fun s1 ws hl hp1 => by simpa [VR] using (hld s1 ws hl hp1).1) (fun rd hq => ?_) hr hpr ht hn hmt
      obtain ⟨n, hn'⟩ := hq
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn'
      exact ⟨n, hn'⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      rcases hμ with h | h <;> cases h
  | fetchEpoch hp hw hep _ hj heq hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwf hpk (.inr rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      have := pwf_epochOK hpwf hep
      unfold epochOK at this; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1.2
    have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
    obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, -, hld, -, -⟩ :=
      locCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
        (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
    obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_num hi.2.1 htvk hjo
    have hj1 := heq ρ hi.1
    simp only [ev] at hj1
    rw [hj1] at hnwv
    refine fetch_ful_core (Q := fun ws => VR ρ η (.word r P) (shp (.word r' P)) ws) hterm hea haddr hev
      hnwv (fun s1 ws hl hp1 => (hld s1 ws hl hp1).1) (fun rd hq => ?_) hr hpr ht hn hmt
    simp only [VR] at hq
    obtain ⟨n, hn', -⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn'
    exact ⟨n, hn'⟩
  | fetchShare hp hw hep hj heq hok hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwf hpk (.inr rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      unfold fetchOK at hok; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact hok.1.1.1.1
    have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
    obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, -, hld, -, -⟩ :=
      locCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
        (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
    obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_num hi.2.1 htvk hjo
    rename_i d
    have hjd := heq ρ hi.1
    simp only [ev] at hjd
    rw [hjd] at hnwv
    refine fetch_ful_core (Q := fun ws => VR ρ η (.word r P) (shp (.word r' P)) ws) hterm hea haddr hev
      hnwv (fun s1 ws hl hp1 => (hld s1 ws hl hp1).1) (fun rd hq => ?_) hr hpr ht hn hmt
    simp only [VR] at hq
    obtain ⟨n, hn', -⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn'
    exact ⟨n, hn'⟩

/-- **(B4 §3.3, fix (a)) A fetch-op's fulfils hold numbers**, at a typed,
in-scope state, for every step whose result keeps `PromAbove`. -/
theorem fetch_ful_num {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} (hterm : th.term = .let_ x (.fetch o acq rel a v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : StepScope cx th.term)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th) (hpr : PromAbove (stOf r.1 r.2.1 r.2.2))
    {t : Ts} {m : Msg} (ht : t ∈ th.promises) (hn : t ∉ r.2.2.promises) (hmt : mem[t]? = some m) :
    ∃ n, m.val = .num n := by
  have hs : OpScope cx (.fetch o acq rel a v) := by
    have h := hsc; rw [hterm] at h; exact h
  have hT0 := hT
  rw [hterm] at hT0
  obtain ⟨tA, hpkA⟩ : ∃ tA, cx.peek a = .ok tA := by
    cases hT0 with
    | let_ hop _ =>
      cases hop with
      | fetchCell hp => exact ⟨_, hp⟩
      | fetchEpoch hp => exact ⟨_, hp⟩
      | fetchShare hp => exact ⟨_, hp⟩
  obtain ⟨μ, u, hteq | hteq, hμ⟩ := hs tA hpkA
  · rw [hteq] at hpkA
    exact fetch_ful_numP hterm hP hpkA hμ hT hi hE htv hm hr hpr ht hn hmt
  · rw [hteq] at hpkA
    exact fetch_ful_numL hterm hP hpkA hμ hT hi hE htv hm hr hpr ht hn hmt

/-- **(B4 §3.3) `certified_promNotUndef`, tied and at `E0`'s cells**: an
outstanding promise of a certified thread is not `undef`, and so a `WordOK`
word of its start cell's type in an extension `E2` of `E0`.  The fulfilling
`SW` is a typed value word (`SW_nundef`) or a fetch-op's, which writes a
number (`fetch_ful_num`). -/
theorem certified_promNotUndefX {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat}
    {E0 : TEnv} {Eu Ea : TEnv} {n0 v0 : Nat} {Z : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} [ProgRetIall p] [WrIniC]
    (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch Eu Ea i c0)
    (h0 : InvAtXZ Z p k arch i E0 n0 v0 c H (Ea := Ea) (Eu := Eu)) (hTA : TidAt i c E0) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hZr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l, BufInitOn th1 l → ¬ Z l := by exact fun _ _ _ _ _ _ _ h => h)
    (hHr : ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ∀ th1, c1.ths[i]? = some th1 →
      ∀ l o τ, (c1.mem.size ≤ τ ∨ (τ ∈ th1.promises ∧ ∃ m, c1.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) → H l o τ := by
      exact fun _ _ _ _ _ _ _ _ _ => trivial) :
    m.val ≠ .undef ∧ ∃ c2 th2 E2, Solo p k arch i c c2 ∧ Certified p k arch c2 i ∧
      c2.ths[i]? = some th2 ∧ Ext E0 E2 ∧ ThInvE p E2 th2 ∧
      MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      (∀ cl, E0.sto m.loc.label = some cl → WordOK E2 cl.ty m.loc.offset (mw m)) ∧
      FrBound E0 n0 v0 E2 ∧ IniLoc Z E0 E2 ∧ IniHeld H E0 E2 th2.vs.vWr := by
  obtain ⟨c1, c2, th1, th2, ρ, η, cx, E2, h1, hc1, h2, hc2, hth1, hth2, -, hE, hT, htv, hi, hmi1, hscope, -,
    hx2, hT2, hm2i, hm1, hm2, ht1, hn2, hsw, hfb2, hIL2, hIH2⟩ := certified_promTypedX hP hsc hvI hwin h0 hTA hc ht hm hPS hSub hSig hZr hHr
  replace hscope := scopeD_SW hscope hsw
  have hnu : m.val ≠ .undef := by
    rcases SW_nundef hE hT htv hi hscope hsw with hnu | ⟨x, o, acq, rel, a, v, e, he⟩
    · exact hnu
    · obtain ⟨th', r, hth', hr, -, -, e3, hpr⟩ := taken_promAbove h2 hc2
      rw [hth1] at hth'
      cases hth'
      rw [hth2] at e3
      obtain rfl := Option.some.inj e3
      obtain ⟨n, hn⟩ := fetch_ful_num he hP hT hi hE htv hmi1 hscope hr hpr ht1 hn2 hm1
      rw [hn]; intro h; cases h
  refine ⟨hnu, c2, th2, E2, solo_trans h1 (.thread h2 (.refl _)), hc2, hth2, hx2, hT2, hm2i,
    fun cl hcl => ?_, hfb2, hIL2, hIH2⟩
  rcases hm2i.1.1 t m cl hn2 hm2 (hx2.2.2.2.2.1 _ _ hcl) with h | h
  · exact absurd h hnu
  · exact h

/-! ## S7f: value-level facts at `WordOK` words -/

/-- A `WordOK` word at a one-word component `U` of the cell type is a value
of `U` in memory's view (`unsee`), up to its view (`WLe1`). -/
theorem wordOK_one {E : TEnv} {T : Ty} {o : Nat} {w : Word} {U : Ty}
    (h : WordOK E T o w) (hP : AtOff T o U) (hU : accs U = some [Acc.one]) :
    ∃ w0, VR (fun _ => 0) (CE E.unsee) U (shp U) [w0] ∧ WLe1 w0 w := by
  obtain ⟨b, S, ws, o', w0, hseg, ⟨⟨hvr, hvd⟩, hsh⟩, hw0, hle, hbo⟩ := h
  have hlt0 : o' < ws.length := (List.getElem?_eq_some_iff.1 hw0).1
  obtain ⟨hatS, usS, hS⟩ : AtOff S o' U ∧ ∃ us, accs S = some us := by
    rcases hseg with ⟨rfl, rfl, hT⟩ | ⟨N, us, j, rfl, hus, hj, rfl⟩
    · subst hbo
      exact ⟨by simpa using hP, Option.ne_none_iff_exists'.1 hT⟩
    · refine ⟨?_, us, hus⟩
      rcases AtOff_arr_elem hP rfl with h | ⟨us', j', o'', hus', hj', ho, hat⟩
      · rw [h] at hU; simp [accs] at hU
      · rw [hus] at hus'
        cases hus'
        have hlt1 : o' < nWords us := hsh us hus ▸ hlt0
        have hlt2 : o'' + nWords [Acc.one] ≤ nWords us := AtOff_bound hat hus hU
        have hlt2' : o'' < nWords us := by have h1 : nWords [Acc.one] = 1 := rfl; omega
        have e : o' + j * nWords us = o'' + j' * nWords us := by omega
        have e2 := congrArg (· % nWords us) e
        simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2'] at e2
        exact e2 ▸ hat
  obtain ⟨nn, hwcU, -, hvrU, -⟩ :=
    VR_at E.unsee hatS hvr hvd (by simp [wc, hS, hsh usS hS])
  have hnn : nn = 1 := by simp [wc, hU, nWords, Acc.size] at hwcU; omega
  subst hnn
  rw [take_one_drop hw0] at hvrU
  exact ⟨w0, hvrU, hle⟩

/-- A `WordOK` word at a non-ghost `.word n P` component: `P` is well formed
and the word holds one of its states. -/
theorem wordOK_word {E : TEnv} {T : Ty} {o : Nat} {w : Word} {n : Idx} {P : Proto}
    (h : WordOK E T o w) (hP : AtOff T o (.word n P)) (hg : P.ghost = false) :
    pwf P = true ∧ ∃ k, w.val = .num k ∧ InP P k := by
  obtain ⟨w0, hvr, hle⟩ := wordOK_one h hP (accs_word hg)
  simp only [VR] at hvr
  obtain ⟨k, hk, hin⟩ := hvr.2 hg
  refine ⟨hvr.1, k, ?_, hin⟩
  rw [← hle.1]
  simpa using hk

/-- A pub-mode reference type. -/
def PubRef (U : Ty) : Prop := ∃ u, U = .ptr .pub u ∨ U = .ptrOpt .pub u ∨ U = .loc .pub u

/-- (S7f) `Fd` keeps closedness backwards. -/
theorem Fd_Clo {T U : Ty} (h : Fd T U) (hU : Clo U) : Clo T := by
  induction h with
  | refl => exact hU
  | fold hW _ _ _ ih => exact ih (Clo_cl hW _ _)

/-- **A `WordOK` reference at a pub-mode component names a cell with a
frontier**; through a `ptr`/`ptrOpt` (whole-cell) reference, the cell's type
is closed. -/
theorem wordOK_pubRef {E : TEnv} {T : Ty} {o : Nat} {w : Word} {U : Ty} {a : Address} {g : Nat}
    (h : WordOK E T o w) (hP : AtOff T o U) (hU : PubRef U) (hv : w.val = .loc a g) :
    ∃ c f, E.sto a.label = some c ∧ E.pfr a.label = some f ∧
      ((∃ u, U = .ptr .pub u ∨ U = .ptrOpt .pub u) → Clo c.ty) := by
  obtain ⟨u, hu⟩ := hU
  have hacc : accs U = some [Acc.one] := by rcases hu with rfl | rfl | rfl <;> rfl
  obtain ⟨w0, hvr, hle⟩ := wordOK_one h hP hacc
  have hw0 : w0.val = .loc a g := hle.1.trans hv
  have hW : ∀ k, Clo ((CE E.unsee).wit k) := fun k => (Coh_CE E.unsee k).1
  rcases hu with rfl | rfl | rfl
  · simp only [VR] at hvr
    obtain ⟨a', c, hws, -, hsto, hFd, ⟨f, hf, -⟩, -⟩ := hvr
    simp only [List.map_cons, List.map_nil, hw0, List.cons.injEq, and_true, Val.loc.injEq] at hws
    obtain ⟨rfl, -⟩ := hws
    exact ⟨c, f, hsto, hf, fun _ => Fd_Clo hFd (Clo_cl hW _ _)⟩
  · simp only [VR] at hvr
    rcases hvr with hws | ⟨a', c, hws, -, hsto, hFd, ⟨f, hf, -⟩, -⟩
    · simp [hw0] at hws
    · simp only [List.map_cons, List.map_nil, hw0, List.cons.injEq, and_true, Val.loc.injEq] at hws
      obtain ⟨rfl, -⟩ := hws
      exact ⟨c, f, hsto, hf, fun _ => Fd_Clo hFd (Clo_cl hW _ _)⟩
  · simp only [VR] at hvr
    rcases hvr with ⟨hws, -⟩ | ⟨a', c, U', hws, hsto, -, -, ⟨f, hf, -⟩, -⟩
    · simp [hw0] at hws
    · simp only [List.map_cons, List.map_nil, hw0, List.cons.injEq, and_true, Val.loc.injEq] at hws
      obtain ⟨rfl, -⟩ := hws
      refine ⟨c, f, hsto, hf, fun ⟨u', hu'⟩ => ?_⟩
      rcases hu' with h' | h' <;> cases h'

/-- `encodeArm` keeps every `loc` address of its payload. -/
theorem locPub_encRev {tr : Tier} {as : List Ty} {j : Nat} {p q : List Word}
    (h : encodeArm tr as j p = some q) :
    ∀ w ∈ p, ∀ y g, w.val = .loc y g → ∃ w' ∈ q, ∃ g', w'.val = .loc y g' := by
  intro w hw y g hv
  rcases p with _ | ⟨w0, _ | ⟨w1, p⟩⟩
  · simp at hw
  · simp at hw; subst hw
    cases tr with
    | niche =>
      simp only [encodeArm] at h
      cases harm : as[j]? with
      | none => simp [harm] at h
      | some arm =>
        cases hk : armK arm <;> simp [harm, hk, hv] at h
        all_goals (subst h; exact ⟨_, List.mem_singleton_self _, _, rfl⟩)
    | wide => simp [encodeArm] at h; subst h; exact ⟨w, by simp, g, hv⟩
    | boxed => simp [encodeArm] at h
  · cases tr with
    | niche =>
      simp only [encodeArm] at h
      cases harm : as[j]? with
      | none => simp [harm] at h
      | some arm => cases armK arm <;> simp [harm] at h
    | wide => simp [encodeArm] at h
    | boxed => simp [encodeArm] at h

/-- Every `loc` address `encodeArm` writes is one of its payload's. -/
theorem locPub_encFwd {tr : Tier} {as : List Ty} {j : Nat} {p q : List Word}
    (h : encodeArm tr as j p = some q) :
    ∀ w ∈ q, ∀ y g, w.val = .loc y g → ∃ w' ∈ p, ∃ g', w'.val = .loc y g' := by
  intro w hw y g hv
  rcases p with _ | ⟨w0, _ | ⟨w1, p⟩⟩
  · cases tr with
    | niche =>
      simp only [encodeArm] at h
      cases harm : as[j]? with
      | none => simp [harm] at h
      | some arm =>
        cases hk : armK arm <;> simp [harm, hk] at h
        subst h; simp at hw; subst hw; simp [cst, Promises.TVal.mk0] at hv
    | wide =>
      simp [encodeArm] at h; subst h; simp at hw
      rcases hw with rfl | rfl <;> simp [cst, Promises.TVal.mk0] at hv
    | boxed => simp [encodeArm] at h
  · cases tr with
    | niche =>
      simp only [encodeArm] at h
      cases harm : as[j]? with
      | none => simp [harm] at h
      | some arm =>
        simp [harm] at h
        split at h <;> (try split at h) <;> (try split at h) <;> (try simp only [Option.some.injEq] at h) <;>
          (try (subst h; simp only [List.mem_singleton] at hw; subst hw)) <;> simp_all [cst, Promises.TVal.mk0]
    | wide =>
      simp [encodeArm] at h; subst h; simp at hw
      rcases hw with rfl | rfl
      · simp [cst, Promises.TVal.mk0] at hv
      · exact ⟨w, by simp, g, hv⟩
    | boxed => simp [encodeArm] at h
  · cases tr with
    | niche =>
      simp only [encodeArm] at h
      cases harm : as[j]? with
      | none => simp [harm] at h
      | some arm => cases armK arm <;> simp [harm] at h
    | wide => simp [encodeArm] at h
    | boxed => simp [encodeArm] at h

/-- `ofArm` keeps every `loc` address of its payload. -/
theorem locPub_ofArmRev {t : Ty} {j : Nat} {p q : List Word} (h : ofArm t j p = some q) :
    ∀ w ∈ p, ∀ y g, w.val = .loc y g → ∃ w' ∈ q, ∃ g', w'.val = .loc y g' := by
  unfold ofArm at h
  split at h
  · exact locPub_encRev h
  · split at h
    · simp at h; subst h; intro w hw y g hv; exact ⟨w, hw, g, hv⟩
    · contradiction

theorem locPub_push0_rels {η : TEnv} (h : ∀ k r vs, ¬ η.rels k r vs) (s : Ty) :
    ∀ k r vs, ¬ (η.push0 s).rels k r vs := by
  intro k r vs hk
  simp only [TEnv.push0, TEnv.ins, TEnv.insR] at hk
  by_cases h0 : k = 0
  · subst h0; simp at hk
  · simp [h0] at hk; exact h _ _ _ hk

/-- A word of a value is one of the value's word values. -/
theorem locPub_mem_val {ws : List Word} {vs : List WeakMem.Val} (h : ws.map (·.val) = vs) {w : Word}
    (hw : w ∈ ws) : w.val ∈ vs := h ▸ List.mem_map_of_mem hw

/-- The labels a pub/box-closed value names. -/
def LPGood (η : TEnv) (l : AllocLabel) : Prop :=
  (∃ c f, η.sto l = some c ∧ η.pfr l = some f) ∨ ∃ B, η.box l = some B

/-- **Inversion.**  Every `loc` word of an `own`- and region-free value (at its
own shape, of its own word count, valid, in an env with no type-variable
values) names a published cell or a box. -/
theorem locPub_VR : ∀ (T : Ty) (ke : KEnv) (ρ : Nat → Nat) (η : TEnv) (ws : List Word),
    (∀ k r vs, ¬ η.rels k r vs) → Ty.noOwnIn ke T = true → rgnFree T = true →
    wc T = some ws.length → Valid T ws → VR ρ η T (shp T) ws →
    ∀ w ∈ ws, ∀ x g, w.val = .loc x g → LPGood η x.label := by
  intro T
  induction T with
  | prod a b iha ihb =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    simp only [Ty.noOwnIn, rgnFree, Bool.and_eq_true] at hno hrf
    rw [wc_prod] at hlen
    cases ha : wc a with
    | none => simp [ha] at hlen
    | some na =>
      cases hb : wc b with
      | none => simp [ha, hb] at hlen
      | some nb =>
        simp [ha, hb] at hlen
        obtain ⟨ra, rb, hr, hv⟩ := hv
        simp only [shp, Shp.prod.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨hle, hva, hvb⟩ := hv na (by rw [shp_wc]; exact ha)
        obtain ⟨Va, Vb⟩ := hval na ha
        rw [← List.take_append_drop na ws] at hw
        rcases List.mem_append.1 hw with h | h
        · exact iha ke ρ η _ hrel hno.1 hrf.1 (by rw [ha, List.length_take]; congr 1; omega) Va hva w h x g hx
        · exact ihb ke ρ η _ hrel hno.2 hrf.2 (by rw [hb, List.length_drop]; congr 1; omega) Vb hvb w h x g hx
  | sum a b iha ihb =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    simp only [Ty.noOwnIn, rgnFree, Bool.and_eq_true] at hno hrf
    obtain ⟨n, Ra, Rb, hr, hcase⟩ := hv
    simp only [shp, lnorm, Shp.sum.injEq, Ty.sum.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have htl : (Ty.sum (lnorm a) (lnorm b)).tier = (Ty.sum a b).tier := tier_lnorm (.sum a b)
    rcases hcase with ⟨-, y, s, B, hvals, -, hbox, -⟩ | ⟨j, p, hd, hA, hB⟩
    · have hm := locPub_mem_val hvals hw
      rw [hx] at hm
      simp at hm
      obtain ⟨rfl, -⟩ := hm
      exact Or.inr ⟨B, hbox⟩
    · rcases hval with htb | ⟨j', p', arm, hd', -, -, ⟨q0, he, hveq⟩, hA', hB'⟩
      · rw [htl, htb] at hd; simp [decodeArm] at hd
      · have hd2 := decodeArm_mono (arms_lnorm (.sum a b)) hd'
        rw [htl] at hd
        have hjp : (j, p) = (j', p') := Option.some.inj (hd.symm.trans hd2)
        simp only [Prod.mk.injEq] at hjp
        obtain ⟨rfl, rfl⟩ := hjp
        have hm : w.val ∈ q0.map (·.val) := hveq ▸ List.mem_map_of_mem hw
        obtain ⟨w0, hw0, hv0⟩ := List.mem_map.1 hm
        obtain ⟨w1, hw1, g1, hv1⟩ := locPub_encFwd he w0 hw0 x g (hv0.trans hx)
        have hlenA : (armsOf (lnorm a)).length = (armsOf a).length := by
          rw [armsOf_lnorm, List.length_map]
        by_cases hj : j < (armsOf a).length
        · obtain ⟨q, hq, hvq⟩ := hA (by rw [hlenA]; exact hj)
          obtain ⟨q', hq', hsq, hwq, hvalq⟩ := hA' hj
          have hqq : q' = q := Option.some.inj ((ofArm_lnorm hq').symm.trans hq)
          subst hqq
          obtain ⟨w2, hw2, g2, hv2⟩ := locPub_ofArmRev hq' w1 hw1 x g1 hv1
          have hwc : wc a = some q'.length := by
            cases hu : accs a with
            | none => simp [wc, hu] at hwq
            | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
          rw [shp_lnorm] at hvq
          exact iha ke ρ η q' hrel hno.1 hrf.1 hwc hvalq hvq w2 hw2 x g2 hv2
        · have hj2 : (armsOf a).length ≤ j := Nat.le_of_not_lt hj
          obtain ⟨q, hq, hvq⟩ := hB (by rw [hlenA]; exact hj2)
          obtain ⟨q', hq', hsq, hwq, hvalq⟩ := hB' hj2
          rw [hlenA] at hq
          have hqq : q' = q := Option.some.inj ((ofArm_lnorm hq').symm.trans hq)
          subst hqq
          obtain ⟨w2, hw2, g2, hv2⟩ := locPub_ofArmRev hq' w1 hw1 x g1 hv1
          have hwc : wc b = some q'.length := by
            cases hu : accs b with
            | none => simp [wc, hu] at hwq
            | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
          rw [shp_lnorm] at hvq
          exact ihb ke ρ η q' hrel hno.2 hrf.2 hwc hvalq hvq w2 hw2 x g2 hv2
  | refine t ψ ih =>
    intro ke ρ η ws hrel hno hrf hlen hval hv
    exact ih ke ρ η ws hrel hno hrf hlen hval hv.1
  | iall t ih =>
    intro ke ρ η ws hrel hno hrf hlen hval hv
    exact ih ke (vcons 0 ρ) η ws hrel hno hrf hlen hval (hv 0)
  | iex t ih =>
    intro ke ρ η ws hrel hno hrf hlen hval hv
    obtain ⟨n, rb, w, hr, hv⟩ := hv
    simp only [shp, Shp.iex.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    rw [wc_iex] at hlen
    exact ih ke (vcons w ρ) η ws hrel hno hrf hlen hval hv
  | mu t ih =>
    intro ke ρ η ws hrel hno hrf hlen hval hv
    exact ih (none :: ke) ρ (η.push0 (cl ρ η.wit 0 0 (.mu t))) ws (locPub_push0_rels hrel _) hno hrf hlen hval hv
  | tex κ t ih =>
    intro ke ρ η ws hrel hno hrf hlen hval hv
    simp only [Ty.noOwnIn, Bool.and_eq_true] at hno
    obtain ⟨n, rb, s, hr, -, -, hv⟩ := hv
    simp only [shp, Shp.tex.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    rw [wc_tex] at hlen
    exact ih (some κ :: ke) ρ (η.push0 s) ws (locPub_push0_rels hrel s) hno.2 hrf hlen hval hv
  | tvar k =>
    intro ke ρ η ws hrel hno hrf hlen hval hv
    obtain ⟨ws', -, hg⟩ := hv
    exact absurd hg (hrel _ _ _)
  | ptr μ u =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    cases μ with
    | own => simp [Ty.noOwnIn] at hno
    | rgn r => simp [rgnFree] at hrf
    | pub =>
      obtain ⟨a, c, h1, -, h3, -, ⟨f, hf, -⟩, -⟩ := hv
      have hm := locPub_mem_val h1 hw
      rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
      exact Or.inl ⟨c, f, h3, hf⟩
  | ptrOpt μ u =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    cases μ with
    | own => simp [Ty.noOwnIn] at hno
    | rgn r => simp [rgnFree] at hrf
    | pub =>
      rcases hv with h0 | ⟨a, c, h1, -, h3, -, ⟨f, hf, -⟩, -⟩
      · have hm := locPub_mem_val h0 hw
        rw [hx] at hm; simp at hm
      · have hm := locPub_mem_val h1 hw
        rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
        exact Or.inl ⟨c, f, h3, hf⟩
  | loc μ u =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    cases μ with
    | own => simp [Ty.noOwnIn] at hno
    | rgn r => simp [rgnFree] at hrf
    | pub =>
      rcases hv with ⟨h0, -⟩ | ⟨a, c, U, h1, h3, -, -, ⟨f, hf, -⟩, -⟩
      · have hm := locPub_mem_val h0 hw
        rw [hx] at hm; simp at hm
      · have hm := locPub_mem_val h1 hw
        rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
        exact Or.inl ⟨c, f, h3, hf⟩
  | void =>
    intro ke ρ η ws hrel hno hrf hlen hval hv
    simp [VR] at hv
  | intS i =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    have hm := locPub_mem_val hv hw
    rw [hx] at hm; simp at hm
  | int =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨n, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | opq _ =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨n, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | tid =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨n, c, hn, hs, -, hmo⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm
    simp only [List.mem_singleton, Val.loc.injEq] at hm
    obtain ⟨rfl, -⟩ := hm
    obtain ⟨f, hf, -⟩ := hmo
    exact Or.inl ⟨c, f, hs, hf⟩
  | fix sg wd =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨-, n, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | lanes sg wd =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨-, n, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | code a b _ _ =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨i, d, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | word r P =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    cases hg : P.ghost with
    | true =>
      simp [wc, accs, hg, nWords] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen.symm] at hw; simp at hw
    | false =>
      obtain ⟨n, hn, -⟩ := hv.2 hg
      have hm := locPub_mem_val hn hw
      rw [hx] at hm; simp at hm
  | word2 r P =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨-, n0, n1, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | epair r P =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw x g hx
    obtain ⟨-, n0, n1, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | array i t _ =>
    intro ke ρ η ws hrel hno hrf hlen
    simp [wc, accs] at hlen
  | unit | share _ | cap _ _ | tok _ _ | tok2 _ _ _ _ | tokE _ _ _ =>
    intro ke ρ η ws hrel hno hrf hlen hval hv w hw
    simp [wc, accs, nWords] at hlen
    rw [List.eq_nil_of_length_eq_zero hlen.symm] at hw; simp at hw

/-- **`wordOK_locPub`.** -/
theorem wordOK_locPub {E : TEnv} {T : Ty} {o : Nat} {w : Word} {a : Address} {g : Nat}
    (h : WordOK E T o w) (hno : Ty.noOwnIn [] T = true) (hrf : rgnFree T = true)
    (hv : w.val = .loc a g) :
    (∃ c f, E.sto a.label = some c ∧ E.pfr a.label = some f) ∨ ∃ B, E.box a.label = some B := by
  obtain ⟨b, S, ws, o', w0, hseg, ⟨⟨hvr, hval⟩, hsh⟩, hget, hle, -⟩ := h
  have hS : Ty.noOwnIn [] S = true ∧ rgnFree S = true ∧ accs S ≠ none := by
    rcases hseg with ⟨-, rfl, hacc⟩ | ⟨N, us, j, rfl, hus, -, -⟩
    · exact ⟨hno, hrf, hacc⟩
    · simp only [Ty.noOwnIn, rgnFree] at hno hrf
      exact ⟨hno, hrf, by rw [hus]; simp⟩
  obtain ⟨hnoS, hrfS, hacc⟩ := hS
  have hwc : wc S = some ws.length := by
    cases hu : accs S with
    | none => exact absurd hu hacc
    | some us => simp only [wc, hu, Option.map_some]; rw [hsh us hu]
  have hrel : ∀ k r vs, ¬ (CE E.unsee).rels k r vs := fun _ _ _ h => h
  exact locPub_VR S [] (fun _ => 0) (CE E.unsee) ws hrel hnoS hrfS hwc hval hvr w0
    (List.mem_of_getElem? hget) a g (hle.1.trans hv)

/-- (S7f, gap b) **Words of a closed type are at literal regions.** -/
theorem AtOff_word_lit {T U : Ty} {o : Nat} (h : AtOff T o U) (hT : Clo T) :
    ∀ r P, U = .word r P → ∃ n, r = .lit n := by
  have hT' := hT.2 (fun _ => 0) (fun _ => .void) 0 0
  clear hT
  induction h with
  | here _ =>
      intro r P e
      subst e
      simp only [cl, clI_zero, Ty.word.injEq] at hT'
      exact ⟨_, hT'.1.symm⟩
  | fst _ ih =>
      simp only [cl, Ty.prod.injEq] at hT'
      exact ih hT'.1
  | snd _ _ ih =>
      simp only [cl, Ty.prod.injEq] at hT'
      exact ih hT'.2
  | elem _ _ _ ih =>
      simp only [cl, clI, Ty.array.injEq] at hT'
      exact ih hT'.2
  | mu hW _ _ ih => exact ih ((Clo_cl hW _ _).2 _ _ 0 0)
  | fold _ _ _ _ _ =>
      intro r P e
      simp [cl] at e

/-- (S7f, gap c) `IniAt` is vacuous outside buffers. -/
theorem IniAt_nonbuf {ini : AllocLabel → Nat} {c : Cell} {a : Address} {U : Ty}
    (h : ∀ N e, c.ty ≠ .array (.lit N) e) : IniAt ini c a U :=
  fun N e hc => absurd hc (h N e)

/-! ## Gap (a): a fulfilled promise is the coherence point -/

/-- (Gap a) Every promise a step discharges is, afterwards, the thread's
coherence point at its message's address. -/
def FulC (s s' : St) : Prop :=
  ∀ t, t ∈ s.promises → t ∉ s'.promises → ∃ m, s.mem[t]? = some m ∧ s'.vs.coh m.loc = t

theorem fulC_of_keep {s s' : St} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size) (h : KeepR s s') :
    FulC s s' :=
  fun t ht hn => absurd (h.2.2 t ht (hlt t ht)) hn

theorem stepStore_fulC {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {th th' : Promises.Thread} {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) :
    (∀ b, b ≠ a → th'.vs.coh b = th.vs.coh b) ∧
      ∀ t, t ∈ th.promises → t ∉ th'.promises → th'.vs.coh a = t := by
  cases e <;>
  · simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
    rcases h with h | ⟨tw, _, hf⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨fun b hb => by simp [hb], fun t ht hn => absurd ht hn⟩
    · cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm] at hf
          split at hf
          · simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            refine ⟨fun b hb => by simp [hb], fun t ht hn => ?_⟩
            have e := not_mem_erase ht hn
            subst e; simp
          · simp at hf

theorem stepRmw_fulC_at {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel) :
    ∀ t, t ∈ th.promises → t ∉ th'.promises → th'.vs.coh a = t := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, ⟨htr, _⟩, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro t ht hn; rw [lockFence_prom] at hn; exact absurd ht hn
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro t ht hn; rw [lockFence_prom] at hn; exact absurd ht hn
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨-, rfl, rfl⟩ := hf
          intro t ht hn
          rw [lockFence_prom] at hn
          have e := not_mem_erase ht hn
          subst e
          rw [lockFence_coh]; simp

theorem stepRmw_fulC {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) :
    ∀ t, t ∈ th.promises → t ∉ th'.promises → th'.vs.coh a = t := by
  intro t ht hn
  exact stepRmw_fulC_at (th := if arch = .tso then Promises.stepFence th .sy else th) h t (by rw [TermFul.lockFence_prom]; exact ht) hn

theorem offs_ne {a : Address} {i j : Nat} (h : i ≠ j) : offs a i ≠ offs a j := by
  intro e
  have := congrArg Address.offset e
  simp [offs] at this
  exact h this

/-- (Gap a) `storeUnits` leaves coherence alone off the words it writes. -/
theorem storeUnits_cohO {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      ∀ b, (∀ j, b ≠ offs a (i + j)) → s'.vs.coh b = s.vs.coh b
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; intros; rfl
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      intro b hb
      rw [storeUnits_cohO us ws (i + 1) _ s' hs b
        (fun j => by rw [show i + 1 + j = i + (1 + j) by omega]; exact hb _)]
      exact (stepStore_fulC hst).1 b (by simpa using hb 0)
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨-, -, q3, -, -⟩ := TermMem.stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i)
        (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at q3 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q3
      intro b hb
      rw [storeUnits_cohO us ws (i + 2) _ s' hs b
        (fun j => by rw [show i + 2 + j = i + (2 + j) by omega]; exact hb _)]
      show th.vs.coh b = s.vs.coh b
      have h0 : b ≠ offs a i := by simpa using hb 0
      have h1 : b ≠ (offs a i).next := by
        have := hb 1
        have e : (offs a i).next = offs a (i + 1) := by
          simp only [offs, Address.next, Nat.add_assoc]
        rw [e]; exact this
      rw [q3]; simp [h0, h1, mth]
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

/-- (Gap a) A promise `storeUnits` discharges is its final coherence point. -/
theorem storeUnits_fulC {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      (∀ t, t ∈ s.promises → t < s.mem.size) → FulC s s'
  | [], _, _, s, s', hs, _ => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      exact fun t ht hn => absurd ht hn
  | .one :: us, w :: ws, i, s, s', hs, hlt => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨e1, sub1, rem1⟩ := stepStore_ful hst
      intro t ht hn
      by_cases h1 : t ∈ th.promises
      · have hlt' : ∀ t, t ∈ th.promises → t < mem'.size := fun t' h' =>
          Nat.lt_of_lt_of_le (hlt t' (sub1.subset h')) (memExt_size e1)
        obtain ⟨m, hm, hc⟩ := storeUnits_fulC us ws (i + 1) _ s' hs hlt' t h1 hn
        exact ⟨m, memExt_back e1 (hlt t ht) hm, hc⟩
      · obtain ⟨-, m, hm, hl, -⟩ := rem1 t ht h1
        refine ⟨m, hm, ?_⟩
        rw [storeUnits_cohO us ws (i + 1) _ s' hs m.loc (fun j => by
          rw [hl]; exact offs_ne (by omega))]
        rw [hl]; exact (stepStore_fulC hst).2 t ht h1
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs, hlt => by
      simp only [storeUnits] at hs
      obtain ⟨p1, ⟨m0, m1, q1, -, -⟩, -, -, -⟩ := stepStorePair_shape s.mem s.pairs (mth s pw w0 w1)
        (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at p1 q1 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at p1 q1
      have e1 : MemExt s.mem mem' := by rw [q1]; exact (MemExt.push _ _).trans (MemExt.push _ _)
      have p1' : th.promises = s.promises := p1
      have hlt' : ∀ t, t ∈ th.promises → t < mem'.size := fun t' h' =>
        Nat.lt_of_lt_of_le (hlt t' (p1' ▸ h')) (memExt_size e1)
      intro t ht hn
      obtain ⟨m, hm, hc⟩ := storeUnits_fulC us ws (i + 2) _ s' hs hlt' t (p1' ▸ ht) hn
      exact ⟨m, memExt_back e1 (hlt t ht) hm, hc⟩
  | .one :: _, [], _, _, s', hs, _ => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs, _ => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs, _ => by simp [storeUnits] at hs

theorem units_fulC {k : Promises.Knobs} {arch : Arch} {pw : Word} {b : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {s s1 s' : St}
    (hlt : ∀ t, t ∈ s.promises → t < s.mem.size) (hm1 : s1.mem = s.mem) (hp1 : s1.promises = s.promises)
    (hs : s' ∈ storeUnits k arch pw b rel us ws 0 s1) : FulC s s' := by
  have hlt1 : ∀ t, t ∈ s1.promises → t < s1.mem.size := by rw [hm1, hp1]; exact hlt
  intro t ht hn
  obtain ⟨m, hm, hc⟩ := storeUnits_fulC _ _ _ _ _ hs hlt1 t (hp1 ▸ ht) hn
  exact ⟨m, hm1 ▸ hm, hc⟩

section
variable {g : G} {env : Env} {σs : List Ty} {s : St} {r : St × Ty × List Word}

theorem evalOp_store_fulC {rel : Bool} {a v : At} {o : Option At}
    (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.store rel a v o)) : FulC s r.1 := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       exact units_fulC hlt rfl rfl hs)

theorem evalOp_xchg_fulC {a v : At} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.xchg a v)) : FulC s r.1 := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
       exact units_fulC hlt k1 k3 hy)

theorem evalOp_xchgAt_fulC {bb i v : At} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.xchgAt bb i v)) : FulC s r.1 := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
       exact units_fulC hlt k1 k3 hy)

theorem evalOp_xchgAtF_fulC {bb i : At} {p : List Nat} {v : At}
    (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.xchgAtF bb i p v)) : FulC s r.1 := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
       exact units_fulC hlt k1 k3 hy)

theorem evalOp_bufInit_fulC {bb i x : At} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.bufInit bb i x)) : FulC s r.1 := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       exact units_fulC hlt rfl rfl hs)

theorem evalOp_stl_fulC {bb i v : At} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.stl bb i v)) : FulC s r.1 := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
         exact units_fulC hlt k1 k3 hy
       · simp at h)

theorem evalOp_stlw_fulC {bb wi jl v : At} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.stlw bb wi jl v)) : FulC s r.1 := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
         exact units_fulC hlt k1 k3 hy
       · simp at h)

theorem evalOp_fetch_fulC {o : FetchOp} {acq rel : Bool} {a v : At}
    (h : r ∈ evalOp g env σs s (.fetch o acq rel a v)) : FulC s r.1 := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨⟨mem', th'⟩, hx, rfl⟩ := h
       obtain ⟨-, -, rem⟩ := stepRmw_ful hx
       intro t ht hn
       obtain ⟨-, m, tr, mr, hm, -, -, hl, -⟩ := rem t ht hn
       exact ⟨m, hm, by rw [hl]; exact stepRmw_fulC hx t ht hn⟩)

/-- (Gap a) **An operation's fulfils are coherence points.** -/
theorem evalOp_fulC {op : Op} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s op) : FulC s r.1 := by
  cases op
  case spawn => simp [evalOp] at h
  case store => exact evalOp_store_fulC hlt h
  case xchg => exact evalOp_xchg_fulC hlt h
  case xchgAt => exact evalOp_xchgAt_fulC hlt h
  case xchgAtF => exact evalOp_xchgAtF_fulC hlt h
  case bufInit => exact evalOp_bufInit_fulC hlt h
  case stl => exact evalOp_stl_fulC hlt h
  case stlw => exact evalOp_stlw_fulC hlt h
  case fetch => exact evalOp_fetch_fulC h
  all_goals
    apply fulC_of_keep hlt
    simp only [evalOp] at h
    (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
    (repeat' (first | (split at h) | (dsimp only at h; split at h)))
    all_goals first
      | (simp at h; done)
      | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
         subst h
         first | exact KeepR.refl _ | exact keepR_fence | exact allocBuf_keep)
      | (simp only [List.mem_map] at h
         obtain ⟨x, hx, rfl⟩ := h
         first
           | exact keepR_eq (loadUnits_keep _ _ _ _ hx).1 (loadUnits_keep _ _ _ _ hx).2.2
           | exact storeUnits_keepTwo hx
           | exact alloc_keep hx)
      | (simp only [List.mem_flatMap, List.mem_map] at h
         obtain ⟨x, hx, y, hy, rfl⟩ := h
         exact (keepR_eq (projM_keep hx).1 (projM_keep hx).2.2).trans (injM_keep hy))
      | (simp only [List.mem_filterMap] at h
         obtain ⟨x, hx, h⟩ := h
         cases hn : numOf x.2 <;> simp [hn] at h
         subst h; exact keepR_eq (loadUnits_keep _ _ _ _ hx).1 (loadUnits_keep _ _ _ _ hx).2.2)
      | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
         subst h; dsimp only; exact allocBuf_keep)

end

theorem cas_fulC {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {pw nw : Word} {b : Address}
    {ew : WeakMem.Val} {acq rel : Bool} {x : Memory × Promises.Thread}
    (hx : x ∈ Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 b
      (.cas ew) (dataE 1 nw) [0] acq rel) (s'' : St) (hs : s''.promises = x.2.promises)
    (hv : s''.vs.coh = x.2.vs.coh) : FulC (stOf mem pairs th) s'' := by
  obtain ⟨-, -, rem⟩ := stepRmw_ful (mem' := x.1) (th' := x.2) hx
  intro t ht hn
  rw [hs] at hn
  obtain ⟨-, m, tr, mr, hm, -, -, hl, -⟩ := rem t ht hn
  exact ⟨m, hm, by rw [hv, hl]; exact stepRmw_fulC (mem' := x.1) (th' := x.2) hx t ht hn⟩

/-- (Gap a) **A thread step's fulfils are coherence points.** -/
theorem tstep_fulC {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hlt : ∀ t, t ∈ th.promises → t < mem.size) (hpp : ∀ t, t ∈ th.promises → t ∉ pairs)
    (h : r ∈ tstep g mem pairs th) : FulC (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact fulC_of_keep hlt (keepR_eq rfl rfl))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       have := enter_eqM he
       exact fulC_of_keep hlt (keepR_eq rfl this))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       have := enter_eqM he
       exact fulC_of_keep hlt (keepR_eq rfl this))
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_fulC hlt hx
         | exact cas_fulC hx _ rfl rfl
         | exact fulC_of_keep hlt (keepR_of (stepRmwPair_grow (x := x) hx).1
             (stepRmwPair_prom (mem' := x.1) (pairs' := x.2.1) (th' := x.2.2) hx hpp)))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact fulC_of_keep hlt ((keepR_eq (projM_keep hx).1 (projM_keep hx).2.2).trans (injM_keep hy)))

/-- (Gap a) A value of `T` has a number at a non-ghost `.word` component. -/
theorem vr_word_at {E : TEnv} {T : Ty} {o : Nat} {r : Idx} {P : Proto} {vals : List Word}
    (hv : ValOf E T vals) (hwc : wc T = some vals.length) (hat : AtOff T o (.word r P))
    (hg : P.ghost = false) : ∃ w k, vals[o]? = some w ∧ w.val = .num k := by
  obtain ⟨nn, hwcU, hle, hvrU, -⟩ := VR_at E.unsee hat hv.1 hv.2 hwc
  have hnn : nn = 1 := by simp [wc, accs_word hg, nWords, Acc.size] at hwcU; omega
  subst hnn
  have hlt : o < vals.length := by omega
  have hw : vals[o]? = some vals[o] := List.getElem?_eq_getElem hlt
  rw [take_one_drop hw] at hvrU
  simp only [VR] at hvrU
  obtain ⟨k, hk, -⟩ := hvrU.2 hg
  exact ⟨_, k, hw, by simpa using hk⟩

/-- (Gap a) **An own cell's coherence point at a non-ghost `.word` unit holds
a number** (`OwnOKP`'s `CellOK`; in a buffer, at a slot below the real count
`E.rc`: a planted slot's coherence point may be its placeholder). -/
theorem own_num {g : G} {E : TEnv} {s : St} {c : Cell} {t : Ts} {m : Msg} {r : Idx} {P : Proto}
    (hm : MemInv g E s) (hsto : E.sto m.loc.label = some c) (hown : c.owner = some E.tid)
    (hmt : s.mem[t]? = some m) (hc : s.vs.coh m.loc = t)
    (hat : AtOff c.ty m.loc.offset (.word r P)) (hg : P.ghost = false)
    (hini : IniAt E.rc c m.loc (.word r P)) : ∃ k, m.val = .num k := by
  obtain ⟨vals, hcell, hlat, -⟩ := hm.2.1 _ c hsto hown
  suffices hw : ∃ w k, vals[m.loc.offset]? = some w ∧ w.val = .num k by
    obtain ⟨w, k, hw, hk⟩ := hw
    obtain ⟨⟨m', hm', -, hv'⟩, -⟩ := hlat _ w hw
    have e : (⟨m.loc.label, m.loc.offset⟩ : Address) = m.loc := rfl
    rw [e, hc, hmt] at hm'
    cases hm'
    rcases hv' with ⟨hv', -⟩ | ⟨-, hty⟩
    · exact ⟨k, hv'.trans hk⟩
    · -- (F2) at a cell with a frontier the coherence message may be a typed word
      obtain ⟨k', hk', -⟩ := wordOK_good (T := c.ty) (o := m.loc.offset) hty hat hg
      exact ⟨k', by simpa [mw] using hk'⟩
  rcases hcell with ⟨hwc, hv⟩ | ⟨N, e, us, hT, hus, hnN, hlen, hj⟩
  · exact vr_word_at hv hwc hat hg
  · rcases hini N e hT with ⟨hU, -⟩ | ⟨us', j, o', hus', hjn, ho, hat'⟩
    · rw [hT] at hU; cases hU
    rw [hus] at hus'; cases hus'
    have hjN : j < N := Nat.lt_of_lt_of_le hjn hnN
    have hslot := hj j hjn
    have hmul : (j + 1) * nWords us ≤ N * nWords us := Nat.mul_le_mul_right _ hjN
    rw [Nat.succ_mul] at hmul
    have hwl : ((vals.drop (j * nWords us)).take (nWords us)).length = nWords us := by
      rw [List.length_take, List.length_drop, hlen]; omega
    obtain ⟨w, k, hw, hk⟩ := vr_word_at hslot (by simp [wc, hus, hwl]) hat' hg
    refine ⟨w, k, ?_, hk⟩
    rw [← ho]
    have hlt : o' < nWords us := by have := (List.getElem?_eq_some_iff.1 hw).1; omega
    rw [List.getElem?_take, List.getElem?_drop] at hw
    simpa [hlt] using hw

/-- **(Gap a) An own non-ghost word promise is a number**: an outstanding
promise at a non-ghost `.word` unit of an own cell `cl` of the start
environment (below the real count `rc`, if a buffer slot) holds a number.  The fulfilling
step makes it the thread's coherence point (`tstep_fulC`), where the owner's
invariant holds a number (`own_num`). -/
theorem certified_promNumX {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {E0 : TEnv} {Eu Ea : TEnv}
    [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch Eu Ea i c0)
    {n0 v0 : Nat} (h0 : InvAtX p k arch i E0 n0 v0 c (Ea := Ea) (Eu := Eu)) (hTA : TidAt i c E0) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m)
    {cl : Cell} {r : Idx} {P : Proto} (hcl : E0.sto m.loc.label = some cl) (hown : cl.owner = some E0.tid)
    (hat : AtOff cl.ty m.loc.offset (.word r P)) (hg : P.ghost = false)
    (hini : IniAt E0.rc cl m.loc (.word r P)) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : ∃ k, m.val = .num k := by
  obtain ⟨c1, c2, th1, th2, ρ, η, cx, E2, -, -, h2, -, hth1, hth2, -, -, -, -, -, hmi1, -, -, hx2, -, hm2i,
    hm1, hm2, ht1, hn2, -⟩ := certified_promTypedX hP hsc hvI hwin h0 hTA hc ht hm hPS hSub hSig
  obtain ⟨th', r', hth', hr, e1, -, e3, -⟩ := threadSteps_inv h2
  rw [hth1] at hth'
  cases hth'
  rw [hth2] at e3
  cases e3
  obtain ⟨m', hm', hcoh⟩ := tstep_fulC (MemInv_promLt hmi1) (MemInv_nopair hmi1) hr t ht1 hn2
  have hm1' : c1.mem[t]? = some m' := hm'
  rw [hm1] at hm1'
  cases hm1'
  exact own_num hm2i (hx2.2.2.2.2.1 _ _ hcl) (by rw [hx2.2.2.2.1]; exact hown) hm2 hcoh hat hg
    (IniAt_mono (TermSound.TEnv.rc_mono hx2.2.2.2.2.2.1 hx2.2.2.2.2.2.2.2.2.2.2.2) hini)

/-- **(Gap a) `certified_promWordX` without `undef`** at a non-ghost `.word`
unit of an own cell of the start environment. -/
theorem certified_promWordNX {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {E0 : TEnv} {Eu Ea : TEnv}
    [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch Eu Ea i c0)
    {n0 v0 : Nat} (h0 : InvAtX p k arch i E0 n0 v0 c (Ea := Ea) (Eu := Eu)) (hTA : TidAt i c E0) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ c2 th2 E2, Solo p k arch i c c2 ∧ Certified p k arch c2 i ∧ c2.ths[i]? = some th2 ∧ Ext E0 E2 ∧
      ThInvE p E2 th2 ∧ MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      ∀ cl r P, E0.sto m.loc.label = some cl → cl.owner = some E0.tid →
        AtOff cl.ty m.loc.offset (.word r P) → P.ghost = false → IniAt E0.rc cl m.loc (.word r P) →
        WordOK E2 cl.ty m.loc.offset (mw m) := by
  obtain ⟨c2, th2, E2, h1, h2, h3, h4, h5, h6, hok, -⟩ := certified_promWordX hP hsc hvI hwin h0 hTA hc ht hm hPS hSub hSig
  refine ⟨c2, th2, E2, h1, h2, h3, h4, h5, h6, fun cl r P hcl hown hat hg hini => ?_⟩
  rcases hok cl hcl with hu | hw
  · obtain ⟨n, hn⟩ := certified_promNumX hP hsc hvI hwin h0 hTA hc ht hm hcl hown hat hg hini hPS hSub hSig
    rw [hn] at hu; cases hu
  · exact hw

/-! ## S7f: `FlipOK` and the plant's type facts from the tied certificate -/

/-- **(S7f) `FlipOK` from the tied certificate** (as `FlipOK_of`, inlined for
the owner `Priv` gives): at a configuration `c` where thread `i` is certified
and its stage-A invariant holds at `CE η`, `certified_noPairPromX` excludes
`word2` units and `certified_promWordNX` gives the word (no `undef`: gap a),
given that every cell type of `CE η` is closed (`hSC`, gap b; gives the
literal region, `AtOff_word_lit`).  (S7f α) `FlipOK` asks only at initialised
addresses (`IniW`), which give `IniAt` (`IniAt_of_IniW`): no side condition
on initialisation remains: at a `Priv` cell the real count is `ini`
(`OwnHidP`'s second part). -/
theorem flipOK_cert {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {th : TTh} {η : TEnv}
    {l : AllocLabel} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch (CE η) (CE η) i c0)
    (hth : c.ths[i]? = some th) (hT : ThInvE p (CE η) th)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th)) (hc : Certified p k arch c i)
    (hSC : StoClo (CE η)) (hbo : (gOf p k arch c i).boxFence = true) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hrc : RiniCoh (CE η) (stOf c.mem c.pairs th))
    (hfl : ∀ l cl f, (CE η).sto l = some cl → (CE η).pfr l = some f → f ≤ c.mem.size - 1) (hTA : TidAt i c (CE η)) :
    FlipOK (CE η) (stOf c.mem c.pairs th) l := by
  have h0 := InvAtX_of hth hT hm hSC hbo hrc hfl
  have hpr : ∀ t, t ∈ th.promises → t ∈ promsOf c i := fun t ht => by rw [promsOf_some hth]; exact ht
  intro hpv t m ht hm' hl hwu hIW
  obtain ⟨c0, hc0, hown⟩ := hpv.1
  obtain ⟨cl, hcl, hw⟩ := hwu
  rw [hl] at hcl
  have hcl' : (CE η).sto m.loc.label = some cl := by rw [hl]; exact hcl
  rcases hw with ⟨r, P, hg, hat⟩ | ⟨r, P, hat⟩ | ⟨r, P, h1, hat⟩
  · rw [hc0] at hcl
    cases hcl
    obtain ⟨n, rfl⟩ := AtOff_word_lit hat (hSC _ c0 hc0) r P rfl
    have hi : IniAt η.ini c0 m.loc (.word (.lit n) P) := IniAt_of_IniW hcl' hat hIW
    obtain ⟨c2, th2, E2, -, -, -, -, -, -, hok⟩ := certified_promWordNX hP hsc hvI hwin h0 hTA hc (hpr t ht) hm' hPS hSub hSig
    have hi' : IniAt (CE η).rc c0 m.loc (.word (.lit n) P) := IniAt_monoAt (Nat.le_of_not_lt fun hlt => by
      obtain ⟨f, hf, -⟩ := hm.2.2.2.2.2.1.2 _ c0 hcl' hown hlt
      rw [hl, hpv.2] at hf; cases hf) hi
    obtain ⟨hp, v, hv, hin⟩ := wordOK_word (hok c0 _ P hcl' hown hat hg hi') hat hg
    exact ⟨c0, n, P, hc0, hat, hg, hi, hp, v, hv, hin⟩
  · exact absurd rfl (certified_noPairPromX hP hsc hvI hwin h0 hTA hc (hpr t ht) hm' hPS hSub hSig cl hcl' _ r P hat).1
  · exact absurd (Nat.sub_add_cancel h1).symm
      (certified_noPairPromX hP hsc hvI hwin h0 hTA hc (hpr t ht) hm' hPS hSub hSig cl hcl' _ r P hat).2

/-- **(S7f) The planted cell's type facts from the tied certificate**: an
outstanding promise of a reference to `a` in a cell of a `noOwn`,
region-free type in `E0` is fulfilled by a typed write; in the environment `E2`
after it (an extension of `E0`), memory's word there is `WordOK`, so `a`'s
cell has a frontier (`wordOK_locPub`), and `PubCpl` gives the cell's type — the
same `Cell` as in `E0` — its layout and coupling facts. -/
theorem plant_typeFacts {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {E0 : TEnv} {Eu Ea : TEnv}
    [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch Eu Ea i c0)
    {n0 v0 : Nat} (h0 : InvAtX p k arch i E0 n0 v0 c (Ea := Ea) (Eu := Eu)) (hTA : TidAt i c E0) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ promsOf c i) (hm : c.mem[t]? = some m)
    {ca : Cell} (hca : E0.sto m.loc.label = some ca) (hno : Ty.noOwnIn [] ca.ty = true)
    (hrf : rgnFree ca.ty = true) {a : Address} {g : Nat} (hv : m.val = .loc a g) {cl : Cell}
    (hcl : E0.sto a.label = some cl) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    LayT cl.ty ∧ (∀ b S, SegOf cl.ty b S → accs S ≠ none → TearOK S) ∧ Ty.coupledOKIn [] cl.ty = true ∧
      Ty.noOwnIn [] cl.ty = true ∧ rgnFree cl.ty = true := by
  obtain ⟨c2, th2, E2, -, -, -, hx2, -, hm2, hok, -⟩ := certified_promWordX hP hsc hvI hwin h0 hTA hc ht hm hPS hSub hSig
  rcases hok ca hca with hu | hw
  · rw [hv] at hu; cases hu
  rcases wordOK_locPub hw hno hrf hv with ⟨c', f, hsto, hf⟩ | ⟨B, hB⟩
  rotate_left
  · have := (hm2.2.2.2.2.2.2.2.2.2.1.2.2 _ B hB).1
    rw [hx2.2.2.2.2.1 _ _ hcl] at this
    cases this
  rw [hx2.2.2.2.2.1 _ _ hcl] at hsto
  cases hsto
  exact hm2.2.2.2.2.2.2.2.2.1.2.2.1 a.label cl f (hx2.2.2.2.2.1 _ _ hcl) hf

/-- **(S7f) The plant's side condition (`hpl` of `ThInvMC_plant`) at one
environment, from the tied certificate**: at a certified configuration whose
thread has the stage-A invariant at `CE η`, an outstanding promise of a
reference to a private own cell `a.label`, in a cell of a `noOwn`,
region-free type, gives the
type facts (`plant_typeFacts`) and `FlipOK` (`flipOK_cert`).  (S7f α) No
initialisation side condition: the closedness of cell types is the
environment invariant `StoClo` (gap b, kept by every step: `StoClo_EFoot`). -/
theorem plant_hpl {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {th : TTh} {η : TEnv}
    [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch (CE η) (CE η) i c0)
    (hth : c.ths[i]? = some th) (hT : ThInvE p (CE η) th)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th)) (hc : Certified p k arch c i)
    {t : Ts} {m : Msg} (ht : t ∈ th.promises) (hmt : c.mem[t]? = some m)
    {ca : Cell} (hca : η.sto m.loc.label = some ca) (hno : Ty.noOwnIn [] ca.ty = true)
    (hrf : rgnFree ca.ty = true) {a : Address} {g : Nat} (hv : m.val = .loc a g) {cl : Cell}
    (hcl : η.sto a.label = some cl) (hown : cl.owner = some η.tid) (hnone : η.pfr a.label = none)
    (hSC : StoClo (CE η)) (hbo : (gOf p k arch c i).boxFence = true) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hrc : RiniCoh (CE η) (stOf c.mem c.pairs th))
    (hfl : ∀ l cl f, (CE η).sto l = some cl → (CE η).pfr l = some f → f ≤ c.mem.size - 1) (hTA : TidAt i c (CE η)) :
    ∃ c', η.sto a.label = some c' ∧ c'.owner = some η.tid ∧ η.pfr a.label = none ∧
      (∀ b S, SegOf c'.ty b S → accs S ≠ none → TearOK S) ∧ Ty.coupledOKIn [] c'.ty = true ∧
      Ty.noOwnIn [] c'.ty = true ∧ rgnFree c'.ty = true ∧ FlipOK (CE η) (stOf c.mem c.pairs th) a.label := by
  have h0 := InvAtX_of hth hT hm hSC hbo hrc hfl
  have ht' : t ∈ promsOf c i := by rw [promsOf_some hth]; exact ht
  obtain ⟨-, h2, h3, h4, h5⟩ := plant_typeFacts hP hsc hvI hwin h0 hTA hc ht' hmt hca hno hrf hv hcl hPS hSub hSig
  exact ⟨cl, hcl, hown, hnone, h2, h3, h4, h5, flipOK_cert hP hsc hvI hwin hth hT hm hc hSC hbo hPS hSub hSig hrc hfl hTA⟩

#print axioms certified_promAboveSt
#print axioms scopeD_SW
#print axioms taken_promAbove
#print axioms PAx_of_step
#print axioms certified_next
#print axioms ThInvM_promise_tr
#print axioms solo_typedL
#print axioms solo_typedW
#print axioms solo_typedP
#print axioms certified_promTyped
#print axioms certified_promWordOK
#print axioms certified_noPairPromT
#print axioms certified_promWordT
#print axioms SWOne_holds
#print axioms wordOK_good
#print axioms pwf_of_inv
#print axioms certified_noPairPromS
#print axioms certified_promWordS
#print axioms certified_noPairPromP
#print axioms certified_promWordP
#print axioms InvAtX_of
#print axioms solo_typedX
#print axioms certified_promTypedX
#print axioms certified_promWordX
#print axioms certified_noPairPromX
#print axioms wordOK_one
#print axioms wordOK_word
#print axioms Fd_Clo
#print axioms wordOK_pubRef
#print axioms locPub_encRev
#print axioms locPub_encFwd
#print axioms locPub_ofArmRev
#print axioms locPub_push0_rels
#print axioms locPub_mem_val
#print axioms locPub_VR
#print axioms wordOK_locPub
#print axioms AtOff_word_lit
#print axioms IniAt_nonbuf
#print axioms flipOK_cert
#print axioms plant_typeFacts
#print axioms plant_hpl
#print axioms storeUnits_fulC
#print axioms evalOp_fulC
#print axioms tstep_fulC
#print axioms own_num
#print axioms certified_promNumX
#print axioms certified_promWordNX
#print axioms StoClo_EFoot
#print axioms WrUp.trans
#print axioms loadUnits_wrUp
#print axioms storeUnits_wrUp
#print axioms alloc_wrUp
#print axioms allocBuf_wrUp
#print axioms rmw_wrUp
#print axioms rmwPair_wrUp
#print axioms evalOp_wrUp
#print axioms enter_wrUp
#print axioms tstep_wrUp
#print axioms FrBound_refl
#print axioms FrBound_foot
#print axioms IniLoc_foot
#print axioms IniHeld_foot
#print axioms witP_run
#print axioms oneAt_append
#print axioms oneAt_single
#print axioms nWords_eq_one
#print axioms oneAt_not_two
#print axioms nu_nil
#print axioms nu_two
#print axioms nu_single
#print axioms accs_iex_cases
#print axioms accs_tex_cases
#print axioms decodeArm_head
#print axioms VR_one_nundef
#print axioms useVal_cl
#print axioms nu_num
#print axioms cell_nu
#print axioms store_nu
#print axioms xchg_nu
#print axioms xchgAt_nu
#print axioms xchgAtF_nu
#print axioms bufInit_nu
#print axioms unitsOp_nu
#print axioms cas_nu
#print axioms SW_nundef
#print axioms certified_promNotUndefX
#print axioms fetch_ful_core
#print axioms fetch_ful_numP
#print axioms fetch_ful_numL
#print axioms fetch_ful_num
#print axioms swAt_of_ua
#print axioms cell_ua
#print axioms store_ua
#print axioms xchg_ua
#print axioms xchgAt_ua
#print axioms xchgAtF_ua
#print axioms bufInit_ua
#print axioms stl_ua
#print axioms stlw_ua
#print axioms unitsOp_ua
#print axioms unitsOp_sw

/-! ## (F2′) The own-handle key along the typed run (`solo_ownZero`)

Once thread `i`'s frame and memory's holding carry no own-handle key of a
label `x` already in Σ, no later configuration of the solo run gives one
back: only an allocation mints `own x`, at a label not yet in Σ
(`MintStep_own_sto`); promise credits and debits never carry own keys
(`WRes` holds only region keys).  The step lemmas' side conditions are
run-level hypotheses (`OwnSide`, `PromSide`), as `ScopeAt` is for
`solo_typedL`. -/

theorem VRes_own_zero {E : TEnv} {a : Address} {w : Word} {R : Res} (h : VRes E a w R) (l : Nat) :
    R (.own l) = 0 := by
  rcases h with ⟨-, -, ⟨n, P, -, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, rfl⟩ <;> simp

theorem DbRes_own_zero {E : TEnv} {mem : Memory} {m : Msg} {tw : Ts} {R : Res}
    (h : DbRes E mem m tw R) (l : Nat) : R (.own l) = 0 := by
  rcases h with ⟨hV, hI, h3, h4⟩ | ⟨-, rfl⟩
  · by_cases hi : InitAt mem m.loc tw
    · obtain ⟨R₁, Z, hF, hS, hZ, rfl⟩ := h3 hi
      have hZo : Z (.own l) = 0 := by
        by_cases hd : DesigAt E mem m.loc tw
        · obtain ⟨Zb, Zz, -, -, rfl⟩ := hS hd
          exact noOwnR_own _ l
        · rw [hZ hd]; rfl
      have hR1 : R₁ (.own l) = 0 := by
        rcases hF with ⟨n, P, -, rfl⟩ | ⟨-, rfl⟩
        · simp only [Res.add_apply, wr, wdW]
          split <;> split <;> simp
        · rfl
      simp only [Res.add_apply, hZo, hR1]
    · exact VRes_own_zero (Or.inl ⟨hV, hI, h4 hi⟩) l
  · rfl

theorem sum_map_key_zero {f : Ts → Res} {k : Key} :
    ∀ {L : List Ts}, (∀ t, t ∈ L → f t k = 0) → Res.sum (L.map f) k = 0
  | [], _ => rfl
  | t :: L, h => by
      simp only [List.map_cons, Res.sum_cons, Res.add_apply]
      rw [h t (List.mem_cons_self ..), sum_map_key_zero (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]

/-- (F2′) Promise credits and debits carry no own-handle key. -/
theorem PromCr_own_zero {E : TEnv} {s : St} {cr db : Ts → Res} (h : PromCr E s cr db) (l : Nat) :
    pSum s cr (.own l) = 0 ∧ pSum s db (.own l) = 0 := by
  refine ⟨sum_map_key_zero fun t ht => ?_, sum_map_key_zero fun t ht => ?_⟩
  · obtain ⟨m, -, -, ⟨w, -, hw⟩ | ⟨-, hz⟩⟩ := h t ht
    · exact VRes_own_zero hw l
    · rw [hz]; rfl
  · obtain ⟨m, -, hd, -⟩ := h t ht
    exact DbRes_own_zero hd l

/-- (F2′) The side conditions of `tstepMCF_step` at a thread state, at every
typing of its frame: the scope (`hsc`), `hia`, `hdw` (`StoreDwf`), `hnvp`
(`OwnNVP`), `hwp` (`FlipOK` at a publish), `hfo` (`FpOK`), `hRF`
(`OwnFrontierRMW`), `hrmw` (`NoPlantRMW`). -/
def OwnSide (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) : Prop :=
  ∀ ρ η cx Rf Rs, EnvOK p η → Typed p cx th.term → TvOK cx →
    FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf → MemInv g (CE η) (stOf mem pairs th) →
    (StepScope cx th.term ∨ StepScopeR th.σs cx th.term) ∧
    StoreIall ρ η cx th ∧
    StoreCrZ η cx (stOf mem pairs th) th ∧ OwnNVP (CE η) (stOf mem pairs th) ∧
    (∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → FlipOK (CE η) (stOf mem pairs th) ad.label) ∧
    PubWinT (CE η) (stOf mem pairs th) th ∧
    FpOK (CE η) (stOf mem pairs th) ∧ OwnFrontierRMW (CE η) (stOf mem pairs th) ∧ NoPlantRMW (CE η) th ∧
    (∀ H, MemHeld (CE η) (stOf mem pairs th) H → PubLe1 th Rf Rs H)

/-- (F2′) The side conditions of `tstepMC_prom` (`hwu`, and (U3) `hfw`: a
predicted unit has a first write) for a promise of `v` at `a` with view `w`. -/
def PromSide (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (a : Address)
    (v : WeakMem.Val) (w : Ts) : Prop :=
  (∀ (η : TEnv) Tot, ThInvRE p (CE η) th Tot → MemInv g (CE η) (stOf mem pairs th) → VisU (CE η) a →
    ∃ c n P, η.sto a.label = some c ∧ AtOff c.ty a.offset (.word (.lit n) P) ∧
      P.ghost = false ∧ IniAt η.ini c a (.word (.lit n) P) ∧
      ∃ Rn, VRR (fun _ => 0) (CE (CE η).unsee) (.word (.lit n) P) (shp (.word (.lit n) P)) [mw ⟨a, v, w⟩] Rn) ∧
  ∀ (η : TEnv) Tot, ThInvRE p (CE η) th Tot → MemInv g (CE η) (stOf mem pairs th) → PredU (CE η) a →
    ∃ h, FirstW mem a h

/-- (F2′) Thread `i` of `c` satisfies the resourceful invariant (`ThInvMC`,
witness `E`), `x` is in Σ, and neither the frame nor memory's holding
carries `own x`. -/
def OwnZeroAt (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (x : AllocLabel) (c : Cfg) : Prop :=
  ∃ th, c.ths[i]? = some th ∧ ∃ E Tot H cr db, ThInvRE p E th Tot ∧
    MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧ MemHeld E (stOf c.mem c.pairs th) H ∧
    TermPlant.PromCrK E (stOf c.mem c.pairs th) cr db ∧ E.sto x ≠ none ∧ Tot (.own x) + H (.own x) = 0

/-- **(F2′) No own handle of `x` comes back along the solo run.**  From a
configuration where thread `i`'s frame and memory's holding carry no
`own x` (e.g. right after `publish` consumed `x`'s handle, `MintStep.consume`),
every certified configuration reached keeps the resourceful invariant with
no `own x`.  Run-level hypotheses: `hside` (`OwnSide`, at every certified
configuration reached) and `hprom` (`PromSide`, at every promise step taken);
`hn`, `hbf` at the start (`gOf` is constant along the run). -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem solo_ownZero {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} {c : Cfg}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hn : 0 < (gOf p k arch c i).n) (hbf : (gOf p k arch c i).boxFence = true)
    (hside : ∀ c0 th, Solo p k arch i c c0 → Certified p k arch c0 i → c0.ths[i]? = some th →
      OwnSide p (gOf p k arch c0 i) c0.mem c0.pairs th)
    (hprom : ∀ c0 th a v w, Solo p k arch i c c0 → w < c0.mem.size → Certified p k arch (promise c0 i a v w) i →
      c0.ths[i]? = some th → PromSide p (gOf p k arch c0 i) c0.mem c0.pairs th a v w)
    (h0 : OwnZeroAt p k arch i x c) (hnb : NoBoxedCur p k arch i c) {c2 : Cfg} (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    OwnZeroAt p k arch i x c2 := by
  refine (run_inv (c1 := c2)
    (P := fun c0 => Solo p k arch i c c0 ∧ gOf p k arch c0 i = gOf p k arch c i ∧ OwnZeroAt p k arch i x c0)
    ?_ ?_ ?_ h (.refl _) ⟨.refl _, rfl, h0⟩).2.2
  · rintro c0 c0' ⟨hc0, hg0, th, hth, E, Tot, H, cr, db, hT, hm, hH, hC, hx, hz⟩ hs hrest
    have hc0' : Certified p k arch c0' i := certified_back hrest hc2
    have hcert0 : Certified p k arch c0 i := certified_back (.thread hs hrest) hc2
    obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc0'
    rw [hth] at hth'
    cases hth'
    obtain ⟨ρ, η, cx, Rf, Rs, rfl, hE, hTy, htv, hFI, hsum, hRP⟩ := hT
    obtain ⟨hsc, hia, hdw, hnvp, hwp, hwin, hfo, hRF, hrmw, hpl⟩ := hside c0 th hc0 hcert0 hth ρ η cx Rf Rs hE hTy.1 htv hFI hm
    have hown1 := hpl H hH
    obtain ⟨Tot', H', C, F, cr', db', ⟨E', hfoot, hSK, hBV, hT', hm', hH', hC'⟩, hM, -, hle⟩ :=
      (tstepMCF_step hP rfl (by rw [hg0]; exact hn) (tstep_notDone hr) hsc hTy.1 hTy.2 hFI hE htv hm hH
        (PAx_of_step hs hc0' hth) (PromCrP_drop hC.toP) hia hdw (fun _ => OwnNVPF_of hnvp) hwp hwin hfo (fun _ => hRF) hrmw (by rw [hg0]; exact hbf) hRP hPS hSub hSig).2 r hr hpa
    have hg' : gOf p k arch c0' i = gOf p k arch c0 i := gOf_thread hs
    have hst : stOf c0'.mem c0'.pairs r.2.2 = stOf r.1 r.2.1 r.2.2 := by rw [e1, e2]
    refine ⟨solo_trans hc0 (.thread hs (.refl _)), hg'.trans hg0, r.2.2, e3, E', Tot', H', cr', db', hT',
      by rw [hg', hst]; exact hm', by rw [hst]; exact hH', by rw [hst]; exact TermPlant.PromCrK_of hC', ?_, ?_⟩
    · rcases hfoot.2.2.1 x with e | ⟨-, T, e, -⟩
      · rw [e]; exact hx
      · rw [e]; exact fun h => by cases h
    · have hF : F (.own x) = 0 := Classical.byContradiction fun hF => hx (MintStep_own_sto hM hF)
      have h1 := Res.le_def.1 hle (.own x)
      have h2 := congrArg (fun R : Res => R (.own x)) hsum
      have z1 := PromCr_own_zero (PromCrP_drop hC.toP) x
      have z2 := PromCr_own_zero hC' x
      simp only [Res.add_apply] at h1 h2
      omega
  · rintro c0 a v w ⟨hc0, hg0, th, hth, E, Tot, H, cr, db, hT, hm, hH, hC, hx, hz⟩ hw hrest
    have hcp : Certified p k arch (promise c0 i a v w) i := certified_back hrest hc2
    have hwu := hprom c0 th a v w hc0 hw hcp hth
    obtain ⟨ρ, η, cx, Rf, Rs, rfl, hrest'⟩ := hT
    obtain ⟨H', cr', db', -, hH', hC', heq⟩ :=
      promise_acct hH (PromCrP_drop hC.toP) (MemInv_promLt hm) (hwu.1 η Tot ⟨ρ, η, cx, Rf, Rs, rfl, hrest'⟩ hm)
        (hwu.2 η Tot ⟨ρ, η, cx, Rf, Rs, rfl, hrest'⟩ hm)
    have hpi := promise_inv (a := a) (v := v) (w := w) hth
    refine ⟨solo_trans hc0 (.prom a v w hw (.refl _)), gOf_promise.trans hg0, _, hpi.2.1, CE η, Tot, H', cr', db',
      ⟨ρ, η, cx, Rf, Rs, rfl, hrest'⟩, by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm,
      by rw [hpi.2.2]; exact hH', by rw [hpi.2.2]; exact TermPlant.PromCrK_of hC', hx, ?_⟩
    have h1 := congrArg (fun R : Res => R (.own x)) heq
    have z1 := PromCr_own_zero (PromCrP_drop hC.toP) x
    have z2 := PromCr_own_zero hC' x
    simp only [Res.add_apply] at h1
    omega
  · rintro c0 c0' ⟨hc0, hg0, th, hth, E, Tot, H, cr, db, hT, hm, hH, hC, hx, hz⟩ hs _
    rcases extSteps_res hs hth with ⟨x1, n1, a1, e1, rt1, ws1, rs1, hterm, hn1, hev1, hrs1, rfl⟩ | ⟨x1, a1, e1, lb, hterm, htl, -⟩
    · exact ⟨solo_trans hc0 (.ext hs (.refl _)), (gOf_ext hs).trans hg0, _, set_self hth, E, Tot, H, cr, db,
        ThInvRE_ext hn1 hterm hev1 hrs1 hT, by rw [gOf_ext hs]; exact hm, hH, hC, hx, hz⟩
    · rw [hnb c0 hc0 th hth _ _ _ hterm] at htl; cases htl

#print axioms VRes_own_zero
#print axioms DbRes_own_zero
#print axioms sum_map_key_zero
#print axioms PromCr_own_zero
#print axioms solo_ownZero


/-! ## (F2′) `publish` consumes the own handle; no own-mode use reaches it after

`publish_ownZero`: the publish step through an own handle to `x` leaves
`own x` nowhere in the frame or memory's holding, given the global bound
`Tot (own x) + H (own x) ≤ 1` (`SysInvW.own_thread`).  `use_own_ne`: an
own-mode use (`cellOf`/`bufOf` mode `.own`) in a frame without `own x` does not
resolve to a handle of `x`.  `ownZeroAt_use_ne` combines them at an
`OwnZeroAt` configuration. -/

/-- (F2′) **The publish step consumes `x`'s own key.**  Thread `i` of `c`
publishes `a`, whose handle points into `x`; at the certified successor, the
frame and memory's holding carry no `own x` and `x` stays in Σ. -/
theorem publish_ownZero {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel}
    {c c' : Cfg} (hP : ProgT p) (hs : c' ∈ threadSteps p k arch c i) (hc' : Certified p k arch c' i)
    {th : TTh} (hth : c.ths[i]? = some th) {y : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ y (.publish a) e)
    {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat} (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad g']) (hx : ad.label = x)
    {E : TEnv} {Tot H : Res} {cr db : Ts → Res} (hT : ThInvRE p E th Tot)
    (hm : MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th)) (hH : MemHeld E (stOf c.mem c.pairs th) H)
    (hC : TermPlant.PromCrK E (stOf c.mem c.pairs th) cr db) (h1 : Tot (.own x) + H (.own x) ≤ 1)
    (hside : OwnSide p (gOf p k arch c i) c.mem c.pairs th) (hPS : PwSkel) :
    OwnZeroAt p k arch i x c' := by
  obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc'
  rw [hth] at hth'
  cases hth'
  obtain ⟨ρ, η, cx, Rf, Rs, rfl, hE, hTy, htv, hFI, hsum, hRP⟩ := hT
  obtain ⟨hsc, -, -, -, hwp, hwin, hfo, -, -, hpl⟩ := hside ρ η cx Rf Rs hE hTy.1 htv hFI hm
  have hown1 := hpl H hH
  have hps : PubScope cx a := by
    rcases hsc with h | h <;> rw [hterm] at h
    · exact h
    · exact h.elim
  obtain ⟨Sp, hHL⟩ := hH.toS
  obtain ⟨Tot', H', cr', db', rt', ws', hea', hsto, ⟨E', hfoot, hSK, hBV, hT', hm', hH', hC'⟩, hle⟩ :=
    (tstepMR_publish hterm hP hTy.1 hTy.2 hFI hE htv hm hHL hps (PromCrP_drop hC.toP)
      (fun rt ws ad h1 h2 => hwp _ _ _ rt ws ad hterm h1 h2)
      (fun rt ws ad h1 h2 => hwin _ _ _ rt ws ad hterm h1 h2) hfo hRP hPS).2 r hr hpa
  rw [hea] at hea'
  cases hea'
  have hst : stOf c'.mem c'.pairs r.2.2 = stOf r.1 r.2.1 r.2.2 := by rw [e1, e2]
  have hg' : gOf p k arch c' i = gOf p k arch c i := gOf_thread hs
  subst hx
  refine ⟨r.2.2, e3, E', Tot', H', cr', db', hT', by rw [hg', hst]; exact hm', by rw [hst]; exact hH'.memHeld,
    by rw [hst]; exact TermPlant.PromCrK_of hC', ?_, ?_⟩
  · rcases hfoot.2.2.1 ad.label with e | ⟨-, T, e, -⟩
    · rw [e]; exact hsto ad g' hws
    · rw [e]; exact fun h => by cases h
  · have h2 := Res.le_def.1 hle (.own ad.label)
    have h3 := congrArg (fun R : Res => R (.own ad.label)) hsum
    have z1 := PromCr_own_zero (PromCrP_drop hC.toP) ad.label
    have z2 := PromCr_own_zero hC' ad.label
    rw [ownW_own_loc hws] at h2
    simp only [Res.add_apply, Res.one, ite_true] at h1 h2 h3
    omega

/-- (F2′) **An own-mode use does not reach a consumed label.**  In a frame
without `own x`, a use at a cell or buffer type of mode `.own` resolves to a
handle of a label other than `x`. -/
theorem use_own_ne {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → Nat → List Word → Res → Prop} {cx c₁ : Cx} {env : Env} {a : At} {t : Ty} {Rf : Res}
    {x : AllocLabel} (hu : cx.use a = .ok (t, c₁)) (hi : FInvR ρ η σs K cx env Rf) (hE : EnvOK p η)
    (ht : (∃ u, cellOf t = some (.own, u)) ∨ ∃ n u k, bufOf t = some (.own, n, u, k))
    (h0 : Rf (.own x) = 0) {rt : Ty} {ws : List Word} {ad : Address} {g : Nat}
    (hea : evalAt env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad g]) : ad.label ≠ x := by
  obtain ⟨rt', ws', R, Rr, hea', -, -, hvR, -, hle⟩ := useR hu hi hE.2.2
  rw [hea] at hea'
  cases hea'
  have hR : R = ownW .own ws := by
    rcases ht with ⟨u, hc⟩ | ⟨n, u, k, hc⟩
    · exact VRR_cell_R hc hvR
    · exact VRR_buf_R hc hvR
  rw [hR, ownW_own_loc hws] at hle
  rintro rfl
  have h1 := Res.le_def.1 hle (.own ad.label)
  simp only [Res.add_apply, Res.one, ite_true] at h1
  omega

/-- (F2′, P2) **At an `OwnZeroAt` configuration no own-mode use of the
invariant's typing reaches `x`** (e.g. no `bufInit` writes through `x`'s own
handle). -/
theorem ownZeroAt_use_ne {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel}
    {c : Cfg} (h : OwnZeroAt p k arch i x c) :
    ∃ th, c.ths[i]? = some th ∧ ∃ ρ η cx Rf Rs, EnvOK p η ∧ Typed p cx th.term ∧
      FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧
      ∀ a t c₁ rt ws ad g, cx.use a = .ok (t, c₁) →
        ((∃ u, cellOf t = some (.own, u)) ∨ ∃ n u k, bufOf t = some (.own, n, u, k)) →
        evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad g] → ad.label ≠ x := by
  obtain ⟨th, hth, E, Tot, H, cr, db, ⟨ρ, η, cx, Rf, Rs, rfl, hE, hTy, -, hFI, hsum, -⟩, -, -, -, -, hz⟩ := h
  have h0 : Rf (.own x) = 0 := by
    have h3 := congrArg (fun R : Res => R (.own x)) hsum
    simp only [Res.add_apply] at h3
    omega
  exact ⟨th, hth, ρ, η, cx, Rf, Rs, hE, hTy.1, hFI, fun a t c₁ rt ws ad g hu ht hea hws =>
    use_own_ne hu hFI hE ht h0 hea hws⟩

/-- (F2′, P2) **After `publish`, no own-mode use reaches `x` along the
certifying run.**  `publish_ownZero` then `solo_ownZero`. -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem publish_noOwnUse {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel}
    {c c1 : Cfg} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hs : c1 ∈ threadSteps p k arch c i)
    {th : TTh} (hth : c.ths[i]? = some th) {y : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ y (.publish a) e)
    {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat} (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad g']) (hx : ad.label = x)
    {E : TEnv} {Tot H : Res} {cr db : Ts → Res} (hT : ThInvRE p E th Tot)
    (hm : MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th)) (hH : MemHeld E (stOf c.mem c.pairs th) H)
    (hC : TermPlant.PromCrK E (stOf c.mem c.pairs th) cr db) (h1 : Tot (.own x) + H (.own x) ≤ 1)
    (hside0 : OwnSide p (gOf p k arch c i) c.mem c.pairs th)
    (hn : 0 < (gOf p k arch c i).n) (hbf : (gOf p k arch c i).boxFence = true)
    (hside : ∀ c0 th, Solo p k arch i c1 c0 → Certified p k arch c0 i → c0.ths[i]? = some th →
      OwnSide p (gOf p k arch c0 i) c0.mem c0.pairs th)
    (hprom : ∀ c0 th a v w, Solo p k arch i c1 c0 → w < c0.mem.size → Certified p k arch (promise c0 i a v w) i →
      c0.ths[i]? = some th → PromSide p (gOf p k arch c0 i) c0.mem c0.pairs th a v w)
    {c2 : Cfg} (h12 : Solo p k arch i c1 c2) (hc2 : Certified p k arch c2 i) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hnb : NoBoxedCur p k arch i c1) :
    ∃ th, c2.ths[i]? = some th ∧ ∃ ρ η cx Rf Rs, EnvOK p η ∧ Typed p cx th.term ∧
      FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧
      ∀ a t c₁ rt ws ad g, cx.use a = .ok (t, c₁) →
        ((∃ u, cellOf t = some (.own, u)) ∨ ∃ n u k, bufOf t = some (.own, n, u, k)) →
        evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad g] → ad.label ≠ x := by
  have hc1 : Certified p k arch c1 i := certified_back h12 hc2
  have hg : gOf p k arch c1 i = gOf p k arch c i := gOf_thread hs
  exact ownZeroAt_use_ne (solo_ownZero hP (by rw [hg]; exact hn) (by rw [hg]; exact hbf) hside hprom
    (publish_ownZero hP hs hc1 hth hterm hea hws hx hT hm hH hC h1 hside0 hPS) hnb h12 hc2 hPS hSub hSig)

#print axioms publish_ownZero
#print axioms use_own_ne
#print axioms ownZeroAt_use_ne
#print axioms publish_noOwnUse

/-! ## (F2′ b″) The held prefix from the certificate

A planting promise `B` (view `w` below the plant's memory size) is fulfilled in
the certificate only after the planted cell `x` is published.  At that publish
`vWr ≤ w` (`plant_pub_window`, P1).  Every unit of `x` the real count newly
covers during the run was written at an index at most `vWr` there
(`EFoot.riniW`): a new message — impossible, it is at or above the plant's
size — or one of the thread's promises, which (`WinInv`) is a promise of the
plant's configuration.  So, below the real count at the publish, every unit of
`x` past the start's reader-visible count is held by a promise outstanding at
the plant (`certified_prefixHeld`). -/

/-- (F2′ b″) Every unit of buffer `l` that `E`'s real count covers beyond
`E0`'s reader-visible count was written at an index `≤ v`: at or above
`mem0`'s size, or one of the promises `P0` at that unit. -/
def RiniHeld (E0 : TEnv) (mem0 : Memory) (P0 : List Ts) (l : AllocLabel) (c : Cell) (E : TEnv) (v : Nat) :
    Prop :=
  ∀ N e us, c.ty = .array (.lit N) e → accs e = some us → ∀ o, o < E.rini l * nWords us →
    ¬ o < E0.ini l * nWords us →
    ∃ τ, τ ≤ v ∧ (mem0.size ≤ τ ∨ (τ ∈ P0 ∧ ∃ m, mem0[τ]? = some m ∧ m.loc = ⟨l, o⟩))

/-- (F2′ b″) `InvAtX` with `RiniHeld` at the same environment. -/
def InvAtXR (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (E0 : TEnv) (n0 v0 : Nat)
    (mem0 : Memory) (P0 : List Ts) (l : AllocLabel) (cl : Cell) (c : Cfg) : Prop :=
  ∃ th E, c.ths[i]? = some th ∧ Ext E0 E ∧ ThInvE p E th ∧ MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧
    StoClo E ∧ (gOf p k arch c i).boxFence = true ∧ FrBound E0 n0 v0 E ∧ FrRunA E0 n0 v0 E (stOf c.mem c.pairs th) ∧
    RiniHeld E0 mem0 P0 l cl E th.vs.vWr

/-- (F2′ b″) A promise step keeps `InvAtXR` (environment and `vWr` unchanged). -/
theorem InvAtXR_prom {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 : TEnv} {n0 v0 : Nat}
    {mem0 : Memory} {P0 : List Ts} {l : AllocLabel} {cl : Cell} {c0 : Cfg} {a : Address} {v : WeakMem.Val} {w : Ts}
    (h : InvAtXR p k arch i E0 n0 v0 mem0 P0 l cl c0) :
    InvAtXR p k arch i E0 n0 v0 mem0 P0 l cl (promise c0 i a v w) := by
  obtain ⟨th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hrh⟩ := h
  refine ⟨_, E, (promise_inv (a := a) (v := v) (w := w) hth).2.1, hx, hTE, ?_, hSC,
    by rw [gOf_promise]; exact hbo, hfb, ?_, hrh⟩
  · rw [gOf_promise, (promise_inv (a := a) (v := v) (w := w) hth).2.2]
    exact MemInv_promSt hm
  · exact frRunA_prom hth hfr

/-- An extern move keeps `InvAtXR` (environment and `vWr` unchanged). -/
theorem InvAtXR_ext {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 : TEnv} {n0 v0 : Nat}
    {mem0 : Memory} {P0 : List Ts} {l : AllocLabel} {cl : Cell} {c0 c0' : Cfg}
    (h : InvAtXR p k arch i E0 n0 v0 mem0 P0 l cl c0) (hs : c0' ∈ extSteps c0 i) (hTA : TidAt i c0 E0) :
    InvAtXR p k arch i E0 n0 v0 mem0 P0 l cl c0' := by
  obtain ⟨th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hrh⟩ := h
  rcases extSteps_res hs hth with ⟨x1, n1, a1, e1, rt1, ws1, rs1, hterm, hn1, hev1, hrs1, rfl⟩ | ⟨x1, a1, e1, lb, hterm, htl, rfl⟩
  · exact ⟨_, E, set_self hth, hx, ThInvE_ext hn1 hterm hev1 hrs1 hTE, by rw [gOf_ext hs]; exact hm, hSC,
      by rw [gOf_ext hs]; exact hbo, hfb, hfr, hrh⟩
  · obtain ⟨hbs, hbp⟩ := tidBox_ext hx (hTA th hth lb htl)
    exact ⟨_, E, set_self (tr := c0.trace) hth, hx, ThInvE_cur hterm hbs hbp hTE, by rw [gOf_ext hs]; exact hm, hSC,
      by rw [gOf_ext hs]; exact hbo, hfb, hfr, hrh⟩

/-- (F2′ b″) **The typed run, tied, with `RiniHeld`** (`solo_typedX`), from a
configuration `c` after `cP` (`WinInv cP i c`; `mem0`, `P0` are `cP`'s memory
and thread `i`'s promises there). -/
theorem solo_typedXR {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {cP c : Cfg} {E0 : TEnv}
    {n0 v0 : Nat} {thP : TTh} {l : AllocLabel} {cl : Cell} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (hthP : cP.ths[i]? = some thP) (hpl : ∀ t, t ∈ thP.promises → t < cP.mem.size)
    (hcl : E0.sto l = some cl) (hW : WinInv cP i c)
    (h0 : InvAtXR p k arch i E0 n0 v0 cP.mem thP.promises l cl c) (hTA : TidAt i c E0) {c2 : Cfg} (h : Solo p k arch i c c2)
    (hc2 : Certified p k arch c2 i) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    InvAtXR p k arch i E0 n0 v0 cP.mem thP.promises l cl c2 := by
  refine (run_inv (c1 := c2)
    (P := fun c0 => Solo p k arch i c c0 ∧ InvAtXR p k arch i E0 n0 v0 cP.mem thP.promises l cl c0) ?_ ?_ ?_ h
    (.refl _) ⟨.refl _, h0⟩).2
  · rintro c0 c0' ⟨hc0, th, E, hth, hx, hTE, hm, hSC, hbo, hfb, hfr, hrh⟩ hs hrest
    have hc0' : Certified p k arch c0' i := certified_back hrest hc2
    have hcert0 : Certified p k arch c0 i := certified_back (.thread hs hrest) hc2
    obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc0'
    rw [hth] at hth'
    cases hth'
    obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, hrp⟩ := hTE
    have hscope := hsc c0 hc0 hcert0 th hth (not_spawnT_of_mem hr) ρ η cx hE hT htv hi
    obtain ⟨-, hstep⟩ := tstep_footprintQ hP rfl (Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth)))
      (tstep_notDone hr) hscope hT hi hE htv hm hbo (PAx_of_step hs hc0' hth)
      (hwin c0 hc0 hcert0 th hth ρ η cx hE hT htv hi hm (frRunA_ext hfr hx) hfr.2.1.1 hfr.2.1.2.2.1) hrp hPS hSub hSig
    obtain ⟨E', hF, hx', hT', hm', hbB⟩ := hstep r hr hpa
    have hA' := anchR_tstep hF hm' hbB hE hT htv hi hm hscope (TermViewInv.envVR_solo hvI hc0 hth) hr (frRunA_ext hfr hx) hfr.2.1
    have hwu := tstep_wrUp _ _ _ _ r hr
    have hfb' := FrBound_foot hF hwu hfb hfr.1
    have hW0 := solo_winInv hc0 hW
    refine ⟨solo_trans hc0 (.thread hs (.refl _)), r.2.2, E', e3, Ext_trans hx hx', hT', ?_,
      StoClo_EFoot hF.1 hSC, by rw [gOf_thread hs]; exact hbo, hfb'.1, ?_, ?_⟩
    · rw [gOf_thread hs, e1, e2]
      exact hm'
    · rw [e1, e2]
      exact ⟨hfb'.2, hA', hfr.2.2⟩
    · intro N e us hT0 hus o ho hno
      by_cases hlt : o < (CE η).rini l * nWords us
      · obtain ⟨τ, h1, h2⟩ := hrh N e us hT0 hus o hlt hno
        exact ⟨τ, Nat.le_trans h1 hwu.1, h2⟩
      · obtain ⟨τ, hτ, hτ'⟩ := hF.1.riniW l cl (hx.2.2.2.2.1 _ _ hcl) N e us hT0 hus o (Nat.le_of_not_lt hlt) ho
        obtain ⟨thW0, thW, hW0P, hW0t, -, hme, hpr, -, -⟩ := hW0
        rw [hthP] at hW0P; cases hW0P
        rw [hth] at hW0t; cases hW0t
        have hsz := TermFul.memExt_size hme
        refine ⟨τ, hτ, ?_⟩
        rcases hτ' with h | ⟨hu, m, hm1, hl⟩
        · exact Or.inl (Nat.le_trans hsz h)
        · rcases hpr τ hu with h | h
          · have hlt0 := hpl τ h
            have hm0 : cP.mem[τ]? = some cP.mem[τ] := by simp [hlt0]
            have e' : c0.mem[τ]? = some m := hm1
            rw [hme τ _ hm0] at e'
            cases e'
            exact Or.inr ⟨h, _, hm0, hl⟩
          · exact Or.inl h
  · rintro c0 a v w ⟨hc0, h⟩ hw _
    exact ⟨solo_trans hc0 (.prom a v w hw (.refl _)), InvAtXR_prom h⟩
  · rintro c0 c0' ⟨hc0, h⟩ hs _
    exact ⟨solo_trans hc0 (.ext hs (.refl _)), InvAtXR_ext h hs (tidAt_solo hc0 hTA)⟩

/-- **(F2′ b″) The held prefix, from the certificate.**  Thread `i` plants a
promise `B` (index `cP.mem.size`, view `w` below it) at `cP`, runs solo to `c`
and publishes there (certified successor) with `B` outstanding.  At the typed
environment `E` of `c`, every unit of the start cell `cx` of `x` below `E`'s
real count is reader-visible at the start `E0` or carries a promise of thread
`i` outstanding at the plant: `PrefixHeld E0 … (E.rini x)`. -/
theorem certified_prefixHeld {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {cP c c' : Cfg}
    {thP th : TTh} {E0 : TEnv} {x : AllocLabel} {cx : Cell} {a0 : Address} {vB : WeakMem.Val} {w : Ts} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i (promise cP i a0 vB w) c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv (promise cP i a0 vB w))
    (hwin : ∀ c0, Solo p k arch i (promise cP i a0 vB w) c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (hthP : cP.ths[i]? = some thP) (hT0 : ThInvE p E0 thP)
    (hm0 : MemInv (gOf p k arch cP i) E0 (stOf cP.mem cP.pairs thP)) (hSC : StoClo E0)
    (hbo : (gOf p k arch cP i).boxFence = true)
    (hcx : E0.sto x = some cx) (hrle : E0.rini x ≤ E0.ini x)
    (hrc0 : RiniCoh E0 (stOf cP.mem cP.pairs thP))
    (hfl0 : ∀ l cl f, E0.sto l = some cl → E0.pfr l = some f → f ≤ cP.mem.size - 1)
    (hw : w < cP.mem.size) (hsolo : Solo p k arch i (promise cP i a0 vB w) c)
    (hs : c' ∈ threadSteps p k arch c i) (hc' : Certified p k arch c' i)
    (hth : c.ths[i]? = some th) {y : String} {a : At} {e : Expr} (hterm : th.term = .let_ y (.publish a) e)
    (hB : cP.mem.size ∈ th.promises) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    -- (C, b2) `hTB0` is kept as a hypothesis: certified_prefixHeld has no callers, so it is not discharged here (callers would pass
    -- `TermMain.tidAt_cut`/`tidAt_cutP`, as on the anchored X-chain)
    (hTB0 : ∀ l, thP.tidLbl = some l → E0.sto l = some ⟨.unit, none⟩ ∧ E0.pfr l = some 0) :
    ∃ E, Ext E0 E ∧ ThInvE p E th ∧ MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧
      PrefixHeld E0 (stOf cP.mem cP.pairs thP) x cx (E.rini x) := by
  have hc : Certified p k arch c i := certified_back (.thread hs (.refl _)) hc'
  have hv : th.vs.vWr ≤ w := (plant_pub_window hw hsolo hs hc' hthP hth hterm hB).1
  obtain ⟨ρ, η, cx0, rfl, hT1⟩ := id hT0
  have hR0 : InvAtXR p k arch i (CE η) cP.mem.size thP.vs.vWr cP.mem thP.promises x cx cP :=
    ⟨thP, CE η, hthP, Ext_refl (Coh_CE η) (CohR_CE η), hT0, hm0, hSC, hbo,
      FrBound_refl _ _ _, frRunA_start hm0 hrc0 hfl0,
      fun _ _ us _ _ o h1 h2 => absurd (Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right (nWords us) hrle)) h2⟩
  obtain ⟨th1, E, hth1, hx, hTE, hm, -, -, -, -, hrh⟩ :=
    solo_typedXR hP hsc hvI hwin hthP hm0.2.2.1 hcx (winInv_prom (winInv_refl hthP)) (InvAtXR_prom hR0)
      (tidAt_prom fun th0 h0' l hl => by
        rw [hthP] at h0'; cases h0'; exact hTB0 l hl) hsolo hc hPS hSub hSig
  rw [hth] at hth1
  cases hth1
  refine ⟨E, hx, hTE, hm, fun N e us hT hus o ho => ?_⟩
  by_cases hI : o < (CE η).ini x * nWords us
  · refine Or.inl fun N' e' us' hT' hus' => ?_
    rw [hT] at hT'
    simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
    obtain ⟨-, rfl⟩ := hT'
    rw [hus] at hus'
    cases hus'
    exact hI
  · obtain ⟨τ, hτ, h⟩ := hrh N e us hT hus o ho hI
    rcases h with h | h
    · exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans h (Nat.le_trans hτ hv)) hw) (Nat.lt_irrefl _)
    · exact Or.inr ⟨τ, h⟩

#print axioms InvAtXR_prom
#print axioms solo_typedXR
#print axioms certified_prefixHeld
/-- (U3, transitive) **The plant edge** `l → a` at environment `η` and state
`(mem, ps)`: an outstanding promise at `l`, whose cell has a `noOwn`,
region-free type, holds a reference to the private own unplanted cell `a`.
(Closure fix: no `PubRef`/`AtOff` condition, so buffer (`refine`), packed
(`iex`) and niche-sum pointers are edges too.  Only published or planted cells,
both `noOwn` and region-free, hold promise words another thread reads.) -/
def PlantR (η : TEnv) (mem : Memory) (ps : List Ts) (l a : AllocLabel) : Prop :=
  ∃ t ∈ ps, ∃ m, mem[t]? = some m ∧ m.loc.label = l ∧
    (∃ ca, η.sto l = some ca ∧ Ty.noOwnIn [] ca.ty = true ∧ rgnFree ca.ty = true) ∧
    ∃ (a' : Address) (g : Nat), m.val = .loc a' g ∧ a'.label = a ∧
    ∃ cl, η.sto a = some cl ∧ cl.owner = some η.tid ∧ η.pfr a = none

/-- (U3, transitive) **The plant's side conditions along the closure**: from
`x`'s (`plant_hpl` at the root), every member of the plant closure from `x`
is a private own unplanted cell with the type facts and `FlipOK`
(`plant_hpl` at its edge). -/
theorem plant_hplCl {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {th : TTh} {η : TEnv}
    [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv c)
    (hwin : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → NoHoldPubA p k arch (CE η) (CE η) i c0)
    (hth : c.ths[i]? = some th) (hT : ThInvE p (CE η) th)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th)) (hc : Certified p k arch c i)
    (hSC : StoClo (CE η)) (hbo : (gOf p k arch c i).boxFence = true) {x : AllocLabel}
    (hx : ∃ c', η.sto x = some c' ∧ c'.owner = some η.tid ∧ η.pfr x = none ∧
      (∀ b S, SegOf c'.ty b S → accs S ≠ none → TearOK S) ∧ Ty.coupledOKIn [] c'.ty = true ∧
      Ty.noOwnIn [] c'.ty = true ∧ rgnFree c'.ty = true ∧ FlipOK (CE η) (stOf c.mem c.pairs th) x) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hrc : RiniCoh (CE η) (stOf c.mem c.pairs th))
    (hfl : ∀ l cl f, (CE η).sto l = some cl → (CE η).pfr l = some f → f ≤ c.mem.size - 1) (hTA : TidAt i c (CE η)) :
    ∀ a, ClR (PlantR η c.mem th.promises) x a →
      ∃ c', η.sto a = some c' ∧ c'.owner = some η.tid ∧ η.pfr a = none ∧
      (∀ b S, SegOf c'.ty b S → accs S ≠ none → TearOK S) ∧ Ty.coupledOKIn [] c'.ty = true ∧
      Ty.noOwnIn [] c'.ty = true ∧ rgnFree c'.ty = true ∧ FlipOK (CE η) (stOf c.mem c.pairs th) a := by
  refine ClR_of hx fun l a _ hr => ?_
  obtain ⟨t, ht, m, hmt, hl, ⟨ca, hca, hno, hrf⟩, a', g, hv, rfl, cl, hcl, hown, hnone⟩ := hr
  subst hl
  exact plant_hpl hP hsc hvI hwin hth hT hm hc ht hmt hca hno hrf hv hcl hown hnone hSC hbo hPS hSub hSig hrc hfl hTA

#print axioms plant_hplCl

/-! ### (U3 R1, W1) `hinh` at one-word slots, from the certificate -/

/-- (U3 R1, W1) A `WordOK` word of a buffer of one-word slots is (up to its
view) a whole slot value. -/
theorem wordOK_slot1 {E : TEnv} {N : Nat} {S : Ty} {us : List Acc} {o : Nat} {w : Word}
    (h : WordOK E (.array (.lit N) S) o w) (hus : accs S = some us) (h1 : nWords us = 1) :
    ∃ w0, ValOf E S [w0] ∧ WLe1 w0 w := by
  obtain ⟨b, S', ws, o', w0, hseg, ⟨hv, hsh⟩, hw0, hle, -⟩ := h
  rcases hseg with ⟨-, -, hA⟩ | ⟨N', us', j, hT, -, -, -⟩
  · simp [accs] at hA
  · simp only [Ty.array.injEq, Idx.lit.injEq] at hT
    obtain ⟨-, rfl⟩ := hT
    have hl : ws.length = 1 := by rw [hsh us hus, h1]
    match ws, hl, hw0, hv with
    | [x], _, hw0, hv =>
      cases o' with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hw0
        subst hw0
        exact ⟨x, hv, hle⟩
      | succ n => simp at hw0

/-- (U3 R1, W1) **A label `InspM` below the start size was allocated at the
start** (`FrBound` with the start size `n + 1`: a cell or box created during
the run has its frontier at least `n`). -/
theorem FrBound_inspM {E0 E2 : TEnv} {n v0 : Nat} {a : AllocLabel} {v : Ts}
    (hfb : FrBound E0 (n + 1) v0 E2) (hi : InspM E2 a v) (hv : v < n) :
    (∃ c, E0.sto a = some c) ∨ (∃ B, E0.box a = some B) := by
  rcases hi with ⟨c, f, hc, hf, hle⟩ | ⟨B, hB, hle⟩
  · rcases h0 : E0.sto a with _ | c0
    · exact absurd (Nat.lt_of_le_of_lt hle hv) (Nat.not_lt.2 (Nat.le_of_succ_le_succ (hfb.2.1 a c f h0 hc hf)))
    · exact .inl ⟨c0, rfl⟩
  · rcases h0 : E0.box a with _ | B0
    · exact absurd (Nat.lt_of_le_of_lt hle hv) (Nat.not_lt.2 (Nat.le_of_succ_le_succ (hfb.2.2.1 a B h0 hB)))
    · exact .inr ⟨B0, rfl⟩

/-- (U3 R1, W1) The tied invariant restarted right after the plant's promise
step: start size `cP.mem.size + 1`. -/
theorem InvAtX_promOf {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {cP : Cfg} {thP : TTh}
    {E0 : TEnv} {a0 : Address} {vB : WeakMem.Val} {w : Ts}
    (hthP : cP.ths[i]? = some thP) (hT0 : ThInvE p E0 thP)
    (hm0 : MemInv (gOf p k arch cP i) E0 (stOf cP.mem cP.pairs thP)) (hSC : StoClo E0)
    (hbo : (gOf p k arch cP i).boxFence = true) (hrc0 : RiniCoh E0 (stOf cP.mem cP.pairs thP))
    (hfl0 : ∀ l cl f, E0.sto l = some cl → E0.pfr l = some f → f ≤ cP.mem.size - 1) :
    InvAtX p k arch i E0 (cP.mem.size + 1) thP.vs.vWr (promise cP i a0 vB w) := by
  have hpi := promise_inv (a := a0) (v := vB) (w := w) hthP
  have h := InvAtX_of (p := p) (k := k) (arch := arch) hpi.2.1 hT0
    (by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm0) hSC (by rw [gOf_promise]; exact hbo)
    (by rw [hpi.2.2]; exact riniCoh_promSt hrc0)
    (fun l cl f h1 h2 => Nat.le_trans (hfl0 l cl f h1 h2) (by rw [hpi.1, Array.size_push]; exact Nat.sub_le_sub_right (Nat.le_succ _) 1))
  have hs : (promise cP i a0 vB w).mem.size = cP.mem.size + 1 := by rw [hpi.1, Array.size_push]
  rw [hs] at h
  exact h

/-- (U3 R1, W1) **An outstanding promise at the plant is typed after its
fulfil**: the message is a `WordOK` word of its start cell at an extension
`E2` reached along the certificate, with the frontier bound from the start
size `cP.mem.size + 1`. -/
theorem certified_holderWord {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {cP c' : Cfg}
    {thP : TTh} {E0 : TEnv} {a0 : Address} {vB : WeakMem.Val} {w : Ts} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i (promise cP i a0 vB w) c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv (promise cP i a0 vB w))
    (hwin : ∀ c0, Solo p k arch i (promise cP i a0 vB w) c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (hthP : cP.ths[i]? = some thP) (hT0 : ThInvE p E0 thP)
    (hm0 : MemInv (gOf p k arch cP i) E0 (stOf cP.mem cP.pairs thP)) (hSC : StoClo E0)
    (hbo : (gOf p k arch cP i).boxFence = true)
    (hsolo : Solo p k arch i (promise cP i a0 vB w) c') (hc' : Certified p k arch c' i)
    {u : Ts} {m : Msg} (hu : u ∈ thP.promises) (hm : cP.mem[u]? = some m) {cl : Cell}
    (hcl : E0.sto m.loc.label = some cl) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hrc0 : RiniCoh E0 (stOf cP.mem cP.pairs thP))
    (hfl0 : ∀ l cl f, E0.sto l = some cl → E0.pfr l = some f → f ≤ cP.mem.size - 1) (hTA : TidAt i cP E0) :
    ∃ c2 th2 E2, Solo p k arch i (promise cP i a0 vB w) c2 ∧ Certified p k arch c2 i ∧
      c2.ths[i]? = some th2 ∧ Ext E0 E2 ∧ MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) ∧
      WordOK E2 cl.ty m.loc.offset (mw m) ∧ FrBound E0 (cP.mem.size + 1) thP.vs.vWr E2 := by
  have hpi := promise_inv (a := a0) (v := vB) (w := w) hthP
  have hc : Certified p k arch (promise cP i a0 vB w) i := certified_back hsolo hc'
  have h0 := InvAtX_promOf (k := k) (arch := arch) (a0 := a0) (vB := vB) (w := w) hthP hT0 hm0 hSC hbo hrc0 hfl0
  have ht : u ∈ promsOf (promise cP i a0 vB w) i := by
    rw [promsOf_some hpi.2.1]; exact List.mem_append_left _ hu
  have hlt : u < cP.mem.size := hm0.2.2.1 u hu
  have hm' : (promise cP i a0 vB w).mem[u]? = some m := by
    rw [hpi.1]; show (cP.mem.push _)[u]? = some m
    rw [Array.getElem?_push_lt hlt, ← hm]; simp [hlt]
  obtain ⟨-, c2, th2, E2, h2, hc2, hth2, hx2, -, hm2, hw2, hfb2, -⟩ :=
    certified_promNotUndefX hP hsc hvI hwin h0 (tidAt_prom hTA) hc ht hm' hPS hSub hSig
  exact ⟨c2, th2, E2, h2, hc2, hth2, hx2, hm2, hw2 cl hcl, hfb2⟩

/-- (U3 R1, W1) The labels the transfer to the planted environment agrees
on: published cells of the start, the plant set, the start's boxes. -/
def PlantG (E0 : TEnv) (Lp : AllocLabel → Prop) (a : AllocLabel) : Prop :=
  (∃ c f, E0.sto a = some c ∧ E0.pfr a = some f) ∨ Lp a ∨ (∃ B, E0.box a = some B)

/-- (U3 R1, W1) **The run facts left open** for the transfer from a
certificate environment `E2` to the planted one `E'`: (ini) no count of a
published or planted start cell exceeds the planted one (`hIniStab`,
temporary: discharge via (I1′)); (pfr) a planted (or box) label's frontier
set during the run is at least the planted one (`plantF ≤ f`); (pay) old box
payloads stay in `PlantG`. -/
structure RunAgree (E0 E' : TEnv) (Lp : AllocLabel → Prop) (E2 : TEnv) : Prop where
  ini : ∀ a, ((∃ c f, E0.sto a = some c ∧ E0.pfr a = some f) ∨ Lp a) → E2.ini a ≤ E'.ini a
  pfr : ∀ a f, (Lp a ∨ ∃ B, E0.box a = some B) → E2.pfr a = some f → ∃ f', E'.pfr a = some f' ∧ f' ≤ f
  pay : ∀ a B, PlantG E0 Lp a → E2.box a = some B → ∀ w ∈ B.pay, ∀ (a' : Address) (g : Nat),
    w.val = .loc a' g → InspM E2 a'.label w.view → PlantG E0 Lp a'.label

/-- (U3 R1, W1) **`hinh` at a one-word slot, from the certificate.**  A slot
`j` of a plant member `l` newly initialised by the plant lies in the maximal
held prefix, so an outstanding promise `u` of the plant holds it
(`PrefixHeld_Np`); its fulfil types it at a certificate environment `E2`
(`certified_holderWord`), a whole slot value `[w0]` (`wordOK_slot1`), moved to
the planted environment by `ValOf_monoK`.  Its reference names a start label
(`FrBound_inspM`, the promise's view `hpv` below the start size): a published
cell, a box, or (`hfp`: a private start cell is own) an own private cell
named by a holder of a plant member, hence (`hLcl`) a member.  Left: the run
facts `RunAgree` (`hres`). -/
theorem certified_hinhW1 {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {cP c' : Cfg}
    {thP : TTh} {E0 : TEnv} {a0 : Address} {vB : WeakMem.Val} {w : Ts} [ProgRetIall p] [WrIniC] (hP : ProgT p)
    (hsc : ∀ c0, Solo p k arch i (promise cP i a0 vB w) c0 → Certified p k arch c0 i → ScopeAt p i c0) (hvI : TermViewInv.ViewInv (promise cP i a0 vB w))
    (hwin : ∀ c0, Solo p k arch i (promise cP i a0 vB w) c0 → Certified p k arch c0 i → NoHoldPubA p k arch E0 E0 i c0)
    (hthP : cP.ths[i]? = some thP) (hT0 : ThInvE p E0 thP)
    (hm0 : MemInv (gOf p k arch cP i) E0 (stOf cP.mem cP.pairs thP)) (hrc0 : RiniCoh E0 (stOf cP.mem cP.pairs thP))
    (hfl0 : ∀ l cl f, E0.sto l = some cl → E0.pfr l = some f → f ≤ cP.mem.size - 1) (hSC : StoClo E0)
    (hbo : (gOf p k arch cP i).boxFence = true)
    (hsolo : Solo p k arch i (promise cP i a0 vB w) c') (hc' : Certified p k arch c' i)
    {Lp : AllocLabel → Prop}
    (hL : ∀ l, Lp l → ∃ c, E0.sto l = some c ∧ c.owner = some E0.tid)
    (hnone : ∀ l, Lp l → E0.pfr l = none)
    (hLcl : ∀ l, Lp l → ∀ u ∈ thP.promises, ∀ m, cP.mem[u]? = some m → m.loc.label = l →
      ∀ (a : Address) (g : Nat), m.val = .loc a g → ∀ cl, E0.sto a.label = some cl →
      cl.owner = some E0.tid → E0.pfr a.label = none → Lp a.label)
    (hfp : ∀ a cl, E0.sto a = some cl → E0.pfr a = none → cl.owner = some E0.tid)
    (hpv : ∀ u ∈ thP.promises, ∀ m, cP.mem[u]? = some m → m.view < cP.mem.size)
    (hres : ∀ c2 th2 E2, Solo p k arch i (promise cP i a0 vB w) c2 → Certified p k arch c2 i →
      c2.ths[i]? = some th2 → Ext E0 E2 → MemInv (gOf p k arch c2 i) E2 (stOf c2.mem c2.pairs th2) →
      FrBound E0 (cP.mem.size + 1) thP.vs.vWr E2 →
      RunAgree E0 (plantE E0 (stOf cP.mem cP.pairs thP) Lp) Lp E2)
    {l : AllocLabel} {c : Cell} (hl : Lp l) (hc : E0.sto l = some c) {b : Nat} {S : Ty} {us : List Acc}
    (hseg : SegOf c.ty b S) (hus : accs S = some us) (h1 : nWords us = 1)
    (hnS : Ty.noOwnIn [] S = true) (hrS : rgnFree S = true)
    (hini : IniSeg (plantE E0 (stOf cP.mem cP.pairs thP) Lp) c l b) (hnot : ¬ IniSeg E0 c l b) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hTA : TidAt i cP E0) :
    ∃ ws, ValOf (plantE E0 (stOf cP.mem cP.pairs thP) Lp) S ws ∧ ws.length = nWords us := by
  rcases hseg with ⟨-, rfl, hA⟩ | ⟨N, us', j, hT, hus', hjN, rfl⟩
  · exact absurd (fun N e hT => by rw [hT] at hA; simp [accs] at hA) hnot
  rw [hus] at hus'
  cases hus'
  rw [h1]
  simp only [h1, Nat.mul_one] at hini hnot
  -- the slot is in the maximal held prefix, above the start count
  have hge : E0.ini l ≤ j := Nat.le_of_not_lt fun hlt =>
    hnot fun N' e' hT' => by
      rw [hT] at hT'
      simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
      obtain ⟨-, rfl⟩ := hT'
      exact ⟨us, j, hus, hlt, by rw [h1, Nat.mul_one]⟩
  have hjI : j < max (E0.ini l) (Np E0 (stOf cP.mem cP.pairs thP) l) := by
    obtain ⟨us2, j2, hus2, hj2, e⟩ := hini N S hT
    rw [hus] at hus2; cases hus2
    rw [h1, Nat.mul_one] at e; subst e
    rw [plantE_ini_in hl, NpZ_eq_of_pos hc hT hus (by rw [h1]; decide)] at hj2; exact hj2
  have hjN : j < Np E0 (stOf cP.mem cP.pairs thP) l := by
    rcases Nat.le_total (E0.ini l) (Np E0 (stOf cP.mem cP.pairs thP) l) with h | h
    · rw [Nat.max_eq_right h] at hjI; exact hjI
    · rw [Nat.max_eq_left h] at hjI; omega
  rcases PrefixHeld_Np hc N S us hT hus j (by rw [h1, Nat.mul_one]; exact hjN) with hI | ⟨u, hu, m, hm, hloc⟩
  · have := hI N S us hT hus; rw [h1, Nat.mul_one] at this; omega
  have hu' : u ∈ thP.promises := hu
  have hm' : cP.mem[u]? = some m := hm
  have hcl : E0.sto m.loc.label = some c := by rw [hloc]; exact hc
  obtain ⟨c2, th2, E2, h2, hc2, hth2, hx2, hm2, hw2, hfb2⟩ :=
    certified_holderWord (hrc0 := hrc0) (hfl0 := hfl0) hP hsc hvI hwin hthP hT0 hm0 hSC hbo hsolo hc' hu' hm' hcl hPS hSub hSig hTA
  rw [hT] at hw2
  obtain ⟨w0, hV, hle⟩ := wordOK_slot1 hw2 hus h1
  have hR := hres c2 th2 E2 h2 hc2 hth2 hx2 hm2 hfb2
  have hbi := hm2.2.2.2.2.2.2.2.2.2.1
  refine ⟨[w0], ValOf_monoK (G := PlantG E0 Lp) hnS hrS hus (by rw [h1]; rfl) hx2.2.2.1 hx2.2.2.2.1
    (fun a c0 hG hc0 => ?_) (fun a hG => ?_) (fun a f hG hf => ?_) (fun a B hG hB => ?_) hR.pay ?_ hV, rfl⟩
  · show E0.sto a = some c0
    rcases hG with ⟨c1, f, h1', -⟩ | hLa | ⟨B, hB⟩
    · rw [hx2.2.2.2.2.1 a c1 h1'] at hc0; rw [h1', hc0]
    · obtain ⟨c1, h1', -⟩ := hL a hLa
      rw [hx2.2.2.2.2.1 a c1 h1'] at hc0; rw [h1', hc0]
    · have := (hbi.2.2 a B (hx2.2.2.2.2.2.2.2.2.1 a B hB)).1
      rw [hc0] at this; cases this
  · rcases hG with hG | hLa | ⟨B, hB⟩
    · exact hR.ini a (.inl hG)
    · exact hR.ini a (.inr hLa)
    · rw [(hbi.2.2 a B (hx2.2.2.2.2.2.2.2.2.1 a B hB)).2.1]; exact Nat.zero_le _
  · rcases hG with ⟨c1, f0, h1', hf0⟩ | hLa | hB
    · have hnL : ¬ Lp a := fun hLa => by rw [hnone a hLa] at hf0; cases hf0
      rw [hx2.2.2.2.2.2.2.1 a f0 hf0] at hf
      cases hf
      exact ⟨_, by rw [plantE_pfr_ne hnL]; exact hf0, Nat.le_refl _⟩
    · exact hR.pfr a f (.inl hLa) hf
    · exact hR.pfr a f (.inr hB) hf
  · show E0.box a = some B
    rcases hG with ⟨c1, f, h1', -⟩ | hLa | ⟨B0, hB0⟩
    · have := (hbi.2.2 a B hB).1
      rw [hx2.2.2.2.2.1 a c1 h1'] at this; cases this
    · obtain ⟨c1, h1', -⟩ := hL a hLa
      have := (hbi.2.2 a B hB).1
      rw [hx2.2.2.2.2.1 a c1 h1'] at this; cases this
    · rw [hx2.2.2.2.2.2.2.2.2.1 a B0 hB0] at hB; rw [hB0, hB]
  · -- the slot word's reference names a start label
    intro w1 hw1 a g hv
    rw [List.mem_singleton] at hw1
    subst hw1
    have hJ := noJunk_valOf hV hnS hrS hus (by rw [h1]; rfl) w1 (List.mem_singleton_self _) a g hv
    have hvm : w1.view ≤ m.view := hle.2 a g hv
    have hmv : m.val = .loc a g := by rw [← hv]; exact hle.1.symm
    rcases FrBound_inspM hfb2 hJ (Nat.lt_of_le_of_lt hvm (hpv u hu' m hm')) with ⟨c1, hc1⟩ | ⟨B, hB⟩
    · rcases hpf : E0.pfr a.label with _ | f
      · exact .inr (.inl (hLcl l hl u hu' m hm' (by rw [hloc]) a g hmv c1 hc1 (hfp _ c1 hc1 hpf) hpf))
      · exact .inl ⟨c1, f, hc1, hpf⟩
    · exact .inr (.inr ⟨B, hB⟩)

#print axioms wordOK_slot1
#print axioms FrBound_inspM
#print axioms InvAtX_promOf
#print axioms certified_holderWord
#print axioms certified_hinhW1
#print axioms not_spawnT_of_steps
#print axioms TermTyped.ThInvE_emit
#print axioms TermTyped.ThInvRE_emit
#print axioms TermTyped.ThInvM_emit
#print axioms TermTyped.ext_res
#print axioms TermTyped.ThInvE_ext
#print axioms TermTyped.ThInvRE_ext
#print axioms TermTyped.ThInvM_ext
#print axioms TermTyped.InvAt_ext
#print axioms TermTyped.InvAtXR_ext



end TermTyped
