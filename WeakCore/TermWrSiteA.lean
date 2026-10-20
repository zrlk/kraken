import WeakCore.TermAnch
import WeakCore.TermPredStoreFree

/-!
# TermWrSiteA (A″ prototype): `WrSite` with the fulfilled-unit sharpening

`wrSiteA_ok`: a typed, in-scope thread step's non-promise result messages are as in `WrSite`, and a
message at an initialised unit (`InitR`) moreover lies below the real count (`InitRr`, own handles and
buffer element writes), is fresh (`mem.size ≤ t`), lies above the label's frontier (pub handles to an
unseen label: `ModeOK .pub` gives `f ≤ pw.view ≤ dep pw < t`), or the label is seen.
Extra hypothesis over `wrSite_ok`: `TermSeenHid.EnvVR th` (from `TermViewInv.envVR_solo`).
`wrIniC` (replacing `TermAnch.wrIniC`) supplies both fields of `TermTyped.WrIniC`.
-/

namespace TermWrSiteA

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermPredStoreFree
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The sharpening of a fulfilled unit. -/
def FulX (η : TEnv) (l : AllocLabel) (o t : Nat) : Prop :=
  ∃ c, η.sto l = some c ∧ (InitRr η c l o ∨ (∀ f, η.pfr l = some f → f < t) ∨ η.seen l)

/-- (i) Own handles and buffer element writes: below the real count. -/
theorem own_x {η : TEnv} {b : Address} {c : Cell} {U : Ty} {us : List Acc} {j t : Nat}
    (hsto : η.sto b.label = some c) (hus : accs U = some us)
    (hini : IniAt (modeIni .own η.ini η.rini) c b U) (hj : j < nWords us) : FulX η b.label (b.offset + j) t :=
  ⟨c, hsto, .inl fun N e us' hty he => TermSeenHid.slot_lt hini hus hj N e us' hty he⟩

/-- (ii) Pub handles: seen, or the frontier is below every timestamp a write through `pw` fulfils. -/
theorem pub_x {k : Promises.Knobs} {η : TEnv} {l : AllocLabel} {c : Cell} {pw : Word} {o t : Nat}
    (hsto : η.sto l = some c) (hmo : ModeOK η.tid η.pfr η.seen .pub l c [pw]) (hvr : pw.view ≤ pw.rts)
    (hk : ∀ F, t ≤ F → F ≤ TermStoreNI.dep k pw → False) : FulX η l o t := by
  by_cases hs : η.seen l
  · exact ⟨c, hsto, .inr (.inr hs)⟩
  obtain ⟨f, hf, -⟩ := id hmo
  have hd : f ≤ TermStoreNI.dep k pw := PVc.dep_of_modeOK hmo hf hs hvr
  refine ⟨c, hsto, .inr (.inl fun f' hf' => ?_)⟩
  rw [hf] at hf'; cases hf'
  exact Nat.lt_of_not_le fun hle => hk f hle hd

theorem add_zero_x {η : TEnv} {l : AllocLabel} {o t : Nat} (h : FulX η l (o + 0) t) : FulX η l o t := h

/-- **The fulfil sharpening**: a promise `t` a typed, in-scope step fulfils (`SW`) lies at a `FulX`
unit, or the step is a `bufInit`. -/
theorem ful_x {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh} {t : Nat} {m : Msg} (hE : EnvOK p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : StepScope cx th.term) (hvr : TermSeenHid.EnvVR th) (hr : r ∈ tstep g mem pairs th)
    (htp : t ∈ th.promises) (htn : t ∉ r.2.2.promises) (hsw : TermFul.SW g mem pairs th m.loc m.val) :
    FulX η m.loc.label m.loc.offset t ∨ ∃ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e := by
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, hee, hev, hb, -⟩
  · rw [hterm] at hT hsc
    cases hT with
    | let_ hop _ =>
      rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, hloc, -⟩ |
          ⟨o, acq, rel, a', v, ty1, ty2, pw, nw, tr, mr, rfl, hea, hev, hb, -⟩
      · have hjl := TermFul.OneAt_lt hj
        rw [hloc]
        cases op
        case store rl a1 v1 tok =>
          have hsc' : OpScope cx (.store rl a1 v1 tok) := hsc
          obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := store_TI hop hsc' hi hE htv hu
          rcases hμ with rfl | rfl
          · exact .inl (own_x hsto hus' hini hjl)
          · obtain ⟨-, rt, rv, μr, ru, hea, hev, hcr, hb, hus⟩ := hu
            have hk : ∀ F, t ≤ F → F ≤ TermStoreNI.dep g.k pw → False := by
              intro F h1 h2
              have hr' := hr
              rw [TermLocal.tstep_let_gen hterm rfl, List.mem_map] at hr'
              obtain ⟨⟨s', t', ws'⟩, hin, hreq⟩ := hr'
              rw [← hreq] at htn
              simp only [evalOp, hea, hev, hcr, hb, hus, List.mem_map] at hin
              obtain ⟨s'', hs'', he⟩ := hin
              simp only [Prod.mk.injEq] at he
              obtain ⟨rfl, -, -⟩ := he
              exact htn (PVc.storeUnits_keepLow hs'' htp h1 h2)
            exact .inl (pub_x hsto hmo (hvr _ _ _ pw hea (List.mem_singleton_self _)) hk)
        case xchg a1 v1 =>
          have hsc' : OpScope cx (.xchg a1 v1) := hsc
          obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := xchg_TI hop hsc' hi hE htv hu
          rcases hμ with rfl | rfl
          · exact .inl (own_x hsto hus' hini hjl)
          · obtain ⟨-, rt, rv, μr, ru, hea, hev, hcr, hb, hus⟩ := hu
            have hk : ∀ F, t ≤ F → F ≤ TermStoreNI.dep g.k pw → False := by
              intro F h1 h2
              have hr' := hr
              rw [TermLocal.tstep_let_gen hterm rfl, List.mem_map] at hr'
              obtain ⟨⟨s', t', ws'⟩, hin, hreq⟩ := hr'
              rw [← hreq] at htn
              simp only [evalOp, hea, hev, hcr, hb, hus, List.mem_flatMap, List.mem_map] at hin
              obtain ⟨⟨s1, old⟩, hl, s'', hs'', he⟩ := hin
              simp only [Prod.mk.injEq] at he
              obtain ⟨rfl, -, -⟩ := he
              have hk1 := (TermFul.loadUnits_keep us 0 _ _ hl).2.2
              have hh1 : t ∈ s1.promises := by rw [hk1]; exact htp
              exact htn (PVc.storeUnits_keepLow hs'' hh1 h1 h2)
            exact .inl (pub_x hsto hmo (hvr _ _ _ pw hea (List.mem_singleton_self _)) hk)
        case xchgAt =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := xchgAt_uaR hop hi hE htv hu
          exact .inl (own_x hsto hus' hini hjl)
        case xchgAtF =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := xchgAtF_uaR hop hi hE htv hu
          exact .inl (own_x hsto hus' hini hjl)
        case stl =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := stl_uaR hop hi htv hu
          exact .inl (own_x hsto hus' hini hjl)
        case stlw =>
          obtain ⟨c1, U, hsto, -, hus', hini⟩ := stlw_uaR hop hi htv hu
          exact .inl (own_x hsto hus' hini hjl)
        case bufInit bb i1 v1 =>
          exact .inr ⟨x, bb, i1, v1, e, hterm⟩
        all_goals simp [TermFul.UnitsOp] at hu
      · have hsc' : OpScope cx (.fetch o acq rel a' v) := hsc
        obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := fetch_TI hop hsc' hi hE htv hm hea hb
        rcases hμ with rfl | rfl
        · exact .inl (add_zero_x (own_x (j := 0) hsto hus' hini (by decide)))
        · have hk : ∀ F, t ≤ F → F ≤ TermStoreNI.dep g.k pw → False := by
            intro F h1 h2
            have hr' := hr
            rw [TermLocal.tstep_let_gen hterm rfl, List.mem_map] at hr'
            obtain ⟨⟨s', t'', ws'⟩, hin, hreq⟩ := hr'
            rw [← hreq] at htn
            simp only [evalOp, hea, hev, hb, List.mem_map] at hin
            obtain ⟨⟨mem', th'⟩, hst, he⟩ := hin
            simp only [Prod.mk.injEq] at he
            obtain ⟨rfl, -, -⟩ := he
            exact htn (PVc.stepRmw_keepLow hst htp h1 h2)
          exact .inl (pub_x hsto hmo (hvr _ _ _ pw hea (List.mem_singleton_self _)) hk)
  · rw [hterm] at hT hsc
    obtain ⟨c1, U, μ, hsto, -, hus', hmo, hini, hμ⟩ := cas_TI hT hsc hi hE htv hm hea hb
    rcases hμ with rfl | rfl
    · exact .inl (add_zero_x (own_x (j := 0) hsto hus' hini (by decide)))
    · have hk : ∀ F, t ≤ F → F ≤ TermStoreNI.dep g.k pw → False := by
        intro F h1 h2
        have hr' := hr
        simp only [tstep, hterm, hea, hee, hev, hb, List.mem_map] at hr'
        obtain ⟨⟨mem', th'⟩, hst, hreq⟩ := hr'
        rw [← hreq] at htn
        exact htn (PVc.stepRmw_keepLow (s := stOf mem pairs th) hst htp h1 h2)
      exact .inl (pub_x hsto hmo (hvr _ _ _ pw hea (List.mem_singleton_self _)) hk)

/-- The `bufInit` branch of a fulfilled unit (as in `TermAnch.wrSite_ok`). -/
theorem buf_x {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {m : Msg} (hE : EnvOK p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hsw : TermFul.SW g mem pairs th m.loc m.val) {x : String} {bb ib v : At} {e : Expr}
    (hterm : th.term = .let_ x (.bufInit bb ib v) e) :
    ∃ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e ∧ ∃ rt w ad rti wi n c,
      evalAt th.env bb = some (rt, [w]) ∧ w.val = .loc ad 0 ∧ evalAt th.env ib = some (rti, [wi]) ∧
      numOf [wi] = some n ∧ ad.label = m.loc.label ∧ (CE η).sto m.loc.label = some c ∧
      ∀ N el us, c.ty = .array (.lit N) el → accs el = some us → m.loc.offset < (n + 1) * nWords us := by
  refine ⟨x, bb, ib, v, e, hterm, ?_⟩
  rcases hsw with ⟨x', op, e', hterm', hw⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hterm', -⟩
  · rw [hterm] at hterm'
    simp only [Expr.let_.injEq] at hterm'
    obtain ⟨rfl, rfl, rfl⟩ := hterm'
    rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, hj, -, hl, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hop', -⟩
    · have hT' := hT
      rw [hterm] at hT'
      cases hT' with
      | let_ hop _ => rw [hl]; exact TermAnch.bufInit_site (η := η) hop hi hE htv hu (TermFul.OneAt_lt hj)
    · cases hop'
  · rw [hterm] at hterm'; cases hterm'

/-- **The sharpened typed write-location fact.** -/
theorem wrSiteA_ok {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh} (hE : EnvOK p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : ScopeD th.σs cx th.term) (hvr : TermSeenHid.EnvVR th) (hr : r ∈ tstep g mem pairs th) :
    WrSiteA g (CE η) mem pairs th r := by
  intro t m ht hmt
  by_cases hlt : t < mem.size
  · have hm0 : mem[t]? = some mem[t] := by simp [hlt]
    have e2 := (TermFul.tstep_grow hr).1 t _ hm0
    rw [hmt] at e2
    simp only [Option.some.injEq] at e2
    have hm1 : mem[t]? = some m := by rw [hm0, e2]
    by_cases htp : t ∈ th.promises
    · obtain ⟨m', hm', hsw, -, -⟩ :=
        (TermFul.tstep_fulfil (MemInv_promLt hm) (MemInv_nopair hm) hr).2 t htp ht
      have hm'' : mem[t]? = some m' := hm'
      rw [hm1] at hm''; cases hm''
      have hss := TermTyped.scopeD_SW hsc hsw
      rcases TermPlantF.SWIni hE hT htv hi hm hss hsw with ⟨c, hc, hI⟩ | ⟨x, bb, ib, v, e, hterm⟩
      · rcases ful_x hE hT htv hi hm hss hvr hr htp ht hsw with ⟨c', hc', hx⟩ | ⟨x, bb, ib, v, e, hterm⟩
        · rw [hc] at hc'; cases hc'
          refine .inr (.inr (.inl ⟨c, hc, hI, ?_⟩))
          rcases hx with h | h | h
          · exact .inl h
          · exact .inr (.inr (.inl h))
          · exact .inr (.inr (.inr h))
        · exact .inr (.inr (.inr (buf_x hE hT htv hi hsw hterm)))
      · exact .inr (.inr (.inr (buf_x hE hT htv hi hsw hterm)))
    · exact .inl ⟨htp, hm1⟩
  · have hge : mem.size ≤ t := Nat.le_of_not_lt hlt
    rcases TermAnch.wrSite_ok hE hT htv hi hm hsc hr t m ht hmt with h | h | ⟨c, hc, hI⟩ | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl ⟨c, hc, hI, .inr (.inl hge)⟩))
    · exact .inr (.inr (.inr h))

/-- `wrSiteA_ok` with `EnvVR` unfolded (the form `WrIniC` can state without importing `TermSeenHid`). -/
theorem wrSiteA_okU {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {r : Memory × List Ts × TTh} (hE : EnvOK p η) (hT : Typed p cx th.term) (htv : TvOK cx)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : ScopeD th.σs cx th.term)
    (hvr : ∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws →
      w.view ≤ w.rts) (hr : r ∈ tstep g mem pairs th) :
    WrSiteA g (CE η) mem pairs th r :=
  wrSiteA_ok hE hT htv hi hm hsc hvr hr

/-- **`WrIniC` holds** (both fields). -/
theorem wrIniC : WrIniC :=
  ⟨fun hE hT htv hi hm hsc hr => TermAnch.wrSite_ok hE hT htv hi hm hsc hr,
   fun hE hT htv hi hm hsc hvr hr => wrSiteA_okU hE hT htv hi hm hsc hvr hr⟩

end TermWrSiteA

#print axioms TermWrSiteA.wrSiteA_ok
#print axioms TermWrSiteA.wrIniC
#print axioms TermWrSiteA.wrSiteA_okU
