import WeakCore.TermForWU
import WeakCore.TermLocal

/-! # TermFulW: fulfils off the own-path address ops are at word units or RMW atoms (P2″)

A thread step whose term has no own-path address atom (`TermPiece.opAtomP = none`: no store,
`xchg` family, `stl`, `stlw`, `bufInit`) fulfils own promises only by a `fetch` or a `cas`, whose
target is a `WordUnit` or a `TermForWU.RmwAtom` (`fetch_cls`, `cas_cls`), at any cell.
-/

namespace TermFulW

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermB5 TermForWU TermFul
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)


/-! ## RMW targets, one-unit form -/

/-- A one-word solid component at the address (the `Int` / one-word-leaf cases of
`TermForWU.RmwAtom`, at the component's own offset). -/
def RmwAtom1 (E : TEnv) (a : Address) : Prop :=
  ∃ c S us, E.sto a.label = some c ∧ AtOff c.ty a.offset S ∧ accs S = some us ∧ nWords us = 1 ∧ Solid S

theorem solid_int : Solid .int := ⟨fun _ _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h)⟩


/-- A `fetch`'s RMW target: a non-ghost protocol word or an `Int` component. -/
theorem fetch_cls1 {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx c' : Cx} {x : String} {o : FetchOp} {acq rel : Bool}
    {a v : At} {t : Ty} {pw : Word} {b : Address}
    (hop : OpT p cx x (.fetch o acq rel a v) c') (hsc : OpScope cx (.fetch o acq rel a v))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env a = some (t, [pw])) (hb : addrOf pw = some b) :
    WordUnit (CE η) b ∨ RmwAtom1 (CE η) b := by
  cases hop with
  | fetchCell hp _ hc =>
      rcases hc with hc0 | ⟨r, hc0, -⟩
      all_goals
        obtain ⟨c, hsto, hat⟩ := int_tgt hi.2.1 hp (cell_cases hc0) hea hb
        exact .inr ⟨c, .int, [.one], hsto, hat, rfl, nWords_one, solid_int⟩
  | fetchEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨μ', u', ht', hμ'⟩ := hsc _ hp
      have hμ := word_mode ht ht' hμ'
      have hg := pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep
      obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
      exact .inl ⟨c, hsto, .inl ⟨_, _, hg, hat⟩⟩
  | fetchShare hp hw _ _ _ hok =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      simp only [fetchOK, Bool.and_eq_true, Bool.not_eq_true'] at hok
      obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
      exact .inl ⟨c, hsto, .inl ⟨_, _, hok.1.1.1.1, hat⟩⟩

#print axioms fetch_cls1

/-- A `cas`'s RMW target: a non-ghost protocol word or a one-word component. -/
theorem cas_cls1 {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {K : TEnv → List Word → Prop} {cx : Cx} {acq rel : Bool} {w e v : At} {tn : String}
    {ok fail : Expr} {t : Ty} {pw : Word} {b : Address}
    (hT : Typed p cx (.cas acq rel w e v tn ok fail)) (hsc : StepScope cx (.cas acq rel w e v tn ok fail))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th))
    (hea : evalAt th.env w = some (t, [pw])) (hb : addrOf pw = some b) :
    WordUnit (CE η) b ∨ RmwAtom1 (CE η) b := by
  cases hT with
  | casCell hp _ hc hraw haff =>
      have hraw0 := hraw
      rcases hc with hc0 | ⟨r, hc0, -⟩
      all_goals
        obtain ⟨c, U, hsto, hat, hFd, -⟩ := ptr_targetI hi.2.1 hp (cell_cases hc0) hea hb
        have hV : accs (cl ρ η.wit 0 0 _) = some [.one] := accs_cl_one hraw0
        have hacc : accs U = some [.one] := (Fd_accs hFd).trans hV
        have htb := tb_cellOf (peek_tb htv hp) hc0
        have hVa := AffineCl.affine_cl0 ρ η.wit cx.ke (fun k => (hE.2.1 k).1)
          (fun k _ hk => hi.2.2.2.2.2.2.2.2.1 k hk) _ haff htb
        have hVm := mg_cl (ρ := ρ) (fun k => (hE.2.1 k).1.1) (WitAF.mg hi.2.2.2.2.2.2.1) _ 0 0
          (mg_cellOf (peek_mg htv hp) hc0)
        obtain ⟨S, hS, hsol, hSa, hStb, hSaf⟩ := one_leafM _ _ (Nat.lt_succ_self _)
          (Clo_cl (fun k => (hE.2.1 k).1) ρ _) hVm hV hVa
        have hat2 : AtOff c.ty b.offset S := by
          have := AtOff_trans (AtOff_trans hat (Fd_AtOff hFd (by rw [hacc]; exact Option.some_ne_none _))) hS
          simpa using this
        exact .inr ⟨c, S, [.one], hsto, hat2, hSa, nWords_one, hsol⟩
  | casShare hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
      exact .inl ⟨c, hsto, .inl ⟨_, _, hg, hat⟩⟩
  | casTake hp hw hg =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
      exact .inl ⟨c, hsto, .inl ⟨_, _, hg, hat⟩⟩
  | casEpoch hp hw hep =>
      obtain ⟨μ, ht⟩ := wordOf_cases hw
      simp only at ht
      rcases hsc _ hp with ⟨μ', r', P', ht', hμ'⟩ | ⟨u, -, hnw⟩
      · have hμ := word_mode ht ht' hμ'
        have hg := pwf_epoch_ghost (wordRef_pwf hp ht hμ hi hE htv hm) hep
        obtain ⟨c, n, hsto, hat⟩ := word_tgt hi.2.1 hp ht hea hb
        exact .inl ⟨c, hsto, .inl ⟨_, _, hg, hat⟩⟩
      · rw [hw] at hnw; cases hnw

#print axioms cas_cls1

/-- A piece containing a one-word solid component's unit is that component. -/
theorem piece_one {T S S' : Ty} {q o : Nat} {usS us' : List Acc} (hP : TermPiece.Piece T q S)
    (hus : accs S = some usS) (h1 : q ≤ o) (h2 : o < q + nWords usS) (hat : AtOff T o S')
    (hS' : accs S' = some us') (hn : nWords us' = 1) (hsol : Solid S') : q = o ∧ nWords usS = 1 := by
  have hP' : TermPiece.Piece T o S' := ⟨hat, hsol, by rw [wc_of_accs hS', hn]; simp⟩
  rcases TermPiece.Piece_disj hP hP' hus hS' with ⟨e1, rfl⟩ | h | h
  · rw [hus] at hS'
    cases hS'
    exact ⟨e1, hn⟩
  · omega
  · omega

/-! ## The `storeUnits`-issuing ops -/

/-- **An op issuing `storeUnits`** (`UnitsOp`): its result is a `storeUnits` call from a state
with the pre-state's memory and promises (after its loads, if any). -/
theorem evalOp_units {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {r : St × Ty × List Word}
    {pw : Word} {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hu : UnitsOp g env s op pw b rel us ws) (h : r ∈ evalOp g env σs s op) :
    ∃ (k : Promises.Knobs) (arch : Arch) (s1 : St) (pw' : Word) (b' : Address) (rel' : Bool) (us' : List Acc)
      (ws' : List Word), s1.mem = s.mem ∧ s1.promises = s.promises ∧ UnitsOp g env s op pw' b' rel' us' ws' ∧
      r.1 ∈ storeUnits k arch pw' b' rel' us' ws' 0 s1 := by
  cases op <;> (try (simp [UnitsOp] at hu; done))
  all_goals
    simp only [evalOp] at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (simp only [List.mem_map] at h
         obtain ⟨s', hs, rfl⟩ := h
         exact ⟨_, _, _, _, _, _, _, _, rfl, rfl, by dsimp only [UnitsOp]; fillx, hs⟩)
      | (simp only [List.mem_flatMap, List.mem_map] at h
         obtain ⟨x, hx, y, hy, rfl⟩ := h
         obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
         exact ⟨_, _, _, _, _, _, _, _, k1, k3, by dsimp only [UnitsOp]; fillx, hy⟩)
      | (simp only [List.mem_flatMap] at h
         obtain ⟨x, hx, h⟩ := h
         split at h
         · simp only [List.mem_map] at h
           obtain ⟨y, hy, rfl⟩ := h
           obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
           exact ⟨_, _, _, _, _, _, _, _, k1, k3, by dsimp only [UnitsOp]; fillx, hy⟩
         · simp at h)

#print axioms evalOp_units

/-- A `UnitsOp` operation under `let_` has an own-path address atom. -/
theorem opAtomP_of_units {g : G} {env : Env} {s : St} {x : String} {op : Op} {e : Expr} {pw : Word}
    {b : Address} {rel : Bool} {us : List Acc} {ws : List Word}
    (hu : TermFul.UnitsOp g env s op pw b rel us ws) : (TermPiece.opAtomP (.let_ x op e)).isSome = true := by
  cases op <;> simp_all [TermFul.UnitsOp, TermPiece.opAtomP]

/-- **P2″, step form.** -/
theorem tstep_lostNA {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {cx : Cx} {r : Memory × List Ts × TTh} (hE : EnvOK p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (h : r ∈ tstep g mem pairs th) (hna : TermPiece.opAtomP th.term = none) :
    ∀ (t : Nat) (m : Msg), t ∈ th.promises → t ∉ r.2.2.promises → mem[t]? = some m →
      WordUnit (CE η) m.loc ∨ RmwAtom (CE η) m.loc := by
  intro t m ht hn hmt
  obtain ⟨m0, hm0, hsw, -, -⟩ := (TermFul.tstep_fulfil (MemInv_promLt hm) (MemInv_nopair hm) h).2 t ht hn
  obtain rfl : m0 = m := Option.some.inj (hm0.symm.trans hmt)
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, -, -, hb, -⟩
  · have hsc0 := hsc
    rw [hterm] at hT hsc0 hna
    cases hT with
    | let_ hop _ =>
        rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, -, -, -, -⟩ |
            ⟨o, acq, rel, a, v, t0, t1, pw, nw, tr, mr, rfl, hea, -, hb, -⟩
        · have := opAtomP_of_units (x := x) (e := e) hu
          rw [hna] at this; cases this
        · exact fetch_cls hop hsc0 hi hE htv hm hea hb
  · rw [hterm] at hT hsc
    exact cas_cls hT hsc hi hE htv hm hea hb

#print axioms tstep_lostNA

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **P2″ (at the system)**: at a thread step (`TCtx`, typed at `EnvAt` with its `MemInv`)
whose term has no own-path address atom, every own promise the step fulfils is at a
`WordUnit` or an `RmwAtom` of `CE η`. -/
theorem tctx_lostNA {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res}
    (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hna : TermPiece.opAtomP th.term = none) :
    ∀ (t : Nat) (m : Msg), t ∈ th.promises → t ∉ r.2.2.promises → c.mem[t]? = some m →
      WordUnit (CE η) m.loc ∨ RmwAtom (CE η) m.loc := by
  have hs0 := hsc X Y
  obtain ⟨-, -, hE, hT, htv, hF, -⟩ := Y
  have hFi : FInv ρ η th.σs (Resume p th.stack) cx th.env :=
    FInvR_FInv (htv.2.2.2.2.2.2.2)
      (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs E rd ws R h) hF
  rcases hs0 with hs | hR
  · exact fun t m ht hn hm1 => tstep_lostNA hE hT.1 htv hFi hm hs X.hr hna t m ht hn hm1
  · have hk := frame_keep hR hT.1 hT.2 hF hE htv hm r X.hr
    intro t m ht hn _
    have hk2 : r.2.2.promises = th.promises := hk.2.1
    exact absurd (hk2 ▸ ht) hn

#print axioms tctx_lostNA

end


/-! ## WPD: whole-piece discharge -/

/-- **WPD, step form.**  Under `PromAbove` after the step, a step discharging an own non-word
promise at `m.loc` discharges, at every unit of every piece containing `m.loc`, the lowest own
promise there.  A `storeUnits` op writes its whole component (`Piece_sub`), ending each written
unit at a new message or an own promise there (`storeUnits_cohW`); a `fetch`/`cas` writes a
one-word solid component (`fetch_cls1`, `cas_cls1`), ending at the fulfilled promise
(`tstep_fulC`). -/
theorem tstep_wpd {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {cx : Cx} {r : Memory × List Ts × TTh} (hE : EnvOK p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (h : r ∈ tstep g mem pairs th) (hpa : PromAbove (stOf r.1 r.2.1 r.2.2)) :
    ∀ (t : Ts) (m : Msg) (cl : Cell), t ∈ th.promises → t ∉ r.2.2.promises → mem[t]? = some m →
      (CE η).sto m.loc.label = some cl → ¬ WordUnit (CE η) m.loc →
      ∀ q S usS, TermPiece.Piece cl.ty q S → accs S = some usS → q ≤ m.loc.offset →
        m.loc.offset < q + nWords usS → ∀ o th0, q ≤ o → o < q + nWords usS →
          TermPlant.LowOwn (stOf mem pairs th) ⟨m.loc.label, o⟩ th0 → th0 ∉ r.2.2.promises := by
  intro t m cl ht hn hmt hcl hnw q S usS hP hus hq1 hq2 o th0 ho1 ho2 hlo hth0
  have hlt := MemInv_promLt hm
  have key : th0 ≤ (stOf r.1 r.2.1 r.2.2).vs.coh ⟨m.loc.label, o⟩ → False := by
    intro hle
    obtain ⟨-, ⟨m0, hm0, hl0⟩, -⟩ := hlo
    have hm0' : r.1[th0]? = some m0 := (tstep_grow h).1 th0 m0 hm0
    have h2 := hpa th0 hth0 m0 hm0'
    rw [hl0] at h2
    exact absurd hle (Nat.not_le.2 h2)
  have single : (∃ c S' us', (CE η).sto m.loc.label = some c ∧ AtOff c.ty m.loc.offset S' ∧
      accs S' = some us' ∧ nWords us' = 1 ∧ Solid S') → False := by
    rintro ⟨c, S', us', hc, hat, hS', h1, hsol⟩
    obtain rfl : cl = c := Option.some.inj (hcl.symm.trans hc)
    obtain ⟨e1, e2⟩ := piece_one hP hus hq1 hq2 hat hS' h1 hsol
    obtain ⟨m1, hm1, hc1⟩ := TermTyped.tstep_fulC hlt (MemInv_nopair hm) h t ht hn
    obtain rfl : m = m1 := Option.some.inj (hmt.symm.trans hm1)
    have e : (⟨m.loc.label, o⟩ : Address) = m.loc := by
      have : o = m.loc.offset := by omega
      rw [this]
    apply key
    rw [e]
    show th0 ≤ (stOf r.1 r.2.1 r.2.2).vs.coh m.loc
    rw [hc1]
    exact hlo.2.2 t m ht hmt e.symm
  obtain ⟨m0, hm0, hsw, -, -⟩ := (TermFul.tstep_fulfil hlt (MemInv_nopair hm) h).2 t ht hn
  obtain rfl : m = m0 := Option.some.inj (hmt.symm.trans hm0)
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, -, -, hb, -⟩
  · have hsc0 := hsc
    rw [hterm] at hT hsc0
    cases hT with
    | let_ hop _ =>
        rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, -, -, -, -⟩ |
            ⟨o', acq, rel, a, v, t0, t1, pw, nw, tr, mr, rfl, hea, -, hb, -⟩
        · have hcall : Robust.isCallOp op = false := by
            cases op <;> first | rfl | (simp [UnitsOp] at hu)
          have h2 := h
          rw [TermLocal.tstep_let_gen hterm hcall (fun _ _ h => by subst h; simp [UnitsOp] at hu)] at h2
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h2
          obtain ⟨k, arch, s1, pw', b', rel', us', ws', hs1m, hs1p, hu', hst⟩ := evalOp_units hu hy
          obtain ⟨c2, U, hsto2, hat2, hacc2⟩ := TermTyped.unitsOp_ua hop hsc0 hi hE htv hu'
          have hlt1 : PromLt s1 := by
            intro t' ht'; rw [hs1m]; rw [hs1p] at ht'; exact hlt t' ht'
          have hnd : s1.promises.Nodup := by rw [hs1p]; exact MemInv_nodup hm
          obtain ⟨n, j', m1, w1, hn1, hj', hm1, -, hl1, -⟩ :=
            TermPiece.storeUnits_fulU us' ws' 0 s1 y.1 hnd hlt1 hst t (by rw [hs1p]; exact ht) hn
          rw [hs1m] at hm1
          obtain rfl : m = m1 := Option.some.inj (hmt.symm.trans hm1)
          have hjl : j' + 1 ≤ nWords us' := TermStep.OneAt_lt ⟨n, hn1, hj'⟩
          have hlab : m.loc.label = b'.label := by rw [hl1]; rfl
          have hoff : m.loc.offset = b'.offset + j' := by rw [hl1]; simp [offs]
          have hsto2' : (CE η).sto m.loc.label = some c2 := by rw [hlab]; exact hsto2
          obtain rfl : cl = c2 := Option.some.inj (hcl.symm.trans hsto2')
          have hq1' : q ≤ b'.offset + j' := hoff ▸ hq1
          have hq2' : b'.offset + j' < q + nWords usS := hoff ▸ hq2
          obtain ⟨hs1, hs2, -⟩ := TermPiece.Piece_sub hat2 hacc2 hP hus
            (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hq2') (Nat.lt_of_le_of_lt hq1' (by omega))
          have hj'' : o - b'.offset < nWords us' := by omega
          have eaddr : offs b' (0 + (o - b'.offset)) = ⟨m.loc.label, o⟩ := by
            have h3 : b'.offset + (0 + (o - b'.offset)) = o := by
              rw [Nat.zero_add]; exact Nat.add_sub_cancel' (Nat.le_trans hs1 ho1)
            show (⟨b'.label, b'.offset + (0 + (o - b'.offset))⟩ : Address) = ⟨m.loc.label, o⟩
            rw [h3, hlab]
          rcases storeUnits_cohW us' ws' 0 s1 y.1 hst hlt1 (o - b'.offset) hj'' with hc | ⟨u, hu1, m2, hm2, hl2, hc⟩
          · apply key
            rw [← eaddr]
            refine Nat.le_trans (Nat.le_of_lt ?_) hc
            rw [hs1m]
            exact hlt th0 hlo.1
          · apply key
            rw [← eaddr]
            show th0 ≤ y.1.vs.coh _
            rw [hc]
            rw [hs1p] at hu1
            rw [hs1m] at hm2
            exact hlo.2.2 u m2 hu1 hm2 (by rw [hl2, eaddr])
        · exact single ((fetch_cls1 hop hsc0 hi hE htv hm hea hb).resolve_left hnw)
  · rw [hterm] at hT hsc
    exact single ((cas_cls1 hT hsc hi hE htv hm hea hb).resolve_left hnw)

#print axioms tstep_wpd

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **WPD (at the system)**, in the premise form (`poolTagOwnT`): at a thread
step (`TCtx`, typed at `EnvAt` with its `MemInv`) under `PromAbove` after the step. -/
theorem tctx_wpd {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res}
    (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hpa : PromAbove (stOf r.1 r.2.1 r.2.2)) :
    ∀ (t : Ts) (m : Msg) (cl : Cell), t ∈ th.promises → t ∉ r.2.2.promises → c.mem[t]? = some m →
      (CE η).sto m.loc.label = some cl → cl.owner = some i → (CE η).pfr m.loc.label ≠ none →
      ¬ WordUnit (CE η) m.loc →
      ∀ q S usS, TermPiece.Piece cl.ty q S → accs S = some usS → q ≤ m.loc.offset →
        m.loc.offset < q + nWords usS → ∀ o th0, q ≤ o → o < q + nWords usS →
          TermPlant.LowOwn (stOf c.mem c.pairs th) ⟨m.loc.label, o⟩ th0 → th0 ∉ r.2.2.promises := by
  have hs0 := hsc X Y
  obtain ⟨-, -, hE, hT, htv, hF, -⟩ := Y
  have hFi : FInv ρ η th.σs (Resume p th.stack) cx th.env :=
    FInvR_FInv (htv.2.2.2.2.2.2.2)
      (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs E rd ws R h) hF
  intro t m cl ht hn hmt hcl _ _ hnw
  rcases hs0 with hs | hR
  · exact tstep_wpd hE hT.1 htv hFi hm hs X.hr hpa t m cl ht hn hmt hcl hnw
  · have hk := frame_keep hR hT.1 hT.2 hF hE htv hm r X.hr
    have hk2 : r.2.2.promises = th.promises := hk.2.1
    exact absurd (hk2 ▸ ht) hn

#print axioms tctx_wpd

end

end TermFulW
