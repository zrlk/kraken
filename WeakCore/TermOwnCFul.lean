import WeakCore.TermOwnCTop
import WeakCore.TermOwnCR5
import WeakCore.TermRiseLoc

/-! # TermOwnCFul: case B of the post-demand trichotomy, the fulfil cover (ownC)

`caseB_of : CaseBCov` from `StepScopeF`.

A demanded unit `a = ⟨l, o⟩` whose coherence the step raises to a pre-step own promise `K′`:
* the raised view lands on a message at `a` (`TermRiseLoc.tstep_riseLoc`), `K′`'s; `PromAbove` after
  the step makes `K′` fulfilled (`tstep_fulfil`: `SW` at `a`);
* `a` is no word unit (`¬ VisU` at a frontier cell), so the fulfilling write is a `UnitsOp`, whose
  address atom gives `OpTgtP th l` (`opTgt_of_units`), or a `fetch`/`cas` at an RMW atom
  (`fetch_cls2`, `cas_cls2`);
* `UnitsOp`: `KeepQRS`'s `RepinCovS` (the `bufInit` premise is vacuous: `bufInit` at a frontier target
  is `KindA`), at the lowest own promise `th0 ≤ K′` (gone after the step by `PromAbove`), the piece
  from `PromTyOK` at `K′`;
* RMW atom: a `freeQW` zero item, pinned at `K′`'s message (`predAt_coh`), typed by `MemOKP` after
  the step (`K′` is no promise there; not `undef` by `PromNotUndef`).
-/

namespace TermOwnCFul

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermTyped TermB5 TermForWU TermFul TermPool TermOverCrBII
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem steps_reach {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (h : TermStep.Steps p k arch c c') : TermLiveProps.Reach p k arch c c' := by
  induction h with
  | refl c => exact .refl c
  | step hs _ ih => exact .step hs ih

theorem val_of_addrOf {w : Word} {a : Address} (h : addrOf w = some a) : ∃ g, w.val = .loc a g := by
  unfold addrOf at h
  revert h
  cases w.val <;> intro h <;> simp at h
  subst h
  exact ⟨_, rfl⟩

theorem addr_eq {a : Address} {l : AllocLabel} {o : Nat} (h1 : a.label = l) (h2 : a.offset = o) :
    a = ⟨l, o⟩ := by
  cases a
  cases h1
  cases h2
  rfl

/-- A `UnitsOp`'s write address lies in the label of the op's address atom. -/
theorem opTgt_of_units {g : G} {th : TTh} {x : String} {op : Op} {e : Expr} {pw : Word} {b : Address}
    {rel : Bool} {us : List Acc} {ws : List Word} {s : St} (hterm : th.term = .let_ x op e)
    (hu : UnitsOp g th.env s op pw b rel us ws) : TermPiece.OpTgtP th b.label := by
  unfold TermPiece.OpTgtP
  rw [hterm]
  cases op <;> simp only [UnitsOp] at hu
  case store rl a v tok =>
    obtain ⟨-, t, t', μ, u, hea, -, -, hb, -⟩ := hu
    obtain ⟨g0, hg⟩ := val_of_addrOf hb
    exact ⟨a, t, pw, b, g0, rfl, hea, hg, rfl⟩
  case xchg a v =>
    obtain ⟨-, t, t', μ, u, hea, -, -, hb, -⟩ := hu
    obtain ⟨g0, hg⟩ := val_of_addrOf hb
    exact ⟨a, t, pw, b, g0, rfl, hea, hg, rfl⟩
  case xchgAt bb i v =>
    obtain ⟨-, t, t1, t2, iws, μ, u, j, a0, hea, -, -, -, -, hb, -, hbe⟩ := hu
    obtain ⟨g0, hg⟩ := val_of_addrOf hb
    exact ⟨bb, t, pw, a0, g0, rfl, hea, hg, by rw [hbe]; rfl⟩
  case xchgAtF bb i q v =>
    obtain ⟨-, t, t1, t2, iws, μ, u, j, a0, us0, c, o, hea, -, -, -, -, hb, -, -, -, hbe⟩ := hu
    obtain ⟨g0, hg⟩ := val_of_addrOf hb
    exact ⟨bb, t, pw, a0, g0, rfl, hea, hg, by rw [hbe]; rfl⟩
  case bufInit bb i v =>
    obtain ⟨-, t, t1, t2, iws, μ, u, j, a0, μ', n, e', ψ, hea, -, -, -, -, hb, -, -, hbe⟩ := hu
    obtain ⟨g0, hg⟩ := val_of_addrOf hb
    exact ⟨bb, t, pw, a0, g0, rfl, hea, hg, by rw [hbe]; rfl⟩
  case stl bb i v =>
    obtain ⟨-, -, t, t1, t2, iws, vs, μ, u, j, y, a0, sg, w, s1, old, x', hea, -, -, -, -, -, hb, -, hbe, -⟩ := hu
    obtain ⟨g0, hg⟩ := val_of_addrOf hb
    exact ⟨bb, t, pw, a0, g0, rfl, hea, hg, by rw [hbe]; rfl⟩
  case stlw bb wi jl v =>
    obtain ⟨-, -, t, t1, t2, t3, iws, jws, vs, μ, u, i, j, y, a0, sg, w, s1, old, x', hea, -, -, -, -, -, -, -,
      hb, -, hbe, -⟩ := hu
    obtain ⟨g0, hg⟩ := val_of_addrOf hb
    exact ⟨bb, t, pw, a0, g0, rfl, hea, hg, by rw [hbe]; rfl⟩
  all_goals exact hu.elim

#print axioms opTgt_of_units

/-- **Fulfils off word units**: the fulfilling write's target is the op's address-atom label
(`UnitsOp`) or an RMW atom (`fetch`, `cas`). -/
theorem tstep_fulCls {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {cx : Cx} {r : Memory × List Ts × TTh} (hE : EnvOK p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (h : r ∈ tstep g mem pairs th) :
    ∀ (t : Ts) (m : Msg), t ∈ th.promises → t ∉ r.2.2.promises → mem[t]? = some m →
      ¬ WordUnit (CE η) m.loc → TermPiece.OpTgtP th m.loc.label ∨ TermOwnCR5.RmwAtomC (CE η) m.loc := by
  intro t m ht hn hmt hnw
  have hlt := MemInv_promLt hm
  obtain ⟨m0, hm0, hsw, -, -⟩ := (TermFul.tstep_fulfil hlt (MemInv_nopair hm) h).2 t ht hn
  obtain rfl : m = m0 := Option.some.inj (hmt.symm.trans hm0)
  rcases hsw with ⟨x, op, e, hterm, hw⟩ |
      ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, tr, mr, hterm, hea, -, -, hb, -⟩
  · have hsc0 := hsc
    have hT0 := hT
    rw [hterm] at hT0 hsc0
    cases hT0 with
    | let_ hop _ =>
        rcases hw with ⟨pw, b, rel, us, ws, j, w, hu, -, -, hloc, -⟩ |
            ⟨o', acq, rel, a, v, t0, t1, pw, nw, tr, mr, rfl, hea, -, hb, -⟩
        · left
          rw [hloc]
          exact (opTgt_of_units hterm hu : TermPiece.OpTgtP th b.label)
        · exact .inr ((TermOwnCR5.fetch_cls2 hop hsc0 hi hE htv hm hea hb).resolve_left hnw)
  · rw [hterm] at hT hsc
    exact .inr ((TermOwnCR5.cas_cls2 hT hsc hi hE htv hm hea hb).resolve_left hnw)

#print axioms tstep_fulCls

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- `tstep_fulCls` at a thread step (`tctx_wpd`'s frame). -/
theorem tctx_fulCls {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res}
    (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th)) :
    ∀ (t : Ts) (m : Msg), t ∈ th.promises → t ∉ r.2.2.promises → c.mem[t]? = some m →
      ¬ WordUnit (CE η) m.loc → TermPiece.OpTgtP th m.loc.label ∨ TermOwnCR5.RmwAtomC (CE η) m.loc := by
  have hs0 := hsc X Y
  obtain ⟨-, -, hE, hT, htv, hF, -⟩ := Y
  have hFi : FInv ρ η th.σs (Resume p th.stack) cx th.env :=
    FInvR_FInv (htv.2.2.2.2.2.2.2)
      (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs E rd ws R h) hF
  intro t m ht hn hmt hnw
  rcases hs0 with hs | hR
  · exact tstep_fulCls hE hT.1 htv hFi hm hs X.hr t m ht hn hmt hnw
  · have hk := frame_keep hR hT.1 hT.2 hF hE htv hm r X.hr
    have hk2 : r.2.2.promises = th.promises := hk.2.1
    exact absurd (hk2 ▸ ht) hn

#print axioms tctx_fulCls

/-- **Case B** (`CaseBCov`). -/
theorem caseB_of (hsc : StepScopeF p k arch Sp Init MintOK c0) :
    TermOwnCTop.CaseBCov p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs X Y hK hPA _ E' RSc RSh hF hMI hcovS l cl hold ho hpf0
    hs1 hpe o tw hPD hgt hKp
  -- coherence after the step lands on a message at its address
  obtain ⟨m', hm', hml'⟩ := TermRiseLoc.tstep_riseLoc X.hr hgt
  have hm'r : r.1[r.2.2.vs.coh ⟨l, o⟩]? = some m' := hm'
  -- `K′` is a pre-step own promise, fulfilled by the step
  have hKlt : r.2.2.vs.coh ⟨l, o⟩ < c.mem.size := X.inv.plt i th _ X.hth hKp
  have hcm' : c.mem[r.2.2.vs.coh ⟨l, o⟩]? = some m' := by
    have h := Array.getElem?_eq_getElem hKlt
    have h2 := (TermFul.tstep_grow X.hr).1 _ _ h
    rw [h]
    exact congrArg some (Option.some.inj (h2.symm.trans hm'r))
  have hKn : r.2.2.vs.coh ⟨l, o⟩ ∉ r.2.2.promises := by
    intro h
    have h1 := hPA _ h m' hm'
    rw [hml'] at h1
    exact Nat.lt_irrefl _ h1
  -- the unit is no word unit
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 (show E'.pfr l ≠ none by rw [hpe]; exact hpf0)
  have hnwE' : ¬ WordUnit E' ⟨l, o⟩ := fun h => hPD.2.1 ⟨h, Vis_pfr hf⟩
  have hstoL : E'.sto l = (CE η).sto l := hs1.trans hold.symm
  have hnw : ¬ WordUnit (CE η) ⟨l, o⟩ := fun h => hnwE' ((WordUnit_congr (a := ⟨l, o⟩) hstoL).2 h)
  -- the invariant's typing
  obtain ⟨S0, ρ0, η0, cx0, Rf0, Rs0, hCE0, htid0, hE0, hT0, htv0, hFI0, hsum0, -, hm0, -, -⟩ :=
    (X.inv.thr i th X.hth).env X.inv.clo
  have Y0 : EnvAt p Eg i th (Tot i) S0 ρ0 η0 cx0 Rf0 Rs0 := ⟨hCE0, htid0, hE0, hT0, htv0, hFI0, hsum0⟩
  have hsto00 : ∀ l, (CE η0).sto l = (CE η).sto l := fun l => by rw [hCE0, Y.1]; rfl
  have hnw0 : ¬ WordUnit (CE η0) m'.loc := by
    rw [hml']
    exact fun h => hnw ((WordUnit_congr (a := ⟨l, o⟩) (hsto00 l)).1 h)
  have hcls := tctx_fulCls hsc X Y0 hm0 _ m' hKp hKn hcm' hnw0
  rw [hml'] at hcls
  have hsG : Eg.sto l = some cl := by
    have h1 := hold
    rw [Y.1] at h1
    exact cutSto_sub h1
  rcases hcls with hOT | hR0
  · -- `UnitsOp`: the re-pin cover
    right
    have hpgE : Eg.pfr l ≠ none := by
      have h := hpf0
      rw [Y.1] at h
      exact h
    obtain ⟨fg, hfg⟩ := Option.ne_none_iff_exists'.1 hpgE
    have hw := X.inv.promTy i th _ m' X.hth hKp hcm' cl (by rw [hml']; exact hsG) (by rw [hml']; exact ⟨fg, hfg⟩)
    obtain ⟨q, S1, us, hP1, hus, hq1, hq2⟩ :=
      TermOwnCTop.piece_of_wordOKA (X.inv.clo l cl hsG) (X.inv.cmg l cl hsG) hw
    have hoff : m'.loc.offset = o := by rw [hml']
    rw [hoff] at hq1 hq2
    -- the lowest own promise at the unit, gone after the step
    obtain ⟨t0, m0, ht0, hm0', hl0, h1, h2, hle, hmin⟩ :=
      TermPiece.lowest_inR (s := stOf c.mem c.pairs th) (lo := o) (hi := o + 1) hKp hcm' (by rw [hml'])
        (Nat.le_of_eq hoff.symm) (by rw [hoff]; exact Nat.lt_succ_self o)
    have hm0loc : m0.loc = ⟨l, o⟩ := addr_eq hl0 (Nat.le_antisymm (Nat.le_of_lt_succ h2) h1)
    have hlo0 : TermPiece.LowOwn (stOf c.mem c.pairs th) ⟨l, o⟩ t0 :=
      ⟨ht0, ⟨m0, hm0', hm0loc⟩, fun t' m'' h3 h4 h5 => hmin t' m'' h3 h4 (by rw [h5])
        (by rw [h5]; exact Nat.le_refl o) (by rw [h5]; exact Nat.lt_succ_self o)⟩
    have hth0 : t0 ∉ r.2.2.promises := by
      intro h
      have hm0r : r.1[t0]? = some m0 := (TermFul.tstep_grow X.hr).1 t0 m0 hm0'
      have h3 := hPA t0 h m0 hm0r
      rw [hm0loc] at h3
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h3 hle)
    have hbuf : ∀ x b i' v e, th.term = .let_ x (.bufInit b i' v) e → ∀ rti wi n,
        evalAt th.env i' = some (rti, [wi]) → numOf [wi] = some n → n ≠ (CE η).rc l := by
      intro x b i' v e hterm
      exfalso
      refine hK ⟨by rw [hterm]; rfl, Or.inl ⟨x, e, ?_⟩, l, hpf0, (TermPlant.opTgt_iffP).2 hOT⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨b, i', v, hterm⟩))))
    have hown : cl.owner = some (CE η).tid := by
      show cl.owner = some η.tid
      rw [Y.2.1]
      exact ho
    obtain ⟨y, hy, hy1, hy2⟩ := hcovS l hbuf hOT cl o t0 tw hold hown hpf0 (fun h => hnw h.1) hlo0 hth0
      hPD.2.2.1 hPD.2.2.2.2 hPD.2.2.2.1 ⟨q, S1, us, hP1, hus, hq1, hq2⟩
    exact ⟨y, hy, hy1, hy2⟩
  · -- RMW atom: a zero item
    left
    obtain ⟨c1, S1, h1, h2⟩ := hR0
    have h1' : (CE η0).sto l = some c1 := h1
    rw [hsto00, hold] at h1'
    cases h1'
    have hR : TermOwnCR5.RmwAtomC E' ⟨l, o⟩ := ⟨cl, S1, hs1, h2⟩
    have hlo := hPD.2.2.1
    have hpin := TermOwnCPin.predAt_coh hlo (TermOwnCPin.coh_lt_of_promAbove hPA hlo) hm' hml' hPD.2.2.2.1
    have hok : WordOK E' cl.ty o (mw m') := by
      rcases hMI.1.1 _ m' cl hKn hm' (by rw [hml']; exact hs1) with hu | hw
      · exact absurd hu (X.inv.promNU i th _ m' X.hth hKp hcm')
      · have hoff : m'.loc.offset = o := by rw [hml']
        rw [hoff] at hw
        exact hw
    obtain ⟨x, hx⟩ := TermOwnCR5.freeQW_rmw hR hs1 hlo hnwE' hpin hok
    exact ⟨x, TermOwnCOld.zeroIt_of_freeQW hx⟩

#print axioms caseB_of

end

end TermOwnCFul
