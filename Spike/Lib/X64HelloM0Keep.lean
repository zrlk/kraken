/-
**hello.w on x86-64: main's steps after the spawn that keep memory, and
its exit** (first half; the twin of `Spike/Lib/X64WakeM0Frame.lean`,
`X64WakeM0Keep`, `X64WakeM0Instr`, `X64WakeM0Sys` and `X64WakeM0Exit` at hello's worker
data `PT1h` and kernel relation `KRH`).

wake's proofs of main's steps read the worker's data only to carry it
across (`PT1` is kept: main's step keeps the worker's threads and the
source memory) and the flag's record only through `WCompat.cT`; its kernel
relation `KR` only for `MainLive` and for no `exit` in the source trace.
Here the same proofs run at `Post` unpacked as `PartsM` (`X64HelloW1.PartsH`
with the worker at `X64HelloEmitPh.PT1hE`, so also mid-`write`), with the
worker data `PT1hE D` and the facts `MainCompatH` (`pt1`, `cT`), and with
`X64HelloWriteK.KRH` (no `exit` in the source trace, in place of an empty
trace). main's own facts are wake's `X64WakeM0.WCompat0`, unchanged.

- `MainCompatH`: the two worker-side facts main's steps read.
- `PartsM`, `post_partsM`, `PartsM.s1_get`: `Post`'s parts at `PT1hE`.
- `PartsM.s0_get`, `pt0M`, `mCtl`, `mi0`: `X64WakeW1.Parts`' main-side
  projections at `PartsM`.
- `post_frame0H'`, `post_keep0H`, `post_instrKeep0H` and the rows
  `post_silent0H`, `post_choice0H`, `post_fnc0H`, `post_rtLoad0H`,
  `post_sys0H`, `post_exited0H`, `post_exit0H`: as wake's (without the `H`).

x86-64 twin of `Spike/Lib/HelloM0Keep.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, `WCompat0.own0` reads `Q.own w 0 s []` (not `[]`): main's owned words are `WCompat0`'s
(constant, `ownConst0`; in main's cover, `ownCov0`; never a runtime write's target, `ownMp0`), as in wake's
`X64WakeM0Own`, so `post_rtLoad0H` reads an owned word's value from `PartsM.own0`.
- `PartsM.own0_const`, `ownOk0`, `own0`, `ownDisj0`, `ownCov0`, `ownMp0`: `X64WakeW1.Parts`' own facts
  (`X64WakeM0Own`) at `PartsM`.
-/
import Spike.Lib.X64WakeM0Post
import Spike.Lib.X64HelloW1Print
import Spike.Lib.X64HelloWriteK
import Spike.Lib.X64HelloKRE
import Spike.Lib.X64HelloEmitPh
import Spike.Lib.X64WakeOwn

namespace Spike.Lib.X64HelloM0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1 Spike.Lib.WorkerSrc Spike.Lib.WorkerSrcStep
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt Spike.Lib.X64WakeW1 Spike.Lib.X64WakeM0
open Spike.Lib.WakeMLive (wlRet MainLive)
open Spike.Lib.X64HelloW1 (WSideH PT1h PartsH)
open Spike.Lib.X64HelloKRE (KRHE)
open Spike.Lib.X64HelloWriteK (KRH krh_live)

/-- **The worker-side facts main's steps read**: `WakeRel`'s worker data is
hello's (`X64HelloW1.WCompatH.pt1`), and `cT` is the word placed for `cS` at
the spawn (`X64WakeW1.WCompat.cT`, at `relW`, whose `C` and `SR` are `Q`'s). -/
structure MainCompatH (Q : WakeRel) (D : WSideH Q.ι) : Prop where
  pt1 : Q.PT1 = X64HelloEmitPh.PT1hE D
  cT : ∀ w, ∃ a, (Q.C w).cT = wordLoc a ∧ wordAddr (Q.SR w).lbl (Q.C w).cS = some a ∧
    (Q.C w).cS.offset < (Q.SR w).lsize (Q.C w).cS.label

/-- **`Post`'s parts for main's steps**: `X64HelloW1.PartsH` with the worker at
`PT1hE` (`PT1h`, or mid-`write`, `X64HelloEmitPh.EmitPh`). main's step keeps the
worker's thread, its source thread and the source memory, so it carries
`PT1hE` across whichever disjunct holds. -/
structure PartsM (Q : WakeRel) (D : WSideH Q.ι) (Λ : Scc.Sem.Layout) (w : Q.ι) (t : Cfg) (s : TermRun.Cfg)
    (t0 t1 : Thread isa) (s0 s1 : TermRun.TTh) (ts : Nat → Option Nat) (tp sp : List Nat)
    (oc : Option (Nat × Nat)) : Prop where
  th : t.1.threads = #[t0, t1]
  ths : s.ths = #[s0, s1]
  core : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
    (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1.st s1.stack) t.1.mem t0 t1 s.mem s0 s1 ts
    tp sp
  preC : PreC (Q.SR w) (Q.C w).cT t.1.mem t0.views
  pt0 : Q.PT0 w t.1.mem s.mem t0 s0
  pt1 : X64HelloEmitPh.PT1hE D w t.1.mem s.mem t1 s1
  prot : CProt (Q.SR w) (Q.C w) oc t.1.mem t1 s.mem s1 ts tp sp
  kr : Q.KR w t s

/-- **`Post` unpacks at `PartsM`**, when the relation's worker data is
`PT1hE D`. -/
theorem post_partsM {Q : WakeRel} {D : WSideH Q.ι} {Λ : Scc.Sem.Layout} (hpt1 : Q.PT1 = X64HelloEmitPh.PT1hE D)
    {t : Cfg} {s : TermRun.Cfg} (h : Q.Post Λ t s) :
    ∃ w t0 t1 s0 s1 ts tp sp oc, PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc := by
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hth, hs, hcore, hp0, hp1, oc, hprot⟩, hkr⟩ := h
  simp only [WakeRel.PTw, ite_true] at hp0
  simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hpt1] at hp1
  exact ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, hth, hs, hcore, hp0.1, hp0.2, hp1, hprot, hkr⟩

/-- `PartsM`'s source worker is thread 1's. -/
theorem PartsM.s1_get {Q : WakeRel} {D : WSideH Q.ι} {Λ : Scc.Sem.Layout} {w : Q.ι} {t : Cfg}
    {s : TermRun.Cfg} {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}
    {oc : Option (Nat × Nat)} (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : s.ths[1]? = some s1 := by
  rw [h.ths]; rfl

section

/-- **`Post` after a step of main**: from `Post`'s worker parts before
(`PT1`, the protocol, `KR`), the target memory kept or one message off `cT`
appended, the source memory kept, and the new core, `PreC` and `PT0`, with
the kernel state kept and main's source off its return. -/
theorem post_frame0H' {Q : WakeRel} {D : WSideH Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range}
    {Λ : Scc.Sem.Layout} (hC : MainCompatH Q D) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1) {w : Q.ι} {t : Cfg} {s s' : TermRun.Cfg} {t0 t1 t0' : Thread isa}
    {s1 s0' : TermRun.TTh} {mem' : Memory} {ts' : Nat → Option Nat} {tp' sp' : List Nat}
    {oc : Option (Nat × Nat)} {ts : Nat → Option Nat} {tp sp : List Nat}
    (hth : t.1.threads = #[t0, t1]) (hs' : s'.ths = #[s0', s1]) (hs1 : s.ths[1]? = some s1)
    (hsm : s'.mem = s.mem) (hstr : s'.trace = s.trace)
    (hpt1 : X64HelloEmitPh.PT1hE D w t.1.mem s.mem t1 s1)
    (hprot : CProt (Q.SR w) (Q.C w) oc t.1.mem t1 s.mem s1 ts tp sp)
    (hkr : Q.KR w t s)
    (hm : mem' = t.1.mem ∨ ∃ m : Msg, mem' = (t.1.mem.append m).1 ∧ m.loc ≠ (Q.C w).cT)
    (hbk : ts' = ts ∧ tp' = tp ∧ sp' = sp)
    (hcore : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
      (fun i => if i = 0 then Q.own w 0 t0'.st s0'.stack else Q.own w 1 t1.st s1.stack)
      mem' t0' t1 s'.mem s0' s1 ts' tp' sp')
    (hpre : PreC (Q.SR w) (Q.C w).cT mem' t0'.views) (hpt0 : PT0 M w mem' s'.mem t0' s0')
    (hlive : s0'.term ≠ wlRet) :
    Q.Post Λ (t.1.withThread 0 t0' mem', t.2) s' := by
  obtain ⟨rfl, rfl, rfl⟩ := hbk
  have hth' := withThread0 (t0' := t0') (mem := mem') hth
  refine ⟨w, ⟨t0', t1, s0', s1, ts', tp', sp', hth', hs', hcore, ?_, ?_, oc, ?_⟩, ?_⟩
  · simp only [WakeRel.PTw, ite_true]
    exact ⟨hpre, by rw [hPT0]; exact hpt0⟩
  · simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hC.pt1]
    rw [hsm]
    exact hpt1
  · rw [hsm]
    rcases hm with rfl | ⟨m, rfl, hl⟩
    · exact hprot
    · exact cProt_append0 hprot hl
  · rw [hKR] at hkr ⊢
    obtain ⟨⟨hn, h0, h1, hh, -, htr⟩, hlk⟩ := hkr
    refine ⟨⟨hn, h0, h1, hh, fun _ s0'' h => ?_, by simp only [SrcSem.traceOf, hstr] at htr ⊢; exact htr⟩,
      X64HelloKRE.lk_frame0 hlk ?_ (by rw [hs', hs1]; rfl) rfl⟩
    · rw [hs'] at h
      cases (show some s0' = some s0'' from h)
      exact hlive
    · show (t.1.withThread 0 t0' mem').threads[1]? = t.1.threads[1]?
      rw [hth', hth]; rfl

/-- info: 'Spike.Lib.X64HelloM0.post_frame0H'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_frame0H'

end

section

variable {Q : WakeRel} {D : WSideH Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}

namespace Parts

variable {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

theorem _root_.Spike.Lib.X64HelloM0.PartsM.s0_get (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) :
    s.ths[0]? = some s0 := by
  rw [h.ths]; rfl

/-- `Parts`' `PT0` at `hPT0`. -/
theorem _root_.Spike.Lib.X64HelloM0.PartsM.pt0M (hPT0 : Q.PT0 = PT0 M)
    (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) :
    PT0 M w t.1.mem s.mem t0 s0 := by
  have := h.pt0; rw [hPT0] at this; exact this

/-- main's control invariant at its source thread. -/
theorem _root_.Spike.Lib.X64HelloM0.PartsM.mCtl (hPT0 : Q.PT0 = PT0 M)
    (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) :
    MCtl (M.cw w) (Ctl.of s0) :=
  ⟨rfl, (h.pt0M hPT0).2.2.2.1, (h.pt0M hPT0).2.2.2.2.1⟩

/-- **main's state and control are in `Mi`** while the process runs: `PT0`
puts them there or main's source at `wlRet`, which `KR`'s `MainLive`
excludes before the exit. -/
theorem _root_.Spike.Lib.X64HelloM0.PartsM.mi0 (hPT0 : Q.PT0 = PT0 M) (hKR : Q.KR = KRHE D r0 r1)
    (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hx : t.2.exited = none) : M.Mi w t0.st (Ctl.of s0) := by
  refine (h.pt0M hPT0).1.resolve_right fun hr => ?_
  have hk := h.kr
  rw [hKR] at hk
  exact krh_live hk.1 hx s0 h.s0_get hr

/-- **main's owned words do not depend on its state** (`ownConst0`, main's source stack empty by `PT0`;
`X64WakeW1.Parts.own0_const` at `PartsM`). -/
theorem _root_.Spike.Lib.X64HelloM0.PartsM.own0_const {μ : Marks} (hC0 : WCompat0 Q M μ Λ)
    (hPT0 : Q.PT0 = PT0 M) (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (st : isa.State) :
    Q.own w 0 st s0.stack = Q.own w 0 t0.st s0.stack := by
  rw [(h.pt0M hPT0).2.1]; exact hC0.ownConst0 w _ _

/-- **main's owned words read as their values** at any new state of main, at the same memory and
promises. -/
theorem _root_.Spike.Lib.X64HelloM0.PartsM.ownOk0 {μ : Marks} (hC0 : WCompat0 Q M μ Λ)
    (hPT0 : Q.PT0 = PT0 M) (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (st : isa.State) :
    ExtRows.OwnOk (Q.own w 0 st s0.stack) t.1.mem t0.prom := by
  rw [h.own0_const hC0 hPT0 st]; exact h.core.own0

/-- **main's owned words read as their values**, at main's empty source stack (`PT0`). -/
theorem _root_.Spike.Lib.X64HelloM0.PartsM.own0 (hPT0 : Q.PT0 = PT0 M)
    (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) :
    ExtRows.OwnOk (Q.own w 0 t0.st []) t.1.mem t0.prom := by
  have := h.core.own0
  simp only [ite_true] at this
  rw [(h.pt0M hPT0).2.1] at this
  exact this

/-- **main's owned words are not the worker's**, at any new state of main. -/
theorem _root_.Spike.Lib.X64HelloM0.PartsM.ownDisj0 {μ : Marks} (hC0 : WCompat0 Q M μ Λ)
    (hPT0 : Q.PT0 = PT0 M) (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (st : isa.State) :
    ∀ L v v', (L, v) ∈ Q.own w 0 st s0.stack → (L, v') ∈ Q.own w 1 t1.st s1.stack → False := by
  rw [h.own0_const hC0 hPT0 st]; exact h.core.own_disj

/-- **main's owned words are in its cover set** (`ownCov0`). -/
theorem _root_.Spike.Lib.X64HelloM0.PartsM.ownCov0 {μ : Marks} (hC0 : WCompat0 Q M μ Λ)
    (hPT0 : Q.PT0 = PT0 M) (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (st : isa.State) :
    ∀ L v, (L, v) ∈ Q.own w 0 st s0.stack → (Q.P w).cov 0 L := by
  rw [(h.pt0M hPT0).2.1]; exact hC0.ownCov0 w st

/-- **A runtime write of main is to none of its owned words** (`ownMp0`). -/
theorem _root_.Spike.Lib.X64HelloM0.PartsM.ownMp0 {μ : Marks} (hC0 : WCompat0 Q M μ Λ)
    (hPT0 : Q.PT0 = PT0 M) (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (st : isa.State) {l : Loc}
    (hmp : (M.ms w).mp l true) : ∀ L v, (L, v) ∈ Q.own w 0 st s0.stack → l ≠ L := by
  rw [(h.pt0M hPT0).2.1]
  rintro L v hm rfl
  exact hC0.ownMp0 w st _ v hm hmp

end Parts

/-- **A step of main keeping memory, promises and the kernel state, matched
by a local run of main's source, keeps `Post`**: thread 0 replaced by `t0'`
(same promises, its bound, cover, no-promise fact and `PreC` at the
memory), main's source after a local run from its control to `c'` with
`Mi w t0'.st c'`. -/
theorem post_keep0H (hC : MainCompatH Q D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1) {w : Q.ι} {t : Cfg} {s : TermRun.Cfg}
    {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}
    {oc : Option (Nat × Nat)} (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    {t0' : Thread isa} {c' : Ctl} (hp : t0'.prom = t0.prom) (hb : t0'.Bnd t.1.mem.last)
    (hcov : CohCoversL t0'.views t0'.prom t.1.mem ((Q.P w).cov 0))
    (hnp : (Q.P w).noProm t0'.st → t0'.prom = [])
    (hpre : PreC (Q.SR w) (Q.C w).cT t.1.mem t0'.views)
    (hr : LocalRun M.p (Ctl.of s0) c') (hmi : M.Mi w t0'.st c') :
    ∃ s', (srcS M.p arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 t0' t.1.mem, t.2) s' := by
  have hpt0 := h.pt0M hPT0
  have hctl' := localRun_mCtl hr (h.mCtl hPT0) M.wl
  let s0' : TermRun.TTh := { s0 with term := c'.term, env := c'.env }
  have hc'eq : Ctl.of s0' = c' := by
    obtain ⟨tm, en, hd⟩ := c'
    have : hd = none := hctl'.hold
    subst this; rfl
  have hlive : c'.term ≠ wlRet := hC0.live0 w _ _ hmi
  have hs' : ({ s with ths := s.ths.set! 0 s0' } : TermRun.Cfg).ths = #[s0', s1] := by
    show s.ths.set! 0 s0' = _
    rw [h.ths]; rfl
  have hex' : SrcSem.mainExit { s with ths := s.ths.set! 0 s0' } = [] :=
    mainExit_of_notRet hs' hctl'.term hlive
  have hrun : (srcS M.p arch).Run s [] { s with ths := s.ths.set! 0 s0' } :=
    WakeM0Src.localRunS_run_source_0 (P := srcPo 2 arch M.p) rfl hr.toS h.s0_get rfl rfl hpt0.2.2.1
      hpt0.2.1 hpt0.2.2.2.2.2.1 hex'
  refine ⟨_, hrun, post_frame0H' (s := s) (ts' := ts) (tp' := tp) (sp' := sp) hC hPT0 hKR h.th hs' h.s1_get
    rfl rfl h.pt1 h.prot h.kr
    (.inl rfl) ⟨rfl, rfl, rfl⟩ ?_ hpre ?_ hlive⟩
  · refine core0_same h.core (by simp) hp rfl hb hcov h.core.scov0 ?_ ?_ ?_ hnp
    · show ExtRows.OwnOk (Q.own w 0 t0'.st s0.stack) _ _
      rw [hp]; exact h.ownOk0 hC0 hPT0 _
    · exact h.ownDisj0 hC0 hPT0 _
    · exact h.ownCov0 hC0 hPT0 _
  · exact ⟨.inl (hc'eq ▸ hmi), hpt0.2.1, hpt0.2.2.1, hctl'.term, hctl'.env, hpt0.2.2.2.2.2.1, hpt0.2.2.2.2.2.2⟩

/-- info: 'Spike.Lib.X64HelloM0.post_keep0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_keep0H

end

section

/-! ## Steps keeping memory and promises -/

variable {Q : WakeRel} {D : WSideH Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **An instruction step of main keeping memory and promises keeps
`Post`**, its new state with main's source's local run in `Mi`. -/
theorem post_instrKeep0H (hC : MainCompatH Q D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1)
    (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    {outs : List (Except String (Outcome isa))} {o : Outcome isa}
    (hso : stepOne Arch.tso t0 0 t.1.mem = some outs) (ho : .ok o ∈ outs)
    (hco : CertOkC Arch.tso (certSem abi Arch.tso μ t.2 0) 0 o.thread o.mem)
    (hm : o.mem = t.1.mem) (hp : o.thread.prom = t0.prom) {c' : Ctl}
    (hr : LocalRun M.p (Ctl.of s0) c') (hmi : M.Mi w o.thread.st c') :
    ∃ s', (srcS M.p arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  have hb := (stepOne_bnd _ hso ho h.core.bnd0).1
  have hcov := stepOne_cohL _ hso ho h.core.cov0
  have hpre := h.preC.mono (stepOne_getCoh_mono _ _ hso ho _)
  rw [hm] at hb hcov ⊢
  exact post_keep0H hC hC0 hPT0 hKR h hp hb hcov (fun hn => hC0.noProm0 w _ _ _ hn hco) hpre hr hmi

section Rows

variable (hC : MainCompatH Q D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
  (hKR : Q.KR = KRHE D r0 r1)
  (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
  {outs : List (Except String (Outcome isa))} {o : Outcome isa}
  (hso : stepOne Arch.tso t0 0 t.1.mem = some outs) (ho : .ok o ∈ outs)
  (hco : CertOkC Arch.tso (certSem abi Arch.tso μ t.2 0) 0 o.thread o.mem)
include hC hC0 hPT0 hKR h hso ho hco

/-- **main's silent row keeps `Post`.** -/
theorem post_silent0H {s' : isa.State} {c' : Ctl} (he : isa.exec t0.st = some (.done s'))
    (hr : LocalRun M.p (Ctl.of s0) c') (hX : M.Mi w s' c') :
    ∃ s', (srcS M.p arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  obtain ⟨st, hP, hth, hm⟩ := Lower.stepOne_silent_ok Arch.tso 0 he (Lower.silentTree_done s')
    ⟨outs, o, hso, ho, rfl, rfl⟩
  exact post_instrKeep0H hC hC0 hPT0 hKR h hso ho hco hm (finishInstr_relKey hth).1 hr
    ((finishInstr_st hth) ▸ hP ▸ hX)

/-- **main's choice row keeps `Post`.** -/
theorem post_choice0H {P : isa.State → Prop} {tree : EvTree isa.State}
    (he : isa.exec t0.st = some tree) (hs : Lower.SilentTree P tree)
    (hX : ∀ s', P s' → ∃ c', LocalRun M.p (Ctl.of s0) c' ∧ M.Mi w s' c') :
    ∃ s', (srcS M.p arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  obtain ⟨st, hP, hth, hm⟩ := Lower.stepOne_silent_ok Arch.tso 0 he hs ⟨outs, o, hso, ho, rfl, rfl⟩
  obtain ⟨c', hr, hX'⟩ := hX _ ((finishInstr_st hth) ▸ hP)
  exact post_instrKeep0H hC hC0 hPT0 hKR h hso ho hco hm (finishInstr_relKey hth).1 hr hX'

/-- **main's fence row keeps `Post`.** -/
theorem post_fnc0H {k : Kraken.FenceKind} {s' : isa.State} {c' : Ctl}
    (he : isa.exec t0.st = some (.fence k fun _ => .done s'))
    (hr : LocalRun M.p (Ctl.of s0) c') (hX : M.Mi w s' c') :
    ∃ s', (srcS M.p arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  obtain ⟨hst, hm, hp⟩ := stepOne_fence_eq Arch.tso he hso ho
  exact post_instrKeep0H hC hC0 hPT0 hKR h hso ho hco hm hp hr (hst ▸ hX)

/-- **main's runtime-load row keeps `Post`**: the value read is a `G` value
(the memory's invariant); main owns no word (`WCompat0.own0`). -/
theorem post_rtLoad0H {kl : Kraken.LoadKind} {L : Loc} {g : Val → isa.State} {c' : Ctl}
    (he : isa.exec t0.st = some (.load kl false L fun v => .done (g v)))
    (hr : LocalRun M.p (Ctl.of s0) c')
    (hX : ∀ v, (M.ms w).G L v → (∀ u, (L, u) ∈ (M.ms w).own t0.st → v = u) → M.Mi w (g v) c') :
    ∃ s', (srcS M.p arch).Run s [] s' ∧ Q.Post Λ (t.1.withThread 0 o.thread o.mem, t.2) s' := by
  obtain ⟨hm, hp⟩ := stepOne_load_keep' 0 he hso ho
  rw [hC0.G0 w] at hX
  simp only [hC0.own0 w] at hX
  have hmi : M.Mi w o.thread.st c' := by
    by_cases hL : ∃ v0, (L, v0) ∈ Q.own w 0 t0.st []
    · obtain ⟨v0, hv0⟩ := hL
      have hown := h.own0 hPT0
      have hL8 := (hown L v0 hv0).1
      have hcL := hC0.ownCov0 w _ L v0 hv0
      obtain ⟨a, rfl⟩ : ∃ a, L = wordLoc a := ⟨_, ExtRows.loc_wordLoc hL8⟩
      obtain ⟨-, ts1, v, hst, hl, hrd⟩ := stepOne_load_tlatestL Arch.tso he hso ho h.core.cov0 hcL
      rw [hst]
      exact hX v (h.core.memInv.read? hrd) fun u hu => hown.read hl hrd u hu
    · obtain ⟨v, hst, hG⟩ := stepOne_load_msgsExcept he hso ho (Scc.Sem.MemInv.msgsExcept h.core.memInv _)
        h.core.memInv.1
      rw [hst]
      exact hX v hG fun u hu => absurd ⟨u, hu⟩ hL
  exact post_instrKeep0H hC hC0 hPT0 hKR h hso ho hco hm hp hr hmi

end Rows

/-- info: 'Spike.Lib.X64HelloM0.post_rtLoad0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_rtLoad0H

end

section

variable {Q : WakeRel} {D : WSideH Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **A returning system call of main keeps `Post`**: the call is not
`exit_group` (`hg`), nor `exit` or `clone` (the row's `SysOk`) nor `write`
(`WCompat0.noWrite0`), so it returns (`sysStep_back`) to a state the row
lists (`sysStep_cases`), with no event; no promise at a no-promise state
(`CertAfter`, `WCompat0.noProm0`). main's state and control are given in
`Mi` (`hmi`). -/
theorem post_sys0H (hC : MainCompatH Q D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1)
    (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hmi : M.Mi w t0.st (Ctl.of s0))
    {call : Call} (hat : abi.atSys t0.st = true) (hd : decode abi.nrs (abi.nr t0.st) (abi.arg t0.st) = some call)
    (hg : ∀ v, call ≠ .exitGroup v)
    {p : Pick} {es : List Ev} {t' : Cfg} (hs : sysStep abi Arch.tso 0 t p = some (es, t'))
    (hca : CertAfter abi Arch.tso μ 0 t') :
    es = [] ∧ ∃ s', (srcS M.p arch).Run s [] s' ∧ Q.Post Λ t' s' := by
  obtain ⟨hok, hX⟩ := sys_rows0 hC0 hmi hat hd
  have hc : callOf abi t0 = some call := hd
  have hnx : call ≠ .exit := hok.1
  have hcl : ∀ st tl, call ≠ .clone st tl := hok.2.1
  have hnw : ∀ fd buf n, call ≠ .write fd buf n := fun fd buf n e =>
    hC0.noWrite0 w _ _ fd buf n hmi hat (e ▸ hd)
  have ht0 : t.1.threads[0]? = some t0 := by rw [h.th]; rfl
  obtain ⟨-, call', hc', hcases⟩ := sysStep_cases ht0 hs (fun fd buf n hw => by
    exact absurd (Option.some.inj (hc.symm.trans hw)) (hnw fd buf n))
  rw [hc] at hc'
  cases hc'
  obtain ⟨t'', ht'', hmem⟩ : ∃ t'', t'.1.threads[0]? = some t'' ∧ t''.st ∈ certSuccs abi t0.st call := by
    rcases hcases with ⟨fd, buf, n, -, -, -, hw, -⟩ | ⟨r, -, -, -, -, -, t'', ht'', hm, -⟩ | ⟨hw, -⟩ |
      ⟨v, hw, -⟩
    · exact absurd hw (hnw fd buf n)
    · exact ⟨t'', ht'', hm⟩
    · exact absurd hw hnx
    · exact absurd hw (hg v)
  obtain ⟨rfl, u, r, rfl, hv, hp, hrv, hwv⟩ := sysStep_back ht0 hc hnw hnx hg hcl hs
  refine ⟨rfl, ?_⟩
  have hget : (t.1.withThread 0 (retThread abi u r) t.1.mem).threads[0]? = some (retThread abi u r) :=
    Live.Sem.withThread_get_self ht0
  rw [hget] at ht''
  cases ht''
  have hub : u.Bnd t.1.mem.last :=
    ⟨hv ▸ h.core.bnd0.views, by unfold Thread.RegsLe; rw [hrv, hwv]; exact h.core.bnd0.regs⟩
  obtain ⟨c', hr, hmi'⟩ := hX _ hmem
  exact post_keep0H hC hC0 hPT0 hKR h (t0' := retThread abi u r) (by rw [retThread_prom, hp])
    (ExtThread.bnd_retThread abi hub r)
    (by rw [retThread_views abi u r, retThread_prom, hv, hp]; exact h.core.cov0)
    (fun hn => hC0.noProm0 w _ _ _ hn (hca _ hget)) (by rw [retThread_views abi u r, hv]; exact h.preC) hr hmi'

/-- **The process exiting keeps `Post`** (`exit_group`'s kernel state, with
any outcome): the configuration and the source are kept, and `KR`'s
`MainLive` holds vacuously once the process has exited. -/
theorem post_exited0H (hKR : Q.KR = KRHE D r0 r1) {t : Cfg} {s : TermRun.Cfg} (hpost : Q.Post Λ t s)
    (o : Outcome) : Q.Post Λ (t.1, { t.2 with exited := some o }) s := by
  obtain ⟨w, hi, hk⟩ := hpost
  refine ⟨w, hi, ?_⟩
  rw [hKR] at hk ⊢
  obtain ⟨⟨hn, h0, h1, hh, -, htr⟩, hlk⟩ := hk
  exact ⟨⟨hn, h0, h1, hh, fun hx => (by cases hx), htr⟩, X64HelloKRE.lk_frame0 hlk rfl rfl rfl⟩

/-- info: 'Spike.Lib.X64HelloM0.post_sys0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_sys0H

end

section

variable {Q : WakeRel} {D : WSideH Q.ι} {M : MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **main's `exit_group` off every abort site keeps `Post`**: the row's
`SysOk` (off `abortAt` by `WCompat0.abortAt0`) is `MainExit`, a local run of
main's source to a control whose return is the exit event; the source runs
there with that event as its trace (no exit before it: `KR`'s empty trace),
landing at `wlRet` (`PT0`'s exited disjunct); the kernel state records the
exit, so `KR`'s `MainLive` holds vacuously. -/
theorem post_exit0H (hC : MainCompatH Q D) (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (hKR : Q.KR = KRHE D r0 r1) (h : PartsM Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hmi : M.Mi w t0.st (Ctl.of s0)) (hat : abi.atSys t0.st = true) {v : Nat}
    (hd : decode abi.nrs (abi.nr t0.st) (abi.arg t0.st) = some (.exitGroup v))
    (hoff : ¬ ∃ k a, μ.abortAt k = some a ∧ pcOf t0.st = a) :
    ∃ s', (srcS M.p arch).Run s [.exit (exitCode v)] s' ∧
      Q.Post Λ (t.1, { t.2 with exited := some (.exit (exitCode v)) }) s' := by
  obtain ⟨hok, -⟩ := sys_rows0 hC0 hmi hat hd
  obtain ⟨c', hr, -, hex⟩ := hok.2.2.2 v rfl (fun hab => hoff (hC0.abortAt0 w _ hab))
  have hpt0 := h.pt0M hPT0
  have hctl' := localRun_mCtl hr (h.mCtl hPT0) M.wl
  have hlive : s0.term ≠ wlRet := hC0.live0 w _ _ hmi
  have hnr : ∀ a, (Ctl.of s0).term ≠ .ret a := fun a hra => hlive (mterm_ret (h.mCtl hPT0).term hra)
  have hk := h.kr
  rw [hKR] at hk
  obtain ⟨⟨hn, h0, h1, hh, -, htr⟩, hlk⟩ := hk
  let s0' : TermRun.TTh := { s0 with term := c'.term, env := c'.env }
  have hrun := localRun_run_source_wc (P := srcPo 2 arch M.p) rfl hr h.s0_get rfl rfl hpt0.2.2.1 hpt0.2.1
    hpt0.2.2.2.2.2.1 hnr (fun x hx => by
      change Ev.exit x ∈ SrcSem.traceOf s at hx
      exact htr x hx)
  have hs' : ({ s with ths := s.ths.set! 0 s0' } : TermRun.Cfg).ths = #[s0', s1] := by
    show s.ths.set! 0 s0' = _
    rw [h.ths]; rfl
  have hi' : ({ s with ths := s.ths.set! 0 s0' } : TermRun.Cfg).ths[0]? = some s0' := by rw [hs']; rfl
  have hme := hex _ s0' hi' rfl rfl hpt0.2.1
  have hret : s0'.term = wlRet := by
    by_cases hr' : ∀ a, s0'.term ≠ .ret a
    · rw [mainExit_of_not_ret hi' hr'] at hme; cases hme
    · obtain ⟨a, ha⟩ : ∃ a, s0'.term = .ret a := Classical.byContradiction fun hn => hr' fun a ha => hn ⟨a, ha⟩
      exact mterm_ret hctl'.term ha
  rw [hme] at hrun
  refine ⟨_, hrun, w, ⟨t0, t1, s0', s1, ts, tp, sp, h.th, hs', ?_, ?_, ?_, oc, h.prot⟩, ?_⟩
  · exact core0_same h.core (by simp) rfl rfl h.core.bnd0 h.core.cov0 h.core.scov0 h.core.own0 h.core.own_disj
      (fun L v hm => h.core.own_cov 0 L v (by decide) hm) h.core.noProm0
  · simp only [WakeRel.PTw, ite_true]
    refine ⟨h.preC, ?_⟩
    rw [hPT0]
    exact ⟨.inr hret, hpt0.2.1, hpt0.2.2.1, hctl'.term, hctl'.env, hpt0.2.2.2.2.2.1, hpt0.2.2.2.2.2.2⟩
  · simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hC.pt1]
    exact h.pt1
  · rw [hKR]
    exact ⟨⟨hn, h0, h1, hh, fun hx => (by cases hx), htr⟩,
      X64HelloKRE.lk_frame0 hlk rfl (by rw [hs', h.s1_get]; rfl) rfl⟩

/-- info: 'Spike.Lib.X64HelloM0.post_exit0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms post_exit0H

end

end Spike.Lib.X64HelloM0

/-- info: 'Spike.Lib.X64HelloM0.post_partsM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloM0.post_partsM

/-- info: 'Spike.Lib.X64HelloM0.PartsM.s1_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloM0.PartsM.s1_get

/-- info: 'Spike.Lib.X64HelloM0.PartsM.s0_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloM0.PartsM.s0_get

/-- info: 'Spike.Lib.X64HelloM0.PartsM.pt0M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloM0.PartsM.pt0M

/-- info: 'Spike.Lib.X64HelloM0.PartsM.mCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloM0.PartsM.mCtl

/-- info: 'Spike.Lib.X64HelloM0.PartsM.mi0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloM0.PartsM.mi0

/-- info: 'Spike.Lib.X64HelloM0.post_instrKeep0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloM0.post_instrKeep0H

/-- info: 'Spike.Lib.X64HelloM0.post_silent0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloM0.post_silent0H

/-- info: 'Spike.Lib.X64HelloM0.post_choice0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloM0.post_choice0H

/-- info: 'Spike.Lib.X64HelloM0.post_fnc0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloM0.post_fnc0H

/-- info: 'Spike.Lib.X64HelloM0.post_exited0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloM0.post_exited0H
